#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/CommandLine.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/Utils.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Serialization/ASTReader.h"
#include <algorithm>
#include <iostream>
#include <sstream>
#include <fstream>
#include <unistd.h>
#include "llvm/Support/Path.h"

using namespace std;
using namespace std::placeholders;
using namespace llvm; 
using namespace clang;
using namespace clang::ast_matchers;
using namespace clang::tooling;

// Apply a custom category to all command-line options so that they are the
// only ones displayed.
// static cl::OptionCategory MyToolCategory("my-tool options");

static cl::opt<std::string> occDir
( "d",
  cl::value_desc("occ directory"),
  cl::desc("occ directory"),
  cl::Required);

static cl::opt<std::string> outputDir
( "o",
  cl::value_desc("output directory"),
  cl::desc("Output directory where the generated files will be put"),
  cl::Required);

static cl::opt<std::string> TargetClass
( "c",
  cl::value_desc("target class"),
  cl::desc("the target class file which should be generated"),
  cl::Optional);

static llvm::SmallString<256> realOutputDir;
static llvm::SmallString<256> realOccDir;

//static llvm::cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// A help message for this specific tool can be added afterwards.
// static llvm::cl::extrahelp MoreHelp("\nMore help text...\n");

//hasName("gp_Pnt"))
DeclarationMatcher ClassMatcher =
  cxxRecordDecl(isExpansionInMainFile(), hasDefinition()
		).bind("classDecl");
DeclarationMatcher EnumMatcher =
  enumDecl(isExpansionInMainFile()//, hasDefinition()
	   ).bind("enumDecl");

class FType {
public:
  FType(): builtin(false), pointer(false), handle( false), templateClass(false) {}
  string name;
  string inClass;
  bool   builtin;
  bool   pointer;
  bool   handle;
  bool   templateClass;
  string templateTypeSpec;
  list<FType> typeArgs;
  string log;
};


bool translateStandardTypes( const string& name, FType& t) {
  bool ret = true;
  if( name == "Real" )
    { t.name = "double"; t.builtin = true; t.inClass.clear(); }
  else if( name == "ShortReal" )
    { t.name = "float"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Integer" )
    { t.name = "int"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Boolean" )
    { t.name = "bool"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Character" )
    { t.name = "char"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Byte" )
    { t.name = "byte"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Address" )
    { t.name = "caddress"; t.builtin = true; t.inClass.clear(); }
  else if( name == "Size" )
    { t.name = "size"; t.builtin = true; t.inClass.clear(); }
  else if( name == "ExtCharacter" )
    { t.name = "uint16"; t.builtin = true; t.inClass.clear(); }
  else if( name == "CString" )
    { t.name = "cstring"; t.builtin = true; t.inClass.clear(); }
  else if( name == "ExtendedString" )
    { t.name = "+uint16"; t.builtin = true; t.inClass.clear(); }
  else ret = false;
  return ret;
}


string cToFclass( const string& n) {
  if( n == "NCollection" ) return "Collection";
  return n;
}

// string fToCclass( const string& n) {
//   if( n == "Collection" ) return "NCollection";
//   return n;
// }

void setClassAndName( const string& n, FType& t) {
  string::size_type p = n.find_first_of( '_');
  if( p != string::npos ) {
    t.inClass = cToFclass( n.substr( 0, p));
    t.name = n.substr( p+1, string::npos);
  } else {
    t.name = n;
  }
}

template<class T> string dumpToStr(const T& t) {
  string s;
  raw_string_ostream ss( s);
  //PrintingPolicy pp = LangOptions();
  //pp.FullyQualifiedName = 1;
  // pp.PrintCanonicalTypes = 1;
  t.dump(ss);
  ss.flush();
  return s;
}


enum TypeImplementation {
  Value,
  OccHandle,
  TemplateClassVH,
  Other
};

bool checkFor( const string& cl, const TypeImplementation& ti);

bool trTemplate( const QualType& qt, FType& t);

bool trTColName( const string& name, FType& t, string& coltype);

FType trType( const QualType& qt_) {
  QualType qt = qt_;
  FType t; t.builtin=false; t.pointer=false;
  if( qt->isReferenceType() || qt->isPointerType()) {
    qt = qt->getPointeeType();
    t.log += "p,";
    if( !qt.isLocalConstQualified() ) t.pointer = true; 
  }
  if( qt.isLocalConstQualified()) qt.removeLocalConst();
  
  if( qt->isTypedefNameType()){
    t.log += "td,";
    setClassAndName( qt.getAsString(), t);
    FType u = trType( qt->getAs<TypedefType>()->desugar());
    if( u.inClass == "Collection" && u.templateClass) { // t.inClass.compare( 0,4,"TCol" ) == 0) {
      // this will expand to NCollection ...
      t.log += t.inClass + ",";
      bool p = t.pointer; string l = t.log;
      //t = trType( qt->getAs<TypedefType>()->desugar());
      t = u;
      t.pointer = p; t.log = l + t.log;
    } else if( t.inClass == "Standard") {
      translateStandardTypes( t.name, t);
    }
  } else if( qt->isBuiltinType() ) {
    t.log += "bi,";
    t.name = qt.getAsString(); t.builtin = true;
  } else if( auto et = qt->getAs<ElaboratedType>()) {
    t.log += "el,";
    if( !trTemplate( qt, t)) {
      t.name = qt.getAsString();
    }
  } else if( qt->isRecordType()) {
    t.log += "rd,";
    if( !trTemplate( qt, t)) {
      const CXXRecordDecl* crd = qt->getAsCXXRecordDecl();
      string coltype;
      if( !trTColName( crd->getNameAsString(), t, coltype)) {
	setClassAndName( crd->getNameAsString(), t);
      }
    }
  } else if( qt->isEnumeralType()) {
    t.log += "en,";
    string n = qt.getAsString();
    string::size_type p = n.find( "enum ");
    if( p != string::npos ) {
      n = n.substr( p+5, string::npos);
    }
    setClassAndName( n, t);
  } else {
    t.log += string("cl=") + string(qt->getTypeClassName());
    //qt->dump();
    t.name = qt.getAsString();
  }
  if( !t.templateTypeSpec.empty()) {
    t.log += string(",") + t.templateTypeSpec;
  }
  return t;
}

bool trTemplate( const QualType& qt, FType& t) {
  if( auto st = qt->getAs<TemplateSpecializationType>()) {
    t.log += "ts,";
    string tn = dumpToStr( st->getTemplateName());
    if( tn == "handle" ) { 
      FType p = trType(st->getArg(0).getAsType());
      if( checkFor( p.inClass, OccHandle)) {
	// these types will always be implemented as handle
	t.log += "hd,";	
	t.name = p.name;
	t.inClass = p.inClass;
	t.handle = true;
	t.log += p.log;
      } else if( p.inClass == "Collection") {
	t.log += "col,";
	t.name = p.name;
	t.inClass = p.inClass;
	t.templateClass = p.templateClass;
	t.templateTypeSpec = p.templateTypeSpec;
	t.typeArgs = p.typeArgs;
	t.log += p.log;
      } else {
	t.log += "ehd,";
	t.name = "handle";
	t.inClass = "Standard";
	t.templateClass = true;
	t.typeArgs.push_back( p);
      }
    } else {
      // no handle
      setClassAndName( tn, t);
      t.log += "ta,";
      const auto n = st->getNumArgs();
      for( unsigned int i = 0; i<n; ++i) {
	t.typeArgs.push_back( trType(st->getArg(i).getAsType()));
      }
      t.templateClass = true;
      if( t.inClass == "Collection" ) {
	t.templateTypeSpec = "V"; // ValueType
      }
    }
    return true;
  }
  return false;
}

bool trTColName( const string& name, FType& t, string& coltype)
{
  if( name.compare( 0,4,"TCol" ) == 0) {
    t.inClass = "Collection";
    t.templateClass = true;
    // get the class of the argument
    string::size_type p = name.find_first_of( '_');
    coltype = name.substr( p+1, string::npos);
    FType a;
    a.inClass = name.substr( 4 /*TCol*/, p-4);
    if( a.inClass == "Std") a.inClass = "Standard";
    p = coltype.find( "Of"); // the first Of
    if( p != string::npos ) {
      string n = coltype.substr( p+2, string::npos);
      t.name = coltype.substr( 0, p);
      if( t.name[0] == 'H' ) {
	t.templateTypeSpec = "H"; // HandleType
	t.name = t.name.substr(1, string::npos);
      } else {
	t.templateTypeSpec = "V"; // ValueType
      }
      p = n.find( "Of");       // can we find a second "Of"?
      if( p != string::npos) {
	a.inClass = "Collection";
	a.templateClass = true;
	a.templateTypeSpec = "V";
	a.name = n.substr( 0,p); // no H types
	FType b;
	b.name = n.substr( p+2,string::npos);
	translateStandardTypes( b.name, b); // we assume a standard type
	a.typeArgs.push_back( b);
      } else {
	// normal argument
	a.name = n;
	if( a.inClass == "Standard")
	  translateStandardTypes( a.name, a);	
      }
      t.typeArgs.push_back( a);	
    }
    return true;  
  }
  return false;
}

string trTypeLog( const FType& t) {
  stringstream l;
  if( !t.inClass.empty()) l << t.inClass << "::";
  l << t.name;
  string v;
  if( t.pointer) v = "&";
  if( t.builtin) { if( v.empty()) v = "b"; else v+= ",b"; }
  if( t.handle)  { if( v.empty()) v = "h"; else v+= ",h"; }
  if( t.templateClass) { if( v.empty()) v = "t"; else v+= ",t"; }
  if( !v.empty()) l << "(" << v <<")"; 
  if( !t.typeArgs.empty()) {
    l << "[";
    for( auto i = t.typeArgs.begin(); i != t.typeArgs.end(); ++i) {
      if( i != t.typeArgs.begin()) l << ",";
      l << trTypeLog( *i);
    }
    l << "]";
  }
  l << "{" << t.log << "}";
  return l.str();
}


FType trType( const QualType& qt, set<string>& log) {
  const FType t = trType( qt);
  log.insert( trTypeLog( t) + " <- " + qt.getAsString() );
  return t;
}

struct DefStackItem {
  DefStackItem( const DeclContext* dc) : decl( dc) {}
  const DeclContext*   decl;
  stringstream   def;
  stringstream   eofTypeDef;
};

struct TranslationUnit {
  TranslationUnit(): defs( deque<shared_ptr<DefStackItem>>( 1, shared_ptr<DefStackItem>(new DefStackItem( 0)))),
		     def( &defs.top()->def),
		     eofTypeDef( &defs.top()->eofTypeDef) {}
  string filePath;
  string fileName;
  string headerName;
  // dependent classes
  set<string> dpClasses;
  // dependent in class types 
  set<string> dpTypes;
  // provided (in class) types 
  set<string> prTypes;
  int currentIndent;
  set<string> trTypeLog;
private:
  stack<shared_ptr<DefStackItem>> defs;
public:
  stringstream  headerDefs;
  stringstream* def;
  stringstream* eofTypeDef;
  void setDeclContext( const DeclContext* dc) {
    auto t = defs.top();
    if( t->decl == 0) {
      //cout << "setDeclContext( )" << endl;
      t->decl=dc;
    } else if( t->decl == dc ) {
      //cout << "setDeclContext( == )" << endl;
    } else if( dc != 0 && t->decl == dc->getParent()) {
      // push
      //cout << "setDeclContext( == parent)" << endl;
      defs.push( shared_ptr<DefStackItem>( new DefStackItem( dc)));
      auto t_ = defs.top();
      def = &(t_->def);
      eofTypeDef = &(t_->eofTypeDef);
      ++currentIndent;
    } else {
      // pop
      //cout << "setDeclContext( != parent), defs.size=" << defs.size() << endl;
      while( defs.size() > 0 && defs.top()->decl != dc) {
	auto t = defs.top();
	t->def << t->eofTypeDef.str();
	if( defs.size() > 1) {
	  defs.pop();
	  defs.top()->def << t->def.str();
	  --currentIndent;
	} else {
	  break;
	}
      }
      def = &(defs.top()->def);
      eofTypeDef = &(defs.top()->eofTypeDef);
    }
  }
};

string indent( const int& n) { return string( (n < 0 ? 0 : ( n > 10 ? 10 : n ) ) * 2,' '); }

bool containsAtLeastOneOf(const set<string>& u,const set<string>& v) {
  auto i = u.begin();
  while( i != u.end() && v.find( *i) == v.end()) ++i;
  return i != u.end();
}
  

class ClassContext {
public:
  const string& inClass;
  const set<string>& openClasses;
  string ftype;
  string ctype;
  bool handle;
  string classHierarchyTypeVar; 
  ClassContext( const string& inClass_,
		const set<string>& openClasses_,
		bool handle_,
		const string& classHierarchyTypeVar_) :
    inClass( inClass_), openClasses( openClasses_),
    handle(handle_), classHierarchyTypeVar( classHierarchyTypeVar_) {}
};

string inClassType( const FType& ft, const ClassContext& ct, const bool& isRetType, TranslationUnit& tu) {
  string name;
  if( isRetType || ct.classHierarchyTypeVar.empty() || ft.name != ct.ftype) 
    name = ft.name;
  else
    name = ct.classHierarchyTypeVar;
  
  if( !(ft.builtin || ft.inClass.empty())) {
    if ( ft.inClass == ct.inClass ) {
      if( tu.prTypes.find( ft.name) == tu.prTypes.end())
	tu.dpTypes.insert( ft.name);
    } else {
      tu.dpClasses.insert( ft.inClass);
      if( ct.openClasses.find( ft.inClass) == ct.openClasses.end())
	name = ft.inClass + "::" + name;
    }
  }
  if( ft.pointer) name = "&" + name;
  if( !ft.typeArgs.empty()) {
    name += "[";
    for( auto i=ft.typeArgs.begin(); i != ft.typeArgs.end(); ++i) {
      if( i != ft.typeArgs.begin()) name += ",";
      name += inClassType( *i, ct, isRetType, tu);
    }
    name += "]";
  }
  if( ft.templateClass && !ft.templateTypeSpec.empty()) {
    name += "::" + ft.templateTypeSpec;
  }
  return name;
}

list<string> args
( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu )
{
  list<string> a;
  for(unsigned int i=0; i < m->getNumParams(); i++) {
    a.push_back( inClassType( trType ( m->parameters()[i]->getType(), tu.trTypeLog),
			      ct, false, tu));
  }
  return a;
}

void printArgs( const list<string>& args, stringstream& s) {
  if( args.empty()) s << "1";
  for( auto a = args.begin(); a != args.end(); ++a) {
    if( a != args.begin()) s << " * ";
    s << *a;
  }
}

list<pair<string,string>> namedArgs
( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu )
{
  list<pair<string,string>> a;
  for(unsigned int i=0; i < m->getNumParams(); i++) {
    string n = m->parameters()[i]->getQualifiedNameAsString();
    string t = inClassType( trType ( m->parameters()[i]->getType(), tu.trTypeLog), ct, false, tu);
    if( n == t) n = n + string("_");
    a.push_back( pair<string,string>( n,t));				     
  }
  return a;
}

bool setType( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  tu.prTypes.insert( ct.ftype);
  auto& d = *tu.def;
  //  if( ! rd->isAbstract()) {
    d << indent(tu.currentIndent) << "type " << ct.ftype << " = \"";
    if( ct.handle)
      d << "opencascade::handle<" << ct.ctype << ">";
    else
      d << ct.ctype;
    d << "\" requires " << tu.headerName << ";" << endl;
    //}
  if( !ct.classHierarchyTypeVar.empty()) {
    // we create a felix class
    d << indent(tu.currentIndent) << "class " << ct.ftype
      << "_[" << ct.classHierarchyTypeVar << "] {" << endl;
    ++tu.currentIndent;
    list<string> bases;
    for (auto b = rd->bases_begin(); b!=rd->bases_end();++b) {
      FType ft = trType(b->getType());
      if( ct.inClass == ft.inClass) tu.dpTypes.insert( ft.name);
      const string ft_ = inClassType( ft, ct, false,tu);
      bases.push_back( ft_);
      d << indent(tu.currentIndent)
	<< "inherit " << ft_ << "_[" << ct.classHierarchyTypeVar << "];" << endl;
    }
    // here come the member defs
    // and after them
    int ind=tu.currentIndent-1;
    auto& eofTypeDef = *tu.eofTypeDef;
    eofTypeDef << indent(ind) << "}" << endl;
    if( ! rd->isAbstract()) {
      eofTypeDef << indent(ind) << "instance " << ct.ftype
		 << "_[" << ct.ftype << "] {}" << endl;
      eofTypeDef << indent(ind) << "inherit " << ct.ftype
		 << "_[" << ct.ftype << "];" << endl;
    }
    for(auto b = bases.begin(); b != bases.end(); ++b) {
      eofTypeDef << indent(ind)
		 << "supertype " << *b << " (x: "
		 << ct.ftype << ") => C_hack::cast[" << *b << "] x;" << endl;
    }
  } 
  return true;
}

static std::map<std::string,std::list<std::string>> tcolHFiles;  // mapping Container->files 

bool setTypeTemplateVH( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  if( tu.currentIndent > 1) return true;
  tu.prTypes.insert( ct.ftype);
  auto& d = *tu.def;
  if( !ct.classHierarchyTypeVar.empty()) {
    // we create a felix class
    d << indent(tu.currentIndent)
      << "class " << ct.ftype << "[" << ct.classHierarchyTypeVar << "] {" << endl;
    ++tu.currentIndent;
    //d << indent( tu.currentIndent)
    //  << "inherit Standard::ClassVH;" << endl; 
    d << indent( tu.currentIndent)
      << "type V = \"" << ct.ctype << "<?1>\" "
      << "requires " << tu.headerName << ";" << endl
      << indent( tu.currentIndent)
      << "ctor[A] V (a:A) => Standard::Ctor[V,A](a);" << endl		       
      << indent( tu.currentIndent)
      << "virtual type H;" << endl
      << indent( tu.currentIndent)
      << "virtual fun createH[A]: A -> H;" << endl;

    // here come the member defs
    // and after them
    int ind=tu.currentIndent-1;
    auto& eofTypeDef = *tu.eofTypeDef;
    eofTypeDef << indent(ind) << "}" << endl;
    auto i = tcolHFiles.find( ct.ftype);
    if( i != tcolHFiles.end()) {
      auto l = i->second;
      for( auto j = l.begin(); j != l.end(); ++j) {
	// set instances
	// we construct the information from the names of files
	FType t; string coltype;
	trTColName( *j,t, coltype);
	tu.headerDefs
	  << "header " << *j << "_hxx = '#include \"" << *j << ".hxx\"';" << endl;
	eofTypeDef
	  << indent(ind)
	  << "instance " << ct.ftype
	  << "[" << inClassType( t.typeArgs.front(), ct, false, tu) << "] {" << endl
	  << indent(ind+1) 
	  << "type " << coltype << " = \"" << coltype << "\" requires " << *j << "_hxx;"
	  << endl << indent(ind+1)
	  << "instance type H = handle[" << coltype << "];" << endl
	  << indent(ind+1)
	  << "fun createH[A] (a:A) => createHandle[" << coltype << ",A](a);" << endl
	  << indent( ind) << "}" << endl;
      }
    }
  } 
  return true;
}

bool checkForCollectionInstance( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  // we check if the type is a handle<Class(Transient,CollectionContainer)>
  return true;
}


bool trCtor( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {    
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    auto& d = *tu.def;
    d << indent(tu.currentIndent) << "ctor " << ct.ftype << ": ";
    auto args_ = args( m, ct, tu); 
    printArgs( args_, d);
    d << " = \"";
    if( ct.handle)
      d << "opencascade::handle<" << ct.ctype << ">(new ";
    d << ct.ctype << "("; if( !args_.empty()) d << "$a"; d << ")";
    if( ct.handle)
      d << ")";
    d << "\";" << endl;
    return true;
  } else return false;
}

bool trMemberFct( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if ( !isa<CXXConstructorDecl>(m) && !isa<CXXDestructorDecl>(m) &&
       ! m->isOverloadedOperator() &&
       ! (m->isVirtual() && !m->isPure())
       ) {
    auto& d = *tu.def;
    string name = m->getNameAsString();
    if( name == "get_type_descriptor" ||
	name == "get_type_name") return true;
    const QualType rt = m->getReturnType();
    string frt;
    if ( !rt->isVoidType() )
      frt = inClassType( trType( rt, tu.trTypeLog), ct, true, tu);
    d << indent(tu.currentIndent);
    if ( frt.empty() ) d << "proc ";
    //else if (frt == name) d << "ctor ";
    else d << "fun ";
    std::list<string> args_ = args( m, ct, tu);
    //if( tu.dpTypes.find( name) != tu.dpTypes.end()) {
    // we rename the member name
    string fname = name;
    fname[0] = tolower(fname[0]);
      //}
    d << fname << ": ";

    // if not a static method then first arg is of type ftype
    if( !m->isStatic()) {
      if( ct.classHierarchyTypeVar.empty())
	args_.push_front( ct.ftype);
      else
	args_.push_front( ct.classHierarchyTypeVar);
    }
    printArgs( args_, d);
    if ( !rt->isVoidType()/* && frt != name*/ ) // print return type
      d << " -> " << frt;
    d << " = \""; 
    if( m->isStatic()) {
      d << name << "("; if( !args_.empty()) d << "$a";
      d << ")\";" << endl;
    }
    else {
      d << "$1";
      if( ct.handle) d << "->"; else d << ".";
      d << name << "("; if( args_.size()>1) d << "$b";
      d << ")\";" << endl;
    }
    return true;
  } else return false;
}

string camelToSpaces( string s) {
  string r;
  string::size_type p = s.find_first_of( '_');
  if( p != string::npos ) s = s.substr(p+1,string::npos);
  for( int i = 0; i< s.size(); ++i) {
    auto c = s[i];
    if( i > 0 && isupper( c)) r.push_back( ' ');
    r.push_back( c);
  }
  return r;
}


bool setEnum( const EnumDecl* ed, const ClassContext& ct, TranslationUnit& tu) {
  tu.prTypes.insert( ct.ftype);
  auto& d = *tu.def;
  auto ind = tu.currentIndent;
  d << indent(ind) << "type " << ct.ftype << " = \"" << ct.ctype << "\" "
    << "requires " << tu.headerName << ";" << endl;
  for( auto i = ed->enumerator_begin(); i != ed->enumerator_end(); ++i) {
    string cs = i->getNameAsString(); string fs = cs;
    string::size_type p = fs.find_first_of( '_');
    if( p != string::npos ) fs = fs.substr(p+1,string::npos);
    d << indent(ind) << "const " << fs << ": " << ct.ftype << " = \"" << cs << "\";" << endl;
  }
  d << indent( ind) << "fun == : " << ct.ftype << " * " << ct.ftype << " -> bool = \"$1==$2\";" << endl;
  d << indent( ind)
    << "instance Str[" << ct.ftype << "] {" << endl;
  ++ind;
  d << indent( ind)
    << "fun str: " << ct.ftype << " -> string =" << endl ;
  ++ind;
  for( auto i = ed->enumerator_begin(); i != ed->enumerator_end(); ++i) {
    //if( i != ed->enumerator_begin()) d << "," << endl << indent(ind);
    string fs = i->getNameAsString(); 
    string::size_type p = fs.find_first_of( '_');
    if( p != string::npos ) fs = fs.substr(p+1,string::npos);
    d << indent( ind)
      << "| $(" << fs<< ") => \"" << camelToSpaces(fs) << "\"" << endl;
  }
  d << indent( ind) << ";" << endl;
  --ind; --ind;
  d << indent( ind) << "}" << endl;
  return true;
}


struct ClassTranslation {
  string targetClass;
  string package;
  set<string> openClasses;
  set<string> includes;
  TypeImplementation typeImpl;
  string classHierarchyTypeVar;
  function<bool( const CXXRecordDecl*,const ClassContext&, TranslationUnit&)> typeTr;
  list<function<bool( const CXXMethodDecl*, const ClassContext&, TranslationUnit&)> > mfTr;
  set<string> includeFiles;
  set<string> excludeFiles;
};

class ClassWriter : public MatchFinder::MatchCallback {
private:
  list<shared_ptr<TranslationUnit>> tus;
  shared_ptr<TranslationUnit> tu;
  ClassTranslation ctr;
  bool first = true;
  
  ClassContext classContext( const string& name) {
    ClassContext ct( ctr.targetClass, ctr.openClasses, ctr.typeImpl==OccHandle,ctr.classHierarchyTypeVar);
    ct.ctype = name;
    string::size_type p = ct.ctype.find_first_of( '_');
    if( p != string::npos ) {
      const string inClass = ct.ctype.substr( 0, p);
      if( ct.inClass != inClass ) {
	//cout << "Error, found definition for " << inClass << ", but required class is " << ct.inClass
	//     << "! for type " << ct.ctype << " in file " << tu->fileName << endl;
      }
      ct.ftype = ct.ctype.substr( p+1, string::npos);
    } else {
      //cout << "Warning, found unclassified type " << ct.ctype << " in file " << tu->fileName << endl; 
      ct.ftype = ct.ctype;
    }
    return ct;
  }
public :
  ClassWriter ( const ClassTranslation& ctr_) :ctr( ctr_) {}
  virtual void onStartOfTranslationUnit() {
    //std::cout << "startOfTU" << std::endl;
    tu = shared_ptr<TranslationUnit>( new TranslationUnit());
  }

  virtual void run(const MatchFinder::MatchResult &Result) {
    if( tu->filePath.empty()) {
      clang::SourceManager* sm = Result.SourceManager;
      auto fp = sm->getNonBuiltinFilenameForID( sm->getMainFileID());
      if( fp.hasValue()) {
	tu->filePath = fp.getValue().str();
	tu->fileName = sys::path::filename( tu->filePath).str();
	tu->headerName = tu->fileName; replace( tu->headerName.begin(), tu->headerName.end(), '.', '_');
	tu->currentIndent = 1;
	cout << tu->fileName << endl;
      }      
    }
    
    const CXXRecordDecl *rd = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("classDecl");
    const EnumDecl *ed = Result.Nodes.getNodeAs<clang::EnumDecl>("enumDecl");
    if ( rd && rd->isCompleteDefinition() ) {
      tu->setDeclContext( rd->getDeclContext());
      //if( first )
      //	rd->dumpLookups();
      //first = false;
      ClassContext ct = classContext( rd->getDeclName().getAsString());
      //std::cout << "run" << std::endl;
      
      if( ctr.typeTr( rd, ct, *tu)) {
	// methods
	for( auto mi = rd->method_begin(); mi != rd->method_end(); ++mi) {
	  const CXXMethodDecl* m = mi.operator*();
	  for( auto tr = ctr.mfTr.begin(); tr != ctr.mfTr.end(); ++tr) {
	    if( (*tr)( m, ct, *tu)) break;
	  }
	}
	//tu->def << tu->eofTypeDef.str();
      }
    } else if ( ed && ed->isCompleteDefinition() ) {
      tu->setDeclContext( ed->getDeclContext());
      ClassContext ct = classContext( ed->getNameAsString());
      //tu->currentIndent = 1;
      setEnum( ed, ct, *tu);
    }
  }
  virtual void onEndOfTranslationUnit() {
    //std::cout << "endOfTU:" /*<< std::string( outputFilePath.str()) */ << std::endl;
    //cout << tu->def.str() << endl;
    //cout << "---- trType log ----" << endl;
    //for( auto i = tu->trTypeLog.begin(); i != tu->trTypeLog.end(); ++i) {
    //  cout << *i << endl;     
    //}
    tu->setDeclContext( 0); // pop  up
    for( auto i = tu->dpClasses.begin(); i != tu->dpClasses.end(); ++i) {
      ctr.includes.insert( *i);
    }
    auto i = tus.begin();
    for( ; i != tus.end(); ++i) {
      if( containsAtLeastOneOf( tu->prTypes, (*i)->dpTypes)) {
	tus.insert( i, tu); break;
      }
    }
    if( i==tus.end()) tus.push_back( tu);
  }

  void writeFile() {
    llvm::SmallString<256> outputFilePath;
    outputFilePath.append( realOutputDir);
    sys::path::append( outputFilePath, ctr.targetClass);
    outputFilePath.append( ".flx");
    cout << "output file:" << string( outputFilePath.str()) << endl;        
    // Open the output file
    ofstream os( outputFilePath.c_str());
    set<string> typeLog;
    set<string> prTypes;
    set<string> dpTypes;
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      const TranslationUnit& tu = *(*i);
      for( auto j = tu.trTypeLog.begin(); j != tu.trTypeLog.end(); ++j) {
	typeLog.insert( *j);
      }
      os << "// --- " << tu.fileName << " ---" << endl;
      os << "// provides: ";
      for( auto j = tu.prTypes.begin(); j != tu.prTypes.end(); ++j) {
	prTypes.insert( *j);
	if( j != tu.prTypes.begin()) os << ", ";
	os << *j;
      }
      os << endl;
      os << "// requires: ";
      for( auto j = tu.dpTypes.begin(); j != tu.dpTypes.end(); ++j) {
	dpTypes.insert( *j);
	if( j != tu.dpTypes.begin()) os << ", ";
	os << *j;
      }
      os << endl;
    }
    // we remove all known (provided) types from the dependend types,
    // the rest we just define
    for( auto i = prTypes.begin(); i != prTypes.end(); ++i) {
      dpTypes.erase( *i);
    }
    os << "// ---------------------------------------------------------" << endl;
    os << "// type translations:" << endl;
    for( auto i = typeLog.begin(); i != typeLog.end(); ++i) {
      os << "// " << *i << endl;
    }
    os << "// ---------------------------------------------------------" << endl;
    for( auto i = ctr.includes.begin(); i != ctr.includes.end(); ++i) {
      os << "include \"./" << *i << "\";" << endl;
    }
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      if( !(*i)->headerName.empty())
	os << "header " << (*i)->headerName << " = '#include \"" << (*i)->fileName << "\"';" << endl;
      os << (*i)->headerDefs.str();
    }
    for( auto i = dpTypes.begin(); i != dpTypes.end(); ++i) {
      // we dont regard renamings here!
      string hn = ctr.targetClass + "_" + *i;
      os << "header " << hn << "_hxx = '#include \"" << hn << ".hxx\"';" << endl;
    }
    os << "class " << ctr.targetClass << " {" << endl;
    os << "  requires package \"" << ctr.package << "\";" << endl;
    for( auto i = ctr.openClasses.begin(); i != ctr.openClasses.end(); ++i) {
      os << "  open " << *i << ";" << endl;
    }
    for( auto i = dpTypes.begin(); i != dpTypes.end(); ++i) {
      // we dont regard renamings here!
      string hn = ctr.targetClass + "_" + *i;
      os << "  type " << *i << " = \"" << hn << "\" requires " << hn << "_hxx;" << endl;
    }
    
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      os << "// --- " << (*i)->fileName << " ---" << endl;
      os << (*i)->def->str();
    }
    os << "};" << endl;
    os.close();
  }
};

static string makerRetType;

bool setTypeMaker( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  makerRetType.clear();
  string makerErrorType;
  string n = ct.ftype;
  bool error = false;
  bool gcClass = false;
  if(n.find( "Make") == 0) n = ct.ftype.substr( 4);
  else return false;
  for( auto mi = rd->method_begin(); mi != rd->method_end(); ++mi) {
    const CXXMethodDecl* m = mi.operator*();
    const CXXConversionDecl* cd = dynamic_cast<CXXConversionDecl*>(mi.operator*());
    if( cd != 0) {
      FType ft = trType( cd->getConversionType(), tu.trTypeLog);
      makerRetType = ft.name;
    } else if( m->getNameAsString() == "Error" ) {
      FType ft = trType( m->getReturnType(), tu.trTypeLog);
      if( ct.inClass == ft.inClass)
	tu.dpTypes.insert( ft.name);
      makerErrorType = ft.name;
      error = true;
    } else if( m->getNameAsString() == "Value" ) {
      gcClass = true;
    }
  }
  setType( rd, ct, tu);
  bool withoutError = ( gcClass && rd->bases_begin() == rd->bases_end())
    || !error; // no base class
  *tu.def << indent(tu.currentIndent) << "#init";
  if( withoutError) *tu.def << "WE";
  *tu.def << "[" << ct.ftype << "," << makerRetType << "];" << endl;
  if( error) {
    auto& eofTypeDef = *tu.eofTypeDef;
    eofTypeDef << indent( tu.currentIndent)
	       << "instance Maker::Interface[" << ct.ftype << "] {" << endl
	       << indent( tu.currentIndent+1)
	       << "instance type E = " << makerErrorType << ";" << endl
	       << indent( tu.currentIndent+1)
	       << "fun IsDone[I] : I -> bool = \"$1->IsDone()\";" << endl
	       << indent( tu.currentIndent+1)      
	       << "fun Error[I] : I ->  E = \"$1->Error()\";" << endl
    	       << indent( tu.currentIndent+1)
	       << "fun Value[I,O] : I -> O = \"(?2) *$1\";" << endl
  	       << indent( tu.currentIndent)
	       << "}" << endl;
  }
  return true;
}

bool trCtorMaker( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {    
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    auto& d = *tu.def;
    string n = ct.ftype;
    if( ct.ftype.find( "Make") == 0) n = ct.ftype.substr( 4);
    n[0]=tolower(n[0]);
    d << indent(tu.currentIndent) << "fun " << n << " ";
    auto args_ = namedArgs( m, ct, tu);
    d << "(";
    for( auto a = args_.begin(); a != args_.end(); ++a) {
      if( a != args_.begin()) d << ", ";
      d << a->first << ":" << a->second;
    }
    d << ") ";
    d << "=> maker[" << ct.ftype << "," << makerRetType << "](";
    for( auto a = args_.begin(); a != args_.end(); ++a) {
      if( a != args_.begin()) d << ",";
      d << a->first;
    }
    d << ");" << endl;
    return true;
  } else return false;
}



static list<ClassTranslation> classTranslations =
  {
    {"Collection","TKMath",{"Standard","gp"},{},TemplateClassVH,"T"
     ,setTypeTemplateVH,{},{"Array1","Array2","Sequence","List"},{}}
    ,{"gp","TKMath",{"Standard"},{},Value,""
      ,setType,{trCtor,trMemberFct},{},{"VectorWithNullMagnitude"}}
    ,{"GeomAbs", "TKG3d",{},{},Value,""
      ,setType,{},{},{}}
    ,{"Geom", "TKG3d",{"gp","Collection"},{"Standard"},OccHandle,"T"
      ,setType,{trCtor,trMemberFct},{},
      {"UndefinedDerivative","UndefinedValue","SequenceOfBSplineSurface","HSequenceOfBSplineSurface"}}
    ,{"Geom2d", "TKG2d",{"gp","Collection"},{"Standard"},OccHandle,"T"
      ,setType,{trCtor,trMemberFct},{},
      {"UndefinedDerivative","UndefinedValue"}}
    ,{"GC", "TKGeomBase",{"Standard","Geom","gp","GC_Maker"},{"GC_Maker","Geom"},Other,""
      ,setTypeMaker,{trCtorMaker},{},{"Root"}}
    ,{"TopAbs", "TKBRep",{},{},Value,"",setType,{},{},{}}
    ,{"TopLoc", "TKBRep",{},{},Value,"",setType,{},{},{}}
    ,{"TopoDS", "TKBRep",{"gp","Collection"},{"Standard"},Value,""
      ,setType,{trCtor,trMemberFct},
      {"Shape","Shell","Solid","Iterator","Compound","CompSolid","Edge",
       "Face","Vertex","Wire"},{}}
    ,{"BRepBuilderAPI", "TKTopAlgo",
      {"Standard","Geom","gp","TopoDS","BRepBuilderAPI_Maker"},{"BRepBuilderAPI_Maker","Geom"},Other,""
      ,setTypeMaker,{trCtorMaker},
      { "MakeEdge2d","MakeEdge","MakeFace","MakePolygon","MakeShape","MakeShell","MakeSolid","MakeVertex","MakeWire",
	"EdgeError","WireError","FaceError", "PipeError","ShellError"},
      {/*"Sewing","VertexInspector"*/}}
    
  };

bool checkFor( const string& cl, const TypeImplementation& ti) {
  for( auto ctr = classTranslations.begin(); ctr != classTranslations.end(); ++ctr) {
    if( cl != ctr->targetClass) continue;
    return ctr->typeImpl == ti;
  }
  return false;
}


int main(int argc, const char **argv) {
  llvm::cl::ParseCommandLineOptions(argc, argv);
  std::error_code ec;
  ec = sys::fs::real_path( occDir, realOccDir, true);
  if( ec ) {
    std::cout << "occ dir not found:" << occDir << ", " << ec.message() << std::endl;
    exit(1);
  }
  llvm::SmallString<256> occIncDir;
  occIncDir.append( realOccDir);
  sys::path::append( occIncDir, "include");
  std::stringstream iFlag;
  iFlag << "-I" << std::string( occIncDir.str());
  std::string flags[] = { iFlag.str(), "-std=c++0x" };
  FixedCompilationDatabase cdb( realOccDir.str(), flags);
  std::map<std::string,std::list<std::string>> groupedFiles;
  //  std::map<std::string,std::list<std::string>> tcolHFiles;  // mapping Container->files 
  std::error_code EC;
  Regex modre("(^[A-Za-z0-9]+)[_]*([A-Za-z0-9]*)\\.hxx");
  Regex tcolre("^TCol[A-Za-z]+_H([A-Za-z12]+)(Of[A-Za-z0-9]+)+\\.hxx");
  for( sys::fs::directory_iterator i( occIncDir, EC);
       i != sys::fs::directory_iterator(); i.increment( EC)) {
    if (EC) {
      llvm::errs() << "while traverse '" << occIncDir << "': "
		   << EC.message() << '\n';
      exit(1);
    }
    SmallVector<StringRef,3> m;
    if( modre.match( sys::path::filename( i->path()),&m)) {
      auto m_ = m.begin(); m_++; 
      if( m_ != m.end()) {
	groupedFiles[ cToFclass(m_->str())].push_back(i->path());
      }
    }
    if( tcolre.match( sys::path::filename( i->path()),&m)) {
      auto m_ = m.begin(); m_++;
      if( m_ != m.end()) {
	string n = m_->str();
	string::size_type p = n.find( "Of"); // filter out Of...
	if( p != string::npos ) n = n.substr( 0, p);
	string f = sys::path::filename(i->path()).str();
	f = f.substr(0,f.size()-4); // chop of ".hxx"
	tcolHFiles[ n].push_back( f);
      }   
    }
  }
  //  for( auto i = groupedFiles.begin(); i != groupedFiles.end(); ++i) {
  //  std::cout << i->first << ":" << i->second.size() << std::endl;
  // }
  // for( auto i = tcolHFiles.begin(); i != tcolHFiles.end(); ++i) {
  //   std::cout << i->first << ":" << std::endl;
  //   for( auto j = i->second.begin(); j != i->second.end(); ++j)
  //     std::cout << "  " << *j << std::endl;
  // }
  //exit(1);
  //  std::string files[] = { "/home/robert/prog/apps/opencascade-7.5.0-install/include/gp_Pnt.hxx"};
  {
    char cwd[256]; getcwd(cwd, 256); 
    sys::fs::set_current_path( cwd);
    std::cout << "cwd:" << cwd << std::endl;
    
    ec = sys::fs::real_path( outputDir, realOutputDir, true);
    if( ec ) {
      std::cout << "could not find output dir:" << outputDir
		<< ", " << ec.message() << std::endl;
      exit(1);
    } 
  }
     
  for( auto ctr = classTranslations.begin(); ctr != classTranslations.end(); ++ctr) {
    if( !TargetClass.empty() && TargetClass != ctr->targetClass) continue;
    auto& files_ = groupedFiles[ctr->targetClass];
    std::vector<std::string> files;//( files_.size()); int j=0;
    for( auto i = files_.begin(); i != files_.end(); ++i) {
      string::size_type p = i->find_last_of( '_');
      string::size_type q = i->find_last_of( '.');
      string s;
      if( p != string::npos && q != string::npos ) {
	s = i->substr( p+1, q-p-1);
	//cout << *i << " : [" << s << "]" << endl;
      }
      if( (!ctr->includeFiles.empty() && ctr->includeFiles.find(s)!=ctr->includeFiles.end()) ||
	  (!ctr->excludeFiles.empty() && ctr->excludeFiles.find(s)==ctr->excludeFiles.end()) ||
	  (ctr->includeFiles.empty() && ctr->excludeFiles.empty())) {
	files.push_back(*i);//[j++] = *i;
      }
    }
    ClangTool Tool(cdb, files); 
    ClassWriter Writer(*ctr);
    MatchFinder Finder;
    Finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, ClassMatcher), &Writer);
    Finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource, EnumMatcher), &Writer);
    int result = Tool.run(newFrontendActionFactory( &Finder).get());
    if( result != 0) cout << "Error during Tool run" << endl;
    Writer.writeFile();
  }
}
