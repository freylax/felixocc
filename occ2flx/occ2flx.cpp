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
  FType(): builtin(false), pointer(false), handle( false) {}
  string name;
  string inClass;
  bool   builtin;
  bool   pointer;
  bool   handle;
  list<FType> typeArgs;
  string log;
};


void setClassAndName( const string& n, FType& t) {
  string::size_type p = n.find_first_of( '_');
  if( p != string::npos ) {
    t.inClass = n.substr( 0, p);
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
  Other
};

bool checkFor( const string& cl, const TypeImplementation& ti);

bool trTemplate( const QualType& qt, FType& t);

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
    if( t.inClass == "TColStd" ) {
      t.log += "TColStd,";
      bool p = t.pointer; string l = t.log;
      t = trType( qt->getAs<TypedefType>()->desugar());
      t.pointer = p; t.log = l + t.log;
    } else if( t.inClass == "Standard") {
      if( t.name == "Real" )
	{ t.name = "double"; t.builtin = true; t.inClass.clear(); }
      else if( t.name == "Integer" )
	{ t.name = "int"; t.builtin = true; t.inClass.clear(); }
      else if( t.name == "Boolean" )
	{ t.name = "bool"; t.builtin = true; t.inClass.clear(); }
      //   else if( n == "Standard_OStream" )
      //     { t.name = "ostream"; t.inClass = "std"; return t; }
      //   else if( n == "Standard_SStream" )
      //     { t.name = "stringstream"; t.inClass = "std"; return t; }
    
      //   //const TypedefType* tt = 
      //   //qt = tt->desugar();
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
      setClassAndName( crd->getNameAsString(), t);
    }
  } else {
    t.log += string("cl=") + string(qt->getTypeClassName());
    //qt->dump();
    t.name = qt.getAsString();
  }
  return t;
}

bool trTemplate( const QualType& qt, FType& t) {
  if( auto st = qt->getAs<TemplateSpecializationType>()) {
    t.log += "ts,";
    string tn = dumpToStr( st->getTemplateName());
    if( tn == "handle" ) {
      t.log += "hd,";
      FType p = trType(st->getArg(0).getAsType());
      t.name = p.name;
      t.inClass = p.inClass;
      t.handle = true;
      if( !checkFor( t.inClass, OccHandle)) {
	cout << endl << "warning: " << t.inClass
	     << "is not implemented as OccHandle but was requested as such!"
	     << endl;
      }
    } else {
      // no handle
      setClassAndName( tn, t);
      t.log += "ta,";
      const auto n = st->getNumArgs();
      for( unsigned int i = 0; i<n; ++i) {
	t.typeArgs.push_back( trType(st->getArg(i).getAsType()));
      }
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

struct TranslationUnit {
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
  stringstream def;
  stringstream eofTypeDef;
  set<string> trTypeLog;
};

string indent( const int& n) { return string(2*n,' '); }

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
    a.push_back( pair<string,string>(m->parameters()[i]->getQualifiedNameAsString(),
				     inClassType( trType ( m->parameters()[i]->getType(), tu.trTypeLog),
						  ct, false, tu)));
  }
  return a;
}


bool setType( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  tu.prTypes.insert( ct.ftype);
  tu.def << indent(tu.currentIndent) << "type " << ct.ftype << " = \"";
  if( ct.handle)
    tu.def << "opencascade::handle<" << ct.ctype << ">";
  else
    tu.def << ct.ctype;
  tu.def << "\" requires " << tu.headerName << ";" << endl;
  if( !ct.classHierarchyTypeVar.empty()) {
    // we create a felix class
    tu.def << indent(tu.currentIndent) << "class " << ct.ftype
	   << "_[" << ct.classHierarchyTypeVar << "] {" << endl;
    ++tu.currentIndent;
    for (auto b = rd->bases_begin(); b!=rd->bases_end();++b) {
      FType ft = trType(b->getType());
      tu.def << indent(tu.currentIndent) << "inherit " << ft.name << "_[" << ct.classHierarchyTypeVar << "];" << endl;
      tu.dpTypes.insert( ft.name);
    }
    // here come the member defs
    // and after them
    int ind=tu.currentIndent-1;
    tu.eofTypeDef << indent(ind) << "}" << endl;
    tu.eofTypeDef << indent(ind) << "instance " << ct.ftype
		  << "_[" << ct.ftype << "] {}" << endl;
    tu.eofTypeDef << indent(ind) << "inherit " << ct.ftype
		  << "_[" << ct.ftype << "];" << endl;
  } 
  return true;
}

bool trCtor( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {    
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    auto& d = tu.def;
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
       ! m->isOverloadedOperator()) {
    auto& d = tu.def;
    const string name = m->getNameAsString(); 
    const QualType rt = m->getReturnType();
    string frt;
    if ( !rt->isVoidType() )
      frt = inClassType( trType( rt, tu.trTypeLog), ct, true, tu);
    d << indent(tu.currentIndent);
    if ( frt.empty() )
      d << "proc ";
    else if (frt == name)
      d << "ctor ";
    else
      d << "fun ";
    d << name << ": ";
    std::list<string> args_ = args( m, ct, tu);
    // if not a static method then first arg is of type ftype
    if( !m->isStatic()) {
      if( ct.classHierarchyTypeVar.empty())
	args_.push_front( ct.ftype);
      else
	args_.push_front( ct.classHierarchyTypeVar);
    }
    printArgs( args_, d);
    if ( !rt->isVoidType() && frt != name ) // print return type
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


struct ClassTranslation {
  string targetClass;
  string package;
  set<string> openClasses;
  set<string> includes;
  TypeImplementation typeImpl;
  string classHierarchyTypeVar;
  function<bool( const CXXRecordDecl*,const ClassContext&, TranslationUnit&)> typeTr;
  list<function<bool( const CXXMethodDecl*, const ClassContext&, TranslationUnit&)> > mfTr;
};

class ClassWriter : public MatchFinder::MatchCallback {
private:
  list<shared_ptr<TranslationUnit>> tus;
  shared_ptr<TranslationUnit> tu;
  ClassTranslation ctr;

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
	cout << tu->fileName << endl;
      }      
    }
    const CXXRecordDecl *rd = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("classDecl");
    const EnumDecl *ed = Result.Nodes.getNodeAs<clang::EnumDecl>("enumDecl");
    if ( rd && rd->isCompleteDefinition() ) {
      ClassContext ct = classContext( rd->getDeclName().getAsString());
      //std::cout << "run" << std::endl;
      tu->currentIndent = 1;
      if( ctr.typeTr( rd, ct, *tu)) {
	// methods
	for( auto mi = rd->method_begin(); mi != rd->method_end(); ++mi) {
	  const CXXMethodDecl* m = mi.operator*();
	  for( auto tr = ctr.mfTr.begin(); tr != ctr.mfTr.end(); ++tr) {
	    if( (*tr)( m, ct, *tu)) break;
	  }
	}
	tu->def << tu->eofTypeDef.str();
      }
    } else if ( ed && ed->isCompleteDefinition() ) {
      ClassContext ct = classContext( ed->getNameAsString());
      tu->currentIndent = 1;
      cout << "enum " << ct.ctype << endl; 
    }
  }
  virtual void onEndOfTranslationUnit() {
    //std::cout << "endOfTU:" /*<< std::string( outputFilePath.str()) */ << std::endl;
    //cout << tu->def.str() << endl;
    //cout << "---- trType log ----" << endl;
    //for( auto i = tu->trTypeLog.begin(); i != tu->trTypeLog.end(); ++i) {
    //  cout << *i << endl;     
    //}
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
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      const TranslationUnit& tu = *(*i);
      for( auto j = tu.trTypeLog.begin(); j != tu.trTypeLog.end(); ++j) {
	typeLog.insert( *j);
      }
      os << "// --- " << tu.fileName << " ---" << endl;
      os << "// provides: ";
      for( auto j = tu.prTypes.begin(); j != tu.prTypes.end(); ++j) {
	if( j != tu.prTypes.begin()) os << ", ";
	os << *j;
      }
      os << endl;
      os << "// requires: ";
      for( auto j = tu.dpTypes.begin(); j != tu.dpTypes.end(); ++j) {
	if( j != tu.dpTypes.begin()) os << ", ";
	os << *j;
      }
      os << endl;
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
    }
    os << "class " << ctr.targetClass << " {" << endl;
    os << "  requires package \"" << ctr.package << "\";" << endl;
    for( auto i = ctr.openClasses.begin(); i != ctr.openClasses.end(); ++i) {
      os << "  open " << *i << ";" << endl;
    }
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      os << "// --- " << (*i)->fileName << " ---" << endl;
      os << (*i)->def.str();
    }
    os << "};" << endl;
    os.close();
  }
};

static string makerRetType;

bool setTypeMaker( const CXXRecordDecl* rd, const ClassContext& ct, TranslationUnit& tu) {
  makerRetType.clear();
  for( auto mi = rd->method_begin(); mi != rd->method_end(); ++mi) {
    const CXXMethodDecl* m = mi.operator*();
    if( m->getNameAsString() == "Value" ) {
      FType ft = trType( m->getReturnType(), tu.trTypeLog);
      makerRetType = ft.name;
      break;
    } 
  }
  setType( rd, ct, tu);
  tu.def << indent(tu.currentIndent) << "#init[" << ct.ftype << "," << makerRetType << "];" << endl;
  return true;
}

bool trCtorMaker( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {    
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    auto& d = tu.def;
    string n = ct.ftype;
    if( ct.ftype.find( "Make") == 0) n = ct.ftype.substr( 4);
    d << indent(tu.currentIndent) << "gen " << n << " ";
    auto args_ = namedArgs( m, ct, tu);
    for( auto a = args_.begin(); a != args_.end(); ++a) {
      d << "(" << a->first << ":" << a->second << ") ";
    }
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
    {"gp","TKMath",{"Standard"},{},Value,""
     ,setType,{trCtor,trMemberFct}}
    ,{"Geom", "TKG3d",{"Standard","gp"},{},OccHandle,"T"
      ,setType,{trCtor,trMemberFct}}
    ,{"GC", "TKGeomBase",{"Standard","Geom","gp"},{"GC_Impl"},Other,""
      ,setTypeMaker,{trCtorMaker}}
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
  std::error_code EC;
  Regex modre("([A-Za-z0-9]+)[_A-Za-z0-9]*\\.hxx");
  for( sys::fs::directory_iterator i( occIncDir, EC);
       i != sys::fs::directory_iterator(); i.increment( EC)) {
    if (EC) {
      llvm::errs() << "while traverse '" << occIncDir << "': "
		   << EC.message() << '\n';
      exit(1);
    }
    SmallVector<StringRef,2> m;
    if( modre.match( sys::path::filename( i->path()),&m)) {
      auto m_ = m.begin(); m_++; 
      if( m_ != m.end()) {
	groupedFiles[ m_->str()].push_back(i->path());
      }
    }
  }
  //  for( auto i = groupedFiles.begin(); i != groupedFiles.end(); ++i) {
  //  std::cout << i->first << ":" << i->second.size() << std::endl;
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
    std::vector<std::string> files( files_.size()); int j=0;
    for( auto i = files_.begin(); i != files_.end(); ++i) {
      files[j++] = *i;
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
