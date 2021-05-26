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

static llvm::SmallString<256> realOutputDir;
static llvm::SmallString<256> realOccDir;

//static llvm::cl::extrahelp CommonHelp(CommonOptionsParser::HelpMessage);

// A help message for this specific tool can be added afterwards.
// static llvm::cl::extrahelp MoreHelp("\nMore help text...\n");

//hasName("gp_Pnt"))
DeclarationMatcher ClassMatcher =
  cxxRecordDecl(isExpansionInMainFile()
		, hasDefinition()
		/*.hasDeclContext(translationUnitDecl())*/
		).bind("classDecl");

class FType {
public:
  string name;
  string inClass;
  bool   builtin;
  bool   pointer;
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

FType trType( const QualType& qt_) {
  QualType qt = qt_;
  FType t; t.builtin=false; t.pointer=false;
  if( qt->isReferenceType() || qt->isPointerType()) {
    qt = qt->getPointeeType();
    if( !qt.isLocalConstQualified() ) t.pointer = true; 
  }
  if( qt.isLocalConstQualified()) qt.removeLocalConst();
  if( qt->isTypedefNameType()){
    setClassAndName( qt.getAsString(), t);
  //   string n = qt.getAsString();
  //   if( n == "Standard_Real" )
  //     { t.name = "double"; t.builtin = true; return t;}
  //   else if( n == "Standard_Integer" )
  //     { t.name = "int"; t.builtin = true; return t;}
  //   else if( n == "Standard_Boolean" )
  //     { t.name = "bool"; t.builtin = true; return t;}
  //   else if( n == "Standard_OStream" )
  //     { t.name = "ostream"; t.inClass = "std"; return t; }
  //   else if( n == "Standard_SStream" )
  //     { t.name = "stringstream"; t.inClass = "std"; return t; }
    
  //   //const TypedefType* tt = qt->getAs<TypedefType>();
  //   //qt = tt->desugar();
  } else if( qt->isBuiltinType() ) {
    t.name = qt.getAsString(); t.builtin = true;
  } else if( qt->isRecordType()) {
    const CXXRecordDecl* crd = qt->getAsCXXRecordDecl();
    setClassAndName( crd->getNameAsString(), t);
  } else {
    t.name = qt.getAsString();
  }
  return t;
}

FType trType( const QualType& qt, set<string>& log) {
  stringstream l; l << "trType(" << qt.getAsString() << ") -> ";
  const FType t = trType( qt);
  if( !t.inClass.empty()) l << t.inClass << "::";
  l << t.name;
  if( t.pointer) l <<"&";
  if( t.builtin) l <<" b";
  log.insert( l.str());
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
  stringstream def;
  set<string> trTypeLog;
};

bool containsAtLeastOneOf(const set<string>& u,const set<string>& v) {
  auto i = u.begin();
  while( i != u.end() && v.find( *i) == v.end()) ++i;
  return i != u.end();
}
  
string inClassType( const FType& ft, const string& inClass, const set<string>& openClasses,
		    TranslationUnit& tu) {
  string name = ft.name;
  if( ft.pointer) name += "&";
  if( ft.builtin || ft.inClass.empty()) return name;
  else { 
    if ( ft.inClass == inClass ) {
      if( tu.prTypes.find( ft.name) == tu.prTypes.end())
	tu.dpTypes.insert( ft.name);
      return name;
    } else {
      tu.dpClasses.insert( ft.inClass);
      if( openClasses.find( ft.inClass) != openClasses.end())
	return name;
      else
	return ft.inClass + "::" + name;
    }
  }
}

list<string> args
( const CXXMethodDecl* m, const string& inClass, const set<string>& openClasses, TranslationUnit& tu )
{
  list<string> a;
  for(unsigned int i=0; i < m->getNumParams(); i++) {
    a.push_back( inClassType( trType ( m->parameters()[i]->getType(), tu.trTypeLog),
			      inClass, openClasses, tu));
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

class ClassContext {
public:
  const string& inClass;
  const set<string>& openClasses;
  string ftype;
  string ctype;
  ClassContext( const string& inClass_,
		const set<string>& openClasses_) :
    inClass( inClass_), openClasses( openClasses_) {}
};

bool trCtor( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {    
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    auto& d = tu.def;
    d << "  " << "ctor " << ct.ftype << ": ";
    auto args_ = args( m, ct.inClass, ct.openClasses, tu); 
    printArgs( args_, d);
    d << " = \"" << ct.ctype << "("; if( !args_.empty()) d << "$a";
    d << ")\";" << endl;
    return true;
  } else return false;
}

bool trMemberFct( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if ( !isa<CXXConstructorDecl>(m) && !isa<CXXDestructorDecl>(m) &&
       ! m->isOverloadedOperator()) {
    auto& d = tu.def;
    const QualType rt = m->getReturnType();
    if ( rt->isVoidType() ) d << "  proc "; else d << "  fun ";
    const string name = m->getNameAsString(); 
    d << name << ": ";
    std::list<string> args_ = args( m, ct.inClass, ct.openClasses, tu);
    // if not a static method then first arg is of type ftype
    if( !m->isStatic()) args_.push_front( ct.ftype);
    printArgs( args_, d);
    if ( !rt->isVoidType() ) // print return type
      d << " -> " << inClassType( trType( rt, tu.trTypeLog), ct.inClass, ct.openClasses, tu);
    d << " = \""; 
    if( m->isStatic()) {
      d << name << "("; if( !args_.empty()) d << "$a";
      d << ")\";" << endl;
    }
    else {
      d << "$1." << name << "("; if( args_.size()>1) d << "$b";
      d << ")\";" << endl;
    }
    return true;
  } else return false;
}
 

class ClassWriter : public MatchFinder::MatchCallback {
private:
  list<shared_ptr<TranslationUnit>> tus;
  shared_ptr<TranslationUnit> tu;
  string targetClass;
  string package;
  set<string> openClasses;
  set<string> dpClasses;
public :
  ClassWriter ( const string& targetClass_, const string& package_,
		const set<string>& openClasses_)
    :targetClass( targetClass_),
     package(package_), openClasses( openClasses_)
  {} //: str(""), os( str) {}
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
    if (const CXXRecordDecl *RD = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("classDecl")) {
      //std::cout << "run" << std::endl;
      ClassContext ct( targetClass, openClasses);
      ct.ctype = RD->getDeclName().getAsString();
      string::size_type p = ct.ctype.find_first_of( '_');
      if( p != string::npos ) {
	const string inClass = ct.ctype.substr( 0, p);
	if( ct.inClass != inClass ) {
	  //cout << "Error, found definition for " << inClass << ", but required class is " << ct.inClass
	  //     << "! for type " << ct.ctype << " in file " << tu->fileName << endl;
	  return;
	}
	ct.ftype = ct.ctype.substr( p+1, string::npos);
      } else {
	//cout << "Warning, found unclassified type " << ct.ctype << " in file " << tu->fileName << endl; 
	ct.ftype = ct.ctype;
      }      
      //cout << ct.ftype;
      if (RD->isCompleteDefinition()) {
	//cout << "*";
	tu->prTypes.insert( ct.ftype);
	tu->def << "  " << "type " << ct.ftype << " = \"" << ct.ctype << "\" requires " << tu->headerName << ";" << endl;
	// methods
	for( DeclContext::specific_decl_iterator<CXXMethodDecl> mi = RD->method_begin(); mi != RD->method_end(); ++mi) {
	  const CXXMethodDecl* m = mi.operator*();
	  trCtor( m, ct, *tu);
	  trMemberFct( m, ct, *tu);
	}
      }
      //cout << endl;
    }
  }
  virtual void onEndOfTranslationUnit() {
    //    std::cout << "endOfTU:" /*<< std::string( outputFilePath.str()) */ << std::endl;
    //cout << tu->def.str() << endl;
    //cout << "---- trType log ----" << endl;
    //for( auto i = tu->trTypeLog.begin(); i != tu->trTypeLog.end(); ++i) {
    //  cout << *i << endl;
    //}
    for( auto i = tu->dpClasses.begin(); i != tu->dpClasses.end(); ++i) {
      dpClasses.insert( *i);
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
    sys::path::append( outputFilePath, targetClass);
    outputFilePath.append( ".flx");
    cout << "output file:" << string( outputFilePath.str()) << endl;        
    // Open the output file
    ofstream os( outputFilePath.c_str());
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      const TranslationUnit& tu = *(*i);
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
    os << "---------------------------------------------------------" << endl;
    for( auto i = dpClasses.begin(); i != dpClasses.end(); ++i) {
      os << "include \"" << *i << "\";" << endl;
    }
    for( auto i = tus.begin(); i != tus.end(); ++i) {
      if( !(*i)->headerName.empty())
	os << "header " << (*i)->headerName << " = '#include \"" << (*i)->fileName << "\"';" << endl;
    }
    os << "class " << targetClass << " {" << endl;
    os << "  requires package \"" << package << "\";" << endl;
    for( auto i = openClasses.begin(); i != openClasses.end(); ++i) {
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
  auto& files_ = groupedFiles["gp"];
  std::vector<std::string> files( files_.size()); int j=0;
  for( auto i = files_.begin(); i != files_.end(); ++i) {
   files[j++] = *i;
  }
  ClangTool Tool(cdb, files); //OptionsParser.getSourcePathList());
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
     
  ClassWriter Writer("gp","TKMath", set<string>({"Standard"}));
  MatchFinder Finder;
  Finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource,
			     ClassMatcher
			     ), &Writer);

  
  int result = Tool.run(newFrontendActionFactory( &Finder).get());
  if( result != 0) cout << "Error during Tool run" << endl;
  Writer.writeFile();
}
