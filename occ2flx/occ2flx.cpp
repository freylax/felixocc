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
};

FType trType( const QualType& qt_) {
  const QualType qt = qt_.getLocalUnqualifiedType();
  FType t; t.builtin=false;
  if(qt->isBuiltinType() || (qt->isPointerType() && qt->getPointeeType()->isBuiltinType())) {
    t.name = qt.getAsString(); t.builtin = true;
  } else if(qt->isRecordType()) {
    const CXXRecordDecl* crd = qt->getAsCXXRecordDecl();
    string rn = crd->getNameAsString();
    cout << "tr(" << rn << ")" << endl;
    if( rn.compare( "Standard_Real" ) == 0 ) { t.name = "double"; t.builtin = true; }
    else if( rn.compare( "Standard_Integer" ) == 0 ) { t.name = "int"; t.builtin = true; }
    else if( rn.compare( "Standard_Boolean" ) == 0 ) { t.name = "bool"; t.builtin = true; }
    else {
      string::size_type p = rn.find_first_of( '_');
      if( p != string::npos ) {
	t.inClass = rn.substr( 0, p);
	t.name = rn.substr( p+1, string::npos);
      } else {
	t.name = rn;
      }
    }
  } else {
    t.name = qt.getAsString();
    cout << "TR(" << t.name << ")" << endl;
  }
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
};

string inClassType( const FType& ft, const string& inClass, TranslationUnit& tu) {
  if( ft.builtin || ft.inClass.empty()) return ft.name;
  else { 
    if ( ft.inClass == inClass ) {
      tu.dpTypes.insert( ft.name);
      return ft.name;
    } else {
      tu.dpClasses.insert( ft.inClass);
      return inClass + "::" + ft.name;
    }
  }
}

list<string> args
( const CXXMethodDecl* m, const string& inClass, TranslationUnit& tu )
{
  list<string> a;
  for(unsigned int i=0; i < m->getNumParams(); i++) {
    a.push_back( inClassType( trType ( m->parameters()[i]->getType()),
			      inClass, tu));
  }
  return a;
}

void printArgs( const list<string>& args, stringstream& s) {
  for( auto a = args.begin(); a != args.end(); ++a) {
    if( a != args.begin()) s << " *";
    s << " " << *a;
  }
}

struct ClassContext { string inClass, ftype, ctype; };

bool trCtor( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m)) {
    if(c->isCopyConstructor() || c->isMoveConstructor()) return true;
    tu.def << "  " << "ctor " << ct.ftype << ": ";
    printArgs( args( m, ct.inClass, tu), tu.def);
    tu.def << " = \"" << ct.ctype << "($a)\";" << endl;
    return true;
  } else return false;
}

bool trMemberFct( const CXXMethodDecl* m, const ClassContext& ct, TranslationUnit& tu) {
  if ( !isa<CXXConstructorDecl>(m) && !isa<CXXDestructorDecl>(m) &&
       ! m->isOverloadedOperator()) {
    const QualType rt = m->getReturnType();
    if ( rt->isVoidType() ) tu.def << "  proc "; else tu.def << "  fun ";
    const string name = m->getNameAsString(); 
    tu.def << name << ": ";
    std::list<string> args_ = args( m, ct.inClass, tu);
    // if not a static method then first arg is of type ftype
    if( !m->isStatic()) args_.push_front( ct.ftype);
    printArgs( args_, tu.def);
    if ( !rt->isVoidType() ) // print return type
      tu.def << " -> " << inClassType( trType( rt), ct.inClass, tu);
    if( m->isStatic()) tu.def << name << "($a)\";" << endl;
    else tu.def << "$1." << name << "($b)\";" << endl;
    return true;
  } else return false;
}
 

class ClassWriter : public MatchFinder::MatchCallback {
private:
  list<TranslationUnit> tus;
  TranslationUnit tu;
  string targetClass;
public :
  ClassWriter ( const string& targetClass_):targetClass( targetClass_) {} //: str(""), os( str) {}
  virtual void onStartOfTranslationUnit() {
    std::cout << "startOfTU" << std::endl;
    tu = TranslationUnit();
  }
  
  virtual void run(const MatchFinder::MatchResult &Result) {
    if( tu.filePath.empty()) {
      clang::SourceManager* sm = Result.SourceManager;
      auto fp = sm->getNonBuiltinFilenameForID( sm->getMainFileID());
      if( fp.hasValue()) {
	tu.filePath = fp.getValue().str();
	tu.fileName = sys::path::filename( tu.filePath).str();
	tu.headerName = tu.fileName; replace( tu.headerName.begin(), tu.headerName.end(), '.', '_'); 
      }      
    }
    if (const CXXRecordDecl *RD = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("classDecl")) {
      //std::cout << "run" << std::endl;
      ClassContext ct; ct.inClass = targetClass;
      ct.ctype = RD->getDeclName().getAsString();
      string::size_type p = ct.ctype.find_first_of( '_');
      if( p != string::npos ) {
	const string inClass = ct.ctype.substr( 0, p);
	if( ct.inClass != inClass ) {
	  cout << "Error, found definition for " << inClass << ", but required class is " << ct.inClass
	       << "! for type " << ct.ctype << " in file " << tu.fileName << endl;
	  return;
	}
	ct.ftype = ct.ctype.substr( p+1, string::npos);
      } else {
	cout << "Warning, found unclassified type " << ct.ctype << " in file " << tu.fileName << endl; 
	ct.ftype = ct.ctype;
      }      
      cout << ct.ftype;
      if (RD->isCompleteDefinition()) {
	cout << "*";
	tu.prTypes.insert( ct.ftype);
	tu.def << "  " << "type " << ct.ftype << " = \"" << ct.ctype << "\" requires " << tu.headerName << ";" << endl;
	// methods
	for( DeclContext::specific_decl_iterator<CXXMethodDecl> mi = RD->method_begin(); mi != RD->method_end(); ++mi) {
	  const CXXMethodDecl* m = mi.operator*();
	  trCtor( m, ct, tu);
	  trMemberFct( m, ct, tu);
	}
      }
      cout << endl;
    }
  }
  virtual void onEndOfTranslationUnit() {
    std::cout << "endOfTU:" /*<< std::string( outputFilePath.str()) */ << std::endl;
    cout << tu.def.str() << endl;
    // Open the output file
    //std::error_code EC;
    //llvm::raw_fd_ostream HOS(outputFilePath, EC, llvm::sys::fs::F_None);
    //if (EC) {
    //  llvm::errs() << "while opening '" << outputFilePath << "': "
    //		   << EC.message() << '\n';
    //  exit(1);
    //}
  }
  //private:
  //std::string str;
  //llvm::raw_string_ostream os;
  //llvm::SmallString<256> outputFilePath;
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
  std::string files[] = { "/home/robert/prog/apps/opencascade-7.5.0-install/include/gp_Pnt.hxx"};
  //auto& files_ = groupedFiles["gp"];
  //std::vector<std::string> files( files_.size()); int j=0;
  //for( auto i = files_.begin(); i != files_.end(); ++i) {
  // files[j++] = *i;
  //}
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
     
  ClassWriter Writer("gp");
  MatchFinder Finder;
  Finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource,
			     ClassMatcher
			     ), &Writer);

  
  return Tool.run(newFrontendActionFactory( &Finder).get());
}
	// std::cout << "completeDefinition" << std::endl; 
	//RD->dump();
	//outputFilePath.clear();
	//outputFilePath.append( realOutputDir);
	//sys::path::append( outputFilePath, RD->getDeclName().getAsString());
	//outputFilePath.append( ".flx");
	//std::cout << "ofp:" << std::string( outputFilePath.str()) << std::endl;
