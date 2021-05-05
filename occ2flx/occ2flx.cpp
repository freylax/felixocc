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


struct TranslationUnit {
  string filePath;
  string fileName;
  string headerName;
  set<string> dependentTypes;
  set<string> providesTypes;
  stringstream def;
};

enum funKind { ctor, fun, proc, none};

class ClassWriter : public MatchFinder::MatchCallback {
private:
  list<TranslationUnit> tus;
  TranslationUnit tu;
public :
  ClassWriter () {} //: str(""), os( str) {}
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
      string ctype = RD->getDeclName().getAsString();
      string ftype = ctype;
      cout << ftype;
      if (RD->isCompleteDefinition()) {
	cout << "*";
	tu.providesTypes.insert( ftype);
	tu.def << "  " << "type " << ftype << " = \" << ctype << \" requires " << tu.headerName << ";" << endl;
	// methods
	for( DeclContext::specific_decl_iterator<CXXMethodDecl> m = RD->method_begin(); m != RD->method_end(); ++m) {
	  string fun,name,ret;
	  std::list< string> args;
	  bool isCtor = false;
	  bool isMemberFun = false;
	  // ignore operator overloading
	  if( m->isOverloadedOperator()) continue;
	  // ctor
	  if (const CXXConstructorDecl* c = dyn_cast<CXXConstructorDecl>(m.operator*())) {
	    if(c->isCopyConstructor() || c->isMoveConstructor()) continue;
	    fun = "ctor"; name = ftype; isCtor=true;
	  } else if (isa<CXXDestructorDecl>(m.operator*())) { continue;
	  } else {
	    const QualType qt = m->getReturnType();
	    if (qt->isVoidType()) {
	      fun = "proc"; 
	    } else {
	      fun = "fun";
	      ret = qt.getAsString();
	    }
	    name = m->getNameAsString();
	    // if not a static method then first arg is of type ftype
	    if( !m->isStatic()) {
	      args.push_back( ftype);
	      isMemberFun = true;
	    }
	  }
	  for(unsigned int i=0; i < m->getNumParams(); i++) {
	    const QualType qt = m->parameters()[i]->getType();
	    args.push_back( qt.getAsString());
	  }
	  tu.def << "  " << fun << name << ": ";
	  for( auto a = args.begin(); a != args.end(); ++a) {
	    if( a != args.begin()) tu.def << " *";
	    tu.def << " " << *a;
	  }
	  if( !ret.empty())
	    tu.def << " -> " << ret;
	  tu.def << " = \"";
	  if( isCtor) tu.def << ctype << "($a)";
	  else if( isMemberFun) tu.def << "$1." << name << "($b)";
	  else tu.def << name << "($a)";
	  tu.def << "\";" << endl;
	}
	// std::cout << "completeDefinition" << std::endl; 
	//RD->dump();
	//outputFilePath.clear();
	//outputFilePath.append( realOutputDir);
	//sys::path::append( outputFilePath, RD->getDeclName().getAsString());
	//outputFilePath.append( ".flx");
	//std::cout << "ofp:" << std::string( outputFilePath.str()) << std::endl;
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
     
  ClassWriter Writer;
  MatchFinder Finder;
  Finder.addMatcher(traverse(TK_IgnoreUnlessSpelledInSource,
			     ClassMatcher
			     ), &Writer);

  
  return Tool.run(newFrontendActionFactory( &Finder).get());
}
