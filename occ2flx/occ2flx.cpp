#include "clang/Tooling/CommonOptionsParser.h"
#include "llvm/Support/CommandLine.h"
#include "clang/ASTMatchers/ASTMatchers.h"
#include "clang/ASTMatchers/ASTMatchFinder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/Utils.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Serialization/ASTReader.h"
#include <iostream>
#include <sstream>
#include <unistd.h>
#include "llvm/Support/Path.h"

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

DeclarationMatcher ClassMatcher = cxxRecordDecl(hasName("gp_Pnt")).bind("classDecl");

class ClassWriter : public MatchFinder::MatchCallback {
public :
  ClassWriter () : str(""), os( str) {}
  virtual void run(const MatchFinder::MatchResult &Result) {
    if (const CXXRecordDecl *RD = Result.Nodes.getNodeAs<clang::CXXRecordDecl>("classDecl")) {
      std::cout << "run" << std::endl;
      std::cout << RD->getDeclName().getAsString() <<  std::endl;
      if (RD->isCompleteDefinition()) {
	std::cout << "completeDefinition" << std::endl; 
	//RD->dump();
	outputFilePath.clear();
	outputFilePath.append( realOutputDir);
	sys::path::append( outputFilePath, RD->getDeclName().getAsString());
	outputFilePath.append( ".flx");
	std::cout << "ofp:" << std::string( outputFilePath.str()) << std::endl;
      }
    }
  }
  virtual void onStartOfTranslationUnit() {
    std::cout << "startOfTU" << std::endl;
  }
  virtual void onEndOfTranslationUnit() {
    std::cout << "endOfTU:" << std::string( outputFilePath.str()) << std::endl;
    // Open the output file
    std::error_code EC;
    llvm::raw_fd_ostream HOS(outputFilePath, EC, llvm::sys::fs::F_None);
    if (EC) {
      llvm::errs() << "while opening '" << outputFilePath << "': "
		   << EC.message() << '\n';
      exit(1);
    }

  }
private:
  std::string str;
  llvm::raw_string_ostream os;
  llvm::SmallString<256> outputFilePath;
};




int main(int argc, const char **argv) {
  llvm::cl::ParseCommandLineOptions(argc, argv);
  std::error_code ec;
  ec = sys::fs::real_path( occDir, realOccDir, true);
  if( ec ) {
    std::cout << "occ dir not found:" << occDir << ", " << ec.message() << std::endl;
    exit(1);
  } 
  std::stringstream iFlag;
  iFlag << "-I" << std::string( realOccDir.str()) << "/include";
  std::string flags[] = { iFlag.str(), "-std=c++0x" };
  FixedCompilationDatabase cdb( realOccDir.str(), flags);

  std::string files[] = { "/home/robert/prog/apps/opencascade-7.5.0-install/include/gp_Pnt.hxx"};
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
