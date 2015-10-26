//===- ClangFnMapGen.cpp -----------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===--------------------------------------------------------------------===//
//
// Clang tool which creates a list of defined functions and the files in which
// they are defined.
//
//===--------------------------------------------------------------------===//

#include "clang/AST/ASTConsumer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/GlobalDecl.h"
#include "clang/AST/Mangle.h"
#include "clang/AST/StmtVisitor.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Frontend/CompilerInstance.h"
#include "clang/Frontend/FrontendActions.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Signals.h"
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <string>
#include <vector>
#include <assert.h>
#include <limits.h>
#include <sys/file.h>
#include <unistd.h>
#include <sstream>

using namespace llvm;
using namespace clang;
using namespace clang::tooling;

typedef std::set<std::string> StrSet;
typedef std::map<std::string, StrSet> CallGraph;

// Utility Functions to get the temporary directory
static const char* getTmpDir(void) {
  char *tmpdir;
  if ((tmpdir = getenv ("OUT_DIR")) != NULL)   return tmpdir;
  if ((tmpdir = getenv ("TEMP")) != NULL)   return tmpdir;
  if ((tmpdir = getenv ("TMP")) != NULL)    return tmpdir;
  if ((tmpdir = getenv ("TMPDIR")) != NULL) return tmpdir;
  return "/tmp";
}

static void lockedWrite(const std::string &fileName, const std::string &content) {
  if (!content.empty()) {
    int fd = open(fileName.c_str(), O_CREAT|O_WRONLY|O_APPEND, 0777);
    flock(fd, LOCK_EX);
    write(fd, content.c_str(), content.length());
    flock(fd, LOCK_UN);
    close(fd);
  }
}


static std::string getTripleSuffix(ASTContext &Ctx) {
  // We are not going to support vendor and don't support OS and environment.
  // FIXME: support OS and environment correctly
  llvm::Triple::ArchType T = Ctx.getTargetInfo().getTriple().getArch();
  if (T == llvm::Triple::thumb)
    T = llvm::Triple::arm;
  return Ctx.getTargetInfo().getTriple().getArchTypeName(T);
}

class MapFunctionNamesConsumer : public ASTConsumer {
private:
  ASTContext &Ctx;
  ItaniumMangleContext *ItaniumCtx;
  std::stringstream DefinedFuncsStr;
  std::stringstream ExternFuncStr;
  CallGraph CG;
  const std::string Triple;

public:
  MapFunctionNamesConsumer(ASTContext &Context, ItaniumMangleContext *MangleCtx)
      : Ctx(Context), ItaniumCtx(MangleCtx),
        Triple(std::string("@") + getTripleSuffix(Context)),
        Magic(getenv("XTU_MAGIC") ? getenv("XTU_MAGIC") : "") {
  }
  std::string CurrentFileName;
  std::string Magic;

  ~MapFunctionNamesConsumer();
  virtual void HandleTranslationUnit(ASTContext &Ctx) {
    handleDecl(Ctx.getTranslationUnitDecl());
  }

private:
  std::string getMangledName(const FunctionDecl* FD, MangleContext *Ctx);
  std::string getMangledName(const FunctionDecl* FD) {
    return getMangledName(FD, ItaniumCtx);
  }

  bool isCLibraryFunction(const FunctionDecl *FD);
  void handleDecl(const Decl *D);

  class WalkAST : public ConstStmtVisitor<WalkAST> {
    MapFunctionNamesConsumer &Parent;
    std::string CurrentFuncName;
    MangleContext *MangleCtx;
    const std::string Triple;
  public:
    WalkAST(MapFunctionNamesConsumer &parent, const std::string &FuncName,
            MangleContext *Ctx, const std::string &triple)
        : Parent(parent), CurrentFuncName(FuncName), MangleCtx(Ctx),
          Triple(triple) {}
    void VisitCallExpr(const CallExpr *CE);
    void VisitStmt(const Stmt *S) { VisitChildren(S); }
    void VisitChildren(const Stmt *S);
  };
};

std::string MapFunctionNamesConsumer::getMangledName(const FunctionDecl *FD,
                                                     MangleContext *Ctx) {
  std::string MangledName;
  llvm::raw_string_ostream os(MangledName);
  if (const CXXConstructorDecl *CCD = dyn_cast<CXXConstructorDecl>(FD))
    // FIXME: Use correct Ctor/DtorType
    Ctx->mangleCXXCtor(CCD, Ctor_Complete, os);
  else if (const CXXDestructorDecl *CDD = dyn_cast<CXXDestructorDecl>(FD))
    Ctx->mangleCXXDtor(CDD, Dtor_Complete, os);
  else
    Ctx->mangleName(FD, os);
  os.flush();
  return MangledName;
}

void MapFunctionNamesConsumer::handleDecl(const Decl *D) {
  if (!D)
    return;

  if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
    if (const Stmt *Body = FD->getBody()) {
      std::string MangledName = getMangledName(FD);
      const SourceManager &SM = Ctx.getSourceManager();
      if (CurrentFileName.empty()) {
        const char *SMgrName = SM.getFileEntryForID(SM.getMainFileID())
            ->getName();
        char *Path = realpath(SMgrName, NULL);
        CurrentFileName = Path;
        free(Path);
      }

      std::string FileName = std::string("/ast/") + Magic + CurrentFileName;
      std::string FullName = MangledName + Triple;

      if (!FileName.empty())
        switch (FD->getLinkageInternal()) {
        case ExternalLinkage:
        case VisibleNoLinkage:
        case UniqueExternalLinkage:
          if (SM.isInMainFile(Body->getLocStart()))
            DefinedFuncsStr << "!";
          DefinedFuncsStr << FullName << " " << FileName << "\n";
        default:
          break;
        }

      WalkAST Walker(*this, FullName, ItaniumCtx, Triple);
      Walker.Visit(Body);
    } else if (!FD->getBody() && !FD->getBuiltinID()) {
      std::string MangledName = getMangledName(FD);
      ExternFuncStr << MangledName << Triple << "\n";
    }
  }

  if (const DeclContext *DC = dyn_cast<DeclContext>(D))
    for (DeclContext::decl_iterator I = DC->decls_begin(), E = DC->decls_end();
         I != E; ++I)
      handleDecl(*I);
}

bool MapFunctionNamesConsumer::isCLibraryFunction(const FunctionDecl *FD) {
  SourceManager &SM = Ctx.getSourceManager();
  if (!FD)
    return false;
  SourceLocation Loc = FD->getLocation();
  if (Loc.isValid())
    return SM.isInSystemHeader(Loc);
  return true;
}

MapFunctionNamesConsumer::~MapFunctionNamesConsumer() {
  // flush results to files
  std::string BuildDir = getTmpDir();
  lockedWrite(BuildDir + "/externalFns.txt", ExternFuncStr.str());
  lockedWrite(BuildDir + "/definedFns.txt", DefinedFuncsStr.str());
  std::stringstream CFGStr;
  for (CallGraph::const_iterator I = CG.begin(), E = CG.end(); I != E; I++) {
    CFGStr << CurrentFileName << Triple << "::" << I->first;
    for (StrSet::const_iterator IS = I->second.begin(), ES = I->second.end();
         IS != ES; IS++)
      CFGStr << ' ' << *IS;
    CFGStr << '\n';
  }

  lockedWrite(BuildDir + "/cfg.txt", CFGStr.str());
}


void MapFunctionNamesConsumer::WalkAST::VisitChildren(const Stmt *S) {
  for (Stmt::const_child_iterator I = S->child_begin(), E = S->child_end();
       I != E; ++I)
    if (*I)
      Visit(*I);
}

void MapFunctionNamesConsumer::WalkAST::VisitCallExpr(const CallExpr *CE) {
  const FunctionDecl *FD = dyn_cast_or_null<FunctionDecl>(CE->getCalleeDecl());
  if (FD && !FD->getBuiltinID()) {
    std::string FuncName = (FD->hasBody() ? "::" : "") +
        Parent.getMangledName(FD, MangleCtx) + Triple;
    Parent.CG[CurrentFuncName].insert(FuncName);
  }
  VisitChildren(CE);
}


class MapFunctionNamesAction: public ASTFrontendAction {
protected:
  ASTConsumer *CreateASTConsumer(CompilerInstance &CI, llvm::StringRef) {
    ItaniumMangleContext *ItaniumCtx =
        ItaniumMangleContext::create(CI.getASTContext(), CI.getDiagnostics());
    ItaniumCtx->setShouldForceMangleProto(true);
    MapFunctionNamesConsumer* PFC =
        new MapFunctionNamesConsumer(CI.getASTContext(), ItaniumCtx);
    return PFC;
}
};


int main(int argc, const char **argv) {
  // Print a stack trace if we signal out.
  sys::PrintStackTraceOnErrorSignal();
  PrettyStackTraceProgram X(argc, argv);

  std::vector<std::string> Sources;
  CommonOptionsParser OptionsParser(argc, argv);
  for (int i = 1; i < argc; i++) {
    StringRef arg = argv[i];
    const std::string cppFile = ".cpp", ccFile = ".cc", cFile = ".c",
        cxxFile = ".cxx";
    if (arg.endswith(cppFile) || arg.endswith(ccFile) ||
        arg.endswith(cFile) || arg.endswith(cxxFile)) {
      Sources.push_back(arg);
    }
  }
  ClangTool Tool(OptionsParser.getCompilations(), Sources);
  Tool.run(newFrontendActionFactory<MapFunctionNamesAction>());
}
