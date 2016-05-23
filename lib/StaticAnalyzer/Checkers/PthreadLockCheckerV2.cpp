//===--- PthreadLockChecker.cpp - Check for locking problems ---*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This defines PthreadLockChecker, a simple lock -> unlock checker.
// Also handles XNU locks, which behave similarly enough to share code.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "llvm/ADT/ImmutableList.h"

using namespace clang;
using namespace ento;

namespace {
enum PthreadMutexLockState { Destroyed, Locked, Unlocked };
enum LockingSemantics { NotApplicable = 0, PthreadSemantics, XNUSemantics };

SmartStateTrait PthreadLockMutexStateTrait;
SmartStateTrait PthreadLockStackPointerTrait;

struct InitLockSpec {
  unsigned ArgNo;
};
llvm::StringMap<InitLockSpec> InitLockFunctions = {
  { "pthread_mutex_init" , { 0 } }
};

struct AcquireSpec {
  unsigned ArgNo;
  bool IsTrylock;
  LockingSemantics Semantics;
};
llvm::StringMap<AcquireSpec> AcquireLockFunctions = {
  { "pthread_mutex_lock",    { 0, false, PthreadSemantics } },
  { "pthread_rwlock_rdlock", { 0, false, PthreadSemantics } },
  { "pthread_rwlock_wrlock", { 0, false, PthreadSemantics } },

  { "lck_mtx_lock",          { 0, false, XNUSemantics } },
  { "lck_rw_lock_exclusive", { 0, false, XNUSemantics } },
  { "lck_rw_lock_shared",    { 0, false, XNUSemantics } },

  { "pthread_mutex_trylock",    { 0, true, PthreadSemantics } },
  { "pthread_rwlock_tryrdlock", { 0, true, PthreadSemantics } },
  { "pthread_rwlock_trywrlock", { 0, true, PthreadSemantics } },

  { "lck_mtx_try_lock",          { 0, true, XNUSemantics } },
  { "lck_rw_try_lock_exclusive", { 0, true, XNUSemantics } },
  { "lck_rw_try_lock_shared",    { 0, true, XNUSemantics } }
};

struct ReleaseLockSpec {
  unsigned ArgNo;
};
llvm::StringMap<ReleaseLockSpec> ReleaseLockFunctions = {
  { "pthread_mutex_unlock",  { 0 } },
  { "pthread_rwlock_unlock", { 0 } },
  { "lck_mtx_unlock",        { 0 } },
  { "lck_rw_done",           { 0 } }
};

struct DestroyLockSpec {
  unsigned ArgNo;
};
llvm::StringMap<DestroyLockSpec> DestroyLockFunctions = {
  { "pthread_mutex_destroy", { 0 } },
  { "lck_mtx_destroy",       { 0 } },
};
} // end anonymous namespace


namespace {
class PthreadLockMutexStateModel
    : public Checker<check::ASTDecl<TranslationUnitDecl>,
                     check::PostStmt<CallExpr>> {
public:
  void checkASTDecl(const TranslationUnitDecl *D, AnalysisManager &AMgr,
                    BugReporter &BR) const;
  void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;
};
} // end anonymous namespace

void PthreadLockMutexStateModel::checkASTDecl(const TranslationUnitDecl *D,
                                              AnalysisManager &AMgr,
                                              BugReporter &BR) const {
  PthreadLockMutexStateTrait.initialize("PthreadLockMutexState",
                                        AMgr.getASTContext().IntTy);
}

void PthreadLockMutexStateModel::checkPostStmt(const CallExpr *CE,
                                               CheckerContext &C) const {
  ProgramStateRef state = C.getState();
  StringRef FName = C.getCalleeName(CE);
  if (FName.empty())
    return;

  if (CE->getNumArgs() != 1 && CE->getNumArgs() != 2)
    return;

  auto InitI = InitLockFunctions.find(FName);
  if (InitI != InitLockFunctions.end()) {
    const auto &Spec = InitI->second;
    const MemRegion *LockR = C.getSVal(CE->getArg(Spec.ArgNo)).getAsRegion();
    if (!LockR)
      return;

    SVal OldLState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (OldLState.isConstant(Locked) || OldLState.isConstant(Unlocked))
      state = state->bindLoc(PthreadLockMutexStateTrait, LockR, UndefinedVal());
    else
      state = state->bindLoc(PthreadLockMutexStateTrait, LockR, Unlocked);
    C.addTransition(state);
    return;
  }

  auto AcquireI = AcquireLockFunctions.find(FName);
  if (AcquireI != AcquireLockFunctions.end()) {
    const auto &Spec = AcquireI->second;
    const MemRegion *LockR = C.getSVal(CE->getArg(Spec.ArgNo)).getAsRegion();
    if (!LockR)
      return;

    SVal X = C.getSVal(CE);
    if (X.isUnknownOrUndef())
      return;
    DefinedSVal retVal = X.castAs<DefinedSVal>();

    ProgramStateRef lockSucc = state;
    if (Spec.IsTrylock) {
      // Bifurcate the state, and allow a mode where the lock acquisition fails.
      ProgramStateRef lockFail;
      switch (Spec.Semantics) {
      case PthreadSemantics:
        std::tie(lockFail, lockSucc) = state->assume(retVal);
        break;
      case XNUSemantics:
        std::tie(lockSucc, lockFail) = state->assume(retVal);
        break;
      default:
        llvm_unreachable("Unknown tryLock locking semantics");
      }
      assert(lockFail && lockSucc);
      C.addTransition(lockFail);
    } else  if (Spec.Semantics == PthreadSemantics) {
      // Assume that the return value was 0.
      lockSucc = state->assume(retVal, false);
      assert(lockSucc);
    } else {
      // XNU locking semantics return void on non-try locks
      assert((Spec.Semantics == XNUSemantics) && "Unknown locking semantics");
      lockSucc = state;
    }
    lockSucc = lockSucc->bindLoc(PthreadLockMutexStateTrait, LockR, Locked);
    C.addTransition(lockSucc);
    return;
  }

  auto ReleaseI = ReleaseLockFunctions.find(FName);
  if (ReleaseI != ReleaseLockFunctions.end()) {
    const auto &Spec = ReleaseI->second;
    const MemRegion *LockR = C.getSVal(CE->getArg(Spec.ArgNo)).getAsRegion();
    if (!LockR)
      return;

    SVal OldLState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (OldLState.isConstant(Destroyed))
      state = state->bindLoc(PthreadLockMutexStateTrait, LockR, UndefinedVal());
    else
      state = state->bindLoc(PthreadLockMutexStateTrait, LockR, Unlocked);
    C.addTransition(state);
    return;
  }

  auto DestroyI = DestroyLockFunctions.find(FName);
  if (DestroyI != DestroyLockFunctions.end()) {
    const auto &Spec = DestroyI->second;
    const MemRegion *LockR = C.getSVal(CE->getArg(Spec.ArgNo)).getAsRegion();
    if (!LockR)
      return;

    state = state->bindLoc(PthreadLockMutexStateTrait, LockR, Destroyed);
    C.addTransition(state);
    return;
  }
}


namespace {
class PthreadLockStackModel
    : public Checker<check::ASTDecl<TranslationUnitDecl>,
                     check::PostStmt<CallExpr>> {
public:
  void checkASTDecl(const TranslationUnitDecl *D, AnalysisManager &AMgr,
                    BugReporter &BR) const;
  void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;
};
} // end anonymous namespace

void PthreadLockStackModel::checkASTDecl(const TranslationUnitDecl *D,
                                         AnalysisManager &AMgr,
                                         BugReporter &BR) const {
  ASTContext &ACtx = AMgr.getASTContext();
  PthreadLockStackPointerTrait.initialize("PthreadLockStackPointer",
                                          ACtx.getPointerType(ACtx.VoidPtrTy));
}

void PthreadLockStackModel::checkPostStmt(const CallExpr *CE,
                                          CheckerContext &C) const {
  ProgramStateRef state = C.getState();
  StringRef FName = C.getCalleeName(CE);
  if (FName.empty())
    return;

  if (CE->getNumArgs() != 1 && CE->getNumArgs() != 2)
    return;

  auto AcquireI = AcquireLockFunctions.find(FName);
  if (AcquireI != AcquireLockFunctions.end()) {
    const auto &Spec = AcquireI->second;
    SVal LockR = C.getSVal(CE->getArg(Spec.ArgNo));

    // Record that the lock was acquired:
    SValBuilder &SVB = C.getSValBuilder();
    // 1. Increment the current stack pointer location.
    // In order to simplify code, we start at offset 1.
    SVal StackPointer = state->getSVal(PthreadLockStackPointerTrait);
    StackPointer = SVB.evalBinOp(state, BO_Add, StackPointer,
                                 SVB.makeIntValWithPtrWidth(1, true),
                                 PthreadLockStackPointerTrait.getTraitType());
    state = state->bindLoc(PthreadLockStackPointerTrait, StackPointer);
    // 2. Bind the mutex to the current stack pointer location,
    state = state->bindLoc(StackPointer.castAs<Loc>(), LockR);
    C.addTransition(state);
    return;
  }

  auto ReleaseI = ReleaseLockFunctions.find(FName);
  if (ReleaseI != ReleaseLockFunctions.end()) {
    const auto &Spec = ReleaseI->second;
    const MemRegion *LockR = C.getSVal(CE->getArg(Spec.ArgNo)).getAsRegion();
    if (!LockR)
      return;

    // Record that the lock was released.
    SValBuilder &SVB = C.getSValBuilder();
    ASTContext &ACtx = SVB.getContext();
    // Essentially, just decrement the current stack pointer location.
    SVal StackPointer = state->getSVal(PthreadLockStackPointerTrait);
    StackPointer = SVB.evalBinOp(state, BO_Sub, StackPointer,
                                 SVB.makeIntValWithPtrWidth(1, true),
                                 ACtx.getPointerType(ACtx.VoidPtrTy));
    state = state->bindLoc(PthreadLockStackPointerTrait, StackPointer);
    C.addTransition(state);
    return;
  }
}


namespace {
class PthreadLockChecker : public Checker<check::PreStmt<CallExpr>> {
  mutable std::unique_ptr<BugType> BT_doublelock;
  mutable std::unique_ptr<BugType> BT_doubleunlock;
  mutable std::unique_ptr<BugType> BT_destroylock;
  mutable std::unique_ptr<BugType> BT_initlock;
  mutable std::unique_ptr<BugType> BT_lor;

  void reportBug(std::unique_ptr<BugType> &BT, const Expr *E, CheckerContext &C,
                 StringRef BugName, StringRef Message) const;

public:
  void checkPreStmt(const CallExpr *CE, CheckerContext &C) const;
};
} // end anonymous namespace

void PthreadLockChecker::reportBug(std::unique_ptr<BugType> &BT, const Expr *E,
                                   CheckerContext &C, StringRef BugName,
                                   StringRef Message) const {
  if (!BT)
    BT.reset(new BugType(this, BugName, "Lock checker"));
  ExplodedNode *N = C.generateErrorNode();
  if (!N)
    return;
  auto report = llvm::make_unique<BugReport>(*BT, Message, N);
  report->addRange(E->getSourceRange());
  C.emitReport(std::move(report));
}

void PthreadLockChecker::checkPreStmt(const CallExpr *CE,
                                      CheckerContext &C) const {
  ProgramStateRef state = C.getState();
  StringRef FName = C.getCalleeName(CE);
  if (FName.empty())
    return;

  if (CE->getNumArgs() != 1 && CE->getNumArgs() != 2)
    return;

  auto InitI = InitLockFunctions.find(FName);
  if (InitI != InitLockFunctions.end()) {
    const auto &Spec = InitI->second;
    const Expr *LockE = CE->getArg(Spec.ArgNo);
    const MemRegion *LockR = C.getSVal(LockE).getAsRegion();
    if (!LockR)
      return;

    SVal LState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (!LState.isConstant() || LState.isConstant(Destroyed))
      return;

    StringRef Message;

    if (LState.isConstant(Locked)) {
      Message = "This lock is still being held";
    } else {
      Message = "This lock has already been initialized";
    }

    reportBug(BT_initlock, LockE, C, "Init invalid lock", Message);
  }

  auto AcquireI = AcquireLockFunctions.find(FName);
  if (AcquireI != AcquireLockFunctions.end()) {
    const auto &Spec = AcquireI->second;
    const Expr *LockE = CE->getArg(Spec.ArgNo);
    const MemRegion *LockR = C.getSVal(LockE).getAsRegion();
    if (!LockR)
      return;

    SVal LState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (LState.isConstant(Locked)) {
      reportBug(BT_doublelock, LockE, C, "Double locking",
                "This lock has already been acquired");
      return;
    }
    if (LState.isConstant(Destroyed)) {
      reportBug(BT_destroylock, LockE, C, "Use destroyed lock",
                "This lock has already been destroyed");
      return;
    }
    return;
  }

  auto ReleaseI = ReleaseLockFunctions.find(FName);
  if (ReleaseI != ReleaseLockFunctions.end()) {
    const auto &Spec = ReleaseI->second;
    const Expr *LockE = CE->getArg(Spec.ArgNo);
    const MemRegion *LockR = C.getSVal(LockE).getAsRegion();
    if (!LockR)
      return;

    SVal LState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (LState.isConstant(Unlocked)) {
      reportBug(BT_doubleunlock, LockE, C, "Double unlocking",
                "This lock has already been unlocked");
      return;
    }

    if (LState.isConstant(Destroyed)) {
      reportBug(BT_destroylock, LockE, C, "Use destroyed lock",
                "This lock has already been destroyed");
      return;
    }

    const MemRegion *StackPointerR =
        state->getSVal(PthreadLockStackPointerTrait).getAsRegion();
    assert(StackPointerR);

    // Below offset 0 on our stack lies the stack frame of the caller function
    // of the top-level function from which we've started our analysis. While
    // we've no problem symbolicating the mutex we last locked in that imaginary
    // caller code, our store model, which thinks of all different base regions
    // as certainly-different, would make us think we're unlocking a different
    // mutex, which is most likely incorrect, so we avoid this check.
    RegionOffset RO = StackPointerR->getAsOffset();
    assert(!RO.hasSymbolicOffset());
    if (RO.getOffset() <= 0) // Recall that we start from 1.
      return;

    const MemRegion *firstLockR = state->getSVal(StackPointerR).getAsRegion();
    if (firstLockR && firstLockR != LockR) {
      reportBug(BT_lor, LockE, C, "Lock order reversal",
                "This was not the most recently acquired lock. Possible "
                "lock order reversal");
      return;
    }

    return;
  }

  auto DestroyI = DestroyLockFunctions.find(FName);
  if (DestroyI != DestroyLockFunctions.end()) {
    const auto &Spec = DestroyI->second;
    const Expr *LockE = CE->getArg(Spec.ArgNo);
    const MemRegion *LockR = C.getSVal(LockE).getAsRegion();
    if (!LockR)
      return;

    SVal LState = state->getSVal(PthreadLockMutexStateTrait, LockR);
    if (!LState.isConstant() || LState.isConstant(Unlocked))
      return;

    StringRef Message;

    if (LState.isConstant(Locked)) {
      Message = "This lock is still locked";
    } else {
      Message = "This lock has already been destroyed";
    }

    reportBug(BT_destroylock, LockE, C, "Destroy invalid lock", Message);
    return;
  }
}

void ento::registerPthreadLockCheckerV2(CheckerManager &mgr) {
  mgr.registerChecker<PthreadLockMutexStateModel>();
  mgr.registerChecker<PthreadLockStackModel>();
  mgr.registerChecker<PthreadLockChecker>();
}
