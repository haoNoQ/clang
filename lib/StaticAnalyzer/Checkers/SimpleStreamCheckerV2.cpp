//===-- SimpleStreamChecker.cpp -----------------------------------------*- C++ -*--//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// Defines a checker for proper use of fopen/fclose APIs.
//   - If a file has been closed with fclose, it should not be accessed again.
//   Accessing a closed file results in undefined behavior.
//   - If a file was opened with fopen, it must be closed with fclose before
//   the execution ends. Failing to do so results in a resource leak.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"

using namespace clang;
using namespace ento;

namespace {
enum SimpleStreamState { Closed, Opened };
SmartStateTrait SimpleStreamTrait;
typedef SmallVector<SymbolRef, 2> SymbolVector;

class SimpleStreamModel
    : public Checker<check::ASTDecl<TranslationUnitDecl>, check::PostCall,
                     check::PointerEscape> {
  CallDescription OpenFn, CloseFn;
  bool guaranteedNotToCloseFile(const CallEvent &Call) const;

public:
  SimpleStreamModel() : OpenFn("fopen"), CloseFn("fclose") {}

  void checkASTDecl(const TranslationUnitDecl *D, AnalysisManager &AMgr,
                    BugReporter &BR) const;
  void checkPostCall(const CallEvent &Call, CheckerContext &C) const;
  ProgramStateRef checkPointerEscape(ProgramStateRef State,
                                     const InvalidatedSymbols &Escaped,
                                     const CallEvent *Call,
                                     PointerEscapeKind Kind) const;
};
} // end of anonymous namespace

bool SimpleStreamModel::guaranteedNotToCloseFile(
    const CallEvent &Call) const {
  // If it's not in a system header, assume it might close a file.
  if (!Call.isInSystemHeader())
    return false;

  // Handle cases where we know a buffer's /address/ can escape.
  if (Call.argumentsMayEscape())
    return false;

  // Note, even though fclose closes the file, we do not list it here
  // since the checker is modeling the call.
  return true;
}

void SimpleStreamModel::checkASTDecl(const TranslationUnitDecl *D,
                                       AnalysisManager &AMgr,
                                       BugReporter &BR) const {
  // Once the AST context is available, we can express the fact that our trait
  // has type 'int'.
  // FIXME: This is ugly. Maybe make a separate callback, or delay registering
  // checkers until AST is constructed?
  SimpleStreamTrait.initialize("SimpleStream", AMgr.getASTContext().IntTy);
}

void SimpleStreamModel::checkPostCall(const CallEvent &Call,
                                        CheckerContext &C) const {
  if (!Call.isGlobalCFunction())
    return;

  if (Call.isCalled(OpenFn)) {

    // Get the symbolic value corresponding to the file handle.
    SymbolRef FileDesc = Call.getReturnValue().getAsSymbol();
    if (!FileDesc)
      return;

    // Generate the next transition (an edge in the exploded graph).
    ProgramStateRef State = C.getState();
    State = State->bindLoc(SimpleStreamTrait, FileDesc, Opened);
    C.addTransition(State);

  } else if (Call.isCalled(CloseFn)) {

    // Get the symbolic value corresponding to the file handle.
    SymbolRef FileDesc = Call.getArgSVal(0).getAsSymbol();
    if (!FileDesc)
      return;

    // Generate the next transition, in which the stream is closed.
    ProgramStateRef State = C.getState();
    State = State->bindLoc(SimpleStreamTrait, FileDesc, Closed);
    C.addTransition(State);
  }
}

ProgramStateRef SimpleStreamModel::checkPointerEscape(
    ProgramStateRef State, const InvalidatedSymbols &Escaped,
    const CallEvent *Call, PointerEscapeKind Kind) const {
  // If we know that the call cannot close a file, there is nothing to do.
  if (Kind == PSK_DirectEscapeOnCall && guaranteedNotToCloseFile(*Call))
    return State;

  for (auto I = Escaped.begin(), E = Escaped.end(); I != E; ++I) {
    SymbolRef Sym = *I;

    // The symbol escaped. Optimistically, assume that the corresponding file
    // handle will be closed somewhere else.
    // FIXME: We're doing double lookup here, and we could have probably just
    // deleted the binding, because our checker doesn't discriminate between
    // different kind of unknowns.
    if (State->hasAnyBinding(SimpleStreamTrait, Sym))
      State = State->bindLoc(SimpleStreamTrait, Sym, UnknownVal());
  }
  return State;
}

namespace {
class SimpleStreamChecker
    : public Checker<check::PreCall, check::DeadSymbols> {
  CallDescription CloseFn;

  std::unique_ptr<BugType> DoubleCloseBugType;
  std::unique_ptr<BugType> LeakBugType;

  void reportDoubleClose(SymbolRef FileDescSym,
                         const CallEvent &Call,
                         CheckerContext &C) const;

  void reportLeaks(ArrayRef<SymbolRef> LeakedStreams, CheckerContext &C,
                   ExplodedNode *ErrNode) const;

public:
  SimpleStreamChecker();

  /// Process fclose.
  void checkPreCall(const CallEvent &Call, CheckerContext &C) const;

  /// Detect leaks.
  void checkDeadSymbols(SymbolReaper &SymReaper, CheckerContext &C) const;
};
} // end anonymous namespace

SimpleStreamChecker::SimpleStreamChecker() : CloseFn("fclose", 1) {
  // Initialize the bug types.
  DoubleCloseBugType.reset(
      new BugType(this, "Double fclose", "Unix Stream API Error"));

  LeakBugType.reset(
      new BugType(this, "Resource Leak", "Unix Stream API Error"));
  // Sinks are higher importance bugs as well as calls to assert() or exit(0).
  LeakBugType->setSuppressOnSink(true);
}

void SimpleStreamChecker::checkPreCall(const CallEvent &Call,
                                       CheckerContext &C) const {
  if (!Call.isGlobalCFunction())
    return;

  if (!Call.isCalled(CloseFn))
    return;

  // Get the symbolic value corresponding to the file handle.
  SymbolRef FileDesc = Call.getArgSVal(0).getAsSymbol();
  if (!FileDesc)
    return;


  // Check if the stream has already been closed.
  ProgramStateRef State = C.getState();
  SVal Val = State->getSVal(SimpleStreamTrait, FileDesc);
  if (Val.isConstant(Closed)) {
    reportDoubleClose(FileDesc, Call, C);
    return;
  }
}

static bool isLeaked(SymbolRef Sym, ProgramStateRef State) {
  // If a symbol is NULL, assume that fopen failed on this path.
  // A symbol should only be considered leaked if it is non-null.
  ConstraintManager &CMgr = State->getConstraintManager();
  ConditionTruthVal OpenFailed = CMgr.isNull(State, Sym);
  return !OpenFailed.isConstrainedTrue();
}

void SimpleStreamChecker::checkDeadSymbols(SymbolReaper &SymReaper,
                                           CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  SymbolVector LeakedStreams;
  // FIXME: Iterate through trait, not through dead symbols (might be faster)?
  for (auto I = SymReaper.dead_begin(), E = SymReaper.dead_end(); I != E; ++I) {
    SymbolRef FileDesc = *I;
    SVal Val = State->getSVal(SimpleStreamTrait, FileDesc);
    if (!Val.isConstant(Opened))
      continue;

    // Collect leaked symbols.
    if (isLeaked(FileDesc, State))
      LeakedStreams.push_back(FileDesc);
  }

  if (LeakedStreams.empty())
    return;

  ExplodedNode *N = C.generateNonFatalErrorNode(State);
  if (!N)
    return;
  reportLeaks(LeakedStreams, C, N);
}

void SimpleStreamChecker::reportDoubleClose(SymbolRef FileDescSym,
                                            const CallEvent &Call,
                                            CheckerContext &C) const {
  // We reached a bug, stop exploring the path here by generating a sink.
  ExplodedNode *ErrNode = C.generateErrorNode();
  // If we've already reached this node on another path, return.
  if (!ErrNode)
    return;

  // Generate the report.
  auto R = llvm::make_unique<BugReport>(*DoubleCloseBugType,
      "Closing a previously closed file stream", ErrNode);
  R->addRange(Call.getSourceRange());
  R->markInteresting(FileDescSym);
  C.emitReport(std::move(R));
}

void SimpleStreamChecker::reportLeaks(ArrayRef<SymbolRef> LeakedStreams,
                                      CheckerContext &C,
                                      ExplodedNode *ErrNode) const {
  // Attach bug reports to the leak node.
  // TODO: Identify the leaked file descriptor.
  for (SymbolRef LeakedStream : LeakedStreams) {
    auto R = llvm::make_unique<BugReport>(*LeakBugType,
        "Opened file is never closed; potential resource leak", ErrNode);
    R->markInteresting(LeakedStream);
    C.emitReport(std::move(R));
  }
}

void ento::registerSimpleStreamCheckerV2(CheckerManager &mgr) {
  mgr.registerChecker<SimpleStreamModel>();
  mgr.registerChecker<SimpleStreamChecker>();
}
