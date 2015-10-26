//===- FunctionCallSummary.h - Summary for function calls ---------*- C++ -*--//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
/// \file This file defines FunctionCallSummarySet and FunctionCallBranchSummary
/// which represent summary for the whole function declaration or a single
/// branch. (C, C++).
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_STATICANALYZER_FUNCTIONCALLSUMMARY_H
#define LLVM_CLANG_STATICANALYZER_FUNCTIONCALLSUMMARY_H

#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/ExprObjC.h"
#include "clang/Analysis/AnalysisContext.h"
#include "clang/Basic/SourceManager.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExplodedGraph.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "llvm/ADT/PointerIntPair.h"
#include "llvm/ADT/FoldingSet.h"
#include <set>

namespace clang {

namespace ento {

class NodeBuilder;
class ExplodedNode;

class ExportMap {

  typedef llvm::DenseMap<const SymbolConjured *, const SymbolConjured *>
          ConjSymbolMap;
  typedef llvm::DenseMap<const CXXTempObjectRegion *, const CXXTempObjectRegion *>
          TempRegionMap;

  const unsigned OriginalBlockCount;
  unsigned NewBlockCount;

  unsigned getBlockCount(unsigned Count);

  ConjSymbolMap ConjSymMap;
  TempRegionMap TempRegMap;

public:
  ExportMap(unsigned BlockCount)
      : OriginalBlockCount(BlockCount + 1), NewBlockCount(BlockCount),
        ConjSymMap(), TempRegMap() {}

  unsigned updatedBlockCount() const { return NewBlockCount; }

  const SymbolConjured *get(const SymbolConjured *ConjSym,
                            CallEventRef<CallEvent> Call);
  const CXXTempObjectRegion *get(const CXXTempObjectRegion *TempReg,
                                 CallEventRef<CallEvent> Call);
};

class Summarizer {
private:
  CallEventRef<CallEvent> Call;
  ExportMap &ExpMap;
  const StackFrameContext *CalleeSFC;
  CheckerManager &CMgr;

  // This state contains temporary bindings of explicit and implicit
  // argument values to their respective stack regions.
  ProgramStateRef TempState;

  typedef llvm::DenseMap<const MemRegion *, SVal> RegionCacheTy;
  typedef llvm::DenseMap<SymbolRef, SVal> SymbolCacheTy;
  typedef llvm::DenseMap<SVal, SVal> SValCacheTy;

  RegionCacheTy RegionCache;
  SymbolCacheTy SymbolCache;
  SValCacheTy SValCache;

  SVal composeRegionUncached(const MemRegion *);
  SVal composeSymbolUncached(SymbolRef);
  SVal composeSValUncached(SVal);

  SVal composeRegion(const MemRegion *R) {
    if (!R)
      return UnknownVal();
    if (RegionCache.count(R))
      return RegionCache[R];
    SVal Ret = composeRegionUncached(R);
    RegionCache[R] = Ret;
    return Ret;
  }
  SVal composeSymbol(SymbolRef S) {
    if (!S)
      return UnknownVal();
    if (SymbolCache.count(S))
      return SymbolCache[S];
    SVal Ret = composeSymbolUncached(S);
    SymbolCache[S] = Ret;
    return Ret;
  }
  SVal composeSVal(SVal V) {
    if (V.isUnknownOrUndef())
      return V;
    if (SValCache.count(V))
      return SValCache[V];
    SVal Ret = composeSValUncached(V);
    SValCache[V] = Ret;
    return Ret;
  }

public:
  Summarizer(CallEventRef<CallEvent> call, ExportMap &expMap,
             const StackFrameContext *SFC, CheckerManager &cMgr)
      : Call(call), ExpMap(expMap), CalleeSFC(SFC), CMgr(cMgr),
        TempState(getState()) {}

  const CallEvent &getCall() const { return *Call; }
  ProgramStateRef getState() const { return Call->getState(); }

  Summarizer cloneWithState(ProgramStateRef State) const {
    return Summarizer(Call->cloneWithState(State), ExpMap, CalleeSFC, CMgr);
  }

  template <typename T> T actualize(const T&);
  template <typename T> T actualizeAll(const T &);

  const MemRegion *actualizeRegion(const MemRegion *);
  SymbolRef actualizeSymbol(SymbolRef);
  SVal actualizeSVal(SVal);
};

class FunctionCallBranchSummary;

class FunctionCallSummary
    : public std::vector<const FunctionCallBranchSummary *> {
public:
  bool isValid;
  size_t NodesProceed;
  FunctionCallSummary() : isValid(false), NodesProceed(0) {}
};

class FunctionCallBranchSummary {
  CheckerSummaries CheckerSummary;
  const ExplodedNode *CorrespondingNode;

public:
  FunctionCallBranchSummary(ProgramStateRef state,
                            const ExplodedNode *FinishNode, SubEngine *EE);
  static ProgramStateRef saveReturnValue(ProgramStateRef state, SVal Ret);
  CheckerSummaries &getCheckerSummary() { return CheckerSummary; }
  const CheckerSummaries &getCheckerSummary() const { return CheckerSummary; }

  const ExplodedNode *getCorrespondingNode() const { return CorrespondingNode; }
  void setCorrespondingNode (const ExplodedNode *Node) {
    CorrespondingNode = Node;
  }

  friend void CallFunction(ExprEngine &Eng, const CallEvent &Call,
                           NodeBuilder &Bldr, ento::ExplodedNode *Pred,
                           const StackFrameContext *CalleeSFC,
                           ProgramStateRef State,
                           const FunctionCallSummary &CS);
};


typedef llvm::DenseMap<const Decl *, FunctionCallSummary> CallSummaryMap;

void CallFunction(ExprEngine &Eng, const CallEvent &Call, NodeBuilder &Bldr,
                  ExplodedNode *Pred, const StackFrameContext *CalleeSFC,
                  ProgramStateRef State, const FunctionCallSummary &CS);
}} // end namespace clang::ento

#endif // LLVM_CLANG_STATICANALYZER_FUNCTIONCALLSUMMARY_H
