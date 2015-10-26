//=== ConstModifiedChecker.cpp - Modification of constant data--*- C++ -*--===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This files defines ConstModifiedChecker, a checker that checks for
// modifications of constant data via pointer.
// This check corresponds to CERT EXP05-C.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "llvm/ADT/DenseMap.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"
#include "clang/AST/ExprCXX.h"

using namespace clang;
using namespace ento;
using namespace llvm;

struct Access {
  const Stmt *Statement;
  const ExplodedNode *Node;

  Access(const Stmt *S = NULL, const ExplodedNode *N = NULL)
      : Statement(S), Node(N) {}

  void Profile(FoldingSetNodeID &ID) const {
    ID.AddPointer(Statement);
    ID.AddPointer(Node);
  }

  bool operator==(const Access &Rhs) const {
    return Statement == Rhs.Statement && Node == Rhs.Node;
  }

  Access Actualize(Summarizer &S) const {
    return Access(Statement, Node);
  }
};
typedef SummaryMap<const MemRegion *, Access> AccessMap;


namespace clang {
namespace ento {

template<> Access Summarizer::actualizeAll<Access>(const Access &Acc) {
  return Acc;
}

template<> const ExplodedNode *
Summarizer::actualizeAll<const ExplodedNode *>(const ExplodedNode * const &N) {
  return N;
}

}} // end namespace clang::ento

REGISTER_MAP_WITH_PROGRAMSTATE(CastedFromConst, \
                               const MemRegion *, const ExplodedNode *)
REGISTER_SET_WITH_PROGRAMSTATE(NonConstPointersL, const MemRegion *)
REGISTER_SET_WITH_PROGRAMSTATE(NonConstPointersNL, const MemRegion *)
REGISTER_SET_WITH_PROGRAMSTATE(ConstPointersL, const MemRegion *)
REGISTER_SET_WITH_PROGRAMSTATE(ConstPointersNL, const MemRegion *)
REGISTER_MAP_WITH_PROGRAMSTATE(WritedLocations, const MemRegion *, Access)

namespace {
class ConstModifiedChecker : public Checker< check::PostStmt<CastExpr>,
                                             check::Location,
                                             check::PostStmt<CallExpr>,
                                             check::PostStmt<UnaryOperator>,
                                             check::PostStmt<CXXMemberCallExpr>,
                                             eval::SummaryApply,
                                             check::EndAnalysis> {
  mutable OwningPtr<BugType> BT;
  typedef std::map<const ExplodedNode *, const ExplodedNode *> NodeMapTy;
  // XXX: Place it into state or engine?
  mutable NodeMapTy NodeMap;
public:
  void checkPostStmt(const CastExpr *CE, CheckerContext &C) const;
  void checkPostStmt(const CXXMemberCallExpr *Call, CheckerContext &C) const;
  void checkPostStmt(const UnaryOperator *UOp, CheckerContext &C) const;
  void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;
  void checkLocation(SVal SV, bool isLoad, const Stmt *S,
                     CheckerContext &C) const;

  void evalSummaryApply(Summarizer &S, const CallEvent &Call, const void *,
                        CheckerContext &C,
                        ProgramStateRef CalleeEndState) const;

  void checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                        ExprEngine &Eng) const;

  void printState(raw_ostream &Out, ProgramStateRef State,
                  const char *NL, const char *Sep) const;

  const void *getTag() const {
    static int X = 0;
    return &X;
  }

private:
  ExplodedNode *emitReport(CheckerContext &C, ProgramStateRef State,
                           const Stmt *S, const MemRegion *MR,
                           const ExplodedNode *SummaryNode) const;

  /// The bug visitor which allows us to print extra diagnostics along the
  /// BugReport path. It shows a place where cast happened.
  class ConstModifiedBugVisitor :
      public BugReporterVisitorImpl<ConstModifiedBugVisitor> {
    // The allocated region tracked by the main analysis.
    const MemRegion *MR;
  public:
    ConstModifiedBugVisitor(const MemRegion *mr) : MR(mr) {}

    virtual ~ConstModifiedBugVisitor() {}

    void Profile(llvm::FoldingSetNodeID &ID) const {
      static int X = 0;
      ID.AddPointer(&X);
      ID.AddPointer(MR);
    }

    PathDiagnosticPiece *VisitNode(const ExplodedNode *N,
                                   const ExplodedNode *PrevN,
                                   BugReporterContext &BRC,
                                   BugReport &BR);

    PathDiagnosticPiece* getEndPath(BugReporterContext &BRC,
                                    const ExplodedNode *EndPathNode,
                                    BugReport &BR) {
      PathDiagnosticLocation L =
        PathDiagnosticLocation::createEndOfPath(EndPathNode,
                                                BRC.getSourceManager());
      return new PathDiagnosticEventPiece(L, BR.getDescription(), true);
    }
  };

};
}

static QualType getLocationType(const MemRegion *MR) {
  if (isa<AllocaRegion>(MR))
    return QualType();
  QualType T;
  if (isa<SymbolicRegion>(MR) ||
      isa<CodeTextRegion>(MR)) {
    if (const TypedRegion *TR = dyn_cast<TypedRegion>(MR)) {
      T = TR->getLocationType();
    } else {
      const SymbolicRegion *SR = cast<SymbolicRegion>(MR);
      T = SR->getSymbol()->getType();
    }
    if (T->isAnyPointerType() || T->isReferenceType())
      T = T->getPointeeType();
  } else if (const TypedValueRegion *TVR = dyn_cast<TypedValueRegion>(MR)) {
    T = TVR->getValueType();
  }
  return T.getCanonicalType();
}

static bool isConstInState(const MemRegion *MR, ProgramStateRef State) {
  return State->contains<ConstPointersL>(MR) || State->contains<ConstPointersNL>(MR);
}

static bool isNonConstInState(const MemRegion *MR, ProgramStateRef State) {
  return State->contains<NonConstPointersL>(MR) ||
      State->contains<NonConstPointersNL>(MR);
}

static ProgramStateRef addConstRegion(const MemRegion *MR,
                                      ProgramStateRef State) {
  return MR->hasStackStorage() ? State->add<ConstPointersL>(MR)
                               : State->add<ConstPointersNL>(MR);
}

static ProgramStateRef addNonConstRegion(const MemRegion *MR,
                                         ProgramStateRef State) {
  return MR->hasStackStorage() ? State->add<NonConstPointersL>(MR)
                               : State->add<NonConstPointersNL>(MR);
}

static ProgramStateRef addMemRegion(const Expr *E, CheckerContext &C,
                                    ProgramStateRef state = NULL) {

  if (!state)
    state = C.getState();
  SVal SV = state->getSVal(E, C.getLocationContext());
  const MemRegion *MR = SV.getAsRegion();
  if (!MR)
    return state;
  if (isa<FunctionTextRegion>(MR))
    return state;

  const SubRegion *SR = dyn_cast<SubRegion>(MR);
  bool IsMutable = false;
  const MemRegion *UpperConst = NULL;
  const MemRegion *UpperNonConst = NULL;
  while (SR) {
    if (isConstInState(SR, state) || isNonConstInState(SR, state))
      return state;
    QualType T = getLocationType(SR);
    // AllocaRegion is never const-qualified.
    if (!isa<AllocaRegion>(SR) && T.isConstant(C.getASTContext())) {
      if (!IsMutable) {
        UpperConst = SR;
      }
    } else {
      UpperNonConst = SR;
      if (const FieldRegion *FR = dyn_cast<FieldRegion>(SR))
        if (FR->getDecl()->isMutable())
          IsMutable = true;
    }
    SR = dyn_cast<SubRegion>(SR->getSuperRegion());
  }

  if (UpperConst)
    state = addConstRegion(UpperConst, state);
  else
    state = addNonConstRegion(UpperNonConst, state);
  return state;
}


enum ConstType { CT_Const, CT_NonConst, CT_Unknown };

static ConstType getConstStatus(const MemRegion *MR, ProgramStateRef State) {
  const SubRegion *Base = cast<SubRegion>(MR);
  do {
    MR = Base;
    if (isConstInState(MR, State))
      return CT_Const;
    if (isNonConstInState(MR, State))
      return CT_NonConst;
    if (isa<CXXTempObjectRegion>(MR))
      return CT_NonConst;
    if (const FieldRegion *FR = dyn_cast<FieldRegion>(MR)) {
      const FieldDecl *FD = FR->getDecl();
      if (FD->isMutable())
        return CT_NonConst;
      if (FD->getType().isConstQualified())
        return CT_Const;
    }
    Base = dyn_cast<SubRegion>(Base->getSuperRegion());
  } while (Base);
  return CT_Unknown;
}


void ConstModifiedChecker::checkPostStmt(const CXXMemberCallExpr *Call,
                                         CheckerContext &C) const {
  C.addTransition(addMemRegion(Call->getImplicitObjectArgument(), C));
}

void ConstModifiedChecker::checkPostStmt(const UnaryOperator *UOp,
                                         CheckerContext &C) const {
  if (UOp->getOpcode() == UO_AddrOf)
    C.addTransition(addMemRegion(UOp->getSubExpr(), C));
}

void ConstModifiedChecker::checkPostStmt(const CallExpr *CE,
                                         CheckerContext &C) const {
  const FunctionDecl *FDecl = C.getCalleeDecl(CE);
  if (!FDecl)
    return;
  StringRef Name = C.getCalleeName(FDecl);
  if (Name == "malloc" || Name == "calloc" || Name == "realloc" ||
      Name == "memcpy") {
    ProgramStateRef state = C.getState();
    const MemRegion *MR = C.getSVal(CE).getAsRegion();
    if (MR)
      C.addTransition(addNonConstRegion(MR, state));
  }
}

void ConstModifiedChecker::checkPostStmt(const CastExpr *CE,
                                         CheckerContext &C) const {

  const Expr *E = CE->getSubExpr();
  ProgramStateRef state = addMemRegion(E, C);
  state = addMemRegion(CE, C, state);

  const ExplicitCastExpr *ECE = dyn_cast<ExplicitCastExpr>(CE);
  if (ECE) {

    static SimpleProgramPointTag Tag("ConstModifiedChecker : HandleCast");
    QualType OrigTy = E->getType();
    QualType ToTy = ECE->getTypeAsWritten();

    // Pointer cast
    if ((OrigTy->isAnyPointerType() && ToTy->isAnyPointerType()) ||
        // Reference cast
        (ToTy->isReferenceType() && (OrigTy->isReferenceType() || E->isLValue())))
      if (((E->isLValue() && OrigTy.isConstQualified()) ||
          (!E->isLValue() && OrigTy->getPointeeType().isConstQualified())) &&
          !ToTy->getPointeeType().isConstQualified())
        if (const MemRegion *MR = C.getSVal(CE).getAsRegion())
          if (getConstStatus(MR, state) != CT_NonConst) {
            if (const ElementRegion *ER = dyn_cast<ElementRegion>(MR))
              MR = ER->getSuperRegion();
            ExplodedNode *N = C.addTransition(state, &Tag);
            state = state->set<CastedFromConst>(MR, N);
            C.addTransition(state, N);
            return;
          }
  }
  C.addTransition(state);
}

void ConstModifiedChecker::checkLocation(SVal SV, bool isLoad, const Stmt *S,
                                         CheckerContext &C) const {
  if (isLoad)
    return;
  const MemRegion *MR = SV.getAsRegion();
  if (!MR)
    return;
  ProgramStateRef State = C.getState();
  const SubRegion *SR = dyn_cast<SubRegion>(MR);
  while (SR) {
    if (isNonConstInState(SR, State))
      break;
    if (isConstInState(SR, State)) {
      emitReport(C, State, S, MR, NULL);
      break;
    }
    if (const FieldRegion *FR = dyn_cast<FieldRegion>(SR))
      if (FR->getDecl()->isMutable())
        break;
    SR = dyn_cast<SubRegion>(SR->getSuperRegion());
  }

  if (!MR->hasStackStorage() && !State->get<WritedLocations>(MR) &&
      C.getStateManager().getOwningEngine()->getAnalysisManager()
      .getAnalyzerOptions().getIPAMode() == IPAK_Summary) {
    static SimpleProgramPointTag Tag("ConstModified - write");
    ExplodedNode *N = C.addTransition(State, &Tag);
    State = State->set<WritedLocations>(MR, Access(S, N));
    C.addTransition(State, N);
  }
}

static const ExplodedNode *getCastNode(ProgramStateRef State,
                                       const MemRegion *MR) {
  const ExplodedNode *CastNode = NULL;
  const SubRegion *SR = cast<SubRegion>(MR);
  while (!CastNode && SR) {
    const ExplodedNode * const *N = State->get<CastedFromConst>(SR);
    if (N)
      return *N;
    SR = dyn_cast<SubRegion>(SR->getSuperRegion());
  }
  return NULL;
}

ExplodedNode *
ConstModifiedChecker::emitReport(CheckerContext &C, ProgramStateRef State,
                                 const Stmt *S, const MemRegion *MR,
                                 const ExplodedNode *SummaryNode) const {
  const ExplodedNode *CastNode = getCastNode(State, MR);
  // A constant object may be modified directly in some cases
  // (in dtors, for example). But we're not interested in these cases.
  if (!CastNode)
    return NULL;

  ExplodedNode *N = C.addTransition();
  if (N) {
    if (!BT)
      BT.reset(new BugType("Assigning value to const variable",
                           categories::UndefBehavior));
    std::string Message;
    const PrintingPolicy &Policy = C.getASTContext().getPrintingPolicy();
    llvm::raw_string_ostream os(Message);
    os << "Writing to a memory that originally had constant qualifier ";
    std::string VarName = dumpMemRegion(MR, State->getEnvironment(),
                                        Policy, "");
    os << "(";
    if (!VarName.empty())
      os << VarName;
    else
      S->printPretty(os, NULL, Policy);
    os << ") ";
    os.flush();

    BugReport *R = new BugReport(*BT, Message, N);
    R->addVisitor(new ConstModifiedBugVisitor(MR));
    R->addRange(S->getSourceRange());

    while (SummaryNode) {
      R->appendSummaryNode(SummaryNode);
      NodeMapTy::const_iterator I = NodeMap.find(SummaryNode);
      SummaryNode = I == NodeMap.end() ? NULL : I->second;
    }

    R->appendIntermediateSummaryInfo(getTag(), CastNode);
    C.emitReport(R);
  }

  return N;
}

void ConstModifiedChecker::evalSummaryApply(
    Summarizer &S, const CallEvent &Call, const void *,
    CheckerContext &C, ProgramStateRef CalleeEndState) const {
  ProgramStateRef state = C.getState();
  const ExplodedNode *Pred = C.getPredecessor();
  ExplodedNode *Created = NULL;

  const CastedFromConstTy &Casted = CalleeEndState->get<CastedFromConst>();
  const NonConstPointersNLTy &NonConstPtrs =
      CalleeEndState->get<NonConstPointersNL>();
  const ConstPointersNLTy &ConstPtrs = CalleeEndState->get<ConstPointersNL>();
  const WritedLocationsTy &WritedLocs = CalleeEndState->get<WritedLocations>();

  ConstPointersNLTy CPtrsNL = state->get<ConstPointersNL>();
  ConstPointersNLTy::Factory &CFactNL = state->get_context<ConstPointersNL>();
  ConstPointersNLTy CPtrsL = state->get<ConstPointersL>();
  ConstPointersNLTy::Factory &CFactL = state->get_context<ConstPointersL>();
  CastedFromConstTy::Factory &CastF = state->get_context<CastedFromConst>();
  CastedFromConstTy CastedBefore = state->get<CastedFromConst>();

  for (CastedFromConstTy::iterator I = Casted.begin(), E = Casted.end(); I != E;
       ++I) {
    if (I->first->hasStackStorage())
      continue;
    const MemRegion *MR = S.actualizeRegion(I->first);
    const ExplodedNode *CastNode = I->second;
    if (!MR)
      continue;
    if (getConstStatus(MR, state) == CT_NonConst)
      continue;
    CastedBefore = CastF.add(CastedBefore, MR, CastNode);
    if (MR->hasStackStorage())
      CPtrsL = CFactL.add(CPtrsL, MR);
    else
      CPtrsNL = CFactNL.add(CPtrsNL, MR);
  }
  state = state->set<CastedFromConst>(CastedBefore);

  WritedLocationsTy NewWrited = state->get<WritedLocations>();
  WritedLocationsTy::Factory &WritedF = state->get_context<WritedLocations>();
  for (WritedLocationsTy::iterator I = WritedLocs.begin(), E = WritedLocs.end();
       I != E; ++I) {
    const Access &Acc = I->second;
    bool Reported = false;
    const MemRegion *MR = S.actualizeRegion(I->first);
    bool ParseLater = MR && !MR->hasStackStorage();
    if (MR) {
      const SubRegion *SR = dyn_cast<SubRegion>(MR);
      while (SR) {
        if (MR->hasStackStorage() && isNonConstInState(SR, state)) {
          ParseLater = false;
          break;
        }
        if (isConstInState(SR, state)) {
          const CXXDestructorCall *DC = dyn_cast<CXXDestructorCall>(&Call);
          const MemRegion *This = DC ? DC->getCXXThisVal().getAsRegion() : NULL;
          if (!(DC && This && (SR == This || SR->isSubRegionOf(This)))) {
            Created = emitReport(C, state, Acc.Statement, MR, Acc.Node);
            Reported = true;
            break;
          }
        }

        if (const FieldRegion *FR = dyn_cast<FieldRegion>(SR))
          if (FR->getDecl()->isMutable())
            break;
        SR = dyn_cast<SubRegion>(SR->getSuperRegion());
      }
    }
    if (!Reported && ParseLater) {
      NodeMap[Pred] = Acc.Node;
      NewWrited = WritedF.add(NewWrited, MR, Access(Acc.Statement, Pred));
    }
  }
  state = state->set<WritedLocations>(NewWrited);

  NonConstPointersLTy NCPtrsL = state->get<NonConstPointersL>();
  NonConstPointersLTy::Factory &NCFactL =
      state->get_context<NonConstPointersL>();
  NonConstPointersNLTy NCPtrsNL = state->get<NonConstPointersNL>();
  NonConstPointersNLTy::Factory &NCFactNL =
      state->get_context<NonConstPointersNL>();

  for (NonConstPointersNLTy::iterator I = NonConstPtrs.begin(),
       E = NonConstPtrs.end(); I != E; ++I) {
    const MemRegion *MR = S.actualizeRegion(*I);
    if (!MR)
      continue;
    if (getConstStatus(MR, state) != CT_Const) {
      if (MR->hasStackStorage())
        NCPtrsL = NCFactL.add(NCPtrsL, MR);
      else
        NCPtrsNL = NCFactNL.add(NCPtrsNL, MR);
    }
  }
  state = state->set<NonConstPointersL>(NCPtrsL);
  state = state->set<NonConstPointersNL>(NCPtrsNL);

  for (ConstPointersNLTy::iterator I = ConstPtrs.begin(), E = ConstPtrs.end();
       I != E; ++I) {
    const MemRegion *MR = S.actualizeRegion(*I);
    if (!MR)
      continue;
    if (getConstStatus(MR, state) != CT_NonConst) {
      if (MR->hasStackStorage())
        CPtrsL = CFactL.add(CPtrsL, MR);
      else
        CPtrsNL = CFactNL.add(CPtrsNL, MR);
    }
  }
  state = state->set<ConstPointersL>(CPtrsL);
  state = state->set<ConstPointersNL>(CPtrsNL);

  C.addTransition(state, Created);
}


void ConstModifiedChecker::printState(raw_ostream &Out, ProgramStateRef state,
                                      const char *NL, const char *Sep) const {

  ConstPointersLTy ConstPtsL = state->get<ConstPointersL>();
  ConstPointersNLTy ConstPtsNL = state->get<ConstPointersNL>();
  NonConstPointersLTy NonConstPtsL = state->get<NonConstPointersL>();
  NonConstPointersNLTy NonConstPtsNL = state->get<NonConstPointersNL>();
  CastedFromConstTy Casted = state->get<CastedFromConst>();

  if (ConstPtsL.isEmpty() && ConstPtsNL.isEmpty() &&
      NonConstPtsL.isEmpty() && NonConstPtsNL.isEmpty() && Casted.isEmpty())
    return;

  Out << Sep << "ConstModifiedChecker:" << NL;

  if (!ConstPtsL.isEmpty()) {
    Out << "Constant pointers - local:" << NL;
    for (ConstPointersLTy::iterator I = ConstPtsL.begin(), E = ConstPtsL.end();
         I != E; ++I) {
      (*I)->dumpToStream(Out);
      Out << NL;
    }
  }

  if (!ConstPtsNL.isEmpty()) {
    Out << "Constant pointers - non-local:" << NL;
    for (ConstPointersNLTy::iterator I = ConstPtsNL.begin(),
         E = ConstPtsNL.end(); I != E; ++I) {
      (*I)->dumpToStream(Out);
      Out << NL;
    }
  }

  if (!NonConstPtsL.isEmpty()) {
    Out << "Non-Constant pointers - local:" << NL;
    for (NonConstPointersLTy::iterator I = NonConstPtsL.begin(),
         E = NonConstPtsL.end(); I != E; ++I) {
      (*I)->dumpToStream(Out);
      Out << NL;
    }
  }

  if (!NonConstPtsNL.isEmpty()) {
    Out << "Non-Constant pointers - non-local:" << NL;
    for (NonConstPointersNLTy::iterator I = NonConstPtsNL.begin(),
         E = NonConstPtsNL.end(); I != E; ++I) {
      (*I)->dumpToStream(Out);
      Out << NL;
    }
  }

  if (!Casted.isEmpty()) {
    Out << "Casted from constant pointers:" << NL;
    for (CastedFromConstTy::iterator I = Casted.begin(), E = Casted.end();
         I != E; ++I) {
      I->first->dumpToStream(Out);
      Out << NL;
    }
  }
}

void ConstModifiedChecker::checkEndAnalysis(ExplodedGraph &G, BugReporter &BR,
                                            ExprEngine &Eng) const {
/*  const Decl *D = &G.nodes_begin()->getCodeDecl();
  CallSummaryMap::iterator I = Eng.getCallSummaries().find(D);
  if (I == Eng.getCallSummaries().end())
    return;
  FunctionCallSummary &FCS = I->second;
  if (!FCS.isValid)
    return;
  std::set<const ExplodedNode *> SummNodes;
  for (FunctionCallSummary::iterator FI = FCS.begin(), FE = FCS.end(); FI != FE;
       ++FI)
    SummNodes.insert((*FI)->getCorrespondingNode());

  for (ExplodedGraph::node_iterator I = G.nodes_begin(), E = G.nodes_end();
       I != E; ++I) {
    ProgramStateRef State = I->getState()->remove<NonConstPointersL>();
    State = State->remove<ConstPointersL>();
    if (!SummNodes.count(&*I)) {
      State = State->remove<CastedFromConst>();
      State = State->remove<NonConstPointersNL>();
      State = State->remove<ConstPointersNL>();
      State = State->remove<WritedLocations>();
    }
    I->setState(State);
  }*/
}

void ento::registerConstModifiedChecker(CheckerManager &mgr) {
  mgr.registerChecker<ConstModifiedChecker>();
}

PathDiagnosticPiece *
ConstModifiedChecker::ConstModifiedBugVisitor::VisitNode(
    const ExplodedNode *N, const ExplodedNode *PrevN, BugReporterContext &BRC,
    BugReport &BR) {

  const Stmt *S = NULL;
  std::string Msg;
  StackHintGeneratorForMemRegion *StackHint = 0;

  // Retrieve the associated statement.
  ProgramPoint ProgLoc = N->getLocation();
  if (Optional<StmtPoint> SP = ProgLoc.getAs<StmtPoint>()) {
    S = SP->getStmt();
  } else if (Optional<CallExitEnd> Exit = ProgLoc.getAs<CallExitEnd>()) {
    S = Exit->getCalleeContext()->getCallSite();
  } else if (Optional<BlockEdge> Edge = ProgLoc.getAs<BlockEdge>()) {
    // If an assumption was made on a branch, it should be caught
    // here by looking at the state transition.
    S = Edge->getSrc()->getTerminator();
  }

  if (!S)
    return 0;

  // Find out if this is an interesting point and what is the kind.
  const BugReport::IntermediateSummaryInfoTy &BRInfo =
      BR.getIntermediateSummaryInfo();
  if (!BRInfo.empty() && N == BRInfo.begin()->second) {
    llvm::raw_string_ostream os(Msg);
    if (const CastExpr *CastE = dyn_cast<CastExpr>(S)) {
      os << "Cast removes const qualifier here from '";
      CastE->getSubExprAsWritten()->printPretty(
          os, NULL, BRC.getASTContext().getPrintingPolicy());
      os << "'";
      StackHint = new StackHintGeneratorForMemRegion(
          MR, "Returned pointer casted from const memory");
    } else {
      const CallExpr *CallE = cast<CallExpr>(S);
      if (const FunctionDecl *FD = CallE->getDirectCallee()) {
        os << "Const qualifier was casted away while calling '"
           << FD->getNameAsString() << "'";
      } else {
        os << "Const qualifier was casted away";
      }
      StackHint = new StackHintGeneratorForMemRegion(
          MR, "Returned pointer casted from const memory");
    }
  }

  if (Msg.empty())
    return 0;
  assert(StackHint);

  // Generate the extra diagnostic.
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return new PathDiagnosticEventPiece(Pos, Msg, true, StackHint);
}
