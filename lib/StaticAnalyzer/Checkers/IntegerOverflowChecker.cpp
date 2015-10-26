//=== IntegerOverflowChecker.cpp - integer overflows checker ----*- C++ -*-===//
//
//           The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
///
/// \file
/// \brief This defines IntegerOverflowChecker, which checks arithmetic
/// operations for integer overflows. This check corresponds to CWE-190.
///
//===----------------------------------------------------------------------===//
//
// Check for overflow performs by checkAdd(), checkSub() and checkMul()
// functions. checkAdd() and checkSub() consist of two parts for signed integer
// overflow check and unsigned integer overflow check(wraparound).
//
// Couple of heuristics were added for FP suppressing. USubHeuristic prevents
// warnings for intentional integer overflow while getting i.e UINT_MAX by
// subtracting 1U from 0U. GlobalsMembersHeuristic suppresses warning if
// arguments of arithmetic operation are global variables or class members.
// Sometimes CSA fails to determine right value for that type of arguments and
// inter-unit analysis assumed to be the best solution of this problem.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/BugReporter/PathDiagnostic.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/FunctionCallSummary.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"

using namespace clang;
using namespace ento;
using namespace nonloc;

namespace {
struct BinExpr {
  SVal Lhs, Rhs;
  const Expr *E;
  const ExplodedNode *N;
  BinExpr(SVal LhsI, SVal RhsI, const Expr *EI, const ExplodedNode *Node)
      : Lhs(LhsI), Rhs(RhsI), E(EI), N(Node) {}

  void Profile(llvm::FoldingSetNodeID &ID) const {
    ID.AddPointer(N);
  }
  SVal getLHS(Summarizer &S) const { return S.actualizeSVal(Lhs); }
  SVal getRHS(Summarizer &S) const { return S.actualizeSVal(Rhs); }
};

class IntegerOverflowChecker : public Checker<check::PostStmt<BinaryOperator>,
                                              check::PostStmt<CXXNewExpr>,
                                              eval::SummaryApply> {
  mutable OwningPtr<BuiltinBug> BT;

  /// Stores SourceLocations in which overflows happened for reducing the amount
  /// of equivalent warnings.
  mutable std::set<const Expr *> OverflowExpr;
  mutable llvm::DenseSet<ValueDecl *> VisitedDecl;
  mutable llvm::DenseMap<SymbolRef, bool> IgnoredMap;
  mutable std::map<const ExplodedNode *, const ExplodedNode *> NodeMap;

  /// Used for compact transfer of output information from functions which
  /// detect overflow to functions which compose warning message.
  struct OutputPack {
    const bool LValueIsTainted;
    const bool RValueIsTainted;
    const bool IsUndef;
    const std::string LValue;
    const std::string RValue;
    std::string Operation;
    OutputPack(bool LValueIsTainted, bool RValueIsTainted, bool IsUndef,
               const std::string &LValue, const std::string &RValue)
        : LValueIsTainted(LValueIsTainted), RValueIsTainted(RValueIsTainted),
          IsUndef(IsUndef), LValue(LValue), RValue(RValue) {}
  };

  struct IntegerOverflowFilter {
    DefaultBool CheckIntegerOverflowDef;
    DefaultBool CheckIntegerOverflowUndef;
  };

  ExplodedNode *reportBug(const std::string &Msg, CheckerContext &C,
                          const Expr *E, const ExplodedNode *SummaryNode) const;

  std::string composeMsg(ProgramStateRef StateNotOverflow, const SVal &Lhs,
                         const SVal &Rhs, const Expr *ExprLhs,
                         const Expr *ExprRhs, bool isSigned, bool isOverflow,
                         BinaryOperator::Opcode *Op, CheckerContext &C) const;

  /// Check if addition of \p Lhs and \p Rhs can overflow.
  Optional<DefinedOrUnknownSVal> checkAdd(CheckerContext &C, const SVal &Lhs,
                                          const SVal &Rhs, QualType BinType,
                                          bool &isOverflow) const;

  /// Check if subtraction of \p Lhs and \p Rhs can overflow.
  Optional<DefinedOrUnknownSVal> checkSub(CheckerContext &C, const SVal &Lhs,
                                          const SVal &Rhs,
                                          const QualType &BinType,
                                          bool &isOverflow) const;

  /// Check if multiplication of \p Lhs and \p Rhs can overflow.
  Optional<DefinedOrUnknownSVal> checkMul(CheckerContext &C, const SVal &Lhs,
                                          const SVal &Rhs,
                                          const QualType &BinType,
                                          bool &isOverflow) const;

  /// \returns dump and constraints of \p Val.
  std::string getSymbolInformation(const SVal &Val, const Expr *E,
                                   CheckerContext &C) const;

  /// We ignore intentional underflow because of subtracting X from zero - the
  /// minimum unsigned value.
  bool makeUSubHeuristics(const BinaryOperator *BO) const;

  bool * getSymStatus(SymbolRef Sym) const  {
    if (Sym)
      return IgnoredMap.count(Sym) ? &IgnoredMap[Sym] : 0;
    return 0;
  }

  bool * getSymStatus(const Stmt *S, ProgramStateRef State,
                      const LocationContext *LCtx) const  {
    if (const Expr *E = dyn_cast_or_null<Expr>(S))
      S = E->IgnoreParens();

    return getSymStatus(State->getSVal(S, LCtx).getAsSymbol());
  }

  void noteBinExpr(CheckerContext &C, const SVal &Lhs, const SVal &Rhs,
                   const Expr *E) const;

  typedef std::vector<BinExpr> BinExprVector;

public:
  IntegerOverflowFilter Filter;

  /// Check addition, multiplication, and subtraction for overflow.
  void checkPostStmt(const BinaryOperator *B, CheckerContext &C) const;

  /// Contains check for new[].
  void checkPostStmt(const CXXNewExpr *NE, CheckerContext &C) const;

  void evalSummaryApply(Summarizer &S, const CallEvent &Call,
                        const void *summary, CheckerContext &C,
                        ProgramStateRef CalleeEndState) const;
};
} // end anonymous namespace

REGISTER_LIST_WITH_PROGRAMSTATE(BinExprList, BinExpr)

void IntegerOverflowChecker::evalSummaryApply(
    Summarizer &S, const CallEvent &Call, const void *summary,
    CheckerContext &C, ProgramStateRef CalleeEndState) const {
  ProgramStateRef State = C.getState();
  ExplodedNode *Created = NULL;

  const BinExprListTy &BinExprSumm = CalleeEndState->get<BinExprList>();
  for (BinExprListTy::iterator I = BinExprSumm.begin(),
       E = BinExprSumm.end(); I != E; ++I) {
    BinExpr BE = *I;
    const BinaryOperator *BO = dyn_cast<BinaryOperator>(BE.E);
    const CXXNewExpr *NewE = dyn_cast<CXXNewExpr>(BE.E);
    if (OverflowExpr.find(BE.E) != OverflowExpr.end())
      continue;
    BinaryOperator::Opcode Op = BO ? BO->getOpcode() : BO_Mul;
    QualType BinType = BO ? BO->getType() : NewE->getArraySize()->getType();
    SVal Lhs = BE.getLHS(S);
    SVal Rhs = BE.getRHS(S);
    Optional<DefinedOrUnknownSVal> CondOverflow;
    ProgramStateRef StateOverflow, StateNotOverflow;

    const Expr *ExprLhs = 0, *ExprRhs = 0;
    if (BO)
      ExprLhs = BO->getLHS(), ExprRhs = BO->getRHS();
    if (Lhs.getAs<loc::ConcreteInt>() && Rhs.getAs<nonloc::ConcreteInt>())
      continue;
    if (Lhs.getAs<nonloc::ConcreteInt>() && Rhs.getAs<loc::ConcreteInt>())
      continue;

    bool isOverflow = false;

    if (Op == BO_Add || Op == BO_AddAssign)
      CondOverflow = checkAdd(C, Lhs, Rhs, BinType, isOverflow);
    else if (Op == BO_Sub || Op == BO_SubAssign) {
      CondOverflow = checkSub(C, Lhs, Rhs, BinType, isOverflow);
    } else if (Op == BO_Mul || Op == BO_MulAssign)
      CondOverflow = checkMul(C, Lhs, Rhs, BinType, isOverflow);


    if (!CondOverflow)
      continue;

    llvm::tie(StateOverflow, StateNotOverflow) = State->assume(*CondOverflow);

    if (!(State->isTainted(Lhs) || State->isTainted(Rhs)) && StateNotOverflow) {
      if (StateOverflow) {
        const ExplodedNode *Pred = C.getPredecessor();
        NodeMap[Pred] = BE.N;
        State = State->add<BinExprList>(BinExpr(Lhs, Rhs, BE.E, Pred));
      }
      continue;
    }

    std::string Msg = composeMsg(StateNotOverflow, Lhs, Rhs, ExprLhs, ExprRhs,
                                 BinType->isSignedIntegerOrEnumerationType(),
                                 isOverflow, &Op, C);
    Created = reportBug(Msg, C, BE.E, BE.N);
  }

  C.addTransition(State, Created);
}

ExplodedNode *
IntegerOverflowChecker::reportBug(const std::string &Msg,
                                       CheckerContext &C,
                                       const Expr *E,
                                       const ExplodedNode *SummaryNode) const {
  static SimpleProgramPointTag Tag("IntegerOverflow_warning");
  ExplodedNode *N = C.addTransition(C.getState(), &Tag);
  if (N) {
    if (!BT)
      BT.reset(new BuiltinBug("Integer overflow",
                            "Arithmetic operation resulted in an overflow"));
    BugReport *R;
    R = new BugReport(*BT, Msg, N);
    while (SummaryNode) {
      R->appendSummaryNode(SummaryNode);
      SummaryNode = NodeMap[SummaryNode];
    }
    C.emitReport(R);
    OverflowExpr.insert(E);
  }
  return N;
}

std::string
IntegerOverflowChecker::composeMsg(ProgramStateRef StateNotOverflow,
                                   const SVal &Lhs, const SVal &Rhs,
                                   const Expr *ExprLhs, const Expr *ExprRhs,
                                   bool isSigned, bool isOverflow,
                                   BinaryOperator::Opcode *Op,
                                   CheckerContext &C) const {
  std::string Msg;
  std::string ErrorType = (!Op || isOverflow) ? "Overflow" : "Underflow";
  if (StateNotOverflow) {
    Msg.assign("Possible integer " + ErrorType + ": ");
    if (C.getState()->isTainted(Lhs))
      Msg.append("left operand is tainted. ");
    else
      Msg.append("right operand is tainted. ");
  } else {
    if (isSigned)
      Msg.assign("Undefined behavior: ");

    Msg.append("Integer " + ErrorType + ". ");
  }
  std::string Operation, Preposition;

  if (!Op || *Op == BO_Mul || *Op == BO_MulAssign) {
    Operation = "Multiplication of ";
    Preposition = " with ";
  } else if (*Op == BO_Add || *Op == BO_AddAssign) {
    Operation = "Addition of ";
    Preposition = " with ";
  } else {
    Operation = "Subtraction of ";
    Preposition = " from ";
  }

  if (Op && (*Op == BO_Sub || (*Op == BO_SubAssign)))
    Msg.append(Operation + getSymbolInformation(Rhs, ExprRhs, C) + Preposition +
               getSymbolInformation(Lhs, ExprLhs, C));
  else
    Msg.append(Operation + getSymbolInformation(Lhs, ExprLhs, C) + Preposition +
               getSymbolInformation(Rhs, ExprRhs, C));

  if (!Op)
    Msg.append(" while memory allocation.");

  return Msg;
}

Optional<DefinedOrUnknownSVal>
IntegerOverflowChecker::checkAdd(CheckerContext &C, const SVal &Lhs,
                                 const SVal &Rhs, QualType BinType,
                                 bool &isOverflow) const {
  SVal CondOverflow;
  ProgramStateRef State = C.getState();
  SValBuilder &SvalBuilder = C.getSValBuilder();
  SVal NullSval = SvalBuilder.makeZeroVal(BinType);
  QualType CondType = SvalBuilder.getConditionType();
  SVal ValArgSum = SvalBuilder.evalBinOp(State, BO_Add, Lhs, Rhs, BinType);
  if (BinType->isSignedIntegerType()) {
    // For positive operands
    // rhs > 0
    SVal CondRhsGtNull = SvalBuilder.evalBinOp(State, BO_GT, Rhs, NullSval,
                                               CondType);
    // lhs > 0
    SVal CondLhsGtNull = SvalBuilder.evalBinOp(State, BO_GT, Lhs, NullSval,
                                               CondType);
    // rhs > 0 && lhs > 0
    SVal CondArgsGtNull = SvalBuilder.evalBinOp(State, BO_And, CondRhsGtNull,
                                                CondLhsGtNull, CondType);
    // lhs+rhs<=0
    SVal CondArgSumLtNull = SvalBuilder.evalBinOp(State, BO_LE, ValArgSum,
                                                  NullSval, CondType);

    SVal CondPositiveOverflow =
        SvalBuilder.evalBinOp(State, BO_And, CondArgsGtNull, CondArgSumLtNull,
                              CondType);
    // For negative operands
    // lhs < 0
    SVal CondLhsLtNull = SvalBuilder.evalBinOp(State, BO_LT, Rhs, NullSval,
                                               CondType);
    // rhs < 0
    SVal CondRhsLtNull = SvalBuilder.evalBinOp(State, BO_LT, Lhs, NullSval,
                                               CondType);
    // rhs < 0 && lhs < 0
    SVal CondArgsLtNull = SvalBuilder.evalBinOp(State, BO_And, CondLhsLtNull,
                                                CondRhsLtNull, CondType);

    // lhs+rhs>=0
    SVal CondArgSumGtNull = SvalBuilder.evalBinOp(State, BO_GE, ValArgSum,
                                                  NullSval, CondType);

    SVal CondNegativeOverflow =
        SvalBuilder.evalBinOp(State, BO_And, CondArgsLtNull, CondArgSumGtNull,
                              CondType);
    if (!CondPositiveOverflow.isZeroConstant())
      isOverflow = true;

    CondOverflow = SvalBuilder.evalBinOp(State, BO_Or, CondPositiveOverflow,
                                         CondNegativeOverflow, CondType);
  } else {
    isOverflow = true;
    // lhs > sum
    SVal CondLhsGtArgSum = SvalBuilder.evalBinOp(State, BO_GT, Lhs, ValArgSum,
                                                 CondType);
    // rhs > sum
    SVal CondRhsGtArgSum = SvalBuilder.evalBinOp(State, BO_GT, Rhs, ValArgSum,
                                                 CondType);
    // lhs > sum && rhs > sum
    CondOverflow = SvalBuilder.evalBinOp(State, BO_And, CondLhsGtArgSum,
                                         CondRhsGtArgSum, CondType);
  }

  return CondOverflow.getAs<DefinedOrUnknownSVal>();
}

Optional<DefinedOrUnknownSVal>
IntegerOverflowChecker::checkSub(CheckerContext &C, const SVal &Lhs,
                                 const SVal &Rhs, const QualType &BinType,
                                 bool &isOverflow) const {
  SVal CondOverflow;
  ProgramStateRef State = C.getState();
  SValBuilder &SvalBuilder = C.getSValBuilder();
  SVal NullSval = SvalBuilder.makeZeroVal(BinType);
  QualType CondType = SvalBuilder.getConditionType();
  SVal ValArgSub = SvalBuilder.evalBinOp(State, BO_Sub, Lhs, Rhs, BinType);
  if (BinType->isSignedIntegerType()) {
    // When first operand is negative
    // lhs < 0
    SVal CondLhsLtNull = SvalBuilder.evalBinOp(State, BO_LT, Lhs, NullSval,
                                               CondType);
    // rhs > 0
    SVal CondRhsGtNull = SvalBuilder.evalBinOp(State, BO_GT, Rhs, NullSval,
                                               CondType);
    // rhs > 0 && lhs < 0
    SVal CondLhsLtNullRhsGtNull =
        SvalBuilder.evalBinOp(State, BO_And, CondLhsLtNull, CondRhsGtNull,
                              CondType);
    // lhs - rhs >= 0
    SVal CondArgSubGeNull = SvalBuilder.evalBinOp(State, BO_GE, ValArgSub,
                                                  NullSval, CondType);

    // rhs > 0 && lhs < 0 && lhs-rhs >= 0
    SVal CondNegativeOverflow =
        SvalBuilder.evalBinOp(State, BO_And, CondLhsLtNullRhsGtNull,
                              CondArgSubGeNull, CondType);

    // When first operand is positive
    // lhs > 0
    SVal CondLhsGtNull = SvalBuilder.evalBinOp(State, BO_GT, Lhs, NullSval,
                                               CondType);
    // rhs < 0
    SVal CondRhsLtNull = SvalBuilder.evalBinOp(State, BO_LT, Rhs, NullSval,
                                               CondType);
    // rhs < 0 && lhs > 0
    SVal CondLhsGtNullRhsLtNull =
        SvalBuilder.evalBinOp(State, BO_And, CondLhsGtNull, CondRhsLtNull,
                              CondType);
    // lhs - rhs <= 0
    SVal CondArgSubLeNull = SvalBuilder.evalBinOp(State, BO_LE, ValArgSub,
                                                  NullSval, CondType);

    // rhs < 0 && lhs > 0 && lhs - rhs <= 0
    SVal CondPositiveOverflow =
        SvalBuilder.evalBinOp(State, BO_And, CondLhsGtNullRhsLtNull,
                              CondArgSubLeNull, CondType);

    CondOverflow = SvalBuilder.evalBinOp(State, BO_Or, CondNegativeOverflow,
                                         CondPositiveOverflow, CondType);
    if (!CondPositiveOverflow.isZeroConstant())
      isOverflow = true;
  } else
    CondOverflow = SvalBuilder.evalBinOp(State, BO_LT, Lhs, Rhs, CondType);

  return CondOverflow.getAs<DefinedOrUnknownSVal>();
}

Optional<DefinedOrUnknownSVal>
IntegerOverflowChecker::checkMul(CheckerContext &C, const SVal &Lhs,
                                 const SVal &Rhs, const QualType &BinType,
                                 bool &isOverflow) const {
  ProgramStateRef State = C.getState();
  ProgramStateRef CondNotOverflow, CondPossibleOverflow;
  SValBuilder &SvalBuilder = C.getSValBuilder();
  SVal NullSval = SvalBuilder.makeZeroVal(BinType);
  QualType CondType = SvalBuilder.getConditionType();

  // lhs == 0
  SVal LhsNotNull = SvalBuilder.evalBinOp(State, BO_NE, Lhs, NullSval,
                                          CondType);

  // rhs == 0
  SVal RhsNotNull = SvalBuilder.evalBinOp(State, BO_NE, Rhs, NullSval,
                                          CondType);

  Optional<DefinedOrUnknownSVal> CondOverflow =
      SvalBuilder.evalBinOp(State, BO_And, LhsNotNull, RhsNotNull, CondType)
          .getAs<DefinedOrUnknownSVal>();

  if (!CondOverflow.hasValue())
    return CondOverflow;

  llvm::tie(CondPossibleOverflow, CondNotOverflow) =
      State->assume(*CondOverflow);

  if (CondNotOverflow && CondPossibleOverflow)
    return CondOverflow;

  if (CondPossibleOverflow) {
    // lhs * rhs
    SVal ValMulti = SvalBuilder.evalBinOp(State, BO_Mul, Lhs, Rhs, BinType);
    // First operand(lhs) is not 0
    // (lhs * rhs)/lhs
    SVal ValDiv = SvalBuilder.evalBinOp(State, BO_Div, ValMulti, Lhs, BinType);
    // (lhs * rhs)/lhs != rhs

    CondOverflow = SvalBuilder.evalBinOp(State, BO_NE, ValDiv, Rhs, CondType)
                       .getAs<DefinedOrUnknownSVal>();
  }

  isOverflow = BinType->isUnsignedIntegerOrEnumerationType() ||
               SvalBuilder.evalBinOp(State, BO_LT, Lhs, NullSval, CondType)
                       .isZeroConstant() ==
                   SvalBuilder.evalBinOp(State, BO_LT, Rhs, NullSval, CondType)
                       .isZeroConstant();

  return CondOverflow;
}

std::string
IntegerOverflowChecker::getSymbolInformation(const SVal &Val, const Expr *E,
                                             CheckerContext &C) const {
  ProgramStateRef State = C.getState();
  std::string StreamRangeStr, ResultStr, SValDumpStr;
  llvm::raw_string_ostream StreamRange(StreamRangeStr), Result(ResultStr),
                           SValDump(SValDumpStr);
  Val.dumpToStream(SValDump);

  if (E && !isa<IntegerLiteral>(E->IgnoreParenCasts())) {
    E = E->IgnoreParens();
    const UnaryOperator *UO = dyn_cast<UnaryOperator>(E);
    if (!UO || (UO->getOpcode() != UO_Plus && UO->getOpcode() != UO_Minus) ||
        !isa<IntegerLiteral>(UO->getSubExpr())) {
      if (Val.getSubKind() == ConcreteIntKind)
        Result  << Val << " (";
      E->printPretty(Result, 0, C.getASTContext().getPrintingPolicy());
      if (Val.getSubKind() == ConcreteIntKind)
        Result << ")";
    }
    else
      Result << Val;
  }
  else
    Result << Val;

  if (Val.getSubKind() == SymbolValKind) {
    State->getConstraintManager().print(State, StreamRange, "\n", "\n");
    StreamRange.flush();
    size_t from = StreamRangeStr.find(SValDump.str() + " : ");
    if (from != std::string::npos) {
      size_t to = StreamRangeStr.find("\n", from);
      from += SValDump.str().length();
      Result.str().append(StreamRangeStr.substr(from, to - from));
    }
  }

  return Result.str();
}

// We ignore intentional underflow with subtracting X from zero - the minimal
// unsigned value.
bool
IntegerOverflowChecker::makeUSubHeuristics(const BinaryOperator *BO) const {
  const Expr *ExprLhs = BO->getLHS()->IgnoreParenCasts();
  if (isa<IntegerLiteral>(ExprLhs)) {
    const IntegerLiteral *IL = dyn_cast<IntegerLiteral>(ExprLhs);
    return IL->getValue().isMinValue();
  }
  return false;
}

void IntegerOverflowChecker::checkPostStmt(const BinaryOperator *B,
                                           CheckerContext &C) const {
  if (OverflowExpr.find(B) != OverflowExpr.end())
    return;

  if (!B->getLHS()->getType()->isIntegerType() ||
      !B->getRHS()->getType()->isIntegerType())
    return;

  ProgramStateRef State = C.getState();
  QualType BinType = B->getType();
  const Expr *ExprLhs = B->getLHS();
  const Expr *ExprRhs = B->getRHS();
  SVal Lhs = C.getSVal(ExprLhs);
  SVal Rhs = C.getSVal(ExprRhs);
  BinaryOperator::Opcode Op = B->getOpcode();

  if (!Filter.CheckIntegerOverflowDef && BinType->isUnsignedIntegerType())
    return;

  if (!Filter.CheckIntegerOverflowUndef && BinType->isSignedIntegerType())
    return;

  if (Op != BO_Add && Op != BO_Mul && Op != BO_Sub && Op != BO_AddAssign &&
      Op != BO_MulAssign && Op != BO_SubAssign)
    return;

  Optional<DefinedOrUnknownSVal> CondOverflow;
  ProgramStateRef StateOverflow, StateNotOverflow;

  bool isOverflow = false;
  if (Op == BO_Add || Op == BO_AddAssign)
    CondOverflow = checkAdd(C, Lhs, Rhs, BinType, isOverflow);
  else if (Op == BO_Sub || Op == BO_SubAssign) {
    if ((BinType->isUnsignedIntegerType()) && makeUSubHeuristics(B))
      return;
    CondOverflow = checkSub(C, Lhs, Rhs, BinType, isOverflow);
  } else if (Op == BO_Mul || Op == BO_MulAssign)
    CondOverflow = checkMul(C, Lhs, Rhs, BinType, isOverflow);

  if (!CondOverflow)
    return;

  llvm::tie(StateOverflow, StateNotOverflow) = State->assume(*CondOverflow);
  if (StateOverflow && StateNotOverflow && !State->isTainted(Lhs) &&
      !State->isTainted(Rhs)) {
    noteBinExpr(C, Lhs, Rhs, B);
    return;
  }

  if (!StateOverflow ||
      (StateNotOverflow && !(State->isTainted(Lhs) || State->isTainted(Rhs))))
    return;

  std::string Msg = composeMsg(StateNotOverflow, Lhs, Rhs, ExprLhs, ExprRhs,
                               B->getType()->isSignedIntegerOrEnumerationType(),
                               isOverflow, &Op, C);
  reportBug(Msg, C, B, NULL);
}
void IntegerOverflowChecker::noteBinExpr(CheckerContext &C, const SVal &Lhs,
                                         const SVal &Rhs, const Expr *E) const {
  if (C.getStateManager().getOwningEngine()->getAnalysisManager()
      .getAnalyzerOptions().getIPAMode() == IPAK_Summary) {
    static SimpleProgramPointTag Tag("IntegerOverflow_noteBinExpr");
    ProgramStateRef State = C.getState();
    ExplodedNode *N = C.addTransition(State, &Tag);
    C.addTransition(State->add<BinExprList>(
        BinExpr(Lhs, Rhs, E, N)), N);
  }
}

void IntegerOverflowChecker::checkPostStmt(const CXXNewExpr *NewExpr,
                                           CheckerContext &C) const {
  if (OverflowExpr.find(NewExpr) != OverflowExpr.end())
    return;
  if (!Filter.CheckIntegerOverflowDef)
    return;

  if (NewExpr->getOperatorNew()->getOverloadedOperator() != OO_Array_New)
    return;

  const Expr *ArrSize = NewExpr->getArraySize();
  SVal ElementCount = C.getSVal(ArrSize);
  ProgramStateRef State = C.getState();

  QualType NewExprType = NewExpr->getAllocatedType();
  uint64_t NewExprTypeSize = C.getASTContext().getTypeSizeInChars(NewExprType)
                                              .getQuantity();
  SValBuilder &SvalBuilder = C.getSValBuilder();
  SVal NewExprTypeSizeVal = SvalBuilder.makeIntVal(NewExprTypeSize, true);

  bool isOverflow;
  Optional<DefinedOrUnknownSVal> CondOverflow = checkMul(C, NewExprTypeSizeVal,
                                                         ElementCount,
                                                         ArrSize->getType(),
                                                         isOverflow);

  if (!CondOverflow)
    return;

  ProgramStateRef StateOverflow, StateNotOverflow;
  llvm::tie(StateOverflow, StateNotOverflow) = State->assume(*CondOverflow);

  if (StateOverflow && StateNotOverflow && !State->isTainted(ElementCount))
    noteBinExpr(C, NewExprTypeSizeVal,  ElementCount, NewExpr);

  if (!StateOverflow || (StateNotOverflow && !State->isTainted(ElementCount)))
    return;

  std::string Msg = composeMsg(StateNotOverflow, NewExprTypeSizeVal,
                               ElementCount, 0, ArrSize, false, isOverflow, 0,
                               C);
  reportBug(Msg, C, NewExpr, NULL);
}

#define REGISTER_CHECKER(name)                                                 \
  void ento::register##name(CheckerManager &mgr) {                             \
    IntegerOverflowChecker *checker =                                          \
        mgr.registerChecker<IntegerOverflowChecker>();                         \
    checker->Filter.CheckIntegerOverflowDef = true;                            \
    checker->Filter.CheckIntegerOverflowUndef = true;                          \
  }

REGISTER_CHECKER(IntegerOverflowDef)
