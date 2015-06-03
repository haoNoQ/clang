//== BasicStringBoundChecker.cpp --------------------------------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines BasicStringBoundChecker, which is a path-sensitive check
// which looks for an out-of-bound element access for basic_string
// objects.
//
//===----------------------------------------------------------------------===//

#include "ClangSACheckers.h"
#include "clang/AST/CharUnits.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/ADT/StringSwitch.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/DeclTemplate.h"

using namespace llvm;
using namespace clang;
using namespace ento;

namespace {
struct BasicStringState {
  StringRef StrValue; // Unused now, but maybe later we'll keep the string.
  SVal Length;
  bool IsChar;
  BasicStringState(): IsChar(false) {}
  BasicStringState(const StringRef &Str, SVal Len)
      : StrValue(Str), Length(Len), IsChar(true) {}

  bool operator==(const BasicStringState &X) const {
    return StrValue == X.StrValue && Length == X.Length && IsChar == X.IsChar;
  }

  static BasicStringState getEmpty(SValBuilder &svalBuilder, bool isChar) {
    SVal Zero = svalBuilder.makeZeroVal(svalBuilder.getContext().getSizeType());
    return BasicStringState(Zero, isChar);
  }

  void Profile(llvm::FoldingSetNodeID &ID) const {
    Length.Profile(ID);
    ID.AddPointer(StrValue.data());
    ID.AddBoolean(IsChar);
  }

  BasicStringState(SVal Len) : StrValue(""), Length(Len), IsChar(false) {}
  BasicStringState(SVal Len, bool isChar)
      : StrValue(""), Length(Len), IsChar(isChar) {}

  BasicStringState Actualize(Summarizer &S) const {
    return BasicStringState(S.actualizeSVal(Length), IsChar);
  }
};

struct StringAccess {
  SVal Length;
  SVal Index;
  const MemRegion *String;
  const Expr *AccExpr;

  StringAccess(SVal Len, SVal Idx, const MemRegion *MR, const Expr *AE) :
    Length(Len), Index(Idx), String(MR), AccExpr(AE) {}

  void Profile(llvm::FoldingSetNodeID &ID) const {
    Length.Profile(ID);
    Index.Profile(ID);
    ID.AddPointer(String);
    ID.AddPointer(AccExpr);
  }
  bool operator <(const StringAccess &RHS) const {
    llvm::FoldingSetNodeID ID, ID2;
    Profile(ID);
    RHS.Profile(ID2);
    return ID.ComputeHash() < ID2.ComputeHash();
  }
  bool operator ==(const StringAccess &RHS) const {
    return String == RHS.String && Length == RHS.Length && Index == RHS.Index;
  }
  StringAccess Actualize(Summarizer &S) const {
    return StringAccess(S.actualizeSVal(Length),
                        S.actualizeSVal(Index),
                        S.actualizeRegion(String),
                        AccExpr);
  }
};
typedef SummarySet<StringAccess> SummaryAccessSet;
}

REGISTER_SET_WITH_PROGRAMSTATE(SummaryAccesses, StringAccess)

namespace clang {
namespace ento {

template<>
BasicStringState Summarizer::actualizeAll<BasicStringState>(
      const BasicStringState &BSS) {
  return BSS.Actualize(*this);
}

template<>
StringAccess Summarizer::actualizeAll<StringAccess>(const StringAccess &SA) {
  return SA.Actualize(*this);
}
} // end namespace ento
} // end namespace clang


namespace {

class BasicStringBoundChecker
    : public Checker<eval::Call, check::Location, check::RegionChanges,
                     check::PostStmt<CXXOperatorCallExpr>,
                     check::PostStmt<CXXConstructExpr>,
                     check::LiveSymbols, check::DeadSymbols,
                     check::TemporaryValue, eval::SummaryPopulate,
                     eval::SummaryApply, eval::SummarySVal> {

  typedef void (BasicStringBoundChecker::*StringMethod)(
      CheckerContext &C, const CXXMemberCallExpr *CE) const;
  mutable OwningPtr<BugType> BT;
  enum OOB_Kind { OOB_Precedes, OOB_Excedes, OOB_Tainted };

  static const StringLiteral *getCStringLiteral(SVal SV, ProgramStateRef State);
  static SVal getExtent(CheckerContext &C, ProgramStateRef state, SVal l);
  static bool isNpos(CheckerContext &C, const Expr *E);
  static SVal getSubStrLength(CheckerContext &C, const Expr *String,
                              const Expr *SubPos, const Expr *SubLen,
                              const Expr *OrigExpr);

  bool checkNegativeIndex(SVal Index, const MemRegion *MR, SourceRange R,
                          ProgramStateRef State, CheckerContext &C) const;
  bool checkOverflow(SVal Len, SVal Index, const MemRegion *MR, SourceRange R,
                     ProgramStateRef State, CheckerContext &C) const;
  ProgramStateRef checkIndex(CheckerContext &C, const Expr *Object, SVal Index,
                             SourceRange R, const Expr *OrigExpr) const;
  ProgramStateRef checkIndex(CheckerContext &C, const Expr *Object,
                             const Expr *IndexExpr, const Expr *OrigExpr) const;

  // For copy ctors and assignment operator
  ProgramStateRef addCopy(ProgramStateRef State, const LocationContext *LCtx,
                          const MemRegion *MR, const Expr *Copy,
                          const Expr *OrigExpr) const;
  // For null-terminated strings ctors and assignment operator
  ProgramStateRef addPointer(CheckerContext &C, const Expr *Dst,
                             const Expr *Src) const;
  ProgramStateRef Initialize(CheckerContext &C, const Expr *What,
                             const Expr *const *Args, unsigned NumArgs,
                             const Expr *OrigExpr) const;
  ProgramStateRef evalAssignment(CheckerContext &C, const Expr *E,
                                 const Expr *Copy, const Expr *OrigExpr) const;
  ProgramStateRef evalPlus(CheckerContext &C, const Expr *LHS, const Expr *RHS,
                           const Expr *Dst, const Expr *OrigExpr) const;

  typedef std::pair<SVal, ProgramStateRef> LengthStatePair;
  static LengthStatePair getOrCreateStringState(ProgramStateRef State,
                                                const MemRegion *MR,
                                                bool IsChar,
                                                const Expr *OrigExpr);

  void At(CheckerContext &C, const CXXMemberCallExpr *CE) const;
  void Append(CheckerContext &C, const CXXMemberCallExpr *MCE) const;
  void Assign(CheckerContext &C, const CXXMemberCallExpr *MCE) const;
  void evalFind(CheckerContext &C, const CXXMemberCallExpr *CE) const;
  void evalClear(CheckerContext &C, const CXXMemberCallExpr *CE) const;
  void evalSize(CheckerContext &C, const CXXMemberCallExpr *MCE) const;
  void evalEmpty(CheckerContext &C, const CXXMemberCallExpr *MCE) const;
  void evalResize(CheckerContext &C, const CXXMemberCallExpr *MCE) const;
  void evalPushBack(CheckerContext &C, const CXXMemberCallExpr *MCE) const;

  void reportIndexOverflow(CheckerContext &C, ProgramStateRef state,
                           const MemRegion *MR, SourceRange Range, SVal Len,
                           SVal Index, OOB_Kind K) const;

  static void *getTag() {
    static int tag;
    return &tag;
  }

public:
  void checkPostStmt(const CXXOperatorCallExpr *OCE, CheckerContext &C) const;
  void checkPostStmt(const CXXConstructExpr *CCE, CheckerContext &C) const;
  void checkLocation(SVal l, bool isLoad, const Stmt* S,
                     CheckerContext &C) const;
  bool evalCall(const CallExpr *CE, CheckerContext &C) const;
  void checkLiveSymbols(ProgramStateRef state, SymbolReaper &SR) const;
  void checkDeadSymbols(SymbolReaper &SR, CheckerContext &C) const;
  ProgramStateRef checkRegionChanges(ProgramStateRef state,
                                     const InvalidatedSymbols *,
                                     ArrayRef<const MemRegion *> ExplicitRegions,
                                     ArrayRef<const MemRegion *> Regions,
                                     const CallEvent *Call) const;
  bool wantsRegionChangeUpdate(ProgramStateRef State) const;

  ProgramStateRef checkTemporaryValue(ProgramStateRef State,
                                      const LocationContext *LCtx,
                                      const Expr *E, SVal Src, SVal Dst) const;

  const void *evalSummaryPopulate(ProgramStateRef State) const;
  void evalSummaryApply(Summarizer &S, const CallEvent &Call,
                        const void *Summary, CheckerContext &C,
                        ProgramStateRef CalleeEndState) const;
  SVal evalSummarySVal(Summarizer &S, SVal SV) const;

  void printState(raw_ostream &Out, ProgramStateRef State,
                  const char *NL, const char *Sep) const;

private:
  class BasicStringVisitor : public BugReporterVisitorImpl<BasicStringVisitor> {
  protected:
    // Track lock that was unlocked somewhere on the path
    const MemRegion *Region;

  public:
    BasicStringVisitor(const MemRegion *Reg) : Region(Reg) {}
    virtual ~BasicStringVisitor() {}

    void Profile(llvm::FoldingSetNodeID &ID) const { ID.AddPointer(Region); }

    inline bool isChanged(const BasicStringState *S,
                          const BasicStringState *SPrev, const Stmt *Stmt) {
      return Stmt && isa<CallExpr>(Stmt) && !(*S == *SPrev);
    }

    inline bool isCreated(const BasicStringState *S,
                          const BasicStringState *SPrev, const Stmt *Stmt) {
      return Stmt && S && !SPrev;
    }

    PathDiagnosticPiece *VisitNode(const ExplodedNode *N,
                                   const ExplodedNode *PrevN,
                                   BugReporterContext &BRC, BugReport &BR);
  };
};
}

REGISTER_MAP_WITH_PROGRAMSTATE(StringLengths, const MemRegion *,
                               BasicStringState)

static const MemRegion *getMemRegion(SVal SV) {
  const MemRegion *MR = SV.getAsRegion();
  if (MR)
    return MR;
  if (Optional<nonloc::LazyCompoundVal> LCV =
      SV.getAs<nonloc::LazyCompoundVal>())
    return LCV->getRegion();
  return NULL;
}

static const MemRegion *getMemRegion(const Expr *E, CheckerContext &C) {
  SVal SV = C.getSVal(E);
  return getMemRegion(SV);
}

static const MemRegion *getMemRegion(const Expr *E, ProgramStateRef State,
                                     const LocationContext *LCtx) {
  SVal SV = State->getSVal(E, LCtx);
  return getMemRegion(SV);
}

static const ClassTemplateSpecializationDecl *getBasicStringDecl(QualType T) {
  const CXXRecordDecl *D = T->getAsCXXRecordDecl();
  if (!D && (T->isAnyPointerType() || T->isReferenceType()))
    D = T->getPointeeCXXRecordDecl();
  return D && D->getNameAsString() == "basic_string" &&
         AnalysisDeclContext::isInStdNamespace(D)
      ? dyn_cast<ClassTemplateSpecializationDecl>(D) : NULL;
}

static const ClassTemplateSpecializationDecl *
getBasicStringDecl(const Expr *E) {
  return getBasicStringDecl(E->getType());
}

static inline bool isCharTemplate(QualType T) {
  const ClassTemplateSpecializationDecl *Spec = getBasicStringDecl(T);
  assert(Spec && "basic_string should be a template specialization!");
  return Spec->getTemplateArgs()[0].getAsType()->isCharType();
}

static NonLoc getMinusOneSized(SValBuilder &svalBuilder, ASTContext &Ctx) {
  QualType SizeType = Ctx.getSizeType();
  return svalBuilder.makeIntVal(-1, SizeType).castAs<NonLoc>();
}

static NonLoc getMinusOneSized(CheckerContext &C) {
  return getMinusOneSized(C.getSValBuilder(), C.getASTContext());
}

static ProgramStateRef getMaxLenValue(ProgramStateRef state, NonLoc SV,
                                      SValBuilder &svalBuilder,
                                      ASTContext &Ctx) {
  BasicValueFactory &BV = svalBuilder.getBasicValueFactory();
  QualType SizeT = Ctx.getSizeType();
  APSInt MaxSize = BV.getMaxValue(SizeT).getInt() /
      BV.getValue(4, SizeT).getInt();
  nonloc::ConcreteInt CI(BV.getValue(MaxSize).getInt());
  Optional<DefinedOrUnknownSVal> LessThanMaxVal =
      svalBuilder.evalBinOpNN(state, BO_LE, SV, CI,
                              svalBuilder.getConditionType())
      .getAs<DefinedOrUnknownSVal>();
  if (LessThanMaxVal)
    state = state->assume(*LessThanMaxVal, true);
  return state;
}

static SymbolRef getNPosVariable(SVal SV) {
  SymbolRef Sym = SV.getAsSymExpr();
  if (!Sym)
    return NULL;
  while (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
    Sym = SC->getOperand();

  if (const SymbolRegionValue *SReg = dyn_cast<SymbolRegionValue>(Sym)) {
    std::string VarName;
    llvm::raw_string_ostream os(VarName);
    SReg->getRegion()->dumpToStream(os);
    os.flush();
    if (VarName == "npos")
      return Sym;
  }
  return NULL;
}

static unsigned getBlockCount(ProgramStateRef State) {
  return State->getStateManager().getOwningEngine()->blockCount();
}

// Checks if given expression is npos
bool BasicStringBoundChecker::isNpos(CheckerContext &C, const Expr *E) {
  SVal SV = C.getSVal(E);
  if (SV.isUnknownOrUndef())
    return false;
  // Some systems define npos as an external variable
  if (getNPosVariable(SV))
    return true;

  // npos is usually defined as ~0
  SValBuilder &svalBuilder = C.getSValBuilder();
  NonLoc Npos = getMinusOneSized(C);
  ProgramStateRef state = C.getState();
  Optional<NonLoc> EqualToNpos =
      svalBuilder.evalBinOp(state, BO_EQ, Npos, SV,
                            svalBuilder.getConditionType()).getAs<NonLoc>();
  if (EqualToNpos) {
    ProgramStateRef stateNPos, stateNonNpos;
    llvm::tie(stateNPos, stateNonNpos) = state->assume(*EqualToNpos);
    return stateNPos && !stateNonNpos;
  }
  return false;
}

SVal BasicStringBoundChecker::getSubStrLength(CheckerContext &C,
                                              const Expr *String,
                                              const Expr *SubPos,
                                              const Expr *SubLen,
                                              const Expr *OrigExpr) {
  if (isNpos(C, SubLen)) { // Given length is npos
    const MemRegion *ArgMR = getMemRegion(String, C);
    // FIXME: consider distinguish between unknown and undefined.
    if (!ArgMR) {
      return UnknownVal();
    } else {
      SValBuilder &svalBuilder = C.getSValBuilder();
      ProgramStateRef state = C.getState();
      ASTContext &Ctx = C.getASTContext();
      SVal ArgLen;
      llvm::tie(ArgLen, state) = getOrCreateStringState(
          state, ArgMR, isCharTemplate(String->getType()), OrigExpr);
      Optional<NonLoc> From = C.getSVal(SubPos).getAs<NonLoc>();
      Optional<NonLoc> Len = ArgLen.getAs<NonLoc>();
      if (!From || !Len)
        return UnknownVal();
      return svalBuilder.evalBinOp(state, BO_Sub, *Len, *From,
                                   Ctx.getSizeType());
    }
  }
  // FIXME: Consider case if SubPos + SubLen > String.Length
  return C.getSVal(SubLen);
}

const StringLiteral *BasicStringBoundChecker::getCStringLiteral(
    SVal SV, ProgramStateRef State) {
  const MemRegion *bufRegion = getMemRegion(SV);
  if (!bufRegion)
    return NULL;

  bufRegion = bufRegion->StripCasts();
  const StringRegion *strRegion = dyn_cast<StringRegion>(bufRegion);
  if (strRegion)
    return strRegion->getStringLiteral();

  if (isa<AllocaRegion>(bufRegion))
    return NULL;

  if (Optional<nonloc::LazyCompoundVal> LCV =
      State->getSVal(bufRegion).getAs<nonloc::LazyCompoundVal>())
    // FIXME: find correct solution.
    if (LCV->getRegion() != bufRegion)
      return getCStringLiteral(*LCV, State);

  return NULL;
}

// FIXME: Position of '0' in array should be returned instead of array length
// FIXME: getExtent() returns an upper approximation.
SVal BasicStringBoundChecker::getExtent(CheckerContext &C,
                                        ProgramStateRef state, SVal l) {
  if (!state)
    return UndefinedVal();

  const MemRegion *R = l.getAsRegion();
  if (!R)
    return UnknownVal();

  const ElementRegion *ER = dyn_cast<ElementRegion>(R);
  if (!ER)
    return UnknownVal();

  // Get the size of the array.
  SValBuilder &svalBuilder = C.getSValBuilder();
  const SubRegion *superReg = cast<SubRegion>(ER->getSuperRegion());

  DefinedOrUnknownSVal ElementLen = ER->getExtent(svalBuilder);
  SVal Extent =
      svalBuilder.convertToArrayIndex(superReg->getExtent(svalBuilder));
  Optional<DefinedOrUnknownSVal> Size = Extent.getAs<DefinedOrUnknownSVal>();
  assert(Size && "Size isn't defined or unknown");
  QualType SizeType = C.getASTContext().getSizeType();
  SVal ElemCount = svalBuilder.evalBinOp(state, BO_Div, *Size, ElementLen,
                                         SizeType);
    // Don't include trailing zero.
  NonLoc One = svalBuilder.makeIntVal(1, SizeType).castAs<NonLoc>();
  SVal Res = svalBuilder.evalBinOp(state, BO_Sub, ElemCount, One, SizeType);
  return Res;
}

BasicStringBoundChecker::LengthStatePair
BasicStringBoundChecker::getOrCreateStringState(ProgramStateRef State,
                                                const MemRegion *MR,
                                                bool IsChar,
                                                const Expr *OrigExpr) {
  assert(State);
  if (!MR)
    return LengthStatePair(UndefinedVal(), State);
  const BasicStringState *BSS = State->get<StringLengths>(MR);
  if (BSS)
    return LengthStatePair(BSS->Length, State);
  SValBuilder &svalBuilder = State->getStateManager().getSValBuilder();
  ASTContext &Ctx = svalBuilder.getContext();
  NonLoc Len = svalBuilder.getMetadataSymbolVal(
        getTag(), MR, OrigExpr, Ctx.getSizeType(), getBlockCount(State))
        .castAs<NonLoc>();
  BasicStringState NewBSS(Len, IsChar);
  State = State->set<StringLengths>(MR, NewBSS);
  State = getMaxLenValue(State, Len, svalBuilder, Ctx);
  return LengthStatePair(Len, State);
}

ProgramStateRef BasicStringBoundChecker::checkTemporaryValue(
    ProgramStateRef State, const LocationContext *LCtx,
    const Expr *E, SVal Src, SVal Dst) const {
  const MemRegion *MR = getMemRegion(Dst);
  if (MR && getBasicStringDecl(E->getType()))
    State = addCopy(State, LCtx, MR, E, E);
  return State;
}

// basic_string::operator+
ProgramStateRef BasicStringBoundChecker::evalPlus(CheckerContext &C,
                                                  const Expr *LHS,
                                                  const Expr *RHS,
                                                  const Expr *Dst,
                                                  const Expr *OrigExpr) const {
  ProgramStateRef state = C.getState();
  const MemRegion *MR = getMemRegion(Dst, C);
  if (!MR)
    return state;

  QualType T = Dst->getType();
  bool isChar = isCharTemplate(T);
  SValBuilder &svalBuilder = C.getSValBuilder();
  QualType SizeType = C.getASTContext().getSizeType();

  // At least one argument should be a basic_string. Assume it is LHS.
  if (!getBasicStringDecl(LHS))
    // We're just calculating lengths. If we'll need to emulate
    // basic_string completely, we cannot swap right and left sides.
    std::swap(LHS, RHS);
  const MemRegion *LhsMR = getMemRegion(LHS, C);
  SVal LenLHS;
  llvm::tie(LenLHS, state) =
      getOrCreateStringState(state, LhsMR, isChar, OrigExpr);
  SVal LenRHS;
  // Get length of rhs
  QualType ArgType = RHS->getType();
  // Rhs is string
  if (getBasicStringDecl(ArgType)) {
    const MemRegion *RhsMR = getMemRegion(RHS, C);
    llvm::tie(LenRHS, state) =
        getOrCreateStringState(state, RhsMR, isChar, OrigExpr);
  } else {
    if (ArgType->isPointerType()) {
      const ClassTemplateSpecializationDecl *Spec = getBasicStringDecl(T);
      const Type *SpecT = Spec->getTemplateArgs()[0].getAsType().getTypePtr();
      if (SpecT == ArgType->getPointeeType().getTypePtr()) {
        const StringLiteral *Str =
            getCStringLiteral(C.getSVal(RHS->IgnoreImplicit()), state);
        if (Str) { // Rhs is a string literal
          LenRHS = svalBuilder.makeIntVal(Str->getLength(), SizeType);
        } else { // Rhs is just a null-terminated string of a same type
          LenRHS = getExtent(C, state, C.getSVal(RHS));
        }
      } else {
        // Rhs is a pointer but it is a pointer of template type (charT)
        // See test21 as an example.
        LenRHS = svalBuilder.makeIntVal(1, SizeType);
      }
    } else { // Just a charT
      LenRHS = svalBuilder.makeIntVal(1, SizeType);
    }
  }
  if (LenLHS.isUnknownOrUndef() || LenRHS.isUnknownOrUndef()) {
    state = state->remove<StringLengths>(MR);
  } else {
    QualType cmpTy = svalBuilder.getConditionType();
    SVal finalStrLength = svalBuilder.evalBinOp(
        state, BO_Add, LenLHS, LenRHS, SizeType);
    if (!finalStrLength.isUnknown()) {
      BasicStringState NewLenState(finalStrLength, isChar);
      state = state->set<StringLengths>(MR, NewLenState);
    } else {
      // If final length is unknown,
      assert(MR);
      llvm::tie(finalStrLength, state) =
          getOrCreateStringState(state, MR, isChar, OrigExpr);
    }
    // Ensure that final length is not less than lengths
    // of any concatenating strings
    NonLoc finalStrLengthNL = finalStrLength.castAs<NonLoc>();
    if (!LenLHS.isUnknown()) {
      // finalStrLength >= LenLHS
      SVal lhsInResult = svalBuilder.evalBinOpNN(
          state, BO_GE, finalStrLengthNL, LenLHS.castAs<NonLoc>(), cmpTy);
      ProgramStateRef stateLHS =
          state->assume(lhsInResult.castAs<DefinedOrUnknownSVal>(), true);
      if (!stateLHS) // FIXME: add an assertion?
        return state;
      else
        state = stateLHS;
    }

    if (!LenRHS.isUnknown()) {
      // finalStrLength >= LenRHS
      SVal rhsInResult = svalBuilder.evalBinOpNN(
          state, BO_GE, finalStrLengthNL, LenRHS.castAs<NonLoc>(), cmpTy);
      ProgramStateRef stateRHS =
          state->assume(rhsInResult.castAs<DefinedOrUnknownSVal>(), true);
      if (!stateRHS) // FIXME: add an assertion?
        return state;
      else
        state = stateRHS;
    }
    if (LenLHS.isUnknown() && LenRHS.isUnknown())
      state = state->remove<StringLengths>(MR);
  }
  return state;
}

// basic_string::append()
// Add lengths of RHS to length of object
void BasicStringBoundChecker::Append(CheckerContext &C,
                                     const CXXMemberCallExpr *MCE) const {
  const Expr *Object = MCE->getImplicitObjectArgument();
  // Meaningful arguments for insert() call are started from the 2nd
  unsigned Shift = MCE->getMethodDecl()->getName() == "insert";
  const MemRegion *MR = getMemRegion(Object, C);
  if (!MR)
    return;
  ProgramStateRef state = C.getState();
  state = state->BindExpr(MCE, C.getLocationContext(), C.getSVal(Object));
  const Expr *const *Args = MCE->getArgs();
  if (MCE->getNumArgs() == 1 + Shift) { // basic_string and c-string
    state = evalPlus(C, Object, Args[Shift], Object, MCE);
  } else {
    bool isChar = isCharTemplate(Object->getType());
    SVal LenLHS;
    llvm::tie(LenLHS, state) = getOrCreateStringState(state, MR, isChar, MCE);
    SVal LenRHS = UnknownVal();
    // Get length of rhs
    SValBuilder &svalBuilder = C.getSValBuilder();
    const QualType SizeType = C.getASTContext().getSizeType();
    if (MCE->getNumArgs() == 3 + Shift) { // Substring
      LenRHS = getSubStrLength(C, Args[0 + Shift], Args[1 + Shift],
                               Args[2 + Shift], MCE);
    } else {
      const Type *FirstArgType = MCE->getArg(Shift)->getType().getTypePtr();
      if (FirstArgType->isPointerType()) {
        if (MCE->getArg(1 + Shift)->getType().getTypePtr()->isIntegerType()) {
          // Buffer
          LenRHS = C.getSVal(MCE->getArg(1 + Shift));
        }
      } else { // Fill
        LenRHS = C.getSVal(MCE->getArg(1 + Shift));
      }
    }
    if (!LenRHS.isUnknownOrUndef()) {
      SVal NewLen =
          svalBuilder.evalBinOp(state, BO_Add, LenLHS, LenRHS, SizeType);
      if (!NewLen.isUnknownOrUndef()) {
        BasicStringState BSS(NewLen, isChar);
        state = state->set<StringLengths>(MR, BSS);
      }
    } else { // We don't know anything about string length now
      state = state->remove<StringLengths>(MR);
    }
  }
  C.addTransition(state);
}

// basic_string::assign()
// Add lengths of RHS to length of object
void BasicStringBoundChecker::Assign(CheckerContext &C,
                                     const CXXMemberCallExpr *MCE) const {
  const MemRegion *MR = getMemRegion(
        C.getSVal(MCE->getImplicitObjectArgument()));
  if (!MR)
    return;
  ProgramStateRef State = Initialize(C, MCE->getImplicitObjectArgument(),
                                     MCE->getArgs(), MCE->getNumArgs(), MCE);
  State = State->BindExpr(MCE, C.getLocationContext(), loc::MemRegionVal(MR));
  C.addTransition(State);
}

// basic_string::push_back()
// Increment length of the object
void BasicStringBoundChecker::evalPushBack(CheckerContext &C,
                                           const CXXMemberCallExpr *MCE) const {
  const Expr *Object = MCE->getImplicitObjectArgument();
  const MemRegion *MR = getMemRegion(Object, C);
  if (!MR)
    return;
  ProgramStateRef state = C.getState();
  SVal Len;
  SValBuilder &svalBuilder = C.getSValBuilder();
  bool IsChar = isCharTemplate(Object->getType());
  llvm::tie(Len, state) = getOrCreateStringState(state, MR, IsChar, MCE);
  const QualType SizeType = C.getASTContext().getSizeType();
  NonLoc One = svalBuilder.makeIntVal(1, SizeType).castAs<NonLoc>();
  SVal NewLen = svalBuilder.evalBinOp(state, BO_Add, Len, One, SizeType);
  BasicStringState BSS(NewLen, IsChar);
  state = state->set<StringLengths>(MR, BSS);
  C.addTransition(state);
}

// operator=
ProgramStateRef
BasicStringBoundChecker::evalAssignment(CheckerContext &C, const Expr *Dst,
                                        const Expr *Src,
                                        const Expr *OrigExpr) const {
  QualType ArgType = Src->getType();
  ProgramStateRef state = C.getState();

  const MemRegion *MR = getMemRegion(Dst, C);
  if (!MR)
    return state;

  if (getBasicStringDecl(ArgType)) // Copying assignment
    return addCopy(state, C.getLocationContext(), MR, Src, OrigExpr);

  ASTContext &Ctx = C.getASTContext();
  QualType T = Dst->getType();
  if (ArgType->isPointerType()) {
    const ClassTemplateSpecializationDecl *Spec = getBasicStringDecl(T);
    QualType SpecT = Spec->getTemplateArgs()[0].getAsType();
    if (Ctx.hasSameUnqualifiedType(SpecT, ArgType->getPointeeType()))
      return addPointer(C, Dst, Src); // Pointer assignment
  }

  // Assignment of charT
  bool isChar = isCharTemplate(T);
  QualType SizeType = Ctx.getSizeType();
  NonLoc Len = C.getSValBuilder().makeIntVal(1, SizeType).castAs<NonLoc>();
  state = state->set<StringLengths>(MR, BasicStringState(Len, isChar));
  state = state->BindExpr(Dst, C.getLocationContext(), loc::MemRegionVal(MR));
  return state;
}

bool BasicStringBoundChecker::evalCall(const CallExpr *CE,
                                       CheckerContext &C) const {
  const CXXMemberCallExpr *MCE = dyn_cast<CXXMemberCallExpr>(CE);
  if (MCE) { // Method call
    const Expr *Object = MCE->getImplicitObjectArgument();
    const ClassTemplateSpecializationDecl *Spec = getBasicStringDecl(Object);
    if (!Spec)
      return false;
    const CXXMethodDecl *MD = MCE->getMethodDecl();
    if (!MD->getDeclName().isIdentifier())
      return false;
    StringMethod Method =
        llvm::StringSwitch<StringMethod>(MD->getName())
            .Case("find", &BasicStringBoundChecker::evalFind)
            .Case("find_first_of", &BasicStringBoundChecker::evalFind)
            .Case("find_last_of", &BasicStringBoundChecker::evalFind)
            .Case("find_first_not_of", &BasicStringBoundChecker::evalFind)
            .Case("find_last_not_of", &BasicStringBoundChecker::evalFind)
            .Case("clear", &BasicStringBoundChecker::evalClear)
            .Case("size", &BasicStringBoundChecker::evalSize)
            .Case("length", &BasicStringBoundChecker::evalSize)
            .Case("resize", &BasicStringBoundChecker::evalResize)
            .Case("empty", &BasicStringBoundChecker::evalEmpty)
            .Case("at", &BasicStringBoundChecker::At)
            .Case("push_back", &BasicStringBoundChecker::evalPushBack)
            .Case("append", &BasicStringBoundChecker::Append)
            .Case("insert", &BasicStringBoundChecker::Append)
            .Case("assign", &BasicStringBoundChecker::Assign)
            .Default(0);
    if (!Method)
      return false;
    (this->*Method)(C, MCE);
    return true;
  } else if (const CXXOperatorCallExpr *OCE =
                 dyn_cast<CXXOperatorCallExpr>(CE)) {
    const OverloadedOperatorKind Op = OCE->getOperator();
    if (Op != OO_Subscript && Op != OO_PlusEqual && Op != OO_Equal)
      return false;
    const Expr *Object = OCE->getArg(0);
    if (!getBasicStringDecl(Object))
      return false;
    ProgramStateRef state;
    if (Op == OO_Subscript) {
      // Model operator[]
      state = checkIndex(C, Object, OCE->getArg(1), CE);
      state = state->BindExpr(OCE, C.getLocationContext(), UnknownVal());
    } else if (Op == OO_PlusEqual) {
      // operator +=
      state = evalPlus(C, Object, OCE->getArg(1), Object, OCE);
      state = state->BindExpr(OCE, C.getLocationContext(), C.getSVal(Object));
    } else if (Op == OO_Equal) {
      state = evalAssignment(C, Object, OCE->getArg(1), OCE);
    } else {
      return false;
    }
    C.addTransition(state);
    return true;
  }
  return false;
}

// Evaluate length of a new string if it can be reasoned about
void BasicStringBoundChecker::checkPostStmt(const CXXConstructExpr *CCE,
                                            CheckerContext &C) const {
  C.addTransition(Initialize(C, CCE, CCE->getArgs(), CCE->getNumArgs(), CCE));
}

// Operators are checked here
void BasicStringBoundChecker::checkPostStmt(const CXXOperatorCallExpr *OCE,
                                            CheckerContext &C) const {
  if (OCE->getOperator() != OO_Plus)
    return;
  if (!getBasicStringDecl(OCE))
    return;
  ProgramStateRef state = evalPlus(C, OCE->getArg(0), OCE->getArg(1), OCE, OCE);
  C.addTransition(state);
}

void BasicStringBoundChecker::checkLocation(
    SVal l, bool isLoad, const Stmt* S, CheckerContext &C) const {
  if (!isLoad)
    return;
  if (l.isUnknownOrUndef())
    return;
  const Expr *E = dyn_cast<Expr>(S);
  if (!E)
    return;

  ProgramStateRef State = C.getState();
  SVal SV = State->getSVal(l.castAs<Loc>(), E->getType());
  SymbolRef NposSym = getNPosVariable(SV);
  if (!NposSym)
    return;
  SValBuilder &svalBuilder = C.getSValBuilder();
  NonLoc Npos = getMinusOneSized(C);
  NonLoc EqualToNpos =
      svalBuilder.evalBinOp(State, BO_EQ, Npos, SV,
                            C.getASTContext().getSizeType()).castAs<NonLoc>();
  State = State->assume(EqualToNpos, true);
  C.addTransition(State);
}

// We should model at and operator[] completely because GNU STL implementation
// inlines most functions. It leads to fast growth of analysis time.
void BasicStringBoundChecker::At(CheckerContext &C,
                                 const CXXMemberCallExpr *CE) const {
  const Expr *Object = CE->getImplicitObjectArgument();
  ProgramStateRef state = checkIndex(C, Object, CE->getArg(0), CE);
  state = state->BindExpr(CE, C.getLocationContext(), UnknownVal());
  C.addTransition(state);
}

void BasicStringBoundChecker::evalFind(CheckerContext &C,
                                       const CXXMemberCallExpr *CE) const {
  const Expr *Object = CE->getImplicitObjectArgument();
  ProgramStateRef state = C.getState();
  const LocationContext *LCtx = C.getLocationContext();
  const MemRegion *MR = getMemRegion(Object, C);
  if (!MR) {
    state = state->BindExpr(CE, LCtx, UnknownVal());
    C.addTransition(state);
    return;
  }
  SValBuilder &svalBuilder = C.getSValBuilder();
  QualType SizeType = C.getASTContext().getSizeType();
  QualType CondType = svalBuilder.getConditionType();
  NonLoc RetVal = svalBuilder.conjureSymbolVal(CE, LCtx, SizeType,
                                               C.blockCount()).castAs<NonLoc>();
  state = state->BindExpr(CE, LCtx, RetVal);

  // If length is known assume result is npos or it is less than length
  // and greater or equal to start position
  ProgramStateRef stateNpos = NULL, stateNonNpos = NULL;
  NonLoc Npos = getMinusOneSized(C);
  NonLoc EqualToNpos = svalBuilder.evalBinOp(state, BO_EQ, Npos, RetVal,
                                             SizeType).castAs<NonLoc>();
  llvm::tie(stateNpos, stateNonNpos) = state->assume(EqualToNpos);
  if (stateNonNpos) {
    SVal Len;
    llvm::tie(Len, stateNonNpos) =
        getOrCreateStringState(stateNonNpos, MR,
                               isCharTemplate(Object->getType()), CE);
    NonLoc Length = Len.castAs<NonLoc>();

    // Return value is not less than start search position
    // stlport has find() declaration without a default parameter
    SVal StartPos = CE->getNumArgs() == 1 ? svalBuilder.makeZeroVal(SizeType)
                                          : C.getSVal(CE->getArg(1));
    Optional<NonLoc> StartPosNL = StartPos.getAs<NonLoc>();
    if (StartPosNL) {
      DefinedOrUnknownSVal GreaterOrEqThanMinPos =
          svalBuilder.evalBinOpNN(state, BO_GE, RetVal, *StartPosNL, CondType)
              .castAs<DefinedOrUnknownSVal>();
      if (!GreaterOrEqThanMinPos.isUnknown())
        stateNonNpos = stateNonNpos->assume(GreaterOrEqThanMinPos, true);

      // string.length() > start if char is found.
      if (stateNonNpos) {
        DefinedOrUnknownSVal MoreThanStart =
            svalBuilder.evalBinOpNN(state, BO_GT, Length, *StartPosNL, CondType)
                .castAs<DefinedOrUnknownSVal>();
        if (stateNonNpos && !MoreThanStart.isUnknown())
          stateNonNpos = stateNonNpos->assume(MoreThanStart, true);
      }
    }

    // Return value is less than string.length()
    if (stateNonNpos) {
      DefinedOrUnknownSVal LessThanLen =
          svalBuilder.evalBinOpNN(state, BO_LT, RetVal, Length, CondType)
              .castAs<DefinedOrUnknownSVal>();
      if (!LessThanLen.isUnknown())
        stateNonNpos = stateNonNpos->assume(LessThanLen, true);
    }
  }

  if (stateNpos)
    C.addTransition(stateNpos);
  if (stateNonNpos)
    C.addTransition(stateNonNpos);
}

// basic_stream.clear()
// Set length of basic_string to 0.
void BasicStringBoundChecker::evalClear(CheckerContext &C,
                                        const CXXMemberCallExpr *CE) const {
  const Expr *Object = CE->getImplicitObjectArgument();
  ProgramStateRef state = C.getState();
  const MemRegion *MR = getMemRegion(Object, C);
  if (!MR)
    return;
  bool isChar = isCharTemplate(Object->getType());
  state = state->set<StringLengths>(
      MR, BasicStringState::getEmpty(C.getSValBuilder(), isChar));
  C.addTransition(state);
}

// basic_string.empty()
// Returns true iff length of string is 0.
void BasicStringBoundChecker::evalEmpty(CheckerContext &C,
                                        const CXXMemberCallExpr *MCE) const {
  const Expr *Object = MCE->getImplicitObjectArgument();
  const MemRegion *MR = C.getSVal(Object).getAsRegion();
  if (!MR)
    return;
  ProgramStateRef state = C.getState();
  const LocationContext *LCtx = C.getLocationContext();
  SValBuilder &svalBuilder = C.getSValBuilder();
  SVal Len;
  llvm::tie(Len, state) =
      getOrCreateStringState(state, MR, isCharTemplate(Object->getType()), MCE);
  if (Len.isUnknownOrUndef())
    return;
  NonLoc Length = Len.castAs<NonLoc>();
  NonLoc ZeroVal = svalBuilder.makeZeroVal(C.getASTContext().getSizeType())
      .castAs<NonLoc>();
  SVal RetVal = svalBuilder.evalEQ(state, ZeroVal, Length);
  state = state->BindExpr(MCE, LCtx, RetVal);
  C.addTransition(state);
}

// basic_string.size(), basic_string.length()
// return length if we know it
void BasicStringBoundChecker::evalSize(CheckerContext &C,
                                       const CXXMemberCallExpr *MCE) const {
  const Expr *Object = MCE->getImplicitObjectArgument();
  ProgramStateRef state = C.getState();
  const MemRegion *MR = getMemRegion(Object, C);
  SVal RetVal;
  if (!MR)
    RetVal = UnknownVal();
  else
    llvm::tie(RetVal, state) = getOrCreateStringState(
        state, MR, isCharTemplate(Object->getType()), MCE);

  state = state->BindExpr(MCE, C.getLocationContext(), RetVal);
  C.addTransition(state);
}

// basic_string.resize()
// Set string length to a new value if it is known
void BasicStringBoundChecker::evalResize(CheckerContext &C,
                                         const CXXMemberCallExpr *MCE) const {
  const Expr *Object = MCE->getImplicitObjectArgument();
  const MemRegion *MR = C.getSVal(Object).getAsRegion();
  if (!MR)
    return;

  ProgramStateRef state = C.getState();
  QualType T = Object->getType();
  Optional<DefinedOrUnknownSVal> ArgSVal =
      C.getSVal(MCE->getArg(0)).getAs<DefinedOrUnknownSVal>();
  if (!ArgSVal)
    state = state->remove<StringLengths>(MR);
  else {
    bool isChar = isCharTemplate(T);
    state = state->set<StringLengths>(MR, BasicStringState(*ArgSVal, isChar));
  }
  C.addTransition(state);
}

// Some created symbols don't belong to any expression. They should be kept.
void BasicStringBoundChecker::checkLiveSymbols(ProgramStateRef state,
                                               SymbolReaper &SR) const {
  // Mark all symbols in our string length map as valid.
  StringLengthsTy Entries = state->get<StringLengths>();

  for (StringLengthsTy::iterator I = Entries.begin(), E = Entries.end(); I != E;
       ++I) {
    SVal Len = I.getData().Length;

    for (SymExpr::symbol_iterator si = Len.symbol_begin(),
                                  se = Len.symbol_end();
         si != se; ++si)
      SR.markLive(*si);
  }
}

// A new string is initialized to a value of an existing string
ProgramStateRef BasicStringBoundChecker::addCopy(ProgramStateRef State,
                                                 const LocationContext *LCtx,
                                                 const MemRegion *MR,
                                                 const Expr *Copy,
                                                 const Expr *OrigExpr) const {
  assert(MR);
  const MemRegion *ArgMR = getMemRegion(Copy, State, LCtx);
  if (!ArgMR)
    return State;
  SVal UnusedLen;
  bool isChar = isCharTemplate(Copy->getType());
  llvm::tie(UnusedLen, State) =
      getOrCreateStringState(State, ArgMR, isChar, OrigExpr);
  const BasicStringState *BSS = State->get<StringLengths>(ArgMR);
  State = State->set<StringLengths>(MR, *BSS);
  return State;
}

// Initialize string via null-terminated string
ProgramStateRef BasicStringBoundChecker::addPointer(CheckerContext &C,
                                                    const Expr *Dst,
                                                    const Expr *Src) const {
  const MemRegion *MR = getMemRegion(Dst, C);
  assert(MR);
  ProgramStateRef state = C.getState();

  // Try to retrieve value for charT*
  const StringLiteral *Str = getCStringLiteral(C.getSVal(Src), state);
  if (Str) { // String literal, keep its value
    StringRef StrRef = Str->getBytes();
    QualType SizeType = C.getASTContext().getSizeType();
    SVal Len = C.getSValBuilder().makeIntVal(Str->getLength(), SizeType);
    state = state->set<StringLengths>(MR, BasicStringState(StrRef, Len));
  } else { // Retrieve length only
    SVal Len = getExtent(C, state, C.getSVal(Src));
    if (!Len.isUnknownOrUndef())
      state = state->set<StringLengths>(
          MR, BasicStringState(Len, isCharTemplate(Dst->getType())));
    else // Value to copy is unknown, we can't use it anymore
      state = state->remove<StringLengths>(MR);
  }
  return state;
}

ProgramStateRef
BasicStringBoundChecker::Initialize(CheckerContext &C, const Expr *What,
                                    const Expr *const *Args, unsigned NumArgs,
                                    const Expr *OrigExpr) const {
  ProgramStateRef state = C.getState();
  QualType T = What->getType();
  const ClassTemplateSpecializationDecl *Spec = getBasicStringDecl(T);
  if (!Spec)
    return state;
  const MemRegion *MR = getMemRegion(What, C);
  if (!MR)
    return state;
  bool isChar = isCharTemplate(T);

  if (NumArgs == 0) { // Default constructor
    state = state->set<StringLengths>(
        MR, BasicStringState::getEmpty(C.getSValBuilder(), isChar));
  } else {
    const Expr *Arg = Args[0];
    QualType ArgType = Arg->getType();
    // Initialize via pointer or string
    if (ArgType->isPointerType() &&
        C.getASTContext().hasSameUnqualifiedType(
          Spec->getTemplateArgs()[0].getAsType(), ArgType->getPointeeType())) {
      QualType SecArgType;
      if (NumArgs > 1) {
        SecArgType = Args[1]->getType();
        if (SecArgType->isPointerType()) // Iterator ctor. FIXME: model it.
          return state;
      }
      if (NumArgs == 1 || !SecArgType->isIntegerType()) {
        state = addPointer(C, What, Arg);
      } else {
        // Sequence
        SVal Len = C.getSVal(Args[1]);
        if (!Len.isUnknownOrUndef())
          state = state->set<StringLengths>(MR, BasicStringState(Len, isChar));
        else
          state = state->remove<StringLengths>(MR);
      }
    } else if (getBasicStringDecl(ArgType)) { // First arg is basic_string
      if (NumArgs == 1) {                // Copy ctor
        state = addCopy(state, C.getLocationContext(), MR, Arg, OrigExpr);
      } else if (NumArgs >= 3) { // Substring ctor
        SVal NewLen = getSubStrLength(C, Args[0], Args[1], Args[2], OrigExpr);
        if (!NewLen.isUnknownOrUndef())
          state =
              state->set<StringLengths>(MR, BasicStringState(NewLen, isChar));
        else
          state = state->remove<StringLengths>(MR);
      }
    } else if (ArgType->isIntegerType()) { // Fill ctor
      SVal ArgSVal = C.getSVal(Arg);
      if (!ArgSVal.isUnknownOrUndef())
        state =
            state->set<StringLengths>(MR, BasicStringState(ArgSVal, isChar));
    }
  }
  return state;
}

bool BasicStringBoundChecker::checkNegativeIndex(SVal Index,
                                                 const MemRegion *MR,
                                                 SourceRange R,
                                                 ProgramStateRef State,
                                                 CheckerContext &C) const {
  ConstraintManager &CM = C.getConstraintManager();
  SValBuilder &svalBuilder = C.getSValBuilder();
  QualType CondType = svalBuilder.getConditionType();
  // Check on possible negative index
  NonLoc MaxSize = getMinusOneSized(C);
  QualType SizeType = C.getASTContext().getSizeType();
  // FIXME: Move this to a separate func
  DefinedOrUnknownSVal MaxSigned =
      svalBuilder.evalBinOp(State, BO_Div, MaxSize,
                            svalBuilder.makeIntVal(2, SizeType), SizeType)
      .castAs<NonLoc>();
  Optional<DefinedSVal> Negative =
      svalBuilder.evalBinOp(State, BO_GT, Index, MaxSigned, CondType)
          .getAs<DefinedSVal>();
  if (Negative) {
    ProgramStateRef stateSegfault, stateGood;
    llvm::tie(stateSegfault, stateGood) = CM.assumeDual(State, *Negative);
    if (stateSegfault && !stateGood) {
      reportIndexOverflow(C, State, MR, R, UnknownVal(), Index, OOB_Precedes);
      return true;
    }
  }
  return false;
}

bool BasicStringBoundChecker::checkOverflow(SVal Len, SVal Index,
                                            const MemRegion *MR, SourceRange R,
                                            ProgramStateRef State,
                                            CheckerContext &C) const {
  ConstraintManager &CM = C.getConstraintManager();
  SValBuilder &svalBuilder = C.getSValBuilder();
  QualType CondType = svalBuilder.getConditionType();
  Optional<DefinedSVal> Segfault =
      svalBuilder.evalBinOp(State, BO_GT, Index, Len, CondType)
          .getAs<DefinedSVal>();
  if (Segfault) {
    ProgramStateRef StateSegfault, StateGood;
    llvm::tie(StateSegfault, StateGood) = CM.assumeDual(State, *Segfault);
    if (StateSegfault) {
      if (!StateGood) {
        reportIndexOverflow(C, State, MR, R, Len, Index, OOB_Excedes);
        return true;
      } else if (State->isTainted(Index)) {
        reportIndexOverflow(C, State, MR, R, Len, Index, OOB_Tainted);
        return true;
      }
    }
  }
  return false;
}

ProgramStateRef
BasicStringBoundChecker::checkIndex(CheckerContext &C, const Expr *Object,
                                    const Expr *IndexExpr,
                                    const Expr *OrigExpr) const {
  Optional<DefinedOrUnknownSVal> Index =
      C.getSVal(IndexExpr).getAs<DefinedOrUnknownSVal>();
  return Index
      ? checkIndex(C, Object, *Index, IndexExpr->getSourceRange(), OrigExpr)
      : C.getState();
}

ProgramStateRef
BasicStringBoundChecker::checkIndex(CheckerContext &C, const Expr *Object,
                                    SVal Index, SourceRange R,
                                    const Expr *OrigExpr) const {
  const MemRegion *MR = getMemRegion(Object, C);
  ProgramStateRef state = C.getState();
  if (!MR)
    return state;
  if (checkNegativeIndex(Index, MR, R, state, C))
    return state;
  // Check on possible positive buffer overflows
  // We're ignore strings passed as params because it is often assumed
  // that they are non-empty
  SVal Len;
  llvm::tie(Len, state) = getOrCreateStringState(
      state, MR, isCharTemplate(Object->getType()), OrigExpr);
  if (checkOverflow(Len, Index, MR, R, state, C))
    return state;
  return state->add<SummaryAccesses>(StringAccess(Len, Index, MR, Object));
}


bool BasicStringBoundChecker::wantsRegionChangeUpdate(
    ProgramStateRef State) const {
  StringLengthsTy Entries = State->get<StringLengths>();
  return !Entries.isEmpty();
}

ProgramStateRef
BasicStringBoundChecker::checkRegionChanges(ProgramStateRef State,
                                   const InvalidatedSymbols *,
                                   ArrayRef<const MemRegion *> ExplicitRegions,
                                   ArrayRef<const MemRegion *> Regions,
                                   const CallEvent *Call) const {
  if (Call) {
    if (isa<CXXConstructorCall>(Call))
      return State;
    else if (const CXXOperatorCallExpr *OCE =
               dyn_cast_or_null<CXXOperatorCallExpr>(Call->getOriginExpr()))
      if (OCE->getOperator() == OO_Plus && getBasicStringDecl(OCE))
        return State;
  }

  StringLengthsTy Entries = State->get<StringLengths>();
  if (Entries.isEmpty())
    return State;

  llvm::SmallPtrSet<const MemRegion *, 8> Invalidated;
  llvm::SmallPtrSet<const MemRegion *, 32> SuperRegions;

  // First build sets for the changed regions and their super-regions.
  for (ArrayRef<const MemRegion *>::iterator
       I = Regions.begin(), E = Regions.end(); I != E; ++I) {
    const MemRegion *MR = *I;
    Invalidated.insert(MR);

    SuperRegions.insert(MR);
    while (const SubRegion *SR = dyn_cast<SubRegion>(MR)) {
      MR = SR->getSuperRegion();
      SuperRegions.insert(MR);
    }
  }

  StringLengthsTy::Factory &F = State->get_context<StringLengths>();

  // Then loop over the entries in the current state.
  for (StringLengthsTy::iterator I = Entries.begin(),
       E = Entries.end(); I != E; ++I) {
    const MemRegion *MR = I.getKey();

    // Is this entry for a super-region of a changed region?
    if (SuperRegions.count(MR)) {
      Entries = F.remove(Entries, MR);
      continue;
    }

    // Is this entry for a sub-region of a changed region?
    const MemRegion *Super = MR;
    while (const SubRegion *SR = dyn_cast<SubRegion>(Super)) {
      Super = SR->getSuperRegion();
      if (Invalidated.count(Super)) {
        Entries = F.remove(Entries, MR);
        break;
      }
    }
  }

  return State->set<StringLengths>(Entries);
}

void BasicStringBoundChecker::checkDeadSymbols(SymbolReaper &SR,
                                               CheckerContext &C) const {
/*  ProgramStateRef state = C.getState();
  StringLengthsTy Entries = state->get<StringLengths>();
  if (Entries.isEmpty())
    return;

  StringLengthsTy::Factory &F = state->get_context<StringLengths>();
  for (StringLengthsTy::iterator I = Entries.begin(), E = Entries.end(); I != E;
       ++I) {
    const MemRegion *MR = I.getKey();
    if (!SR.isLiveRegion(MR))
      Entries = F.remove(Entries, MR);
  }

  state = state->set<StringLengths>(Entries);
  C.addTransition(state);*/
}


typedef SummaryMap<const MemRegion *, BasicStringState> SummaryBSSMap;

// Summary == vector of two parts:
// 1. Set of accesses that happened in this call
// 2. Map of all string lengths that are reasoned in this function
const void *
BasicStringBoundChecker::evalSummaryPopulate(ProgramStateRef State) const {
  VoidVector *Summary = new VoidVector;
  SummaryAccessSet *SumAccSet = new SummaryAccessSet;
  SummaryAccessesTy Accesses = State->get<SummaryAccesses>();
  for (SummaryAccessesTy::iterator I = Accesses.begin(), E = Accesses.end();
       I != E; ++I)
    SumAccSet->insert(*I);
  Summary->push_back(SumAccSet);
  StringLengthsTy Lengths = State->get<StringLengths>();
  SummaryBSSMap *States = new SummaryBSSMap(toMap(Lengths));
  Summary->push_back(States);
  return Summary;
}

void BasicStringBoundChecker::evalSummaryApply(
    Summarizer &S, const CallEvent &Call, const void *Summary,
    CheckerContext &C, ProgramStateRef CalleeEndState) const {
  const VoidVector *Summ = (const VoidVector *)Summary;
  ProgramStateRef State = Call.getState();
  const SummaryAccessSet *Accesses = (const SummaryAccessSet *)(*Summ)[0];
  for (SummaryAccessSet::const_iterator I = Accesses->begin(),
       E = Accesses->end(); I != E; ++I) {
    StringAccess Acc = I->Actualize(S);
    if (Acc.String) {
      SourceRange R = Call.getOriginExpr()->getSourceRange();
      if (State->isTainted(Acc.Index)) {
        reportIndexOverflow(C, State, Acc.String, R, UnknownVal(), Acc.Index,
                            OOB_Tainted);
        continue;
      }
      if (checkNegativeIndex(Acc.Index, Acc.String, R, State, C))
        continue;
      checkOverflow(Acc.Length, Acc.Index, Acc.String, R, State, C);
    }
  }
  const SummaryBSSMap &SMap = ((const SummaryBSSMap *)(*Summ)[1])->Actualize(S);
  for (SummaryBSSMap::const_iterator I = SMap.begin(), E = SMap.end(); I != E;
       ++I) {
    const MemRegion *MR = I->first;
    if (MR)
      State = State->set<StringLengths>(MR, I->second);
  }
  C.addTransition(State);
}

SVal BasicStringBoundChecker::evalSummarySVal(Summarizer &S, SVal SV) const {
  const SymbolMetadata *MetaSym =
      dyn_cast_or_null<SymbolMetadata>(SV.getAsSymbol());
  if (MetaSym) {
    const MemRegion *MR = MetaSym->getRegion();
    const BasicStringState *BSS = S.getCall().getState()->get<StringLengths>(MR);
    if (BSS)
      return BSS->Length;
  }
  return SV;
}


static void dumpPretty(llvm::raw_ostream &os, const MemRegion *MR) {
  if (MR->canPrintPretty()) {
    MR->printPretty(os);
  } else if (const SymbolicRegion *SR = dyn_cast<SymbolicRegion>(MR)) {
    SymbolRef Sym = SR->getSymbol();
    if (const SymbolRegionValue *SRV = dyn_cast<SymbolRegionValue>(Sym))
      dumpPretty(os, SRV->getRegion());
    else
      Sym->dumpToStream(os);
  } else {
    MR->dumpToStream(os);
  }
}

// FIXME: Unify with Julia's code (IntegerOverflowChecker)
static void addRangeInformation(const SVal &Val, ProgramStateRef state,
                                llvm::raw_ostream &Stream) {
  std::string S;
  llvm::raw_string_ostream StreamRange(S);
  if (Optional<nonloc::SymbolVal> Sym = Val.getAs<nonloc::SymbolVal>()) {
    std::string SymbolName;
    llvm::raw_string_ostream NameStream(SymbolName);
    NameStream << *Sym << " : ";
    state->getConstraintManager().print(state, StreamRange, "\n", "\n");
    StreamRange.flush();
    NameStream.flush();
    size_t from = S.find(SymbolName);
    if (from != std::string::npos) {
      size_t to = S.find("\n", from);
      from += SymbolName.length();
      Stream << "range: " << S.substr(from, to - from);
      return;
    }
  }
  Stream << "value: " << Val;
}

void BasicStringBoundChecker::printState(raw_ostream &Out,
                                         ProgramStateRef State,
                                         const char *NL,
                                         const char *Sep) const {
  StringLengthsTy Lengths = State->get<StringLengths>();

  if (Lengths.isEmpty())
    return;

  Out << Sep << "BasicStringBoundChecker:" << NL;

  for (StringLengthsTy::iterator I = Lengths.begin(), E = Lengths.end();
       I != E; ++I) {
    Out << I->first << " : " << I->second.Length;
    Out << NL;
  }
  Out << Sep;

}

void BasicStringBoundChecker::reportIndexOverflow(
    CheckerContext &C, ProgramStateRef state, const MemRegion *MR,
    SourceRange Range, SVal Len, SVal Index, OOB_Kind K) const {

  ExplodedNode *Sink = C.generateSink(state);
  if (!Sink)
    return;

  if (!BT)
    BT.reset(new BugType("Out-of-bound access for basic_string",
                         "UNDEFINED_BEHAVIOR_BUFFER_OVERFLOW"));

  SmallString<256> buf;
  llvm::raw_svector_ostream os(buf);
  os << "Out of bound access for ";
  dumpPretty(os, MR);
  os << " ";
  switch (K) {
  case OOB_Precedes:
    os << "(accessed memory precedes memory block).";
    break;
  case OOB_Excedes:
    os << "(access exceeds upper limit of memory block).";
    break;
  case OOB_Tainted:
    os << "(index is tainted).";
    break;
  }

  os << " Index has ";
  addRangeInformation(Index, state, os);
  if (K != OOB_Precedes) {
    os << ", length has ";
    addRangeInformation(Len, state, os);
  }
  os << ".";

  BugReport *R = new BugReport(*BT, os.str(), Sink);
  R->markInteresting(MR);
  R->addVisitor(new BasicStringVisitor(MR));
  R->addRange(Range);
  C.emitReport(R);
}

void ento::registerBasicStringBoundChecker(CheckerManager &mgr) {
  if (mgr.getLangOpts().CPlusPlus)
    mgr.registerChecker<BasicStringBoundChecker>();
}

PathDiagnosticPiece *BasicStringBoundChecker::BasicStringVisitor::VisitNode(
    const ExplodedNode *N, const ExplodedNode *PrevN, BugReporterContext &BRC,
    BugReport &BR) {
  ProgramStateRef state = N->getState();
  ProgramStateRef statePrev = PrevN->getState();

  const BasicStringState *BSS = state->get<StringLengths>(Region);
  const BasicStringState *BSSPrev = statePrev->get<StringLengths>(Region);
  if (!BSS)
    return 0;

  const Stmt *S = 0;
  std::string Msg;
  llvm::raw_string_ostream os(Msg);
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
  if (isCreated(BSS, BSSPrev, S)) {
    os << "String is reasoned here first with length ";
    addRangeInformation(BSS->Length, state, os);
    StackHint = new StackHintGeneratorForMemRegion(
        Region, "Returned; string was reasoned about");
  } else if (isChanged(BSS, BSSPrev, S)) {
    os << "String is changed here; new length has ";
    addRangeInformation(BSS->Length, state, os);
    StackHint = new StackHintGeneratorForMemRegion(
        Region, "Returning; string was modified");
  }
  os.flush();

  if (Msg.empty()) {
    assert(!StackHint);
    return 0;
  }
  assert(StackHint);

  // Generate the extra diagnostic.
  PathDiagnosticLocation Pos(S, BRC.getSourceManager(),
                             N->getLocationContext());
  return new PathDiagnosticEventPiece(Pos, Msg, true, StackHint);
}
