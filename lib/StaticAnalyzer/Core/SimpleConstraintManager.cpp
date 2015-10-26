//== SimpleConstraintManager.cpp --------------------------------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines SimpleConstraintManager, a class that holds code shared
//  between BasicConstraintManager and RangeConstraintManager.
//
//===----------------------------------------------------------------------===//

#include "SimpleConstraintManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/APSIntType.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"

namespace clang {

namespace ento {

SimpleConstraintManager::~SimpleConstraintManager() {}

bool SimpleConstraintManager::canReasonAbout(ProgramStateRef state, SVal X) const {
  Optional<nonloc::SymbolVal> SymVal = X.getAs<nonloc::SymbolVal>();
  if (SymVal && SymVal->isExpression()) {
    const SymExpr *SE = SymVal->getSymbol();

    if (const SymIntExpr *SIE = dyn_cast<SymIntExpr>(SE)) {
      switch (SIE->getOpcode()) {
          // We don't reason yet about bitwise-constraints on symbolic values.
        case BO_And:
        case BO_Or:
        case BO_Xor:
          return false;
        // We don't reason yet about these arithmetic constraints on
        // symbolic values.
        case BO_Mul:
        case BO_Div:
        case BO_Rem:
        case BO_Shl:
        case BO_Shr:
          return false;
        // All other cases.
        default:
          return true;
      }
    }
    if (isa<SymFloatExpr>(SE)) {
      return true;
    }
    if (const SymSymExpr *SSE = dyn_cast<SymSymExpr>(SE)) {
      if (BinaryOperator::isComparisonOp(SSE->getOpcode())) {
        // We handle Loc <> Loc comparisons, but not (yet) NonLoc <> NonLoc.
        if (Loc::isLocType(SSE->getLHS()->getType())) {
          // Temporary workaround about NonLoc::LocAsInteger
          // whose symbols have Loc types
          if (Loc::isLocType(SSE->getRHS()->getType()))
          //  assert(Loc::isLocType(SSE->getRHS()->getType()));
            return true;
        } else if (canReasonAboutSymbol(state, SSE))
          return true;
      }
    }

    return false;
  }

  return true;
}

ProgramStateRef SimpleConstraintManager::assume(ProgramStateRef state,
                                               DefinedSVal Cond,
                                               bool Assumption) {
  // If we have a Loc value, cast it to a bool NonLoc first.
  if (Optional<Loc> LV = Cond.getAs<Loc>()) {
    SValBuilder &SVB = state->getStateManager().getSValBuilder();
    QualType T;
    const MemRegion *MR = LV->getAsRegion();
    if (const TypedRegion *TR = dyn_cast_or_null<TypedRegion>(MR))
      T = TR->getLocationType();
    else
      T = SVB.getContext().VoidPtrTy;

    Cond = SVB.evalCast(*LV, SVB.getContext().BoolTy, T).castAs<DefinedSVal>();
  }

  return assume(state, Cond.castAs<NonLoc>(), Assumption);
}

ProgramStateRef SimpleConstraintManager::assume(ProgramStateRef state,
                                               NonLoc cond,
                                               bool assumption) {
  state = assumeAux(state, cond, assumption);
  if (NotifyAssumeClients && SU)
    return SU->processAssume(state, cond, assumption);
  return state;
}


ProgramStateRef
SimpleConstraintManager::assumeAuxForSymbol(ProgramStateRef State,
                                            SymbolRef Sym, bool Assumption) {
  BasicValueFactory &BVF = getBasicVals();
  QualType T = Sym->getType();

  // None of the constraint solvers currently support non-integer types.
  if (!T->isIntegralOrEnumerationType() && !T->isRealFloatingType())
    return State;
  if (T->isRealFloatingType()) {
    const llvm::APFloat &zero =
        BVF.getValue(llvm::APFloat(0.0)).getFloat();
    if (Assumption)
      return assumeSymNE(State, Sym, zero, zero);
    else
      return assumeSymEQ(State, Sym, zero, zero);
  }

  const llvm::APSInt &zero = BVF.getValue(0, T).getInt();
  if (Assumption)
    return assumeSymNE(State, Sym, zero, zero);
  else
    return assumeSymEQ(State, Sym, zero, zero);

}

ProgramStateRef SimpleConstraintManager::assumeAux(ProgramStateRef state,
                                                  NonLoc Cond,
                                                  bool Assumption) {

  // We cannot reason about SymSymExprs, and can only reason about some
  // SymIntExprs.
  if (!canReasonAbout(state, Cond)) {
    // Just add the constraint to the expression without trying to simplify.
    SymbolRef sym = Cond.getAsSymExpr();
    return assumeAuxForSymbol(state, sym, Assumption);
  }

  switch (Cond.getSubKind()) {
  default:
    llvm_unreachable("'Assume' not implemented for this NonLoc");

  case nonloc::SymbolValKind: {
    nonloc::SymbolVal SV = Cond.castAs<nonloc::SymbolVal>();
    SymbolRef sym = SV.getSymbol();
    assert(sym);

    // Handle SymbolData.
    if (!SV.isExpression()) {
      return assumeAuxForSymbol(state, sym, Assumption);

    // Handle symbolic expression.
    } else if (const SymIntExpr *SE = dyn_cast<SymIntExpr>(sym)) {
      // We can only simplify expressions whose RHS is an integer.

      BinaryOperator::Opcode op = SE->getOpcode();
      if (BinaryOperator::isComparisonOp(op)) {
        if (!Assumption)
          op = BinaryOperator::negateComparisonOp(op);

        return assumeSymRel(state, SE->getLHS(), op, SE->getRHS());
      }

    } else if (const SymFloatExpr *SE = dyn_cast<SymFloatExpr>(sym)) {

      BinaryOperator::Opcode op = SE->getOpcode();
      if (BinaryOperator::isComparisonOp(op)) {
        if (!Assumption)
          op = BinaryOperator::negateComparisonOp(op);

        return assumeSymRel(state, SE->getLHS(), op, SE->getRHS());
      }
    } else if (const SymSymExpr *SSE = dyn_cast<SymSymExpr>(sym)) {
      SymbolManager &SymMgr = getSymbolManager();
      BinaryOperator::Opcode Op = SSE->getOpcode();
      if (!Assumption)
        Op = BinaryOperator::negateComparisonOp(Op);
      assert(BinaryOperator::isComparisonOp(Op));

      if (Loc::isLocType(SSE->getLHS()->getType()) &&
          Loc::isLocType(SSE->getRHS()->getType())) {
        // Translate "a != b" to "(b - a) != 0".
        // We invert the order of the operands as a heuristic for how loop
        // conditions are usually written ("begin != end") as compared to length
        // calculations ("end - begin"). The more correct thing to do would be to
        // canonicalize "a - b" and "b - a", which would allow us to treat
        // "a != b" and "b != a" the same.
        assert(Loc::isLocType(SSE->getRHS()->getType()));
        QualType DiffTy = SymMgr.getContext().getPointerDiffType();
        SymbolRef Subtraction = SymMgr.getSymSymExpr(SSE->getRHS(), BO_Sub,
                                                     SSE->getLHS(), DiffTy);

        const llvm::APSInt &Zero = getBasicVals().getValue(0, DiffTy).getInt();
        Op = BinaryOperator::reverseComparisonOp(Op);
        return assumeSymRel(state, Subtraction, Op, Zero);
      } else if (!Loc::isLocType(SSE->getLHS()->getType()) &&
                 !Loc::isLocType(SSE->getRHS()->getType())) {
        // Only comparisons are supported now for NonLocs
        assert(BinaryOperator::isComparisonOp(Op));
        return assumeSymSymRel(state, SSE->getLHS(), Op, SSE->getRHS());
      }
    }

    // If we get here, there's nothing else we can do but treat the symbol as
    // opaque.
    return assumeAuxForSymbol(state, sym, Assumption);
  }

  case nonloc::ConcreteIntKind: {
    bool b = Cond.castAs<nonloc::ConcreteInt>().getValue() != 0;
    bool isFeasible = b ? Assumption : !Assumption;
    return isFeasible ? state : NULL;
  }
  case nonloc::ConcreteFloatKind : {
    bool b = !Cond.castAs<nonloc::ConcreteFloat>().getValue().isZero();
    bool isFeasible = b ? Assumption : !Assumption;
    return isFeasible ? state : NULL;
  }

  case nonloc::LocAsIntegerKind:
    return assume(state, Cond.castAs<nonloc::LocAsInteger>().getLoc(),
                  Assumption);
  } // end switch
}

ProgramStateRef SimpleConstraintManager::assumeBound(ProgramStateRef state,
                                                     NonLoc Value,
                                                     const llvm::APSInt &From,
                                                     const llvm::APSInt &To,
                                                     bool InBound) {

  if (!canReasonAbout(state, Value)) {
    // Just add the constraint to the expression without trying to simplify.
    SymbolRef sym = Value.getAsSymExpr();
    return assumeSymBound(state, sym, From, To, InBound);
  }

  switch (Value.getSubKind()) {
  default:
    llvm_unreachable("'AssumeBound' not implemented for this NonLoc");

  case nonloc::LocAsIntegerKind:
  case nonloc::SymbolValKind: {
    if (SymbolRef sym = Value.getAsSymbol())
      return assumeSymBound(state, sym, From, To, InBound);
    return state;
  } // end switch

  case nonloc::ConcreteIntKind: {
    const llvm::APSInt &IntVal = Value.castAs<nonloc::ConcreteInt>().getValue();
    bool b = IntVal >= From && IntVal <= To;
    bool isFeasible = (b == InBound);
    return isFeasible ? state : NULL;
  }
  } // end switch
}

static void computeAdjustment(SymbolRef &Sym, llvm::APSInt &Adjustment) {
  // Is it a "($sym+constant1)" expression?
  if (const SymIntExpr *SE = dyn_cast<SymIntExpr>(Sym)) {
    BinaryOperator::Opcode Op = SE->getOpcode();
    if (Op == BO_Add || Op == BO_Sub) {
      Sym = SE->getLHS();
      Adjustment = APSIntType(Adjustment).convert(SE->getRHS());

      // Don't forget to negate the adjustment if it's being subtracted.
      // This should happen /after/ promotion, in case the value being
      // subtracted is, say, CHAR_MIN, and the promoted type is 'int'.
      if (Op == BO_Sub)
        Adjustment = -Adjustment;
    }
  }

}

ProgramStateRef SimpleConstraintManager::assumeSymRel(ProgramStateRef state,
                                                     const SymExpr *LHS,
                                                     BinaryOperator::Opcode op,
                                                     const llvm::APSInt& Int) {
  assert(BinaryOperator::isComparisonOp(op) &&
         "Non-comparison ops should be rewritten as comparisons to zero.");

  // Get the type used for calculating wraparound.
  BasicValueFactory &BVF = getBasicVals();
  APSIntType WraparoundType = BVF.getAPSIntType(LHS->getType());

  // We only handle simple comparisons of the form "$sym == constant"
  // or "($sym+constant1) == constant2".
  // The adjustment is "constant1" in the above expression. It's used to
  // "slide" the solution range around for modular arithmetic. For example,
  // x < 4 has the solution [0, 3]. x+2 < 4 has the solution [0-2, 3-2], which
  // in modular arithmetic is [0, 1] U [UINT_MAX-1, UINT_MAX]. It's up to
  // the subclasses of SimpleConstraintManager to handle the adjustment.
  SymbolRef Sym = LHS;
  llvm::APSInt Adjustment = WraparoundType.getZeroValue();
  computeAdjustment(Sym, Adjustment);

  // Convert the right-hand side integer as necessary.
  APSIntType ComparisonType = std::max(WraparoundType, APSIntType(Int));
  llvm::APSInt ConvertedInt = ComparisonType.convert(Int);

  // Prefer unsigned comparisons.
  if (ComparisonType.getBitWidth() == WraparoundType.getBitWidth() &&
      ComparisonType.isUnsigned() && !WraparoundType.isUnsigned())
    Adjustment.setIsSigned(false);

  switch (op) {
  default:
    llvm_unreachable("invalid operation not caught by assertion above");

  case BO_EQ:
    return assumeSymEQ(state, Sym, ConvertedInt, Adjustment);

  case BO_NE:
    return assumeSymNE(state, Sym, ConvertedInt, Adjustment);

  case BO_GT:
    return assumeSymGT(state, Sym, ConvertedInt, Adjustment);

  case BO_GE:
    return assumeSymGE(state, Sym, ConvertedInt, Adjustment);

  case BO_LT:
    return assumeSymLT(state, Sym, ConvertedInt, Adjustment);

  case BO_LE:
    return assumeSymLE(state, Sym, ConvertedInt, Adjustment);
  } // end switch
}

ProgramStateRef SimpleConstraintManager::assumeSymRel(ProgramStateRef state,
                                                     const SymExpr *LHS,
                                                     BinaryOperator::Opcode op,
                                                     const llvm::APFloat& Float) {
  assert(BinaryOperator::isComparisonOp(op) &&
         "Non-comparison ops should be rewritten as comparisons to zero.");
  SymbolRef Sym = LHS;
  llvm::APFloat Adjustment(Float.getZero(Float.getSemantics()));

  switch (op) {
  default:
    llvm_unreachable("invalid operation not caught by assertion above");

  case BO_EQ:
    return assumeSymEQ(state, Sym, Float, Adjustment);

  case BO_NE:
    return assumeSymNE(state, Sym, Float, Adjustment);

  case BO_GT:
    return assumeSymGT(state, Sym, Float, Adjustment);

  case BO_GE:
    return assumeSymGE(state, Sym, Float, Adjustment);

  case BO_LT:
    return assumeSymLT(state, Sym, Float, Adjustment);

  case BO_LE:
    return assumeSymLE(state, Sym, Float, Adjustment);
  } // end switch
}

ProgramStateRef
SimpleConstraintManager::bindCastSVal(ProgramStateRef State,
                                      const LocationContext *LCtx,
                                      const Stmt *S, SVal &Val, QualType castTy,
                                      QualType originalTy) {
  if (castTy == originalTy)
    return State;
  SVal NewVal = SVB.evalCast(Val, castTy, originalTy);
  State = State->BindExpr(S, LCtx, NewVal);
  if (Val.getAsSymbol() && NewVal.getAsSymbol())
    return castConstraints(State, Val.getAsSymbol(), NewVal.getAsSymbol());
  return State;
}

ProgramStateRef
SimpleConstraintManager::assumeSymBound(ProgramStateRef state, SymbolRef sym,
                                        const llvm::APSInt &From,
                                        const llvm::APSInt &To,
                                        bool InBound) {
  // Get the type used for calculating wraparound.
  BasicValueFactory &BVF = getBasicVals();
  APSIntType WraparoundType = BVF.getAPSIntType(sym->getType());

  llvm::APSInt Adjustment = WraparoundType.getZeroValue();
  SymbolRef Sym = sym;
  computeAdjustment(Sym, Adjustment);

  // Convert the right-hand side integer as necessary.
  APSIntType ComparisonType = std::max(WraparoundType, APSIntType(From));
  llvm::APSInt ConvertedFrom = ComparisonType.convert(From);
  llvm::APSInt ConvertedTo = ComparisonType.convert(To);

  // Prefer unsigned comparisons.
  if (ComparisonType.getBitWidth() == WraparoundType.getBitWidth() &&
      ComparisonType.isUnsigned() && !WraparoundType.isUnsigned())
    Adjustment.setIsSigned(false);

  if (InBound)
    return assumeSymInBound(state, Sym, ConvertedFrom, ConvertedTo, Adjustment);
  return assumeSymOutOfBound(state, Sym, ConvertedFrom, ConvertedTo, Adjustment);
}

ProgramStateRef
SimpleConstraintManager::assumeSymSymRel(ProgramStateRef state,
                                         const SymExpr *LHS,
                                         BinaryOperator::Opcode op,
                                         const SymExpr *RHS) {
  SymbolRef Sym = LHS;
  APValue Adjustment;
  if (LHS->getType()->isIntegralOrEnumerationType() ||
      RHS->getType()->isIntegralOrEnumerationType()) {
    assert(BinaryOperator::isComparisonOp(op) &&
           "Non-comparison ops should be rewritten as comparisons to zero.");

    // Get the type used for calculating wraparound.
    BasicValueFactory &BVF = getBasicVals();
    APSIntType WraparoundType = BVF.getAPSIntType(LHS->getType());

   // Comment about adjustment is upper
    llvm::APSInt Adj = WraparoundType.getZeroValue();
  //  computeAdjustment(Sym, Adj);

    // Convert the right-hand side integer as necessary.
    APSIntType ComparisonType =
        std::max(WraparoundType, APSIntType(BVF.getMaxValue(RHS->getType()).getInt()));
    // FIXME: convert type for symbols

    // Prefer unsigned comparisons.
    if (ComparisonType.getBitWidth() == WraparoundType.getBitWidth() &&
        ComparisonType.isUnsigned() && !WraparoundType.isUnsigned())
      Adj.setIsSigned(false);
    Adjustment = APValue(Adj);
  } else {
    Adjustment = APValue(llvm::APFloat(SVB.getContext().getFloatTypeSemantics(
                                         Sym->getType()), 0));
  }

  switch (op) {
  default:
    llvm_unreachable("invalid operation not caught by assertion above");
  // FIXME: Consider adjustment for LHS
  case BO_EQ:
    return assumeSymSymEQ(state, Sym, RHS, Adjustment);

  case BO_NE:
    return assumeSymSymNE(state, Sym, RHS, Adjustment);

  case BO_GT:
    return assumeSymSymGT(state, Sym, RHS, Adjustment);

  case BO_GE:
    return assumeSymSymGE(state, Sym, RHS, Adjustment);

  case BO_LT:
    return assumeSymSymLT(state, Sym, RHS, Adjustment);

  case BO_LE:
    return assumeSymSymLE(state, Sym, RHS, Adjustment);
  } // end switch
}

} // end of namespace ento

} // end of namespace clang
