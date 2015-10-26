//== SimpleConstraintManager.h ----------------------------------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  Code shared between BasicConstraintManager and RangeConstraintManager.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_GR_SIMPLE_CONSTRAINT_MANAGER_H
#define LLVM_CLANG_GR_SIMPLE_CONSTRAINT_MANAGER_H

#include "clang/StaticAnalyzer/Core/PathSensitive/ConstraintManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"

namespace clang {

namespace ento {

class SimpleConstraintManager : public ConstraintManager {
  SubEngine *SU;
  SValBuilder &SVB;
public:
  SimpleConstraintManager(SubEngine *subengine, SValBuilder &SB)
    : SU(subengine), SVB(SB) {}
  virtual ~SimpleConstraintManager();

  //===------------------------------------------------------------------===//
  // Common implementation for the interface provided by ConstraintManager.
  //===------------------------------------------------------------------===//

  ProgramStateRef assume(ProgramStateRef state, DefinedSVal Cond,
                        bool Assumption);

  ProgramStateRef assume(ProgramStateRef state, NonLoc Cond, bool Assumption);

  ProgramStateRef assumeBound(ProgramStateRef state, NonLoc Value,
                              const llvm::APSInt &From, const llvm::APSInt &To,
                              bool InBound);

  ProgramStateRef assumeSymRel(ProgramStateRef state,
                              const SymExpr *LHS,
                              BinaryOperator::Opcode op,
                              const llvm::APSInt& Int);

  ProgramStateRef assumeSymRel(ProgramStateRef state,
                                const SymExpr *LHS,
                                BinaryOperator::Opcode op,
                                const llvm::APFloat& Float);

  ProgramStateRef bindCastSVal(ProgramStateRef State,
                               const LocationContext *LCtx, const Stmt *S,
                               SVal &Val, QualType castTy, QualType originalTy);

  ProgramStateRef assumeSymBound(ProgramStateRef state, SymbolRef Sym,
                                 const llvm::APSInt &From,
                                 const llvm::APSInt &To, bool InBound);

  ProgramStateRef assumeSymSymRel(ProgramStateRef state,
                                  const SymExpr *LHS,
                                  BinaryOperator::Opcode op,
                                  const SymExpr *RHS);

protected:

  //===------------------------------------------------------------------===//
  // Interface that subclasses must implement.
  //===------------------------------------------------------------------===//

  // Each of these is of the form "$sym+Adj <> V", where "<>" is the comparison
  // operation for the method being invoked.
  virtual ProgramStateRef assumeSymNE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymEQ(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymLT(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymGT(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymLE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymGE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APSInt& V,
                                     const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymNE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef assumeSymEQ(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef assumeSymLT(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef assumeSymGT(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef assumeSymLE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef assumeSymGE(ProgramStateRef state, SymbolRef sym,
                                     const llvm::APFloat& V,
                                     const llvm::APFloat& Adjustment) = 0;

  virtual ProgramStateRef castConstraints(ProgramStateRef State,
                                          SymbolRef OldSym,
                                          SymbolRef NewSym) = 0;

  virtual ProgramStateRef assumeSymInBound(ProgramStateRef state, SymbolRef sym,
                                           const llvm::APSInt& From,
                                           const llvm::APSInt& To,
                                           const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymOutOfBound(ProgramStateRef state,
                                              SymbolRef sym,
                                              const llvm::APSInt& From,
                                              const llvm::APSInt& To,
                                              const llvm::APSInt& Adjustment) = 0;

  virtual ProgramStateRef assumeSymSymNE(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;
  virtual ProgramStateRef assumeSymSymEQ(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;
  virtual ProgramStateRef assumeSymSymLT(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;
  virtual ProgramStateRef assumeSymSymGT(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;
  virtual ProgramStateRef assumeSymSymLE(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;

  virtual ProgramStateRef assumeSymSymGE(ProgramStateRef state, SymbolRef rhs,
                                         SymbolRef lhs,
                                         const APValue &Adjustment) = 0;


  //===------------------------------------------------------------------===//
  // Internal implementation.
  //===------------------------------------------------------------------===//

  BasicValueFactory &getBasicVals() const { return SVB.getBasicValueFactory(); }
  SymbolManager &getSymbolManager() const { return SVB.getSymbolManager(); }

  bool canReasonAbout(ProgramStateRef state, SVal X) const;
  virtual bool canReasonAboutSymbol(ProgramStateRef state,
                              const SymSymExpr *E) const = 0;

  ProgramStateRef assumeAux(ProgramStateRef state,
                                NonLoc Cond,
                                bool Assumption);

  ProgramStateRef assumeAuxForSymbol(ProgramStateRef State,
                                         SymbolRef Sym,
                                         bool Assumption);
};

} // end GR namespace

} // end clang namespace

#endif
