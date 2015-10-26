//=== BasicValueFactory.cpp - Basic values for Path Sens analysis --*- C++ -*-//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines BasicValueFactory, a class that manages the lifetime
//  of APSInt objects and symbolic constraints used by ExprEngine
//  and related classes.
//
//===----------------------------------------------------------------------===//

#include "clang/AST/ASTContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/BasicValueFactory.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/Store.h"

using namespace clang;
using namespace ento;

void CompoundValData::Profile(llvm::FoldingSetNodeID& ID, QualType T,
                              llvm::ImmutableList<SVal> L) {
  T.Profile(ID);
  ID.AddPointer(L.getInternalPointer());
}

void LazyCompoundValData::Profile(llvm::FoldingSetNodeID& ID,
                                  const StoreRef &store,
                                  const TypedValueRegion *region) {
  ID.AddPointer(store.getStore());
  ID.AddPointer(region);
}

typedef std::pair<SVal, uintptr_t> SValData;
typedef std::pair<SVal, SVal> SValPair;

namespace llvm {
template<> struct FoldingSetTrait<SValData> {
  static inline void Profile(const SValData& X, llvm::FoldingSetNodeID& ID) {
    X.first.Profile(ID);
    ID.AddPointer( (void*) X.second);
  }
};

template<> struct FoldingSetTrait<SValPair> {
  static inline void Profile(const SValPair& X, llvm::FoldingSetNodeID& ID) {
    X.first.Profile(ID);
    X.second.Profile(ID);
  }
};
}

typedef llvm::FoldingSet<llvm::FoldingSetNodeWrapper<SValData> >
  PersistentSValsTy;

BasicValueFactory::~BasicValueFactory() {
  // Note that the dstor for the contents of APSIntSet will never be called,
  // so we iterate over the set and invoke the dstor for each APSInt.  This
  // frees an aux. memory allocated to represent very large constants.
  for (APValueSetTy::iterator I=APValueSet.begin(), E=APValueSet.end(); I!=E; ++I)
    I->getValue().~APValue();

  delete (PersistentSValsTy*) PersistentSVals;
}

const APValue& BasicValueFactory::getValue(const APValue& X) {
  llvm::FoldingSetNodeID ID;
  void *InsertPos;
  typedef llvm::FoldingSetNodeWrapper<APValue> FoldNodeTy;

  X.Profile(ID);
  FoldNodeTy* P = APValueSet.FindNodeOrInsertPos(ID, InsertPos);
  if (!P) {
    P = (FoldNodeTy*) BPAlloc.Allocate<FoldNodeTy>();
    new (P) FoldNodeTy(X);
    APValueSet.InsertNode(P, InsertPos);
  }

  return *P;
}

const APValue& BasicValueFactory::getValue(const llvm::APSInt& X) {
  APValue V(X);
  return getValue(V);
}

const APValue& BasicValueFactory::getValue(const llvm::APFloat& X) {
  APValue V(X);
  return getValue(V);
}

const APValue& BasicValueFactory::getValue(const llvm::APInt& X,
                                                bool isUnsigned) {
  llvm::APSInt I(X, isUnsigned);
  APValue V(I);
  return getValue(V);
}

const APValue& BasicValueFactory::getValue(uint64_t X, unsigned BitWidth,
                                           bool isUnsigned) {
  llvm::APSInt I(BitWidth, isUnsigned);
  I = X;
  APValue V(I);
  return getValue(V);
}

const APValue& BasicValueFactory::getValue(uint64_t X, QualType T) {
  APValue V(getAPSIntType(T).getValue(X));
  return getValue(V);
}

const CompoundValData*
BasicValueFactory::getCompoundValData(QualType T,
                                      llvm::ImmutableList<SVal> Vals) {

  llvm::FoldingSetNodeID ID;
  CompoundValData::Profile(ID, T, Vals);
  void *InsertPos;

  CompoundValData* D = CompoundValDataSet.FindNodeOrInsertPos(ID, InsertPos);

  if (!D) {
    D = (CompoundValData*) BPAlloc.Allocate<CompoundValData>();
    new (D) CompoundValData(T, Vals);
    CompoundValDataSet.InsertNode(D, InsertPos);
  }

  return D;
}

const LazyCompoundValData*
BasicValueFactory::getLazyCompoundValData(const StoreRef &store,
                                          const TypedValueRegion *region) {
  llvm::FoldingSetNodeID ID;
  LazyCompoundValData::Profile(ID, store, region);
  void *InsertPos;

  LazyCompoundValData *D =
    LazyCompoundValDataSet.FindNodeOrInsertPos(ID, InsertPos);

  if (!D) {
    D = (LazyCompoundValData*) BPAlloc.Allocate<LazyCompoundValData>();
    new (D) LazyCompoundValData(store, region);
    LazyCompoundValDataSet.InsertNode(D, InsertPos);
  }

  return D;
}

const APValue*
BasicValueFactory::evalAPSInt(BinaryOperator::Opcode Op,
                             const llvm::APSInt& V1, const llvm::APSInt& V2) {

  switch (Op) {
    default:
      assert (false && "Invalid Opcode.");

    case BO_Mul:
      return &getValue( V1 * V2 );

    case BO_Div:
      if (V2 == 0) // Avoid division by zero
        return NULL;
      return &getValue( V1 / V2 );

    case BO_Rem:
      if (V2 == 0) // Avoid division by zero
        return NULL;
      return &getValue( V1 % V2 );

    case BO_Add:
      return &getValue( V1 + V2 );

    case BO_Sub:
      return &getValue( V1 - V2 );

    case BO_Shl: {

      // FIXME: This logic should probably go higher up, where we can
      // test these conditions symbolically.

      // FIXME: Expand these checks to include all undefined behavior.

      if (V2.isSigned() && V2.isNegative())
        return NULL;

      uint64_t Amt = V2.getZExtValue();

      if (Amt > V1.getBitWidth())
        return NULL;

      return &getValue( V1.operator<<( (unsigned) Amt ));
    }

    case BO_Shr: {

      // FIXME: This logic should probably go higher up, where we can
      // test these conditions symbolically.

      // FIXME: Expand these checks to include all undefined behavior.

      if (V2.isSigned() && V2.isNegative())
        return NULL;

      uint64_t Amt = V2.getZExtValue();

      if (Amt > V1.getBitWidth())
        return NULL;

      return &getValue( V1.operator>>( (unsigned) Amt ));
    }

    case BO_LT:
      return &getTruthValue( V1 < V2 );

    case BO_GT:
      return &getTruthValue( V1 > V2 );

    case BO_LE:
      return &getTruthValue( V1 <= V2 );

    case BO_GE:
      return &getTruthValue( V1 >= V2 );

    case BO_EQ:
      return &getTruthValue( V1 == V2 );

    case BO_NE:
      return &getTruthValue( V1 != V2 );

      // Note: LAnd, LOr, Comma are handled specially by higher-level logic.

    case BO_And:
      return &getValue( V1 & V2 );

    case BO_Or:
      return &getValue( V1 | V2 );

    case BO_Xor:
      return &getValue( V1 ^ V2 );
  }
}

const APValue*
BasicValueFactory::evalAPFloat(BinaryOperator::Opcode Op,
                             const llvm::APFloat& V1, const llvm::APFloat& V2) {
  llvm::APFloat Val1(V1);
  llvm::APFloat Val2(V2);
  bool losesInfo;
  if(Val1.semanticsPrecision(Val1.getSemantics()) <
      Val2.semanticsPrecision(Val2.getSemantics())) {
    Val1.convert(Val2.getSemantics(),
                 llvm::APFloat::rmNearestTiesToEven,
                 &losesInfo);

  } else if (Val1.semanticsPrecision(Val1.getSemantics()) >
              Val2.semanticsPrecision(Val2.getSemantics())) {
    Val2.convert(Val1.getSemantics(),
                 llvm::APFloat::rmNearestTiesToEven,
                 &losesInfo);
  }
  switch (Op) {
    default:
      assert (false && "Invalid Opcode.");

    case BO_Mul:
      Val1.multiply(Val2, llvm::APFloat::rmNearestTiesToEven);
      return &getValue(Val1);
    case BO_Div:
      Val1.divide(Val2,llvm::APFloat::rmNearestTiesToEven);
      return &getValue(Val1);
    case BO_Add:
      Val1.add(Val2,llvm::APFloat::rmNearestTiesToEven);
      return &getValue(Val1);

    case BO_Sub:
      Val1.subtract(Val2,llvm::APFloat::rmNearestTiesToEven);
      return &getValue(Val1);
    case BO_LT:
      return &getTruthValue( Val1.compareWithConversion(Val2) == llvm::APFloat::cmpLessThan );
    case BO_GT:
      return &getTruthValue( Val1.compareWithConversion(Val2) == llvm::APFloat::cmpGreaterThan );

    case BO_LE:
      return &getTruthValue( Val1.compareWithConversion(Val2) == llvm::APFloat::cmpLessThan ||
                              Val1.compareWithConversion(Val2) == llvm::APFloat::cmpEqual);

    case BO_GE:
      return &getTruthValue( Val1.compareWithConversion(Val2) == llvm::APFloat::cmpGreaterThan ||
                              Val1.compareWithConversion(Val2) == llvm::APFloat::cmpEqual );

    case BO_EQ:
      return &getTruthValue(Val1.compareWithConversion(Val2) == llvm::APFloat::cmpEqual );

    case BO_NE:
      return &getTruthValue(Val1.compareWithConversion(Val2) != llvm::APFloat::cmpEqual );

  }
}

const std::pair<SVal, uintptr_t>&
BasicValueFactory::getPersistentSValWithData(const SVal& V, uintptr_t Data) {

  // Lazily create the folding set.
  if (!PersistentSVals) PersistentSVals = new PersistentSValsTy();

  llvm::FoldingSetNodeID ID;
  void *InsertPos;
  V.Profile(ID);
  ID.AddPointer((void*) Data);

  PersistentSValsTy& Map = *((PersistentSValsTy*) PersistentSVals);

  typedef llvm::FoldingSetNodeWrapper<SValData> FoldNodeTy;
  FoldNodeTy* P = Map.FindNodeOrInsertPos(ID, InsertPos);

  if (!P) {
    P = (FoldNodeTy*) BPAlloc.Allocate<FoldNodeTy>();
    new (P) FoldNodeTy(std::make_pair(V, Data));
    Map.InsertNode(P, InsertPos);
  }

  return P->getValue();
}
