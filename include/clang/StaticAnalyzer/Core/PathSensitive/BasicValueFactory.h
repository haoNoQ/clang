//=== BasicValueFactory.h - Basic values for Path Sens analysis --*- C++ -*---//
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

#ifndef LLVM_CLANG_GR_BASICVALUEFACTORY_H
#define LLVM_CLANG_GR_BASICVALUEFACTORY_H

#include "clang/AST/ASTContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/APSIntType.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/SVals.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/StoreRef.h"

namespace clang {
namespace ento {

class CompoundValData : public llvm::FoldingSetNode {
  QualType T;
  llvm::ImmutableList<SVal> L;

public:
  CompoundValData(QualType t, llvm::ImmutableList<SVal> l)
    : T(t), L(l) {}

  QualType getType() const { return T; }

  typedef llvm::ImmutableList<SVal>::iterator iterator;
  iterator begin() const { return L.begin(); }
  iterator end() const { return L.end(); }

  static void Profile(llvm::FoldingSetNodeID& ID, QualType T,
                      llvm::ImmutableList<SVal> L);

  void Profile(llvm::FoldingSetNodeID& ID) { Profile(ID, T, L); }
};

class LazyCompoundValData : public llvm::FoldingSetNode {
  StoreRef store;
  const TypedValueRegion *region;
public:
  LazyCompoundValData(const StoreRef &st, const TypedValueRegion *r)
    : store(st), region(r) {}

  const void *getStore() const { return store.getStore(); }
  const TypedValueRegion *getRegion() const { return region; }

  static void Profile(llvm::FoldingSetNodeID& ID,
                      const StoreRef &store,
                      const TypedValueRegion *region);

  void Profile(llvm::FoldingSetNodeID& ID) { Profile(ID, store, region); }
};

class BasicValueFactory {
  typedef llvm::FoldingSet<llvm::FoldingSetNodeWrapper<APValue> >
          APValueSetTy;

  ASTContext &Ctx;
  llvm::BumpPtrAllocator BPAlloc;

  APValueSetTy   APValueSet;

  void *        PersistentSVals;

  llvm::ImmutableList<SVal>::Factory SValListFactory;
  llvm::FoldingSet<CompoundValData>  CompoundValDataSet;
  llvm::FoldingSet<LazyCompoundValData> LazyCompoundValDataSet;

  // This is private because external clients should use the factory
  // method that takes a QualType.
  const APValue& getValue(uint64_t X, unsigned BitWidth, bool isUnsigned);

public:
  BasicValueFactory(ASTContext &ctx)
  : Ctx(ctx), PersistentSVals(0), SValListFactory(BPAlloc) {}

  ~BasicValueFactory();

  ASTContext &getContext() const { return Ctx; }

  llvm::BumpPtrAllocator &getAllocator() { return BPAlloc; }

  const APValue& getValue(const llvm::APSInt& X);
  const APValue& getValue(const llvm::APInt& X, bool isUnsigned);
  const APValue& getValue(uint64_t X, QualType T);
  const APValue& getValue(const llvm::APFloat& X);
  const APValue& getValue(const APValue& X);

  /// Returns the type of the APSInt used to store values of the given QualType.
  APSIntType getAPSIntType(QualType T) const {
    assert(T->isIntegralOrEnumerationType() || Loc::isLocType(T));
    return APSIntType(Ctx.getTypeSize(T),
                      !T->isSignedIntegerOrEnumerationType());
  }

  /// Convert - Create a new persistent APSInt with the same value as 'From'
  ///  but with the bitwidth and signedness of 'To'.
  const APValue &Convert(const llvm::APSInt& To,
                              const llvm::APSInt& From) {
    APSIntType TargetType(To);
    if (TargetType == APSIntType(From))
      return getValue(From);

    return getValue(TargetType.convert(From));
  }
  
  const APValue &Convert(QualType T, const llvm::APSInt &From) {
    if (T->isRealFloatingType()) {
      llvm::APFloat val(0.0);
      val.convertFromAPInt(From, true, llvm::APFloat::rmNearestTiesToEven);

      return getValue(val);
    }
    APSIntType TargetType = getAPSIntType(T);
    if (TargetType == APSIntType(From))
      return getValue(From);
    
    return getValue(TargetType.convert(From));
  }

  const llvm::APSInt& getIntValue(uint64_t X, bool isUnsigned) {
    QualType T = isUnsigned ? Ctx.UnsignedIntTy : Ctx.IntTy;
    return getValue(X, T).getInt();
  }

  inline const APValue& getMaxValue(const APValue &v) {
    if (v.isInt())
      return getValue(APSIntType(v.getInt()).getMaxValue());
    else if (v.isFloat())
      return getValue(v.getFloat().getLargest(v.getFloat().getSemantics(), false));
    else {
      llvm_unreachable("Only int and float types are supported");
    }
  }

  inline const APValue& getMinValue(const APValue &v) {
    if (v.isInt())
      return getValue(APSIntType(v.getInt()).getMinValue());
    else if (v.isFloat())
      return getValue(v.getFloat().getLargest(v.getFloat().getSemantics(), true));
    else {
      llvm_unreachable("Only int and float types are supported");
    }
  }

  inline const APValue& getMaxValue(QualType T) {
    if (T->isRealFloatingType()) {
      llvm::APFloat val(0.0);
      return getValue(val.getLargest(Ctx.getFloatTypeSemantics(T), false));
    }
    return getValue(getAPSIntType(T).getMaxValue());
  }

  inline const APValue& getMinValue(QualType T) {
    if (T->isRealFloatingType()) {
      llvm::APFloat val(0.0);
      return getValue(val.getLargest(Ctx.getFloatTypeSemantics(T), true));
    }
    return getValue(getAPSIntType(T).getMinValue());
  }

  inline const APValue& Add1(const llvm::APSInt& V) {
    llvm::APSInt X = V;
    ++X;
    return getValue(X);
  }

  inline const APValue& Sub1(const llvm::APSInt& V) {
    llvm::APSInt X = V;
    --X;
    return getValue(X);
  }

  inline const APValue& getZeroWithPtrWidth(bool isUnsigned = true) {
    return getValue(0, Ctx.getTypeSize(Ctx.VoidPtrTy), isUnsigned);
  }

  inline const APValue &getIntWithPtrWidth(uint64_t X, bool isUnsigned) {
    return getValue(X, Ctx.getTypeSize(Ctx.VoidPtrTy), isUnsigned);
  }

  inline const APValue& getTruthValue(bool b, QualType T) {
    return getValue(b ? 1 : 0, Ctx.getTypeSize(T),
                    T->isUnsignedIntegerOrEnumerationType());
  }

  inline const APValue& getTruthValue(bool b) {
    return getTruthValue(b, Ctx.getLogicalOperationType());
  }

  const CompoundValData *getCompoundValData(QualType T,
                                            llvm::ImmutableList<SVal> Vals);

  const LazyCompoundValData *getLazyCompoundValData(const StoreRef &store,
                                            const TypedValueRegion *region);

  llvm::ImmutableList<SVal> getEmptySValList() {
    return SValListFactory.getEmptyList();
  }

  llvm::ImmutableList<SVal> consVals(SVal X, llvm::ImmutableList<SVal> L) {
    return SValListFactory.add(X, L);
  }

  const APValue* evalAPSInt(BinaryOperator::Opcode Op,
                                     const llvm::APSInt& V1,
                                     const llvm::APSInt& V2);
  const APValue* evalAPFloat(BinaryOperator::Opcode Op,
                               const llvm::APFloat& V1,
                               const llvm::APFloat& V2);
  const std::pair<SVal, uintptr_t>&
  getPersistentSValWithData(const SVal& V, uintptr_t Data);
};

} // end GR namespace

} // end clang namespace

#endif
