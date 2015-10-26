//== RangeConstraintManager.cpp - Manage range constraints.------*- C++ -*--==//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines RangeConstraintManager, a class that tracks simple
//  equality and inequality constraints on symbolic values of ProgramState.
//
//===----------------------------------------------------------------------===//

#include "SimpleConstraintManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/APSIntType.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/FunctionCallSummary.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "llvm/ADT/FoldingSet.h"
#include "llvm/ADT/ImmutableSet.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "clang/AST/APValue.h"

using namespace clang;
using namespace ento;
using llvm::APSInt;
using llvm::APFloat;

/// A Range represents the closed range [from, to].  The caller must
/// guarantee that from <= to.  Note that Range is immutable, so as not
/// to subvert RangeSet's immutability.
namespace {
class Range : public std::pair<const APValue*, const APValue*> {
public:
  Range(const APValue &from, const APValue &to)
    : std::pair<const APValue*, const APValue*>(&from, &to) {
    if (from.isInt() && to.isInt())
      assert(from.getInt() <= to.getInt());
    if (from.isFloat() && to.isFloat()) {
      assert(from.getFloat().compareWithConversion(to.getFloat()) == llvm::APFloat::cmpLessThan ||
          from.getFloat().compareWithConversion(to.getFloat()) == llvm::APFloat::cmpEqual);
    }
  }
  bool Includes(const APValue &v) const {
    if(v.isInt() && first->isInt() && second->isInt())
        return first->getInt() <= v.getInt() && v.getInt() <= second->getInt();
    else if(v.isFloat() && first->isFloat() && second->isFloat()) {
      llvm::APFloat tmp = v.getFloat();

      return ((first->getFloat().compareWithConversion(tmp) == llvm::APFloat::cmpLessThan ||
              first->getFloat().compareWithConversion(tmp) == llvm::APFloat::cmpEqual) && (
              second->getFloat().compareWithConversion(tmp) == llvm::APFloat::cmpGreaterThan ||
              second->getFloat().compareWithConversion(tmp) == llvm::APFloat::cmpEqual));
    }
    return false;
  }
  const APValue &From() const {
    return *first;
  }
  const APValue &To() const {
    return *second;
  }
  const APValue *getConcreteValue() const {
    return &From() == &To() ? &From() : NULL;
  }

  void Profile(llvm::FoldingSetNodeID &ID) const {
    if (From().isInt())
      ID.AddPointer(&From().getInt());
    else if (From().isFloat())
      ID.AddPointer(&From().getFloat());
    else
      ID.AddPointer(&From());
    if (To().isInt())
      ID.AddPointer(&To().getInt());
    else if (To().isFloat())
      ID.AddPointer(&To().getFloat());
    else
      ID.AddPointer(&To());
  }
};


class RangeTrait : public llvm::ImutContainerInfo<Range> {
public:
  // When comparing if one Range is less than another, we should compare
  // the actual APSInt values instead of their pointers.  This keeps the order
  // consistent (instead of comparing by pointer values) and can potentially
  // be used to speed up some of the operations in RangeSet.
  static inline bool isLess(key_type_ref lhs, key_type_ref rhs) {
    if (lhs.first->isInt() && rhs.first->isInt())
      return (lhs.first->getInt() < rhs.first->getInt() ||
          (!(rhs.first->getInt() < lhs.first->getInt()) &&
              lhs.second->getInt() < rhs.second->getInt()));
    else if (lhs.first->isFloat() && rhs.first->isFloat()) {
      return (lhs.first->getFloat().compareWithConversion(rhs.first->getFloat()) == llvm::APFloat::cmpLessThan ||
          (!(rhs.second->getFloat().compareWithConversion(lhs.first->getFloat()) == llvm::APFloat::cmpLessThan &&
              lhs.second->getFloat().compareWithConversion(rhs.second->getFloat()) == llvm::APFloat::cmpLessThan)));
    }
    else {
      llvm_unreachable("Bad type of APValue");
      return false;
    }
  }
};

/// RangeSet contains a set of ranges. If the set is empty, then
///  there the value of a symbol is overly constrained and there are no
///  possible values for that symbol.
class RangeSet {
  typedef llvm::ImmutableSet<Range, RangeTrait> PrimRangeSet;
  PrimRangeSet ranges; // no need to make const, since it is an
                       // ImmutableSet - this allows default operator=
                       // to work.
public:
  typedef PrimRangeSet::Factory Factory;
  typedef PrimRangeSet::iterator iterator;

  static Factory &GetFactory() { return F; }

  RangeSet(PrimRangeSet RS) : ranges(RS) {}

  static RangeSet getEmptyRange() { return RangeSet(F.getEmptySet()); }
  static RangeSet getFullRange(QualType QT, BasicValueFactory &BV) {
    return RangeSet(F, BV.getMinValue(QT), BV.getMaxValue(QT));
  }

  /// Create a new set with all ranges of this set and RS
  /// Possible intersections are not checked here
  RangeSet addRange(Factory &F, const RangeSet &RS) {
    PrimRangeSet Ranges(RS.ranges);
    for (iterator I = begin(), E = end(); I != E; I++)
      Ranges = F.add(Ranges, *I);
    return RangeSet(Ranges);
  }

  iterator begin() const { return ranges.begin(); }
  iterator end() const { return ranges.end(); }

  bool isEmpty() const { return ranges.isEmpty(); }

  /// Construct a new RangeSet representing '{ [from, to] }'.
  RangeSet(Factory &F, const APValue &from, const APValue &to)
    : ranges(F.add(F.getEmptySet(), Range(from, to))) {}
  /// Profile - Generates a hash profile of this RangeSet for use
  ///  by FoldingSet.
  void Profile(llvm::FoldingSetNodeID &ID) const { ranges.Profile(ID); }

  /// getConcreteValue - If a symbol is constrained to equal a specific integer
  ///  constant then this method returns that value.  Otherwise, it returns
  ///  NULL.
  const APValue* getConcreteValue() const {
    return ranges.isSingleton() ? ranges.begin()->getConcreteValue() : 0;
  }

  const APValue &getMinValue() const {
    assert(!isEmpty());
    return ranges.begin()->From();
  }

  const APValue &getMaxValue() const {
    assert(!isEmpty());
    PrimRangeSet::iterator i = ranges.begin(), e = ranges.end();
    PrimRangeSet::iterator res = i;
    while (i != e)
      res = i++;
    return res->To();
  }

  bool isRangeOfType(QualType QT, BasicValueFactory &BV) const {
    if (!QT->isIntegralOrEnumerationType())
      return false;
    if (!ranges.isSingleton())
      return false;
    const Range &R = *ranges.begin();
    if (!R.From().isInt() || !R.To().isInt())
      return false;
    const APSInt &From = R.From().getInt(), &To = R.To().getInt(),
        &Min = BV.getMinValue(QT).getInt(), &Max = BV.getMaxValue(QT).getInt();
    return Min.compare(From) == APSInt::cmpEqual &&
        Max.compare(To) == APSInt::cmpEqual;
  }

private:
  static Factory F;

  void IntersectInRange(BasicValueFactory &BV, Factory &F,
                        const APValue &Lower,
                        const APValue &Upper,
                        PrimRangeSet &newRanges,
                        PrimRangeSet::iterator &i,
                        PrimRangeSet::iterator &e) const {
    // There are six cases for each range R in the set:
    //   1. R is entirely before the intersection range.
    //   2. R is entirely after the intersection range.
    //   3. R contains the entire intersection range.
    //   4. R starts before the intersection range and ends in the middle.
    //   5. R starts in the middle of the intersection range and ends after it.
    //   6. R is entirely contained in the intersection range.
    // These correspond to each of the conditions below.
    for (/* i = begin(), e = end() */; i != e; ++i) {
      if (i->To().isInt() && i->To().getInt() < Lower.getInt()) {
        continue;
      }
      if (i->To().isFloat()) {
        if (i->To().getFloat().compareWithConversion(Lower.getFloat()) == llvm::APFloat::cmpLessThan)
          continue;
      }

      if (i->From().isInt() &&  i->From().getInt() > Upper.getInt()) {
        break;
      }

      if (i->From().isFloat()) {
        if (i->From().getFloat().compareWithConversion(Upper.getFloat()) == llvm::APFloat::cmpGreaterThan)
         break;
      }
      if (i->Includes(Lower)) {
        if (i->Includes(Upper)) {
          newRanges = F.add(newRanges, Range(BV.getValue(Lower), BV.getValue(Upper)));
          break;
        } else {
          newRanges = F.add(newRanges, Range(BV.getValue(Lower), i->To()));

        }
      } else {
        if (i->Includes(Upper)) {
          newRanges = F.add(newRanges, Range(i->From(), BV.getValue(Upper)));
          break;
        } else
          newRanges = F.add(newRanges, *i);
      }
    }
  }

  bool pin(llvm::APSInt &Lower, llvm::APSInt &Upper) const {
    // This function has nine cases, the cartesian product of range-testing
    // both the upper and lower bounds against the symbol's type.
    // Each case requires a different pinning operation.
    // The function returns false if the described range is entirely outside
    // the range of values for the associated symbol.
    const APValue val = getMinValue();
    if (!val.isInt())
      return true;
    APSIntType Type(val.getInt());
    APSIntType::RangeTestResultKind LowerTest = Type.testInRange(Lower, true);
    APSIntType::RangeTestResultKind UpperTest = Type.testInRange(Upper, true);

    switch (LowerTest) {
    case APSIntType::RTR_Below:
      switch (UpperTest) {
      case APSIntType::RTR_Below:
        // The entire range is outside the symbol's set of possible values.
        // If this is a conventionally-ordered range, the state is infeasible.
        if (Lower < Upper)
          return false;

        // However, if the range wraps around, it spans all possible values.
        Lower = Type.getMinValue();
        Upper = Type.getMaxValue();
        break;
      case APSIntType::RTR_Within:
        // The range starts below what's possible but ends within it. Pin.
        Lower = Type.getMinValue();
        Type.apply(Upper);
        break;
      case APSIntType::RTR_Above:
        // The range spans all possible values for the symbol. Pin.
        Lower = Type.getMinValue();
        Upper = Type.getMaxValue();
        break;
      }
      break;
    case APSIntType::RTR_Within:
      switch (UpperTest) {
      case APSIntType::RTR_Below:
        // The range wraps around, but all lower values are not possible.
        Type.apply(Lower);
        Upper = Type.getMaxValue();
        break;
      case APSIntType::RTR_Within:
        // The range may or may not wrap around, but both limits are valid.
        Type.apply(Lower);
        Type.apply(Upper);
        break;
      case APSIntType::RTR_Above:
        // The range starts within what's possible but ends above it. Pin.
        Type.apply(Lower);
        Upper = Type.getMaxValue();
        break;
      }
      break;
    case APSIntType::RTR_Above:
      switch (UpperTest) {
      case APSIntType::RTR_Below:
        // The range wraps but is outside the symbol's set of possible values.
        return false;
      case APSIntType::RTR_Within:
        // The range starts above what's possible but ends within it (wrap).
        Lower = Type.getMinValue();
        Type.apply(Upper);
        break;
      case APSIntType::RTR_Above:
        // The entire range is outside the symbol's set of possible values.
        // If this is a conventionally-ordered range, the state is infeasible.
        if (Lower < Upper)
          return false;

        // However, if the range wraps around, it spans all possible values.
        Lower = Type.getMinValue();
        Upper = Type.getMaxValue();
        break;
      }
      break;
    }

    return true;
  }

  PrimRangeSet addRangeDiffTypes(BasicValueFactory &BV, Factory &F,
                                 PrimRangeSet &Ranges, const llvm::APSInt &Lhs,
                                 const llvm::APSInt &Rhs) const {
    llvm::APSInt InnerLhs = Lhs, InnerRhs = Rhs;

    if (InnerLhs.getBitWidth() > InnerRhs.getBitWidth())
      InnerRhs = InnerRhs.extend(InnerLhs.getBitWidth());
    else if (InnerLhs.getBitWidth() < InnerRhs.getBitWidth())
      InnerLhs = InnerLhs.extend(InnerRhs.getBitWidth());

    if (InnerLhs.isSigned() != InnerRhs.isSigned()) {
      if (InnerLhs.isSigned() && InnerLhs.isNonNegative())
        InnerLhs = APSIntType(InnerRhs).convert(InnerLhs);
      else if (InnerRhs.isSigned() && InnerRhs.isNonNegative())
        InnerRhs = APSIntType(InnerLhs).convert(InnerRhs);
      else if (InnerLhs.isSigned()) {
        if (APSIntType(InnerLhs).getMaxValue().compare(InnerRhs) ==
            llvm::APSInt::cmpGreaterThan) {
          APSIntType NewType(InnerLhs.getBitWidth()*2, false);
          InnerLhs = NewType.convert(InnerLhs);
          InnerRhs = NewType.convert(InnerRhs);
        }
        else
          InnerRhs = APSIntType(InnerLhs).convert(InnerRhs);
      }
      else {
        if (APSIntType(InnerRhs).getMaxValue().compare(InnerLhs) ==
            llvm::APSInt::cmpGreaterThan) {
          APSIntType NewType(InnerRhs.getBitWidth()*2, false);
          InnerRhs = NewType.convert(InnerRhs);
          InnerLhs = NewType.convert(InnerLhs);
        }
        else
          InnerRhs = APSIntType(InnerLhs).convert(InnerRhs);
      }
    }

    Ranges = F.add(Ranges, Range(BV.getValue(InnerLhs), BV.getValue(InnerRhs)));
    return Ranges;
  }

public:
  // Returns a set containing the values in the receiving set, intersected with
  // the closed range [Lower, Upper]. Unlike the Range type, this range uses
  // modular arithmetic, corresponding to the common treatment of C integer
  // overflow. Thus, if the Lower bound is greater than the Upper bound, the
  // range is taken to wrap around. This is equivalent to taking the
  // intersection with the two ranges [Min, Upper] and [Lower, Max],
  // or, alternatively, /removing/ all integers between Upper and Lower.
  RangeSet Intersect(BasicValueFactory &BV, Factory &F,
                     APValue Lower, APValue Upper) const {
    if (Lower.isInt() && Upper.isInt() && !pin(Lower.getInt(), Upper.getInt()))
      return F.getEmptySet();

    PrimRangeSet newRanges = F.getEmptySet();

    PrimRangeSet::iterator i = begin(), e = end();

    if ((Lower.isInt() && Upper.isInt() && Lower.getInt() <= Upper.getInt()) ||
        (Lower.isFloat() && Upper.isFloat() &&
        (Lower.getFloat().compareWithConversion(Upper.getFloat()) == llvm::APFloat::cmpLessThan ||
        Lower.getFloat().compareWithConversion(Upper.getFloat()) == llvm::APFloat::cmpEqual)))
      IntersectInRange(BV, F, Lower, Upper, newRanges, i, e);
    else {
      // The order of the next two statements is important!
      // IntersectInRange() does not reset the iteration state for i and e.
      // Therefore, the lower range most be handled first.
      IntersectInRange(BV, F, BV.getMinValue(Upper), Upper, newRanges, i, e);
      IntersectInRange(BV, F, Lower, BV.getMaxValue(Lower), newRanges, i, e);
    }

    return newRanges;
  }

  // Returns an intersection of this interval with a given one.
  // Assuming ranges are sorted
  RangeSet Intersect(BasicValueFactory &BV, Factory &F,
                     const RangeSet &RHS) const {
    PrimRangeSet newRanges = F.getEmptySet();
    RangeSet::iterator I1 = begin(), I2 = RHS.begin(), E1 = end(),
        E2 = RHS.end();
    while (I1 != E1 && I2 != E2) {
      // Trivial cases without intersection, just shift to the next range
      if (I1->To().compare(I2->From()) == APFloat::cmpLessThan) {
        I1++;
      } else if (I2->To().compare(I1->From()) == APFloat::cmpLessThan) {
        I2++;
      } else { // Intersection found
        const APValue &From = APValue::max(I1->From(), I2->From());
        const APValue &To = APValue::min(I1->To(), I2->To());
        newRanges = F.add(newRanges, Range(BV.getValue(From), BV.getValue(To)));
        // if first.to < second.to => shift first;
        // else if first.to > second.to => shift second;
        // else shift both;
        APFloat::cmpResult cmpResult = I1->To().compare(I2->To());
        if (cmpResult & (APFloat::cmpLessThan | APFloat::cmpEqual))
          I1++;
        if (cmpResult & (APFloat::cmpGreaterThan | APFloat::cmpEqual))
          I2++;
      }
    }
    return newRanges;
  }


  void print(raw_ostream &os) const {
    bool isFirst = true;
    os << "{ ";
    for (iterator i = begin(), e = end(); i != e; ++i) {
      if (isFirst)
        isFirst = false;
      else
        os << ", ";
      //FIXME: add correct print
      if (i->From().isFloat() &&i->To().isFloat()) {
        llvm::APFloat val = i->From().getFloat();
        bool losesInfo;
        os << '[';
        val.convert(llvm::APFloat::IEEEdouble, llvm::APFloat::rmNearestTiesToEven,&losesInfo);
        os << val.convertToDouble();
        os << ", ";
        val = i->To().getFloat();
        val.convert(llvm::APFloat::IEEEdouble, llvm::APFloat::rmNearestTiesToEven,&losesInfo);
        os << val.convertToDouble();
        os << ']';
      }
      if (i->From().isInt() && i->To().isInt())
        os << '[' << i->From().getInt().toString(10) << ", " << i->To().getInt().toString(10)
         << ']';
    }
    os << " }";
  }

  void dump() const { print(llvm::errs()); }

  bool operator==(const RangeSet &other) const {
    return ranges == other.ranges;
  }

  void addRange(Factory &F, Range R) {
    this->ranges = F.add(this->ranges, R);
  }


  static bool compareRanges(const Range &R1, const Range &R2) {
    llvm::APSInt::cmpResult R = R1.From().compareInteger(R2.From());
    if (R == llvm::APSInt::cmpLessThan)
      return true;
    if (R ==llvm::APSInt::cmpEqual) {
      if (R1.To().compareInteger(R2.To()) == llvm::APSInt::cmpLessThan)
        return true;
    }
    return false;
  }

  static RangeSet castRange(BasicValueFactory &BVF, Factory &F, const Range &R,
                            QualType CastTy);

  RangeSet merge(Factory &F, const Range &NewRange) {
    return merge(F, RangeSet(F, NewRange.From(), NewRange.To()));
  }

  static RangeSet vectorToSet(Factory &F, std::vector<Range> &ranges) {
    if (ranges.empty())
      return RangeSet(F.getEmptySet());
    std::sort(ranges.begin(), ranges.end(), compareRanges);

    PrimRangeSet Res = F.getEmptySet();
    Range R = ranges[0];
    for (size_t i = 1; i < ranges.size(); i++) {
      const Range &R2 = ranges[i];
      llvm::APSInt To = R.To().getInt();
      if (To != To.getMaxValue(To.getBitWidth(), To.isUnsigned()))
        To++;
      assert(R.From().getInt() < To);
      if (R2.From().compareInteger(To) != llvm::APSInt::cmpGreaterThan) {
        if (R2.To().compareInteger(R.To()) != llvm::APSInt::cmpLessThan)
          R = Range(R.From(), R2.To());
        // else: R2 is inside R, skip it
      } else {
        Res = F.add(Res, R);
        R = R2;
      }
    }
    Res = F.add(Res, R);
    return Res;
  }

  RangeSet cast(BasicValueFactory &BVF, Factory &F, QualType T) const {
    std::vector<Range> allRanges;
    for (PrimRangeSet::iterator i = begin(), e = end(); i != e; i++) {
      RangeSet RS = castRange(BVF, F, *i, T);
      for (PrimRangeSet::iterator i1 = RS.begin(), e1 = RS.end(); i1 != e1; i1++)
        allRanges.push_back(*i1);
    }
    return vectorToSet(F, allRanges);
  }

  static const llvm::APSInt calcDiff(const llvm::APSInt &Lhs,
                                     const llvm::APSInt &Rhs);

  RangeSet merge(Factory &F, const RangeSet &NewRange) const {
    std::vector<Range> allRanges;
    PrimRangeSet::iterator i1 = begin(), i2 = NewRange.begin(),
        e1 = end(), e2 = NewRange.end();
    for (; i1 != e1; i1++)
      allRanges.push_back(*i1);
    for (; i2 != e2; i2++)
      allRanges.push_back(*i2);
    return vectorToSet(F, allRanges);
  }
};
} // end anonymous namespace


REGISTER_TRAIT_WITH_PROGRAMSTATE(ConstraintRange,
                                 CLANG_ENTO_PROGRAMSTATE_MAP(SymbolRef,
                                                             RangeSet))

typedef llvm::ImmutableMap<SVal, RangeSet> DeclConstraintRangeTy;

REGISTER_TRAIT_WITH_PROGRAMSTATE(InputConstraintRange, DeclConstraintRangeTy)

RangeSet::Factory RangeSet::F;

typedef std::map<SVal, RangeSet> RangeMap;

namespace {
class RangeConstraintManager : public SimpleConstraintManager{
  RangeSet GetRange(ProgramStateRef state, SymbolRef sym);

  ProgramStateRef castConstraints(ProgramStateRef State, SymbolRef OldSym,
                                  SymbolRef NewSym);
  ProgramStateRef
  castConstraintsRecursively(ProgramStateRef State,
                             SymbolManager::CastSetItPair It,
                             SymbolRef Sym, SymbolRef OldSym);

  RangeSet castRangeSet(const Range &R, QualType CastTy);

  ProgramStateRef constrainSVal(ProgramStateRef St, const RangeSet &Ranges,
                                SymbolRef Sym);
public:
  RangeConstraintManager(SubEngine *subengine, SValBuilder &SVB)
    : SimpleConstraintManager(subengine, SVB),
      F(RangeSet::GetFactory()) {}

  ProgramStateRef assumeSymNE(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymEQ(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymLT(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymGT(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymGE(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymLE(ProgramStateRef state, SymbolRef sym,
                             const llvm::APSInt& Int,
                             const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymNE(ProgramStateRef state, SymbolRef sym,
                               const llvm::APFloat& Float,
                               const llvm::APFloat& Adjustment);

  ProgramStateRef assumeSymEQ(ProgramStateRef state, SymbolRef sym,
                             const llvm::APFloat& Float,
                             const llvm::APFloat& Adjustment);

  ProgramStateRef assumeSymLT(ProgramStateRef state, SymbolRef sym,
                             const llvm::APFloat& Float,
                             const llvm::APFloat& Adjustment);

  ProgramStateRef assumeSymGT(ProgramStateRef state, SymbolRef sym,
                             const llvm::APFloat& Float,
                             const llvm::APFloat& Adjustment);

  ProgramStateRef assumeSymGE(ProgramStateRef state, SymbolRef sym,
                             const llvm::APFloat& Float,
                             const llvm::APFloat& Adjustment);

  ProgramStateRef assumeSymLE(ProgramStateRef state, SymbolRef sym,
                             const llvm::APFloat& Float,
                             const llvm::APFloat& Adjustment);

  const APValue* getSymVal(ProgramStateRef St, SymbolRef sym) const;

  ProgramStateRef assumeSymInBound(ProgramStateRef state, SymbolRef sym,
                                   const llvm::APSInt& From,
                                   const llvm::APSInt& To,
                                   const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymOutOfBound(ProgramStateRef state, SymbolRef sym,
                                      const llvm::APSInt& From,
                                      const llvm::APSInt& To,
                                      const llvm::APSInt& Adjustment);

  ProgramStateRef assumeSymSymNE(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);
  ProgramStateRef assumeSymSymEQ(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);
  ProgramStateRef assumeSymSymLT(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);
  ProgramStateRef assumeSymSymGT(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);
  ProgramStateRef assumeSymSymGE(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);
  ProgramStateRef assumeSymSymLE(ProgramStateRef state, SymbolRef lhs,
                                 SymbolRef rhs, const APValue &Adjustment);

  ConditionTruthVal checkNull(ProgramStateRef State, SymbolRef Sym);

  ProgramStateRef removeDeadBindings(ProgramStateRef St,
                                     SymbolReaper& SymReaper);

  ProgramStateRef
  applyCallBranchSummary(const FunctionCallBranchSummary &Summary,
                         Summarizer &S);

  ProgramStateRef reapSymbol(ProgramStateRef state, SymbolRef sym,
                             const RangeSet &Range) const;

  bool canReasonAboutSymbol(ProgramStateRef state, const SymSymExpr *E) const {
    return state->get<ConstraintRange>(E->getLHS()) ||
        state->get<ConstraintRange>(E->getRHS());
  }

  void print(ProgramStateRef St, raw_ostream &Out,
             const char* nl, const char *sep);
private:
  ProgramStateRef reapRegion(ProgramStateRef state, const MemRegion *MR,
                             const RangeSet &RS) const;
  ProgramStateRef reapRegion(ProgramStateRef state, const MemRegion *MR) const;

  RangeSet::Factory &F;
};

} // end anonymous namespace

ConstraintManager *
ento::CreateRangeConstraintManager(ProgramStateManager &StMgr, SubEngine *Eng) {
  return new RangeConstraintManager(Eng, StMgr.getSValBuilder());
}

const APValue* RangeConstraintManager::getSymVal(ProgramStateRef St,
                                                 SymbolRef sym) const {
  const ConstraintRangeTy::data_type *T = St->get<ConstraintRange>(sym);
  return T ? T->getConcreteValue() : NULL;
}

ConditionTruthVal RangeConstraintManager::checkNull(ProgramStateRef State,
                                                    SymbolRef Sym) {
  const RangeSet *Ranges = State->get<ConstraintRange>(Sym);

  // If we don't have any information about this symbol, it's underconstrained.
  if (!Ranges)
    return ConditionTruthVal();

  // If we have a concrete value, see if it's zero.
  if (const APValue *Value = Ranges->getConcreteValue()) {
    if (Value->isFloat())
      return Value->getFloat().isZero();
    if (Value->isInt())
      return Value->getInt() == 0;
  }

  if(Sym->getType()->isRealFloatingType()) {
    BasicValueFactory &BV = getBasicVals();
    llvm::APFloat Zero(0.0);
    APValue ValueZero(Zero);
    // Check if zero is in the set of possible values.
    if (Ranges->Intersect(BV, F, ValueZero, ValueZero).isEmpty())
      return false;
    return ConditionTruthVal();
  }

  BasicValueFactory &BV = getBasicVals();
  APSIntType IntType = BV.getAPSIntType(Sym->getType());
  llvm::APSInt Zero = IntType.getZeroValue();
  APValue ValueZero(Zero);
  // Check if zero is in the set of possible values.
  if (Ranges->Intersect(BV, F, ValueZero, ValueZero).isEmpty())
    return false;
  // Zero is a possible value, but it is not the /only/ possible value.
  return ConditionTruthVal();
}

/// Scan all symbols referenced by the constraints. If the symbol is not alive
/// as marked in LSymbols, mark it as dead in DSymbols.
ProgramStateRef 
RangeConstraintManager::removeDeadBindings(ProgramStateRef state,
                                           SymbolReaper& SymReaper) {

  ConstraintRangeTy CR = state->get<ConstraintRange>();
  ConstraintRangeTy::Factory& CRFactory = state->get_context<ConstraintRange>();

  for (ConstraintRangeTy::iterator I = CR.begin(), E = CR.end(); I != E; ++I) {
    SymbolRef sym = I.getKey();
    if (SymReaper.maybeDead(sym)) {
      if (static_cast<ExprEngine *>(state->getStateManager().getOwningEngine())
          ->getAnalysisManager().getAnalyzerOptions()
          .getIPAMode() == IPAK_Summary)
        state = reapSymbol(state, sym, I.getData());
      CR = CRFactory.remove(CR, sym);
    }
  }
  return state->set<ConstraintRange>(CR);
}

RangeSet
RangeConstraintManager::GetRange(ProgramStateRef state, SymbolRef sym) {
  BasicValueFactory &BV = getBasicVals();
  if (ConstraintRangeTy::data_type* V = state->get<ConstraintRange>(sym))
    return *V;
  else if (const SymbolCast *SC = dyn_cast<SymbolCast>(sym)) {
    if (SC->getOperand()->getType()->isIntegralOrEnumerationType() &&
        SC->getType()->isIntegralOrEnumerationType())
      return GetRange(state, SC->getOperand()).cast(BV, F, SC->getType());
  }

  // Lazily generate a new RangeSet representing all possible values for the
  // given symbol type.
  QualType T = sym->getType();

  RangeSet Result(F, BV.getMinValue(T), BV.getMaxValue(T));

  // Special case: references are known to be non-zero.
  if (T->isReferenceType()) {
    APSIntType IntType = BV.getAPSIntType(T);
    APValue val1(++IntType.getZeroValue());
    APValue val2(--IntType.getZeroValue());
    Result = Result.Intersect(BV, F, val1, val2);
  }
  return Result;
}

const llvm::APSInt RangeSet::calcDiff(const llvm::APSInt &Lhs,
                                      const llvm::APSInt &Rhs) {
  APSIntType NewType(std::max(Lhs.getBitWidth(), Rhs.getBitWidth()), true);
  if (Lhs.isSigned() && Lhs.isNegative() && (Rhs.isUnsigned() ||
                                             Rhs.isNonNegative()))
    return NewType.getValue(*(Lhs.abs().getRawData())) + NewType.convert(Rhs);
  else if (Rhs.isSigned() && Rhs.isNegative() && (Lhs.isUnsigned() ||
                                                  Lhs.isNonNegative()))
    return NewType.getValue(*(Rhs.abs().getRawData())) + NewType.convert(Lhs);
  else
    return Lhs - Rhs;
}

ProgramStateRef
RangeConstraintManager::castConstraints(ProgramStateRef State, SymbolRef OldSym,
                                        SymbolRef NewSym) {
  QualType OriginalTy = OldSym->getType(), CastTy = NewSym->getType();

  if (OriginalTy.getCanonicalType() == CastTy.getCanonicalType())
    return State->set<ConstraintRange>(NewSym, GetRange(State, OldSym));
  ASTContext &ASTCtx = State->getStateManager().getContext();
  const Type *OriginalTyC = ASTCtx.getCanonicalType(OriginalTy).getTypePtr();
  const Type *CastTyC = ASTCtx.getCanonicalType(CastTy).getTypePtr();

  if (const EnumType *ET = dyn_cast<EnumType>(OriginalTyC))
    OriginalTy = ET->getDecl()->getIntegerType();
  if (const EnumType *ET = dyn_cast<EnumType>(CastTyC))
    CastTy = ET->getDecl()->getIntegerType();

  if (!OriginalTy.getCanonicalType()->isBuiltinType() ||
      !CastTy.getCanonicalType()->isBuiltinType() ||
      !OriginalTy.getCanonicalType()->isIntegerType() ||
      !CastTy.getCanonicalType()->isIntegerType())
    return State;

  const RangeSet *OldRanges = State->get<ConstraintRange>(OldSym);
  if (OldRanges && !OldRanges->begin()->From().isInt())
    return State;
  RangeSet OldTypeRanges = GetRange(State, OldSym);
  if (!OldRanges) {
    if (ASTCtx.getTypeSize(OriginalTy) >= ASTCtx.getTypeSize(CastTy))
      return State;
    OldRanges = &OldTypeRanges;
  }
  RangeSet ResultRange = OldRanges->cast(getBasicVals(), F, CastTy);
  State = ResultRange.isEmpty()
      ? NULL : State->set<ConstraintRange>(NewSym, ResultRange);

  return State;
}

ProgramStateRef RangeConstraintManager::castConstraintsRecursively(
    ProgramStateRef State, SymbolManager::CastSetItPair It, SymbolRef Sym,
    SymbolRef OldSym) {
  for (SymbolManager::CastSetIt I = It.first, E = It.second; I != E; ++I) {
    std::pair<SymbolRef, SymbolRef> SymPair = *I;
    if ((SymPair.second != OldSym) && (SymPair.first == Sym)) {
      State = castConstraints(State, Sym, SymPair.second);
      if (!State)
        return NULL;

      State = castConstraintsRecursively(State, It, SymPair.second,
                                            SymPair.first);
      if (!State)
        return NULL;
    }
    else if ((SymPair.first != OldSym) && (SymPair.second == Sym)) {
      State = castConstraints(State, Sym, SymPair.first);
      if (!State)
        return NULL;

      State = castConstraintsRecursively(State, It, SymPair.first,
                                           SymPair.second);
      if (!State)
        return NULL;
    }
  }
  return State;
}

RangeSet RangeSet::castRange(BasicValueFactory &BVF, Factory &F, const Range &R,
                             QualType CastTy) {
  assert(R.From().isInt() && R.To().isInt() &&
         "This function is for int type only");
  llvm::APSInt From = R.From().getInt(), To = R.To().getInt();
  RangeSet NewRanges(F.getEmptySet());
  llvm::APSInt n = calcDiff(To, From);
  ento::APSIntType NewAPSIntType = BVF.getAPSIntType(CastTy);
  llvm::APSInt NewTypeMaxValueUnSign =
      llvm::APSInt::getMaxValue(NewAPSIntType.getBitWidth(), true);
  if (n.compare(NewTypeMaxValueUnSign) != llvm::APSInt::cmpLessThan) {
    NewRanges.addRange(F, Range(BVF.getValue(NewAPSIntType.getMinValue()),
                                BVF.getValue(NewAPSIntType.getMaxValue())));
    return NewRanges;
  }
  llvm::APSInt NewTypeMaxValue = NewAPSIntType.getMaxValue();
  llvm::APSInt From1 = NewAPSIntType.convert(From);
  llvm::APSInt delta = calcDiff(NewTypeMaxValue, From1);
  if (n.compare(delta) != llvm::APSInt::cmpGreaterThan) {
    llvm::APSInt To = From1 + NewAPSIntType.convert(n);
    NewRanges.addRange(F, Range(BVF.getValue(From1), BVF.getValue(To)));
    return NewRanges;
  }

  llvm::APSInt To1 = NewTypeMaxValue;
  llvm::APSInt From2 = NewAPSIntType.getMinValue();
  llvm::APSInt m = NewAPSIntType.convert(To) -
                   NewAPSIntType.convert(From) -
                   NewAPSIntType.convert(delta) - NewAPSIntType.getValue(1);
  llvm::APSInt To2 = From2 + m;
  NewRanges.addRange(F, Range(BVF.getValue(From1), BVF.getValue(To1)));
  NewRanges.addRange(F, Range(BVF.getValue(From2), BVF.getValue(To2)));
  return NewRanges;
}

ProgramStateRef RangeConstraintManager::constrainSVal(ProgramStateRef St,
                                                      const RangeSet &Ranges,
                                                      SymbolRef Sym) {
  St = St->set<ConstraintRange>(Sym, Ranges);
  ProgramStateRef St2 = castConstraintsRecursively(St, St->getSymbolManager().getCastSetIt(),
                                  Sym, Sym);
  return St2 ? St2 : St;
}

//===------------------------------------------------------------------------===
// assumeSymX methods: public interface for RangeConstraintManager.
//===------------------------------------------------------------------------===/

// The syntax for ranges below is mathematical, using [x, y] for closed ranges
// and (x, y) for open ranges. These ranges are modular, corresponding with
// a common treatment of C integer overflow. This means that these methods
// do not have to worry about overflow; RangeSet::Intersect can handle such a
// "wraparound" range.
// As an example, the range [UINT_MAX-1, 3) contains five values: UINT_MAX-1,
// UINT_MAX, 0, 1, and 2.

ProgramStateRef 
RangeConstraintManager::assumeSymNE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  if (AdjustmentType.testInRange(Int, true) != APSIntType::RTR_Within)
    return St;

  llvm::APSInt Lower = AdjustmentType.convert(Int) - Adjustment;
  llvm::APSInt Upper = Lower;
  --Lower;
  ++Upper;
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  // [Int-Adjustment+1, Int-Adjustment-1]
  // Notice that the lower bound is greater than the upper bound.
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, UpperValue, LowerValue);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}

ProgramStateRef 
RangeConstraintManager::assumeSymNE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {
  // Before we do any real work, see if the value can even show up.
//  if (AdjustmentType.testInRange(Int, true) != APSIntType::RTR_Within)
//    return St;

  llvm::APFloat Lower = Float;
  Lower.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);
  llvm::APFloat Upper = Lower;


  if (Lower.isZero())
    Lower = Lower.getSmallestNormalized(Lower.getSemantics(), true);
  else
    Lower.next(true);

  if (Upper.isZero())
    Upper = Upper.getSmallestNormalized(Upper.getSemantics(), false);
  else
    Upper.next(false);

  APValue LowerValue(Lower);
  APValue UpperValue(Upper);

  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, UpperValue, LowerValue);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}

ProgramStateRef
RangeConstraintManager::assumeSymEQ(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  if (AdjustmentType.testInRange(Int, true) != APSIntType::RTR_Within)
    return NULL;

  // [Int-Adjustment, Int-Adjustment]
  llvm::APSInt AdjInt = AdjustmentType.convert(Int) - Adjustment;
  APValue ValueAdjInt(AdjInt);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, ValueAdjInt, ValueAdjInt);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}


ProgramStateRef
RangeConstraintManager::assumeSymEQ(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {
  // Before we do any real work, see if the value can even show up.

  // [Int-Adjustment, Int-Adjustment]
  llvm::APFloat Val = Float;
  Val.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);
  APValue ValueAdjFloat(Val);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, ValueAdjFloat, ValueAdjFloat);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}

ProgramStateRef 
RangeConstraintManager::assumeSymLT(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  switch (AdjustmentType.testInRange(Int, true)) {
  case APSIntType::RTR_Below:
    return NULL;
  case APSIntType::RTR_Within:
    break;
  case APSIntType::RTR_Above:
    return St;
  }

  // Special case for Int == Min. This is always false.
  llvm::APSInt ComparisonVal = AdjustmentType.convert(Int);
  llvm::APSInt Min = AdjustmentType.getMinValue();
  if (ComparisonVal == Min)
    return NULL;

  llvm::APSInt Lower = Min-Adjustment;
  llvm::APSInt Upper = ComparisonVal-Adjustment;
  --Upper;
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}

ProgramStateRef 
RangeConstraintManager::assumeSymLT(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {

  llvm::APFloat Min = Float.getLargest(Float.getSemantics(), true);
  if (Float.isLargest() && Float.isNegative())
    return NULL;
  llvm::APFloat Lower = Min;
  Lower.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);
  llvm::APFloat Upper = Float;
  Upper.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);
  if (Upper.isZero())
    Upper = Upper.getSmallestNormalized(Upper.getSemantics(), true);
   else
     Upper.next(true);
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}

ProgramStateRef
RangeConstraintManager::assumeSymGT(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  switch (AdjustmentType.testInRange(Int, true)) {
  case APSIntType::RTR_Below:
    return St;
  case APSIntType::RTR_Within:
    break;
  case APSIntType::RTR_Above:
    return NULL;
  }

  // Special case for Int == Max. This is always false.
  llvm::APSInt ComparisonVal = AdjustmentType.convert(Int);
  llvm::APSInt Max = AdjustmentType.getMaxValue();
  if (ComparisonVal == Max)
    return NULL;

  llvm::APSInt Lower = ComparisonVal-Adjustment;
  llvm::APSInt Upper = Max-Adjustment;
  ++Lower;
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
//  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}

ProgramStateRef
RangeConstraintManager::assumeSymGT(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  llvm::APFloat Max = Float.getLargest(Float.getSemantics(), false);
  if (Float.isLargest())
    return NULL;
  llvm::APFloat Lower = Float;

  Lower.subtract(Adjustment, llvm::APFloat::rmNearestTiesToAway);
  llvm::APFloat Upper = Max;
  Upper.subtract(Adjustment, llvm::APFloat::rmNearestTiesToAway);

  if (Lower.isZero())
    Lower = Lower.getSmallestNormalized(Lower.getSemantics(), false);
  else
    Lower.next(false);

  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}


ProgramStateRef 
RangeConstraintManager::assumeSymGE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  switch (AdjustmentType.testInRange(Int, true)) {
  case APSIntType::RTR_Below:
    return St;
  case APSIntType::RTR_Within:
    break;
  case APSIntType::RTR_Above:
    return NULL;
  }

  // Special case for Int == Min. This is always feasible.
  llvm::APSInt ComparisonVal = AdjustmentType.convert(Int);
  llvm::APSInt Min = AdjustmentType.getMinValue();
  if (ComparisonVal == Min)
    return St;

  llvm::APSInt Max = AdjustmentType.getMaxValue();
  llvm::APSInt Lower = ComparisonVal-Adjustment;
  llvm::APSInt Upper = Max-Adjustment;
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}

ProgramStateRef 
RangeConstraintManager::assumeSymGE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {

  llvm::APFloat Min = Float.getLargest(Float.getSemantics(), true);
  if (Float.isLargest() && Float.isNegative())
    return St;
  llvm::APFloat Max = Float.getLargest(Float.getSemantics(), false);

  llvm::APFloat Lower = Float;
  Lower.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);

  llvm::APFloat Upper = Max;
  Upper.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);


  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}

ProgramStateRef
RangeConstraintManager::assumeSymLE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APSInt &Int,
                                    const llvm::APSInt &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  APSIntType AdjustmentType(Adjustment);
  switch (AdjustmentType.testInRange(Int, true)) {
  case APSIntType::RTR_Below:
    return NULL;
  case APSIntType::RTR_Within:
    break;
  case APSIntType::RTR_Above:
    return St;
  }

  // Special case for Int == Max. This is always feasible.
  llvm::APSInt ComparisonVal = AdjustmentType.convert(Int);
  llvm::APSInt Max = AdjustmentType.getMaxValue();
  if (ComparisonVal == Max)
    return St;

  llvm::APSInt Min = AdjustmentType.getMinValue();
  llvm::APSInt Lower = Min-Adjustment;
  llvm::APSInt Upper = ComparisonVal-Adjustment;
  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : constrainSVal(St, New, Sym);
}

ProgramStateRef
RangeConstraintManager::assumeSymLE(ProgramStateRef St, SymbolRef Sym,
                                    const llvm::APFloat &Float,
                                    const llvm::APFloat &Adjustment) {
  // Before we do any real work, see if the value can even show up.
  llvm::APFloat Min = Float.getLargest(Float.getSemantics(), true);
  llvm::APFloat Max = Float.getLargest(Float.getSemantics(), false);

  if (Float.isLargest())
    return St;
  llvm::APFloat Lower = Min;
  Lower.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);
  llvm::APFloat Upper = Float;
  Upper.subtract(Adjustment, llvm::APFloat::rmNearestTiesToEven);

  APValue LowerValue(Lower);
  APValue UpperValue(Upper);
  RangeSet New = GetRange(St, Sym).Intersect(getBasicVals(), F, LowerValue, UpperValue);
  return New.isEmpty() ? NULL : St->set<ConstraintRange>(Sym, New);
}

static const RangeSet *getMinPointerRange(int min, BasicValueFactory &BVF) {
  return new RangeSet(RangeSet::GetFactory(), BVF.getIntWithPtrWidth(min, true),
                            BVF.getMaxValue(BVF.getContext().getUIntPtrType()));
}

static const RangeSet *getPointerRange(const MemRegion *MR,
                                       BasicValueFactory &BVF) {
  if (MR->getSymbolicBase()) {
    RegionOffset RO = MR->getAsOffset();
    if (RO.hasSymbolicOffset()) {
      return getMinPointerRange(0, BVF);
    } else if (RO.getOffset() > 0) {
      return getMinPointerRange(1, BVF);
    } else {
      return getMinPointerRange(0, BVF);
    }
  } else {
    return getMinPointerRange(1, BVF);
  }
}

static const RangeSet *getSValRange(SVal val, BasicValueFactory &BVF,
                                    const ConstraintRangeTy &Ranges,
                                    bool &IsNew) {
  IsNew = true;
  if (Optional<nonloc::LocAsInteger> LAI = val.getAs<nonloc::LocAsInteger>()) {
    return new RangeSet(RangeSet::GetFactory(),
                        BVF.getMinValue(BVF.getContext().getIntTypeForBitwidth(
                            LAI->getNumBits(), 0)),
                        BVF.getMaxValue(BVF.getContext().getIntTypeForBitwidth(
                            LAI->getNumBits(), 0)));
  }
  if (SymbolRef sym = val.getAsSymbol()) {
    if (const SymbolRegionAddress *sra = dyn_cast<SymbolRegionAddress>(sym))
      return getPointerRange(sra->getRegion(), BVF);
    if (isa<SymbolLabelAddress>(sym))
      return getMinPointerRange(1, BVF);
    IsNew = false;
    return Ranges.lookup(sym);
  }
  if (Optional<nonloc::ConcreteInt> NLCI = val.getAs<nonloc::ConcreteInt>()) {
    const APValue &CI = BVF.getValue(NLCI->getValue());
    // HACK: convert "1-bit bools" often created by EvaluateAsInt()
    // into regular 8-bit bools.
    if (CI.getInt().getBitWidth() == 1) {
      const APValue &Val = BVF.getTruthValue(CI.getInt().getLimitedValue(1));
      return new RangeSet(RangeSet::GetFactory(), Val, Val);
    }
    return new RangeSet(RangeSet::GetFactory(), CI, CI);
  }
  if (Optional<loc::ConcreteInt> LCI = val.getAs<loc::ConcreteInt>()) {
    const APValue &CI = BVF.getValue(LCI->getValue());
    return new RangeSet(RangeSet::GetFactory(), CI, CI);
  }
  if (const MemRegion *MR = val.getAsRegion()) {
    return getPointerRange(MR, BVF);
  }
  return NULL;
}

static bool influencesSummary(SymbolRef Sym) {
  if (const SymbolExtent *SE =
          dyn_cast<SymbolExtent>(Sym))
    if (isa<AllocaRegion>(SE->getRegion()))
      return false;
  return true;
}

static bool isReallyConstrainted(SymbolRef Sym, const RangeSet &Range,
                                 BasicValueFactory &BV) {
  while (Sym) {
    QualType T = Sym->getType();
    if (Range.isRangeOfType(T, BV))
      return false;
    if (const SymbolCast *SC = dyn_cast<SymbolCast>(Sym))
      Sym = SC->getOperand();
    else
      break;
  }
  return true;
}

ProgramStateRef
RangeConstraintManager::reapSymbol(ProgramStateRef state, SymbolRef sym,
                                   const RangeSet &Range) const {
  SVal val = nonloc::SymbolVal(sym);
  if (influencesSummary(sym) &&
      isReallyConstrainted(sym, Range, state->getBasicVals()))
      state = state->set<InputConstraintRange>(val, Range);
  return state;
}

static ConstraintRangeTy handleSummaryRange(Summarizer &S,
                                            ConstraintRangeTy::Factory &CRF,
                                            ConstraintRangeTy Ranges,
                                            SVal Val,
                                            const RangeSet &FormalRange,
                                            bool &isNul) {
  SVal KeyVal = S.actualizeSVal(Val);
  ProgramStateRef State = S.getState();
  RangeSet NewRange = FormalRange;
  RangeSet::Factory &F = RangeSet::GetFactory();
  BasicValueFactory &BVF = State->getBasicVals();
  bool IsNew = false;
  if (const RangeSet *ActualRangePtr = getSValRange(KeyVal, BVF, Ranges,
                                                    IsNew)) {
    NewRange = ActualRangePtr->Intersect(BVF, F, FormalRange);
    if (IsNew)
      delete ActualRangePtr;
  }
  if (NewRange.isEmpty()) {
    isNul = true;
    return Ranges;
  }

  isNul = false;
  if (SymbolRef Sym = KeyVal.getAsSymbol()) {
    if (Optional<nonloc::LocAsInteger> LAI =
            KeyVal.getAs<nonloc::LocAsInteger>()) {
      // We cannot represent ranges on LocAsInteger, and ranges on the
      // underlying symbol may be of wrong type for the symbol.
      QualType FromTy = Sym->getType();
      QualType ToTy =
          State->getStateManager().getContext().getIntTypeForBitwidth(
              LAI->getNumBits(), LAI->isSigned());
      Sym = State->getSymbolManager().getCastSymbol(Sym, FromTy, ToTy);
    }
    if (!NewRange.isRangeOfType(Sym->getType(), S.getState()->getBasicVals()))
      return CRF.add(Ranges, Sym, NewRange);
  }

  return Ranges;
}

ProgramStateRef RangeConstraintManager::applyCallBranchSummary(
    const FunctionCallBranchSummary &Summary, Summarizer &S) {
  ProgramStateRef DstState = S.getState();
  ProgramStateRef OldState = Summary.getCorrespondingNode()->getState();
  ConstraintRangeTy Ranges = DstState->get<ConstraintRange>();
  ConstraintRangeTy::Factory &CRF = DstState->get_context<ConstraintRange>();

  bool isNul = false;
  // Apply the ranges stored for the reaped symbols.
  DeclConstraintRangeTy InputConstraints =
      OldState->get<InputConstraintRange>();
  for (DeclConstraintRangeTy::iterator I = InputConstraints.begin(),
                                       E = InputConstraints.end();
       I != E; I++) {
    Ranges = handleSummaryRange(S, CRF, Ranges, I->first, I->second, isNul);
    if (isNul)
      return NULL;
  }

  // Apply the remaining ranges.
  ConstraintRangeTy FinalRanges = OldState->get<ConstraintRange>();
  for (ConstraintRangeTy::iterator I = FinalRanges.begin(),
                                   E = FinalRanges.end();
       I != E; ++I) {
    Ranges = handleSummaryRange(
          S, CRF, Ranges, nonloc::SymbolVal(I->first), I->second, isNul);
    if (isNul)
      return NULL;
  }

  return DstState->set<ConstraintRange>(Ranges);
}

ProgramStateRef
RangeConstraintManager::assumeSymInBound(ProgramStateRef state, SymbolRef sym,
                                         const llvm::APSInt& From,
                                         const llvm::APSInt& To,
                                         const llvm::APSInt& Adjustment) {
  ProgramStateRef St = assumeSymGE(state, sym, From, Adjustment);
  if (St)
    St = assumeSymLE(St, sym, To, Adjustment);
  return St;
}

ProgramStateRef
RangeConstraintManager::assumeSymOutOfBound(ProgramStateRef state, SymbolRef sym,
                                            const llvm::APSInt& From,
                                            const llvm::APSInt& To,
                                            const llvm::APSInt& Adjustment) {
  ProgramStateRef St1 = assumeSymLT(state, sym, From, Adjustment);
  ProgramStateRef St2 = assumeSymGT(state, sym, To, Adjustment);
  RangeSet Range1 = St1 ? GetRange(St1, sym) : F.getEmptySet();
  RangeSet Range2 = St2 ? GetRange(St2, sym) : F.getEmptySet();
  RangeSet New(Range1.addRange(F, Range2));
  return New.isEmpty() ? NULL : state->set<ConstraintRange>(sym, New);
}

// This is going to be only a heuristic, not a full implementation
// More correct implementation should explode with multiple states
// For example, for equality operation, if x in [0;1]U[3;4] and y in [1;3] =>
// 1st state is (x == 1, y == 1) and 2nd state is (x == 3, y == 3)
// This implementation will return (x in {1}U{3} and y in {1}U{3}.
// But this seems to require massive assume() redesign.
ProgramStateRef
RangeConstraintManager::assumeSymSymGE(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // The only way to compare symsym exprs is to constraint their ranges
  BasicValueFactory &BV = getBasicVals();
  const RangeSet *rRS = state->get<ConstraintRange>(rhs),
      *lRS = state->get<ConstraintRange>(lhs);
  QualType LhsT = lhs->getType();
  RangeSet DefaultRS(F, BV.getMinValue(LhsT), BV.getMaxValue(LhsT));
  RangeSet RhsRS = rRS ? *rRS : DefaultRS;
  RangeSet LhsRS = lRS ? *lRS : DefaultRS;
  // x>=y => x.max>=y
  ProgramStateRef New = Adjustment.isInt()
      ? assumeSymLE(state, rhs, LhsRS.getMaxValue().getInt(),
                    Adjustment.getInt())
      : assumeSymLE(state, rhs, LhsRS.getMaxValue().getFloat(),
                    Adjustment.getFloat());
  if (New)
    // x>=y => x>=y.min
    New = Adjustment.isInt()
        ? assumeSymGE(New, lhs, RhsRS.getMinValue().getInt(),
                      Adjustment.getInt())
        : assumeSymGE(New, lhs, RhsRS.getMinValue().getFloat(),
                      Adjustment.getFloat());
  return New;
}

ProgramStateRef
RangeConstraintManager::assumeSymSymGT(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // The only way to compare symsym exprs is to constraint their ranges
  BasicValueFactory &BV = getBasicVals();
  const RangeSet *rRS = state->get<ConstraintRange>(rhs),
      *lRS = state->get<ConstraintRange>(lhs);
  QualType LhsT = lhs->getType();
  RangeSet DefaultRS(F, BV.getMinValue(LhsT), BV.getMaxValue(LhsT));
  RangeSet RhsRS = rRS ? *rRS : DefaultRS;
  RangeSet LhsRS = lRS ? *lRS : DefaultRS;
  // x>=y => x.max>=y
  ProgramStateRef New = Adjustment.isInt()
      ? assumeSymLT(state, rhs, LhsRS.getMaxValue().getInt(),
                    Adjustment.getInt())
      : assumeSymLT(state, rhs, LhsRS.getMaxValue().getFloat(),
                    Adjustment.getFloat());
  if (New)
    // x>=y => x>=y.min
    New = Adjustment.isInt()
        ? assumeSymGT(state, lhs, RhsRS.getMinValue().getInt(),
                      Adjustment.getInt())
        : assumeSymGT(state, lhs, RhsRS.getMinValue().getFloat(),
                      Adjustment.getFloat());
  return New;
}

ProgramStateRef
RangeConstraintManager::assumeSymSymLE(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // The only way to compare symsym exprs is to constraint their ranges
  BasicValueFactory &BV = getBasicVals();
  const RangeSet *rRS = state->get<ConstraintRange>(rhs),
      *lRS = state->get<ConstraintRange>(lhs);
  QualType LhsT = lhs->getType();
  RangeSet DefaultRS(F, BV.getMinValue(LhsT), BV.getMaxValue(LhsT));
  RangeSet RhsRS = rRS ? *rRS : DefaultRS;
  RangeSet LhsRS = lRS ? *lRS : DefaultRS;
  // x<=y => y.max>=x
  ProgramStateRef New = Adjustment.isInt()
      ? assumeSymLE(state, lhs, RhsRS.getMaxValue().getInt(),
                    Adjustment.getInt())
      : assumeSymLE(state, lhs, RhsRS.getMaxValue().getFloat(),
                    Adjustment.getFloat());
  if (New)
    // x<=y => y>=x.min
    New = Adjustment.isInt()
        ? assumeSymGE(New, rhs, LhsRS.getMinValue().getInt(),
                      Adjustment.getInt())
        : assumeSymGE(New, rhs, LhsRS.getMinValue().getFloat(),
                      Adjustment.getFloat());
  return New;
}

ProgramStateRef
RangeConstraintManager::assumeSymSymLT(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // The only way to compare symsym exprs is to constraint their ranges
  BasicValueFactory &BV = getBasicVals();
  const RangeSet *rRS = state->get<ConstraintRange>(rhs),
      *lRS = state->get<ConstraintRange>(lhs);
  QualType LhsT = lhs->getType();
  RangeSet DefaultRS(F, BV.getMinValue(LhsT), BV.getMaxValue(LhsT));
  RangeSet RhsRS = rRS ? *rRS : DefaultRS;
  RangeSet LhsRS = lRS ? *lRS : DefaultRS;
  // x<y => y.max>x
  ProgramStateRef New = Adjustment.isInt()
      ? assumeSymLT(state, lhs, RhsRS.getMaxValue().getInt(),
                    Adjustment.getInt())
      : assumeSymLT(state, lhs, RhsRS.getMaxValue().getFloat(),
                    Adjustment.getFloat());
  if (New)
    // x<y => y>x.min
    New = Adjustment.isInt()
        ? assumeSymGT(New, rhs, LhsRS.getMinValue().getInt(),
                      Adjustment.getInt())
        : assumeSymGE(New, rhs, LhsRS.getMinValue().getFloat(),
                      Adjustment.getFloat());
  return New;
}

ProgramStateRef
RangeConstraintManager::assumeSymSymEQ(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // The only way to compare symsym exprs is to constraint their ranges
  BasicValueFactory &BV = getBasicVals();
  const RangeSet *rRS = state->get<ConstraintRange>(rhs),
      *lRS = state->get<ConstraintRange>(lhs);
  QualType LhsT = lhs->getType();
  RangeSet DefaultRS(F, BV.getMinValue(LhsT), BV.getMaxValue(LhsT));
  RangeSet RhsRS = rRS ? *rRS : DefaultRS;
  RangeSet LhsRS = lRS ? *lRS : DefaultRS;
  RangeSet EQ = RhsRS.Intersect(BV, F, LhsRS);
  if (EQ.isEmpty())
    return 0;
  ProgramStateRef New = state->set<ConstraintRange>(lhs, EQ);
  New = New->set<ConstraintRange>(rhs, EQ);
  return New;
}

ProgramStateRef
RangeConstraintManager::assumeSymSymNE(ProgramStateRef state, SymbolRef lhs,
                                       SymbolRef rhs,
                                       const APValue &Adjustment) {
  // Not implemented yet cause it should return multiple states
  return state;
}


//===------------------------------------------------------------------------===
// Pretty-printing.
//===------------------------------------------------------------------------===/

void RangeConstraintManager::print(ProgramStateRef St, raw_ostream &Out,
                                   const char* nl, const char *sep) {

  ConstraintRangeTy Ranges = St->get<ConstraintRange>();
  InputConstraintRangeTy InputRanges = St->get<InputConstraintRange>();

  if (Ranges.isEmpty()) {
    Out << nl << sep << "Ranges are empty." << nl;
    return;
  }

  Out << nl << sep << "Ranges of symbol values:" << nl;
  for (ConstraintRangeTy::iterator I=Ranges.begin(), E=Ranges.end(); I!=E; ++I){
    Out << ' ' << I.getKey() << " : ";
    I.getData().print(Out);
    Out << nl;
  }
  Out << nl << sep << "Ranges of input values:" << nl;
  for (InputConstraintRangeTy::iterator I = InputRanges.begin(),
       E = InputRanges.end(); I != E; ++I) {
    Out << ' ';
    I.getKey().dumpToStream(Out);
    Out << " : ";
    I.getData().print(Out);
    Out << nl;
  }
}
