//== FunctionCallSummary.cpp - Function call summary path-sensitive checkers-=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines FunctionCallSummary that provides summary for function
//  calls for path-sensitive checkers.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Core/PathSensitive/CallEvent.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CoreEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ExprEngine.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/FunctionCallSummary.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramState.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/AST/RecordLayout.h"
#include <stdio.h>
#include <unistd.h>

using namespace clang;
using namespace ento;
using namespace llvm;

unsigned ExportMap::getBlockCount(unsigned Count) {
  unsigned Ret = OriginalBlockCount + Count;
  assert(Ret > OriginalBlockCount && "Block count overflow!");
  if (Ret > NewBlockCount)
    NewBlockCount = Ret;
  return Ret;
}

size_t getMemorySize() {
  long rss = 0L;
  FILE* fp = NULL;
  if ( (fp = fopen( "/proc/self/statm", "r" )) == NULL )
    return (size_t)0L;      /* Can't open? */
  if ( fscanf( fp, "%*s%ld", &rss ) != 1 ) {
      fclose( fp );
      return (size_t)0L;      /* Can't read? */
  }
  fclose( fp );
  return (size_t)rss * (size_t)sysconf( _SC_PAGESIZE);
}

const SymbolConjured *ExportMap::get(const SymbolConjured *ConjSym,
                                     CallEventRef<CallEvent> Call) {

  assert(ConjSym);
  ConjSymbolMap::const_iterator val = ConjSymMap.find(ConjSym);
  if (val != ConjSymMap.end())
    return val->second;
  const SymbolConjured *NewConjSym =
      Call->getState()->getSymbolManager().conjureSymbol(
          ConjSym->getStmt(), Call->getLocationContext(), ConjSym->getType(),
          getBlockCount(ConjSym->getCount()), ConjSym->getTag());
  ConjSymMap[ConjSym] = NewConjSym;
  return NewConjSym;
}

const CXXTempObjectRegion *ExportMap::get(const CXXTempObjectRegion *TempReg,
                                          CallEventRef<CallEvent> Call) {
  assert(TempReg);
  TempRegionMap::const_iterator val = TempRegMap.find(TempReg);
  if (val != TempRegMap.end())
    return val->second;
  MemRegionManager &MemMgr =
      Call->getState()->getStateManager().getRegionManager();
  const Expr *E = TempReg->getExpr();
  const LocationContext *LCtx = Call->getLocationContext();
  // FIXME: Block count??
  const CXXTempObjectRegion *NewTempReg =
      isa<GlobalInternalSpaceRegion>(TempReg->getMemorySpace())
          ? MemMgr.getCXXStaticTempObjectRegion(E)
          : MemMgr.getCXXTempObjectRegion(E, LCtx);
  TempRegMap[TempReg] = NewTempReg;
  return NewTempReg;
}

namespace clang {
namespace ento {

static const Expr *getCallArgExpr(const ParmVarDecl *PD,
                                  CallEventRef<CallEvent> Call) {
  unsigned maxno = Call->getNumArgs();
  if (isa<FunctionDecl>(Call->getDecl())) {
    // ParmVarDecl::getFunctionScopeIndex gives incorrect results when
    // old-style C function parameter types are written out
    // in a different order than actual function parameters.
    // Try to workaround manually first. But this method fails for some
    // virtual function calls.
    const FunctionDecl *BodyDecl = cast<FunctionDecl>(PD->getDeclContext());
    assert(BodyDecl && BodyDecl->hasBody());
    unsigned no = 0;
    for (FunctionDecl::param_const_iterator I = BodyDecl->param_begin(),
                                            E = BodyDecl->param_end();
         I != E && no < maxno; ++I, ++no) {
      if (*I == PD)
        return Call->getArgExpr(no);
    }
  }
  unsigned no = PD->getFunctionScopeIndex();
  if (no >= maxno)
    return NULL;
  return Call->getArgExpr(no);
}

// note: returns SVal that isn't necessarily a region
SVal Summarizer::composeRegionUncached(const MemRegion *FormalMR) {
  const LocationContext *LCtx = Call->getLocationContext();
  ProgramStateRef state = Call->getState();
  ProgramStateManager &Mgr = state->getStateManager();
  ASTContext &ACtx = Mgr.getContext();
  SValBuilder &SVB = Mgr.getSValBuilder();
  MemRegionManager &MemMgr = Mgr.getRegionManager();

  switch (FormalMR->getKind()) {

  case MemRegion::GlobalInternalSpaceRegionKind:
  case MemRegion::GlobalSystemSpaceRegionKind: {
    return loc::MemRegionVal(
        MemMgr.getGlobalsRegion(FormalMR->getKind(), NULL));
  }

  case MemRegion::AllocaRegionKind: {
    const AllocaRegion *r = cast<AllocaRegion>(FormalMR);
    return loc::MemRegionVal(
        MemMgr.getAllocaRegion(r->getExpr(), r->getCount(), LCtx));
  }
  case MemRegion::SymbolicRegionKind: {
    const SymbolicRegion *r = cast<SymbolicRegion>(FormalMR);
    SVal cs = composeSymbol(r->getSymbol());
    if (cs.isUnknownOrUndef())
      return cs;
    if (Optional<nonloc::SymbolVal> sv = cs.getAs<nonloc::SymbolVal>()) {
      SymbolRef Sym = sv->getAsSymbol();
      if (const SymbolRegionAddress *sra = dyn_cast<SymbolRegionAddress>(Sym))
        return loc::MemRegionVal(sra->getRegion());
      if (const SymbolLabelAddress *sla = dyn_cast<SymbolLabelAddress>(Sym))
        return loc::GotoLabel(sla->getLabel());
      assert(Loc::isLocType(sv->getSymbol()->getType()) &&
             "Trying to compose a symbolic region for a non-pointer symbol");
      return loc::MemRegionVal(MemMgr.getSymbolicRegion(sv->getSymbol()));
    }
    if (Optional<nonloc::ConcreteInt> ci = cs.getAs<nonloc::ConcreteInt>()) {
      // Special case: Symbol resolved to concrete int location.
      // It is already the correct loc value, no further action is required.
      return loc::ConcreteInt(ci->getValue());
    }
    assert(false && "Unsupported Symbol for Symbolic Region");
  }
  case MemRegion::FunctionTextRegionKind: {
    const FunctionTextRegion *r = cast<FunctionTextRegion>(FormalMR);
    return SVB.getFunctionPointer(cast<FunctionDecl>(r->getDecl()));
  }
  case MemRegion::CompoundLiteralRegionKind: {
    const CompoundLiteralRegion *r = cast<CompoundLiteralRegion>(FormalMR);
    return loc::MemRegionVal(
        MemMgr.getCompoundLiteralRegion(r->getLiteralExpr(), LCtx));
  }
  case MemRegion::CXXBaseObjectRegionKind: {
    const CXXBaseObjectRegion *r = cast<CXXBaseObjectRegion>(FormalMR);
    SVal reg = composeRegion(r->getSuperRegion());
    if (const MemRegion *mr = reg.getAsRegion()) {
      const CXXRecordDecl *formalBaseDecl = r->getDecl()->getDefinition();
      assert(formalBaseDecl);
      if (const CXXBaseObjectRegion *br = dyn_cast<CXXBaseObjectRegion>(mr))
        if (br->getDecl()->getDefinition() == formalBaseDecl)
          return loc::MemRegionVal(br);
      mr = MemMgr.getCXXBaseObjectRegion(formalBaseDecl, mr, r->isVirtual());
      return loc::MemRegionVal(mr);
    }
    if (reg.isUnknownOrUndef())
      return reg;
    else if (reg.getAs<loc::ConcreteInt>())
      return UndefinedVal();
    assert(false && "Could not compose CXXBaseObjectRegion");
  }
  case MemRegion::CXXThisRegionKind: {
    const CXXThisRegion *r = cast<CXXThisRegion>(FormalMR);
    const CXXThisRegion *nr =
        MemMgr.getCXXThisRegion(r->getLocationType(), CalleeSFC);
    SVal L = loc::MemRegionVal(nr);
    SVal val;
    if (const CXXConstructorCall *c = dyn_cast<CXXConstructorCall>(Call))
      val = c->getCXXThisVal();
    else if (const CXXDestructorCall *c = dyn_cast<CXXDestructorCall>(Call))
      val = c->getCXXThisVal();
    else if (const CXXInstanceCall *c = dyn_cast<CXXInstanceCall>(Call))
      val = c->getCXXThisVal();
    else
      assert(false && "Unsupported kind of CallEvent for this-object");
    TempState = TempState->bindLoc(L, val);
    return L;
  }
  case MemRegion::FieldRegionKind: {
    const FieldRegion *r = cast<FieldRegion>(FormalMR);
    SVal reg = composeRegion(r->getSuperRegion());
    if (!reg.getAs<Loc>()) {
      if (reg.isUnknownOrUndef())
        return reg;
      assert(false && "Could not compose FieldRegion");
    } else if (reg.getAs<loc::ConcreteInt>())
      return UndefinedVal();
    return state->getLValue(r->getDecl(), reg.castAs<Loc>());
  }
  case MemRegion::VarRegionKind: {
    const VarRegion *r = cast<VarRegion>(FormalMR);
    const VarDecl *d = r->getDecl();
    if (const ParmVarDecl *pd = dyn_cast<ParmVarDecl>(d)) {
      Loc L = state->getLValue(pd, CalleeSFC);
      const Expr *ArgE = getCallArgExpr(pd, Call);
      if (!ArgE)
        return UnknownVal();
      SVal val = state->getSVal(ArgE, Call->getLocationContext());
      TempState = TempState->bindLoc(L, val);
      return L;
    } else {
      return state->getLValue(d, LCtx);
    }
  }
  case MemRegion::ElementRegionKind: {
    const ElementRegion *r = cast<ElementRegion>(FormalMR);
    SVal reg = composeRegion(r->getSuperRegion());
    SVal idx = composeSVal(r->getIndex());
    if (idx.isUnknownOrUndef())
      return idx;
    assert(idx.getAs<NonLoc>() && "Element index should be NonLoc");
    QualType T = r->getElementType();
    if (const MemRegion *mr = reg.getAsRegion()) {
      if (const TypedValueRegion *tr = dyn_cast<TypedValueRegion>(mr))
        if (tr->getValueType() == T) {
          // Implement pointer arithmetic:
          // element{element{MR, i, T}, j, T} == element{MR, i + j, T}
          return SVB.evalBinOpLN(state, BO_Add, reg.castAs<Loc>(),
                                 idx.castAs<NonLoc>(), tr->getLocationType());
        }
      return loc::MemRegionVal(
          MemMgr.getElementRegion(T, idx.castAs<NonLoc>(), mr, ACtx));
    }
    if (reg.isUnknownOrUndef())
      return reg;
    else if (reg.getAs<loc::ConcreteInt>())
      return UndefinedVal();
    assert(false && "Could not compose ElementRegion");
  }
  case MemRegion::StringRegionKind: {
    const StringRegion *r = cast<StringRegion>(FormalMR);
    return *(SVB.getConstantVal(r->getStringLiteral()));
  }
  case MemRegion::CXXTempObjectRegionKind: {
    const CXXTempObjectRegion *r = cast<CXXTempObjectRegion>(FormalMR);
    return loc::MemRegionVal(ExpMap.get(r, Call));
  }
  default:
    assert(false && "Unsupported MemRegion Kind");
  }
}

// note: returns SVal that isn't necessarily a symbol
SVal Summarizer::composeSymbolUncached(SymbolRef FormalSym) {
  ProgramStateRef state = Call->getState();
  ProgramStateManager &Mgr = state->getStateManager();
  SValBuilder &SVB = Mgr.getSValBuilder();
  SymbolManager &SymMgr = state->getSymbolManager();
  ASTContext &ACtx = Mgr.getContext();
  MemRegionManager &MemMgr = Mgr.getRegionManager();

  switch (FormalSym->getKind()) {

  case SymExpr::SymIntKind: {
    const SymIntExpr *s = cast<SymIntExpr>(FormalSym);
    QualType FormalTy = s->getType();
    SVal l = composeSymbol(s->getLHS());
    SVal r = SVB.makeIntVal(s->getRHS());
    return SVB.evalBinOp(state, s->getOpcode(), l, r, FormalTy);
  }
  case SymExpr::IntSymKind: {
    const IntSymExpr *s = cast<IntSymExpr>(FormalSym);
    QualType FormalTy = s->getType();
    SVal l = SVB.makeIntVal(s->getLHS());
    SVal r = composeSymbol(s->getRHS());
    return SVB.evalBinOp(state, s->getOpcode(), l, r, FormalTy);
  }
  case SymExpr::SymFloatKind: {
    const SymFloatExpr *s = cast<SymFloatExpr>(FormalSym);
    QualType FormalTy = s->getType();
    SVal l = composeSymbol(s->getLHS());
    SVal r = SVB.makeFloatVal(s->getRHS());
    return SVB.evalBinOp(state, s->getOpcode(), l, r, FormalTy);
  }
  case SymExpr::FloatSymKind: {
    const FloatSymExpr *s = cast<FloatSymExpr>(FormalSym);
    QualType FormalTy = s->getType();
    SVal l = SVB.makeFloatVal(s->getLHS());
    SVal r = composeSymbol(s->getRHS());
    return SVB.evalBinOp(state, s->getOpcode(), l, r, FormalTy);
  }
  case SymExpr::SymSymKind: {
    const SymSymExpr *s = cast<SymSymExpr>(FormalSym);
    QualType FormalTy = s->getType();
    SVal l = composeSymbol(s->getLHS());
    SVal r = composeSymbol(s->getRHS());
    return SVB.evalBinOp(state, s->getOpcode(), l, r, FormalTy);
  }
  case SymExpr::CastSymbolKind: {
    const SymbolCast *s = cast<SymbolCast>(FormalSym);
    QualType FormalTy = s->getType();
    SVal operand = composeSymbol(s->getOperand());
    QualType OriginalTy = s->getOperand()->getType();
    if (FormalTy->isIntegralOrEnumerationType() && Loc::isLocType(OriginalTy)) {
      if (Optional<nonloc::ConcreteInt> nlci =
              operand.getAs<nonloc::ConcreteInt>()) {
        // Special case: Whenever composeSymbol is supposed to return
        // loc::ConcreteInt, it converts it to nonloc::ConcreteInt.
        // Here we need to convert it back, otherwise evalCast would
        // try to turn it into a SymbolCast of a non-symbol.
        operand = loc::ConcreteInt(nlci->getValue());
      }
    }
    return SVB.evalCast(operand, FormalTy, OriginalTy);
  }
  case SymExpr::ConjuredKind: {
    const SymbolConjured *s = cast<SymbolConjured>(FormalSym);
    return nonloc::SymbolVal(ExpMap.get(s, Call));
  }
  case SymExpr::DerivedKind: {
    const SymbolDerived *s = cast<SymbolDerived>(FormalSym);
    SymbolRef psym = composeSymbol(s->getParentSymbol()).getAsSymbol();
    if (!psym)
      return UnknownVal();
    const MemRegion *preg = composeRegion(s->getRegion()).getAsRegion();
    if (!preg)
      return UnknownVal();
    QualType T = s->getType();
    if (!isa<TypedValueRegion>(preg))
      preg = MemMgr.getElementRegion(T, SVB.makeZeroArrayIndex(), preg, ACtx);
    return nonloc::SymbolVal(
        SymMgr.getDerivedSymbol(psym, cast<TypedValueRegion>(preg)));
  }
  case SymExpr::ExtentKind: {
    const SymbolExtent *s = cast<SymbolExtent>(FormalSym);
    SVal reg = composeRegion(s->getRegion());
    if (const MemRegion *mr = reg.getAsRegion())
      return cast<SubRegion>(mr)->getExtent(SVB);
    return UndefinedVal();
  }
  case SymExpr::MetadataKind: {
    const SymbolMetadata *s = cast<SymbolMetadata>(FormalSym);
    SVal reg = composeRegion(s->getRegion());
    if (const MemRegion *mr = reg.getAsRegion()) {
      const SymbolMetadata *sym = SymMgr.getMetadataSymbol(
          mr, s->getStmt(), s->getType(), s->getCount(), s->getTag());
      return CMgr.runCheckersForEvalSummarySVal(*this, nonloc::SymbolVal(sym));
    }
    return UnknownVal();
  }
  case SymExpr::RegionValueKind: {
    const SymbolRegionValue *s = cast<SymbolRegionValue>(FormalSym);
    ProgramStateRef state = Call->getState();
    QualType FormalT = s->getType();

    SVal regval = composeRegion(s->getRegion());
    if (regval.isUnknownOrUndef())
      return regval;
    if (regval.getAs<loc::ConcreteInt>())
      return UndefinedVal();
    const MemRegion *reg = regval.getAsRegion();
    assert(reg);
    SVal val = TempState->getSVal(regval.castAs<Loc>(), FormalT);

    if (Optional<nonloc::LocAsInteger> LAI =
            val.getAs<nonloc::LocAsInteger>()) {
      const MemRegion *MR = val.getAsRegion();
      SVal Address = MR->getAddress(state);
      SymbolRef AddressSym = Address.getAsSymbol();
      assert(AddressSym && "Memory region address was supposed to be a symbol");
      return SVB.evalCast(Address, FormalT, AddressSym->getType());
    } else if (const MemRegion *MR = val.getAsRegion()) {
      return MR->getAddress(state);
    } else if (Optional<loc::ConcreteInt> LCI = val.getAs<loc::ConcreteInt>()) {
      return nonloc::ConcreteInt(LCI->getValue());
    } else if (Optional<loc::GotoLabel> GL = val.getAs<loc::GotoLabel>()) {
      return nonloc::SymbolVal(SymMgr.getLabelAddressSymbol(GL->getLabel()));
    } else {
      assert(!val.getAs<Loc>());
      assert(!val.getAs<nonloc::CompoundVal>());
      assert(!val.getAs<nonloc::LazyCompoundVal>());
      return val;
    }
  }
  case SymExpr::RegionAddressKind: {
    const SymbolRegionAddress *s = cast<SymbolRegionAddress>(FormalSym);
    SVal reg = composeRegion(s->getRegion());
    if (reg.isUnknownOrUndef())
      return reg;
    if (Optional<loc::ConcreteInt> lci = reg.getAs<loc::ConcreteInt>())
      return nonloc::ConcreteInt(lci->getValue());
    if (const MemRegion *mr = reg.getAsRegion())
      return mr->getAddress(state);
    assert(false && "Unsupported region for SymbolRegionAddress");
  }
  case SymExpr::LabelAddressKind: {
    const SymbolLabelAddress *s = cast<SymbolLabelAddress>(FormalSym);
    return nonloc::SymbolVal(s);
  }
  default:
    assert(false && "Unsupported Symbol Kind");
  }
}

SVal Summarizer::composeSValUncached(SVal Formal) {
  SVal::BaseKind BaseKind = Formal.getBaseKind();
  ProgramStateRef state = Call->getState();
  const LocationContext *LCtx = Call->getLocationContext();
  ProgramStateManager &Mgr = state->getStateManager();
  StoreManager &StMgr = Mgr.getStoreManager();
  SValBuilder &SVB = Mgr.getSValBuilder();
  BasicValueFactory &BVF = Mgr.getBasicVals();
  ASTContext &ACtx = Mgr.getContext();

  switch (BaseKind) {

  case SVal::UndefinedKind:
  case SVal::UnknownKind:
    return Formal;

  case SVal::NonLocKind: {
    unsigned SubKind = Formal.getSubKind();
    switch (SubKind) {

    case nonloc::SymbolValKind: {
      return composeSymbol(Formal.getAsSymbol());
   }

    case nonloc::LocAsIntegerKind: {
      nonloc::LocAsInteger l = Formal.castAs<nonloc::LocAsInteger>();
      SVal reg = composeSVal(l.getLoc());
      if (reg.isUnknownOrUndef())
        return reg;
      if (Optional<loc::ConcreteInt> LCI = reg.getAs<loc::ConcreteInt>()) {
        nonloc::ConcreteInt NLCI(LCI->getValue());
        return SVB.evalCast(
            NLCI, ACtx.getIntTypeForBitwidth(l.getNumBits(), l.isSigned()),
            ACtx.getUIntPtrType());
      }
      return SVB.makeLocAsInteger(reg.castAs<Loc>(), l.getNumBits(),
                                  l.isSigned());
    }

    case nonloc::ConcreteIntKind:
    case nonloc::ConcreteFloatKind:
      return Formal;

    case nonloc::CompoundValKind: {
      nonloc::CompoundVal cv = Formal.castAs<nonloc::CompoundVal>();
      const CompoundValData *cvd = cv.getValue();
      llvm::ImmutableList<SVal> vals = BVF.getEmptySValList();
      for (CompoundValData::iterator i = cvd->begin(), e = cvd->end(); i != e;
           ++i) {
        SVal composed = composeSVal(*i);
        vals = BVF.consVals(composed, vals);
      }
      return SVB.makeCompoundVal(cvd->getType(), vals);
    }

    case nonloc::LazyCompoundValKind: {
      nonloc::LazyCompoundVal lcv = Formal.castAs<nonloc::LazyCompoundVal>();
      const MemRegion *originalReg = lcv.getRegion();
      SVal reg = composeRegion(originalReg);
      if (reg.isUnknownOrUndef())
        return reg;
      if (reg.getAs<loc::ConcreteInt>())
        return UndefinedVal();

      class StoreHandler: public StoreManager::BindingsHandler {
        Summarizer &S;
        StoreRef ToStore;
        StoreManager &ToStoreMgr;
        const MemRegion *ParentRegion;

        bool checkRegion(const MemRegion *Region) {
          while (Region != ParentRegion) {
            if (const SubRegion *SR = dyn_cast_or_null<SubRegion>(Region))
              Region = SR->getSuperRegion();
            else
              return false;
          }
          return true;
        }

        virtual bool HandleBinding(StoreManager &SMgr, Store store,
                                   const MemRegion *Region, uint64_t Offset,
                                   SVal Value, bool Direct) {
          if (!checkRegion(Region))
            return true;
          const MemRegion *reg = S.composeRegion(Region).getAsRegion();
          if (!reg)
            return true;
          RegionOffset RO = reg->getAsOffset();
          if (RO.hasSymbolicOffset())
            return true;
          reg = reg->getBaseRegion();
          SVal val = S.composeSVal(Value);
          ToStore = ToStoreMgr.BindByOffset(ToStore.getStore(),
                                            loc::MemRegionVal(reg), val,
                                            Offset + RO.getOffset(), Direct);
          return true;
        }

      public:
        StoreHandler(Summarizer &s, StoreRef toStore, StoreManager &toStoreMgr,
                     const MemRegion *parentRegion)
            : S(s), ToStore(toStore), ToStoreMgr(toStoreMgr),
              ParentRegion(parentRegion) {}
        StoreRef getStore() const { return ToStore; }
      } handler(*this, StMgr.getInitialStore(LCtx), StMgr, originalReg);

      StMgr.iterBindings(lcv.getStore(), handler);
      StoreRef st = handler.getStore();
      return SVB.makeLazyCompoundVal(st,
                                     cast<TypedValueRegion>(reg.getAsRegion()));
    }

    default:
      assert(false && "Unsupported NonLoc SubKind");
    }
  }
  case SVal::LocKind: {
    unsigned SubKind = Formal.getSubKind();
    switch (SubKind) {

    case loc::MemRegionKind:
      return composeRegion(Formal.getAsRegion());

    case loc::ConcreteIntKind:
      return Formal;

    default:
      assert(false && "Unsupported Loc SubKind");
    }
  }
  default:
    assert(false && "Unsupported SVal BaseKind");
  }
  llvm_unreachable("");
}

const MemRegion *Summarizer::actualizeRegion(const MemRegion *MR) {
  if (!MR)
    return NULL;
  SVal ret = composeRegion(MR);
  return ret.getAsRegion();
}

SymbolRef Summarizer::actualizeSymbol(SymbolRef Sym) {
  if (!Sym)
    return NULL;
  SVal ret = composeSymbol(Sym);
  return ret.getAsSymbol();
}

template <>
const MemRegion *
Summarizer::actualizeAll<const MemRegion *>(const MemRegion *const &MR) {
  return actualizeRegion(MR);
}

SVal Summarizer::actualizeSVal(SVal val) {
  SVal ret = composeSVal(val);

  // Detect composing of loc to non-loc and vice-versa, for debugging.
  if (ret.isUnknownOrUndef())
    return ret;
  assert((((bool)ret.getAs<Loc>()) == ((bool)val.getAs<Loc>())) &&
         "Loc-NonLoc issue");
  return ret;
}

template <> SVal Summarizer::actualizeAll<SVal>(const SVal &SV) {
  return actualizeSVal(SV);
}

} // end namespace ento
} // end namespace clang

typedef CLANG_ENTO_PROGRAMSTATE_MAP(const Expr *, unsigned) SummaryBlockCountTy;
REGISTER_TRAIT_WITH_PROGRAMSTATE(SummaryBlockCount, SummaryBlockCountTy)
REGISTER_TRAIT_WITH_PROGRAMSTATE(ReturnValue, const void *)

FunctionCallBranchSummary::FunctionCallBranchSummary(ProgramStateRef state,
    const ExplodedNode *FinishNode, SubEngine *EE)
    : CorrespondingNode(FinishNode) {
  assert(state);
  assert(FinishNode->getState());
  CheckerSummary = static_cast<ExprEngine *>(EE)
                       ->getCheckerManager()
                       .runCheckersForEvalSummaryPopulate(state);
}

ProgramStateRef
FunctionCallBranchSummary::saveReturnValue(ProgramStateRef State, SVal Ret) {
  return State->set<ReturnValue>(new SVal(Ret));
}

/// Apply summary of given Decl to a current state.
/// This function is a potential replacement for inlineCall mechanism.
void clang::ento::CallFunction(ExprEngine &Eng, const CallEvent &Call,
                               NodeBuilder &Bldr, ExplodedNode *Pred,
                               const StackFrameContext *CalleeSFC,
                               ProgramStateRef State,
                               const FunctionCallSummary &CS) {
  const LocationContext *LCtx = Pred->getLocationContext();
  const StackFrameContext *CallerSFC = LCtx->getCurrentStackFrame();
  const Expr *OriginExpr = Call.getOriginExpr();

  ConstraintManager &CoMgr = State->getStateManager().getConstraintManager();
  CheckerManager &CMgr = Eng.getCheckerManager();

  const unsigned *BlockCountPtr = State->get<SummaryBlockCount>(OriginExpr);
  unsigned BlockCount = BlockCountPtr ? *BlockCountPtr : 0;

  for (FunctionCallSummary::const_iterator FSI = CS.begin(), FSE = CS.end();
       FSI != FSE; FSI++) {

    const FunctionCallBranchSummary &Summary = **FSI;

    ProgramStateRef OldState = Summary.getCorrespondingNode()->getState();
    StoreManager &OldStoreMgr = OldState->getStateManager().getStoreManager();

    // Now we need to actualize a lot of values, so we construct a Summarizer,
    // and for that we need an ExportMap. Return value can safely be bound
    // before we call the checkers, so that it were accessible inside
    // the checker callbacks.
    ExportMap ExpMap(BlockCount);
    CallEventRef<CallEvent> CallBeforeEverything = Call.cloneWithState(State);
    Summarizer S1(CallBeforeEverything, ExpMap, CalleeSFC, CMgr);

    // Consult ConstraintManager to impose the necessary constraints.
    ProgramStateRef DstState = CoMgr.applyCallBranchSummary(Summary, S1);
    if (!DstState)
      continue;

    // Now we need to actualize a lot of values, so we construct a Summarizer,
    // and for that we need an ExportMap. Return value can safely be bound
    // before we call the checkers, so that it were accessible inside
    // the checker callbacks.
    Summarizer S2 = S1.cloneWithState(DstState);
    if (const SVal *OldRetVal =
            static_cast<const SVal *>(OldState->get<ReturnValue>())) {
      SVal Ret = S2.actualizeSVal(*OldRetVal);
      DstState = DstState->BindExpr(OriginExpr, LCtx, Ret);
    }

    // Prepare to run the checkers. Construct pre-apply node for the branch.
    CallSummaryPreApply CallSummPre(OriginExpr, CalleeSFC, LCtx);
    ExplodedNode *PreApplyNode = Bldr.generateNode(CallSummPre, DstState, Pred);
    Bldr.takeNodes(PreApplyNode); // No need to have it in the frontier.
    ExplodedNodeSet Src, Dst;
    // Just one node.
    Src.Add(PreApplyNode);

    CallEventRef<CallEvent> CallAfterResult = Call.cloneWithState(DstState);

    // Woohoooo, here goes nothing.
    CMgr.runCheckersForEvalSummaryApply(
          Dst, Src, Eng, S2, *CallAfterResult, Summary.getCheckerSummary(),
          Summary.getCorrespondingNode()->getState());

    // Checkers might have split our node into many.
    // We need to do the rest of the job for all destination nodes.
    if (Dst.size() == 0)
      Dst.Add(PreApplyNode);

    for (ExplodedNodeSet::const_iterator NI = Dst.begin(), NE = Dst.end();
         NI != NE; ++NI) {

      ProgramStateRef NodeDstState = (*NI)->getState();
      assert(NodeDstState);
      CallEventRef<CallEvent> NodeCall = Call.cloneWithState(NodeDstState);

      // Invalidate globals if necessary.
      class InvalidationHandler : public StoreManager::BindingsHandler {
        ProgramStateRef State;
        NodeBuilder &Bldr;
        const CallEvent &Call;

      public:
        InvalidationHandler(ProgramStateRef state, NodeBuilder &bldr,
                            const CallEvent &call)
            : State(state), Bldr(bldr), Call(call) {}
        virtual ~InvalidationHandler() {}
        ProgramStateRef getState() const { return State; }

        bool HandleBinding(StoreManager &SMgr, Store store, const MemRegion *MR,
                           uint64_t Offset, SVal val, bool Direct) {
          if (isa<GlobalInternalSpaceRegion>(MR) ||
              isa<GlobalSystemSpaceRegion>(MR)) {

            State =
                Call.invalidateRegions(Bldr.getContext().blockCount(), State);
            assert(State);
            return false;
          }
          return true;
        }
      };
      InvalidationHandler IH(NodeDstState, Bldr, *NodeCall);
      OldStoreMgr.iterBindings(OldState->getStore(), IH);
      NodeDstState = IH.getState();

      // Bind final values. We could not have done it before checkers,
      // because actualization inside checker callbacks could break.
      class FinalValueHandler : public StoreManager::BindingsHandler {
        Summarizer &S;
        llvm::SmallVector<OffsetBind, 64> Binds;

      public:
        FinalValueHandler(Summarizer &s)
            : S(s) {}
        virtual ~FinalValueHandler() {}
        const ArrayRef<OffsetBind> getBinds() { return Binds; }

        bool HandleBinding(StoreManager &SMgr, Store store, const MemRegion *MR,
                           uint64_t Offset, SVal val, bool Direct) {
          if (MR->hasStackStorage() ||
              isa<StaticGlobalSpaceRegion>(MR->getMemorySpace()))
            return true;
          const MemRegion *ActualReg = S.actualizeRegion(MR);
          if (!ActualReg)
            return true;
          const RegionOffset &RO = ActualReg->getAsOffset();
          if (RO.hasSymbolicOffset())
            return true;
          ActualReg = ActualReg->getBaseRegion();
          Offset += RO.getOffset();
          SVal ActualVal = S.actualizeSVal(val);
          Binds.push_back(OffsetBind(loc::MemRegionVal(ActualReg),
                                     ActualVal, Offset, Direct));
          return true;
        }
      };
      Summarizer S3 = S2.cloneWithState(NodeDstState);
      FinalValueHandler VH(S3);
      OldStoreMgr.iterBindings(OldState->getStore(), VH);

      NodeDstState = NodeDstState->bindLocsByOffset(VH.getBinds());

      // Bind the constructed object value to CXXConstructExpr.
      if (const CXXConstructExpr *CCE =
              dyn_cast_or_null<CXXConstructExpr>(OriginExpr)) {
        const CXXConstructorCall *CtorCall =
            dyn_cast<CXXConstructorCall>(&Call);
        loc::MemRegionVal This =
            CtorCall->getCXXThisVal().castAs<loc::MemRegionVal>();
        SVal ThisV = This;
        if (const MemRegion *MR = This.getAsRegion())
          if (!OriginExpr->isGLValue() && isa<CXXTempObjectRegion>(MR))
            ThisV = NodeDstState->getSVal(ThisV.getAsRegion());
        NodeDstState = NodeDstState->BindExpr(CCE, CallerSFC, ThisV);
        assert(NodeDstState);
      }

      CallSummaryPostApply CallSummPost(OriginExpr, CalleeSFC,
                                        Summary.getCorrespondingNode(), LCtx);

      // Update the summary block count.
      NodeDstState = NodeDstState->set<SummaryBlockCount>(
          OriginExpr, ExpMap.updatedBlockCount());

      Bldr.generateNode(CallSummPost, NodeDstState, *NI);
    }
  }

  if (CMgr.getAnalyzerOptions().shouldCollectSummaryStat())
    Eng.getSummaries()->addNodesProceed(
          Eng.getSummaryStack().front()->getCanonicalDecl(), CS.NodesProceed);
}
