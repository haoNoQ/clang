//== CheckerHelpers.h - Helper functions for checkers ------------*- C++ -*--=//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines CheckerVisitor.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_GR_PATHSENSITIVE_CHECKERHELPERS
#define LLVM_CLANG_GR_PATHSENSITIVE_CHECKERHELPERS

#include "clang/AST/Stmt.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/Environment.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/FunctionCallSummary.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "llvm/ADT/ImmutableSet.h"
#include <map>
#include <set>

namespace clang {

namespace ento {

typedef std::vector<const void *> VoidVector;

template<class T>
class SummarySet : public std::set<T> {
public:
  typedef typename SummarySet<T>::const_iterator const_iterator;
  typedef typename SummarySet<T>::iterator iterator;

  SummarySet<T> Actualize(Summarizer &S) const {
    SummarySet<T> Result;
    for (SummarySet<T>::const_iterator I = this->begin(),
         E = this->end(); I != E; ++I)
      Result.insert(S.actualizeAll<T>(*I));
    return Result;
  }
};

template<class T>
class SummaryList: public std::vector<T> {
public:
  typedef typename SummaryList<T>::const_iterator const_iterator;
  typedef typename SummaryList<T>::iterator iterator;

  SummaryList<T> Actualize(Summarizer &S) const {
    SummaryList<T> Result;
    for (SummaryList<T>::const_iterator I = this->begin(), E = this->end();
         I != E; ++I)
      Result.push_back(S.actualizeAll<T>(*I));
    return Result;
  }
};

template <class TK, class TV> class SummaryMap : public std::map<TK, TV> {
public:
  typedef typename SummaryMap<TK, TV>::const_iterator const_iterator;
  typedef typename SummaryMap<TK, TV>::iterator iterator;

  SummaryMap<TK, TV> Actualize(Summarizer &S) const {
    SummaryMap<TK, TV> Result;
    for (SummaryMap<TK, TV>::const_iterator I = this->begin(), E = this->end();
         I != E; ++I)
      Result[S.actualizeAll<TK>(I->first)] = S.actualizeAll<TV>(I->second);
    return Result;
  }
};

typedef SummarySet<const MemRegion *> RegionSet;
typedef SummaryList<const MemRegion *> RegionList;

bool containsMacro(const Stmt *S);
bool containsEnum(const Stmt *S);
bool containsStaticLocal(const Stmt *S);
bool containsBuiltinOffsetOf(const Stmt *S);
template <class T> bool containsStmt(const Stmt *S) {
  if (isa<T>(S))
      return true;

  for (Stmt::const_child_range I = S->children(); I; ++I)
    if (const Stmt *child = *I)
      if (containsStmt<T>(child))
        return true;

  return false;
}
// FIXME: Copied from Julia's code
std::string dumpMemRegion(const MemRegion *MR, const Environment &Env,
                          const PrintingPolicy &Pr, const std::string &Default);

template <typename T> SummarySet<T> toSet(const llvm::ImmutableSet<T> &ImmSet) {
  SummarySet<T> res;
  typedef typename llvm::ImmutableSet<T>::iterator iterator;
  for (iterator I = ImmSet.begin(), E = ImmSet.end(); I != E; ++I)
    res.insert(*I);
  return res;
}
template <typename T>
SummaryList<T> toList(const llvm::ImmutableList<T> &ImmList) {
  SummarySet<T> res;
  typedef typename llvm::ImmutableList<T>::iterator iterator;
  for (iterator I = ImmList.begin(), E = ImmList.end(); I != E; ++I)
    res.push_back(*I);
  return res;
}
template <typename TK, typename TV>
SummaryMap<TK, TV> toMap(const llvm::ImmutableMap<TK, TV> &ImmMap) {
  SummaryMap<TK, TV> res;
  typedef typename llvm::ImmutableMap<TK, TV>::iterator iterator;
  for (iterator I = ImmMap.begin(), E = ImmMap.end(); I != E; ++I)
    res[I->first] = I->second;
  return res;
}

template <typename TK, typename TV>
SummaryMap<TK, TV> *toMapPtr(const llvm::ImmutableMap<TK, TV> &ImmMap) {
  SummaryMap<TK, TV> *res = new SummaryMap<TK, TV>;
  typedef typename llvm::ImmutableMap<TK, TV>::iterator iterator;
  for (iterator I = ImmMap.begin(), E = ImmMap.end(); I != E; ++I)
    (*res)[I->first] = I->second;
  return res;
}

RegionSet toRegionSet(const llvm::ImmutableSet<const MemRegion *> &ImmSet);
} // end GR namespace

} // end clang namespace

#endif
