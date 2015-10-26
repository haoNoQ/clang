//===---- CheckerHelpers.cpp - Helper functions for checkers ----*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
//  This file defines several static functions for use in checkers.
//
//===----------------------------------------------------------------------===//

#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerHelpers.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/MemRegion.h"
#include "clang/AST/Expr.h"

// Recursively find any substatements containing macros
bool clang::ento::containsMacro(const Stmt *S) {
  if (S->getLocStart().isMacroID())
    return true;

  if (S->getLocEnd().isMacroID())
    return true;

  for (Stmt::const_child_iterator I = S->child_begin(); I != S->child_end();
      ++I)
    if (const Stmt *child = *I)
      if (containsMacro(child))
        return true;

  return false;
}

// Recursively find any substatements containing enum constants
bool clang::ento::containsEnum(const Stmt *S) {
  const DeclRefExpr *DR = dyn_cast<DeclRefExpr>(S);

  if (DR && isa<EnumConstantDecl>(DR->getDecl()))
    return true;

  for (Stmt::const_child_iterator I = S->child_begin(); I != S->child_end();
      ++I)
    if (const Stmt *child = *I)
      if (containsEnum(child))
        return true;

  return false;
}

// Recursively find any substatements containing static vars
bool clang::ento::containsStaticLocal(const Stmt *S) {
  const DeclRefExpr *DR = dyn_cast<DeclRefExpr>(S);

  if (DR)
    if (const VarDecl *VD = dyn_cast<VarDecl>(DR->getDecl()))
      if (VD->isStaticLocal())
        return true;

  for (Stmt::const_child_iterator I = S->child_begin(); I != S->child_end();
      ++I)
    if (const Stmt *child = *I)
      if (containsStaticLocal(child))
        return true;

  return false;
}

// Recursively find any substatements containing __builtin_offsetof
bool clang::ento::containsBuiltinOffsetOf(const Stmt *S) {
  if (isa<OffsetOfExpr>(S))
    return true;

  for (Stmt::const_child_iterator I = S->child_begin(); I != S->child_end();
      ++I)
    if (const Stmt *child = *I)
      if (containsBuiltinOffsetOf(child))
        return true;

  return false;
}

std::string clang::ento::dumpMemRegion(const MemRegion *MR,
                                       const Environment &Env,
                                       const PrintingPolicy &Pr,
                                       const std::string &Default) {
  std::string MsgStr;
  llvm::raw_string_ostream Msg(MsgStr);
  if (MR->canPrintPretty())
    MR->printPretty(Msg);
  else {
    // FIXME: this should be implemented in more convenient way...
    for (Environment::iterator I = Env.begin(); I != Env.end(); ++I)
      if (I->second.getAsRegion() == MR) {
        const EnvironmentEntry &E = I->first;
        Msg << "'";
        E.getStmt()->printPretty(Msg, NULL, Pr);
        Msg << "'";
        break;
      }
  }
  if (!Msg.GetNumBytesInBuffer())
    return Default;
  return Msg.str();
}

namespace clang {
namespace ento {

RegionSet toRegionSet(const llvm::ImmutableSet<const MemRegion *> &ImmSet) {
  return toSet<const MemRegion *>(ImmSet);
}

} // end namespace ento
} // end namespace clang
