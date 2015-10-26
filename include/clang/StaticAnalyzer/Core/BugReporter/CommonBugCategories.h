//=--- CommonBugCategories.h - Provides common issue categories -*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_STATIC_ANALYZER_BUG_CATEGORIES_H
#define LLVM_CLANG_STATIC_ANALYZER_BUG_CATEGORIES_H

// Common strings used for the "category" of many static analyzer issues.
namespace clang {
  namespace ento {
    namespace categories {
      extern const char * const CoreFoundationObjectiveC;
      extern const char * const LogicError;
      extern const char * const MemoryCoreFoundationObjectiveC;
      extern const char * const UndefBehavior;
      extern const char * const UnixAPI;
    }
  }
}
#endif

