##===- unittests/Lex/Makefile ------------------------------*- Makefile -*-===##
#
#                     The LLVM Compiler Infrastructure
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
##===----------------------------------------------------------------------===##

CLANG_LEVEL = ../..
TESTNAME = Lex
LINK_COMPONENTS := mcparser support mc option bitreader
USEDLIBS = clangAST.a clangFrontend.a clangLex.a clangDriver.a clangParse.a \
  clangSema.a clangEdit.a clangAnalysis.a  clangSerialization.a clangAST.a \
  clangBasic.a LLVMTransformUtils.a

include $(CLANG_LEVEL)/unittests/Makefile
