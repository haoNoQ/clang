// RUN: %clang_cc1 -analyze -analyzer-checker=core.builtin.NoReturnFunctions -analyzer-display-progress %s 2>&1 | FileCheck %s

// Do not reanalyze inlined private functions

class Test {
  void somePrivate() {}
public:
  void somePublic() {}
  void testPrivate();
  void testPublic();
};

void Test::testPrivate() {
  somePrivate();
}

void Test::testPublic() {
  somePublic();
}

// CHECK: analysis-order.cpp somePrivate
// CHECK: analysis-order.cpp somePublic
// CHECK: analysis-order.cpp testPrivate
// CHECK: analysis-order.cpp testPublic
// CHECK: analysis-order.cpp testPublic
// CHECK: analysis-order.cpp testPrivate
// CHECK: analysis-order.cpp somePublic
