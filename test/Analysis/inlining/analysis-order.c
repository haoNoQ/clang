// RUN: %clang_cc1 -analyze -analyzer-checker=core.builtin.NoReturnFunctions -analyzer-display-progress %s 2>&1 | FileCheck %s

// Do not analyze it again because it was inlined
static void someStatic();

void testStatic() {
  someStatic();
}

void someStatic() {
}

void someNonStatic();

void testNonStatic() {
  someNonStatic();
}

void someNonStatic() {
}


// CHECK: analysis-order.c testStatic
// CHECK: analysis-order.c someStatic
// CHECK: analysis-order.c testNonStatic
// CHECK: analysis-order.c someNonStatic
// CHECK: analysis-order.c testNonStatic
// CHECK: analysis-order.c someNonStatic
// CHECK: analysis-order.c testStatic
