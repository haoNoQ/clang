// RUN: %clang_cc1 -analyze -analyzer-checker=core,debug.ExprInspection -verify %s

void clang_analyzer_eval(int);
#define CHECK(expr) if (!(expr)) return; clang_analyzer_eval(expr)

void testPersistentConstraints(int x, int y) {
  CHECK(x); // expected-warning{{TRUE}}
  CHECK(x & 1); // expected-warning{{TRUE}}
  CHECK(1 - x); // expected-warning{{TRUE}}
  CHECK(x & y); // expected-warning{{TRUE}}
}
