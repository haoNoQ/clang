// RUN: %clang_cc1 -analyze -analyzer-checker=core.DivideZero -analyzer-constraints=range -analyzer-config ipa=summary,max-times-inline-large=50,max-inlinable-size=50 -verify -x c++ %s
// expected-no-diagnostics

int divide(int x, int y) {
  return x / (y + 1);
}

void testDivide() {
  divide(0, -1); // no-crash
}
