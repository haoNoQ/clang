// RUN: %clang_cc1 -analyze -analyzer-checker=debug.ExprInspection -analyzer-constraints=range -analyzer-config ipa=summary,max-times-inline-large=50,max-inlinable-size=50 -verify %s

void clang_analyzer_eval(int);

int oldStyleParamOrder(x, y)
  int y; // note: in different order!
  unsigned x;
{
  if (x > 5)
    return 0;
  return 1;
}

void testOldStyleParamOrder() {
  clang_analyzer_eval(oldStyleParamOrder(0, 0)); // expected-warning{{TRUE}}
}

typedef struct { int x, y, z; } ConjS;
ConjS makeConjS();
void useConjS(ConjS s) {
  if (s.x > 0)
    return;
}
void testConjS() {
  useConjS(makeConjS()); // no-crash
}

