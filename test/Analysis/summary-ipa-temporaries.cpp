// RUN: %clang_cc1 -analyze -analyzer-checker=debug.ExprInspection -analyzer-constraints=range -x c++ -analyzer-config ipa=summary,max-times-inline-large=50,max-inlinable-size=50 -verify %s

void clang_analyzer_eval(bool);

int some_func();

void *malloc(unsigned size);

struct SimpleStruct {
  int i, j;
  SimpleStruct(int _i, int _j): i(_i), j(_j) {}
  SimpleStruct() {}
};

int symExprSimpleStruct(const SimpleStruct &a) {
  return 2 * a.i + 1;
}

int symExprSimpleStructDirect(SimpleStruct a) {
  return 2 * a.i + 1;
}

int symExprSimpleStructDirectModify(SimpleStruct a) {
  int j = a.i;
  a.i = 2;
  return a.i + j;
}

int symExprSimpleStructBranches(SimpleStruct a) {
  if (a.j > 2)
    return 2 * a.i + 1;
  return 0;
}

class A { public: int x; };
class B: virtual public A { public: int y; };
class C: virtual public A { public: int z; };
class D: public B, public C { public: int t; };

class DD {
public:
  DD() {}
  DD(const DD &rhs): x(rhs.x), y(rhs.y) {}
  int x, y, z, t;
};

// called by testSymExpr
DD symExprReturnStruct() {
  DD dd;
  dd.x = 1;
  dd.y = 2;
  return dd;
}

int sumStruct(DD dSum) {
  return dSum.x + dSum.y;
}

// called by testSymExpr
int symExprVirtualInheritance(const D &ddd) {
  return ddd.x + ddd.y + ddd.z + ddd.t;
}

// called by testSymExpr
int symExprVirtualInheritanceDirect(D ddd) {
  return ddd.x + ddd.y + ddd.z + ddd.t;
}

SimpleStruct symExprReturnSimpleStruct() {
  SimpleStruct S;
  S.i = 1;
  S.j = 2;
  return S;
}

// called by testSymExpr
D symExprReturnObject() {
  D dd;
  dd.x = 1;
  dd.y = 2;
  dd.z = 3;
  dd.t = 4;
  return dd;
}


void symExprProduceObject(D *&d) {
  d = new D();
  d->x = 1;
  d->y = 2;
  d->z = 3;
  d->t = 4;
}

D *symExprReturnObjectPtr() {
  D *d = new D();
  d->x = 1;
  d->y = 2;
  d->z = 3;
  d->t = 4;
  return d;
}

void testSymExpr() {
  clang_analyzer_eval(symExprReturnSimpleStruct().i == 1); // expected-warning{{TRUE}}

  SimpleStruct q = symExprReturnSimpleStruct();
  clang_analyzer_eval(symExprSimpleStruct(q) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprSimpleStructDirect(q) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprSimpleStructDirectModify(q) == 3); // expected-warning{{TRUE}}
  q.j = some_func();
  if (q.j > 3)
    clang_analyzer_eval(symExprSimpleStructBranches(q) == 3); // expected-warning{{TRUE}}

  {
    DD d = symExprReturnStruct();
    clang_analyzer_eval(d.x + d.y == 3); // expected-warning{{TRUE}}
    clang_analyzer_eval(sumStruct(d) == 3); // expected-warning{{TRUE}}
  }

  D d1 = symExprReturnObject();
  clang_analyzer_eval(symExprVirtualInheritance(d1) == 10); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprVirtualInheritanceDirect(d1) == 10); // expected-warning{{TRUE}}

  clang_analyzer_eval(symExprReturnObject().x == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprVirtualInheritance(symExprReturnObject()) == 10); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprVirtualInheritanceDirect(symExprReturnObject()) == 10); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprReturnObject().x == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprVirtualInheritance(symExprReturnObject()) == 10); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprVirtualInheritanceDirect(symExprReturnObject()) == 10); // expected-warning{{TRUE}}
}

void testAssignment() {
  D d1 = symExprReturnObject();
  d1.x = 1;
  d1.y = 2;
  d1.z = 3;
  d1.t = 4;
  clang_analyzer_eval(symExprVirtualInheritanceDirect(d1) == 10); // expected-warning{{TRUE}}
}

void testPointers() {
  D *dd;
  symExprProduceObject(dd);
  clang_analyzer_eval(symExprVirtualInheritanceDirect(*dd) == 10); // expected-warning{{TRUE}}

  dd = symExprReturnObjectPtr();
  clang_analyzer_eval(symExprVirtualInheritanceDirect(*dd) == 10); // expected-warning{{TRUE}}
}


int &ref(int &b) { return b; }

void testTemporaryRef() {
  int c;
  ref(c) = 42;
  clang_analyzer_eval(c == 42); // expected-warning{{TRUE}}
}
