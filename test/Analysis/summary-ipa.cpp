// RUN: %clang_cc1 -analyze -analyzer-checker=debug.ExprInspection -analyzer-constraints=range -x c++ -analyzer-config ipa=summary,max-times-inline-large=50,max-inlinable-size=50 -verify %s

void clang_analyzer_warnIfReached();
void clang_analyzer_eval(bool);

int global_a;
int global_array[1000];

typedef int (*func_ptr)(void);
func_ptr global_f;
func_ptr global_ff[2];

int some_func();

void *malloc(unsigned size);

// called by testIsZero
int isZero(int i) {
  if (i == 0)
   return 1;
  return 0;
}

int testIsZeroDirect() {
  if (isZero(0)) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    return 3;
  }
  clang_analyzer_warnIfReached(); // no-warning
  return 4;
}

// called by testNestedCallConstraint
int testIsZero() {
  int i = 0;
  if (isZero(i)) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    return 3;
  }
  clang_analyzer_warnIfReached(); // no-warning
  return 4;
}

// called by testMultipleRanges
int multipleRanges(int i) {
  if (i > 0 && i < 10)
    return 0;
  else if (i >= 20)
    return 1;
  return 2;
}

void testMultipleRanges() {
  int k = 4;
  if (multipleRanges(k) != 0)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  if (multipleRanges(25) != 1)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  k = 10;
  if (multipleRanges(k) != 2)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void testNestedCallConstraint() {
  if (testIsZero() == 3)
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // no-warning
}

// called by testSetGlobalVar
void setGlobalToOne() {
  global_a = 1;
}

// called by testSetGlobalVar
void setGlobalToZero() {
  global_a = 0;
}

// called by testSetGlobalVar
void setGlobalToValue(int v) {
  global_a = v;
}

void testSetGlobalVar() {
  setGlobalToZero();
  setGlobalToOne();
  if (global_a == 1)
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // no-warning
  setGlobalToValue(2);
  if (global_a == 2)
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // no-warning
}

// called by testBifurcateGlobalVar
int bifurcateGlobalVar() {
  if (global_a > 7)
    return 1;
  return 0;
}

void testBifurcateGlobalVar() {
  global_a = 10;
  if (bifurcateGlobalVar() == 1)
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // no-warning
}

// called by testSplitGlobalVarThreeStates
int splitGlobalVarThreeStates() {
  if (global_a > 7 && global_a < 20)
    return 1;
  return 0;
}

void testSplitGlobalVarThreeStates() {
  if (global_a > 8 && global_a < 25) {
    if (splitGlobalVarThreeStates() == 1) {
      clang_analyzer_eval(global_a > 8); // expected-warning{{TRUE}}
      clang_analyzer_eval(global_a < 20); // expected-warning{{TRUE}}
    } else {
      clang_analyzer_eval(global_a > 19); // expected-warning{{TRUE}}
      clang_analyzer_eval(global_a < 25); // expected-warning{{TRUE}}
    }
  }
}


void passByVal(int x) {
  x = 1;
  (void)x;
}

void testPassByVal(int k) {
  passByVal(k);
  if (k != 1)
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void passByRef(int &x) {
  x = 1;
}

void testPassByRef(int k) {
  passByRef(k);
  if (k != 1)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void testModifyArgByRef(int &k) {
  passByRef(k);
  if (k != 1)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void testModifyArgByRefDeep() {
  int k;
  testModifyArgByRef(k);
  if (k != 1)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

int condPassByRef(int &y) {
  if (y == 1)
    return 1;
  return 2;
}

void testCondPassByRef(int x) {
  int res = condPassByRef(x);
  if (x == 1 && res == 1) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_eval(x != 1); // expected-warning{{TRUE}}
    clang_analyzer_eval(res == 2); // expected-warning{{TRUE}}
  }
}

int condPassByArrayRef(int (&y)[1000]) {
  if (y[0] == 1)
    return 1;
  return 2;
}

void testCondPassByArrayRef() {
  int res = condPassByArrayRef(global_array);
  if (global_array[0] == 1 && res == 1) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_eval(global_array[0] != 1); // expected-warning{{TRUE}}
    clang_analyzer_eval(res == 2); // expected-warning{{TRUE}}
  }
}

int condPassByPtrRef(int *&y) {
  if (y[0] == 1)
    return 1;
  return 2;
}

void testCondPassByPtrRef(int *x) {
  int res = condPassByPtrRef(x);
  if (x[0] == 1 && res == 1) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_eval(x[0] != 1); // expected-warning{{TRUE}}
    clang_analyzer_eval(res == 2); // expected-warning{{TRUE}}
  }
}

int condRefPassByRef(int &y) {
  if (y == 1)
    return 1;
  return 2;
}

void testCondRefPassByRef(int &x) {
  int res = condRefPassByRef(x);
  if (x == 1 && res == 1) {
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_eval(x != 1); // expected-warning{{TRUE}}
    clang_analyzer_eval(res == 2); // expected-warning{{TRUE}}
  }
}

char passAndModify(long &i) {
  if (i > 10) {
    i = 4;
    return 0;
  } else {
    if (i < 5) {
      i = 7;
      return 1;
    }
  }
  return 2;
}

void testPassAndModify() {
  long k = 20;
  if (passAndModify(k) == 0) {
    clang_analyzer_eval(k == 4); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModify(k) == 1) {
    clang_analyzer_eval(k == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModify(k) == 2) {
    clang_analyzer_eval(k == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
}


char passAndModifyPtrValue(int *p) {
  if (*p > 10) {
    *p = 4;
    return 0;
  } else {
    if (*p < 5) {
      *p = 7;
      return 1;
    }
  }
  return 2;
}

void testPassAndModifyPtrValue(int *ptr) {
  *ptr = 20;
  if (passAndModifyPtrValue(ptr) == 0) {
    clang_analyzer_eval(*ptr == 4); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModifyPtrValue(ptr) == 1) {
    clang_analyzer_eval(*ptr == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModifyPtrValue(ptr) == 2) {
    clang_analyzer_eval(*ptr == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
}

char passAndModifyPtrValueCond(int *p) {
  if (*p > 10) {
    if (p < (int *)30) {
      *p = 4;
      return 0;
    } else {
      *p = 2;
      return 4;
    }
  } else {
    if (*p < 5) {
      *p = 7;
      return 1;
    }
  }
  return 2;
}

void testPassAndModifyPtrValueCond(int *ptr) {
  *ptr = 20;
  char res = passAndModifyPtrValueCond(ptr);
  if (res == 0 || res == 4) {
    if (ptr < (int *)30) {
      clang_analyzer_eval(*ptr == 4); // expected-warning{{TRUE}}
      clang_analyzer_eval(res == 0);  // expected-warning{{TRUE}}
      clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } else {
      clang_analyzer_eval(*ptr == 2); // expected-warning{{TRUE}}
      clang_analyzer_eval(res == 4);  // expected-warning{{TRUE}}
      clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModifyPtrValueCond(ptr) == 1) {
    clang_analyzer_eval(*ptr == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
  if (passAndModifyPtrValueCond(ptr) == 2) {
    clang_analyzer_eval(*ptr == 7); // expected-warning{{TRUE}}
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  } else {
    clang_analyzer_warnIfReached(); // no-warning
  }
}

int ptrIsNull(int *ptr) {
  if (ptr != 0) {
    *ptr = 2;
    return 1;
  }
  return 0;
}

void testConstPtr() {
  int t;
  int res = ptrIsNull(&t);
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(t == 2);   // expected-warning{{TRUE}}
  struct { int tt; } ss;
  res = ptrIsNull(&ss.tt);
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(ss.tt == 2);   // expected-warning{{TRUE}}
  int aa[3];
  res = ptrIsNull(&aa[2]);
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(aa[2] == 2);   // expected-warning{{TRUE}}
}


void testParamPtr(int *p) {
  int res = ptrIsNull(p);
  if (p != 0) {
    clang_analyzer_eval(*p == 2);   // expected-warning{{TRUE}}
    clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  } else
    clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
}

bool constPtrIsNull(const void *ptr) {
  return ptr == 0;
}

void testConstPtrIsNull(const void *p) {
  int t; // test conversion from non-const int* to const void*
  clang_analyzer_eval(constPtrIsNull(&t)); // expected-warning{{FALSE}}
  clang_analyzer_eval(constPtrIsNull(p)); // expected-warning{{UNKNOWN}}
}

struct SimpleStruct {
  int i, j;
  SimpleStruct(int _i, int _j): i(_i), j(_j) {}
  SimpleStruct() {}
};


// called by testConstraintStructOneField
int constraintStructOneField(const SimpleStruct &arg) {
  if (arg.i > 0 && arg.i < 10)
    return 0;
  else if (arg.i >= 20)
    return 1;
  return 2;
}

void testConstraintStructOneField() {
  SimpleStruct s;
  s.i = s.j = 4;
  if (constraintStructOneField(s) != 0)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  s.i = 10;
  if (constraintStructOneField(s) != 2)
    clang_analyzer_warnIfReached(); // no-warning
  else
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

// called by testConstraintStructTwoFields
int hasZeroField(const SimpleStruct &arg) {
  if (arg.i == 0 || arg.j == 0)
   return 1;
  return 0;
}

void testConstraintStructTwoFields(const SimpleStruct &arg) {
  int res = hasZeroField(arg);
  if (arg.i == 0)
    clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  else if (arg.j == 0)
    clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  else
    clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
}

struct SimpleCtorStruct;
int areTwoFieldsZero(const SimpleCtorStruct &arg);

struct SimpleCtorStruct {
  int i, j;
  SimpleCtorStruct(int _i, int _j): i(_i), j(_j) {}
  SimpleCtorStruct(): i(0), j(1) {}
  int areTwoFieldsZero() const {
    if (i == 0 && j == 0)
      return 1;
    return 0;
  }
  int areTwoFieldsZeroWithCall() const {
    return ::areTwoFieldsZero(*this);
  }
  void zeroFields() {
    i = j = 0;
  }
  int testNestedMethodCall() {
    if (areTwoFieldsZero()) {
      i = 1;
      j = 2;
      return 1;
    } else {
      i = -1;
      j = -2;
      return 0;
    }
  }
  void setIErroneous(int _i) { i = _i + 1; }
  int getModifiedI() { return 2 * i + 1; }
};

int areTwoFieldsZero(const SimpleCtorStruct &arg) {
  if (arg.i == 0 && arg.j == 0)
    return 1;
  return 0;
}

void testDefaultCtorStruct() {
  SimpleCtorStruct s;
  clang_analyzer_eval(s.j == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.i == 0); // expected-warning{{TRUE}}
}

void testParametrizedCtorStruct() {
  SimpleCtorStruct s(2, 3);
  clang_analyzer_eval(s.j == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.i == 2); // expected-warning{{TRUE}}
}

// Called by testMethodBifurcateNested
void testMethodBifurcate() {
  SimpleCtorStruct s;
  int res = s.areTwoFieldsZero();
  clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
  s.j = 0;
  res = s.areTwoFieldsZero();
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
}

void testMethodBifurcateNested() {
  SimpleCtorStruct s;
  int res = s.areTwoFieldsZeroWithCall();
  clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
  s.j = 0;
  res = s.areTwoFieldsZeroWithCall();
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
}

void testNestedMethodCall() {
  SimpleCtorStruct s;
  int res = s.testNestedMethodCall();
  clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.i == -1); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.j == -2); // expected-warning{{TRUE}}
  s.zeroFields();
  res = s.testNestedMethodCall();
  clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.i == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.j == 2); // expected-warning{{TRUE}}
}

int isArrZero(int *a) {
  if (a[0] == 0 && a[1] == 0) {
    return 1;
  }
  return 0;
}

void testIsArrZero(int *p) {
  int res = isArrZero(p);
  if (p[0] == 0 && p[1] == 0)
    clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
  else
    clang_analyzer_eval(res == 0); // expected-warning{{TRUE}}
}

void testSymSymBranch(int a, int b) {
  // Just make sure we don't crash on trying to compose a summary
  if (a + b)
    ;
}

// called by testSymExpr
int symExpr(int a) {
  return 2 * a + 1;
}

// called by testSymExpr
int symExprPtr(int *a) {
  return 2 * (*a) + 1;
}

// called by testSymExpr
int symExprRef(const int &a) {
  return 2 * a + 1;
}

// called by testSymExpr
int symExprArr(int *a) {
  return 2 * a[1] + 1;
}

// called by testSymExpr
int symExprDoubleArr(int a[2][2]) {
  return 2 * a[1][0] + 1;
}

// called by testSymExpr
int symExprSimpleStruct(const SimpleStruct &a) {
  return 2 * a.i + 1;
}

// called by testSymExpr
int symExprSimpleStructDirect(SimpleStruct a) {
  return 2 * a.i + 1;
}

// called by testSymExpr
int symExprSimpleStructDirectModify(SimpleStruct a) {
  int j = a.i;
  a.i = 2;
  return a.i + j;
}

// called by testSymExpr
int symExprSimpleStructBranches(SimpleStruct a) {
  if (a.j > 2)
    return 2 * a.i + 1;
  return 0;
}

// called by testSymExpr
void symExprMove(int &a, int b) {
  a = b;
}

// called by testSymExpr
int symExprAdd(int a, int b) {
  return a + b;
}

struct SimplePtrStruct {
  int *i, *j;
  int *getI() { return i; }
  int *getJ() { return j; }
  int getIMinusJ() { return i - j; }
};

class A { public: int x; };
class B: virtual public A { public: int y; };
class C: virtual public A { public: int z; };
class D: public B, public C { public: int t; };

// called by testSymExpr
int symExprVirtualInheritance(const D &d1) {
  return d1.x + d1.y + d1.z + d1.t;
}

// called by testSymExpr
int symExprVirtualInheritanceDirect(D d2) {
  return d2.x + d2.y + d2.z + d2.t;
}

// called by testSymExpr
void symExprProduceObject(D *&d3) {
  d3 = new D();
  d3->x = 1;
  d3->y = 2;
  d3->z = 3;
  d3->t = 4;
}

// called by testSymExpr
SimpleStruct symExprReturnSimpleStruct() {
  SimpleStruct S;
  S.i = 1;
  S.j = 2;
  return S;
}

// called by testSymExpr
D symExprReturnObject() {
  D d4;
  d4.x = 1;
  d4.y = 2;
  d4.z = 3;
  d4.t = 4;
  return d4;
}

// called by testSymExpr
D *symExprReturnObjectPtr() {
  D *d5 = new D();
  d5->x = 1;
  d5->y = 2;
  d5->z = 3;
  d5->t = 4;
  return d5;
}

void testSymExpr(SimplePtrStruct *p) {

  int i = 1;
  clang_analyzer_eval(symExpr(i) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprPtr(&i) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprRef(i) == 3); // expected-warning{{TRUE}}


  int j[2];
  j[1] = 1;
  clang_analyzer_eval(symExprArr(j) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprAdd(i, j[1]) == 2); // expected-warning{{TRUE}}


  int k[2][2];
  k[1][0] = 1;
  clang_analyzer_eval(symExprDoubleArr(k) == 3); // expected-warning{{TRUE}}


  SimpleStruct m;
  m.i = 1;
  clang_analyzer_eval(symExprSimpleStruct(m) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprSimpleStructDirect(m) == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(symExprSimpleStructDirectModify(m) == 3); // expected-warning{{TRUE}}
  m.j = some_func();
  if (m.j > 3)
    clang_analyzer_eval(symExprSimpleStructBranches(m) == 3); // expected-warning{{TRUE}}


  SimpleCtorStruct n(2, 2);
  clang_analyzer_eval(n.getModifiedI() == 5); // expected-warning{{TRUE}}
  n.i = 1;
  clang_analyzer_eval(n.getModifiedI() == 3); // expected-warning{{TRUE}}
  n.setIErroneous(2); // actually sets to 3
  clang_analyzer_eval(n.getModifiedI() == 7); // expected-warning{{TRUE}}


  SimpleCtorStruct *o = new SimpleCtorStruct(2, 2);
  o->i = 1;
  clang_analyzer_eval(o->getModifiedI() == 3); // expected-warning{{TRUE}}
  o->setIErroneous(2); // actually sets to 3
  clang_analyzer_eval(o->getModifiedI() == 7); // expected-warning{{TRUE}}


  if (p->getI())
    return;
  if (p->getJ())
    return;
  clang_analyzer_eval(p->getIMinusJ()); // expected-warning{{FALSE}}
  int l = 3;
  symExprMove(i, l);
  clang_analyzer_eval(symExpr(i) == 7); // expected-warning{{TRUE}}

  D d;
  d.x = 1;
  d.y = 2;
  d.z = 3;
  d.t = 4;
  clang_analyzer_eval(symExprVirtualInheritance(d) == 10); // expected-warning{{TRUE}}

  D *dd;
  symExprProduceObject(dd);
  clang_analyzer_eval(symExprVirtualInheritance(*dd) == 10); // expected-warning{{TRUE}}

  dd = symExprReturnObjectPtr();
  clang_analyzer_eval(symExprVirtualInheritance(*dd) == 10); // expected-warning{{TRUE}}
}

void testRecursive() {
  // Try to not hang.
  testRecursive();
}

float symFloatExpr(float a) {
  return a + 1.0;
}

void testSymFloatExpr() {
  float b = 2.0;
  clang_analyzer_eval(symFloatExpr(b) > 2.5); // expected-warning{{TRUE}}
}

int another_func() {
  return global_a;
}
int codeRegion() {
  global_a = 4;
  global_f = another_func;
  global_ff[0] = some_func;
  global_ff[1] = another_func;
  return global_f() + global_ff[1]();
}
void testCodeRegion() {
  clang_analyzer_eval(codeRegion() == 8); // expected-warning{{TRUE}}
  clang_analyzer_eval(global_f() == 4); // expected-warning{{TRUE}}
  clang_analyzer_eval(global_ff[1]() == 4); // expected-warning{{TRUE}}
}


namespace CrashesTakenFromReferenceCpp {

int *maybeNull() {
  extern bool coin();
  static int x;
  return coin() ? &x : 0;
}
void use(int &x) {
  x = 1;
}
void testSuppression() {
  use(*maybeNull()); // no-crash
}

char* ptr();
char &refFromPointer() {
  return *ptr();
}
void testReturnReference() {
  clang_analyzer_eval(ptr() == 0); // expected-warning{{UNKNOWN}}
  (void)(&refFromPointer() == 0);
}
}

struct StructWithDtor {
  ~StructWithDtor() { global_a = 1; }
};
void causeDestructor() {
  StructWithDtor s;
} // no-crash
void testDestructor() {
  causeDestructor();
  clang_analyzer_eval(global_a == 1); // expected-warning{{TRUE}}
}

struct ComplicatedStruct {
  struct InnerStructOne {
    int foo;
    int x[4];
    int *bar;
  } one[2];
  int extra;
  class InnerStructTwo : public InnerStructOne {
  public:
    InnerStructOne more;
    int y[4];
    int &ref;
    InnerStructTwo(int &val): ref(val) {}
  } two;
  ComplicatedStruct(int &ext): two(ext) {}
};
void modifyComplicatedStruct(ComplicatedStruct &s) {
  s.one[0].x[1] = 1;
  s.one[1].x[0] = 2;
  s.extra = 3;
  s.two.more.x[0] = 4;
  s.two.more.x[1] = 5;
  s.two.y[0] = 6;
  s.two.x[0] = 7;
  s.two.y[1] = 8;
  s.two.x[1] = 9;
  s.one[0].foo = 10;
  s.one[1].foo = 11;
  s.two.foo = 12;
  s.two.more.foo = 13;
  s.one[0].bar = (int *)14;
  s.one[1].bar = (int *)15;
  s.two.bar = (int *)16;
  s.two.more.bar = (int *)17;
}
void testModifyComplicatedStruct() {
  int eightteen = 18;
  ComplicatedStruct s(eightteen);
  modifyComplicatedStruct(s);
  clang_analyzer_eval(s.one[0].x[1] == 1); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.one[1].x[0] == 2); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.extra == 3); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.more.x[0] == 4); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.more.x[1] == 5); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.y[0] == 6); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.x[0] == 7); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.y[1] == 8); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.x[1] == 9); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.one[0].foo == 10); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.one[1].foo == 11); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.foo == 12); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.more.foo == 13); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.one[0].bar == (int *)14); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.one[1].bar == (int *)15); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.bar == (int *)16); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.more.bar == (int *)17); // expected-warning{{TRUE}}
  clang_analyzer_eval(s.two.ref == 18); // expected-warning{{TRUE}}
}

void passAndModifyPoiterByReference(int *&p) {
  p = (int *)malloc(2*sizeof(int));
  if (p) {
    *p = 1;
    *(p + 1) = 2;
  }
}
void testPassAndModifyPoiterByReference() {
  int *p = 0;
  passAndModifyPoiterByReference(p);
  int res = p[0] == 1 && p[1] == 2;
  if (p)
    clang_analyzer_eval(res == 1); // expected-warning{{TRUE}}
}

typedef struct ForwardDeclStruct *ForwardDeclStructRef;
ForwardDeclStructRef createForwardDeclStruct();
class TestForwardDeclStruct {
  static ForwardDeclStructRef ref1, ref2;
  static ForwardDeclStructRef testForwardDeclStruct() {
    ref1 = createForwardDeclStruct();
    ref2 = ref1;
    return ref1;
  } // no-crash
  static void testForwardDeclStructValues() {
    ForwardDeclStructRef ref3 = testForwardDeclStruct();
    clang_analyzer_eval(ref1 == ref3); // expected-warning{{TRUE}}
    clang_analyzer_eval(ref2 == ref3); // expected-warning{{TRUE}}
  }
};

void swap(int &x, int &y) {
  int z = x;
  x = y;
  y = z;
}

void testSwap() {
  int x = 1, y = 2;
  swap(x, y);
  clang_analyzer_eval(x == 2); // expected-warning{{TRUE}}
  clang_analyzer_eval(y == 1); // expected-warning{{TRUE}}
}

class ThisRegionManipulations {
public:
  bool compareThat(const ThisRegionManipulations *that) const {
    return that - this;
  }
};

void testThisRegionManipulations(ThisRegionManipulations *ptr1,
                                 ThisRegionManipulations *ptr2) {
  clang_analyzer_eval(ptr1->compareThat(ptr1)); // expected-warning{{FALSE}}
  clang_analyzer_eval(ptr1->compareThat(ptr2)); // expected-warning{{UNKNOWN}}
}

void invalidateGlobals() {
  some_func();
}

void testInvalidateGlobals() {
  global_a = 0;
  invalidateGlobals();
  clang_analyzer_eval(global_a); // expected-warning{{UNKNOWN}}
}

int conjure();
void exportMapCheckFunction(int *x) {
  *x = conjure();
}
void testExportMap() {
  int x, y;
  int *arr[2];
  arr[0] = &x;
  arr[1] = &y;
  for (int i = 0; i < 2; ++i)
    exportMapCheckFunction(arr[i]);
  clang_analyzer_eval(x - y); // expected-warning{{UNKNOWN}}
}

const bool TRUE = !0;
int defaultArg(bool arg=TRUE) {
  if (arg)
    return 1;
  return 0;
}
void testDefaultArg() {
  if (defaultArg()) // no-crash
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  else
    clang_analyzer_warnIfReached(); // no-warning
}

void *global_label;
void labelFunc(void *label) {
  global_label = label;
  if (label)
    global_a = 1;
}

void testLabelFunc() {
  labelFunc(&&test_label); // no-crash
  clang_analyzer_eval((bool)global_label); // expected-warning{{TRUE}}
  clang_analyzer_eval(global_a); // expected-warning{{TRUE}}
test_label:
  return;
}
