// RUN: %clang_cc1 -analyze -analyzer-checker=debug.ExprInspection -analyzer-constraints=range -x c++ -analyzer-config ipa=summary -verify %s

// XFAIL:

void clang_analyzer_eval(bool);

int some_func();

void *malloc(unsigned size);

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

void testSymExpr() {
  SimpleCtorStruct *o = new SimpleCtorStruct(2, 2);
  clang_analyzer_eval(o->getModifiedI() == 5); // expected-warning{{TRUE}}
}

namespace NiceTestTakenFromArrayStructRegionCpp {
  struct Base {
    int& x;
    Base(int& x) : x(x) {}
  };
  struct Derived : public Base {
    Derived(int& x) : Base(x) {}
    void operator=(int a) { x = a; }
  };
  Derived ref(int& a) { return Derived(a); }
  void testDerived() {
    int b;
    ref(b) = 42;
    clang_analyzer_eval(b == 42); // expected-warning{{TRUE}}
  }
}

namespace NiceTestTakenFromArrayStructRegionCppv2 {
  struct Base {
    int& x;
    Base(int& x) : x(x) {}
    void operator=(int a) { x = a; }
  };
  Base ref(int& a) { return Base(a); }
  void testDerived() {
    int b;
    ref(b) = 42;
    clang_analyzer_eval(b == 42); // expected-warning{{TRUE}}
  }
}

// Callbacks

typedef void *(*CallbackType)(int);
int global_a;

int *callbackFunc() {
  return &global_a;
}

int *callBack(CallbackType cb, int arg) {
  return (int *)cb(arg);
}

void testCallback() {
  clang_analyzer_eval(callBack((CallbackType)callbackFunc, 0)); // expected-warning{{TRUE}}
}

// Symbolic offsets

int global_array[1000];

void invalidateArray(int i) {
    global_array[i] = 1;
}

void testInvalidateArray(int i) {
    global_array[0] = 0;
      invalidateArray(i);
        clang_analyzer_eval(global_array[0]); // expected-warning{{UNKNOWN}}
}
