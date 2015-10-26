// RUN: %clang_cc1 -fcxx-exceptions -analyze -analyzer-checker=alpha.ctordtor.ExpInsideDtor -verify %s

void h() throw ();
void j() throw (int);
void f();
void f() { throw 1; }
void g() {
  try {
    f();
  }
  catch (...)
  {}
}

class A {
  A() {}
  ~A() { throw 1; } // expected-warning {{}}
};

class B {
  B() {}
  ~B() { f(); } // expected-warning {{}}
};

class C {
  C() {}
  ~C() { g(); } // no warning
};


class D {
  D() {}
  ~D() { // no warning
    try {
      f();
    }
    catch (...)
    {}
  }
};

class E {
  E() {}
  ~E() { h(); } // no warning
};

class F {
  F() {}
  ~F() { j(); } // expected-warning {{}}
};
