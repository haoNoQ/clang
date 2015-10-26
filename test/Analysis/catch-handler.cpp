// RUN: %clang_cc1 -analyze -analyzer-checker=core,debug.ExprInspection -fexceptions -fcxx-exceptions -verify %s

void clang_analyzer_warnIfReached();

void testAllHandler(void) {
    try {
        throw "Exc";
    } catch(...) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testCatchSelect(void) {
    try {
        throw "Exc";
    } catch(const char* s) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } catch(int* i) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch(...) {
        clang_analyzer_warnIfReached();  // no-warning
    }
}

void testCatchSelect2(void) {
    try {
        throw "Exc";
    } catch(int* i) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch(...) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testNoArgsThrow() {
    try {
        throw;
    } catch (...) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testNoArgsThrow2() {
    try {
        throw;
    } catch(const char* s) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch (...) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

class Matherr {};
class Overflow: public Matherr {};
class Underflow: public Matherr {};
class ZeroDivide: public Matherr {};
class Wrongflow: public Overflow, Underflow {};

void testInheritance() {
    try {
        throw ZeroDivide();
    } catch (Overflow o) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch (Matherr m) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testInheritance2() {
    try {
        throw Wrongflow();
    } catch (Overflow o) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } catch (Underflow u) {
        clang_analyzer_warnIfReached();  // no-warning
    }
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void testInheritanceNegative() {
    try {
        throw ZeroDivide();
    } catch (Overflow o) {
        clang_analyzer_warnIfReached(); // no-warning
    } catch (Underflow u) {
        clang_analyzer_warnIfReached();  // no-warning
    }
    clang_analyzer_warnIfReached(); // no-warning
}

void g(void) {
    throw ZeroDivide();
    clang_analyzer_warnIfReached();  // no-warning
}

void testThrowInMethod() {
    try {
        g();
        clang_analyzer_warnIfReached();  // no-warning
    } catch (Overflow oo) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch (Matherr mm) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void f(void) {
    g();
    clang_analyzer_warnIfReached();  // no-warning
}

void testThrowInMethod2() {
    try {
        f();
        clang_analyzer_warnIfReached();  // no-warning
    } catch (Overflow oo) {
        clang_analyzer_warnIfReached();  // no-warning
    } catch (...) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void g2() {
    try {
        throw Underflow();
    } catch (Matherr mm) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testInnerCatchBlock() {
    try {
        g2();
    } catch (...) {
        clang_analyzer_warnIfReached();  // no-warning
    }
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void testConditionalThrow(bool b) {
    try {
        if (b) {
            throw Overflow();
        }
    } catch (Overflow oo) {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    }
}

void testNegative() {
    try {
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } catch (...) {
        clang_analyzer_warnIfReached();  // no-warning
    }
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void h(void) {
}

void testNegative2() {
    try {
        h(); // no exception thrown
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } catch (...) {
        clang_analyzer_warnIfReached();  // no-warning
    }
    clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}
