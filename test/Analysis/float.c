// RUN: %clang_cc1 -analyze -analyzer-checker=core,debug.ExprInspection -verify -analyzer-constraints=range %s

#include <float.h>
#include <limits.h>
#include <stdbool.h>
void clang_analyzer_eval(int);
void clang_analyzer_warnIfReached();

void concrete_float_comparison() {
  clang_analyzer_eval(1.0 == 1.0);  // expected-warning{{TRUE}}
  clang_analyzer_eval(1.0 == -1.0);  // expected-warning{{FALSE}}
  clang_analyzer_eval(1.0 != 1.0);  // expected-warning{{FALSE}}
  clang_analyzer_eval(1.0 > 0.0);  // expected-warning{{TRUE}}
  clang_analyzer_eval(-1.0 > 0.0);  // expected-warning{{FALSE}}
  clang_analyzer_eval(0.0 <= 0.0);  // expected-warning{{TRUE}}

  clang_analyzer_eval(1.0 == 1.0f);  // expected-warning{{TRUE}}
  if (1.0 == -1.0f)
    clang_analyzer_warnIfReached();  // no-warning
  clang_analyzer_eval(1.0 == -1.0f);  // expected-warning{{FALSE}}
  clang_analyzer_eval(1.0 != 1.0f);  // expected-warning{{FALSE}}
  clang_analyzer_eval(1.0 > 0.0f);  // expected-warning{{TRUE}}
  clang_analyzer_eval(-1.0 > 0.0f);  // expected-warning{{FALSE}}
  clang_analyzer_eval(0.0 <= 0.0f);  // expected-warning{{TRUE}}

  if (0.0f - 0.0f)
      clang_analyzer_warnIfReached(); // no-warning
  if (0.0 - 0.0)
      clang_analyzer_warnIfReached(); // no-warning
  if (0.0 - 0.0f)
        clang_analyzer_warnIfReached(); // no-warning
}

void float_sym_eval(float a) {

  float c = a;
  clang_analyzer_eval(c == a); // expected-warning{{TRUE}}

  double d = a;
  clang_analyzer_eval(d == a); // expected-warning{{TRUE}}

  if (a > 1.0)
    if (a < 0.0)
      clang_analyzer_eval(1); // no warning, unreachable code

  if (a > FLT_MAX)
    clang_analyzer_warnIfReached(); // no-warning

  if (a < -FLT_MAX)
    clang_analyzer_warnIfReached(); // no-warning
}

void check_float_ranges(float a) {
  if (a > 0.0f) {
    if(a <= FLT_MAX)
      clang_analyzer_warnIfReached(); // expected-warning {{REACHABLE}}
    if (a > FLT_MAX)
      clang_analyzer_warnIfReached(); // no-warning
    if (a > DBL_MAX)
      clang_analyzer_warnIfReached(); // no-warning
//    if (a > LDBL_MAX)
//      clang_analyzer_warnIfReached(); // no-warning

    if(a >= FLT_MIN)
       clang_analyzer_warnIfReached(); // expected-warning {{REACHABLE}}

     // FIXME: Need to normalize float, double, long double values correctly
    if(a < FLT_MIN)
      clang_analyzer_warnIfReached(); // no-warning
    if (a < DBL_MIN)
      clang_analyzer_warnIfReached(); // no-warning
//    if (a < LDBL_MIN)
//      clang_analyzer_warnIfReached(); // no-warning

  } else if (a < 0.0f) {
    if (a >= -FLT_MAX)
      clang_analyzer_warnIfReached(); // expected-warning {{REACHABLE}}
    if (a < -FLT_MAX)
      clang_analyzer_warnIfReached(); // no-warning
    if (a < -DBL_MAX)
      clang_analyzer_warnIfReached(); // no-warning
//    if (a < -LDBL_MAX)
//      clang_analyzer_warnIfReached(); // no-warning
//
    if(a <= -FLT_MIN)
      clang_analyzer_warnIfReached(); // expected-warning {{REACHABLE}}

    // FIXME: Need to normalize float, double, long double values correctly
    if(a > -FLT_MIN)
      clang_analyzer_warnIfReached(); // no-warning
    if(a > -DBL_MIN)
      clang_analyzer_warnIfReached(); // no-warning
//    if(a > -LDBL_MIN)
//      clang_analyzer_warnIfReached(); // no-warning
  } else {
    if (a != 0.0f)
      clang_analyzer_warnIfReached(); // no-warning
  }
}


void check_double_ranges(float a) {
  if (a > 0.0f) {
    if (a < 1.0) {
      clang_analyzer_warnIfReached(); // expected-warning {{REACHABLE}}
    }
  } else {
    if (a > 1.0) {
      clang_analyzer_warnIfReached(); // no-warning
    }
  }
}

//FIXME: We need to handle int to float correctly
void check_int_to_double_ranges(int a) {

  if (a > 0.1) {
    if (a < 0.9) {
      clang_analyzer_warnIfReached(); // FIXME: expected-warning {{REACHABLE}}
    }
  } else {
    if (a > 0.9) {
      clang_analyzer_warnIfReached(); // no-warning
    }
  }
}

void check_int_assign_float_ranges(int a) {
  float f = a;
  if (f > 0.0f) {
    if (f < 1.0) {
      clang_analyzer_warnIfReached();  // expected-warning {{REACHABLE}}
    }
  } else {
    if (f > 1.0) {
      clang_analyzer_warnIfReached(); // no-warning
    }
  }
}


void check_ranges_equality(double a) {
  if (a > 0.0) {

  } else if (a < 0.0) {

  } else {
     if (a != 0.0)
       clang_analyzer_warnIfReached();
  }
}

void check_ranges_binary_op() {
  float a = 2.5f + 2.5f;
  double b = 3.1 + 1.9f;
  if (a == b) {
    clang_analyzer_warnIfReached(); // no-warning
  }
}
