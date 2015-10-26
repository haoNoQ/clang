// RUN: %clang_cc1 -Wno-tautological-compare -analyze -analyzer-checker=core,debug.ExprInspection -verify %s

#define UCHAR_MAX ((unsigned char)(~0U))
#define CHAR_MAX (signed char)((UCHAR_MAX - 1) / 2)
#define CHAR_MIN (signed char)(-CHAR_MAX - 1)
#define INT_MAX ((int)(~0U >> 1))
#define INT_MIN (-INT_MAX - 1)
#define UINT_MAX (~0U)
#define LONG_MAX ((long)(~0UL >> 1))
#define LONG_MIN (-LONG_MAX - 1)

void clang_analyzer_eval(bool);
void clang_analyzer_warnIfReached();
char getChar();
int getInt();
unsigned int getUnsignedInt();
long int getLongInt();
float getFloat();
double getDouble();

void test_1() {
  int a = getInt();
  long long int b = a;
  bool c = b > INT_MAX;
  clang_analyzer_eval(c); // expected-warning{{FALSE}}
}

void test_2() {
  int a = getInt();
  char b = a;
  bool c = (b <= CHAR_MAX) && (b >= CHAR_MIN);
  bool d = (a <= INT_MAX) && (a >= INT_MIN);
  clang_analyzer_eval(c); // expected-warning{{TRUE}}
  clang_analyzer_eval(d); // expected-warning{{TRUE}}
}

void test_3() {
  unsigned int a = getUnsignedInt();
  char b = a;
  if (b > CHAR_MAX)
    clang_analyzer_warnIfReached(); // no-warning
}

void test_4() {
  unsigned int a = getUnsignedInt();
  unsigned char b = a;
  bool c = (b <= UCHAR_MAX) && (b >= 0);
  bool d = (a <= UINT_MAX) && (a >= 0);
  clang_analyzer_eval(c); // expected-warning{{TRUE}}
  clang_analyzer_eval(d); // expected-warning{{TRUE}}
}

void test_5() {
  unsigned int a = getUnsignedInt();
  unsigned char b = a;
  if (a < 50) {
    if (b > 60)
      clang_analyzer_warnIfReached(); // no-warning
    else
      clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
  }
}

void test_6() {
  unsigned char a = getChar();
  int b = a;
  long long c = a;
  if (b > 0)
    if (c < 60)
      clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
}

void test_7() {
  int a = getInt();
  if (a > -6 && a < INT_MAX) {
    unsigned char b = a;
    bool c = (b <= UCHAR_MAX) && (b >= 0);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_8() {
  int a = getInt();
  if (a > 249 && a < 281) {
    char b = a;
    bool c = (b <= 24) && (b >= -6);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_9() {
  int a = getInt();
  if (a > 249 && a < 601) {
    char b = a;
    bool c = (b <= CHAR_MAX) && (b >= CHAR_MIN);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_10() {
  int a = getInt();
  if (a > 249 && a < 601) {
    unsigned char b = a;
    bool c = (b <= UCHAR_MAX) && (b >= 0);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_11() {
  int a = getInt();
  if (a >= -6 && a <= -1) {
    unsigned char b = a;
    bool c = (b <= UCHAR_MAX) && (b >= (UCHAR_MAX - 5));
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_12() {
  int a = getInt();
  char b = a;
  if (b < 200) {
    bool c = (a <= INT_MAX) && (a >= INT_MIN);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

void test_13() {
  unsigned int a = getUnsignedInt();
  int b = a;
  if (b >= 0 && b <= 255) {
    bool c = (a <= UINT_MAX) && (a >= 0);
    clang_analyzer_eval(c); // expected-warning{{TRUE}}
  }
}

// FIXME: Should be TRUE
void test_14() {
  int a = getInt();
  if (a > 249 && a < 281) {
    char b = a;
    if (b > 0) {
      bool c = (a <= 256) && (a >= 280);
      clang_analyzer_eval(c); // expected-warning{{FALSE}}
    }
  }
}
// FIXME: Should be FALSE
void test_15(signed char a) {
  if ((a + 5) < 0LL)
    clang_analyzer_eval(a == 0); // expected-warning{{UNKNOWN}}
}

// FIXME: Ranges of b should be {[65536;4294967295]} instead of {[65536;2147483647],[2147483648;4294967295]}
void test_16() {
  int a = getInt();
  if ((unsigned int)(a) >= 65536)
    unsigned b = a;
}

// FIXME: Should not warn
void test_17(int a) {
  int c = a;
  for (int i = 0; i < 2; i++) {
    if ((unsigned int)(a) <= 65536) {
      if (c > 65536)
        clang_analyzer_warnIfReached(); // expected-warning{{REACHABLE}}
    } else if ((unsigned int)(a) <= 1114111)
      a++;
  }
}


bool test_18(unsigned int i) {
  if (i < 270)
    switch (i) {
    case 0: case 5: case 10: case 16 ... 258: case 269:
      return 1;
    default: {
      unsigned char c1 = i;
      clang_analyzer_eval (c1 > 0 && c1 < 16); // expected-warning{{TRUE}}
    }
    }
  return 0;
}
