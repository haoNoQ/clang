// RUN: %clang_cc1 -Wno-unused-value -Wno-integer-overflow -Wno-constant-conversion -analyze -analyzer-checker=alpha.different.IntegerOverflow,alpha.security.taint,core.DivideZero,deadcode,core.builtin -analyzer-config ipa=summary,max-times-inline-large=50,max-inlinable-size=50 %s -verify
#include "Inputs/system-header-simulator.h"

#define SHRT_MAX ((short)(~0U >> 1))
#define INT_MAX ((int)(~0U >> 1))
#define INT_MIN (-INT_MAX - 1)
#define UINT_MAX (~0U)
#define LONG_MAX ((long)(~0UL >> 1))
#define LONG_MIN (-LONG_MAX - 1)
#define ULONG_MAX (~0UL)
#define LLONG_MAX ((long long)(~0ULL >> 1))
#define LLONG_MIN (-LLONG_MAX - 1)
#define ULLONG_MAX (~0ULL)

char *strchr(const char *s, int c);
int randomInt();
unsigned getUnsignedInt();

// Addition : signed
void signAddEW_1(void) {
  INT_MAX + 1; // expected-warning{{Undefined behavior: Integer Overflow. Addition of 2147483647 S32b ((int)(~0U >> 1)) with 1 S32b}}
}
void signAddEW_2(void) {
  INT_MIN + INT_MIN; // expected-warning{{Undefined behavior: Integer Underflow. Addition of -2147483648 S32b (-((int)(~0U >> 1)) - 1) with -2147483648 S32b (-((int)(~0U >> 1)) - 1)}}
}
void signAddEW_3(void) {
  LONG_MAX + 1; // expected-warning{{Undefined behavior: Integer Overflow. Addition of 9223372036854775807 S64b ((long)(~0UL >> 1)) with 1 S64b}}
}
void signAddNW_4(void) {
  SHRT_MAX + 1; // no-warning
}
void signAddNW_5(int b) {
  if (b > INT_MAX)
    b + 3; // no-warning
}
void signAddEW_6(void) {
  int a = randomInt();
  if (a == INT_MAX)
    a + 2; // expected-warning{{Undefined behavior: Integer Overflow. Addition of 2147483647 S32b (a) with 2 S32b}}
  else if (a < INT_MAX)
    a + 2; // no-warning
}

// Addition : unsigned
void unsignAddEW_1(void) {
  UINT_MAX + 1; // expected-warning{{Integer Overflow. Addition of 4294967295 U32b (~0U) with 1 U32b}}
}
void unsignAddEW_2(void) {
  1 + (unsigned)-1; // expected-warning{{Integer Overflow. Addition of 1 U32b with 4294967295 U32b ((unsigned int)-1)}}
}
void unsignAddEW_3(void) {
  ULONG_MAX + 1; // expected-warning{{Integer Overflow. Addition of 18446744073709551615 U64b (~0UL) with 1 U64b}}
}

// Subtraction : signed
void signSubEW_1(void) {
  INT_MIN - 1; // expected-warning{{Undefined behavior: Integer Underflow. Subtraction of 1 S32b from -2147483648 S32b (-((int)(~0U >> 1)) - 1)}}
}
void signSubEW_2(void) {
  -INT_MAX - 2; // expected-warning{{Undefined behavior: Integer Underflow. Subtraction of 2 S32b from -2147483647 S32b (-((int)(~0U >> 1)))}}
}
void signSubNW_3(void) {
  -INT_MAX - 1; // no-warning
}
void signSubEW_4(void) {
  LONG_MIN - 1; // expected-warning{{Undefined behavior: Integer Underflow. Subtraction of 1 S64b from -9223372036854775808 S64b (-((long)(~0UL >> 1)) - 1)}}
}

// Subtraction : unsigned
void unsignSubNW_1(void) {
  0 - (unsigned)1; // no-warning
}
void unsignSubEW_2(void) {
  int a = 0;
  a - (unsigned)1; // expected-warning{{Integer Underflow. Subtraction of 1 U32b from 0 U32b (a)}}
}

// Multiplication : signed
void signMulEW_1(void) {
  (INT_MAX / 2) * 3; // expected-warning{{Undefined behavior: Integer Overflow. Multiplication of 1073741823 S32b (((int)(~0U >> 1)) / 2) with 3 S32b}}
}
void signMulNW_2(void) {
  INT_MAX * 0; // no-warning
}
void signMulNW_3(void) {
  0 * INT_MAX; // no-warning
}
void signMulEW_4(void) {
  INT_MIN *(-1); // expected-warning{{Undefined behavior: Integer Overflow. Multiplication of -2147483648 S32b (-((int)(~0U >> 1)) - 1) with -1 S32b}}
}
void signMulEW_5(void) {
  (LONG_MAX / 2) * 3; // expected-warning{{Undefined behavior: Integer Overflow. Multiplication of 4611686018427387903 S64b (((long)(~0UL >> 1)) / 2) with 3 S64b}}
}

// Multiplication : unsigned
void unsignMulEW_1(void) {
  (UINT_MAX / 2) * 3; // expected-warning{{Integer Overflow. Multiplication of 2147483647 U32b ((~0U) / 2) with 3 U32b}}
}
void unsignMulEW_2(void) {
  (ULONG_MAX / 2) * 3; // expected-warning{{Integer Overflow. Multiplication of 9223372036854775807 U64b ((~0UL) / 2) with 3 U64b}}
}

// New
void newEW_1(void) {
  // (INT_MAX / 2) * sizeof(int). Overflowed value is used in memory allocation.
  new int[INT_MAX / 2]; // expected-warning{{Integer Overflow. Multiplication of 4 U32b with 1073741823 S32b (((int)(~0U >> 1)) / 2) while memory allocation}}
}

// Test cases for GlobalsMembersHeuristics
namespace HT_1 {
void test_1(int b) {
  if (b == INT_MIN)
    b - 1; // expected-warning{{Undefined behavior: Integer Underflow. Subtraction of 1 S32b from -2147483648}}
}
}

namespace HT_2 {
class C {
  int a;
  void foo() {
    if (a == INT_MIN)
      a - 1; // no-warning
  }
};
}

namespace HT_3 {
class C {
public:
  int a;
};
void foo() {
  C c;
  c.a = INT_MAX;
  c.a + 1; // no-warning
}
}

namespace HT_4 {
class C {
  int a;
  void foo() {
    a = INT_MAX;
    ((a - 1) + 1) + 1; // no-warning
  }
};
}

namespace HT_5 {
class C {
  int a;
  void foo() {
    a = -1;
    a + 1U; // no-warning
  }
};
}
// HQ tests
void HQ_1(unsigned int len) {
  unsigned int i, j;
  if (len == 0) {

  } else {
    for (i = 0; i < 8 && len; i++) {
      len >>= 4;
    }
    // FIXME: shouldn't warn
    for (j = i - 1; j + 1 > 0; j--) { // expected-warning{{Integer Overflow. Addition of 4294967295 U32b (j) with 1 U32b}}
      // do-smth
    }
  }
}


int HQ_2(const char* name, const char* no_proxy) {
  size_t start;
  size_t end;
  size_t no_proxy_len;
  if (no_proxy && no_proxy[0]) {
    no_proxy_len = strlen(no_proxy);
    for (start = 0; start < no_proxy_len; start = end + 1) {
      while (start < no_proxy_len && strchr(", ", no_proxy[start]) != 0) {
        ++start;
      }
      if (start == no_proxy_len)
        break;
      for (end = start; end < no_proxy_len && strchr(", ", no_proxy[end]) == 0;
           ++end) { }
      if (no_proxy[start] == '.')
        ++start;
      // FIXME: shouldn't warn
      const char *checkn = name + strlen(name) - (end - start); // expected-warning{{Integer Underflow. Subtraction of 1 U64b (start) from 0 U64b (end)}}
      return strlen(checkn);
    }
  }
  return 0;
}

// Summary Tests
namespace SummTest1 {
void sum(int a, int b) {
  a + b; // expected-warning{{Undefined behavior: Integer Overflow. Addition of 2147483647 S32b with 1 S32b}}
}

void someFunc() {
  sum(INT_MAX, 1);
}
}

namespace SummTest2 {
void sub(unsigned a, unsigned b) {
  a - b; // expected-warning{{Integer Underflow. Subtraction of conj_$5{unsigned int} : { [1073741824, 4294967295] } from conj_$2{unsigned int} : { [0, 1073741822] }}}
}

void someFunc() {
  unsigned x = getUnsignedInt(), y = getUnsignedInt();
  if (x < INT_MAX / 2 && y > INT_MAX / 2)
    sub(x, y);
}
}

namespace SummTest3 {
void sub(unsigned a, unsigned b) {
  a - b; // expected-warning{{Integer Underflow. Subtraction of reg_$1<y> : { [1073741824, 4294967295] } from reg_$0<x> : { [0, 1073741822] }}}
}

void someFunc(unsigned x, unsigned y) {
  if (x < INT_MAX / 2 && y > INT_MAX / 2)
    sub(x, y);
}

void bar() {
  unsigned d = getUnsignedInt(), f = getUnsignedInt();
  someFunc(d, f);
}
}

namespace SummTest4 {
void sub(unsigned a, unsigned b) {
  a - b; // expected-warning{{Integer Underflow. Subtraction of conj_$5{unsigned int} : { [1073741824, 4294967295] } from conj_$2{unsigned int} : { [0, 1073741822] }}}
}

void someFunc(unsigned x, unsigned y) {
  sub(x, y);
}

void bar() {
  unsigned d = getUnsignedInt(), f = getUnsignedInt();
  if (d < INT_MAX / 2 && f > INT_MAX / 2)
    someFunc(d, f);
}
}

namespace SummTest5 {
unsigned d, f;
void sub(unsigned a, unsigned b) {
  a - b;
}

void someFunc(unsigned x, unsigned y) {
  sub(x, y);
}

void bar() {
  d = getUnsignedInt(), f = getUnsignedInt();
  if (d < INT_MAX / 2 && f > INT_MAX / 2)
    someFunc(d, f);
}
}
