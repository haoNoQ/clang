// RUN: %clang -c -Xclang -analyze %s -std=c++11 -Xclang -analyzer-checker=alpha.security.taint,alpha.undefbehavior.BasicStringBound,debug.ExprInspection -Xclang -analyzer-config -Xclang ipa=summary,max-times-inline-large=50,max-inlinable-size=50 -Xclang -verify

#include <string>

void clang_analyzer_warnIfReached();
void clang_analyzer_eval(bool);

extern void stringRefFunc(std::string &s);
extern void stringValueFunc(std::string s);
extern void stringConstRefFunc(const std::string &s);

char *ptr;

void test() {
  std::basic_string<char> s = "aaa";
  s[0];  // no-warning
  s[3];  // no-warning
  s[2];  // no-warning
  s[-1]; // expected-warning{{}}
}

void test2() {
  std::basic_string<char> s = "aaa";
  s[0]; // no-warning
  s[3]; // no-warning
  s[2]; // no-warning
  s[4]; // expected-warning{{}}
}

void test3() {
  std::basic_string<char> s("aaa");
  s[0]; // no-warning
  s[3]; // no-warning
  s[2]; // no-warning
  s[4]; // expected-warning{{}}
}

void test4() {
  std::string s;
  s[0]; // no-warning
  s[2]; // expected-warning{{}}
}

void test5() {
  std::string s;
  s.at(0);  // no-warning
  s.at(-1); // expected-warning{{}}
}

void test6() {
  std::basic_string<char> s = "aaa";
  s.resize(2);
  s[0]; // no-warning
  s[2]; // no-warning
  s[3]; // expected-warning{{}}
}

void test7() {
  std::basic_string<char> s1 = "aaa";
  std::basic_string<char> s = s1;
  s[0]; // no-warning
  s[3]; // no-warning
  s[2]; // no-warning
  s[4]; // expected-warning{{}}
}

void test8(char *c, size_t pos) {
  std::basic_string<char> s = c;
  s.at(0); // no-warning
  s[3];    // no-warning
  s[2];    // no-warning
  s[4];    // no-warning
  s[pos];  // no-warning
  s[-10];  // expected-warning{{}}
}

void test9(const std::string &s1, int pos) {
  std::basic_string<char> s;
  s = s1;
  s[0];   // no-warning
  s[3];   // no-warning
  s[2];   // no-warning
  s[4];   // no-warning
  s[pos]; // no-warning
  s[-1];  // expected-warning{{}}
}

void test10() {
  std::string s("aa");
  s += "bb";
  s[3]; // no-warning
  s[5]; // expected-warning{{}}
}

void test11() {
  std::string s("aa");
  s.append("ff");
  s[3]; // no-warning
  s[5]; // expected-warning{{}}
}

void test12(const std::string &st, int pos) {
  std::string s("aa");
  s.append("ff");
  s[3]; // no-warning
  s.append(st);
  s[3];   // no-warning
  s[5];   // no-warning
  s[100]; // no-warning
  s[-1];  // expected-warning{{}}
}

void test13() {
  int a[] = {1, 2, 3, 0};
  std::basic_string<int> s(a);
  s[0]; // no-warning
  s[3]; // no-warning
  s[2]; // no-warning
  s[4]; // expected-warning{{}}
}

void test14() {
  int a[] = {1, 2, 3, 0};
  std::basic_string<int> s(a);
  s[-1]; // expected-warning{{}}
}

void test15() {
  std::basic_string<int> s(3, 4);
  s[0]; // no-warning
  s[3]; // no-warning
  s[2]; // no-warning
  s[4]; // expected-warning{{}}
}

template <class T>
void template_test() {
  std::basic_string<T> s;
  s[0]; // no-warning
  s[4]; // expected-warning{{}}
}

void test16() {
  template_test<short>();
}

void test17() {
  std::string s("aa");
  s[0]; // no-warning
  s[1]; // no-warning
  s.clear();
  s[0]; // no-warning
  s[1]; // expected-warning{{}}
}

void test18() {
  std::string s1 = "aa";
  std::string s2 = "bb";
  std::string s3 = s1 + s2;
  std::string s4 = "dd" + s3;
  std::string s5 = s4 + 'f';
  s5[3]; // no-warning
  s5[7]; // no-warning
  s5[8]; // expected-warning{{}}
}

void test19() {
  std::string s1 = "aa";
  std::string s2 = s1 + "cc";
  std::string s3 = 'e' + s2;
  s3[3]; // no-warning
  s3[5]; // no-warning
  s3[7]; // expected-warning{{}}
}

void test20(const std::string &s) {
  s[0];   // no-warning
  s[3];   // no-warning
  s[5];   // no-warning
  s[100]; // no-warning
  s[-1];  // expected-warning{{}}
}

void test21() {
  const char *a[] = {"aa", "bb", "cc"};
  std::basic_string<const char *> s(a, 3);
  s[0]; // no-warning
  s[3]; // no-warning
  s += "dd";
  s[4]; // no-warning
  s[5]; // expected-warning{{}}
}

void test22() {
  std::string s = "aa";
  s.push_back('b');
  s[0]; // no-warning
  s[2]; // no-warning
  s[3]; // no-warning
  s[4]; // expected-warning{{}}
}

void test23() {
  std::string s;
  s.assign("aa");
  s[0]; // no-warning
  s[1]; // no-warning
  s[2]; // no-warning
  s[3]; // expected-warning{{}}
}

void test24() {
  std::string s;
  std::string s1 = "aaaa";
  s.assign(s1, 1, 2);
  s[0]; // no-warning
  s[1]; // no-warning
  s[2]; // no-warning
  s[3]; // expected-warning{{}}
}

void test25() {
  std::string s1 = "aaaa";
  std::string s(s1, 1, 2);
  s[0]; // no-warning
  s[1]; // no-warning
  s[2]; // no-warning
  s[3]; // expected-warning{{}}
}

void test26() {
  std::string s;
  std::string s1 = "aa";
  s.assign(s1);
  s[0]; // no-warning
  s[1]; // no-warning
  s[2]; // no-warning
  s[3]; // expected-warning{{}}
}

void test27() {
  std::string s = "aa";
  if (s.empty()) {
    clang_analyzer_warnIfReached(); // no-warning
    return;
  }
  clang_analyzer_warnIfReached(); // expected-warning{{}}
}

void test28() {
  std::string s;
  if (!s.empty()) {
    clang_analyzer_warnIfReached(); // no-warning
    return;
  }
  clang_analyzer_warnIfReached(); // expected-warning{{}}
}

void test29(const std::string &s) {
  if (s.empty())
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  else
    clang_analyzer_warnIfReached(); // expected-warning{{}}
}

void test30() {
  std::string s;
  stringRefFunc(s);
  s[s.size() - 1]; // no-warning
}

void test31() {
  std::string s;
  stringConstRefFunc(s);
  s[s.size() - 1]; // expected-warning{{}}
}

void test32() {
  std::string s;
  stringValueFunc(s);
  s[s.size() - 1]; // expected-warning{{}}
}

void test33(const std::string &sp) {
  std::string s = "aa";
  s += sp;
  if (s.length() < 2)
    clang_analyzer_warnIfReached(); // no-warning
}

void test34(const std::string &sp) {
  std::string s = sp;
  s.append("aa");
  if (s.length() < 2)
    clang_analyzer_warnIfReached(); // no-warning
}

std::string test35(const std::string &sp1, const std::string &sp2) {
  return "v" + sp1 + sp2; // no-warning
}

void test36() {
  std::string s = "abcd";
  std::string s2(s, 2, 1); // s2 == "c"
  s2[0];              // no-warning
  s2[1];              // no-warning
  s2[2];              // expected-warning{{}}
}

void test37() {
  std::string s = "abcd";
  std::string s2(s, 2, std::string::npos); // s2 == "cd"
  s2[0];                         // no-warning
  s2[1];                         // no-warning
  s2[2];                         // no-warning
  s2[3];                         // expected-warning{{}}
}

void test38() {
  std::string s = "abcd";
  s.append(s, 2, std::string::npos); // s2 == "abcdcd"
  s[0];                         // no-warning
  s[5];                         // no-warning
  s[6];                         // no-warning
  s[7];                         // expected-warning{{}}
}

int test39(const std::string &sp) {
  size_t pos = sp.find('a');
  if (pos == std::string::npos)
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  else
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  return pos;
}

int test40() {
  std::string s = "aaa";
  size_t pos = s.find('a');
  if (pos == std::string::npos)
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  else if (pos > 3)
    clang_analyzer_warnIfReached(); // no-warning
  return pos;
}

void test41(const std::string &s) {
  int pos = s.find('a');
  if (pos != std::string::npos)
    s[pos]; // no-warning
  else
    s[pos]; // expected-warning{{}}
}

void test42(const std::string &s) {
  size_t pos = -1;
  if (pos != std::string::npos)
    s[pos]; // no-warning
}

void test43(const std::string &s) {
  size_t start = 2;
  size_t pos = s.find_first_of('a', start);
  if (pos == std::string::npos)
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  else if (pos >= start)
    clang_analyzer_warnIfReached(); // expected-warning{{}}
  else
    clang_analyzer_warnIfReached(); // no-warning
}

void test44(const std::string &s) {
  int size = 2;
  if (s.size() == size) {
    s[1]; // no-warning
    s[2]; // no-warning
    s[3]; // expected-warning{{}}
  }
}

void test45(const std::string &s) {
  int pos = s.find('a');
  if (pos != std::string::npos)
    if (s.length() < 1)
      clang_analyzer_warnIfReached(); // no-warning
}

void test46(const std::string &s) {
  int pos = s.find('a', 2);
  if (pos != std::string::npos)
    if (s.length() < 3)
      clang_analyzer_warnIfReached(); // no-warning
}

void test47(const std::string &s) {
  if (s.empty()) {
    if (s.size() > 0)
      clang_analyzer_warnIfReached(); // no-warning
    else
      clang_analyzer_warnIfReached(); // expected-warning{{}}
  } else {
    if (s.size() > 0)
      clang_analyzer_warnIfReached(); // expected-warning{{}}
    else
      clang_analyzer_warnIfReached(); // no-warning
  }
}

void test_HQ_find(const std::string &s) {
  std::string Str = s;
  if (Str.empty()) {
    return;
  } else {
    size_t mi = 0;
    size_t me = Str.length();
    while (mi < me) {
      size_t p = Str.find('\n', mi);
      if (p > mi && p != std::string::npos) {
        while (p < me && isspace(Str[p])) // no-warning
          ++p;
        mi = p;
      } else {
        p = mi;
        while (p < me && isspace(Str[p])) // no-warning
          ++p;
          mi = me;
      }
    }
  }
}

std::string test_HQ_insert(const std::string &s) {
  std::string Str(s);
  for (size_t i = 0; i != Str.length(); ++i) {
    switch (Str[i]) {
    case '\n':
      Str.insert(Str.begin()+i, '\\'); // no-warning
      i++;
      break;
    case '\t':
      Str.insert(Str.begin()+i, ' '); // no-warning
      i++;
      break;
    }
  }
  return Str;
}

void testNpos(const std::string &s) {
  size_t pos = s.find('a');
  if (pos != s.npos)
    s[pos];   // no-warning
}

void testNposFirstOf(std::string ret) {
  size_t space_or_tick;
  if (ret.size() < 2)
    return;
  while (ret != "") {
    space_or_tick = ret.find_first_of("` ");
    if (space_or_tick != ret.npos && ret[space_or_tick] == ' ' && // no-warning
        ret.substr(0, space_or_tick).find("operator") == std::string::npos) {
      ret = ret.substr(space_or_tick + 1);
    } else if (space_or_tick != ret.npos && space_or_tick + 1 == ret.size()) {
      ret = ret.substr(0, space_or_tick);
    } else {
      break;
    }
  }
}

typedef std::string StringType;
void testNposTypedef(const std::string &s) {
  size_t pos = s.find('a');
  if (pos != StringType::npos)
    s[pos];   // no-warning
}

void PrintBodyText(const std::string &text) {
  size_t safe = 0;
  std::string pout_;
  for (;;) {
    size_t unsafe = text.find_first_of("<>&", safe);
    if (unsafe == std::string::npos)
      unsafe = text.length();
    pout_ += text.substr(safe, unsafe - safe);
    if (unsafe == text.length())
      return;
    switch (text[unsafe]) {
    case '<': pout_ += "&lt;"; break;
    case '>': pout_ += "&gt;"; break;
    case '&': pout_ += "&amp;"; break;
    }
    safe = unsafe + 1;
    if (safe == text.length())
      return;
  }
}

void testArrayExtent() {
  char a[10] = "aaa";
  std::string s(a);
  s[0];  // no-warning
  s[3];  // no-warning
  s[2];  // no-warning
  s[4]; // expected-warning{{}}
}

void testStringAppendBuffer() {
  std::string s;
  s.append("aaaaaaaaa", 3);
  s[0];  // no-warning
  s[3];  // no-warning
  s[2];  // no-warning
  s[4]; // expected-warning{{}}
}

void testCallChain() {
  std::string s;
  s.assign("a").append("aa");
  s[0];  // no-warning
  s[3];  // no-warning
  s[2];  // no-warning
  s[4]; // expected-warning{{}}
}

int scanf(const char *format, ...);

void testTaint() {
  std::string s = "aaaa";
  unsigned index;
  scanf("%u", &index);
  s[index]; // expected-warning{{}}
}

void testCheckedTaint() {
  std::string s = "aaaa";
  unsigned index;
  scanf("%u", &index);
  if (index < 4)
    s[index]; // no-warning
}

void testUndefinedIndex() {
  std::string s;
  size_t index;
  s[index];  // do not crash
}

void testInlineInvalidation(const std::string &arg) {
  std::string s(arg.size()+1, ' ');
  s.erase(s.find_last_not_of(' ')+1);

  for (unsigned i = 0, e = s.size(); i != e; ++i)
    if (i >= arg.size())
      s[i];
}

void testUnicodeString() {
  std::u16string UStr(u"aa");
  clang_analyzer_eval(UStr.size() == 2);  // expected-warning{{TRUE}}
  UStr[0]; // no-warning
  UStr[3]; // expected-warning{{}}
}

void testUnicodeStringPlus() {
  std::u16string UStr(u"aa");
  UStr += u"bb";
  clang_analyzer_eval(UStr.size() == 4);  // expected-warning{{TRUE}}
  UStr[3]; // no-warning
  UStr[5]; // expected-warning{{}}
}


void summaryStringChange(std::string &arg) {
  arg = "foo";
}

void testSummaryStringChange() {
  std::string s = "1";
  summaryStringChange(s);
  s[0];  // no-warning
  s[1];  // no-warning
  s[2];  // no-warning
  s[3];  // no-warning
  s[4];  // expected-warning{{}}
}

void summaryStringAppend(std::string &arg) {
  arg += "oo";
}

void testSummaryStringAppend() {
  std::string s = "f";
  summaryStringAppend(s);
  s[0];  // no-warning
  s[1];  // no-warning
  s[2];  // no-warning
  s[3];  // no-warning
  s[4];  // expected-warning{{}}
}

std::string sumStrings(const std::string &lhs, const std::string &rhs) {
  return lhs + rhs;
}

void testSummaryPlus() {
  std::string s1 = "f";
  std::string s2 = "oo";
  std::string s = sumStrings(s1, s2);
  s[0];  // no-warning
  s[1];  // no-warning
  s[2];  // no-warning
  s[3];  // no-warning
  s[4];  // expected-warning{{}}
}

void testPlus() {
  std::string s1 = "aa";
  std::string s2 = "bb";
  std::string s3 = s1 + s2;
  s3[3]; // no-warning
  s3[4]; // no-warning
  s3[5]; // expected-warning{{}}
}

void pushBack(std::string &arg) {
  arg.push_back('a');
  arg.push_back('r');
}

void testSummaryPushBack() {
  std::string s = "b";
  pushBack(s);
  s[3]; // no-warning
  s[4]; // expected-warning{{}}
}

void append(std::string &arg) {
  arg.append("ar");
}

void testSummaryAppend() {
  std::string s = "b";
  append(s);
  s[3]; // no-warning
  s[4]; // expected-warning{{}}
}

void accessLocalIndex(std::string &arg) {
  arg[0];
  arg[2];
  arg[3];
  arg[4];
}

void testAccessLocalIndex() {
  std::string s = "foo"; // no-warning
  accessLocalIndex(s);   // expected-warning{{}}
}

void accessLocalString(size_t index) {
  std::string s = "foo";
  s[index];
}

void testAccessLocalString() {
  accessLocalString(0); // no-warning
  accessLocalString(2); // no-warning
  accessLocalString(3); // no-warning
  accessLocalString(4); // expected-warning{{}}
}
