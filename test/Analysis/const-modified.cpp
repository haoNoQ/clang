// RUN: %clang_cc1 -analyze -analyzer-checker=alpha.undefbehavior.ConstModified -analyzer-store region -analyzer-config ipa=summary -verify %s

extern void *malloc(unsigned);

class X {
public :
  mutable int i;
  int j;
};
class Y {
public :
  X x;
  Y();
};

void test() {
  const int *ciq = (int *)malloc(sizeof(int));
  int *iq = const_cast<int *>(ciq);
  *iq = 1; // no-warning
}

void test1() {
  const Y y;
  Y* p = const_cast<Y*>(&y);
  p->x.i = 1; // no-warning
  p->x.j = 1; // expected-warning {{Writing to a memory that originally had constant qualifier ('y.x.j')}}
}

void test2() {
  Y z;
  const Y *cz = &z;
  Y* q = const_cast<Y*>(cz);

  q->x.j = 2; // no-warning
  Y *qx = &z;
  qx->x.j = 5; // no-warning
}

void test3(const int *ciq) {
  int *iq = (int *)ciq;
  *iq = 1; // expected-warning {{Writing to a memory that originally had constant qualifier ('*iq')}}
}

void test4(const int *ciq) {
  ciq = 0; // no-warning
}

void testArray(const int *ciq) {
  int *iq = (int *)ciq;
  iq[2] = 0; // expected-warning{{}}
}

// Guess where this sample is taken from.
int OPENSSL_memcmp(const unsigned char *v1,const unsigned char *v2,int n)
{
  const unsigned char *c1=v1,*c2=v2;
  int ret=0;

  while(n && (ret=*c1-*c2)==0) n--,c1++,c2++; // no-warning

  return ret;
}


void derefParam(int *p) {
  *p = 1; // expected-warning{{Writing to a memory that originally had constant qualifier ('(int *)ptr')}}
}

void testSummaryDerefConstParam(const int *ptr) {
  derefParam((int *)ptr);
}

void derefParamSecondFloor(int *p) {
  *p = 1; // expected-warning{{Writing to a memory that originally had constant qualifier ('(int *)ptr')}}
}

void derefConstParamSecondFloor(int *ptr) {
  derefParamSecondFloor(ptr);
}

void testSummaryDerefConstParamSecondFloor(const int *ptr) {
  derefConstParamSecondFloor((int *)ptr);
}

void testSummaryDerefNonConstParam(int *ptr) {
  derefParam(ptr); // no-warning
}

void testSummaryDerefLocalNonConst() {
  const int *ptr = new int;
  derefParam((int *)ptr); // no-warning
}

void summaryPtrArg(const int *i) {
  i = 0; // no-warning
}

const int *getConstPtr();

void testSummaryPtrArg() {
  const int *i = getConstPtr();
  summaryPtrArg(i);
}

struct Test {
  int i;
  void setI(int n) { i = n; } // expected-warning{{Writing to a memory that originally had constant qualifier (field 'i')}}
  void get() const { ((Test *)this)->setI(0); }
};

void derefMember(Test *t) {
  t->i = 0; // expected-warning{{}}
}

void testDerefMember(const Test *t) {
  Test *nct = const_cast<Test *>(t);
  derefMember(nct);
}

const int cnstPtr = 0;
int ncnstPtr = 0;

int *returnConstCond(int a) {
  if (a)
    return (int *)&cnstPtr;
  return &ncnstPtr;
}

void testFullTrace() {
  int *ptr = returnConstCond(0);
  *ptr = 1;
  ptr = returnConstCond(1);
  *ptr = 1; // expected-warning{{}}
}

void derefCond(int *p, int a) {
  if (a)
    *p = 1; // expected-warning{{}}
}

void testWriteCond(const int *p, int a) {
  int *ncp = const_cast<int *>(p);
  derefCond(ncp, a);
}

void testReference(const int &n) {
  int &ncn = const_cast<int &>(n);
  ncn = 1; // expected-warning{{}}
}

void testReferenceStruct(const X &x) {
  const_cast<X &>(x).j = 1; // expected-warning{{}}
}
