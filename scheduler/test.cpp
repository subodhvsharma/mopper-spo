 #include <iostream>


// class Base {

// public: 
//   Base() {} 
//   Base(int b) { a = ++b;}
//   ~Base(){}
  
//   virtual int foo() {return 0;}
//   int a;
  
// };

// class A : public virtual Base {
    
// public: 
//   A() {}
//   A(int b): Base(b) {} 
//   int foo() {return a*a;}
  
// };

// // class B : public virtual Base {
// // public:
// //   B() {}
// //   B(int b): Base(b) {} 
// //   int foo() { return (a + a);}
  
// // };


// class C : public A {
// public: 
//   C() {}
//   C(int b ): A(b) {}
//   int foo() { return (a*a + a);}

// };


// int main(){
  
//   C *c = new C(5); 
//   //  int resC = c->foo(); 
//   // int resB = c.foo(); 
//   // int resA = c.foo();
//   std::cout << "a = " << c->Base::a << std::endl;
//   // std::cout << resC << std::endl;
//   // std::cout << resB << std::endl;
//   // std::cout << resA << std::endl;
// }

class Base {

public: 
  Base() {};
  Base(int b) { a = ++b;}
  virtual int foo() {return 0;}
  int a;

};

class A : public virtual Base {

public: 
  A() {}
  A(int b): Base(b) {} 
  int foo() {return a*a;}

};

class C : public A {
public: 
  C() {}
  C(int b ): A(b) {}
  int foo() { return (a*a + a);}

};

int main(){

  C *c = new C(5); 
  std::cout << c->Base::a << std::endl;
}
