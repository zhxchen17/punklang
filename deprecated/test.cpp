#include <iostream>
#include <string>
#include "runtime.h"
#include "parser.h"

#define ADD_TEST(STR) \
  test = STR; \
  Parser(test.c_str(), test.c_str() + test.length()+1).next_form()->eval(LispEnv::get_global_env())->print(); \
  std::cout << std::endl;

bool test(std::string str) {
  
}

int main() {
  // startup
  builtin_syms();
  // test
  std::string test;
  // quote
  ADD_TEST("'('a)");
  // def
  ADD_TEST("(def a 1)");
  // a+b
  ADD_TEST("(+ a 0)"); // 1
  // let
  ADD_TEST("(let [b 1] (+ a b))"); // 2
  // fn
  ADD_TEST("((fn [a b] (+ a b)) 1 2)"); // 3
  // if
  ADD_TEST("(if true 5)"); // 5
  // a-b
  ADD_TEST("(- 9 a)"); // 8
  // a*b
  ADD_TEST("(* a 13)"); // 13;
  // a/b
  ADD_TEST("(/ 42 2)"); // 21
  // trial
  // ADD_TEST("(+ (* 3 (+ (* 2 4) (+ 3 5))) (+ (- 10 7) 6))"); // 57

  return 0;
}
