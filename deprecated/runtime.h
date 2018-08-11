#ifndef _RUNTIME_H_
#define _RUNTIME_H_

#include <string>
#include <vector>
#include <deque>
#include <unordered_map>
#include <cstdint>
#include <algorithm>
#include <iostream>

// float refers to IEEE float, therefore there is not ambiguous.
#define INT32P(x) ((x)->type_==LISP_INT32)
#define FLOATP(x) ((x)->type_==LISP_FLOAT)
#define STRINGP(x) ((x)->type_==LISP_STRING)
#define SYMBOLP(x) ((x)->type_==LISP_SYMBOL)
#define KEYWORDP(x) ((x)->type_==LISP_KEYWORD)
#define ARRAYP(x) ((x)->type_==LISP_ARRAY)
#define LISTP(x) ((x)->type_==LISP_LIST)
#define BOOLP(x) ((x)->type_==LISP_BOOL)
#define TRUEP(x) (((LispBool*)(x))->value_ == true)
#define FALSEP(x) (((LispBool*)(x))->value_ == false)
#define NILP(x) ((x)->type_==LISP_NIL)

#define INT32(x) ((LispInt32*)(x))
#define FLOAT(x) ((LispFloat*)(x))
#define LIST(x) ((LispList*)(x))
#define STRING(x) ((LispString*)(x))
#define SYMBOL(x) ((LispSymbol*)(x))
#define KEYWORD(x) ((LispKeyword*)(x))
#define ARRAY(x) ((LispArray*)(x))
#define BOOL(x) ((LispBool*)(x))

#define DEBUG_LOG(x) std::cout << (x) << std::endl

template<typename K, typename V>
using hash_table = std::unordered_map<K, V>;

enum LispType {
  LISP_NIL,
  LISP_FN,
  LISP_SPECIAL_FORM,
  LISP_LIST,
  LISP_BOOL,
  LISP_INT32,
  LISP_FLOAT,
  LISP_STRING,
  LISP_SYMBOL,
  LISP_KEYWORD,
  LISP_ARRAY,
  LISP_DICT,
  LISP_ANY
  // What's next?
};

struct LispEnv;

struct LispObject {
  LispType type_;
  LispObject(LispType type) : type_(type) {}
  LispObject() : type_(LISP_ANY) {}
  virtual void print() {}
  virtual LispObject* eval(LispEnv* env) { return this; }
};

// TODO: should be put in Cons.h
// (fn [ x y ] ())
class List {
  // TODO: can be shared pointer
  std::deque<LispObject*> cons_;
public:
  List(const List&) = default;
  List() {}
  void push(LispObject* obj) { cons_.push_back(obj); }
  LispObject* first() const { return cons_.front(); }
  List rest() const;
  inline int size() const { return cons_.size(); }
  inline LispObject* operator[](int i) const { return cons_[i]; }
};

struct LispList : public LispObject {
  List cons_;
  LispList() : LispObject(LISP_LIST) {}
  void print();
  LispObject* eval(LispEnv*);
};

struct LispBool : public LispObject {
  bool value_;
  LispBool(bool v) : LispObject(LISP_BOOL), value_(v) {}
  void print() { if (value_) std::cout << "true"; else std::cout << "false"; }
};

struct LispInt32 : public LispObject {
  int32_t value_;
  LispInt32(int32_t v) : LispObject(LISP_INT32), value_(v) {}
  void print() { std::cout << value_; }
};

struct LispFloat : public LispObject {
  float value_;
  LispFloat(float v) : LispObject(LISP_FLOAT), value_(v) {}
  void print() { std::cout << value_ << 'f'; }
};

struct LispKeyword : public LispObject {
  const std::string key_;
  LispKeyword(std::string key) : LispObject(LISP_KEYWORD), key_(key) {}
  LispKeyword(const char* key) : LispObject(LISP_KEYWORD), key_(key) {}
  bool operator==(const LispKeyword& other) const { return key_ == other.key_; }
  void print() { std::cout << '\"' << key_ << '\"' ; }
};

struct LispString : public LispObject {
  std::string data_;
  LispString(std::string data) : LispObject(LISP_STRING), data_(data) {}
  LispString(const char* data) : LispObject(LISP_STRING), data_(data) {}
  bool operator==(const LispString& other) const { return data_ == other.data_; }
  void print() { std::cout << '\"' << data_ << '\"' ; }
};

struct LispSymbol : public LispObject {
  const std::string name_;
  LispSymbol(std::string str) : LispObject(LISP_SYMBOL), name_(str) {}
  LispSymbol(const char* str) : LispObject(LISP_SYMBOL), name_(str) {}
  bool operator==(const LispSymbol& other) const { return name_ == other.name_; }
  void print() { std::cout << name_ ; }
  LispObject* eval(LispEnv* env);
};

struct LispArray : public LispObject {
  std::vector<LispObject*> data_;
  LispArray() : LispObject(LISP_ARRAY) {}
};

struct LispNil : public LispObject {
  LispNil() : LispObject(LISP_NIL) {}
  void print() { std::cout << "nil"; }
};

namespace std {
  template <>
  struct hash<LispString> {
    std::size_t operator()(const LispString& str) const { return hash<string>()(str.data_); }
  };

  template <>
  struct hash<LispSymbol> {
    std::size_t operator()(const LispSymbol& sym) const { return hash<string>()(sym.name_); }
  };
}

struct LispEnv {
  static LispEnv global;
  LispEnv* parent_;
  hash_table<LispSymbol, LispObject*> objs_;
  LispObject* resolve(const LispSymbol& sym);
  void bind(const LispSymbol& sym, LispObject* obj) { objs_.emplace(sym, obj); }
  LispEnv() : parent_(nullptr) {}
  LispEnv(LispEnv* env) : parent_(env) {}
  static LispEnv* get_global_env() { return &global; }
};

struct LispFn : public LispObject {
  virtual LispObject* call(const List& args) = 0;
  LispFn() : LispObject(LISP_FN) {}
};

struct LispClosure : public LispFn {
  std::vector<LispObject*> forms_;
  std::vector<LispSymbol*> params_;
  LispEnv* env_;
  LispObject* call(const List& args);
};

struct LispBuiltin : public LispFn {
  LispObject* (*cfn_)(const List&);
  LispBuiltin (LispObject* (*cfn)(const List&)) : cfn_(cfn) {}
  LispObject* call(const List& args) { return cfn_(args); }
};

struct LispSpecialForm : public LispObject {
  LispObject* (*cfn_)(LispEnv*, const List&);
  LispSpecialForm (LispObject* (*cfn)(LispEnv*, const List&)) : LispObject(LISP_SPECIAL_FORM), cfn_(cfn) {}
  LispObject* call(LispEnv* env, const List& args) { return cfn_(env, args); }
};

LispObject* builtin_add(const List& args);

void builtin_syms();

#endif
