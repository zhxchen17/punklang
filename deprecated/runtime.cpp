#include <iostream>
#include <vector>
#include <string>
#include <cassert>
#include "runtime.h"

void LispList::print() {
  std::cout << "( ";
  for (int i = 0; i != cons_.size(); i++) {
    cons_[i]->print();
    std::cout << ' ';
  };
  std::cout << ')';
}

LispObject* LispList::eval(LispEnv* env) {
  assert(cons_.size());
  LispObject* head = cons_.first()->eval(env);
  head->print();
  // DEBUG_LOG(head->type_);
  if (head->type_ == LISP_FN) {
    LispFn* fn = (LispFn*)(head);
    List args;
    for (int i=1; i<cons_.size(); i++)
      args.push(cons_[i]->eval(env));
    return fn->call(args);
  } else if (head->type_ == LISP_SPECIAL_FORM) {
    LispSpecialForm* form = (LispSpecialForm*)(head);
    List args;
    for (int i=1; i<cons_.size(); i++)
      args.push(cons_[i]);
    return form->call(env, args);
  } else {
    assert(false);
  }
}

LispObject* LispEnv::resolve(const LispSymbol& sym) {
  // std::cout << "Resolving symbol: " << sym.name_ << std::endl;
  auto obj_iter = objs_.find(sym);
  LispObject* res = NULL;
  if (obj_iter != objs_.end())
    res = obj_iter->second;
  else {
    if (parent_) res = parent_->resolve(sym);
  }
  // std::cout << res << std::endl;
  return res;
}

List List::rest() const {
  List res(*this);
  res.cons_.pop_front();
  return res;
}

LispObject* LispSymbol::eval(LispEnv* env) {
  return env->resolve(*this);
}

LispObject* LispClosure::call(const List& args) {
  LispEnv* tmp = new LispEnv(env_);
  assert(args.size() == params_.size());
  for (int i=0; i<params_.size(); i++) {
    tmp->bind(*(params_[i]), args[i]);
  }
  LispObject* res = nullptr;
  for (int i=0; i<forms_.size(); i++) {
    res = forms_[i]->eval(tmp);
  }
  assert(res);
  return res;
}

// BUILTINs
LispEnv LispEnv::global;

#define ARITH_REDUCE(OP, ARGS, FLOATING) \
  bool floating = FLOATING; \
  int32_t res_i = 0, tmp_i = 0; \
  float res_f = 0, tmp_f = 0; \
  if (FLOATP(ARGS[0])) { \
    floating = true; \
    res_f = FLOAT(ARGS[0])->value_; \
  } else if (INT32P(ARGS[0])) { \
    if (floating) \
      res_f = (float)(INT32(ARGS[0])->value_); \
    else \
      res_i = INT32(ARGS[0])->value_; \
  } \
  else assert(false); \
  for (int i=1; i<ARGS.size(); i++) { \
    if (FLOATP(ARGS[i])) { \
      if (!floating) { res_f = res_i; floating = true; } \
      tmp_f = FLOAT(ARGS[i])->value_; \
      res_f = res_f OP tmp_f; \
    } else if (INT32P(ARGS[i])) { \
      tmp_i = INT32(ARGS[i])->value_; \
      if (floating) res_f = res_f OP tmp_i; \
      else res_i = res_i OP tmp_i; \
    } else assert(false); \
  } \
  if (floating) return new LispFloat(res_f); \
  else return new LispInt32(res_i);

LispObject* builtin_add(const List& args) {
  ARITH_REDUCE(+, args, false);
}

LispObject* builtin_minus(const List& args) {
  if (args.size() == 0) {
    assert(false);
  } else if (args.size() == 1) {
    if (FLOATP(args[0]))
      return new LispFloat(-FLOAT(args[0])->value_);
    else if (INT32(args[0]))
      return new LispInt32(-INT32(args[0])->value_);
    else
      assert(false);
  } else {
    ARITH_REDUCE(-, args, false);
  }
}

LispObject* builtin_multiply(const List& args) {
  ARITH_REDUCE(*, args, false);
}

LispObject* builtin_divide(const List& args) {
  ARITH_REDUCE(/, args, true);
}

LispObject* builtin_eq(const List& args) {
  assert(args.size()>=2);
  for (int i=0; i<args.size()-1; i++) {
    assert(args[i]->type_ == args[i+1]->type_);
    bool res;
    switch (args[i]->type_) {
    case LISP_INT32:
      res = INT32(args[i])->value_ == INT32(args[i+1])->value_;
      break;
    case LISP_BOOL:
      res = BOOL(args[i])->value_ == BOOL(args[i+1])->value_;
      break;
    case LISP_FLOAT:
      res = FLOAT(args[i])->value_ == FLOAT(args[i+1])->value_;
      break;
    case LISP_NIL:
      res = true;
      break;
    case LISP_STRING:
      res = STRING(args[i])->data_ == STRING(args[i+1])->data_;
      break;
    }
    if (!res) return new LispBool(false);
  }
  return new LispBool(true);
}

LispObject* special_form_def(LispEnv* env, const List& args) {
  assert(args.size() == 2);
  assert(SYMBOLP(args[0]));
  LispSymbol* sym = SYMBOL(args[0]);
  LispEnv::get_global_env()->bind(*sym, args[1]->eval(env));
  return new LispNil;
}

LispObject* special_form_let(LispEnv* env, const List& args) {
  assert(args.size() >= 2);
  LispEnv* tmp = new LispEnv(env);
  assert(ARRAYP(args[0]));
  LispArray* binds = ARRAY(args[0]);
  for (int i=0; i<binds->data_.size(); i+=2) {
    assert(SYMBOLP(binds->data_[i]));
    LispSymbol* sym = SYMBOL(binds->data_[i]);
    tmp->bind(*sym, binds->data_[i+1]->eval(tmp));
  }
  LispObject* res = nullptr;
  for (int i=1; i<args.size(); i++)
    res = args[i]->eval(tmp);
  return res;
}

LispObject* special_form_fn(LispEnv* env, const List& args) {
  assert(args.size() >= 2);
  assert(ARRAYP(args[0]));
  LispArray* params = ARRAY(args[0]);
  LispClosure* fn = new LispClosure;
  for (int i=0; i<params->data_.size(); i++) {
    assert(SYMBOLP(params->data_[i]));
    fn->params_.push_back((LispSymbol*)params->data_[i]);
  }
  for (int i=1; i<args.size(); i++) {
    fn->forms_.push_back(args[i]);
  }
  fn->env_ = env;
  return fn;
}

LispObject* special_form_if(LispEnv* env, const List& args) {
  assert(args.size() >= 2);
  LispObject* pred = args[0]->eval(env);
  assert(BOOLP(pred));
  if (TRUEP(pred)) {
    return args[1]->eval(env);
  } else if (FALSEP(pred)) {
    if (args.size() == 2)
      return new LispNil;
    else if (args.size() == 3)
      return args[2]->eval(env);
    else
      assert(false);
  } else
    assert(false);
}

LispObject* special_form_quote(LispEnv* env, const List& args) {
  assert(args.size() == 1);
  return args[0];
}

LispObject* special_form_defmacro(LispEnv* env, const List& args) {
  
}

#define BIND_SPECIAL_FORM(NAME, FUNC) global->bind(LispSymbol(NAME), new LispSpecialForm(FUNC))
#define BIND_BUILTIN(NAME, FUNC) global->bind(LispSymbol(NAME), new LispBuiltin(FUNC))

void builtin_syms() {
  LispEnv* global = LispEnv::get_global_env();
  // builtin
  BIND_BUILTIN("+", builtin_add);
  BIND_BUILTIN("=", builtin_eq);
  BIND_BUILTIN("-", builtin_minus);
  BIND_BUILTIN("*", builtin_multiply);
  BIND_BUILTIN("/", builtin_divide);

  // special form
  BIND_SPECIAL_FORM("def", special_form_def);
  BIND_SPECIAL_FORM("let", special_form_let);
  BIND_SPECIAL_FORM("fn", special_form_fn);
  BIND_SPECIAL_FORM("if", special_form_if);
  BIND_SPECIAL_FORM("quote", special_form_quote);
  BIND_SPECIAL_FORM("defmacro", special_form_defmacro);
}

