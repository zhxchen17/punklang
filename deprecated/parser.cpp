#include <vector>
#include <string>
#include <cstring>
#include <cassert>
#include <cstdint>
#include <algorithm>
#include <stack>
#include "utf8.h"
#include "parser.h"
#include "runtime.h"

const unichar LEFT_BRACKET = (unichar)'(';
const unichar RIGHT_BRACKET = (unichar)')';
const unichar DOUBLE_QUOTE = (unichar)'\"';
const unichar QUOTE = (unichar)'\'';
const unichar LEFT_ARRAY = (unichar)'[';
const unichar RIGHT_ARRAY = (unichar)']';
const unichar LEFT_BLOCK = (unichar)'{';
const unichar RIGHT_BLOCK = (unichar)'}';
const unichar SPACE = (unichar)' ';
const unichar COLON = (unichar)':';
const unichar EMPTY = (unichar)'\0';
const unichar DOT = (unichar)'.';
const unichar AT = (unichar)'@';
const unichar HASH = (unichar)'#';
const unichar EVAL = (unichar)'$';
const unichar COMMENT = (unichar)';';
const unichar TILDE = (unichar)'~';
const unichar MINUS = (unichar)'-';

unichar Parser::peek_next() { return utf8::peek_next(cursor_, data_end_); }
unichar Parser::next() { return utf8::next(cursor_, data_end_); }

Parser::Parser(const char* s, const char* e) : data_start_(s), data_end_(e), cursor_(s) {
  paren_match[RIGHT_BRACKET] = LEFT_BRACKET;
  paren_match[RIGHT_ARRAY] = LEFT_ARRAY;
  paren_match[RIGHT_BLOCK] = LEFT_BLOCK;
  memset(quote_follow, true, MAX_CHAR);
  quote_follow[SPACE] = quote_follow[RIGHT_BLOCK]
    = quote_follow[RIGHT_ARRAY] = quote_follow[RIGHT_BRACKET] = false;
  punctuation[SPACE] = punctuation[LEFT_BLOCK]
    = punctuation[RIGHT_BLOCK] = punctuation[LEFT_BRACKET]
    = punctuation[RIGHT_BRACKET] = punctuation[LEFT_ARRAY]
    = punctuation[RIGHT_ARRAY] = punctuation[QUOTE]
    = punctuation[DOUBLE_QUOTE] = punctuation[COLON]
    = punctuation[DOT] = punctuation[AT]
    = punctuation[HASH] = punctuation[EVAL]
    = punctuation[COMMENT] = punctuation[TILDE]
    = punctuation[EMPTY] = true;
}

LispObject* Parser::next_form() {
  // if (in_error) return;
  unichar current = EMPTY;
  unichar peek = EMPTY;
  const char* str_start = nullptr;
  LispObject* obj = nullptr;
  while ((current = next()) == SPACE);
  paren_closing_ = false;

  // create current
  switch (current) {
  case LEFT_BRACKET:
    obj = new LispList;
    break;
  case LEFT_ARRAY:
    obj = new LispArray;
    break;
  case LEFT_BLOCK:
    obj = new LispList;
    ((LispList*)obj)->cons_.push(new LispSymbol("do"));
    break;
  default:
    break;
  }
  //std::cout << "Current char: " << (char)current << std::endl;
  //std::cout << "Stack size: " << paren_stack.size() << std::endl;
  // find recursive forms
  switch (current) {
  case LEFT_BLOCK:
  case LEFT_ARRAY:
  case LEFT_BRACKET:
    paren_stack.push(current);
    list_stack.push(obj);
    do next_form(); while (!paren_closing_);
    paren_stack.pop();
    list_stack.pop();
    paren_closing_ = false;
    break;
  case RIGHT_BLOCK:
  case RIGHT_ARRAY:
  case RIGHT_BRACKET:
    assert(paren_stack.top() == paren_match[current]);
    paren_closing_ = true;
    break;
  case QUOTE:
    peek = peek_next();
    assert(quote_follow[peek]);
    obj = new LispList;
    list_stack.push(obj);
    ((LispList*)obj)->cons_.push(new LispSymbol("quote"));
    next_form();
    list_stack.pop();
    break;
  case DOUBLE_QUOTE:
    // TODO: slashes
    str_start = cursor_;
    while ((current=next()) != DOUBLE_QUOTE);
    obj = new LispString(std::string(str_start, cursor_ - str_start - 1));
    break;
  default:
    // symbol or keyitem
    if ('0' <= current && current <= '9' || current == MINUS) {
      // numbers
      bool minus = false;
      bool in_float = false;
      double res = 0;
      if (current == MINUS) {
        minus = true;
        current = next();
        if (current < '0' || current > '9') {
          obj = new LispSymbol("-");
          utf8::unchecked::prior(cursor_);
          break;
        }
      }
      double factor = 1;
      for (; '0' <= current && current <= '9' || current == '.'; current = next()) {
        if (current == '.') {
          assert(!in_float);
          in_float = true;
          factor /= 10;
          continue;
        }
        if (!in_float) {
          res = 10 * res + (current - '0');
        } else {
          res += (current - '0')*factor;
          factor /= 10;
        }
      }
      if (minus) res = -res;
      if (current == 'e') {
        // TODO: left for completion
      } else {
        utf8::unchecked::prior(cursor_);
      }
      if (in_float)
        obj = new LispFloat(static_cast<float>(res));
      else
        obj = new LispInt32(static_cast<int32_t>(res));
    } else {
      // identifiers
      utf8::unchecked::prior(cursor_);
      str_start = cursor_;
      while (!punctuation[next()]);
      utf8::unchecked::prior(cursor_);
      std::string id(str_start, cursor_ - str_start);
      if (id == "nil")
        obj = new LispNil;
      else if (id == "true")
        obj = new LispBool(true);
      else if (id == "false")
        obj = new LispBool(false);
      else
        obj = new LispSymbol(id);
    }
    break;
  }
  if (obj && !list_stack.empty()) {
    LispObject* tmp = list_stack.top();
    if (ARRAYP(tmp)) {
      ((LispArray*)tmp)->data_.push_back(obj);
    } else {
      ((LispList*)tmp)->cons_.push(obj);
    }
  }
  return obj;
}
