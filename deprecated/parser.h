#include <stack>
#include "runtime.h"

using unichar = uint32_t;
const uint32_t MAX_CHAR = 128;

class Parser {
  // data
  const char* data_start_;
  const char* data_end_;
  const char* cursor_;

  // parens
  std::stack<unichar, std::vector<unichar>> paren_stack;
  unichar paren_match[MAX_CHAR] = {0};
  bool paren_closing_;

  // quote
  bool quote_follow[MAX_CHAR] = {0};

  // list
  std::stack<LispObject*, std::vector<LispObject*>> list_stack;

  // symbol
  bool punctuation[MAX_CHAR] = {0};

private:
  inline unichar peek_next();
  inline unichar next();

public:
  Parser(const char* s, const char* e);
  LispObject* next_form();
};
