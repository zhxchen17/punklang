// Signature file for parser generated by fsyacc
module Parser
type token = 
  | WHILE
  | VAR
  | TRUE
  | STRUCT
  | STRING of (string)
  | SEMICOLON
  | RPAREN
  | RETURN
  | RBRACE
  | RBOX
  | PRINTF
  | PLUS
  | MINUS
  | LPAREN
  | LET
  | LESS
  | LBRACE
  | LBOX
  | INT of (int)
  | IF
  | ID of (string)
  | FUNC
  | FALSE
  | EQUAL
  | EOF
  | ELSE
  | DOT
  | CSTRING
  | COMMA
  | COLON
  | CINT
  | CBOOL
  | ASTERISK
  | ASSIGN
type tokenId = 
    | TOKEN_WHILE
    | TOKEN_VAR
    | TOKEN_TRUE
    | TOKEN_STRUCT
    | TOKEN_STRING
    | TOKEN_SEMICOLON
    | TOKEN_RPAREN
    | TOKEN_RETURN
    | TOKEN_RBRACE
    | TOKEN_RBOX
    | TOKEN_PRINTF
    | TOKEN_PLUS
    | TOKEN_MINUS
    | TOKEN_LPAREN
    | TOKEN_LET
    | TOKEN_LESS
    | TOKEN_LBRACE
    | TOKEN_LBOX
    | TOKEN_INT
    | TOKEN_IF
    | TOKEN_ID
    | TOKEN_FUNC
    | TOKEN_FALSE
    | TOKEN_EQUAL
    | TOKEN_EOF
    | TOKEN_ELSE
    | TOKEN_DOT
    | TOKEN_CSTRING
    | TOKEN_COMMA
    | TOKEN_COLON
    | TOKEN_CINT
    | TOKEN_CBOOL
    | TOKEN_ASTERISK
    | TOKEN_ASSIGN
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startterm
    | NONTERM__startprog
    | NONTERM_option_VAR_
    | NONTERM_loption_separated_nonempty_list_COMMA_con__
    | NONTERM_loption_separated_nonempty_list_COMMA_expr__
    | NONTERM_loption_separated_nonempty_list_COMMA_param__
    | NONTERM_loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_con___
    | NONTERM_loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr___
    | NONTERM_list_stmt_
    | NONTERM_separated_nonempty_list_COMMA_con_
    | NONTERM_separated_nonempty_list_COMMA_expr_
    | NONTERM_separated_nonempty_list_COMMA_param_
    | NONTERM_separated_nonempty_list_COMMA_separated_pair_ID_COLON_con__
    | NONTERM_separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr__
    | NONTERM_prog
    | NONTERM_term
    | NONTERM_expr
    | NONTERM_stmt
    | NONTERM_con
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val term : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (expr) 
val prog : (FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> FSharp.Text.Lexing.LexBuffer<'cty> -> (stmt list) 