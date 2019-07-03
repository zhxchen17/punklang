%{
open Tir
%}
%start prog
%start term
%token ASSIGN
%token ASTERISK
%token CBOOL
%token CINT
%token COLON
%token COMMA
%token CSTRING
%token DOT
%token ELSE
%token EOF
%token EQUAL
%token FALSE
%token FUNC
%token <string> ID
%token IF
%token <int> INT
%token LBOX
%token LBRACE
%token LESS
%token LET
%token LPAREN
%token MINUS
%token PLUS
%token PRINTF
%token RBOX
%token RBRACE
%token RETURN
%token RPAREN
%token SEMICOLON
%token <string> STRING
%token STRUCT
%token TRUE
%token VAR
%token WHILE
%left PLUS
%left ASTERISK
%left MINUS
%left LESS
%left EQUAL
%left DOT
%nonassoc LBOX
%nonassoc LPAREN
%type <Tir.stmt list> prog
%type <Tir.expr> term
%%

option_VAR_:
  
    {    ( None )}
| VAR
    {let x = () in
    ( Some x )}

loption_separated_nonempty_list_COMMA_con__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_con_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_COMMA_expr__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_expr_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_COMMA_param__:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_param_
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_con___:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_separated_pair_ID_COLON_con__
    {let x = $1 in
    ( x )}

loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr___:
  
    {    ( [] )}
| separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr__
    {let x = $1 in
    ( x )}

list_stmt_:
  
    {    ( [] )}
| stmt list_stmt_
    {let (x, xs) = ($1, $2) in
    ( x :: xs )}

separated_nonempty_list_COMMA_con_:
  con
    {let x = $1 in
    ( [ x ] )}
| con COMMA separated_nonempty_list_COMMA_con_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_expr_:
  expr
    {let x = $1 in
    ( [ x ] )}
| expr COMMA separated_nonempty_list_COMMA_expr_
    {let (x, _2, xs) = ($1, (), $3) in
    ( x :: xs )}

separated_nonempty_list_COMMA_param_:
  option_VAR_ ID COLON con
    {let (mut, x, _3, ty) = ($1, $2, (), $4) in
let x =                                                ( (Var.newvar (Some x), ty) ) in
    ( [ x ] )}
| option_VAR_ ID COLON con COMMA separated_nonempty_list_COMMA_param_
    {let (mut, x, _3, ty, _2, xs) = ($1, $2, (), $4, (), $6) in
let x =                                                ( (Var.newvar (Some x), ty) ) in
    ( x :: xs )}

separated_nonempty_list_COMMA_separated_pair_ID_COLON_con__:
  ID COLON con
    {let (x, _2, y) = ($1, (), $3) in
let x =     ( (x, y) ) in
    ( [ x ] )}
| ID COLON con COMMA separated_nonempty_list_COMMA_separated_pair_ID_COLON_con__
    {let (x, _2_inlined1, y, _2, xs) = ($1, (), $3, (), $5) in
let x =
  let _2 = _2_inlined1 in
      ( (x, y) )
in
    ( x :: xs )}

separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr__:
  ID COLON expr
    {let (x, _2, y) = ($1, (), $3) in
let x =     ( (x, y) ) in
    ( [ x ] )}
| ID COLON expr COMMA separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr__
    {let (x, _2_inlined1, y, _2, xs) = ($1, (), $3, (), $5) in
let x =
  let _2 = _2_inlined1 in
      ( (x, y) )
in
    ( x :: xs )}

prog:
  list_stmt_ EOF
    {let (s, _2) = ($1, ()) in
                        ( s )}

term:
  expr EOF
    {let (e, _2) = ($1, ()) in
                  ( e )}

expr:
  INT
    {let i = $1 in
           ( Texpr_int i )}
| STRING
    {let s = $1 in
               ( Texpr_string s )}
| TRUE
    {let _1 = () in
         ( Texpr_bool true )}
| FALSE
    {let _1 = () in
          ( Texpr_bool false )}
| ID
    {let x = $1 in
          ( Texpr_var (-1, Some x) )}
| expr PLUS expr
    {let (e0, _2, e1) = ($1, (), $3) in
                              ( Texpr_op (Top_add, [e0; e1]) )}
| expr ASTERISK expr
    {let (e0, _2, e1) = ($1, (), $3) in
                                   ( Texpr_op (Top_multiply, [e0; e1]) )}
| expr MINUS expr
    {let (e0, _2, e1) = ($1, (), $3) in
                                ( Texpr_op (Top_minus, [e0; e1]) )}
| expr LESS expr
    {let (e0, _2, e1) = ($1, (), $3) in
                               ( Texpr_op (Top_lt, [e0; e1]) )}
| expr EQUAL expr
    {let (e0, _2, e1) = ($1, (), $3) in
                                ( Texpr_op (Top_equal, [e0; e1]) )}
| PRINTF LBOX loption_separated_nonempty_list_COMMA_expr__ RBOX
    {let (_1, _2, xs, _4) = ((), (), $3, ()) in
let el =     ( xs ) in
                                                         ( Texpr_op (Top_cprintf, el) )}
| LPAREN expr RPAREN
    {let (_1, e, _3) = ((), $2, ()) in
                            ( e )}
| LBOX loption_separated_nonempty_list_COMMA_expr__ RBOX
    {let (_1, xs, _3) = ((), $2, ()) in
let el =     ( xs ) in
                                                 ( Texpr_array el )}
| ID LBRACE loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_expr___ RBRACE
    {let (c, _2, xs, _4) = ($1, (), $3, ()) in
let xel =     ( xs ) in
                                                                                         ( Texpr_ctor (Tcon_named (-1, Some c), xel) )}
| expr LPAREN loption_separated_nonempty_list_COMMA_expr__ RPAREN
    {let (caller, _2, xs, _4) = ($1, (), $3, ()) in
let args =     ( xs ) in
                                                                      ( Texpr_app(caller, args) )}
| expr DOT ID
    {let (e0, _2, field) = ($1, (), $3) in
                               ( Texpr_field (e0, (-1, Some field)) )}
| expr LBOX expr RBOX
    {let (e, _2, i, _4) = ($1, (), $3, ()) in
                                   ( Texpr_op (Top_idx, [e; i]) )}

stmt:
  FUNC ID LPAREN loption_separated_nonempty_list_COMMA_param__ RPAREN COLON con LBRACE list_stmt_ RBRACE
    {let (_1, fname, _3, xs, _5, _6, tr, _8, sl, _10) = ((), $2, (), $4, (), (), $7, (), $9, ()) in
let args =     ( xs ) in
                                                                                                                            ( Tstmt_decl (Var.newvar (Some fname), Timm, (Some (Tcon_arrow (List.map (fun (_, x) -> x) args, tr))), Texpr_func (args, tr, Tstmt_blk sl)) )}
| LBRACE list_stmt_ RBRACE
    {let (_1, stmts, _3) = ((), $2, ()) in
                                       ( Tstmt_blk stmts )}
| RETURN expr SEMICOLON
    {let (_1, e, _3) = ((), $2, ()) in
                                ( Tstmt_ret e )}
| LET ID COLON con ASSIGN expr SEMICOLON
    {let (_1, x, _3, ty, _5, e, _7) = ((), $2, (), $4, (), $6, ()) in
                                                              ( Tstmt_decl (Var.newvar (Some x), Timm, Some ty, e) )}
| VAR ID COLON con ASSIGN expr SEMICOLON
    {let (_1, x, _3, ty, _5, e, _7) = ((), $2, (), $4, (), $6, ()) in
                                                              ( Tstmt_decl (Var.newvar (Some x), Tmut, Some ty, e) )}
| STRUCT ID LBRACE loption_separated_nonempty_list_COMMA_separated_pair_ID_COLON_con___ RBRACE
    {let (_1, sname, _3, xs, _5) = ((), $2, (), $4, ()) in
let xcl =     ( xs ) in
                                                                                                    ( let v = Var.newvar (Some sname) in Tstmt_struct (v, xcl) )}
| expr SEMICOLON
    {let (e, _2) = ($1, ()) in
                        ( Tstmt_expr e )}
| expr ASSIGN expr SEMICOLON
    {let (lval, _2, e, _4) = ($1, (), $3, ()) in
                                             ( Tstmt_asgn(lval, e) )}
| IF LPAREN expr RPAREN LBRACE list_stmt_ RBRACE
    {let (_1, _2, e, _4, _5, sl0, _7) = ((), (), $3, (), (), $6, ()) in
                                                                   ( Tstmt_if (e, Tstmt_blk sl0, Tstmt_blk []) )}
| IF LPAREN expr RPAREN LBRACE list_stmt_ RBRACE ELSE LBRACE list_stmt_ RBRACE
    {let (_1, _2, e, _4, _5, sl0, _7, _8, _9, sl1, _11) = ((), (), $3, (), (), $6, (), (), (), $10, ()) in
                                                                                                           ( Tstmt_if (e, Tstmt_blk sl0, Tstmt_blk sl1) )}
| WHILE LPAREN expr RPAREN LBRACE list_stmt_ RBRACE
    {let (_1, _2, e, _4, _5, sl, _7) = ((), (), $3, (), (), $6, ()) in
                                                                     ( Tstmt_while (e, Tstmt_blk sl) )}

con:
  CINT
    {let _1 = () in
         ( Tcon_int )}
| CSTRING
    {let _1 = () in
            ( Tcon_string )}
| CBOOL
    {let _1 = () in
          ( Tcon_bool )}
| LPAREN loption_separated_nonempty_list_COMMA_con__ RPAREN
    {let (_1, xs, _3) = ((), $2, ()) in
let cl =     ( xs ) in
                                                   ( Tcon_prod (cl, None) )}
| ID
    {let x = $1 in
           ( Tcon_named (-1, Some x) )}
| con LBOX RBOX
    {let (c, _2, _3) = ($1, (), ()) in
                        ( Tcon_array c )}

%%


