(* The first section of the grammar definition, called the *header*,
   is the part that appears below between %{ and %}.  It is code
   that will simply be copied literally into the generated parser.ml.
   Here we use it just to open the Ast module so that, later on
   in the grammar definition, we can write expressions like
   [Int i] instead of [Ast.Int i]. *)

%{
open Tir
%}

(* The next section of the grammar definition, called the *declarations*,
   first declares all the lexical *tokens* of the language.  These are
   all the kinds of tokens we can expect to read from the token stream.
   Note that each of these is just a descriptive name---nothing so far
   says that LPAREN really corresponds to '(', for example.  The tokens
   that have a <type> annotation appearing in them are declaring that
   they will carry some additional data along with them.  In the
   case of INT, that's an OCaml int.  In the case of ID, that's
   an OCaml string. *)

%token <int> INT
%token <string> ID
%token <string> STRING
%token PRINTF
%token PLUS
%token ASTERISK
%token MINUS
%token LESS
%token EQUAL
%token LPAREN
%token RPAREN
%token VAR
%token CINT
%token CSTRING
%token CBOOL
%token TRUE
%token FALSE
%token IF
%token WHILE
%token ELSE
%token FUNC
%token COLON
%token COMMA
%token DOT
%token SEMICOLON
%token RETURN
%token LBRACE
%token RBRACE
%token LBOX
%token RBOX
%token LET
%token ASSIGN
%token STRUCT
%token EOF

(* After declaring the tokens, we have to provide some additional information
   about precedence and associativity.  The following declarations say that
   PLUS is left associative, that IN is not associative, and that PLUS
   has higher precedence than IN (because PLUS appears on a line after IN).

   Because PLUS is left associative, "1+2+3" will parse as "(1+2)+3"
   and not as "1+(2+3)".

   Because PLUS has higher precedence than IN, "let x=1 in x+2" will
   parse as "let x=1 in (x+2)" and not as "(let x=1 in x)+2". *)

(* %nonassoc IN *)
%left PLUS
%left ASTERISK
%left MINUS
%left LESS
%left EQUAL
%left DOT
%nonassoc LBOX
%nonassoc LPAREN

(* After declaring associativity and precedence, we need to declare what
   the starting point is for parsing the language.  The following
   declaration says to start with a rule (defined below) named [prog].
   The declaration also says that parsing a [prog] will return an OCaml
   value of type [Ast.expr]. *)

%start <Tir.stmt list> prog
%start <Tir.expr> term

(* The following %% ends the declarations section of the grammar definition. *)

%%

prog:
  | s = list(stmt); EOF { s }
	;

term:
  | e = expr; EOF { e }
  ;

expr:
	| i = INT { Texpr_int i }
  | s = STRING { Texpr_string s }
  | TRUE { Texpr_bool true }
  | FALSE { Texpr_bool false }
	| x = ID { Texpr_var (-1, Some x) }
	| e0 = expr; PLUS; e1 = expr { Texpr_op (Top_add, [e0; e1]) }
  | e0 = expr; ASTERISK; e1 = expr { Texpr_op (Top_multiply, [e0; e1]) }
  | e0 = expr; MINUS; e1 = expr { Texpr_op (Top_minus, [e0; e1]) }
  | e0 = expr; LESS; e1 = expr { Texpr_op (Top_lt, [e0; e1]) }
  | e0 = expr; EQUAL; e1 = expr { Texpr_op (Top_equal, [e0; e1]) }
  | PRINTF; LBOX; el = separated_list(COMMA, expr); RBOX { Texpr_op (Top_cprintf, el) }
	| LPAREN; e = expr; RPAREN { e }
  | LBOX; el = separated_list(COMMA, expr); RBOX { Texpr_array el }
  | c = ID; LBRACE; xel = separated_list(COMMA, separated_pair(ID, COLON, expr)); RBRACE { Texpr_ctor (Tcon_named (-1, Some c), xel) }
  | caller = expr; LPAREN; args = separated_list(COMMA, expr); RPAREN { Texpr_app(caller, args) }
  | e0 = expr; DOT; field = ID { Texpr_field (e0, (-1, Some field)) }
  | e = expr; LBOX; i = expr; RBOX { Texpr_op (Top_idx, [e; i]) }
	;

%inline param:
  | mut = option(VAR); x = ID; COLON; ty = con { (Var.newvar (Some x), ty) }

stmt:
  | FUNC; fname = ID; LPAREN; args = separated_list(COMMA, param); RPAREN; COLON; tr = con; LBRACE; sl = list(stmt); RBRACE { Tstmt_decl (Var.newvar (Some fname), Timm, (Some (Tcon_arrow (List.map (fun (_, x) -> x) args, tr))), Texpr_func (args, tr, Tstmt_blk sl)) }
  | LBRACE; stmts = list(stmt); RBRACE { Tstmt_blk stmts }
  | RETURN; e = expr; SEMICOLON { Tstmt_ret e }
  | LET; x = ID; COLON; ty = con; ASSIGN; e = expr; SEMICOLON { Tstmt_decl (Var.newvar (Some x), Timm, Some ty, e) }
  | VAR; x = ID; COLON; ty = con; ASSIGN; e = expr; SEMICOLON { Tstmt_decl (Var.newvar (Some x), Tmut, Some ty, e) }
  | STRUCT; sname = ID; LBRACE; xcl = separated_list(COMMA, separated_pair(ID, COLON, con)); RBRACE { let v = Var.newvar (Some sname) in Tstmt_decl (v, Timm, None, Texpr_con (Tcon_prod (List.map snd xcl, Some (List.map fst xcl)))) }
  | e = expr; SEMICOLON { Tstmt_expr e }
  | lval = expr; ASSIGN; e = expr; SEMICOLON { Tstmt_asgn(lval, e) }
  | IF; LPAREN; e = expr; RPAREN; LBRACE; sl0 = list(stmt); RBRACE { Tstmt_if (e, Tstmt_blk sl0, Tstmt_blk []) }
  | IF; LPAREN; e = expr; RPAREN; LBRACE; sl0 = list(stmt); RBRACE; ELSE; LBRACE; sl1 = list(stmt); RBRACE { Tstmt_if (e, Tstmt_blk sl0, Tstmt_blk sl1) }
  | WHILE; LPAREN; e = expr; RPAREN; LBRACE; sl = list(stmt); RBRACE { Tstmt_while (e, Tstmt_blk sl) }
  ;

con:
  | CINT { Tcon_int }
  | CSTRING { Tcon_string }
  | CBOOL { Tcon_bool }
  | LPAREN; cl = separated_list(COMMA, con) RPAREN { Tcon_prod (cl, None) }
  | x = ID { Tcon_named (-1, Some x) }
  | c = con; LBOX; RBOX { Tcon_array c }
  ;
