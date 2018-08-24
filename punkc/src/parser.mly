(* The first section of the grammar definition, called the *header*,
   is the part that appears below between %{ and %}.  It is code
   that will simply be copied literally into the generated parser.ml.
   Here we use it just to open the Ast module so that, later on
   in the grammar definition, we can write expressions like
   [Int i] instead of [Ast.Int i]. *)

%{
open Ast
module Option = Core.Option
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
%token LESS
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
%left LESS
%left DOT
%nonassoc LBOX
%nonassoc LPAREN

(* After declaring associativity and precedence, we need to declare what
   the starting point is for parsing the language.  The following
   declaration says to start with a rule (defined below) named [prog].
   The declaration also says that parsing a [prog] will return an OCaml
   value of type [Ast.expr]. *)

%start <Ast.stmt list> prog
%start <Ast.expr> term

(* The following %% ends the declarations section of the grammar definition. *)

%%

(* Now begins the *rules* section of the grammar definition.  This is a list
   of rules that are essentially in Backus-Naur Form (BNF), although where in
   BNF we would write "::=" these rules simply write ":".

   The format of a rule is

     name:
       | production { action }
       | production { action }
       | etc.
       ;

    The *production* is the sequence of *symbols* that the rule matches.
    A symbol is either a token or the name of another rule.
    The *action* is the OCaml value to return if a match occurs.
    Each production can *bind* the value carried by a symbol and use
    that value in its action.  This is perhaps best understood by example... *)


prog:
  | s = list(stmt); EOF { s }
	;

term:
  | e = expr; EOF { e }
  ;

expr:
	| i = INT { Eint i }
  | s = STRING { Estring s }
  | TRUE { Ebool true }
  | FALSE { Ebool false }
	| x = ID { Evar (-1, Some x) }
	| e0 = expr; PLUS; e1 = expr { Eop (Add, [e0; e1]) }
  | e0 = expr; LESS; e1 = expr { Eop (Lt, [e0; e1]) }
  | PRINTF; LBOX; el = separated_list(COMMA, expr); RBOX { Eop (Cprintf, el) }
	| LPAREN; e = expr; RPAREN { e }
  | LBOX; el = separated_list(COMMA, expr); RBOX { Earray (None, el) }
  | c = ID; LBRACE; xel = separated_list(COMMA, separated_pair(ID, COLON, expr)); RBRACE { Ector (Cnamed ((-1, Some c), None), xel) }
  | caller = expr; LPAREN; args = separated_list(COMMA, expr); RPAREN { Eapp(caller, args) }
  | e0 = expr; DOT; field = ID { Efield (e0, (-1, Some field)) }
  | e = expr; LBOX; i = expr; RBOX { Eop (Idx, [e; i]) }
	;

%inline param:
  | mut = option(VAR); x = ID; COLON; ty = con { (Var.newvar (Some x), (if Option.is_some mut then Mutable else Immutable), ty) }

stmt:
  | FUNC; fname = ID; LPAREN; params = separated_list(COMMA, param); RPAREN; COLON; tr = con; LBRACE; sl = list(stmt); RBRACE { Sdecl (Var.newvar (Some fname), Immutable, None, Efunc (params, tr, Sblk sl)) }
  | LBRACE; stmts = list(stmt); RBRACE { Sblk stmts }
  | RETURN; e = expr; SEMICOLON { Sret e }
  | LET; x = ID; COLON; ty = con; ASSIGN; e = expr; SEMICOLON { Sdecl (Var.newvar (Some x), Immutable, Some ty, e) }
  | VAR; x = ID; COLON; ty = con; ASSIGN; e = expr; SEMICOLON { Sdecl (Var.newvar (Some x), Mutable, Some ty, e) }
  | STRUCT; sname = ID; LBRACE; xcl = separated_list(COMMA, separated_pair(ID, COLON, con)); RBRACE { let v = Var.newvar (Some sname) in Sdecl (v, Immutable, None, Econ (Cnamed (v, Some (Cprod (List.map snd xcl, Some (List.map fst xcl)))))) }
  | e = expr; SEMICOLON { Sexpr e }
  | lval = expr; ASSIGN; e = expr; SEMICOLON { Sasgn(lval, e) }
  | IF; LPAREN; e = expr; RPAREN; LBRACE; sl0 = list(stmt); RBRACE { Sif (e, Sblk sl0, Sblk []) }
  | IF; LPAREN; e = expr; RPAREN; LBRACE; sl0 = list(stmt); RBRACE; ELSE; LBRACE; sl1 = list(stmt); RBRACE { Sif (e, Sblk sl0, Sblk sl1) }
  | WHILE; LPAREN; e = expr; RPAREN; LBRACE; sl = list(stmt); RBRACE { Swhile (e, Sblk sl) }
  ;

con:
  | CINT { Cint }
  | CSTRING { Cstring }
  | CBOOL { Cbool }
  | LPAREN; cl = separated_list(COMMA, con) RPAREN { Cprod (cl, None) }
  | x = ID { Cnamed ((-1, Some x), None) }
  | c = con; LBOX; len = option(expr); RBOX { Carray(c, len) }
  ;
