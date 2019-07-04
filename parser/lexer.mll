(* The first section of the lexer definition, called the *header*,
   is the part that appears below between { and }.  It is code
   that will simply be copied literally into the generated lexer.ml. *)

{
open Parser
}

(* The second section of the lexer definition defines *identifiers*
   that will be used later in the definition.  Each identifier is
   a *regular expression*.  We won't go into details on how regular
   expressions work.

   Below, we define regular expressions for
     - whitespace (spaces and tabs),
     - digits (0 through 9)
     - integers (nonempty sequences of digits, optionally preceded by a minus sign)
     - letters (a through z, and A through Z), and
     - identifiers (nonempty sequences of letters).

   FYI, these aren't exactly the same as the OCaml definitions of integers and
   identifiers. *)

let white = [' ' '\t' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let id = ['a'-'z' 'A'-'Z' '_']+

(* The final section of the lexer definition defines how to parse a character
   stream into a token stream.  Each of the rules below has the form
     | regexp { action }
   If the lexer sees the regular expression [regexp], it produces the token
   specified by the [action].  We won't go into details on how the actions
   work.  *)

rule read =
  parse
  | white { read lexbuf }
  | "+"   { PLUS }
  | "*"   { ASTERISK }
  | "-"   { MINUS }
  | "=="  { EQUAL }
  | "("   { LPAREN }
  | ")"   { RPAREN }
  | "func" { FUNC }
  | "var" { VAR }
  | ":" { COLON }
  | "," { COMMA }
  | "." { DOT }
  | "int" { CINT }
  | "string" { CSTRING }
  | "bool" { CBOOL }
  | "true" { TRUE }
  | "false" { FALSE }
  | "if" { IF }
  | "while" { WHILE }
  | "else" { ELSE }
  | ";" { SEMICOLON }
  | "return" { RETURN }
  | "<" { LESS }
  | "{" { LBRACE }
  | "}" { RBRACE }
  | "let" { LET }
  | "=" { ASSIGN }
  | "[" { LBOX }
  | "]" { RBOX }
  | "struct" { STRUCT }
  | "printf" { PRINTF }
  | '"' { read_string (Buffer.create bufSize) lexbuf }
  | id    { ID (Lexing.lexeme lexbuf) }
  | int   { INT (int_of_string (Lexing.lexeme lexbuf)) }
  | eof   { EOF }

and read_string buf =
  parse
  | '"'       { STRING (Buffer.contents buf) }
  | '\\' '/'  { Buffer.add_char buf '/'; read_string buf lexbuf }
  | '\\' '\\' { Buffer.add_char buf '\\'; read_string buf lexbuf }
  | '\\' 'b'  { Buffer.add_char buf '\b'; read_string buf lexbuf }
  | '\\' 'f'  { Buffer.add_char buf '\012'; read_string buf lexbuf }
  | '\\' 'n'  { Buffer.add_char buf '\n'; read_string buf lexbuf }
  | '\\' 'r'  { Buffer.add_char buf '\r'; read_string buf lexbuf }
  | '\\' 't'  { Buffer.add_char buf '\t'; read_string buf lexbuf }
  | [^ '"' '\\']+ {
      Buffer.add_string buf (Lexing.lexeme lexbuf);
      read_string buf lexbuf
    }
  | _ { raise (FrontendSyntaxException
                 ("Illegal string character: " ^ Lexing.lexeme lexbuf)) }
  | eof { raise (FrontendSyntaxException ("String is not terminated")) }

(* And that's the end of the lexer definition. *)
