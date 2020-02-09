
type token =
    EOF
  | RBRACK
  | LBRACK
  | RPAREN
  | LPAREN
  | IN
  | DEFINE
  | SEMICOLON
  | COLONCOLON
  | COLONEQUAL
  | EQUAL
  | COMMA
  | TOKEN of string
  | INT of int
  | LIDENT of string
  | UIDENT of string
type ('dypgen__Obj_define_in, 'dypgen__Obj_expr, 'dypgen__Obj_rhs) obj =
    Lexeme_matched of string
  | Obj_COLONCOLON
  | Obj_COLONEQUAL
  | Obj_COMMA
  | Obj_DEFINE
  | Obj_EOF
  | Obj_EQUAL
  | Obj_IN
  | Obj_INT of int
  | Obj_LBRACK
  | Obj_LIDENT of string
  | Obj_LPAREN
  | Obj_RBRACK
  | Obj_RPAREN
  | Obj_SEMICOLON
  | Obj_TOKEN of string
  | Obj_UIDENT of string
  | Obj_define_in of 'dypgen__Obj_define_in
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of Parse_tree.expr
  | Obj_rhs of 'dypgen__Obj_rhs

val pp :
  unit ->
  (token, (unit, Parse_tree.expr, Parse_tree.rhs list) obj, unit, unit,
   Lexing.lexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (Lexing.lexbuf -> token) ->
  Lexing.lexbuf -> (Parse_tree.expr * string) list


