
type token = EOF | TIMES | PLUS | INT of int
type 'dypgen__Obj_expr obj =
    Lexeme_matched of string
  | Obj_EOF
  | Obj_INT of int
  | Obj_PLUS
  | Obj_TIMES
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of Parse_tree.tree

val pp :
  unit ->
  (token, Parse_tree.tree obj, unit, unit, Lexing.lexbuf) Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (Lexing.lexbuf -> token) ->
  Lexing.lexbuf -> (Parse_tree.tree * string) list


