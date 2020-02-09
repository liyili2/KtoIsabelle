
type token = EOF | TIMES | PLUS | INT of int
type 'dypgen__Obj_expr obj =
    Lexeme_matched of string
  | Obj_EOF
  | Obj_INT of int
  | Obj_PLUS
  | Obj_TIMES
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of Parse_tree.tree

# 49 "position_parser.dyp"
        
type lexbuf2 = {
  mutable token_list : (token * (Lexing.position * Lexing.position)) list;
  mutable token_position : (Lexing.position * Lexing.position) }

# 19                 "position_parser.mli"
val pp :
  unit -> (token, Parse_tree.tree obj, unit, unit, lexbuf2) Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (lexbuf2 -> token) -> lexbuf2 -> (Parse_tree.tree * string) list


