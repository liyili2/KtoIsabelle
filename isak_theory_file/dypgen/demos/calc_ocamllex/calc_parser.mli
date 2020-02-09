
type token = EOL | DIV | TIMES | MINUS | PLUS | INT of int | RPAREN | LPAREN
type ('dypgen__Obj_expr, 'dypgen__Obj_main) obj =
    Lexeme_matched of string
  | Obj_DIV
  | Obj_EOL
  | Obj_INT of int
  | Obj_LPAREN
  | Obj_MINUS
  | Obj_PLUS
  | Obj_RPAREN
  | Obj_TIMES
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main

val pp :
  unit -> (token, (int, int) obj, unit, unit, Lexing.lexbuf) Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (int * string) list


