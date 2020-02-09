
type token = EOL | OP of string | INT of int | RPAREN | LPAREN
type 'dypgen__Obj_expr obj =
    Lexeme_matched of string
  | Obj_EOL
  | Obj_INT of int
  | Obj_LPAREN
  | Obj_OP of string
  | Obj_RPAREN
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of int

val pp : unit -> (token, int obj, unit, unit, Lexing.lexbuf) Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (int * string) list


