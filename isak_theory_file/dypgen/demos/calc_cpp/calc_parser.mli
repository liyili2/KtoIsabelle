
type ('dypgen__Obj_expr, 'dypgen__Obj_main) obj =
    Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit, (int, int) obj, unit, unit, 'a Dyp.dyplexbuf) Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit -> (int, int) obj Dyp.dyplexbuf -> (int * string) list


