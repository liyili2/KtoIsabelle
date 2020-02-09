
type ('dypgen__Obj_dypgen__nested_nt_0, 'dypgen__Obj_dypgen__nested_nt_1,
      'dypgen__Obj_expr, 'dypgen__Obj_main)
     obj =
    Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_dypgen__nested_nt_0 of 'dypgen__Obj_dypgen__nested_nt_0
  | Obj_dypgen__nested_nt_1 of 'dypgen__Obj_dypgen__nested_nt_1
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit, ([ `MINUS | `PLUS ], [ `DIV | `TIMES ], int, int) obj, unit, 
   unit, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  ([ `MINUS | `PLUS ], [ `DIV | `TIMES ], int, int) obj Dyp.dyplexbuf ->
  (int * string) list


