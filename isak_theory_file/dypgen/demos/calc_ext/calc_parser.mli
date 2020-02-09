
type ('dypgen__Inh_dypgen__early_action_0,
      'dypgen__Obj_dypgen__early_action_0, 'dypgen__Obj_dypgen__epsilon,
      'dypgen__Obj_expr, 'dypgen__Obj_main)
     obj =
    Inh_dypgen__early_action_0 of 'dypgen__Inh_dypgen__early_action_0
  | Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_dypgen__early_action_0 of 'dypgen__Obj_dypgen__early_action_0
  | Obj_dypgen__epsilon of 'dypgen__Obj_dypgen__epsilon
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit, (string, unit, unit, int, int) obj, unit, unit, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (string, unit, unit, int, int) obj Dyp.dyplexbuf -> (int * string) list


