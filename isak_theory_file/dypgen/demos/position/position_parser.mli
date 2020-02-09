
type ('dypgen__Obj_expr, 'dypgen__Obj_main) obj =
    Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit, (Parse_tree.tree, Parse_tree.tree) obj, unit, unit,
   'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (Parse_tree.tree, Parse_tree.tree) obj Dyp.dyplexbuf ->
  (Parse_tree.tree * string) list


