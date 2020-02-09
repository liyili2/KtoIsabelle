
type ('dypgen__Lex_string, 'dypgen__Obj_LIDENT, 'dypgen__Obj_STRING,
      'dypgen__Obj_UIDENT, 'dypgen__Obj_define_in, 'dypgen__Obj_expr,
      'dypgen__Obj_main, 'dypgen__Obj_rhs)
     obj =
    Lex_string of 'dypgen__Lex_string
  | Lexeme_matched of string
  | Obj_LIDENT of 'dypgen__Obj_LIDENT
  | Obj_STRING of 'dypgen__Obj_STRING
  | Obj_UIDENT of 'dypgen__Obj_UIDENT
  | Obj___dypgen_layout
  | Obj_define_in of 'dypgen__Obj_define_in
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Obj_rhs of 'dypgen__Obj_rhs
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit,
   (unit, string, string, string, unit, Parse_tree.expr, Parse_tree.expr,
    Parse_tree.rhs list)
   obj, unit, unit, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  (unit, string, string, string, unit, Parse_tree.expr, Parse_tree.expr,
   Parse_tree.rhs list)
  obj Dyp.dyplexbuf -> (Parse_tree.expr * string) list


