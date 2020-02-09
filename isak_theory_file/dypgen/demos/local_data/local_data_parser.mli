
# 57 "local_data_parser.dyp"
        
module String_map : Map.S with type key = string

# 7                  "local_data_parser.mli"
type ('dypgen__Obj_IDENT, 'dypgen__Obj_binding, 'dypgen__Obj_expr,
      'dypgen__Obj_main)
     obj =
    Lexeme_matched of string
  | Obj_IDENT of 'dypgen__Obj_IDENT
  | Obj___dypgen_layout
  | Obj_binding of 'dypgen__Obj_binding
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit,
   (String_map.key, Parse_tree.tree, Parse_tree.tree, Parse_tree.tree) obj,
   unit, Parse_tree.tree String_map.t, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:Parse_tree.tree String_map.t ->
  (String_map.key, Parse_tree.tree, Parse_tree.tree, Parse_tree.tree) obj
  Dyp.dyplexbuf -> (Parse_tree.tree * string) list


