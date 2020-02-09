
# 60 "local_data_parser.dyp"
        
module String_map : Map.S with type key = string

# 7                  "local_data_parser.mli"
type ('dypgen__Inh_dypgen__early_action_0, 'dypgen__Obj_IDENT,
      'dypgen__Obj_dypgen__early_action_0, 'dypgen__Obj_dypgen__epsilon,
      'dypgen__Obj_main)
     obj =
    Inh_dypgen__early_action_0 of 'dypgen__Inh_dypgen__early_action_0
  | Lexeme_matched of string
  | Obj_IDENT of 'dypgen__Obj_IDENT
  | Obj___dypgen_layout
  | Obj_dypgen__early_action_0 of 'dypgen__Obj_dypgen__early_action_0
  | Obj_dypgen__epsilon of 'dypgen__Obj_dypgen__epsilon
  | Obj_expr of Parse_tree.tree
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

val pp :
  unit ->
  (unit,
   (string * String_map.key * string * Parse_tree.tree, String_map.key,
    Parse_tree.tree, unit, Parse_tree.tree)
   obj, unit, Parse_tree.tree String_map.t, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val expr :
  ?global_data:unit ->
  ?local_data:Parse_tree.tree String_map.t ->
  (string * String_map.key * string * Parse_tree.tree, String_map.key,
   Parse_tree.tree, unit, Parse_tree.tree)
  obj Dyp.dyplexbuf -> (Parse_tree.tree * string) list

val main :
  ?global_data:unit ->
  ?local_data:Parse_tree.tree String_map.t ->
  (string * String_map.key * string * Parse_tree.tree, String_map.key,
   Parse_tree.tree, unit, Parse_tree.tree)
  obj Dyp.dyplexbuf -> (Parse_tree.tree * string) list


