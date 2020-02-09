

val pp :
  unit ->
  (unit,
   [  `Dypgen__dummy_obj_cons
    | `Lexeme_matched of string
    | `Obj___dypgen_layout
    | `Obj_expr of int
    | `Obj_main of int ],
   unit, unit, 'a Dyp.dyplexbuf)
  Dyp.parser_pilot

val main :
  ?global_data:unit ->
  ?local_data:unit ->
  [  `Dypgen__dummy_obj_cons
   | `Lexeme_matched of string
   | `Obj___dypgen_layout
   | `Obj_expr of int
   | `Obj_main of int ]
  Dyp.dyplexbuf -> (int * string) list


