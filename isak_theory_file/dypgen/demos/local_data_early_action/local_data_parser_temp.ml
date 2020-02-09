
let _ =
  if "20120619" <> Dyp.version
  then (Printf.fprintf stderr
    "version mismatch, dypgen version 20120619 and dyplib version %s\n" Dyp.version;
  exit 2)

module Dyp_symbols =
struct
  let get_token_name () = 0
  let str_token _ = failwith "str_token must not be called with dypgen lexers"
  let ter_string_list = [
      ("IDENT",0);
      ("__dypgen_layout",1);]
end

type ('dypgen__Inh_dypgen__early_action_0, 'dypgen__Obj_IDENT, 'dypgen__Obj_dypgen__early_action_0, 'dypgen__Obj_dypgen__epsilon, 'dypgen__Obj_main) obj =
  | Inh_dypgen__early_action_0 of 'dypgen__Inh_dypgen__early_action_0
  | Lexeme_matched of string
  | Obj_IDENT of 'dypgen__Obj_IDENT
  | Obj___dypgen_layout
  | Obj_dypgen__early_action_0 of 'dypgen__Obj_dypgen__early_action_0
  | Obj_dypgen__epsilon of 'dypgen__Obj_dypgen__epsilon
  | Obj_expr of (Parse_tree.tree)
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"IDENT";
    "__dypgen_layout"|]
  let nt_cons_list =
  [
    ("0_1",4);
    ("dypgen__early_action_0",3);
    ("expr",5);
    ("main",6)]
  let str_cons o = match o with
    | Inh_dypgen__early_action_0 _ -> "Inh_dypgen__early_action_0"
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_IDENT _ -> "Obj_IDENT"
    | Obj_dypgen__early_action_0 _ -> "Obj_dypgen__early_action_0"
    | Obj_dypgen__epsilon _ -> "Obj_dypgen__epsilon"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Inh_dypgen__early_action_0";
    "Lexeme_matched";
    "Obj_IDENT";
    "Obj_dypgen__early_action_0";
    "Obj_dypgen__epsilon";
    "Obj_expr";
    "Obj_main";
    "";
  |]
  let entry_points = [
    "expr";
    "main";]
end

let dypgen_lexbuf_position lexbuf = Dyp.dyplex_lexbuf_position lexbuf

module Dyp_aux_functions =
struct
  let get_token_value _ = Dypgen__dummy_obj_cons
  let cons_table = Dyp.Tools.hashtbl_of_array Dyp_symbols_array.cons_array
end

module Dyp_priority_data =
struct
  let relations = [
  ]
end

let global_data = ()
let local_data = ()
let global_data_equal = (==)
let local_data_equal = (==)

let dyp_merge_Inh_dypgen__early_action_0 = Dyp.Tools.keep_zero
let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_IDENT = Dyp.Tools.keep_zero
let dyp_merge_Obj_dypgen__early_action_0 = Dyp.Tools.keep_zero
let dyp_merge_Obj_dypgen__epsilon = Dyp.Tools.keep_zero
let dyp_merge_Obj_expr = Dyp.Tools.keep_zero
let dyp_merge_Obj_main = Dyp.Tools.keep_zero
let dyp_merge = Dyp.keep_one
let dypgen_match_length = `shortest
let dypgen_choose_token = `first
let dypgen_keep_data = `both
let dypgen_use_rule_order = false
let dypgen_use_all_actions = false

# 1 "local_data_parser.dyp"

open Parse_tree
open Dyp

module OrdString =
struct
  type t = string
  let compare = Pervasives.compare
end
module String_map = Map.Make(OrdString)

let is_bound map id =
  try let _ = String_map.find id map in true
  with Not_found -> false

let insert_binding map id expr =
  String_map.add id expr map

let print_map map =
  print_endline "symbol table :";
  let f s t = print_string (s^" bound to "); print_tree t in
  if String_map.is_empty map then print_endline " empty"
  else String_map.iter f map

let local_data = String_map.empty
let local_data_equal ld1 ld2 = String_map.equal (=) ld1 ld2

let dyp_merge = keep_all

let binding dyp name exp =
  Binding (name,exp),
  [Local_data (insert_binding dyp.local_data name exp)]

let _ = () (* dummy line to improve OCaml error location *)
# 132                "local_data_parser_temp.ml"
let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "\n")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 139                "local_data_parser_temp.ml"
 as _1)); Lexeme_matched _2] -> Obj_main 
# 50 "local_data_parser.dyp"
(
                ( _1 ):'dypgen__Obj_main)
# 144                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_Plus (Dyp.RE_Char_set [('0','9')]))],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Obj_expr 
# 52 "local_data_parser.dyp"
(
                        ( Int (int_of_string _1) ):(Parse_tree.tree))
# 154                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "IDENT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_IDENT  (
(_:'dypgen__Obj_IDENT)
# 162                "local_data_parser_temp.ml"
 as _1)] -> Obj_expr 
# 53 "local_data_parser.dyp"
(
                        ( if is_bound dyp.local_data _1 then Ident _1
                          else raise Giveup ):(Parse_tree.tree))
# 168                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_String "(");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String ")")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 176                "local_data_parser_temp.ml"
 as _2)); Lexeme_matched _3] -> Obj_expr 
# 55 "local_data_parser.dyp"
(
                        ( _2 ):(Parse_tree.tree))
# 181                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "+");Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 189                "local_data_parser_temp.ml"
 as _1)); Lexeme_matched _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 192                "local_data_parser_temp.ml"
 as _3))] -> Obj_expr 
# 56 "local_data_parser.dyp"
(
                        ( Plus (_1,_3) ):(Parse_tree.tree))
# 197                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("0_1",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "let");Dyp.Ter "IDENT";Dyp.Regexp (Dyp.RE_String "=");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Non_ter ("dypgen__early_action_0",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "in");Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_IDENT  (
(_:'dypgen__Obj_IDENT)
# 205                "local_data_parser_temp.ml"
 as _2); Lexeme_matched _3;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 208                "local_data_parser_temp.ml"
 as _4));Obj_dypgen__early_action_0 ( (
(_:'dypgen__Obj_dypgen__early_action_0)
# 211                "local_data_parser_temp.ml"
 as _5)); Lexeme_matched _6;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 214                "local_data_parser_temp.ml"
 as _7))] -> Obj_expr 
# 57 "local_data_parser.dyp"
(
                                                             ( Let (_5,_7) ):(Parse_tree.tree))
# 219                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[6,
(fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_inh_val (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_IDENT  (
(_:'dypgen__Obj_IDENT)
# 225                "local_data_parser_temp.ml"
 as _2); Lexeme_matched _3;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 228                "local_data_parser_temp.ml"
 as _4))] -> Inh_dypgen__early_action_0 
(
((_1, _2, _3, _4)):'dypgen__Inh_dypgen__early_action_0)
# 232                "local_data_parser_temp.ml"
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl)])
;
(("dypgen__early_action_0",[],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Inh_dypgen__early_action_0( (
(_:string)
# 239                "local_data_parser_temp.ml"
 as _1),
 (
(_:'dypgen__Obj_IDENT)
# 243                "local_data_parser_temp.ml"
 as _2),
 (
(_:string)
# 247                "local_data_parser_temp.ml"
 as _3),
 (
(_:(Parse_tree.tree))
# 251                "local_data_parser_temp.ml"
 as _4))] ->  let res = 
# 57 "local_data_parser.dyp"
(
                            ( binding dyp _2 _4 ):'dypgen__Obj_dypgen__early_action_0 * ('t,'obj,'gd,'ld,'l) Dyp.dyp_action list)
# 256                "local_data_parser_temp.ml"
  in Obj_dypgen__early_action_0(fst res), snd res
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("0_1",[],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [] -> Obj_dypgen__epsilon 
(
():'dypgen__Obj_dypgen__epsilon)
# 266                "local_data_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])],

([
  ("__dypgen_layout",(Dyp.RE_Char_set [(' ',' ');('\t','\t')]));
  ("IDENT",(Dyp.RE_Seq [Dyp.RE_Name "lowercase";Dyp.RE_Star (Dyp.RE_Name "identchar")]))],
[
  1,((fun lexbuf -> Obj___dypgen_layout));
  0,((fun lexbuf -> Obj_IDENT
# 46 "local_data_parser.dyp"
(
                               ( Dyp.lexeme lexbuf ):'dypgen__Obj_IDENT)
# 279                "local_data_parser_temp.ml"
))]),

[]

let __dypgen_regexp_decl = [
  ("lowercase",(Dyp.RE_Char_set [('a','z');('\223','\246');('\248','\255');('_','_')]));
  ("identchar",(Dyp.RE_Char_set [('A','Z');('a','z');('_','_');('\192','\214');('\216','\246');('\248','\255');('\'','\'');('0','9')]))]

let dyp_merge_Inh_dypgen__early_action_0 l =
  match dyp_merge_Inh_dypgen__early_action_0 l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Lexeme_matched l =
  match dyp_merge_Lexeme_matched l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_IDENT l =
  match dyp_merge_Obj_IDENT l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_dypgen__early_action_0 l =
  match dyp_merge_Obj_dypgen__early_action_0 l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_dypgen__epsilon l =
  match dyp_merge_Obj_dypgen__epsilon l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_expr l =
  match dyp_merge_Obj_expr l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_main l =
  match dyp_merge_Obj_main l with
    | ([],_,_) -> dyp_merge l
    | res -> res

let __dypgen_merge_list = [(fun l -> (
  let f1 (o,gd,ld) = match o with Inh_dypgen__early_action_0 ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Inh_dypgen__early_action_0"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Inh_dypgen__early_action_0 l in
  let f2 o = Inh_dypgen__early_action_0 o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Lexeme_matched ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Lexeme_matched"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Lexeme_matched l in
  let f2 o = Lexeme_matched o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_IDENT ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_IDENT"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_IDENT l in
  let f2 o = Obj_IDENT o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_dypgen__early_action_0 ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_dypgen__early_action_0"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_dypgen__early_action_0 l in
  let f2 o = Obj_dypgen__early_action_0 o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_dypgen__epsilon ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_dypgen__epsilon"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_dypgen__epsilon l in
  let f2 o = Obj_dypgen__epsilon o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_expr ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_expr"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_expr l in
  let f2 o = Obj_expr o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_main ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_main"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_main l in
  let f2 o = Obj_main o in
  (List.map f2 ol, gd, ld)))]



let __dypgen_test_cons () =  [|
  (fun x -> match x with Inh_dypgen__early_action_0 _ -> true | _ -> false);
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_IDENT _ -> true | _ -> false);
  (fun x -> match x with Obj_dypgen__early_action_0 _ -> true | _ -> false);
  (fun x -> match x with Obj_dypgen__epsilon _ -> true | _ -> false);
  (fun x -> match x with Obj_expr _ -> true | _ -> false);
  (fun x -> match x with Obj_main _ -> true | _ -> false)|]

let __dypgen_dummy_marker_2 = ()
let pp () = Dyp.make_parser
  __dypgen_ra_list Dyp_priority_data.relations global_data local_data
  (Dyp.Tools.make_nt_cons_map Dyp_symbols_array.nt_cons_list)
  Dyp_symbols_array.entry_points
  
  false 2 true
  
  Dyp_aux_functions.get_token_value
  Dyp_symbols.get_token_name Dyp_symbols.str_token
  global_data_equal local_data_equal (__dypgen_test_cons ())
  Dyp_symbols_array.str_cons
  Dyp_symbols_array.cons_array Dyp_aux_functions.cons_table
  (Dyp.Tools.array_of_list __dypgen_merge_list)
  dypgen_lexbuf_position __dypgen_regexp_decl __dypgen_main_lexer
  __dypgen_aux_lexer Dyp_symbols.ter_string_list
  (fun lexbuf -> Lexeme_matched (Dyp.lexeme lexbuf))
  true


let __dypgen_dummy_marker_5 = ()

let __dypgen_dummy_marker_3 = ()

let expr ?(global_data=global_data) ?(local_data=local_data) lexbuf =
  let pf = Dyp.lexparse (pp ()) "expr" ~global_data:global_data
    ~local_data:local_data ~match_len:dypgen_match_length
    ~keep_data:dypgen_keep_data
    ~use_rule_order:dypgen_use_rule_order
    ~use_all_actions:dypgen_use_all_actions
    ~choose_token:dypgen_choose_token lexbuf in
  let aux1 (o,p) = match o with
    | Obj_expr r -> (r,p)
    | _ -> failwith "Wrong type for entry result" in
  List.map aux1 pf

let main ?(global_data=global_data) ?(local_data=local_data) lexbuf =
  let pf = Dyp.lexparse (pp ()) "main" ~global_data:global_data
    ~local_data:local_data ~match_len:dypgen_match_length
    ~keep_data:dypgen_keep_data
    ~use_rule_order:dypgen_use_rule_order
    ~use_all_actions:dypgen_use_all_actions
    ~choose_token:dypgen_choose_token lexbuf in
  let aux1 (o,p) = match o with
    | Obj_main r -> (r,p)
    | _ -> failwith "Wrong type for entry result" in
  List.map aux1 pf


let __dypgen_dummy_marker_4 = ()

