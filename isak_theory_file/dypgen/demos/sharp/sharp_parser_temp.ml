
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
      ("__dypgen_layout",0);]
end

type ('dypgen__Inh_dypgen__early_action_0, 'dypgen__Inh_dypgen__early_action_1, 'dypgen__Obj_dypgen__early_action_0, 'dypgen__Obj_dypgen__early_action_1, 'dypgen__Obj_dypgen__epsilon, 'dypgen__Obj_expr, 'dypgen__Obj_main) obj =
  | Inh_dypgen__early_action_0 of 'dypgen__Inh_dypgen__early_action_0
  | Inh_dypgen__early_action_1 of 'dypgen__Inh_dypgen__early_action_1
  | Lexeme_matched of string
  | Obj___dypgen_layout
  | Obj_dypgen__early_action_0 of 'dypgen__Obj_dypgen__early_action_0
  | Obj_dypgen__early_action_1 of 'dypgen__Obj_dypgen__early_action_1
  | Obj_dypgen__epsilon of 'dypgen__Obj_dypgen__epsilon
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main
  | Dypgen__dummy_obj_cons

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"__dypgen_layout"|]
  let nt_cons_list =
  [
    ("0_1",5);
    ("dypgen__early_action_0",3);
    ("dypgen__early_action_1",4);
    ("expr",6);
    ("main",7)]
  let str_cons o = match o with
    | Inh_dypgen__early_action_0 _ -> "Inh_dypgen__early_action_0"
    | Inh_dypgen__early_action_1 _ -> "Inh_dypgen__early_action_1"
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_dypgen__early_action_0 _ -> "Obj_dypgen__early_action_0"
    | Obj_dypgen__early_action_1 _ -> "Obj_dypgen__early_action_1"
    | Obj_dypgen__epsilon _ -> "Obj_dypgen__epsilon"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Inh_dypgen__early_action_0";
    "Inh_dypgen__early_action_1";
    "Lexeme_matched";
    "Obj_dypgen__early_action_0";
    "Obj_dypgen__early_action_1";
    "Obj_dypgen__epsilon";
    "Obj_expr";
    "Obj_main";
    "";
  |]
  let entry_points = [
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
    ["p1";"p2";];
  ]
end

let global_data = ()
let local_data = ()
let global_data_equal = (==)
let local_data_equal = (==)

let dyp_merge_Inh_dypgen__early_action_0 = Dyp.Tools.keep_zero
let dyp_merge_Inh_dypgen__early_action_1 = Dyp.Tools.keep_zero
let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_dypgen__early_action_0 = Dyp.Tools.keep_zero
let dyp_merge_Obj_dypgen__early_action_1 = Dyp.Tools.keep_zero
let dyp_merge_Obj_dypgen__epsilon = Dyp.Tools.keep_zero
let dyp_merge_Obj_expr = Dyp.Tools.keep_zero
let dyp_merge_Obj_main = Dyp.Tools.keep_zero
let dyp_merge = Dyp.keep_one
let dypgen_match_length = `shortest
let dypgen_choose_token = `first
let dypgen_keep_data = `both
let dypgen_use_rule_order = false
let dypgen_use_all_actions = false

# 1 "sharp_parser.dyp"

open Dyp

let r_sharp = ("expr", [
  Non_ter ("expr",Lesseq_priority "p1");
  Regexp (RE_String "#");
  Non_ter ("expr",Lesseq_priority "p2")
  ],"p1",[])
(* E -> E # E *)

let action_plus = (fun dyp l ->
  let x1, x2 = match l with
    | [Obj_expr x1;_;Obj_expr x2] -> x1, x2
    | _ -> failwith "action_plus"
  in
  (Obj_expr (x1+x2)), [Dont_shift])

let action_time = (fun dyp l ->
  let x1, x2 = match l with
    | [Obj_expr x1;_;Obj_expr x2] -> x1, x2
    | _ -> failwith "action_plus"
  in
  (Obj_expr (x1*x2)), [Dont_shift])

let _ = () (* dummy line to improve OCaml error location *)
# 126                "sharp_parser_temp.ml"
let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "\n")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 133                "sharp_parser_temp.ml"
 as _1)); Lexeme_matched _2] -> Obj_main 
# 31 "sharp_parser.dyp"
(
                ( _1 ):'dypgen__Obj_main)
# 138                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_Plus (Dyp.RE_Char_set [('0','9')]))],"p1",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Obj_expr 
# 34 "sharp_parser.dyp"
(
                ( int_of_string _1 ):'dypgen__Obj_expr)
# 148                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_String "(");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String ")")],"p1",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 156                "sharp_parser_temp.ml"
 as _2)); Lexeme_matched _3] -> Obj_expr 
# 35 "sharp_parser.dyp"
(
                 ( _2 ):'dypgen__Obj_expr)
# 161                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("0_1",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "&+");Dyp.Non_ter ("dypgen__early_action_1",Dyp.No_priority );Dyp.Non_ter ("expr",Dyp.No_priority )],"p2",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_dypgen__early_action_1 ( (
(_:'dypgen__Obj_dypgen__early_action_1)
# 169                "sharp_parser_temp.ml"
 as _2));Obj_expr ( (
(_:'dypgen__Obj_expr)
# 172                "sharp_parser_temp.ml"
 as _3))] -> Obj_expr 
# 36 "sharp_parser.dyp"
(
                                                               ( _3 ):'dypgen__Obj_expr)
# 177                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[3,
(fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_inh_val (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Inh_dypgen__early_action_1 
(
((_1)):'dypgen__Inh_dypgen__early_action_1)
# 184                "sharp_parser_temp.ml"
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl)])
;
(("dypgen__early_action_1",[],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Inh_dypgen__early_action_1( (
(_:string)
# 191                "sharp_parser_temp.ml"
 as _1))] ->  let res = 
# 36 "sharp_parser.dyp"
(
            ( (), [Add_rules [(r_sharp, action_plus)]] ):'dypgen__Obj_dypgen__early_action_1 * ('t,'obj,'gd,'ld,'l) Dyp.dyp_action list)
# 196                "sharp_parser_temp.ml"
  in Obj_dypgen__early_action_1(fst res), snd res
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("0_1",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "&*");Dyp.Non_ter ("dypgen__early_action_0",Dyp.No_priority );Dyp.Non_ter ("expr",Dyp.No_priority )],"p2",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_dypgen__early_action_0 ( (
(_:'dypgen__Obj_dypgen__early_action_0)
# 205                "sharp_parser_temp.ml"
 as _2));Obj_expr ( (
(_:'dypgen__Obj_expr)
# 208                "sharp_parser_temp.ml"
 as _3))] -> Obj_expr 
# 37 "sharp_parser.dyp"
(
                                                               ( _3 ):'dypgen__Obj_expr)
# 213                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[3,
(fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_inh_val (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Inh_dypgen__early_action_0 
(
((_1)):'dypgen__Inh_dypgen__early_action_0)
# 220                "sharp_parser_temp.ml"
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl)])
;
(("dypgen__early_action_0",[],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Inh_dypgen__early_action_0( (
(_:string)
# 227                "sharp_parser_temp.ml"
 as _1))] ->  let res = 
# 37 "sharp_parser.dyp"
(
            ( (), [Add_rules [(r_sharp, action_time)]] ):'dypgen__Obj_dypgen__early_action_0 * ('t,'obj,'gd,'ld,'l) Dyp.dyp_action list)
# 232                "sharp_parser_temp.ml"
  in Obj_dypgen__early_action_0(fst res), snd res
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("0_1",[],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [] -> Obj_dypgen__epsilon 
(
():'dypgen__Obj_dypgen__epsilon)
# 242                "sharp_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])],

([
  ("__dypgen_layout",(Dyp.RE_Char_set [(' ',' ');('\t','\t')]))],
[
  0,((fun lexbuf -> Obj___dypgen_layout))]),

[]

let __dypgen_regexp_decl = []

let dyp_merge_Inh_dypgen__early_action_0 l =
  match dyp_merge_Inh_dypgen__early_action_0 l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Inh_dypgen__early_action_1 l =
  match dyp_merge_Inh_dypgen__early_action_1 l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Lexeme_matched l =
  match dyp_merge_Lexeme_matched l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_dypgen__early_action_0 l =
  match dyp_merge_Obj_dypgen__early_action_0 l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_dypgen__early_action_1 l =
  match dyp_merge_Obj_dypgen__early_action_1 l with
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
  let f1 (o,gd,ld) = match o with Inh_dypgen__early_action_1 ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Inh_dypgen__early_action_1"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Inh_dypgen__early_action_1 l in
  let f2 o = Inh_dypgen__early_action_1 o in
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
  let f1 (o,gd,ld) = match o with Obj_dypgen__early_action_0 ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_dypgen__early_action_0"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_dypgen__early_action_0 l in
  let f2 o = Obj_dypgen__early_action_0 o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_dypgen__early_action_1 ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_dypgen__early_action_1"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_dypgen__early_action_1 l in
  let f2 o = Obj_dypgen__early_action_1 o in
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
  (fun x -> match x with Inh_dypgen__early_action_1 _ -> true | _ -> false);
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_dypgen__early_action_0 _ -> true | _ -> false);
  (fun x -> match x with Obj_dypgen__early_action_1 _ -> true | _ -> false);
  (fun x -> match x with Obj_dypgen__epsilon _ -> true | _ -> false);
  (fun x -> match x with Obj_expr _ -> true | _ -> false);
  (fun x -> match x with Obj_main _ -> true | _ -> false)|]

let __dypgen_dummy_marker_2 = ()
let pp () = Dyp.make_parser
  __dypgen_ra_list Dyp_priority_data.relations global_data local_data
  (Dyp.Tools.make_nt_cons_map Dyp_symbols_array.nt_cons_list)
  Dyp_symbols_array.entry_points
  
  false 1 true
  
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

