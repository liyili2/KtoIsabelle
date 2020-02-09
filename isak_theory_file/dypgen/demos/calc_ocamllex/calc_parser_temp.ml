
let _ =
  if "20120619" <> Dyp.version
  then (Printf.fprintf stderr
    "version mismatch, dypgen version 20120619 and dyplib version %s\n" Dyp.version;
  exit 2)

type token =
  | EOL
  | DIV
  | TIMES
  | MINUS
  | PLUS
  | INT of (int)
  | RPAREN
  | LPAREN

module Dyp_symbols =
struct
  let get_token_name t = match t with
    | DIV -> 0
    | EOL -> 1
    | INT _ -> 2
    | LPAREN -> 3
    | MINUS -> 4
    | PLUS -> 5
    | RPAREN -> 6
    | TIMES -> 7
  let str_token t = match t with
    | DIV -> "DIV"
    | EOL -> "EOL"
    | INT _ -> "INT"
    | LPAREN -> "LPAREN"
    | MINUS -> "MINUS"
    | PLUS -> "PLUS"
    | RPAREN -> "RPAREN"
    | TIMES -> "TIMES"
  let ter_string_list = [
      ("DIV",0);
      ("EOL",1);
      ("INT",2);
      ("LPAREN",3);
      ("MINUS",4);
      ("PLUS",5);
      ("RPAREN",6);
      ("TIMES",7);]
end

type ('dypgen__Obj_expr, 'dypgen__Obj_main) obj =
  | Lexeme_matched of string
  | Obj_DIV
  | Obj_EOL
  | Obj_INT of (int)
  | Obj_LPAREN
  | Obj_MINUS
  | Obj_PLUS
  | Obj_RPAREN
  | Obj_TIMES
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of 'dypgen__Obj_main

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"DIV";
    "EOL";
    "INT";
    "LPAREN";
    "MINUS";
    "PLUS";
    "RPAREN";
    "TIMES"|]
  let nt_cons_list =
  [
    ("expr",2);
    ("main",3)]
  let str_cons o = match o with
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_INT _ -> "Obj_INT"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Lexeme_matched";
    "Obj_INT";
    "Obj_expr";
    "Obj_main";
    "";
    "";
    "";
    "";
    "";
    "";
    "";
  |]
  let entry_points = [
    "main";]
end

let dypgen_lexbuf_position lexbuf =
  (lexbuf.Lexing.lex_start_p,lexbuf.Lexing.lex_curr_p)

module Dyp_aux_functions =
struct
  let get_token_value t = match t with
    | DIV -> Obj_DIV
    | EOL -> Obj_EOL
    | INT x -> Obj_INT x
    | LPAREN -> Obj_LPAREN
    | MINUS -> Obj_MINUS
    | PLUS -> Obj_PLUS
    | RPAREN -> Obj_RPAREN
    | TIMES -> Obj_TIMES
  let cons_table = Dyp.Tools.hashtbl_of_array Dyp_symbols_array.cons_array
end

module Dyp_priority_data =
struct
  let relations = [
    ["pi";"pt";"pp";];
  ]
end

let global_data = ()
let local_data = ()
let global_data_equal = (==)
let local_data_equal = (==)

let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_INT = Dyp.Tools.keep_zero
let dyp_merge_Obj_expr = Dyp.Tools.keep_zero
let dyp_merge_Obj_main = Dyp.Tools.keep_zero
let dyp_merge = Dyp.keep_one
let dypgen_match_length = `shortest
let dypgen_choose_token = `first
let dypgen_keep_data = `both
let dypgen_use_rule_order = false
let dypgen_use_all_actions = false

let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "EOL"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 147                "calc_parser_temp.ml"
 as _1)); _2] -> Obj_main 
# 8 "calc_parser.dyp"
(
                ( _1 ):'dypgen__Obj_main)
# 152                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "INT"],"pi",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_INT  (
(_:(int))
# 160                "calc_parser_temp.ml"
 as _1)] -> Obj_expr 
# 11 "calc_parser.dyp"
(
                               ( _1 ):'dypgen__Obj_expr)
# 165                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "MINUS";Dyp.Non_ter ("expr",Dyp.Eq_priority "pi")],"pi",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 173                "calc_parser_temp.ml"
 as _2))] -> Obj_expr 
# 12 "calc_parser.dyp"
(
                               ( -_2 ):'dypgen__Obj_expr)
# 178                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "LPAREN";Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "RPAREN"],"pi",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 186                "calc_parser_temp.ml"
 as _2)); _3] -> Obj_expr 
# 13 "calc_parser.dyp"
(
                               ( _2 ):'dypgen__Obj_expr)
# 191                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.Lesseq_priority "pp");Dyp.Ter "PLUS";Dyp.Non_ter ("expr",Dyp.Less_priority "pp")],"pp",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 199                "calc_parser_temp.ml"
 as _1)); _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 202                "calc_parser_temp.ml"
 as _3))] -> Obj_expr 
# 14 "calc_parser.dyp"
(
                               ( _1 + _3 ):'dypgen__Obj_expr)
# 207                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.Lesseq_priority "pp");Dyp.Ter "MINUS";Dyp.Non_ter ("expr",Dyp.Less_priority "pp")],"pp",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 215                "calc_parser_temp.ml"
 as _1)); _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 218                "calc_parser_temp.ml"
 as _3))] -> Obj_expr 
# 15 "calc_parser.dyp"
(
                               ( _1 - _3 ):'dypgen__Obj_expr)
# 223                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.Lesseq_priority "pt");Dyp.Ter "TIMES";Dyp.Non_ter ("expr",Dyp.Less_priority "pt")],"pt",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 231                "calc_parser_temp.ml"
 as _1)); _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 234                "calc_parser_temp.ml"
 as _3))] -> Obj_expr 
# 16 "calc_parser.dyp"
(
                               ( _1 * _3 ):'dypgen__Obj_expr)
# 239                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("expr",Dyp.Lesseq_priority "pt");Dyp.Ter "DIV";Dyp.Non_ter ("expr",Dyp.Less_priority "pt")],"pt",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 247                "calc_parser_temp.ml"
 as _1)); _2;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 250                "calc_parser_temp.ml"
 as _3))] -> Obj_expr 
# 17 "calc_parser.dyp"
(
                               ( _1 / _3 ):'dypgen__Obj_expr)
# 255                "calc_parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])],

(["dummy_entry",Dyp.RE_Eof_char],
[0,(fun _ -> Lexeme_matched "")]),

[]

let __dypgen_regexp_decl = []

let dyp_merge_Lexeme_matched l =
  match dyp_merge_Lexeme_matched l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_INT l =
  match dyp_merge_Obj_INT l with
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
  let f1 (o,gd,ld) = match o with Lexeme_matched ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Lexeme_matched"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Lexeme_matched l in
  let f2 o = Lexeme_matched o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_INT ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_INT"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_INT l in
  let f2 o = Obj_INT o in
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
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_INT _ -> true | _ -> false);
  (fun x -> match x with Obj_expr _ -> true | _ -> false);
  (fun x -> match x with Obj_main _ -> true | _ -> false)|]

let __dypgen_dummy_marker_2 = ()
let pp () = Dyp.make_parser
  __dypgen_ra_list Dyp_priority_data.relations global_data local_data
  (Dyp.Tools.make_nt_cons_map Dyp_symbols_array.nt_cons_list)
  Dyp_symbols_array.entry_points
  
  false 8 true
  
  Dyp_aux_functions.get_token_value
  Dyp_symbols.get_token_name Dyp_symbols.str_token
  global_data_equal local_data_equal (__dypgen_test_cons ())
  Dyp_symbols_array.str_cons
  Dyp_symbols_array.cons_array Dyp_aux_functions.cons_table
  (Dyp.Tools.array_of_list __dypgen_merge_list)
  dypgen_lexbuf_position __dypgen_regexp_decl __dypgen_main_lexer
  __dypgen_aux_lexer Dyp_symbols.ter_string_list
  (fun lexbuf -> Lexeme_matched (Dyp.lexeme lexbuf))
  false


let __dypgen_dummy_marker_5 = ()

let __dypgen_dummy_marker_3 = ()

let main ?(global_data=global_data) ?(local_data=local_data) f lexbuf =
  let pf = Dyp.parse (pp ()) "main" ~global_data:global_data
    ~local_data:local_data ~match_len:dypgen_match_length
    ~keep_data:dypgen_keep_data
    ~use_rule_order:dypgen_use_rule_order
    ~use_all_actions:dypgen_use_all_actions
    ~lexpos:dypgen_lexbuf_position f lexbuf in
  let aux1 (o,p) = match o with
    | Obj_main r -> (r,p)
    | _ -> failwith "Wrong type for entry result" in
  List.map aux1 pf


let __dypgen_dummy_marker_4 = ()

