
let _ =
  if "20120619" <> Dyp.version
  then (Printf.fprintf stderr
    "version mismatch, dypgen version 20120619 and dyplib version %s\n" Dyp.version;
  exit 2)

type token =
  | EOF
  | RBRACK
  | LBRACK
  | RPAREN
  | LPAREN
  | IN
  | DEFINE
  | SEMICOLON
  | COLONCOLON
  | COLONEQUAL
  | EQUAL
  | COMMA
  | TOKEN of (string)
  | INT of (int)
  | LIDENT of (string)
  | UIDENT of (string)

module Dyp_symbols =
struct
  let get_token_name t = match t with
    | COLONCOLON -> 0
    | COLONEQUAL -> 1
    | COMMA -> 2
    | DEFINE -> 3
    | EOF -> 4
    | EQUAL -> 5
    | IN -> 6
    | INT _ -> 7
    | LBRACK -> 8
    | LIDENT _ -> 9
    | LPAREN -> 10
    | RBRACK -> 11
    | RPAREN -> 12
    | SEMICOLON -> 13
    | TOKEN _ -> 14
    | UIDENT _ -> 15
  let str_token t = match t with
    | COLONCOLON -> "COLONCOLON"
    | COLONEQUAL -> "COLONEQUAL"
    | COMMA -> "COMMA"
    | DEFINE -> "DEFINE"
    | EOF -> "EOF"
    | EQUAL -> "EQUAL"
    | IN -> "IN"
    | INT _ -> "INT"
    | LBRACK -> "LBRACK"
    | LIDENT _ -> "LIDENT"
    | LPAREN -> "LPAREN"
    | RBRACK -> "RBRACK"
    | RPAREN -> "RPAREN"
    | SEMICOLON -> "SEMICOLON"
    | TOKEN _ -> "TOKEN"
    | UIDENT _ -> "UIDENT"
  let ter_string_list = [
      ("COLONCOLON",0);
      ("COLONEQUAL",1);
      ("COMMA",2);
      ("DEFINE",3);
      ("EOF",4);
      ("EQUAL",5);
      ("IN",6);
      ("INT",7);
      ("LBRACK",8);
      ("LIDENT",9);
      ("LPAREN",10);
      ("RBRACK",11);
      ("RPAREN",12);
      ("SEMICOLON",13);
      ("TOKEN",14);
      ("UIDENT",15);]
end

type ('dypgen__Obj_define_in, 'dypgen__Obj_expr, 'dypgen__Obj_rhs) obj =
  | Lexeme_matched of string
  | Obj_COLONCOLON
  | Obj_COLONEQUAL
  | Obj_COMMA
  | Obj_DEFINE
  | Obj_EOF
  | Obj_EQUAL
  | Obj_IN
  | Obj_INT of (int)
  | Obj_LBRACK
  | Obj_LIDENT of (string)
  | Obj_LPAREN
  | Obj_RBRACK
  | Obj_RPAREN
  | Obj_SEMICOLON
  | Obj_TOKEN of (string)
  | Obj_UIDENT of (string)
  | Obj_define_in of 'dypgen__Obj_define_in
  | Obj_expr of 'dypgen__Obj_expr
  | Obj_main of (Parse_tree.expr)
  | Obj_rhs of 'dypgen__Obj_rhs

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"COLONCOLON";
    "COLONEQUAL";
    "COMMA";
    "DEFINE";
    "EOF";
    "EQUAL";
    "IN";
    "INT";
    "LBRACK";
    "LIDENT";
    "LPAREN";
    "RBRACK";
    "RPAREN";
    "SEMICOLON";
    "TOKEN";
    "UIDENT"|]
  let nt_cons_list =
  [
    ("define_in",5);
    ("expr",6);
    ("main",7);
    ("rhs",8)]
  let str_cons o = match o with
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_INT _ -> "Obj_INT"
    | Obj_LIDENT _ -> "Obj_LIDENT"
    | Obj_TOKEN _ -> "Obj_TOKEN"
    | Obj_UIDENT _ -> "Obj_UIDENT"
    | Obj_define_in _ -> "Obj_define_in"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | Obj_rhs _ -> "Obj_rhs"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Lexeme_matched";
    "Obj_INT";
    "Obj_LIDENT";
    "Obj_TOKEN";
    "Obj_UIDENT";
    "Obj_define_in";
    "Obj_expr";
    "Obj_main";
    "Obj_rhs";
    "";
    "";
    "";
    "";
    "";
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
    | COLONCOLON -> Obj_COLONCOLON
    | COLONEQUAL -> Obj_COLONEQUAL
    | COMMA -> Obj_COMMA
    | DEFINE -> Obj_DEFINE
    | EOF -> Obj_EOF
    | EQUAL -> Obj_EQUAL
    | IN -> Obj_IN
    | INT x -> Obj_INT x
    | LBRACK -> Obj_LBRACK
    | LIDENT x -> Obj_LIDENT x
    | LPAREN -> Obj_LPAREN
    | RBRACK -> Obj_RBRACK
    | RPAREN -> Obj_RPAREN
    | SEMICOLON -> Obj_SEMICOLON
    | TOKEN x -> Obj_TOKEN x
    | UIDENT x -> Obj_UIDENT x
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

let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_INT = Dyp.Tools.keep_zero
let dyp_merge_Obj_LIDENT = Dyp.Tools.keep_zero
let dyp_merge_Obj_TOKEN = Dyp.Tools.keep_zero
let dyp_merge_Obj_UIDENT = Dyp.Tools.keep_zero
let dyp_merge_Obj_define_in = Dyp.Tools.keep_zero
let dyp_merge_Obj_expr = Dyp.Tools.keep_zero
let dyp_merge_Obj_main = Dyp.Tools.keep_zero
let dyp_merge_Obj_rhs = Dyp.Tools.keep_zero
let dyp_merge = Dyp.keep_one
let dypgen_match_length = `shortest
let dypgen_choose_token = `first
let dypgen_keep_data = `both
let dypgen_use_rule_order = false
let dypgen_use_all_actions = false

# 3 "parser.dyp"
 open Parse_tree
open Dyp

let () = dypgen_verbose := 1

let get_token_name s = match s with
  | "[" -> "LBRACK"
  | "]" -> "RBRACK"
  | "::" -> "COLONCOLON"
  | ";" -> "SEMICOLON"
  | _ -> failwith "get_token_name"

let a_define_in dyp (s,ol,e) =
  let f o =
    match o with
      | Nt (s,_) -> Non_ter (s,No_priority)
      | Token s -> Ter (get_token_name s)
  in
  let rule  = s,(List.map f ol),"default_priority",[] in
  let action = (fun _ avl ->
    let f2 env o av = match o with
      | Nt (_,var_name) -> String_map.add var_name av env
      | _ -> env
    in
    let f3 av = match av with
      | Obj_expr exp -> exp
      | _ -> Int 0
    in
    let avl = List.map f3 avl in
    let env = List.fold_left2 f2 String_map.empty ol avl in
    Obj_expr (substitute env e), [])
  in rule, action

let _ = () (* dummy line to improve OCaml error location *)
# 255                "parser_temp.ml"
let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "EOF"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 262                "parser_temp.ml"
 as _1)); _2] -> Obj_main 
# 44 "parser.dyp"
(
                ( _1 ):(Parse_tree.expr))
# 267                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "INT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_INT  (
(_:(int))
# 275                "parser_temp.ml"
 as _1)] -> Obj_expr 
# 47 "parser.dyp"
(
        ( Int _1 ):'dypgen__Obj_expr)
# 280                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "LPAREN";Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "COMMA";Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "RPAREN"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 288                "parser_temp.ml"
 as _2)); _3;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 291                "parser_temp.ml"
 as _4)); _5] -> Obj_expr 
# 48 "parser.dyp"
(
                                  ( Pair (_2,_4) ):'dypgen__Obj_expr)
# 296                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "UIDENT";Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_UIDENT  (
(_:(string))
# 304                "parser_temp.ml"
 as _1);Obj_expr ( (
(_:'dypgen__Obj_expr)
# 307                "parser_temp.ml"
 as _2))] -> Obj_expr 
# 50 "parser.dyp"
(
    ( match _2 with
        | Pair (a,b) -> Cons (_1,(2,[a;b]))
        | exp -> Cons (_1,(1,[exp])) ):'dypgen__Obj_expr)
# 314                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "UIDENT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_UIDENT  (
(_:(string))
# 322                "parser_temp.ml"
 as _1)] -> Obj_expr 
# 53 "parser.dyp"
(
           ( Cons (_1,(0,[])) ):'dypgen__Obj_expr)
# 327                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "LIDENT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:(string))
# 335                "parser_temp.ml"
 as _1)] -> Obj_expr 
# 54 "parser.dyp"
(
           ( Lident _1 ):'dypgen__Obj_expr)
# 340                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("define_in",Dyp.No_priority );Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_define_in ( (
(_:'dypgen__Obj_define_in)
# 348                "parser_temp.ml"
 as _1));Obj_expr ( (
(_:'dypgen__Obj_expr)
# 351                "parser_temp.ml"
 as _2))] -> Obj_expr 
# 55 "parser.dyp"
(
                   ( _2 ):'dypgen__Obj_expr)
# 356                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("define_in",[Dyp.Ter "DEFINE";Dyp.Ter "LIDENT";Dyp.Ter "COLONEQUAL";Dyp.Non_ter ("rhs",Dyp.No_priority );Dyp.Ter "EQUAL";Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Ter "IN"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ _1;Obj_LIDENT  (
(_:(string))
# 364                "parser_temp.ml"
 as _2); _3;Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 367                "parser_temp.ml"
 as _4)); _5;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 370                "parser_temp.ml"
 as _6)); _7] ->  let res = 
# 59 "parser.dyp"
(
    ( (), [ Add_rules [a_define_in dyp (_2,_4,_6)];
      Bind_to_cons [_2,"Obj_expr"]] ):'dypgen__Obj_define_in * ('t,'obj,'gd,'ld,'l) Dyp.dyp_action list)
# 376                "parser_temp.ml"
  in Obj_define_in(fst res), snd res
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "LIDENT";Dyp.Ter "LPAREN";Dyp.Ter "LIDENT";Dyp.Ter "RPAREN"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:(string))
# 385                "parser_temp.ml"
 as _1); _2;Obj_LIDENT  (
(_:(string))
# 388                "parser_temp.ml"
 as _3); _4] -> Obj_rhs 
# 63 "parser.dyp"
(
                                ( [Nt (_1,_3)] ):'dypgen__Obj_rhs)
# 393                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "TOKEN"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_TOKEN  (
(_:(string))
# 401                "parser_temp.ml"
 as _1)] -> Obj_rhs 
# 64 "parser.dyp"
(
          ( [Token _1] ):'dypgen__Obj_rhs)
# 406                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "LIDENT";Dyp.Ter "LPAREN";Dyp.Ter "LIDENT";Dyp.Ter "RPAREN";Dyp.Non_ter ("rhs",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:(string))
# 414                "parser_temp.ml"
 as _1); _2;Obj_LIDENT  (
(_:(string))
# 417                "parser_temp.ml"
 as _3); _4;Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 420                "parser_temp.ml"
 as _5))] -> Obj_rhs 
# 65 "parser.dyp"
(
                                    ( (Nt (_1,_3))::_5 ):'dypgen__Obj_rhs)
# 425                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "TOKEN";Dyp.Non_ter ("rhs",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_TOKEN  (
(_:(string))
# 433                "parser_temp.ml"
 as _1);Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 436                "parser_temp.ml"
 as _2))] -> Obj_rhs 
# 66 "parser.dyp"
(
              ( (Token _1)::_2 ):'dypgen__Obj_rhs)
# 441                "parser_temp.ml"
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
let dyp_merge_Obj_LIDENT l =
  match dyp_merge_Obj_LIDENT l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_TOKEN l =
  match dyp_merge_Obj_TOKEN l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_UIDENT l =
  match dyp_merge_Obj_UIDENT l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_define_in l =
  match dyp_merge_Obj_define_in l with
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
let dyp_merge_Obj_rhs l =
  match dyp_merge_Obj_rhs l with
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
  let f1 (o,gd,ld) = match o with Obj_LIDENT ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_LIDENT"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_LIDENT l in
  let f2 o = Obj_LIDENT o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_TOKEN ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_TOKEN"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_TOKEN l in
  let f2 o = Obj_TOKEN o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_UIDENT ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_UIDENT"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_UIDENT l in
  let f2 o = Obj_UIDENT o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_define_in ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_define_in"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_define_in l in
  let f2 o = Obj_define_in o in
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
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_rhs ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_rhs"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_rhs l in
  let f2 o = Obj_rhs o in
  (List.map f2 ol, gd, ld)))]



let __dypgen_test_cons () =  [|
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_INT _ -> true | _ -> false);
  (fun x -> match x with Obj_LIDENT _ -> true | _ -> false);
  (fun x -> match x with Obj_TOKEN _ -> true | _ -> false);
  (fun x -> match x with Obj_UIDENT _ -> true | _ -> false);
  (fun x -> match x with Obj_define_in _ -> true | _ -> false);
  (fun x -> match x with Obj_expr _ -> true | _ -> false);
  (fun x -> match x with Obj_main _ -> true | _ -> false);
  (fun x -> match x with Obj_rhs _ -> true | _ -> false)|]

let __dypgen_dummy_marker_2 = ()
let pp () = Dyp.make_parser
  __dypgen_ra_list Dyp_priority_data.relations global_data local_data
  (Dyp.Tools.make_nt_cons_map Dyp_symbols_array.nt_cons_list)
  Dyp_symbols_array.entry_points
  
  false 16 false
  
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

