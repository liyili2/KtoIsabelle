
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
      ("LIDENT",0);
      ("STRING",1);
      ("UIDENT",2);
      ("__dypgen_layout",3);]
end

type ('dypgen__Lex_string, 'dypgen__Obj_LIDENT, 'dypgen__Obj_STRING, 'dypgen__Obj_UIDENT, 'dypgen__Obj_define_in, 'dypgen__Obj_expr, 'dypgen__Obj_main, 'dypgen__Obj_rhs) obj =
  | Lex_string of 'dypgen__Lex_string
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

module Dyp_symbols_array =
struct
  let token_name_array =
  [|"LIDENT";
    "STRING";
    "UIDENT";
    "__dypgen_layout"|]
  let nt_cons_list =
  [
    ("define_in",5);
    ("expr",6);
    ("main",7);
    ("rhs",8)]
  let str_cons o = match o with
    | Lex_string _ -> "Lex_string"
    | Lexeme_matched _ -> "Lexeme_matched"
    | Obj_LIDENT _ -> "Obj_LIDENT"
    | Obj_STRING _ -> "Obj_STRING"
    | Obj_UIDENT _ -> "Obj_UIDENT"
    | Obj_define_in _ -> "Obj_define_in"
    | Obj_expr _ -> "Obj_expr"
    | Obj_main _ -> "Obj_main"
    | Obj_rhs _ -> "Obj_rhs"
    | _ -> failwith "str_cons, unexpected constructor"
  let cons_array = [|
    "Lex_string";
    "Lexeme_matched";
    "Obj_LIDENT";
    "Obj_STRING";
    "Obj_UIDENT";
    "Obj_define_in";
    "Obj_expr";
    "Obj_main";
    "Obj_rhs";
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
  ]
end

let global_data = ()
let local_data = ()
let global_data_equal = (==)
let local_data_equal = (==)

let dyp_merge_Lex_string = Dyp.Tools.keep_zero
let dyp_merge_Lexeme_matched = Dyp.Tools.keep_zero
let dyp_merge_Obj_LIDENT = Dyp.Tools.keep_zero
let dyp_merge_Obj_STRING = Dyp.Tools.keep_zero
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

let string_buf = Buffer.create 10

let a_define_in dyp (s,ol,e) =
  let f o =
    match o with
      | Nt (s,_) -> Non_ter (s,No_priority)
      | Token s -> Regexp (RE_String s)
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
# 136                "parser_temp.ml"
let __dypgen_ra_list, __dypgen_main_lexer, __dypgen_aux_lexer =
let string  lexbuf =
  match Dyp.lex "string" [] lexbuf with
  | Lex_string x -> (x:'dypgen__Lex_string)
  | _ -> failwith "lexer `string' returned a wrong obj constructor"
in
[
(("main",[Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_Eof_char)],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_expr ( (
(_:'dypgen__Obj_expr)
# 148                "parser_temp.ml"
 as _1)); Lexeme_matched _2] -> Obj_main 
# 55 "parser.dyp"
(
                ( _1 ):'dypgen__Obj_main)
# 153                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_Plus (Dyp.RE_Char_set [('0','9')]))],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1] -> Obj_expr 
# 58 "parser.dyp"
(
               ( Int (int_of_string _1) ):'dypgen__Obj_expr)
# 163                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Regexp (Dyp.RE_String "(");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String ",");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String ")")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 171                "parser_temp.ml"
 as _2)); Lexeme_matched _3;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 174                "parser_temp.ml"
 as _4)); Lexeme_matched _5] -> Obj_expr 
# 59 "parser.dyp"
(
                          ( Pair (_2,_4) ):'dypgen__Obj_expr)
# 179                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "UIDENT";Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_UIDENT  (
(_:'dypgen__Obj_UIDENT)
# 187                "parser_temp.ml"
 as _1);Obj_expr ( (
(_:'dypgen__Obj_expr)
# 190                "parser_temp.ml"
 as _2))] -> Obj_expr 
# 61 "parser.dyp"
(
    ( match _2 with
        | Pair (a,b) -> Cons (_1,(2,[a;b]))
        | exp -> Cons (_1,(1,[exp])) ):'dypgen__Obj_expr)
# 197                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "UIDENT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_UIDENT  (
(_:'dypgen__Obj_UIDENT)
# 205                "parser_temp.ml"
 as _1)] -> Obj_expr 
# 64 "parser.dyp"
(
           ( Cons (_1,(0,[])) ):'dypgen__Obj_expr)
# 210                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Ter "LIDENT"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 218                "parser_temp.ml"
 as _1)] -> Obj_expr 
# 65 "parser.dyp"
(
           ( Lident _1 ):'dypgen__Obj_expr)
# 223                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("expr",[Dyp.Non_ter ("define_in",Dyp.No_priority );Dyp.Non_ter ("expr",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_define_in ( (
(_:'dypgen__Obj_define_in)
# 231                "parser_temp.ml"
 as _1));Obj_expr ( (
(_:'dypgen__Obj_expr)
# 234                "parser_temp.ml"
 as _2))] -> Obj_expr 
# 66 "parser.dyp"
(
                   ( _2 ):'dypgen__Obj_expr)
# 239                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("define_in",[Dyp.Regexp (Dyp.RE_String "define");Dyp.Ter "LIDENT";Dyp.Regexp (Dyp.RE_String ":=");Dyp.Non_ter ("rhs",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "=");Dyp.Non_ter ("expr",Dyp.No_priority );Dyp.Regexp (Dyp.RE_String "in")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [ Lexeme_matched _1;Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 247                "parser_temp.ml"
 as _2); Lexeme_matched _3;Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 250                "parser_temp.ml"
 as _4)); Lexeme_matched _5;Obj_expr ( (
(_:'dypgen__Obj_expr)
# 253                "parser_temp.ml"
 as _6)); Lexeme_matched _7] ->  let res = 
# 70 "parser.dyp"
(
    ( (), [ Add_rules [a_define_in dyp (_2,_4,_6)];
      Bind_to_cons [_2,"Obj_expr"]] ):'dypgen__Obj_define_in * ('t,'obj,'gd,'ld,'l) Dyp.dyp_action list)
# 259                "parser_temp.ml"
  in Obj_define_in(fst res), snd res
 | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "LIDENT";Dyp.Regexp (Dyp.RE_String "(");Dyp.Ter "LIDENT";Dyp.Regexp (Dyp.RE_String ")")],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 268                "parser_temp.ml"
 as _1); Lexeme_matched _2;Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 271                "parser_temp.ml"
 as _3); Lexeme_matched _4] -> Obj_rhs 
# 74 "parser.dyp"
(
                          ( [Nt (_1,_3)] ):'dypgen__Obj_rhs)
# 276                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "STRING"],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_STRING  (
(_:'dypgen__Obj_STRING)
# 284                "parser_temp.ml"
 as _1)] -> Obj_rhs 
# 75 "parser.dyp"
(
           ( [Token _1] ):'dypgen__Obj_rhs)
# 289                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "LIDENT";Dyp.Regexp (Dyp.RE_String "(");Dyp.Ter "LIDENT";Dyp.Regexp (Dyp.RE_String ")");Dyp.Non_ter ("rhs",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 297                "parser_temp.ml"
 as _1); Lexeme_matched _2;Obj_LIDENT  (
(_:'dypgen__Obj_LIDENT)
# 300                "parser_temp.ml"
 as _3); Lexeme_matched _4;Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 303                "parser_temp.ml"
 as _5))] -> Obj_rhs 
# 76 "parser.dyp"
(
                              ( (Nt (_1,_3))::_5 ):'dypgen__Obj_rhs)
# 308                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])
;
(("rhs",[Dyp.Ter "STRING";Dyp.Non_ter ("rhs",Dyp.No_priority )],"default_priority",[]),
Dyp.Dypgen_action (fun __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl ->
(Dyp.Tools.transform_action (fun dyp __dypgen_av_list -> (match (__dypgen_av_list) with [Obj_STRING  (
(_:'dypgen__Obj_STRING)
# 316                "parser_temp.ml"
 as _1);Obj_rhs ( (
(_:'dypgen__Obj_rhs)
# 319                "parser_temp.ml"
 as _2))] -> Obj_rhs 
# 77 "parser.dyp"
(
               ( (Token _1)::_2 ):'dypgen__Obj_rhs)
# 324                "parser_temp.ml"
,[] | _ -> raise Dyp.Giveup))) __dypgen_ol __dypgen_pos __dypgen_posl __dypgen_gd __dypgen_ld __dypgen_lld __dypgen_di __dypgen_p __dypgen_nl),
[])],

([
  ("__dypgen_layout",(Dyp.RE_Alt [Dyp.RE_Name "newline";Dyp.RE_Plus (Dyp.RE_Name "blank")]));
  ("LIDENT",(Dyp.RE_Seq [Dyp.RE_Name "lowercase";Dyp.RE_Star (Dyp.RE_Name "identchar")]));
  ("UIDENT",(Dyp.RE_Seq [Dyp.RE_Name "uppercase";Dyp.RE_Star (Dyp.RE_Name "identchar")]));
  ("STRING",(Dyp.RE_Char '"'))],
[
  3,((fun lexbuf -> Obj___dypgen_layout));
  0,((fun lexbuf -> Obj_LIDENT
# 47 "parser.dyp"
(
                                ( Dyp.lexeme lexbuf ):'dypgen__Obj_LIDENT)
# 339                "parser_temp.ml"
));
  2,((fun lexbuf -> Obj_UIDENT
# 48 "parser.dyp"
(
                                ( Dyp.lexeme lexbuf ):'dypgen__Obj_UIDENT)
# 345                "parser_temp.ml"
));
  1,((fun lexbuf -> Obj_STRING
# 49 "parser.dyp"
(
              ( Buffer.clear string_buf;
      string lexbuf;
      Buffer.contents string_buf ):'dypgen__Obj_STRING)
# 353                "parser_temp.ml"
))]),

[("string",([
    (Dyp.RE_Char '"');
    (Dyp.RE_Char_set [('\000','\255')])],[(fun __dypgen_av_list lexbuf -> (match __dypgen_av_list with [] -> Lex_string
# 41 "parser.dyp"
(
        ( () ):'dypgen__Lex_string)
# 362                "parser_temp.ml"
  | _ -> failwith "lexing: bad action variable list when calling lexer user action"));(fun __dypgen_av_list lexbuf -> (match __dypgen_av_list with [] -> Lex_string
# 42 "parser.dyp"
(
      ( Buffer.add_string string_buf (Dyp.lexeme lexbuf);
      string lexbuf ):'dypgen__Lex_string)
# 368                "parser_temp.ml"
  | _ -> failwith "lexing: bad action variable list when calling lexer user action"))]))]

let __dypgen_regexp_decl = [
  ("newline",(Dyp.RE_Alt [Dyp.RE_Alt [Dyp.RE_Char '\n';Dyp.RE_Char '\r'];Dyp.RE_String "\r\n"]));
  ("blank",(Dyp.RE_Char_set [(' ',' ');('\t','\t');('\012','\012')]));
  ("lowercase",(Dyp.RE_Char_set [('a','z');('\223','\246');('\248','\255');('_','_')]));
  ("uppercase",(Dyp.RE_Char_set [('A','Z');('\192','\214');('\216','\222')]));
  ("identchar",(Dyp.RE_Char_set [('A','Z');('a','z');('_','_');('\192','\214');('\216','\246');('\248','\255');('\'','\'');('0','9')]))]

let dyp_merge_Lex_string l =
  match dyp_merge_Lex_string l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Lexeme_matched l =
  match dyp_merge_Lexeme_matched l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_LIDENT l =
  match dyp_merge_Obj_LIDENT l with
    | ([],_,_) -> dyp_merge l
    | res -> res
let dyp_merge_Obj_STRING l =
  match dyp_merge_Obj_STRING l with
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
  let f1 (o,gd,ld) = match o with Lex_string ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Lex_string"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Lex_string l in
  let f2 o = Lex_string o in
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
  let f1 (o,gd,ld) = match o with Obj_LIDENT ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_LIDENT"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_LIDENT l in
  let f2 o = Obj_LIDENT o in
  (List.map f2 ol, gd, ld)));
(fun l -> (
  let f1 (o,gd,ld) = match o with Obj_STRING ob -> (ob,gd,ld)
    | _ -> failwith "type error, bad obj in dyp_merge_Obj_STRING"
  in
  let l = List.map f1 l in
  let (ol,gd,ld) = dyp_merge_Obj_STRING l in
  let f2 o = Obj_STRING o in
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
  (fun x -> match x with Lex_string _ -> true | _ -> false);
  (fun x -> match x with Lexeme_matched _ -> true | _ -> false);
  (fun x -> match x with Obj_LIDENT _ -> true | _ -> false);
  (fun x -> match x with Obj_STRING _ -> true | _ -> false);
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
  
  false 4 false
  
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

