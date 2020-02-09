open K
open K
type token =
  | Terminal of (char list)
  | OtherSort of (char list)
  | ARule of (char list)
  | AContext of (char list)
  | Klabel of (char list)
  | AConfi of (char list)
  | LabelId of (char list)
  | OtherSynAttr of (char list)
  | Attr of (synAttrib list)
  | Strict of (nat list)
  | AToken of (atoken list)
  | Connect of (token * token)
  | Bool
  | K
  | KItem
  | KLabel
  | KResult
  | KList
  | List
  | Set
  | Map
  | Bag
  | Id
  | String
  | Int
  | Float
  | ASyntax
  | Assign
  | Bar
  | Gt
  | EOF
  | Left
  | Right
  | Function
  | Seqstrict
  | NonAssoc
  | Tokena
  | Avoid
  | Bracket
  | LBig
  | RBig
  | Dot
  | TheStar
  | Plus
  | LPAREN
  | RPAREN

open Parsing;;
let _ = parse_error;;
# 3 "parser.mly"
(* add any extra code here *)
open K
open K
open Lexer

let rec parNat n = if n < 0 then raise (Failure "Strict Num cannot be less than zero") 
                        else if n = 0 then Zero_nat else Suc (parNat (n - 1));;

let parHex c = match c with '0' -> Nibble0 | '1' -> Nibble1 | '2' -> Nibble2 | '3' -> Nibble3
            | '4' -> Nibble4 | '5' -> Nibble5 | '6' -> Nibble6 | '7' -> Nibble7 | '8' -> Nibble8
            | '9' -> Nibble9 | 'A' -> NibbleA | 'B' -> NibbleB | 'C' -> NibbleC | 'D' -> NibbleD
            | 'E' -> NibbleE | 'F' -> NibbleF | _ -> raise (Failure "A char in a string out of bound.");;

let parHexs cl = match cl with [c] -> Char (Nibble0, parHex c) 
                               | [c1;c2] -> Char (parHex c1, parHex c2) 
                               | _ -> raise (Failure "A char in a string out of bound.");;

let explodep s =
  let rec expp i l =
    if i < 0 then l else expp (i - 1) (s.[i] :: l) in
  expp (String.length s - 1) [];;

let rec getListOfChars a b = if a > b then []
              else if a = b then [parHexs (explodep (Printf.sprintf "%X" b))]
              else (parHexs (explodep (Printf.sprintf "%X" a)))::(getListOfChars (a+1) b);;

let parseNibble c = match c with Nibble0 -> '0' | Nibble1 -> '1' | Nibble2 -> '2' | Nibble3 -> '3'
            | Nibble4 -> '4' | Nibble5 -> '5' | Nibble6 -> '6' | Nibble7 -> '7' | Nibble8 -> '8'
            | Nibble9 -> '9' | NibbleA -> 'A' | NibbleB -> 'B' | NibbleC -> 'C' | NibbleD -> 'D'
            | NibbleE -> 'E' | NibbleF -> 'F';;

let parseKChar c = match c with Char (a,b)
         -> int_of_string ("0X" ^ (String.make 1 (parseNibble a)) ^ (String.make 1 (parseNibble b)));;

let rec getAllChars l = match l with [] -> []
         | x::xl -> (match x with AChar y ->
             (match xl with [] -> (y::(getAllChars xl))
                  | a::al -> (match a with AChar b -> (y::getAllChars xl)
                     | To -> (match al with [] -> raise (Failure "Failed input of a regular expression.")
                  | (c::cl) -> 
                            (match c with AChar d -> (getListOfChars (parseKChar y) (parseKChar d))@(getAllChars cl)
                                        | _ -> raise (Failure "Failed input of a regular expression.")))
                                   | _ -> raise (Failure "Failed input of a regular expression.")))
                    | _ -> raise (Failure "Failed input of a regular expression."));;

let rec formAltsFromChars l = match l with [] -> Eps
                 | [x] -> Sym x | (x::xl) -> Alt (Sym x, formAltsFromChars xl);;

let rec findRBr xl yl = match yl with [] -> raise (Failure "Cannot Find Right BR.")
                   | a::al -> (match a with RBr -> (xl,al) | _ -> findRBr (xl@[a]) al);;

let rec toReg l = match l with [] -> Eps
              | x::xl -> match x with AChar y -> toRegAux (Sym y) xl
                       | LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (formAltsFromChars (getAllChars al)) bl)
                       | _ -> raise (Failure "No other possible input char.")
and toRegAux a l = match l with [] -> a
         | (x::xl) -> (match x with AChar y -> (match toReg l with f -> TheSeq (a,f))
                          | TheStar -> (match toReg xl with f -> TheSeq (Rep a,f))
                          | LBr -> (match findRBr [] xl with (al,bl) -> toRegAux (TheSeq (a,(formAltsFromChars (getAllChars al)))) bl)
                          | Plus -> (match toReg xl with f -> TheSeq (TheSeq (a, (Rep a)),f)) 
                          | OneOrMore -> (match toReg xl with f -> TheSeq (Alt (a, Eps),f))
                          | _ ->  raise (Failure "No other possible input Command."));;

let rec sortAdjustAux t l = match l with [] -> []
          | x::xl -> (match x with Syntax (a,b,c) -> Syntax (t,b,c)::(sortAdjustAux t xl)
                           | Subsort (a,b) -> Subsort (a,t)::(sortAdjustAux t xl)
                           | Token (a,b,c) -> Token (t,b,c)::(sortAdjustAux t xl)
                           | ListSyntax (a,b,c,d) -> ListSyntax (t,b,c,d)::(sortAdjustAux t xl));;

let rec sortAdjust t l = match l with [] -> [] | x::xl -> (sortAdjustAux t x)::(sortAdjust t l);;

let rec dealWithSorts l = match l with [] -> raise (Failure "Cannot have a syntactic sugar construct without fields.")
                               | [a] -> Con (NonTerminal a, Single (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ')')))]))
                               | a::al -> Con (NonTerminal a, Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ',')))], dealWithSorts al));;

let dealWithSugar a l = Con (Terminal a, Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char '(')))], dealWithSorts l));;

let rec dealWithSugarAttr a l = match l with [] -> [Klabel a]
                                    | x::xl -> (match x with Klabel y -> x::xl
                                                      | _ -> x::(dealWithSugarAttr a xl));;
let rec getKlabelChars l = match l with [] -> None
               | (Klabel s)::al -> Some s | a::al -> getKlabelChars al;;

# 136 "parser.ml"
let yytransl_const = [|
  269 (* Bool *);
  270 (* K *);
  271 (* KItem *);
  272 (* KLabel *);
  273 (* KResult *);
  274 (* KList *);
  275 (* List *);
  276 (* Set *);
  277 (* Map *);
  278 (* Bag *);
  279 (* Id *);
  280 (* String *);
  281 (* Int *);
  282 (* Float *);
  283 (* ASyntax *);
  284 (* Assign *);
  285 (* Bar *);
  286 (* Gt *);
    0 (* EOF *);
  287 (* Left *);
  288 (* Right *);
  289 (* Function *);
  290 (* Seqstrict *);
  291 (* NonAssoc *);
  292 (* Tokena *);
  293 (* Avoid *);
  294 (* Bracket *);
  295 (* LBig *);
  296 (* RBig *);
  297 (* Dot *);
  298 (* TheStar *);
  299 (* Plus *);
  300 (* LPAREN *);
  301 (* RPAREN *);
    0|]

let yytransl_block = [|
  257 (* Terminal *);
  258 (* OtherSort *);
  259 (* ARule *);
  260 (* AContext *);
  261 (* Klabel *);
  262 (* AConfi *);
  263 (* LabelId *);
  264 (* OtherSynAttr *);
  265 (* Attr *);
  266 (* Strict *);
  267 (* AToken *);
  268 (* Connect *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\003\000\003\000\004\000\004\000\005\000\005\000\005\000\005\000\
\005\000\005\000\005\000\005\000\006\000\006\000\006\000\006\000\
\007\000\007\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\000\000"

let yylen = "\002\000\
\001\000\002\000\001\000\002\000\001\000\002\000\004\000\005\000\
\001\000\003\000\001\000\003\000\007\000\006\000\002\000\001\000\
\002\000\001\000\004\000\005\000\001\000\001\000\002\000\002\000\
\001\000\003\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\042\000\002\000\
\004\000\006\000\041\000\027\000\028\000\029\000\030\000\031\000\
\032\000\033\000\034\000\035\000\036\000\037\000\038\000\039\000\
\040\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\024\000\000\000\015\000\000\000\
\023\000\008\000\000\000\000\000\017\000\000\000\000\000\000\000\
\010\000\012\000\000\000\000\000\000\000\026\000\020\000\000\000\
\000\000\013\000"

let yydgoto = "\002\000\
\007\000\032\000\033\000\034\000\035\000\036\000\047\000"

let yysindex = "\255\255\
\040\255\000\000\040\255\040\255\040\255\069\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\238\254\002\255\037\255\223\254\005\255\247\254\037\255\
\040\255\001\255\003\255\031\255\000\000\069\255\000\000\069\255\
\000\000\000\000\002\255\002\255\000\000\007\255\253\254\023\255\
\000\000\000\000\069\255\056\255\065\255\000\000\000\000\028\255\
\060\255\000\000"

let yyrindex = "\000\000\
\000\000\000\000\070\000\072\000\073\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\029\000\000\000\037\000\001\000\033\000\
\074\000\081\000\077\000\041\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\030\255\000\000\000\000\
\000\000\000\000\000\000\045\000\000\000\000\000\000\000\000\000\
\049\000\000\000"

let yygindex = "\000\000\
\002\000\252\255\035\000\032\000\000\000\236\255\028\000"

let yytablesize = 364
let yytable = "\001\000\
\033\000\026\000\028\000\011\000\008\000\009\000\010\000\037\000\
\029\000\027\000\038\000\041\000\030\000\039\000\012\000\013\000\
\014\000\015\000\016\000\017\000\031\000\019\000\020\000\021\000\
\022\000\023\000\024\000\025\000\022\000\040\000\043\000\044\000\
\021\000\046\000\042\000\048\000\016\000\028\000\011\000\045\000\
\018\000\052\000\003\000\004\000\019\000\005\000\046\000\051\000\
\014\000\012\000\013\000\014\000\015\000\016\000\017\000\018\000\
\019\000\020\000\021\000\022\000\023\000\024\000\025\000\053\000\
\055\000\056\000\006\000\057\000\058\000\001\000\011\000\003\000\
\005\000\007\000\025\000\050\000\011\000\049\000\054\000\000\000\
\009\000\012\000\013\000\014\000\015\000\016\000\017\000\018\000\
\019\000\020\000\021\000\022\000\023\000\024\000\025\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\033\000\033\000\033\000\033\000\000\000\033\000\000\000\
\000\000\033\000\000\000\000\000\000\000\033\000\033\000\033\000\
\033\000\033\000\033\000\033\000\033\000\033\000\033\000\033\000\
\033\000\033\000\033\000\033\000\000\000\033\000\033\000\022\000\
\022\000\000\000\022\000\021\000\021\000\022\000\021\000\016\000\
\016\000\021\000\016\000\018\000\018\000\000\000\018\000\019\000\
\019\000\000\000\019\000\014\000\014\000\000\000\014\000\022\000\
\000\000\022\000\022\000\021\000\000\000\021\000\021\000\016\000\
\000\000\016\000\016\000\018\000\000\000\018\000\018\000\019\000\
\000\000\019\000\019\000\014\000\000\000\014\000\014\000\011\000\
\011\000\000\000\011\000\009\000\009\000\000\000\009\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\011\000\
\000\000\000\000\011\000\009\000"

let yycheck = "\001\000\
\000\000\006\000\001\001\002\001\003\000\004\000\005\000\028\000\
\007\001\028\001\044\001\032\000\011\001\009\001\013\001\014\001\
\015\001\016\001\017\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\000\000\039\001\030\001\029\001\
\000\000\038\000\033\000\040\000\000\000\001\001\002\001\009\001\
\000\000\045\001\003\001\004\001\000\000\006\001\051\000\041\001\
\000\000\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\041\001\
\009\001\001\001\027\001\040\001\009\001\000\000\002\001\000\000\
\000\000\000\000\045\001\044\000\000\000\043\000\051\000\255\255\
\000\000\013\001\014\001\015\001\016\001\017\001\018\001\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\002\001\003\001\004\001\255\255\006\001\255\255\
\255\255\009\001\255\255\255\255\255\255\013\001\014\001\015\001\
\016\001\017\001\018\001\019\001\020\001\021\001\022\001\023\001\
\024\001\025\001\026\001\027\001\255\255\029\001\030\001\003\001\
\004\001\255\255\006\001\003\001\004\001\009\001\006\001\003\001\
\004\001\009\001\006\001\003\001\004\001\255\255\006\001\003\001\
\004\001\255\255\006\001\003\001\004\001\255\255\006\001\027\001\
\255\255\029\001\030\001\027\001\255\255\029\001\030\001\027\001\
\255\255\029\001\030\001\027\001\255\255\029\001\030\001\027\001\
\255\255\029\001\030\001\027\001\255\255\029\001\030\001\003\001\
\004\001\255\255\006\001\003\001\004\001\255\255\006\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\027\001\
\255\255\255\255\030\001\027\001"

let yynames_const = "\
  Bool\000\
  K\000\
  KItem\000\
  KLabel\000\
  KResult\000\
  KList\000\
  List\000\
  Set\000\
  Map\000\
  Bag\000\
  Id\000\
  String\000\
  Int\000\
  Float\000\
  ASyntax\000\
  Assign\000\
  Bar\000\
  Gt\000\
  EOF\000\
  Left\000\
  Right\000\
  Function\000\
  Seqstrict\000\
  NonAssoc\000\
  Tokena\000\
  Avoid\000\
  Bracket\000\
  LBig\000\
  RBig\000\
  Dot\000\
  TheStar\000\
  Plus\000\
  LPAREN\000\
  RPAREN\000\
  "

let yynames_block = "\
  Terminal\000\
  OtherSort\000\
  ARule\000\
  AContext\000\
  Klabel\000\
  AConfi\000\
  LabelId\000\
  OtherSynAttr\000\
  Attr\000\
  Strict\000\
  AToken\000\
  Connect\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 105 "parser.mly"
                                      ( Parsed ([],[ARule _1]) )
# 397 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  (char list) theoryParsed) in
    Obj.repr(
# 106 "parser.mly"
                                       ( match _2 with Parsed (x,y) -> Parsed (x,(ARule _1)::y) )
# 405 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 107 "parser.mly"
                                      ( Parsed ([],[AContext _1]) )
# 412 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  (char list) theoryParsed) in
    Obj.repr(
# 108 "parser.mly"
                                          ( match _2 with Parsed (x,y) -> Parsed (x,(AContext _1)::y) )
# 420 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 109 "parser.mly"
                                    ( Parsed ([],[AConfi _1]) )
# 427 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  (char list) theoryParsed) in
    Obj.repr(
# 110 "parser.mly"
                                        ( match _2 with Parsed (x,y) -> Parsed (x,(AConfi _1)::y) )
# 435 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'sort) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expressions) in
    Obj.repr(
# 111 "parser.mly"
                                      (Parsed ([(_2,sortAdjust _2 _4)], []))
# 443 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'sort) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expressions) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 :  (char list) theoryParsed) in
    Obj.repr(
# 112 "parser.mly"
                                            (match _5 with Parsed (x,y)
                                               -> match _4 with u -> Parsed ((_2,sortAdjust _2 _4)::x, y))
# 453 "parser.ml"
               :  (char list) theoryParsed))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'subexpressions) in
    Obj.repr(
# 116 "parser.mly"
                   ([_1])
# 460 "parser.ml"
               : 'expressions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'subexpressions) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expressions) in
    Obj.repr(
# 117 "parser.mly"
                                  (_1::_3)
# 468 "parser.ml"
               : 'expressions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expression) in
    Obj.repr(
# 120 "parser.mly"
                ([_1])
# 475 "parser.ml"
               : 'subexpressions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expression) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'subexpressions) in
    Obj.repr(
# 121 "parser.mly"
                                  (_1::_3)
# 483 "parser.ml"
               : 'subexpressions))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'sort) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : char list) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : synAttrib list) in
    Obj.repr(
# 124 "parser.mly"
                                          ( ListSyntax (Top, _3, _5, _7) )
# 492 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'sort) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 125 "parser.mly"
                                     ( ListSyntax (Top, _3, _5, []) )
# 500 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : atoken list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : synAttrib list) in
    Obj.repr(
# 126 "parser.mly"
                (Token (Top, toReg _1, _2))
# 508 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : atoken list) in
    Obj.repr(
# 127 "parser.mly"
           (Token (Top, toReg _1, []))
# 515 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'production) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : synAttrib list) in
    Obj.repr(
# 128 "parser.mly"
                    (match _1 with Single (NonTerminal x) ->
            (match getKlabelChars _2 with None -> Subsort (x, Top)
                  | Some s -> Syntax (Top,
          Con (Terminal s,Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char '(')))], Con (NonTerminal x,
               Single (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ')')))])))), _2))
                           | y -> Syntax (Top, y, _2) )
# 528 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'production) in
    Obj.repr(
# 134 "parser.mly"
               (match _1 with Single (NonTerminal x) -> Subsort (x, Top)
                           | y -> Syntax (Top, y, []) )
# 536 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : char list) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'sorts) in
    Obj.repr(
# 136 "parser.mly"
                                (Syntax (Top,dealWithSugar _1 _3,[Klabel _1]) )
# 544 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : char list) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'sorts) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : synAttrib list) in
    Obj.repr(
# 137 "parser.mly"
                                     (Syntax (Top,dealWithSugar _1 _3, dealWithSugarAttr _1 _5) )
# 553 "parser.ml"
               : 'expression))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sort) in
    Obj.repr(
# 140 "parser.mly"
        (Single (NonTerminal _1))
# 560 "parser.ml"
               : 'production))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 141 "parser.mly"
             (Single (Terminal _1))
# 567 "parser.ml"
               : 'production))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'sort) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'production) in
    Obj.repr(
# 142 "parser.mly"
                    (Con (NonTerminal _1, _2))
# 575 "parser.ml"
               : 'production))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'production) in
    Obj.repr(
# 143 "parser.mly"
                        (Con (Terminal _1, _2))
# 583 "parser.ml"
               : 'production))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sort) in
    Obj.repr(
# 146 "parser.mly"
         ([_1])
# 590 "parser.ml"
               : 'sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'sort) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'sorts) in
    Obj.repr(
# 147 "parser.mly"
                   (_1::_3)
# 598 "parser.ml"
               : 'sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 150 "parser.mly"
           ( Bool )
# 604 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 151 "parser.mly"
           (K)
# 610 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 152 "parser.mly"
               (KItem)
# 616 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
                (KLabel)
# 622 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 154 "parser.mly"
                 (KResult)
# 628 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 155 "parser.mly"
               (KList)
# 634 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 156 "parser.mly"
              (List)
# 640 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 157 "parser.mly"
             (Seta)
# 646 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 158 "parser.mly"
             (Map)
# 652 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 159 "parser.mly"
             (Bag)
# 658 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 160 "parser.mly"
            (Id)
# 664 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 161 "parser.mly"
                (String)
# 670 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 162 "parser.mly"
             (Int)
# 676 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 163 "parser.mly"
               (Float)
# 682 "parser.ml"
               : 'sort))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 164 "parser.mly"
                   (OtherSort _1)
# 689 "parser.ml"
               : 'sort))
(* Entry main *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let main (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf :  (char list) theoryParsed)
