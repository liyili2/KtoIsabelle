type token =
  | OtherSort of (char list)
  | MetaVar of (char list)
  | OtherVar of (char list)
  | LabelId of (char list)
  | BagEnd of (char list var)
  | Number of (int)
  | BagHead of (char list var * feature list)
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
  | LittleK
  | LPAREN
  | RPAREN
  | EOF
  | DoubleComma
  | UnitKList
  | Add
  | Sub
  | OR
  | AND
  | UnitBag
  | UnitMap
  | UnitSet
  | UnitList
  | UnitK
  | ListItem
  | SetItem
  | Mapsto
  | Bindsby
  | Leadsto

open Parsing;;
let _ = parse_error;;
# 3 "conparser.mly"
(* add any extra code here *)
open K
open K

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

let parseChar c = parseHexs (explodep (Printf.sprintf "%X" (int_of_char c)));;

let parseString s = List.map (fun c -> parseChar c) (explodep s);;

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

let rec sortAdjust t l = match l with [] -> []
          | x::xl -> (match x with Syntax (a,b,c) -> Syntax (t,b,c)::(sortAdjust t xl)
                           | Subsort (a,b) -> Subsort (a,t)::(sortAdjust t xl)
                           | Token (a,b,c) -> Token (t,b,c)::(sortAdjust t xl)
                           | ListSyntax (a,b,c,d) -> ListSyntax (t,b,c,d)::(sortAdjust t xl));;

let rec dealWithSorts l = match l with [] -> raise (Failure "Cannot have a syntactic sugar construct without fields.")
                               | [a] -> Con (NonTerminal a, Single (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ')')))]))
                               | a::al -> Con (NonTerminal a, Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ',')))], dealWithSorts al));;

let dealWithSugar a l = Con (Terminal a, Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char '(')))], dealWithSorts l));;

let rec dealWithSugarAttr a l = match l with [] -> [Klabel a]
                                    | x::xl -> (match x with Klabel y -> x::xl
                                                      | _ -> x::(dealWithSugarAttr a xl));;

# 130 "conparser.ml"
let yytransl_const = [|
  264 (* Bool *);
  265 (* K *);
  266 (* KItem *);
  267 (* KLabel *);
  268 (* KResult *);
  269 (* KList *);
  270 (* List *);
  271 (* Set *);
  272 (* Map *);
  273 (* Bag *);
  274 (* Id *);
  275 (* String *);
  276 (* Int *);
  277 (* Float *);
  278 (* LittleK *);
  279 (* LPAREN *);
  280 (* RPAREN *);
    0 (* EOF *);
  281 (* DoubleComma *);
  282 (* UnitKList *);
  283 (* Add *);
  284 (* Sub *);
  285 (* OR *);
  286 (* AND *);
  287 (* UnitBag *);
  288 (* UnitMap *);
  289 (* UnitSet *);
  290 (* UnitList *);
  291 (* UnitK *);
  292 (* ListItem *);
  293 (* SetItem *);
  294 (* Mapsto *);
  295 (* Bindsby *);
  296 (* Leadsto *);
    0|]

let yytransl_block = [|
  257 (* OtherSort *);
  258 (* MetaVar *);
  259 (* OtherVar *);
  260 (* LabelId *);
  261 (* BagEnd *);
  262 (* Number *);
  263 (* BagHead *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\002\000\002\000\002\000\002\000\003\000\003\000\
\003\000\003\000\005\000\005\000\008\000\008\000\004\000\004\000\
\010\000\010\000\010\000\010\000\006\000\006\000\013\000\013\000\
\013\000\013\000\007\000\007\000\014\000\014\000\014\000\014\000\
\009\000\009\000\009\000\009\000\009\000\009\000\009\000\009\000\
\015\000\015\000\015\000\015\000\016\000\016\000\016\000\011\000\
\011\000\011\000\012\000\012\000\018\000\018\000\018\000\018\000\
\018\000\017\000\017\000\017\000\017\000\000\000"

let yylen = "\002\000\
\002\000\003\000\002\000\003\000\003\000\001\000\001\000\001\000\
\001\000\001\000\001\000\003\000\001\000\001\000\001\000\002\000\
\001\000\002\000\004\000\005\000\001\000\002\000\001\000\002\000\
\004\000\005\000\001\000\002\000\001\000\002\000\003\000\005\000\
\001\000\002\000\002\000\004\000\005\000\005\000\001\000\001\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\001\000\
\002\000\005\000\001\000\003\000\001\000\002\000\001\000\001\000\
\001\000\001\000\002\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\006\000\062\000\000\000\003\000\
\000\000\048\000\033\000\029\000\023\000\017\000\013\000\000\000\
\000\000\000\000\000\000\007\000\000\000\009\000\010\000\000\000\
\014\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\000\000\000\000\000\000\049\000\018\000\024\000\030\000\
\059\000\000\000\000\000\004\000\005\000\000\000\000\000\000\000\
\016\000\000\000\000\000\000\000\022\000\000\000\000\000\000\000\
\028\000\000\000\000\000\000\000\000\000\000\000\002\000\000\000\
\000\000\000\000\000\000\031\000\012\000\000\000\000\000\053\000\
\056\000\055\000\000\000\000\000\000\000\000\000\000\000\000\000\
\041\000\043\000\045\000\047\000\042\000\044\000\046\000\000\000\
\019\000\000\000\025\000\000\000\054\000\000\000\000\000\000\000\
\000\000\061\000\060\000\000\000\000\000\038\000\037\000\050\000\
\020\000\026\000\032\000\052\000\000\000\000\000\000\000"

let yydgoto = "\002\000\
\073\000\007\000\074\000\020\000\021\000\022\000\023\000\024\000\
\025\000\026\000\075\000\076\000\028\000\029\000\030\000\031\000\
\032\000\077\000"

let yysindex = "\012\000\
\001\255\000\000\241\254\171\255\000\000\000\000\001\000\000\000\
\212\255\000\000\000\000\000\000\000\000\000\000\000\000\252\254\
\000\255\022\255\041\255\000\000\020\255\000\000\000\000\031\255\
\000\000\070\255\053\255\008\255\085\255\067\255\054\255\055\255\
\000\000\103\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\005\255\005\255\000\000\000\000\005\255\005\255\046\255\
\000\000\087\255\164\255\058\255\000\000\096\255\224\255\020\255\
\000\000\099\255\129\255\129\255\129\255\129\255\000\000\251\254\
\108\255\161\255\128\255\000\000\000\000\164\255\200\255\000\000\
\000\000\000\000\053\255\155\255\160\255\164\255\164\255\011\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\163\255\
\000\000\164\255\000\000\165\255\000\000\227\255\164\255\169\255\
\188\255\000\000\000\000\194\255\081\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\138\255\130\255\154\255"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\147\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\056\255\000\000\000\000\156\255\
\000\000\102\255\000\000\104\255\113\255\012\255\110\255\000\000\
\000\000\000\000\024\255\061\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\147\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\147\255\
\000\000\000\000\000\000\000\000\000\000\000\000\147\255\000\000\
\000\000\000\000\009\255\000\000\195\255\000\000\000\000\073\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\030\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\211\255\119\255"

let yygindex = "\000\000\
\129\000\000\000\220\000\199\000\140\000\202\000\210\000\000\000\
\000\000\000\000\252\255\077\000\000\000\000\000\191\000\193\000\
\186\000\000\000"

let yytablesize = 288
let yytable = "\027\000\
\033\000\008\000\003\000\035\000\036\000\037\000\064\000\004\000\
\010\000\052\000\011\000\010\000\001\000\039\000\041\000\039\000\
\039\000\039\000\042\000\098\000\099\000\050\000\043\000\054\000\
\058\000\034\000\044\000\034\000\034\000\034\000\041\000\005\000\
\057\000\057\000\036\000\039\000\039\000\066\000\066\000\015\000\
\013\000\066\000\066\000\039\000\017\000\045\000\039\000\034\000\
\034\000\039\000\061\000\039\000\061\000\036\000\036\000\034\000\
\037\000\046\000\034\000\038\000\008\000\034\000\035\000\034\000\
\035\000\035\000\035\000\036\000\037\000\036\000\047\000\048\000\
\039\000\010\000\058\000\051\000\058\000\058\000\058\000\008\000\
\008\000\061\000\060\000\062\000\035\000\035\000\055\000\060\000\
\010\000\060\000\011\000\104\000\035\000\059\000\105\000\035\000\
\058\000\058\000\035\000\058\000\035\000\058\000\063\000\014\000\
\058\000\016\000\015\000\058\000\021\000\070\000\058\000\040\000\
\058\000\040\000\040\000\040\000\012\000\027\000\078\000\015\000\
\036\000\079\000\036\000\036\000\036\000\015\000\015\000\021\000\
\021\000\006\000\080\000\089\000\018\000\040\000\040\000\034\000\
\027\000\027\000\102\000\103\000\104\000\040\000\036\000\036\000\
\040\000\107\000\092\000\040\000\104\000\040\000\036\000\091\000\
\106\000\036\000\096\000\097\000\036\000\011\000\036\000\011\000\
\011\000\011\000\102\000\103\000\104\000\071\000\100\000\010\000\
\056\000\011\000\004\000\108\000\009\000\058\000\010\000\058\000\
\011\000\004\000\094\000\011\000\011\000\065\000\067\000\090\000\
\095\000\068\000\069\000\011\000\101\000\072\000\011\000\062\000\
\109\000\011\000\005\000\012\000\013\000\014\000\015\000\016\000\
\017\000\005\000\012\000\013\000\014\000\015\000\016\000\017\000\
\035\000\036\000\037\000\110\000\093\000\038\000\039\000\040\000\
\008\000\111\000\051\000\041\000\035\000\036\000\037\000\019\000\
\049\000\038\000\039\000\040\000\008\000\053\000\000\000\041\000\
\035\000\036\000\037\000\102\000\103\000\104\000\057\000\040\000\
\105\000\106\000\107\000\041\000\082\000\084\000\086\000\088\000\
\036\000\081\000\036\000\085\000\083\000\000\000\087\000\000\000\
\000\000\000\000\003\000\000\000\000\000\000\000\000\000\004\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\005\000"

let yycheck = "\004\000\
\000\000\017\001\002\001\009\001\010\001\011\001\002\001\007\001\
\004\001\002\001\006\001\004\001\001\000\002\001\020\001\004\001\
\005\001\006\001\023\001\009\001\010\001\026\000\023\001\028\000\
\029\000\002\001\005\001\004\001\005\001\006\001\020\001\031\001\
\024\001\025\001\005\001\024\001\025\001\042\000\043\000\035\001\
\033\001\046\000\047\000\032\001\037\001\005\001\035\001\024\001\
\025\001\038\001\027\001\040\001\029\001\024\001\025\001\032\001\
\011\001\038\001\035\001\014\001\005\001\038\001\002\001\040\001\
\004\001\005\001\006\001\038\001\011\001\040\001\040\001\002\001\
\015\001\004\001\002\001\023\001\004\001\005\001\006\001\024\001\
\025\001\027\001\029\001\029\001\024\001\025\001\002\001\027\001\
\004\001\029\001\006\001\011\001\032\001\027\001\014\001\035\001\
\024\001\025\001\038\001\027\001\040\001\029\001\000\000\034\001\
\032\001\036\001\005\001\035\001\005\001\023\001\038\001\002\001\
\040\001\004\001\005\001\006\001\032\001\005\001\023\001\035\001\
\002\001\023\001\004\001\005\001\006\001\024\001\025\001\024\001\
\025\001\001\000\002\001\024\001\004\000\024\001\025\001\007\000\
\024\001\025\001\009\001\010\001\011\001\032\001\024\001\025\001\
\035\001\016\001\070\000\038\001\011\001\040\001\032\001\024\001\
\015\001\035\001\078\000\079\000\038\001\002\001\040\001\004\001\
\005\001\006\001\009\001\010\001\011\001\002\001\090\000\004\001\
\029\000\006\001\007\001\095\000\002\001\027\001\004\001\029\001\
\006\001\007\001\024\001\024\001\025\001\042\000\043\000\023\001\
\025\001\046\000\047\000\032\001\024\001\026\001\035\001\029\001\
\024\001\038\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\009\001\010\001\011\001\024\001\013\001\014\001\015\001\016\001\
\017\001\024\001\024\001\020\001\009\001\010\001\011\001\004\000\
\026\000\014\001\015\001\016\001\017\001\028\000\255\255\020\001\
\009\001\010\001\011\001\009\001\010\001\011\001\029\000\016\001\
\014\001\015\001\016\001\020\001\059\000\060\000\061\000\062\000\
\038\001\059\000\040\001\061\000\060\000\255\255\062\000\255\255\
\255\255\255\255\002\001\255\255\255\255\255\255\255\255\007\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\031\001"

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
  LittleK\000\
  LPAREN\000\
  RPAREN\000\
  EOF\000\
  DoubleComma\000\
  UnitKList\000\
  Add\000\
  Sub\000\
  OR\000\
  AND\000\
  UnitBag\000\
  UnitMap\000\
  UnitSet\000\
  UnitList\000\
  UnitK\000\
  ListItem\000\
  SetItem\000\
  Mapsto\000\
  Bindsby\000\
  Leadsto\000\
  "

let yynames_block = "\
  OtherSort\000\
  MetaVar\000\
  OtherVar\000\
  LabelId\000\
  BagEnd\000\
  Number\000\
  BagHead\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'parsebag) in
    Obj.repr(
# 104 "conparser.mly"
                                         ( _1 )
# 387 "conparser.ml"
               :  (char list ,char list ,char list ) bag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parsebag) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 :  (char list ,char list ,char list ) bag) in
    Obj.repr(
# 105 "conparser.mly"
                                         (BagCon (KTerm _1,KTerm _2))
# 395 "conparser.ml"
               :  (char list ,char list ,char list ) bag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 109 "conparser.mly"
                                 (IdBag _1)
# 402 "conparser.ml"
               : 'parsebag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : char list var * feature list) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 :  (char list ,char list ,char list ) bag) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : char list var) in
    Obj.repr(
# 110 "conparser.mly"
                                 (match _1 with (a,b) -> (match _3 with x -> if a = x then 
                                     Xml (a,b,KTerm _2) else raise (Failure "Xml var not match.")))
# 412 "conparser.ml"
               : 'parsebag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : char list var * feature list) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'parsebigk) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : char list var) in
    Obj.repr(
# 112 "conparser.mly"
                                (match _1 with (a,b) -> (match _3 with x -> if a = x then 
                                     SingleCell (a,b,_2) else raise (Failure "Xml var not match.")))
# 422 "conparser.ml"
               : 'parsebag))
; (fun __caml_parser_env ->
    Obj.repr(
# 114 "conparser.mly"
                                 (UnitBag)
# 428 "conparser.ml"
               : 'parsebag))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parselist) in
    Obj.repr(
# 118 "conparser.mly"
              (_1)
# 435 "conparser.ml"
               : 'parsebigk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsek) in
    Obj.repr(
# 119 "conparser.mly"
           (_1)
# 442 "conparser.ml"
               : 'parsebigk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parseset) in
    Obj.repr(
# 120 "conparser.mly"
             (_1)
# 449 "conparser.ml"
               : 'parsebigk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsemap) in
    Obj.repr(
# 121 "conparser.mly"
             (_1)
# 456 "conparser.ml"
               : 'parsebigk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsesubk) in
    Obj.repr(
# 124 "conparser.mly"
              (_1)
# 463 "conparser.ml"
               : 'parsek))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parsesubk) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parsek) in
    Obj.repr(
# 125 "conparser.mly"
                             ( Tilda (KTerm _1, KTerm _3))
# 471 "conparser.ml"
               : 'parsek))
; (fun __caml_parser_env ->
    Obj.repr(
# 128 "conparser.mly"
              (UnitK)
# 477 "conparser.ml"
               : 'parsesubk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsekitem) in
    Obj.repr(
# 129 "conparser.mly"
               (_1)
# 484 "conparser.ml"
               : 'parsesubk))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsesublist) in
    Obj.repr(
# 132 "conparser.mly"
                 (_1)
# 491 "conparser.ml"
               : 'parselist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'parsesublist) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'parselist) in
    Obj.repr(
# 133 "conparser.mly"
                           ( ListCon (KTerm _1, KTerm _2))
# 499 "conparser.ml"
               : 'parselist))
; (fun __caml_parser_env ->
    Obj.repr(
# 136 "conparser.mly"
                                    (UnitList)
# 505 "conparser.ml"
               : 'parsesublist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 137 "conparser.mly"
                                    (IdList _1)
# 512 "conparser.ml"
               : 'parsesublist))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'parsek) in
    Obj.repr(
# 138 "conparser.mly"
                                    (ListItem (KTerm _3))
# 519 "conparser.ml"
               : 'parsesublist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 139 "conparser.mly"
                                              (ListFun (_1,_3))
# 527 "conparser.ml"
               : 'parsesublist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsesubset) in
    Obj.repr(
# 142 "conparser.mly"
                (_1)
# 534 "conparser.ml"
               : 'parseset))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'parsesubset) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'parseset) in
    Obj.repr(
# 143 "conparser.mly"
                         ( SetCon (KTerm _1, KTerm _2))
# 542 "conparser.ml"
               : 'parseset))
; (fun __caml_parser_env ->
    Obj.repr(
# 146 "conparser.mly"
                (UnitSet)
# 548 "conparser.ml"
               : 'parsesubset))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 147 "conparser.mly"
                                   (IdSet _1)
# 555 "conparser.ml"
               : 'parsesubset))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'parsek) in
    Obj.repr(
# 148 "conparser.mly"
                                   ( SetItem (KTerm _3))
# 562 "conparser.ml"
               : 'parsesubset))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 149 "conparser.mly"
                                             (SetFun (_1,_3))
# 570 "conparser.ml"
               : 'parsesubset))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsesubmap) in
    Obj.repr(
# 152 "conparser.mly"
                (_1)
# 577 "conparser.ml"
               : 'parsemap))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'parsesubmap) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'parsemap) in
    Obj.repr(
# 153 "conparser.mly"
                         ( MapCon (KTerm _1, KTerm _2))
# 585 "conparser.ml"
               : 'parsemap))
; (fun __caml_parser_env ->
    Obj.repr(
# 156 "conparser.mly"
                (UnitMap)
# 591 "conparser.ml"
               : 'parsesubmap))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 157 "conparser.mly"
                                   (IdMap _1)
# 598 "conparser.ml"
               : 'parsesubmap))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parsek) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parsek) in
    Obj.repr(
# 158 "conparser.mly"
                           (MapItem (KTerm _1, KTerm _3))
# 606 "conparser.ml"
               : 'parsesubmap))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 159 "conparser.mly"
                                             (MapFun (_1,_3))
# 614 "conparser.ml"
               : 'parsesubmap))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 162 "conparser.mly"
              (SingleK (KTerm (Constant (IntConst _1))))
# 621 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 163 "conparser.mly"
                                     (IdK _1)
# 628 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 164 "conparser.mly"
                                     (SingleK (KTerm (IdKItem (_1, KItem))))
# 635 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'parseklist) in
    Obj.repr(
# 165 "conparser.mly"
                                         (KItemC (_1,_3,K))
# 643 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 166 "conparser.mly"
                                               (KItemC (_1,_3,KItem))
# 651 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 167 "conparser.mly"
                                           (KFun (_1,_3))
# 659 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 168 "conparser.mly"
         (_1)
# 666 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bexp) in
    Obj.repr(
# 169 "conparser.mly"
         (_1)
# 673 "conparser.ml"
               : 'parsekitem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 172 "conparser.mly"
                (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 681 "conparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'variable) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'aexp) in
    Obj.repr(
# 173 "conparser.mly"
                     (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 689 "conparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'aexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'variable) in
    Obj.repr(
# 174 "conparser.mly"
                     (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 697 "conparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'variable) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'variable) in
    Obj.repr(
# 175 "conparser.mly"
                         (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 705 "conparser.ml"
               : 'aexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'bexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'bexp) in
    Obj.repr(
# 178 "conparser.mly"
               (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 713 "conparser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'variable) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'bexp) in
    Obj.repr(
# 179 "conparser.mly"
                     (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 721 "conparser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'bexp) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'variable) in
    Obj.repr(
# 180 "conparser.mly"
                     (KItemC (KLabelC (parseString "Add"),KListCon (KTerm _1, KTerm _3),OtherSort (parseString "AExp")))
# 729 "conparser.ml"
               : 'bexp))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 183 "conparser.mly"
            (KLabelC _1)
# 736 "conparser.ml"
               : 'parseklabel))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 184 "conparser.mly"
                   (IdKLabel _1)
# 743 "conparser.ml"
               : 'parseklabel))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'parseklabel) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'parseklist) in
    Obj.repr(
# 185 "conparser.mly"
                                                (KLabelFun (_1,_3))
# 751 "conparser.ml"
               : 'parseklabel))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsesubklist) in
    Obj.repr(
# 188 "conparser.mly"
                  (_1)
# 758 "conparser.ml"
               : 'parseklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'parsesubklist) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'parseklist) in
    Obj.repr(
# 189 "conparser.mly"
                                         ( KListCon (KTerm _1, KTerm _3))
# 766 "conparser.ml"
               : 'parseklist))
; (fun __caml_parser_env ->
    Obj.repr(
# 192 "conparser.mly"
                                     (UnitKList)
# 772 "conparser.ml"
               : 'parsesubklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 193 "conparser.mly"
                                     (IdKList _1)
# 779 "conparser.ml"
               : 'parsesubklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parsebigk) in
    Obj.repr(
# 194 "conparser.mly"
                (KListItem (TheBigK _1))
# 786 "conparser.ml"
               : 'parsesubklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  (char list ,char list ,char list ) bag) in
    Obj.repr(
# 195 "conparser.mly"
           (KListItem (TheBigBag (KTerm _1)))
# 793 "conparser.ml"
               : 'parsesubklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'parseklabel) in
    Obj.repr(
# 196 "conparser.mly"
                  (KListItem (TheLabel (KTerm _1)))
# 800 "conparser.ml"
               : 'parsesubklist))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : char list) in
    Obj.repr(
# 199 "conparser.mly"
           (_1)
# 807 "conparser.ml"
               : 'variable))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 200 "conparser.mly"
                (_1)
# 814 "conparser.ml"
               : 'variable))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 201 "conparser.mly"
                  (_1)
# 821 "conparser.ml"
               : 'variable))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : char list) in
    Obj.repr(
# 202 "conparser.mly"
              (_1)
# 828 "conparser.ml"
               : 'variable))
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
   (Parsing.yyparse yytables 1 lexfun lexbuf :  (char list ,char list ,char list ) bag)
