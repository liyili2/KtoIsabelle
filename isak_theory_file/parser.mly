/* Use the expression datatype defined in mp8common.ml: */
%{
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

%}

/* Define the tokens of the language: */
%token <char list> Terminal OtherSort ARule AContext Klabel AConfi LabelId OtherSynAttr
%token <synAttrib list> Attr
%token <nat list> Strict
%token <atoken list> AToken
%token <token * token> Connect
%token Bool K KItem KLabel KResult KList List Set Map Bag Id String Int Float
       ASyntax Assign Bar Gt EOF Left Right Function Seqstrict
       NonAssoc Tokena Avoid Bracket LBig RBig Dot TheStar Plus LPAREN RPAREN 

/* Define the "goal" nonterminal of the grammar: */
%start main
%type < (char list) theoryParsed> main

%%

main: 
    ARule                             { Parsed ([],[ARule $1]) }
  | ARule main                         { match $2 with Parsed (x,y) -> Parsed (x,(ARule $1)::y) }
  | AContext                          { Parsed ([],[AContext $1]) }
  | AContext main                         { match $2 with Parsed (x,y) -> Parsed (x,(AContext $1)::y) }
  | AConfi                          { Parsed ([],[AConfi $1]) }
  | AConfi main                         { match $2 with Parsed (x,y) -> Parsed (x,(AConfi $1)::y) }
  | ASyntax sort Assign expressions   {Parsed ([($2,sortAdjust $2 $4)], [])}
  | ASyntax sort Assign expressions main    {match $5 with Parsed (x,y)
                                               -> match $4 with u -> Parsed (($2,sortAdjust $2 $4)::x, y)}

expressions:
    subexpressions {[$1]}
  | subexpressions Gt expressions {$1::$3}

subexpressions:
    expression  {[$1]}
  | expression Bar subexpressions {$1::$3}

expression:
    List LBig sort Dot Terminal RBig Attr { ListSyntax (Top, $3, $5, $7) }
  | List LBig sort Dot Terminal RBig { ListSyntax (Top, $3, $5, []) }
  | AToken Attr {Token (Top, toReg $1, $2)}
  | AToken {Token (Top, toReg $1, [])}
  | production Attr {match $1 with Single (NonTerminal x) ->
            (match getKlabelChars $2 with None -> Subsort (x, Top)
                  | Some s -> Syntax (Top,
          Con (Terminal s,Con (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char '(')))], Con (NonTerminal x,
               Single (Terminal [parHexs (explodep (Printf.sprintf "%X" (int_of_char ')')))])))), $2))
                           | y -> Syntax (Top, y, $2) }
  | production {match $1 with Single (NonTerminal x) -> Subsort (x, Top)
                           | y -> Syntax (Top, y, []) }
  | LabelId LPAREN sorts RPAREN {Syntax (Top,dealWithSugar $1 $3,[Klabel $1]) }
  | LabelId LPAREN sorts RPAREN Attr {Syntax (Top,dealWithSugar $1 $3, dealWithSugarAttr $1 $5) }

production:
   sort {Single (NonTerminal $1)}
  | Terminal {Single (Terminal $1)}
  | sort production {Con (NonTerminal $1, $2)}
  | Terminal production {Con (Terminal $1, $2)}

sorts:
    sort {[$1]}
  | sort Dot sorts {$1::$3}
	
sort:
    Bool   { Bool }
  | K      {K}
  | KItem      {KItem}
  | KLabel      {KLabel}
  | KResult      {KResult}
  | KList      {KList}
  | List      {List}
  | Set      {Seta}
  | Map      {Map}
  | Bag      {Bag}
  | Id      {Id}
  | String      {String}
  | Int      {Int}
  | Float      {Float}
  | OtherSort      {OtherSort $1}
   

