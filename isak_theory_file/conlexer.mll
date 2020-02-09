{

open K;;
open K;;
open Conparser;;

let rec parseAux n input out = if n < 1 then raise (Failure "Num cannot less than 1.")
         else if input > n then raise (Failure "Wrong input of parseAux.")
        else if n = input then out
        else parseAux n (input + 1) (inc out);;

let parseNum n = parseAux n 1 One;;

let parseInt n = if n < 0 then Pos (parseNum (abs n)) else if n = 0 then Zero_int 
                else Neg (parseNum (abs n));;

let rec parseNat n = if n < 0 then raise (Failure "Strict Num cannot be less than zero") 
                        else if n = 0 then Zero_nat else Suc (parseNat (n - 1));;

let parseHex c = match c with '0' -> Nibble0 | '1' -> Nibble1 | '2' -> Nibble2 | '3' -> Nibble3
            | '4' -> Nibble4 | '5' -> Nibble5 | '6' -> Nibble6 | '7' -> Nibble7 | '8' -> Nibble8
            | '9' -> Nibble9 | 'A' -> NibbleA | 'B' -> NibbleB | 'C' -> NibbleC | 'D' -> NibbleD
            | 'E' -> NibbleE | 'F' -> NibbleF | _ -> raise (Failure "A char in a string out of bound.");;

let parseHexs cl = match cl with [c] -> Char (Nibble0, parseHex c) 
                               | [c1;c2] -> Char (parseHex c1, parseHex c2) 
                               | _ -> raise (Failure "A char in a string out of bound.");;

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;


let parseChar c = parseHexs (explode (Printf.sprintf "%X" (int_of_char c)));;

let parseString s = List.map (fun c -> parseChar c) (explode s);;

let dealwithSort s = match s with "K" -> K | "Bool" -> Bool | "KItem" -> KItem
         | "KLabel" -> KLabel | "KResult" -> KResult
    | "KList" -> KList | "List" -> List | "Set" -> Set
    | "Map" -> Map | "Bag" -> Bag | "Id" -> Id | "String" -> String
    | "Int" -> Int | "Float" -> Float | _ -> OtherSort (parseString s);;

let parseBagVar s = match s with "k" -> LittleK | _ -> OtherVar (parseString s)

}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let uppercase = ['A' - 'Z']
let alpha = ['a' - 'z' 'A' - 'Z' ]
let letter = numeric | alpha | ['_']
let special = ['`' '~' '!' '@' '#' '$' '%' '^' '&' '*' '(' ')' '-' '=' '+' '[' '{' ']' '}' '|' ';' ':' '\'' ',' '<' '.' '>' '/' '?']

let xmlid = numeric | alpha
let xmllater = xmlid | '-'
let id_char = letter | '\''
let open_comment = "/*"
let close_comment = "*/"
let whitespace = [' ' '\t' '\n']

rule token = parse
  | [' ' '\t'] { token lexbuf }
  | ['\n']     { token lexbuf }  (* skip over whitespace *)
  | eof        { EOF }
  | "("       { LPAREN  }
  | ")"       { RPAREN  }
  | ",,"      {DoubleComma}
  | "<" whitespace* ((xmlid (xmllater | xmllater)*) as s)   {getXml s [] lexbuf}
  | "</" whitespace* ((xmlid xmllater*) as s) whitespace* ">" {BagEnd (parseBagVar s)}
  | ".Bag"      {UnitBag}
  | ".Map"      {UnitMap}
  | ".Set"      {UnitSet}
  | ".List"     {UnitList}
  | ".K"        {UnitK}
  | ".KList"        {UnitKList}
  | "ListItem"  {ListItem}
  | "SetItem"   {SetItem}
  | "["       {LBrace}
  | "]"       {RBrace}
  | "|->"       {Mapsto}
  | "<-"        {Bindsby}
  | "~>"        {Leadsto}
  | ":" "Bool" {Bool}
  | ":" "K" {K}
  | ":" "KItem" {KItem}
  | ":" "KLabel"  {KLabel}
  | ":" "KResult" {KResult}
  | ":" "KList"  {KList}
  | ":" "List"   {List}
  | ":" "Set"       {Set}
  | ":" "Map"       {Map}
  | ":" "Bag"          {Bag}
  | ":" "Id"       {Id}
  | ":" "String"    {String}
  | ":" "Int"         {Int}
  | ":"  "Float"     {Float}
  | ("'" (id_char+)) as s {LabelId (parseString s)}

(* generated from syntax *)
  | ":" "AExp"  {AExp}
  | ":"  "BExp"  {BExp}
  | ":"  "Block" {Block}
  | ":"  "Stmt"  {Stmt}
  | ":"  "Ids"      {Ids}
  | ":"  "AExps"      {AExps}
  | ":"  "Stmts"      {Stmts}


  | (['+' '-']? numeric+) as s {Number (parseInt (int_of_string s))}
  | ("$" uppercase id_char*) as s {MetaVar (parseString s)}
  | ("//"([^'\n']*))   { token lexbuf }
  | open_comment   { multiline_comment lexbuf }
  | _           { raise (Failure "Token Lexical error") }

and getXml name attrs = parse
    ">"    {BagHead (parseBagVar s, attrs)}
  | "multiplicity" whitespace* "=" whitespace* "\"" whitespace* "*" whitespace* "\"" {getXml name attrs@[Multiplicity Star] lexbuf}
  | "multiplicity" whitespace* "=" whitespace* "\"" whitespace* "?" whitespace* "\"" {getXml name attrs@[Multiplicity Question] lexbuf}
  | "stream" whitespace* "=" whitespace* "\"" whitespace* "stdin" whitespace* "\"" {getXml name attrs@[Stream Stdin] lexbuf}
  | "stream" whitespace* "=" whitespace* "\"" whitespace* "stdout" whitespace* "\"" {getXml name attrs@[Stream Stdout] lexbuf}
  | "color" whitespace* "=" whitespace* "\"" ([^'\"']*) "\"" {getXml name attrs lexbuf}


and multiline_comment = parse
   close_comment   { token lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment lexbuf }

(* do not modify this function: *)
{
let lextest s = token (Lexing.from_string s)

 }
