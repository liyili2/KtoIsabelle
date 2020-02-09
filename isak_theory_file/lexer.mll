{

open K;;
open K;;
open Parser;;
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
let id_char = numeric | letter | "'" | "_"
let open_comment = "/*"
let close_comment = "*/"
let whitespace = [' ' '\t' '\n']

let escapednum = '0' numeric numeric | '1' numeric numeric | '2' ['0' - '4'] numeric | "25" ['0' -'5']

rule token = parse
  | [' ' '\t'] { token lexbuf }
  | ['\n']     { token lexbuf }  (* skip over whitespace *)
  | eof        { EOF }
  | "rule"       { arule "" lexbuf }
  | "imports"  whitespace* ((("#")? letter (letter | ['-'])*))    { token lexbuf }
  | "import" whitespace*  ((("#")? letter (letter | ['-'])*))    { token lexbuf }
  | "context" {acontext "" lexbuf}
  | "configuration" {aconfi "" lexbuf}
  | "require" whitespace* "\""  { (require lexbuf) }
  | "module" whitespace*  (("#")? letter (letter | ['-'])*)  { token lexbuf }
  | "endmodule"       { token lexbuf }
  | "syntax" {ASyntax}
  | "\""       {string "" lexbuf}
  | (("#")? uppercase xmlid*) as s {dealwithSort s}
  | "::="  { Assign }
  | "|"    {Bar}
  | ">"    {Gt}
  | "["    {syntaxattr [] lexbuf}
  | "Token" whitespace* "{" {dealwithtoken [] lexbuf}
  | "{" {LBig}
  | "}" {RBig}
  | ("#")? alpha xmlid* as s {LabelId (parseString s)}
  | "("       { LPAREN  }
  | ")"       { RPAREN  }
  | "," {Dot}
  | ("//"([^'\n']*))   { token lexbuf }
  | open_comment   { multiline_comment lexbuf }
  | _           { raise (Failure "Token Lexical error") }

and multiline_comment = parse
   close_comment   { token lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment lexbuf }


and dealwithtoken tokens = parse
   "}" {AToken tokens}
  | "\\?" {dealwithtoken (tokens@[AChar (parseChar '?')]) lexbuf}
  | "\\_" {dealwithtoken (tokens@[AChar (parseChar '_')]) lexbuf}
  | "\\\\" {dealwithtoken (tokens@[AChar (parseChar '\\')]) lexbuf}
  | "\\\'" {dealwithtoken (tokens@[AChar (parseChar '\'')]) lexbuf}
  | "\\-"  {dealwithtoken (tokens@[AChar (parseChar '-')]) lexbuf}
  | "\\\"" {dealwithtoken (tokens@[AChar (parseChar '\"')]) lexbuf}
  | "[" {dealwithtoken (tokens@[LBr]) lexbuf}
  | "]" {dealwithtoken (tokens@[RBr]) lexbuf}
  | "-" {dealwithtoken (tokens@[To]) lexbuf}
  | "*" {dealwithtoken (tokens@[TheStar]) lexbuf}
  | "+" {dealwithtoken (tokens@[Plus]) lexbuf}
  | "?" {dealwithtoken (tokens@[OneOrMore]) lexbuf}
  | _ as c {dealwithtoken (tokens@[AChar (parseChar c)]) lexbuf}

and syntaxattr attrs = parse
  | [' ' '\t'] { syntaxattr attrs lexbuf }
  | ['\n']     { syntaxattr attrs lexbuf }  (* skip over whitespace *)
  | eof        { raise (Failure "Bad in syntax attributes.") }
  | "]" {Attr attrs}
  | "left" {syntaxattr (attrs@[Left]) lexbuf}
  | "right" {syntaxattr (attrs@[Right]) lexbuf}
  | "function" {syntaxattr (attrs@[Function]) lexbuf}
  | "seqstrict" {syntaxattr (attrs@[Seqstrict]) lexbuf}
  | "strict"  whitespace* "(" {syntaxattrnum attrs [] lexbuf}
  | "strict" {syntaxattr (attrs@[Strict []]) lexbuf}
  | "non-assoc" {syntaxattr (attrs@[NonAssoc]) lexbuf}
  | "token" {syntaxattr (attrs@[Tokena]) lexbuf}
  | "avoid" {syntaxattr (attrs@[Avoid]) lexbuf}
  | "bracket" {syntaxattr (attrs@[Bracket]) lexbuf}
  | "onlyLabel" {syntaxattr (attrs@[OnlyLabel]) lexbuf}
  | "klabel"  whitespace* "(" ([^'\"' ')']* as s) ")" {syntaxattr (attrs@[Klabel (parseString s)]) lexbuf}
  | "notInRules" {syntaxattr (attrs@[NotInRules]) lexbuf}
  | "latex" whitespace* "(" ([^',' ' ' '\t' ']' ')']+) ")" as s  {syntaxattr (attrs@[OtherSynAttr (parseString s)]) lexbuf}
  | "hook" whitespace* "(" ([^',' ' ' '\t' ']' ')']+) ")" as s {syntaxattr (attrs@[OtherSynAttr (parseString s)]) lexbuf}
  | "division" {syntaxattr (attrs@[OtherSynAttr (parseString "division")]) lexbuf}
  | "variable" {syntaxattr (attrs@[OtherSynAttr (parseString "variable")]) lexbuf}
  | "autoReject" {syntaxattr (attrs@[OtherSynAttr (parseString "autoReject")]) lexbuf}
  | "arith" {syntaxattr (attrs@[OtherSynAttr (parseString "arith")]) lexbuf}
  | "prefer" {syntaxattr (attrs@[OtherSynAttr (parseString "prefer")]) lexbuf}
  | "," {syntaxattr attrs lexbuf}

and syntaxattrnum attrs nums = parse
  (((['1' - '9'])(numeric*)) as s) whitespace* "," { syntaxattrnum attrs (nums@[parseNat (int_of_string s)]) lexbuf}
  | (((['1' - '9'])(numeric*)) as s) whitespace* ")" {syntaxattr (attrs@[Strict (nums@[parseNat (int_of_string s)])]) lexbuf }

and string start_string = parse
   "\""     { Terminal (parseString start_string) }
 | "\\\\"   { string (start_string ^ "\\") lexbuf }
 | "\\\""   { string (start_string ^ "\"") lexbuf }
 | "\\t"    { string (start_string ^ "\t") lexbuf }
 | "\\n"    { string (start_string ^ "\n") lexbuf }
 | "\\r"    { string (start_string ^ "\r") lexbuf }
 | "\\"     { raise (Failure "String Content Lexical error") }
 | _ as c   { string (start_string ^ (String.make 1 c)) lexbuf }

and require = parse
   "\""     { token lexbuf }
 | "\\\""   { require lexbuf }
 | _   { require lexbuf }

and arule rule_string = parse
  | ['\n']     { arule rule_string lexbuf }  (* skip over whitespace *)
  | eof        { raise (Failure "unterminated rule.") }
  | "syntax" {Connect (ARule (parseString rule_string), Connect (ASyntax, (token lexbuf)))}
  | "rule" {Connect (ARule (parseString rule_string), (arule "" lexbuf))}
  | "context" {Connect (ARule (parseString rule_string), (acontext "" lexbuf))}
  | "configuration" {Connect (ARule (parseString rule_string), (aconfi "" lexbuf))}
  | "imports"  whitespace* ((("#")? letter (letter | ['-'])*))
                 { ARule (parseString rule_string) }
  | "import"  whitespace* ((("#")? letter (letter | ['-'])*))   
                 { ARule (parseString rule_string) }
  | ("//"([^'\n']*))   { arule rule_string lexbuf }
  | open_comment   { multiline_comment_rule rule_string lexbuf }
  | "endmodule"       { ARule (parseString rule_string) }
  | _ as c {arule (rule_string^(String.make 1 c)) lexbuf}

and multiline_comment_rule rule_string = parse
  | close_comment   { arule rule_string lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment_rule rule_string lexbuf }

and acontext rule_string = parse
  | ['\n']     { acontext rule_string lexbuf }  (* skip over whitespace *)
  | eof        { raise (Failure "unterminated context rule.") }
  | "syntax" {Connect (AContext (parseString rule_string), Connect (ASyntax, (token lexbuf)))}
  | "rule" {Connect (AContext (parseString rule_string), (arule "" lexbuf))}
  | "context" {Connect (AContext (parseString rule_string), (acontext "" lexbuf))}
  | "configuration" {Connect (AContext (parseString rule_string), (aconfi "" lexbuf))}
  | "imports" whitespace* ((("#")? letter (letter | ['-'])*))
                 { AContext (parseString rule_string) }
  | "import" whitespace* ((("#")? letter (letter | ['-'])*))
                              { AContext (parseString rule_string) }
  | ("//"([^'\n']*))  { acontext rule_string lexbuf }
  | open_comment   { multiline_comment_context rule_string lexbuf }
  | "endmodule"       { AContext (parseString rule_string) }
  | _ as c {acontext (rule_string^(String.make 1 c)) lexbuf}

and multiline_comment_context rule_string = parse
  | close_comment   { acontext rule_string lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment_context rule_string lexbuf }

and aconfi rule_string = parse
  | ['\n']     { aconfi rule_string lexbuf }  (* skip over whitespace *)
  | eof        { raise (Failure "unterminated configuration") }
  | "syntax" {Connect (AConfi (parseString rule_string), Connect (ASyntax, (token lexbuf)))}
  | "rule" {Connect (AConfi (parseString rule_string),(arule "" lexbuf))}
  | "context" {Connect (AConfi (parseString rule_string), (acontext "" lexbuf))}
  | "configuration" {Connect (AConfi (parseString rule_string), (aconfi "" lexbuf))}
  | "imports" whitespace* ((("#")? letter (letter | ['-'])*))
                 { AConfi (parseString rule_string) }
  | "import" whitespace* ((("#")? letter (letter | ['-'])*))
                              { AConfi (parseString rule_string) }
  | ("//"([^'\n']*))  { aconfi rule_string lexbuf }
  | open_comment  { multiline_comment_confi rule_string lexbuf }
  | "endmodule"       { AConfi (parseString rule_string) }
  | _ as c {aconfi (rule_string^(String.make 1 c)) lexbuf}

and multiline_comment_confi rule_string = parse
  | close_comment   { aconfi rule_string lexbuf }
  | eof    { raise (Failure "unterminated comment") }
  | _      { multiline_comment_confi rule_string lexbuf }


(* do not modify this function: *)
{
let lextest s = token (Lexing.from_string s)

 }
