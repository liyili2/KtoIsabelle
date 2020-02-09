/* Use the expression datatype defined in mp8common.ml: */
%{
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

%}

/* Define the tokens of the language: */
%token <char list> OtherSort MetaVar OtherVar LabelId
%token <char list var> BagEnd
%token <int> Number 
%token <char list var * feature list> BagHead
%token Bool K KItem KLabel KResult KList List Set Map Bag Id String Int Float
       LittleK LPAREN RPAREN EOF DoubleComma UnitKList Add Sub OR AND
       UnitBag UnitMap UnitSet UnitList UnitK ListItem SetItem Mapsto Bindsby Leadsto
%left Add Sub OR AND

/* Define the "goal" nonterminal of the grammar: */
%start main
%type < (char list ,char list ,char list ) bag> main

%%

main: 
    parsebag EOF                         { $1 }
  | parsebag main EOF                    {BagCon (KTerm $1,KTerm $2)}

parsebag:
    
    MetaVar Bag                  {IdBag $1}
  | BagHead main BagEnd          {match $1 with (a,b) -> (match $3 with x -> if a = x then 
                                     Xml (a,b,KTerm $2) else raise (Failure "Xml var not match."))}
  | BagHead parsebigk BagEnd    {match $1 with (a,b) -> (match $3 with x -> if a = x then 
                                     SingleCell (a,b,$2) else raise (Failure "Xml var not match."))}
  | UnitBag                      {UnitBag}

parsebigk:

    parselist {$1}
  | parsek {$1}
  | parseset {$1}
  | parsemap {$1} 

parsek:
    parsesubk {$1}
  | parsesubk Leadsto parsek { Tilda (KTerm $1, KTerm $3)}

parsesubk:
    UnitK     {UnitK}
  | parsekitem {$1}

parselist:
    parsesublist {$1}
  | parsesublist parselist { ListCon (KTerm $1, KTerm $2)}

parsesublist:
    UnitList                        {UnitList}
  | MetaVar List                    {IdList $1}
  | ListItem LPAREN parsek RPAREN   {ListItem (KTerm $3)}
  | parseklabel LPAREN parseklist RPAREN List {ListFun ($1,$3)}

parseset:
    parsesubset {$1}
  | parsesubset parseset { SetCon (KTerm $1, KTerm $2)}

parsesubset:
    UnitSet     {UnitSet}
  | MetaVar Set                    {IdSet $1}
  | SetItem LPAREN parsek RPAREN   { SetItem (KTerm $3)}
  | parseklabel LPAREN parseklist RPAREN Set {SetFun ($1,$3)}

parsemap:
    parsesubmap {$1}
  | parsesubmap parsemap { MapCon (KTerm $1, KTerm $2)}

parsesubmap:
    UnitMap     {UnitMap}
  | MetaVar Map                    {IdMap $1}
  | parsek Mapsto parsek   {MapItem (KTerm $1, KTerm $3)}
  | parseklabel LPAREN parseklist RPAREN Map {MapFun ($1,$3)}

parsekitem:
    Number    {SingleK (KTerm (Constant (IntConst $1)))}
  | MetaVar K                        {IdK $1}
  | MetaVar KItem                    {SingleK (KTerm (IdKItem ($1, KItem)))}
  | parseklabel LPAREN parseklist RPAREN {KItemC ($1,$3,K)}
  | parseklabel LPAREN parseklist RPAREN KItem {KItemC ($1,$3,KItem)}
  | parseklabel LPAREN parseklist RPAREN K {KFun ($1,$3)}
  | aexp {$1}
  | bexp {$1}

aexp:
  aexp Add aexp {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}
 | variable Add aexp {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}
 | aexp Add variable {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}
 | variable Add variable {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}

bexp:
  bexp OR bexp {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}
|   variable OR bexp {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}
|   bexp OR variable {KItemC (KLabelC (parseString "Add"),KListCon (KTerm $1, KTerm $3),OtherSort (parseString "AExp"))}

parseklabel:
    LabelId {KLabelC $1}
  | MetaVar KLabel {IdKLabel $1}
  | parseklabel LPAREN parseklist RPAREN KLabel {KLabelFun ($1,$3)}

parseklist:
    parsesubklist {$1}
  | parsesubklist DoubleComma parseklist { KListCon (KTerm $1, KTerm $3)}

parsesubklist:
    UnitKList                        {UnitKList}
  | MetaVar KList                    {IdKList $1}
  | parsebigk   {KListItem (TheBigK $1)}
  | main   {KListItem (TheBigBag (KTerm $1))}
  | parseklabel   {KListItem (TheLabel (KTerm $1))}

variable:
   MetaVar {$1}
  | MetaVar Int {$1}
  | MetaVar KItem {$1}
  | MetaVar K {$1}
