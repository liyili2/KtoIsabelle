open K;;
open K;;
open Lexer;;
open Parser;;

(* file functions *)
let save file string =
     let channel = open_out_gen [Open_wronly; Open_append; Open_creat; Open_text] 0o666 file in
     output_string channel string;
     close_out channel;;

let read_file filename = 
let lines = ref [] in
let chan = open_in filename in
try
  while true; do
    lines := input_line chan :: !lines
  done; []
with End_of_file ->
  close_in chan;
  List.rev !lines ;;

(* functions for dealing with tokens
   the parsed tokens from syntax parser is a list of tokens, 
   these functions make it flatten *)
let rec tokenToList s
     = match s with Connect (a,b) -> 
          (tokenToList a) @ (tokenToList b)
          | _ -> [s];;

let get_all_tokens_fun lexbuf = let rec g () =
    match Lexer.token lexbuf with EOF -> []
      | t -> (tokenToList t) @ g () in
      g ();;

let deflate = 
  let q = Queue.create () in
  fun lexbuf -> 
    if not (Queue.is_empty q) then Queue.pop q else   
      match Lexer.token lexbuf with 
        | EOF -> EOF 
        | tok -> (match tokenToList tok with [] -> EOF
              | [a] -> a
              | hd::t ->  List.iter (fun tok -> Queue.add tok q) t ; hd);;

let rec combineString lst = match lst with [] -> ""
                                     | x::xs -> x^"\n"^combineString xs;;

let get_all_tokens s =
      let b = Lexing.from_string (s^"\n") in
      let rec g () =
      match token b with EOF -> []
      | t -> t :: g () in
      g ();;

(* lexsee is a function to get the result from the lexer *)
let lexsee () = (get_all_tokens (combineString (read_file "kool-untyped.k")));;

(* results from syntax parser from a special file *)
let interpreta () = (Parser.main deflate (Lexing.from_string (combineString (read_file "kool-untyped.k"))));;

(* helper functions *)

(* parse ASNI character to their numbers *)
let parseNibble c = match c with Nibble0 -> '0' | Nibble1 -> '1' | Nibble2 -> '2' | Nibble3 -> '3'
            | Nibble4 -> '4' | Nibble5 -> '5' | Nibble6 -> '6' | Nibble7 -> '7' | Nibble8 -> '8'
            | Nibble9 -> '9' | NibbleA -> 'A' | NibbleB -> 'B' | NibbleC -> 'C' | NibbleD -> 'D'
            | NibbleE -> 'E' | NibbleF -> 'F';;

let parseKChar c = match c with Char (a,b)
         -> int_of_string ("0X" ^ (String.make 1 (parseNibble a)) ^ (String.make 1 (parseNibble b)));;

(* giving a Isabelle representation char list print out the Ocaml string *)
let rec printUserString cl = match cl with [] -> ""
                   | a::al -> (String.make 1 (char_of_int (parseKChar a))) ^ (printUserString al);;

(* printing functions to print out a K file by given a parsed Isabelle K syntax *)
let printRuleInString s = match s with K.ARule cl -> "ARule \""^printUserString cl^"\"\n"
                                   | K.AContext cl -> "AContext \""^printUserString cl^"\"\n"
                                   | K.AConfi cl -> "AConfi \""^printUserString cl^"\"\n";;

let printRuleInStrings s = "[ "^ (List.fold_left (fun a b -> 
             match a with "" -> printRuleInString b | _ -> a ^ ";\n " ^ printRuleInString b ) "" s)^"]";;

(* given a Isabelle sort datatype, print out the Ocaml string for the sort
   the format is in Isabelle datatype *)
let printCharSort s = match s with K.Bool -> "Bool" | K -> "K" | KItem -> "KItem" | KLabel -> "KLabel"
                        | KResult -> "KResult" | KList -> "KList" | List -> "List" | Seta -> "Seta"
                        | Map -> "Map" | Bag -> "Bag" | OtherSort c -> "OtherSort "^(printUserString c)
                        | Top -> "Top" | Int -> "Int" | Float -> "Float" | Id -> "Id" | String -> "String";;

(* get the Ocaml nature number by given a Isabelle representation *)
let rec intOfNat n = match n with Zero_nat -> 0 | Suc na -> 1 + intOfNat na;;

(* print out a list of natural number by a list of Isabelle natural numbers *)
let rec printNatList s = match s with [] -> "" | a::al -> string_of_int (intOfNat a) ^","^ printNatList al;;

(* dealing with regular expressions. given a Isabelle reg, printout the Ocaml string *)
let rec printReg s = match s with K.Eps -> "Eps" | Sym c -> "Sym " ^ (String.make 1 (char_of_int (parseKChar c)))
                   | Alt (a,b) -> "Alt ("^ printReg a ^ ", " ^ printReg b ^ ")"
                   | TheSeq (a,b) -> "TheSeq ("^ printReg a ^ ", " ^ printReg b ^ ")"
                   | Rep a -> "Rep "^ printReg a;;

(* print out Ocaml string for the input syntax attribute in Isabelle in concrete syntax 
    not dealing with ASTs *)
let printSynAttrib s = match s with K.Strict cl -> "Strict ("^printNatList cl^")" | Seqstrict -> "Seqstrict"
                         | Left -> "Left" | Right -> "Right" | Hook s -> "Hook ("^printUserString s^")"
                | Function -> "Function" | Klabel s -> "Klabel ("^printUserString s ^")"
                | Bracket -> "Bracket" | Tokena -> "Tokena" | Avoid -> "Avoid"
                | OnlyLabel -> "OnlyLabel" | Regex r -> "Regex ("^printReg r ^ ")"
                | NotInRules -> "NotInRules"
                | NonAssoc -> "NonAssoc" | OtherSynAttr s -> "OtherSynAttr "^printUserString s;;

(* print out a list of concrete syntax of a given Isabelle attribute list *)
let printSynAttribList s = "[ " ^(List.fold_left (fun a b -> match a with "" -> printSynAttrib b
                          | _ -> a ^"; "^ printSynAttrib b) "" s)^ "]";;

(* print out concrete syntax in Ocaml by inputing a list of production in K Isabelle *)
let printSymbol s = match s with NonTerminal s -> "NonTerminal "^ printCharSort s
                        | Terminal s -> "Terminal \""^printUserString s^"\"";;

(* print concrete syntax in Ocaml of a Isabelle ne list for production *)
let rec printNeList s = match s with Single a -> "Single ("^printSymbol a^")"
                      | Con (a,b) -> "Con ("^printSymbol a^", "^printNeList b^")";;

(* print out concrete syntax in Ocaml for K syntax in Isabelle *)
let printSyntaxAuxB s = match s with Syntax (a,b,c) -> "Syntax ("^printCharSort a^", "^printNeList b^", "^printSynAttribList c^")"
               | Subsort (a,b) -> "Subsort ("^ printCharSort a^", "^printCharSort b^")"
               | Token (a,b,c) -> "Token ("^printCharSort a^", "^ printReg b^", "^printSynAttribList c^")"
               | ListSyntax (a,b,c,d) -> "ListSyntax ("^printCharSort a^", "^ printCharSort b
                                                    ^ ", "^printUserString c^", "^printSynAttribList d^")";;
(* print out the parsed terms from a K Isabelle specification
   and put it in a special data structure Parsed (x,y) such that x is a list of printing syntatic definitions
   and y is a list of rules in string format *)
let printSyntaxAuxA s = "[ "^ (List.fold_left (fun a b ->
    match a with "" ->  printSyntaxAuxB b | _ -> a ^ ";\n " ^ printSyntaxAuxB b ) "" s)^"]";;

let printSyntaxAux s = "[ "^ (List.fold_left (fun a b ->
    match a with "" ->  printSyntaxAuxA b | _ -> a ^ ";\n " ^ printSyntaxAuxA b ) "" s)^"]";;

let printSyntax s = match s with (a,b) -> "("^printCharSort a^", "^printSyntaxAux b^")";;

let printSyntaxs s = "[ "^ (List.fold_left (fun a b ->
    match a with "" ->  printSyntax b | _ -> a ^ ";\n " ^ printSyntax b ) "" s)^"]";;

let printParsed s = match s with Parsed (a,b) -> "Parsed ("^printSyntaxs a^", "^printRuleInStrings b^")";;

(* the above is the end of the first parser's job, where read in a specification and 
    get all information about the syntax, and put rules in a string list *)

(* a helper function for print out Parsed terms *)
let printKProg () = print_string (printParsed (interpreta ()));;

(* helper functions for the lexer *)
(* insert an element to a set *)
let rec insertToSet a l = match l with [] -> [a] | (x::y) -> if a = x then y else x::(insertToSet a y);;

(* insert a list of elements to a set *)
let insertsToSet l xl = List.fold_left (fun acc -> fun b -> insertToSet b acc) xl l;;

(* get a list of sorts in order from a input production *)
let rec getSortInNeList l = match l with Single (NonTerminal s) -> [s] 
           | Single (Terminal s) -> []
           | Con (NonTerminal s, xl) -> insertToSet s (getSortInNeList xl) 
           | Con (Terminal s, xl) -> getSortInNeList xl;;

(* get all sorts in a set from a syntax *)
let rec getSort s = match s with Syntax (a,b,c) -> insertToSet a (getSortInNeList b)
                 | Subsort (a,b) -> insertToSet a [b]
                 | Token (a,b,c) -> [a]
                 | ListSyntax (a,b,c,d) -> insertToSet a [b];;										

(* get all sorts in a list of syntax *)
let rec getSorts l = match l with [] -> []
           | x::xl -> insertsToSet (getSort x) (getSorts xl);;

(* get a list of terminals in order from an input production *)
let rec getTerminals l = match l with Single (NonTerminal s) -> []
           | Single (Terminal s) -> [s]
           | Con (NonTerminal s, xl) -> (getTerminals xl)
           | Con (Terminal s, xl) -> insertToSet s (getTerminals xl);; 

(* get a list of terminals from a syntactic definition *)
let rec getSynTerminal s = match s with Syntax (a,b,c) -> 
     if List.exists (fun a -> a = OnlyLabel) c then [] else (getTerminals b)
                 | Subsort (a,b) -> []
                 | Token (a,b,c) -> []
                 | ListSyntax (a,b,c,d) ->
         if List.exists (fun a -> a = OnlyLabel) d then [] else [c];;				

(* get all terminals as a set from a syntax list *)
let rec getSynTerminals l = match l with [] -> []
            | x::xl -> insertsToSet (getSynTerminal x) (getSynTerminals xl);;

(* given a Isabelle sort datatype, print out the Ocaml string for the sort
   the format is in K definition *)
let printSortString s = match s with K.Bool -> "Bool" | K -> "K" | KItem -> "KItem" | KLabel -> "KLabel"
                        | KResult -> "KResult" | KList -> "KList" | List -> "List" | Seta -> "Set"
                        | Map -> "Map" | Bag -> "Bag" | OtherSort c -> (printUserString c)
                        | Top -> "Top" | Int -> "Int" 
                        | Float -> "Float" | Id -> "Id" | String -> "String";;						

(* constant built-in sorts in K *)
let builtinSorts = [K.Bool; K; KItem; KLabel; KResult;
                   KList; List; Seta; Map; Bag; Id; String; Int; Float];;

let builtinCoreSorts = [K.K; KLabel; KList; List; Seta; Map; Bag];;

let builtinUserSort = [K.Id; String; Int; Float; Bool];;

(* print out user defined sorts in the lexer to parse sort generate
   using the name of sorts as the AST
   format -> : Sort --> Sort *)
let rec printNewSorts l = match l with [] -> ""
         | x::xl -> if (List.exists (fun a -> a = x) builtinSorts) then printNewSorts xl
                 else " |  \":\" \"" ^ printSortString x ^ "\"   {"
                 ^ printSortString x ^ "}\n" ^ printNewSorts xl;;

(* constant set of K built in operators *)
let builtinTerminals = ["(";")";".Bag";".Map";".Set";".List";
                        ".K";"ListItem";"SetItem";"[";"[";"|->";"<-";"~>"];;

(* a map to map K built in operators to AST form in the Lexer *)
let builtinTerminalMap = [("(", "LPAREN");(")", "RPAREN");(".Bag", "UnitBag");
           (".Map","UnitMap"); (".Set", "UnitSet");(".List", "UnitList"); (".K", "UnitK");
           ("ListItem", "ListItem");("SetItem", "SetItem");("[", "LBrace");("]", "RBrace");
           ("|->", "Mapsto");("<-", "Bindsby"); ("~>", "Leadsto"); (",,", "DoubleComma")];;

(* for a string in K, print out the Ocaml version *)
let realTerminalString s = let rec realTerminalAux s n acc = if n >= String.length s then acc
              else if s.[n] = '\\' then realTerminalAux s (n+1) (acc^"\\\\")
              else if s.[n] = '\"' then realTerminalAux s (n+1) (acc^"\\\"")
              else realTerminalAux s (n+1) acc^(String.make 1 s.[n])
             in realTerminalAux s 0 "";;

(*  *)
let printNewTerminals l = let rec printNewTerminalsAux l num = 
 match l with [] -> ("",builtinTerminalMap)
          | x::xl -> if List.exists (fun (a,b) -> a = x) builtinTerminalMap
          then printNewTerminalsAux xl num
          else (match printNewTerminalsAux xl (num + 1) with (left,right) ->
             ((left ^ " |  \"" ^ (realTerminalString x) ^ "\"   { A"^string_of_int num ^ "}\n")
                , (x,"A"^(string_of_int num))::right))
        in printNewTerminalsAux l 0 ;;

let rec printRegToFile s = match s with K.Eps -> ""
                | Sym c -> "\"" ^
                 (if (char_of_int (parseKChar c)) = '"' then "\\\""
                       else if (char_of_int (parseKChar c)) = '\\' then "\\\\"
                         else (String.make 1 (char_of_int (parseKChar c)))) ^"\""
                   | Alt (a,b) -> "("^ printRegToFile a ^ " | " ^ printRegToFile b ^ ")"
                   | TheSeq (a,b) -> "("^ printRegToFile a ^ " " ^ printRegToFile b ^ ")"
                   | Rep a -> printRegToFile a ^ "*";;


let symbolsToLabelString a = match symbolsToKLabel a with OtherLabel x -> x
                                     | _ -> [];;

let rec genSyntaxListWithLabel l = match l with [] -> []
        | (Syntax (a,b,c)::xl) -> 
       (match getKLabelName c with Some (OtherLabel n)
              -> (Syntax (a,b,c), [(printUserString n)])::(genSyntaxListWithLabel xl)
                    | _ -> (Syntax (a,b,c), [printUserString (symbolsToLabelString b)])::(genSyntaxListWithLabel xl))
        | (ListSyntax (a,b,c,d)::xl) -> 
                 (match getKLabelName d with
            Some (OtherLabel n) -> 
                (ListSyntax (a,b,c,d), [printUserString n;
              "."^(printSortString a)])::(genSyntaxListWithLabel xl)
              | _  -> (ListSyntax (a,b,c,d),
                                [(printUserString 
                                     (symbolsToLabelString 
                                        (Con (NonTerminal b,
                                           Con (Terminal c, 
                                               Single (NonTerminal a))))));
                               "."^(printSortString a)])::(genSyntaxListWithLabel xl))
        | (x::xl) -> genSyntaxListWithLabel xl;;

let rec printOutTokens l = match l with [] -> ""
                           | x::xl -> "%token "^x^"\n"^(printOutTokens xl);;

let getSortSyntaxAuxB s = match s with Syntax (a,b,c) -> []
               | Subsort (a,b) -> (if List.exists (fun x -> x = a) builtinUserSort then [a] else [])
                                      @(if List.exists (fun x -> x = b) builtinUserSort then [b] else [])
               | Token (a,b,c) -> []
               | ListSyntax (a,b,c,d) -> []

let getSortSyntaxAuxA s = (List.fold_left (fun a b -> insertsToSet (getSortSyntaxAuxB b) a) [] s);;

let getSortSyntaxAux s = (List.fold_left (fun a b -> insertsToSet (getSortSyntaxAuxA b) a) [] s);;

let getSortSyntax s = match s with (a,b) -> insertToSet a (getSortSyntaxAux b);;

let getSortSyntaxs s = (List.fold_left (fun a b -> insertsToSet (getSortSyntax b) a) [] s)@[K.KItem; KResult];;


let getSubSortSyntaxAuxB s = match s with Syntax (a,b,c) -> []
               | Subsort (a,b) -> [(a,b)]
               | Token (a,b,c) -> []
               | ListSyntax (a,b,c,d) -> []

let getSubSortSyntaxAuxA s = (List.fold_left (fun a b -> insertsToSet (getSubSortSyntaxAuxB b) a) [] s);;

let getSubSortSyntaxAux s = (List.fold_left (fun a b -> insertsToSet (getSubSortSyntaxAuxA b) a) [] s);;

let rec removeKResultSubsorts l = match l with [] -> []
                    | (a,b)::l -> if b = K.KResult then removeKResultSubsorts l else (a,b)::(removeKResultSubsorts l);;

(* a set of functions to add the subsort relations between target sort of a listsyntax to its child. *)
let rec getListSyntaxSubSortAux l = match l with [] -> []
           | (ListSyntax (a,b,c,d))::al -> insertToSet (b,a) (getListSyntaxSubSortAux al)
           | a::al -> getListSyntaxSubSortAux al;;

let rec getListSyntaxSubSorts l = match l with [] -> []
     | (a,b)::al -> List.fold_left (fun acc x -> insertsToSet (getListSyntaxSubSortAux x) acc)
                (getListSyntaxSubSorts al) b;;

let getSubSortSyntax s = match s with (a,b) -> (removeKResultSubsorts (getSubSortSyntaxAux b));;

let getSubSortSyntaxs s = insertsToSet (getListSyntaxSubSorts s)
              (List.fold_left (fun a b -> insertsToSet (getSubSortSyntax b) a) [] s);;

let ocaml_equal = {equal = (=)};;

let getSubSortGraph l = match l with Parsed (a,b) -> formGraph ocaml_equal (getSortSyntaxs a) (getSubSortSyntaxs a);;

let rec getEdges a l = match l with [] -> None | (x,y)::xl -> if a = x then Some y else getEdges a xl;;

let rec getSortComponentAux l = match l with [] -> [] | (x,y)::xl -> getSortComponentA x y l [x]
and getSortComponentA x y l acc = match y with [] -> acc | a::al 
               -> (match getEdges a l with None -> (getSortComponentA x al l (insertToSet a acc))
                     | Some yl -> (getSortComponentA a yl l (getSortComponentA x al l (insertToSet a acc))));;

let rec cutGraphs l xl = match l with [] -> ([],[]) | (a,b)::al -> 
            (match cutGraphs al xl with (left,right) ->
            if List.exists (fun t -> a = t) xl then ((a,b)::left,right) else (left,(a,b)::right));;

let rec getAllComponents l = match getSortComponentAux l with xl -> 
               (match cutGraphs l xl with (left,right) -> if left = [] then []
                  else left::(getAllComponents right));;

let getAllComponentsGraph l = getAllComponents (getSubSortGraph l);;

let rec collectSyntaxComponents l xl = match l with [] -> []
                           | (a,l)::al -> if List.exists (fun (x,y) -> x = a) xl
                            then (a,l)::(collectSyntaxComponents al xl)
                           else collectSyntaxComponents al xl;;

let collectSyntaxsAux l xl = match l with Parsed (a,b) -> collectSyntaxComponents a xl;;

let collectSyntaxs l = List.map (fun x -> collectSyntaxsAux l x) (getAllComponentsGraph l);;

(* collet syntax components for adjusted sort syntax list *)
let rec collectAdjSyntaxComponents l xl = match l with [] -> []
                           | (a,b,l)::al -> if List.exists (fun (x,y) -> x = a) xl
                            then (a,b,l)::(collectAdjSyntaxComponents al xl)
                           else collectAdjSyntaxComponents al xl;;

let rec removeNotRuleSyntaxAux l = match l with [] -> [] | a::al ->
   (match a with Syntax (x,y,z) -> if List.exists (fun a -> a = NotInRules || a = Bracket || a = OnlyLabel) z
               then removeNotRuleSyntaxAux al else a::(removeNotRuleSyntaxAux al)
        | Subsort (x,y) -> a::(removeNotRuleSyntaxAux al)
        | Token (x,y,z) -> if List.exists (fun a -> a = NotInRules || a = Bracket || a = OnlyLabel) z
               then removeNotRuleSyntaxAux al else a::(removeNotRuleSyntaxAux al)
        | ListSyntax (x,y,z,u) -> if List.exists (fun a -> a = NotInRules || a = Bracket || a = OnlyLabel) u
               then removeNotRuleSyntaxAux al else a::(removeNotRuleSyntaxAux al));;

let rec removeNotRuleSyntax l = match l with [] -> [] | a::al ->
        (match removeNotRuleSyntaxAux a with ax ->
             if ax = [] then removeNotRuleSyntax al else ax::(removeNotRuleSyntax al));;

let rec removeNotRulesSyntaxSort l = match l with [] -> []
            | (a,b)::al -> (match removeNotRuleSyntax b with [] -> removeNotRulesSyntaxSort al
             | x::xl -> (a,x::xl)::(removeNotRulesSyntaxSort al));;
       
let rec removeNotRulesSyntaxSorts l = match l with [] -> [] | a::al ->
        (match removeNotRulesSyntaxSort a with ax ->
             if ax = [] then removeNotRulesSyntaxSorts al else ax::(removeNotRulesSyntaxSorts al));;

let collectSyntaxsForRule l = removeNotRulesSyntaxSorts (collectSyntaxs l);;

(* find all commmon super sorts of two given sorts *)
let findAllCommonSuperSorts a b allSorts subG =
     let rec findAllCommonSuperSortsAux a b allSorts subG acc =
       match allSorts with [] -> (if acc = [] then None else Some acc)
         | x::xl -> if K.subsort ocaml_equal a x subG && subsort ocaml_equal b x subG
              then findAllCommonSuperSortsAux a b xl subG (insertToSet x acc)
              else findAllCommonSuperSortsAux a b xl subG acc
     in findAllCommonSuperSortsAux a b allSorts subG [];;

(* find the least common super sorts in a list *)
let findLeastSort allSorts subG = let rec findLeastSortAux allSorts subG acc =
      match allSorts with [] -> acc
         | a::al -> if subsort ocaml_equal a acc subG then findLeastSortAux al subG a
                      else findLeastSortAux al subG acc
      in findLeastSortAux (List.tl allSorts) subG (List.hd allSorts);;

(* remove all sorts in a list that are super sorts of some sorts in the least*)
let rec isLeastSortsAux t allSorts subG =
   match allSorts with [] -> true
     | x::xl -> if subsort ocaml_equal x t subG then false
                  else (isLeastSortsAux t xl subG);;

let rec getLeastSorts allSorts subG =
   match allSorts with [] -> []
      | x::xl -> if (isLeastSortsAux x xl subG)
                 then x::(getLeastSorts xl subG)
                 else (getLeastSorts xl subG);;

(* get common children of two given sorts *)
let rec intersect xl al = match xl with [] -> []
      | b::bl -> if List.exists (fun x -> x = b) al
          then b::(intersect bl al) else intersect bl al;;

let rec getListByPair a subG = match subG with [] -> None
       | (x,y)::xl -> if x = a then Some y else getListByPair a xl;;
      
let findCommonSubChild a b subG =
      match getListByPair a subG with None -> []
         | Some ax -> (match getListByPair b subG with None -> []
          | Some bx -> intersect ax bx);;

let rec getSortsFromPair l = match l with [] -> []
              | (a,b)::xl -> a::(getSortsFromPair xl);;

(* a set of functions to remove common subsorts of given sorts of syntaxs *)
let rec findCommonSubSortAux t allSorts subG =
    match allSorts with [] -> []
      | x::xl -> if t = x then findCommonSubSortAux t xl subG
        else insertsToSet (findCommonSubChild t x subG) (findCommonSubSortAux t xl subG);;

let rec removeSubsortSynAux l sorts = 
   match l with [] -> []
       | (Subsort (x,y))::xl -> if List.exists (fun a -> a = x) sorts
               then removeSubsortSynAux xl sorts
               else (Subsort (x,y))::(removeSubsortSynAux xl sorts)
       | x::xl -> x::(removeSubsortSynAux xl sorts);;

let rec removeSubsortSyn l sorts =
    match l with [] -> []
        | x::xl -> (match removeSubsortSynAux x sorts with [] -> removeSubsortSyn xl sorts
                | a::al -> (a::al)::(removeSubsortSyn xl sorts));;

(* find all common sub child sorts for every sort components *)
let findAllCommons l subG = let rec findAllCommonAux l allSorts subG =
    match l with [] -> []
        | (a,b)::xl -> (a,findCommonSubSortAux a allSorts subG,b)
                           ::(findAllCommonAux xl allSorts subG)
        in findAllCommonAux l (getSortsFromPair l) subG;;

let rec findAllCommonsComponents l subG = match l with [] -> []
       | a::al -> (findAllCommons a subG)::(findAllCommonsComponents al subG);;

(* remove the subsort syntax that have common child sorts in every components *)
let rec removeAllCommonSyn l = match l with [] -> []
         | (a,b,c)::xl -> (a,b,removeSubsortSyn c b)::(removeAllCommonSyn xl);;

(* remove edges that have common subs in the subsort graph *)
let rec removeAllCommonSubsortsAux subG a b = match subG with [] -> []
       | (x,y)::xl -> if x = a then (x,List.filter
            (fun u -> not (List.exists (fun v -> u = v) b)) y)::(removeAllCommonSubsortsAux xl a b)
           else (x,y)::(removeAllCommonSubsortsAux xl a b);;

let rec removeAllCommonSubsorts l subG = match l with [] -> subG
        | (a,b,c)::xl -> removeAllCommonSubsorts xl (removeAllCommonSubsortsAux subG a b);;

let rec removeAllCSInComponents l subG = match l with [] -> subG
       | a::al -> removeAllCSInComponents al (removeAllCommonSubsorts a subG);;

let rec mergeSynLists l = match l with [] -> [] | x::xl -> x@(mergeSynLists xl);;

(* the real final syntax tree ready to print out parser *)
let restructSubsortGraph l = match collectSyntaxsForRule l with sl
    -> (match getSubSortGraph l with subG -> (match findAllCommonsComponents sl subG with fsl
         -> match removeAllCSInComponents fsl subG with newSubG -> 
              List.map (fun a -> collectAdjSyntaxComponents
                    (removeAllCommonSyn (mergeSynLists fsl)) a) (getAllComponents newSubG)));;


(*
let mergeSortSyntaxsOne t l allSorts subG num = 
    match l with [] -> ([],num)
      | (a,xl)::al ->
       (match mergeSortSyntaxsOne t al allSorts subG num with (rl,numR) ->
    if findCommonSubSort t a then
         (match findCommonSuperSort t a allSorts subG
       with None -> 

))

let mergeSortSyntaxs l subG = let rec mergeSortSyntaxs l allSorts subG =
       match l with [] -> []
           | (a,xl)::al -> 

('a K.K.sort * 'a K.K.kSyntax list list) list
*)

(* generate parser for each sort components and put all of the sort constructs in a same component to be in one cell
  but use the information of the syntax in K core to determine if a parsed term is valid and has valid arguments. 
   ex: exp = abc (Int, Val, Exp), since the three arguemnts will be parsed as IntConstant, KItemC label(KList) Val
   and KItemC label(KList) Exp, then the parser will have the statement that
   match $1,$2,$3 with (IntConstant, KItemC x y Val, KItemC label(KList) Exp) -> .... | _ -> raise (Failure ) *)

let rec countBlocks l = match l with [] -> 0 | x::xl -> 1 + countBlocks xl;;

let getMax a b = if a < b then b else a;;

let rec countAllBlocks l = match l with [] -> None | (a,b)::al -> 
            (match countAllBlocks al with None -> Some (countBlocks b)
                             | Some x -> Some (getMax x (countBlocks b)));;

let rec produceRelations t n = if n <= 0 then []
                       else ("p"^(printSortString t)^(string_of_int n))::(produceRelations t (n-1));;

let printRelations l = let rec printRelationsAux l acc = match l with [] -> "%relation "^acc^"\n"
                              | a::al -> if acc = "" then printRelationsAux l (acc^a)
                                      else printRelationsAux l (acc^" < "^a)
                    in printRelationsAux l "";;

let rec assignRelationsAux l tl = match l with [] -> Some []
               | a::al -> (match tl with [] -> None
                 | x::xl -> match assignRelationsAux al xl with None -> None
                      | Some axl -> Some ((a,x)::axl));;

let rec assignRelations l tl = match l with [] -> Some []
              | (a,b)::al -> (match assignRelationsAux b tl with None -> None
                       | Some axl -> (match assignRelations al tl with None -> None
                       | Some ltl -> Some ((a,axl)::ltl)));;

let getFirstSort l = match l with [] -> None | (a,b)::al -> Some a;;

let rec genRelations l = match l with [] -> Some ([],"")
                | a::al -> (match countAllBlocks a with None -> genRelations al
            | Some n -> (match getFirstSort a with None -> genRelations al
                    | Some t -> (match produceRelations t n with tl -> 
            (match assignRelations a tl with None -> None
                   | Some rl -> (match genRelations al with None -> None
                    | Some (rls,sl) -> Some (rl::rls, sl^(printRelations tl)))))));;
                        

(* changes for rule parser only:
  1. the default id is not in rule. For all not in rule/onlyLabel and bracket constructs, we eliminate them from
     the sort -> syntax list.good.
  2. if a sort -> syntax list is empty, then we eliminate the entry.good.
  3. for list syntax construct. if the element of a list is subsort to the element of another list, and the breakers are the same.
     we merge them together, but treat them specially, as match $1 with Id -> Id list | _ -> AExp list
  4. for every construct, for every argument, we generate two different sorts, one for the original sort, the other for the variable sort.
  5. always start with a top sort in each sort component,if there is none, then generate one.
  6. good. remove KResult from the subsort relations and the syntax, check subsorts,
    if there is an expression sort A and it has A = B and A = C, and B = C, then remove A = C, only keeps A = B
  7. add ListSyntax relations,. good.
  8. if a syntax's klabel format and normal format are the same, then parse the klabel format only. same means
        klabel ( kitem ) = [klabel, '(', kitem ')']
 *)
(* collecting parsing information with tokens
  (target sort, token reg, attributes, token parser name) *)
let printLabelLex l = let rec printLabelLexAux l num = 
 match l with [] -> ("",[])
          | x::xl -> if List.exists (fun (a,b) -> a = x) builtinTerminalMap then printLabelLexAux xl num
          else (match printLabelLexAux xl (num + 1) with (left,right) ->
             ((left ^ " |  \"" ^ (realTerminalString x) ^ "\"   { Label"^string_of_int num ^ "}\n"), (x,"Label"^(string_of_int num))::right))
        in printLabelLexAux l 0 ;;

(* a data structure for easy printing out parsing data, all in AST form *)
type parTerm = ParTerm of string | ParSort of string

(*  normal syntax: target sort, argument sorts, concrete production, klabel name, klabel format production * syntax attributes * precedence relation in dypen. 
    token syntax: target sort, lex rule as string, AST name in parser, attributes, precedence.
    List syntax: target sort, source sort, separator string,
 ( subsort element list (target sort, source sort, unit string)),
            klabel separator, klabel unit separator, attribute, precedence
    subsort syntax:  source, target, precedence *)
type datas =  SynData of (char list sort * char list sort list * parTerm list * string * parTerm list * synAttrib * string)
            | TokenData of (char list sort * string (* lex rule *) * string (* parser AST *) * synAttrib * string)
            | ListData of (char list sort * char list sort * string (* AST form *)
           * (char list sort * char list sort * string (* unit AST sep *)) list
           * string (* con sep *) * string (* con unit sep *) * synAttrib * string)
            | SubsortData of (char list sort * char list sort * string)

(* a function to transfer terminal nelist to string list *)
let rec productionToString l = match l with
      Single (K.Terminal s) -> [ParTerm (printUserString s)]
     | Single (NonTerminal s) -> [ParSort (printSortString s)]
     | Con (Terminal s, xl) -> (ParTerm (printUserString s))::(productionToString xl)
     | Con (NonTerminal s, xl) -> (ParSort (printSortString s))::(productionToString xl);;

(* get the parser AST of a given reg *)
let getToken b num = 
      ((printRegToFile b),"Token"^ string_of_int num);;

let getTokenLex (a,b,c) num = 
      (" |  (" ^ (printRegToFile b) ^ ")  as s  {Token"^ string_of_int num ^" (parseString s)}",
                         (a,b,c,"Token"^ string_of_int num));;

let getLabelAST num = "Label"^(string_of_int num);;

let rec mapUpdate a b map = match map with [] -> [(a,b)]
         | (x,y)::xl -> if a = x then (x,b)::xl else (x,y)::(mapUpdate a b xl);;

(* a function to transfer kSyntax to datas *)
let rec kSyntaxToData x pi regMap labelMap num = match x with Syntax (a,b,c)
      -> (SynData (a,
   getNonTerminalInList b,
      productionToString b,
          printUserString (symbolsToLabelString b), [ParTerm (printUserString
       (symbolsToLabelString b)); ParTerm "("; ParTerm "parseklist";ParTerm ")"],
     (if List.exists (fun a -> a = K.Left) c then K.Left
     else if List.exists (fun a -> a = K.Right) c then Right
     else K.NonAssoc),pi), regMap, labelMap, num)
   | Subsort (a,b) -> (SubsortData (b,a,pi), regMap,labelMap, num)
   | Token (a,b,c) -> (match getValueTerm ocaml_equal b regMap with None ->
      (match getToken b num with (u,v) ->
       (TokenData (a,u,v, (if List.exists (fun a -> a = K.Left) c
            then K.Left else if List.exists (fun a -> a = K.Right) c
     then Right else NonAssoc),pi), mapUpdate b v regMap,labelMap, num+1))
      | Some v -> (TokenData (a,printRegToFile b, v, (if List.exists (fun a -> a = K.Left) c
            then K.Left else if List.exists (fun a -> a = K.Right) c
     then Right else NonAssoc),pi), regMap, labelMap, num))
   | ListSyntax (a,b,c,d) ->
        (match getValueTerm ocaml_equal ("'_"^(printUserString c)^"_") labelMap
           with None -> (match getLabelAST num with v ->
     (ListData (a,b,printUserString c,
           [(a,b,"."^(printSortString a))], "'_"^(printUserString c)^"_",
     v, (if List.exists (fun a -> a = K.Left) d
            then K.Left else if List.exists (fun a -> a = K.Right) d
     then Right else NonAssoc),pi),regMap,
             mapUpdate ("'_"^(printUserString c)^"_") v labelMap,num+1))
       | Some v -> (ListData (a,b,printUserString c,
           [(a,b,"."^(printSortString a))], "'_"^(printUserString c)^"_",
     v, (if List.exists (fun a -> a = K.Left) d
            then K.Left else if List.exists (fun a -> a = K.Right) d
     then Right else NonAssoc),pi),regMap,labelMap,num));;

(* add an char to the front of all strings in a string list 
    and a list of chars to to the front of all strings in a string list *)
let rec addToStringList a l = match l with [] -> []
                          | x::xl -> ((a^x)::(addToStringList a xl));;

let rec addAllToStringList bl l = match bl with [] -> []
            | x::xl -> (addToStringList x l)@(addAllToStringList xl l);;

(* print out parsing source for non left assoc concrete format *)
let rec parserLineLeft target sources concrete relation flag = 
     match concrete with [] -> Some [""]
         | (ParTerm s)::xl -> (match parserLineLeft target sources xl relation flag with None -> None
                        | Some rl -> Some (addToStringList (" "^s^" ") rl))
         | (ParSort s)::xl -> (match sources with [] -> None | t::tl -> 
           if (target = t) && flag = 0 then
                (match parserLineLeft target tl xl relation 1 with None -> None
             | Some rl -> Some (addAllToStringList [" "^s^"(<="^relation^") "; " variable "] rl))
           else if (target = t) && flag = 1 then
                (match parserLineLeft target tl xl relation 2 with None -> None
                        | Some rl -> Some (addAllToStringList [" "^s^"(<"^relation^") "; " variable "] rl))
           else (match parserLineLeft target tl xl relation flag with None -> None
                        | Some rl -> Some (addAllToStringList [" "^s^" "; " variable "] rl)));;

(* print out parsing source for non right assoc concrete format *)
let rec parserLineRight target sources concrete relation flag = 
     match concrete with [] -> Some [""]
         | (ParTerm s)::xl -> (match parserLineRight target sources xl relation flag with None -> None
                        | Some r -> Some (addToStringList (" "^s^" ") r))
         | (ParSort s)::xl -> (match sources with [] -> None | t::tl -> 
           if (target = t) && flag = 0 then
                (match parserLineRight target tl xl relation 1 with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^"(<"^relation^") "; " variable "] r))
           else if (target = t) && flag = 1 then
                (match parserLineRight target tl xl relation 2 with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^"(<="^relation^") "; " variable "] r))
           else (match parserLineRight target tl xl relation flag with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^" "; " variable "] r)));;

(* print out parsing source for non assoc concrete format *)
let rec parserLineNonAssoc target sources concrete relation = 
     match concrete with [] -> Some [""]
         | (ParTerm s)::xl -> (match parserLineNonAssoc target sources xl relation with None -> None
                        | Some r -> Some (addToStringList (" "^s^" ") r))
         | (ParSort s)::xl -> (match sources with [] -> None | t::tl -> 
           if (target = t) then
                (match parserLineNonAssoc target tl xl relation with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^"(<="^relation^") "; " variable "] r))
           else (match parserLineNonAssoc target tl xl relation with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^" "; " variable "] r)));;

(* print out parsing source for klabel format *)
let rec parserLineKLabel target sources concrete relation = 
     match concrete with [] -> Some [""]
         | (ParTerm s)::xl -> (match parserLineKLabel target sources xl relation with None -> None
                        | Some r -> Some (addToStringList (" "^s^" ") r))
         | (ParSort s)::xl -> (match sources with [] -> None | t::tl -> 
           (match parserLineKLabel target tl xl relation with None -> None
                        | Some r -> Some (addAllToStringList [" "^s^" "; " variable "] r)));;

(* print out parsing target for kList terms *)
let rec printKList cl n = match cl with [] -> "UnitKList"
                  | (ParTerm s)::xl -> printKList xl (n+1)
                  | (ParSort s)::xl ->
                 ("KListCon (KItem $"^(string_of_int n)^") ")
               ^" (KItem ("^(printKList xl (n+1))^"))";;

(* print out parsing target for a normal syntax *)
let rec printConcreteLine label concrete target relation sl = match sl with [] -> ""
          | x::xl -> "  | "^x^
         " {"^"KItemC (KTerm (KLabelC (parseString \""^label^"\"))) (KTerm "
               ^(printKList concrete 1)^") ("^(printCharSort target)^")} "
                  ^relation^"\n"^(printConcreteLine label concrete target relation xl);;

(* print out parsing target for unit list syntax *)
let rec printListUnits contents relation = match contents with [] -> ""
      | (a,b,c)::xl -> "  | "^c^" { ."^printSortString a^" } "^relation^"\n"
                          ^(printListUnits xl relation);;

(*  print out parsing target for list syntax *)
let rec printConds contents conLabel var s1 s2 = match contents with [] -> ""
         | (a,b,c)::xl -> if xl = [] then
      "KItemC (KItem (KLabelC (parseString \""^conLabel^"\")))
            (KItem (KListCon (KItem (KListItem
                 (TheBigK (TheK (KItem (SingleK (KItem ("^s1^"))))))))
         (KListCon (KItem (KListItem
                 (TheBigK (TheK (KItem (SingleK (KItem ("^s2^")))))))) (KItem UnitKList)))) "
            ^(printSortString a) else
    "if "^var^" = "^(printSortString a)^" then (KItemC (KItem (KLabelC (parseString \""^conLabel^"\")))
            (KItem (KListCon (KItem (KListItem
                 (TheBigK (TheK (KItem (SingleK (KItem ("^s1^"))))))))
         (KListCon (KItem (KListItem
                 (TheBigK (TheK (KItem (SingleK (KItem ("^s2^")))))))) (KItem UnitKList)))) "
            ^(printSortString a)^") else "^(printConds xl conLabel var s1 s2);;

(* print out the Dypen parser a line of by getting left assoc, right assoc, etc *)
let rec printParserLine d subG = match d with SynData
           (target,sources,concrete,label,labels,assoc,relation) ->
                (if assoc = Left && (List.length sources = 2)
          then (match parserLineLeft target sources concrete relation 0 with None -> ""
                    | Some sl -> printConcreteLine label concrete target relation sl)
            else if assoc = Right && (List.length sources = 2)
          then (match parserLineRight target sources concrete relation 0 with None -> ""
                    | Some sl -> printConcreteLine label concrete target relation sl)
            else (match parserLineNonAssoc target sources concrete relation with None -> ""
                    | Some sl -> printConcreteLine label concrete target relation sl))
               ^ (if concrete = labels then "" else
                    (match parserLineKLabel target sources concrete relation with None -> ""
                 | Some sl -> printConcreteLine label concrete target relation sl))
         | TokenData (target, regString, rule, assoc, relation) -> "  | "
            ^rule^" {KItemC (KItem (KLabelC (parseString $1))) (KItem UnitKList) ("
                     ^(printCharSort target)^")} "^relation^"\n"
        | ListData (target, source, sep, contents, conLabel, conAst, assoc,relation)
          -> (printListUnits contents relation)
          ^("  | "^(printSortString source)^" "^sep^" "^(printSortString target)
            ^"(<"^relation^") { match $1 with KItemC (x,y,z) -> "
                ^ printConds contents conLabel "z" "$1" "$3" ^"} "^relation)
         ^("  | "^conAst^" LPAREN "^(printSortString source)
           ^" DoubleComma "^(printSortString target)
            ^"RPAREN { match $3 with KItemC (x,y,z) -> "
                ^ printConds contents conLabel "z" "$3" "$5" ^"} "^relation)
         | SubsortData (source, target, relation) -> "  | "^(printSortString source)^" {"^(printSortString target)^"} "^relation;;












