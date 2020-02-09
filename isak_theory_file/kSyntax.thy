theory kSyntax
imports Main Real List
begin

(* this file defines all syntax of K and its helper functions *)
(* regular expression *)
datatype reg = Eps | Sym char | Alt reg reg | TheSeq reg reg | Rep reg

datatype atoken = AChar char | LBr | RBr | To | TheStar | Plus | OneOrMore

(* k syntax *)
datatype 'a state = Continue 'a | Stop 'a | Div 'a

datatype ('a, 'b) oneStep = Success 'a | Failure 'b

datatype ruleLabel = FunTrans | AnywhereTrans | NormalTrans

datatype 'a nelist = Single 'a | Con 'a "'a nelist"

datatype theConstant = IntConst int | FloatConst real | StringConst string
                     | BoolConst bool | IdConst string

datatype 'var var = LittleK | OtherVar 'var

datatype 'upVar sort = Bool | K | KItem | KLabel | KResult | KList | List | Set | Map | Bag
                   | OtherSort 'upVar | Top | Int | Float | Id | String

datatype 'metaVar metaVar = Defined 'metaVar | Generated nat | FunHole

datatype 'upVar label = UnitLabel "'upVar sort" | ConstToLabel theConstant
            | Sort | GetKLabel | IsKResult | AndBool | NotBool | OtherLabel string
           | TokenLabel string

datatype 'upVar symbol = NonTerminal "'upVar sort" | Terminal string

(*encoding an parsing tree leaving out the non-Terminal
exists a function to compile a production list to a kitem
*)
(*
datatype 'var programProduction = ProgTerminal string | programConst "'var theConstant"
                                | ProgNonTerminal "'var programProduction nelist"

datatype 'var program = TheProg "'var programProduction nelist"
*)

datatype synAttrib = Strict "nat list" | Seqstrict
                                | Left | Right | Hook string | Function | Klabel string
                                | Bracket | Token | Avoid | OnlyLabel | NotInRules
                                | Regex reg | NonAssoc | OtherSynAttr string

(* exist a function will take in a k syntax to generate the kitems for each term*)
datatype 'upVar kSyntax = Syntax "'upVar sort" "'upVar symbol nelist" "synAttrib list"
                         | Subsort "'upVar sort" "'upVar sort"
                         | Token "'upVar sort" reg "synAttrib list"
                         | ListSyntax "'upVar sort" "'upVar sort" string "synAttrib list"

datatype ruleInString = ARule string | AContext string | AConfi string
datatype 'upVar theoryParsed =
                     Parsed "('upVar sort * 'upVar kSyntax list list) list" "ruleInString list"

datatype key = Star | Question

datatype stdType = Stdin | Stdout

datatype feature = Multiplicity key | Stream stdType | DotDotDot

datatype 'a rewrite = KTerm 'a | KRewrite 'a 'a

datatype ('upVar, 'var, 'metaVar) kLabel
     = KLabelC "'upVar label"
     | KLabelFun "('upVar, 'var, 'metaVar) kLabel"
                 "('upVar, 'var, 'metaVar) kList rewrite"
     | IdKLabel "'metaVar metaVar"
and ('upVar, 'var, 'metaVar) kItem = KItemC "('upVar, 'var, 'metaVar) kLabel rewrite"
                                              "('upVar, 'var, 'metaVar) kList rewrite"
                                              "'upVar sort"
                                      | Constant theConstant "'upVar sort"
                                      | IdKItem "'metaVar metaVar" "'upVar sort"
                                      |  HOLE "'upVar sort"
and ('upVar, 'var, 'metaVar) kList =
                                   KListCon "('upVar, 'var, 'metaVar) kList rewrite"
                                            "('upVar, 'var, 'metaVar) kList rewrite"
                                 | UnitKList
                                 | KListItem  "('upVar, 'var, 'metaVar) bigKWithBag"
                                 | IdKList "'metaVar metaVar"
and ('upVar, 'var, 'metaVar) bigK = TheK "('upVar, 'var, 'metaVar) k rewrite"
                                | TheList "('upVar, 'var, 'metaVar) theList rewrite"
                                | TheSet "('upVar, 'var, 'metaVar) theSet rewrite"
                                | TheMap "('upVar, 'var, 'metaVar) theMap rewrite"
and ('upVar, 'var, 'metaVar) bigKWithBag = TheBigK "('upVar, 'var, 'metaVar) bigK"
                             | TheBigBag "('upVar, 'var, 'metaVar) bag rewrite"
                             | TheLabel "('upVar, 'var, 'metaVar) kLabel rewrite"
and ('upVar, 'var, 'metaVar) k
         = Tilda "('upVar, 'var, 'metaVar) k rewrite"
                 "('upVar, 'var, 'metaVar) k rewrite"
           | UnitK | IdK "'metaVar metaVar"
           | SingleK "('upVar, 'var, 'metaVar) kItem rewrite"
           | KFun "('upVar, 'var, 'metaVar) kLabel"
                  "('upVar, 'var, 'metaVar) kList rewrite"
and ('upVar, 'var, 'metaVar) theList =
               ListCon "('upVar, 'var, 'metaVar) theList rewrite"
                                      "('upVar, 'var, 'metaVar) theList rewrite"
                                    | UnitList
                                    | IdList "'metaVar metaVar"
                                    | ListItem "('upVar, 'var, 'metaVar) k rewrite"
                                    | ListFun "('upVar, 'var, 'metaVar) kLabel"
                                              "('upVar, 'var, 'metaVar) kList rewrite"
and ('upVar, 'var, 'metaVar) theSet = SetCon "('upVar, 'var, 'metaVar) theSet rewrite"
                                     "('upVar, 'var, 'metaVar) theSet rewrite"
                                    | UnitSet
                                    | IdSet "'metaVar metaVar"
                                    | SetItem "('upVar, 'var, 'metaVar) k rewrite"
                                    | SetFun "('upVar, 'var, 'metaVar) kLabel"
                                             "('upVar, 'var, 'metaVar) kList rewrite"
and ('upVar, 'var, 'metaVar) theMap 
  = MapCon "('upVar, 'var, 'metaVar) theMap rewrite"
           "('upVar, 'var, 'metaVar) theMap rewrite"
         | UnitMap
         | IdMap "'metaVar metaVar"
         | MapItem "('upVar, 'var, 'metaVar) k rewrite"
                   "('upVar, 'var, 'metaVar) k rewrite"
         | MapFun "('upVar, 'var, 'metaVar) kLabel"
                  "('upVar, 'var, 'metaVar) kList rewrite"
and ('upVar, 'var, 'metaVar) bag
            = BagCon "('upVar, 'var, 'metaVar) bag rewrite"
                     "('upVar, 'var, 'metaVar) bag rewrite"
             | UnitBag
             | IdBag "'metaVar metaVar"
             | Xml "'var var" "feature list" "('upVar, 'var, 'metaVar) bag rewrite"
             | SingleCell "'var var" "feature list" "('upVar, 'var, 'metaVar) bigK"

datatype ('var, 'upVar) ruleAttrib = Attr 'var | Heat | Cool | Transition
                                | Anywhere | Structural | Owise | Macro | Result "'upVar sort"

datatype ('upVar, 'var, 'metaVar) kRule
                  = Context "('upVar, 'var, 'metaVar) kItem"  "('var, 'upVar) ruleAttrib list"
                  | ContextWithCon "('upVar, 'var, 'metaVar) kItem" 
                                   "('upVar, 'var, 'metaVar) kItem"
                                   "('var, 'upVar) ruleAttrib list"
                  | KRule "('upVar, 'var, 'metaVar) k rewrite"
                          "('var, 'upVar) ruleAttrib list"
                  | KRuleWithCon "('upVar, 'var, 'metaVar) k rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                             "('var, 'upVar) ruleAttrib list"
                  | KItemRule "('upVar, 'var, 'metaVar) kItem rewrite"
                          "('var, 'upVar) ruleAttrib list"
                  | KItemRuleWithCon "('upVar, 'var, 'metaVar) kItem rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                             "('var, 'upVar) ruleAttrib list"
                  | KLabelRule "('upVar, 'var, 'metaVar) kLabel rewrite"
                          "('var, 'upVar) ruleAttrib list"
                  | KLabelRuleWithCon "('upVar, 'var, 'metaVar) kLabel rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                             "('var, 'upVar) ruleAttrib list"
                  | BagRule "('upVar, 'var, 'metaVar) bag rewrite"
                             "('var, 'upVar) ruleAttrib list"
                  | BagRuleWithCon "('upVar, 'var, 'metaVar) bag rewrite"
                                 "('upVar, 'var, 'metaVar) kItem"
                                    "('var, 'upVar) ruleAttrib list"
                  | ListRule "('upVar, 'var, 'metaVar) theList rewrite"
                             "('var, 'upVar) ruleAttrib list"
                  | ListRuleWithCon "('upVar, 'var, 'metaVar) theList rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                           "('var, 'upVar) ruleAttrib list"
                  | SetRule "('upVar, 'var, 'metaVar) theSet rewrite"
                             "('var, 'upVar) ruleAttrib list"
                  | SetRuleWithCon "('upVar, 'var, 'metaVar) theSet rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                             "('var, 'upVar) ruleAttrib list"
                  | MapRule "('upVar, 'var, 'metaVar) theMap rewrite"
                            "('var, 'upVar) ruleAttrib list"
                  | MapRuleWithCon "('upVar, 'var, 'metaVar) theMap rewrite"
                           "('upVar, 'var, 'metaVar) kItem"
                           "('var, 'upVar) ruleAttrib list"

datatype kRequire = Requires string

datatype ('upVar, 'var, 'acapvar, 'metaVar) kModuleItem
                  = TheSyntax "'upVar kSyntax"
                   | Imports 'acapvar
                   | TheConfiguration "('upVar, 'var, 'metaVar) bag"
                   | TheRule "('upVar, 'var, 'metaVar) kRule"

datatype ('upVar, 'var, 'acapvar, 'metaVar) kModule =
              Module 'acapvar "('upVar, 'var, 'acapvar, 'metaVar) kModuleItem list"
datatype ('upVar, 'var, 'acapvar, 'metaVar) kFileItem = 
                  TheModule "('upVar, 'var, 'acapvar, 'metaVar) kModule"
                | TheRequires kRequire
datatype ('upVar, 'var, 'acapvar, 'metaVar) kFile = TheFile
                              "('upVar, 'var, 'acapvar, 'metaVar) kFileItem  nelist"

datatype ('upVar, 'metaVar) irKLabel
     = IRKLabel "'upVar label"
     | IRIdKLabel "'metaVar metaVar"

datatype ('upVar, 'var, 'metaVar) irKItem =
                                        IRKItem "('upVar, 'metaVar) irKLabel"
                                              "('upVar, 'var, 'metaVar) irKList"
                                              "'upVar sort list"
                                      | IRIdKItem "'metaVar metaVar" "'upVar sort list"
                                      |  IRHOLE "'upVar sort list"
and ('upVar, 'var, 'metaVar) irBigKWithBag = IRK "('upVar, 'var, 'metaVar) irK"
                                | IRList "('upVar, 'var, 'metaVar) irList"
                                | IRSet "('upVar, 'var, 'metaVar) irSet"
                                | IRMap "('upVar, 'var, 'metaVar) irMap"
                                | IRBag "('upVar, 'var, 'metaVar) irBag"
and ('upVar, 'var, 'metaVar) irBigKWithLabel =
             IRBigBag "('upVar, 'var, 'metaVar) irBigKWithBag"
           | IRBigLabel "('upVar, 'metaVar) irKLabel"
and ('upVar, 'var, 'metaVar) irK
         = KPat "('upVar, 'var, 'metaVar) irKItem list" "'metaVar metaVar option"
and ('upVar, 'var, 'metaVar) irKList =
         KListPatNoVar "('upVar, 'var, 'metaVar) irBigKWithLabel list"
       | KListPat "('upVar, 'var, 'metaVar) irBigKWithLabel list" "'metaVar metaVar"
                    "('upVar, 'var, 'metaVar) irBigKWithLabel list"
and ('upVar, 'var, 'metaVar) irList =
          ListPatNoVar "('upVar, 'var, 'metaVar) irK list"
        | ListPat "('upVar, 'var, 'metaVar) irK list" "'metaVar metaVar"
                   "('upVar, 'var, 'metaVar) irK list"
and ('upVar, 'var, 'metaVar) irSet
         = SetPat "('upVar, 'var, 'metaVar) irK list" "'metaVar metaVar option"
and ('upVar, 'var, 'metaVar) irMap 
  =  MapPat "(('upVar, 'var, 'metaVar) irK
                  * ('upVar, 'var, 'metaVar) irK) list" "'metaVar metaVar option"
and ('upVar, 'var, 'metaVar) irBag
  = BagPat "('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list" "'metaVar metaVar option"

datatype ('upVar, 'var, 'metaVar) matchFactor = 
   KLabelMatching "('upVar, 'metaVar) irKLabel"
 | KItemMatching "('upVar, 'var, 'metaVar) irKItem"
 | KListMatching "('upVar, 'var, 'metaVar) irKList"
 | KMatching "('upVar, 'var, 'metaVar) irK"
 | ListMatching "('upVar, 'var, 'metaVar) irList"
 | SetMatching "('upVar, 'var, 'metaVar) irSet"
 | MapMatching "('upVar, 'var, 'metaVar) irMap"
 | BagMatching "('upVar, 'var, 'metaVar) irBag"

datatype ('upVar, 'var, 'metaVar) pat
     = KLabelFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | KFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | KItemFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | ListFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | SetFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | MapFunPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
     | NormalPat "('upVar, 'var, 'metaVar) matchFactor"

datatype ('upVar, 'var, 'metaVar) suKLabel
     = SUKLabel "'upVar label"
     | SUIdKLabel "'metaVar metaVar"
     | SUKLabelFun "('upVar, 'var, 'metaVar) suKLabel"
                    "('upVar, 'var, 'metaVar) suKl list"
and ('upVar, 'var, 'metaVar) suKItem =
                                        SUKItem "('upVar, 'var, 'metaVar) suKLabel"
                                              "('upVar, 'var, 'metaVar) suKl list"
                                              "'upVar sort list"
                                      | SUIdKItem "'metaVar metaVar" "'upVar sort list"
                                      |  SUHOLE "'upVar sort list"
and ('upVar, 'var, 'metaVar) suBigKWithBag
                                = SUK "('upVar, 'var, 'metaVar) suKFactor list"
                                | SUList "('upVar, 'var, 'metaVar) suL list"
                                | SUSet "('upVar, 'var, 'metaVar) suS list"
                                | SUMap "('upVar, 'var, 'metaVar) suM list"
                                | SUBag "('upVar, 'var, 'metaVar) suB list"
and ('upVar, 'var, 'metaVar) suBigKWithLabel =
               SUBigBag "('upVar, 'var, 'metaVar) suBigKWithBag"
             | SUBigLabel "('upVar, 'var, 'metaVar) suKLabel"
and ('upVar, 'var, 'metaVar) suKFactor
         = ItemFactor "('upVar, 'var, 'metaVar) suKItem"
         | IdFactor "'metaVar metaVar"
         | SUKKItem "('upVar, 'var, 'metaVar) suKLabel"
                    "('upVar, 'var, 'metaVar) suKl list" "'upVar sort list"
and ('upVar, 'var, 'metaVar) suKl
         = ItemKl "('upVar, 'var, 'metaVar) suBigKWithLabel"
         | IdKl "'metaVar metaVar"
and ('upVar, 'var, 'metaVar) suL
         = ItemL "('upVar, 'var, 'metaVar) suKFactor list"
         | IdL "'metaVar metaVar"
         | SUListKItem "('upVar, 'var, 'metaVar) suKLabel"
                       "('upVar, 'var, 'metaVar) suKl list"
and ('upVar, 'var, 'metaVar) suS
         = ItemS "('upVar, 'var, 'metaVar) suKFactor list"
         | IdS "'metaVar metaVar"
         | SUSetKItem "('upVar, 'var, 'metaVar) suKLabel"
                      "('upVar, 'var, 'metaVar) suKl list"
and ('upVar, 'var, 'metaVar) suM
         = ItemM "('upVar, 'var, 'metaVar) suKFactor list"
                 "('upVar, 'var, 'metaVar) suKFactor list"
         | IdM "'metaVar metaVar"
         | SUMapKItem "('upVar, 'var, 'metaVar) suKLabel"
                      "('upVar, 'var, 'metaVar) suKl list"
and ('upVar, 'var, 'metaVar) suB
  = ItemB "'var var" "feature list" "('upVar, 'var, 'metaVar) suBigKWithBag"
  | IdB "'metaVar metaVar"

datatype ('upVar, 'var, 'metaVar) subsFactor = 
   KLabelSubs "('upVar, 'var, 'metaVar) suKLabel"
 | KItemSubs "('upVar, 'var, 'metaVar) suKItem"
 | KListSubs "('upVar, 'var, 'metaVar) suKl list"
 | KSubs "('upVar, 'var, 'metaVar) suKFactor list"
 | ListSubs "('upVar, 'var, 'metaVar) suL list"
 | SetSubs "('upVar, 'var, 'metaVar) suS list"
 | MapSubs "('upVar, 'var, 'metaVar) suM list"
 | BagSubs "('upVar, 'var, 'metaVar) suB list"

(*
subsort rules: cannot have a ground kitem term that has a sort K.
               can have a variable in KItem position that has a sort K.
               klabel svar is the only item that distinguishes user defined kitems.
*)
datatype ('upVar, 'var, 'metaVar) rulePat
    = FunPat "'upVar label"  "(('upVar, 'var, 'metaVar) pat * 
         ('upVar, 'var, 'metaVar) subsFactor *
                       ('upVar, 'var, 'metaVar) suKItem) list"
         "(('upVar, 'var, 'metaVar) pat * 
         ('upVar, 'var, 'metaVar) subsFactor *
                     ('upVar, 'var, 'metaVar) suKItem) option"
    | MacroPat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
                "('upVar, 'var, 'metaVar) suKFactor list"
    | AnywherePat "'upVar label" "('upVar, 'var, 'metaVar) irKList"
                "('upVar, 'var, 'metaVar) suKFactor list"
                "('upVar, 'var, 'metaVar) suKItem"
    | KRulePat "('upVar, 'var, 'metaVar) irK"
                "('upVar, 'var, 'metaVar) suKFactor list"
                "('upVar, 'var, 'metaVar) suKItem" bool
    | BagRulePat "('upVar, 'var, 'metaVar) irBag"
                "('upVar, 'var, 'metaVar) suB list"
                "('upVar, 'var, 'metaVar) suKItem" bool

(* define svar var type var etc *)
datatype 'a KItemSyntax = SingleTon "'a" | SetTon "'a \<Rightarrow> bool"

(* use for type check mapping to diff klabel var type vs klabel(klist) var type *)
datatype ('upVar, 'var, 'metaVar) varType = VarType "'metaVar metaVar"
                         | KLabelType "('upVar, 'var, 'metaVar) suKLabel"

definition BuiltinSorts :: "'upVar sort list" where
"BuiltinSorts = [KItem, K, KList, List, Set, Bag, Map, KResult, KLabel]"

definition topSubsort where
"topSubsort = [(K, Top), (KList, Top), (List,Top), (Set,Top), (Bag,Top), (Map, Top), (KLabel, Top)]"

definition isConst :: "'upVar label \<Rightarrow> bool" where
"isConst a = (case a of ConstToLabel x \<Rightarrow> True | _ \<Rightarrow> False)"

definition labelToConst where
"labelToConst a = (case a of ConstToLabel x \<Rightarrow> Some x | _ \<Rightarrow> None)"

(* datatype 'metaVar metaVar = ConfiVar 'metaVar | RuleVar 'metaVar | HoleVar *)

definition abc :: "real \<Rightarrow> string" where
"abc a = ''a''"

primrec getMaxNum :: "'metaVar metaVar list \<Rightarrow> nat \<Rightarrow> nat" where
"getMaxNum [] n = n"
| "getMaxNum (a#l) n = (case a of Defined aa \<Rightarrow> getMaxNum l n
              | Generated x \<Rightarrow> if x < n then getMaxNum l n else getMaxNum l x)"

definition freshVar :: "'metaVar metaVar list \<Rightarrow> 'metaVar metaVar" where
"freshVar a = (case getMaxNum a 0 of x \<Rightarrow> (Generated x))"

fun symbolsToKLabelAux where
"symbolsToKLabelAux (Single (Terminal s)) = s"
| "symbolsToKLabelAux (Single (NonTerminal v)) = ''_''"
| "symbolsToKLabelAux (Con (NonTerminal v) l) = ''_''@(symbolsToKLabelAux l)"
| "symbolsToKLabelAux (Con (Terminal s) l) = s@(symbolsToKLabelAux l)"

definition symbolsToKLabel where
"symbolsToKLabel a = OtherLabel (''\047''@symbolsToKLabelAux a)"

primrec isGroundTermInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> bool"
    and isGroundTermInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> bool"
    and isGroundTermInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> bool"
    and isGroundTermInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> bool"
    and isGroundTermInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> bool"
    and isGroundTermInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> bool"
    and isGroundTermInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> bool"
    and isGroundTermInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> bool"
    and isGroundTermInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> bool"
    and isGroundTermInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> bool"
    and isGroundTermInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> bool"
    and isGroundTermInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> bool"
    and isGroundTermInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> bool"
    and isGroundTermInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> bool"
    and isGroundTermInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> bool"
    and isGroundTermInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> bool"
    and isGroundTermInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> bool"
    and isGroundTermInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> bool"
 where
  "isGroundTermInKLabel (KLabelC a) = True"
| "isGroundTermInKLabel (KLabelFun a b) = (isGroundTermInKLabel a \<and> isGroundTermInKListR b)"
| "isGroundTermInKLabel (IdKLabel n) = False"
| "isGroundTermInKLabelR (KTerm n) = isGroundTermInKLabel n"
| "isGroundTermInKLabelR (KRewrite l r) = ((isGroundTermInKLabel l) \<and> (isGroundTermInKLabel r))"
| "isGroundTermInKItem (KItemC l r ty) = ((isGroundTermInKLabelR l) \<and> (isGroundTermInKListR r))"
| "isGroundTermInKItem (Constant a b) = True"
| "isGroundTermInKItem (IdKItem a b) = False"
| "isGroundTermInKItem (HOLE a) = True"
| "isGroundTermInKItemR (KTerm t) = isGroundTermInKItem t"
| "isGroundTermInKItemR (KRewrite l r) = False"
| "isGroundTermInKList (KListCon b t) = ((isGroundTermInKListR b) \<and> (isGroundTermInKListR t))"
| "isGroundTermInKList UnitKList = True"
| "isGroundTermInKList (IdKList a) = False"
| "isGroundTermInKList (KListItem a) = (isGroundTermInBigKWithBag a)"
| "isGroundTermInKListR (KTerm t) = isGroundTermInKList t"
| "isGroundTermInKListR (KRewrite l r) = False"
| "isGroundTermInBigKWithBag (TheBigK a) = isGroundTermInBigK a"
| "isGroundTermInBigKWithBag (TheBigBag b) = isGroundTermInBagR b"
| "isGroundTermInBigKWithBag (TheLabel b) = isGroundTermInKLabelR b"
| "isGroundTermInBigK (TheK t) = isGroundTermInKR t"
| "isGroundTermInBigK (TheList t) = isGroundTermInListR t"
| "isGroundTermInBigK (TheSet t) = isGroundTermInSetR t"
| "isGroundTermInBigK (TheMap t) = isGroundTermInMapR t"
| "isGroundTermInK (Tilda a t) = ((isGroundTermInKR a) \<and> (isGroundTermInKR t))"
| "isGroundTermInK UnitK = True"
| "isGroundTermInK (IdK a) = False"
| "isGroundTermInK (KFun a b) = ((isGroundTermInKLabel a) \<and> (isGroundTermInKListR b))"
| "isGroundTermInK (SingleK a) = (isGroundTermInKItemR a)"
| "isGroundTermInKR (KTerm a) = (isGroundTermInK a)"
| "isGroundTermInKR (KRewrite l r) = False"
| "isGroundTermInList (ListCon l r) = ((isGroundTermInListR l) \<and> (isGroundTermInListR r))"
| "isGroundTermInList UnitList = True"
| "isGroundTermInList (IdList a) = False"
| "isGroundTermInList (ListItem a) = isGroundTermInKR a"
| "isGroundTermInList (ListFun a b) = ((isGroundTermInKLabel a) \<and> (isGroundTermInKListR b))"
| "isGroundTermInListR (KTerm a) = (isGroundTermInList a)"
| "isGroundTermInListR (KRewrite l r) = False"
| "isGroundTermInSet (SetCon l r) = ((isGroundTermInSetR l) \<and> (isGroundTermInSetR r))"
| "isGroundTermInSet UnitSet = True"
| "isGroundTermInSet (IdSet a) = False"
| "isGroundTermInSet (SetItem a) = isGroundTermInKR a"
| "isGroundTermInSet (SetFun a b) = ((isGroundTermInKLabel a) \<and> (isGroundTermInKListR b))"
| "isGroundTermInSetR (KTerm a) = (isGroundTermInSet a)"
| "isGroundTermInSetR (KRewrite l r) = False"
| "isGroundTermInMap (MapCon l r) = ((isGroundTermInMapR l) \<and> (isGroundTermInMapR r))"
| "isGroundTermInMap UnitMap = True"
| "isGroundTermInMap (IdMap a) = False"
| "isGroundTermInMap (MapItem l r) = ((isGroundTermInKR l) \<and> (isGroundTermInKR r))"
| "isGroundTermInMap (MapFun a b) = ((isGroundTermInKLabel a) \<and> (isGroundTermInKListR b))"
| "isGroundTermInMapR (KTerm a) = (isGroundTermInMap a)"
| "isGroundTermInMapR (KRewrite l r) = False"
| "isGroundTermInBag (BagCon l r) = ((isGroundTermInBagR l) \<and> (isGroundTermInBagR r))"
| "isGroundTermInBag UnitBag = True"
| "isGroundTermInBag (IdBag a) = False"
| "isGroundTermInBag (Xml a n t) =  isGroundTermInBagR t"
| "isGroundTermInBag (SingleCell a n t) =  isGroundTermInBigK t"
| "isGroundTermInBagR (KTerm a) = (isGroundTermInBag a)"
| "isGroundTermInBagR (KRewrite l r) = False"

fun isGroundTermInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel
                        \<Rightarrow> bool"
    and isGroundTermInSUKItem :: "('upVar, 'var, 'metaVar) suKItem
                         \<Rightarrow> bool"
    and isGroundTermInSUKList :: "('upVar, 'var, 'metaVar) suKl list
                          \<Rightarrow> bool"
    and isGroundTermInSUK :: "('upVar, 'var, 'metaVar) suKFactor list 
                          \<Rightarrow> bool"
    and isGroundTermInSUList :: "('upVar, 'var, 'metaVar) suL list 
                          \<Rightarrow> bool"
    and isGroundTermInSUSet :: "('upVar, 'var, 'metaVar) suS list 
                           \<Rightarrow> bool"
    and isGroundTermInSUMap :: "('upVar, 'var, 'metaVar) suM list 
                           \<Rightarrow> bool"
    and isGroundTermInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag 
                       \<Rightarrow> bool"
    and isGroundTermInSUBigKWithLabel :: "('upVar, 'var, 'metaVar) suBigKWithLabel
                       \<Rightarrow> bool"
    and isGroundTermInSUBag :: "('upVar, 'var, 'metaVar) suB list 
                       \<Rightarrow> bool"
 where 
  "isGroundTermInSUKLabel (SUKLabel a) = True"
| "isGroundTermInSUKLabel (SUKLabelFun a b) =
            (isGroundTermInSUKLabel a \<and> isGroundTermInSUKList b)"
| "isGroundTermInSUKLabel (SUIdKLabel n) = False"
| "isGroundTermInSUKItem (SUKItem l r ty) =
            (isGroundTermInSUKLabel l \<and> isGroundTermInSUKList r)"
| "isGroundTermInSUKItem (SUIdKItem a b) = False"
| "isGroundTermInSUKItem (SUHOLE a) = True"
| "isGroundTermInSUKList [] = True"
| "isGroundTermInSUKList (b#l) = (case b of ItemKl a \<Rightarrow>
        isGroundTermInSUBigKWithLabel a \<and> isGroundTermInSUKList l
      | _ \<Rightarrow> False)"
| "isGroundTermInSUBigKWithLabel (SUBigBag a) = isGroundTermInSUBigKWithBag a"
| "isGroundTermInSUBigKWithLabel (SUBigLabel a) = isGroundTermInSUKLabel a"
| "isGroundTermInSUBigKWithBag (SUK a) = isGroundTermInSUK a"
| "isGroundTermInSUBigKWithBag (SUList a) = isGroundTermInSUList a"
| "isGroundTermInSUBigKWithBag (SUSet a) = isGroundTermInSUSet a"
| "isGroundTermInSUBigKWithBag (SUMap a) = isGroundTermInSUMap a"
| "isGroundTermInSUBigKWithBag (SUBag a) = isGroundTermInSUBag a"
| "isGroundTermInSUK [] = True"
| "isGroundTermInSUK (b#l) = (case b of ItemFactor x \<Rightarrow>
          (isGroundTermInSUKItem x \<and> isGroundTermInSUK l)
     | IdFactor x \<Rightarrow> False
     | SUKKItem x y ty \<Rightarrow> (isGroundTermInSUKLabel x \<and>
                          isGroundTermInSUKList y \<and> isGroundTermInSUK l))"
| "isGroundTermInSUList [] = True"
| "isGroundTermInSUList (b#l) = (case b of ItemL x \<Rightarrow>
          (isGroundTermInSUK x \<and> isGroundTermInSUList l)
     | IdL x \<Rightarrow> False
     | SUListKItem x y \<Rightarrow> (isGroundTermInSUKLabel x \<and>
                          isGroundTermInSUKList y \<and> isGroundTermInSUList l))"
| "isGroundTermInSUSet [] = True"
| "isGroundTermInSUSet (b#l) = (case b of ItemS x \<Rightarrow>
          (isGroundTermInSUK x \<and> isGroundTermInSUSet l)
     | IdS x \<Rightarrow> False
     | SUSetKItem x y \<Rightarrow> (isGroundTermInSUKLabel x \<and>
                          isGroundTermInSUKList y \<and> isGroundTermInSUSet l))"
| "isGroundTermInSUMap [] = True"
| "isGroundTermInSUMap (b#l) = (case b of ItemM x y \<Rightarrow>
          (isGroundTermInSUK x \<and> isGroundTermInSUK y \<and> isGroundTermInSUMap l)
     | IdM x \<Rightarrow> False
     | SUMapKItem x y \<Rightarrow> (isGroundTermInSUKLabel x \<and>
                          isGroundTermInSUKList y \<and> isGroundTermInSUMap l))"
| "isGroundTermInSUBag [] = True"
| "isGroundTermInSUBag (b#l) = (case b of ItemB x y z \<Rightarrow>
          (isGroundTermInSUBigKWithBag z \<and> isGroundTermInSUBag l)
     | IdB x \<Rightarrow> False)"

fun insertA :: "('upVar * 'a list) list
               \<Rightarrow> 'upVar \<Rightarrow> 'a
                       \<Rightarrow> ('upVar * 'a list) list" where
"insertA [] a x = [(a,[x])]"
| "insertA ((a,kl)#l) v x = (if a = v then (a,x#kl)#l  else (a,kl)# (insertA l v x))"

fun insertAll :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insertAll a [] = a"
| "insertAll a (b#l) = insertAll (List.insert b a) l"

fun getRealSyntax :: "'upVar kSyntax list
         \<Rightarrow> 'upVar kSyntax list" where
"getRealSyntax [] = []"
| "getRealSyntax ((Syntax a b c)#l) = (Syntax a b c)#(getRealSyntax l)"
| "getRealSyntax ((Subsort a b)#l) = (getRealSyntax l)"
| "getRealSyntax ((Token a b c)#l) = (Token a b c)#(getRealSyntax l)"
| "getRealSyntax ((ListSyntax a b c d)#l) = (ListSyntax a b c d)#(getRealSyntax l)"

fun getSyntaxBySort where
"getSyntaxBySort [] = []"
| "getSyntaxBySort ((Syntax a b c)#l) = insertA (getSyntaxBySort l) a (Syntax a b c)"
| "getSyntaxBySort ((Subsort a b)#l) = (getSyntaxBySort l)"
| "getSyntaxBySort ((Token a b c)#l) = insertA (getSyntaxBySort l) a (Token a b c)"
| "getSyntaxBySort ((ListSyntax a b c d)#l) = insertA (getSyntaxBySort l) a (ListSyntax a b c d)"

definition noOverlapSyntax :: "synAttrib list \<Rightarrow> bool" where
"noOverlapSyntax l = ((Function \<in> set l \<longrightarrow>
         (Seqstrict \<notin> set l \<and> (\<forall> s . Strict s \<notin> set l)))
        \<or> (Seqstrict \<in> set l \<longrightarrow>
         (Function \<notin> set l \<and> (\<forall> s . Strict s \<notin> set l)))
        \<or> (\<exists> s . Strict s \<in> set l \<longrightarrow>
         (Function \<notin> set l \<and> Seqstrict \<notin> set l)))"

fun isValidSyntax :: "'upVar kSyntax list \<Rightarrow> bool" where
"isValidSyntax [] = True"
| "isValidSyntax ((Syntax a b c)#l) = (if noOverlapSyntax c then isValidSyntax l else False)"
| "isValidSyntax ((Subsort a b)#l) = isValidSyntax l"
| "isValidSyntax ((Token a b c)#l) = (if noOverlapSyntax c then isValidSyntax l else False)"
| "isValidSyntax ((ListSyntax a b c d)#l) = (if noOverlapSyntax d then isValidSyntax l else False)"

function regMatch :: "reg \<Rightarrow> string \<Rightarrow> bool"
   and regSplit :: "reg \<Rightarrow> reg \<Rightarrow> string \<Rightarrow>
                  string \<Rightarrow> bool"
   and regPart :: "reg \<Rightarrow> string \<Rightarrow> string \<Rightarrow> bool" where
"regMatch a s = (case a of Eps \<Rightarrow> s = [] 
     | Sym x \<Rightarrow> s = [x]
      | Alt x y \<Rightarrow> regMatch x s \<or> regMatch y s
   | TheSeq x y \<Rightarrow> regSplit x y [] s
   | Rep x \<Rightarrow> (case s of [] \<Rightarrow> True | b#bl \<Rightarrow> regPart x [b] bl))"
| "regPart x a [] = regMatch x a"
| "regPart x a (s#l) = (if regMatch x a then regMatch (Rep x) (s#l) else regPart x (a@[s]) l)"
| "regSplit x y s [] = False"
| "regSplit x y s (a#al) = (if regMatch x s then regMatch y (a#al) else regSplit x y (s@[a]) al)"
by pat_completeness auto

termination sorry

fun getAllRedex :: "'upVar kSyntax list \<Rightarrow> reg list" where
"getAllRedex [] = []"
| "getAllRedex ((Token a s c)#l) = s#(getAllRedex l)"
| "getAllRedex (a#l) = getAllRedex l"

primrec validArgSyntaxAux where
"validArgSyntaxAux [] = True"
| "validArgSyntaxAux (a#l) = (if a \<in> {[Top],[KList],[KResult]} then False
                                else validArgSyntaxAux l)"

fun validArgSynax where
"validArgSynax [] = True"
| "validArgSynax ((a,b,c)#l) = (validArgSyntaxAux b \<and> validArgSynax l)"

fun validSyntaxs where
"validSyntaxs [] = True"
| "validSyntaxs ((a,b,c,nl,True)#l) = ((a \<notin> {[Top], [KList], [Bag]}) \<and> (validSyntaxs l))"
| "validSyntaxs ((a,b,c,nl,False)#l) = 
           ((a \<notin> {[Top], [KList], [Bag], [List], [Set], [Map], [KLabel], [K]}) \<and> (validSyntaxs l))"

(* deal with strict attributes *)
primrec getStrictInAttributes :: "synAttrib list \<Rightarrow> nat list option" where
"getStrictInAttributes [] = None"
| "getStrictInAttributes (b#l) = (case b of Strict nl \<Rightarrow> Some nl
                   | _ \<Rightarrow> getStrictInAttributes l)"

primrec generatingStrict :: "'upVar list \<Rightarrow> nat \<Rightarrow> nat list" where
"generatingStrict [] n = []"
| "generatingStrict (b#l) n = n#(generatingStrict l (n + 1))"

definition getStrictList :: "synAttrib list
               \<Rightarrow> 'upVar list \<Rightarrow> nat list" where
"getStrictList sl tyl = (case getStrictInAttributes sl of None \<Rightarrow> []
      | Some nl \<Rightarrow> if nl = [] then generatingStrict tyl 1 else nl)"

primrec hasOutOfPositionStrict :: "nat list \<Rightarrow> 'upVar list \<Rightarrow> bool" where
"hasOutOfPositionStrict [] L = False"
| "hasOutOfPositionStrict (n#l) L = (if n > length L then True else hasOutOfPositionStrict l L)"

primrec getRidStrictAttrs :: "synAttrib list
                      \<Rightarrow> synAttrib list" where
"getRidStrictAttrs [] = []"
| "getRidStrictAttrs (b#l) = (case b of Strict nl \<Rightarrow> getRidStrictAttrs l
                   | Seqstrict \<Rightarrow> getRidStrictAttrs l
                     | _ \<Rightarrow> b#(getRidStrictAttrs l))"

(* translate syntactic definitions to a database *)
fun getKLabelName :: "synAttrib list \<Rightarrow> 'upVar label option" where
"getKLabelName [] = None"
| "getKLabelName ((Klabel a)#l) = Some (OtherLabel a)"
| "getKLabelName (a#l) = getKLabelName l"

fun getAllSyntaxInKModuleItemList :: "('upVar, 'var, 'acapvar, 'metaVar) kModuleItem list
                               \<Rightarrow> 'upVar kSyntax list" where
 "getAllSyntaxInKModuleItemList [] = []"
| "getAllSyntaxInKModuleItemList ((TheSyntax x)#l) =  List.insert x (getAllSyntaxInKModuleItemList l)"
| "getAllSyntaxInKModuleItemList ((Imports x)#l) = (getAllSyntaxInKModuleItemList l)"
| "getAllSyntaxInKModuleItemList ((TheConfiguration x)#l) = (getAllSyntaxInKModuleItemList l)"
| "getAllSyntaxInKModuleItemList ((TheRule x)#l) = (getAllSyntaxInKModuleItemList l)"

fun getAllSyntaxInKFile :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
                                         \<Rightarrow> 'upVar kSyntax list" where
"getAllSyntaxInKFile (TheFile (Single (TheRequires m))) = []"
| "getAllSyntaxInKFile (TheFile (Single (TheModule (Module a m)))) =  getAllSyntaxInKModuleItemList m"
| "getAllSyntaxInKFile (TheFile (Con (TheRequires m) xs)) = getAllSyntaxInKFile (TheFile xs)"
| "getAllSyntaxInKFile (TheFile (Con (TheModule (Module a m)) xs))
           =  insertAll (getAllSyntaxInKModuleItemList m) (getAllSyntaxInKFile (TheFile xs))"

fun isBracket :: "synAttrib list \<Rightarrow> bool" where
"isBracket [] = False"
| "isBracket (Bracket#l) = True"
| "isBracket (a#l) = isBracket l"

fun getArgSortsInSyntax where
"getArgSortsInSyntax (Single (NonTerminal a)) = [[a]]"
| "getArgSortsInSyntax (Single (Terminal a)) = []"
| "getArgSortsInSyntax (Con (NonTerminal a) l) = [a]#(getArgSortsInSyntax l)"
| "getArgSortsInSyntax (Con (Terminal a) l) = (getArgSortsInSyntax l)"

primrec syntaxToKItem where
"syntaxToKItem (Syntax a b c) = (if isBracket c then None
      else (case getKLabelName c of None \<Rightarrow>
    (if Function \<in> set c then 
          Some [([a], getArgSortsInSyntax b,
            SingleTon (symbolsToKLabel b), (getRidStrictAttrs c), True)]
     else (if
       hasOutOfPositionStrict (getStrictList c (getArgSortsInSyntax b)) (getArgSortsInSyntax b)
       then None else Some [([a], getArgSortsInSyntax b,
             SingleTon (symbolsToKLabel b), c, False)]))
       | Some t \<Rightarrow>
       (if Function \<in> set c
                 then Some [([a], getArgSortsInSyntax b, SingleTon t, (getRidStrictAttrs c), True)]
   else (if hasOutOfPositionStrict
                 (getStrictList c (getArgSortsInSyntax b)) (getArgSortsInSyntax b)
       then None else Some [([a], getArgSortsInSyntax b, SingleTon t, c, False)]))))"
| "syntaxToKItem (Token a s c) =
      Some [([a], [], SetTon (\<lambda> x . (case x of TokenLabel y
       \<Rightarrow> regMatch s y | _ \<Rightarrow> False)),
     (getRidStrictAttrs c), Function \<in> set c)]"
| "syntaxToKItem (Subsort a b) = None"
| "syntaxToKItem (ListSyntax a b s c) = (case getKLabelName c of None
      \<Rightarrow> if hasOutOfPositionStrict (getStrictList c [[b],[a]]) [[b],[a]]
       then None else (Some [([a],[[b],[a]], SingleTon (symbolsToKLabel (Con (NonTerminal b)
                 (Con (Terminal s) (Single (NonTerminal a))))), c, False),
                 ([a],[],SingleTon (UnitLabel a),(getRidStrictAttrs c), False)])
      | Some t \<Rightarrow> if hasOutOfPositionStrict (getStrictList c [[b],[a]]) [[b],[a]]
       then None else (Some [([a],[[b],[a]], SingleTon t,c, False),
                    ([a],[],SingleTon (UnitLabel a),(getRidStrictAttrs c), False)]))"

primrec syntaxSetToKItemSetAux where
"syntaxSetToKItemSetAux [] order = Some []"
| "syntaxSetToKItemSetAux (a#l) order = (case syntaxToKItem a of
            None \<Rightarrow> None
           | Some l' \<Rightarrow>
        (case (syntaxSetToKItemSetAux l (order@[a])) of None \<Rightarrow> None
            | Some la \<Rightarrow> Some (l'@la)))"

definition syntaxSetToKItemTest where
"syntaxSetToKItemTest Theory
   = syntaxSetToKItemSetAux (getAllSyntaxInKFile Theory) []"

definition syntaxSetToKItemSet where
"syntaxSetToKItemSet Theory 
   = (case syntaxSetToKItemTest Theory of None \<Rightarrow> []
                      | Some l \<Rightarrow> l)"

fun isUnitLabelInList where
"isUnitLabelInList s [] = True"
| "isUnitLabelInList (SingleTon s) ((a,b,SingleTon c, nl, d)#l)
                = (if s = c then False else isUnitLabelInList (SingleTon s) l)"
| "isUnitLabelInList (SingleTon s) ((a,b,SetTon c, nl, d)#l)
               = (if c s then False else isUnitLabelInList (SingleTon s) l)"
| "isUnitLabelInList (SetTon s) ((a,b,SingleTon c, nl, d)#l)
                = (if  s c then False else isUnitLabelInList (SetTon s) l)"
| "isUnitLabelInList (SetTon s) ((a,b,SetTon c, nl, d)#l)
               = (isUnitLabelInList (SetTon s) l)"

fun isUnitLabel where
"isUnitLabel [] = True"
| "isUnitLabel (a#l) = (case a of (u,v,w,nl,t) \<Rightarrow>
                  isUnitLabelInList w l \<and> isUnitLabel l)"

end