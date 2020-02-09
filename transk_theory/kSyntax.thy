theory kSyntax
imports Main HOL.Real
begin

(* this file defines all syntax of K and its helper functions *)

(* k syntax *)
datatype 'a state = Continue 'a | Stop 'a | Div 'a

datatype ('a, 'b) oneStep = Success 'a | Failure 'b

datatype 'a nelist = Single 'a | Con 'a "'a nelist"

datatype theConstant = IntConst int | FloatConst real | StringConst string
                     | BoolConst bool | IdConst string

datatype 'var var = littleK | OtherVar 'var

datatype 'upVar sort = Bool | K | KItemSort | KLabelSort | KResult | KList | List | Set | Map | Bag
                   | OtherSort 'upVar

datatype 'metaVar metaVar = Defined 'metaVar | Generated nat | FunHole

datatype 'upVar label = UnitLabel "'upVar sort" | ConstToLabel theConstant
            | Sort | GetKLabel | IsKResult | AndBool | NotBool | OtherLabel string
            | TokenLabel string

datatype key = Star | Question

datatype stdType = Stdin | Stdout

datatype feature = Multiplicity key | Stream stdType | DotDotDot

datatype 'a rewrite = KTerm 'a | KRewrite 'a 'a

datatype ('upVar, 'metaVar) irKLabel
     = IRKLabel "'upVar label"
     | IRIdKLabel "'metaVar metaVar"

datatype ('upVar, 'var, 'metaVar) irKItem =
                                        IRKItem "('upVar, 'metaVar) irKLabel"
                                              "('upVar, 'var, 'metaVar) irKList"
                                              "'upVar sort"
                                      | IRIdKItem "'metaVar metaVar" "'upVar sort"
                                      |  IRHOLE "'upVar sort"
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
           KListPat "('upVar, 'var, 'metaVar) irBigKWithLabel list" "'metaVar metaVar option"
                    "('upVar, 'var, 'metaVar) irBigKWithLabel list"
and ('upVar, 'var, 'metaVar) irList
         = ListPat "('upVar, 'var, 'metaVar) irK list" "'metaVar metaVar option"
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
                                              "'upVar sort"
                                      | SUIdKItem "'metaVar metaVar" "'upVar sort"
                                      |  SUHOLE "'upVar sort"
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
                    "('upVar, 'var, 'metaVar) suKl list" "'upVar sort"
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
"BuiltinSorts = [KItemSort, K, KList, List, Set, Bag, Map, KResult, KLabelSort]"

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