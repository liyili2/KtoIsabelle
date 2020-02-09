theory kGetters
imports Main kSyntax
begin

(* This file defines all getter functions that will be used later*)

primrec getAllMetaVarsInIRKLabel ::
                 "('svar, 'metaVar) irKLabel \<Rightarrow> 'metaVar metaVar list" where
  "getAllMetaVarsInIRKLabel (IRKLabel a) = []"
| "getAllMetaVarsInIRKLabel (IRIdKLabel n) = [n]"

fun getAllMetaVarsInIRKItem ::
                 "('upVar, 'var, 'metaVar) irKItem \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRKList ::
                  "('upVar, 'var, 'metaVar) irKList \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRK :: "('upVar, 'var, 'metaVar) irK \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRList ::
                  "('upVar, 'var, 'metaVar) irList \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRSet :: "('upVar, 'var, 'metaVar) irSet \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRMap :: "('upVar, 'var, 'metaVar) irMap \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRBigKWithBag ::
           "('upVar, 'var, 'metaVar) irBigKWithBag \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRBigKWithLabel ::
           "('upVar, 'var, 'metaVar) irBigKWithLabel \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInIRBag :: "('upVar, 'var, 'metaVar) irBag \<Rightarrow> 'metaVar metaVar list"
where
 "getAllMetaVarsInIRKItem (IRKItem l r ty) =
                                 (getAllMetaVarsInIRKLabel l)@(getAllMetaVarsInIRKList r)"
| "getAllMetaVarsInIRKItem (IRIdKItem a b) = [a]"
| "getAllMetaVarsInIRKItem (IRHOLE a) = []"
| "getAllMetaVarsInIRKList (KListPat a b c) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc y . (getAllMetaVarsInIRBigKWithLabel y)@acc) [] (a@c)
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc y . (getAllMetaVarsInIRBigKWithLabel y)@acc) [] (a@c)))"
| "getAllMetaVarsInIRBigKWithBag (IRBag b) = getAllMetaVarsInIRBag b"
| "getAllMetaVarsInIRBigKWithBag (IRK t) = getAllMetaVarsInIRK t"
| "getAllMetaVarsInIRBigKWithBag (IRList t) = getAllMetaVarsInIRList t"
| "getAllMetaVarsInIRBigKWithBag (IRSet t) = getAllMetaVarsInIRSet t"
| "getAllMetaVarsInIRBigKWithBag (IRMap t) = getAllMetaVarsInIRMap t"
| "getAllMetaVarsInIRBigKWithLabel (IRBigBag t) = getAllMetaVarsInIRBigKWithBag t"
| "getAllMetaVarsInIRBigKWithLabel (IRBigLabel t) = getAllMetaVarsInIRKLabel t"
| "getAllMetaVarsInIRK (KPat a b) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc y . (getAllMetaVarsInIRKItem y)@acc) [] a
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc y . (getAllMetaVarsInIRKItem y)@acc) [] a))"
| "getAllMetaVarsInIRList (ListPat a b c) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] (a@c)
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] (a@c)))"
| "getAllMetaVarsInIRSet (SetPat a b) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] a
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] a))"
| "getAllMetaVarsInIRMap (MapPat a b) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc (x,y) . (getAllMetaVarsInIRK x)@(getAllMetaVarsInIRK y)@acc) [] a
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc (x,y) .
                       (getAllMetaVarsInIRK x)@(getAllMetaVarsInIRK y)@acc) [] a))"
| "getAllMetaVarsInIRBag (BagPat a b) = (case b of None \<Rightarrow> 
           foldl (\<lambda> acc (x,y,z) . (getAllMetaVarsInIRBigKWithBag z)@acc) [] a
        | Some x \<Rightarrow>
                 x#(foldl (\<lambda> acc (x,y,z) . (getAllMetaVarsInIRBigKWithBag z)@acc) [] a))"

fun getAllMetaVarsInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel
                        \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUKItem ::
                  "('upVar, 'var, 'metaVar) suKItem \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUKList ::
                   "('upVar, 'var, 'metaVar) suKl list \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUK ::
                   "('upVar, 'var, 'metaVar) suKFactor list \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUList ::
                   "('upVar, 'var, 'metaVar) suL list \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUSet ::
                    "('upVar, 'var, 'metaVar) suS list \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUMap ::
                    "('upVar, 'var, 'metaVar) suM list \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUBigKWithBag ::
                "('upVar, 'var, 'metaVar) suBigKWithBag \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUBigKWithLabel ::
                "('upVar, 'var, 'metaVar) suBigKWithLabel \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSUBag ::
                   "('upVar, 'var, 'metaVar) suB list \<Rightarrow> 'metaVar metaVar list"
 where 
  "getAllMetaVarsInSUKLabel (SUKLabel a) = []"
| "getAllMetaVarsInSUKLabel (SUKLabelFun a b) = getAllMetaVarsInSUKList b"
| "getAllMetaVarsInSUKLabel (SUIdKLabel n) = [n]"
| "getAllMetaVarsInSUKItem (SUKItem l r ty) =
                                 (getAllMetaVarsInSUKLabel l)@(getAllMetaVarsInSUKList r)"
| "getAllMetaVarsInSUKItem (SUIdKItem a b) = [a]"
| "getAllMetaVarsInSUKItem (SUHOLE a) = []"
| "getAllMetaVarsInSUKList [] = []"
| "getAllMetaVarsInSUKList (b#l) = (case b of (IdKl a) \<Rightarrow> [a]
             | ItemKl a \<Rightarrow> getAllMetaVarsInSUBigKWithLabel a)"
| "getAllMetaVarsInSUBigKWithBag (SUBag b) = getAllMetaVarsInSUBag b"
| "getAllMetaVarsInSUBigKWithBag (SUK t) = getAllMetaVarsInSUK t"
| "getAllMetaVarsInSUBigKWithBag (SUList t) = getAllMetaVarsInSUList t"
| "getAllMetaVarsInSUBigKWithBag (SUSet t) = getAllMetaVarsInSUSet t"
| "getAllMetaVarsInSUBigKWithBag (SUMap t) = getAllMetaVarsInSUMap t"
| "getAllMetaVarsInSUBigKWithLabel (SUBigBag t) = getAllMetaVarsInSUBigKWithBag t"
| "getAllMetaVarsInSUBigKWithLabel (SUBigLabel t) = getAllMetaVarsInSUKLabel t"
| "getAllMetaVarsInSUK [] = []"
| "getAllMetaVarsInSUK (b#l) = (case b of (IdFactor x) \<Rightarrow> [x]
        | ItemFactor x \<Rightarrow> getAllMetaVarsInSUKItem x
        | SUKKItem l r ty \<Rightarrow> (getAllMetaVarsInSUKLabel l)@(getAllMetaVarsInSUKList r))"
| "getAllMetaVarsInSUList [] = []"
| "getAllMetaVarsInSUList (b#l) = (case b of (IdL x) \<Rightarrow> [x]
        | ItemL x \<Rightarrow> getAllMetaVarsInSUK x
        | SUListKItem l r \<Rightarrow> (getAllMetaVarsInSUKLabel l)@(getAllMetaVarsInSUKList r))"
| "getAllMetaVarsInSUSet [] = []"
| "getAllMetaVarsInSUSet (b#l) = (case b of (IdS x) \<Rightarrow> [x]
        | ItemS x \<Rightarrow> getAllMetaVarsInSUK x
        | SUSetKItem l r \<Rightarrow> (getAllMetaVarsInSUKLabel l)@(getAllMetaVarsInSUKList r))"
| "getAllMetaVarsInSUMap [] = []"
| "getAllMetaVarsInSUMap (b#l) = (case b of (IdM x) \<Rightarrow> [x]
        | ItemM x y \<Rightarrow> (getAllMetaVarsInSUK x)@(getAllMetaVarsInSUK y)
        | SUMapKItem l r \<Rightarrow> (getAllMetaVarsInSUKLabel l)@(getAllMetaVarsInSUKList r))"
| "getAllMetaVarsInSUBag [] = []"
| "getAllMetaVarsInSUBag (b#l) = (case b of (IdB x) \<Rightarrow> [x]
        | ItemB x y z \<Rightarrow> getAllMetaVarsInSUBigKWithBag z)"

primrec getAllMetaVarsInMatchFactor ::
       "('upVar, 'var, 'metaVar) matchFactor \<Rightarrow> 'metaVar metaVar list" where
"getAllMetaVarsInMatchFactor (KLabelMatching a) = getAllMetaVarsInIRKLabel a"
| "getAllMetaVarsInMatchFactor (KItemMatching a) = getAllMetaVarsInIRKItem a"
| "getAllMetaVarsInMatchFactor (KListMatching a) = getAllMetaVarsInIRKList a"
| "getAllMetaVarsInMatchFactor (KMatching a) = getAllMetaVarsInIRK a"
| "getAllMetaVarsInMatchFactor (ListMatching a) = getAllMetaVarsInIRList a"
| "getAllMetaVarsInMatchFactor (SetMatching a) = getAllMetaVarsInIRSet a"
| "getAllMetaVarsInMatchFactor (MapMatching a) = getAllMetaVarsInIRMap a"
| "getAllMetaVarsInMatchFactor (BagMatching a) = getAllMetaVarsInIRBag a"

primrec getAllMetaVarsInPat ::
       "('upVar, 'var, 'metaVar) pat \<Rightarrow> 'metaVar metaVar list" where
"getAllMetaVarsInPat (KLabelFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (KFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (KItemFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (ListFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (SetFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (MapFunPat a b) = getAllMetaVarsInIRKList b"
| "getAllMetaVarsInPat (NormalPat a) = getAllMetaVarsInMatchFactor a"

primrec getAllMetaVarsInSubsFactor ::
       "('upVar, 'var, 'metaVar) subsFactor \<Rightarrow> 'metaVar metaVar list" where
"getAllMetaVarsInSubsFactor (KLabelSubs a) = getAllMetaVarsInSUKLabel a"
| "getAllMetaVarsInSubsFactor (KItemSubs a) = getAllMetaVarsInSUKItem a"
| "getAllMetaVarsInSubsFactor (KListSubs a) = getAllMetaVarsInSUKList a"
| "getAllMetaVarsInSubsFactor (KSubs a) = getAllMetaVarsInSUK a"
| "getAllMetaVarsInSubsFactor (ListSubs a) = getAllMetaVarsInSUList a"
| "getAllMetaVarsInSubsFactor (SetSubs a) = getAllMetaVarsInSUSet a"
| "getAllMetaVarsInSubsFactor (MapSubs a) = getAllMetaVarsInSUMap a"
| "getAllMetaVarsInSubsFactor (BagSubs a) = getAllMetaVarsInSUBag a"


fun getAllSubsortOnItem :: "('upVar * 'upVar) list \<Rightarrow> 'upVar \<Rightarrow> 'upVar list" where
"getAllSubsortOnItem [] a = []"
| "getAllSubsortOnItem ((x,y)#l) a = (if x = a
                       then y#(getAllSubsortOnItem l a) else getAllSubsortOnItem l a)"

definition myZip :: "'a list \<Rightarrow> 'b list \<Rightarrow> ('a * 'b) list option" where
"myZip a b = (if List.length a = List.length b then Some (zip a b) else None)"

fun keys :: "('a * 'b) list \<Rightarrow> 'a list" where
"keys [] = []"
| "keys ((a,b)#l) = a#(keys l)"

fun theValues :: "('a * 'b) list \<Rightarrow> 'b list" where
"theValues [] = []"
| "theValues ((a,b)#l) = b#(theValues l)"

(* get a value by a key from a map *)
fun getValueTerm :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option" where
"getValueTerm a [] = None"
| "getValueTerm a ((a',b)#l) = (if a = a' then Some b else getValueTerm a l)"

end