theory kCompile
imports Main Real List kSort
begin

(* this file defines the k core to k IR translation *)

(* configuration checks *)
fun uniqueCellNameInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
       \<Rightarrow> 'var var list \<Rightarrow> 'var var list option"
    and uniqueCellNameInSUBag :: "('upVar, 'var, 'metaVar) suB list 
       \<Rightarrow> 'var var list \<Rightarrow> 'var var list option" where
"uniqueCellNameInSUBag [] A = Some A"
| "uniqueCellNameInSUBag (b#l) A = (case b of ItemB x y z \<Rightarrow>
            if x \<in> set A then None else
          (case uniqueCellNameInSUBigKWithBag z (x#A) of None \<Rightarrow> None
              | Some A' \<Rightarrow> uniqueCellNameInSUBag l A')
        | IdB x \<Rightarrow> uniqueCellNameInSUBag l A)"
| "uniqueCellNameInSUBigKWithBag (SUK a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUList a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUSet a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUMap a) A = Some A"
| "uniqueCellNameInSUBigKWithBag (SUBag a) A = uniqueCellNameInSUBag a A"

fun hasNoBagVarInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
and hasNoBagVarInSUBigKWithBag :: "('upVar, 'var, 'metaVar)
                              suBigKWithBag \<Rightarrow> bool" where
"hasNoBagVarInSUBag [] = True"
| "hasNoBagVarInSUBag (b#l) = (case b of IdB x \<Rightarrow> False
            | _ \<Rightarrow> hasNoBagVarInSUBag l)"
| "hasNoBagVarInSUBigKWithBag (SUBag a) = hasNoBagVarInSUBag a"
| "hasNoBagVarInSUBigKWithBag a = True"

fun noDotInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
and noDotInSUBigKWithBag :: "('upVar, 'var, 'metaVar)
                              suBigKWithBag \<Rightarrow> bool" where
"noDotInSUBag [] = True"
| "noDotInSUBag (b#l) = (case b of IdB x \<Rightarrow> noDotInSUBag l
         | ItemB x y z \<Rightarrow> if DotDotDot \<in> set y then False
               else (noDotInSUBigKWithBag z \<and> noDotInSUBag l))"
| "noDotInSUBigKWithBag (SUBag a) = noDotInSUBag a"
| "noDotInSUBigKWithBag a = True"

(* if a context rule has rewrites, then the rewrite must be on rewriting a hole to other items*)
primrec validContextInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> bool"
    and validContextInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> bool"
    and validContextInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> bool"
    and validContextInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> bool"
    and validContextInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> bool"
    and validContextInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> bool"
    and validContextInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> bool"
    and validContextInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> bool"
    and validContextInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> bool"
    and validContextInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> bool"
    and validContextInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> bool"
    and validContextInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> bool"
    and validContextInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> bool"
    and validContextInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> bool"
    and validContextInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> bool"
    and validContextInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> bool"
    and validContextInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> bool"
    and validContextInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> bool"
 where
  "validContextInKLabel (KLabelC a) = True"
| "validContextInKLabel (KLabelFun a b) = (validContextInKLabel a \<and> validContextInKListR b)"
| "validContextInKLabel (IdKLabel n) = True"
| "validContextInKLabelR (KTerm n) = validContextInKLabel n"
| "validContextInKLabelR (KRewrite l r) = False"
| "validContextInKItem (KItemC l r ty) = (validContextInKLabelR l \<and> validContextInKListR r)"
| "validContextInKItem (Constant a b) = True"
| "validContextInKItem (IdKItem a b) = True"
| "validContextInKItem (HOLE a) = True"
| "validContextInKItemR (KTerm t) = validContextInKItem t"
| "validContextInKItemR (KRewrite l r) = (case l of HOLE a \<Rightarrow> True
                                                      | _ \<Rightarrow> False)"
| "validContextInKList (KListCon b t) = ((validContextInKListR b) \<and> (validContextInKListR t))"
| "validContextInKList UnitKList = True"
| "validContextInKList (KListItem a) = (validContextInBigKWithBag a)"
| "validContextInKList (IdKList a) = True"
| "validContextInKListR (KTerm t) = validContextInKList t"
| "validContextInKListR (KRewrite l r) = False"
| "validContextInBigKWithBag (TheBigK a) = validContextInBigK a"
| "validContextInBigKWithBag (TheBigBag b) = validContextInBagR b"
| "validContextInBigKWithBag (TheLabel b) = validContextInKLabelR b"
| "validContextInBigK (TheK t) = validContextInKR t"
| "validContextInBigK (TheList t) = validContextInListR t"
| "validContextInBigK (TheSet t) = validContextInSetR t"
| "validContextInBigK (TheMap t) = validContextInMapR t"
| "validContextInK (Tilda a t) = ((validContextInKR a) \<and> (validContextInKR t))"
| "validContextInK UnitK = True"
| "validContextInK (SingleK a) = validContextInKItemR a"
| "validContextInK (IdK a) = True"
| "validContextInK (KFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInKR (KTerm a) = (validContextInK a)"
| "validContextInKR (KRewrite l r) = False"
| "validContextInList (ListCon l r) = ((validContextInListR l) \<and> (validContextInListR r))"
| "validContextInList UnitList = True"
| "validContextInList (IdList a) = True"
| "validContextInList (ListItem a) = validContextInKR a"
| "validContextInList (ListFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInListR (KTerm a) = (validContextInList a)"
| "validContextInListR (KRewrite l r) = False"
| "validContextInSet (SetCon l r) = ((validContextInSetR l) \<and> (validContextInSetR r))"
| "validContextInSet UnitSet = True"
| "validContextInSet (IdSet a) = True"
| "validContextInSet (SetItem a) = validContextInKR a"
| "validContextInSet (SetFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInSetR (KTerm a) = (validContextInSet a)"
| "validContextInSetR (KRewrite l r) = False"
| "validContextInMap (MapCon l r) = ((validContextInMapR l) \<and> (validContextInMapR r))"
| "validContextInMap UnitMap = True"
| "validContextInMap (IdMap a) = True"
| "validContextInMap (MapItem l r) = (validContextInKR l \<and> validContextInKR r)"
| "validContextInMap (MapFun l r) = (validContextInKLabel l \<and> validContextInKListR r)"
| "validContextInMapR (KTerm a) = (validContextInMap a)"
| "validContextInMapR (KRewrite l r) = False"
| "validContextInBag (BagCon l r) =((validContextInBagR l) \<and> (validContextInBagR r))"
| "validContextInBag UnitBag = True"
| "validContextInBag (IdBag a) = True"
| "validContextInBag (Xml a n t) =  validContextInBagR t"
| "validContextInBag (SingleCell a n t) =  validContextInBigK t"
| "validContextInBagR (KTerm a) = (validContextInBag a)"
| "validContextInBagR (KRewrite l r) = False"

fun mapLookup ::
     "'a \<Rightarrow> ('a * 'b) list
            \<Rightarrow> 'b option" where
"mapLookup x [] = None"
| "mapLookup x ((a,b)#l) = (if x = a then Some b else mapLookup x l)"

primrec isElement :: "'c \<Rightarrow> ('a * 'b * 'c KItemSyntax) list \<Rightarrow> bool" where
"isElement a [] = False"
| "isElement a (h#l) = (case h of (x,y, SingleTon z) \<Rightarrow> if a = z then True else
                        isElement a l | (x,y, SetTon s) \<Rightarrow> if s a then True else
                        isElement a l)"


fun hasHoleInIRKItem :: "('upVar, 'var, 'metaVar) irKItem \<Rightarrow> bool"
    and hasHoleInIRKList :: "('upVar, 'var, 'metaVar) irKList \<Rightarrow> bool"
    and hasHoleInIRK :: "('upVar, 'var, 'metaVar) irK \<Rightarrow> bool"
    and hasHoleInIRList :: "('upVar, 'var, 'metaVar) irList \<Rightarrow> bool"
    and hasHoleInIRSet :: "('upVar, 'var, 'metaVar) irSet \<Rightarrow> bool"
    and hasHoleInIRMap :: "('upVar, 'var, 'metaVar) irMap \<Rightarrow> bool"
    and hasHoleInIRBigKWithBag :: "('upVar, 'var, 'metaVar) irBigKWithBag \<Rightarrow> bool"
    and hasHoleInIRBigKWithLabel ::
             "('upVar, 'var, 'metaVar) irBigKWithLabel \<Rightarrow> bool"
    and hasHoleInIRBag :: "('upVar, 'var, 'metaVar) irBag \<Rightarrow> bool"
 where 
 "hasHoleInIRKItem (IRKItem l r ty) = (hasHoleInIRKList r)"
| "hasHoleInIRKItem (IRIdKItem a b) = False"
| "hasHoleInIRKItem (IRHOLE a) = True"
| "hasHoleInIRKList (KListPatNoVar l) =
                    foldl (\<lambda> b t . b \<or> hasHoleInIRBigKWithLabel t) False (l)"
| "hasHoleInIRKList (KListPat l a r) =
                    foldl (\<lambda> b t . b \<or> hasHoleInIRBigKWithLabel t) False (l@r)"
| "hasHoleInIRBigKWithBag (IRK a) = hasHoleInIRK a"
| "hasHoleInIRBigKWithBag (IRList a) = hasHoleInIRList a"
| "hasHoleInIRBigKWithBag (IRSet a) = hasHoleInIRSet a"
| "hasHoleInIRBigKWithBag (IRMap a) = hasHoleInIRMap a"
| "hasHoleInIRBigKWithBag (IRBag a) = hasHoleInIRBag a"
| "hasHoleInIRBigKWithLabel (IRBigBag a) = hasHoleInIRBigKWithBag a"
| "hasHoleInIRBigKWithLabel (IRBigLabel a) = False"
| "hasHoleInIRK (KPat l a) = foldl (\<lambda> b t . b \<or> hasHoleInIRKItem t) False l"
| "hasHoleInIRList (ListPatNoVar l) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False (l)"
| "hasHoleInIRList (ListPat l a r) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False (l@r)"
| "hasHoleInIRSet (SetPat l a) = foldl (\<lambda> b t . b \<or> hasHoleInIRK t) False l"
| "hasHoleInIRMap (MapPat l a) = foldl (\<lambda> b t . case t of (x,y) \<Rightarrow>
                           b \<or> hasHoleInIRK x \<or> hasHoleInIRK y) False l"
| "hasHoleInIRBag (BagPat l a) = foldl (\<lambda> b t . case t of (x,y,z) \<Rightarrow>
                           b \<or> hasHoleInIRBigKWithBag z) False l"

primrec hasHoleInMatchFactor :: "('upVar, 'var, 'metaVar) matchFactor \<Rightarrow> bool"
where
"hasHoleInMatchFactor (KLabelMatching a) = False"
| "hasHoleInMatchFactor (KItemMatching a) = hasHoleInIRKItem a"
| "hasHoleInMatchFactor (KListMatching a) = hasHoleInIRKList a"
| "hasHoleInMatchFactor (KMatching a) = hasHoleInIRK a"
| "hasHoleInMatchFactor (ListMatching a) = hasHoleInIRList a"
| "hasHoleInMatchFactor (SetMatching a) = hasHoleInIRSet a"
| "hasHoleInMatchFactor (MapMatching a) = hasHoleInIRMap a"
| "hasHoleInMatchFactor (BagMatching a) = hasHoleInIRBag a"

primrec hasHoleInPat :: "('upVar, 'var, 'metaVar) pat \<Rightarrow> bool" where
"hasHoleInPat (KLabelFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (KFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (KItemFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (ListFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (SetFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (MapFunPat a b) = hasHoleInIRKList b"
| "hasHoleInPat (NormalPat b) = hasHoleInMatchFactor b"


fun hasHoleInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel \<Rightarrow> bool"
    and hasHoleInSUKItem :: "('upVar, 'var, 'metaVar) suKItem \<Rightarrow> bool"
    and hasHoleInSUKList :: "('upVar, 'var, 'metaVar) suKl list \<Rightarrow> bool"
    and hasHoleInSUK :: "('upVar, 'var, 'metaVar) suKFactor list \<Rightarrow> bool"
    and hasHoleInSUList :: "('upVar, 'var, 'metaVar) suL list \<Rightarrow> bool"
    and hasHoleInSUSet :: "('upVar, 'var, 'metaVar) suS list \<Rightarrow> bool"
    and hasHoleInSUMap :: "('upVar, 'var, 'metaVar) suM list \<Rightarrow> bool"
    and hasHoleInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag \<Rightarrow> bool"
    and hasHoleInSUBigKWithLabel ::
                     "('upVar, 'var, 'metaVar) suBigKWithLabel \<Rightarrow> bool"
    and hasHoleInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool"
 where 
  "hasHoleInSUKLabel (SUKLabel a) = False"
| "hasHoleInSUKLabel (SUKLabelFun a b) = hasHoleInSUKList b"
| "hasHoleInSUKLabel (SUIdKLabel n) = False"
| "hasHoleInSUKItem (SUKItem l r ty) = ((hasHoleInSUKLabel l) \<or> (hasHoleInSUKList r))"
| "hasHoleInSUKItem (SUIdKItem a b) = False"
| "hasHoleInSUKItem (SUHOLE a) = True"
| "hasHoleInSUKList [] = False"
| "hasHoleInSUKList ((ItemKl t)#l) = (hasHoleInSUBigKWithLabel t \<or> hasHoleInSUKList l)"
| "hasHoleInSUKList ((IdKl t)#l) = hasHoleInSUKList l"
| "hasHoleInSUBigKWithBag (SUK a) = hasHoleInSUK a"
| "hasHoleInSUBigKWithBag (SUList a) = hasHoleInSUList a"
| "hasHoleInSUBigKWithBag (SUSet a) = hasHoleInSUSet a"
| "hasHoleInSUBigKWithBag (SUMap a) = hasHoleInSUMap a"
| "hasHoleInSUBigKWithBag (SUBag a) = hasHoleInSUBag a"
| "hasHoleInSUBigKWithLabel (SUBigBag a) = hasHoleInSUBigKWithBag a"
| "hasHoleInSUBigKWithLabel (SUBigLabel a) = hasHoleInSUKLabel a"
| "hasHoleInSUK [] = False"
| "hasHoleInSUK ((IdFactor t)#l) = hasHoleInSUK l"
| "hasHoleInSUK ((ItemFactor t)#l) = (hasHoleInSUKItem t \<or> hasHoleInSUK l)"
| "hasHoleInSUK ((SUKKItem a b ty)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUK l)"
| "hasHoleInSUList [] = False"
| "hasHoleInSUList ((IdL t)#l) = hasHoleInSUList l"
| "hasHoleInSUList ((ItemL t)#l) = (hasHoleInSUK t \<or> hasHoleInSUList l)"
| "hasHoleInSUList ((SUListKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUList l)"
| "hasHoleInSUSet [] = False"
| "hasHoleInSUSet ((IdS t)#l) = hasHoleInSUSet l"
| "hasHoleInSUSet ((ItemS t)#l) = (hasHoleInSUK t \<or> hasHoleInSUSet l)"
| "hasHoleInSUSet ((SUSetKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUSet l)"
| "hasHoleInSUMap [] = False"
| "hasHoleInSUMap ((IdM t)#l) = hasHoleInSUMap l"
| "hasHoleInSUMap ((ItemM a b)#l) = ((hasHoleInSUK a)
                                   \<or> (hasHoleInSUK b) \<or> hasHoleInSUMap l)"
| "hasHoleInSUMap ((SUMapKItem a b)#l) = ((hasHoleInSUKLabel a)
                                   \<or> (hasHoleInSUKList b) \<or> hasHoleInSUMap l)"
| "hasHoleInSUBag [] = False"
| "hasHoleInSUBag ((IdB t)#l) = hasHoleInSUBag l"
| "hasHoleInSUBag ((ItemB x y z)#l) = (hasHoleInSUBigKWithBag z \<or> hasHoleInSUBag l)"

(* constant to klabels *)
definition isConstInKItem where
"isConstInKItem a = (case a of (IRKItem (IRKLabel s) kl ty) \<Rightarrow> isConst s
                      | _ \<Rightarrow> False)"

definition labelToConstInKItem where
"labelToConstInKItem a = (case a of (IRKItem (IRKLabel s) kl ty) \<Rightarrow> 
                         (labelToConst s) | _ \<Rightarrow> None)"
(*
definition functionKItems :: "('upVar * ('upVar, 'var, 'metaVar metaVar) kItem KItemSyntax) list" where
"functionKItems = syntaxSetToKItemSet (getAllFunctionsInSyntax (getAllSyntaxInKFile Theory))"
*)

(* get the core label by given a term *)
definition getSUKLabelMeaning  where
"getSUKLabelMeaning x = (case x of (SUKLabel a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInSUKItem where
"getKLabelInSUKItem A = (case A of (SUKItem a b ty) \<Rightarrow> getSUKLabelMeaning a
                     | _ \<Rightarrow> None)"

definition getKLabelInSUK where
"getKLabelInSUK x = (case x of (SUKKItem a b ty) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUKS where
"getKLabelInSUKS x = (case x of [x'] \<Rightarrow> getKLabelInSUK x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUList where
"getKLabelInSUList x = (case x of (SUListKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUListS where
"getKLabelInSUListS x = (case x of [x'] \<Rightarrow> getKLabelInSUList x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUSet where
"getKLabelInSUSet x = (case x of (SUSetKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUSetS where
"getKLabelInSUSetS x = (case x of [x'] \<Rightarrow> getKLabelInSUSet x'
                          | _ \<Rightarrow> None)"

definition getKLabelInSUMap where
"getKLabelInSUMap x = (case x of (SUMapKItem a b) \<Rightarrow> getSUKLabelMeaning a
                          | _ \<Rightarrow> None)"

definition getKLabelInSUMapS where
"getKLabelInSUMapS x = (case x of [x'] \<Rightarrow> getKLabelInSUMap x'
                          | _ \<Rightarrow> None)"

definition getIRKLabel where
"getIRKLabel x = (case x of (IRKLabel a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelMeaning where
"getKLabelMeaning x = (case x of (KLabelC a) \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInKLabelR where
"getKLabelInKLabelR x = (case x of (KTerm (KLabelC a))
                              \<Rightarrow> Some a | _ \<Rightarrow> None)"

definition getKLabelInIRKItem where
"getKLabelInIRKItem A = (case A of (IRKItem a b ty) \<Rightarrow> getIRKLabel a
                     | _ \<Rightarrow> None)"

(* giving a function term and check a term has a function label *)
definition FunctionTerms where
"FunctionTerms database =
 foldl (\<lambda> acc (a,b,c,nl,d) . if d then acc@[(a,b,c,nl,d)] else acc) [] (database)"

fun isFunctionItemAux where
"isFunctionItemAux [] s = False"
| "isFunctionItemAux ((a,b, SingleTon t, nl, True)#l) s =
     (if (t = s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, SetTon t, nl, True)#l) s =
     (if (t s) then True else isFunctionItemAux l s)"
| "isFunctionItemAux ((a,b, t, nl, False)#l) s = isFunctionItemAux l s"

definition isFunctionItem where
"isFunctionItem s database = isFunctionItemAux database s"

(* translate pattern in K core to K IR *)
primrec toIRInKLabel
    and toIRInKLabelR
    and toIRInKItem
    and toIRInKItemR
    and toIRInKList
    and toIRInKListR
    and toIRInK
    and toIRInKR
    and toIRInList
    and toIRInListR
    and toIRInSet
    and toIRInSetR
    and toIRInMap
    and toIRInMapR
    and toIRInBigKWithBag
    and toIRInBigK
    and toIRInBag
    and toIRInBagR
 where 
  "toIRInKLabel (KLabelC a) database = Some (NormalPat (KLabelMatching (IRKLabel a)))"
| "toIRInKLabel (KLabelFun a b) database =
    (case getKLabelMeaning a of None \<Rightarrow> None
       | Some s \<Rightarrow> (case toIRInKListR b database of None \<Rightarrow> None
           | Some b' \<Rightarrow>  Some (KLabelFunPat s b')))"
| "toIRInKLabel (IdKLabel n) database = Some (NormalPat (KLabelMatching (IRIdKLabel n)))"
| "toIRInKLabelR (KTerm n) database = toIRInKLabel n database"
| "toIRInKLabelR (KRewrite l r) database = None"
| "toIRInKItem (KItemC l r ty) database =
 (case getKLabelInKLabelR l of None \<Rightarrow>
     (case (toIRInKLabelR l database) of Some (NormalPat (KLabelMatching l'))
      \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
        | Some r' \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' [ty])))) 
        | _ \<Rightarrow> None)
    | Some s \<Rightarrow> (if isFunctionItem s database then
         (case toIRInKListR r database of None \<Rightarrow> None
            | Some r' \<Rightarrow> Some (KItemFunPat s r'))
        else (case (toIRInKLabelR l database) of Some (NormalPat (KLabelMatching l'))
      \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
        | Some r' \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' [ty])))) 
        | _ \<Rightarrow> None)))"
| "toIRInKItem (Constant a b) database = Some (NormalPat (KItemMatching
                          (IRKItem (IRKLabel (ConstToLabel a)) (KListPatNoVar []) [b])))"
| "toIRInKItem (IdKItem a b) database = Some (NormalPat (KItemMatching (IRIdKItem a [b])))"
| "toIRInKItem (HOLE a) database = Some (NormalPat (KItemMatching (IRHOLE [a])))"
| "toIRInKItemR (KTerm t) database =  toIRInKItem t database"
| "toIRInKItemR (KRewrite l r) database= None"
| "toIRInKList (KListCon b t) database =
 (case (toIRInKListR b database, toIRInKListR t database)
     of (Some (KListPatNoVar la), Some (KListPatNoVar lb))
    \<Rightarrow> Some (KListPatNoVar (la@lb))
   | (Some (KListPat la x ra), Some (KListPatNoVar lb))
    \<Rightarrow> Some (KListPat la x (ra@lb))
   | (Some (KListPatNoVar la), Some (KListPat lb y rb))
         \<Rightarrow> Some (KListPat (la@lb) y rb)
   | _ \<Rightarrow> None)"
| "toIRInKList UnitKList database = Some (KListPatNoVar [])"
| "toIRInKList (KListItem a) database = (case toIRInBigKWithBag a database of None \<Rightarrow> None
             | Some a' \<Rightarrow> Some (KListPatNoVar [a']))"
| "toIRInKList (IdKList a) database = Some (KListPat [] a [])"
| "toIRInKListR (KTerm t) database = toIRInKList t database"
| "toIRInKListR (KRewrite l r) database = None"
| "toIRInBigKWithBag (TheBigK a) database = (case (toIRInBigK a database) of None \<Rightarrow> None
                                   | Some a' \<Rightarrow> Some (IRBigBag a'))"
| "toIRInBigKWithBag (TheBigBag b) database = (case toIRInBagR b database of Some b'
              \<Rightarrow> Some (IRBigBag (IRBag b'))
                   | None \<Rightarrow> None)"
| "toIRInBigKWithBag (TheLabel b) database =
      (case toIRInKLabelR b database of Some (NormalPat (KLabelMatching b'))
              \<Rightarrow> Some (IRBigLabel b')
                   | _ \<Rightarrow> None)"
| "toIRInBigK (TheK t) database = (case toIRInKR t database of Some (NormalPat (KMatching t'))
                            \<Rightarrow> Some (IRK t')
                    | _ \<Rightarrow> None)"
| "toIRInBigK (TheList t) database = (case toIRInListR t database of Some (NormalPat (ListMatching t'))
                            \<Rightarrow> Some (IRList t')
                    | _ \<Rightarrow> None)"
| "toIRInBigK (TheSet t) database = (case toIRInSetR t database of Some (NormalPat (SetMatching t'))
                            \<Rightarrow> Some (IRSet t')
                    | _ \<Rightarrow> None)"
| "toIRInBigK (TheMap t) database = (case toIRInMapR t database of Some (NormalPat (MapMatching t'))
                            \<Rightarrow> Some (IRMap t')
                    | _ \<Rightarrow> None)"
| "toIRInK (Tilda a b) database =
 (case (toIRInKR a database, toIRInKR b database) of
       (Some (NormalPat (KMatching (KPat la (Some va)))),
                     Some (NormalPat (KMatching (KPat lb None))))
    \<Rightarrow> (if lb \<noteq> [] then
                Some (NormalPat (KMatching (KPat (la@[IRIdKItem va [K]]@lb) None)))
             else Some (NormalPat (KMatching (KPat (la@lb) (Some (va))))))
   | (Some (NormalPat (KMatching (KPat la (Some va)))),
                 Some (NormalPat (KMatching (KPat lb (Some vb)))))
    \<Rightarrow> Some (NormalPat (KMatching (KPat (la@[IRIdKItem va [K]]@lb) (Some vb))))
   | (Some (NormalPat (KMatching (KPat la None))),
                Some (NormalPat (KMatching (KPat lb (Some vb)))))
              \<Rightarrow> Some (NormalPat (KMatching (KPat (la@lb) (Some vb))))
   | (Some (NormalPat (KMatching (KPat la None))),
                    Some (NormalPat (KMatching (KPat lb None))))
              \<Rightarrow> Some (NormalPat (KMatching (KPat (la@lb) None)))
   | _ \<Rightarrow> None)"
| "toIRInK UnitK database = Some (NormalPat (KMatching (KPat [] None)))"
| "toIRInK (SingleK a) database = (case toIRInKItemR a database of Some (NormalPat (KItemMatching a'))
           \<Rightarrow> Some (NormalPat (KMatching (KPat [a'] None)))
               | _ \<Rightarrow> None)"
| "toIRInK (IdK a) database = Some (NormalPat (KMatching (KPat [] (Some (a)))))"
| "toIRInK (KFun l r) database = (case getKLabelMeaning l of None \<Rightarrow> None
       | Some s \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some (KFunPat s r')))"
| "toIRInKR (KTerm a) database = (toIRInK a database)"
| "toIRInKR (KRewrite l r) database = None"
| "toIRInList (ListCon a b) database =
 (case (toIRInListR a database, toIRInListR b database) of
   (Some (NormalPat (ListMatching (ListPatNoVar la))),
              Some (NormalPat (ListMatching (ListPatNoVar lb))))
    \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar (la@lb))))
   | (Some (NormalPat (ListMatching (ListPat la x ra))),
                    Some (NormalPat (ListMatching (ListPatNoVar lb))))
    \<Rightarrow> Some (NormalPat (ListMatching (ListPat la x (ra@lb))))
   | (Some (NormalPat (ListMatching (ListPatNoVar la))),
                Some (NormalPat (ListMatching (ListPat lb x rb))))
    \<Rightarrow> Some (NormalPat (ListMatching (ListPat (la@lb) x rb)))
   | _ \<Rightarrow> None)"
| "toIRInList UnitList database = Some (NormalPat (ListMatching (ListPatNoVar [])))"
| "toIRInList (IdList a) database = Some (NormalPat (ListMatching (ListPat [] a [])))"
| "toIRInList (ListItem a) database = (case toIRInKR a database of Some (NormalPat (KMatching a'))
           \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar [a'])))
               | _ \<Rightarrow> None)"
| "toIRInList (ListFun l r) database = (case getKLabelMeaning l of None \<Rightarrow> None
       | Some s \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some (ListFunPat s r')))"
| "toIRInListR (KTerm a) database = (toIRInList a database)"
| "toIRInListR (KRewrite l r) database = None"
| "toIRInSet (SetCon a b) database =
 (case (toIRInSetR a database, toIRInSetR b database) of
    (Some (NormalPat (SetMatching (SetPat la (Some va)))),
                  Some (NormalPat (SetMatching (SetPat lb None))))
    \<Rightarrow> Some (NormalPat (SetMatching (SetPat (la@lb) (Some va))))
   | (Some (NormalPat (SetMatching (SetPat la None))),
           Some (NormalPat (SetMatching (SetPat lb (Some vb)))))
              \<Rightarrow> Some (NormalPat (SetMatching (SetPat (la@lb) (Some vb))))
   | _ \<Rightarrow> None)"
| "toIRInSet UnitSet database = Some (NormalPat (SetMatching (SetPat [] None)))"
| "toIRInSet (IdSet a) database = Some (NormalPat (SetMatching (SetPat [] (Some a))))"
| "toIRInSet (SetItem a) database = (case toIRInKR a database of Some (NormalPat (KMatching a'))
            \<Rightarrow> Some (NormalPat (SetMatching (SetPat [a'] None)))
               | _ \<Rightarrow> None)"
| "toIRInSet (SetFun l r) database = (case getKLabelMeaning l of None \<Rightarrow> None
       | Some s \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some (SetFunPat s r')))"
| "toIRInSetR (KTerm a) database = (toIRInSet a database)"
| "toIRInSetR (KRewrite l r) database = None"
| "toIRInMap (MapCon a b) database =
 (case (toIRInMapR a database, toIRInMapR b database) of
    (Some (NormalPat (MapMatching (MapPat la (Some va)))),
                Some (NormalPat (MapMatching (MapPat lb None))))
    \<Rightarrow> Some (NormalPat (MapMatching (MapPat (la@lb) (Some va))))
   | (Some (NormalPat (MapMatching (MapPat la None))),
                Some (NormalPat (MapMatching (MapPat lb (Some vb)))))
              \<Rightarrow> Some (NormalPat (MapMatching (MapPat (la@lb) (Some vb))))
   | _ \<Rightarrow> None)"
| "toIRInMap UnitMap database = Some (NormalPat (MapMatching (MapPat [] None)))"
| "toIRInMap (IdMap a) database = Some (NormalPat (MapMatching (MapPat [] (Some a))))"
| "toIRInMap (MapItem l r) database =
    (case (toIRInKR l database, toIRInKR r database) of
    (Some (NormalPat (KMatching l')), Some (NormalPat (KMatching r')))
             \<Rightarrow> Some (NormalPat (MapMatching (MapPat [(l',r')] None)))
           | _ \<Rightarrow> None) "
| "toIRInMap (MapFun l r) database = (case getKLabelMeaning l of None \<Rightarrow> None
       | Some s \<Rightarrow> (case toIRInKListR r database of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some (MapFunPat s r')))"
| "toIRInMapR (KTerm a) database = (toIRInMap a database)"
| "toIRInMapR (KRewrite l r) database = None"
| "toIRInBag (BagCon a b) database =
 (case (toIRInBagR a database, toIRInBagR b database) of
    (Some (BagPat la (Some va)), Some (BagPat lb None))
    \<Rightarrow> Some (BagPat (la@lb) (Some va))
   | (Some (BagPat la None), Some (BagPat lb (Some vb)))
              \<Rightarrow> Some (BagPat (la@lb) (Some vb))
   | _ \<Rightarrow> None)"
| "toIRInBag UnitBag database = Some (BagPat [] None)"
| "toIRInBag (IdBag a) database = Some (BagPat [] (Some a))"
| "toIRInBag (Xml a n t) database =  (case toIRInBagR t database of None \<Rightarrow> None
          | Some t' \<Rightarrow> Some (BagPat [ (a,n,IRBag t')] None))"
| "toIRInBag (SingleCell a n t) database =  (case toIRInBigK t database of None \<Rightarrow> None
          | Some t' \<Rightarrow> Some (BagPat [(a,n,t')] None))"
| "toIRInBagR (KTerm a) database = (toIRInBag a database)"
| "toIRInBagR (KRewrite l r) database = None"

primrec toSUInKLabel
    and toSUInKLabelR
    and toSUInKItem 
    and toSUInKItemR
    and toSUInKList
    and toSUInKListR
    and toSUInK
    and toSUInKR
    and toSUInList
    and toSUInListR
    and toSUInSet
    and toSUInSetR
    and toSUInMap
    and toSUInMapR
    and toSUInBigKWithBag
    and toSUInBigK
    and toSUInBag
    and toSUInBagR where 
  "toSUInKLabel (KLabelC a) = Some (SUKLabel a)"
| "toSUInKLabel (KLabelFun a b) = (case toSUInKLabel a of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case toSUInKListR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "toSUInKLabel (IdKLabel n) = Some (SUIdKLabel n)"
| "toSUInKLabelR (KTerm n) = toSUInKLabel n"
| "toSUInKLabelR (KRewrite l r) = None"
| "toSUInKItem (KItemC l r ty) =
 (case (toSUInKLabelR l) of None \<Rightarrow> None 
     | Some l' \<Rightarrow> (case toSUInKListR r of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some (SUKItem l' r' [ty])))"
| "toSUInKItem (Constant a b) = Some (SUKItem (SUKLabel (ConstToLabel a)) [] [b])"
| "toSUInKItem (IdKItem a b) = Some (SUIdKItem a [b])"
| "toSUInKItem (HOLE a) = Some (SUHOLE [a])"
| "toSUInKItemR (KTerm t) =  toSUInKItem t"
| "toSUInKItemR (KRewrite l r) = None"
| "toSUInKList (KListCon b t) = (case (toSUInKListR b, toSUInKListR t)
     of (Some l, Some l') \<Rightarrow> Some (l@l')
   | _ \<Rightarrow> None)"
| "toSUInKList UnitKList = Some []"
| "toSUInKList (KListItem a) = (case toSUInBigKWithBag a of None \<Rightarrow> None
             | Some a' \<Rightarrow> Some [ItemKl a'])"
| "toSUInKList (IdKList a) = Some [IdKl a]"
| "toSUInKListR (KTerm t) = toSUInKList t"
| "toSUInKListR (KRewrite l r) = None"
| "toSUInBigKWithBag (TheBigK a) = (case toSUInBigK a of None \<Rightarrow> None
               | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "toSUInBigKWithBag (TheBigBag b) = (case toSUInBagR b of Some b'
              \<Rightarrow> Some (SUBigBag (SUBag b'))
                   | None \<Rightarrow> None)"
| "toSUInBigKWithBag (TheLabel b) = (case toSUInKLabelR b of Some b'
              \<Rightarrow> Some (SUBigLabel b')
                   | None \<Rightarrow> None)"
| "toSUInBigK (TheK t) = (case toSUInKR t of None \<Rightarrow> None
                    | Some t' \<Rightarrow> Some (SUK t'))"
| "toSUInBigK (TheList t) = (case toSUInListR t of None \<Rightarrow> None
                    | Some t' \<Rightarrow> Some (SUList t'))"
| "toSUInBigK (TheSet t) = (case toSUInSetR t of None \<Rightarrow> None
                    | Some t' \<Rightarrow> Some (SUSet t'))"
| "toSUInBigK (TheMap t) = (case toSUInMapR t of None \<Rightarrow> None
                    | Some t' \<Rightarrow> Some (SUMap t'))"
| "toSUInK (Tilda a b) = (case (toSUInKR a, toSUInKR b) of (Some l, Some l')
    \<Rightarrow> Some (l@l') | _ \<Rightarrow> None)"
| "toSUInK UnitK = Some []"
| "toSUInK (SingleK a) = (case toSUInKItemR a of None \<Rightarrow> None
               | Some a' \<Rightarrow> Some [ItemFactor a'])"
| "toSUInK (IdK a) = Some [IdFactor a]"
| "toSUInK (KFun l r) = (case (toSUInKLabel l) of None \<Rightarrow> None 
     | Some l' \<Rightarrow> (case toSUInKListR r of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some ([SUKKItem l' r' [K]])))"
| "toSUInKR (KTerm a) = (toSUInK a)"
| "toSUInKR (KRewrite l r) = None"
| "toSUInList (ListCon a b) = (case (toSUInListR a, toSUInListR b) of (Some l, Some l')
    \<Rightarrow> Some (l@l') | _ \<Rightarrow> None)"
| "toSUInList UnitList = Some []"
| "toSUInList (IdList a) = Some [IdL a]"
| "toSUInList (ListItem a) = (case toSUInKR a of None \<Rightarrow> None
               | Some a' \<Rightarrow> Some [ItemL a'])"
| "toSUInList (ListFun l r) = (case (toSUInKLabel l) of None \<Rightarrow> None 
     | Some l' \<Rightarrow> (case toSUInKListR r of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some ([SUListKItem l' r'])))"
| "toSUInListR (KTerm a) = (toSUInList a)"
| "toSUInListR (KRewrite l r) = None"
| "toSUInSet (SetCon a b) = (case (toSUInSetR a, toSUInSetR b) of (Some l, Some l')
    \<Rightarrow> Some (l@l') | _ \<Rightarrow> None)"
| "toSUInSet UnitSet = Some []"
| "toSUInSet (IdSet a) = Some [IdS a]"
| "toSUInSet (SetItem a) = (case toSUInKR a of None \<Rightarrow> None 
               | Some a' \<Rightarrow> Some [ItemS a'])"
| "toSUInSet (SetFun l r) = (case (toSUInKLabel l) of None \<Rightarrow> None 
     | Some l' \<Rightarrow> (case toSUInKListR r of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some ([SUSetKItem l' r'])))"
| "toSUInSetR (KTerm a) = (toSUInSet a)"
| "toSUInSetR (KRewrite l r) = None"
| "toSUInMap (MapCon a b) = (case (toSUInMapR a, toSUInMapR b)
     of (Some l, Some l') \<Rightarrow> Some (l@l')
       | _ \<Rightarrow> None)"
| "toSUInMap UnitMap = Some []"
| "toSUInMap (IdMap a) = Some [IdM a]"
| "toSUInMap (MapItem l r) =
    (case (toSUInKR l, toSUInKR r) of (Some l', Some r') \<Rightarrow> Some [ItemM l' r']
           | _ \<Rightarrow> None)"
| "toSUInMap (MapFun l r) = (case (toSUInKLabel l) of None \<Rightarrow> None 
     | Some l' \<Rightarrow> (case toSUInKListR r of None \<Rightarrow> None
     | Some r' \<Rightarrow> Some ([SUMapKItem l' r'])))"
| "toSUInMapR (KTerm a) = (toSUInMap a)"
| "toSUInMapR (KRewrite l r) = None"
| "toSUInBag (BagCon a b) =
 (case (toSUInBagR a, toSUInBagR b) of (Some l, Some l')
    \<Rightarrow> Some (l@l')
   | _ \<Rightarrow> None)"
| "toSUInBag UnitBag = Some []"
| "toSUInBag (IdBag a) = Some [IdB a]"
| "toSUInBag (Xml a n t) =  (case toSUInBagR t of None \<Rightarrow> None
          | Some t' \<Rightarrow> Some [ItemB a n (SUBag t')])"
| "toSUInBag (SingleCell a n t) =  (case toSUInBigK t of None \<Rightarrow> None
          | Some t' \<Rightarrow> Some [ItemB a n t'])"
| "toSUInBagR (KTerm a) = (toSUInBag a)"
| "toSUInBagR (KRewrite l r) = None"

primrec irToSUInKLabel where
  "irToSUInKLabel (IRKLabel a) = SUKLabel a"
| "irToSUInKLabel (IRIdKLabel n) = (SUIdKLabel n)"

fun irToSUInKItem
    and irToSUInKList
    and irToSUInK
    and irToSUInList
    and irToSUInSet
    and irToSUInMap
    and irToSUInBigKWithBag
    and irToSUInBigKWithLabel
    and irToSUInBag where 
 "irToSUInKItem (IRKItem l r ty) = (SUKItem (irToSUInKLabel l) (irToSUInKList r) ty)"
| "irToSUInKItem (IRIdKItem a b) = (SUIdKItem a b)"
| "irToSUInKItem (IRHOLE a) = (SUHOLE a)"
| "irToSUInKList (KListPatNoVar l) = 
   (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)"
| "irToSUInKList (KListPat l a r) = 
   (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)@[IdKl a]
          @((List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) r))"
| "irToSUInBigKWithLabel (IRBigBag a) = SUBigBag (irToSUInBigKWithBag a)"
| "irToSUInBigKWithLabel (IRBigLabel a) = SUBigLabel (irToSUInKLabel a)"
| "irToSUInBigKWithBag (IRK a) = SUK (irToSUInK a)"
| "irToSUInBigKWithBag (IRList a) = SUList (irToSUInList a)"
| "irToSUInBigKWithBag (IRSet a) = SUSet (irToSUInSet a)"
| "irToSUInBigKWithBag (IRMap a) = SUMap (irToSUInMap a)"
| "irToSUInBigKWithBag (IRBag a) = SUBag (irToSUInBag a)"
| "irToSUInK (KPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = [K] then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = [K] then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l)@[(IdFactor a')])"
| "irToSUInList (ListPatNoVar l) =
     (List.map (\<lambda> x . ItemL (irToSUInK x)) l)"
| "irToSUInList (ListPat l a r) =
     (List.map (\<lambda> x . ItemL (irToSUInK x)) l)@[IdL a]
          @((List.map (\<lambda> x . ItemL (irToSUInK x)) r))"
| "irToSUInSet (SetPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> x . ItemS (irToSUInK x)) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> x . ItemS (irToSUInK x)) l)@[(IdS a')])"
| "irToSUInMap (MapPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> (x,y) . ItemM (irToSUInK x) (irToSUInK y)) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> (x,y) . ItemM (irToSUInK x) (irToSUInK y)) l)@[(IdM a')])"
| "irToSUInBag (BagPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> (a,b,c) . ItemB a b (irToSUInBigKWithBag c)) l
   | Some a'  \<Rightarrow>
        (List.map (\<lambda> (a,b,c) . ItemB a b (irToSUInBigKWithBag c)) l)@[(IdB a')])"

primrec irToSUInMatchFactor where
"irToSUInMatchFactor (KLabelMatching a) = KLabelSubs (irToSUInKLabel a)"
| "irToSUInMatchFactor (KItemMatching a) = KItemSubs (irToSUInKItem a)"
| "irToSUInMatchFactor (KMatching a) = KSubs (irToSUInK a)"
| "irToSUInMatchFactor (KListMatching a) = KListSubs (irToSUInKList a)"
| "irToSUInMatchFactor (ListMatching a) = ListSubs (irToSUInList a)"
| "irToSUInMatchFactor (SetMatching a) = SetSubs (irToSUInSet a)"
| "irToSUInMatchFactor (MapMatching a) = MapSubs (irToSUInMap a)"
| "irToSUInMatchFactor (BagMatching a) = BagSubs (irToSUInBag a)"

primrec irToSUInPat where
"irToSUInPat (KLabelFunPat s l) database = KLabelSubs (SUKLabelFun (SUKLabel s) (irToSUInKList l))"
| "irToSUInPat (KItemFunPat s l) database = (case getSort s database of Some ty
              \<Rightarrow> KItemSubs (SUKItem (SUKLabel s) (irToSUInKList l) ty)
             | _ \<Rightarrow> KItemSubs (SUKItem (SUKLabel s) (irToSUInKList l) [KItem]))"
| "irToSUInPat (KFunPat s l) database = KSubs [SUKKItem (SUKLabel s) (irToSUInKList l) [K]]"
| "irToSUInPat (ListFunPat s l) database = ListSubs [SUListKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (SetFunPat s l) database = SetSubs [SUSetKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (MapFunPat s l) database = MapSubs [SUMapKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (NormalPat a) database = irToSUInMatchFactor a"

fun irToSUInIRBagList where
"irToSUInIRBagList [] = []"
| "irToSUInIRBagList ((x,y,z)#l) = (ItemB x y (irToSUInBigKWithBag z))#(irToSUInIRBagList l)"

primrec sizeInSUKLabel
  and sizeInSUKItem
  and sizeInSUKListElem
  and sizeInSUKList
  and sizeInSUKElem
  and sizeInSUK
  and sizeInSUListElem
  and sizeInSUList
  and sizeInSUSetElem
  and sizeInSUSet
  and sizeInSUMapElem
  and sizeInSUMap
  and sizeInSUBigKWithBag
  and sizeInSUBigKWithLabel
  and sizeInSUBagElem
  and sizeInSUBag where
"sizeInSUKLabel (SUKLabel a) = 0"
|"sizeInSUKLabel (SUIdKLabel a) = 0"
| "sizeInSUKLabel (SUKLabelFun a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUKItem (SUKItem a b t) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUKItem (SUIdKItem a t) = 0"
| "sizeInSUKItem (SUHOLE t) = 0"
| "sizeInSUKListElem (ItemKl a) = 1 + (sizeInSUBigKWithLabel a)"
| "sizeInSUKListElem (IdKl a) = 0"
| "sizeInSUKList [] = 0"
| "sizeInSUKList (a#l) = 1 + (sizeInSUKListElem a) + (sizeInSUKList l)"
| "sizeInSUKElem (ItemFactor a) = 1 + (sizeInSUKItem a)"
| "sizeInSUKElem (IdFactor a) = 0"
| "sizeInSUKElem (SUKKItem a b t) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUK [] = 0"
| "sizeInSUK (a#l) = 1 + (sizeInSUKElem a) + (sizeInSUK l)"
| "sizeInSUListElem (ItemL a) = 1 + (sizeInSUK a)"
| "sizeInSUListElem (IdL a) = 0"
| "sizeInSUListElem (SUListKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUList [] = 0"
| "sizeInSUList (a#l) = 1 + (sizeInSUListElem a) + (sizeInSUList l)"
| "sizeInSUSetElem (ItemS a) = 1 + (sizeInSUK a)"
| "sizeInSUSetElem (IdS a) = 0"
| "sizeInSUSetElem (SUSetKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUSet [] = 0"
| "sizeInSUSet (a#l) = 1 + (sizeInSUSetElem a) + (sizeInSUSet l)"
| "sizeInSUMapElem (ItemM a b) = 1 + (sizeInSUK a) + (sizeInSUK b)"
| "sizeInSUMapElem (IdM a) = 0"
| "sizeInSUMapElem (SUMapKItem a b) = 1 + (sizeInSUKLabel a) + (sizeInSUKList b)"
| "sizeInSUMap [] = 0"
| "sizeInSUMap (a#l) = 1 + (sizeInSUMapElem a) + (sizeInSUMap l)"
| "sizeInSUBigKWithBag (SUK a) = 1 + (sizeInSUK a)"
| "sizeInSUBigKWithBag (SUList a) = 1 + (sizeInSUList a)"
| "sizeInSUBigKWithBag (SUSet a) = 1 + (sizeInSUSet a)"
| "sizeInSUBigKWithBag (SUMap a) = 1 + (sizeInSUMap a)"
| "sizeInSUBigKWithBag (SUBag a) = 1 + (sizeInSUBag a)"
| "sizeInSUBigKWithLabel (SUBigBag a) = 1 + (sizeInSUBigKWithBag a)"
| "sizeInSUBigKWithLabel (SUBigLabel a) = 1 + (sizeInSUKLabel a)"
| "sizeInSUBagElem (ItemB x y z) = 1 + (sizeInSUBigKWithBag z)"
| "sizeInSUBagElem (IdB a) = 0"
| "sizeInSUBag [] = 0"
| "sizeInSUBag (a#l) = 1 + (sizeInSUBagElem a) + (sizeInSUBag l)"

function suToIRInKLabel
    and suToIRInKItem
    and suToIRInKList
    and suToIRInK
    and suToIRInList
    and suToIRInSet
    and suToIRInMap
    and suToIRInBigKWithBag
    and suToIRInBigKWithLabel
    and suToIRInBag  where 
  "suToIRInKLabel (SUKLabel a) database = Some (NormalPat (KLabelMatching (IRKLabel a)))"
| "suToIRInKLabel (SUKLabelFun a b) database = (case getSUKLabelMeaning a of None \<Rightarrow> None
         | Some s \<Rightarrow> (case (suToIRInKList b database) of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (KLabelFunPat s b')))"
| "suToIRInKLabel (SUIdKLabel n) database = Some (NormalPat (KLabelMatching (IRIdKLabel n)))"
| "suToIRInKItem (SUKItem l r ty) database = (case getSUKLabelMeaning l of None \<Rightarrow>
     (case (suToIRInKLabel l database, suToIRInKList r database) 
        of (Some (NormalPat (KLabelMatching l')), Some r')
             \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' ty)))
         | _ \<Rightarrow> None)
      | Some s \<Rightarrow> (if isFunctionItem s database then
      (case suToIRInKList r database of None \<Rightarrow> None
          | Some r' \<Rightarrow> Some (KFunPat s r')) else
            (case (suToIRInKLabel l database, suToIRInKList r database) 
        of (Some (NormalPat (KLabelMatching l')), Some r')
                \<Rightarrow> Some (NormalPat (KItemMatching (IRKItem l' r' ty)))
         | _ \<Rightarrow> None)))"
| "suToIRInKItem (SUIdKItem a b) database = Some (NormalPat (KItemMatching (IRIdKItem a b)))"
| "suToIRInKItem (SUHOLE a) database = Some (NormalPat (KItemMatching (IRHOLE a)))"
| "suToIRInKList [] database = Some (KListPatNoVar [])"
| "suToIRInKList (b#l) database = (case suToIRInKList l database of None \<Rightarrow> None
        | Some (KListPatNoVar la) \<Rightarrow> (case b of (ItemKl x) 
         \<Rightarrow> (case suToIRInBigKWithLabel x database of None \<Rightarrow> None
            | Some x' \<Rightarrow> Some (KListPatNoVar (x'#la)))
           | IdKl x \<Rightarrow> Some (KListPat [] x la))
        | Some (KListPat la x ra) \<Rightarrow> (case b of (ItemKl u) 
         \<Rightarrow> (case suToIRInBigKWithLabel u database of None \<Rightarrow> None
            | Some u' \<Rightarrow> Some (KListPat (u'#la) x ra))
             | IdKl u \<Rightarrow> None))"
| "suToIRInBigKWithLabel (SUBigBag a) database =
      (case (suToIRInBigKWithBag a database) of None \<Rightarrow> None
                    | Some a' \<Rightarrow> Some (IRBigBag a'))"
| "suToIRInBigKWithLabel (SUBigLabel a) database = (case (suToIRInKLabel a database) of
        Some (NormalPat (KLabelMatching a')) \<Rightarrow> Some (IRBigLabel a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUK a) database = (case (suToIRInK a database) of
         Some (NormalPat (KMatching a')) \<Rightarrow> Some (IRK a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUList a) database = (case (suToIRInList a database) of
         Some (NormalPat (ListMatching a')) \<Rightarrow> Some (IRList a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUSet a) database = (case (suToIRInSet a database) of
         Some (NormalPat (SetMatching a')) \<Rightarrow> Some (IRSet a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUMap a) database = (case (suToIRInMap a database) of
         Some (NormalPat (MapMatching a')) \<Rightarrow> Some (IRMap a')
                    | _ \<Rightarrow> None)"
| "suToIRInBigKWithBag (SUBag a) database = (case (suToIRInBag a database) of None \<Rightarrow> None
                    | Some a' \<Rightarrow> Some (IRBag a'))"
| "suToIRInK [] database = Some (NormalPat (KMatching (KPat [] None)))"
| "suToIRInK (b#l) database = (case suToIRInK l database of
        Some (NormalPat (KMatching (KPat t None)))
          \<Rightarrow> (case b of (ItemFactor x) 
             \<Rightarrow> (if t = [] then (case x of (SUIdKItem xa xty) \<Rightarrow>
               if xty = [K] then Some (NormalPat (KMatching (KPat [] (Some xa))))
                 else Some (NormalPat (KMatching (KPat [(IRIdKItem xa xty)] None)))
           | _ \<Rightarrow> (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat [x'] None)))))
     else (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat (x'#t) None)))
             | _ \<Rightarrow> None))
           | IdFactor x \<Rightarrow> (if t = [] then
                 Some (NormalPat (KMatching (KPat [] (Some x)))) else
                 Some (NormalPat (KMatching (KPat ((IRIdKItem x [K])#t) None))))
           | SUKKItem u v ty \<Rightarrow> (if t = [] then
           (case getSUKLabelMeaning u of None \<Rightarrow> None
              | Some s \<Rightarrow> if isFunctionItem s database then
               (case suToIRInKList v database of Some v'
                    \<Rightarrow> Some (KFunPat s v')
                 | _ \<Rightarrow> None) else None) else None))
        | Some (NormalPat (KMatching (KPat t (Some v))))
         \<Rightarrow> (case b of (ItemFactor x) 
            \<Rightarrow> (case suToIRInKItem x database of Some (NormalPat (KItemMatching x'))
                 \<Rightarrow> Some (NormalPat (KMatching (KPat (x'#t) None)))
             | _ \<Rightarrow> None)
             | IdFactor x \<Rightarrow>
                   Some (NormalPat (KMatching (KPat ((IRIdKItem x [K])#t) (Some v))))
             | SUKKItem u v ty \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInList [] database = Some (NormalPat (ListMatching (ListPatNoVar [])))"
| "suToIRInList (b#l) database = (case suToIRInList l database of
       Some (NormalPat (ListMatching (ListPatNoVar la)))
         \<Rightarrow> (case b of (ItemL x)
           \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
            \<Rightarrow> Some (NormalPat (ListMatching (ListPatNoVar (x'#la))))
                       | _ \<Rightarrow> None)
           | IdL x \<Rightarrow> Some (NormalPat (ListMatching (ListPat [] x la)))
           | SUListKItem u v \<Rightarrow> if la = [] then 
             (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some s \<Rightarrow> (if isFunctionItem s database then
                  (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (ListFunPat s v')) else None))
                    else None)
        | Some (NormalPat (ListMatching (ListPat la x ra)))
           \<Rightarrow> (case b of (ItemL u)
             \<Rightarrow> (case suToIRInK u database of Some (NormalPat (KMatching u'))
              \<Rightarrow> Some (NormalPat (ListMatching (ListPat (u'#la) x ra)))
                  | _ \<Rightarrow> None)
                | IdL u \<Rightarrow> None
               | SUListKItem u v \<Rightarrow> None)
           | _ \<Rightarrow> None)"
| "suToIRInSet [] database = Some (NormalPat (SetMatching (SetPat [] None)))"
| "suToIRInSet (b#l) database = (case suToIRInSet l database of 
       Some (NormalPat (SetMatching (SetPat t None)))
       \<Rightarrow> (case b of (ItemS x) 
         \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
           \<Rightarrow> Some (NormalPat (SetMatching (SetPat (x'#t) None)))
                | _ \<Rightarrow> None)
           | IdS x \<Rightarrow> Some (NormalPat (SetMatching (SetPat t (Some x))))
          | SUSetKItem u v \<Rightarrow> if t = [] then
            (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some u' \<Rightarrow> if isFunctionItem u' database then
                 (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (SetFunPat u' v')) else None) else None)
        | Some (NormalPat (SetMatching (SetPat t (Some v))))
         \<Rightarrow> (case b of (ItemS x) 
         \<Rightarrow> (case suToIRInK x database of Some (NormalPat (KMatching x'))
            \<Rightarrow> Some (NormalPat (SetMatching (SetPat (x'#t) (Some v))))
                | _ \<Rightarrow> None)
             | IdS x \<Rightarrow> None
             | (SUSetKItem u v) \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInMap [] database = Some (NormalPat (MapMatching (MapPat [] None)))"
| "suToIRInMap (b#l) database = (case suToIRInMap l database of 
       Some (NormalPat (MapMatching (MapPat t None)))
       \<Rightarrow> (case b of (ItemM x y) 
         \<Rightarrow> (case (suToIRInK x database, suToIRInK y database)
          of (Some (NormalPat (KMatching x')), Some (NormalPat (KMatching y')))
           \<Rightarrow> Some (NormalPat (MapMatching (MapPat ((x',y')#t) None)))
                | _ \<Rightarrow> None)
           | IdM x \<Rightarrow> Some (NormalPat (MapMatching (MapPat t (Some x))))
          | SUMapKItem u v \<Rightarrow> if t = [] then
            (case getSUKLabelMeaning u of None \<Rightarrow> None
                | Some u' \<Rightarrow> if isFunctionItem u' database then
                 (case suToIRInKList v database of None \<Rightarrow> None
                    | Some v' \<Rightarrow> Some (MapFunPat u' v')) else None) else None)
        | Some (NormalPat (MapMatching (MapPat t (Some v))))
         \<Rightarrow> (case b of (ItemM x y)  \<Rightarrow> 
              (case (suToIRInK x database, suToIRInK y database) of
          (Some (NormalPat (KMatching x')), Some (NormalPat (KMatching y')))
            \<Rightarrow> Some (NormalPat (MapMatching (MapPat ((x',y')#t) (Some v))))
                | _ \<Rightarrow> None)
             | IdM x \<Rightarrow> None
             | (SUMapKItem u v) \<Rightarrow> None)
        | _ \<Rightarrow> None)"
| "suToIRInBag [] database = Some (BagPat [] None)"
| "suToIRInBag (b#l) database = (case suToIRInBag l database of None \<Rightarrow> None
        | Some (BagPat t None) \<Rightarrow> (case b of (ItemB a b c) 
         \<Rightarrow> (case suToIRInBigKWithBag c database of None \<Rightarrow> None
            | Some c' \<Rightarrow> Some (BagPat ((a,b,c')#t) None))
           | IdB x \<Rightarrow> Some (BagPat t (Some x)))
        | Some (BagPat t (Some v)) \<Rightarrow> (case b of (ItemB a b c) 
         \<Rightarrow> (case suToIRInBigKWithBag c database of None \<Rightarrow> None
            | Some c' \<Rightarrow> Some (BagPat ((a,b,c')#t) (Some v)))
           | IdB x \<Rightarrow> None))"
by pat_completeness auto

termination
by (relation "measure (\<lambda> x . (case x of Inl x1 => (case x1 of Inl x2
       \<Rightarrow> (case x2 of Inl (a,b) \<Rightarrow> sizeInSUKLabel a | Inr (a,b) \<Rightarrow> sizeInSUKItem a)
        | Inr x3 \<Rightarrow> (case x3 of Inl (a,b) \<Rightarrow> sizeInSUKList a | Inr x4 \<Rightarrow> 
       (case x4 of Inl (a,b) \<Rightarrow> sizeInSUK a | Inr (a,b) \<Rightarrow> sizeInSUList a)))
      | Inr x1 => (case x1 of Inl x2
       \<Rightarrow> (case x2 of Inl (a,b) \<Rightarrow> sizeInSUSet a | Inr (a,b) \<Rightarrow> sizeInSUMap a)
        | Inr x3 \<Rightarrow> (case x3 of Inl (a,b) \<Rightarrow> sizeInSUBigKWithBag a | Inr x4 \<Rightarrow> 
       (case x4 of Inl (a,b) \<Rightarrow> sizeInSUBigKWithLabel a | Inr (a,b) \<Rightarrow> sizeInSUBag a)))))") auto

primrec suToIRInSubsFactor where
"suToIRInSubsFactor (KLabelSubs a) database = (suToIRInKLabel a database)"
| "suToIRInSubsFactor (KItemSubs a) database = (suToIRInKItem a database)"
| "suToIRInSubsFactor (KSubs a) database = (suToIRInK a database)"
| "suToIRInSubsFactor (KListSubs a) database = (case suToIRInKList a database of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (NormalPat (KListMatching a')))"
| "suToIRInSubsFactor (ListSubs a) database = (suToIRInList a database)"
| "suToIRInSubsFactor (SetSubs a) database = (suToIRInSet a database)"
| "suToIRInSubsFactor (MapSubs a) database = (suToIRInMap a database)"
| "suToIRInSubsFactor (BagSubs a) database = (case suToIRInBag a database of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (NormalPat (BagMatching a')))"

(* check the syntatic congruence of two ir terms *)
function syntacticMonoidInSUKLabel
    and syntacticMonoidInSUKItem
    and syntacticMonoidInSUKList
    and syntacticMonoidInSUK
    and syntacticMonoidInSUList
    and syntacticMonoidInSUSet
    and syntacticMonoidInSUMap
    and syntacticMonoidInSUBigKWithBag
    and syntacticMonoidInSUBigKWithLabel
    and syntacticMonoidInSUBag
    and syntacticMonoidInSUSubSet
    and syntacticMonoidInSUMember
    and syntacticMonoidInSUSubMap
    and syntacticMonoidInSUMapMember
    and syntacticMonoidInSUBagMember where
 "syntacticMonoidInSUKLabel (SUKLabel a) S subG =
   (case S of (SUKLabel a') \<Rightarrow>
      (if a = a' then Some (SUKLabel a) else None)
       | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKLabel (SUIdKLabel a) B subG = (case B of SUIdKLabel a' \<Rightarrow>
                                  if a = a' then Some (SUIdKLabel a)
                                  else None | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKLabel (SUKLabelFun a b) B subG = (case B of SUKLabelFun a' b' \<Rightarrow>
     (case syntacticMonoidInSUKLabel a a' subG of None \<Rightarrow> None
    | Some a1 \<Rightarrow> (case syntacticMonoidInSUKList b b' subG of None \<Rightarrow> None
                 | Some ba \<Rightarrow> Some (SUKLabelFun a1 ba))) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUKItem l r ty) S subG = (case S of (SUKItem l' r' ty') \<Rightarrow>
  (case (syntacticMonoidInSUKLabel l l' subG, syntacticMonoidInSUKList r r' subG) of (Some la, Some ra)
       \<Rightarrow> (case meet ty ty' subG of [] \<Rightarrow> None
       | (x#xl) \<Rightarrow> Some (SUKItem la ra (x#xl)))
    | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUHOLE a) S subG = (case S of (SUHOLE a') \<Rightarrow>
     (case meet a a' subG of [] \<Rightarrow> None | (x#xl) \<Rightarrow>
               Some (SUHOLE (x#xl))) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUIdKItem a b) B subG = (case B of SUIdKItem a' b' \<Rightarrow>
         if (a = a') then (case meet b b' subG of [] \<Rightarrow> None
         | (x#xl) \<Rightarrow> Some (SUIdKItem a (x#xl))) else None | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKList [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKList (b#l) S subG = (case S of [] \<Rightarrow> None
         | (b'#l') \<Rightarrow> (case (b,b') of (ItemKl bs, ItemKl bs') \<Rightarrow>
         (case syntacticMonoidInSUBigKWithLabel bs bs' subG of None \<Rightarrow> None
       | Some bsa \<Rightarrow> (case syntacticMonoidInSUKList l l' subG of None \<Rightarrow> None
       | Some la \<Rightarrow> Some ((ItemKl bsa)#la)))
         | (IdKl x, IdKl x') \<Rightarrow>  if x = x' then
       (case syntacticMonoidInSUKList l l' subG of None \<Rightarrow> None
           | Some la \<Rightarrow> Some ((IdKl x)#la)) else None | _ \<Rightarrow> None))"
| "syntacticMonoidInSUBigKWithLabel (SUBigBag a) b subG =
   (case b of (SUBigBag a') \<Rightarrow>
   (case syntacticMonoidInSUBigKWithBag a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBigBag aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithLabel (SUBigLabel a) b subG =
   (case b of (SUBigLabel a') \<Rightarrow>
   (case syntacticMonoidInSUKLabel a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBigLabel aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUK a) b subG =
   (case b of (SUK a') \<Rightarrow>
   (case syntacticMonoidInSUK a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUK aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUList a) b subG =
   (case b of (SUList a') \<Rightarrow>
   (case syntacticMonoidInSUList a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUList aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUSet a) b subG =
   (case b of (SUSet a') \<Rightarrow>
   (case syntacticMonoidInSUSet a a' a subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUSet aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUMap a) b subG =
   (case b of (SUMap a') \<Rightarrow>
   (case syntacticMonoidInSUMap a a' a subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUMap aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBigKWithBag (SUBag a) b subG =
   (case b of (SUBag a') \<Rightarrow>
   (case syntacticMonoidInSUBag a a' subG of None \<Rightarrow> None
      | Some aa \<Rightarrow> Some (SUBag aa)) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUK [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUK (b#l) S subG = (case S of (b'#l') \<Rightarrow>
       (case (b,b') of (ItemFactor x, ItemFactor x') \<Rightarrow>
          (case (syntacticMonoidInSUKItem x x' subG, syntacticMonoidInSUK l l' subG)
           of (Some xa, Some la) \<Rightarrow> Some ((ItemFactor xa)#la) | _ \<Rightarrow> None)
          | (IdFactor x, IdFactor x') \<Rightarrow> if x = x' then
            (case (syntacticMonoidInSUK l l' subG) of None \<Rightarrow> None
               | Some la \<Rightarrow> Some ((IdFactor x)#la)) else None
          | (IdFactor x, ItemFactor (SUIdKItem x' ty)) \<Rightarrow> 
             if x = x' then (case syntacticMonoidInSUK l l' subG of None \<Rightarrow> None
                 | Some la \<Rightarrow> Some ((ItemFactor (SUIdKItem x' ty))#la)) else None
          | (ItemFactor (SUIdKItem x ty), IdFactor x') \<Rightarrow> if x = x' then
              (case syntacticMonoidInSUK l l' subG of None \<Rightarrow> None
                 | Some la \<Rightarrow> Some ((ItemFactor (SUIdKItem x ty))#la)) else None
   | (SUKKItem x y ty, SUKKItem x' y' ty')
      \<Rightarrow> (case (syntacticMonoidInSUKLabel x x' subG,
       syntacticMonoidInSUKList y y' subG, syntacticMonoidInSUK l l' subG) of 
       (Some xa, Some ya, Some la) \<Rightarrow> (case meet ty ty' subG of [] \<Rightarrow> None
          | (newTy#newTyl) \<Rightarrow> Some ((SUKKItem xa ya (newTy#newTyl))#la))
        | _ \<Rightarrow> None) | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUList [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUList (b#l) S subG = (case S of (b'#l') \<Rightarrow>
       (case (b,b') of (ItemL x, ItemL x') \<Rightarrow>
     (case (syntacticMonoidInSUK x x' subG, syntacticMonoidInSUList l l' subG)
       of (Some xa, Some la) \<Rightarrow> Some ((ItemL xa)#la) | _ \<Rightarrow> None)
      | (IdL x, IdL x') \<Rightarrow> if x = x' then
     (case syntacticMonoidInSUList l l' subG of None \<Rightarrow> None
        | Some la \<Rightarrow> Some ((IdL x)#la)) else None
      | (SUListKItem x y, SUListKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG,
       syntacticMonoidInSUList l l' subG) of (Some xa, Some ya, Some la) \<Rightarrow>
           Some ((SUListKItem xa ya)#la) | _ \<Rightarrow> None)
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUMember b [] subG = None"
| "syntacticMonoidInSUMember b (b'#l) subG = (case (b,b')
   of (ItemS x, ItemS x') \<Rightarrow>
   (case syntacticMonoidInSUK x' x subG of None \<Rightarrow> syntacticMonoidInSUMember b l subG
      | Some xa \<Rightarrow> Some (ItemS xa))
    | (IdS x, IdS x') \<Rightarrow> if x = x' then Some (IdS x) else syntacticMonoidInSUMember b l subG
    | (SUSetKItem x y, SUSetKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x' x subG, syntacticMonoidInSUKList y' y subG)
      of (Some xa, Some ya) \<Rightarrow> Some (SUSetKItem xa ya)
        | _ \<Rightarrow> syntacticMonoidInSUMember b l subG) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUSubSet [] T subG = Some []"
| "syntacticMonoidInSUSubSet (b#l) T subG =
      (case syntacticMonoidInSUMember b T subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case syntacticMonoidInSUSubSet l T subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some (b'#l')))"
| "syntacticMonoidInSUSet [] S T subG = syntacticMonoidInSUSubSet S T subG"
| "syntacticMonoidInSUSet (b#l) S T subG =
    (case syntacticMonoidInSUMember b S subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> syntacticMonoidInSUSet l S T subG)"
| "syntacticMonoidInSUMapMember b [] subG = None"
| "syntacticMonoidInSUMapMember b (b'#l) subG = (case (b,b')
   of (ItemM x y, ItemM x' y') \<Rightarrow>
   (case syntacticMonoidInSUK x' x subG of None \<Rightarrow> syntacticMonoidInSUMapMember b l subG
      | Some xa \<Rightarrow> (case syntacticMonoidInSUK y' y subG of None \<Rightarrow> None
       | Some ya \<Rightarrow> Some (ItemM xa ya)))
    | (IdM x, IdM x') \<Rightarrow> if x = x' then Some (IdM x)
                 else syntacticMonoidInSUMapMember b l subG
    | (SUMapKItem x y, SUMapKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x' x subG, syntacticMonoidInSUKList y' y subG)
      of (Some xa, Some ya) \<Rightarrow> Some (SUMapKItem xa ya)
        | _ \<Rightarrow> syntacticMonoidInSUMapMember b l subG) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUSubMap [] T subG = Some []"
| "syntacticMonoidInSUSubMap (b#l) T subG =
      (case syntacticMonoidInSUMapMember b T subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case syntacticMonoidInSUSubMap l T subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some (b'#l')))"
| "syntacticMonoidInSUMap [] S T subG = syntacticMonoidInSUSubMap S T subG"
| "syntacticMonoidInSUMap (b#l) S T subG =
    (case syntacticMonoidInSUMapMember b S subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> syntacticMonoidInSUMap l S T subG)"
| "syntacticMonoidInSUBagMember b [] subG = None"
| "syntacticMonoidInSUBagMember b (b'#l) subG = (case (b,b') of
       (ItemB x y z,ItemB x' y' z') \<Rightarrow>
     (if x = x' then (case syntacticMonoidInSUBigKWithBag z' z subG of None \<Rightarrow> None
        | Some za \<Rightarrow> Some (ItemB x y za, l)) else
     (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
       | Some (ba,la) \<Rightarrow> Some (ba,b'#la)))
     | (IdB x, IdB x') \<Rightarrow> if x = x' then Some (IdB x, l)
          else (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
           | Some (ba, la) \<Rightarrow> Some (ba, (IdB x')#la))
     | _ \<Rightarrow> (case syntacticMonoidInSUBagMember b l subG of None \<Rightarrow> None
         | Some (ba,la) \<Rightarrow> Some (ba, b'#la)))"
| "syntacticMonoidInSUBag [] S subG = (case S of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "syntacticMonoidInSUBag (b#l) S subG =
    (case syntacticMonoidInSUBagMember b S subG of None \<Rightarrow> None
       | Some (ba, S') \<Rightarrow> (case syntacticMonoidInSUBag l S' subG of None \<Rightarrow> None
           | Some la \<Rightarrow> Some (ba#la)))"
by pat_completeness auto

termination sorry

(* giving a configuration and getting a initial program state of it. *)
primrec composeConfiAndProgInSUKLabel
    and composeConfiAndProgInSUKItem
    and composeConfiAndProgInSUKListElem
    and composeConfiAndProgInSUKList
    and composeConfiAndProgInSUKElem
    and composeConfiAndProgInSUK
    and composeConfiAndProgInSUListElem
    and composeConfiAndProgInSUList
    and composeConfiAndProgInSUSetElem
    and composeConfiAndProgInSUSet
    and composeConfiAndProgInSUMapElem
    and composeConfiAndProgInSUMap
    and composeConfiAndProgInSUBigKWithBag
    and composeConfiAndProgInSUBigKWithLabel
    and composeConfiAndProgInSUBagElem
    and composeConfiAndProgInSUBag where
  "composeConfiAndProgInSUKLabel (SUKLabel a) acc subG = Some (SUKLabel a)"
| "composeConfiAndProgInSUKLabel (SUKLabelFun a b) acc subG =
      (case composeConfiAndProgInSUKLabel a acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> 
             (case composeConfiAndProgInSUKList b acc subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "composeConfiAndProgInSUKLabel (SUIdKLabel n) acc subG =
       (case getValueTerm n acc of Some (KLabelSubs a) \<Rightarrow> Some a
         | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKItem (SUKItem l r ty) acc subG =
    (case composeConfiAndProgInSUKLabel l acc subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> (case composeConfiAndProgInSUKList r acc subG of
              None \<Rightarrow> None
             | Some r' \<Rightarrow> Some [ItemFactor (SUKItem l' r' ty)]))"
| "composeConfiAndProgInSUKItem (SUIdKItem a b) acc subG =
     (case getValueTerm a acc of
         Some (KItemSubs (SUKItem l' r' ty')) \<Rightarrow>
       if subsortList ty' b subG then Some [ItemFactor (SUKItem l' r' ty')] else None
        | Some (KItemSubs (SUHOLE ty)) \<Rightarrow> if subsortList ty b subG then
         Some [ItemFactor (SUHOLE ty)] else None
        | Some (KSubs a) \<Rightarrow> if b = [K] then Some a else None
        | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKItem (SUHOLE a) acc subG = Some [ItemFactor (SUHOLE a)]"
| "composeConfiAndProgInSUKListElem (ItemKl s) acc subG =
     (case composeConfiAndProgInSUBigKWithLabel s acc subG of None \<Rightarrow> None
          | Some s' \<Rightarrow> Some [ItemKl s'])"
| "composeConfiAndProgInSUKListElem (IdKl s) acc subG =
    (case getValueTerm s acc of Some (KListSubs t) \<Rightarrow>
              Some t | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKList [] acc subG = Some []"
| "composeConfiAndProgInSUKList (b#l) acc subG =
   (case composeConfiAndProgInSUKListElem b acc subG of None \<Rightarrow> None
     | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList l acc subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (a'@l')))"
| "composeConfiAndProgInSUBigKWithLabel (SUBigBag a) acc subG =
      (case composeConfiAndProgInSUBigKWithBag a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "composeConfiAndProgInSUBigKWithLabel (SUBigLabel a) acc subG =
      (case composeConfiAndProgInSUKLabel a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "composeConfiAndProgInSUBigKWithBag (SUK a) acc subG =
      (case composeConfiAndProgInSUK a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "composeConfiAndProgInSUBigKWithBag (SUList a) acc subG =
      (case composeConfiAndProgInSUList a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "composeConfiAndProgInSUBigKWithBag (SUSet a) acc subG =
      (case composeConfiAndProgInSUSet a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "composeConfiAndProgInSUBigKWithBag (SUMap a) acc subG =
      (case composeConfiAndProgInSUMap a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "composeConfiAndProgInSUBigKWithBag (SUBag a) acc subG =
      (case composeConfiAndProgInSUBag a acc subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "composeConfiAndProgInSUKElem (ItemFactor x) acc subG =
    composeConfiAndProgInSUKItem x acc subG"
| "composeConfiAndProgInSUKElem (IdFactor x) acc subG =
    (case getValueTerm x acc of Some (KSubs a) \<Rightarrow> Some a
              | Some (KItemSubs a) \<Rightarrow> Some [(ItemFactor a)] | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUKElem (SUKKItem x y z) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some ([SUKKItem a' b' z])))"
| "composeConfiAndProgInSUK [] acc subG = Some []"
| "composeConfiAndProgInSUK (b#l) acc subG =
      (case composeConfiAndProgInSUKElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUK l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUListElem (ItemL x) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> Some [ItemL x'])"
| "composeConfiAndProgInSUListElem (IdL x) acc subG =
    (case getValueTerm x acc of Some (ListSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUListElem (SUListKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUListKItem a' b']))"
| "composeConfiAndProgInSUList [] acc subG = Some []"
| "composeConfiAndProgInSUList (b#l) acc subG =
      (case composeConfiAndProgInSUListElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUList l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUSetElem (ItemS x) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> Some [ItemS x'])"
| "composeConfiAndProgInSUSetElem (IdS x) acc subG =
    (case getValueTerm x acc of Some (SetSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUSetElem (SUSetKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUSetKItem a' b']))"
| "composeConfiAndProgInSUSet [] acc subG = Some []"
| "composeConfiAndProgInSUSet (b#l) acc subG =
    (case composeConfiAndProgInSUSetElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUSet l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUMapElem (ItemM x y) acc subG =
    (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
        | Some x' \<Rightarrow> (case composeConfiAndProgInSUK x acc subG of None \<Rightarrow> None
     | Some y' \<Rightarrow> Some [ItemM x' y']))"
| "composeConfiAndProgInSUMapElem (IdM x) acc subG =
    (case getValueTerm x acc of Some (MapSubs a) \<Rightarrow> Some a
      | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUMapElem (SUMapKItem x y) acc subG =
    (case composeConfiAndProgInSUKLabel x acc subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> (case composeConfiAndProgInSUKList y acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> Some [SUMapKItem a' b']))"
| "composeConfiAndProgInSUMap [] acc subG = Some []"
| "composeConfiAndProgInSUMap (b#l) acc subG =
    (case composeConfiAndProgInSUMapElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUMap l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"
| "composeConfiAndProgInSUBagElem (ItemB x y z) acc subG =
     (case composeConfiAndProgInSUBigKWithBag z acc subG of None \<Rightarrow> None
          | Some z' \<Rightarrow> Some [ItemB x y z'])"
| "composeConfiAndProgInSUBagElem (IdB s) acc subG =
    (case getValueTerm s acc of Some (BagSubs t) \<Rightarrow>
              Some t | _ \<Rightarrow> None)"
| "composeConfiAndProgInSUBag [] acc subG = Some []"
| "composeConfiAndProgInSUBag (b#l) acc subG =
    (case composeConfiAndProgInSUBagElem b acc subG of None \<Rightarrow> None
       | Some b' \<Rightarrow> (case composeConfiAndProgInSUBag l acc subG of None \<Rightarrow> None
    | Some l' \<Rightarrow> Some (b'@l')))"

(* check if a kitem is contained in a structure, no function terms
    only used for checking correctness of configurations *)
primrec subSyntaxInSUKLabel
    and subSyntaxInSUKItem
    and subSyntaxInSUKListElem
    and subSyntaxInSUKList
    and subSyntaxInSUKElem
    and subSyntaxInSUK
    and subSyntaxInSUListElem
    and subSyntaxInSUList
    and subSyntaxInSUSetElem
    and subSyntaxInSUSet
    and subSyntaxInSUMapElem
    and subSyntaxInSUMap
    and subSyntaxInSUBigKWithBag
    and subSyntaxInSUBigKWithLabel
    and subSyntaxInSUBagElem
    and subSyntaxInSUBag where
 "subSyntaxInSUKLabel s kl (SUKLabel a') subG = False"
| "subSyntaxInSUKLabel s kl (SUIdKLabel a) subG = False"
| "subSyntaxInSUKLabel s kl (SUKLabelFun a b) subG =
           (subSyntaxInSUKLabel s kl a subG \<or> subSyntaxInSUKList s kl b subG)"
| "subSyntaxInSUKItem s kl (SUKItem l r ty) subG = (case getSUKLabelMeaning l of None \<Rightarrow>
          (subSyntaxInSUKLabel s kl l subG \<or> subSyntaxInSUKList s kl r subG)
       | Some ss \<Rightarrow> if s = ss then
         (case syntacticMonoidInSUKList kl r subG of None \<Rightarrow> subSyntaxInSUKList s kl r subG
             | Some kl' \<Rightarrow> True) else subSyntaxInSUKList s kl r subG)"
| "subSyntaxInSUKItem s kl (SUHOLE a) subG = False"
| "subSyntaxInSUKItem s kl (SUIdKItem a b) subG = False"
| "subSyntaxInSUKListElem s kl (IdKl x) subG = False"
| "subSyntaxInSUKListElem s kl (ItemKl x) subG = subSyntaxInSUBigKWithLabel s kl x subG"
| "subSyntaxInSUKList s kl [] subG = False"
| "subSyntaxInSUKList s kl (b#l) subG = 
     (subSyntaxInSUKListElem s kl b subG \<or> subSyntaxInSUKList s kl l subG)"
| "subSyntaxInSUBigKWithLabel s kl (SUBigBag a) subG = subSyntaxInSUBigKWithBag s kl a subG"
| "subSyntaxInSUBigKWithLabel s kl (SUBigLabel a) subG = subSyntaxInSUKLabel s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUK a) subG = subSyntaxInSUK s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUList a) subG = subSyntaxInSUList s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUSet a) subG = subSyntaxInSUSet s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUMap a) subG = subSyntaxInSUMap s kl a subG"
| "subSyntaxInSUBigKWithBag s kl (SUBag a) subG = subSyntaxInSUBag s kl a subG"
| "subSyntaxInSUKElem s kl (IdFactor x) subG = False"
| "subSyntaxInSUKElem s kl (ItemFactor x) subG = subSyntaxInSUKItem s kl x subG"
| "subSyntaxInSUKElem s kl (SUKKItem x y ty) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUK s kl [] subG = False"
| "subSyntaxInSUK s kl (b#l) subG = (subSyntaxInSUKElem s kl b subG \<or> subSyntaxInSUK s kl l subG)"
| "subSyntaxInSUListElem s kl (IdL x) subG = False"
| "subSyntaxInSUListElem s kl (ItemL x) subG = subSyntaxInSUK s kl x subG"
| "subSyntaxInSUListElem s kl (SUListKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUList s kl [] subG = False"
| "subSyntaxInSUList s kl (b#l) subG =
            (subSyntaxInSUListElem s kl b subG \<or> subSyntaxInSUList s kl l subG)"
| "subSyntaxInSUSetElem s kl (IdS x) subG = False"
| "subSyntaxInSUSetElem s kl (ItemS x) subG = subSyntaxInSUK s kl x subG"
| "subSyntaxInSUSetElem s kl (SUSetKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUSet s kl [] subG = False"
| "subSyntaxInSUSet s kl (b#l) subG = 
   (subSyntaxInSUSetElem s kl b subG \<or> subSyntaxInSUSet s kl l subG)"
| "subSyntaxInSUMapElem s kl (IdM x) subG = False"
| "subSyntaxInSUMapElem s kl (ItemM x y) subG =
    (subSyntaxInSUK s kl x subG \<or> subSyntaxInSUK s kl y subG)"
| "subSyntaxInSUMapElem s kl (SUMapKItem x y) subG =
    (subSyntaxInSUKLabel s kl x subG \<or> subSyntaxInSUKList s kl y subG)"
| "subSyntaxInSUMap s kl [] subG = False"
| "subSyntaxInSUMap s kl (b#l) subG =
   (subSyntaxInSUMapElem s kl b subG \<or> subSyntaxInSUMap s kl l subG)"
| "subSyntaxInSUBagElem s kl (IdB x) subG = False"
| "subSyntaxInSUBagElem s kl (ItemB x y z) subG = subSyntaxInSUBigKWithBag s kl z subG"
| "subSyntaxInSUBag s kl [] subG = False"
| "subSyntaxInSUBag s kl (b#l) subG = 
      (subSyntaxInSUBagElem s kl b subG \<or> subSyntaxInSUBag s kl l subG)"

(* normalizing step, checking if two elements are the same in a set or a map*)
primrec isCommonElemInSUSet where
"isCommonElemInSUSet a [] subG = False"
| "isCommonElemInSUSet a (b#l) subG =
        (case a of ItemS v \<Rightarrow> (case b of ItemS v' \<Rightarrow>
           (case syntacticMonoidInSUK v v' subG of None \<Rightarrow> (isCommonElemInSUSet a l subG)
             | Some va \<Rightarrow> True)
             | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
          | IdS x \<Rightarrow> (case b of IdS x' \<Rightarrow>
                  if x = x' then True else (isCommonElemInSUSet a l subG)
                | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
          | SUSetKItem x y \<Rightarrow>
              (case b of SUSetKItem x' y' \<Rightarrow>
               (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
                 of (Some xa, Some ya) \<Rightarrow> True
                  | _ \<Rightarrow> (isCommonElemInSUSet a l subG))
                 | _ \<Rightarrow> (isCommonElemInSUSet a l subG)))"

primrec isCommonElemInSUMap where
"isCommonElemInSUMap a [] subG = False"
| "isCommonElemInSUMap a (b#l) subG =
        (case a of ItemM v w \<Rightarrow> (case b of ItemM v' w' \<Rightarrow>
           (case syntacticMonoidInSUK v v' subG of None \<Rightarrow>
             (isCommonElemInSUMap a l subG)
             | Some va \<Rightarrow> (case syntacticMonoidInSUK w w' subG of None \<Rightarrow>
             (isCommonElemInSUMap a l subG) | Some wa \<Rightarrow> True))
             | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
          | IdM x \<Rightarrow> (case b of IdM x' \<Rightarrow>
                  if x = x' then True else (isCommonElemInSUMap a l subG)
                | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
          | SUMapKItem x y \<Rightarrow>
              (case b of SUMapKItem x' y' \<Rightarrow>
               (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
                 of (Some xa, Some ya) \<Rightarrow> True
                  | _ \<Rightarrow> (isCommonElemInSUMap a l subG))
                 | _ \<Rightarrow> (isCommonElemInSUMap a l subG)))"

primrec getValueInSUMap where
"getValueInSUMap a [] subG = None"
| "getValueInSUMap a (b#l) subG = (case b of ItemM x y \<Rightarrow>
         (case syntacticMonoidInSUK a x subG of None \<Rightarrow> getValueInSUMap a l subG
            | Some xa \<Rightarrow>  Some y)
              | IdM x \<Rightarrow> getValueInSUMap a l subG
              | SUMapKItem x y \<Rightarrow> getValueInSUMap a l subG)"

(* merge duplicate copys of set and map 
     and if there is a map being non-functional, return none *)
primrec regularizeInSUKLabel
    and regularizeInSUKItem
    and regularizeInSUKListElem
    and regularizeInSUKList
    and regularizeInSUKElem
    and regularizeInSUK
    and regularizeInSUListElem
    and regularizeInSUList
    and regularizeInSUSetElem
    and regularizeInSUSet
    and regularizeInSUMapElem
    and regularizeInSUMap
    and regularizeInSUBigKWithBag
    and regularizeInSUBigKWithLabel
    and regularizeInSUBagElem
    and regularizeInSUBag where
 "regularizeInSUKLabel (SUKLabel a) subG = Some (SUKLabel a)"
| "regularizeInSUKLabel (SUIdKLabel a) subG = Some (SUIdKLabel a)"
| "regularizeInSUKLabel (SUKLabelFun a b) subG =
   (case (regularizeInSUKLabel a subG) of None \<Rightarrow> None
       | Some a' \<Rightarrow> (case (regularizeInSUKList b subG) of None \<Rightarrow> None
          | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "regularizeInSUKItem (SUKItem l r ty) subG=
   (case (regularizeInSUKLabel l subG) of None \<Rightarrow> None
       | Some a' \<Rightarrow> (case (regularizeInSUKList r subG) of None \<Rightarrow> None
          | Some b' \<Rightarrow> Some (SUKItem a' b' ty)))"
| "regularizeInSUKItem (SUHOLE a) subG = Some (SUHOLE a)"
| "regularizeInSUKItem (SUIdKItem a b) subG = Some (SUIdKItem a b)"
| "regularizeInSUKListElem (IdKl x) subG = Some (IdKl x)"
| "regularizeInSUKListElem (ItemKl x) subG = (case (regularizeInSUBigKWithLabel x subG)
    of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemKl x'))"
| "regularizeInSUKList [] subG = Some []"
| "regularizeInSUKList (b#l) subG =
   (case regularizeInSUKListElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUKList l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUBigKWithLabel (SUBigBag a) subG =
    (case regularizeInSUBigKWithBag a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "regularizeInSUBigKWithLabel (SUBigLabel a) subG =
    (case regularizeInSUKLabel a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "regularizeInSUBigKWithBag (SUK a) subG =
    (case regularizeInSUK a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "regularizeInSUBigKWithBag (SUList a) subG =
    (case regularizeInSUList a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "regularizeInSUBigKWithBag (SUSet a) subG =
    (case regularizeInSUSet a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "regularizeInSUBigKWithBag (SUMap a) subG =
    (case regularizeInSUMap a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "regularizeInSUBigKWithBag (SUBag a) subG =
    (case regularizeInSUBag a subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "regularizeInSUKElem (IdFactor x) subG = Some (IdFactor x)"
| "regularizeInSUKElem (ItemFactor x) subG = (case (regularizeInSUKItem x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemFactor x'))"
| "regularizeInSUKElem (SUKKItem x y z) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUKKItem x' y' z)))"
| "regularizeInSUK [] subG = Some []"
| "regularizeInSUK (b#l) subG =
   (case regularizeInSUKElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUK l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUListElem (IdL x) subG = Some (IdL x)"
| "regularizeInSUListElem (ItemL x) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemL x'))"
| "regularizeInSUListElem (SUListKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUListKItem x' y')))"
| "regularizeInSUList [] subG = Some []"
| "regularizeInSUList (b#l) subG =
   (case regularizeInSUListElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUList l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"
| "regularizeInSUSetElem (IdS x) subG = Some (IdS x)"
| "regularizeInSUSetElem (ItemS x) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> Some (ItemS x'))"
| "regularizeInSUSetElem (SUSetKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUSetKItem x' y')))"
| "regularizeInSUSet [] subG = Some []"
| "regularizeInSUSet (b#l) subG =
   (case regularizeInSUSetElem b subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case regularizeInSUSet l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> (if isCommonElemInSUSet b' l' subG
            then Some l' else Some (b'#l'))))"
| "regularizeInSUMapElem (IdM x) subG = Some (IdM x)"
| "regularizeInSUMapElem (ItemM x y) subG = (case (regularizeInSUK x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow> (case regularizeInSUK y subG of None \<Rightarrow> None
          | Some y' \<Rightarrow>  Some (ItemM x' y')))"
| "regularizeInSUMapElem (SUMapKItem x y) subG = (case (regularizeInSUKLabel x subG)
     of None \<Rightarrow> None | Some x' \<Rightarrow>
    (case regularizeInSUKList y subG of None \<Rightarrow> None
       | Some y' \<Rightarrow> Some (SUMapKItem x' y')))"
| "regularizeInSUMap [] subG = Some []"
| "regularizeInSUMap (b#l) subG =
   (case regularizeInSUMapElem b subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case regularizeInSUMap l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> (if isCommonElemInSUMap b' l' subG
            then Some l' else 
   (case b' of (ItemM x y) \<Rightarrow> (case getValueInSUMap x l' subG of None \<Rightarrow> Some (b'#l')
          | Some y' \<Rightarrow> None)
     | _ \<Rightarrow> Some (b'#l')))))"
| "regularizeInSUBagElem (IdB x) subG = Some (IdB x)"
| "regularizeInSUBagElem (ItemB x y z) subG = (case (regularizeInSUBigKWithBag z subG)
    of None \<Rightarrow> None | Some z' \<Rightarrow> Some (ItemB x y z'))"
| "regularizeInSUBag [] subG = Some []"
| "regularizeInSUBag (b#l) subG =
   (case regularizeInSUBagElem b subG of None \<Rightarrow> None
     | Some b' \<Rightarrow> (case regularizeInSUBag l subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some (b'#l')))"

(* compiling strict rules and context rules *)
definition genKListByTypeListFactor where
"genKListByTypeListFactor ty newVar subG =
     (if subsortList ty [List] subG then
             (ItemKl (SUBigBag (SUList ([IdL ( newVar)]))))
     else if subsortList ty [Set] subG then
             (ItemKl (SUBigBag (SUSet ([IdS ( newVar)]))))
     else if subsortList ty [Map] subG then
             (ItemKl (SUBigBag (SUMap ([IdM ( newVar)]))))
     else if subsortList ty [Bag] subG then
             (ItemKl (SUBigLabel (SUIdKLabel ( newVar))))
     else if subsortList ty [KLabel] subG then
             (ItemKl (SUBigBag (SUBag ([IdB ( newVar)]))))
     else if ty = [K] then (ItemKl (SUBigBag (SUK ([IdFactor ( newVar)]))))
        else (ItemKl (SUBigBag (SUK ([ItemFactor (SUIdKItem ( newVar) ty)])))))"

primrec genKListByTypeList where
"genKListByTypeList [] vars subG = []"
| "genKListByTypeList (ty#l) vars subG = (case freshVar vars of newVar \<Rightarrow>
      (genKListByTypeListFactor ty newVar subG)#(genKListByTypeList l (newVar#vars) subG))"

definition genKItemByTypeList where
"genKItemByTypeList s sty l vars subG = SUKItem (SUKLabel s) (genKListByTypeList l vars subG) sty"

primrec splitHoleFromKList where
"splitHoleFromKList (c::nat) n [] = None"
| "splitHoleFromKList c n (b#l) = (if c = n then (case b of
      ItemKl (SUBigBag z) \<Rightarrow> (case z of SUK [IdFactor u] \<Rightarrow> 
       Some ((IdFactor u), (ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE [K])])))#l)
          | SUK [ItemFactor (SUIdKItem u ty)] \<Rightarrow> 
        Some (ItemFactor (SUIdKItem u ty), (ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE ty)])))#l)
           | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       else (case splitHoleFromKList (c + 1) n l of None \<Rightarrow> None
                | Some (u, v) \<Rightarrow> Some (u, b#v)))"

primrec getTypeFromKList where
"getTypeFromKList (c::nat) n [] = None"
| "getTypeFromKList c n (b#l) = (if c = n then (case b of
         ItemKl (SUBigLabel a) \<Rightarrow> Some [KLabel]
     | ItemKl (SUBigBag (SUK [IdFactor a])) \<Rightarrow> Some [K]
      | ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem a ty)])) \<Rightarrow> Some ty
    | ItemKl (SUBigBag (SUSet a)) \<Rightarrow> Some [Set]
    | ItemKl (SUBigBag (SUList a)) \<Rightarrow> Some [List]
    | ItemKl (SUBigBag (SUMap a)) \<Rightarrow> Some [Map] 
    | ItemKl (SUBigBag (SUBag a)) \<Rightarrow> Some [Bag]
    | _ \<Rightarrow> None) else getTypeFromKList c n l)"

fun getMetaVar where
"getMetaVar (IdFactor x) = Some x"
| "getMetaVar (ItemFactor x) = (case x of SUIdKItem a b \<Rightarrow> Some a
                       | _ \<Rightarrow> None)"
| "getMetaVar x = None"

primrec genStrictRulesAux where
"genStrictRulesAux s sty [] newKList database subG = Some []"
| "genStrictRulesAux s sty  (n#l) newKList database subG =
  (case getTypeFromKList 1 n newKList of None \<Rightarrow> None
     | Some newTy \<Rightarrow> if subsortList newTy [K] subG then 
    (case splitHoleFromKList 1 n newKList of None \<Rightarrow> None
       | Some (front, kl') \<Rightarrow> (case genStrictRulesAux s sty l newKList database subG
      of None \<Rightarrow> None | Some rl \<Rightarrow>
   (case freshVar (getAllMetaVarsInSUKList newKList) of newVar \<Rightarrow>
   (case suToIRInKList newKList database of Some left \<Rightarrow>
    (case suToIRInKList kl' database of Some left' \<Rightarrow>
    (case getMetaVar front of None \<Rightarrow> None | Some frontVar \<Rightarrow>
        Some ((KRulePat (KPat [IRKItem (IRKLabel s) left sty] (Some ( newVar))) 
           [front, ItemFactor (SUKItem (SUKLabel s) kl' sty), IdFactor (newVar)]
         (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                                 [ItemKl (SUBigBag (SUK [front]))] [Bool])]))] [Bool]) False)#
     (KRulePat (KPat [IRIdKItem frontVar [KResult],
             IRKItem (IRKLabel s) left' sty] (Some (newVar)))
           [ItemFactor (SUKItem (SUKLabel s) newKList sty), IdFactor (newVar)]
         (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#rl))
     | _ \<Rightarrow> None) | _ \<Rightarrow> None)))) else genStrictRulesAux s sty l newKList database subG)"

primrec genKListByTypeListInSeq where
"genKListByTypeListInSeq c n [] vars subG = []"
| "genKListByTypeListInSeq c n (ty#l) vars subG =
   (case freshVar vars of newVar \<Rightarrow>
    (if c < n \<and> subsortList ty [K] subG then
           ((ItemKl (SUBigBag (SUK ([ItemFactor (SUIdKItem ( newVar) [KResult])]))))
               # genKListByTypeListInSeq (c + 1) n l (( newVar)#vars) subG)
  else (genKListByTypeListFactor ty newVar subG)
        # genKListByTypeListInSeq (c + 1) n l (( newVar)#vars) subG))"

primrec genStrictRulesSeq :: "'upVar label \<Rightarrow> 'upVar sort list
         \<Rightarrow> 'upVar sort list list \<Rightarrow> nat \<Rightarrow>
        'upVar sort list list \<Rightarrow> ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list \<Rightarrow>
     ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<Rightarrow>
        ('upVar, 'var, 'metaVar) rulePat list option" where
"genStrictRulesSeq s sty tyl n [] database subG = Some []"
| "genStrictRulesSeq s sty tyl n (b#l) database subG =
 (if subsortList b [K] subG then 
    genStrictRulesSeq s sty tyl (n+1) l database subG else
    (case genKListByTypeListInSeq 1 n tyl [] subG of newKList \<Rightarrow>
    (case splitHoleFromKList 1 n newKList of None \<Rightarrow> None
       | Some (front, kl') \<Rightarrow> (case genStrictRulesSeq s sty tyl (n + 1) l database subG
      of None \<Rightarrow> None | Some rl \<Rightarrow>
   (case freshVar (getAllMetaVarsInSUKList newKList) of newVar \<Rightarrow>
   (case suToIRInKList newKList database of Some left \<Rightarrow>
    (case suToIRInKList kl' database of Some left' \<Rightarrow>
    (case getMetaVar front of None \<Rightarrow> None | Some frontVar \<Rightarrow>
        Some ((KRulePat (KPat [IRKItem (IRKLabel s) left sty] (Some ( newVar))) 
           [front, ItemFactor (SUKItem (SUKLabel s) kl' sty), IdFactor ( newVar)]
         (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                                 [ItemKl (SUBigBag (SUK [front]))] [Bool])]))] [Bool]) False)#
     (KRulePat (KPat [IRIdKItem frontVar [KResult],
             IRKItem (IRKLabel s) left' sty] (Some (newVar)))
           [ItemFactor (SUKItem (SUKLabel s) newKList sty), IdFactor (newVar)]
         (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#rl))
     | _ \<Rightarrow> None) | _ \<Rightarrow> None))))))"

primrec genStrictRules :: "'metaVar metaVar list \<Rightarrow> ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list \<Rightarrow>
   ('upVar sort list * 'upVar sort list list
   * 'upVar label KItemSyntax * synAttrib list * bool) list
   \<Rightarrow> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list
      \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list option" where
"genStrictRules S [] database subG = Some []"
| "genStrictRules S (b#l) database subG =
   (case b of (ty, tyl, SingleTon s, stl, True) \<Rightarrow>
        if Seqstrict \<in> set stl then (if getStrictInAttributes stl = None
        then (case genStrictRulesSeq s ty tyl 1 tyl database subG of None \<Rightarrow> None
          | Some rl \<Rightarrow> (case genStrictRules S l database subG of None \<Rightarrow> None
            | Some rl' \<Rightarrow> Some (rl@rl'))) else None)
     else (case getStrictList stl tyl of [] \<Rightarrow> genStrictRules S l database subG
       | (n#nl) \<Rightarrow> (case genKListByTypeList tyl [] subG of newKList \<Rightarrow>
          (case genStrictRulesAux s ty (n#nl) newKList database subG of None \<Rightarrow> None
           | Some rl \<Rightarrow> (case genStrictRules S l database subG of None \<Rightarrow> None
            | Some rl' \<Rightarrow> Some (rl@rl'))))))"

definition strictRuleTest ::
   "'metaVar metaVar list \<Rightarrow> ('upVar, 'var, 'acapvar, 'metaVar) kFile \<Rightarrow>
      ('upVar sort \<times> 'upVar sort list) list \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list option" where
"strictRuleTest vars Theory subG = (case syntaxSetToKItemTest Theory of None \<Rightarrow> None
  | Some database \<Rightarrow> (case genStrictRules vars database database subG of None \<Rightarrow> None
                    | Some rl \<Rightarrow> Some rl))"

(* important compilation check *)
definition validSyntaxSort :: "'metaVar metaVar list \<Rightarrow>
    ('upVar, 'var, 'acapvar, 'metaVar) kFile
   \<Rightarrow> ('upVar sort list * 'upVar sort list list *
     'upVar label KItemSyntax * synAttrib list * bool) list
   \<Rightarrow> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<Rightarrow> bool" where
"validSyntaxSort metaVars Theory database subG =
    (validSyntaxs database \<and> validArgSynax database \<and>
       syntaxSetToKItemTest Theory \<noteq> None
              \<and> strictRuleTest metaVars Theory subG \<noteq> None)"

primrec locateHoleInKLabel :: "('upVar, 'var, 'metaVar) kLabel
                                                 \<Rightarrow> ('upVar sort) option"
    and locateHoleInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite
                                                            \<Rightarrow> ('upVar sort) option"
    and locateHoleInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> ('upVar sort) option"
    and locateHoleInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite
                                                            \<Rightarrow> ('upVar sort) option"
    and locateHoleInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> ('upVar sort) option"
    and locateHoleInKListR :: "('upVar, 'var, 'metaVar) kList rewrite
                                                             \<Rightarrow> ('upVar sort) option"
    and locateHoleInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> ('upVar sort) option"
    and locateHoleInKR :: "('upVar, 'var, 'metaVar)
                   k rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInList :: "('upVar, 'var, 'metaVar)
                                theList \<Rightarrow> ('upVar sort) option"
    and locateHoleInListR :: "('upVar, 'var, 'metaVar)
                       theList rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> ('upVar sort) option"
    and locateHoleInSetR :: "('upVar, 'var, 'metaVar)
                          theSet rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> ('upVar sort) option"
    and locateHoleInMapR :: "('upVar, 'var, 'metaVar)
                              theMap rewrite \<Rightarrow> ('upVar sort) option"
    and locateHoleInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag
                                                        \<Rightarrow> ('upVar sort) option"
    and locateHoleInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> ('upVar sort) option"
    and locateHoleInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> ('upVar sort) option"
    and locateHoleInBagR :: "('upVar, 'var, 'metaVar)
                              bag rewrite \<Rightarrow> ('upVar sort) option"
 where
  "locateHoleInKLabel (KLabelC a) = None"
| "locateHoleInKLabel (KLabelFun a b) =
     (case locateHoleInKLabel a of None \<Rightarrow> locateHoleInKListR b
        | Some ty \<Rightarrow> (case locateHoleInKListR b of None \<Rightarrow> Some ty
        | Some ty' \<Rightarrow> None))"
| "locateHoleInKLabel (IdKLabel n) = None"
| "locateHoleInKLabelR (KTerm n) = locateHoleInKLabel n"
| "locateHoleInKLabelR (KRewrite l r) =
                    (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKLabel r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                 | Some a \<Rightarrow> (case locateHoleInKLabel r of None \<Rightarrow> Some a
                 | Some a' \<Rightarrow> None))"
| "locateHoleInKItem (KItemC l r ty) = (case (locateHoleInKLabelR l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                 | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                 | Some a' \<Rightarrow> None))"
| "locateHoleInKItem (Constant a b) = None"
| "locateHoleInKItem (IdKItem a b) = None"
| "locateHoleInKItem (HOLE a) = Some a"
| "locateHoleInKItemR (KTerm t) = locateHoleInKItem t"
| "locateHoleInKItemR (KRewrite l r) = (case (locateHoleInKItem l) of None
                          \<Rightarrow> (case locateHoleInKItem r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKItem r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKList (KListCon l r) = (case (locateHoleInKListR l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKList UnitKList = None"
| "locateHoleInKList (IdKList a) = None"
| "locateHoleInKList (KListItem a) = (locateHoleInBigKWithBag a)"
| "locateHoleInKListR (KTerm t) = locateHoleInKList t"
| "locateHoleInKListR (KRewrite l r) = (case (locateHoleInKList l) of None
                          \<Rightarrow> (case locateHoleInKList r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKList r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBigKWithBag (TheBigK a) = locateHoleInBigK a"
| "locateHoleInBigKWithBag (TheLabel a) = locateHoleInKLabelR a"
| "locateHoleInBigKWithBag (TheBigBag b) = locateHoleInBagR b"
| "locateHoleInBigK (TheK t) = locateHoleInKR t"
| "locateHoleInBigK (TheList t) = locateHoleInListR t"
| "locateHoleInBigK (TheSet t) = locateHoleInSetR t"
| "locateHoleInBigK (TheMap t) = locateHoleInMapR t"
| "locateHoleInK (Tilda l r) = (case (locateHoleInKR l) of None
                          \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInK UnitK = None"
| "locateHoleInK (IdK a) = None"
| "locateHoleInK (SingleK a) = (locateHoleInKItemR a)"
| "locateHoleInK (KFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInKR (KTerm a) = (locateHoleInK a)"
| "locateHoleInKR (KRewrite l r) = (case (locateHoleInK l) of None
                          \<Rightarrow> (case locateHoleInK r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInK r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInList (ListCon l r) = (case (locateHoleInListR l) of None
                          \<Rightarrow> (case locateHoleInListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInList UnitList = None"
| "locateHoleInList (IdList a) = None"
| "locateHoleInList (ListItem a) = locateHoleInKR a"
| "locateHoleInList (ListFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInListR (KTerm a) = (locateHoleInList a)"
| "locateHoleInListR (KRewrite l r) = (case (locateHoleInList l) of None
                          \<Rightarrow> (case locateHoleInList r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInList r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSet (SetCon l r) = (case (locateHoleInSetR l) of None
                          \<Rightarrow> (case locateHoleInSetR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInSetR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSet UnitSet = None"
| "locateHoleInSet (IdSet a) = None"
| "locateHoleInSet (SetItem a) = locateHoleInKR a"
| "locateHoleInSet (SetFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInSetR (KTerm a) = (locateHoleInSet a)"
| "locateHoleInSetR (KRewrite l r) = (case (locateHoleInSet l) of None
                          \<Rightarrow> (case locateHoleInSet r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInSet r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap (MapCon l r) = (case (locateHoleInMapR l) of None
                          \<Rightarrow> (case locateHoleInMapR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInMapR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap UnitMap = None"
| "locateHoleInMap (IdMap a) = None"
| "locateHoleInMap (MapItem l r) = (case (locateHoleInKR l) of None
                          \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMap (MapFun l r) = (case (locateHoleInKLabel l) of None
                          \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInKListR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInMapR (KTerm a) = (locateHoleInMap a)"
| "locateHoleInMapR (KRewrite l r) = (case (locateHoleInMap l) of None
                          \<Rightarrow> (case locateHoleInMap r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInMap r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBag (BagCon l r) = (case (locateHoleInBagR l) of None
                          \<Rightarrow> (case locateHoleInBagR r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInBagR r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"
| "locateHoleInBag UnitBag = None"
| "locateHoleInBag (IdBag a) = None"
| "locateHoleInBag (Xml a n t) =  locateHoleInBagR t"
| "locateHoleInBag (SingleCell a n t) =  locateHoleInBigK t"
| "locateHoleInBagR (KTerm a) = (locateHoleInBag a)"
| "locateHoleInBagR (KRewrite l r) = (case (locateHoleInBag l) of None
                          \<Rightarrow> (case locateHoleInBag r of None \<Rightarrow> None
                              | Some a \<Rightarrow> Some a)
                         | Some a \<Rightarrow> (case locateHoleInBag r of None \<Rightarrow> Some a
                         | Some a' \<Rightarrow> None))"


function fillHoleInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel"
    and fillHoleInKLabelR ::
         "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> 'metaVar metaVar
              \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel rewrite"
    and fillHoleInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kItem"
    and fillHoleInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kItem rewrite"
    and fillHoleInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kList"
    and fillHoleInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) kList rewrite"
    and fillHoleInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) k"
    and fillHoleInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) k rewrite"
    and fillHoleInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theList"
    and fillHoleInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theList rewrite"
    and fillHoleInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theSet"
    and fillHoleInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theSet rewrite"
    and fillHoleInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theMap"
    and fillHoleInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) theMap rewrite"
    and fillHoleInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bigKWithBag"
    and fillHoleInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bigK"
    and fillHoleInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bag"
    and fillHoleInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> 'metaVar metaVar
            \<Rightarrow> 'upVar sort \<Rightarrow> ('upVar, 'var, 'metaVar) bag rewrite"
 where
  "fillHoleInKLabel (KLabelC a) x ty = KLabelC a"
| "fillHoleInKLabel (KLabelFun a b) x ty =
              (KLabelFun (fillHoleInKLabel a x ty) (fillHoleInKListR b x ty))"
| "fillHoleInKLabel (IdKLabel n) x ty = (IdKLabel n)"
| "fillHoleInKLabelR (KTerm n) x ty = KTerm (fillHoleInKLabel n x ty)"
| "fillHoleInKLabelR (KRewrite l r) x ty =
                     KRewrite (fillHoleInKLabel l x ty) (fillHoleInKLabel r x ty)"
| "fillHoleInKItem (KItemC l r ty) x tya =
                  KItemC (fillHoleInKLabelR l x tya) (fillHoleInKListR r x tya) ty"
| "fillHoleInKItem (Constant a b) x ty = (Constant a b)"
| "fillHoleInKItem (IdKItem a b) x ty = (IdKItem a b)"
| "fillHoleInKItem (HOLE a) x ty = IdKItem x ty"
| "fillHoleInKItemR (KTerm t) x ty = KTerm (fillHoleInKItem t  x ty)"
| "fillHoleInKItemR (KRewrite l r) x ty =
          KRewrite (fillHoleInKItem l x ty) (fillHoleInKItem r x ty)"
| "fillHoleInKList (KListCon l r) x ty =
               KListCon (fillHoleInKListR l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInKList UnitKList x ty = UnitKList"
| "fillHoleInKList (IdKList a) x ty = (IdKList a)"
| "fillHoleInKList (KListItem a) x ty = KListItem (fillHoleInBigKWithBag a x ty)"
| "fillHoleInKListR (KTerm t) x ty = KTerm (fillHoleInKList t x ty)"
| "fillHoleInKListR (KRewrite l r) x ty =
                 KRewrite (fillHoleInKList l x ty) (fillHoleInKList r x ty)"
| "fillHoleInBigKWithBag (TheBigK a) x ty = TheBigK (fillHoleInBigK a x ty)"
| "fillHoleInBigKWithBag (TheBigBag b) x ty = TheBigBag (fillHoleInBagR b x ty)"
| "fillHoleInBigKWithBag (TheLabel b) x ty = TheLabel (fillHoleInKLabelR b x ty)"
| "fillHoleInBigK (TheK t) x ty = TheK (fillHoleInKR t x ty)"
| "fillHoleInBigK (TheList t) x ty = TheList (fillHoleInListR t x ty)"
| "fillHoleInBigK (TheSet t) x ty = TheSet (fillHoleInSetR t x ty)"
| "fillHoleInBigK (TheMap t) x ty = TheMap (fillHoleInMapR t x ty)"
| "fillHoleInK (Tilda l r) x ty =
                   Tilda (fillHoleInKR l x ty) (fillHoleInKR r x ty)"
| "fillHoleInK UnitK x ty = UnitK"
| "fillHoleInK (IdK a) x ty = (IdK a)"
| "fillHoleInK (SingleK a) x ty = SingleK (fillHoleInKItemR a x ty)"
| "fillHoleInK (KFun l r) x ty =
                  KFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInKR (KTerm a) x ty = KTerm (fillHoleInK a x ty)"
| "fillHoleInKR (KRewrite l r) x ty = KRewrite (fillHoleInK l x ty) (fillHoleInK r x ty)"
| "fillHoleInList (ListCon l r) x ty = ListCon (fillHoleInListR l x ty) (fillHoleInListR r x ty)"
| "fillHoleInList UnitList x ty = UnitList"
| "fillHoleInList (IdList a) x ty = (IdList a)"
| "fillHoleInList (ListItem a) x ty = ListItem (fillHoleInKR a x ty)"
| "fillHoleInList (ListFun l r) x ty = ListFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInListR (KTerm a) x ty = KTerm (fillHoleInList a x ty)"
| "fillHoleInListR (KRewrite l r) x ty =
                     KRewrite (fillHoleInList l x ty) (fillHoleInList r x ty)"
| "fillHoleInSet (SetCon l r) x ty = SetCon (fillHoleInSetR l x ty) (fillHoleInSetR r x ty)"
| "fillHoleInSet UnitSet x ty = UnitSet"
| "fillHoleInSet (IdSet a) x ty = (IdSet a)"
| "fillHoleInSet (SetItem a) x ty = SetItem (fillHoleInKR a x ty)"
| "fillHoleInSet (SetFun l r) x ty =  SetFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInSetR (KTerm a) x ty = KTerm (fillHoleInSet a x ty)"
| "fillHoleInSetR (KRewrite l r) x ty = KRewrite (fillHoleInSet l x ty) (fillHoleInSet r x ty)"
| "fillHoleInMap (MapCon l r) x ty = MapCon (fillHoleInMapR l x ty) (fillHoleInMapR r x ty)"
| "fillHoleInMap UnitMap x ty = UnitMap"
| "fillHoleInMap (IdMap a) x ty = (IdMap a)"
| "fillHoleInMap (MapItem l r) x ty = MapItem (fillHoleInKR l x ty) (fillHoleInKR r x ty)"
| "fillHoleInMap (MapFun l r) x ty = MapFun (fillHoleInKLabel l x ty) (fillHoleInKListR r x ty)"
| "fillHoleInMapR (KTerm a) x ty = KTerm (fillHoleInMap a x ty)"
| "fillHoleInMapR (KRewrite l r) x ty =
                    KRewrite (fillHoleInMap l x ty) (fillHoleInMap r x ty)"
| "fillHoleInBag (BagCon l r) x ty = BagCon (fillHoleInBagR l x ty) (fillHoleInBagR r x ty)"
| "fillHoleInBag UnitBag x ty = UnitBag"
| "fillHoleInBag (IdBag a) x ty = (IdBag a)"
| "fillHoleInBag (Xml a n t) x ty =  Xml a n (fillHoleInBagR t x ty)"
| "fillHoleInBag (SingleCell a n t) x ty =  SingleCell a n (fillHoleInBigK t x ty)"
| "fillHoleInBagR (KTerm a) x ty = KTerm (fillHoleInBag a x ty)"
| "fillHoleInBagR (KRewrite l r) x ty = KRewrite (fillHoleInBag l x ty) (fillHoleInBag r x ty)"
by pat_completeness auto

termination sorry

(* defining type checking algorithm for K and type adjustment *)
primrec updateMap where
"updateMap a b [] subG = Some [(a,b)]"
| "updateMap a b (x#l) subG = (case x of (a',b') \<Rightarrow> 
   (if a = a' then (case meet b b' subG of [] \<Rightarrow> None
     | (ty#tyl) \<Rightarrow> Some ((a,(ty#tyl))#l)) else
   (case (updateMap a b l subG) of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x#l'))))"

primrec updateBeta where
"updateBeta a b [] subG = Some []"
| "updateBeta a b (x#l) subG = (case x of (a',b') \<Rightarrow> 
   (if a = a' then (case meet b b' subG of [] \<Rightarrow> None
     | (ty#tyl) \<Rightarrow> Some ((a,(ty#tyl))#l)) else
   (case (updateBeta a b l subG) of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x#l'))))"

(*
primrec isMinInList where
"isMinInList a [] subG = True"
| "isMinInList a (b#l) subG = (if subsortList a b subG then isMinInList a l subG else False)"

primrec pickMinInListAux where
"pickMinInListAux l [] subG = None"
| "pickMinInListAux l (a#al) subG =
     (if isMinInList a (l@al) subG then Some a else pickMinInListAux (l@[a]) al subG)"

definition pickMinInList where
"pickMinInList l subG = pickMinInListAux [] l subG"


primrec makeSortMap where
"makeSortMap [] subG = Some []"
| "makeSortMap (a#l) subG = (case a of (x,y) \<Rightarrow> 
          (case pickMinInList y subG of None \<Rightarrow> None
             | Some v \<Rightarrow> (case makeSortMap l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some ((x,v)#l'))))"
*)

primrec hasIdInKList where
"hasIdInKList [] = False"
| "hasIdInKList (a#l) = (case a of IdKl x \<Rightarrow> True | _ \<Rightarrow> hasIdInKList l)"

primrec numberOfItemsInKList where
"numberOfItemsInKList [] = 0"
| "numberOfItemsInKList (x#l) = (case x of IdKl a \<Rightarrow> numberOfItemsInKList l
          | ItemKl a \<Rightarrow> 1 + numberOfItemsInKList l)"

(*
definition pickMinSortInTwo where
"pickMinSortInTwo a b subG = (if subsortList a b subG then Some a 
              else if subsortList b a subG then Some b
                else None)"

definition pickMinSortInThree where
"pickMinSortInThree a b c subG =
        (if subsortList a b subG \<and> subsortList a c subG then Some a 
     else if subsortList b a subG \<and> subsortList b c subG then Some b
     else if subsortList c a subG \<and> subsortList c b subG then Some c
                else None)"
*)

fun getDomainInIRKItem
  and getDomainInIRBigKWithBag
  and getDomainInIRBigKWithLabel
  and getDomainInIRK
  and getDomainInIRKList
  and getDomainInIRList
  and getDomainInIRSet
  and getDomainInIRMap
  and getDomainInIRBag where
"getDomainInIRKItem (IRKItem a b ty) = (case a of (IRIdKLabel x) \<Rightarrow> x#(getDomainInIRKList b)
          | _ \<Rightarrow> getDomainInIRKList b)"
| "getDomainInIRKItem (IRIdKItem a ty) = []"
| "getDomainInIRKItem (IRHOLE ty) = []"
| "getDomainInIRBigKWithBag (IRK a) = getDomainInIRK a"
| "getDomainInIRBigKWithBag (IRList a) = getDomainInIRList a"
| "getDomainInIRBigKWithBag (IRSet a) = getDomainInIRSet a"
| "getDomainInIRBigKWithBag (IRMap a) = getDomainInIRMap a"
| "getDomainInIRBigKWithBag (IRBag a) = getDomainInIRBag a"
| "getDomainInIRBigKWithLabel (IRBigBag a) = getDomainInIRBigKWithBag a"
| "getDomainInIRBigKWithLabel (IRBigLabel a) = []"
| "getDomainInIRK (KPat [] b) = []"
| "getDomainInIRK (KPat (x#l) b) = (getDomainInIRKItem x)@(getDomainInIRK (KPat l b))"
| "getDomainInIRKList (KListPatNoVar []) = []"
| "getDomainInIRKList (KListPatNoVar (x#l)) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPatNoVar l))"
| "getDomainInIRKList (KListPat [] b []) = []"
| "getDomainInIRKList (KListPat [] b (x#l)) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPat [] b l))"
| "getDomainInIRKList (KListPat (x#l) b S) = (getDomainInIRBigKWithLabel x)@
                                   (getDomainInIRKList (KListPat l b S))"
| "getDomainInIRList (ListPatNoVar []) = []"
| "getDomainInIRList (ListPatNoVar (x#l)) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPatNoVar l))"
| "getDomainInIRList (ListPat [] b []) = []"
| "getDomainInIRList (ListPat [] b (x#l)) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPat [] b l))"
| "getDomainInIRList (ListPat (x#l) b S) = (getDomainInIRK x)@
                                   (getDomainInIRList (ListPat l b S))"
| "getDomainInIRSet (SetPat [] b) = []"
| "getDomainInIRSet (SetPat (x#l) b) = (getDomainInIRK x)@
                                   (getDomainInIRSet (SetPat l b))"
| "getDomainInIRMap (MapPat [] b) = []"
| "getDomainInIRMap (MapPat ((x,y)#l) b) = (getDomainInIRK x)@(getDomainInIRK y)@
                                   (getDomainInIRMap (MapPat l b))"
| "getDomainInIRBag (BagPat [] b) = []"
| "getDomainInIRBag (BagPat ((x,y,z)#l) b) = (getDomainInIRBigKWithBag z)@
                                   (getDomainInIRBag (BagPat l b))"

primrec getDomainInMatchFactor where
"getDomainInMatchFactor (KLabelMatching a) = []"
| "getDomainInMatchFactor (KItemMatching a) = getDomainInIRKItem a"
| "getDomainInMatchFactor (KListMatching a) = getDomainInIRKList a"
| "getDomainInMatchFactor (KMatching a) = getDomainInIRK a"
| "getDomainInMatchFactor (ListMatching a) = getDomainInIRList a"
| "getDomainInMatchFactor (SetMatching a) = getDomainInIRSet a"
| "getDomainInMatchFactor (MapMatching a) = getDomainInIRMap a"
| "getDomainInMatchFactor (BagMatching a) = getDomainInIRBag a"

primrec getDomainInPat where
"getDomainInPat (KLabelFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (KFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (KItemFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (ListFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (SetFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (MapFunPat a b) = getDomainInIRKList b"
| "getDomainInPat (NormalPat a) = getDomainInMatchFactor a"

primrec constructSortMap where
"constructSortMap [] = []"
| "constructSortMap (a#l) = (a,[Top])#(constructSortMap l)"

fun hasNoTop where
"hasNoTop [] = True"
| "hasNoTop ((a,b)#l) = (if Top \<in> set b then False else hasNoTop l)"

fun getIdInSUKLabel where
"getIdInSUKLabel (SUIdKLabel a) = Some a"
| "getIdInSUKLabel a = None"

(* get domain of beta for configuration *)
fun getDomainInSUKLabel
  and getDomainInSUKItem
  and getDomainInSUBigKWithBag
  and getDomainInSUBigKWithLabel
  and getDomainInSUK
  and getDomainInSUKList
  and getDomainInSUList
  and getDomainInSUSet
  and getDomainInSUMap
  and getDomainInSUBag where
"getDomainInSUKLabel (SUKLabel a) = []"
| "getDomainInSUKLabel (SUIdKLabel x) = []"
| "getDomainInSUKLabel (SUKLabelFun x y) = (case x of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUKList y)
           | _ \<Rightarrow> getDomainInSUKList y)"
| "getDomainInSUKItem (SUKItem a b ty) = (case a of (SUIdKLabel x) \<Rightarrow> x#(getDomainInSUKList b)
          | _ \<Rightarrow> getDomainInSUKList b)"
| "getDomainInSUKItem (SUIdKItem a ty) = []"
| "getDomainInSUKItem (SUHOLE ty) = []"
| "getDomainInSUBigKWithBag (SUK a) = getDomainInSUK a"
| "getDomainInSUBigKWithBag (SUList a) = getDomainInSUList a"
| "getDomainInSUBigKWithBag (SUSet a) = getDomainInSUSet a"
| "getDomainInSUBigKWithBag (SUMap a) = getDomainInSUMap a"
| "getDomainInSUBigKWithBag (SUBag a) = getDomainInSUBag a"
| "getDomainInSUBigKWithLabel (SUBigBag a) = getDomainInSUBigKWithBag a"
| "getDomainInSUBigKWithLabel (SUBigLabel a) = []"
| "getDomainInSUK [] = []"
| "getDomainInSUK (x#l) = (case x of (ItemFactor x') \<Rightarrow> (getDomainInSUKItem x')@(getDomainInSUK l)
          | IdFactor x' \<Rightarrow> getDomainInSUK l
         | SUKKItem a b c \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUK l)
           | _ \<Rightarrow> getDomainInSUK l))"
| "getDomainInSUKList [] = []"
| "getDomainInSUKList (x#l) =
      (case x of (ItemKl x') \<Rightarrow> (getDomainInSUBigKWithLabel x')@(getDomainInSUKList l)
          | IdKl x' \<Rightarrow> getDomainInSUKList l)"
| "getDomainInSUList [] = []"
| "getDomainInSUList (x#l) = (case x of (ItemL x') \<Rightarrow> (getDomainInSUK x')@(getDomainInSUList l)
          | IdL x' \<Rightarrow> getDomainInSUList l
         | SUListKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUList l)
           | _ \<Rightarrow> getDomainInSUList l))"
| "getDomainInSUSet [] = []"
| "getDomainInSUSet (x#l) = (case x of (ItemS x') \<Rightarrow> (getDomainInSUK x')@(getDomainInSUSet l)
          | IdS x' \<Rightarrow> getDomainInSUSet l
         | SUSetKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUSet l)
           | _ \<Rightarrow> getDomainInSUSet l))"
| "getDomainInSUMap [] = []"
| "getDomainInSUMap (x#l) = (case x of (ItemM x' y')
      \<Rightarrow> (getDomainInSUK x')@((getDomainInSUK y')@(getDomainInSUMap l))
          | IdM x' \<Rightarrow> getDomainInSUMap l
         | SUMapKItem a b \<Rightarrow> (case a of (SUIdKLabel x') \<Rightarrow> x'#(getDomainInSUMap l)
           | _ \<Rightarrow> getDomainInSUMap l))"
| "getDomainInSUBag [] = []"
| "getDomainInSUBag (x#l) =
    (case x of (ItemB x' y' z') \<Rightarrow> (getDomainInSUBigKWithBag z')@(getDomainInSUBag l)
          | IdB x' \<Rightarrow> getDomainInSUBag l)"

(* type check terms *)
function checkTermsInSUKLabel
    and checkTermsInSUKItem
    and checkTermsInSUKListAux
    and checkTermsInNoneSUKList
    and checkTermsInSUKList
    and checkTermsInSUK
    and checkTermsInSUList
    and checkTermsInSUSet
    and checkTermsInSUMap
    and checkTermsInSUBigKWithBag
    and checkTermsInSUBigKWithLabel
    and checkTermsInSUBag where 
  "checkTermsInSUKLabel (SUKLabel a) acc beta database subG = Some (acc,beta, SUKLabel a)"
| "checkTermsInSUKLabel (SUKLabelFun a b) acc beta database subG = (case getSUKLabelMeaning a of 
       None \<Rightarrow> (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
          | Some (acc',beta', a') \<Rightarrow>
        (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
           | Some (acca,betaa, b') \<Rightarrow>
          (case getIdInSUKLabel a' of None \<Rightarrow> Some (acca,betaa,SUKLabelFun a' b')
        | Some x \<Rightarrow> (case updateMap x [KLabel] betaa subG of None \<Rightarrow> None
          | Some betab \<Rightarrow> Some (acca,betab, SUKLabelFun a' b')))))
    | Some s \<Rightarrow> (if isFunctionItem s database then 
     (case getArgSort s database of None \<Rightarrow> None
      | Some l \<Rightarrow> (case getSort s database of None \<Rightarrow> None
             | Some ty \<Rightarrow> if subsortList ty [KLabel] subG then
           (case checkTermsInSUKList b l acc beta database subG of None \<Rightarrow> None
           | Some (acc',beta', b') \<Rightarrow> Some (acc', beta', SUKLabelFun a b')) else None)) else None))"
| "checkTermsInSUKLabel (SUIdKLabel n) acc beta database subG =
   (case updateMap n [KLabel] acc subG of None \<Rightarrow> None
      | Some acc' \<Rightarrow> Some (acc', beta, SUIdKLabel n))"
| "checkTermsInSUKItem (SUKItem l r ty) maxTy acc beta database subG = 
   (if subsortList maxTy [K] subG \<and> subsortList ty [K] subG then
      (case getSUKLabelMeaning l of None \<Rightarrow> 
         (case checkTermsInSUKLabel l acc beta database subG of None \<Rightarrow> None
             | Some (acc', beta', l') \<Rightarrow>
           (case checkTermsInNoneSUKList r acc' beta' database subG of None \<Rightarrow> None
             | Some (acca, betaa, r') \<Rightarrow>
        (case meet ty maxTy subG of [] \<Rightarrow> None
            | (tya#tyl) \<Rightarrow> (case getIdInSUKLabel l' of None \<Rightarrow> 
                 Some (acca,betaa, SUKItem l' r' (tya#tyl))
          | Some newId \<Rightarrow>
          (case updateBeta newId (tya#tyl) acca subG of None \<Rightarrow> None
          | Some betab \<Rightarrow> Some (acca,betab, SUKItem l' r' (tya#tyl)))))))
         | Some s \<Rightarrow> (case getSort s database of None \<Rightarrow> None
           | Some theTy \<Rightarrow>
        (case getArgSort s database of None \<Rightarrow> None | Some tyl \<Rightarrow>
         (case checkTermsInSUKList r tyl acc beta database subG of None \<Rightarrow> None
          | Some (acc', beta', r') \<Rightarrow>
      (if isFunctionItem s database then
       (case meet theTy (meet ty maxTy subG) subG of [] \<Rightarrow> None
          | tya \<Rightarrow> Some (acc',beta', SUKItem l r' tya))
       else if subsortList theTy ty subG \<and> subsortList theTy maxTy subG then
            Some (acc',beta', SUKItem l r' theTy) else None))))) else None)"
| "checkTermsInSUKItem (SUIdKItem a b) maxTy acc beta database subG =
    (case meet b maxTy subG of [] \<Rightarrow> None
        | ty' \<Rightarrow> (case updateMap a ty' acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> Some (acc',beta, SUIdKItem a ty')))"
| "checkTermsInSUKItem (SUHOLE a) maxTy acc beta database subG =
    (case meet a maxTy subG of [] \<Rightarrow> None
      | ty' \<Rightarrow> Some (acc,beta,  SUHOLE ty'))"
| "checkTermsInNoneSUKList [] acc beta database subG = Some (acc, beta, [])"
| "checkTermsInNoneSUKList (x#l) acc beta database subG = (case x of IdKl a
      \<Rightarrow> (case updateMap a [KList] acc subG of None \<Rightarrow> None
           | Some acc' \<Rightarrow> (case checkTermsInNoneSUKList l acc' beta database subG of None \<Rightarrow> None
         | Some (acca, betaa, l') \<Rightarrow> Some (acca, betaa, (IdKl a)#l')))
    | ItemKl a \<Rightarrow> (case checkTermsInSUBigKWithLabel a None acc beta database subG of None \<Rightarrow> None
      | Some (acc', beta', a') \<Rightarrow> (case checkTermsInNoneSUKList l acc beta database subG
          of None \<Rightarrow> None | Some (acca, betaa, l') \<Rightarrow> Some (acca, betaa, (ItemKl a')#l'))))"
| "checkTermsInSUKListAux [] tyl acc beta database subG = Some (acc,beta, [], [])"
| "checkTermsInSUKListAux (b#l) tyl acc beta database subG =
     (case b of IdKl x \<Rightarrow>
      (case updateMap x [KList] acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> Some (acc',beta, [] , b#l))
    | ItemKl x \<Rightarrow> (case tyl of [] \<Rightarrow> None
         | (ty#tyl') \<Rightarrow>
      (case checkTermsInSUBigKWithLabel x (Some ty) acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', x') \<Rightarrow>
        (case checkTermsInSUKListAux l tyl' acc' beta' database subG of None \<Rightarrow> None
          | Some (acca, betaa, l', la) \<Rightarrow> Some (acca, betaa, ((ItemKl x')#l', la))))))"
| "checkTermsInSUKList l tyl acc beta database subG =
     (if numberOfItemsInKList l > length tyl then None
         else (if hasIdInKList l then
       (case checkTermsInSUKListAux l tyl acc beta database subG of None \<Rightarrow> None
           | Some (acc', beta', la, lb) \<Rightarrow> 
         (case checkTermsInSUKListAux (rev lb) (rev tyl) acc' beta' database subG of None \<Rightarrow> None
             | Some (acca, betaa, la', lb') \<Rightarrow>
      (if lb' = [] then Some (acca, betaa, la@(rev la'))
         else (case checkTermsInNoneSUKList (rev lb') acca betaa database subG of None \<Rightarrow> None
             | Some (accb, betab, lbb) \<Rightarrow> Some (accb, betab, la@lbb@(rev la'))))))
       else if numberOfItemsInKList l = length tyl
            then (case checkTermsInSUKListAux l tyl acc beta database subG
         of Some (acca,betaa, la, []) 
                 \<Rightarrow> Some (acca,betaa, la) | _ \<Rightarrow> None) else None))"
| "checkTermsInSUBigKWithLabel (SUBigBag a) ty acc beta database subG =
     (case checkTermsInSUBigKWithBag a ty acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigBag a'))"
| "checkTermsInSUBigKWithLabel (SUBigLabel a) ty acc beta database subG = (case ty of None \<Rightarrow> 
   (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigLabel a'))
    | Some ty' \<Rightarrow> if ty' = [KLabel] then
        (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
         | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBigLabel a')) else None)"
| "checkTermsInSUBigKWithBag (SUK a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUK a [K] acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUK a'))
              | Some ty' \<Rightarrow> (if subsortList ty' [K] subG then 
          (case checkTermsInSUK a [K] acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUK a')) else None))"
| "checkTermsInSUBigKWithBag (SUList a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUList a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUList a'))
              | Some ty' \<Rightarrow> (if ty' = [List] then 
          (case checkTermsInSUList a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUList a')) else None))"
| "checkTermsInSUBigKWithBag (SUSet a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUSet a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUSet a'))
              | Some ty' \<Rightarrow> (if ty' = [Set] then 
          (case checkTermsInSUSet a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUSet a')) else None))"
| "checkTermsInSUBigKWithBag (SUMap a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUMap a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUMap a'))
              | Some ty' \<Rightarrow> (if ty' = [Map] then 
          (case checkTermsInSUMap a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUMap a')) else None))"
| "checkTermsInSUBigKWithBag (SUBag a) ty acc beta database subG = (case ty of None
    \<Rightarrow> (case checkTermsInSUBag a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBag a'))
              | Some ty' \<Rightarrow> (if ty' = [Bag] then 
          (case checkTermsInSUBag a acc beta database subG of None \<Rightarrow> None
                   | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', SUBag a')) else None))"
| "checkTermsInSUK l ty acc beta database subG = (if ty = [K] then 
       (case l of [] \<Rightarrow> Some (acc,beta,[])
          | ((ItemFactor x)#xl) \<Rightarrow>
              (case checkTermsInSUKItem x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta',x') \<Rightarrow>
        (case checkTermsInSUK xl ty acc' beta' database subG of None \<Rightarrow> None
           | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (ItemFactor x')#xl')))
         | ((IdFactor x)#xl) \<Rightarrow>
         (case updateMap x [K] acc subG of None \<Rightarrow> None
          | Some acc' \<Rightarrow> (case checkTermsInSUK xl ty acc' beta database subG of
   None \<Rightarrow> None | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (IdFactor x)#xl')))
         | ((SUKKItem a b ty')#xl) \<Rightarrow>
         (if subsortList ty' [K] subG then
            (case getSUKLabelMeaning a of None \<Rightarrow>
               (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
                  | Some (acc',beta', a') \<Rightarrow>
                (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
                   | Some (acca,betaa, b') \<Rightarrow>
                  (case checkTermsInSUK xl ty acca betaa database subG of None \<Rightarrow> None
                     | Some (accb,betab, xl') \<Rightarrow> Some (accb,betab,(SUKKItem a' b' ty')#xl'))))
             | Some s \<Rightarrow> if isFunctionItem s database then
         (case (getSort s database, getArgSort s database) of (Some tya, Some tyl)
      \<Rightarrow> (case meet ty' tya subG of [] \<Rightarrow> None
             |  tyb \<Rightarrow>
               (case checkTermsInSUKList b tyl acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', b') \<Rightarrow>
               (case checkTermsInSUK xl ty acc' beta' database subG of None \<Rightarrow> None
                  | Some (acca,betaa, xl') \<Rightarrow> Some (acca,betaa, (SUKKItem a b' tyb)#xl'))))
              | _ \<Rightarrow> None) else None) else None))
           else if subsortList ty [KItem] subG then
          (case l of [u] \<Rightarrow> (case u of (IdFactor a) \<Rightarrow>
            (case updateMap a ty acc subG of None \<Rightarrow> None
               | Some acc' \<Rightarrow> Some (acc',beta, [ItemFactor (SUIdKItem a ty)]))
             | ItemFactor a \<Rightarrow> (case checkTermsInSUKItem a ty acc beta database subG
              of None \<Rightarrow> None
               | Some (acc',beta', a') \<Rightarrow> Some (acc',beta', [ItemFactor a']))
             | SUKKItem a b ty' \<Rightarrow> if subsortList ty' [K] subG then
                 (case getSUKLabelMeaning a of None \<Rightarrow>
                (case checkTermsInSUKLabel a acc beta database subG of None \<Rightarrow> None
                  | Some (acc',beta', a') \<Rightarrow>
                  (case checkTermsInNoneSUKList b acc' beta' database subG of None \<Rightarrow> None
                    | Some (acca,betaa, b') \<Rightarrow>
                (case meet ty ty' subG of [] \<Rightarrow> None | tya \<Rightarrow>
                  Some (acca,betaa,[SUKKItem a' b' tya]))))
                  | Some s \<Rightarrow> if isFunctionItem s database
                 then (case (getSort s database, getArgSort s database)
                     of (Some theTy, Some tyl) \<Rightarrow>
       (case checkTermsInSUKList b tyl acc beta database subG of None \<Rightarrow> None
           | Some (acc',beta', b') \<Rightarrow>
    (case meet ty (meet ty' theTy subG) subG of [] \<Rightarrow> None
         | tya \<Rightarrow> Some (acc', beta', [SUKKItem a b' tya])))) else None)
           else None)) else None)"
| "checkTermsInSUList [] acc beta database subG = Some (acc,beta,[])"
| "checkTermsInSUList (b#l) acc beta database subG = (case b of ItemL x \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
         (case checkTermsInSUList l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemL x')#l')))
         | IdL x \<Rightarrow> (case updateMap x [List] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUList l acc' beta database subG of
            None \<Rightarrow> None | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (IdL x)#l')))
        | SUListKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca, betaa, y') \<Rightarrow>
               (case checkTermsInSUList l acca betaa database subG of None \<Rightarrow> None
            | Some (accb,betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None \<Rightarrow> 
                   Some (accb,betab,(SUListKItem x' y')#l')
          | Some xx \<Rightarrow> (case updateMap xx [List] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb,betac, (SUListKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database
            then (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if ty = [List] then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc',beta', y') \<Rightarrow>
               (case checkTermsInSUList l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUListKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUSet [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUSet (b#l) acc beta database subG = (case b of ItemS x \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
         (case checkTermsInSUSet l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemS x')#l')))
         | IdS x \<Rightarrow> (case updateMap x [Set] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUSet l acc' beta database subG of None \<Rightarrow> None
            | Some (acca, betaa, l') \<Rightarrow> Some (acca,betaa, (IdS x)#l')))
        | SUSetKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca,betaa, y') \<Rightarrow>
               (case checkTermsInSUSet l acca betaa database subG of None \<Rightarrow> None
            | Some (accb, betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None 
               \<Rightarrow> Some (accb,betab,(SUSetKItem x' y')#l') | Some xx \<Rightarrow>
          (case updateMap xx [Set] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb,betac,(SUSetKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database then
            (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Set] subG then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc',beta', y') \<Rightarrow>
               (case checkTermsInSUSet l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUSetKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUMap [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUMap (b#l) acc beta database subG = (case b of ItemM x y \<Rightarrow>
             (case checkTermsInSUK x [K] acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', x') \<Rightarrow>
               (case checkTermsInSUK y [K] acc' beta' database subG of None \<Rightarrow> None
                   | Some (acca,betaa, y') \<Rightarrow>
         (case checkTermsInSUMap l acca betaa database subG of None \<Rightarrow> None
            | Some (accb,betab, l') \<Rightarrow> Some (accb, betab, (ItemM x' y')#l'))))
         | IdM x \<Rightarrow> (case updateMap x [Map] acc subG of None \<Rightarrow> None
            | Some acc' \<Rightarrow> (case checkTermsInSUMap l acc' beta database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca, betaa, (IdM x)#l')))
        | SUMapKItem x y \<Rightarrow> (case getSUKLabelMeaning x of None \<Rightarrow> 
           (case checkTermsInSUKLabel x acc beta database subG of None \<Rightarrow> None
             | Some (acc',beta', x') \<Rightarrow>
              (case checkTermsInNoneSUKList y acc' beta' database subG of None \<Rightarrow> None
                 | Some (acca,betaa, y') \<Rightarrow>
               (case checkTermsInSUMap l acca betaa database subG of None \<Rightarrow> None
            | Some (accb, betab, l') \<Rightarrow> (case getIdInSUKLabel x' of None \<Rightarrow>
                   Some (accb, betab, (SUMapKItem x' y')#l')
            | Some xx \<Rightarrow> (case updateMap xx [Map] betab subG of None \<Rightarrow> None
            | Some betac \<Rightarrow> Some (accb, betac, (SUMapKItem x' y')#l'))))))
           | Some s \<Rightarrow> if isFunctionItem s database then
          (case (getSort s database, getArgSort s database) of
             (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Map] subG then 
                 (case checkTermsInSUKList y tyl acc beta database subG of None \<Rightarrow> None
                 | Some (acc', beta', y') \<Rightarrow>
               (case checkTermsInSUMap l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (SUMapKItem x y')#l')))
              else None | _ \<Rightarrow> None) else None))"
| "checkTermsInSUBag [] acc beta database subG = Some (acc,beta, [])"
| "checkTermsInSUBag (b#l) acc beta database subG = (case b of ItemB x y z \<Rightarrow>
             (case checkTermsInSUBigKWithBag z None acc beta database subG of None \<Rightarrow> None
                | Some (acc',beta', z') \<Rightarrow>
         (case checkTermsInSUBag l acc' beta' database subG of None \<Rightarrow> None
            | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (ItemB x y z')#l')))
         | IdB x \<Rightarrow> (case updateMap x [Bag] acc subG of None \<Rightarrow> None
   | Some acc' \<Rightarrow> (case checkTermsInSUBag l acc' beta database subG of None \<Rightarrow> None
   | Some (acca,betaa, l') \<Rightarrow> Some (acca,betaa, (IdB x)#l'))))"
by pat_completeness auto

termination sorry
    
primrec checkTermsInSubsFactor where
"checkTermsInSubsFactor (KLabelSubs a) beta database subG =
    (case checkTermsInSUKLabel a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KLabelSubs a'))"
| "checkTermsInSubsFactor (KItemSubs a) beta database subG =
      (case checkTermsInSUKItem a [KItem] [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KItemSubs a'))"
| "checkTermsInSubsFactor (KListSubs a) beta database subG =
      (case checkTermsInNoneSUKList a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KListSubs a'))"
| "checkTermsInSubsFactor (KSubs a) beta database subG =
      (case checkTermsInSUK a [K] [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', KSubs a'))"
| "checkTermsInSubsFactor (ListSubs a) beta database subG =
      (case checkTermsInSUList a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', ListSubs a'))"
| "checkTermsInSubsFactor (SetSubs a) beta database subG =
      (case checkTermsInSUSet a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', SetSubs a'))" 
| "checkTermsInSubsFactor (MapSubs a) beta database subG =
      (case checkTermsInSUMap a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', MapSubs a'))" 
| "checkTermsInSubsFactor (BagSubs a) beta database subG =
      (case checkTermsInSUBag a [] beta database subG of None \<Rightarrow> None
       | Some (acc,beta', a') \<Rightarrow> Some (acc,beta', BagSubs a'))"

primrec replaceVarSortInSUKLabel
    and replaceVarSortInSUKItem
    and replaceVarSortInSUKListElem
    and replaceVarSortInSUKList
    and replaceVarSortInSUKElem
    and replaceVarSortInSUK
    and replaceVarSortInSUListElem
    and replaceVarSortInSUList
    and replaceVarSortInSUSetElem
    and replaceVarSortInSUSet
    and replaceVarSortInSUMapElem
    and replaceVarSortInSUMap
    and replaceVarSortInSUBigKWithBag
    and replaceVarSortInSUBigKWithLabel
    and replaceVarSortInSUBagElem
    and replaceVarSortInSUBag where 
  "replaceVarSortInSUKLabel (SUKLabel a) acc beta subG = Some (SUKLabel a)"
| "replaceVarSortInSUKLabel (SUKLabelFun a b) acc beta subG =
      (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
         | Some a' \<Rightarrow> 
             (case replaceVarSortInSUKList b acc beta subG of None \<Rightarrow> None
         | Some b' \<Rightarrow> Some (SUKLabelFun a' b')))"
| "replaceVarSortInSUKLabel (SUIdKLabel n) acc beta subG = Some (SUIdKLabel n)"
| "replaceVarSortInSUKItem (SUKItem l r ty) acc beta subG =
    (case getIdInSUKLabel l of Some lx \<Rightarrow>
     (case getValueTerm lx beta of None \<Rightarrow> None
        | Some ty' \<Rightarrow>
       (case replaceVarSortInSUKList r acc beta subG of None \<Rightarrow> None
             | Some r' \<Rightarrow> Some (SUKItem l r' ty')))
         | None \<Rightarrow> (case replaceVarSortInSUKLabel l acc beta subG of None \<Rightarrow> None
    | Some l' \<Rightarrow>  (case replaceVarSortInSUKList r acc beta subG of None \<Rightarrow> None
             | Some r' \<Rightarrow> Some (SUKItem l' r' ty))))"
| "replaceVarSortInSUKItem (SUIdKItem a b) acc beta subG =
        (case getValueTerm a acc of None \<Rightarrow> None
             | Some b' \<Rightarrow> Some (SUIdKItem a b'))"
| "replaceVarSortInSUKItem (SUHOLE a) acc beta subG = Some (SUHOLE a)"
| "replaceVarSortInSUKListElem (IdKl x) acc beta subG = Some (IdKl x)"
| "replaceVarSortInSUKListElem (ItemKl x) acc beta subG = 
    (case replaceVarSortInSUBigKWithLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemKl x'))"
| "replaceVarSortInSUKList [] acc beta subG = Some []"
| "replaceVarSortInSUKList (b#l) acc beta subG = 
    (case replaceVarSortInSUKListElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUKList l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUBigKWithLabel (SUBigBag a) acc beta subG =
      (case replaceVarSortInSUBigKWithBag a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "replaceVarSortInSUBigKWithLabel (SUBigLabel a) acc beta subG =
      (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "replaceVarSortInSUBigKWithBag (SUK a) acc beta subG =
      (case replaceVarSortInSUK a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUK a'))"
| "replaceVarSortInSUBigKWithBag (SUList a) acc beta subG =
      (case replaceVarSortInSUList a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUList a'))"
| "replaceVarSortInSUBigKWithBag (SUSet a) acc beta subG =
      (case replaceVarSortInSUSet a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUSet a'))"
| "replaceVarSortInSUBigKWithBag (SUMap a) acc beta subG =
      (case replaceVarSortInSUMap a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUMap a'))"
| "replaceVarSortInSUBigKWithBag (SUBag a) acc beta subG =
      (case replaceVarSortInSUBag a acc beta subG of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SUBag a'))"
| "replaceVarSortInSUKElem (IdFactor x) acc beta subG =
   (case getValueTerm x acc of None \<Rightarrow> None
       | Some ty \<Rightarrow> if ty = [K] then Some (IdFactor x)
            else if subsortList ty [KItem] subG then Some (ItemFactor (SUIdKItem x ty)) else None)"
| "replaceVarSortInSUKElem (ItemFactor x) acc beta subG = 
    (case replaceVarSortInSUKItem x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemFactor x'))"
| "replaceVarSortInSUKElem (SUKKItem x y ty) acc beta subG = 
    (case getIdInSUKLabel x of Some xx \<Rightarrow>
      (case getValueTerm xx beta of None \<Rightarrow> None
       | Some ty' \<Rightarrow> 
    (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUKKItem x y' ty'))))
        | _ \<Rightarrow> (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow>
    (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow>  Some ((SUKKItem x' y' ty)))))"
| "replaceVarSortInSUK [] acc beta subG = Some []"
| "replaceVarSortInSUK (b#l) acc beta subG =
    (case replaceVarSortInSUKElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUK l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUListElem (IdL x) acc beta subG = Some (IdL x)"
| "replaceVarSortInSUListElem (ItemL x) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemL x'))"
| "replaceVarSortInSUListElem (SUListKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUListKItem x' y'))))"
| "replaceVarSortInSUList [] acc beta subG = Some []"
| "replaceVarSortInSUList (b#l) acc beta subG =
    (case replaceVarSortInSUListElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUList l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUSetElem (IdS x) acc beta subG = Some (IdS x)"
| "replaceVarSortInSUSetElem (ItemS x) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> Some (ItemS x'))"
| "replaceVarSortInSUSetElem (SUSetKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUSetKItem x' y'))))"
| "replaceVarSortInSUSet [] acc beta subG = Some []"
| "replaceVarSortInSUSet (b#l) acc beta subG =
    (case replaceVarSortInSUSetElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUSet l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUMapElem (IdM x) acc beta subG = Some (IdM x)"
| "replaceVarSortInSUMapElem (ItemM x y) acc beta subG = 
    (case replaceVarSortInSUK x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUK y acc beta subG of None
          \<Rightarrow> None | Some y' \<Rightarrow> Some (ItemM x' y')))"
| "replaceVarSortInSUMapElem (SUMapKItem x y) acc beta subG = 
   (case replaceVarSortInSUKLabel x acc beta subG of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case replaceVarSortInSUKList y acc beta subG of None \<Rightarrow> None
         | Some y' \<Rightarrow> Some ((SUMapKItem x' y'))))"
| "replaceVarSortInSUMap [] acc beta subG = Some []"
| "replaceVarSortInSUMap (b#l) acc beta subG =
    (case replaceVarSortInSUMapElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUMap l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"
| "replaceVarSortInSUBagElem (IdB x) acc beta subG = Some (IdB x)"
| "replaceVarSortInSUBagElem (ItemB x y z) acc beta subG = 
    (case replaceVarSortInSUBigKWithBag z acc beta subG of None \<Rightarrow> None
       | Some z' \<Rightarrow> Some (ItemB x y z'))"
| "replaceVarSortInSUBag [] acc beta subG = Some []"
| "replaceVarSortInSUBag (b#l) acc beta subG =
      (case replaceVarSortInSUBagElem b acc beta subG of None \<Rightarrow> None
      | Some b' \<Rightarrow> (case replaceVarSortInSUBag l acc beta subG of None \<Rightarrow> None
     | Some l' \<Rightarrow> Some (b'#l')))"

primrec replaceVarSortInSubsFactor where
"replaceVarSortInSubsFactor (KLabelSubs a) acc beta subG =
       (case replaceVarSortInSUKLabel a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "replaceVarSortInSubsFactor (KItemSubs a) acc beta subG =
       (case replaceVarSortInSUKItem a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KItemSubs a'))"
| "replaceVarSortInSubsFactor (KListSubs a) acc beta subG =
       (case replaceVarSortInSUKList a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KListSubs a'))"
| "replaceVarSortInSubsFactor (KSubs a) acc beta subG =
       (case replaceVarSortInSUK a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (KSubs a'))"
| "replaceVarSortInSubsFactor (ListSubs a) acc beta subG =
       (case replaceVarSortInSUList a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (ListSubs a'))"
| "replaceVarSortInSubsFactor (SetSubs a) acc beta subG =
       (case replaceVarSortInSUSet a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (SetSubs a'))"
| "replaceVarSortInSubsFactor (MapSubs a) acc beta subG =
       (case replaceVarSortInSUMap a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (MapSubs a'))"
| "replaceVarSortInSubsFactor (BagSubs a) acc beta subG =
       (case replaceVarSortInSUBag a acc beta subG of None \<Rightarrow> None
       | Some a' \<Rightarrow> Some (BagSubs a'))"

primrec hasIdInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool" where
"hasIdInSUBag [] = False"
| "hasIdInSUBag (b#l) = (case b of IdB x \<Rightarrow> True
                | _ \<Rightarrow> hasIdInSUBag l)"

primrec onlyIdInSUBag :: "('upVar, 'var, 'metaVar) suB list \<Rightarrow> bool" where
"onlyIdInSUBag [] = True"
| "onlyIdInSUBag (b#l) = (case b of IdB x \<Rightarrow> onlyIdInSUBag l
                | _ \<Rightarrow> False)"

primrec searchBagWithName :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
            \<Rightarrow> (('upVar, 'var, 'metaVar) suB list
                                * ('upVar, 'var, 'metaVar) suB list)" where
"searchBagWithName x [] = ([], [])"
| "searchBagWithName a (b#l) = (case b of IdB x \<Rightarrow>
      (case searchBagWithName a l of  (u,v) \<Rightarrow> (u, b#l))
      | ItemB u v w \<Rightarrow> (case searchBagWithName a l of (q,t)
      \<Rightarrow> (if a = u then ((ItemB u v w)#q,t)
                              else (q, (ItemB u v w)#t))))"

fun checkTermsWithConfi
 and checkTermsWithConfiList
 and checkTermsWithConfiAux where
"checkTermsWithConfi [] A subG = (if onlyIdInSUBag A then True else False)"
| "checkTermsWithConfi (b#l) A subG = (case b of IdB x \<Rightarrow> False
        | ItemB x y z \<Rightarrow> (case searchBagWithName x A of (al, ar) \<Rightarrow>
        (case al of [] \<Rightarrow>
           (if hasIdInSUBag A \<or> Multiplicity Question \<in> set y 
                then checkTermsWithConfi l A subG else False)
           | [a] \<Rightarrow> checkTermsWithConfiList z al subG \<and> checkTermsWithConfi l ar subG
           | al' \<Rightarrow> if Multiplicity Star \<in> set y then
          checkTermsWithConfiList z al subG \<and> checkTermsWithConfi l ar subG
           else False)))"
| "checkTermsWithConfiList P [] subG = True"
| "checkTermsWithConfiList P (b#l) subG = (case b of IdB x \<Rightarrow> False
         | ItemB x y z \<Rightarrow>
            (checkTermsWithConfiAux P z subG \<and> checkTermsWithConfiList P l subG))"
| "checkTermsWithConfiAux (SUBag x) y subG = (case y of SUBag y'
      \<Rightarrow> checkTermsWithConfi x y' subG | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUK x) y subG = (case y of SUK y' \<Rightarrow>
      (case x of [a] \<Rightarrow> (case a of ItemFactor u \<Rightarrow> 
       (case y' of [ItemFactor u'] \<Rightarrow>
         if subsortList (getType u') (getType u) subG then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if subsortList ty (getType u) subG then True else False
            | _ \<Rightarrow> if getType u = [K] then True else False)
          | SUKKItem xl xkl xty \<Rightarrow> (case y' of [ItemFactor u'] \<Rightarrow>
         if subsortList (getType u') xty subG then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if subsortList ty xty subG then True else False
            | _ \<Rightarrow> if xty = [K] then True else False)
           | _ \<Rightarrow> (case y' of [ItemFactor u'] \<Rightarrow>
         if getType u' = [K] then True else False
            | [SUKKItem l kl ty] \<Rightarrow> 
           if ty = [K] then True else False
            | _ \<Rightarrow> True)) | _ \<Rightarrow> True) | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUList x) y subG = (case y of SUList y' \<Rightarrow> True
           | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUSet x) y subG = (case y of SUSet y' \<Rightarrow> True
           | _ \<Rightarrow> False)"
| "checkTermsWithConfiAux (SUMap x) y subG = (case y of SUMap y' \<Rightarrow> True
           | _ \<Rightarrow> False)"

fun wellFormRules :: "('upVar, 'var, 'metaVar) rulePat list \<Rightarrow> bool" where
"wellFormRules [] = True"
| "wellFormRules ((FunPat s rl a)#l) = ((foldl (\<lambda> b (x,y,z) . b \<and>
       (set (getAllMetaVarsInSubsFactor y @ getAllMetaVarsInSUKItem z)
           \<subseteq> set (getAllMetaVarsInPat x))) True
                (case a of None \<Rightarrow> rl | Some a' \<Rightarrow> (a'#rl)))
             \<and> wellFormRules l)"
| "wellFormRules ((MacroPat s a b)#l) =
  ((set (getAllMetaVarsInSUK b) \<subseteq> set (getAllMetaVarsInIRKList a))
          \<and> wellFormRules l)"
| "wellFormRules ((AnywherePat ss a b c)#l) =
         ((set (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c)
                    \<subseteq> set (getAllMetaVarsInIRKList a)) \<and> wellFormRules l)"
| "wellFormRules ((KRulePat a b c tb)#l) =
         ((set (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c)
                \<subseteq> set (getAllMetaVarsInIRK a)) \<and> wellFormRules l)"
| "wellFormRules ((BagRulePat a b c tb)#l) =
      ((set (getAllMetaVarsInSUBag b @ getAllMetaVarsInSUKItem c)
             \<subseteq> set (getAllMetaVarsInIRBag a)) \<and> wellFormRules l)"

(* type adjustment each rule *)
primrec inferTypesInFunPat where
"inferTypesInFunPat s [] database subG = Some []"
| "inferTypesInFunPat s (b#l) database subG = (case b of (x,y,z) \<Rightarrow>
    (case x of KLabelFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KLabelSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if ty = [KLabel] then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUKLabel sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUKLabel sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUKLabel sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KLabelFunPat s klb', KLabelSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | KFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [K] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUK sl ty acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUK sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KFunPat s klb', KSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | KItemFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (KItemSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [KItem] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUKItem sl ty acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUKItem sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUKItem sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((KItemFunPat s klb', KItemSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | ListFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (ListSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [List] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUList sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUList sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUList sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((ListFunPat s klb', ListSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | SetFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (SetSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Set] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUSet sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUSet sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUSet sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((SetFunPat s klb', SetSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
    | MapFunPat ss kl \<Rightarrow> if ss = s then
     (case y of (MapSubs sl) \<Rightarrow> (case (getSort s database, getArgSort s database)
       of (Some ty, Some tyl) \<Rightarrow> if subsortList ty [Map] subG then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
                      (constructSortMap (getDomainInIRKList kl)) database subG)
      of None \<Rightarrow> None | Some (acckl, betakl, kl') \<Rightarrow>
     (case checkTermsInSUMap sl acckl betakl database subG of None \<Rightarrow> None
        | Some (accsl, betasl, sl') \<Rightarrow>
      (case checkTermsInSUKItem z [KItem] accsl betasl database subG of None \<Rightarrow> None
       | Some (accz, betaz, z') \<Rightarrow> if hasNoTop accz \<and> hasNoTop betaz then
    (case (replaceVarSortInSUKList kl' accz betaz subG, replaceVarSortInSUMap sl' accz betaz subG,
      replaceVarSortInSUKItem z' accz betaz subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUMap sla subG,
         regularizeInSUKItem za subG) of (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInFunPat s l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((MapFunPat s klb', MapSubs slb, zb)#l')))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))) else None | _ \<Rightarrow> None)
            | _ \<Rightarrow> None) else None
     | _ \<Rightarrow> None))"

fun inferTypesInRules where
"inferTypesInRules [] Theory database subG = Some []"
| "inferTypesInRules ((FunPat s kl ow)#l) Theory database subG = (case ow of None \<Rightarrow>
     (case inferTypesInFunPat s kl database subG of None \<Rightarrow> None
        | Some kl' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((FunPat s kl' None)#l')))
  | Some (x,y,z) \<Rightarrow>
       (case inferTypesInFunPat s [(x,y,z)] database subG of Some [(x',y',z')] \<Rightarrow>
        (case inferTypesInFunPat s kl database subG of None \<Rightarrow> None
        | Some kl' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((FunPat s kl' (Some (x',y',z')))#l'))) | _ \<Rightarrow> None))"
| "inferTypesInRules ((MacroPat s kl sl)#l) Theory database subG =
    (case (getSort s database, getArgSort s database) of (Some ty, Some tyl) \<Rightarrow>
      if subsortList ty [KItem] subG \<and> \<not> isFunctionItem s database then
         (case (checkTermsInSUKList (irToSUInKList kl) tyl []
             (constructSortMap (getDomainInIRKList kl)) database subG) of None \<Rightarrow> None
      | Some (acckl,betakl,kl') \<Rightarrow> (case 
      checkTermsInSUK sl [K] acckl betakl database subG of None \<Rightarrow> None
       | Some (accsl,betasl, sl') \<Rightarrow> if hasNoTop accsl \<and> hasNoTop betasl then
      (case (replaceVarSortInSUKList kl' accsl betasl subG, replaceVarSortInSUK sl' accsl betasl subG)
         of (Some kla, Some sla) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG) of (Some klb, Some slb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((MacroPat s klb' slb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None))
      else None | _ \<Rightarrow> None)"
| "inferTypesInRules ((AnywherePat ss kl r c)#l) Theory database subG =
   (case (getSort ss database, getArgSort ss database) of (Some ty, Some tyl) \<Rightarrow>
      if subsortList ty [KItem] subG \<and> \<not> isFunctionItem ss database then
   (case (checkTermsInSUKList (irToSUInKList kl) tyl []
              (constructSortMap (getDomainInIRKList kl)) database subG) of None \<Rightarrow> None
     | Some (acckl, betakl, kl') \<Rightarrow> 
     (case (checkTermsInSUK r [K] acckl betakl database subG) of None \<Rightarrow> None
      | Some (accr, betar, r') \<Rightarrow>
     (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
       | Some (accc, betac, c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
       (case (replaceVarSortInSUKList kl' accc betac subG, replaceVarSortInSUK r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUKList kla subG, regularizeInSUK sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInKList klb database of None \<Rightarrow> None
             | Some klb' \<Rightarrow>
          (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
      | Some l' \<Rightarrow> Some ((AnywherePat ss klb' slb zb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))
     else None | _ \<Rightarrow> None)"
| "inferTypesInRules ((KRulePat kl r c tb)#l) Theory database subG =
   (case (checkTermsInSUK (irToSUInK kl) [K] []
                    (constructSortMap (getDomainInIRK kl)) database subG) of None \<Rightarrow> None
       | Some (acckl, betakl, kl') \<Rightarrow>
        (case checkTermsInSUK r [K] acckl betakl database subG of None \<Rightarrow> None
         | Some (accr, betar, r') \<Rightarrow>
        (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
         | Some (accc, betac, c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
        (case (replaceVarSortInSUK kl' accc betac subG, replaceVarSortInSUK r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUK kla subG, regularizeInSUK sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInK klb database of None \<Rightarrow> None
             | Some (NormalPat (KMatching klb')) \<Rightarrow>
          (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((KRulePat klb' slb zb tb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))"
| "inferTypesInRules ((BagRulePat kl r c tb)#l) Theory database subG =
   (case getConfiguration Theory of [confi] \<Rightarrow>
    (case toSUInBag confi of None \<Rightarrow> None | Some confi' \<Rightarrow>
      if (checkTermsWithConfi confi' (irToSUInBag kl) subG \<and> checkTermsWithConfi confi' r subG)
           then (case (checkTermsInSUBag (irToSUInBag kl) []
         (constructSortMap (getDomainInIRBag kl)) database subG) of None \<Rightarrow> None
        | Some (acckl, betakl,kl') \<Rightarrow>
         (case checkTermsInSUBag r acckl betakl database subG of None \<Rightarrow> None
          | Some (accr,betar,r') \<Rightarrow>
         (case checkTermsInSUKItem c [KItem] accr betar database subG of None \<Rightarrow> None
         | Some (accc,betac,c') \<Rightarrow> if hasNoTop accc \<and> hasNoTop betac then
      (case (replaceVarSortInSUBag kl' accc betac subG, replaceVarSortInSUBag r' accc betac subG,
      replaceVarSortInSUKItem c' accc betac subG) of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUBag kla subG, regularizeInSUBag sla subG, regularizeInSUKItem za subG) of
          (Some klb, Some slb, Some zb) \<Rightarrow>
          (case suToIRInBag klb database of None \<Rightarrow> None
       | Some klb' \<Rightarrow> (case inferTypesInRules l Theory database subG of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((BagRulePat klb' slb zb tb)#l'))) | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)))
         else None) | _ \<Rightarrow> None)"


(* given a bag term in K core, compile it to a K IR version that is compared with the
    configuration of a language spec and fulfilled missing cells *)
primrec removeDotInFeatureList :: "feature list \<Rightarrow> feature list" where
"removeDotInFeatureList [] = []"
| "removeDotInFeatureList (b#l) = (case b of DotDotDot \<Rightarrow> removeDotInFeatureList l
          | _ \<Rightarrow> b#(removeDotInFeatureList l))"

function completeBagHasDotInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                            ('upVar, 'var, 'metaVar) suB list) option"
   and completeBagNoDotInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option"
   and completeSameBagsInSUBag :: "feature list \<Rightarrow>
           ('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option"
   and completeNextBagsInSUBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list * 
                    ('upVar, 'var, 'metaVar) suB list) option"
      and completeBagInSUBigKWithBag :: "feature list \<Rightarrow>
      ('upVar, 'var, 'metaVar) suBigKWithBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag
       \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag option" where
 "completeBagNoDotInSUBag [] A postp = (if postp = [] then
        (if onlyIdInSUBag A then Some A else None)
         else (if onlyIdInSUBag A \<and> hasIdInSUBag A then Some A else None))"
| "completeBagNoDotInSUBag (b#l) A postp = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
         (case searchBagWithName x A of (al, as) \<Rightarrow>
    if al = [] then completeBagNoDotInSUBag l A (postp@[b]) else
     (if Multiplicity Star \<in> set y then
          (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow>
           (case completeBagNoDotInSUBag l as postp of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (al'@l')))
      else ( if length al > 1 then None
             else  (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
    | Some al' \<Rightarrow> (case completeBagNoDotInSUBag l as postp of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some (al'@l')))))))"
| "completeSameBagsInSUBag f p [] = Some []"
| "completeSameBagsInSUBag f p (b#l) = (case b of IdB x \<Rightarrow> None
             | ItemB x y z \<Rightarrow>
       (case completeBagInSUBigKWithBag f p z of None \<Rightarrow> None
              | Some z' \<Rightarrow>
          (case completeSameBagsInSUBag f p l of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemB x (removeDotInFeatureList y) z')#l'))))"
| "completeBagHasDotInSUBag [] A postp acc = completeNextBagsInSUBag postp A acc"
| "completeBagHasDotInSUBag (b#l) A postp acc = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
      (case searchBagWithName x A of (al,as) \<Rightarrow>
     if al = [] then
            completeBagHasDotInSUBag l A (postp@[ItemB x (removeDotInFeatureList y) z]) acc
      else
       (if Multiplicity Star \<in> set y then
          (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow> completeBagHasDotInSUBag l as postp (acc@al'))
      else (if length al > 1 then None
             else  (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
              | Some al' \<Rightarrow> completeBagHasDotInSUBag l as postp (acc@al'))))))"
| "completeNextBagsInSUBag [] A acc = Some (acc, A)"
| "completeNextBagsInSUBag (b#l) A acc = (if A = [] then Some (acc@(b#l), [])
     else (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
           (case z of SUBag al \<Rightarrow>
    (case completeBagHasDotInSUBag al A [] [] of None \<Rightarrow> None
        | Some (acc', A') \<Rightarrow> 
       completeNextBagsInSUBag l A' (acc@[ItemB x (removeDotInFeatureList y) (SUBag acc')]))
            | _ \<Rightarrow>
                completeNextBagsInSUBag l A (acc@[ItemB x (removeDotInFeatureList y) z]))))"
| "completeBagInSUBigKWithBag f (SUBag a) S = (case S of (SUBag b) \<Rightarrow>
      (if DotDotDot \<in> set f then
        (case completeBagHasDotInSUBag a b [] [] of None \<Rightarrow> None
            | Some (a', still) \<Rightarrow> if still = [] then Some (SUBag a') else None)
       else (case completeBagNoDotInSUBag a b [] of None \<Rightarrow> None
            | Some a' \<Rightarrow>  Some (SUBag a')))
          | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUK a) S =
                    (case S of (SUK b) \<Rightarrow> Some (SUK b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUList a) S =
                 (case S of (SUList b) \<Rightarrow> Some (SUList b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUSet a) S =
                 (case S of (SUSet b) \<Rightarrow> Some (SUSet b) | _ \<Rightarrow> None)"
| "completeBagInSUBigKWithBag f (SUMap a) S =
                (case S of (SUMap b) \<Rightarrow> Some (SUMap b) | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun completeBagBySearchBags :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                         ('upVar, 'var, 'metaVar) suB list) option"
    and completeBagBySearchBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
      \<Rightarrow> (('upVar, 'var, 'metaVar) suB list *
                         ('upVar, 'var, 'metaVar) suB list) option" where
"completeBagBySearchBags [] P acc = Some (acc, P)"
| "completeBagBySearchBags (b#l) P acc = (case b of IdB x \<Rightarrow> None
        | ItemB x y z \<Rightarrow> (case searchBagWithName x P of (al, ar)
           \<Rightarrow> if al = [] then
            (case completeBagBySearchBigKWithBag z P acc of None \<Rightarrow> None
        | Some (acc', remain) \<Rightarrow> completeBagBySearchBags l remain acc')
   else (case completeSameBagsInSUBag y z al of None \<Rightarrow> None
            | Some al' \<Rightarrow>
       (case completeBagBySearchBigKWithBag z ar (acc@al') of None \<Rightarrow> None
      | Some (acc', remain) \<Rightarrow> completeBagBySearchBags l remain acc'))))"
| "completeBagBySearchBigKWithBag (SUBag x) P acc = completeBagBySearchBags x P acc"
| "completeBagBySearchBigKWithBag X P acc = Some (acc, P)"

primrec getListInIRBag :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list" where
"getListInIRBag (BagPat x y) = x"

primrec getVarInIRBag :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> 'metaVar metaVar option" where
"getVarInIRBag (BagPat x y) = y"

primrec mergeListToIRBag :: "('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
           \<Rightarrow> ('upVar, 'var, 'metaVar) irBag \<Rightarrow>
                  ('upVar, 'var, 'metaVar) irBag" where
"mergeListToIRBag l (BagPat x y) = BagPat (l@x) y"

primrec searchBagWithNameInIRBag
        :: "'var var \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
            \<Rightarrow> (('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
                                * ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list)" where
"searchBagWithNameInIRBag x [] = ([], [])"
| "searchBagWithNameInIRBag a (b#l) = (case b of (x,y,z) \<Rightarrow>
      (case searchBagWithNameInIRBag a l of (q,t) \<Rightarrow>
        (if a = x then ((x,y,z)#q,t) else (q, (x,y,z)#t))))"

function fillVarsBagHasDotInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
   and fillVarsBagNoDotInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
   \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
       \<Rightarrow> 'metaVar metaVar list
   \<Rightarrow> (('upVar, 'var, 'metaVar) irBag * 'metaVar metaVar list) option"
   and fillVarsSameBagsInIRBag :: "feature list \<Rightarrow>
           ('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('var var * feature list *
                 ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list \<Rightarrow> (('var var * feature list *
     ('upVar, 'var, 'metaVar) irBigKWithBag) list * 'metaVar metaVar list) option"
   and fillVarsNextBagsInIRBag :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('var var * feature list *
            ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list \<Rightarrow> (('var var * feature list *
            ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
      and fillVarsInIRBigKWithBag :: "feature list \<Rightarrow>
      ('upVar, 'var, 'metaVar) suBigKWithBag
      \<Rightarrow> ('upVar, 'var, 'metaVar) irBigKWithBag
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('upVar, 'var, 'metaVar) irBigKWithBag * 
                        'metaVar metaVar list)  option" where
 "fillVarsBagHasDotInIRBag [] A postp acc vars = (case A of (BagPat [] None)
        \<Rightarrow> (case freshVar vars of newVar \<Rightarrow>
              Some (BagPat acc (Some ( newVar)), [], ( newVar)#vars))
       | BagPat [] (Some v) \<Rightarrow> None
       | BagPat (b#l) None \<Rightarrow> (case fillVarsNextBagsInIRBag postp (b#l) vars
         of None \<Rightarrow> None
      | Some (acc', remains, vars') \<Rightarrow>
          (case freshVar vars' of newVar \<Rightarrow> Some (BagPat (acc@acc')
            (Some (newVar)), remains, (newVar)#vars')))
      | _ \<Rightarrow> None)"
| "fillVarsBagHasDotInIRBag (b#l) A postp acc vars = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
          (case searchBagWithNameInIRBag x (getListInIRBag A) of (al,as) \<Rightarrow>
               if al = [] then
            fillVarsBagHasDotInIRBag l A (postp@[ItemB x y z]) acc vars
     else (if Multiplicity Star \<in> set y then
          (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
              | Some (al', vars') \<Rightarrow>
               fillVarsBagHasDotInIRBag l (BagPat as (getVarInIRBag A)) postp (acc@al') vars')
      else (if length al > 1 then None
             else  (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
       | Some (al', vars') \<Rightarrow>
          fillVarsBagHasDotInIRBag l (BagPat as (getVarInIRBag A)) postp (acc@al') vars')))))"
| "fillVarsBagNoDotInIRBag [] A postp vars = (case A of (BagPat [] None)
   \<Rightarrow> if postp = [] then Some (BagPat [] None, vars) else None
     | (BagPat [] (Some x)) \<Rightarrow> Some (BagPat [] (Some x), vars)
      | _ \<Rightarrow> None)"
| "fillVarsBagNoDotInIRBag (b#l) A postp vars = (case b of IdB x \<Rightarrow> None
               | ItemB x y z \<Rightarrow>
         (case searchBagWithNameInIRBag x (getListInIRBag A) of (al, as)
          \<Rightarrow> if al = [] then fillVarsBagNoDotInIRBag l A (postp@[b]) vars
         else (if Multiplicity Star \<in> set y then
          (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
              | Some (al', vars') \<Rightarrow>
           (case fillVarsBagNoDotInIRBag l (BagPat as (getVarInIRBag A)) postp vars'
             of None \<Rightarrow> None
              | Some (l', varsa) \<Rightarrow> Some (mergeListToIRBag al' l', varsa)))
      else ( if length al > 1 then None
             else  (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
         | Some (al', vars') \<Rightarrow>
           (case fillVarsBagNoDotInIRBag l (BagPat as (getVarInIRBag A)) postp vars'
              of None \<Rightarrow> None
                 | Some (l', varsa) \<Rightarrow> Some (mergeListToIRBag al' l', varsa)))))))"
| "fillVarsNextBagsInIRBag [] A vars = Some ([], A, vars)"
| "fillVarsNextBagsInIRBag (b#l) A vars = (if A = [] then Some ([], [], vars)
     else (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
           (case z of SUBag al \<Rightarrow>
    (case fillVarsBagHasDotInIRBag al (BagPat A None) [] [] vars of None \<Rightarrow> None
        | Some (acc', A', vars') \<Rightarrow> 
      (case fillVarsNextBagsInIRBag l A' vars' of None \<Rightarrow> None
          | Some (acca, Aa, varsa) \<Rightarrow>
                Some ((x,removeDotInFeatureList y,IRBag acc')#acca, Aa, varsa)))
            | _ \<Rightarrow> fillVarsNextBagsInIRBag l A vars)))"
| "fillVarsSameBagsInIRBag f p [] vars = Some ([], vars)"
| "fillVarsSameBagsInIRBag f p (b#l) vars = (case b of (x,y,z) \<Rightarrow>
       (case fillVarsInIRBigKWithBag f p z vars of None \<Rightarrow> None
              | Some (z', vars') \<Rightarrow>
          (case fillVarsSameBagsInIRBag f p l vars' of None \<Rightarrow> None
              | Some (l', varsa) \<Rightarrow>
                    Some ((x,(removeDotInFeatureList y),z')#l', varsa))))"
| "fillVarsInIRBigKWithBag f (SUBag a) S vars = (case S of (IRBag b) \<Rightarrow>
      (if DotDotDot \<in> set f then
        (case fillVarsBagHasDotInIRBag a b [] [] vars of None \<Rightarrow> None
            | Some (a', still, vars')
          \<Rightarrow> if still = [] then Some (IRBag a', vars') else None)
       else (case fillVarsBagNoDotInIRBag a b [] vars of None \<Rightarrow> None
            | Some (a', vars') \<Rightarrow>  Some (IRBag a', vars')))
          | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUK a) S vars =
     (case S of (IRK b) \<Rightarrow> Some (IRK b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUList a) S vars =
      (case S of (IRList b) \<Rightarrow> Some (IRList b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUSet a) S vars =
      (case S of (IRSet b) \<Rightarrow> Some (IRSet b, vars) | _ \<Rightarrow> None)"
| "fillVarsInIRBigKWithBag f (SUMap a) S vars =
     (case S of (IRMap b) \<Rightarrow> Some (IRMap b, vars) | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun fillVarsBySearchBags :: "('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('var var * feature list *
                  ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option"
    and fillVarsBySearchBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
   \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
 \<Rightarrow> ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
       \<Rightarrow> 'metaVar metaVar list
       \<Rightarrow> (('var var * feature list *
                  ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list
                        * 'metaVar metaVar list) option" where
"fillVarsBySearchBags [] P acc vars = Some (acc, P, vars)"
| "fillVarsBySearchBags (b#l) P acc vars = (case b of IdB x \<Rightarrow> None
        | ItemB x y z \<Rightarrow> (case searchBagWithNameInIRBag x P of (al, ar)
           \<Rightarrow> if al = [] then
            (case fillVarsBySearchBigKWithBag z P acc vars of None \<Rightarrow> None
           | Some (acc', remain, varsa) \<Rightarrow> fillVarsBySearchBags l remain acc' varsa)
   else (case fillVarsSameBagsInIRBag y z al vars of None \<Rightarrow> None
            | Some (al', vars') \<Rightarrow>
       (case fillVarsBySearchBigKWithBag z ar (acc@al') vars' of None \<Rightarrow> None
           | Some (acc', remain, varsa) \<Rightarrow> fillVarsBySearchBags l remain acc' varsa))))"
| "fillVarsBySearchBigKWithBag (SUBag x) P acc vars = fillVarsBySearchBags x P acc vars"
| "fillVarsBySearchBigKWithBag X P acc vars = Some (acc, P, vars)"

definition notIdOfKLabel :: "('svar, 'metaVar) irKLabel \<Rightarrow> bool" where
"notIdOfKLabel a = (case a of (IRIdKLabel x) \<Rightarrow> False | _ \<Rightarrow> True)"

primrec mergeTwoIRBag :: "('upVar, 'var, 'metaVar) irBag
               \<Rightarrow> ('upVar, 'var, 'metaVar) irBag
              \<Rightarrow> ('upVar, 'var, 'metaVar) irBag option" where
"mergeTwoIRBag (BagPat a b) P = (case P of BagPat a' b' \<Rightarrow> 
        (case (b,b') of (None, None) \<Rightarrow> Some (BagPat (a@a') None)
             | (Some x, None) \<Rightarrow> Some (BagPat (a@a') (Some x))
             | (None, Some x) \<Rightarrow> Some (BagPat (a@a') (Some x))
             | _ \<Rightarrow> None))"

definition mergeBagTuple :: "('upVar, 'var, 'metaVar) irBag
     \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
        \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
           ('upVar, 'var, 'metaVar) suB list)
           \<Rightarrow> (('upVar, 'var, 'metaVar) irBag *
           ('upVar, 'var, 'metaVar) suB list) option" where
"mergeBagTuple a b t = (case t of (BagPat l v, y) \<Rightarrow>
       (case a of BagPat l' v' \<Rightarrow> (case (v,v') of (None, None) \<Rightarrow>
          Some (BagPat (l@l') None, y@b)
         | (Some u, None) \<Rightarrow> Some (BagPat (l@l') (Some u), y@b)
         | (None, Some u) \<Rightarrow> Some (BagPat (l@l') (Some u), y@b)
         | (Some u, Some w) \<Rightarrow> None)))"

fun getSubPattern :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
   \<Rightarrow> (feature list *
           ('upVar, 'var, 'metaVar) suBigKWithBag) option"
    and getSubPatternAux :: "'var var \<Rightarrow>
       ('upVar, 'var, 'metaVar) suBigKWithBag \<Rightarrow> (feature list *
           ('upVar, 'var, 'metaVar) suBigKWithBag) option" where
"getSubPattern x [] = None"
| "getSubPattern x (b#l) = (case b of IdB x \<Rightarrow> None
              | ItemB u v w \<Rightarrow> if u = x then Some (v,w) else
       (case getSubPatternAux x w of None \<Rightarrow> getSubPattern x l
             | Some tu \<Rightarrow> Some tu))"
| "getSubPatternAux x (SUBag y) = getSubPattern x y"
| "getSubPatternAux x y = None"

primrec ditachBag :: "('upVar, 'var, 'metaVar) bag
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option"
    and ditachBagR :: "('upVar, 'var, 'metaVar) bag rewrite
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option" where
"ditachBag UnitBag = Some ([],[],[])"
| "ditachBag (IdBag x) = None"
| "ditachBag (Xml x y z) = (if hasRewriteInBagR z then Some ([], [(Xml x y z)],[])
                          else Some ([], [], [(Xml x y z)]))"
| "ditachBag (SingleCell x y z) = (if hasRewriteInBigK z then Some ([], [(SingleCell x y z)],[])
                          else Some ([], [], [(SingleCell x y z)]))"
| "ditachBag (BagCon l r) = (case (ditachBagR l, ditachBagR r) of (Some (x,y,z), Some (u,v,w))
              \<Rightarrow> Some (x@u,y@v,z@w) | _ \<Rightarrow> None)"
| "ditachBagR (KTerm a) = ditachBag a"
| "ditachBagR (KRewrite a b) = (if (\<not> hasRewriteInBag a) \<and> (\<not> hasRewriteInBag b)
                then Some ([(a,b)],[],[]) else None)"

primrec ditachBagWithVars :: "('upVar, 'var, 'metaVar) bag
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option"
    and ditachBagRWithVars :: "('upVar, 'var, 'metaVar) bag rewrite
          \<Rightarrow> ((('upVar, 'var, 'metaVar) bag *
            ('upVar, 'var, 'metaVar) bag) list
         * ('upVar, 'var, 'metaVar) bag list
         * ('upVar, 'var, 'metaVar) bag list) option" where
"ditachBagWithVars UnitBag = Some ([],[],[])"
| "ditachBagWithVars (IdBag x) = None"
| "ditachBagWithVars (Xml x y z) = (if hasRewriteInBagR z then Some ([], [(Xml x y z)],[])
                          else Some ([], [], [(Xml x y z)]))"
| "ditachBagWithVars (SingleCell x y z) =
                (if hasRewriteInBigK z then Some ([], [(SingleCell x y z)],[])
                          else Some ([], [], [(SingleCell x y z)]))"
| "ditachBagWithVars (BagCon l r) =
         (case (ditachBagRWithVars l, ditachBagRWithVars r) of (Some (x,y,z), Some (u,v,w))
              \<Rightarrow> Some (x@u,y@v,z@w) | _ \<Rightarrow> None)"
| "ditachBagRWithVars (KTerm a) = ditachBagWithVars a"
| "ditachBagRWithVars (KRewrite a b) =
              (if (\<not> hasRewriteInBag a) \<and> (\<not> hasRewriteInBag b)
                then Some ([(a,b)],[],[]) else None)"

primrec searchBagWithNameInList ::
  "'var var \<Rightarrow>
       (('var var * feature list * ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list
      \<Rightarrow> (('var var * feature list *
     ('upVar, 'var, 'metaVar) irBigKWithBag) list *
         ('upVar, 'var, 'metaVar) suB list * (('var var * feature list *
          ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list
     * (('var var * feature list *
          ('upVar, 'var, 'metaVar) irBigKWithBag) list *
           ('upVar, 'var, 'metaVar) suB list) list)" where
"searchBagWithNameInList v [] = ([],[],[], [])"
| "searchBagWithNameInList v (b#l) = (case b of (x,y) \<Rightarrow>
       (case (searchBagWithNameInIRBag v x, searchBagWithName v y) of ((xl, xr),(yl, yr))
       \<Rightarrow> (case searchBagWithNameInList v l of
        (left, right, acc, changeAcc) \<Rightarrow>
          if xl = [] \<and> yl = [] then (left, right, b#acc, changeAcc) else
         if xr = [] \<and> yr = [] then
           (xl@left, yl@right, acc, changeAcc)
         else (xl@left, yl@right, acc, (xr, yr)#changeAcc))))"

function prepareBagTripleList
    and normalizeBagTripleList
    and prepareBagNoDot
    and normalizeBagNoDot
    and normalizeNextBag
    and normalizeInSUBigKWithBag where
 "prepareBagTripleList P [] [] [] vars acc database = 
       (case normalizeBagTripleList P acc vars database of None \<Rightarrow> None
         | Some (l, r, lrr, vars') \<Rightarrow> 
           if lrr = [] \<and> hasNoBagVarInSUBag r then
          (case freshVar vars' of newVar \<Rightarrow>
            Some (BagPat l (Some (newVar)), r@[IdB (newVar)],
                   (newVar)#vars')) else None)"
| "prepareBagTripleList P [] [] (b#l) vars acc database = (case toIRInBag b database of
         Some (BagPat x None) \<Rightarrow>
          (case fillVarsBySearchBags P x [] vars of None \<Rightarrow> None
            | Some (x', xr, vars') \<Rightarrow> if xr = [] then
             prepareBagTripleList P [] [] l vars' (acc@[(x',(irToSUInIRBagList x'))]) database
             else None) | _ \<Rightarrow> None)"
| "prepareBagTripleList P [] (b#l) L vars acc database = (case b of SingleCell x y z \<Rightarrow>
      (case (getLeftInBigK z, getRightInBigK z) of (Some zl, Some zr) \<Rightarrow>
         (case (toIRInBigK zl database, toSUInBigK zr) of (Some zl', Some zr') \<Rightarrow>
       prepareBagTripleList P [] l L vars (acc@[([(x,removeDotInFeatureList y,zl')],
                 [(ItemB x (removeDotInFeatureList y) zr')])]) database
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       | Xml x y z \<Rightarrow> (case getSubPattern x P of None \<Rightarrow> None
            | Some (fl,P') \<Rightarrow>
         (case normalizeInSUBigKWithBag x y P' z vars database of None \<Rightarrow> None
          | Some (left, right, vars') \<Rightarrow>
           prepareBagTripleList P [] l L vars' (acc@[([left],[right])]) database))
         | _ \<Rightarrow> None)"
| "prepareBagTripleList P (b#l) R L vars acc database = (case b of (x,y) \<Rightarrow>
      (case (toIRInBag x database, toSUInBag y) of (Some (BagPat x' None), Some y') \<Rightarrow>
      (case fillVarsBySearchBags P x' [] vars of None \<Rightarrow> None
       | Some (xa, xr, varsa) \<Rightarrow>
          (case completeBagBySearchBags y' P [] of None \<Rightarrow> None
      | Some (ya, yr) \<Rightarrow> if xr = [] \<and> yr = [] then
       prepareBagTripleList P l R L varsa (acc@[(xa, ya)]) database else None))
        | _ \<Rightarrow> None))"
| "normalizeBagTripleList [] acc vars database = Some ([], [], acc, vars)"
| "normalizeBagTripleList (b#l) acc vars database = (case b of IdB x \<Rightarrow> None
            | ItemB x y z \<Rightarrow>
    (case searchBagWithNameInList x acc of (left, right, acc', accChange) \<Rightarrow>
     if acc' = [] then
             (case normalizeBagTripleList l accChange vars database of None \<Rightarrow> None
          | Some (lefta, righta, acca, varsa) \<Rightarrow> 
            Some (left@lefta, right@righta, acca, varsa))
   else (case normalizeNextBag z acc' vars database of None \<Rightarrow> None
       | Some (left', right', acca, vars') \<Rightarrow>
           (case normalizeBagTripleList l acca vars' database of None \<Rightarrow> None
          | Some (lefta, righta, accb, varsa) \<Rightarrow> 
         if left' = [] \<and> right' = [] then
            Some (left@lefta, right@righta, accb, varsa)
         else (case freshVar varsa of newVar \<Rightarrow>
  Some (left@[(x,removeDotInFeatureList y, IRBag (BagPat left' (Some (newVar))))]@lefta,
           right@[(ItemB x y (SUBag (right'@[IdB (newVar)])))]@righta, accb, varsa))))))"
| "normalizeNextBag a acc vars database = (case a of SUBag x \<Rightarrow>
    normalizeBagTripleList x acc vars database | _ \<Rightarrow> Some ([], [], acc, vars))"
| "normalizeInSUBigKWithBag x y S B vars database = (case S of SUBag T \<Rightarrow>
      (if DotDotDot \<in> set y then
       (case ditachBagR B of None \<Rightarrow> None
              | Some (u, v, w) \<Rightarrow>
    (case prepareBagTripleList T u v w vars [] database of None \<Rightarrow> None
       | Some (left, right, vars') \<Rightarrow> Some ((x, removeDotInFeatureList y, IRBag left),
              ItemB x (removeDotInFeatureList y) (SUBag right), vars')))
   else (case ditachBagRWithVars B of None \<Rightarrow> None
              | Some (u, v, w) \<Rightarrow>
       (case prepareBagNoDot T u v w vars (BagPat [] None, []) database of None \<Rightarrow> None
       | Some (left, right, vars') \<Rightarrow>
                  Some ((x, y, IRBag left), ItemB x y (SUBag right), vars'))))
       | _ \<Rightarrow> None)"
|  "prepareBagNoDot P [] [] [] vars acc database = (case normalizeBagNoDot P acc database 
      of None \<Rightarrow> None
      | Some (x,y) \<Rightarrow> Some (x,y,vars))"
| "prepareBagNoDot P [] [] (b#l) vars acc database = (case toIRInBag b database of
         Some (BagPat x y) \<Rightarrow>
          (case fillVarsBySearchBags P x [] vars of None \<Rightarrow> None
            | Some (x', xr, vars') \<Rightarrow> if xr = [] then
        (case mergeBagTuple (BagPat x' y) (irToSUInIRBagList x') acc of None \<Rightarrow> None
          | Some acc' \<Rightarrow> prepareBagNoDot P [] [] l vars' acc' database)
             else None) | _ \<Rightarrow> None)"
| "prepareBagNoDot P [] (b#l) L vars acc database = (case b of SingleCell x y z \<Rightarrow>
      (case (getLeftInBigK z, getRightInBigK z) of (Some zl, Some zr) \<Rightarrow>
         (case (toIRInBigK zl database, toSUInBigK zr) of (Some zl', Some zr') \<Rightarrow>
         (case mergeBagTuple (BagPat [(x,removeDotInFeatureList y,zl')] None)
                    [(ItemB x (removeDotInFeatureList y) zr')] acc of None \<Rightarrow> None
           | Some acc' \<Rightarrow> prepareBagNoDot P [] l L vars acc' database)
        | _ \<Rightarrow> None) | _ \<Rightarrow> None)
       | Xml x y z \<Rightarrow> (case getSubPattern x P of None \<Rightarrow> None
            | Some (fl,P') \<Rightarrow>
         (case normalizeInSUBigKWithBag x y P' z vars database of None \<Rightarrow> None
          | Some (left, right, vars') \<Rightarrow>
           (case mergeBagTuple (BagPat [left] None) [right] acc of None \<Rightarrow> None
              | Some acc' \<Rightarrow> prepareBagNoDot P [] l L vars' acc' database)))
         | _ \<Rightarrow> None)"
| "prepareBagNoDot P (b#l) R L vars acc database = (case b of (x,y) \<Rightarrow>
      (case (toIRInBag x database, toSUInBag y) of (Some (BagPat x' v), Some y') \<Rightarrow>
      (case fillVarsBySearchBags P x' [] vars of None \<Rightarrow> None
       | Some (xa, xr, varsa) \<Rightarrow>
          (case completeBagBySearchBags y' P [] of None \<Rightarrow> None
      | Some (ya, yr) \<Rightarrow> if xr = [] \<and> yr = [] then
       (case mergeBagTuple (BagPat xa v) ya acc of None \<Rightarrow> None
          | Some acc' \<Rightarrow>
       prepareBagNoDot P l R L varsa acc' database) else None))
        | _ \<Rightarrow> None))"
| "normalizeBagNoDot [] T database = (case T of (BagPat u v, y) \<Rightarrow> 
         if u = [] \<and> onlyIdInSUBag y then Some (BagPat [] v, y) else None)"
| "normalizeBagNoDot (b#l) T database = (case b of IdB x \<Rightarrow> None
         | ItemB x y z \<Rightarrow> (case T of (BagPat u v, y) \<Rightarrow>
        (case (searchBagWithNameInIRBag x u, searchBagWithName x y)
          of ((ul, ur), (yl, yr)) \<Rightarrow>
           (case normalizeBagNoDot l (BagPat ur v, yr) database of None \<Rightarrow> None
              | Some (BagPat u' v', y') \<Rightarrow> Some (BagPat (ul@u') v', yl@y')))))"
by pat_completeness auto

termination sorry

(* final k compile step *)
primrec updateFunInRules where
"updateFunInRules a [] = (case a of (s, x, y, z, rs) \<Rightarrow>
         if Owise \<in> set rs then Some [(FunPat s [] (Some (x,y,z)))]
          else Some [(FunPat s [(x,y,z)] None)])"
| "updateFunInRules a (b#l) = (case b of (FunPat s rl None) \<Rightarrow>
             (case a of (s', x, y, z, rs) \<Rightarrow>
     if s = s' then (if Owise \<in> set rs then Some ((FunPat s rl (Some (x,y,z)))#l)
                            else Some ((FunPat s (rl@[(x,y,z)]) None)#l))
          else (case updateFunInRules a l of None \<Rightarrow> None
                      | Some l' \<Rightarrow> Some (b#l')))
      | (FunPat s rl (Some r)) \<Rightarrow> (case a of (s', x, y, z, rs) \<Rightarrow>
      if s = s' then (if Owise \<in> set rs then None
                  else Some ((FunPat s (rl@[(x,y,z)]) (Some r))#l)) else
         (case updateFunInRules a l of None \<Rightarrow> None
                      | Some l' \<Rightarrow> Some (b#l')))
          | _ \<Rightarrow> None)"

(* a funtion to transfer rules in IR format to SUIR format with type check
   and does a lot of checks on valid rules
   Representing the core of compilation step *)
fun normalizeRules where
"normalizeRules [] Theory database subG = Some []"
| "normalizeRules ((KRule a b)#l) Theory database subG = (if hasRewriteInKR a then
     (case (getLeftInKR a, getRightInKR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInKR al database, toSUInKR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUK ar') then None else
         (if Macro \<in> set b then (case al' of
             (NormalPat (KMatching (KPat [IRKItem ala alb alty] None))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
              | Some l' \<Rightarrow> (case getIRKLabel ala of None \<Rightarrow> None
                    | Some ss \<Rightarrow>
                  if isFunctionItem ss database then None else Some ((MacroPat ss alb ar')#l')))
            (* not a necessary check isFunctionItem here. Adding only because of easy proof *)
             | _ \<Rightarrow> None)
          else if Anywhere \<in> set b then
  (case al' of (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss) alb alty] None))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat ss alb ar'
                   (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))#l'))
       | _ \<Rightarrow> None)
          else (case al' of (KFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then 
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, (KFunPat ss alb), KSubs ar',
             (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l') else None
               | _ \<Rightarrow> (case al' of (NormalPat (KMatching ala))
                \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
               Some ((KRulePat ala ar' (SUKItem (SUKLabel 
                         (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
             else Some ((KRulePat ala ar' (SUKItem (SUKLabel 
                         (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
                 | _ \<Rightarrow> None))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKR a then
     (case (getLeftInKR a, getRightInKR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKR al database, toSUInKR ar, toSUInKItem c) of
        (Some al', Some ar', Some c') \<Rightarrow>
       (if (hasHoleInPat al' \<or> hasHoleInSUK ar' \<or> hasHoleInSUKItem c') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then
              (case al' of (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss) alb alty] None)))
                \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat  ss alb ar' c')#l'))
       | _ \<Rightarrow> None)
          else (case al' of (KFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KSubs ar', c', b) l') else None
               | _ \<Rightarrow> (case al' of (NormalPat (KMatching ala)) \<Rightarrow>
                (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then Some ((KRulePat ala ar' c' True)#l')
                          else Some ((KRulePat ala ar' c' False)#l'))
                | _ \<Rightarrow> None))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KItemRule a b)#l) Theory database subG = (if hasRewriteInKItemR a then
     (case (getLeftInKItemR a, getRightInKItemR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKItemR al database, toSUInKItemR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKItem ar') then None else
         (if Macro \<in> set b then (case al' of
             (NormalPat (KItemMatching (IRKItem ala alb alty))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
              | Some l' \<Rightarrow> (case getIRKLabel ala of None \<Rightarrow> None
           | Some ss \<Rightarrow>
           if isFunctionItem ss database then None else Some ((MacroPat ss alb [ItemFactor ar'])#l')))
             (* not a necessary check isFunctionItem here. Adding only because of easy proof *)
             | _ \<Rightarrow> None)
          else if Anywhere \<in> set b then
         (case al' of (NormalPat (KItemMatching (IRKItem (IRKLabel ss) alb alty))) \<Rightarrow>
                 (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow> Some ((AnywherePat ss alb [ItemFactor ar']
                       (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))#l'))
               | _ \<Rightarrow> None)
          else (case al' of (KItemFunPat ss alb) \<Rightarrow>
            (if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KItemSubs ar',
                 (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l')
               else None)
               | _ \<Rightarrow> (case al' of (NormalPat (KItemMatching ala))
            \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
                Some ((KRulePat (KPat [ala] None) [ItemFactor ar']
               (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
              else Some ((KRulePat (KPat [ala] None) [ItemFactor ar']
               (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KItemRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKItemR a then
     (case (getLeftInKItemR a, getRightInKItemR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKItemR al database, toSUInKItemR ar, toSUInKItem c) of
                      (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUKItem ar' \<or> hasHoleInSUKItem c') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then
              (case al' of (NormalPat (KItemMatching (IRKItem (IRKLabel ss) alb alty)))
           \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None 
    | Some l' \<Rightarrow>  Some ((AnywherePat ss alb
                               [ItemFactor ar'] c')#l'))  | _ \<Rightarrow> None)
          else (case al' of (KItemFunPat ss alb) \<Rightarrow>
            (if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow>
                    updateFunInRules (ss, al', KItemSubs ar', c', b) l') else None)
               | _ \<Rightarrow> (case al' of (NormalPat (KItemMatching ala))
             \<Rightarrow> (case normalizeRules l Theory database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> if Transition \<in> set b then
                    Some ((KRulePat (KPat [ala] None) [ItemFactor ar'] c' True)#l')
             else Some ((KRulePat (KPat [ala] None) [ItemFactor ar'] c' False)#l'))))))
             | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KLabelRule a b)#l) Theory database subG = (if hasRewriteInKLabelR a then
     (case (getLeftInKLabelR a, getRightInKLabelR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKLabelR al database, toSUInKLabelR ar) of (Some al', Some ar') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKLabel ar') then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (KLabelFunPat ss alb) \<Rightarrow>
           if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KLabelSubs ar',
                        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]), b) l')
                  else None | _ \<Rightarrow> None)))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((KLabelRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInKLabelR a then
     (case (getLeftInKLabelR a, getRightInKLabelR a) of (Some al, Some ar) \<Rightarrow>
   (case (toIRInKLabelR al database, toSUInKLabelR ar, toSUInKItem c)
      of (Some al', Some ar', Some c') \<Rightarrow>
           (if (hasHoleInPat al' \<or> hasHoleInSUKLabel ar' \<or> hasHoleInSUKItem c') 
            then None else (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (KLabelFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', KLabelSubs ar', c', b) l')
        else None | _ \<Rightarrow> None)))
        | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((BagRule a b)#l) Theory database subG = (if hasRewriteInBagR a then
   (case ditachBagR a of None \<Rightarrow> None 
     | Some (u,v,w) \<Rightarrow> (case getConfiguration Theory of [P] \<Rightarrow>
     (case toSUInBag P of None \<Rightarrow> None | Some P' \<Rightarrow>
      (case prepareBagTripleList P' u v w (getAllMetaVarsInBagR a) [] database 
              of None \<Rightarrow> None
         | Some (al, ar, vars) \<Rightarrow>
      (if (hasHoleInIRBag al \<or> hasHoleInSUBag ar) then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case normalizeRules l Theory database subG of None \<Rightarrow> None 
            | Some l' \<Rightarrow> if Transition \<in> set b then
             Some ((BagRulePat al ar
              (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l')
          else Some ((BagRulePat al ar
              (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))))))
           | _ \<Rightarrow> None)) else None)"
| "normalizeRules ((BagRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInBagR a then
   (case ditachBagR a of None \<Rightarrow> None 
     | Some (u,v,w) \<Rightarrow> (case getConfiguration Theory of [P] \<Rightarrow>
     (case (toSUInBag P, toSUInKItem c) of (Some P', Some c') \<Rightarrow>
      (case prepareBagTripleList P' u v w (getAllMetaVarsInBagR a) [] database
         of None \<Rightarrow> None | Some (al, ar, vars) \<Rightarrow>
      (if (hasHoleInIRBag al \<or> hasHoleInSUBag ar) then None else
         (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case normalizeRules l Theory database subG of None \<Rightarrow> None 
            | Some l' \<Rightarrow> if Transition \<in> set b then
             Some ((BagRulePat al ar c' True)#l') else  Some ((BagRulePat al ar c' False)#l')))))
             | _ \<Rightarrow> None)
           | _ \<Rightarrow> None)) else None)"
| "normalizeRules ((ListRule a b)#l) Theory database subG = (if hasRewriteInListR a then
     (case (getLeftInListR a, getRightInListR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInListR al database, toSUInListR ar) of (Some al', Some ar') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUList ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (ListFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', ListSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
                   else None | _ \<Rightarrow> None)))
           | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((ListRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInListR a then
     (case (getLeftInListR a, getRightInListR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInListR al database, toSUInListR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUList ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (ListFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', ListSubs ar', c', b) l')
                       else None | _ \<Rightarrow> None)))
           | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((SetRule a b)#l) Theory database subG = (if hasRewriteInSetR a then
     (case (getLeftInSetR a, getRightInSetR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInSetR al database, toSUInSetR ar) of (Some al', Some ar') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUSet ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (SetFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', SetSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
          else None | _ \<Rightarrow> None)))
          | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((SetRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInSetR a then
     (case (getLeftInSetR a, getRightInSetR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInSetR al database, toSUInSetR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUSet ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (SetFunPat ss alb) \<Rightarrow>
             if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', SetSubs ar', c', b) l')
        else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((MapRule a b)#l) Theory database subG = (if hasRewriteInMapR a then
     (case (getLeftInMapR a, getRightInMapR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInMapR al database, toSUInMapR ar) of (Some al', Some ar') \<Rightarrow> 
     (if (hasHoleInPat al' \<or> hasHoleInSUMap ar') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (MapFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
               (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', MapSubs ar',
                  SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool], b) l')
     else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((MapRuleWithCon a c b)#l) Theory database subG = (if hasRewriteInMapR a then
     (case (getLeftInMapR a, getRightInMapR a) of (Some al, Some ar) \<Rightarrow>
        (case (toIRInMapR al database, toSUInMapR ar, toSUInKItem c)
         of (Some al', Some ar', Some c') \<Rightarrow>
     (if (hasHoleInPat al' \<or> hasHoleInSUMap ar' \<or> hasHoleInSUKItem c') then None else
       (if Macro \<in> set b then None
          else if Anywhere \<in> set b then None
          else (case al' of (MapFunPat ss alb) \<Rightarrow>
            if isFunctionItem ss database then
              (case normalizeRules l Theory database subG of None \<Rightarrow> None
               | Some l' \<Rightarrow> updateFunInRules (ss, al', MapSubs ar', c', b) l')
      else None | _ \<Rightarrow> None)))
         | _ \<Rightarrow> None) | _ \<Rightarrow> None) else None)"
| "normalizeRules ((Context a b)#l) Theory database subG = 
    (case a of (KItemC (KTerm (KLabelC ss)) alb alt) \<Rightarrow>
     if (isFunctionItem ss database \<or> \<not> validContextInKItem a
         \<or> Macro \<in> set b \<or> Anywhere \<in> set b) then None else
       (case locateHoleInKItem a of None \<Rightarrow> None
                    | Some ty \<Rightarrow> (if subsort ty KItem subG then
     (case (getLeftInKItem a, getRightInKItem a) of (Some al, Some ar) \<Rightarrow>
      (case freshVar (getAllMetaVarsInKItem al) of newVar \<Rightarrow>
      (case (toIRInKItem al database, toIRInKItem (fillHoleInKItem al (newVar) ty) database,
                  toSUInKItem (fillHoleInKItem ar (newVar) KResult))
         of (Some (NormalPat (KItemMatching alHole)),
                Some (NormalPat (KItemMatching al')), Some ar') \<Rightarrow>
       (case normalizeRules l Theory database subG of None \<Rightarrow> None 
          | Some l' \<Rightarrow>
         (case getResultSortInAttrs b of None \<Rightarrow>
    if Transition \<in> set b then
    Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
          [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
  else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
          [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
        (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
         | Some resultT \<Rightarrow>
          (case meet [KResult] [resultT] subG of [] \<Rightarrow> None
          | resultT' \<Rightarrow> if Transition \<in> set b then
     Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
          (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
    else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
       ItemFactor (irToSUInKItem alHole)] (SUKItem (SUKLabel NotBool)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
          (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l')))))
                   | _ \<Rightarrow> None)) | _ \<Rightarrow> None) else None)) | _ \<Rightarrow> None)"
| "normalizeRules ((ContextWithCon a c b)#l) Theory database subG =
    (case a of (KItemC (KTerm (KLabelC ss)) alb alt) \<Rightarrow>
     if (isFunctionItem ss database \<or> \<not> validContextInKItem a
         \<or> Macro \<in> set b \<or> Anywhere \<in> set b) then None else
       (case locateHoleInKItem a of None \<Rightarrow> None
                    | Some ty \<Rightarrow>
   (if subsort ty KItem subG then
     (case (getLeftInKItem a, getRightInKItem a, toSUInKItem c)
       of (Some al, Some ar, Some c') \<Rightarrow>
      if hasHoleInSUKItem c' then None else
      (case freshVar (getAllMetaVarsInKItem al) of newVar \<Rightarrow>
       (case (toIRInKItem al database, toIRInKItem (fillHoleInKItem al (newVar) ty) database,
                  toSUInKItem (fillHoleInKItem ar (newVar) KResult))
         of (Some (NormalPat (KItemMatching alHole)),
                 Some (NormalPat (KItemMatching al')), Some ar') \<Rightarrow>
       (case normalizeRules l Theory database subG of None \<Rightarrow> None 
          | Some l' \<Rightarrow>
         (case getResultSortInAttrs b of None \<Rightarrow>
          if Transition \<in> set b then
    Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
            ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
        ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
    [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
       [Bool])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
            (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
   else Some ((KRulePat (KPat [al'] None) [ItemFactor (SUIdKItem (newVar) [ty]),
            ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
        ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
    [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
        [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
       [Bool])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) [KResult], alHole] None) [ItemFactor ar'] 
            (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l'))
         | Some resultT \<Rightarrow>
          (case meet [KResult] [resultT] subG of [] \<Rightarrow> None
          | resultT' \<Rightarrow> if Transition \<in> set b then
     Some ((KRulePat (KPat [al'] None)
             [ItemFactor (SUIdKItem (newVar) [ty]), ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
           ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
           [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
        [Bool])]))] [Bool])]))] [Bool]) True)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
           (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) True)#l'))
     else Some ((KRulePat (KPat [al'] None)
             [ItemFactor (SUIdKItem (newVar) [ty]), ItemFactor (irToSUInKItem alHole)]
        (SUKItem (SUKLabel AndBool) [ItemKl (SUBigBag (SUK [ItemFactor c'])),
           ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel NotBool)
           [ItemKl (SUBigBag (SUK [ItemFactor (SUKItem (SUKLabel IsKResult)
                [ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar) [ty])]))]
        [Bool])]))] [Bool])]))] [Bool]) False)
        #((KRulePat (KPat [IRIdKItem (newVar) resultT', alHole] None) [ItemFactor ar'] 
           (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]) False)#l')))))
                   | _ \<Rightarrow> None)) | _ \<Rightarrow> None) else None)) | _ \<Rightarrow> None)"

end