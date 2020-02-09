theory kGetters
imports Main Real List kSyntax
begin

(* This file defines all getter functions that will be used later*)

primrec  hasRewriteInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> bool"
    and hasRewriteInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite \<Rightarrow> bool"
    and hasRewriteInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> bool"
    and hasRewriteInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite \<Rightarrow> bool"
    and hasRewriteInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> bool"
    and hasRewriteInKListR :: "('upVar, 'var, 'metaVar) kList rewrite \<Rightarrow> bool"
    and hasRewriteInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> bool"
    and hasRewriteInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> bool"
    and hasRewriteInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> bool"
    and hasRewriteInListR :: "('upVar, 'var, 'metaVar) theList rewrite \<Rightarrow> bool"
    and hasRewriteInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> bool"
    and hasRewriteInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite \<Rightarrow> bool"
    and hasRewriteInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> bool"
    and hasRewriteInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite \<Rightarrow> bool"
    and hasRewriteInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag \<Rightarrow> bool"
    and hasRewriteInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> bool"
    and hasRewriteInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> bool"
    and hasRewriteInBagR :: "('upVar, 'var, 'metaVar) bag rewrite \<Rightarrow> bool"
 where
  "hasRewriteInKLabel (KLabelC a) = False"
| "hasRewriteInKLabel (KLabelFun a b) = (hasRewriteInKLabel a \<or> hasRewriteInKListR b)"
| "hasRewriteInKLabel (IdKLabel n) = False"
| "hasRewriteInKLabelR (KTerm n) = hasRewriteInKLabel n"
| "hasRewriteInKLabelR (KRewrite l r) = True"
| "hasRewriteInKItem (KItemC l r ty) = ((hasRewriteInKLabelR l) \<or> (hasRewriteInKListR r))"
| "hasRewriteInKItem (Constant a b) = False"
| "hasRewriteInKItem (IdKItem a b) = False"
| "hasRewriteInKItem (HOLE a) = False"
| "hasRewriteInKItemR (KTerm t) = hasRewriteInKItem t"
| "hasRewriteInKItemR (KRewrite l r) = True"
| "hasRewriteInKList (KListCon b t) = ((hasRewriteInKListR b) \<or> (hasRewriteInKListR t))"
| "hasRewriteInKList UnitKList = False"
| "hasRewriteInKList (KListItem a) = (hasRewriteInBigKWithBag a)"
| "hasRewriteInKList (IdKList a) = False"
| "hasRewriteInKListR (KTerm t) = hasRewriteInKList t"
| "hasRewriteInKListR (KRewrite l r) = True"
| "hasRewriteInBigKWithBag (TheBigK a) = hasRewriteInBigK a"
| "hasRewriteInBigKWithBag (TheBigBag b) = hasRewriteInBagR b"
| "hasRewriteInBigKWithBag (TheLabel b) = hasRewriteInKLabelR b"
| "hasRewriteInBigK (TheK t) = hasRewriteInKR t"
| "hasRewriteInBigK (TheList t) = hasRewriteInListR t"
| "hasRewriteInBigK (TheSet t) = hasRewriteInSetR t"
| "hasRewriteInBigK (TheMap t) = hasRewriteInMapR t"
| "hasRewriteInK (Tilda a t) = ((hasRewriteInKR a) \<or> (hasRewriteInKR t))"
| "hasRewriteInK UnitK = False"
| "hasRewriteInK (SingleK a) = hasRewriteInKItemR a"
| "hasRewriteInK (IdK a) = False"
| "hasRewriteInK (KFun l r) = ((hasRewriteInKLabel l) \<or> (hasRewriteInKListR r))"
| "hasRewriteInKR (KTerm a) = (hasRewriteInK a)"
| "hasRewriteInKR (KRewrite l r) = True"
| "hasRewriteInList (ListCon l r) = ((hasRewriteInListR l) \<or> (hasRewriteInListR r))"
| "hasRewriteInList UnitList = False"
| "hasRewriteInList (IdList a) = False"
| "hasRewriteInList (ListItem a) = hasRewriteInKR a"
| "hasRewriteInList (ListFun l r) = ((hasRewriteInKLabel l) \<or> (hasRewriteInKListR r))"
| "hasRewriteInListR (KTerm a) = (hasRewriteInList a)"
| "hasRewriteInListR (KRewrite l r) = True"
| "hasRewriteInSet (SetCon l r) = ((hasRewriteInSetR l) \<or> (hasRewriteInSetR r))"
| "hasRewriteInSet UnitSet = False"
| "hasRewriteInSet (IdSet a) = False"
| "hasRewriteInSet (SetItem a) = hasRewriteInKR a"
| "hasRewriteInSet (SetFun l r) = ((hasRewriteInKLabel l) \<or> (hasRewriteInKListR r))"
| "hasRewriteInSetR (KTerm a) = (hasRewriteInSet a)"
| "hasRewriteInSetR (KRewrite l r) = True"
| "hasRewriteInMap (MapCon l r) = ((hasRewriteInMapR l) \<or> (hasRewriteInMapR r))"
| "hasRewriteInMap UnitMap = False"
| "hasRewriteInMap (IdMap a) = False"
| "hasRewriteInMap (MapItem l r) = ((hasRewriteInKR l) \<or> (hasRewriteInKR r))"
| "hasRewriteInMap (MapFun l r) = ((hasRewriteInKLabel l) \<or> (hasRewriteInKListR r))"
| "hasRewriteInMapR (KTerm a) = (hasRewriteInMap a)"
| "hasRewriteInMapR (KRewrite l r) = True"
| "hasRewriteInBag (BagCon l r) = ((hasRewriteInBagR l) \<or> (hasRewriteInBagR r))"
| "hasRewriteInBag UnitBag = False"
| "hasRewriteInBag (IdBag a) = False"
| "hasRewriteInBag (Xml a n t) =  hasRewriteInBagR t"
| "hasRewriteInBag (SingleCell a n t) =  hasRewriteInBigK t"
| "hasRewriteInBagR (KTerm a) = (hasRewriteInBag a)"
| "hasRewriteInBagR (KRewrite l r) = True"

primrec getLeftInKLabel :: "('upVar, 'var, 'metaVar) kLabel
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel option"
and getLeftInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel rewrite option"
and getLeftInKItem :: "('upVar, 'var, 'metaVar) kItem
                        \<Rightarrow> ('upVar, 'var, 'metaVar) kItem option"
    and getLeftInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite
                       \<Rightarrow> ('upVar, 'var, 'metaVar) kItem rewrite option"
    and getLeftInKList :: "('upVar, 'var, 'metaVar) kList
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kList option"
    and getLeftInKListR :: "('upVar, 'var, 'metaVar) kList rewrite
               \<Rightarrow> ('upVar, 'var, 'metaVar) kList rewrite option"
    and getLeftInK :: "('upVar, 'var, 'metaVar) k
                         \<Rightarrow> ('upVar, 'var, 'metaVar) k option"
    and getLeftInKR :: "('upVar, 'var, 'metaVar) k rewrite
                      \<Rightarrow> ('upVar, 'var, 'metaVar) k rewrite option"
    and getLeftInList :: "('upVar, 'var, 'metaVar) theList
                       \<Rightarrow> ('upVar, 'var, 'metaVar) theList option"
    and getLeftInListR :: "('upVar, 'var, 'metaVar) theList rewrite
                \<Rightarrow> ('upVar, 'var, 'metaVar) theList rewrite option"
    and getLeftInSet :: "('upVar, 'var, 'metaVar) theSet
               \<Rightarrow> ('upVar, 'var, 'metaVar) theSet option"
    and getLeftInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite
               \<Rightarrow> ('upVar, 'var, 'metaVar) theSet rewrite option"
    and getLeftInMap :: "('upVar, 'var, 'metaVar) theMap
                        \<Rightarrow> ('upVar, 'var, 'metaVar) theMap option"
    and getLeftInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite
                  \<Rightarrow> ('upVar, 'var, 'metaVar) theMap rewrite option"
    and getLeftInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag
                    \<Rightarrow> ('upVar, 'var, 'metaVar) bigKWithBag option"
    and getLeftInBigK :: "('upVar, 'var, 'metaVar) bigK
                          \<Rightarrow> ('upVar, 'var, 'metaVar) bigK option"
    and getLeftInBag :: "('upVar, 'var, 'metaVar) bag
                            \<Rightarrow> ('upVar, 'var, 'metaVar) bag option"
    and getLeftInBagR :: "('upVar, 'var, 'metaVar) bag rewrite
                      \<Rightarrow> ('upVar, 'var, 'metaVar) bag rewrite option"
 where
"getLeftInKLabel (KLabelC a) = Some (KLabelC a)"
| "getLeftInKLabel (KLabelFun a b) = (case getLeftInKLabel a of None \<Rightarrow> None
                   | Some a' \<Rightarrow> (case getLeftInKListR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (KLabelFun a' b')))"
| "getLeftInKLabel (IdKLabel n) = Some (IdKLabel n)"
| "getLeftInKLabelR (KTerm n) = (case getLeftInKLabel n of None \<Rightarrow> None
                                      | Some n' \<Rightarrow> Some (KTerm n'))"
| "getLeftInKLabelR (KRewrite l r) = (if (hasRewriteInKLabel l \<or> hasRewriteInKLabel r)
                                        then None else Some (KTerm l))"
| "getLeftInKItem (KItemC l r ty) = (case (getLeftInKLabelR l) of None \<Rightarrow> None
                      | Some l' \<Rightarrow> (case getLeftInKListR r of None \<Rightarrow> None
                     | Some r' \<Rightarrow> Some (KItemC l' r' ty)))"
| "getLeftInKItem (Constant a b) = Some (Constant a b)"
| "getLeftInKItem (IdKItem a b) = Some (IdKItem a b)"
| "getLeftInKItem (HOLE a) = Some (HOLE a)"
| "getLeftInKItemR (KTerm t) = (case getLeftInKItem t of None \<Rightarrow> None
                       | Some t' \<Rightarrow> Some (KTerm t'))"
| "getLeftInKItemR (KRewrite l r) = (if (hasRewriteInKItem l
                            \<or> hasRewriteInKItem r) then None else Some (KTerm l))"
| "getLeftInKList (KListCon b t) = (case (getLeftInKListR b)
                of None \<Rightarrow> None | Some b' \<Rightarrow>
                 (case (getLeftInKListR t) of None \<Rightarrow> None
                  | Some t' \<Rightarrow> Some (KListCon b' t')))"
| "getLeftInKList UnitKList = Some UnitKList"
| "getLeftInKList (KListItem a) = (case (getLeftInBigKWithBag a) of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KListItem a'))"
| "getLeftInKList (IdKList a) = Some (IdKList a)"
| "getLeftInKListR (KTerm t) = (case (getLeftInKList t) of None \<Rightarrow> None
                                 | Some t' \<Rightarrow> Some (KTerm t'))"
| "getLeftInKListR (KRewrite l r) = (if (hasRewriteInKList l \<or> hasRewriteInKList r)
                                then None else Some (KTerm l))"
| "getLeftInBigKWithBag (TheBigK a) = (case getLeftInBigK a of None \<Rightarrow> None 
                                   | Some a' \<Rightarrow> Some (TheBigK a'))"
| "getLeftInBigKWithBag (TheBigBag b) = (case getLeftInBagR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (TheBigBag b'))"
| "getLeftInBigKWithBag (TheLabel b) = (case getLeftInKLabelR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (TheLabel b'))"
| "getLeftInBigK (TheK t) = (case getLeftInKR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheK t'))"
| "getLeftInBigK (TheList t) = (case getLeftInListR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheList t'))"
| "getLeftInBigK (TheSet t) = (case getLeftInSetR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheSet t'))"
| "getLeftInBigK (TheMap t) = (case getLeftInMapR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheMap t'))"
| "getLeftInK (Tilda a t) = (case (getLeftInKR a) of None \<Rightarrow> None
                          | Some a' \<Rightarrow> (case (getLeftInKR t) of None \<Rightarrow> None
                          | Some t' \<Rightarrow> Some (Tilda a' t')))"
| "getLeftInK UnitK = Some UnitK"
| "getLeftInK (SingleK a) = (case getLeftInKItemR a of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SingleK a'))"
| "getLeftInK (IdK a) = Some (IdK a)"
| "getLeftInK (KFun l r) = (case (getLeftInKLabel l) of None \<Rightarrow> None
                          | Some l' \<Rightarrow> (case getLeftInKListR r of None \<Rightarrow> None
                         | Some r' \<Rightarrow> Some (KFun l' r')))"
| "getLeftInKR (KTerm a) = (case (getLeftInK a) of None \<Rightarrow> None
                           | Some a' \<Rightarrow> Some (KTerm a'))"
| "getLeftInKR (KRewrite l r) = (if (hasRewriteInK l \<or> hasRewriteInK r)
                             then None else Some (KTerm l))"
| "getLeftInList (ListCon l r) = (case getLeftInListR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getLeftInListR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (ListCon l' r')))"
| "getLeftInList UnitList = Some UnitList"
| "getLeftInList (IdList a) = Some (IdList a)"
| "getLeftInList (ListItem a) = (case getLeftInKR a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (ListItem a'))"
| "getLeftInList (ListFun l r) = (case (getLeftInKLabel l) of None \<Rightarrow> None
                        | Some l' \<Rightarrow> (case getLeftInKListR r of None \<Rightarrow> None
                        | Some r' \<Rightarrow> Some (ListFun l' r')))"
| "getLeftInListR (KTerm a) = (case getLeftInList a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getLeftInListR (KRewrite l r) = (if hasRewriteInList l \<or> hasRewriteInList r
                                     then None else Some (KTerm l))"
| "getLeftInSet (SetCon l r) = (case getLeftInSetR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getLeftInSetR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (SetCon l' r')))"
| "getLeftInSet UnitSet = Some UnitSet"
| "getLeftInSet (IdSet a) = Some (IdSet a)"
| "getLeftInSet (SetItem a) = (case getLeftInKR a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (SetItem a'))"
| "getLeftInSet (SetFun l r) = (case (getLeftInKLabel l) of None \<Rightarrow> None
                       | Some l' \<Rightarrow> (case getLeftInKListR r of None \<Rightarrow> None
                       | Some r' \<Rightarrow> Some (SetFun l' r')))"
| "getLeftInSetR (KTerm a) = (case getLeftInSet a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getLeftInSetR (KRewrite l r) = (if hasRewriteInSet l \<or> hasRewriteInSet r
                                     then None else Some (KTerm l))"
| "getLeftInMap (MapCon l r) = (case getLeftInMapR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getLeftInMapR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (MapCon l' r')))"
| "getLeftInMap UnitMap = Some UnitMap"
| "getLeftInMap (IdMap a) = Some (IdMap a)"
| "getLeftInMap (MapItem l r) = (case getLeftInKR l of None \<Rightarrow> None
                 | Some l' \<Rightarrow> (case getLeftInKR r of None \<Rightarrow> None
                 | Some r' \<Rightarrow> Some (MapItem l' r')))"
| "getLeftInMap (MapFun l r) = (case (getLeftInKLabel l) of None \<Rightarrow> None
                     | Some l' \<Rightarrow> (case getLeftInKListR r of None \<Rightarrow> None
                     | Some r' \<Rightarrow> Some (MapFun l' r')))"
| "getLeftInMapR (KTerm a) = (case getLeftInMap a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getLeftInMapR (KRewrite l r) = (if hasRewriteInMap l \<or> hasRewriteInMap r
                                     then None else Some (KTerm l))"
| "getLeftInBag (BagCon l r) = (case (getLeftInBagR l) of None \<Rightarrow> None
                       | Some l' \<Rightarrow> (case (getLeftInBagR r) of None \<Rightarrow> None
                       | Some r' \<Rightarrow> Some (BagCon l' r')))"
| "getLeftInBag UnitBag = Some UnitBag"
| "getLeftInBag (IdBag a) = Some (IdBag a)"
| "getLeftInBag (Xml a n t) = (case getLeftInBagR t of None \<Rightarrow> None
                           | Some t' \<Rightarrow> Some (Xml a n t'))"
| "getLeftInBag (SingleCell a n t) =  (case getLeftInBigK t of None \<Rightarrow> None
                           | Some t' \<Rightarrow> Some (SingleCell a n t'))"
| "getLeftInBagR (KTerm a) = (case getLeftInBag a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (KTerm a'))"
| "getLeftInBagR (KRewrite l r) = (if hasRewriteInBag l \<or> hasRewriteInBag r
                                  then None else Some (KTerm l))"

primrec getRightInKLabel :: "('upVar, 'var, 'metaVar) kLabel
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel option"
and getRightInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kLabel rewrite option"
and getRightInKItem :: "('upVar, 'var, 'metaVar) kItem
                        \<Rightarrow> ('upVar, 'var, 'metaVar) kItem option"
    and getRightInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite
                       \<Rightarrow> ('upVar, 'var, 'metaVar) kItem rewrite option"
    and getRightInKList :: "('upVar, 'var, 'metaVar) kList
                  \<Rightarrow> ('upVar, 'var, 'metaVar) kList option"
    and getRightInKListR :: "('upVar, 'var, 'metaVar) kList rewrite
               \<Rightarrow> ('upVar, 'var, 'metaVar) kList rewrite option"
    and getRightInK :: "('upVar, 'var, 'metaVar) k
                         \<Rightarrow> ('upVar, 'var, 'metaVar) k option"
    and getRightInKR :: "('upVar, 'var, 'metaVar) k rewrite
                      \<Rightarrow> ('upVar, 'var, 'metaVar) k rewrite option"
    and getRightInList :: "('upVar, 'var, 'metaVar) theList
                       \<Rightarrow> ('upVar, 'var, 'metaVar) theList option"
    and getRightInListR :: "('upVar, 'var, 'metaVar) theList rewrite
                \<Rightarrow> ('upVar, 'var, 'metaVar) theList rewrite option"
    and getRightInSet :: "('upVar, 'var, 'metaVar) theSet
               \<Rightarrow> ('upVar, 'var, 'metaVar) theSet option"
    and getRightInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite
               \<Rightarrow> ('upVar, 'var, 'metaVar) theSet rewrite option"
    and getRightInMap :: "('upVar, 'var, 'metaVar) theMap
                        \<Rightarrow> ('upVar, 'var, 'metaVar) theMap option"
    and getRightInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite
                  \<Rightarrow> ('upVar, 'var, 'metaVar) theMap rewrite option"
    and getRightInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag
                    \<Rightarrow> ('upVar, 'var, 'metaVar) bigKWithBag option"
    and getRightInBigK :: "('upVar, 'var, 'metaVar) bigK
                          \<Rightarrow> ('upVar, 'var, 'metaVar) bigK option"
    and getRightInBag :: "('upVar, 'var, 'metaVar) bag
                            \<Rightarrow> ('upVar, 'var, 'metaVar) bag option"
    and getRightInBagR :: "('upVar, 'var, 'metaVar) bag rewrite
                      \<Rightarrow> ('upVar, 'var, 'metaVar) bag rewrite option"
 where
"getRightInKLabel (KLabelC a) = Some (KLabelC a)"
| "getRightInKLabel (KLabelFun a b) = (case getRightInKLabel a of None \<Rightarrow> None
          | Some a' \<Rightarrow> (case getRightInKListR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (KLabelFun a' b')))"
| "getRightInKLabel (IdKLabel n) = Some (IdKLabel n)"
| "getRightInKLabelR (KTerm n) = (case getRightInKLabel n of None \<Rightarrow> None
                                      | Some n' \<Rightarrow> Some (KTerm n'))"
| "getRightInKLabelR (KRewrite l r) = (if (hasRewriteInKLabel l \<or> hasRewriteInKLabel r)
                                        then None else Some (KTerm r))"
| "getRightInKItem (KItemC l r ty) = (case getRightInKLabelR l of None \<Rightarrow> None
                               | Some l' \<Rightarrow>
                                 (case getRightInKListR r of None \<Rightarrow> None
                               | Some r' \<Rightarrow> Some (KItemC  l' r' ty)))"
| "getRightInKItem (Constant a b) = Some (Constant a b)"
| "getRightInKItem (IdKItem a b) = Some (IdKItem a b)"
| "getRightInKItem (HOLE a) = Some (HOLE a)"
| "getRightInKItemR (KTerm t) = (case getRightInKItem t of None \<Rightarrow> None
                       | Some t' \<Rightarrow> Some (KTerm t'))"
| "getRightInKItemR (KRewrite l r) = (if (hasRewriteInKItem l
                            \<or> hasRewriteInKItem r) then None else Some (KTerm r))"
| "getRightInKList (KListCon b t) = (case (getRightInKListR b)
                of None \<Rightarrow> None | Some b' \<Rightarrow>
                 (case (getRightInKListR t) of None \<Rightarrow> None
                  | Some t' \<Rightarrow> Some (KListCon b' t')))"
| "getRightInKList UnitKList = Some UnitKList"
| "getRightInKList (KListItem a) = (case (getRightInBigKWithBag a) of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KListItem a'))"
| "getRightInKList (IdKList a) = Some (IdKList a)"
| "getRightInKListR (KTerm t) = (case (getRightInKList t) of None \<Rightarrow> None
                                 | Some t' \<Rightarrow> Some (KTerm t'))"
| "getRightInKListR (KRewrite l r) = (if (hasRewriteInKList l \<or> hasRewriteInKList r)
                                then None else Some (KTerm r))"
| "getRightInBigKWithBag (TheBigK a) = (case getRightInBigK a of None \<Rightarrow> None 
                                   | Some a' \<Rightarrow> Some (TheBigK a'))"
| "getRightInBigKWithBag (TheBigBag b) = (case getRightInBagR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (TheBigBag b'))"
| "getRightInBigKWithBag (TheLabel b) = (case getRightInKLabelR b of None \<Rightarrow> None
                                   | Some b' \<Rightarrow> Some (TheLabel b'))"
| "getRightInBigK (TheK t) = (case getRightInKR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheK t'))"
| "getRightInBigK (TheList t) = (case getRightInListR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheList t'))"
| "getRightInBigK (TheSet t) = (case getRightInSetR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheSet t'))"
| "getRightInBigK (TheMap t) = (case getRightInMapR t of None \<Rightarrow> None
                            | Some t' \<Rightarrow> Some (TheMap t'))"
| "getRightInK (Tilda a t) = (case (getRightInKR a) of None \<Rightarrow> None
                          | Some a' \<Rightarrow> (case (getRightInKR t) of None \<Rightarrow> None
                          | Some t' \<Rightarrow> Some (Tilda a' t')))"
| "getRightInK UnitK = Some UnitK"
| "getRightInK (SingleK a) = (case getRightInKItemR a of None \<Rightarrow> None
          | Some a' \<Rightarrow> Some (SingleK a'))"
| "getRightInK (IdK a) = Some (IdK a)"
| "getRightInK (KFun l r) = (case (getRightInKLabel l) of None \<Rightarrow> None
                       | Some l' \<Rightarrow> (case getRightInKListR r of None \<Rightarrow> None
                     | Some r' \<Rightarrow> Some (KFun l' r')))"
| "getRightInKR (KTerm a) = (case (getRightInK a) of None \<Rightarrow> None
                           | Some a' \<Rightarrow> Some (KTerm a'))"
| "getRightInKR (KRewrite l r) = (if (hasRewriteInK l \<or> hasRewriteInK r)
                             then None else Some (KTerm r))"
| "getRightInList (ListCon l r) = (case getRightInListR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getRightInListR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (ListCon l' r')))"
| "getRightInList UnitList = Some UnitList"
| "getRightInList (IdList a) = Some (IdList a)"
| "getRightInList (ListItem a) = (case getRightInKR a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (ListItem a'))"
| "getRightInList (ListFun l r) = (case (getRightInKLabel l) of None \<Rightarrow> None
                      | Some l' \<Rightarrow> (case getRightInKListR r of None \<Rightarrow> None
                      | Some r' \<Rightarrow> Some (ListFun l' r')))"
| "getRightInListR (KTerm a) = (case getRightInList a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getRightInListR (KRewrite l r) = (if hasRewriteInList l \<or> hasRewriteInList r
                                     then None else Some (KTerm r))"
| "getRightInSet (SetCon l r) = (case getRightInSetR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getRightInSetR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (SetCon l' r')))"
| "getRightInSet UnitSet = Some UnitSet"
| "getRightInSet (IdSet a) = Some (IdSet a)"
| "getRightInSet (SetFun l r) = (case (getRightInKLabel l) of None \<Rightarrow> None
                      | Some l' \<Rightarrow> (case getRightInKListR r of None \<Rightarrow> None
                      | Some r' \<Rightarrow> Some (SetFun l' r')))"
| "getRightInSet (SetItem a) = (case getRightInKR a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (SetItem a'))"
| "getRightInSetR (KTerm a) = (case getRightInSet a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getRightInSetR (KRewrite l r) = (if hasRewriteInSet l \<or> hasRewriteInSet r
                                     then None else Some (KTerm r))"
| "getRightInMap (MapCon l r) = (case getRightInMapR l of None \<Rightarrow> None
                  | Some l' \<Rightarrow> (case getRightInMapR r of None \<Rightarrow> None
                  | Some r' \<Rightarrow> Some (MapCon l' r')))"
| "getRightInMap UnitMap = Some UnitMap"
| "getRightInMap (IdMap a) = Some (IdMap a)"
| "getRightInMap (MapFun l r) = (case (getRightInKLabel l) of None \<Rightarrow> None
                    | Some l' \<Rightarrow> (case getRightInKListR r of None \<Rightarrow> None
                    | Some r' \<Rightarrow> Some (MapFun l' r')))"
| "getRightInMap (MapItem l r) = (case getRightInKR l of None \<Rightarrow> None
                 | Some l' \<Rightarrow> (case getRightInKR r of None \<Rightarrow> None
                 | Some r' \<Rightarrow> Some (MapItem l' r')))"
| "getRightInMapR (KTerm a) = (case getRightInMap a of None \<Rightarrow> None
                                  | Some a' \<Rightarrow> Some (KTerm a'))"
| "getRightInMapR (KRewrite l r) = (if hasRewriteInMap l \<or> hasRewriteInMap r
                                     then None else Some (KTerm r))"
| "getRightInBag (BagCon l r) = (case (getRightInBagR l) of None \<Rightarrow> None
                       | Some l' \<Rightarrow> (case (getRightInBagR r) of None \<Rightarrow> None
                       | Some r' \<Rightarrow> Some (BagCon l' r')))"
| "getRightInBag UnitBag = Some UnitBag"
| "getRightInBag (IdBag a) = Some (IdBag a)"
| "getRightInBag (Xml a n t) = (case getRightInBagR t of None \<Rightarrow> None
                           | Some t' \<Rightarrow> Some (Xml a n t'))"
| "getRightInBag (SingleCell a n t) =  (case getRightInBigK t of None \<Rightarrow> None
                           | Some t' \<Rightarrow> Some (SingleCell a n t'))"
| "getRightInBagR (KTerm a) = (case getRightInBag a of None \<Rightarrow> None
                               | Some a' \<Rightarrow> Some (KTerm a'))"
| "getRightInBagR (KRewrite l r) = (if hasRewriteInBag l \<or> hasRewriteInBag r
                                  then None else Some (KTerm r))"

primrec getAllMetaVarsInKLabel :: "('upVar, 'var, 'metaVar) kLabel \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKLabelR :: "('upVar, 'var, 'metaVar) kLabel rewrite
                                                                   \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKItem :: "('upVar, 'var, 'metaVar) kItem \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKItemR :: "('upVar, 'var, 'metaVar) kItem rewrite
                                                            \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKList :: "('upVar, 'var, 'metaVar) kList \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKListR :: "('upVar, 'var, 'metaVar) kList rewrite
                                                             \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInK :: "('upVar, 'var, 'metaVar) k \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInKR :: "('upVar, 'var, 'metaVar) k rewrite \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInList :: "('upVar, 'var, 'metaVar) theList \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInListR :: "('upVar, 'var, 'metaVar) theList rewrite
                                                                   \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSet :: "('upVar, 'var, 'metaVar) theSet \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInSetR :: "('upVar, 'var, 'metaVar) theSet rewrite
                                                                   \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInMap :: "('upVar, 'var, 'metaVar) theMap \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInMapR :: "('upVar, 'var, 'metaVar) theMap rewrite
                                                                      \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInBigKWithBag :: "('upVar, 'var, 'metaVar) bigKWithBag
                                                                    \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInBigK :: "('upVar, 'var, 'metaVar) bigK \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInBag :: "('upVar, 'var, 'metaVar) bag \<Rightarrow> 'metaVar metaVar list"
    and getAllMetaVarsInBagR :: "('upVar, 'var, 'metaVar) bag rewrite
                                                                   \<Rightarrow> 'metaVar metaVar list"
 where
  "getAllMetaVarsInKLabel (KLabelC a) = []"
| "getAllMetaVarsInKLabel (KLabelFun a b) = (getAllMetaVarsInKLabel a @ getAllMetaVarsInKListR b)"
| "getAllMetaVarsInKLabel (IdKLabel n) = [n]"
| "getAllMetaVarsInKLabelR (KTerm n) = getAllMetaVarsInKLabel n"
| "getAllMetaVarsInKLabelR (KRewrite l r) = ((getAllMetaVarsInKLabel l)@(getAllMetaVarsInKLabel r))"
| "getAllMetaVarsInKItem (KItemC l r ty) = ((getAllMetaVarsInKLabelR l)@(getAllMetaVarsInKListR r))"
| "getAllMetaVarsInKItem (Constant a b) = []"
| "getAllMetaVarsInKItem (IdKItem a b) = [a]"
| "getAllMetaVarsInKItem (HOLE a) = []"
| "getAllMetaVarsInKItemR (KTerm t)= (getAllMetaVarsInKItem t)"
| "getAllMetaVarsInKItemR (KRewrite l r)
                               = ((getAllMetaVarsInKItem l) @ (getAllMetaVarsInKItem r))"
| "getAllMetaVarsInKList (KListCon b t) = ((getAllMetaVarsInKListR b)@(getAllMetaVarsInKListR t))"
| "getAllMetaVarsInKList UnitKList = []"
| "getAllMetaVarsInKList (IdKList a) = [a]"
| "getAllMetaVarsInKList (KListItem a) = (getAllMetaVarsInBigKWithBag a)"
| "getAllMetaVarsInKListR (KTerm t) = getAllMetaVarsInKList t"
| "getAllMetaVarsInKListR (KRewrite l r) = ((getAllMetaVarsInKList l)@(getAllMetaVarsInKList r))"
| "getAllMetaVarsInBigKWithBag (TheBigK a) = getAllMetaVarsInBigK a"
| "getAllMetaVarsInBigKWithBag (TheBigBag b) = getAllMetaVarsInBagR b"
| "getAllMetaVarsInBigKWithBag (TheLabel b) = getAllMetaVarsInKLabelR b"
| "getAllMetaVarsInBigK (TheK t) = getAllMetaVarsInKR t"
| "getAllMetaVarsInBigK (TheList t) = getAllMetaVarsInListR t"
| "getAllMetaVarsInBigK (TheSet t) = getAllMetaVarsInSetR t"
| "getAllMetaVarsInBigK (TheMap t) = getAllMetaVarsInMapR t"
| "getAllMetaVarsInK (Tilda a t) = ((getAllMetaVarsInKR a)@(getAllMetaVarsInKR t))"
| "getAllMetaVarsInK UnitK = []"
| "getAllMetaVarsInK (IdK a) = [a]"
| "getAllMetaVarsInK (SingleK a) = (getAllMetaVarsInKItemR a)"
| "getAllMetaVarsInK (KFun l r) = ((getAllMetaVarsInKLabel l)@(getAllMetaVarsInKListR r))"
| "getAllMetaVarsInKR (KTerm a) = (getAllMetaVarsInK a)"
| "getAllMetaVarsInKR (KRewrite l r) = ((getAllMetaVarsInK l)@(getAllMetaVarsInK r))"
| "getAllMetaVarsInList (ListCon l r) = ((getAllMetaVarsInListR l)@(getAllMetaVarsInListR r))"
| "getAllMetaVarsInList UnitList = []"
| "getAllMetaVarsInList (IdList a) = [a]"
| "getAllMetaVarsInList (ListItem a) = getAllMetaVarsInKR a"
| "getAllMetaVarsInList (ListFun l r) = ((getAllMetaVarsInKLabel l)@(getAllMetaVarsInKListR r))"
| "getAllMetaVarsInListR (KTerm a) = (getAllMetaVarsInList a)"
| "getAllMetaVarsInListR (KRewrite l r) = ((getAllMetaVarsInList l)@(getAllMetaVarsInList r))"
| "getAllMetaVarsInSet (SetCon l r) = ((getAllMetaVarsInSetR l)@(getAllMetaVarsInSetR r))"
| "getAllMetaVarsInSet UnitSet = []"
| "getAllMetaVarsInSet (IdSet a) = [a]"
| "getAllMetaVarsInSet (SetItem a) = getAllMetaVarsInKR a"
| "getAllMetaVarsInSet (SetFun l r) = ((getAllMetaVarsInKLabel l)@(getAllMetaVarsInKListR r))"
| "getAllMetaVarsInSetR (KTerm a) = (getAllMetaVarsInSet a)"
| "getAllMetaVarsInSetR (KRewrite l r) = ((getAllMetaVarsInSet l)@(getAllMetaVarsInSet r))"
| "getAllMetaVarsInMap (MapCon l r) = ((getAllMetaVarsInMapR l)@(getAllMetaVarsInMapR r))"
| "getAllMetaVarsInMap UnitMap = []"
| "getAllMetaVarsInMap (IdMap a) = [a]"
| "getAllMetaVarsInMap (MapItem l r) = ((getAllMetaVarsInKR l)@(getAllMetaVarsInKR r))"
| "getAllMetaVarsInMap (MapFun l r) = ((getAllMetaVarsInKLabel l)@(getAllMetaVarsInKListR r))"
| "getAllMetaVarsInMapR (KTerm a) = (getAllMetaVarsInMap a)"
| "getAllMetaVarsInMapR (KRewrite l r) = ((getAllMetaVarsInMap l)@(getAllMetaVarsInMap r))"
| "getAllMetaVarsInBag (BagCon l r) = ((getAllMetaVarsInBagR l)@(getAllMetaVarsInBagR r))"
| "getAllMetaVarsInBag UnitBag = []"
| "getAllMetaVarsInBag (IdBag a) = [a]"
| "getAllMetaVarsInBag (Xml a n t) =  getAllMetaVarsInBagR t"
| "getAllMetaVarsInBag (SingleCell a n t) =  getAllMetaVarsInBigK t"
| "getAllMetaVarsInBagR (KTerm a) = (getAllMetaVarsInBag a)"
| "getAllMetaVarsInBagR (KRewrite l r) = ((getAllMetaVarsInBag l)@(getAllMetaVarsInBag r))"

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
| "getAllMetaVarsInIRKList (KListPatNoVar a) =
             foldl (\<lambda> acc y . (getAllMetaVarsInIRBigKWithLabel y)@acc) [] a"
| "getAllMetaVarsInIRKList (KListPat a b c) =
        b#(foldl (\<lambda> acc y . (getAllMetaVarsInIRBigKWithLabel y)@acc) [] (a@c))"
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
| "getAllMetaVarsInIRList (ListPatNoVar a) = foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] a"
| "getAllMetaVarsInIRList (ListPat a b c) =
         b#(foldl (\<lambda> acc y . (getAllMetaVarsInIRK y)@acc) [] (a@c))"
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

(*
fun getAllConfiVarsInMetaVars :: "'metaVar metaVar list \<Rightarrow> 'metaVar list" where
"getAllConfiVarsInMetaVars [] = []"
| "getAllConfiVarsInMetaVars ((ConfiVar a)#l) = a#(getAllConfiVarsInMetaVars l)"
| "getAllConfiVarsInMetaVars (x#l) = (getAllConfiVarsInMetaVars l)"
*)

fun getNonTerminalInList :: "'upVar symbol nelist \<Rightarrow> 'upVar sort list" where
"getNonTerminalInList (Single (Terminal a)) = []"
| "getNonTerminalInList (Single (NonTerminal a)) = [a]"
| "getNonTerminalInList (Con (Terminal a) l) = getNonTerminalInList l"
| "getNonTerminalInList (Con (NonTerminal a) l) = a#(getNonTerminalInList l)"

fun getRelationSortInSyntax where
 "getRelationSortInSyntax (Syntax a bl cl) = Some [(getNonTerminalInList bl,a)]"
| "getRelationSortInSyntax (Token a b cl) = Some [([],a)]"
| "getRelationSortInSyntax (ListSyntax a b s cl) = Some [([b,a],a),([],a)]"
| "getRelationSortInSyntax A = None"

fun getAllFunctionsInSyntax :: "'upVar kSyntax list
     \<Rightarrow> 'upVar kSyntax list" where
"getAllFunctionsInSyntax [] = []"
| "getAllFunctionsInSyntax ((Syntax a bl cl)#l) = (if Function \<in> set cl
     then (Syntax a bl cl)#(getAllFunctionsInSyntax l)
     else getAllFunctionsInSyntax l)"
| "getAllFunctionsInSyntax (A#l) = getAllFunctionsInSyntax l"

fun getAllSubsortInKModuleItemList where
 "getAllSubsortInKModuleItemList [] = []"
| "getAllSubsortInKModuleItemList ((TheSyntax (Subsort a b))#l)
                                  = List.insert (a,b) (getAllSubsortInKModuleItemList l)"
| "getAllSubsortInKModuleItemList ((TheSyntax x)#l) =  (getAllSubsortInKModuleItemList l)"
| "getAllSubsortInKModuleItemList ((Imports x)#l) = (getAllSubsortInKModuleItemList l)"
| "getAllSubsortInKModuleItemList ((TheConfiguration x)#l) = (getAllSubsortInKModuleItemList l)"
| "getAllSubsortInKModuleItemList ((TheRule x)#l) = (getAllSubsortInKModuleItemList l)"

fun getAllSubsortInKFile :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
                                         \<Rightarrow> ('upVar sort * 'upVar sort) list" where
"getAllSubsortInKFile (TheFile (Single (TheRequires m))) = []"
| "getAllSubsortInKFile (TheFile (Single (TheModule (Module a m)))) = getAllSubsortInKModuleItemList m"
| "getAllSubsortInKFile (TheFile (Con (TheRequires m) xs)) = getAllSubsortInKFile (TheFile xs)"
| "getAllSubsortInKFile (TheFile (Con (TheModule (Module a m)) xs))
           =  insertAll (getAllSubsortInKModuleItemList m) (getAllSubsortInKFile (TheFile xs))"

fun getAllSorts :: "'upVar kSyntax list \<Rightarrow> 'upVar sort list" where
 "getAllSorts [] = []"
| "getAllSorts ((Syntax x pros l)#xs) = List.insert x (getAllSorts xs)"
| "getAllSorts ((ListSyntax a b pros l)#xs) = List.insert a (getAllSorts xs)"
| "getAllSorts ((Token a s l)#xs) = List.insert a (getAllSorts xs)"
| "getAllSorts (a#xs) = (getAllSorts xs)"

fun getAllSubsortOnItem :: "('upVar * 'upVar) list \<Rightarrow> 'upVar \<Rightarrow> 'upVar list" where
"getAllSubsortOnItem [] a = []"
| "getAllSubsortOnItem ((x,y)#l) a = (if y = a
                       then x#(getAllSubsortOnItem l a) else getAllSubsortOnItem l a)"

fun getAllRulesInKModuleItemList :: "('upVar, 'var, 'acapvar, 'metaVar) kModuleItem list
                               \<Rightarrow> ('upVar, 'var, 'metaVar) kRule list" where
 "getAllRulesInKModuleItemList [] = []"
| "getAllRulesInKModuleItemList ((TheSyntax x)#l) =  (getAllRulesInKModuleItemList l)"
| "getAllRulesInKModuleItemList ((Imports x)#l) = (getAllRulesInKModuleItemList l)"
| "getAllRulesInKModuleItemList ((TheConfiguration x)#l) = (getAllRulesInKModuleItemList l)"
| "getAllRulesInKModuleItemList ((TheRule x)#l) = x#(getAllRulesInKModuleItemList l)"

fun getAllRulesInKModule :: "('upVar, 'var, 'acapvar, 'metaVar) kModule
                    \<Rightarrow> ('upVar, 'var, 'metaVar) kRule list" where
"getAllRulesInKModule (Module a l) = getAllRulesInKModuleItemList l"

fun getAllRules :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
       \<Rightarrow> ('upVar, 'var, 'metaVar) kRule list" where
"getAllRules (TheFile (Single (TheRequires s))) = []"
| "getAllRules (TheFile (Single (TheModule m))) = getAllRulesInKModule m"
| "getAllRules (TheFile (Con (TheRequires s) l)) = getAllRules (TheFile l)"
| "getAllRules (TheFile (Con (TheModule m) l)) = (getAllRulesInKModule m)@(getAllRules (TheFile l))"

fun getConfigurationList :: "('upVar, 'var, 'acapvar, 'metaVar) kModuleItem list
                               \<Rightarrow> ('upVar, 'var, 'metaVar) bag list" where
 "getConfigurationList [] = []"
| "getConfigurationList ((TheSyntax x)#l) =  (getConfigurationList l)"
| "getConfigurationList ((Imports x)#l) = (getConfigurationList l)"
| "getConfigurationList ((TheConfiguration x)#l) = x#(getConfigurationList l)"
| "getConfigurationList ((TheRule x)#l) = (getConfigurationList l)"

fun getConListInModule :: "('upVar, 'var, 'acapvar, 'metaVar) kModule
                    \<Rightarrow> ('upVar, 'var, 'metaVar) bag list" where
"getConListInModule (Module a l) = getConfigurationList l"

fun getConfiguration :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
                    \<Rightarrow> ('upVar, 'var, 'metaVar) bag list" where
"getConfiguration (TheFile (Single (TheRequires s))) = []"
| "getConfiguration (TheFile (Single (TheModule m))) = getConListInModule m"
| "getConfiguration (TheFile (Con (TheRequires s) l)) = getConfiguration (TheFile l)"
| "getConfiguration (TheFile (Con (TheModule m) l)) =
                                          (getConListInModule m)@(getConfiguration (TheFile l))"

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