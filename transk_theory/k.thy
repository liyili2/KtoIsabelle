theory k
imports Main kSort
begin

(*
assume that the parser will remove the following cases and make K to KItem:

A:K \<leadsto> c ...  becomes A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> c ... becomes ... c \<leadsto> A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> B:K becomes c \<leadsto> A:KItem \<leadsto> B:K

hence, left vars do not apply on the K case.

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
| "irToSUInKList (KListPat l a r) = 
   (case a of None \<Rightarrow>
     (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)
          @((List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) r))
   | Some x
      \<Rightarrow> (List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) l)@[IdKl x]
          @((List.map (\<lambda> x . ItemKl (irToSUInBigKWithLabel x)) r)))"
| "irToSUInBigKWithLabel (IRBigBag a) = SUBigBag (irToSUInBigKWithBag a)"
| "irToSUInBigKWithLabel (IRBigLabel a) = SUBigLabel (irToSUInKLabel a)"
| "irToSUInBigKWithBag (IRK a) = SUK (irToSUInK a)"
| "irToSUInBigKWithBag (IRList a) = SUList (irToSUInList a)"
| "irToSUInBigKWithBag (IRSet a) = SUSet (irToSUInSet a)"
| "irToSUInBigKWithBag (IRMap a) = SUMap (irToSUInMap a)"
| "irToSUInBigKWithBag (IRBag a) = SUBag (irToSUInBag a)"
| "irToSUInK (KPat l a) = (case a of None
       \<Rightarrow> List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = K then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l
   | Some a'
      \<Rightarrow> (List.map (\<lambda> x . (case x of (IRIdKItem u v) \<Rightarrow>
           if v = K then (IdFactor u) else ItemFactor (irToSUInKItem x)
            | _ \<Rightarrow> ItemFactor (irToSUInKItem x))) l)@[(IdFactor a')])"
| "irToSUInList (ListPat l a r) = (case a of None \<Rightarrow>
     (List.map (\<lambda> x . ItemL (irToSUInK x)) l)
          @((List.map (\<lambda> x . ItemL (irToSUInK x)) r))
   | Some x
      \<Rightarrow> (List.map (\<lambda> x . ItemL (irToSUInK x)) l)@[IdL x]
          @((List.map (\<lambda> x . ItemL (irToSUInK x)) r)))"
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
             | _ \<Rightarrow> KItemSubs (SUKItem (SUKLabel s) (irToSUInKList l) KItemSort))"
| "irToSUInPat (KFunPat s l) database = KSubs [SUKKItem (SUKLabel s) (irToSUInKList l) K]"
| "irToSUInPat (ListFunPat s l) database = ListSubs [SUListKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (SetFunPat s l) database = SetSubs [SUSetKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (MapFunPat s l) database = MapSubs [SUMapKItem (SUKLabel s) (irToSUInKList l)]"
| "irToSUInPat (NormalPat a) database = irToSUInMatchFactor a"

fun irToSUInIRBagList where
"irToSUInIRBagList [] = []"
| "irToSUInIRBagList ((x,y,z)#l) = (ItemB x y (irToSUInBigKWithBag z))#(irToSUInIRBagList l)"

(* implementation of krun and ksearch *)

(* giving a list of input initial program and a configuration, generating a initial program state *)
fun bagContainsCell :: "'var var \<Rightarrow> ('upVar, 'var, 'metaVar) suB list
                  \<Rightarrow> bool"
   and bagContainsCellAux :: "'var var
      \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag
                  \<Rightarrow> bool"
 where
"bagContainsCell x [] = False"
| "bagContainsCell x (b#l) = (case b of IdB a \<Rightarrow> bagContainsCell x l
          | ItemB u v w \<Rightarrow> if x = u then True else
         (bagContainsCellAux x w \<or> bagContainsCell x l))"
| "bagContainsCellAux x (SUBag y) = bagContainsCell x y"
| "bagContainsCellAux x y = False"

fun createInitState
    and createInitStateAux where
"createInitState [] = Some []"
| "createInitState (b#l) = (case b of IdB x \<Rightarrow> None
         | ItemB x y z \<Rightarrow> if Multiplicity Star \<in> set y
               \<or> Multiplicity Question \<in> set y then
       (if bagContainsCellAux littleK z then (case createInitStateAux z of None \<Rightarrow> None
            | Some z' \<Rightarrow> (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemB x y z')#l')))
     else (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some l')) else
        (case createInitStateAux z of None \<Rightarrow> None
            | Some z' \<Rightarrow> (case createInitState l of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
| "createInitStateAux (SUBag x) = (case createInitState x of None \<Rightarrow> None
            | Some x' \<Rightarrow> Some (SUBag x'))"
| "createInitStateAux a = Some a"

(*
(checkTermsInSUBag (irToSUInBag kl) [],
              checkTermsInSUBag r [], checkTermsInSUKItem c KItem [])
           of (Some (acckl, kl'), Some (accsl, sl'), Some (accz, z')) \<Rightarrow>
    (case (makeSortMap acckl, makeSortMap accsl, makeSortMap accz) of
        (Some acckl', Some accsl', Some accz') \<Rightarrow>
      (case (replaceVarSortInSUBag kl' acckl', replaceVarSortInSUBag sl' accsl',
      replaceVarSortInSUKItem z' accz') of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUBag kla *)

primrec getValueInMatchingMap where
"getValueInMatchingMap a [] = None"
| "getValueInMatchingMap a (b#l) = (case b of (x',y') \<Rightarrow>
               if a = x' then Some y' else getValueInMatchingMap a l)"

(* divide the map into two parts: one's values have zero list,
          the other's value have more than zero element list*)
fun searchZero where
"searchZero [] = ([],[])"
| "searchZero ((a,b)#l) = (case searchZero l of (have, noHave) \<Rightarrow>
                     if b = [] then ((a,b)#have,noHave) else (have,(a,b)#noHave))"

fun eliminateEntry where
"eliminateEntry a [] = []"
| "eliminateEntry a ((b,c)#l) = (if a = b then l else (b,c)#eliminateEntry a l)"

fun eliminateEntryList where
"eliminateEntryList a [] = []"
| "eliminateEntryList a ((b,c)#l) = (b,eliminateEntry a c)#eliminateEntryList a l"

fun eliminateEntryMap where
"eliminateEntryMap [] S = Some S"
| "eliminateEntryMap ((a,(b,c))#l) S = eliminateEntryMap l (eliminateEntryList b S)"

fun searchOneAux where
"searchOneAux [] = ([],[])"
| "searchOneAux ((a,b)#l) = (case searchOneAux l of (have, noHave) \<Rightarrow>
       (case b of [b'] \<Rightarrow> ((a,b')#have,noHave)
            | _ \<Rightarrow> (have,(a,b)#noHave)))"

function searchOne where
"searchOne l acc = (case searchZero l of (x,y) \<Rightarrow>
            if x = [] then (case searchOneAux y of (u,v) \<Rightarrow>
               if u = [] then Some (acc,v)
            else  (case eliminateEntryMap u v of None \<Rightarrow> None
            | Some v' \<Rightarrow> searchOne v' (u@acc))) else None)"
by pat_completeness auto

termination sorry

(* a function to find a way to match each pattern to a expression one by one and on two *)
function findBijection and findBijectionAux where
"findBijection l = (case searchOne l [] of None \<Rightarrow> None
        | Some (ones, mores) \<Rightarrow> (case mores of []
        \<Rightarrow> Some (ones,[]) | ((a,b)#al)
      \<Rightarrow> if al = [] then Some (ones,b) else findBijectionAux a b al))"
| "findBijectionAux a [] S = None"
| "findBijectionAux a ((b,c)#al) S =
     (case searchOne (eliminateEntryList b S) [] of None \<Rightarrow>
        findBijectionAux a al S | Some (ones, mores) \<Rightarrow> 
            if mores = [] then Some ((a,(b,c))#ones,[])
              else (case findBijection mores of None \<Rightarrow> None
         | Some (ones',remains) \<Rightarrow> Some ((a,(b,c))#ones@ones', remains)))"
by pat_completeness auto

termination sorry

primrec searchAllNonTermsInSUSet where
"searchAllNonTermsInSUSet [] = []"
| "searchAllNonTermsInSUSet (a#l) = (case a of ItemS a' \<Rightarrow> searchAllNonTermsInSUSet l
               | _ \<Rightarrow> a#searchAllNonTermsInSUSet l)"

primrec searchAllNonTermsInSUMap where
"searchAllNonTermsInSUMap [] = []"
| "searchAllNonTermsInSUMap (a#l) = (case a of ItemM a' b \<Rightarrow> searchAllNonTermsInSUMap l
               | _ \<Rightarrow> a#searchAllNonTermsInSUMap l)"

primrec searchAllNonTermsInSUBag where
"searchAllNonTermsInSUBag [] = []"
| "searchAllNonTermsInSUBag (a#l) = (case a of ItemB a' b c \<Rightarrow> searchAllNonTermsInSUBag l
               | _ \<Rightarrow> a#searchAllNonTermsInSUBag l)"

(* a pattern matching algorithm that allowing non-linear commutativity equestional rewriting *)
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
       \<Rightarrow> if subsort ty ty' subG then Some (SUKItem la ra ty)
          else Some (SUKItem la ra ty')
    | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "syntacticMonoidInSUKItem (SUHOLE a) S subG = (case S of (SUHOLE a') \<Rightarrow>
     if subsort a a' subG then Some (SUHOLE a) else Some (SUHOLE a'))"
| "syntacticMonoidInSUKItem (SUIdKItem a b) B subG = (case B of SUIdKItem a' b' \<Rightarrow>
         if (a = a') then (if subsort b b' subG then Some (SUIdKItem a b)
           else Some (SUIdKItem a b')) else None)"
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
       (Some xa, Some ya, Some la) \<Rightarrow> if subsort ty ty' subG then
           Some ((SUKKItem xa ya ty)#la) else Some ((SUKKItem xa ya ty')#la)
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
   (case syntacticMonoidInSUK x x' subG of None \<Rightarrow> syntacticMonoidInSUMember b l subG
      | Some xa \<Rightarrow> Some (ItemS xa))
    | (IdS x, IdS x') \<Rightarrow> if x = x' then Some (IdS x) else syntacticMonoidInSUMember b l subG
    | (SUSetKItem x y, SUSetKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
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
   (case syntacticMonoidInSUK x x' subG of None \<Rightarrow> syntacticMonoidInSUMapMember b l subG
      | Some xa \<Rightarrow> (case syntacticMonoidInSUK y y' subG of None \<Rightarrow> None
       | Some ya \<Rightarrow> Some (ItemM xa ya)))
    | (IdM x, IdM x') \<Rightarrow> if x = x' then Some (IdM x)
                 else syntacticMonoidInSUMapMember b l subG
    | (SUMapKItem x y, SUMapKItem x' y') \<Rightarrow>
     (case (syntacticMonoidInSUKLabel x x' subG, syntacticMonoidInSUKList y y' subG)
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
     (if x = x' then (case syntacticMonoidInSUBigKWithBag z z' subG of None \<Rightarrow> None
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

fun macroEquality where
"macroEquality (KLabelSubs a) (KLabelSubs b) subG = 
      (case syntacticMonoidInSUKLabel a b subG of Some a' \<Rightarrow> Some (KLabelSubs a')
          | None \<Rightarrow> None)"
| "macroEquality (KItemSubs a) (KItemSubs b) subG =
  (case syntacticMonoidInSUKItem a b subG
     of Some a' \<Rightarrow> Some (KItemSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (KListSubs a) (KListSubs b) subG =
   (case syntacticMonoidInSUKList a b subG
       of Some a' \<Rightarrow> Some (KListSubs a')
        | _ \<Rightarrow> None)"
| "macroEquality (KSubs a) (KSubs b) subG =
   (case syntacticMonoidInSUK a b subG
        of Some a' \<Rightarrow> Some (KSubs a')
                 | _ \<Rightarrow> None)"
| "macroEquality (ListSubs a) (ListSubs b) subG =
 (case syntacticMonoidInSUList a b subG
    of Some a' \<Rightarrow> Some (ListSubs a')
     | _ \<Rightarrow> None)"
| "macroEquality (SetSubs a) (SetSubs b) subG =
  (case syntacticMonoidInSUSet a b a subG
     of Some a' \<Rightarrow> Some (SetSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (MapSubs a) (MapSubs b) subG =
  (case syntacticMonoidInSUMap a b a subG
     of Some a' \<Rightarrow> Some (MapSubs a')
      | _ \<Rightarrow> None)"
| "macroEquality (BagSubs a) (BagSubs b) subG =
  (case syntacticMonoidInSUBag a b subG
     of Some a' \<Rightarrow> Some (BagSubs a')
     | _ \<Rightarrow> None)"
| "macroEquality A B subG = None"

fun updateMatchingMap where
"updateMatchingMap x y [] subG = Some [(x,y)]"
| "updateMatchingMap x y ((a,b)#l) subG = (if x = a then
           (case macroEquality y b subG of None \<Rightarrow> None
               | Some y' \<Rightarrow> Some ((a,y')#l))
             else (case updateMatchingMap x y l subG of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some ((a,b)#l')))"

fun mergePatMatchMap where
"mergePatMatchMap [] S subG = Some S"
| "mergePatMatchMap ((a,b)#l) S subG = (case updateMatchingMap a b S subG
     of None \<Rightarrow> None | Some S' \<Rightarrow> mergePatMatchMap l S' subG)"

fun mergeMapWithOnes where
"mergeMapWithOnes [] acc subG = Some acc"
| "mergeMapWithOnes ((a,b,c)#l) acc subG =
    (case mergePatMatchMap c acc subG of None \<Rightarrow> None
       | Some acc' \<Rightarrow> mergeMapWithOnes l acc' subG)"

function patternMacroingInSUKLabel
   and patternMacroingInSUKItem
   and patternMacroingInSUKList
   and patternMacroingInSUBigKWithLabel
   and patternMacroingInSUBigKWithBag
   and patternMacroingInSUK
   and patternMacroingInSUList
   and patternMacroingInSUSet
   and patternMacroingInSUSetAux
   and patternMacroingInSUMember
   and patternMacroingInSUMapMember
   and patternMacroingInSUMapAux
   and patternMacroingInSUBagMember
   and patternMacroingInSUBagAux
   and patternMacroingInSUMap
   and patternMacroingInSUBag
  where
"patternMacroingInSUKLabel (IRKLabel a) S acc subG =
    (case S of (SUKLabel b) \<Rightarrow>
     if a = b then Some acc else None
       | _ \<Rightarrow> None)"
| "patternMacroingInSUKLabel (IRIdKLabel a) S acc subG
           = (updateMatchingMap a (KLabelSubs S) acc subG)"
| "patternMacroingInSUKItem (IRKItem l r ty) S acc subG = (case S of (SUKItem l' r' ty') \<Rightarrow>
 (if subsort ty' ty subG then
       (case patternMacroingInSUKLabel l l' acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow>
              (case patternMacroingInSUKList r r' acc' subG of None \<Rightarrow> None
          | Some acca \<Rightarrow> Some acca)) else None) | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRHOLE a) S acc subG = (case S of (SUHOLE a') \<Rightarrow>
     (if (subsort a' a subG) then Some acc else None)
      | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRIdKItem a b) B acc subG = (case B of (SUIdKItem a' b')
         \<Rightarrow> (if subsort b' b subG then
                updateMatchingMap a (KItemSubs (SUIdKItem a' b')) acc subG
            else None)
       | (SUKItem l r ty) \<Rightarrow> (if subsort ty b subG then
       updateMatchingMap a (KItemSubs (SUKItem l r ty)) acc subG else None)
       | _ \<Rightarrow> None)"
| "patternMacroingInSUKList (KListPat l n r) S acc subG = (case l of [] \<Rightarrow>
     (case rev r of [] \<Rightarrow> (case n of None \<Rightarrow>
       (case S of [] \<Rightarrow> Some acc | (sua#sul) \<Rightarrow> None)
          | Some v \<Rightarrow> updateMatchingMap v (KListSubs S) acc subG)
       | (ra#rl) \<Rightarrow> (case rev S of [] \<Rightarrow> None
       | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow>
         (case patternMacroingInSUBigKWithLabel ra x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
         (case patternMacroingInSUKList (KListPat l n (rev rl)) (rev sul) acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca))
         | IdKl x \<Rightarrow> None)))
       | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
          | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow>
         (case patternMacroingInSUBigKWithLabel la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
         (case patternMacroingInSUKList (KListPat ll n r) sul acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca))
            | _ \<Rightarrow> None)))"
| "patternMacroingInSUK (KPat l n) S acc subG = (case l of [] \<Rightarrow>
           (case n of None \<Rightarrow> (case S of [] \<Rightarrow> Some acc
             | (sua#sul) \<Rightarrow> None)
               | Some v \<Rightarrow> updateMatchingMap v (KSubs S) acc subG)
          | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
           | (sua#sul) \<Rightarrow> (case sua of ItemFactor x \<Rightarrow>
          (case patternMacroingInSUKItem la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG)
          | IdFactor x \<Rightarrow> (case la of (IRIdKItem x' ty) \<Rightarrow> 
            if ty = K then (case updateMatchingMap x' (KSubs [(IdFactor x)]) acc subG
                 of None \<Rightarrow> None | Some acc'
                 \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
            | _ \<Rightarrow> None)
          | SUKKItem x y ty \<Rightarrow> (case la of (IRIdKItem x' ty') \<Rightarrow>
            if ty = K then (case updateMatchingMap x' (KSubs [(SUKKItem x y ty)]) acc subG
            of None \<Rightarrow> None | Some acc'
                \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
              |  _ \<Rightarrow> None))))"
| "patternMacroingInSUList (ListPat l n r) S acc subG = (case l of [] \<Rightarrow>
          (case rev r of [] \<Rightarrow>
           (case n of None \<Rightarrow> (case S of [] \<Rightarrow> Some acc
             | (sua#sul) \<Rightarrow> None)
               | Some v \<Rightarrow> updateMatchingMap v (ListSubs S) acc subG)
            | (ra#rl) \<Rightarrow> (case rev S of [] \<Rightarrow> None
                | (sua#sul) \<Rightarrow> (case sua of ItemL x \<Rightarrow>
          (case patternMacroingInSUK ra x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow>
                    patternMacroingInSUList (ListPat l n (rev rl)) (rev sul) acc' subG)
              | _ \<Rightarrow> None)))
          | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
           | (sua#sul) \<Rightarrow> (case sua of ItemL x \<Rightarrow>
          (case patternMacroingInSUK la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow> patternMacroingInSUList (ListPat ll n r) sul acc' subG)
          | _ \<Rightarrow> None)))"
| "patternMacroingInSUMember a [] acc subG = (a,[])"
| "patternMacroingInSUMember a (t#l) acc subG = (case t of (ItemS x) \<Rightarrow>
   (case patternMacroingInSUK a x acc subG of None
      \<Rightarrow> patternMacroingInSUMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acc')#v)))
     | _ \<Rightarrow> patternMacroingInSUMember a l acc subG)"
| "patternMacroingInSUSetAux [] S acc subG = []"
| "patternMacroingInSUSetAux (a#l) S acc subG =
          (patternMacroingInSUMember a S acc subG)#(patternMacroingInSUSetAux l S acc subG)"
| "patternMacroingInSUSet (SetPat l n) S acc subG =
      (case patternMacroingInSUSetAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUSet S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMap var (SetSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUMapMember a [] acc subG = (a,[])"
| "patternMacroingInSUMapMember a (t#l) acc subG = (case a of (b,c) \<Rightarrow>
      (case t of (ItemM x y) \<Rightarrow>
   (case patternMacroingInSUK b x acc subG of None
      \<Rightarrow> patternMacroingInSUMapMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUK c y acc' subG of None \<Rightarrow>
        patternMacroingInSUMapMember a l acc subG | Some acca \<Rightarrow>
     (case patternMacroingInSUMapMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acca)#v))))
     | _ \<Rightarrow> patternMacroingInSUMapMember a l acc subG))"
| "patternMacroingInSUMapAux [] S acc subG = []"
| "patternMacroingInSUMapAux (a#l) S acc subG =
          (patternMacroingInSUMapMember a S acc subG)#(patternMacroingInSUMapAux l S acc subG)"
| "patternMacroingInSUMap (MapPat l n) S acc subG =
   (case patternMacroingInSUMapAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUMap S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMap var (MapSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUBagMember a [] acc subG = (a,[])"
| "patternMacroingInSUBagMember a (t#l) acc subG = (case a of (b,c,d) \<Rightarrow>
      (case t of (ItemB x y z) \<Rightarrow> if b = x then
   (case patternMacroingInSUBigKWithBag d z acc subG of None
      \<Rightarrow> patternMacroingInSUBagMember a l acc subG
       | Some acc' \<Rightarrow> (case patternMacroingInSUBagMember a l acc subG
          of (u,v) \<Rightarrow> (u,(t,acc')#v))) else patternMacroingInSUBagMember a l acc subG
     | _ \<Rightarrow> patternMacroingInSUBagMember a l acc subG))"
| "patternMacroingInSUBagAux [] S acc subG = []"
| "patternMacroingInSUBagAux (a#l) S acc subG =
          (patternMacroingInSUBagMember a S acc subG)#(patternMacroingInSUBagAux l S acc subG)"
| "patternMacroingInSUBag (BagPat l n) S acc subG =
    (case patternMacroingInSUBagAux l S acc subG of S' \<Rightarrow>
       (case findBijection S' of None \<Rightarrow> None
      | Some (ones, remains) \<Rightarrow>
    (case searchAllNonTermsInSUBag S of rest \<Rightarrow>
       (case n of None \<Rightarrow> if rest = [] \<and> remains = [] then 
        mergeMapWithOnes ones acc subG else None
         | Some var \<Rightarrow>
   (case updateMatchingMap var (BagSubs (rest@(keys remains))) acc subG of
        None \<Rightarrow> None | Some acc' \<Rightarrow> mergeMapWithOnes ones acc' subG)))))"
| "patternMacroingInSUBigKWithBag (IRK t) S acc subG =
        (case S of (SUK r) \<Rightarrow> patternMacroingInSUK t r acc subG
           | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRBag t) S acc subG =
        (case S of (SUBag r) \<Rightarrow> patternMacroingInSUBag t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRList t) S acc subG =
        (case S of (SUList r) \<Rightarrow> patternMacroingInSUList t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRSet t) S acc subG =
        (case S of (SUSet r) \<Rightarrow> patternMacroingInSUSet t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithBag (IRMap t) S acc subG =
        (case S of (SUMap r) \<Rightarrow> patternMacroingInSUMap t r acc subG
            | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithLabel (IRBigBag t) S acc subG =
        (case S of (SUBigBag t') \<Rightarrow> patternMacroingInSUBigKWithBag t t' acc subG
          | _ \<Rightarrow> None)"
| "patternMacroingInSUBigKWithLabel (IRBigLabel t) S acc subG =
        (case S of (SUBigLabel t') \<Rightarrow> patternMacroingInSUKLabel t t' acc subG
          | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

function substitutionInSUKLabel :: "('upVar, 'var, 'metaVar) suKLabel
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKLabel option"
    and substitutionInSUKItem :: "('upVar, 'var, 'metaVar) suKItem
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKItem option"
    and substitutionInSUKList :: "('upVar, 'var, 'metaVar) suKl list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKl list option"
    and substitutionInSUBigKWithBag :: "('upVar, 'var, 'metaVar) suBigKWithBag
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithBag option"
    and substitutionInSUBigKWithLabel :: "('upVar, 'var, 'metaVar) suBigKWithLabel
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suBigKWithLabel option"
    and substitutionInSUK :: "('upVar, 'var, 'metaVar) suKFactor list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suKFactor list option"
    and substitutionInSUList :: "('upVar, 'var, 'metaVar) suL list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suL list option"
    and substitutionInSUSet :: "('upVar, 'var, 'metaVar) suS list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suS list option"
    and substitutionInSUMap :: "('upVar, 'var, 'metaVar) suM list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suM list option"
    and substitutionInSUBag :: "('upVar, 'var, 'metaVar) suB list
         \<Rightarrow> ('metaVar metaVar * ('upVar, 'var, 'metaVar) subsFactor) list
         \<Rightarrow> ('upVar, 'var, 'metaVar) suB list option" where
 "substitutionInSUKLabel (SUKLabel a) acc = Some (SUKLabel a)"
| "substitutionInSUKLabel (SUIdKLabel a) acc =
         (case getValueInMatchingMap a acc of Some (KLabelSubs x) \<Rightarrow> Some x
             | _ \<Rightarrow> None)"
| "substitutionInSUKLabel (SUKLabelFun a b) acc =
     (case (substitutionInSUKLabel a acc, substitutionInSUKList b acc)
       of (Some x, Some y) \<Rightarrow> Some (SUKLabelFun x y)
          | _ \<Rightarrow> None)"
| "substitutionInSUKItem (SUKItem l r ty) acc =
   (case (substitutionInSUKLabel l acc, substitutionInSUKList r acc) of (Some x, Some y)
      \<Rightarrow> Some (SUKItem x y ty) | _ \<Rightarrow> None)"
| "substitutionInSUKItem (SUHOLE a) acc = Some (SUHOLE a)"
| "substitutionInSUKItem (SUIdKItem a b) acc = (case getValueInMatchingMap a acc
     of Some (KItemSubs a') \<Rightarrow> Some a' | _ \<Rightarrow> None)"
| "substitutionInSUKList [] acc = Some []"
| "substitutionInSUKList (b#l) acc = (case b of IdKl x \<Rightarrow>
         (case getValueInMatchingMap x acc of Some (KListSubs x') \<Rightarrow>
           (case substitutionInSUKList l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (x'@l'))
             | _ \<Rightarrow> None)
       | ItemKl x \<Rightarrow>
        (case substitutionInSUBigKWithLabel x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow>
           (case substitutionInSUKList l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemKl x')#l'))))"
| "substitutionInSUK [] acc = Some []"
| "substitutionInSUK (b#l) acc = (case b of IdFactor x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (KSubs x') \<Rightarrow>
           (case substitutionInSUK l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemFactor x \<Rightarrow> (case substitutionInSUKItem x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUK l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemFactor x')#l')))
    | SUKKItem x y ty \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUK l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUKKItem x' y' ty)#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUList [] acc = Some []"
| "substitutionInSUList (b#l) acc = (case b of IdL x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (ListSubs x') \<Rightarrow>
           (case substitutionInSUList l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemL x \<Rightarrow> (case substitutionInSUK x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUList l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemL x')#l')))
    | SUListKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUList l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUListKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUSet [] acc = Some []"
| "substitutionInSUSet (b#l) acc = (case b of IdS x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (SetSubs x') \<Rightarrow>
           (case substitutionInSUSet l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemS x \<Rightarrow> (case substitutionInSUK x acc of None \<Rightarrow> None
           | Some x' \<Rightarrow> (case substitutionInSUSet l acc of None \<Rightarrow> None
         | Some l' \<Rightarrow> Some ((ItemS x')#l')))
    | SUSetKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUSet l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUSetKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUMap [] acc = Some []"
| "substitutionInSUMap (b#l) acc = (case b of IdM x \<Rightarrow>
      (case getValueInMatchingMap x acc of Some (MapSubs x') \<Rightarrow>
           (case substitutionInSUMap l acc of None \<Rightarrow> None
               | Some l' \<Rightarrow> Some (x'@l')) | _ \<Rightarrow> None)
    | ItemM x y \<Rightarrow> (case (substitutionInSUK x acc, substitutionInSUK y acc,
         substitutionInSUMap l acc) of (Some x', Some y', Some l')
         \<Rightarrow> Some ((ItemM x' y')#l') | _ \<Rightarrow> None)
    | SUMapKItem x y \<Rightarrow> (case (substitutionInSUKLabel x acc,
       substitutionInSUKList y acc, substitutionInSUMap l acc)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUMapKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "substitutionInSUBigKWithBag (SUK a) acc = (case substitutionInSUK a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUK a'))"
| "substitutionInSUBigKWithBag (SUList a) acc = (case substitutionInSUList a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUList a'))"
| "substitutionInSUBigKWithBag (SUSet a) acc = (case substitutionInSUSet a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUSet a'))"
| "substitutionInSUBigKWithBag (SUMap a) acc = (case substitutionInSUMap a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUMap a'))"
| "substitutionInSUBigKWithBag (SUBag a) acc = (case substitutionInSUBag a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBag a'))"
| "substitutionInSUBigKWithLabel (SUBigBag a) acc = (case substitutionInSUBigKWithBag a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "substitutionInSUBigKWithLabel (SUBigLabel a) acc = (case substitutionInSUKLabel a acc of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "substitutionInSUBag [] acc = Some []"
| "substitutionInSUBag (b#l) acc = (case b of IdB x \<Rightarrow>
         (case getValueInMatchingMap x acc of Some (BagSubs x') \<Rightarrow>
           (case substitutionInSUBag l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some (x'@l'))
             | _ \<Rightarrow> None)
       | ItemB x y z \<Rightarrow>
        (case substitutionInSUBigKWithBag z acc of None \<Rightarrow> None
           | Some z' \<Rightarrow>
           (case substitutionInSUBag l acc of None \<Rightarrow> None
              | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
by pat_completeness auto

termination sorry

fun substitutionInSubsFactor where
"substitutionInSubsFactor (KLabelSubs a) acc = (case substitutionInSUKLabel a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "substitutionInSubsFactor (KItemSubs a) acc = (case substitutionInSUKItem a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KItemSubs a'))"
| "substitutionInSubsFactor (KListSubs a) acc = (case substitutionInSUKList a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KListSubs a'))"
| "substitutionInSubsFactor (KSubs a) acc = (case substitutionInSUK a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (KSubs a'))"
| "substitutionInSubsFactor (ListSubs a) acc = (case substitutionInSUList a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (ListSubs a'))"
| "substitutionInSubsFactor (SetSubs a) acc = (case substitutionInSUSet a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (SetSubs a'))"
| "substitutionInSubsFactor (MapSubs a) acc = (case substitutionInSUMap a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (MapSubs a'))"
| "substitutionInSubsFactor (BagSubs a) acc = (case substitutionInSUBag a acc
      of None \<Rightarrow> None | Some a' \<Rightarrow> Some (BagSubs a'))"

(* dealing with function rules *)
function hasFunLabelInSUKLabel
    and hasFunLabelInSUKItem
    and hasFunLabelInSUKList
    and hasFunLabelInSUBigKWithBag
    and hasFunLabelInSUBigKWithLabel
    and hasFunLabelInSUK
    and hasFunLabelInSUList
    and hasFunLabelInSUSet
    and hasFunLabelInSUMap
    and hasFunLabelInSUBag where
"hasFunLabelInSUKLabel (SUKLabel a) database = False"
| "hasFunLabelInSUKLabel (SUIdKLabel a) database = False"
| "hasFunLabelInSUKLabel (SUKLabelFun x y) database = (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))"
| "hasFunLabelInSUKItem (SUKItem x y z) database = (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))"
| "hasFunLabelInSUKItem (SUIdKItem x y) database = False"
| "hasFunLabelInSUKItem (SUHOLE x) database = False"
| "hasFunLabelInSUKList [] database = False"
| "hasFunLabelInSUKList (a#l) database = (case a of ItemKl x \<Rightarrow> 
       hasFunLabelInSUBigKWithLabel x database \<or> hasFunLabelInSUKList l database
       | _ \<Rightarrow> hasFunLabelInSUKList l database)"
| "hasFunLabelInSUBigKWithBag (SUK a) database = hasFunLabelInSUK a database"
| "hasFunLabelInSUBigKWithBag (SUList a) database = hasFunLabelInSUList a database"
| "hasFunLabelInSUBigKWithBag (SUSet a) database = hasFunLabelInSUSet a database"
| "hasFunLabelInSUBigKWithBag (SUMap a) database = hasFunLabelInSUMap a database"
| "hasFunLabelInSUBigKWithBag (SUBag a) database = hasFunLabelInSUBag a database"
| "hasFunLabelInSUBigKWithLabel (SUBigBag a) database = hasFunLabelInSUBigKWithBag a database"
| "hasFunLabelInSUBigKWithLabel (SUBigLabel a) database = hasFunLabelInSUKLabel a database"
| "hasFunLabelInSUK [] database = False"
| "hasFunLabelInSUK (a#l) database = (case a of ItemFactor x \<Rightarrow> 
       hasFunLabelInSUKItem x database \<or> hasFunLabelInSUK l database
       | SUKKItem x y z \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUK l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUK l database)"
| "hasFunLabelInSUList [] database = False"
| "hasFunLabelInSUList (a#l) database = (case a of ItemL x \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUList l database
       | SUListKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUList l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUList l database)"
| "hasFunLabelInSUSet [] database = False"
| "hasFunLabelInSUSet (a#l) database = (case a of ItemS x \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUSet l database
       | SUSetKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUSet l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUSet l database)"
| "hasFunLabelInSUMap [] database = False"
| "hasFunLabelInSUMap (a#l) database = (case a of ItemM x y \<Rightarrow> 
       hasFunLabelInSUK x database \<or> hasFunLabelInSUK y database \<or>
     hasFunLabelInSUMap l database
       | SUMapKItem x y \<Rightarrow> (hasFunLabelInSUKLabel x database \<or>
         hasFunLabelInSUKList y database \<or> hasFunLabelInSUMap l database \<or>
          (case getSUKLabelMeaning x of None \<Rightarrow> False
            | Some s \<Rightarrow> if isFunctionItem s database then True else False))
      | _ \<Rightarrow> hasFunLabelInSUMap l database)"
| "hasFunLabelInSUBag [] database = False"
| "hasFunLabelInSUBag (a#l) database = (case a of ItemB x y z \<Rightarrow> 
       hasFunLabelInSUBigKWithBag z database \<or> hasFunLabelInSUBag l database
       | _ \<Rightarrow> hasFunLabelInSUBag l database)"
by pat_completeness auto

termination sorry

function localteFunTermInSUKLabel
    and localteFunTermInSUKItem
    and localteFunTermInSUKList
    and localteFunTermInSUBigKWithBag
    and localteFunTermInSUBigKWithLabel
    and localteFunTermInSUK
    and localteFunTermInSUList
    and localteFunTermInSUSet
    and localteFunTermInSUMap
    and localteFunTermInSUBag where
"localteFunTermInSUKLabel (SUKLabel a) database = None"
| "localteFunTermInSUKLabel (SUIdKLabel a) database = None"
| "localteFunTermInSUKLabel (SUKLabelFun x y) database =
    (case localteFunTermInSUKLabel x database of None \<Rightarrow> 
      (case localteFunTermInSUKList y database of None \<Rightarrow> 
    (case getSUKLabelMeaning x of None \<Rightarrow> None
      | Some s \<Rightarrow> if isFunctionItem s database then
          Some (s, y, KLabelSort, SUIdKLabel FunHole) else None)
           | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKLabelFun x r))
          | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKLabelFun r y))"
| "localteFunTermInSUKItem (SUKItem x y z) database =
       (case localteFunTermInSUKLabel x database of None \<Rightarrow> 
      (case localteFunTermInSUKList y database of None \<Rightarrow> 
    (case getSUKLabelMeaning x of None \<Rightarrow> None
      | Some s \<Rightarrow> if isFunctionItem s database then
          Some (s, y, z, SUIdKItem FunHole z) else None)
           | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKItem x r z))
          | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUKItem r y z))"
| "localteFunTermInSUKItem (SUIdKItem x y) database = None"
| "localteFunTermInSUKItem (SUHOLE x) database = None"
| "localteFunTermInSUKList [] database = None"
| "localteFunTermInSUKList (a#l) database = (case a of ItemKl x \<Rightarrow>
       (case localteFunTermInSUBigKWithLabel x database
       of None \<Rightarrow> (case localteFunTermInSUKList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemKl r)#l))
       | _ \<Rightarrow> (case localteFunTermInSUKList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUBigKWithBag (SUK a) database = (case localteFunTermInSUK a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUK r))"
| "localteFunTermInSUBigKWithBag (SUList a) database = (case localteFunTermInSUList a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUList r))"
| "localteFunTermInSUBigKWithBag (SUSet a) database = (case localteFunTermInSUSet a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUSet r))"
| "localteFunTermInSUBigKWithBag (SUMap a) database = (case localteFunTermInSUMap a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUMap r))"
| "localteFunTermInSUBigKWithBag (SUBag a) database = (case localteFunTermInSUBag a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBag r))"
| "localteFunTermInSUBigKWithLabel (SUBigBag a) database =
      (case localteFunTermInSUBigKWithBag a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBigBag r))"
| "localteFunTermInSUBigKWithLabel (SUBigLabel a) database =
          (case localteFunTermInSUKLabel a database of
    None \<Rightarrow> None | Some (l, fun,ty, r) \<Rightarrow> Some (l, fun,ty, SUBigLabel r))"
| "localteFunTermInSUK [] database = None"
| "localteFunTermInSUK (a#l) database = (case a of ItemFactor x \<Rightarrow> 
      (case localteFunTermInSUKItem x database of None \<Rightarrow>
        (case localteFunTermInSUK l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemFactor r)#l))
       | SUKKItem x y z \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUK l database of None \<Rightarrow> 
            (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,z, (if z = K then IdFactor FunHole else ItemFactor (SUIdKItem (FunHole) z))#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUKKItem x r z)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUKKItem r y z)#l))
      | _ \<Rightarrow> (case localteFunTermInSUK l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUList [] database = None"
| "localteFunTermInSUList (a#l) database = (case a of ItemL x \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
        (case localteFunTermInSUList l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemL r)#l))
       | SUListKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUList l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,List, (IdL FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUListKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUListKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUList l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun, ty,a#r)))"
| "localteFunTermInSUSet [] database = None"
| "localteFunTermInSUSet (a#l) database = (case a of ItemS x \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
        (case localteFunTermInSUSet l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemS r)#l))
       | SUSetKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUSet l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,Set, (IdS FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUSetKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUSetKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUSet l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUMap [] database = None"
| "localteFunTermInSUMap (a#l) database = (case a of ItemM x y \<Rightarrow> 
      (case localteFunTermInSUK x database of None \<Rightarrow>
      (case localteFunTermInSUK y database of None \<Rightarrow>
        (case localteFunTermInSUMap l database of None \<Rightarrow> None
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemM x r)#l))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun, ty,(ItemM r y)#l))
       | SUMapKItem x y \<Rightarrow>
       (case localteFunTermInSUKLabel x database of None \<Rightarrow>
        (case localteFunTermInSUKList y database of None \<Rightarrow>
       (case localteFunTermInSUMap l database of None \<Rightarrow>
        (case getSUKLabelMeaning x of None \<Rightarrow> None
          | Some s \<Rightarrow> if isFunctionItem s database then
            Some (s, y,Map, (IdM FunHole)#l)
              else None)
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
          | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUMapKItem x r)#l))
        | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (SUMapKItem r y)#l))
      | _ \<Rightarrow> (case localteFunTermInSUMap l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
| "localteFunTermInSUBag [] database = None"
| "localteFunTermInSUBag (a#l) database = (case a of ItemB x y z \<Rightarrow>
       (case localteFunTermInSUBigKWithBag z database
       of None \<Rightarrow> (case localteFunTermInSUBag l database of None \<Rightarrow> None
         | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, a#r))
       | Some (la, fun,ty, r) \<Rightarrow> Some (la, fun,ty, (ItemB x y r)#l))
       | _ \<Rightarrow> (case localteFunTermInSUBag l database of None \<Rightarrow> None
         | Some (la, fun, ty, r) \<Rightarrow> Some (la, fun,ty, a#r)))"
by pat_completeness auto

termination sorry

fun getFunRules :: "('upVar, 'var, 'metaVar) rulePat list
                   \<Rightarrow> ('upVar, 'var, 'metaVar) rulePat list" where
"getFunRules [] = []"
| "getFunRules ((FunPat s fl f)#l) = (FunPat s fl f)#(getFunRules l)"
| "getFunRules (x#l) = getFunRules l"

fun getRidOfLabel where
"getRidOfLabel [] = Some []"
| "getRidOfLabel ((KLabelFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((KFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((KItemFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((ListFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((SetFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((MapFunPat s kl,b,c)#l) = (case getRidOfLabel l of None \<Rightarrow> None
       | Some l' \<Rightarrow> Some ((kl,b,c)#l'))"
| "getRidOfLabel ((NormalPat a,b,c)#l) = None"

fun getFunRule where
"getFunRule s [] = None"
| "getFunRule s ((FunPat s' fl f)#l) = (if s = s' then
    (case f of None \<Rightarrow> getRidOfLabel fl 
       | Some f' \<Rightarrow> getRidOfLabel (fl@[f'])) else getFunRule s l)"
| "getFunRule s (x#l) = getFunRule s l"

(* function rule evaluations. Evaluating the boolean predicate first. 
    type of allRules: ('labelName, 'cellName, 'metaVar) rulePat list
    type of database:  target-sort \<times> arg-sorts \<times> symbol name or symbol name set
                        \<times> synAttrib list this is the syntactic attributes
                         \<times> bool a boolean value indicating if the entry is a function label
    type of subG: a Directed acyclic graph  of relations on sorts determining subsorting relations. 
         *)
inductive funEvaluationBool and funEvaluationBoolAux where
 conZeroStep : " \<not> hasFunLabelInSUKItem C database
    \<Longrightarrow> funEvaluationBool allRules database subG (Continue C) (Stop C)"
| conOneStep : "\<lbrakk> hasFunLabelInSUKItem C database ;
    localteFunTermInSUKItem C database = Some (l, fun, ty, Cr); getFunRule l allRules = Some fl;
          funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C');
       funEvaluationBool allRules database subG (Continue C') (Stop C'') \<rbrakk>
        \<Longrightarrow> funEvaluationBool allRules database subG (Continue C) (Stop C'')"
| emptyRule : "funEvaluationBoolAux allRules database subG [] fun (Continue Cr) (Div Cr)"
| noPatRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = None ;
   funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C') \<rbrakk>
         \<Longrightarrow> funEvaluationBoolAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Cr) (Stop C')"
| falseRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
   funEvaluationBoolAux allRules database subG fl fun (Continue Cr) (Stop C') \<rbrakk>
         \<Longrightarrow> funEvaluationBoolAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Cr) (Stop C')"
| trueRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSubsFactor r acc = Some r' ; substitutionInSUKItem Cr [(FunHole, r')] = Some C';
     typeCheckCondition C' database subG = Some C'' \<rbrakk> 
                \<Longrightarrow> funEvaluationBoolAux allRules database subG
       ((p,r,c)#l) fun (Continue Cr) (Stop C'')"

code_pred funEvaluationBool .
code_pred funEvaluationBoolAux .

inductive funEvaluation
    and funEvaluationAux
where
 conZeroStep : " \<not> hasFunLabelInSUBag B database
                 \<Longrightarrow> funEvaluation allRules database subG (Continue B) (Stop B)"
| conOneStep : "\<lbrakk> hasFunLabelInSUBag B database ;
    localteFunTermInSUBag B database = Some (l, fun, ty, Br); getFunRule l allRules = Some fl;
          funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B');
       funEvaluation allRules database subG (Continue B') (Stop B'') \<rbrakk>
        \<Longrightarrow> funEvaluation allRules database subG (Continue B) (Stop B'')"
| emptyRule : "funEvaluationAux allRules database subG [] fun (Continue Br) (Div Br)"
| noPatRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = None ;
   funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B') \<rbrakk>
         \<Longrightarrow> funEvaluationAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Br) (Stop B')"
| falseRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
   funEvaluationAux allRules database subG fl fun (Continue Br) (Stop B') \<rbrakk>
         \<Longrightarrow> funEvaluationAux allRules database subG
                               ((p,r,c)#fl) fun (Continue Br) (Stop B')"
| trueRule : "\<lbrakk> patternMacroingInSUKList p fun [] subG = Some acc ;
   substitutionInSUKItem c acc  = Some value ;
   funEvaluationBool allRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSubsFactor r acc = Some r' ; substitutionInSUBag Br [(FunHole, r')] = Some B';
     typeCheckProgramState B' database subG = Some B'' \<rbrakk> 
                \<Longrightarrow> funEvaluationAux allRules database subG
       ((p,r,c)#l) fun (Continue Br) (Stop B'')"

code_pred funEvaluation .
code_pred funEvaluationAux .

(* dealing with anywhere rules *)

fun getAnywhereRules where
"getAnywhereRules [] = []"
| "getAnywhereRules ((AnywherePat s pl right con)#l) =
                    (s, pl, right, con)#(getAnywhereRules l)"
| "getAnywhereRules (x#l) = getAnywhereRules l"

function applyAnywhereRuleInSUKItem
    and applyAnywhereRuleInSUKList
    and applyAnywhereRuleInSUBigKWithBag
    and applyAnywhereRuleInSUBigKWithLabel
    and applyAnywhereRuleInSUK
    and applyAnywhereRuleInSUList
    and applyAnywhereRuleInSUSet
    and applyAnywhereRuleInSUMap
    and applyAnywhereRuleInSUBag where
"applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUKItem l r ty) = (case getSUKLabelMeaning l of None \<Rightarrow> None
      | Some s' \<Rightarrow> (if isFunctionItem s' database then None else
    (case applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) r of None \<Rightarrow> None
    | Some r' \<Rightarrow> if r = r' then (if s = s' then 
         (case patternMacroingInSUKList kl r [] subG of None \<Rightarrow>
        Some [ItemFactor (SUKItem l r ty)] | Some acc \<Rightarrow>
      (case substitutionInSUKItem con acc of None \<Rightarrow> Some [ItemFactor (SUKItem l r ty)]
       | Some value \<Rightarrow> (if funEvaluationBool allRules database subG
       (Continue value) (Stop (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] Bool))
        then (case substitutionInSUK t acc of None \<Rightarrow> Some [ItemFactor (SUKItem l r ty)]
          | Some t' \<Rightarrow> Some t') else Some [ItemFactor (SUKItem l r ty)])))
         else Some [ItemFactor (SUKItem l r ty)]) else Some [ItemFactor (SUKItem l r' ty)])))"
| "applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUIdKItem x ty) = None"
| "applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) (SUHOLE ty) = Some [ItemFactor (SUHOLE ty)]"
| "applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) (a#l) = (case a of IdKl x \<Rightarrow> None
         | ItemKl x \<Rightarrow> (case applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUKList allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemKl x')#l'))))"
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUK a) = (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUK a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUList a) = (case applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUList a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUSet a) = (case applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUSet a')) "
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUMap a) = (case applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUMap a'))"
| "applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) (SUBag a) = (case applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUBag a'))"
| "applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) (SUBigBag a) = (case applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) a of None \<Rightarrow> None
        | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "applyAnywhereRuleInSUBigKWithLabel allRules database subG
          (s, kl, t, con) (SUBigLabel a) = Some (SUBigLabel a)"
| "applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemFactor x \<Rightarrow>
        (case applyAnywhereRuleInSUKItem allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some (x'@l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemL x \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUList allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemL x')#l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemS x \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUSet allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemS x')#l')))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemM x y \<Rightarrow>
        (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) x of None \<Rightarrow> None
       | Some x' \<Rightarrow> (case applyAnywhereRuleInSUK allRules database subG
          (s, kl, t, con) y of None \<Rightarrow> None
       | Some y' \<Rightarrow> (case applyAnywhereRuleInSUMap allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemM x' y')#l'))))
     | _ \<Rightarrow> None)"
| "applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) [] = Some []"
| "applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) (a#l) = (case a of ItemB x y z \<Rightarrow>
        (case applyAnywhereRuleInSUBigKWithBag allRules database subG
          (s, kl, t, con) z of None \<Rightarrow> None
       | Some z' \<Rightarrow> (case applyAnywhereRuleInSUBag allRules database subG
          (s, kl, t, con) l of None \<Rightarrow> None
        | Some l' \<Rightarrow> Some ((ItemB x y z')#l')))
     | _ \<Rightarrow> None)"
by pat_completeness auto

termination sorry

fun applyAnywhereRules :: "('m, 'n, 'o) rulePat list
     ⇒ ('m kSyntax.sort × 'm kSyntax.sort list × 'm label KItemSyntax × 'p × bool) list
        ⇒ ('m kSyntax.sort × 'm kSyntax.sort list) list
           ⇒ ('m label × ('m, 'n, 'o) irKList × ('m, 'n, 'o) suKFactor list
     × ('m, 'n, 'o) suKItem) list
            ⇒ ('m, 'n, 'o) suB list ⇒ ('m, 'n, 'o) suB list option" where
"applyAnywhereRules allRules database subG [] B = Some B"
| "applyAnywhereRules allRules database subG (f#fl) B =
    (case applyAnywhereRuleInSUBag allRules database subG f B
    of None \<Rightarrow> None | Some B' \<Rightarrow> 
       if B = B' then applyAnywhereRules allRules database subG fl B
      else Some B')"

inductive funAnywhere where
zeroStep : "\<lbrakk> funEvaluation allFunRules database subG (Continue B) (Stop B');
            applyAnywhereRules allFunRules database subG anywheres B' = Some B' \<rbrakk>
       \<Longrightarrow> funAnywhere allFunRules anywheres database subG (Continue B) (Stop B')"
| oneStep : "\<lbrakk> funEvaluation allFunRules database subG (Continue B) (Stop B');
            applyAnywhereRules allFunRules database subG anywheres B' = Some B'';
   B \<noteq> B'';  funAnywhere allFunRules anywheres database subG (Continue B'') (Stop B''') \<rbrakk>
       \<Longrightarrow> funAnywhere allFunRules anywheres database subG (Continue B) (Stop B''')"

code_pred funAnywhere .

(* define K cell rule and bag rule *)
fun getAllKCells and getAllKCellsAux where
"getAllKCells [] = Some []"
| "getAllKCells ((IdB x)#l) = None"
| "getAllKCells ((ItemB x y z)#l) = (if x = littleK then (case z of SUK a \<Rightarrow>
                (case (getAllKCells l) of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some (a#l')) | _ \<Rightarrow> None)
                   else (case getAllKCellsAux z of None \<Rightarrow> None
           | Some z' \<Rightarrow> (case  getAllKCells l of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some (z'@l'))))"
| "getAllKCellsAux (SUBag a) = getAllKCells a"
| "getAllKCellsAux a = Some []"

fun replaceKCells
   and replaceKCellsAux where
"replaceKCells [] t r = Some []"
| "replaceKCells ((IdB x)#l) t r = None"
| "replaceKCells ((ItemB x y z)#l) t r = (if x = littleK then (case z of SUK a \<Rightarrow>
                (case (replaceKCells l t r) of None \<Rightarrow> None
           | Some l' \<Rightarrow> if a = t then Some ((ItemB x y (SUK r))#l')
             else Some ((ItemB x y z)#l')) | _ \<Rightarrow> None)
                   else (case replaceKCellsAux z t r of None \<Rightarrow> None
           | Some z' \<Rightarrow> (case  replaceKCells l t r of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some ((ItemB x y z')#l'))))"
| "replaceKCellsAux (SUBag a) t r = (case replaceKCells a t r of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (SUBag a'))"
| "replaceKCellsAux a t r = Some a"

fun getAllKRules where
"getAllKRules [] = []"
| "getAllKRules ((KRulePat a b c d)#l) = (a,b,c,d)#(getAllKRules l)"
| "getAllKRules (x#l) = getAllKRules l"

fun getAllBagRules where
"getAllBagRules [] = []"
| "getAllBagRules ((BagRulePat a b c d)#l) = (a,b,c,d)#(getAllBagRules l)"
| "getAllBagRules (x#l) = getAllBagRules l"

inductive oneStepKRuleAux where
zeroStep : "oneStepKRuleAux allFunRules database subG [] (Continue C) (Stop C)"
| noPatRule : "\<lbrakk> patternMacroingInSUK p C [] subG = None;
      oneStepKRuleAux allFunRules database subG fl (Continue C) (Stop C') \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop C')"
| falseRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneStepKRuleAux allFunRules database subG fl (Continue C) (Stop C') \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop C')"
| trueRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUK r acc = Some r' \<rbrakk>
    \<Longrightarrow> oneStepKRuleAux allFunRules database subG ((p,r,con,l)#fl) (Continue C) (Stop r')"

code_pred oneStepKRuleAux .

inductive oneStepKRule where
zeroStep : "oneStepKRule allFunRules database subG allKRule [] None"
| failStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C);
   oneStepKRule allFunRules database subG allKRule l S \<rbrakk>
     \<Longrightarrow> oneStepKRule allFunRules database subG allKRule (C#l) S"
| oneStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C');
      C \<noteq> C' \<rbrakk>
     \<Longrightarrow> oneStepKRule allFunRules database subG allKRule (C#l) (Some (C,C'))"

code_pred oneStepKRule .

inductive oneStepBagRule where
zeroStep : "oneStepBagRule allFunRules database subG [] (Continue B) (Stop B)"
| noPatRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = None;
      oneStepBagRule allFunRules database subG fl (Continue B) (Stop B') \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop B')"
| falseRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneStepBagRule allFunRules database subG fl (Continue B) (Stop B') \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop B')"
| trueRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUBag r acc = Some r' \<rbrakk>
    \<Longrightarrow> oneStepBagRule allFunRules database subG ((p,r,con,l)#fl) (Continue B) (Stop r')"

code_pred oneStepBagRule .

(* defining K compile: compilation and checking process of K theory 
definition kcompile :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
   ⇒ (('upVar, 'var, 'acapvar, 'metaVar) kFile × ('upVar kSyntax.sort × 'upVar kSyntax.sort list ×
          'upVar label KItemSyntax × 'var synAttrib list × bool) list
    × ('upVar kSyntax.sort × 'upVar kSyntax.sort list) list × ('upVar, 'var, 'metaVar) suB list
    × ('upVar, 'var, 'metaVar) rulePat list, char list) oneStep" where
"kcompile Theory = (case syntaxSetToKItemTest Theory of None \<Rightarrow> 
         Failure (''Not a valid K theory.'') | Some database \<Rightarrow>
    if invalidSortChecks Theory then (if uniqueKLabelSyntax Theory
       then (if validSyntaxSort Theory database then
     (case subsortGraph Theory of subG \<Rightarrow>
     (case configurationTest Theory database subG of None
               \<Rightarrow> Failure (''The configuration is not valid.'')
        | Some confi \<Rightarrow> (case typeCheckRules Theory database subG of None \<Rightarrow>
            Failure (''The theory has invalid rules.'')
    | Some allRules \<Rightarrow> (case strictRuleTest Theory of None \<Rightarrow>
            Failure (''The theory has invalid strict attributes.'')
        | Some stl \<Rightarrow>
            Success (Theory,database,subG,confi,allRules@stl)))))
        else Failure (''K theory has invalid syntax or strict attributes failed.''))
     else Failure (''kLabels are not uniquely defined in this K theory.''))
         else Failure (''K theory has invalid subsort.''))"
*)

(* defining K Run *)
inductive krunAux where
zeroStep : "funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B')
           \<Longrightarrow> krunAux database subG (0::nat)
                      allFunRules allAnywheres allKRules allBagRules B B'"
| noStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl None;
    oneStepBagRule allFunRules database subG allBagRules (Continue B') (Stop B') \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B B'"
| kStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl (Some (C,C'));
     replaceKCells B' C C' = Some B''; typeCheckProgramState B'' database subG = Some Ba; n > 0;
     krunAux database subG (n - 1) allFunRules allAnywheres allKRules allBagRules Ba Bb \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B Bb"
| bagStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
    getAllKCells B' = Some cl; oneStepKRule allFunRules database subG allKRules cl None; n > 0;
    oneStepBagRule allFunRules database subG allBagRules (Continue B') (Stop B''); B' \<noteq> B'';
     typeCheckProgramState B'' database subG = Some Ba;
     krunAux database subG (n - 1) allFunRules allAnywheres allKRules allBagRules Ba Bb \<rbrakk>
    \<Longrightarrow> krunAux database subG n allFunRules allAnywheres allKRules allBagRules B Bb"

(*
code_pred krunAux .


inductive krun where
theoryFail : "kcompile Theory = Failure s \<Longrightarrow>
      krun Theory n l (Failure (''Bad result: ''@s))"
| programFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG, confi, allRules);
   realConfigurationTest l Theory database subG = None \<rbrakk>
   \<Longrightarrow> krun Theory n l (Failure ''Bad input program.'')"
| macroRuleFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
   applyAllMacroRulesCheck l Theory database subG = None \<rbrakk>
   \<Longrightarrow> krun Theory n l (Failure ''Macro rules have a problem.'')"
| goodRun : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
      applyAllMacroRulesCheck l Theory database subG = Some (noMacroRules, B);
    getFunRules noMacroRules = allFunRules; getAnywhereRules noMacroRules = allAnywheres;
    getAllKRules noMacroRules = allKRules; getAllBagRules noMacroRules = allBagRules;
     krunAux database subG n  allFunRules allAnywheres allKRules allBagRules B B' \<rbrakk>
\<Longrightarrow> krun Theory n l (Success B')"
*)
(*
code_pred krun .
*)

(* defining K search *)
fun divideAllKRules where
"divideAllKRules [] = ([],[])"
| "divideAllKRules ((KRulePat a b c d)#l) = (case divideAllKRules l of (left, right) \<Rightarrow>
       if d then ((a,b,c,d)#left,right) else (left,(a,b,c,d)#right))"
| "divideAllKRules (x#l) = divideAllKRules l"

fun divideAllBagRules where
"divideAllBagRules [] = ([],[])"
| "divideAllBagRules ((BagRulePat a b c d)#l) = (case divideAllBagRules l
     of (left, right) \<Rightarrow>
       if d then ((a,b,c,d)#left,right) else (left,(a,b,c,d)#right))"
| "divideAllBagRules (x#l) = divideAllBagRules l"

(* one step k rule in k search becomes collecting a list of results *)
inductive oneTransKRuleAux where
zeroStep : "oneTransKRuleAux allFunRules database subG [] C []"
| noPatRule : "\<lbrakk> patternMacroingInSUK p C [] subG = None;
      oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
             ((p,r,con,l)#fl) C Cl"
| falseRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
               ((p,r,con,l)#fl) C Cl"
| trueRule : "\<lbrakk> patternMacroingInSUK p C [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUK r acc = Some r';
   oneTransKRuleAux allFunRules database subG fl C Cl \<rbrakk>
    \<Longrightarrow> oneTransKRuleAux allFunRules database subG
           ((p,r,con,l)#fl) C (List.insert (C,r') Cl)"

(*
code_pred oneTransKRuleAux .
*)

inductive oneTransKRule where
zeroStep : "oneTransKRule allFunRules database subG allKRule transKRule [] []"
| oneStep : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C');
    C \<noteq> C'; oneTransKRule allFunRules database subG allKRule transKRule l Cl \<rbrakk>
     \<Longrightarrow> oneTransKRule allFunRules database subG allKRule transKRule
            (C#l) (List.insert (C,C') Cl)"
| oneTrans : "\<lbrakk> oneStepKRuleAux allFunRules database subG allKRule (Continue C) (Stop C);
      oneTransKRuleAux allFunRules database subG transKRule C Cl;
       oneTransKRule allFunRules database subG allKRule transKRule l Cl' \<rbrakk>
     \<Longrightarrow> oneTransKRule allFunRules database subG allKRule transKRule
            (C#l) (insertAll Cl Cl')"

code_pred oneTransKRule .

inductive oneTransBagRule where
zeroStep : "oneTransBagRule allFunRules database subG [] B []"
| noPatRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = None;
      oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG ((p,r,con,l)#fl) B Bl"
| falseRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst False));
      oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG ((p,r,con,l)#fl) B Bl"
| trueRule : "\<lbrakk> patternMacroingInSUBag p B [] subG = Some acc;
   substitutionInSUKItem con acc = Some value ;
   funEvaluationBool allFunRules database subG (Continue value) (Stop value');
   getKLabelInSUKItem value' = Some (ConstToLabel (BoolConst True));
   substitutionInSUBag r acc = Some r';
   oneTransBagRule allFunRules database subG fl B Bl \<rbrakk>
    \<Longrightarrow> oneTransBagRule allFunRules database subG
      ((p,r,con,l)#fl) B (List.insert r' Bl)"

code_pred oneTransBagRule .

fun replaceKCellsInList where
"replaceKCellsInList B [] = []"
| "replaceKCellsInList B ((a,b)#l) = (case replaceKCells B a b of None
      \<Rightarrow> replaceKCellsInList B l
   | Some B' \<Rightarrow>  List.insert B' (replaceKCellsInList B l))"

inductive oneTransKSearch where
zeroStep : "oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules tranBagRules [] []"
| oneBagStep : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B');
    B \<noteq> B'; oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Cl \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (List.insert B' Cl)"
| oneKTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl acc;
  replaceKCellsInList B acc = Bl; oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Bl' \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (insertAll Bl Bl')"
| oneBagTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl [];
  oneTransBagRule allFunRules database subG transBagRules B Bl;
  oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules l Bl' \<rbrakk>
     \<Longrightarrow> oneTransKSearch allFunRules database subG
            allKRules allBagRules transKRules transBagRules (B#l) (insertAll Bl Bl')"

code_pred oneTransKSearch .

inductive allAllFunAnywhere where
zeroStep : "allAllFunAnywhere allFunRules allAnywheres database subG [] []"
| oneStep : "\<lbrakk> funAnywhere allFunRules allAnywheres database subG (Continue B) (Stop B');
      allAllFunAnywhere allFunRules allAnywheres database subG l Bl \<rbrakk>
    \<Longrightarrow> 
    allAllFunAnywhere allFunRules allAnywheres database subG (B#l) (B'#Bl)"

code_pred allAllFunAnywhere .

(* defining K search *)
inductive ksearchAux where
zeroStep : "allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl'
           \<Longrightarrow> ksearchAux database subG (0::nat)
            allFunRules allAnywheres allKRules allBagRules transKRules transBagRules Bl Bl'"
| noStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKSearch allFunRules database subG allKRules allBagRules
         transKRules transBagRules Bl' [] \<rbrakk>
    \<Longrightarrow> ksearchAux database subG n
            allFunRules allAnywheres allKRules allBagRules transKRules transBagRules Bl []"
| oneStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKSearch allFunRules database subG allKRules allBagRules
         transKRules transBagRules Bl' Bl''; n > 0; length Bl'' > 0;
    ksearchAux database subG (n - 1) allFunRules
        allAnywheres allKRules allBagRules transKRules transBagRules Bl'' Bl''' \<rbrakk>
    \<Longrightarrow> ksearchAux database subG n allFunRules
        allAnywheres allKRules allBagRules transKRules transBagRules Bl Bl'''"

(*
code_pred ksearchAux .

inductive ksearch where
theoryFail : "kcompile Theory = Failure s \<Longrightarrow>
      ksearch Theory n l (Failure (''Bad result: ''@s))"
| programFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG, confi, allRules);
   realConfigurationTest l Theory database subG = None \<rbrakk>
   \<Longrightarrow> ksearch Theory n l (Failure ''Bad input program.'')"
| macroRuleFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
   applyAllMacroRulesCheck l Theory database subG = None \<rbrakk>
   \<Longrightarrow> ksearch Theory n l (Failure ''Macro rules have a problem.'')"
| goodRun : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
      applyAllMacroRulesCheck l Theory database subG = Some (noMacroRules, B);
    getFunRules noMacroRules = allFunRules; getAnywhereRules noMacroRules = allAnywheres;
    divideAllKRules noMacroRules = (transKRules,allKRules);
     divideAllBagRules noMacroRules = (transBagRules,allBagRules);
     ksearchAux database subG n  allFunRules allAnywheres allKRules
                  allBagRules transKRules transBagRules [B] Bl \<rbrakk>
\<Longrightarrow> ksearch Theory n l (Success Bl)"
*)
(*
code_pred ksearch .

export_code krun ksearch
  in OCaml
  module_name k file "k.ml"
*)

end