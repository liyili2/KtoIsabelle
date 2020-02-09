theory k
imports Main Real List kCompile
begin

(*
assume that the parser will remove the following cases and make K to KItem:

A:K \<leadsto> c ...  becomes A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> c ... becomes ... c \<leadsto> A:KItem \<leadsto> c ...

... c \<leadsto> A:K \<leadsto> B:K becomes c \<leadsto> A:KItem \<leadsto> B:K

hence, left vars do not apply on the K case.

*)

(* implementation of krun and ksearch *)

(* type check programs *)
definition typeCheckProgramState where
"typeCheckProgramState a database subG = (if isGroundTermInSUBag a
    then (case checkTermsInSUBag a [] [] database subG
          of None \<Rightarrow> None | Some (acc,beta,aa) \<Rightarrow>
        regularizeInSUBag aa subG) else None)"

definition typeCheckCondition where
"typeCheckCondition a database subG = (if isGroundTermInSUKItem a
    then (case checkTermsInSUKItem a [Bool] [] [] database subG
          of None \<Rightarrow> None | Some (acc,beta,aa) \<Rightarrow>
         regularizeInSUKItem aa subG) else None)"

definition validConfiguration where
"validConfiguration a = (case uniqueCellNameInSUBag a [] of None \<Rightarrow> False
     | _ \<Rightarrow> (noDotInSUBag a \<and> hasNoBagVarInSUBag a))"

(* check and get all macro rules *)
fun divideMacroRules where
"divideMacroRules [] subG = Some ([],[])"
| "divideMacroRules ((MacroPat x y z)#l) subG = (if subSyntaxInSUK x (irToSUInKList y) z subG
               then (case divideMacroRules l subG of None \<Rightarrow> None
                 | Some (l',S) \<Rightarrow> Some (Some (x,y,z)#l',S)) else None)"
| "divideMacroRules (x#l) subG = (case divideMacroRules l subG of None \<Rightarrow> None
       | Some (l', S)  \<Rightarrow> Some (l', x#S))"

(* type check all rules *)
definition typeCheckRules where
"typeCheckRules Theory database subG =
    (case normalizeRules (getAllRules Theory) Theory database subG of None \<Rightarrow> None
       | Some l \<Rightarrow> if wellFormRules l then
         inferTypesInRules l Theory database subG else None)"

(* check uniqueness of KLabel in a spec *)
definition uniqueKLabelSyntax where
"uniqueKLabelSyntax Theory = isUnitLabel (syntaxSetToKItemSet Theory)"

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
       (if bagContainsCellAux LittleK z then (case createInitStateAux z of None \<Rightarrow> None
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

(* checks needing to be made: 1, it is a ground term. 2, it is type checked *)
definition configurationTest where
"configurationTest Theory database subG = (case getConfiguration Theory of [a] \<Rightarrow>
        (case toSUInBag a of None \<Rightarrow> None | Some a' \<Rightarrow>
        if validConfiguration a' then 
       (case checkTermsInSUBag a' []
                  (constructSortMap (getDomainInSUBag a')) database subG of None \<Rightarrow> None
           | Some (acc,beta, akl) \<Rightarrow> if hasNoTop acc \<and> hasNoTop beta then
        (case replaceVarSortInSUBag akl acc beta subG of None \<Rightarrow> None
       | Some kla \<Rightarrow> regularizeInSUBag kla subG) else None) else None) | _ \<Rightarrow> None)"

definition realConfigurationTest where
"realConfigurationTest l Theory database subG 
    = (case getConfiguration Theory of [a] \<Rightarrow>
        (case toSUInBag a of None \<Rightarrow> None | Some a' \<Rightarrow>
        if validConfiguration a' then 
          (case composeConfiAndProgInSUBag a' l subG of None \<Rightarrow> None
             | Some aa \<Rightarrow>
         typeCheckProgramState aa database subG) else None))"

(*
(checkTermsInSUBag (irToSUInBag kl) [],
              checkTermsInSUBag r [], checkTermsInSUKItem c KItem [])
           of (Some (acckl, kl'), Some (accsl, sl'), Some (accz, z')) \<Rightarrow>
    (case (makeSortMap acckl, makeSortMap accsl, makeSortMap accz) of
        (Some acckl', Some accsl', Some accz') \<Rightarrow>
      (case (replaceVarSortInSUBag kl' acckl', replaceVarSortInSUBag sl' accsl',
      replaceVarSortInSUKItem z' accz') of (Some kla, Some sla, Some za) \<Rightarrow>
      (case (regularizeInSUBag kla *)

(* the pattern matching algorithm *)
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

fun updateMatchingMapMacro where
"updateMatchingMapMacro x y [] subG = Some [(x,y)]"
| "updateMatchingMapMacro x y ((a,b)#l) subG = (if x = a then
           (case macroEquality y b subG of None \<Rightarrow> None
               | Some y' \<Rightarrow> Some ((a,y')#l))
             else (case updateMatchingMapMacro x y l subG of None \<Rightarrow> None
                 | Some l' \<Rightarrow> Some ((a,b)#l')))"

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

fun mergePatMatchMap where
"mergePatMatchMap [] S subG = Some S"
| "mergePatMatchMap ((a,b)#l) S subG = (case updateMatchingMapMacro a b S subG
     of None \<Rightarrow> None | Some S' \<Rightarrow> mergePatMatchMap l S' subG)"

fun mergeMapWithOnes where
"mergeMapWithOnes [] acc subG = Some acc"
| "mergeMapWithOnes ((a,b,c)#l) acc subG =
    (case mergePatMatchMap c acc subG of None \<Rightarrow> None
       | Some acc' \<Rightarrow> mergeMapWithOnes l acc' subG)"

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
           = (updateMatchingMapMacro a (KLabelSubs S) acc subG)"
| "patternMacroingInSUKItem (IRKItem l r ty) S acc subG = (case S of (SUKItem l' r' ty') \<Rightarrow>
 (if subsortList ty' ty subG then
       (case patternMacroingInSUKLabel l l' acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow>
              (case patternMacroingInSUKList r r' acc' subG of None \<Rightarrow> None
          | Some acca \<Rightarrow> Some acca)) else None) | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRHOLE a) S acc subG = (case S of (SUHOLE a') \<Rightarrow>
     (if (subsortList a' a subG) then Some acc else None)
      | _ \<Rightarrow> None)"
| "patternMacroingInSUKItem (IRIdKItem a b) B acc subG = (case B of (SUIdKItem a' b')
         \<Rightarrow> (if subsortList b' b subG then
                updateMatchingMapMacro a (KItemSubs (SUIdKItem a' b')) acc subG
            else None)
       | (SUKItem l r ty) \<Rightarrow> (if subsortList ty b subG then
       updateMatchingMapMacro a (KItemSubs (SUKItem l r ty)) acc subG else None)
       | _ \<Rightarrow> None)"
| "patternMacroingInSUKList (KListPatNoVar l) S acc subG =
    (case l of [] \<Rightarrow> (case S of [] \<Rightarrow> Some acc | (sua#sul) \<Rightarrow> None)
        | la#ll \<Rightarrow> (case S of [] \<Rightarrow> None
          | (sua#sul) \<Rightarrow> (case sua of ItemKl x \<Rightarrow> 
          (case patternMacroingInSUBigKWithLabel la x acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> (case patternMacroingInSUKList (KListPatNoVar ll) sul acc' subG
           of None \<Rightarrow> None | Some acca \<Rightarrow> Some acca)) | _ \<Rightarrow> None)))"
| "patternMacroingInSUKList (KListPat l n r) S acc subG = (case l of [] \<Rightarrow>
     (case rev r of [] \<Rightarrow> (updateMatchingMapMacro n (KListSubs S) acc subG)
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
               | Some v \<Rightarrow> updateMatchingMapMacro v (KSubs S) acc subG)
          | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None
           | (sua#sul) \<Rightarrow> (case sua of ItemFactor x \<Rightarrow>
          (case patternMacroingInSUKItem la x acc subG of None \<Rightarrow> None
              | Some acc' \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG)
          | IdFactor x \<Rightarrow> (case la of (IRIdKItem x' ty) \<Rightarrow> 
            if ty = [K] then (case updateMatchingMapMacro x' (KSubs [(IdFactor x)]) acc subG
                 of None \<Rightarrow> None | Some acc'
                 \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
            | _ \<Rightarrow> None)
          | SUKKItem x y ty \<Rightarrow> (case la of (IRIdKItem x' ty') \<Rightarrow>
            if ty = [K] then (case updateMatchingMapMacro x' (KSubs [(SUKKItem x y ty)]) acc subG
            of None \<Rightarrow> None | Some acc'
                \<Rightarrow> patternMacroingInSUK (KPat ll n) sul acc' subG) else None
              |  _ \<Rightarrow> None))))"
| "patternMacroingInSUList (ListPatNoVar l) S acc subG = (case l of [] \<Rightarrow> 
       (case S of [] \<Rightarrow> Some acc | (sua#sul) \<Rightarrow> None)
      | (la#ll) \<Rightarrow> (case S of [] \<Rightarrow> None | (sua#sul) \<Rightarrow> 
         (case sua of ItemL x \<Rightarrow> (case patternMacroingInSUK la x acc subG of None \<Rightarrow> None
         | Some acc' \<Rightarrow> patternMacroingInSUList (ListPatNoVar ll) sul acc' subG)
      | _ \<Rightarrow> None)))"
| "patternMacroingInSUList (ListPat l n r) S acc subG = (case l of [] \<Rightarrow>
          (case rev r of [] \<Rightarrow>
           (updateMatchingMapMacro n (ListSubs S) acc subG)
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
   (case updateMatchingMapMacro var (SetSubs (rest@(keys remains))) acc subG of
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
   (case updateMatchingMapMacro var (MapSubs (rest@(keys remains))) acc subG of
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
   (case updateMatchingMapMacro var (BagSubs (rest@(keys remains))) acc subG of
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

(* dealing with macro rules *)
function applyMacroRuleInSUKLabel
    and applyMacroRuleInSUKItem
    and applyMacroRuleInSUKList
    and applyMacroRuleInSUBigKWithBag
    and applyMacroRuleInSUBigKWithLabel
    and applyMacroRuleInSUK
    and applyMacroRuleInSUList
    and applyMacroRuleInSUSet
    and applyMacroRuleInSUMap
    and applyMacroRuleInSUBag where
 "applyMacroRuleInSUKLabel s kl t (SUKLabel a) subG = Some (SUKLabel a)"
| "applyMacroRuleInSUKLabel s kl t (SUIdKLabel a) subG = Some (SUIdKLabel a)"
| "applyMacroRuleInSUKLabel s kl t (SUKLabelFun a b) subG =
     (case (applyMacroRuleInSUKLabel s kl t a subG, applyMacroRuleInSUKList s kl t b subG)
       of (Some a', Some b') \<Rightarrow> Some (SUKLabelFun a' b') | _ \<Rightarrow> None)"
| "applyMacroRuleInSUKItem s kl t (SUKItem l r ty) subG =
  (case (applyMacroRuleInSUKLabel s kl t l subG, applyMacroRuleInSUKList s kl t r subG)
       of (Some l', Some r') \<Rightarrow>
     (case getSUKLabelMeaning l' of None \<Rightarrow> Some [ItemFactor (SUKItem l' r' ty)]
         | Some ss \<Rightarrow> if s = ss then
    (case patternMacroingInSUKList kl r' [] subG of None \<Rightarrow>
          Some [ItemFactor (SUKItem l' r' ty)]
      | Some acc \<Rightarrow> (case substitutionInSUK t acc of None \<Rightarrow>
          Some [ItemFactor (SUKItem l' r' ty)]
        | Some t' \<Rightarrow> Some t'))
     else Some [ItemFactor (SUKItem l' r' ty)]))"
| "applyMacroRuleInSUKItem s kl t (SUHOLE a) subG = Some [ItemFactor (SUHOLE a)]"
| "applyMacroRuleInSUKItem s kl t (SUIdKItem a b) subG = Some [ItemFactor (SUIdKItem a b)]"
| "applyMacroRuleInSUKList s kl t [] subG = Some []"
| "applyMacroRuleInSUKList s kl t (b#l) subG = (case b of IdKl x \<Rightarrow>
         (case applyMacroRuleInSUKList s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemKl x \<Rightarrow>
         (case (applyMacroRuleInSUBigKWithLabel s kl t x subG, applyMacroRuleInSUKList s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemKl x')#l') | _ \<Rightarrow> None))"
| "applyMacroRuleInSUK s kl t [] subG = Some []"
| "applyMacroRuleInSUK s kl t  (b#l) subG = (case b of IdFactor x \<Rightarrow>
         (case applyMacroRuleInSUK s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemFactor x \<Rightarrow>
       (case (applyMacroRuleInSUKItem s kl t x subG, applyMacroRuleInSUK s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some (x'@l') | _ \<Rightarrow> None)
    | SUKKItem x y ty \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUK s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUKKItem x' y' ty)#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUList s kl t [] subG = Some []"
| "applyMacroRuleInSUList s kl t (b#l) subG = (case b of IdL x \<Rightarrow>
         (case applyMacroRuleInSUList s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemL x \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUList s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemL x')#l') | _ \<Rightarrow> None)
    | SUListKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUList s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUListKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUSet s kl t [] subG = Some []"
| "applyMacroRuleInSUSet s kl t (b#l) subG = (case b of IdS x \<Rightarrow>
         (case applyMacroRuleInSUSet s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemS x \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUSet s kl t l subG)
          of (Some x', Some l') \<Rightarrow> Some ((ItemS x')#l') | _ \<Rightarrow> None)
    | SUSetKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUSet s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUSetKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUMap s kl t [] subG = Some []"
| "applyMacroRuleInSUMap s kl t (b#l) subG = (case b of IdM x \<Rightarrow>
         (case applyMacroRuleInSUMap s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemM x y \<Rightarrow>
       (case (applyMacroRuleInSUK s kl t x subG, applyMacroRuleInSUK s kl t x subG, 
             applyMacroRuleInSUMap s kl t l subG)
          of (Some x', Some y', Some l')
            \<Rightarrow> Some ((ItemM x' y')#l') | _ \<Rightarrow> None)
    | SUMapKItem x y \<Rightarrow> (case (applyMacroRuleInSUKLabel s kl t x subG,
       applyMacroRuleInSUKList s kl t y subG, applyMacroRuleInSUMap s kl t l subG)
            of (Some x', Some y', Some l') \<Rightarrow> Some ((SUMapKItem x' y')#l')
              | _ \<Rightarrow> None))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUK a) subG = (case applyMacroRuleInSUK  s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUK a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUList a) subG = (case applyMacroRuleInSUList s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUList a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUSet a) subG = (case applyMacroRuleInSUSet s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUSet a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUMap a) subG = (case applyMacroRuleInSUMap s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUMap a'))"
| "applyMacroRuleInSUBigKWithBag s kl t (SUBag a) subG = (case applyMacroRuleInSUBag s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBag a'))"
| "applyMacroRuleInSUBigKWithLabel s kl t (SUBigBag a) subG =
     (case applyMacroRuleInSUBigKWithBag s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigBag a'))"
| "applyMacroRuleInSUBigKWithLabel s kl t (SUBigLabel a) subG =
     (case applyMacroRuleInSUKLabel s kl t a subG of
     None \<Rightarrow> None | Some a' \<Rightarrow> Some (SUBigLabel a'))"
| "applyMacroRuleInSUBag s kl t [] subG = Some []"
| "applyMacroRuleInSUBag s kl t (b#l) subG =  (case b of IdB x \<Rightarrow>
         (case applyMacroRuleInSUBag s kl t l subG of None \<Rightarrow> None
             | Some l' \<Rightarrow> Some (b#l'))
    | ItemB x y z \<Rightarrow>
         (case (applyMacroRuleInSUBigKWithBag s kl t z subG, applyMacroRuleInSUBag s kl t l subG)
          of (Some z', Some l') \<Rightarrow> Some ((ItemB x y z')#l') | _ \<Rightarrow> None))"
by pat_completeness auto

termination sorry

primrec applyMacroRuleInSubsFactor where
"applyMacroRuleInSubsFactor s kl t (KLabelSubs a) subG =
       (case applyMacroRuleInSUKLabel s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KLabelSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KItemSubs a) subG =
       (case applyMacroRuleInSUKItem s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KListSubs a) subG =
       (case applyMacroRuleInSUKList s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KListSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (KSubs a) subG =
       (case applyMacroRuleInSUK s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (KSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (ListSubs a) subG =
       (case applyMacroRuleInSUList s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (ListSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (SetSubs a) subG =
       (case applyMacroRuleInSUSet s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (SetSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (MapSubs a) subG =
       (case applyMacroRuleInSUMap s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (MapSubs a'))"
| "applyMacroRuleInSubsFactor s kl t (BagSubs a) subG =
       (case applyMacroRuleInSUBag s kl t a subG of None \<Rightarrow> None
           | Some a' \<Rightarrow> Some (BagSubs a'))"

primrec applyMacroRulesInFun ::
    "'a label
      \<Rightarrow> ('a, 'b, 'c) irKList
         \<Rightarrow> ('a, 'b, 'c) suKFactor list
            \<Rightarrow> (('a, 'b, 'c) pat \<times> ('a, 'b, 'c) subsFactor \<times> ('a, 'b, 'c) suKItem) list
               \<Rightarrow> ('a kSyntax.sort list \<times> 'a kSyntax.sort list list
          \<times> 'a label KItemSyntax \<times> 'e \<times> bool) list
                  \<Rightarrow> ('a kSyntax.sort \<times> 'a kSyntax.sort list) list
     \<Rightarrow> (('a, 'b, 'c) pat \<times> ('a, 'b, 'c) subsFactor \<times> ('a, 'b, 'c) suKItem) list option"where
"applyMacroRulesInFun s kl t [] database subG = Some []"
| "applyMacroRulesInFun s kl t (b#l) database subG = (case b of (u,v,w) \<Rightarrow>
       (case (applyMacroRuleInSubsFactor s kl t (irToSUInPat u database) subG,
             applyMacroRuleInSubsFactor s kl t v subG,
                       applyMacroRuleInSUKItem s kl t w subG)
      of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
       (case suToIRInSubsFactor u' database of None \<Rightarrow> None
           | Some ua \<Rightarrow> (case applyMacroRulesInFun s kl t l database subG of
              None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((ua,v',w')#l'))) | _ \<Rightarrow> None))"

fun applyMacroRules :: "'a label
     \<Rightarrow> ('a, 'b, 'c) irKList
        \<Rightarrow> ('a, 'b, 'c) suKFactor list
           \<Rightarrow> ('a, 'b, 'c) rulePat list
              \<Rightarrow> ('a kSyntax.sort list \<times> 'a kSyntax.sort list list
             \<times> 'a label KItemSyntax \<times> 'e \<times> bool) list
                 \<Rightarrow> ('a kSyntax.sort \<times> 'a kSyntax.sort list) list
           \<Rightarrow> ('a, 'b, 'c) rulePat list option" where
"applyMacroRules s kl t [] database subG = Some []"
| "applyMacroRules s kl t ((FunPat ss L ow)#l) database subG =
         (case applyMacroRulesInFun s kl t L database subG of None \<Rightarrow> None
           | Some L' \<Rightarrow> (case ow of None \<Rightarrow>
            (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> Some ((FunPat ss L' ow)#l'))
               | Some q \<Rightarrow>
           (case applyMacroRulesInFun s kl t [q] database subG of None \<Rightarrow> None
                 | Some [q'] \<Rightarrow>
             (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
                | Some l' \<Rightarrow> Some ((FunPat ss L' (Some q'))#l')))))"
| "applyMacroRules s kl t ((MacroPat ss kl' t')#l) database subG =
      (case getSort ss database of None \<Rightarrow> None
          | Some ty \<Rightarrow> 
      (case (applyMacroRuleInSUKItem s kl t (SUKItem (SUKLabel ss) (irToSUInKList kl') ty) subG,
              applyMacroRuleInSUK s kl t t' subG) of (Some mla, Some ta) \<Rightarrow>
    (case suToIRInK mla database of None \<Rightarrow> None
     | Some (NormalPat (KMatching (KPat [IRKItem (IRKLabel ss') kla ty'] None))) \<Rightarrow>
         (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
           | Some l' \<Rightarrow> Some ((MacroPat ss' kla ta)#l')) | _ \<Rightarrow> None)))"
| "applyMacroRules s kl t ((AnywherePat ss u v w)#l) database subG =
    (case (applyMacroRuleInSUKList s kl t (irToSUInKList u) subG, applyMacroRuleInSUK s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInKList u' database of Some ua
          \<Rightarrow> (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((AnywherePat ss ua v' w')#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "applyMacroRules s kl t ((KRulePat u v w tb)#l) database subG =
    (case (applyMacroRuleInSUK s kl t (irToSUInK u) subG, applyMacroRuleInSUK s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInK u' database of Some (NormalPat (KMatching ua)) \<Rightarrow>
           (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((KRulePat ua v' w' tb)#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"
| "applyMacroRules s kl t ((BagRulePat u v w tb)#l) database subG =
    (case (applyMacroRuleInSUBag s kl t (irToSUInBag u) subG, applyMacroRuleInSUBag s kl t v subG,
     applyMacroRuleInSUKItem s kl t w subG) of (Some u', Some v', Some [ItemFactor w']) \<Rightarrow>
    (case suToIRInBag u' database of Some ua \<Rightarrow>
           (case applyMacroRules s kl t l database subG of None \<Rightarrow> None
          | Some l' \<Rightarrow> Some ((BagRulePat ua v' w' tb)#l'))
            | _ \<Rightarrow> None) | _ \<Rightarrow> None)"

fun applyAllMacroRulesInList where
"applyAllMacroRulesInList [] L confi database subG = (case L of None \<Rightarrow> None
       | Some L' \<Rightarrow> Some (L', confi))"
| "applyAllMacroRulesInList (b#l) L confi database subG =
      (case (b,L) of (Some (x,y,z), Some L') \<Rightarrow>
    (case applyMacroRuleInSUBag x y z confi subG of None \<Rightarrow> None
          | Some confi' \<Rightarrow>
        applyAllMacroRulesInList (List.map (\<lambda> t . (case t of None \<Rightarrow> None
            | Some (a,b,c) \<Rightarrow>
               (case applyMacroRules x y z [MacroPat a b c] database subG of 
           Some [MacroPat a' b' c'] \<Rightarrow> Some (a',b',c') | _ \<Rightarrow> None))) l)
        (applyMacroRules x y z L' database subG) confi' database subG) | _ \<Rightarrow> None)"

fun adjustKSortsInIRKItem
  and adjustKSortsInIRBigKWithBag
  and adjustKSortsInIRBigKWithLabel
  and adjustKSortsInIRK
  and adjustKSortsInIRKList
  and adjustKSortsInIRList
  and adjustKSortsInIRSet
  and adjustKSortsInIRMap
  and adjustKSortsInIRBag where
"adjustKSortsInIRKItem (IRKItem a b ty ) = (IRKItem a (adjustKSortsInIRKList b) ty)"
| "adjustKSortsInIRKItem (IRIdKItem a ty) = IRIdKItem a ty"
| "adjustKSortsInIRKItem (IRHOLE ty) = (IRHOLE ty)"
| "adjustKSortsInIRBigKWithBag (IRK a) = IRK (adjustKSortsInIRK a)"
| "adjustKSortsInIRBigKWithBag (IRList a) = IRList (adjustKSortsInIRList a)"
| "adjustKSortsInIRBigKWithBag (IRSet a) = IRSet (adjustKSortsInIRSet a)"
| "adjustKSortsInIRBigKWithBag (IRMap a) = IRMap (adjustKSortsInIRMap a)"
| "adjustKSortsInIRBigKWithBag (IRBag a) = IRBag (adjustKSortsInIRBag a)"
| "adjustKSortsInIRBigKWithLabel (IRBigBag a) = IRBigBag (adjustKSortsInIRBigKWithBag a)"
| "adjustKSortsInIRBigKWithLabel (IRBigLabel a) = (IRBigLabel a)"
| "adjustKSortsInIRK (KPat [] b) = (KPat [] b)"
| "adjustKSortsInIRK (KPat (x#l) b) = (case adjustKSortsInIRK (KPat l b) of 
          (KPat l' b') \<Rightarrow> (case x of (IRIdKItem a [K]) \<Rightarrow> 
            KPat ((IRIdKItem a [KItem])#l') b' | _ \<Rightarrow> (KPat (x#l') b')))"
| "adjustKSortsInIRKList (KListPatNoVar l) = (case l of [] \<Rightarrow> KListPatNoVar []
        | la#ll \<Rightarrow> (case adjustKSortsInIRKList (KListPatNoVar ll) of (KListPatNoVar ll') 
          \<Rightarrow> (KListPatNoVar ((adjustKSortsInIRBigKWithLabel la)#ll'))
           | _ \<Rightarrow> KListPatNoVar l))"
| "adjustKSortsInIRKList (KListPat [] y []) = (KListPat [] y [])"
|  "adjustKSortsInIRKList (KListPat [] y (x#l)) = 
     (case adjustKSortsInIRKList (KListPat [] y l) of (KListPat [] y' l')
        \<Rightarrow>  (KListPat [] y' ((adjustKSortsInIRBigKWithLabel x)#l'))
       | _ \<Rightarrow> (KListPat [] y (x#l)))"
|  "adjustKSortsInIRKList (KListPat (x#l) y S) = 
     (case adjustKSortsInIRKList (KListPat l y S) of (KListPat l' y' S')
        \<Rightarrow>  (KListPat ((adjustKSortsInIRBigKWithLabel x)#l') y' S')
       | _ \<Rightarrow> (KListPat (x#l) y S))"
| "adjustKSortsInIRList (ListPatNoVar l) = (case l of [] \<Rightarrow> ListPatNoVar []
        | la#ll \<Rightarrow> (case adjustKSortsInIRList (ListPatNoVar ll) of (ListPatNoVar ll') 
          \<Rightarrow> (ListPatNoVar ((adjustKSortsInIRK la)#ll'))
           | _ \<Rightarrow> ListPatNoVar l))"
| "adjustKSortsInIRList (ListPat [] y []) = (ListPat [] y [])"
|  "adjustKSortsInIRList (ListPat [] y (x#l)) = 
     (case adjustKSortsInIRList (ListPat [] y l) of (ListPat [] y' l')
        \<Rightarrow>  (ListPat [] y' ((adjustKSortsInIRK x)#l'))
       | _ \<Rightarrow> (ListPat [] y (x#l)))"
| "adjustKSortsInIRList (ListPat (x#l) y S) = 
     (case adjustKSortsInIRList (ListPat l y S) of (ListPat l' y' S')
        \<Rightarrow>  (ListPat ((adjustKSortsInIRK x)#l') y' S')
       | _ \<Rightarrow> (ListPat (x#l) y S))"
| "adjustKSortsInIRSet (SetPat [] b) = (SetPat [] b)"
| "adjustKSortsInIRSet (SetPat (x#l) b) = (case adjustKSortsInIRSet (SetPat l b) of 
          (SetPat l' b') \<Rightarrow> SetPat ((adjustKSortsInIRK x)#l') b')"
| "adjustKSortsInIRMap (MapPat [] b) = (MapPat [] b)"
| "adjustKSortsInIRMap (MapPat ((x,y)#l) b) = (case adjustKSortsInIRMap (MapPat l b) of 
          (MapPat l' b') \<Rightarrow> MapPat ((adjustKSortsInIRK x,adjustKSortsInIRK y)#l') b')"
| "adjustKSortsInIRBag (BagPat [] b) = (BagPat [] b)"
| "adjustKSortsInIRBag (BagPat ((x,y,z)#l) b) = (case adjustKSortsInIRBag (BagPat l b) of 
          (BagPat l' b') \<Rightarrow> BagPat ((x,y,(adjustKSortsInIRBigKWithBag z))#l') b')"

primrec adjustKSortsInMatchFactor where
"adjustKSortsInMatchFactor (KLabelMatching l) = (KLabelMatching l)"
| "adjustKSortsInMatchFactor (KItemMatching l) = (KItemMatching (adjustKSortsInIRKItem l))"
| "adjustKSortsInMatchFactor (KListMatching l) = (KListMatching (adjustKSortsInIRKList l))"
| "adjustKSortsInMatchFactor (KMatching l) = (KMatching (adjustKSortsInIRK l))"
| "adjustKSortsInMatchFactor (ListMatching l) = (ListMatching (adjustKSortsInIRList l))"
| "adjustKSortsInMatchFactor (SetMatching l) = (SetMatching (adjustKSortsInIRSet l))"
| "adjustKSortsInMatchFactor (MapMatching l) = (MapMatching (adjustKSortsInIRMap l))"
| "adjustKSortsInMatchFactor (BagMatching l) = (BagMatching (adjustKSortsInIRBag l))"

primrec adjustKSortsInPat where
"adjustKSortsInPat (KLabelFunPat x y) = (KLabelFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (KFunPat x y) = (KFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (KItemFunPat x y) = (KItemFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (ListFunPat x y) = (ListFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (SetFunPat x y) = (SetFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (MapFunPat x y) = (MapFunPat x (adjustKSortsInIRKList y))"
| "adjustKSortsInPat (NormalPat x) = (NormalPat (adjustKSortsInMatchFactor x))"

fun adjustKSortsInFunPatList where
"adjustKSortsInFunPatList [] = []"
| "adjustKSortsInFunPatList ((x,y,z)#l) = (adjustKSortsInPat x,y,z)#(adjustKSortsInFunPatList l)"

fun adjustKSortsInRulePats where
"adjustKSortsInRulePats [] = []"
| "adjustKSortsInRulePats ((FunPat x y z)#l) = 
   (case z of None \<Rightarrow> (FunPat x (adjustKSortsInFunPatList y) None)#(adjustKSortsInRulePats l)
    | Some (a,b,c) \<Rightarrow> (FunPat x (adjustKSortsInFunPatList y)
                          (Some (adjustKSortsInPat a,b,c)))#adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((MacroPat x y z)#l) =
                (MacroPat x (adjustKSortsInIRKList y) z)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((AnywherePat a b c d)#l) =
                (AnywherePat a (adjustKSortsInIRKList b) c d)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((KRulePat a b c d)#l) =
                (KRulePat (adjustKSortsInIRK a) b c d)#(adjustKSortsInRulePats l)"
| "adjustKSortsInRulePats ((BagRulePat a b c d)#l) =
                (BagRulePat (adjustKSortsInIRBag a) b c d)#(adjustKSortsInRulePats l)"

definition applyAllMacroRulesCheck where
"applyAllMacroRulesCheck stl Theory database subG =
    (case typeCheckRules Theory database subG of None \<Rightarrow> None
          | Some l \<Rightarrow> (case realConfigurationTest stl Theory database subG 
      of None \<Rightarrow> None
         | Some bl \<Rightarrow> (case divideMacroRules l subG of Some (x,y)
       \<Rightarrow> (case applyAllMacroRulesInList x (Some y) bl database subG of
         None \<Rightarrow> None | Some (l', confi) \<Rightarrow> if wellFormRules l'
        then (case inferTypesInRules l' Theory database subG of None \<Rightarrow> None
             | Some la \<Rightarrow> (case adjustKSortsInRulePats la of la' \<Rightarrow>
      (case inferTypesInRules la' Theory database subG of None \<Rightarrow> None
          | Some lb \<Rightarrow> (case typeCheckProgramState confi database subG of None \<Rightarrow> None
      | Some confi' \<Rightarrow> Some (lb, confi'))))) else None))))"

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
          Some (s, y, [KLabel], SUIdKLabel FunHole) else None)
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
            Some (s, y,z, (if z = [K] then IdFactor FunHole else ItemFactor (SUIdKItem (FunHole) z))#l)
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
            Some (s, y,[List], (IdL FunHole)#l)
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
            Some (s, y, [Set], (IdS FunHole)#l)
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
            Some (s, y,[Map], (IdM FunHole)#l)
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
       (Continue value) (Stop (SUKItem (SUKLabel (ConstToLabel (BoolConst True))) [] [Bool]))
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
     \<Rightarrow> ('m kSyntax.sort list \<times> 'm kSyntax.sort list list \<times> 'm label KItemSyntax \<times> 'p \<times> bool) list
        \<Rightarrow> ('m kSyntax.sort \<times> 'm kSyntax.sort list) list
           \<Rightarrow> ('m label \<times> ('m, 'n, 'o) irKList \<times> ('m, 'n, 'o) suKFactor list
     \<times> ('m, 'n, 'o) suKItem) list
            \<Rightarrow> ('m, 'n, 'o) suB list \<Rightarrow> ('m, 'n, 'o) suB list option" where
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
| "getAllKCells ((ItemB x y z)#l) = (if x = LittleK then (case z of SUK a \<Rightarrow>
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
| "replaceKCells ((ItemB x y z)#l) t r = (if x = LittleK then (case z of SUK a \<Rightarrow>
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

(* defining K compile: compilation and checking process of K theory *)
definition kcompile :: "('upVar, 'var, 'acapvar, 'metaVar) kFile
   \<Rightarrow> (('upVar, 'var, 'acapvar, 'metaVar) kFile \<times>
           ('upVar kSyntax.sort list \<times> 'upVar kSyntax.sort list list \<times>
          'upVar label KItemSyntax \<times> synAttrib list \<times> bool) list
    \<times> ('upVar kSyntax.sort \<times> 'upVar kSyntax.sort list) list \<times> ('upVar, 'var, 'metaVar) suB list
    \<times> ('upVar, 'var, 'metaVar) rulePat list, char list) oneStep" where
"kcompile Theory = (case syntaxSetToKItemTest Theory of None \<Rightarrow> 
         Failure (''Not a valid K theory.'') | Some database \<Rightarrow>
    if invalidSortChecks Theory then (if uniqueKLabelSyntax Theory
       then (case subsortGraph Theory of subG \<Rightarrow>
     (if validSyntaxSort [] Theory database subG then
     (case configurationTest Theory database subG of None
               \<Rightarrow> Failure (''The configuration is not valid.'')
        | Some confi \<Rightarrow> (case typeCheckRules Theory database subG of None \<Rightarrow>
            Failure (''The theory has invalid rules.'')
    | Some allRules \<Rightarrow> (case strictRuleTest [] Theory subG of None \<Rightarrow>
            Failure (''The theory has invalid strict attributes.'')
        | Some stl \<Rightarrow>
            Success (Theory,database,subG,confi,allRules@stl))))
       else Failure (''K theory has invalid syntax or strict attributes failed.'')))
     else Failure (''kLabels are not uniquely defined in this K theory.''))
         else Failure (''K theory has invalid subsort.''))"

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

code_pred krun .

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

code_pred oneTransKRuleAux .

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

code_pred ksearch .

export_code Eps Continue Success FunTrans Single IntConst Bool Defined UnitLabel NonTerminal
    Strict Syntax Star Stdin Multiplicity KTerm KLabelC Heat TheSyntax IRKLabel IRKItem
       KLabelMatching KLabelFunPat SUKLabel KLabelSubs FunPat SingleTon OtherVar krun ksearch
    ARule Parsed AChar Suc Nibble0 Char Num.One Int.Pos Num.inc formGraph
   symbolsToKLabel syntaxToKItem syntaxSetToKItemTest getKLabelName subsort getNonTerminalInList
    getValueTerm in OCaml  module_name K file "k.ml"

end