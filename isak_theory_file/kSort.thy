theory kSort
imports Main Real List kSyntax kGetters
begin

primrec getType where
"getType (SUKItem x y ty) = ty"
| "getType (SUIdKItem a ty) = ty"
| "getType (SUHOLE ty) = ty"

fun formGraph :: "'upVar list \<Rightarrow> ('upVar * 'upVar) list
                     \<Rightarrow> ('upVar * 'upVar list) list" where
"formGraph [] S = []"
| "formGraph (a#l) S = (a,getAllSubsortOnItem S a)#formGraph l S"

fun addImplicitSubsorts :: "'upVar \<Rightarrow> 'upVar list
                        \<Rightarrow> 'upVar list \<Rightarrow> ('upVar * 'upVar) list" where
"addImplicitSubsorts x S [] = []"
| "addImplicitSubsorts x S (a#l) = (if a \<in> set S then addImplicitSubsorts x S l
                                                else (x, a)#(addImplicitSubsorts x S l))"

fun formDatabase :: "('upVar * 'upVar list * 'a * 'b) list
               \<Rightarrow> ('upVar * ('upVar list * 'a * 'b) list) list" where
"formDatabase [] = []"
| "formDatabase ((a,al,k,b)#l) = insertA (formDatabase l) a (al,k,b)"

fun searchDataBaseByKey :: "('a * 'b list) list \<Rightarrow> 'a \<Rightarrow> 'b list option" where
"searchDataBaseByKey [] x = None"
| "searchDataBaseByKey ((x,y)#l) a = (if x = a then Some y else searchDataBaseByKey l a)"

fun deleteDataBaseByKey :: "('a * 'b list) list \<Rightarrow> 'a \<Rightarrow> ('a * 'b list) list" where
"deleteDataBaseByKey [] x = []"
| "deleteDataBaseByKey ((x,y)#l) a = (if x = a then l else (x,y)#(deleteDataBaseByKey l a))"

fun insertInDatabase :: "('a * 'b list) list \<Rightarrow>
                  'a \<Rightarrow> 'b list \<Rightarrow> ('a * 'b list) list" where
"insertInDatabase [] a b = []"
| "insertInDatabase ((x,y)#l) a b = (if a = x
                  then (x, insertAll y b)#l else (x,y)#(insertInDatabase l a b))"

fun formSubsortDatabase :: "('upVar * 'upVar) list
      \<Rightarrow> ('upVar * 'a list) list
      \<Rightarrow> ('upVar * 'a list) list" where
"formSubsortDatabase [] D = D"
| "formSubsortDatabase ((x,y)#l) D = (case searchDataBaseByKey D y of None
                                \<Rightarrow> formSubsortDatabase l D
                   | Some vs \<Rightarrow> formSubsortDatabase l (insertInDatabase D x vs))"

definition splitList :: "'a list \<Rightarrow> ('a * 'a list) option" where
"splitList L = (case L of [] \<Rightarrow> None
                   | (b#l) \<Rightarrow> Some (last (b#l), butlast (b#l)))"

definition inValidBuiltinSubsort where
"inValidBuiltinSubsort a b = (a \<in> {K, KList, List, Set, Bag, Map, KLabel}
      \<or> b \<in> {K, KList, List, Set, Bag, Map, KLabel})"

definition inValidBuiltinSubsortOne where
"inValidBuiltinSubsortOne a b = (a = KResult \<or> a = KItem)"

definition inValidFactorOne where
"inValidFactorOne a b = (a = b)"

definition invalidSubsortFactor where
"invalidSubsortFactor a b = ((inValidBuiltinSubsort a b) \<or> (inValidBuiltinSubsortOne a b)
                      \<or> (inValidFactorOne a b))"

primrec hasInvalidSubsort where
"hasInvalidSubsort [] = False"
| "hasInvalidSubsort (a#l) = (case a of (x,y) \<Rightarrow>
      if (invalidSubsortFactor x y) then True
         else hasInvalidSubsort l)"


function hasInvalidTranstiveClosureAux and hasInvalidTranstiveClosureInList where
"hasInvalidTranstiveClosureInList G a [] acc = True"
| "hasInvalidTranstiveClosureInList G a (x#l) acc = (if x \<in> set acc then False
    else (hasInvalidTranstiveClosureAux G G x acc \<and> hasInvalidTranstiveClosureInList G a l acc))"
| "hasInvalidTranstiveClosureAux G [] x acc = True"
| "hasInvalidTranstiveClosureAux G (en#l) x acc = (case en of (a,b) \<Rightarrow>
                 if a = x then hasInvalidTranstiveClosureInList G x b (x#acc)
                    else hasInvalidTranstiveClosureAux G l x acc)"
by pat_completeness auto

termination sorry

fun hasInvalidTranstiveClosure where
"hasInvalidTranstiveClosure G [] = True"
| "hasInvalidTranstiveClosure G ((x,y)#l) =
     (hasInvalidTranstiveClosureInList G x y [x] \<and> hasInvalidTranstiveClosure G l)"

fun getResultSortInAttrs :: "('var, 'upVar) ruleAttrib list \<Rightarrow> 'upVar sort option" where
"getResultSortInAttrs [] = None"
| "getResultSortInAttrs ((Result a)#l) = (case getResultSortInAttrs l of None \<Rightarrow> Some a
                    | Some a' \<Rightarrow> None)"
| "getResultSortInAttrs (a#l) = getResultSortInAttrs l"

definition PreAllSubsorts where
"PreAllSubsorts Theory = (getAllSubsortInKFile Theory)
                     @ (addImplicitSubsorts KItem BuiltinSorts
                          (getAllSorts (getAllSyntaxInKFile Theory)))
                     @ [(KResult, KItem), (KItem, K)]@topSubsort"

definition preSubsortTerms where
"preSubsortTerms Theory database 
   = formSubsortDatabase (PreAllSubsorts Theory)
         (formDatabase database)"

definition preSubsortGraph where
"preSubsortGraph Theory = formGraph (insertAll (getAllSorts
        (getAllSyntaxInKFile Theory)) BuiltinSorts) (PreAllSubsorts Theory)"


function subsortAux :: "'upVar \<Rightarrow> 'upVar \<Rightarrow>
                           ('upVar * 'upVar list) list \<Rightarrow> bool"
and subsortInList :: "'upVar \<Rightarrow>
                 'upVar list \<Rightarrow> ('upVar * 'upVar list) list \<Rightarrow> bool" where
"subsortAux a b [] = False"
| "subsortAux a b S = (case searchDataBaseByKey S b of None \<Rightarrow> False
                       | Some l \<Rightarrow> (if a \<in> set l then True
                                else subsortInList a l (deleteDataBaseByKey S b)))"
| "subsortInList a [] S = False"
| "subsortInList a (b#l) S = ((subsortAux a b S) \<or> (subsortInList a l S))"
by pat_completeness auto

termination sorry

primrec getKResultSubsorts where
"getKResultSubsorts [] subG = []"
| "getKResultSubsorts (a#l) subG = (if a \<in> set BuiltinSorts then 
        getKResultSubsorts l subG else if subsortAux KResult a subG
           then getKResultSubsorts l subG
      else (KResult,a)#(getKResultSubsorts l subG))"

definition kResultSubsorts where
"kResultSubsorts Theory = 
       getKResultSubsorts (getAllSorts (getAllSyntaxInKFile Theory)) (preSubsortGraph Theory)"

definition AllSubsorts where
"AllSubsorts Theory = (getAllSubsortInKFile Theory)
                     @ (addImplicitSubsorts KItem BuiltinSorts
                          (getAllSorts (getAllSyntaxInKFile Theory)))
                     @ [(KResult, KItem), (KItem, K)]@topSubsort@(kResultSubsorts Theory)"

definition subsortTerms where
"subsortTerms Theory database 
   = formSubsortDatabase (AllSubsorts Theory)
         (formDatabase database)"

definition subsortGraph where
"subsortGraph Theory = formGraph (insertAll (getAllSorts
        (getAllSyntaxInKFile Theory)) BuiltinSorts) (AllSubsorts Theory)"

definition subsort where
"subsort a b subG = (if a = b then True else subsortAux a b subG)"

primrec subsortListAux where
"subsortListAux a [] subG = False"
| "subsortListAux a (x#l) subG = (if subsort a x subG then True
                else subsortListAux a l subG)"

primrec subsortList where
"subsortList [] b subG = True"
| "subsortList (x#l) b subG = (if subsortListAux x b subG then
               subsortList l b subG else False)"

definition invalidSortChecks where
"invalidSortChecks Theory = (case subsortGraph Theory of subG \<Rightarrow>
    (\<not> hasInvalidSubsort (getAllSubsortInKFile Theory)
         \<and> \<not> hasInvalidTranstiveClosure subG subG))"

primrec insertSortInList where
"insertSortInList a [] subG = [a]"
| "insertSortInList a (b#l) subG = (if subsort a b subG then (b#l)
      else if subsort b a subG then insertSortInList a l subG
       else b#(insertSortInList a l subG))"

primrec insertAllSortsInList where
"insertAllSortsInList [] l subG = l"
| "insertAllSortsInList (x#l) S subG = insertAllSortsInList l (insertSortInList x S subG) subG"

(* get max sorts of a sort a and the children of sort b as a list 
   assume that a and b do not have subsort relation *)
function getMaxSorts where
"getMaxSorts a [] subG checked acc = acc"
| "getMaxSorts a (c#l) subG checked acc = (if subsort c a subG then
              (getMaxSorts a l subG (c#checked) (insertSortInList c acc subG))
           else if c \<in> set checked then (getMaxSorts a l subG checked acc)
        else (case getValueTerm c subG of None \<Rightarrow> 
                (getMaxSorts a l subG (c#checked) acc)
            | Some newl \<Rightarrow> (case getMaxSorts a newl subG (c#checked) acc
                 of acc' \<Rightarrow> (getMaxSorts a l subG (c#checked) acc'))))"
by pat_completeness auto

termination sorry

primrec meetAux where
"meetAux a [] subG = []"
| "meetAux a (x#l) subG = (if subsort a x subG then (insertSortInList a (meetAux a l subG) subG)
      else if subsort x a subG then (insertSortInList x (meetAux a l subG) subG)
     else (case getValueTerm x subG of None \<Rightarrow> meetAux a l subG
             | Some newl \<Rightarrow>
           insertAllSortsInList (getMaxSorts a newl subG [x] []) (meetAux a l subG) subG))"

primrec meet where
"meet [] b subG = []"
| "meet (x#l) b subG = insertAllSortsInList (meetAux x b subG) (meet l b subG) subG"

primrec sortMembership where
"sortMembership a [] = False"
| "sortMembership a (x#l) = (if x = a then True else sortMembership a l)"

primrec sortMembershipList where
"sortMembershipList [] S = True"
| "sortMembershipList (a#l) S = ((sortMembership a S) \<and> (sortMembershipList l S))"

definition sortEqual where
"sortEqual S1 S2 = (sortMembershipList S1 S2 \<and> sortMembershipList S2 S1)"

fun getSortMeaning where
"getSortMeaning a [] = None"
| "getSortMeaning a ((v, vs, SingleTon a', nl, b)#l) =
       (if a = a' then Some v  else getSortMeaning a l)"
| "getSortMeaning a ((v, vs, SetTon S, nl, b)#l) =
             (if S a then Some v else getSortMeaning a l)"

(* getting the least sort of a given kitem *)
definition getSort where
"getSort a database = getSortMeaning a database"

fun getArgSortsMeaning  where
"getArgSortsMeaning a [] = None"
| "getArgSortsMeaning a ((v, vs, SingleTon a', nl, b)#l) =
   (if a = a' then Some vs else getArgSortsMeaning a l)"
| "getArgSortsMeaning a ((v, vs, SetTon S, nl, b)#l) =
        (if S a then Some vs else getArgSortsMeaning a l)"

(* getting the least sort of a given kitem *)
definition getArgSort where
"getArgSort a database = getArgSortsMeaning a database"

definition getSUArgSort where
"getSUArgSort a database 
  = (case a of (SUKItem (SUKLabel s) kl ty) \<Rightarrow>
       getArgSort s database | _ \<Rightarrow> None)"

end