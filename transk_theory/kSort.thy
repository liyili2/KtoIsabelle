theory kSort
imports Main kSyntax kGetters
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
"inValidBuiltinSubsort a b = (a \<in> {K, KList, List, Set, Bag, Map, KLabelSort}
      \<or> b \<in> {K, KList, List, Set, Bag, Map, KLabelSort})"

definition inValidBuiltinSubsortOne where
"inValidBuiltinSubsortOne a b = (a = KResult \<or> a = KItemSort)"

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

definition subsort where
"subsort a b subG = (if a = b then True else subsortAux a b subG)"

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

(*
fun hasSort :: "('upVar, 'var, 'metaVar metaVar) irKItem
                       \<Rightarrow> 'upVar \<Rightarrow> bool" where
"hasSort a ty = (case a of (IRKItem (IRKLabel s) kl ty')
          \<Rightarrow> (case getSort s of None \<Rightarrow> False
                    | Some tya \<Rightarrow> subsort tya ty subsortGraph))" *)

definition mergeSubsort where
"mergeSubsort a b subG = (if subsort a b subG then Some a
                     else if subsort b a subG then Some b
                    else None)"

end