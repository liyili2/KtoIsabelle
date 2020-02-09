theory isabInIsab
imports Main isabLambda
begin

(* datatype defining terms in Isabelle 
   ? look for Isabelle isabelle quotient type in Isabelle.
     context equivalence under congruence. *)
datatype 'tVar isabType = OtherType 'tVar | IsabList "'tVar isabType" | IsabOption "'tVar isabType"
                    | BoolIsab | QuoteA | QuoteB | IsabState "'tVar isabType" "'tVar isabType"

datatype ('tVar, 'cVar, 'iVar) isabTerm =
          Term 'tVar 'cVar "('tVar, 'cVar, 'iVar) isabTerm list"
      | VarTerm 'tVar 'iVar
      | CaseList "('tVar, 'cVar, 'iVar) isabTerm"
                  "(('tVar, 'cVar, 'iVar) isabTerm * ('tVar, 'cVar, 'iVar) isabTerm) list"
      | CaseOwise | IsabListAt "('tVar, 'cVar, 'iVar) isabTerm" "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabListCon "('tVar, 'cVar, 'iVar) isabTerm" "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabEmptyList | IsabNone | IsabSome "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabTrue | IsabFalse | IsabNot "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabAnd "('tVar, 'cVar, 'iVar) isabTerm" "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabOr "('tVar, 'cVar, 'iVar) isabTerm" "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabExist 'iVar 'tVar "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabEqual "('tVar, 'cVar, 'iVar) isabTerm" "('tVar, 'cVar, 'iVar) isabTerm"
      | AppFun 'cVar "('tVar, 'cVar, 'iVar) isabTerm list"
      | IsabContinue "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabGood "('tVar, 'cVar, 'iVar) isabTerm"
      | IsabBad


locale IsabelleFun = 
  fixes Types :: "'tVar isabType set" (* type names *)
  and Constructs :: "'cVar set" (* constructor names *)
  and IsabVars :: "'iVar set" (* isabelle variables *)
  and IVarOne :: "'iVar"
  and IVarTwo :: "'iVar"
  and IVarThree :: "'iVar"
  and freshCVar :: "'cVar list \<Rightarrow> 'cVar"
  and freshIVar :: "'iVar list \<Rightarrow> 'iVar"
  and renameCVar :: "'cVar \<Rightarrow> 'cVar list \<Rightarrow> 'cVar"
  assumes freshCVarRule : "\<forall> l . freshCVar l \<notin> set l"
  and freshIVarRule : "\<forall> l . freshIVar l \<notin> set l"
  and renameCVarRule : "\<forall> c l . renameCVar c l \<notin> set (c#l)"
  and IsabVarsRule : "\<forall> l . (freshIVar l) \<in> IsabVars"
  and IVarConstsRule : "{IVarOne, IVarTwo, IVarThree} \<subseteq> IsabVars"
context IsabelleFun begin

(* given a list of syntax with datatypes, the function gets all defined types *)
fun getAllTypeInSyntaxList :: "('tVar isabType * ('cVar * 'tVar isabType list) list) list
     \<Rightarrow> 'tVar isabType list" where
"getAllTypeInSyntaxList [] = []"
| "getAllTypeInSyntaxList ((x,y)#l) = x#getAllTypeInSyntaxList l"

(* all allowed types are user defined types plus an extra type named bool *)
definition allAllowBasicTypes :: "('tVar isabType * ('cVar * 'tVar isabType list) list) list
     \<Rightarrow> ('tVar isabType) list" where
"allAllowBasicTypes l = BoolIsab#getAllTypeInSyntaxList l"

(* all user defined type automatically get a corresponding list type *)
fun genListTypes :: "'tVar isabType list \<Rightarrow> 'tVar isabType list" where
"genListTypes [] = []"
| "genListTypes (a#l) = (IsabList a)#genListTypes l"

(*all allowed types are user defined types, bool and list of user defined types. *)
definition allAllowTypes :: "('tVar isabType * ('cVar * 'tVar isabType list) list) list
        \<Rightarrow> 'tVar isabType list" where
"allAllowTypes l = (allAllowBasicTypes l)@(genListTypes (allAllowBasicTypes l))"

(* function to check if a datatype type has defined twice *)
primrec checkDeclTypeList :: "'tVar isabType list \<Rightarrow>
                       'tVar isabType list \<Rightarrow> bool" where
"checkDeclTypeList [] S = True"
| "checkDeclTypeList (b#l) S = (if b \<in> set S then False else checkDeclTypeList l (b#S))"

(* a function to check if a datatype type is defined in the system *)
primrec checkTypeList :: "'tVar isabType list
              \<Rightarrow> 'tVar isabType list \<Rightarrow> bool" where
"checkTypeList [] S = True"
| "checkTypeList (b#l) S = (if b\<notin> set S then False else checkTypeList l (b#S))"

(* a function (checkSyntaxList with aux version)
    to check if any type in a datatype has been declared. *)
fun checkSyntaxListAux :: "'tVar isabType list \<Rightarrow> 'cVar list
                  \<Rightarrow> ('cVar * 'tVar isabType list) list \<Rightarrow> 'cVar list option" where
"checkSyntaxListAux S T [] = Some T"
| "checkSyntaxListAux S T ((x,y)#l) = (if x \<in> set T then None else
         if checkTypeList S y then checkSyntaxListAux S (x#T) l else None)"

fun checkSyntaxList :: "'tVar isabType list \<Rightarrow> 'cVar list \<Rightarrow>
        ('tVar isabType * ('cVar * 'tVar isabType list) list) list \<Rightarrow> 'cVar list option" where
"checkSyntaxList S T [] = Some T"
| "checkSyntaxList S T ((x,y)#l) = (if x \<in> set S then
    (case checkSyntaxListAux S T y of None \<Rightarrow> None
      | Some T' \<Rightarrow> checkSyntaxList S T' l) else None)"

(* a function to check if all datatypes declared in a file makes sense. Two issues:
   all types are declared exactly once, and all types used in any datatypes
    must be decleared in some datatypes. *)
definition checkSyntax :: "('tVar isabType * ('cVar * 'tVar isabType list) list) list \<Rightarrow> bool" where
"checkSyntax l = (if checkDeclTypeList (getAllTypeInSyntaxList l) [] then 
   (case allAllowTypes l of atl \<Rightarrow>
       (case checkSyntaxList atl [] l of None \<Rightarrow> False
       | Some cl \<Rightarrow> True)) else False)"

(* compare two types and see if they can be unified with each other. 
   the output is a most specific type of the two. *)
fun compareTypes :: "'tVar isabType \<Rightarrow> 'tVar isabType
      \<Rightarrow> 'tVar isabType option" where
 "compareTypes QuoteA B = Some B"
| "compareTypes A QuoteA = Some A"
| "compareTypes QuoteB B = Some B"
| "compareTypes A QuoteB = Some A"
| "compareTypes (OtherType x) B = (case B of (OtherType y) \<Rightarrow>
    (if x = y then Some (OtherType x) else None) | _ \<Rightarrow> None)"
| "compareTypes (IsabList x) B = (case B of (IsabList y) \<Rightarrow>
       (case compareTypes x y of None \<Rightarrow> None
          | Some x' \<Rightarrow> Some (IsabList x')) | _ \<Rightarrow> None)"
| "compareTypes (IsabOption x) B = (case B of (IsabOption y) \<Rightarrow>
        (case compareTypes x y of None \<Rightarrow> None
          | Some x' \<Rightarrow> Some (IsabOption x')) | _ \<Rightarrow> None)"
| "compareTypes (IsabState x y) B = (case B of IsabState x' y' \<Rightarrow>
    (case compareTypes x x' of None \<Rightarrow> None | Some xa \<Rightarrow> (case compareTypes y y' of None \<Rightarrow> None
       | Some ya \<Rightarrow> Some (IsabState xa ya))) | _ \<Rightarrow> None)"
| "compareTypes BoolIsab B = (case B of BoolIsab \<Rightarrow> Some BoolIsab
             | _ \<Rightarrow> None)"

(* grab all variables in an isabelle term. *)
primrec grabVars :: "('tVar isabType, 'cVar, 'iVar) isabTerm \<Rightarrow> ('iVar * 'tVar isabType) list
          \<Rightarrow> ('iVar * 'tVar isabType) list option"
  and grabVarsInList :: "('tVar isabType, 'cVar, 'iVar) isabTerm list \<Rightarrow> ('iVar * 'tVar isabType) list
          \<Rightarrow> ('iVar * 'tVar isabType) list option" where
"grabVars IsabTrue S = Some S"
| "grabVars IsabFalse S = Some S"
| "grabVars (Term x y z) S = grabVarsInList z S"
| "grabVars (VarTerm x y) S = (case lookup y S of None \<Rightarrow> Some (update y x S)
           | _ \<Rightarrow> None)"
| "grabVars CaseOwise S = Some S"
| "grabVars (CaseList a b) S = None"
| "grabVars IsabEmptyList S = Some S"
| "grabVars IsabNone S = Some S"
| "grabVars (IsabSome a) S = grabVars a S"
| "grabVars (IsabNot a) S = grabVars a S"
| "grabVars (IsabAnd a b) S = (case grabVars a S of None \<Rightarrow> None
            | Some S' \<Rightarrow> grabVars b S')"
| "grabVars (IsabOr a b) S = (case grabVars a S of None \<Rightarrow> None
            | Some S' \<Rightarrow> grabVars b S')"
| "grabVars (IsabExist a t b) S = None"
| "grabVars (IsabEqual a b) S = (case grabVars a S of None \<Rightarrow> None
            | Some S' \<Rightarrow> grabVars b S')"
| "grabVars IsabBad S = Some S"
| "grabVars (IsabGood a) S = grabVars a S"
| "grabVars (IsabContinue a) S = grabVars a S"
| "grabVars (AppFun a b) S = None"
| "grabVars (IsabListAt a b) S = None"
| "grabVars (IsabListCon a b) S = (case grabVars a S of None \<Rightarrow> None
             | Some S' \<Rightarrow> grabVars b S')"
| "grabVarsInList [] S = Some S"
| "grabVarsInList (a#l) S = (case grabVars a S of None \<Rightarrow> None
          | Some S' \<Rightarrow> grabVarsInList l S')"

(* in a case of structure, what is the valid case analysis term in lambda calculus. *)
primrec validCaseFactor :: "('tVar isabType, 'cVar, 'iVar) isabTerm  \<Rightarrow> bool" where
"validCaseFactor IsabTrue = True"
| "validCaseFactor IsabFalse = True"
| "validCaseFactor (Term x y z) = True"
| "validCaseFactor (VarTerm x y) = True"
| "validCaseFactor CaseOwise = False"
| "validCaseFactor (CaseList a b) = False"
| "validCaseFactor IsabEmptyList = True"
| "validCaseFactor IsabNone = True"
| "validCaseFactor (IsabSome a) = True"
| "validCaseFactor (IsabGood a) = True"
| "validCaseFactor (IsabBad) = True"
| "validCaseFactor (IsabContinue a) = True"
| "validCaseFactor (IsabNot a) = True"
| "validCaseFactor (IsabAnd a b) = True"
| "validCaseFactor (IsabOr a b) = True"
| "validCaseFactor (IsabExist a t b) = False"
| "validCaseFactor (IsabEqual a b) = True"
| "validCaseFactor (AppFun a b) = True"
| "validCaseFactor (IsabListAt a b) = True"
| "validCaseFactor (IsabListCon a b) = True"

(* unify two finite maps together. *)
fun updateAll :: "('a * 'b) list \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
"updateAll [] S = S"
| "updateAll ((x,y)#l) S = updateAll l (update x y S)"

(* This function implements the simple typed algorithm in Isabelle. *)
primrec typeCheckTerm :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
          \<Rightarrow> ('iVar * 'tVar isabType) list
  \<Rightarrow> ('tVar isabType, 'cVar, 'iVar) isabTerm  \<Rightarrow> 'tVar isabType option"
 and typeCheckPairList :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
    \<Rightarrow> ('iVar * 'tVar isabType) list \<Rightarrow> 'tVar isabType
     \<Rightarrow> (('tVar isabType, 'cVar, 'iVar) isabTerm  * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list
    \<Rightarrow>  'tVar isabType option"
 and typeCheckPair :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
    \<Rightarrow> ('iVar * 'tVar isabType) list \<Rightarrow> 'tVar isabType
     \<Rightarrow> (('tVar isabType, 'cVar, 'iVar) isabTerm  * ('tVar isabType, 'cVar, 'iVar) isabTerm )
    \<Rightarrow>  'tVar isabType option"
 and typeCheckTermList :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
    \<Rightarrow> ('iVar * 'tVar isabType) list \<Rightarrow> ('tVar isabType, 'cVar, 'iVar) isabTerm  list
          \<Rightarrow> 'tVar isabType list
    \<Rightarrow> bool" where
"typeCheckTerm M S IsabTrue = Some BoolIsab"
| "typeCheckTerm M S IsabFalse = Some BoolIsab"
| "typeCheckTerm M S IsabEmptyList = Some (IsabList QuoteA)"
| "typeCheckTerm M S (VarTerm x y) = (case lookup y S of None \<Rightarrow> None
        | Some t' \<Rightarrow> (case compareTypes x t' of None \<Rightarrow> None
           | Some x' \<Rightarrow> Some x'))"
| "typeCheckTerm M S (Term x y z) = (case lookup y M of None \<Rightarrow> None
      | Some (tyl, ty) \<Rightarrow> (if typeCheckTermList M S z tyl then 
           compareTypes ty x else None))"
| "typeCheckTerm M S CaseOwise = Some QuoteA"
| "typeCheckTerm M S (CaseList a b) = (if validCaseFactor a then
      (case typeCheckTerm M S a of None \<Rightarrow> None
         | Some ty \<Rightarrow> typeCheckPairList M S ty b) else None)"
| "typeCheckTerm M S (IsabBad) = Some (IsabState QuoteA QuoteB)"
| "typeCheckTerm M S (IsabContinue a) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> Some (IsabState t QuoteB))"
| "typeCheckTerm M S (IsabGood a) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> Some (IsabState QuoteA t))"
| "typeCheckTerm M S (IsabNone) = Some (IsabOption QuoteA)"
| "typeCheckTerm M S (IsabSome a) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> Some (IsabOption t))"
| "typeCheckTerm M S (IsabNot a) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> compareTypes t BoolIsab)"
| "typeCheckTerm M S (IsabAnd a b) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> (case compareTypes t BoolIsab of None \<Rightarrow> None
          | Some t' \<Rightarrow> (case typeCheckTerm M S b of None \<Rightarrow> None
        | Some ty \<Rightarrow> compareTypes ty BoolIsab)))"
| "typeCheckTerm M S (IsabOr a b) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> (case compareTypes t BoolIsab of None \<Rightarrow> None
          | Some t' \<Rightarrow> (case typeCheckTerm M S b of None \<Rightarrow> None
        | Some ty \<Rightarrow> compareTypes ty BoolIsab)))"
| "typeCheckTerm M S (IsabEqual a b) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> (case typeCheckTerm M S b of None \<Rightarrow> None
        | Some ty \<Rightarrow> compareTypes t ty))"
| "typeCheckTerm M S (IsabExist a t b) = (case typeCheckTerm M (update a t S) b of
         None \<Rightarrow> None | Some t \<Rightarrow> compareTypes t BoolIsab)"
| "typeCheckTerm M S (AppFun c l) = (case lookup c M of None \<Rightarrow> None
      | Some (tyl, ty) \<Rightarrow> (if typeCheckTermList M S l tyl then 
           Some ty else None))"
| "typeCheckTerm M S (IsabListCon a b) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> (case typeCheckTerm M S b of None \<Rightarrow> None
        | Some ty \<Rightarrow> compareTypes (IsabList t) ty))"
| "typeCheckTerm M S (IsabListAt a b) = (case typeCheckTerm M S a of None \<Rightarrow> None
        | Some t \<Rightarrow> (case typeCheckTerm M S b of None \<Rightarrow> None
        | Some ty \<Rightarrow> (case compareTypes t ty of None \<Rightarrow> None
           | Some listTy \<Rightarrow> compareTypes (IsabList QuoteA) listTy)))"
| "typeCheckPair M S t (x,y) = (case grabVars x [] of None \<Rightarrow> None
         | Some S' \<Rightarrow> (case typeCheckTerm M (updateAll S' S) x
      of None \<Rightarrow> None | Some t' \<Rightarrow> (case compareTypes t t' of
           None \<Rightarrow> None | Some ta \<Rightarrow> typeCheckTerm M (updateAll S' S) y)))"
| "typeCheckPairList M S t [] = Some QuoteA"
| "typeCheckPairList M S t (a#l) = (case typeCheckPair M S t a of None \<Rightarrow> None
         | Some ty \<Rightarrow> (case typeCheckPairList M S t l of None \<Rightarrow> None
           | Some ty' \<Rightarrow> compareTypes ty ty'))"
| "typeCheckTermList M S [] tyl = (case tyl of [] \<Rightarrow> True | _ \<Rightarrow> False)"
| "typeCheckTermList M S (t#terml) tyl = (case tyl of [] \<Rightarrow> False
      | (ty#tyl') \<Rightarrow> (case typeCheckTerm M S t of None \<Rightarrow> False
 | Some ty' \<Rightarrow> if ty = ty' then (typeCheckTermList M S terml tyl') else False))"

(* This function creates a finite mapping from a variable to a type. *)
primrec bindTypesWithVars :: "'iVar list \<Rightarrow> 'tVar isabType list
     \<Rightarrow> ('iVar * 'tVar isabType) list option" where
"bindTypesWithVars [] T = (case T of [] \<Rightarrow> Some [] | _ \<Rightarrow> None)"
| "bindTypesWithVars (x#l) T = (case T of [] \<Rightarrow> None | (t#tyl) \<Rightarrow>
          (case bindTypesWithVars l T of None \<Rightarrow> None 
         | Some M \<Rightarrow> Some ((x,t)#M)))"

(* This function applies the type checking algorithm above, and the grabs the var-type map
     by the above function, and then giving a function the most specific type. *)
definition typeCheckFunction :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
    \<Rightarrow> ('cVar * 'tVar isabType list * 'tVar isabType)
   \<Rightarrow> ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) \<Rightarrow> bool" where
"typeCheckFunction M H B = (case H of (x,y,z) \<Rightarrow>
        (case B of (u,v,w) \<Rightarrow> if x = u then
     (case bindTypesWithVars v y of None \<Rightarrow> False
         | Some S \<Rightarrow> (case typeCheckTerm M S w of None \<Rightarrow> False
        | Some ty \<Rightarrow> (case compareTypes ty z of None \<Rightarrow> False
              | Some ty' \<Rightarrow> True))) else False))"

fun findAllBodiesByConstr :: "'cVar \<Rightarrow>
      ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list
     \<Rightarrow> (('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list
                  * ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list)" where
"findAllBodiesByConstr c [] = ([],[])"
| "findAllBodiesByConstr c ((x,y,z)#l) = (case findAllBodiesByConstr c l of (left,right)
       \<Rightarrow> if c = x then ((x,y,z)#left,right) else (left,(x,y,z)#right))"

(* this function type checks all function bodies for a function. *)
primrec typeCheckAllBodies :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
   \<Rightarrow> ('cVar * 'tVar isabType list * 'tVar isabType)
    \<Rightarrow> ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list
     \<Rightarrow> bool" where
"typeCheckAllBodies M c [] = True"
| "typeCheckAllBodies M c (a#l) = (typeCheckFunction M c a \<and> typeCheckAllBodies M c l)"

(* This function type checks all functions in an Isabelle file. *)
fun typeCheckFunctions :: "('cVar * ('tVar isabType list * 'tVar isabType)) list
    \<Rightarrow> ('cVar * 'tVar isabType list * 'tVar isabType) list
   \<Rightarrow> ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm ) list
    \<Rightarrow> bool" where
"typeCheckFunctions M [] S = (case S of [] \<Rightarrow> True | _ \<Rightarrow> False)"
| "typeCheckFunctions M ((x,y,z)#l) S = (case findAllBodiesByConstr x S of (left,right) \<Rightarrow>
         typeCheckAllBodies M (x,y,z) left \<and> typeCheckFunctions M l right)"

(* This function restructures a triple list to a finite map. *)
fun genLabelTypes :: "('cVar * 'tVar isabType list * 'tVar isabType) list
          \<Rightarrow> ('cVar * ('tVar isabType list * 'tVar isabType)) list" where
"genLabelTypes [] = []"
| "genLabelTypes ((x,y,z)#l) = update x (y,z) (genLabelTypes l)"

(* This function type checks all functions in an Isabelle Theory. *)
definition typeCheckFuns :: "('cVar * 'tVar isabType list * 'tVar isabType) list
   \<Rightarrow> ('cVar * 'iVar list * ('tVar isabType, 'cVar, 'iVar) isabTerm) list
    \<Rightarrow> bool" where
"typeCheckFuns H B = typeCheckFunctions (genLabelTypes H) H B"

end

(* datatype of K that is transferred from K in Isabelle. *)
datatype 'a kType = CellNameType | CellType | SingleKIsab |  KItemIsab | KLabelIsab
           | KResultIsab | SingleKListIsab | SingleListIsab | SingleSetIsab | SingleMapIsab
           | SingleBagIsab | CellConType | OtherKType 'a

datatype ('a, 'tVar, 'var) kConstr = UserConstr 'a | KCellIsab | ListCellIsab | SetCellIsab
           | MapCellIsab | BagCellIsab | ListItemIsab | SetItemIsab | MapItemIsab | KItemAsK
           | KAsList | KAsSet | KAsMap | SingleCellAsBag | StarCellAsBag | OptionCellAsBag
           | Cell | CellAsKList | KLabelAsKList | GetKLabelFun | The | CastFun 'tVar 'tVar
           | GetKListFun | GetCoreKLabelFun | GetCoreKListFun | ToKItemFun | Membership
           | KSubset | KMembership | HalfMembership | Congruence | IsNormalForm
           | UnifyFun 'tVar 'tVar | CellNameConstr 'var | ToKListFun | CastConstr 'tVar 'tVar
           | CaseInduct 'tVar 'tVar | FunRuleInduct 'tVar | FunRuleAux "('a, 'tVar, 'var) kConstr"
           | FunRuleOwise "('a, 'tVar, 'var) kConstr" | HasFunConstr 'tVar
           | KLabelConstr "('a, 'tVar, 'var) kConstr" | SubsortConstr 'tVar 'tVar
           | LabelFormConstr 'tVar | HoleConstr 'tVar | KItemConstr 'tVar
           | BuiltInFunConstr "('a, 'tVar, 'var) kConstr" 'tVar | AnywhereInduct 'tVar
           | AnywhereAux 'tVar | AnywhereSeq | KRuleInduct | BagRuleInduct 'tVar
           | TopRule

datatype isabelleStricts = KStrict "nat list" | KSeqStrict

(* every type in Isabelle translating types in types *)
locale KInIsabelleSyntax = 
IsabelleFun
  where Types = "Types :: 'tVar kType isabType set" (* type names *)
  and Constructs = "Constructs :: ('cVar, 'tVar kType isabType, 'var) kConstr set" (* constructor names *)
  and IsabVars = "IsabVars :: 'iVar set" (* isabelle variables *)
  and IVarOne = "IVarOne :: 'iVar"
  and IVarTwo = "IVarTwo :: 'iVar"
  and IVarThree = "IVarThree :: 'iVar"
  and freshCVar = "freshCVar :: ('cVar, 'tVar kType isabType, 'var) kConstr list
                              \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr"
  and freshIVar = "freshIVar :: 'iVar list \<Rightarrow> 'iVar"
  and renameCVar = "renameCVar :: ('cVar, 'tVar kType isabType, 'var) kConstr \<Rightarrow>
             ('cVar, 'tVar kType isabType, 'var) kConstr list
              \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr"
 for Types Constructs IsabVars IVarOne IVarTwo IVarThree freshCVar freshIVar renameCVar +
 fixes  Builtins :: "('cVar, 'tVar kType isabType, 'var) kConstr list" (* built-in function set *)
  and CellNames :: "'var set" (* set of cell names *)
  and UserConstrs :: "'cVar set"
  and KTokenNames :: "'kTVar set"
  and KTokenType :: "'tVar kType isabType"
  and KTokenConstr :: "'kTVar \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr"
  and translateType :: "'upVar \<Rightarrow> 'tVar kType"
  and translateLabel :: "'svar \<Rightarrow> 'cVar"
  and translateVar :: "'metaVar \<Rightarrow> 'iVar"
  and translateSyntaxSet :: "'svar set \<Rightarrow> ('cVar * 'tVar list) list option"
  and getToken :: "('cVar, 'tVar kType isabType, 'var) kConstr \<Rightarrow> ('tVar kType isabType,
            ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm"
  and getKTerm :: "('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr,
             'iVar) isabTerm \<Rightarrow> ('cVar, 'tVar kType isabType, 'var) kConstr"
assumes existOfToken : "\<forall> y . (\<exists> x . getToken y = Term (KTokenType) (KTokenConstr x) [])"
   and bijectionOfToken : "(\<forall> x . x = (getToken (getKTerm x)))
                                  \<and> (\<forall> x . x = (getKTerm (getToken x)))"
   and UserConstrsRule : "\<forall> a \<in> UserConstrs . UserConstr a \<in> Constructs"
context KInIsabelleSyntax begin

definition extendableFunctionBuiltinTypes :: "'tVar kType isabType set" where
"extendableFunctionBuiltinTypes = {OtherType SingleKIsab, OtherType KLabelIsab, OtherType SingleListIsab,
   OtherType SingleSetIsab, OtherType SingleMapIsab}"

definition extendableBuiltinTypes :: "'tVar kType isabType set" where
"extendableBuiltinTypes = {OtherType KItemIsab, OtherType KResultIsab} Un extendableFunctionBuiltinTypes"

definition nonExtendableBuiltinTypes :: "'tVar kType isabType set" where
"nonExtendableBuiltinTypes = {OtherType CellNameType,
     OtherType SingleKListIsab, IsabList (OtherType SingleKListIsab), OtherType SingleBagIsab,
    IsabList (OtherType SingleBagIsab), IsabList (OtherType SingleListIsab),OtherType CellConType,
        IsabList (OtherType SingleSetIsab), IsabList (OtherType SingleMapIsab), OtherType CellType}"

fun addSyntaxToList :: "'tVar kType isabType \<Rightarrow>
       (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool)
        \<Rightarrow> ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * isabelleStricts option * bool) list) list
    \<Rightarrow> ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"addSyntaxToList t tu [] = [(t,[tu])]"
| "addSyntaxToList t tu ((x,yl)#l) = (if t = x then (x,tu#yl)#l else
         (x,yl)#(addSyntaxToList t tu l))"

fun addSyntaxSetToList :: "'tVar kType isabType \<Rightarrow>
       ('cVar * 'tVar list) list \<Rightarrow> bool
        \<Rightarrow> ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * isabelleStricts option * bool) list) list
    \<Rightarrow> ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
       * 'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"addSyntaxSetToList t tu b [] = [(t,map (\<lambda> (x,z) . (UserConstr x,
                            (map (\<lambda> x . OtherType (OtherKType x)) z), None, b)) tu)]"
| "addSyntaxSetToList t tu b ((x,yl)#l) = (if t = x then
        (x,(map (\<lambda> (u,w) . (UserConstr u, (map (\<lambda> x . OtherType (OtherKType x)) w),
      None, b)) tu)@yl)#l else (x,yl)#(addSyntaxSetToList t tu b l))"

fun findTypeList :: "'tVar kType isabType \<Rightarrow> ('tVar kType isabType *
            (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list) list \<Rightarrow> 
      (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
                     * isabelleStricts option * bool) list option" where
"findTypeList a [] = None"
| "findTypeList a ((x,y)#l) = (if a = x then Some y else findTypeList a l)"

fun getAllUserTypesInIsab :: "('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
   * 'tVar kType isabType list * isabelleStricts option * bool) list) list
          \<Rightarrow> 'tVar kType isabType list" where
"getAllUserTypesInIsab [] = []"
| "getAllUserTypesInIsab ((x,y)#l) = x#getAllUserTypesInIsab l"

fun insertConstrsInList :: "'tVar kType isabType \<Rightarrow>
     (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
       * isabelleStricts option * bool) list \<Rightarrow> ('tVar kType isabType *
       (('cVar, 'tVar kType isabType, 'var) kConstr * 'tVar kType isabType list
        * isabelleStricts option * bool) list) list
   \<Rightarrow> ('tVar kType isabType * (('cVar, 'tVar kType isabType, 'var) kConstr
  * 'tVar kType isabType list * isabelleStricts option * bool) list) list" where
"insertConstrsInList a b [] = [(a,b)]"
| "insertConstrsInList a b ((x,y)#l) = (if a = x then (x,y@b)#l
          else (x,y)#(insertConstrsInList a b l))"

definition builtinSyntaxFormSyntax :: "(('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"builtinSyntaxFormSyntax = [(KItemAsK, [OtherType KItemIsab], OtherType SingleKIsab),
         (KAsList, [(IsabList (OtherType SingleKIsab))], OtherType SingleListIsab),
  (KAsSet, [(IsabList (OtherType SingleKIsab))], OtherType SingleSetIsab), (KAsMap,
      [IsabList (OtherType SingleKIsab), IsabList (OtherType SingleKIsab)], OtherType SingleMapIsab),
   (KCellIsab, [IsabList (OtherType SingleKIsab)], OtherType CellConType),
   (ListCellIsab, [IsabList (OtherType SingleListIsab)], OtherType CellConType),
   (SetCellIsab, [IsabList (OtherType SingleSetIsab)], OtherType CellConType),
   (MapCellIsab, [IsabList (OtherType SingleMapIsab)], OtherType CellConType),
   (BagCellIsab, [IsabList (OtherType SingleBagIsab)], OtherType CellConType),
   (Cell, [OtherType CellNameType, OtherType CellConType], OtherType CellType),
   (SingleCellAsBag, [OtherType CellType], OtherType SingleBagIsab),
   (OptionCellAsBag, [IsabOption (OtherType CellType)], OtherType SingleBagIsab),
   (StarCellAsBag, [OtherType CellNameType, IsabList (OtherType CellConType)],
     OtherType SingleBagIsab)]"

definition genSingleKLabelSyntax :: "'svar \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType)" where
"genSingleKLabelSyntax c = (KLabelConstr (UserConstr (translateLabel c)), [], OtherType KLabelIsab)"

definition genTokenKLabelSyntax :: "'cVar \<Rightarrow> 'tVar list \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType)" where
"genTokenKLabelSyntax c tyl = (KLabelConstr (UserConstr c),
           map (\<lambda> t . OtherType (OtherKType t)) tyl, OtherType KLabelIsab)"

fun genTokenKLabelSyntaxsAux :: "('cVar * 'tVar list) list
            \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) list" where
"genTokenKLabelSyntaxsAux [] = []"
| "genTokenKLabelSyntaxsAux ((x,y)#l) = (genTokenKLabelSyntax x y)#genTokenKLabelSyntaxsAux l"

definition genTokenKLabelSyntaxs :: "'svar set \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) list option" where
"genTokenKLabelSyntaxs a = (case translateSyntaxSet a of None \<Rightarrow> None
         | Some l \<Rightarrow> Some (genTokenKLabelSyntaxsAux l))"

definition genLabelFormSyntax :: "'upVar \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) option" where
"genLabelFormSyntax x = (case (translateType x) of KItemIsab \<Rightarrow> Some (LabelFormConstr (OtherType (translateType x)),
                [OtherType KLabelIsab,IsabList (OtherType SingleKListIsab)], OtherType (translateType x))
             | KResultIsab \<Rightarrow> Some (LabelFormConstr (OtherType (translateType x)),
                [OtherType KLabelIsab,IsabList (OtherType SingleKListIsab)], OtherType (translateType x))
           | OtherKType a \<Rightarrow> Some (LabelFormConstr (OtherType (translateType x)),
                [OtherType KLabelIsab,IsabList (OtherType SingleKListIsab)], OtherType (translateType x))
            | _ \<Rightarrow> None)"

definition genHoleFormSyntax :: "'upVar \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) option" where
"genHoleFormSyntax x = (case (translateType x) of KItemIsab \<Rightarrow> Some (HoleConstr (OtherType (translateType x)),
                [], OtherType (translateType x))
           | OtherKType a \<Rightarrow> Some (HoleConstr (OtherType (translateType x)),[], OtherType (translateType x))
            | _ \<Rightarrow> None)"

definition genKItemFormSyntax :: "'upVar \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) option" where
"genKItemFormSyntax x = (case (translateType x) of KResultIsab \<Rightarrow> Some (KItemConstr (OtherType (translateType x)),
                [OtherType KResultIsab], OtherType KItemIsab)
           | OtherKType a \<Rightarrow> Some (KItemConstr (OtherType (translateType x)),
                      [OtherType (translateType x)], OtherType KItemIsab)
            | _ \<Rightarrow> None)"

definition genSubsortFormSyntax :: "('upVar * 'upVar) \<Rightarrow> (('cVar, 'tVar kType isabType, 'var) kConstr
                         * 'tVar kType isabType list * 'tVar kType isabType) option" where
"genSubsortFormSyntax x = (case x of (t1,t2) \<Rightarrow>
(case (translateType t1) of KResultIsab \<Rightarrow> (case (translateType t2) of OtherKType t2' \<Rightarrow>
    Some (SubsortConstr (OtherType (translateType t1)) (OtherType (translateType t2)),
        [OtherType (translateType t2)], OtherType (translateType t1)) | _ \<Rightarrow> None)
    | KItemIsab \<Rightarrow> (case (translateType t2) of OtherKType t2' \<Rightarrow>
     Some (SubsortConstr (OtherType (translateType t1)) (OtherType (translateType t2)),
        [OtherType (translateType t2)], OtherType (translateType t1)) | _ \<Rightarrow> None)
    | OtherKType a \<Rightarrow> (case (translateType t2) of OtherKType t2' \<Rightarrow>
    Some (SubsortConstr (OtherType (translateType t1)) (OtherType (translateType t2)),
        [OtherType (translateType t2)], OtherType (translateType t1)) | _ \<Rightarrow> None)
    | _ \<Rightarrow> None))"

(* builtin function headers and bodies *)
definition theHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
           * 'tVar kType isabType list * 'tVar kType isabType)" where
"theHeader = (The, [IsabOption QuoteA], QuoteA)"

definition theBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list *
      ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"theBodies = (The, [IVarOne], CaseList (VarTerm (IsabList QuoteA) IVarOne)
     [(IsabSome (VarTerm QuoteA IVarTwo), VarTerm QuoteA IVarTwo)])"

(* builtin function headers and bodies *)
definition membershipHeader :: "(('cVar, 'tVar kType isabType, 'var) kConstr
           * 'tVar kType isabType list * 'tVar kType isabType)" where
"membershipHeader = (Membership, [QuoteA, IsabList QuoteA], BoolIsab)"

definition membershipBodies :: "(('cVar, 'tVar kType isabType, 'var) kConstr * 'iVar list *
      ('tVar kType isabType, ('cVar, 'tVar kType isabType, 'var) kConstr, 'iVar) isabTerm)" where
"membershipBodies = (case freshIVar [IVarOne, IVarTwo, IVarThree] of newVar \<Rightarrow>
(Membership,
       [IVarOne, IVarTwo], CaseList (VarTerm (IsabList QuoteA) IVarTwo) [(IsabEmptyList, IsabFalse),
       (IsabListCon (VarTerm QuoteA IVarThree) (VarTerm (IsabList QuoteA) newVar),
         (CaseList (IsabEqual (VarTerm QuoteA IVarOne) (VarTerm QuoteA IVarThree))
          [(IsabTrue, IsabTrue), (IsabFalse,
           AppFun Membership [VarTerm QuoteA IVarOne, VarTerm (IsabList QuoteA) newVar])]))]))"                                                                                                           

end

end