theory isabLambda
imports Main
begin

(* basic isabelle syntax
  a type is either a type variable ?x, or a typeConst with a name and a list of types
 *)
datatype ('tyVar, 'tyConst) isaType =
   TyVar 'tyVar
   | TyConst "'tyConst" "('tyVar, 'tyConst) isaType list"

(* an Isabelle term is a variable term, a constant an application or a lambda term *)
datatype ('tyVar, 'iVar, 'cVar) isaTerm =
   VarTm 'tyVar 'iVar | Const 'tyVar 'cVar
 | App "('tyVar, 'iVar, 'cVar) isaTerm" "('tyVar, 'iVar, 'cVar) isaTerm"
 | Lambda 'iVar 'tyVar "('tyVar, 'iVar, 'cVar) isaTerm"

(* the map look up function *)
fun lookup :: "'a \<Rightarrow> ('a * 'b) list \<Rightarrow> 'b option" where
"lookup a [] = None"
| "lookup a ((x,y)#l) = (if a = x then Some y else lookup a l)"

(* a map update function *)
fun update :: "'a \<Rightarrow> 'b \<Rightarrow> ('a * 'b) list \<Rightarrow> ('a * 'b) list" where
"update a b [] = [(a,b)]"
| "update a b ((x,y)#l) = (if a = x then ((x,b)#l) else update a b l)"

(* finite set insert function *)
primrec insertToList :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insertToList a [] = [a]"
| "insertToList a (b#l) = (if a = b then b#l else b#(insertToList a l))"

(* finite set union function *)
primrec insertAllToList :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"insertAllToList [] S = S"
| "insertAllToList (a#l) S = insertAllToList l (insertToList a S)"

(* a function to quantify all free variables in a type *)
primrec toMonoType :: "('tyVar, 'tyConst) isaType
             \<Rightarrow> ('tyVar list * ('tyVar, 'tyConst) isaType)"
  and toMonoTypeInList :: "('tyVar, 'tyConst) isaType list
             \<Rightarrow> ('tyVar list * ('tyVar, 'tyConst) isaType list)" where
"toMonoType (TyVar a) = ([a], TyVar a)"
| "toMonoType (TyConst t l) = (case toMonoTypeInList l of (vl, terms) \<Rightarrow> 
      (vl, TyConst t terms))"
| "toMonoTypeInList [] = ([], [])"
| "toMonoTypeInList (a#l) = (case toMonoType a of (S, t) \<Rightarrow> (case toMonoTypeInList l of
      (aS, T) \<Rightarrow> (insertAllToList S aS, t#T)))"

(* a function to delete a variable in a variable list *)
primrec deleteVarFromList :: "'iVar \<Rightarrow> 'iVar list \<Rightarrow> 'iVar list" where
"deleteVarFromList a [] = []"
| "deleteVarFromList a (x#l) = (if x = a then deleteVarFromList a l else x#(deleteVarFromList a l))"

(* a function to get all free variables in a term *)
primrec getFreeVarsInTerm :: "('tyVar, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar list" where
"getFreeVarsInTerm (VarTm t x) = [x]"
| "getFreeVarsInTerm (Const t x) = []"
| "getFreeVarsInTerm (App u v) = insertAllToList (getFreeVarsInTerm u) (getFreeVarsInTerm v)"
| "getFreeVarsInTerm (Lambda x t e) = deleteVarFromList x (getFreeVarsInTerm e)"

(* a function to substitute all occurrences of a variable by a type *)
primrec substInType :: "('tyVar, 'tyConst) isaType \<Rightarrow> 'tyVar \<Rightarrow> ('tyVar, 'tyConst) isaType
            \<Rightarrow> ('tyVar, 'tyConst) isaType"
  and substInTypeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> 'tyVar \<Rightarrow> ('tyVar, 'tyConst) isaType
            \<Rightarrow> ('tyVar, 'tyConst) isaType list" where
"substInType (TyVar a) x b = (if x = a then b else (TyVar a))"
| "substInType (TyConst x l) a b = TyConst x (substInTypeInList l a b)"
| "substInTypeInList [] a b = []"
| "substInTypeInList (x#l) a b = (substInType x a b)#(substInTypeInList l a b)"

(* a function to substitute all occurrences of variables by types represented by a map in a type term *)
fun substTypeByMap :: "('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar, 'tyConst) isaType" where
"substTypeByMap a [] = a"
| "substTypeByMap a ((x,y)#l) = substTypeByMap (substInType a x y) l"

(* a function to substitute all occurrences of a variable by a type in a map *)
fun substInMap :: "('tyVar * ('tyVar, 'tyConst) isaType) list \<Rightarrow> 'tyVar
  \<Rightarrow> ('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list" where
"substInMap [] x a = [(x,a)]"
| "substInMap ((x,y)#l) a b = ((x,substInType y a b)#(substInMap l a b))"

(* check if a variable occurred in a term *)
primrec occurInTerm :: "('tyVar, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar \<Rightarrow> bool" where
"occurInTerm (VarTm t x) a = (x = a)"
| "occurInTerm (Const t x) a = False"
| "occurInTerm (App u v) a = (occurInTerm u a \<or> occurInTerm v a)"
| "occurInTerm (Lambda x t e) a = (if a = x then False else occurInTerm e a)"

(* check if a variable occurred in a type term *)
primrec occurInType :: "('tyVar, 'tyConst) isaType \<Rightarrow> 'tyVar \<Rightarrow> bool"
   and occurInTypeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> 'tyVar \<Rightarrow> bool" where
"occurInType (TyVar a) x = (if a = x then True else False)"
| "occurInType (TyConst a l) x = occurInTypeInList l x"
| "occurInTypeInList [] x = False"
| "occurInTypeInList (a#l) x = ((occurInType a x) \<or> (occurInTypeInList l x))"

(* the functions below are implementing unification algorithm *)
(* a function to flip the orders of pairs in a pair list *)
fun orientInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
          \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list" where
"orientInList [] = []"
| "orientInList ((x,y)#l) = (case y of (TyVar a) \<Rightarrow> (case x of (TyConst b l')
            \<Rightarrow> (y,x)#(orientInList l)
        | TyVar b \<Rightarrow> (x,y)#(orientInList l)) | (TyConst a l') \<Rightarrow> (x,y)#(orientInList l))"

(* a function to delete type pairs if they are the same in a list *)
fun deleteInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
          \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list" where
"deleteInList [] = []"
| "deleteInList ((x,y)#l) = (if x = y then deleteInList l else (x,y)#(deleteInList l))"

(*  a function implementing the decompose algorithm in a unification process *)
fun decomposeInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> ('tyVar, 'tyConst) isaType list
           \<Rightarrow> (('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list option" where
"decomposeInList [] [] = Some []"
| "decomposeInList (a#l) (x#l') = (case decomposeInList l l' of None \<Rightarrow> None
           | Some la \<Rightarrow> Some ((a,x)#la))"
| "decomposeInList a b = None"

(* this function implements the unification algorithm for a list of type terms *)
function unifyInList :: "(('tyVar, 'tyConst) isaType * ('tyVar, 'tyConst) isaType) list
        \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"unifyInList [] = Some []"
| "unifyInList ((x,y)#l) = (case x of TyVar a \<Rightarrow> if occurInType y a then None
          else (case unifyInList l of None \<Rightarrow> None | Some m \<Rightarrow> Some (substInMap m a y))
   | TyConst a n \<Rightarrow> (case y of TyVar b \<Rightarrow> None
      | TyConst b n' \<Rightarrow> if a = b then (case decomposeInList n n' of None \<Rightarrow> None
         | Some na \<Rightarrow> unifyInList (l@(orientInList (deleteInList na)))) else None))"
by pat_completeness auto

(* the joinMap and joinMapAux functions unify two maps from type variables to type terms. *)
fun joinMapAux :: "('tyVar * ('tyVar, 'tyConst) isaType) list \<Rightarrow> 'tyVar
     \<Rightarrow> ('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"joinMapAux [] a b = Some [(a,b)]"
| "joinMapAux ((x,y)#l) a b = (if x = a then (case unifyInList (orientInList [(y,b)])
        of None \<Rightarrow> None | Some m \<Rightarrow> Some ((x,substTypeByMap y m)#l))
      else (case joinMapAux l a b of None \<Rightarrow> None
          | Some la \<Rightarrow> Some ((x,y)#la)))"
 
fun joinMap :: "('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list
   \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"joinMap [] S = Some S"
| "joinMap ((x,y)#l) S = (case joinMapAux S x y of None \<Rightarrow> None
       | Some m \<Rightarrow> joinMap l m)"

(* the function compares two type terms. In the location where the left is a tyVar
    and the right is a type term, the function crates a map from the tyVar to the term.
    So by comparing two type terms, the function generates a map including all unification factors
    of the two terms *)
fun getTypeMap :: "('tyVar, 'tyConst) isaType \<Rightarrow> ('tyVar, 'tyConst) isaType
    \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option"
  and  getTypeMapInList :: "('tyVar, 'tyConst) isaType list \<Rightarrow> ('tyVar, 'tyConst) isaType list
    \<Rightarrow> ('tyVar * ('tyVar, 'tyConst) isaType) list option" where
"getTypeMap (TyVar x) b = Some [(x,b)]"
| "getTypeMap (TyConst t l) b = (case b of TyVar y \<Rightarrow> None
       | (TyConst t' l') \<Rightarrow> if t = t' then getTypeMapInList l l' else None)"
| "getTypeMapInList [] [] = Some []"
| "getTypeMapInList (a#l) (b#l') = (case getTypeMap a b of None \<Rightarrow> None
        | Some m1 \<Rightarrow> (case getTypeMapInList l l' of None \<Rightarrow> None
        | Some m2 \<Rightarrow> joinMap m1 m2))"
| "getTypeMapInList a g = None"

(* an Isabelle Theory conntains a set of type consts, a set of types,
    a set of tyVars and terms. and a set of function type names. 
    we require all function applications are binary relations here. *)
locale ITheory =
 fixes TypeConsts :: "'tyConst set" 
 and Types :: "('tyVar, 'tyConst) isaType set"
 and TmConsts :: "'cVar set"
 and typeIds :: "'tyVar set"
 and tmIds :: "'iVar set"
 and Terms :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm set"
 and FunType :: "'tyConst"
 and freshLambdaVar :: "'iVar list \<Rightarrow> 'iVar"
 assumes funTypeRule : "\<forall> a b . a \<in> Types \<and> a = TyConst FunType b \<longrightarrow> (length b = 2)"
 and freshLambdaVarRule : "\<forall> S . freshLambdaVar S \<in> set S"
context ITheory begin

(* given a term and a mapping from variables to poly-type lists, 
    the function type checks if every var-type relation in the map makes sense.
    If so, we outputs the most specific var-type relations *)
primrec typeCheckInTerm :: "('iVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
      \<Rightarrow> ('cVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
    \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
            \<Rightarrow> (('iVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
      * ('tyVar list * ('tyVar, 'tyConst) isaType)) option" where
"typeCheckInTerm S M (VarTm t x) = (case lookup x S of None \<Rightarrow>
        Some (update x (toMonoType t) S, toMonoType t)
          | Some (binds, t') \<Rightarrow> (case unifyInList (orientInList [(t,t')]) of None \<Rightarrow> None
         | Some tm \<Rightarrow> (case toMonoType (substTypeByMap t tm) of ta 
      \<Rightarrow> Some (update x ta S, ta))))"
| "typeCheckInTerm S M (Const t c) = (case lookup c M of None \<Rightarrow> None
        | Some (binds, t') \<Rightarrow> (case unifyInList (orientInList [(t,t')]) of None \<Rightarrow> None
      | Some tm \<Rightarrow> (case toMonoType (substTypeByMap t tm) of ta \<Rightarrow> 
     Some (S, ta))))"
| "typeCheckInTerm S M (App a b) = (case typeCheckInTerm S M a of
    Some (S', binds, TyConst tc [lt,rt])
      \<Rightarrow> if tc = FunType then (case typeCheckInTerm S' M b of None \<Rightarrow> None
        | Some (Sa, binds, lt') \<Rightarrow>
      (case unifyInList (orientInList [(lt,lt')]) of None \<Rightarrow> None
             | Some tm \<Rightarrow> Some (Sa, toMonoType (substTypeByMap rt tm)))) else None
      | _ \<Rightarrow> None)"
| "typeCheckInTerm S M (Lambda x t e) =
       (case typeCheckInTerm (update x (toMonoType t) S) M e of None \<Rightarrow> None
      | Some (S',binds, t') \<Rightarrow> Some (S, toMonoType (TyConst FunType [t, t'])))"

(* the function substitutes a variable with another variable. *)
primrec substInTermByVar :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar \<Rightarrow> 'iVar
      \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm" where
"substInTermByVar (VarTm t x) a b = (if a = x then VarTm t b else VarTm t x)"
| "substInTermByVar (Const t x) a b = (Const t x)"
| "substInTermByVar (App u v) a b = App (substInTermByVar u a b) (substInTermByVar v a b)"
| "substInTermByVar (Lambda x t e) a b = (if x = a then Lambda x t e
     else Lambda x t (substInTermByVar e a b))"

(* the function substitutes a variable with a term *)
function substInTerm :: "(('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> 'iVar
     \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
      \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm" where
"substInTerm (VarTm t x) y b = (if x = y then b else (VarTm t x))"
| "substInTerm (Const t x) y b = Const t x"
| "substInTerm (App u v) y b = App (substInTerm u y b) (substInTerm v y b)"
| "substInTerm (Lambda x t e) y b = (if y = x then
  Lambda x t e else if occurInTerm b x then
    (case freshLambdaVar (y#((getFreeVarsInTerm e)@(getFreeVarsInTerm b))) of newVar
      \<Rightarrow> Lambda newVar t (substInTerm (substInTermByVar e x newVar) y b))
            else Lambda x t (substInTerm e y b))"
by pat_completeness auto

(* the function to apply beta reduction. *)
inductive LambdaInduct :: "('cVar * ('tyVar list * ('tyVar, 'tyConst) isaType)) list
   \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm
    \<Rightarrow> (('tyVar, 'tyConst) isaType, 'iVar, 'cVar) isaTerm \<Rightarrow> bool" where
unitRule : "typeCheckInTerm [] M (App (Lambda x t e) e') = Some v
                     \<Longrightarrow> LambdaInduct M (App (Lambda x t e) e') (substInTerm e x e')"

end

datatype a = A | B int | CtoA c | BtoA b
and c = C1 b | C2 a 
and b = B1 int int | B2 int int | CtoB c

fun dataeqa and dataeqb and dataeqc where
"dataeqa A A = True"
| "dataeqa (B x) (B y) = ( x = y)"
| "dataeqa (CtoA x) (CtoA y) = dataeqc x y"
| "dataeqa (CtoA x) (BtoA (CtoB y)) = dataeqc x y"
| "dataeqa (BtoA (CtoB x)) (CtoA y) = dataeqc x y"
| "dataeqa (BtoA x) (BtoA y) = dataeqb x y"
| "dataeqa x y = False"
| "dataeqb (B1 x y) (B1 u v) = ((x = u) \<and> (y = v))"
| "dataeqb (B2 x y) (B2 u v) = ((x = u) \<and> (y = v))"
| "dataeqb (CtoB x) (CtoB y) = dataeqc x y"
| "dataeqb x y = False"
| "dataeqc (C1 x) (C1 y) = dataeqb x y"
| "dataeqc (C2 x) (C2 y) = dataeqa x y"
| "dataeqc x y = False"

inductive dataeq where
basic: "dataeqa x y \<Longrightarrow> dataeq x y"
| refle: "dataeq x x"
| symtric: "dataeq x y \<Longrightarrow> dataeq y x"
| trans: "\<lbrakk> dataeq x y ; dataeq y z\<rbrakk> \<Longrightarrow> dataeq x z"

quotient_type aq = "a" / "dataeq"
  apply (simp add: Equiv_Relations.equivp_reflp_symp_transp)
  apply (rule conjI)
   apply (simp add: reflp_def)
   apply (simp add: dataeq.refle)
  apply (rule conjI)
   apply (simp add: symp_def,clarsimp)
   apply (simp add: dataeq.symtric)
  apply (simp add:transp_def,clarsimp)
  apply (simp add: dataeq.trans)
  done

inductive databeq where
basic: "dataeqb x y \<Longrightarrow> databeq x y"
| refle: "databeq x x"
| symtric: "databeq x y \<Longrightarrow> databeq y x"
| trans: "\<lbrakk> databeq x y ; databeq y z\<rbrakk> \<Longrightarrow> databeq x z"

quotient_type aqb = "b" / "databeq"
  apply (simp add: Equiv_Relations.equivp_reflp_symp_transp)
  apply (rule conjI)
   apply (simp add: reflp_def)
   apply (simp add: databeq.refle)
  apply (rule conjI)
   apply (simp add: symp_def,clarsimp)
   apply (simp add: databeq.symtric)
  apply (simp add:transp_def,clarsimp)
  apply (simp add: databeq.trans)
  done

inductive dataceq where
basic: "dataeqc x y \<Longrightarrow> dataceq x y"
| refle: "dataceq x x"
| symtric: "dataceq x y \<Longrightarrow> dataceq y x"
| trans: "\<lbrakk> dataceq x y ; dataceq y z\<rbrakk> \<Longrightarrow> dataceq x z"

quotient_type aqc = "c" / "dataceq"
  apply (simp add: Equiv_Relations.equivp_reflp_symp_transp)
  apply (rule conjI)
   apply (simp add: reflp_def)
   apply (simp add: dataceq.refle)
  apply (rule conjI)
   apply (simp add: symp_def,clarsimp)
   apply (simp add: dataceq.symtric)
  apply (simp add:transp_def,clarsimp)
  apply (simp add: dataceq.trans)
  done

(* datatype a = A | B int | CtoA c | BtoA b
and c = C1 b | C2 a 
and b = B1 int int | B2 int int | CtoB c*)

inductive usea where
"usea ((abs_aq A),env) (None,env)"
| "\<lbrakk> abs_aq (B x) = e\<rbrakk> \<Longrightarrow> usea (e, env) (Some x, env)"
| "\<lbrakk>abs_aq (CtoA x) = e\<rbrakk>\<Longrightarrow> usea (e, env) (None,env)"

inductive useb :: "aq \<times> (int \<Rightarrow> int) \<Rightarrow> aq option \<times> (int \<Rightarrow> int) \<Rightarrow> bool" where
"useb (a,b) (None,b)"

end