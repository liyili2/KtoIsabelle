(* File: mp8common.ml *)

let space() = print_string " ";;

type 'a nelist = {first : 'a; rest : 'a list}

let nelist_map f {first = x; rest = ys} = {first = f x; rest = List.map f ys}
let nelist_fold_right f b {first = x; rest = ys} = f x (List.fold_right f ys b)
let nelist_gen_fold_right f1 f_rest b {first = x; rest = ys} =
    f1 x (List.fold_right f_rest ys b)
let nelist_fold_left f a  {first = x; rest = ys} = List.fold_left f (f a x) ys
let nelist_gen_fold_left f1 frest a {first = x; rest = ys} = List.fold_left frest (f1 a x) ys
let nelist_app f1 frest {first = x; rest = ys} = f1 x; List.iter frest ys
let list_of_nelist {first = x; rest = ys} = x :: ys
let nelist_cons x {first = y; rest = ys} = {first = x; rest = y::ys}
let nelist_append {first = x; rest = xs} nel2 = {first = x; rest = xs @ list_of_nelist nel2}
let nelist_singleton x = {first = x; rest = []}


let option_map f o = (match o with None -> None | Some x -> Some (f x))
let option_compose f g o = option_map f (option_map g o)
let partial_map_compose f g x =
    match g x with None -> None | Some y -> f y

(* expressions for MicroML *)

type bin_op =
     IntPlusOp
   | IntMinusOp
   | IntTimesOp
   | IntDivOp
   | RealPlusOp
   | RealMinusOp
   | RealTimesOp
   | RealDivOp
   | ConcatOp
   | ConsOp
   | CommaOp
   | EqOp
   | GreaterOp

let print_binop = function
     IntPlusOp  -> print_string "+"
   | IntMinusOp -> print_string "-"
   | IntTimesOp -> print_string "*"
   | IntDivOp -> print_string "/"
   | RealPlusOp -> print_string "+."
   | RealMinusOp -> print_string "-."
   | RealTimesOp -> print_string "*."
   | RealDivOp -> print_string "/."
   | ConcatOp -> print_string "^"
   | ConsOp -> print_string "::"
   | CommaOp -> print_string ","
   | EqOp  -> print_string "="
   | GreaterOp -> print_string ">"

type prim_op = BinOp of bin_op | IntNeg | HdOp | TlOp | FstOp | SndOp

let print_prim_op = function
     BinOp b -> print_binop b
   | IntNeg -> print_string "~"
   | HdOp -> print_string "hd"
   | TlOp -> print_string "tl"
   | FstOp -> print_string "fst"
   | SndOp -> print_string "snd"

type const =
     BoolConst of bool
   | IntConst of int
   | RealConst of float
   | StringConst of string
   | NilConst
   | UnitConst
   | PrimOp of prim_op

let print_const = function
   BoolConst b     -> print_string(if b then "true" else "false")
 | IntConst i      -> print_int i
 | RealConst f     -> (print_float f;if ceil f = floor f then (print_string"0") else ())
 (* FIXME: will print 2.0 as "2." ---Done -ELG *)
 (* TODO: we would need to escape string here, if we were to decide to use \n and \t, etc..  ---Done -ELG *)
 | StringConst s   -> print_string "\""; print_string (String.escaped s); print_string "\""
 | NilConst        -> print_string "nil"
 | UnitConst       -> print_string "()"
 | PrimOp p        -> print_prim_op p


type dec =
     Val of string option * exp
   | Rec of (string * exp) nelist
   | Seq of dec * dec
   | Local of dec * dec

and exp =
   | VarExp of string
   | ConstExp of const
   | IfExp of exp * exp * exp
   | AppExp of exp * exp
   | FnExp of string pattern
   | LetExp of dec * exp
   | RaiseExp of exp
   | Handle of exp * (int option pattern nelist)

and 'a pattern = 'a * exp

let rec print_exc_match (int_opt, e) =
    (match int_opt with None -> print_string "_" | Some n -> print_int n);
    print_string " => ";
    print_exp e

and print_exp = function
   VarExp s -> print_string s
 | ConstExp c -> (match c with
                     PrimOp(BinOp _) -> (print_string "(op "; print_const c; print_string ")")
                   | _ -> print_const c)
 | IfExp(e1,e2,e3)->print_string "if "; print_exp e1;
                 print_string " then "; print_exp e2;
                 print_string " else "; print_exp e3
 | AppExp (AppExp (ConstExp(PrimOp(BinOp b)), e1), e2) ->
   if b = CommaOp then print_string "(";
   (match e1 with VarExp _ | ConstExp _ | AppExp _ ->  print_exp e1
    | _ -> print_string "("; print_exp e1; print_string ")");
   space(); print_binop b; space();
   (match e2 with AppExp (AppExp (ConstExp(PrimOp(BinOp b')), _), _) when b' <> CommaOp ->
      print_string "("; print_exp e2; print_string ")"
    | _ -> print_exp e2);
   if b = CommaOp then print_string ")";
 | AppExp(e1,e2) ->
   (match e1 with FnExp _ -> print_string "("; print_exp e1; print_string ")"
    | _ ->  print_exp e1);
   space();
   (match e2 with AppExp _ | FnExp _ -> print_string "("; print_exp e2; print_string ")"
    | _ ->  print_exp e2)
 | FnExp f -> print_func (* "fn " " -> " *) f
 | LetExp (d,e2) -> print_string "let "; print_dec d; print_string " in ";
   print_exp e2; print_string " end"
 | RaiseExp e -> print_string "raise "; print_exp e
 | Handle (e,{first = exc_match; rest = match_list}) ->
                 print_string "handle "; print_exp e; print_string" with ";
                 print_exc_match exc_match;
                 List.iter (fun m ->(print_string " | "; print_exc_match m)) match_list

and print_dec = function
   Val (Some s, e) -> print_string ("val "^s^" = "); print_exp e
 | Val (None, e) -> print_string ("val _ = "); print_exp e
(*
 | Rec {first = f ; rest = fs} -> print_func "fun " " = " f;
    List.iter (fun x -> print_string (" " ^ x)) args;
    print_string " =\n    ";
    print_exp body
*)
 | Rec {first = (name, fn) ; rest = fs} ->
     print_string ("val rec " ^ name ^ " = "); print_exp fn;
     List.iter (fun (name, fn) ->
       print_newline();
       print_string ("and " ^ name ^ " = "); print_exp fn)
     fs

 | Seq (d1,d2) -> print_dec d1; print_newline(); print_dec d2
 | Local (d1,d2) -> print_string "local "; print_dec d1;
   print_string "\nin "; print_dec d2; print_string " end"

(* and print_func pre mid (s,e) = print_string (pre^s^mid); print_exp e *)
and print_func (s,e) = print_string ("fn " ^ s ^ " => "); print_exp e

type tyExp =
     VarType of int
   | BoolType
   | IntType
   | RealType
   | StringType
   | UnitType
   | FunType of tyExp * tyExp
   | PairType of tyExp * tyExp
   | ListType of tyExp
   | OptionType of tyExp

let rec expand n (list,len) =
    let q = n / 26 in
        if q = 0 then (n :: list, len + 1)
        else expand q (((n mod 26)::list), len + 1);;

let showVarType n =
   let (num_list,len) =
       match (expand n ([],0))
       with ([],l) -> ([],l) (* can't actually happen *)
          | ([s],l) -> ([s],l)
          | (x::xs,l) -> ((x - 1) :: xs, l)
   in
   let s = (String.create len)
   in
   let _ =
    List.fold_left
    (fun n c -> (String.set s n c; n + 1))
    0
    (List.map (fun x -> Char.chr(x + 97)) num_list)  (* Char.code 'a' = 97 *)
   in "'"^s;;

let rec print_tyExp = function
    VarType n -> print_string (showVarType n)
  | BoolType -> print_string "bool"
  | IntType -> print_string "int"
  | RealType -> print_string "real"
  | StringType -> print_string "string"
  | UnitType -> print_string "unit"
  | FunType (dom, range) -> parens_print_tyExp dom; print_string " -> "; print_tyExp range
  | PairType (fst,snd) -> parens_print_tyExp fst; print_string " * "; print_tyExp snd
  | ListType t -> parens_print_tyExp t; print_string " list"
  | OptionType t -> parens_print_tyExp t; print_string " option"

and parens_print_tyExp t  = match t with
    VarType _ | BoolType | IntType | RealType | StringType | UnitType | ListType _ | OptionType _  -> print_tyExp t
  | FunType _ | PairType _ -> print_string "("; print_tyExp t; print_string ")"


(*fresh type variable*)
let (fresh, reset) =
   let nxt = ref 0 in
   let f () = (nxt := !nxt + 1; VarType(!nxt)) in
   let r () = nxt := 0 in
    (f, r)

(* environments *)
type 'exp env = (string * 'exp) list

let print_env prnt_exp gamma =
  let rec print_env_aux gamma =
    match gamma with
       []        -> ()
     | (x,y)::xs -> print_string x; print_string " : "; prnt_exp y;
                    match xs with [] -> () | _  -> print_string ", ";
                                                   print_env_aux xs
  in
    print_string "{ "; print_env_aux gamma; print_string " }"


let rec pretty_print_env prnt_exp gamma =
    (match gamma with
       []        -> ()
     | (x,y)::xs ->
       (match xs with [] -> () | _  -> pretty_print_env prnt_exp xs;
                                       print_newline());
       print_string "val "; print_string x; print_string " : "; prnt_exp y)

(*environment operations*)
let empty_env = ([]:'exp env)
let make_env x y = ([(x,y)]:'exp env)
let rec lookup_env (gamma:'exp env) x =
  match gamma with
     []        -> None
   | (y,z)::ys -> if x = y then Some z else lookup_env ys x
let sum_env (delta:'exp env) (gamma:'exp env) = ((delta@gamma):'exp env)
let insert_env (gamma:'exp env) x y = (x, y) :: gamma

let int_op_ty = FunType(IntType, (FunType(IntType, IntType)))
let real_op_ty = FunType(RealType, (FunType(RealType, RealType)))
let string_op_ty = FunType(StringType, (FunType(StringType, StringType)))

let init_type_env =
    insert_env (insert_env empty_env "mod" int_op_ty)
    "@" (FunType (ListType (VarType 0),
          FunType (ListType (VarType 0), ListType (VarType 0))))

(* fixed signatures *)
let bin_op_signature = function
     IntPlusOp   -> int_op_ty
   | IntMinusOp   -> int_op_ty
   | IntTimesOp   -> int_op_ty
   | IntDivOp   -> int_op_ty
   | RealPlusOp   -> real_op_ty
   | RealMinusOp   -> real_op_ty
   | RealTimesOp   -> real_op_ty
   | RealDivOp   -> real_op_ty
   | ConcatOp -> string_op_ty
   | ConsOp ->
       let alpha = fresh() in
           FunType(alpha, (FunType ((ListType alpha), (ListType alpha))))
   | CommaOp ->
       let alpha = fresh() in
       let beta = fresh() in
           FunType(alpha, (FunType(beta, (PairType (alpha, beta)))))
(*    | EqOp -> FunType(IntType, (FunType(IntType, BoolType))) *)
   | EqOp -> let alpha = fresh() in FunType(alpha, (FunType(alpha, BoolType)))
   (* EqOp works only for integers, but GreaterOp works for any type? *)
   | GreaterOp -> let alpha = fresh() in FunType(alpha, (FunType(alpha, BoolType)))

let prim_op_signature = function
    BinOp b -> bin_op_signature b
  | IntNeg -> FunType(IntType, IntType)
  | HdOp -> let alpha = fresh() in FunType(ListType alpha, alpha)
  | TlOp -> let alpha = fresh() in FunType(ListType alpha, ListType alpha)
  | FstOp -> let alpha = fresh() in let beta = fresh() in FunType(PairType(alpha,beta),alpha)
  | SndOp -> let alpha = fresh() in let beta = fresh() in FunType(PairType(alpha,beta),beta)

let const_signature = function
   BoolConst b -> BoolType
 | IntConst n -> IntType
 | RealConst f -> RealType
 | StringConst s -> StringType
 | NilConst -> ListType (fresh())
 | UnitConst -> UnitType
 | PrimOp p -> prim_op_signature p

(*judgment*)
type 'exp judgment_exp = { gamma_exp:'exp env; exp:exp; result: 'exp }
type 'exp judgment_dec = { gamma_dec:'exp env; dec:dec; result_env:'exp env }
type 'exp judgment =
    ExpJudgment of 'exp judgment_exp
  | DecJudgment of 'exp judgment_dec

let print_jexp prnt_exp ({exp=exp; gamma_exp=gamma; result=rexp} : 'exp judgment_exp) =
  print_env prnt_exp gamma; print_string " |= "; print_exp exp;
  print_string " : "; prnt_exp rexp

let print_jdec prnt_exp { gamma_dec=gamma; dec=dec; result_env=result_env } =
  print_env prnt_exp gamma; print_string " |= "; print_dec dec;
  print_string " :: "; print_env prnt_exp result_env

let print_judg prnt_exp = function
  | ExpJudgment j -> print_jexp prnt_exp j
  | DecJudgment j -> print_jdec prnt_exp j

type 'exp proof = {antecedents : 'exp proof list; conclusion : 'exp judgment}

(*proof printing*)

let print_proof prnt_exp p =
  let depth_max = 10 in
  let rec print_struts = function
     []    -> ()
   | _::[] -> print_string "|-"
   | x::xs -> print_string (if x then "  " else "| "); print_struts xs
  in let rec print_proof_aux {antecedents = ant; conclusion = conc} depth lst =
    print_newline(); print_string "  "; print_struts lst;
    if (depth > 0) then print_char('-');
    let assum = (print_judg prnt_exp conc; ant)
    in if depth <= depth_max then
      print_assum depth lst assum
  and print_assum depth lst assum =
    match assum with
       []     -> ()
     | p'::ps -> print_proof_aux p' (depth + 1) (lst@[ps=[]]);
                 print_assum depth lst ps
  in
    print_proof_aux p 0 []; print_newline(); print_newline()
(*----------------------gather_exp_ty_constraints - mp5.ml --------------------*)
(*now to create the proof + gather the constraints
  gather_exp_ty_constraints : tyExp judgment -> (tyExp proof * (expType * expType) list) option
*)

let rec gather_exp_ty_constraints judgment =
    let {gamma_exp = gamma; exp = exp; result = tau} = judgment in
    match exp
(*
----------------------------------------------
Gamma |- c : tau | {tau = const_signature (c)}
*)
    with ConstExp c ->
      let tau' = const_signature c in
         Some ({antecedents = []; conclusion = ExpJudgment judgment}, [(tau, tau')])
(*
-----------------------------------
Gamma |- x : tau | {tau = Gamma(x)}
*)
    | VarExp x ->
      option_map
       (fun tau' -> ({antecedents = []; conclusion = ExpJudgment judgment}, [(tau, tau')]))
       (lookup_env gamma x)
(*
Gamma |- e1 : bool | C1  Gamma |- e2 : tau | C2  Gamma |- e3 : tau | C3
-------------------------------------------------------------------------
      Gamma |- if e1 then e2 else e3 : tau | C1 U C2 U C3
*)
    | IfExp (e1, e2, e3) ->
      (match
        (gather_exp_ty_constraints {gamma_exp = gamma; exp = e1; result = BoolType},
         gather_exp_ty_constraints {gamma_exp = gamma; exp = e2; result = tau},
         gather_exp_ty_constraints {gamma_exp = gamma; exp = e3; result = tau})
       with (Some(bool_pf, c1), Some(then_pf, c2), Some(else_pf, c3))
        -> Some({antecedents = [bool_pf; then_pf; else_pf]; conclusion = ExpJudgment judgment},
                   (c1 @ (c2 @ c3)))
       | _ -> None)
(*
Gamma |- e1 : tau1 -> tau | C1   Gamma |- e2 : tau1 | C2
--------------------------------------------------------
        Gamma |- e1 e2 : tau | C1 U C2
*)
    | AppExp (e1, e2) ->
      let tau1 = fresh() in
      (match
        (gather_exp_ty_constraints {gamma_exp = gamma; exp = e1; result = FunType(tau1,tau)},
         gather_exp_ty_constraints {gamma_exp = gamma; exp = e2; result = tau1})
       with (Some(e1_pf, c1), Some(e2_pf, c2))
           -> Some({antecedents = [e1_pf; e2_pf]; conclusion = ExpJudgment judgment},
                   (c1 @ c2))
       | _ -> None)
(*
       {x -> tau1} + Gamma |- e : tau2 | C
-----------------------------------------------------
Gamma |- fun x -> e : tau | {tau = tau1 -> tau2} U C
*)
    | FnExp (x,e) ->
      let tau1 = fresh() in let tau2 = fresh() in
      option_map (fun (pf, c) ->
                   ({antecedents = [pf]; conclusion = ExpJudgment judgment},
            (tau, FunType(tau1, tau2)) :: c))
      (gather_exp_ty_constraints
       {gamma_exp = (insert_env gamma x tau1); exp = e; result = tau2})
(*

Gamma |- dec : Delta | C1    Delta + Gamma |- e : tau | C2
-----------------------------------------------------------
       Gamma |- let dec in e end : tau | C1 U C2
*)
    | LetExp (dec, e) ->
      (match gather_dec_ty_constraints gamma dec
       with Some (dec_pf, env_inc, c1) ->
        (option_map
         (fun (e_pf, c2) ->
              ({antecedents = [dec_pf ; e_pf]; conclusion = ExpJudgment judgment},
                (c2 @ c1)))
         (gather_exp_ty_constraints
          {gamma_exp = (sum_env env_inc gamma); exp = e; result = tau}))
       | None -> None)
(*
Gamma |- e : int | C
--------------------------
Gamma |- raise e : tau | C
*)
    | RaiseExp e ->
      option_map
      (fun (pf, c) -> ({antecedents = [pf]; conclusion = ExpJudgment judgment}, c))
      (gather_exp_ty_constraints {gamma_exp = gamma; exp = e; result = IntType})
(*
  Gamma |- e : tau | C  Gamma |- e1 : tau | C1 ... Gamma |- en : tau | Cn
---------------------------------------------------------------------------
Gamma |- handle e with n1 -> e1 | ... | nm -> em  : tau | C U C1 U ... U Cn
*)
    | Handle (e, matches) ->
      let gather_proofs (int_opt, exp) res=
          (match res with Some (proofs, consts) ->
             option_map
             (fun (pf, c) -> (pf::proofs, c @ consts))
             (gather_exp_ty_constraints {gamma_exp = gamma; exp = exp; result = tau})
          | None -> None) in
      (match (nelist_fold_right gather_proofs (Some([],[])) matches)
       with Some (ei_pfs, cis) ->
          (option_map
           (fun (e_pf, c) ->
            ({antecedents= e_pf::ei_pfs; conclusion = ExpJudgment judgment}, c@cis))
           (gather_exp_ty_constraints {gamma_exp = gamma; exp = e; result = tau}))
       | None -> None)


and gather_dec_ty_constraints gamma dec =
(*
     Gamma |- e : tau | C
----------------------------------
Gamma |- val x = e : {x : tau} | C
*)
    match dec with Val (Some v,e) ->
       let tau = fresh() in
       let env_inc = make_env v tau in
       option_map
       (fun (e_pf, c) ->
        ({antecedents=[e_pf];
         conclusion =
          DecJudgment {gamma_dec = gamma; dec = dec; result_env = env_inc}},
        env_inc,
        c))
        (gather_exp_ty_constraints {gamma_exp = gamma; exp = e; result = tau})
(*
     Gamma |- e : tau | C
----------------------------------
Gamma |- val _ = e : {} | C
*)
    | Val (None,e) ->
       let tau = fresh() in
       option_map
       (fun (e_pf, c) ->
        ({antecedents=[e_pf];
         conclusion =
          DecJudgment {gamma_dec = gamma; dec = dec; result_env = empty_env}},
        empty_env,
        c))
        (gather_exp_ty_constraints {gamma_exp = gamma; exp = e; result = tau})
(*
       {xn : taun} + ... + {x1 : tau1} + Gamma |- ei : taui | Ci (for i = 1 ... n}
--------------------------------------------------------------------------------------------
Gamma |- val rec x1 = e1 and ... and xn = en | {xn : taun} + ... + {x1 : tau1}
   C1 U ... U Cn U {tau1 = tau1a -> tau1b; ...; taun = tauna -> taunb}
*)
     | Rec decs ->
       let env_inc = nelist_fold_left
                     (fun env1 -> fun (xi,_) -> insert_env env1 xi (fresh()))
                     empty_env
                     decs  in
       let rec_env = sum_env env_inc gamma in
       let merge_hyps (xi,ei)  part_hyps_opt =
           (match part_hyps_opt
            with Some (part_hyps, part_consts) ->
            (match lookup_env rec_env xi with Some taui ->
            (option_map
             (fun (ei_pf, ei_consts) ->
              (ei_pf::part_hyps, ((taui,FunType(fresh(),fresh()))::(ei_consts @ part_consts))))
             (gather_exp_ty_constraints
              {gamma_exp = rec_env; exp = ei; result = taui}))
             | None -> None)
           | None -> None) in
       let hyps = nelist_fold_right merge_hyps (Some([],[])) decs in
       (option_map
        (fun (asms, consts) ->
             ({antecedents = asms;
               conclusion = DecJudgment {gamma_dec=gamma; dec = dec;
                                         result_env = env_inc}},
              env_inc, consts))
         hyps)
(*
Gamma |- dec1 : Delta1 | C1   Delta1 + Gamma |- dec2 : Delta2 | C2
--------------------------------------------------------------------
        Gamma | dec1 dec2 : Delta2 + Delta1 | C1 U C2
*)
     | Seq (dec1, dec2) ->
       (match gather_dec_ty_constraints gamma dec1
        with Some (dec1_pf, delta1, c1) ->
         let gamma1 = sum_env delta1 gamma in
         (option_map
          (fun (dec2_pf, delta2, c2) ->
            let env_inc = sum_env delta2 delta1 in
            ({antecedents = [dec1_pf; dec2_pf];
              conclusion = DecJudgment{gamma_dec = gamma; dec = dec;
                                       result_env = env_inc}},
             env_inc, c1 @ c2))
         (gather_dec_ty_constraints gamma1 dec2))
       | None -> None)
(*
Gamma |- dec1 : Delta1 | C1  Delta1 + Gamma |- dec2 : Delta2 | C2
------------------------------------------------------------------
           Gamma | local dec1 in dec2 : Delta2 | C1 U C2
*)
     | Local(dec1, dec2) ->
       (match gather_dec_ty_constraints gamma dec1
        with Some (dec1_pf, delta1, c1) ->
         let gamma1 = sum_env delta1 gamma in
         (option_map
          (fun (dec2_pf, delta2, c2) ->
            ({antecedents = [dec1_pf; dec2_pf];
              conclusion = DecJudgment{gamma_dec = gamma; dec = dec;
                                       result_env = delta2}},
                   delta2, c1 @ c2))
         (gather_dec_ty_constraints gamma1 dec2))
       | None -> None)

(*-------------------end of gather_exp_ty_constraints - mp5.ml --------------------*)

type constTy =
  | BoolTy
  | IntTy
  | RealTy
  | StringTy
  | UnitTy
  | FunTy
  | PairTy
  | ListTy
  | OptionTy

type 'constTy term = TmVar of int | TmConst of ('constTy * 'constTy term list)

type 'constTy substitution = (int * 'constTy term) list

let subst_has_var s n = List.exists (fun (m,t) -> n = m) s

(*------------------------------unify - mp6.ml------------------------------*)
(* Not needed here
(* Problem 1 *)
(* Write a function from unit to constTy term to produce a
representation of each of the following types: *)
(* bool -> int list *)
let asTerm1 () = TmConst(FunTy,[TmConst(BoolTy,[]);TmConst(IntTy,[])]);;
(* 'a -> 'b -> 'd -> 'c *)
let asTerm2 () =
   TmConst(FunTy,[TmVar 0; TmConst(FunTy,[TmVar 1; TmConst(FunTy,[TmVar 3; TmVar 2])])]);;
(* 'a -> ('b * int) list *)
let asTerm3 () =
   TmConst(FunTy,[TmVar 0; TmConst(ListTy,[TmConst(PairTy,[TmVar 1; TmConst(IntTy,[])])])]);;
(* string * ('b list -> 'a) *)
let asTerm4 () =
   TmConst(PairTy,[TmConst(StringTy,[]);TmConst(FunTy,[TmConst(ListTy,[TmVar 1]); TmVar 0])]);;

(* Problem 2, 0 pts *)
let asTyExp1 () = FunType(BoolType, ListType IntType);;
(* bool -> int list *)
let asTyExp2 () = FunType(VarType 0, FunType(VarType 1, FunType(VarType 3, VarType 2)));;
(* 'a -> 'b -> 'd -> 'c *)
let asTyExp3 () = FunType(VarType 0, ListType(PairType(VarType 1, IntType)));;
(* 'a -> ('b * int) list *)
let asTyExp4 () = PairType(StringType, FunType(ListType(VarType 1), VarType 0));;
(* string * (('b list) -> 'a) *)
End of not needed here*)

(* Problem 3 *)
(* Implement the term of tyExp function as described in Section 7. *)
let rec term_of_tyExp t =
    (match t with VarType n -> TmVar n
     | BoolType -> TmConst(BoolTy,[])
     | IntType -> TmConst(IntTy,[])
     | StringType -> TmConst(StringTy,[])
     | RealType -> TmConst(RealTy,[])
     | UnitType -> TmConst(UnitTy,[])
     | ListType ty -> TmConst(ListTy,[term_of_tyExp ty])
     | OptionType ty -> TmConst(OptionTy,[term_of_tyExp ty])
     | PairType (ty1, ty2) -> TmConst(PairTy,[term_of_tyExp ty1;term_of_tyExp ty2])
     | FunType (ty1, ty2) -> TmConst(FunTy,[term_of_tyExp ty1;term_of_tyExp ty2]))

(* Problem 4 *)
(* Implement the tyExp_of_term function as described in Section 7. *)
let rec tyExp_of_term t =
    (match t with TmVar n -> VarType n
     | TmConst(BoolTy,[]) -> BoolType
     | TmConst(IntTy,[]) -> IntType
     | TmConst(StringTy,[]) -> StringType
     | TmConst(RealTy,[]) -> RealType
     | TmConst(UnitTy,[]) -> UnitType
     | TmConst(ListTy,[ty]) -> ListType(tyExp_of_term ty)
     | TmConst(OptionTy,[ty]) -> OptionType(tyExp_of_term ty)
     | TmConst(PairTy,[ty1; ty2]) -> PairType(tyExp_of_term ty1,tyExp_of_term ty2)
     | TmConst(FunTy,[ty1; ty2]) -> FunType (tyExp_of_term ty1,tyExp_of_term ty2)
     | _ -> failwith "Not a correct type.")

(* Problem 5 *)
(* Implement the subst fun function as described in Section 5. *)
let subst_fun s =
    fun n -> (List.fold_left (fun tm -> fun (m,t) -> if n = m then t else tm) (TmVar n) s)

(* Problem 6 *)
let rec lift_subst s = fun tm ->
    (match tm with TmVar n -> subst_fun s n
     | TmConst(c,tms) -> TmConst(c,List.map (lift_subst s) tms))

(* A test for whether a varaible occurs in a term. *)
(* Problem 7 *)
let rec occurs n tm =
    match tm with TmVar m -> (n = m)
    | TmConst (c,tms) -> List.exists (occurs n) tms

(*unification algorithm*)

(* Problem 8 *)
let rec unify eqlst =
  let rec addNewEqs lst1 lst2 acc =
    match lst1,lst2 with
      [],[] -> Some acc
    | t::tl, t'::tl' -> addNewEqs tl tl' ((t,t')::acc)
    | _ -> None  (* This it checks that the two lists of arguments have the same length. *)
  in
  match eqlst with
    (* Empty constraint set -> identity substitution. *)
    [] -> Some([])
    (* Decompose *)
  | (TmConst(str, tl), TmConst(str', tl'))::eqs ->
    if str=str'
    then (match (addNewEqs tl tl' eqs) with None -> None
          | Some l -> unify l)
    else None
    (* Orient *)
  | (TmConst(str, tl), TmVar(m))::eqs -> unify ((TmVar(m), TmConst(str, tl))::eqs)
    (* Eliminate *)
  | (TmVar(n),t)::eqs ->
     if occurs n t then
     (* Delete *)
     if t = TmVar n then unify eqs else None
     else
      let eqs' = List.map (fun (t1,t2) -> (lift_subst [(n,t)] t1 , lift_subst [(n,t)] t2)) eqs
      in (match unify eqs' with
           None -> None
         | Some(phi) -> Some((n, lift_subst phi t):: phi));;

(* Problem 9 - equivalence to to terms with variables *)
(* Not needed here.
let rec equated_by s tm1 tm2 =
    (match tm1 with TmConst(c1,tms1) ->
       (match tm2 with TmConst(c2,tms2) ->
           if c1 = c2 then list_equated_by s tms1 tms2 else None
         | TmVar _ -> None
       )
     | TmVar v1 ->
       (match tm2 with TmConst _ -> None
         | TmVar v2 ->
            (match List.fold_left (fun r -> fun (n,m) -> if n = v1 then Some m else r) None s with
                Some m -> if v2 = m then Some s else None
              | None ->
                (match List.fold_left (fun r -> fun(n,m) -> if v2 = m then Some n else r) None s with
                    None -> Some((v1,v2)::s)
                  | Some n -> None
                )
             )
       )
   )
and list_equated_by s tms1 tms2 =
    (match tms1 with [] ->
       (match tms2 with [] -> Some s | _ -> None)
      | tm1::rem_tms1 ->
         (match tms2 with [] -> None
           | tm2::rem_tms2 ->
             (match equated_by s tm1 tm2 with None -> None
               | Some s' -> list_equated_by s' rem_tms1 rem_tms2)))

let equiv_terms tm1 tm2 = match equated_by [] tm1 tm2 with Some _ -> true | None -> false
End of not needed here*)

(*-------------------------end of unify - mp6.ml------------------------------*)

let print_term t = print_tyExp (tyExp_of_term t)

let sub_to_tyExp_sub sub = List.map (fun (v,tm) -> (v,tyExp_of_term tm)) sub
let tyExp_sub_to_sub tyExp_sub = List.map (fun (v,ty) -> (v,term_of_tyExp ty)) tyExp_sub
let tyExp_subst_fun tyExp_sub v = tyExp_of_term(subst_fun (tyExp_sub_to_sub tyExp_sub) v)
let tyExp_lift_subst tyExp_sub ty =
    tyExp_of_term (lift_subst (tyExp_sub_to_sub tyExp_sub) (term_of_tyExp ty))
let tyExp_unify tyExp_constraints =
    option_map sub_to_tyExp_sub
    (unify (List.map (fun (ty1,ty2) -> (term_of_tyExp ty1,term_of_tyExp ty2))
            tyExp_constraints))

(*constraint list*)

type consList = (tyExp * tyExp) list

let print_constraints c =
  print_string "[";
  List.iter (fun (s, t) -> print_tyExp s; print_string " --> ";
             print_tyExp t; print_string "; ") c;
  print_string "]\n"

(*fresh type*)
let fresh_type ty =
    let rec get_subst sub = function
        | VarType n         -> if subst_has_var sub n then sub else (n, fresh()) :: sub
        | FunType (t1, t2)
        | PairType (t1, t2) -> get_subst (get_subst sub t1) t2
        | ListType t1
        | OptionType t1     -> get_subst sub t1
        | _                 -> sub
    in
        tyExp_lift_subst (get_subst [] ty)  ty

let rec subst_env f gamma = List.map (fun (x, y) -> (x, tyExp_lift_subst f y)) gamma

(*applying a substitution to a proof*)

let rec subst_proof f = function
  | {conclusion = ExpJudgment {gamma_exp = gamma; exp = exp; result = tyExp};
     antecedents = assum} ->
    {conclusion = ExpJudgment {gamma_exp = subst_env f gamma; exp = exp;
                               result = tyExp_lift_subst f tyExp};
                   antecedents = List.map (subst_proof f) assum}
   | {conclusion = DecJudgment {gamma_dec = gamma; dec = dec; result_env = gamma'};
     antecedents = assum} ->
    {conclusion = DecJudgment {gamma_dec = subst_env f gamma; dec = dec;
                               result_env = subst_env f gamma'};
                   antecedents = List.map (subst_proof f) assum}


let get_ty = function
  | None       -> raise(Failure "None")
  | Some(ty,p) -> ty

let get_proof = function
  | None       -> raise(Failure "None")
  | Some(ty,p) -> p

let infer_exp gather_exp gamma exp =
  let ty = fresh() in
  let result =
    match gather_exp {gamma_exp=gamma;exp=exp;result=ty} with
       None         -> None
     | Some(p,cons) ->
         match tyExp_unify cons,ty with
            Some f,VarType n -> Some (tyExp_subst_fun f n, subst_proof f p)
          | _           -> None
  in (*let _ = reset() in*)
  result
(* There is a question what gather_dec should take, since you need *)
let infer_dec gather_dec (gamma:tyExp env) (dec:dec) =
  let result =
    match gather_dec gamma dec with
       None         -> None
     | Some(p,(gamma':tyExp env),cons) ->
         match tyExp_unify cons with
            Some f -> Some (((subst_env f gamma'):tyExp env), subst_proof f p)
          | _           -> None
  in (*let _ = reset() in*)
  (result: (tyExp env * tyExp proof) option)

let print_substitution s =
  let rec aux s =
     match s with
     | [] -> ()
     | (i,t)::s' -> (print_string ((showVarType i)  ^ " --> ");
                     print_tyExp t; print_string "; "; aux s')
  in (print_string "["; aux s; print_string "]\n")

let niceInfer_exp gather_exp gamma exp =
  let ty = fresh()
  in
  let result =
    match gather_exp {gamma_exp=gamma;exp=exp;result = ty} with
     None ->
      ((print_string "Failure: No type for expression: ";
       print_exp exp; print_string "\n";
       print_string "in the environment: ";
       print_env print_tyExp gamma; print_string "\n");
       raise (Failure ""))
   | Some (p,c) ->
   (print_proof print_tyExp p;
   print_string "Constraints: ";
   print_constraints c ;
   print_string "Unifying...";
   match tyExp_unify c with
     None -> (print_string "Failure: No solution for these constraints!\n";
              raise (Failure ""))
   | Some s ->
   (print_string "Unifying substitution: ";
    print_substitution s;
    print_string "Substituting...\n";
    let new_p = subst_proof s p in
    print_proof print_tyExp new_p)) in
  let _ = reset() in
  result;;

let niceInfer_dec gather_dec (gamma:tyExp env) dec =
  let result =
    match gather_dec gamma dec with
     None ->
      ((print_string "Failure: No type for declaration: ";
       print_dec dec; print_string "\n";
       print_string "in the environment: ";
       print_env print_tyExp gamma; print_string "\n");
       raise (Failure ""))
   | Some (p,(e:tyExp env),c) ->
   (print_proof print_tyExp p;
   print_string "Constraints: ";
   print_constraints c ;
   print_string "Unifying...";
   match tyExp_unify c with
     None -> (print_string "Failure: No solution for these constraints!\n";
              raise (Failure ""))
   | Some s ->
   (print_string "Unifying substitution: ";
    print_substitution s;
    print_string "Substituting...\n";
    let new_p = subst_proof s p in
    print_proof print_tyExp new_p)) in
  let _ = reset() in
  result

(* Collect all the VarType indices in a proof *)
let rec collectTypeVars ty lst =
  match ty with
    VarType m -> m::lst
  | FunType (dom, range) -> collectTypeVars dom (collectTypeVars range lst)
  | PairType (fst,snd) -> collectTypeVars fst (collectTypeVars snd lst)
  | ListType t -> collectTypeVars t lst
  | OptionType t -> collectTypeVars t lst
  | _ -> lst

let rec collectEnvVars gamma lst =
    match gamma with
       []        -> lst
     | (x,y)::xs -> collectEnvVars xs (collectTypeVars y lst)

let collectExpJdgVars {gamma_exp = gamma;exp=exp;result = tyExp} lst =
  collectEnvVars gamma (collectTypeVars tyExp lst)
let collectDecJdgVars {gamma_dec = gamma;dec=dec;result_env = delta} lst =
  collectEnvVars gamma (collectEnvVars delta lst)
let collectJdgVars =
    function (ExpJudgment je) -> collectExpJdgVars je
  | (DecJudgment jd) -> collectDecJdgVars jd

let rec collectProofVars prf lst =
  match prf with {conclusion = jdg; antecedents = assum}
   -> collectAssumVars assum (collectJdgVars jdg lst)
and collectAssumVars assum lst =
  match assum with
    []     -> lst
  | p::ps -> collectAssumVars ps (collectProofVars p lst)

(* Rename all the variables in a proof in a canonical way *)
let rec drop y = function
   []    -> []
 | x::xs -> if x=y then drop y xs else x::drop y xs

let rec delete_duplicates = function
   []    -> []
 | x::xs -> x::delete_duplicates (drop x xs)

let canonicalize_proof (ty, prf) =
  let (varlst,_) =
    List.fold_right (fun x (xl,idx) -> ((x,VarType idx)::xl), idx+1)
      (delete_duplicates (collectProofVars prf (collectTypeVars ty [])))
      ([],1)
  in (tyExp_lift_subst varlst ty, subst_proof varlst prf)

let canon = option_map canonicalize_proof

let canon_dec =
    option_map
    (fun ((env:tyExp env), prf) ->
    let (varlst,_) =
    List.fold_right (fun x (xl,idx) -> ((x,VarType idx)::xl), idx+1)
      (delete_duplicates (collectProofVars prf (collectEnvVars env [])))
      ([],1)
  in (((subst_env varlst env):tyExp env), subst_proof varlst prf))
