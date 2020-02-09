open Printf
  
exception Failed

(* implementation of John Backus FP language from his 1977 Turing Award Lecture *)
(* http://www.thocp.net/biographies/papers/backus_turingaward_lecture.pdf       *)
(* as an example of use of the LRTT parser (Left to Right Tree Traversal)       *)

type bobject =

    (* this is the type of the language interpreter objects *)

  | Row of bobject array
  | Int of int
  | Flo of float
  | Blv of bool
  | Chr of char
  | Str of string
  | Sel of bobject
  | Apa of bobject
  | Ins of bobject
  | Cst of bobject
  | Cnd of (bobject * bobject * bobject)
  | Com of (bobject * bobject)
  | Idn of string
  | Opr of (string * (bobject -> bobject))
  | Bot

    (* instanciating the parser functor *)

module BackusParse =   (* do NOT give a type to this module in order to expose           *)
  struct               (* the actual type of the 'parsevalue' to the caller              *)
                       (* semantic callbacks: int -> int -> 'parsevalue' -> 'parsevalue' *)
    type t = bobject   (* the 'parsevalue' is just a single object                       *)
  end;;
    
module ParseSample = LRTTfunctor.Parser(BackusParse);;

open ParseSample

  (* parser options *)

let debugrun = ref false
let debugall = ref false
let stamping = ref false
let memflush = ref true
let memosize = ref 8
let parseloc = ref 0
let parseskew = ref 0

   (* incremental parser input *)

let lines = ref [0]
let chanstack = ref [stdin]
let filestack = ref ["-"]
let startstack = ref [[]]

let input = ref ""

let len = ref 0

let debugeval = ref false 

let gmessages = ref false 

let evalprint = ref false 

let startrule = ref ""

let isinteractive () = !chanstack <> [] && List.tl !chanstack = [] && Unix.isatty Unix.stdin && Unix.isatty Unix.stdout

let userprompt () =
  if isinteractive () then begin
    printf "fp>";
    flush stdout;
  end;;

let linepos beg =
  let line = ref !lines in
  let pos = beg + !parseskew in
  while !line <> [] && List.hd !line >= pos do line := List.tl !line; done;
  "line " ^ (string_of_int ((List.length !line) - (List.length (List.hd !startstack)) + 1)) ^ " col " ^ 
  (string_of_int (if !line <> [] then pos - List.hd !line else pos)) ^
  (if List.hd !filestack = "-" then "" else " file \"" ^  List.hd !filestack ^ "\"")

let charfeed ask lng =
  let pos = ask + !parseskew in
  if ask < 0 || lng < 0 then
    ""
  else if pos + lng > !len && pos < !len && isinteractive () then
    "\n"   (* this hack is needed to avoid hanging on tty input *)
  else begin
    while pos + lng > !len do
      try
	userprompt ();
	let line = input_line (List.hd !chanstack) in
	input := !input ^ "\n" ^ line;
	if !debugall && String.length line > 0 && (String.length line < 2 || not (String.sub line 0 2 = "--")) then
	  printf "--LINE %s '%s'\n" (linepos (1 + (List.hd !lines))) line;
	len := String.length !input;
      with
	End_of_file ->
	  if (List.tl !chanstack) = [] then raise Not_found;
	  close_in (List.hd !chanstack);
	  chanstack := List.tl !chanstack;
	  filestack := List.tl !filestack;
	  lines := List.hd !startstack;
	  startstack := List.tl !startstack;
    done;
   
    for i = (if !lines = [] then 0 else (List.hd !lines) + 1) to pos+lng-1 do
      if !input.[i] = '\n' then lines := i :: !lines;
    done;

    if pos > !parseloc then parseloc := pos;   (* for the 'read' stream interleave *)

    (String.sub !input pos lng)
  end;;

    (* "on-the-fly" lexing functions *)

let testeof pos _ =
  (try
    let _ = charfeed pos 0 in (); 
    (try
      let _ = charfeed pos 1 in ();
      0                     (* before eof *)
    with Not_found -> -1)   (* exactly at eof *)
  with Not_found -> 0)      (* BEYOND 'eof' isn't eof *)

let tkillone pos _ = pos + 1

let tsymbol pos name =
  let k = String.length name in
  if (try charfeed pos k with Not_found -> "") = name then k else 0
  
let nquotchar pos =
  if charfeed pos 1 = "\\" then
      (* peek one extra char beyond to account for the closing quote  *)
      let _ = charfeed (pos+2) 1 in 
      2
  else
    1

let tquotchar pos _ =
  (try 
    let k = nquotchar (pos+1) in
    if charfeed pos 1 = "'" && charfeed (pos+k+1) 1 = "'" then
      k + 2 
    else
      0
  with Not_found -> 0)
 
let tstring pos _ =
  (try 
    if charfeed pos 1 = "\"" then
      let ptr = ref (pos + 1) in
      while charfeed !ptr 1 <> "\"" do
	ptr := !ptr + (nquotchar !ptr);
      done;
      ((!ptr - pos) + 1)
    else
      0
  with Not_found -> 0)

let tident pos _ =
  let ptr = ref pos  in
  (try 
    while (let ch = charfeed !ptr 1 in ch.[0] >= 'a' && ch.[0] <= 'z') do
      ptr := !ptr +1;
    done;
  with Not_found -> ());
  (!ptr - pos)

let lineskip ptr =
    while (charfeed !ptr 1 <> "\n") do  ptr := !ptr +1; done

let tspace pos _ =
  let ptr = ref pos  in
  (try 
    while (let ch = charfeed !ptr 1 in ch = " " || ch = "\n" || ch = "\t") do
      ptr := !ptr +1;
    done;
    if charfeed !ptr 2 = "--" then begin
      ptr := !ptr +2;
      lineskip ptr;
      ptr := !ptr +1;
  end;
  with Not_found -> ());
  (!ptr - pos)

let ninteger line =
  (try
    let k = ref 0 in
    Scanf.sscanf line "%i%n" (fun _ n -> k := n);
    if !debugall then printf "Integer %i '%s'\n" !k  (String.sub line 0 !k);
    !k
  with Scanf.Scan_failure _ -> 0)
    
let tinteger pos _ =
  let ptr = ref pos in
  (try lineskip ptr; with Not_found -> ());  
  ninteger (charfeed pos (!ptr - pos))

let tnumber pos _ =
  let ptr = ref pos in
  (try lineskip ptr; with Not_found -> ());  
  let line = charfeed pos (!ptr - pos) in
  (try
    Scanf.sscanf line "%g%n" (fun _ n -> ptr := pos + n);
    (* workaround for cretinous bug in Ocaml 3.10.2 which has been fixed in 3.12.1 *)
    let ch =  (charfeed (!ptr - 1) 1).[0] in
    if ch < '0' || ch > '9' then ptr := !ptr - 1;
    if !debugall then printf "Number %i %i '%s'\n" pos (!ptr - pos) (charfeed pos (!ptr - pos));
    (!ptr - pos)
  with Scanf.Scan_failure _ ->
    ninteger line)


      (* output functions & miscellanea *)

let names = Hashtbl.create 101

let objnest = ref 0
let objfirst = ref true
let objinarray = ref 0
let accu = ref Bot

let rec printobj obj = 
  objnest := !objnest + 1;
  (match obj with

  | Row arr ->
      objinarray := !objinarray + 1;
      printf "[";
      let flip = ref false in
      Array.iter (fun a ->
	  if !flip then 
	    printf ","
	  else
	    flip := true;
	  printobj a;) arr;
      printf "]";
      if false && !objinarray = 2 && !objnest = 2 then printf "\n"; (* crude matrix display *)
      objinarray := !objinarray - 1;

  | Blv bv -> printf "%s" (if bv then "T" else "F");
  | Int num -> printf "%i" num;
  | Flo num -> printf "%e" num;
  | Chr chr -> printf "'%c'" chr;
  | Str str -> printf "\"%s\"" str;
  | Idn str -> printf "%s" str;
  | Opr (str,_) -> printf "%s" str;
  | Sel sel -> printf "@";
      (match sel with 
      |	Int num -> printf "%i" num;
      |	_ ->
	  printf "(";
	  printobj sel;
	  printf ")";)
  | Apa app ->
	  printf "(ap ";
	  printobj app;
	  printf ")";
  | Ins ins ->
	  printf "(ins ";
	  printobj ins;
	  printf ")";
  | Cst cst ->
 	  printf "(const ";
	  printobj cst;
	  printf ")";
  | Cnd (cond, thn, els) ->
      let paren = !objfirst in
      if !objfirst then printf "(";
      printobj cond;
      printf " -> ";
      printobj thn;
      printf "; ";
      objfirst := false;
      printobj els;
      if paren then printf ")";
      objfirst := paren;
  | Com (lef, rig) ->
      printobj lef;
      printf "°";
      printobj rig;
  | Bot -> printf "_|_"
      );
  objnest := !objnest - 1
;;
     (* interpreter functions *)

let rec bottomfails pval =
  (match pval with
  | Bot-> raise Failed
  | Row arr ->  Array.iter (fun a -> bottomfails a) arr
  | Sel  obj | Apa  obj | Ins  obj | Cst  obj -> bottomfails obj
  | Cnd (a,b,c) -> 
      bottomfails a;
      bottomfails b;
      bottomfails c;
  | Com (a,b) ->
      bottomfails a;
      bottomfails b;
  | _ -> ())

let allbottom pval = Bot

let getargpair pval =
  (match pval with
  | Row arr ->
      if Array.length arr <> 2 then raise Failed;
      arr
  | _ -> raise Failed)

let getnumargs pval = 
  (let arr = getargpair pval in
  (match arr.(0) with 
	| Int num -> 
	    (match arr.(1) with | Flo _ -> Flo (float_of_int num) | _ -> arr.(0))
	| Flo _ -> arr.(0) | _ -> raise Failed),

	(match arr.(1) with 
	| Int num -> (match arr.(0) with | Flo _ -> Flo (float_of_int num) | _ -> arr.(1))
	| Flo _ -> arr.(1) | _ -> raise Failed))
    
let doltnums pval =
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Blv (numa < numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Blv (numa < numb) | _-> raise Failed) 
  | _-> raise Failed) 

let dogenums pval =
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Blv (numa >= numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Blv (numa >= numb) | _-> raise Failed) 
  | _-> raise Failed) 

let dogtnums pval =
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Blv (numa > numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Blv (numa > numb) | _-> raise Failed) 
  | _-> raise Failed) 

let dolenums pval =
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Blv (numa <= numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Blv (numa <= numb) | _-> raise Failed) 
  | _-> raise Failed) 

let doaddition pval = 
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Int (numa + numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Flo (numa +. numb) | _-> raise Failed) 
  | _-> raise Failed) 
  
let dosubtract pval = 
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Int (numa - numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Flo (numa -. numb) | _-> raise Failed) 
  | _ -> raise Failed) 
  
let domultiply pval = 
  (let (a,b) = getnumargs pval in
  match a  with 
  | Int numa -> (match b  with | Int numb -> Int (numa * numb) | _-> raise Failed) 
  | Flo numa -> (match b  with | Flo numb -> Flo (numa *. numb) | _-> raise Failed) 
  | _ -> raise Failed) 
  
let dodivide pval = 
  (let (a,b) = getnumargs pval in
  try
    match a  with 
    | Int numa -> (match b  with | Int numb -> Int (numa / numb) | _ -> raise Failed) 
    | Flo numa -> (match b  with | Flo numb -> Flo (numa /. numb) | _ -> raise Failed) 
    | _ -> raise Failed;
  with Division_by_zero -> raise Failed)
  
let doimplicit pval = 
  bottomfails !accu;
  !accu
  
let domodulus pval = 
  (let (a,b) = getnumargs pval in
  try
    match a with 
    | Int numa -> (match b  with | Int numb -> Int (numa mod numb) | _ -> raise Failed) 
    | Flo numa -> (match b  with | Flo numb -> Flo (mod_float numa numb) | _ -> raise Failed) 
    | _ -> raise Failed;
  with Division_by_zero -> raise Failed) 
  
let doarraytl pval =
  (match pval with
  | Row arr -> let k = Array.length arr in
    if k < 1 then raise Failed;
    let war = Array.make (k-1) Bot in
    Array.blit arr 1 war 0 (k-1);
    (Row war)
  | Str str -> let k = String.length str in
    if k < 1 then raise Failed;
    (Str (String.sub str 1 (k-1)))
  | _ -> raise Failed)

let doarraylength pval =
  (match pval with
  | Row arr -> (Int (Array.length arr))
  | Str str -> (Int (String.length str))
  | _ -> raise Failed)

let doreversearray pval =
  (match pval with
  | Row arr -> let num = Array.length arr in
    if num = 0 then 
      pval
    else
      let war = Array.make num Bot in
       for k = num - 1 downto 0 do war.(k) <- arr.((num - k) -1); done;
      (Row war)
  | Str str -> let num = String.length str in
    if num = 0 then 
      pval
    else
      let war = String.create num in
      for k = num - 1 downto 0 do war.[k] <- str.[(num - k) -1]; done;
      (Str war)
  | _ -> raise Failed)

let doiotagener pval =
  (match pval with
  | Int num ->
      if num < 0 || num > Sys.max_array_length then raise Failed;
      let war = Array.make num Bot in
      for k = num - 1 downto 0 do war.(k) <- (Int k); done;
      Row war
  | _ -> raise Failed)
     
let donulltest pval =
    (let res = doarraylength pval in
    match res with Int n  -> (Blv (n = 0)) | _ -> raise Failed)

let dotranspose pval =
  (match pval with
  | Row arr ->
      let k = ref (-1) in
      Array.iter (fun a -> match a  with
      | Row elm ->
	  if !k < 0 then
	    k := Array.length elm
	  else if !k <> Array.length elm then
	    raise Failed
      |	_ -> raise Failed) arr;
      let war = Array.make !k Bot in
      Array.iteri (fun i _ ->
	war.(i) <- Row (Array.map (fun x -> match x with Row ext -> ext.(i)| _ -> raise Failed) arr)) war;
      Row war
  | _ -> raise Failed)

let doidentity pval =
  bottomfails pval;
  pval

let doreadexpr = ref doidentity

let doprintexpr pval =
  if !debugall then printf "\nOBJ ";
  (match pval with
  | Chr '\n' -> printf "\n";   (* a hack... *)
  | _ -> printobj pval);
  flush stdout;
  pval

let doequalobjs pval =
  (let arr = getargpair pval in
  bottomfails arr.(0);
  bottomfails arr.(1);
  Blv (arr.(0) = arr.(1)))

let nullelement fn =
  (match fn with 
  | Opr  (name,_) ->
      if name = "+" then 
	Int 0
      else if name = "-" then 
	Int 0
      else if name = "x" then 
	Int 1
      else if name = "/" then 
	Int 1
      else if name = "%" then 
	Int 1
      else
	raise Failed
  | _ ->
      raise Failed)

    (* interpreter loop *)

let rec evalpair func arg = 

  if !debugeval then begin
    printf "EVAL ";
    printobj func;
    printf "  ";
    printobj arg;
    printf "\n";
    flush stdout;
  end;

  let argv = (match arg with Bot -> raise Failed
  | Idn name -> (try Hashtbl.find names name with Not_found -> arg) | _ -> arg) in

  match func with
  | Idn name -> (try 
      evalpair (Hashtbl.find names name) argv 
  with Not_found -> func)
  | Bot -> raise Failed
  | Row arr ->  Row (Array.map (fun f -> evalpair f argv) arr)
  | Opr (_,fn) -> fn argv

  | Com (f,g) ->
      evalpair f (evalpair g argv)

  | Sel num ->
      (let i = (match num with 
      |	Int x -> x 
      | _ -> (match (evalpair num argv) with | Int y -> y | _ -> raise Failed)) in

      if i < 0 then raise Failed;

      match argv with
      |	Row arr -> 
	  if i >= Array.length arr then raise Failed;
	  arr.(i)
      |	Str str ->
 	  if i >= String.length str then raise Failed;
	  Chr str.[i]
      |	_ -> raise Failed)

  | Cnd (cond, thn, els) ->
      (let bv = (match evalpair cond argv with Blv boo -> boo | _ -> raise Failed) in
      if bv then
	evalpair thn argv
      else
	evalpair els argv)

  | Apa fn ->
      (let res = ref Bot in
      let i = ref 0 in
      let war = ref [| |] in
      (match argv with
      |	Row arr -> 
	  i := Array.length arr;
	  if !i = 0 then
	    res := argv
	  else begin
	    war :=  Array.map (fun a -> evalpair fn a) arr;
	    res := Row !war;
	  end;

     |	Str str ->
	  i := String.length str;
	  if !i = 0 then
	    res := argv
	  else begin
	    war := Array.make !i Bot;    
	    res := Row !war; 
	    i := 0;
	    String.iter (fun c -> !war.(!i) <- evalpair fn (Chr c); i := !i +1) str;
	  end;

      |	_ -> raise Failed);

      if !i <> 0 then
	(let allc = ref true in
	Array.iter (fun a -> match a with Chr _ -> () | Bot -> raise Failed | _ -> allc := false) !war;
	if !allc then 
	  let str = String.create !i in
	  Array.iteri (fun j a -> match a with Chr c -> str.[j] <- c | _ -> raise Failed) !war;
	  res := Str str);
      !res)

  | Ins fn ->
      (let res = ref Bot in
      let i = ref 0 in
      (match argv with
      |	Row arr -> 
	  i := Array.length arr;
	  if !i = 0 then
	    res := nullelement fn
	  else if !i = 1 then
	    res := evalpair fn (Row [| arr.(0); nullelement fn |])
	  else if !i = 2 then
	    res := evalpair fn argv
	  else
	    res := Array.fold_right (fun e b -> 
	      (* cheat the foldright to also work when no 'nullelement' *)
	      if e == b then e 
	      else evalpair fn (Row [| e; b |])) arr arr.(!i-1);

       | Str str -> 
	  i := String.length str;
	  if !i = 0 then
	    res := nullelement fn
	  else if !i = 1 then
	    res := evalpair fn (Row [| Chr str.[0]; nullelement fn |])
	  else if !i = 2 then
	    res := evalpair fn (Row [| Chr str.[0]; Chr str.[1] |])
	  else begin
	    let arr = Array.make !i Bot in
	    i := 0;
	    String.iter (fun c -> arr.(!i) <- Chr c; i := !i + 1) str;
	    res := Array.fold_right (fun e b -> 
	      (* cheat the foldright to also work when no 'nullelement' *)
	      if e == b then e 
	      else evalpair fn (Row [| e; b |])) arr arr.(!i);
	  end;

        | _ -> raise Failed);
	!res)

  | Cst exp ->
      exp

  |Str _|Chr _|Blv _|Flo _|Int _ ->
      func

     (* semantic callbacks *)

let exprstack = ref [Bot] 

let popvalue () =
  if !exprstack = [] then
    Bot
  else
    let pop = List.hd !exprstack in
    exprstack := List.tl !exprstack;
    pop

let unimplemented beg pos pval = 
  exprstack := pval :: !exprstack;
  let loc = ref beg in
  (try
    while (charfeed !loc 1) >= "a" && (charfeed !loc 1) <= "z" do
      loc := !loc + 1;
    done;
  with Not_found -> ());
  eprintf "Sorry %i '%s' is not implemented %s\n" beg (charfeed beg (!loc - beg)) (linepos beg);
  printf "Sorry %i %s' is not implemented %s\n" beg (charfeed beg (!loc - beg)) (linepos beg);
  Bot

let gotbottom beg pos pval = 
  exprstack := pval :: !exprstack;
  Bot

let gotbool beg pos pval = 
  exprstack := pval :: !exprstack;
  Blv ((charfeed beg 1) = "T")

let emptyarr beg pos pval =
  exprstack := pval :: !exprstack;
  Row (Array.make 0 Bot)

let arrayone beg pos pval =
  Row (Array.make 1 pval)

let arrayadd beg pos pval =
   let arv = popvalue () in
  (match arv with
  | Row arr -> Row (Array.append arr (Array.make 1 pval))
  | _ ->
      eprintf "ERROR extending array %s\n" (linepos beg);
      printf "ERROR extending array, not an array %s " (linepos beg);
      printobj arv;
      printf "\n";
      flush stderr;
      flush stdout;
      Bot)

let onechar beg pos pval =
  exprstack := pval :: !exprstack;
  let ch = ref (charfeed (beg + 1) 1) in
  if !ch = "\\" then
    (match (charfeed (beg + 2) 1).[0] with
    | 'n' -> ch := "\n";
    | 't' -> ch := "\t";
    | '\'' -> ch := "'";
    | _ -> ch := (charfeed (beg + 2) 1));
  Chr !ch.[0]

let gotident beg pos pval =
  exprstack := pval :: !exprstack;
  Idn (charfeed beg (pos - beg))

let onestring beg pos pval =
  exprstack := pval :: !exprstack;
  Str (charfeed (beg + 1) (pos - (beg + 2)))

let selector beg pos pval =  Sel pval 

let integer beg pos pval =
  exprstack := pval :: !exprstack;
  let res = ref Bot in
  (try
    Scanf.sscanf (charfeed (beg) (pos - beg)) "%i" (fun k -> res := Int k);
  with Scanf.Scan_failure _ -> ());
  !res

let snumber beg pos pval =
  exprstack := pval :: !exprstack;
  let res = ref Bot in
  (try
    Scanf.sscanf (charfeed (beg) (pos - beg)) "%g" (fun k -> res := Flo k);
  with Scanf.Scan_failure _ -> ());
  !res

let tofloat beg pos pval =
  (match pval with
  | Int num ->
      Flo (float_of_string ((string_of_int num) ^ (charfeed beg (pos - beg))))
  | _ ->
      eprintf "ERROR in floating point creation %s\n" (linepos beg);
      printf "ERROR in floating point creation, no previous int %s " (linepos beg);
      printobj pval;
      printf "\n";
      flush stderr;
      flush stdout;
     Bot)

let setdefine beg pos pval =
  let nm = popvalue () in
  (match nm with
  | Idn name ->
      Hashtbl.add names name pval;
      if !evalprint then begin
	printf "DEF %s = " name;
	printobj pval;
	printf "\n";
	flush stdout;
      end;
      popvalue ()
  | _ ->
      eprintf "ERROR in define, not a valid name %s\n" (linepos beg);
      flush stderr;
      if !debugall then begin
	printf "ERROR in define, not a valid name %s : " (linepos beg);
	printobj nm;
	printf " = ";
	printobj pval;
	printf "\n";
	flush stdout;
      end;
      popvalue ())

let composf beg pos pval =  Com (popvalue (), pval)

let condition beg pos pval = 
  let mid = popvalue () in
  Cnd (popvalue (), mid, pval)

let makeapp beg pos pval =
  exprstack := pval :: !exprstack;
  (Apa Bot)

let makeins beg pos pval =
  exprstack := pval :: !exprstack;
  (Ins Bot)

let makecst beg pos pval =
  exprstack := pval :: !exprstack;
  (Cst Bot)

let funcomp beg pos pval = 
  let opr = popvalue () in
  (match opr with
  | Apa _ -> (Apa pval)
  | Ins _ -> (Ins pval)
  | Cst _ -> (Cst pval)
  | _ ->
      eprintf "ERROR not a valid functional %s\n" (linepos beg);
      printf "ERROR not a valid functional %s : " (linepos beg);
      printobj opr;
      printf "\n";
      popvalue ())

let addition beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("+",doaddition))

let subtract beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("-",dosubtract))

let multiply beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("x",domultiply))

let divide beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("/",dodivide))

let modulus beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",domodulus))

let implicit beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("*",doimplicit))

let ltnums beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",doltnums))

let gtnums beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",dogtnums))

let lenums beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",dolenums))

let genums beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",dogenums))

let arraytl beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",doarraytl))

let nulltest beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",donulltest))

let arraylength beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("%",doarraylength))

let transpose beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("trans",dotranspose))

let doarraylength beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("length",doarraylength))

let doarraytl beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("tl",doarraytl))

let iotagener beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("iota",doiotagener))

let reversearray beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("reverse",doreversearray))

let equalobjs beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("eq",doequalobjs))

let identity beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("id",doidentity))

let transpose beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("trans",dotranspose))

let defaultexpr beg pos pval =
  exprstack := pval :: !exprstack;
  (Int 1)

let defaultfunc beg pos pval = addition  beg pos pval

let readexpr beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("read",!doreadexpr))

let printexpr beg pos pval =
  exprstack := pval :: !exprstack;
  (Opr ("print",doprintexpr))

let quitprog beg pos pval =
  exit 0

let warnbracket beg pos pval =
  printf "Spurious '%s' bracket ignored %s\n" (charfeed beg (pos - beg)) (linepos beg);
  flush stdout;
  pval

let warnkill beg pos pval =
  printf "Unrecognized text \"%s\" deleted %s\n" (charfeed beg (pos - beg)) (linepos beg);
  flush stdout;
  pval

let gramessage beg pos pval =
  if !gmessages then begin
    printf "stacked %i exprs, %s, val = " (List.length !exprstack) (linepos beg);
    printobj pval;
    printf "\n";
    flush stdout;
  end;;

let tryingdefault  beg pos msg pval =
  if !gmessages then begin
    printf "%s\n" msg;
    gramessage beg pos pval;
  end

let endofkill  beg pos msg pval =
  if !gmessages then begin
    printf "'%s' bracket terminating kill\n" 
      (charfeed beg (if pos - beg <= 0 then 1 else pos - beg));
    gramessage beg pos pval;
  end

let endspurious  beg pos pval =
  if !gmessages then begin
    printf "end of purge \"%s\"\n" 
      (charfeed beg (if pos - beg <= 0 then 1 else pos - beg));
    gramessage beg pos pval;
  end;
  pval

let fileinclude beg pos pval =
  (match pval with Str name ->
    (try
      let file = open_in name in
      chanstack := file :: !chanstack;
      filestack := name :: !filestack;
      startstack := !lines :: !startstack;
    with Sys_error msg ->
      eprintf "%s %s\n" msg (linepos beg);
      flush stderr;
      if !debugall then begin
	printf "%s %s\n" msg (linepos beg);
	flush stdout;
      end);
    popvalue ();
 | _ ->
     eprintf "ERROR not a valid name %s\n" (linepos beg);
     flush stderr;
     if !debugall then begin
       printf "ERROR not a valid name %s : " (linepos beg);
       printobj pval;
       printf "\n";
      flush stdout;
     end;
     popvalue ())

let application  beg pos pval = 
  (try
    accu := evalpair (popvalue ()) pval;
    if !evalprint then begin
      printobj !accu;
      printf "\n";
      flush stdout;
    end;
    !accu
  with Failed -> 
    if !evalprint then begin
      printf "_|_\n";
      flush stdout;
    end;
    Bot)
 
let deleteident  beg pos pval = 
  (match pval with 
  | Idn name -> 
      Hashtbl.remove names name;
      (try 
	let more = Hashtbl.find names name in
	if !evalprint then begin
	  printf "'%s' restored = " name;
	  printobj more;
	  printf "\'n";
	  flush stdout;
	end;
      with Not_found ->
	if !evalprint then begin
	  printf "'%s' cleared\'n" name;
	  flush stdout;
	end;
	)
 | _ -> 
     printf "Error, bad name %s '" (linepos beg);
     printobj pval;
     printf "\'n";
     flush stdout;
    );
  flush stdout;
  popvalue ()

let saveaccu  beg pos pval = 
  (match pval with 
  | Idn name -> 
      Hashtbl.add names name !accu;
      if !evalprint then begin
	printf "Saved '%s' = " name;
	printobj !accu;
	printf "\n";
	flush stdout;
      end;
  | _ -> 
      printf "Error, bad name %s '" (linepos beg);
      printobj pval;
      printf "\'n";
      flush stdout;
     );
  flush stdout;
  popvalue ()

let showaccu  beg pos pval = 
  printobj !accu;
  printf "\n";
  flush stdout;
  pval

let showident  beg pos pval = 
  (match pval with 
  | Idn name -> let vlis = (try 
      Hashtbl.find_all names name 
  with Not_found -> [pval]) in
    List.iter (fun a ->
      if List.tl vlis <> [] then
	printf "%s = " name;
      printobj a;
      printf "\n") vlis;
  | _ -> 
      printobj pval;
      printf "\n");
  flush stdout;
  popvalue ()

let showstore  beg pos pval = 
  Hashtbl.iter (fun name obj -> 
    printf "%s = " name;
    printobj obj;
    printf "\n";) names;
  flush stdout;
  pval

let postdone  beg pos pval = 
  printf "\nDONE\n";
  flush stdout;
  pval

let posta  beg pos pval = 
  printf " -A)";
  pval

let postb  beg pos pval = 
  printf " -B)";
  pval

let postc  beg pos pval = 
  printf " -C)";
  pval

let preva  beg pos pval = 
  printf "(A ";
  pval

let prevb  beg pos pval = 
  printf "(B ";
  pval

let prevc  beg pos pval = 
  printf "(C ";
  pval
 
let identc  beg pos pval = 
  printf " %s" (try (charfeed (pos -1) 1) with Not_found -> "<eof>") ;
  pval
 
let grammar : ParseSample.grammar = [

  "loop", [
    "", "", [ NT "osp"; NT "a"; NT "osp"; S postdone; (A (testeof, "EOF"))]
   ];

  "a", [
   "", "", [S preva; NT "a"; A (tsymbol, "a"); S identc; S posta; ];
   "", "", [S preva; NT "b"; S posta;];
   ];

  "b", [
   "", "", [ S prevb; NT "b";  A (tsymbol,"b"); S identc;S postb; ];
   "", "", [ S prevb; NT "a" ; S postb];
   "", "", [ S prevb; NT "c" ; S postb];
   ];

  "c", [
   "", "", [ S prevc; NT "c";  A (tsymbol, "c"); S identc; S postc; ];
   "", "", [ S prevc; NT "b"; S postc; ];
   "", "", [ S prevc;  A (tsymbol, "d"); S identc; S postc; ];
   ];


  "start", [
    "", "", [ NT "osp"; Z(NT "command"); NT "osp"; (A (testeof, "EOF"))]
   ];

   "read", [
    "", "", [ NT "readwrap" ];
   ];

   "readwrap", [
    (* the closing ";" of previous parse may still be in the stream *)
    "", "", [Opt (A (tsymbol, ";")) ; NT "osp"; NT "expr"; NT "purge" ];
   ];

  "command", [ 
     "quit", "", [ NT "osp"; A (tsymbol, "quit"); NT "purge"; S quitprog ];
     "file", "", [ NT "osp"; A (tsymbol, "include") ; NT "osp"; NT "string"; S fileinclude; NT "purge" ];
     "show", "", [ NT "osp"; A (tsymbol, "show") ; NT "osp"; NT "showval";];
     "save", "", [ NT "osp"; A (tsymbol, "save") ; NT "osp";  NT "ident"; S saveaccu; NT "purge" ;];
     "delete", "", [ NT "osp"; A (tsymbol, "del") ; NT "osp";  NT "ident"; S deleteident; NT "purge" ;];
     "definition", "", [ NT "osp"; NT "define";];
     "application", "", [ NT "osp"; NT "expr"; NT "osp"; NT "expr"; S application; NT "purge" ];
  ];

  "purge", [
    (* error recovery by deletion of spurious closing brackets before ";" *)
    "", "", [ NT "osp"; A (tsymbol, ";") ];                 (* correct *)
    "", "", [ NT "spurious"; NT "osp"; A (tsymbol, ";") ];  (* delete closing brackets *)
  ];

  "spurious", [ 
    "", "", [NT "osp"; A (tsymbol, "->") ; NT "osp"; NT "killtext"; S warnkill ; NT "spurious";]; (* serious garbage *)
    "", "", [NT "osp"; NT "fiducials"; S warnbracket ; NT "spurious";];
    "", "", [NT "osp"; NT "killtext"; S warnkill ; NT "spurious";]; 
   ];

   "killtext", [ 
    "", "", [L (NT "fiducials"); M (endofkill,"") ;];   (* stop deletion *)
    "", "", [A (tkillone, ".");  NT "killtext";];  (* skip only one character & retry *)
  ];

  "showval", [
  "", "", [ A (tsymbol, "*") ; NT "purge"; S showstore ];
  "", "", [ NT "ident"; NT "purge"; S showident];
  "", "", [ NT "purge";  S showaccu];
  ];

  "define", [
  "", "", [ NT "ident"; NT "osp";  A (tsymbol, "=") ; NT "osp"; NT "expr"; S setdefine; NT "purge" ]
  ];

  "exprsure", [
    "recovery", "", [ S defaultexpr; NT "osp"; L (L (NT "fiducials")); M (tryingdefault,"Trying to supply default expr") ];
    "normal", "", [ NT "expr" ];
  ];

  "expr", [
    "functional", "", [ A (tsymbol, "(") ; NT "osp"; NT "functional"; A (tsymbol, ")") ];
    "nullarray", "", [ A (tsymbol, "[") ; NT "osp"; A (tsymbol, "]") ; S emptyarr ]; 
    "array", "", [ A (tsymbol, "[") ; NT "osp"; NT "exprsure"; S arrayone; Z (NT "listelem"); NT "osp"; A (tsymbol, "]") ;]; 
    "char", "", [A (tquotchar, "'.'"); S onechar; ]; 
    "string", "", [NT "string"]; 
    "selector", "", [A (tsymbol, "@") ;  NT "osp"; NT "indice"; S selector ];
    "number", "", [NT "number"];
    "ops", "", [NT "operators"];
    "single", "", [NT "ident"];
    "composition", "", [NT "composition"; NT "osp"; ];
  ];

  "fiducials", [
     (* solid symbols for lookahead & recovery *)
    "", "", [ A (tsymbol, ";") ];
    "", "", [ A (tsymbol, ")") ];
    "", "", [ A (tsymbol, "]") ];
    "", "", [ A (tsymbol, "->") ];
    "", "", [ L (L (A (testeof, "EOF"))) ];  (* do not skip over EOF *)
  ];

  "string", [
    "", "", [A (tstring, "\" ... \""); S onestring]
  ];

  "indice", [
    "numconst", "", [NT "integer";];
    "numval", "", [A (tsymbol, "(") ; NT "osp"; NT "exprsure";  NT "osp"; A (tsymbol, ")") ; ];
  ];

  "integer", [ "", "", [A (tinteger, "int") ]
  ];
 
  "functional", [
    "","", [NT "funcomps";  NT "osp"; NT "function"; S funcomp ];
    "","", [NT "conditional"; NT "osp";];
    "","", [NT "exprsure"; NT "osp";];
  ];
  
  "function", [
    (* error recovery by deletion of erroneous 'expr' & replacement *)
    "","", [NT "expr"; D defaultfunc ; NT "osp"; L (L (A (tsymbol, ")"))) ];
  ];
  
  "composition", [
    "leftrecurs", "" , [NT "composition"; NT "osp"; A (tsymbol, "°") ; NT "osp"; NT "expr"; S composf];
    "initial", "", [NT "expr"];
  ];

  "conditional", [
     "condition", "", [NT "exprsure"; NT "osp"; A (tsymbol, "->") ; NT "osp"; NT "exprsure"; A (tsymbol, ";") ; NT "osp"; NT "elseclause"; S condition ];
  ];

  "elseclause", [
    "more", "", [NT "conditional"];
    "last", "", [NT "exprsure"; NT "osp"; ];
  ];

  "listelem",  [
    "", "", [NT "osp"; A (tsymbol, ","); NT "osp"; NT "exprsure"; S arrayadd];
  ];

  "number",  [
      "", "", [A (tnumber,"num"); S snumber;];
    ];

  "funcomps", [
     "applytoall", "", [A (tsymbol, "ap") ; S makeapp];
     "insert", "", [A (tsymbol, "ins") ; S makeins];
     "constant", "", [A (tsymbol, "const") ; S makecst];
    ];

  "operators", [
     "add", "", [A (tsymbol, "+") ; S addition];
     "sub", "", [A (tsymbol, "-") ; S subtract];
     "mul", "", [A (tsymbol, "x") ; S multiply];
     "div", "", [A (tsymbol, "/") ; S divide];
     "mod", "", [A (tsymbol, "%") ; S modulus];
     "implicit", "", [A (tsymbol, "*") ; S implicit];
     "transpose", "", [A (tsymbol, "trans") ; S transpose];
     "equal", "", [A (tsymbol, "eq") ; S equalobjs];
     "equal", "", [A (tsymbol, "lt") ; S ltnums];
     "equal", "", [A (tsymbol, "gt") ; S gtnums];
     "equal", "", [A (tsymbol, "le") ; S lenums];
     "equal", "", [A (tsymbol, "ge") ; S genums];
     "tail", "", [A (tsymbol, "tl") ; S arraytl];
     "ident", "", [A (tsymbol, "id") ; S identity];
     "true", "", [A (tsymbol, "A (tsymbol, ") ; S gotbool];         (* actually a constant*)
     "false", "", [A (tsymbol, "F") ; S gotbool];        (* actually a constant*)
     "bottom", "", [A (tsymbol, "_|_") ; S gotbottom];   (* actually a constant*)
     "nulltest", "", [A (tsymbol, "null") ; S nulltest];
     "read", "", [A (tsymbol, "read") ; S readexpr];
     "print", "", [A (tsymbol, "print") ; S printexpr];
     "reverse", "", [A (tsymbol, "reverse") ; S reversearray];
     "appendleft", "", [A (tsymbol, "appndl") ; S unimplemented];
     "appendright", "", [A (tsymbol, "appndr") ; S unimplemented];
     "logicand", "", [A (tsymbol, "and") ; S unimplemented];
     "logicor", "", [A (tsymbol, "or") ; S unimplemented];
     "logicnot", "", [A (tsymbol, "not") ; S unimplemented];
     "rotateleft", "", [A (tsymbol, "rotl") ; S unimplemented];
     "rotateright", "", [A (tsymbol, "rotr") ; S unimplemented];
     "iota", "", [A (tsymbol, "iota") ; S iotagener];
     "length", "", [A (tsymbol, "length") ; S arraylength];
     "distributeleft", "", [A (tsymbol, "distl") ; S unimplemented];
     "distributeright", "", [A (tsymbol, "distr") ; S unimplemented];
   ];

  "ident", [
    "", "", [A (tident, "-id-"); S gotident;];
  ];

  "sp", [
    "", "", [P (NT "space")];
  ];

  "osp", [
    "", "", [Z (NT "space")];
  ];

  "space", [
    "", "", [A (tspace,"_")];
  ];
]
  
let actualread pval =
  bottomfails pval;

  (* sharing the input stream requires some acrobatics *)
  let oldskew = !parseskew in
  parseskew := 0;
  let oldloc = !parseloc in

  if !debugall then
    printf "\nREAD at loc %i old skew %i [%s]\n" !parseloc oldskew (charfeed !parseloc (!len - !parseloc));

  let (parsed,endloc) = ParseSample.streamparse !parseloc Bot grammar "read" 
      ((if !debugrun then run_debug else 0)
	 + (if !debugall then full_debug else 0)
	 + (if !memflush then flush_memo else 0)
	 + (!memosize land 4095))
  in

  (* since the 'read' picks chars from the SAME input stream   *)
  (* succeeding 'feed' requests must be skewed forward because *)
  (* the main parser is "unaware" that the 'read' is stealing  *)
  (* characters from the same stream                           *)
  if !debugall then begin
    printobj parsed;
    (try
      printf "\nHAS READ new loc %i new skew %i [%s]\n" endloc 
	(oldskew + (endloc - oldloc)) (charfeed oldloc (endloc - oldloc));
    with Not_found -> printf "\nBARF\n");
  end;
  parseskew := oldskew + (endloc - oldloc);
  parseloc := endloc;
  parsed

let () =
  doreadexpr := actualread;

  Arg.parse
    [ ("-s", Arg.Set_string startrule, "name of starting rule, defaults to \"start\"");
      ("-k", Arg.Set_int memosize, "min size of memoized parses, defaults to 8, max 4095");
      ("-d", Arg.Set debugall, "display all parsing debug messages, EXTREMELY verbose");
      ("-t", Arg.Set stamping, "node stamps in debug messages");
      ("-g", Arg.Set gmessages, "display grammar debug messages");
      ("-r", Arg.Set debugrun, "display semantic runs debug messages");
      ("-n", Arg.Clear memflush, "do not flush memoized parses before each semantic run");
      ("-e", Arg.Set debugeval, "display interpreter evaluation debug messages");
      ("-p", Arg.Set evalprint, "print each eval result");
      ]

    (fun f ->  
      if !debugall then begin
	eprintf "FILE %s\n" f;
	flush stderr;
      end;
      let _ = fileinclude 0 0 (Str f) in ()) 

    "Usage: demo [options] [file] ...";
 
  (try 
    userprompt ();
    input := input_line (List.hd !chanstack);
    len := String.length !input;
  with
    End_of_file ->
      eprintf "NO input\n";
      flush stderr;);

  let (parsed,i) = ParseSample.streamparse !parseloc Bot grammar 
      (if !startrule <> "" then !startrule else "start")
      ((if !debugrun then run_debug else 0)
	 + (if !debugall then full_debug else 0)
	 + (if !stamping then node_stamping else 0)
	 + (if !memflush then flush_memo else 0)
	 + (!memosize land 4095))
  in

  printf "\nPARSED ";
  printobj parsed;
  printf "\n";
  flush stdout;

  if i <= 0 then (
    eprintf "parse error: parsing failed %i\n" i;
    exit 1
  )
  else if i + !parseskew < !len then (
    eprintf "parse error: %i extra characters after end of input\n" (!len - i);
    exit 1
  )
  else
    printf "parsed OK\n"
;;
