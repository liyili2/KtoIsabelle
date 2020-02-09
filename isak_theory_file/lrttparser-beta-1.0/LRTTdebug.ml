
(*

   LRTTparser.ml --  Left to Right Tree Traversal parser (modified MIT License)

   Copyright (c) 2012 Jean-Luc Delatre a.k.a. Kevembuangga

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

NO PART OF THIS SOFTWARE OR DERIVED VERSIONS SHALL BE LICENSED UNDER ANY OTHER TERMS THAN THE PRESENT LICENSE

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

*)

module type PARSETREE = sig
  type t
end;;

module Parser =
  functor (Parsetree: PARSETREE) ->
  struct
    open Printf
    exception Done
    exception Abort

    type parsevalue = Parsetree.t
    and grammar = production list
    and production = string * choice list       (* rule name -> e1 | e2 | ... *)
    and choice = string * string * parsing list (* choice name, comment, sequence *)
    and semantic = int -> int -> parsevalue -> parsevalue
    and messaging = int -> int -> string -> parsevalue -> unit
    and acceptor = int -> string -> int 
    and parsing =
      | A of acceptor * string              (* parsing test callback *)
      | S of semantic                       (* semantic action *)
      | D of semantic                       (* error recovery by deletion *)
      |	M of messaging * string             (* debugging action executed "en passant" *)
      | Z of parsing                        (* e* *)
      | P of parsing                        (* e+ *)
      | Opt of parsing                      (* e? *)
      | L of parsing                        (* lookahead, parsing resumes at the START *)
      | NT of string                        (* nonterminal 'name' *)
      | Empty                               (* epsilon *)
     and parsepoint = {  
	mutable from : parsepoint;              (* source node back pointer *)
	mutable source : string;                (* source node id *)
	mutable pos : int;                      (* text position at start of production *)
	mutable stamp : int;                    (* node stamp for debugging *)
	mutable prod : parsing list;            (* start of production *)
	mutable curs : parsing list;            (* end of production segment for this node  *)
	mutable recursive : parsing list;       (* location of recursive call in this production *)
	mutable hook : parsepoint list;         (* current recursive call of this node *)
	mutable successors : parsepoint list }  (* recursion stack + production list + node successor *)
	 
    let full_debug = 4096
    let run_debug = 8192
    let flush_memo = 16384
    let single_parse = 32768
    let node_stamping = 65536

    let streamparse cpos initial grammar rule opts =

      let fulldebug = (opts land full_debug) <> 0 in
      let rundebug = (opts land run_debug) <> 0 in
      let flushmemo = (opts land flush_memo) <> 0 in
      let fork = ref (if (opts land single_parse) <> 0 then 0 else -1) in
      let stamping = ref ((opts land node_stamping) <> 0) in
      let minspan = (opts land 4095) in   (* minimal size for memoized non terminals *)
 
      if fulldebug then 
	printf "OPTS D=%b R=%b U=%b F=%b S=%b M=%i\n" 
	  fulldebug rundebug (!fork = 0) flushmemo !stamping minspan;

      let parsed = ref initial in
      let rules = Hashtbl.create 101 in
      let parses = Hashtbl.create 101 in
      
      List.iter (fun (name,body) ->  Hashtbl.add rules name body;) grammar;
      
      let stamp = ref 0 in
      let start = [NT rule] in
      let root = { from = (Obj.magic 0);
		   source = "";
		   pos = cpos;
		   stamp = !stamp;
		   prod = start;
		   curs = start;
		   recursive = [];
		   hook = [];
		   successors = []
		 } in
      
      root.from <- root;
      let status = ref root in
      let seed = ref !status in
   
      let recursivecall parse = 
   	try match parse with
	| NT subr -> subr
	| P subparse | Z subparse | Opt subparse ->
	    (* recursion occurence embedded in optional parse *)
	    (match subparse with
	    | NT subr -> subr
	      | _ -> raise Done)
	| _ -> raise Done
	with Done ->
	  (* should not happen *)
	  eprintf "Parser ERROR, mutual recursion not a non terminal\n";
	  if fulldebug then printf "Parser ERROR, mutual recursion not a non terminal\n";
	  raise Abort;
      in

      let leftrecursive prod =
	prod.recursive <> [] && recursivecall (List.hd prod.recursive) = prod.source
      in
      
      let rec opcode parse =
	match parse with
	| A (_,id) ->  "<" ^ id ^ ">" 
	| S _ -> "<semantic>"
	| M _ -> "<message>"
	| Empty -> "()"
	| D _ -> "<deletion>"
	| Z subparse -> "(" ^ (opcode subparse) ^ ")*"
	| P subparse -> "(" ^ (opcode subparse) ^ ")+"
	| Opt subparse -> "(" ^ (opcode subparse) ^ ")?"
	| L subparse -> "--> (" ^ (opcode subparse) ^ ")"
	| NT subr -> "{" ^ subr ^ "}" 
      in
      
      let rec printparse parse =
	printf "%s " (opcode parse);
      in

      let printparselist pl = List.iter (fun p -> printparse p; printf " ";) pl
      in

      let printprodlist plis stop =
	let prod = ref plis in	
	while !prod <> [] do
	  if !prod == stop then printf "°";
	  printf " ";
	  printparse (List.hd !prod);
	  prod := List.tl !prod;
	done;
	printf "%s" (if stop = [] then "°" else "");
      in

      let printprodmisc h =
	printf "%i (%i) %i:'%s%s%s%s':= " h.pos 
	  (List.length h.successors)
	  h.stamp
	  (if h.hook <> [] && h.recursive <> [] then "* " else "")
	  (if leftrecursive h then "+" else "")
	  (if h.recursive <> [] then "R " else "")
	  h.source;
      in
      
      let printproduction h =
	printprodmisc h;
	printprodlist h.prod h.curs;
	printf "\n";
      in

      let rec mutualrecursive parse name =
	match List.hd parse.curs with
	| NT subr ->
	    (subr = name || parse != root && mutualrecursive parse.from name)
 	| P _ | Z _ | Opt _ ->
	    mutualrecursive parse.from name
	| _ -> false 
      in

      let rec checkancestors subr pos h =
	if h == root then
	  false
	else if h.pos = pos && h.recursive <> [] && h.source = subr then
	  true  (* detect identical recursive occurrences at the same location *)
	else 
	  checkancestors subr pos h.from;
      in

      let rec printancestors h =
	if h != root then printancestors h.from;
	printf "PRED ";
	printproduction h
      in
      
      let rec printflow parse =
	let n = ref 0 in
	let h = ref parse in
	while !h.successors <> [] do
	  for k = !n downto 0 do printf "    "; done;
	  n := !n + 1;
	  printf "FLOW ";
	  printproduction (List.hd !h.successors);
	  h := List.hd !h.successors;
	done;
      in

      let printnonterm parse head succ =
	printf "%s" head;
	printproduction parse;
	List.iter (fun s ->
	  printf "%s" succ;
	  printproduction s) parse.successors
      in

      let tdepth = ref 0 in

      let rec printfulltree parse =
	for k = !tdepth downto 0 do printf "    "; done;
	printproduction parse;
	if parse.successors <> [] then
	  let save = !tdepth in
	  List.iter (fun p -> 
	    tdepth := !tdepth + 1;
	    printfulltree p) (List.rev (List.tl parse.successors));
	  tdepth := save;
	  printfulltree (List.hd parse.successors);
      in

      let rec runsemantic deep parse = 
	(* store the last seed  *)
	seed := parse;   
	let  curs = ref parse.prod in
	let skew = ref 0 in

	let printline () =
	  if rundebug then begin
	    if false && fulldebug then  begin
	      printproduction parse;
	      printflow parse;
	    end;
	    let pad = String.make (max 0 (10 - String.length parse.source)) ' ' in
	    printf "%i %i \t%s " (parse.pos + !skew)
	      deep
	      (if parse.source = "" then ("{}" ^ pad) else ("{" ^ parse.source ^ "}" ^ pad));
	    if false then printprodlist !curs parse.curs;
 	  end;
	in
	
	while !curs <> [] do
	  printline ();
	  (match (List.hd !curs) with
	  | NT subr -> 
	      if rundebug then begin 
		printf "  ";
 		printprodlist !curs parse.curs;
 	      end;

	  | Empty -> 
	      if rundebug then printf "() ";
	      
	  | A (_,name) -> 
	      if rundebug then printf "(%s) " name;
	      
	  | M (_,msg) -> 
	      (* debugging messages are not executed during *)
	      (* the "run" but during parsing attempts      *)
	      if rundebug then printf "(message %s) " msg;
	      
	  | S callback -> 
	      if rundebug then printf "\nSEM ";
	      parsed := callback parse.from.pos parse.pos !parsed;
 	      
	  | D callback -> 
	      if rundebug then printf "\nDEL ";
 	      parsed := callback parse.from.pos parse.pos !parsed;
 		  
	  | L subparse -> 
	      if rundebug then 	printf "(-->) "

	  | Z subparse -> 
	      if rundebug then printf "(*) "
	      
	  | P subparse ->
	      if rundebug then printf "(+) "
	      
	  | Opt subparse -> 
	      if rundebug then printf "(?) ");

	  if !curs != parse.curs then
	    curs := List.tl !curs
	  else 
	    curs := [];
	done;
	
	if rundebug then printf "\n";

	if parse.successors <> [] then begin
	  List.iter (fun a -> runsemantic (deep + 1) a) (List.rev (List.tl parse.successors));
	  runsemantic deep (List.hd parse.successors);
	  (* erase the used up successors to free memory *)
	  parse.successors <- [];
	end;
      in
      
      let getruleprods rule = try Hashtbl.find rules rule with Not_found -> [] 
      in
      
      let showscan = false in

      let rec markrecursive rulestack prod =
        (* return the recursion occurence point in the 'prod' production *)
        (* exits with 'Done' when a solid non recursive term is met      *)

	let printrstack () =  List.iter (fun a -> printf "%s " a) rulestack in

	if showscan && fulldebug then begin
	  printf "SCAN ";
	  printrstack ();
	  printprodlist prod prod;
	  printf "\n";
	end;

	let curs = ref prod in
	let mark = ref [] in
	while !curs <> [] do
	  if showscan && fulldebug then begin
	    printf " => ";
	    printparse (List.hd !curs);
	    printf "\n";
	  end;
	  match List.hd !curs with
	  | A _ ->  raise Done

	  | L sub -> 
	      (match sub with  L _ -> raise Done | _ -> curs := List.tl !curs)

	  | NT subr -> 
	      if List.mem subr rulestack then begin
		if subr <> List.nth rulestack ((List.length rulestack) - 1) then 
		  raise Done;

		if fulldebug then begin
		  printprodlist prod !curs;
		  printf "\n";
		  printf "RECURSIVE ";
		  printparse (List.hd !curs);
		  printf " AMONG ";
		  printrstack ();
		  printf "\n";
		end;

		mark := !curs;
		curs := [];
	      end
	      else
		let stack = subr :: rulestack in
		let solid = ref true in
		let recurs = ref false in
		List.iter (fun (_, _, alt) ->
		  try
		    if markrecursive stack alt <> [] then
		      recurs := true;
		    if false && fulldebug then begin
		      printf "%s THRU R=%b " (List.hd rulestack) !recurs;
		      printprodlist alt alt;
		      printf "\n";
		    end;
		    solid := false;
		  with Done -> 
		    if false && fulldebug then printf "SOLID\n";
		    ()
		      ) (getruleprods subr);
		
		if !solid then 
		  raise Done
		else
		  if !recurs then begin
		    mark := !curs;
		    curs := [];
		  end else
		    curs := List.tl !curs;
		
	  | Z sub | Opt sub ->
	      (try 
		mark := markrecursive rulestack [sub]
	      with Done -> mark := []);
	      if !mark <> [] then begin
		mark := !curs;
		curs := [];
	      end else
		curs := List.tl !curs;
	      
	  | P sub ->  
	      (try 
		mark := markrecursive rulestack [sub]
	      with Done -> curs := []);
	      if !curs = [] then raise Done;
	      if !mark <> [] then begin
		mark := !curs;
		curs := [];
	      end else
		curs := List.tl !curs;
	      
	  |  _ -> 
	      curs := List.tl !curs;
	done;
	!mark
      in
      
      let expandstate origin spos subr =
	
	if fulldebug then
	  printf "expandstate '%s' \t[0-%i]\n" subr spos;

	let prods = getruleprods subr in
	if prods = [] then begin
	  eprintf "Grammar ERROR, rule %s has no defined productions\n" subr;
	end;
	
 	if fulldebug then begin
	  printf "ORIGIN ";
	  printproduction origin;
	end;

        (* prepare all variants before rule expansion *)
	
	let spare = ref [] in
	let mutual = ref [] in
	
	List.iter (fun (name, _, parse) -> 
	  if !stamping then stamp := !stamp + 1;
	  let sprod =  { from = origin;
			 source = subr;
			 pos = spos;
			 stamp = !stamp;
			 prod = parse;
			 curs = parse;
			 hook = [];
			 recursive = [];
			 successors = []
		       }
	  in
	  
	  try
	    sprod.recursive <- markrecursive [subr] parse;
	    
	    if sprod.recursive <> [] then
	      if leftrecursive sprod then
		origin.successors <- sprod :: origin.successors
	      else
		mutual := sprod :: !mutual
	    else
	      spare := sprod :: !spare;
	    
	    if false && fulldebug then begin
	      printf "%s/%s \t" subr name;
	      printparselist parse;
	      printf "%s\n" (if (List.hd origin.successors).recursive <> [] then " R" else " <V>");
	    end;

	  with Done -> 
	    if false && fulldebug then begin
	      printf "%s/%s \t" subr name;
	      printparselist parse;
	      printf "\n";
	    end;
	    spare := sprod :: !spare;
	    )  prods;
	
	(* keep productions in original order except recursive *)
	(* ones which are moved beyond the non recursive ones  *)
	(* while mutual recursives are moved in front          *)

	origin.successors <- List.rev_append !mutual (List.rev_append !spare (List.rev origin.successors))
      in

      let rec endposition parse =
	if parse.successors = [] then 
	  if parse.curs = [] then
	    parse.pos
	  else
	    match (List.hd parse.curs) with
	    | A (callback, name) ->  parse.pos + (callback parse.pos name)
	    | _ -> parse.pos
	else
	  endposition (List.hd parse.successors)
      in
      
      let rec endproduction nex =
	let above = !status.from in

	if fulldebug then begin
	  printf "NEXT %i " nex;
	  printproduction above;
	end;
	
	(* all 'continueparse' are tail calls *)
	
	match (List.hd above.curs) with
	  
	| P subparse | Z subparse ->
	    continueparse nex above [subparse] "repeat";
	    
	| Opt _ ->
	    status := above;
	    continueparse nex !status.from (List.tl !status.curs) "OPT";
	    
	| L _ ->
	    status := above;
	    raise Abort;
	    
	| NT subr -> 
	    if !status.hook <> [] && leftrecursive !status then begin
	      (* BOTH left & right recursive! *)
	      if fulldebug then begin
		    printf "BOTH   ";
		    printfulltree !status;
		    printf "HOOK %i " (List.length !status.hook);
		    printfulltree (List.hd !status.hook);
	      end;
	      let more = (List.hd !status.hook).curs in
	      continueparse !status.pos !status.from more "middle";
	    end else
	      let succ = ref [] in
	      if fulldebug then begin
		printf "ENDP %s FORK=%i\n" subr !fork;
		printnonterm above "FINAL " "      ";
	      end;
	      
	      status := above;
	      if !status.successors <> [] then begin
		succ :=  (List.hd !status.successors).hook;
		(List.hd !status.successors).hook <- [];   (* release memory reference *)
		
	        (* only direct left recursion is kept *)
		while !succ <> [] && not (leftrecursive (List.hd !succ)) do
		  if fulldebug then begin
		    printf "NONREC ";
		    printfulltree (List.hd !succ);
		  end;
		  succ := List.tl !succ;
		done;
	      end;

	      if fulldebug then begin
		if !succ <> [] then begin
		  printf "KEPT   ";
		  printfulltree (List.hd !succ);
		end;
		if false then printnonterm !status "REDUCED " "  STILL ";
		printf "REDUCED %s %i FORK=%i\n" subr !status.pos !fork;
		printfulltree !status;
	      end;

	    if !succ <> [] then
	      launchrecursion nex !succ
	    else		      
	      finalreduction nex subr;
	    	    
	| _ -> 
	    eprintf "Parser ERROR in end production of '%s', caller NOT a non terminal!\n" !status.source;
	    flush stderr;
	    if fulldebug then begin
	      printf "Parser ERROR in end production of '%s', caller NOT a non terminal!\n"  !status.source;
	      printproduction !status;
	    end;	    
	    
      and continueparse pos from parse name =
	
	if fulldebug then begin
	  printf "CONT ";
	  printprodmisc !status;
	  printprodlist !status.prod !status.curs;
	  printf " [%s]" name;
	end;
	
	if parse = [] then begin
	  if fulldebug then begin
	    printf " <void>\n";
	    printf "DONE ";
	    printfulltree !status;
	  end;
	  
	  if !status != !status.from then
	      endproduction pos;     (* tail call *)

	end else begin
	  
	  if fulldebug then printf "\n";
	  
	  if !stamping then stamp := !stamp + 1;
	  !status.successors <- { from = from;
				  source = (match List.hd from.curs with | NT subr -> subr| _ -> "");
				  pos = pos;
				  stamp = !stamp;
				  prod = parse;
				  curs = parse; 
				  recursive = [];
				  hook = [];
				  successors = []
				} :: !status.successors;

	  status := List.hd !status.successors;

	  if fulldebug then begin
	    printancestors !status;
	    if !status.from.successors <> [] then
	      printnonterm (List.hd !status.from.successors) "  UP " " NEW ";
	  end;
	end
	    
     and confirm inline pos name = 
	(* erasing 'D' opcodes when no longer relevant *)
	if fulldebug then
	  printnonterm !status ("CONFIRM " ^ name ^ " ") ("        " ^ (String.make (1 + String.length name) ' '));	
	if List.tl !status.curs <> [] && 
	  (match List.hd (List.tl !status.curs) with | D _ -> true | _ -> false) then begin
	    if fulldebug then begin
	      printf "ERASE ";
	      printproduction !status;
	    end;
	    continueparse pos !status.from (List.tl (List.tl !status.curs)) name;
	  end else if inline then
	    !status.curs <- List.tl !status.curs
	  else 
	    continueparse pos !status.from (List.tl !status.curs) name;

      and launchrecursion pos succ =

	let head = List.hd succ in

	if head.prod = [] then begin
	  eprintf "ERROR in grammar, recursive rule '%s' is an empty production\n" head.source;
	  flush stderr;
	  if fulldebug then printf "ERROR in grammar, recursive rule '%s' is an empty production\n" head.source; 
	  raise Done;
	end;

	let subr = head.source in
	let prev = !status in
	continueparse pos !status head.prod ("recurse " ^ subr);
	!status.recursive <- head.recursive;
	!status.source <- subr;                                (* exception to 'continueparse' default *)
	!status.hook <- succ;                                  (* remember tried recursions *)
		
        (* skip over the recursion occurrence to adjust the ending position *)
	(* thus keeping leading semantics in front of recursive NT          *)

	if leftrecursive !status then begin	
	  !status.curs <- !status.recursive;
	  if fulldebug then begin
	    printf "SKIP ";
	    printproduction !status;
	  end;
	  confirm true pos "OVER";
	end;

	if fulldebug then begin
	  printancestors !status;
	  printf "INSERT ";
	  printproduction head;
	  printnonterm prev "FROM   " " STACK ";
	  printnonterm !status "RECURSION " "          " ;
	  let n = ref 0 in
	  List.iter (fun s -> 
	    n := !n + 1; 
	    printf "succ %i\n" !n;
	    printfulltree s) !status.hook;
	end;

      and finalreduction pos subr =

	if !status.successors <> [] then
	  (List.hd !status.successors).hook <- [];   (* release memory reference *)

	if pos > !status.pos then begin
 	  if fulldebug then printf "CLEAR %s,%i-%i FORK=%i\n" subr !status.pos pos !fork;
	  Hashtbl.remove parses (subr, !status.pos);
	  if pos - !status.pos >= minspan && !status.from != !status then begin
	    if fulldebug then begin
	      printnonterm !status ("MEMOIZE '" ^ subr ^ "' ") "INNER ";
	    end;
	    Hashtbl.add parses (subr, !status.pos) !status.successors;
	  end
	end;

	(* decrease 'fork' before calling confirm because of 'L' aborting *)
	fork := !fork - 1;

	confirm false pos ("reduce " ^ subr);

	if !fork <= 0 then begin

          (* incremental semantic upon ambiguity resolution (single parsing path) *)
	  
	  if fulldebug then begin
	    printf "RUN %s FORK=%i\n" subr !fork;
	    printnonterm !seed.from "UPPER  " " STACK ";
	    printfulltree !seed;
	    flush stdout;
	  end;

	  if flushmemo then
	    Hashtbl.clear parses;

	  if false then begin
	    printf "\nR\n";
	    flush stdout;
	  end;

	  if !seed.from.successors <> [] && List.tl !seed.from.successors = [] then begin
	    let real = List.hd !seed.from.successors in
	    !seed.from.successors <- [];
	    seed := real;
	  end;
	  runsemantic 0 !seed;

	  if fulldebug then begin 
	    printf "]SEED ";          (* ']' is closing the 'FORK' bracket *)
	    printproduction !seed;
	  end;

	  (* exit when the root parse has been reached *)
	  if !status == !status.from then begin
	    if fulldebug then printf "FINISH\n";
	    !status.curs <- [];
	    raise Done;
	  end;

	end else if fulldebug then begin
	  printf "FORK -'%s' %i [%i-%i] " subr !fork !status.from.pos pos;
	  printf "]\n";
	end;
      in

      let dismiss parse subr =
	fork := !fork - 1; 
	if fulldebug then begin
	  printf "DISMISS -'%s' %i  FORK=%i [0-%i] " subr parse.pos !fork parse.pos;
	  printf "]\n"; 
	  if false then printnonterm parse "DISS   " " FLUSH ";
	end;
	try
	  (* do not clobber successful left recursion *)
	  let _ = Hashtbl.find parses (subr, !status.pos) in ();
	with Not_found ->
	  Hashtbl.add parses (subr, !status.pos) [];
	  if fulldebug then
	    printf "PREVENTED\n";
      in
      
      (try             (* Done *)
	while true do  (* depth first expansion of current branch  *)
	
	  try          (* Abort, to cancel a failing branch *)
	    
	    (* 'endproduction' will return with non empty parsepoint or raise Done *)
	    while !status.curs = [] do
	      endproduction !status.pos;
	    done;

	    if fulldebug then begin
	      if !status.from != root then begin
		printf "ABOVE  ";
		printproduction !status.from;
	      end;
	      printnonterm !status "HEAD   " "       ";
	      flush stdout;
	    end;
	    
	    match List.hd !status.curs with 
	
	    | A (callback, name) -> 
		if false then begin
		  printf "<A %s>" name;
		  flush stdout;
		end;
		let k = callback !status.pos name in
		if false then begin
		  printf "<B>";
		  flush stdout;
		end;
		if k = 0 then raise Abort;
		if k < 0 then begin
		  if fulldebug then printf "--EOF-- FORK=%i\n" !fork;
		  confirm true !status.pos "erase at EOF";
		end else begin
		  if fulldebug then printf "Accept '%s' %i %i\n" name !status.pos k;
		  !status.pos <- !status.pos + k;
		  confirm true !status.pos ("erase " ^ name);
		end

	    | Empty | S _ -> 
		confirm true !status.pos "erase";

	    | D _ -> 
		eprintf "ERROR, misplaced deletion in '%s'\n" !status.source;
		if fulldebug then printf "ERROR, misplaced deletion in '%s'\n" !status.source;
		raise Abort;

	    | M (callback,msg) -> 
		callback !status.from.pos !status.pos msg !parsed;
		confirm true !status.pos "erase";

	    | P subparse | Z subparse -> 
		continueparse !status.pos !status [subparse] "(*/+)"
	    
	    | Opt subparse -> 
		continueparse !status.pos !status [subparse] "(?)"
		  
	    | L subparse -> 
		continueparse !status.pos !status [subparse] "(-->)"
		  
	    | NT subr -> 
		try
	          (* retrieve memoized parse tree if any *)

		  if fulldebug then begin
		    printnonterm !status "RETRIEVE " "    SUCC ";
		    if false && !status.hook <> [] then begin
		      let n = ref 0 in
		      List.iter (fun s -> 
			n := !n + 1; 
			printf "succ %i\n" !n;
			printfulltree s) !status.hook;
		      printfulltree (List.hd !status.hook);
		    end;
		  end;

		  !status.successors <- Hashtbl.find parses (subr, !status.pos);

		  if !status.successors = [] then begin
		    if fulldebug then printf "NULLSTATE %s,%i FORK=%i\n" subr !status.pos !fork;
		    if !status == root then raise Done;
		    raise Abort;   (* memoized rejection *)
		  end;

		  if fulldebug then begin
		    printf "TREE %i\n" (endposition !status);
		    printfulltree !status;
		  end;

		  confirm false (endposition !status) "RECALL";
		  
		with Not_found ->
		  
		  expandstate !status !status.pos subr;

		  if fulldebug then begin
		    if true then printancestors !status;
		    if !status.from != root then begin
		      printnonterm !status.from "FROM  " " WITH ";
		    end;
		    printnonterm !status "STATE " " SUCC ";
		  end;
		  
		  if !status.successors = [] || leftrecursive (List.hd !status.successors) then begin
		    eprintf "Grammar ERROR, rule '%s' has no non recursive production\n" subr;
		    flush stderr;
		    raise Abort;
		  end;

		  if (List.hd !status.successors).recursive <> [] && 
		    checkancestors subr !status.pos !status.from then
		    (* THIS IS THE CORE OF RECURSION RESOLUTION *)
		    (* remove recursive productions ONLY when   *)
		    (* they are actually entering a loop        *)
		    while (List.hd !status.successors).recursive <> [] do
		      !status.successors <- List.tl !status.successors;
		      if !status.successors = [] then begin
			if fulldebug then printf "REJECT %s,%i FORK=%i\n" subr !status.pos !fork;
			raise Abort;
		      end;
		    done;
		  
		  (List.hd !status.successors).hook <- !status.successors;  (* remember start point *)
		  !status.successors <- [List.hd !status.successors];       (* pick the first production *)
		  status := List.hd !status.successors;                     (* launch *)
		  fork := !fork + 1;                                        (* number of forked paths *)
		  if fulldebug then printf "FORK +'%s' %i [0-%i] [\n" subr !fork !status.pos;
		  
	  with Abort -> 
	    if fulldebug then begin
	      printf "-----\n";
	      printnonterm !status "ABORT  " "       ";	
	    end;
	    let curs = ref (List.tl !status.curs) in
	    while !curs <> [] && (match List.hd !curs with | S _ | M _ | Empty -> true |  _ -> false)
	    do
	      curs := List.tl !curs;
	    done;
	
	    if !curs <> [] && (match List.hd !curs with  | D _ -> true |  _ -> false) then begin
	      (* recovery by text deletion *)
	      if fulldebug then
		printnonterm !status.from "DELETION " "      OF ";
	      !status.from.successors <- [!status];
	      !status.prod <- !curs;
	      !status.curs <- List.tl !curs;
	    end
	    else (try  (* Done *)

	      (* unwind current branch until solid or end-of-grammar *)
	      while !fork >= 0 && !status != root do    
		
		let prev = !status in
		status := !status.from;

		if fulldebug then begin
		  printnonterm prev "UNWIND " " SUCC ";
		  printf "  ---> ";
		  printfulltree !status;
		end;
		
		match List.hd !status.curs with
		  
		| L _ ->
		    (try
		      continueparse !status.pos !status.from (List.tl !status.curs) "PASS";
		      raise Done;
		    with Abort ->
		      (* nested lookahead, accept without advancing *)
		      if fulldebug then
			printf "NOTNOT %i\n" !status.pos;
		      ());

		| P _ | Z _ | Opt _ ->
		    
	            (* locate last repeated item *)
		    let stop = ref [] in
		    let sucs = ref !status.successors in
		    while !sucs <> [] && (List.hd !sucs).successors <> [] do
		      if fulldebug then begin
			printf "SKIP ";
			printfulltree (List.hd !sucs);
		      end;
		      stop := !sucs;
		      sucs := (List.hd !sucs).successors;
		    done;
		    
		    if !stop <> [] && List.hd !sucs == prev then begin
		       (* remove only the last failed repeat *)
		      status := List.hd !stop;

		      if fulldebug then begin
			printf "KILL ";
			printfulltree prev;
			printnonterm !status  "KEPT   " "   OFF ";
		      end;

		      !status.successors <- List.tl !status.successors;    (* erase partial match *)
		      status := !status.from;
		      continueparse prev.pos !status.from (List.tl !status.curs) "ENDREP";
		      raise Done;

		    end else begin

		      if fulldebug then printnonterm !status  "KILL   " "   OFF ";

		      if (match List.hd !status.curs with | P _ -> false | _ -> true) then begin
		        (* optional subterm not matched but accepted as empty  *)
			!status.successors <- [];  (* erase partial match *)
			continueparse prev.pos !status.from (List.tl !status.curs) "NOPE";
			raise Done;
		      end;
		    end;
		    
		| NT subr ->
	            
		    if !status.successors <> [] then
		    let slot = List.hd !status.successors in
		    !status.successors <- List.tl !status.successors;
		    
		    if fulldebug then begin
		      printnonterm slot "REMOVE " "  SUCC " ;
		      if false then begin
			printf "REMOVE from\n";
			printfulltree !status;
		      end;
		    end;
		    
		    if slot.hook = [] then begin
		      eprintf "Parser ERROR, lost productions list for rule '%s'\n" subr;
		      flush stderr;
		      raise Abort;
		    end;

		    if List.tl slot.hook <> [] then begin

		      (* try next production *)

		      let go = List.hd (List.tl slot.hook) in
		      go.hook <- List.tl slot.hook;
		      slot.hook <- [];

		      if fulldebug then begin
			printnonterm !status "AGAIN  " " TAIL  ";
			printnonterm go "GO  " "    ";
			let n = ref 0 in
			List.iter (fun s -> 
			  n := !n + 1; 
			  printf "succ %i\n" !n;
			  printfulltree s) go.hook;
		      end;

		      if leftrecursive go && !status.successors = [] then begin
			dismiss !status subr;
		      end
		      else
			if !status.successors = [] then begin

			  (* still awaiting for an initial match, launch next production *)
			  !status.successors <- [go];
			  status := go;
			  raise Done;			
			  
			end else if go.recursive <> [] then begin
			  if fulldebug then printf "ABORTED %s -> %s\n" slot.source go.source;
			  launchrecursion slot.pos go.hook;
			  raise Done;			
			end else begin
			  eprintf "Parser ERROR, non recursive production lingering in production list for rule '%s'.\n" subr;
			  printf "Parser ERROR, non recursive production lingering in production list for rule '%s'.\n" subr;
		      end

		    end else if !status.successors = [] then begin
		      (* all productions have been rejected *)
		      dismiss !status subr;
		      if !status == root then raise Done;  (* whole text rejected *)
		    end else begin
		      (* last recursion attempt failed yet the original term succeeded  *)
		      finalreduction slot.pos subr;
		      raise Done;
		    end
		| _ -> ();
	      done;             (* while true *)
	    with Done -> ());   (* unwind current branch until solid *)
	    
	    if !fork < 0 then raise Done;
	    
	done;    (* while true, depth first expansion of current branch  *)
      with Done -> ());

      (* return the last parsevalue & the position beyond last parse *)

      (!parsed,endposition !seed) 
	
  end;;
