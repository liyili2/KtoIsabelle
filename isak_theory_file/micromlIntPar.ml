(*
  interactive-parser.ml - DO NOT EDIT
*)

open Mp8common
open Student

let _ =
  print_endline "\nWelcome to the Student parser \n";
  let rec loop gamma =
  try
      let lexbuf = Lexing.from_channel stdin in
        print_string "> "; flush stdout;
        (try
          let dec = main (fun lb -> match Micromllex.token lb
                         with EOF -> raise Micromllex.EndInput
                     | r -> r)
                    lexbuf in
          match infer_dec gather_dec_ty_constraints gamma dec with
             None          -> (print_string "\ndoes not type check\n"; loop gamma)
           | Some (env_inc,p) ->
              let gamma' = sum_env env_inc gamma
              in
                        (pretty_print_env print_tyExp env_inc;
                              print_newline();
                              print_string "\n\nfinal environment:\n\n";
                              print_env print_tyExp gamma';  print_string "\n\nproof:";
                              print_proof print_tyExp p; loop gamma')
        with Failure s -> (print_newline(); print_endline s; print_newline(); loop gamma)
           | Parsing.Parse_error -> print_string "\ndoes not parse\n"); loop gamma;
  with Micromllex.EndInput -> exit 0
(* in loop init_type_env *)
  in loop empty_env
