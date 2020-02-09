{
 open Mp8;;
 
}

(* You can assign names to commonly-used regular expressions in this part
   of the code, to save the trouble of re-typing them each time they are used *)

let numeric = ['0' - '9']
let lowercase = ['a' - 'z']
let alpha = ['a' - 'z' 

               'A' - 'Z' ]
let letter =['a' - 'z' 'A' - 'Z' '_']
let special = ['`' '~' '!' '@' '#' '$' '%' '^' '&' '*' '(' ')' '-' '=' '+' '[' '{' ']' '}' '|' ';' ':' '\'' ',' '<' '.' '>' '/' '?']

let id_char = numeric | letter | "'" | "_"
let open_comment = "(*"
let close_comment = "*)"
let whitespace = [' ' '\t' '\n']

let escapednum = '0' numeric numeric | '1' numeric numeric | '2' ['0' - '4'] numeric | "25" ['0' -'5']

let xml_id 

rule token = parse
  | [' ' '\t'] { token lexbuf }
  | ['\n']     { token lexbuf }  (* skip over whitespace *)
  | eof        { EOF }

(* your rules go here *)
  | "~"       { OP "~" }
  | "+"       { OP "+"  }
  | "-"       { OP "-"  }
  | "*"       { OP "*"  }
  | "("        {OP "("}
  | ")"        {OP ")"}

  | numeric+ as s                      { INT (int_of_string s) }

(* do not modify this function: *)
{
let lextest s = token (Lexing.from_string s)

 }
