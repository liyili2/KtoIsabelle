/* Use the expression datatype defined in mp8common.ml: */
%{
    (*open Mp8common *)

(* add any extra code here *)


%}

/* Define the tokens of the language: */
%token <int> INT
%token <string> OP
%token EOF
%left OP "+"  OP "-"
%left OP "*"
%nonassoc OP "~"

/* Define the "goal" nonterminal of the grammar: */
%start main
%type <int> main

%%

main:
    INT                             { $1 }
  | (OP "~") main                        { - $2}
  | main (OP "+") main                 { $1 + $3}
  | main (OP "-") main                {$1 - $3}
  | main (OP "*") main                {$1 * $3}
  | (OP "(") main (OP ")")                   {$2}

