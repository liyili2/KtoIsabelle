open K
open K
type token =
  | Terminal of (char list)
  | OtherSort of (char list)
  | ARule of (char list)
  | AContext of (char list)
  | Klabel of (char list)
  | AConfi of (char list)
  | LabelId of (char list)
  | OtherSynAttr of (char list)
  | Attr of (synAttrib list)
  | Strict of (nat list)
  | AToken of (atoken list)
  | Connect of (token * token)
  | Bool
  | K
  | KItem
  | KLabel
  | KResult
  | KList
  | List
  | Set
  | Map
  | Bag
  | Id
  | String
  | Int
  | Float
  | ASyntax
  | Assign
  | Bar
  | Gt
  | EOF
  | Left
  | Right
  | Function
  | Seqstrict
  | NonAssoc
  | Tokena
  | Avoid
  | Bracket
  | LBig
  | RBig
  | Dot
  | TheStar
  | Plus
  | LPAREN
  | RPAREN

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  (char list) theoryParsed
