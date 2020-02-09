type token =
  | OtherSort of (char list)
  | MetaVar of (char list)
  | OtherVar of (char list)
  | LabelId of (char list)
  | BagEnd of (char list var)
  | Number of (int)
  | BagHead of (char list var * feature list)
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
  | LittleK
  | LPAREN
  | RPAREN
  | EOF
  | DoubleComma
  | UnitKList
  | Add
  | Sub
  | OR
  | AND
  | UnitBag
  | UnitMap
  | UnitSet
  | UnitList
  | UnitK
  | ListItem
  | SetItem
  | Mapsto
  | Bindsby
  | Leadsto

val main :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  (char list ,char list ,char list ) bag
