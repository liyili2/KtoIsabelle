(* parsing tree for K *)
type modId = ModId of string;;
type sortId = SortId of string;;
type cellName = CellName of string;;
type userListLabel = NormalList | NeList
type attribute = Anywhere | LeftAssoc | RightAssoc | NonAssoc | CoolRule | HeatRule
               | Bracket | Function | Macro | Seqstrict | OnlyLabel | KLabel of string
               | Strict of int list | Attribute of (string (* key *) * string (* value *))
type def = Definition of theModule list
and theModule = Require of string | DefComment of string | Module of (modId * moduleItem list)
and moduleItem = Import of modId
               | ModComment of string
               | Syntax of (sortId * priorityBlock list)
               | SyntaxPriority of term list list
               | Configuration of term
               | Rule of (string * term * term * term * attribute list) (* name, body, requires, ensures, attributes *)
               | Context of (term * attribute list)
and priorityBlock = PriorityBlock of (attribute * production list)
and production = SubsortRelation of (sortId * attribute list)
               | Normal of (productionItem list * attribute list)
               | LexToken of (string * attribute list)
               | Constant of (sortId * productionItem * attribute list)
               | Bracket of (productionItem list * attribute list)
               | UserList of (sortId * string (* separator *) * userListLabel)
and productionItem = Terminal of string | NonTerminal of sortId
and term = Bag of term list | Cell of (cellName * (string * string) list * term)
         | K of term list | KItem of (sortId * term * term) | KLabelAsTerm of string
         | FreshVar of (string * sortId) | FreshConst of (string * sortId)
         | VarTerm of (string * sortId) | Rewrite of (term * term)
         | KList of term list | IntBuiltin of int | StringBuiltin of string
         | FloatBuiltin of float | BoolBuiltin of bool | ListBuiltin of term list
         | MapBuiltin of term list | SetBuiltin of term list | Hole of sortId
         | Empty (* use for empty terms in rule's require and ensure field *)
