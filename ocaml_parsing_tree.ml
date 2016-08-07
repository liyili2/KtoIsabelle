(* parsing tree for K *)
type modId = ModId of string;;
type sortId = SortId of string;;
type attribute = Anywhere | LeftAssoc | RightAssoc | NonAssoc | CoolRule | HeatRule
               | Bracket | Function | Macro | Seqstrict | OnlyLabel | Klabel of string
               | Strict of int list | Attribute of (string * string)
type def = Definition of theModule list
and theModule = Require of string | DefComment of string | Module of (modId * moduleItem list)
and moduleItem = Import of modId
               | ModComment of string
               | Syntax of (sortId * priorityBlock list)
               | Configuration of term
and priorityBlock = PriorityBlock of (attribute * production list)
and production = SubsortRelation of (sortId * attribute list)
               | Normal of (productionItem list * attribute list)
               | LexToken of (string * attribute list)
               | Constant of (sortId * productionItem list)
               | Bracket of (productionItem list * attribute list)
and productionItem = Terminal of string | NonTerminal of sortId;;
 

