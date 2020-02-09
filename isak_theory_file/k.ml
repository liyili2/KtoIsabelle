module K : sig
  type num = One | Bit0 of num | Bit1 of num
  type int = Zero_int | Pos of num | Neg of num
  type 'a equal = {equal : 'a -> 'a -> bool};;
  type nat = Zero_nat | Suc of nat
  type 'a rewrite = KTerm of 'a | KRewrite of 'a * 'a
  type 'a metaVar = Defined of 'a | Generated of nat | FunHole
  type nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
    Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC |
    NibbleD | NibbleE | NibbleF
  type char = Char of nibble * nibble
  type real
  type theConstant = IntConst of int | FloatConst of real |
    StringConst of char list | BoolConst of bool | IdConst of char list
  type 'a sort = Bool | K | KItem | KLabel | KResult | KList | List | Seta | Map
    | Bag | OtherSort of 'a | Top | Int | Float | Id | String
  type 'a label = UnitLabel of 'a sort | ConstToLabel of theConstant | Sort |
    GetKLabel | IsKResult | AndBool | NotBool | OtherLabel of char list |
    TokenLabel of char list
  type stdType = Stdin | Stdout
  type key = Star | Question
  type feature = Multiplicity of key | Stream of stdType | DotDotDot
  type 'a var = LittleK | OtherVar of 'a
  type ('a, 'b, 'c) kLabel = KLabelC of 'a label |
    KLabelFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite |
    IdKLabel of 'c metaVar
  and ('a, 'b, 'c) bigKWithBag = TheBigK of ('a, 'b, 'c) bigK |
    TheBigBag of ('a, 'b, 'c) bag rewrite |
    TheLabel of ('a, 'b, 'c) kLabel rewrite
  and ('a, 'b, 'c) kList =
    KListCon of ('a, 'b, 'c) kList rewrite * ('a, 'b, 'c) kList rewrite |
    UnitKList | KListItem of ('a, 'b, 'c) bigKWithBag | IdKList of 'c metaVar
  and ('a, 'b, 'c) kItem =
    KItemC of ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kList rewrite * 'a sort
    | Constant of theConstant * 'a sort | IdKItem of 'c metaVar * 'a sort |
    HOLE of 'a sort
  and ('a, 'b, 'c) k = Tilda of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite
    | UnitK | IdK of 'c metaVar | SingleK of ('a, 'b, 'c) kItem rewrite |
    KFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) theMap =
    MapCon of ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) theMap rewrite |
    UnitMap | IdMap of 'c metaVar |
    MapItem of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
    MapFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) theSet =
    SetCon of ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) theSet rewrite |
    UnitSet | IdSet of 'c metaVar | SetItem of ('a, 'b, 'c) k rewrite |
    SetFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) theList =
    ListCon of ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) theList rewrite |
    UnitList | IdList of 'c metaVar | ListItem of ('a, 'b, 'c) k rewrite |
    ListFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
  and ('a, 'b, 'c) bigK = TheK of ('a, 'b, 'c) k rewrite |
    TheList of ('a, 'b, 'c) theList rewrite |
    TheSet of ('a, 'b, 'c) theSet rewrite |
    TheMap of ('a, 'b, 'c) theMap rewrite
  and ('a, 'b, 'c) bag =
    BagCon of ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) bag rewrite | UnitBag |
    IdBag of 'c metaVar |
    Xml of 'b var * feature list * ('a, 'b, 'c) bag rewrite |
    SingleCell of 'b var * feature list * ('a, 'b, 'c) bigK
  type ('a, 'b) irKLabel = IRKLabel of 'a label | IRIdKLabel of 'b metaVar
  type ('a, 'b, 'c) irK = KPat of ('a, 'b, 'c) irKItem list * 'c metaVar option
  and ('a, 'b, 'c) irMap =
    MapPat of (('a, 'b, 'c) irK * ('a, 'b, 'c) irK) list * 'c metaVar option
  and ('a, 'b, 'c) irSet = SetPat of ('a, 'b, 'c) irK list * 'c metaVar option
  and ('a, 'b, 'c) irList = ListPatNoVar of ('a, 'b, 'c) irK list |
    ListPat of ('a, 'b, 'c) irK list * 'c metaVar * ('a, 'b, 'c) irK list
  and ('a, 'b, 'c) irBigKWithBag = IRK of ('a, 'b, 'c) irK |
    IRList of ('a, 'b, 'c) irList | IRSet of ('a, 'b, 'c) irSet |
    IRMap of ('a, 'b, 'c) irMap | IRBag of ('a, 'b, 'c) irBag
  and ('a, 'b, 'c) irBag =
    BagPat of
      ('b var * (feature list * ('a, 'b, 'c) irBigKWithBag)) list *
        'c metaVar option
  and ('a, 'b, 'c) irBigKWithLabel = IRBigBag of ('a, 'b, 'c) irBigKWithBag |
    IRBigLabel of ('a, 'c) irKLabel
  and ('a, 'b, 'c) irKList = KListPatNoVar of ('a, 'b, 'c) irBigKWithLabel list
    | KListPat of
        ('a, 'b, 'c) irBigKWithLabel list * 'c metaVar *
          ('a, 'b, 'c) irBigKWithLabel list
  and ('a, 'b, 'c) irKItem =
    IRKItem of ('a, 'c) irKLabel * ('a, 'b, 'c) irKList * 'a sort list |
    IRIdKItem of 'c metaVar * 'a sort list | IRHOLE of 'a sort list
  type ('a, 'b, 'c) matchFactor = KLabelMatching of ('a, 'c) irKLabel |
    KItemMatching of ('a, 'b, 'c) irKItem |
    KListMatching of ('a, 'b, 'c) irKList | KMatching of ('a, 'b, 'c) irK |
    ListMatching of ('a, 'b, 'c) irList | SetMatching of ('a, 'b, 'c) irSet |
    MapMatching of ('a, 'b, 'c) irMap | BagMatching of ('a, 'b, 'c) irBag
  type ('a, 'b, 'c) pat = KLabelFunPat of 'a label * ('a, 'b, 'c) irKList |
    KFunPat of 'a label * ('a, 'b, 'c) irKList |
    KItemFunPat of 'a label * ('a, 'b, 'c) irKList |
    ListFunPat of 'a label * ('a, 'b, 'c) irKList |
    SetFunPat of 'a label * ('a, 'b, 'c) irKList |
    MapFunPat of 'a label * ('a, 'b, 'c) irKList |
    NormalPat of ('a, 'b, 'c) matchFactor
  type ('a, 'b, 'c) suBigKWithBag = SUK of ('a, 'b, 'c) suKFactor list |
    SUList of ('a, 'b, 'c) suL list | SUSet of ('a, 'b, 'c) suS list |
    SUMap of ('a, 'b, 'c) suM list | SUBag of ('a, 'b, 'c) suB list
  and ('a, 'b, 'c) suB =
    ItemB of 'b var * feature list * ('a, 'b, 'c) suBigKWithBag |
    IdB of 'c metaVar
  and ('a, 'b, 'c) suBigKWithLabel = SUBigBag of ('a, 'b, 'c) suBigKWithBag |
    SUBigLabel of ('a, 'b, 'c) suKLabel
  and ('a, 'b, 'c) suKl = ItemKl of ('a, 'b, 'c) suBigKWithLabel |
    IdKl of 'c metaVar
  and ('a, 'b, 'c) suKLabel = SUKLabel of 'a label | SUIdKLabel of 'c metaVar |
    SUKLabelFun of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suKItem =
    SUKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list |
    SUIdKItem of 'c metaVar * 'a sort list | SUHOLE of 'a sort list
  and ('a, 'b, 'c) suKFactor = ItemFactor of ('a, 'b, 'c) suKItem |
    IdFactor of 'c metaVar |
    SUKKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list
  and ('a, 'b, 'c) suL = ItemL of ('a, 'b, 'c) suKFactor list |
    IdL of 'c metaVar |
    SUListKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suM =
    ItemM of ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKFactor list |
    IdM of 'c metaVar |
    SUMapKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  and ('a, 'b, 'c) suS = ItemS of ('a, 'b, 'c) suKFactor list |
    IdS of 'c metaVar |
    SUSetKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
  type 'a symbol = NonTerminal of 'a sort | Terminal of char list
  type 'a nelist = Single of 'a | Con of 'a * 'a nelist
  type reg = Eps | Sym of char | Alt of reg * reg | TheSeq of reg * reg |
    Rep of reg
  type synAttrib = Strict of nat list | Seqstrict | Left | Right |
    Hook of char list | Function | Klabel of char list | Bracket | Tokena |
    Avoid | OnlyLabel | NotInRules | Regex of reg | NonAssoc |
    OtherSynAttr of char list
  type 'a kSyntax = Syntax of 'a sort * 'a symbol nelist * synAttrib list |
    Subsort of 'a sort * 'a sort | Token of 'a sort * reg * synAttrib list |
    ListSyntax of 'a sort * 'a sort * char list * synAttrib list
  type ('a, 'b, 'c) subsFactor = KLabelSubs of ('a, 'b, 'c) suKLabel |
    KItemSubs of ('a, 'b, 'c) suKItem | KListSubs of ('a, 'b, 'c) suKl list |
    KSubs of ('a, 'b, 'c) suKFactor list | ListSubs of ('a, 'b, 'c) suL list |
    SetSubs of ('a, 'b, 'c) suS list | MapSubs of ('a, 'b, 'c) suM list |
    BagSubs of ('a, 'b, 'c) suB list
  type ('a, 'b, 'c) rulePat =
    FunPat of
      'a label *
        (('a, 'b, 'c) pat *
          (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) list *
        (('a, 'b, 'c) pat *
          (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) option
    | MacroPat of 'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list
    | AnywherePat of
        'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list *
          ('a, 'b, 'c) suKItem
    | KRulePat of
        ('a, 'b, 'c) irK * ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKItem *
          bool
    | BagRulePat of
        ('a, 'b, 'c) irBag * ('a, 'b, 'c) suB list * ('a, 'b, 'c) suKItem * bool
  type ('a, 'b) ruleAttrib = Attr of 'a | Heat | Cool | Transition | Anywhere |
    Structural | Owise | Macro | Result of 'b sort
  type ('a, 'b, 'c) kRule
  type ('a, 'b, 'c, 'd) kModuleItem = TheSyntax of 'a kSyntax | Imports of 'c |
    TheConfiguration of ('a, 'b, 'd) bag | TheRule of ('a, 'b, 'd) kRule
  type 'a seq
  type 'a pred
  type ('a, 'b, 'c, 'd) kFile
  type 'a state = Continue of 'a | Stop of 'a | Div of 'a
  type atoken = AChar of char | LBr | RBr | To | TheStar | Plus | OneOrMore
  type ('a, 'b) oneStep = Success of 'a | Failure of 'b
  type ruleLabel = FunTrans | AnywhereTrans | NormalTrans
  type 'a kItemSyntax = SingleTon of 'a | SetTon of ('a -> bool)
  type ruleInString = ARule of char list | AContext of char list |
    AConfi of char list
  type 'a theoryParsed =
    Parsed of ('a sort * ('a kSyntax list) list) list * ruleInString list
  val subsort : 'a equal -> 'a -> 'a -> ('a * 'a list) list -> bool
  val getValueTerm : 'a equal -> 'a -> ('a * 'b) list -> 'b option
  val symbolsToKLabel : 'a symbol nelist -> 'b label
  val getKLabelName : synAttrib list -> 'a label option
  val syntaxToKItem :
    'a kSyntax ->
      (('a sort list *
         (('a sort list) list *
           ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val syntaxSetToKItemTest :
    'a equal ->
      ('a, 'b, 'c, 'd) kFile ->
        (('a sort list *
           (('a sort list) list *
             ('a label kItemSyntax * (synAttrib list * bool)))) list) option
  val formGraph : 'a equal -> 'a list -> ('a * 'a) list -> ('a * 'a list) list
  val krun :
    'a equal -> 'b equal -> 'c equal -> 'd equal ->
      ('a, 'b, 'c, 'd) kFile ->
        nat ->
          ('d metaVar * ('a, 'b, 'd) subsFactor) list ->
            ((('a, 'b, 'd) suB list), (char list)) oneStep -> bool
  val inc : num -> num
  val ksearch :
    'a equal -> 'b equal -> 'c equal -> 'd equal ->
      ('a, 'b, 'c, 'd) kFile ->
        nat ->
          ('d metaVar * ('a, 'b, 'd) subsFactor) list ->
            (((('a, 'b, 'd) suB list) list), (char list)) oneStep -> bool
  val getNonTerminalInList : 'a symbol nelist -> 'a sort list
end = struct

type num = One | Bit0 of num | Bit1 of num;;

let rec equal_num x0 x1 = match x0, x1 with Bit0 x2, Bit1 x3 -> false
                    | Bit1 x3, Bit0 x2 -> false
                    | One, Bit1 x3 -> false
                    | Bit1 x3, One -> false
                    | One, Bit0 x2 -> false
                    | Bit0 x2, One -> false
                    | Bit1 x3, Bit1 y3 -> equal_num x3 y3
                    | Bit0 x2, Bit0 y2 -> equal_num x2 y2
                    | One, One -> true;;

type int = Zero_int | Pos of num | Neg of num;;

let rec equal_inta x0 x1 = match x0, x1 with Neg k, Neg l -> equal_num k l
                     | Neg k, Pos l -> false
                     | Neg k, Zero_int -> false
                     | Pos k, Neg l -> false
                     | Pos k, Pos l -> equal_num k l
                     | Pos k, Zero_int -> false
                     | Zero_int, Neg l -> false
                     | Zero_int, Pos l -> false
                     | Zero_int, Zero_int -> true;;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_int = ({equal = equal_inta} : int equal);;

type nat = Zero_nat | Suc of nat;;

let rec equal_nata x0 x1 = match x0, x1 with Zero_nat, Suc x2 -> false
                     | Suc x2, Zero_nat -> false
                     | Suc x2, Suc y2 -> equal_nata x2 y2
                     | Zero_nat, Zero_nat -> true;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let one_nata : nat = Suc Zero_nat;;

type 'a one = {one : 'a};;
let one _A = _A.one;;

let one_nat = ({one = one_nata} : nat one);;

let rec plus_nata x0 n = match x0, n with Suc m, n -> plus_nata m (Suc n)
                    | Zero_nat, n -> n;;

type 'a plus = {plus : 'a -> 'a -> 'a};;
let plus _A = _A.plus;;

let plus_nat = ({plus = plus_nata} : nat plus);;

type 'a zero = {zero : 'a};;
let zero _A = _A.zero;;

let zero_nat = ({zero = Zero_nat} : nat zero);;

let rec less_eq_nat x0 n = match x0, n with Suc m, n -> less_nat m n
                      | Zero_nat, n -> true
and less_nat m x1 = match m, x1 with m, Suc n -> less_eq_nat m n
               | n, Zero_nat -> false;;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let ord_nat = ({less_eq = less_eq_nat; less = less_nat} : nat ord);;

let rec eq _A a b = equal _A a b;;

let rec equal_lista _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_lista _A x22 y22
    | [], [] -> true;;

let rec equal_list _A = ({equal = equal_lista _A} : ('a list) equal);;

type 'a rewrite = KTerm of 'a | KRewrite of 'a * 'a;;

let rec equal_rewrite _A
  x0 x1 = match x0, x1 with KTerm x1, KRewrite (x21, x22) -> false
    | KRewrite (x21, x22), KTerm x1 -> false
    | KRewrite (x21, x22), KRewrite (y21, y22) -> eq _A x21 y21 && eq _A x22 y22
    | KTerm x1, KTerm y1 -> eq _A x1 y1;;

type 'a metaVar = Defined of 'a | Generated of nat | FunHole;;

let rec equal_metaVara _A
  x0 x1 = match x0, x1 with Generated x2, FunHole -> false
    | FunHole, Generated x2 -> false
    | Defined x1, FunHole -> false
    | FunHole, Defined x1 -> false
    | Defined x1, Generated x2 -> false
    | Generated x2, Defined x1 -> false
    | Generated x2, Generated y2 -> equal_nata x2 y2
    | Defined x1, Defined y1 -> eq _A x1 y1
    | FunHole, FunHole -> true;;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

type nibble = Nibble0 | Nibble1 | Nibble2 | Nibble3 | Nibble4 | Nibble5 |
  Nibble6 | Nibble7 | Nibble8 | Nibble9 | NibbleA | NibbleB | NibbleC | NibbleD
  | NibbleE | NibbleF;;

type char = Char of nibble * nibble;;

type rat = Frct of (int * int);;

type real = Ratreal of rat;;

type theConstant = IntConst of int | FloatConst of real |
  StringConst of char list | BoolConst of bool | IdConst of char list;;

let rec equal_proda _A _B (x1, x2) (y1, y2) = eq _A x1 y1 && eq _B x2 y2;;

let rec quotient_of (Frct x) = x;;

let rec equal_rat
  a b = equal_proda equal_int equal_int (quotient_of a) (quotient_of b);;

let rec equal_real (Ratreal x) (Ratreal y) = equal_rat x y;;

let rec equal_nibble x0 x1 = match x0, x1 with NibbleE, NibbleF -> false
                       | NibbleF, NibbleE -> false
                       | NibbleD, NibbleF -> false
                       | NibbleF, NibbleD -> false
                       | NibbleD, NibbleE -> false
                       | NibbleE, NibbleD -> false
                       | NibbleC, NibbleF -> false
                       | NibbleF, NibbleC -> false
                       | NibbleC, NibbleE -> false
                       | NibbleE, NibbleC -> false
                       | NibbleC, NibbleD -> false
                       | NibbleD, NibbleC -> false
                       | NibbleB, NibbleF -> false
                       | NibbleF, NibbleB -> false
                       | NibbleB, NibbleE -> false
                       | NibbleE, NibbleB -> false
                       | NibbleB, NibbleD -> false
                       | NibbleD, NibbleB -> false
                       | NibbleB, NibbleC -> false
                       | NibbleC, NibbleB -> false
                       | NibbleA, NibbleF -> false
                       | NibbleF, NibbleA -> false
                       | NibbleA, NibbleE -> false
                       | NibbleE, NibbleA -> false
                       | NibbleA, NibbleD -> false
                       | NibbleD, NibbleA -> false
                       | NibbleA, NibbleC -> false
                       | NibbleC, NibbleA -> false
                       | NibbleA, NibbleB -> false
                       | NibbleB, NibbleA -> false
                       | Nibble9, NibbleF -> false
                       | NibbleF, Nibble9 -> false
                       | Nibble9, NibbleE -> false
                       | NibbleE, Nibble9 -> false
                       | Nibble9, NibbleD -> false
                       | NibbleD, Nibble9 -> false
                       | Nibble9, NibbleC -> false
                       | NibbleC, Nibble9 -> false
                       | Nibble9, NibbleB -> false
                       | NibbleB, Nibble9 -> false
                       | Nibble9, NibbleA -> false
                       | NibbleA, Nibble9 -> false
                       | Nibble8, NibbleF -> false
                       | NibbleF, Nibble8 -> false
                       | Nibble8, NibbleE -> false
                       | NibbleE, Nibble8 -> false
                       | Nibble8, NibbleD -> false
                       | NibbleD, Nibble8 -> false
                       | Nibble8, NibbleC -> false
                       | NibbleC, Nibble8 -> false
                       | Nibble8, NibbleB -> false
                       | NibbleB, Nibble8 -> false
                       | Nibble8, NibbleA -> false
                       | NibbleA, Nibble8 -> false
                       | Nibble8, Nibble9 -> false
                       | Nibble9, Nibble8 -> false
                       | Nibble7, NibbleF -> false
                       | NibbleF, Nibble7 -> false
                       | Nibble7, NibbleE -> false
                       | NibbleE, Nibble7 -> false
                       | Nibble7, NibbleD -> false
                       | NibbleD, Nibble7 -> false
                       | Nibble7, NibbleC -> false
                       | NibbleC, Nibble7 -> false
                       | Nibble7, NibbleB -> false
                       | NibbleB, Nibble7 -> false
                       | Nibble7, NibbleA -> false
                       | NibbleA, Nibble7 -> false
                       | Nibble7, Nibble9 -> false
                       | Nibble9, Nibble7 -> false
                       | Nibble7, Nibble8 -> false
                       | Nibble8, Nibble7 -> false
                       | Nibble6, NibbleF -> false
                       | NibbleF, Nibble6 -> false
                       | Nibble6, NibbleE -> false
                       | NibbleE, Nibble6 -> false
                       | Nibble6, NibbleD -> false
                       | NibbleD, Nibble6 -> false
                       | Nibble6, NibbleC -> false
                       | NibbleC, Nibble6 -> false
                       | Nibble6, NibbleB -> false
                       | NibbleB, Nibble6 -> false
                       | Nibble6, NibbleA -> false
                       | NibbleA, Nibble6 -> false
                       | Nibble6, Nibble9 -> false
                       | Nibble9, Nibble6 -> false
                       | Nibble6, Nibble8 -> false
                       | Nibble8, Nibble6 -> false
                       | Nibble6, Nibble7 -> false
                       | Nibble7, Nibble6 -> false
                       | Nibble5, NibbleF -> false
                       | NibbleF, Nibble5 -> false
                       | Nibble5, NibbleE -> false
                       | NibbleE, Nibble5 -> false
                       | Nibble5, NibbleD -> false
                       | NibbleD, Nibble5 -> false
                       | Nibble5, NibbleC -> false
                       | NibbleC, Nibble5 -> false
                       | Nibble5, NibbleB -> false
                       | NibbleB, Nibble5 -> false
                       | Nibble5, NibbleA -> false
                       | NibbleA, Nibble5 -> false
                       | Nibble5, Nibble9 -> false
                       | Nibble9, Nibble5 -> false
                       | Nibble5, Nibble8 -> false
                       | Nibble8, Nibble5 -> false
                       | Nibble5, Nibble7 -> false
                       | Nibble7, Nibble5 -> false
                       | Nibble5, Nibble6 -> false
                       | Nibble6, Nibble5 -> false
                       | Nibble4, NibbleF -> false
                       | NibbleF, Nibble4 -> false
                       | Nibble4, NibbleE -> false
                       | NibbleE, Nibble4 -> false
                       | Nibble4, NibbleD -> false
                       | NibbleD, Nibble4 -> false
                       | Nibble4, NibbleC -> false
                       | NibbleC, Nibble4 -> false
                       | Nibble4, NibbleB -> false
                       | NibbleB, Nibble4 -> false
                       | Nibble4, NibbleA -> false
                       | NibbleA, Nibble4 -> false
                       | Nibble4, Nibble9 -> false
                       | Nibble9, Nibble4 -> false
                       | Nibble4, Nibble8 -> false
                       | Nibble8, Nibble4 -> false
                       | Nibble4, Nibble7 -> false
                       | Nibble7, Nibble4 -> false
                       | Nibble4, Nibble6 -> false
                       | Nibble6, Nibble4 -> false
                       | Nibble4, Nibble5 -> false
                       | Nibble5, Nibble4 -> false
                       | Nibble3, NibbleF -> false
                       | NibbleF, Nibble3 -> false
                       | Nibble3, NibbleE -> false
                       | NibbleE, Nibble3 -> false
                       | Nibble3, NibbleD -> false
                       | NibbleD, Nibble3 -> false
                       | Nibble3, NibbleC -> false
                       | NibbleC, Nibble3 -> false
                       | Nibble3, NibbleB -> false
                       | NibbleB, Nibble3 -> false
                       | Nibble3, NibbleA -> false
                       | NibbleA, Nibble3 -> false
                       | Nibble3, Nibble9 -> false
                       | Nibble9, Nibble3 -> false
                       | Nibble3, Nibble8 -> false
                       | Nibble8, Nibble3 -> false
                       | Nibble3, Nibble7 -> false
                       | Nibble7, Nibble3 -> false
                       | Nibble3, Nibble6 -> false
                       | Nibble6, Nibble3 -> false
                       | Nibble3, Nibble5 -> false
                       | Nibble5, Nibble3 -> false
                       | Nibble3, Nibble4 -> false
                       | Nibble4, Nibble3 -> false
                       | Nibble2, NibbleF -> false
                       | NibbleF, Nibble2 -> false
                       | Nibble2, NibbleE -> false
                       | NibbleE, Nibble2 -> false
                       | Nibble2, NibbleD -> false
                       | NibbleD, Nibble2 -> false
                       | Nibble2, NibbleC -> false
                       | NibbleC, Nibble2 -> false
                       | Nibble2, NibbleB -> false
                       | NibbleB, Nibble2 -> false
                       | Nibble2, NibbleA -> false
                       | NibbleA, Nibble2 -> false
                       | Nibble2, Nibble9 -> false
                       | Nibble9, Nibble2 -> false
                       | Nibble2, Nibble8 -> false
                       | Nibble8, Nibble2 -> false
                       | Nibble2, Nibble7 -> false
                       | Nibble7, Nibble2 -> false
                       | Nibble2, Nibble6 -> false
                       | Nibble6, Nibble2 -> false
                       | Nibble2, Nibble5 -> false
                       | Nibble5, Nibble2 -> false
                       | Nibble2, Nibble4 -> false
                       | Nibble4, Nibble2 -> false
                       | Nibble2, Nibble3 -> false
                       | Nibble3, Nibble2 -> false
                       | Nibble1, NibbleF -> false
                       | NibbleF, Nibble1 -> false
                       | Nibble1, NibbleE -> false
                       | NibbleE, Nibble1 -> false
                       | Nibble1, NibbleD -> false
                       | NibbleD, Nibble1 -> false
                       | Nibble1, NibbleC -> false
                       | NibbleC, Nibble1 -> false
                       | Nibble1, NibbleB -> false
                       | NibbleB, Nibble1 -> false
                       | Nibble1, NibbleA -> false
                       | NibbleA, Nibble1 -> false
                       | Nibble1, Nibble9 -> false
                       | Nibble9, Nibble1 -> false
                       | Nibble1, Nibble8 -> false
                       | Nibble8, Nibble1 -> false
                       | Nibble1, Nibble7 -> false
                       | Nibble7, Nibble1 -> false
                       | Nibble1, Nibble6 -> false
                       | Nibble6, Nibble1 -> false
                       | Nibble1, Nibble5 -> false
                       | Nibble5, Nibble1 -> false
                       | Nibble1, Nibble4 -> false
                       | Nibble4, Nibble1 -> false
                       | Nibble1, Nibble3 -> false
                       | Nibble3, Nibble1 -> false
                       | Nibble1, Nibble2 -> false
                       | Nibble2, Nibble1 -> false
                       | Nibble0, NibbleF -> false
                       | NibbleF, Nibble0 -> false
                       | Nibble0, NibbleE -> false
                       | NibbleE, Nibble0 -> false
                       | Nibble0, NibbleD -> false
                       | NibbleD, Nibble0 -> false
                       | Nibble0, NibbleC -> false
                       | NibbleC, Nibble0 -> false
                       | Nibble0, NibbleB -> false
                       | NibbleB, Nibble0 -> false
                       | Nibble0, NibbleA -> false
                       | NibbleA, Nibble0 -> false
                       | Nibble0, Nibble9 -> false
                       | Nibble9, Nibble0 -> false
                       | Nibble0, Nibble8 -> false
                       | Nibble8, Nibble0 -> false
                       | Nibble0, Nibble7 -> false
                       | Nibble7, Nibble0 -> false
                       | Nibble0, Nibble6 -> false
                       | Nibble6, Nibble0 -> false
                       | Nibble0, Nibble5 -> false
                       | Nibble5, Nibble0 -> false
                       | Nibble0, Nibble4 -> false
                       | Nibble4, Nibble0 -> false
                       | Nibble0, Nibble3 -> false
                       | Nibble3, Nibble0 -> false
                       | Nibble0, Nibble2 -> false
                       | Nibble2, Nibble0 -> false
                       | Nibble0, Nibble1 -> false
                       | Nibble1, Nibble0 -> false
                       | NibbleF, NibbleF -> true
                       | NibbleE, NibbleE -> true
                       | NibbleD, NibbleD -> true
                       | NibbleC, NibbleC -> true
                       | NibbleB, NibbleB -> true
                       | NibbleA, NibbleA -> true
                       | Nibble9, Nibble9 -> true
                       | Nibble8, Nibble8 -> true
                       | Nibble7, Nibble7 -> true
                       | Nibble6, Nibble6 -> true
                       | Nibble5, Nibble5 -> true
                       | Nibble4, Nibble4 -> true
                       | Nibble3, Nibble3 -> true
                       | Nibble2, Nibble2 -> true
                       | Nibble1, Nibble1 -> true
                       | Nibble0, Nibble0 -> true;;

let rec equal_chara
  (Char (x1, x2)) (Char (y1, y2)) = equal_nibble x1 y1 && equal_nibble x2 y2;;

let equal_char = ({equal = equal_chara} : char equal);;

let rec equal_theConstant
  x0 x1 = match x0, x1 with BoolConst x4, IdConst x5 -> false
    | IdConst x5, BoolConst x4 -> false
    | StringConst x3, IdConst x5 -> false
    | IdConst x5, StringConst x3 -> false
    | StringConst x3, BoolConst x4 -> false
    | BoolConst x4, StringConst x3 -> false
    | FloatConst x2, IdConst x5 -> false
    | IdConst x5, FloatConst x2 -> false
    | FloatConst x2, BoolConst x4 -> false
    | BoolConst x4, FloatConst x2 -> false
    | FloatConst x2, StringConst x3 -> false
    | StringConst x3, FloatConst x2 -> false
    | IntConst x1, IdConst x5 -> false
    | IdConst x5, IntConst x1 -> false
    | IntConst x1, BoolConst x4 -> false
    | BoolConst x4, IntConst x1 -> false
    | IntConst x1, StringConst x3 -> false
    | StringConst x3, IntConst x1 -> false
    | IntConst x1, FloatConst x2 -> false
    | FloatConst x2, IntConst x1 -> false
    | IdConst x5, IdConst y5 -> equal_lista equal_char x5 y5
    | BoolConst x4, BoolConst y4 -> equal_bool x4 y4
    | StringConst x3, StringConst y3 -> equal_lista equal_char x3 y3
    | FloatConst x2, FloatConst y2 -> equal_real x2 y2
    | IntConst x1, IntConst y1 -> equal_inta x1 y1;;

type 'a sort = Bool | K | KItem | KLabel | KResult | KList | List | Seta | Map |
  Bag | OtherSort of 'a | Top | Int | Float | Id | String;;

let rec equal_sorta _A x0 x1 = match x0, x1 with Id, String -> false
                         | String, Id -> false
                         | Float, String -> false
                         | String, Float -> false
                         | Float, Id -> false
                         | Id, Float -> false
                         | Int, String -> false
                         | String, Int -> false
                         | Int, Id -> false
                         | Id, Int -> false
                         | Int, Float -> false
                         | Float, Int -> false
                         | Top, String -> false
                         | String, Top -> false
                         | Top, Id -> false
                         | Id, Top -> false
                         | Top, Float -> false
                         | Float, Top -> false
                         | Top, Int -> false
                         | Int, Top -> false
                         | OtherSort x11, String -> false
                         | String, OtherSort x11 -> false
                         | OtherSort x11, Id -> false
                         | Id, OtherSort x11 -> false
                         | OtherSort x11, Float -> false
                         | Float, OtherSort x11 -> false
                         | OtherSort x11, Int -> false
                         | Int, OtherSort x11 -> false
                         | OtherSort x11, Top -> false
                         | Top, OtherSort x11 -> false
                         | Bag, String -> false
                         | String, Bag -> false
                         | Bag, Id -> false
                         | Id, Bag -> false
                         | Bag, Float -> false
                         | Float, Bag -> false
                         | Bag, Int -> false
                         | Int, Bag -> false
                         | Bag, Top -> false
                         | Top, Bag -> false
                         | Bag, OtherSort x11 -> false
                         | OtherSort x11, Bag -> false
                         | Map, String -> false
                         | String, Map -> false
                         | Map, Id -> false
                         | Id, Map -> false
                         | Map, Float -> false
                         | Float, Map -> false
                         | Map, Int -> false
                         | Int, Map -> false
                         | Map, Top -> false
                         | Top, Map -> false
                         | Map, OtherSort x11 -> false
                         | OtherSort x11, Map -> false
                         | Map, Bag -> false
                         | Bag, Map -> false
                         | Seta, String -> false
                         | String, Seta -> false
                         | Seta, Id -> false
                         | Id, Seta -> false
                         | Seta, Float -> false
                         | Float, Seta -> false
                         | Seta, Int -> false
                         | Int, Seta -> false
                         | Seta, Top -> false
                         | Top, Seta -> false
                         | Seta, OtherSort x11 -> false
                         | OtherSort x11, Seta -> false
                         | Seta, Bag -> false
                         | Bag, Seta -> false
                         | Seta, Map -> false
                         | Map, Seta -> false
                         | List, String -> false
                         | String, List -> false
                         | List, Id -> false
                         | Id, List -> false
                         | List, Float -> false
                         | Float, List -> false
                         | List, Int -> false
                         | Int, List -> false
                         | List, Top -> false
                         | Top, List -> false
                         | List, OtherSort x11 -> false
                         | OtherSort x11, List -> false
                         | List, Bag -> false
                         | Bag, List -> false
                         | List, Map -> false
                         | Map, List -> false
                         | List, Seta -> false
                         | Seta, List -> false
                         | KList, String -> false
                         | String, KList -> false
                         | KList, Id -> false
                         | Id, KList -> false
                         | KList, Float -> false
                         | Float, KList -> false
                         | KList, Int -> false
                         | Int, KList -> false
                         | KList, Top -> false
                         | Top, KList -> false
                         | KList, OtherSort x11 -> false
                         | OtherSort x11, KList -> false
                         | KList, Bag -> false
                         | Bag, KList -> false
                         | KList, Map -> false
                         | Map, KList -> false
                         | KList, Seta -> false
                         | Seta, KList -> false
                         | KList, List -> false
                         | List, KList -> false
                         | KResult, String -> false
                         | String, KResult -> false
                         | KResult, Id -> false
                         | Id, KResult -> false
                         | KResult, Float -> false
                         | Float, KResult -> false
                         | KResult, Int -> false
                         | Int, KResult -> false
                         | KResult, Top -> false
                         | Top, KResult -> false
                         | KResult, OtherSort x11 -> false
                         | OtherSort x11, KResult -> false
                         | KResult, Bag -> false
                         | Bag, KResult -> false
                         | KResult, Map -> false
                         | Map, KResult -> false
                         | KResult, Seta -> false
                         | Seta, KResult -> false
                         | KResult, List -> false
                         | List, KResult -> false
                         | KResult, KList -> false
                         | KList, KResult -> false
                         | KLabel, String -> false
                         | String, KLabel -> false
                         | KLabel, Id -> false
                         | Id, KLabel -> false
                         | KLabel, Float -> false
                         | Float, KLabel -> false
                         | KLabel, Int -> false
                         | Int, KLabel -> false
                         | KLabel, Top -> false
                         | Top, KLabel -> false
                         | KLabel, OtherSort x11 -> false
                         | OtherSort x11, KLabel -> false
                         | KLabel, Bag -> false
                         | Bag, KLabel -> false
                         | KLabel, Map -> false
                         | Map, KLabel -> false
                         | KLabel, Seta -> false
                         | Seta, KLabel -> false
                         | KLabel, List -> false
                         | List, KLabel -> false
                         | KLabel, KList -> false
                         | KList, KLabel -> false
                         | KLabel, KResult -> false
                         | KResult, KLabel -> false
                         | KItem, String -> false
                         | String, KItem -> false
                         | KItem, Id -> false
                         | Id, KItem -> false
                         | KItem, Float -> false
                         | Float, KItem -> false
                         | KItem, Int -> false
                         | Int, KItem -> false
                         | KItem, Top -> false
                         | Top, KItem -> false
                         | KItem, OtherSort x11 -> false
                         | OtherSort x11, KItem -> false
                         | KItem, Bag -> false
                         | Bag, KItem -> false
                         | KItem, Map -> false
                         | Map, KItem -> false
                         | KItem, Seta -> false
                         | Seta, KItem -> false
                         | KItem, List -> false
                         | List, KItem -> false
                         | KItem, KList -> false
                         | KList, KItem -> false
                         | KItem, KResult -> false
                         | KResult, KItem -> false
                         | KItem, KLabel -> false
                         | KLabel, KItem -> false
                         | K, String -> false
                         | String, K -> false
                         | K, Id -> false
                         | Id, K -> false
                         | K, Float -> false
                         | Float, K -> false
                         | K, Int -> false
                         | Int, K -> false
                         | K, Top -> false
                         | Top, K -> false
                         | K, OtherSort x11 -> false
                         | OtherSort x11, K -> false
                         | K, Bag -> false
                         | Bag, K -> false
                         | K, Map -> false
                         | Map, K -> false
                         | K, Seta -> false
                         | Seta, K -> false
                         | K, List -> false
                         | List, K -> false
                         | K, KList -> false
                         | KList, K -> false
                         | K, KResult -> false
                         | KResult, K -> false
                         | K, KLabel -> false
                         | KLabel, K -> false
                         | K, KItem -> false
                         | KItem, K -> false
                         | Bool, String -> false
                         | String, Bool -> false
                         | Bool, Id -> false
                         | Id, Bool -> false
                         | Bool, Float -> false
                         | Float, Bool -> false
                         | Bool, Int -> false
                         | Int, Bool -> false
                         | Bool, Top -> false
                         | Top, Bool -> false
                         | Bool, OtherSort x11 -> false
                         | OtherSort x11, Bool -> false
                         | Bool, Bag -> false
                         | Bag, Bool -> false
                         | Bool, Map -> false
                         | Map, Bool -> false
                         | Bool, Seta -> false
                         | Seta, Bool -> false
                         | Bool, List -> false
                         | List, Bool -> false
                         | Bool, KList -> false
                         | KList, Bool -> false
                         | Bool, KResult -> false
                         | KResult, Bool -> false
                         | Bool, KLabel -> false
                         | KLabel, Bool -> false
                         | Bool, KItem -> false
                         | KItem, Bool -> false
                         | Bool, K -> false
                         | K, Bool -> false
                         | OtherSort x11, OtherSort y11 -> eq _A x11 y11
                         | String, String -> true
                         | Id, Id -> true
                         | Float, Float -> true
                         | Int, Int -> true
                         | Top, Top -> true
                         | Bag, Bag -> true
                         | Map, Map -> true
                         | Seta, Seta -> true
                         | List, List -> true
                         | KList, KList -> true
                         | KResult, KResult -> true
                         | KLabel, KLabel -> true
                         | KItem, KItem -> true
                         | K, K -> true
                         | Bool, Bool -> true;;

type 'a label = UnitLabel of 'a sort | ConstToLabel of theConstant | Sort |
  GetKLabel | IsKResult | AndBool | NotBool | OtherLabel of char list |
  TokenLabel of char list;;

let rec equal_labela _A
  x0 x1 = match x0, x1 with OtherLabel x8, TokenLabel x9 -> false
    | TokenLabel x9, OtherLabel x8 -> false
    | NotBool, TokenLabel x9 -> false
    | TokenLabel x9, NotBool -> false
    | NotBool, OtherLabel x8 -> false
    | OtherLabel x8, NotBool -> false
    | AndBool, TokenLabel x9 -> false
    | TokenLabel x9, AndBool -> false
    | AndBool, OtherLabel x8 -> false
    | OtherLabel x8, AndBool -> false
    | AndBool, NotBool -> false
    | NotBool, AndBool -> false
    | IsKResult, TokenLabel x9 -> false
    | TokenLabel x9, IsKResult -> false
    | IsKResult, OtherLabel x8 -> false
    | OtherLabel x8, IsKResult -> false
    | IsKResult, NotBool -> false
    | NotBool, IsKResult -> false
    | IsKResult, AndBool -> false
    | AndBool, IsKResult -> false
    | GetKLabel, TokenLabel x9 -> false
    | TokenLabel x9, GetKLabel -> false
    | GetKLabel, OtherLabel x8 -> false
    | OtherLabel x8, GetKLabel -> false
    | GetKLabel, NotBool -> false
    | NotBool, GetKLabel -> false
    | GetKLabel, AndBool -> false
    | AndBool, GetKLabel -> false
    | GetKLabel, IsKResult -> false
    | IsKResult, GetKLabel -> false
    | Sort, TokenLabel x9 -> false
    | TokenLabel x9, Sort -> false
    | Sort, OtherLabel x8 -> false
    | OtherLabel x8, Sort -> false
    | Sort, NotBool -> false
    | NotBool, Sort -> false
    | Sort, AndBool -> false
    | AndBool, Sort -> false
    | Sort, IsKResult -> false
    | IsKResult, Sort -> false
    | Sort, GetKLabel -> false
    | GetKLabel, Sort -> false
    | ConstToLabel x2, TokenLabel x9 -> false
    | TokenLabel x9, ConstToLabel x2 -> false
    | ConstToLabel x2, OtherLabel x8 -> false
    | OtherLabel x8, ConstToLabel x2 -> false
    | ConstToLabel x2, NotBool -> false
    | NotBool, ConstToLabel x2 -> false
    | ConstToLabel x2, AndBool -> false
    | AndBool, ConstToLabel x2 -> false
    | ConstToLabel x2, IsKResult -> false
    | IsKResult, ConstToLabel x2 -> false
    | ConstToLabel x2, GetKLabel -> false
    | GetKLabel, ConstToLabel x2 -> false
    | ConstToLabel x2, Sort -> false
    | Sort, ConstToLabel x2 -> false
    | UnitLabel x1, TokenLabel x9 -> false
    | TokenLabel x9, UnitLabel x1 -> false
    | UnitLabel x1, OtherLabel x8 -> false
    | OtherLabel x8, UnitLabel x1 -> false
    | UnitLabel x1, NotBool -> false
    | NotBool, UnitLabel x1 -> false
    | UnitLabel x1, AndBool -> false
    | AndBool, UnitLabel x1 -> false
    | UnitLabel x1, IsKResult -> false
    | IsKResult, UnitLabel x1 -> false
    | UnitLabel x1, GetKLabel -> false
    | GetKLabel, UnitLabel x1 -> false
    | UnitLabel x1, Sort -> false
    | Sort, UnitLabel x1 -> false
    | UnitLabel x1, ConstToLabel x2 -> false
    | ConstToLabel x2, UnitLabel x1 -> false
    | TokenLabel x9, TokenLabel y9 -> equal_lista equal_char x9 y9
    | OtherLabel x8, OtherLabel y8 -> equal_lista equal_char x8 y8
    | ConstToLabel x2, ConstToLabel y2 -> equal_theConstant x2 y2
    | UnitLabel x1, UnitLabel y1 -> equal_sorta _A x1 y1
    | NotBool, NotBool -> true
    | AndBool, AndBool -> true
    | IsKResult, IsKResult -> true
    | GetKLabel, GetKLabel -> true
    | Sort, Sort -> true;;

type stdType = Stdin | Stdout;;

type key = Star | Question;;

type feature = Multiplicity of key | Stream of stdType | DotDotDot;;

type 'a var = LittleK | OtherVar of 'a;;

type ('a, 'b, 'c) kLabel = KLabelC of 'a label |
  KLabelFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite |
  IdKLabel of 'c metaVar
and ('a, 'b, 'c) bigKWithBag = TheBigK of ('a, 'b, 'c) bigK |
  TheBigBag of ('a, 'b, 'c) bag rewrite |
  TheLabel of ('a, 'b, 'c) kLabel rewrite
and ('a, 'b, 'c) kList =
  KListCon of ('a, 'b, 'c) kList rewrite * ('a, 'b, 'c) kList rewrite |
  UnitKList | KListItem of ('a, 'b, 'c) bigKWithBag | IdKList of 'c metaVar
and ('a, 'b, 'c) kItem =
  KItemC of ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kList rewrite * 'a sort |
  Constant of theConstant * 'a sort | IdKItem of 'c metaVar * 'a sort |
  HOLE of 'a sort
and ('a, 'b, 'c) k = Tilda of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
  UnitK | IdK of 'c metaVar | SingleK of ('a, 'b, 'c) kItem rewrite |
  KFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) theMap =
  MapCon of ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) theMap rewrite | UnitMap
  | IdMap of 'c metaVar |
  MapItem of ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) k rewrite |
  MapFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) theSet =
  SetCon of ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) theSet rewrite | UnitSet
  | IdSet of 'c metaVar | SetItem of ('a, 'b, 'c) k rewrite |
  SetFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) theList =
  ListCon of ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) theList rewrite |
  UnitList | IdList of 'c metaVar | ListItem of ('a, 'b, 'c) k rewrite |
  ListFun of ('a, 'b, 'c) kLabel * ('a, 'b, 'c) kList rewrite
and ('a, 'b, 'c) bigK = TheK of ('a, 'b, 'c) k rewrite |
  TheList of ('a, 'b, 'c) theList rewrite |
  TheSet of ('a, 'b, 'c) theSet rewrite | TheMap of ('a, 'b, 'c) theMap rewrite
and ('a, 'b, 'c) bag =
  BagCon of ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) bag rewrite | UnitBag |
  IdBag of 'c metaVar | Xml of 'b var * feature list * ('a, 'b, 'c) bag rewrite
  | SingleCell of 'b var * feature list * ('a, 'b, 'c) bigK;;

let rec equal_vara _A x0 x1 = match x0, x1 with LittleK, OtherVar x2 -> false
                        | OtherVar x2, LittleK -> false
                        | OtherVar x2, OtherVar y2 -> eq _A x2 y2
                        | LittleK, LittleK -> true;;

let rec equal_stdType x0 x1 = match x0, x1 with Stdin, Stdout -> false
                        | Stdout, Stdin -> false
                        | Stdout, Stdout -> true
                        | Stdin, Stdin -> true;;

let rec equal_key x0 x1 = match x0, x1 with Star, Question -> false
                    | Question, Star -> false
                    | Question, Question -> true
                    | Star, Star -> true;;

let rec equal_featurea x0 x1 = match x0, x1 with Stream x2, DotDotDot -> false
                         | DotDotDot, Stream x2 -> false
                         | Multiplicity x1, DotDotDot -> false
                         | DotDotDot, Multiplicity x1 -> false
                         | Multiplicity x1, Stream x2 -> false
                         | Stream x2, Multiplicity x1 -> false
                         | Stream x2, Stream y2 -> equal_stdType x2 y2
                         | Multiplicity x1, Multiplicity y1 -> equal_key x1 y1
                         | DotDotDot, DotDotDot -> true;;

let equal_feature = ({equal = equal_featurea} : feature equal);;

let rec equal_k _A _B _C = ({equal = equal_ka _A _B _C} : ('a, 'b, 'c) k equal)
and equal_theLista _A _B _C
  x0 x1 = match x0, x1 with ListItem x4, ListFun (x51, x52) -> false
    | ListFun (x51, x52), ListItem x4 -> false
    | IdList x3, ListFun (x51, x52) -> false
    | ListFun (x51, x52), IdList x3 -> false
    | IdList x3, ListItem x4 -> false
    | ListItem x4, IdList x3 -> false
    | UnitList, ListFun (x51, x52) -> false
    | ListFun (x51, x52), UnitList -> false
    | UnitList, ListItem x4 -> false
    | ListItem x4, UnitList -> false
    | UnitList, IdList x3 -> false
    | IdList x3, UnitList -> false
    | ListCon (x11, x12), ListFun (x51, x52) -> false
    | ListFun (x51, x52), ListCon (x11, x12) -> false
    | ListCon (x11, x12), ListItem x4 -> false
    | ListItem x4, ListCon (x11, x12) -> false
    | ListCon (x11, x12), IdList x3 -> false
    | IdList x3, ListCon (x11, x12) -> false
    | ListCon (x11, x12), UnitList -> false
    | UnitList, ListCon (x11, x12) -> false
    | ListFun (x51, x52), ListFun (y51, y52) ->
        equal_kLabela _A _B _C x51 y51 &&
          equal_rewrite (equal_kList _A _B _C) x52 y52
    | ListItem x4, ListItem y4 -> equal_rewrite (equal_k _A _B _C) x4 y4
    | IdList x3, IdList y3 -> equal_metaVara _C x3 y3
    | ListCon (x11, x12), ListCon (y11, y12) ->
        equal_rewrite (equal_theList _A _B _C) x11 y11 &&
          equal_rewrite (equal_theList _A _B _C) x12 y12
    | UnitList, UnitList -> true
and equal_theList _A _B _C =
  ({equal = equal_theLista _A _B _C} : ('a, 'b, 'c) theList equal)
and equal_bigK _A _B _C
  x0 x1 = match x0, x1 with TheSet x3, TheMap x4 -> false
    | TheMap x4, TheSet x3 -> false
    | TheList x2, TheMap x4 -> false
    | TheMap x4, TheList x2 -> false
    | TheList x2, TheSet x3 -> false
    | TheSet x3, TheList x2 -> false
    | TheK x1, TheMap x4 -> false
    | TheMap x4, TheK x1 -> false
    | TheK x1, TheSet x3 -> false
    | TheSet x3, TheK x1 -> false
    | TheK x1, TheList x2 -> false
    | TheList x2, TheK x1 -> false
    | TheMap x4, TheMap y4 -> equal_rewrite (equal_theMap _A _B _C) x4 y4
    | TheSet x3, TheSet y3 -> equal_rewrite (equal_theSet _A _B _C) x3 y3
    | TheList x2, TheList y2 -> equal_rewrite (equal_theList _A _B _C) x2 y2
    | TheK x1, TheK y1 -> equal_rewrite (equal_k _A _B _C) x1 y1
and equal_baga _A _B _C
  x0 x1 = match x0, x1 with
    Xml (x41, x42, x43), SingleCell (x51, x52, x53) -> false
    | SingleCell (x51, x52, x53), Xml (x41, x42, x43) -> false
    | IdBag x3, SingleCell (x51, x52, x53) -> false
    | SingleCell (x51, x52, x53), IdBag x3 -> false
    | IdBag x3, Xml (x41, x42, x43) -> false
    | Xml (x41, x42, x43), IdBag x3 -> false
    | UnitBag, SingleCell (x51, x52, x53) -> false
    | SingleCell (x51, x52, x53), UnitBag -> false
    | UnitBag, Xml (x41, x42, x43) -> false
    | Xml (x41, x42, x43), UnitBag -> false
    | UnitBag, IdBag x3 -> false
    | IdBag x3, UnitBag -> false
    | BagCon (x11, x12), SingleCell (x51, x52, x53) -> false
    | SingleCell (x51, x52, x53), BagCon (x11, x12) -> false
    | BagCon (x11, x12), Xml (x41, x42, x43) -> false
    | Xml (x41, x42, x43), BagCon (x11, x12) -> false
    | BagCon (x11, x12), IdBag x3 -> false
    | IdBag x3, BagCon (x11, x12) -> false
    | BagCon (x11, x12), UnitBag -> false
    | UnitBag, BagCon (x11, x12) -> false
    | SingleCell (x51, x52, x53), SingleCell (y51, y52, y53) ->
        equal_vara _B x51 y51 &&
          (equal_lista equal_feature x52 y52 && equal_bigK _A _B _C x53 y53)
    | Xml (x41, x42, x43), Xml (y41, y42, y43) ->
        equal_vara _B x41 y41 &&
          (equal_lista equal_feature x42 y42 &&
            equal_rewrite (equal_bag _A _B _C) x43 y43)
    | IdBag x3, IdBag y3 -> equal_metaVara _C x3 y3
    | BagCon (x11, x12), BagCon (y11, y12) ->
        equal_rewrite (equal_bag _A _B _C) x11 y11 &&
          equal_rewrite (equal_bag _A _B _C) x12 y12
    | UnitBag, UnitBag -> true
and equal_bag _A _B _C =
  ({equal = equal_baga _A _B _C} : ('a, 'b, 'c) bag equal)
and equal_bigKWithBag _A _B _C
  x0 x1 = match x0, x1 with TheBigBag x2, TheLabel x3 -> false
    | TheLabel x3, TheBigBag x2 -> false
    | TheBigK x1, TheLabel x3 -> false
    | TheLabel x3, TheBigK x1 -> false
    | TheBigK x1, TheBigBag x2 -> false
    | TheBigBag x2, TheBigK x1 -> false
    | TheLabel x3, TheLabel y3 -> equal_rewrite (equal_kLabel _A _B _C) x3 y3
    | TheBigBag x2, TheBigBag y2 -> equal_rewrite (equal_bag _A _B _C) x2 y2
    | TheBigK x1, TheBigK y1 -> equal_bigK _A _B _C x1 y1
and equal_kLista _A _B _C
  x0 x1 = match x0, x1 with KListItem x3, IdKList x4 -> false
    | IdKList x4, KListItem x3 -> false
    | UnitKList, IdKList x4 -> false
    | IdKList x4, UnitKList -> false
    | UnitKList, KListItem x3 -> false
    | KListItem x3, UnitKList -> false
    | KListCon (x11, x12), IdKList x4 -> false
    | IdKList x4, KListCon (x11, x12) -> false
    | KListCon (x11, x12), KListItem x3 -> false
    | KListItem x3, KListCon (x11, x12) -> false
    | KListCon (x11, x12), UnitKList -> false
    | UnitKList, KListCon (x11, x12) -> false
    | IdKList x4, IdKList y4 -> equal_metaVara _C x4 y4
    | KListItem x3, KListItem y3 -> equal_bigKWithBag _A _B _C x3 y3
    | KListCon (x11, x12), KListCon (y11, y12) ->
        equal_rewrite (equal_kList _A _B _C) x11 y11 &&
          equal_rewrite (equal_kList _A _B _C) x12 y12
    | UnitKList, UnitKList -> true
and equal_kList _A _B _C =
  ({equal = equal_kLista _A _B _C} : ('a, 'b, 'c) kList equal)
and equal_kLabela _A _B _C
  x0 x1 = match x0, x1 with KLabelFun (x21, x22), IdKLabel x3 -> false
    | IdKLabel x3, KLabelFun (x21, x22) -> false
    | KLabelC x1, IdKLabel x3 -> false
    | IdKLabel x3, KLabelC x1 -> false
    | KLabelC x1, KLabelFun (x21, x22) -> false
    | KLabelFun (x21, x22), KLabelC x1 -> false
    | IdKLabel x3, IdKLabel y3 -> equal_metaVara _C x3 y3
    | KLabelFun (x21, x22), KLabelFun (y21, y22) ->
        equal_kLabela _A _B _C x21 y21 &&
          equal_rewrite (equal_kList _A _B _C) x22 y22
    | KLabelC x1, KLabelC y1 -> equal_labela _A x1 y1
and equal_kLabel _A _B _C =
  ({equal = equal_kLabela _A _B _C} : ('a, 'b, 'c) kLabel equal)
and equal_kItema _A _B _C
  x0 x1 = match x0, x1 with IdKItem (x31, x32), HOLE x4 -> false
    | HOLE x4, IdKItem (x31, x32) -> false
    | Constant (x21, x22), HOLE x4 -> false
    | HOLE x4, Constant (x21, x22) -> false
    | Constant (x21, x22), IdKItem (x31, x32) -> false
    | IdKItem (x31, x32), Constant (x21, x22) -> false
    | KItemC (x11, x12, x13), HOLE x4 -> false
    | HOLE x4, KItemC (x11, x12, x13) -> false
    | KItemC (x11, x12, x13), IdKItem (x31, x32) -> false
    | IdKItem (x31, x32), KItemC (x11, x12, x13) -> false
    | KItemC (x11, x12, x13), Constant (x21, x22) -> false
    | Constant (x21, x22), KItemC (x11, x12, x13) -> false
    | HOLE x4, HOLE y4 -> equal_sorta _A x4 y4
    | IdKItem (x31, x32), IdKItem (y31, y32) ->
        equal_metaVara _C x31 y31 && equal_sorta _A x32 y32
    | Constant (x21, x22), Constant (y21, y22) ->
        equal_theConstant x21 y21 && equal_sorta _A x22 y22
    | KItemC (x11, x12, x13), KItemC (y11, y12, y13) ->
        equal_rewrite (equal_kLabel _A _B _C) x11 y11 &&
          (equal_rewrite (equal_kList _A _B _C) x12 y12 &&
            equal_sorta _A x13 y13)
and equal_kItem _A _B _C =
  ({equal = equal_kItema _A _B _C} : ('a, 'b, 'c) kItem equal)
and equal_ka _A _B _C
  x0 x1 = match x0, x1 with SingleK x4, KFun (x51, x52) -> false
    | KFun (x51, x52), SingleK x4 -> false
    | IdK x3, KFun (x51, x52) -> false
    | KFun (x51, x52), IdK x3 -> false
    | IdK x3, SingleK x4 -> false
    | SingleK x4, IdK x3 -> false
    | UnitK, KFun (x51, x52) -> false
    | KFun (x51, x52), UnitK -> false
    | UnitK, SingleK x4 -> false
    | SingleK x4, UnitK -> false
    | UnitK, IdK x3 -> false
    | IdK x3, UnitK -> false
    | Tilda (x11, x12), KFun (x51, x52) -> false
    | KFun (x51, x52), Tilda (x11, x12) -> false
    | Tilda (x11, x12), SingleK x4 -> false
    | SingleK x4, Tilda (x11, x12) -> false
    | Tilda (x11, x12), IdK x3 -> false
    | IdK x3, Tilda (x11, x12) -> false
    | Tilda (x11, x12), UnitK -> false
    | UnitK, Tilda (x11, x12) -> false
    | KFun (x51, x52), KFun (y51, y52) ->
        equal_kLabela _A _B _C x51 y51 &&
          equal_rewrite (equal_kList _A _B _C) x52 y52
    | SingleK x4, SingleK y4 -> equal_rewrite (equal_kItem _A _B _C) x4 y4
    | IdK x3, IdK y3 -> equal_metaVara _C x3 y3
    | Tilda (x11, x12), Tilda (y11, y12) ->
        equal_rewrite (equal_k _A _B _C) x11 y11 &&
          equal_rewrite (equal_k _A _B _C) x12 y12
    | UnitK, UnitK -> true
and equal_theMapa _A _B _C
  x0 x1 = match x0, x1 with MapItem (x41, x42), MapFun (x51, x52) -> false
    | MapFun (x51, x52), MapItem (x41, x42) -> false
    | IdMap x3, MapFun (x51, x52) -> false
    | MapFun (x51, x52), IdMap x3 -> false
    | IdMap x3, MapItem (x41, x42) -> false
    | MapItem (x41, x42), IdMap x3 -> false
    | UnitMap, MapFun (x51, x52) -> false
    | MapFun (x51, x52), UnitMap -> false
    | UnitMap, MapItem (x41, x42) -> false
    | MapItem (x41, x42), UnitMap -> false
    | UnitMap, IdMap x3 -> false
    | IdMap x3, UnitMap -> false
    | MapCon (x11, x12), MapFun (x51, x52) -> false
    | MapFun (x51, x52), MapCon (x11, x12) -> false
    | MapCon (x11, x12), MapItem (x41, x42) -> false
    | MapItem (x41, x42), MapCon (x11, x12) -> false
    | MapCon (x11, x12), IdMap x3 -> false
    | IdMap x3, MapCon (x11, x12) -> false
    | MapCon (x11, x12), UnitMap -> false
    | UnitMap, MapCon (x11, x12) -> false
    | MapFun (x51, x52), MapFun (y51, y52) ->
        equal_kLabela _A _B _C x51 y51 &&
          equal_rewrite (equal_kList _A _B _C) x52 y52
    | MapItem (x41, x42), MapItem (y41, y42) ->
        equal_rewrite (equal_k _A _B _C) x41 y41 &&
          equal_rewrite (equal_k _A _B _C) x42 y42
    | IdMap x3, IdMap y3 -> equal_metaVara _C x3 y3
    | MapCon (x11, x12), MapCon (y11, y12) ->
        equal_rewrite (equal_theMap _A _B _C) x11 y11 &&
          equal_rewrite (equal_theMap _A _B _C) x12 y12
    | UnitMap, UnitMap -> true
and equal_theMap _A _B _C =
  ({equal = equal_theMapa _A _B _C} : ('a, 'b, 'c) theMap equal)
and equal_theSeta _A _B _C
  x0 x1 = match x0, x1 with SetItem x4, SetFun (x51, x52) -> false
    | SetFun (x51, x52), SetItem x4 -> false
    | IdSet x3, SetFun (x51, x52) -> false
    | SetFun (x51, x52), IdSet x3 -> false
    | IdSet x3, SetItem x4 -> false
    | SetItem x4, IdSet x3 -> false
    | UnitSet, SetFun (x51, x52) -> false
    | SetFun (x51, x52), UnitSet -> false
    | UnitSet, SetItem x4 -> false
    | SetItem x4, UnitSet -> false
    | UnitSet, IdSet x3 -> false
    | IdSet x3, UnitSet -> false
    | SetCon (x11, x12), SetFun (x51, x52) -> false
    | SetFun (x51, x52), SetCon (x11, x12) -> false
    | SetCon (x11, x12), SetItem x4 -> false
    | SetItem x4, SetCon (x11, x12) -> false
    | SetCon (x11, x12), IdSet x3 -> false
    | IdSet x3, SetCon (x11, x12) -> false
    | SetCon (x11, x12), UnitSet -> false
    | UnitSet, SetCon (x11, x12) -> false
    | SetFun (x51, x52), SetFun (y51, y52) ->
        equal_kLabela _A _B _C x51 y51 &&
          equal_rewrite (equal_kList _A _B _C) x52 y52
    | SetItem x4, SetItem y4 -> equal_rewrite (equal_k _A _B _C) x4 y4
    | IdSet x3, IdSet y3 -> equal_metaVara _C x3 y3
    | SetCon (x11, x12), SetCon (y11, y12) ->
        equal_rewrite (equal_theSet _A _B _C) x11 y11 &&
          equal_rewrite (equal_theSet _A _B _C) x12 y12
    | UnitSet, UnitSet -> true
and equal_theSet _A _B _C =
  ({equal = equal_theSeta _A _B _C} : ('a, 'b, 'c) theSet equal);;

let rec equal_optiona _A x0 x1 = match x0, x1 with None, Some x2 -> false
                           | Some x2, None -> false
                           | Some x2, Some y2 -> eq _A x2 y2
                           | None, None -> true;;

type ('a, 'b) irKLabel = IRKLabel of 'a label | IRIdKLabel of 'b metaVar;;

type ('a, 'b, 'c) irK = KPat of ('a, 'b, 'c) irKItem list * 'c metaVar option
and ('a, 'b, 'c) irMap =
  MapPat of (('a, 'b, 'c) irK * ('a, 'b, 'c) irK) list * 'c metaVar option
and ('a, 'b, 'c) irSet = SetPat of ('a, 'b, 'c) irK list * 'c metaVar option
and ('a, 'b, 'c) irList = ListPatNoVar of ('a, 'b, 'c) irK list |
  ListPat of ('a, 'b, 'c) irK list * 'c metaVar * ('a, 'b, 'c) irK list
and ('a, 'b, 'c) irBigKWithBag = IRK of ('a, 'b, 'c) irK |
  IRList of ('a, 'b, 'c) irList | IRSet of ('a, 'b, 'c) irSet |
  IRMap of ('a, 'b, 'c) irMap | IRBag of ('a, 'b, 'c) irBag
and ('a, 'b, 'c) irBag =
  BagPat of
    ('b var * (feature list * ('a, 'b, 'c) irBigKWithBag)) list *
      'c metaVar option
and ('a, 'b, 'c) irBigKWithLabel = IRBigBag of ('a, 'b, 'c) irBigKWithBag |
  IRBigLabel of ('a, 'c) irKLabel
and ('a, 'b, 'c) irKList = KListPatNoVar of ('a, 'b, 'c) irBigKWithLabel list |
  KListPat of
    ('a, 'b, 'c) irBigKWithLabel list * 'c metaVar *
      ('a, 'b, 'c) irBigKWithLabel list
and ('a, 'b, 'c) irKItem =
  IRKItem of ('a, 'c) irKLabel * ('a, 'b, 'c) irKList * 'a sort list |
  IRIdKItem of 'c metaVar * 'a sort list | IRHOLE of 'a sort list;;

let rec equal_metaVar _A = ({equal = equal_metaVara _A} : 'a metaVar equal);;

let rec equal_irKLabel _A _B
  x0 x1 = match x0, x1 with IRKLabel x1, IRIdKLabel x2 -> false
    | IRIdKLabel x2, IRKLabel x1 -> false
    | IRIdKLabel x2, IRIdKLabel y2 -> equal_metaVara _B x2 y2
    | IRKLabel x1, IRKLabel y1 -> equal_labela _A x1 y1;;

let rec equal_prod _A _B = ({equal = equal_proda _A _B} : ('a * 'b) equal);;

let rec equal_var _A = ({equal = equal_vara _A} : 'a var equal);;

let rec equal_sort _A = ({equal = equal_sorta _A} : 'a sort equal);;

let rec equal_irK _A _B _C =
  ({equal = equal_irKa _A _B _C} : ('a, 'b, 'c) irK equal)
and equal_irMap _A _B _C
  (MapPat (x1, x2)) (MapPat (y1, y2)) =
    equal_lista (equal_prod (equal_irK _A _B _C) (equal_irK _A _B _C)) x1 y1 &&
      equal_optiona (equal_metaVar _C) x2 y2
and equal_irSet _A _B _C
  (SetPat (x1, x2)) (SetPat (y1, y2)) =
    equal_lista (equal_irK _A _B _C) x1 y1 &&
      equal_optiona (equal_metaVar _C) x2 y2
and equal_irList _A _B _C
  x0 x1 = match x0, x1 with ListPatNoVar x1, ListPat (x21, x22, x23) -> false
    | ListPat (x21, x22, x23), ListPatNoVar x1 -> false
    | ListPat (x21, x22, x23), ListPat (y21, y22, y23) ->
        equal_lista (equal_irK _A _B _C) x21 y21 &&
          (equal_metaVara _C x22 y22 &&
            equal_lista (equal_irK _A _B _C) x23 y23)
    | ListPatNoVar x1, ListPatNoVar y1 -> equal_lista (equal_irK _A _B _C) x1 y1
and equal_irBigKWithBaga _A _B _C
  x0 x1 = match x0, x1 with IRMap x4, IRBag x5 -> false
    | IRBag x5, IRMap x4 -> false
    | IRSet x3, IRBag x5 -> false
    | IRBag x5, IRSet x3 -> false
    | IRSet x3, IRMap x4 -> false
    | IRMap x4, IRSet x3 -> false
    | IRList x2, IRBag x5 -> false
    | IRBag x5, IRList x2 -> false
    | IRList x2, IRMap x4 -> false
    | IRMap x4, IRList x2 -> false
    | IRList x2, IRSet x3 -> false
    | IRSet x3, IRList x2 -> false
    | IRK x1, IRBag x5 -> false
    | IRBag x5, IRK x1 -> false
    | IRK x1, IRMap x4 -> false
    | IRMap x4, IRK x1 -> false
    | IRK x1, IRSet x3 -> false
    | IRSet x3, IRK x1 -> false
    | IRK x1, IRList x2 -> false
    | IRList x2, IRK x1 -> false
    | IRBag x5, IRBag y5 -> equal_irBag _A _B _C x5 y5
    | IRMap x4, IRMap y4 -> equal_irMap _A _B _C x4 y4
    | IRSet x3, IRSet y3 -> equal_irSet _A _B _C x3 y3
    | IRList x2, IRList y2 -> equal_irList _A _B _C x2 y2
    | IRK x1, IRK y1 -> equal_irKa _A _B _C x1 y1
and equal_irBigKWithBag _A _B _C =
  ({equal = equal_irBigKWithBaga _A _B _C} : ('a, 'b, 'c) irBigKWithBag equal)
and equal_irBag _A _B _C
  (BagPat (x1, x2)) (BagPat (y1, y2)) =
    equal_lista
      (equal_prod (equal_var _B)
        (equal_prod (equal_list equal_feature) (equal_irBigKWithBag _A _B _C)))
      x1 y1 &&
      equal_optiona (equal_metaVar _C) x2 y2
and equal_irBigKWithLabela _A _B _C
  x0 x1 = match x0, x1 with IRBigBag x1, IRBigLabel x2 -> false
    | IRBigLabel x2, IRBigBag x1 -> false
    | IRBigLabel x2, IRBigLabel y2 -> equal_irKLabel _A _C x2 y2
    | IRBigBag x1, IRBigBag y1 -> equal_irBigKWithBaga _A _B _C x1 y1
and equal_irBigKWithLabel _A _B _C =
  ({equal = equal_irBigKWithLabela _A _B _C} :
    ('a, 'b, 'c) irBigKWithLabel equal)
and equal_irKList _A _B _C
  x0 x1 = match x0, x1 with KListPatNoVar x1, KListPat (x21, x22, x23) -> false
    | KListPat (x21, x22, x23), KListPatNoVar x1 -> false
    | KListPat (x21, x22, x23), KListPat (y21, y22, y23) ->
        equal_lista (equal_irBigKWithLabel _A _B _C) x21 y21 &&
          (equal_metaVara _C x22 y22 &&
            equal_lista (equal_irBigKWithLabel _A _B _C) x23 y23)
    | KListPatNoVar x1, KListPatNoVar y1 ->
        equal_lista (equal_irBigKWithLabel _A _B _C) x1 y1
and equal_irKItema _A _B _C
  x0 x1 = match x0, x1 with IRIdKItem (x21, x22), IRHOLE x3 -> false
    | IRHOLE x3, IRIdKItem (x21, x22) -> false
    | IRKItem (x11, x12, x13), IRHOLE x3 -> false
    | IRHOLE x3, IRKItem (x11, x12, x13) -> false
    | IRKItem (x11, x12, x13), IRIdKItem (x21, x22) -> false
    | IRIdKItem (x21, x22), IRKItem (x11, x12, x13) -> false
    | IRHOLE x3, IRHOLE y3 -> equal_lista (equal_sort _A) x3 y3
    | IRIdKItem (x21, x22), IRIdKItem (y21, y22) ->
        equal_metaVara _C x21 y21 && equal_lista (equal_sort _A) x22 y22
    | IRKItem (x11, x12, x13), IRKItem (y11, y12, y13) ->
        equal_irKLabel _A _C x11 y11 &&
          (equal_irKList _A _B _C x12 y12 &&
            equal_lista (equal_sort _A) x13 y13)
and equal_irKItem _A _B _C =
  ({equal = equal_irKItema _A _B _C} : ('a, 'b, 'c) irKItem equal)
and equal_irKa _A _B _C
  (KPat (x1, x2)) (KPat (y1, y2)) =
    equal_lista (equal_irKItem _A _B _C) x1 y1 &&
      equal_optiona (equal_metaVar _C) x2 y2;;

type ('a, 'b, 'c) matchFactor = KLabelMatching of ('a, 'c) irKLabel |
  KItemMatching of ('a, 'b, 'c) irKItem | KListMatching of ('a, 'b, 'c) irKList
  | KMatching of ('a, 'b, 'c) irK | ListMatching of ('a, 'b, 'c) irList |
  SetMatching of ('a, 'b, 'c) irSet | MapMatching of ('a, 'b, 'c) irMap |
  BagMatching of ('a, 'b, 'c) irBag;;

let rec equal_matchFactor _A _B _C
  x0 x1 = match x0, x1 with MapMatching x7, BagMatching x8 -> false
    | BagMatching x8, MapMatching x7 -> false
    | SetMatching x6, BagMatching x8 -> false
    | BagMatching x8, SetMatching x6 -> false
    | SetMatching x6, MapMatching x7 -> false
    | MapMatching x7, SetMatching x6 -> false
    | ListMatching x5, BagMatching x8 -> false
    | BagMatching x8, ListMatching x5 -> false
    | ListMatching x5, MapMatching x7 -> false
    | MapMatching x7, ListMatching x5 -> false
    | ListMatching x5, SetMatching x6 -> false
    | SetMatching x6, ListMatching x5 -> false
    | KMatching x4, BagMatching x8 -> false
    | BagMatching x8, KMatching x4 -> false
    | KMatching x4, MapMatching x7 -> false
    | MapMatching x7, KMatching x4 -> false
    | KMatching x4, SetMatching x6 -> false
    | SetMatching x6, KMatching x4 -> false
    | KMatching x4, ListMatching x5 -> false
    | ListMatching x5, KMatching x4 -> false
    | KListMatching x3, BagMatching x8 -> false
    | BagMatching x8, KListMatching x3 -> false
    | KListMatching x3, MapMatching x7 -> false
    | MapMatching x7, KListMatching x3 -> false
    | KListMatching x3, SetMatching x6 -> false
    | SetMatching x6, KListMatching x3 -> false
    | KListMatching x3, ListMatching x5 -> false
    | ListMatching x5, KListMatching x3 -> false
    | KListMatching x3, KMatching x4 -> false
    | KMatching x4, KListMatching x3 -> false
    | KItemMatching x2, BagMatching x8 -> false
    | BagMatching x8, KItemMatching x2 -> false
    | KItemMatching x2, MapMatching x7 -> false
    | MapMatching x7, KItemMatching x2 -> false
    | KItemMatching x2, SetMatching x6 -> false
    | SetMatching x6, KItemMatching x2 -> false
    | KItemMatching x2, ListMatching x5 -> false
    | ListMatching x5, KItemMatching x2 -> false
    | KItemMatching x2, KMatching x4 -> false
    | KMatching x4, KItemMatching x2 -> false
    | KItemMatching x2, KListMatching x3 -> false
    | KListMatching x3, KItemMatching x2 -> false
    | KLabelMatching x1, BagMatching x8 -> false
    | BagMatching x8, KLabelMatching x1 -> false
    | KLabelMatching x1, MapMatching x7 -> false
    | MapMatching x7, KLabelMatching x1 -> false
    | KLabelMatching x1, SetMatching x6 -> false
    | SetMatching x6, KLabelMatching x1 -> false
    | KLabelMatching x1, ListMatching x5 -> false
    | ListMatching x5, KLabelMatching x1 -> false
    | KLabelMatching x1, KMatching x4 -> false
    | KMatching x4, KLabelMatching x1 -> false
    | KLabelMatching x1, KListMatching x3 -> false
    | KListMatching x3, KLabelMatching x1 -> false
    | KLabelMatching x1, KItemMatching x2 -> false
    | KItemMatching x2, KLabelMatching x1 -> false
    | BagMatching x8, BagMatching y8 -> equal_irBag _A _B _C x8 y8
    | MapMatching x7, MapMatching y7 -> equal_irMap _A _B _C x7 y7
    | SetMatching x6, SetMatching y6 -> equal_irSet _A _B _C x6 y6
    | ListMatching x5, ListMatching y5 -> equal_irList _A _B _C x5 y5
    | KMatching x4, KMatching y4 -> equal_irKa _A _B _C x4 y4
    | KListMatching x3, KListMatching y3 -> equal_irKList _A _B _C x3 y3
    | KItemMatching x2, KItemMatching y2 -> equal_irKItema _A _B _C x2 y2
    | KLabelMatching x1, KLabelMatching y1 -> equal_irKLabel _A _C x1 y1;;

type ('a, 'b, 'c) pat = KLabelFunPat of 'a label * ('a, 'b, 'c) irKList |
  KFunPat of 'a label * ('a, 'b, 'c) irKList |
  KItemFunPat of 'a label * ('a, 'b, 'c) irKList |
  ListFunPat of 'a label * ('a, 'b, 'c) irKList |
  SetFunPat of 'a label * ('a, 'b, 'c) irKList |
  MapFunPat of 'a label * ('a, 'b, 'c) irKList |
  NormalPat of ('a, 'b, 'c) matchFactor;;

let rec equal_pata _A _B _C
  x0 x1 = match x0, x1 with MapFunPat (x61, x62), NormalPat x7 -> false
    | NormalPat x7, MapFunPat (x61, x62) -> false
    | SetFunPat (x51, x52), NormalPat x7 -> false
    | NormalPat x7, SetFunPat (x51, x52) -> false
    | SetFunPat (x51, x52), MapFunPat (x61, x62) -> false
    | MapFunPat (x61, x62), SetFunPat (x51, x52) -> false
    | ListFunPat (x41, x42), NormalPat x7 -> false
    | NormalPat x7, ListFunPat (x41, x42) -> false
    | ListFunPat (x41, x42), MapFunPat (x61, x62) -> false
    | MapFunPat (x61, x62), ListFunPat (x41, x42) -> false
    | ListFunPat (x41, x42), SetFunPat (x51, x52) -> false
    | SetFunPat (x51, x52), ListFunPat (x41, x42) -> false
    | KItemFunPat (x31, x32), NormalPat x7 -> false
    | NormalPat x7, KItemFunPat (x31, x32) -> false
    | KItemFunPat (x31, x32), MapFunPat (x61, x62) -> false
    | MapFunPat (x61, x62), KItemFunPat (x31, x32) -> false
    | KItemFunPat (x31, x32), SetFunPat (x51, x52) -> false
    | SetFunPat (x51, x52), KItemFunPat (x31, x32) -> false
    | KItemFunPat (x31, x32), ListFunPat (x41, x42) -> false
    | ListFunPat (x41, x42), KItemFunPat (x31, x32) -> false
    | KFunPat (x21, x22), NormalPat x7 -> false
    | NormalPat x7, KFunPat (x21, x22) -> false
    | KFunPat (x21, x22), MapFunPat (x61, x62) -> false
    | MapFunPat (x61, x62), KFunPat (x21, x22) -> false
    | KFunPat (x21, x22), SetFunPat (x51, x52) -> false
    | SetFunPat (x51, x52), KFunPat (x21, x22) -> false
    | KFunPat (x21, x22), ListFunPat (x41, x42) -> false
    | ListFunPat (x41, x42), KFunPat (x21, x22) -> false
    | KFunPat (x21, x22), KItemFunPat (x31, x32) -> false
    | KItemFunPat (x31, x32), KFunPat (x21, x22) -> false
    | KLabelFunPat (x11, x12), NormalPat x7 -> false
    | NormalPat x7, KLabelFunPat (x11, x12) -> false
    | KLabelFunPat (x11, x12), MapFunPat (x61, x62) -> false
    | MapFunPat (x61, x62), KLabelFunPat (x11, x12) -> false
    | KLabelFunPat (x11, x12), SetFunPat (x51, x52) -> false
    | SetFunPat (x51, x52), KLabelFunPat (x11, x12) -> false
    | KLabelFunPat (x11, x12), ListFunPat (x41, x42) -> false
    | ListFunPat (x41, x42), KLabelFunPat (x11, x12) -> false
    | KLabelFunPat (x11, x12), KItemFunPat (x31, x32) -> false
    | KItemFunPat (x31, x32), KLabelFunPat (x11, x12) -> false
    | KLabelFunPat (x11, x12), KFunPat (x21, x22) -> false
    | KFunPat (x21, x22), KLabelFunPat (x11, x12) -> false
    | NormalPat x7, NormalPat y7 -> equal_matchFactor _A _B _C x7 y7
    | MapFunPat (x61, x62), MapFunPat (y61, y62) ->
        equal_labela _A x61 y61 && equal_irKList _A _B _C x62 y62
    | SetFunPat (x51, x52), SetFunPat (y51, y52) ->
        equal_labela _A x51 y51 && equal_irKList _A _B _C x52 y52
    | ListFunPat (x41, x42), ListFunPat (y41, y42) ->
        equal_labela _A x41 y41 && equal_irKList _A _B _C x42 y42
    | KItemFunPat (x31, x32), KItemFunPat (y31, y32) ->
        equal_labela _A x31 y31 && equal_irKList _A _B _C x32 y32
    | KFunPat (x21, x22), KFunPat (y21, y22) ->
        equal_labela _A x21 y21 && equal_irKList _A _B _C x22 y22
    | KLabelFunPat (x11, x12), KLabelFunPat (y11, y12) ->
        equal_labela _A x11 y11 && equal_irKList _A _B _C x12 y12;;

let rec equal_pat _A _B _C =
  ({equal = equal_pata _A _B _C} : ('a, 'b, 'c) pat equal);;

type ('a, 'b, 'c) suBigKWithBag = SUK of ('a, 'b, 'c) suKFactor list |
  SUList of ('a, 'b, 'c) suL list | SUSet of ('a, 'b, 'c) suS list |
  SUMap of ('a, 'b, 'c) suM list | SUBag of ('a, 'b, 'c) suB list
and ('a, 'b, 'c) suB =
  ItemB of 'b var * feature list * ('a, 'b, 'c) suBigKWithBag |
  IdB of 'c metaVar
and ('a, 'b, 'c) suBigKWithLabel = SUBigBag of ('a, 'b, 'c) suBigKWithBag |
  SUBigLabel of ('a, 'b, 'c) suKLabel
and ('a, 'b, 'c) suKl = ItemKl of ('a, 'b, 'c) suBigKWithLabel |
  IdKl of 'c metaVar
and ('a, 'b, 'c) suKLabel = SUKLabel of 'a label | SUIdKLabel of 'c metaVar |
  SUKLabelFun of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suKItem =
  SUKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list |
  SUIdKItem of 'c metaVar * 'a sort list | SUHOLE of 'a sort list
and ('a, 'b, 'c) suKFactor = ItemFactor of ('a, 'b, 'c) suKItem |
  IdFactor of 'c metaVar |
  SUKKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list * 'a sort list
and ('a, 'b, 'c) suL = ItemL of ('a, 'b, 'c) suKFactor list | IdL of 'c metaVar
  | SUListKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suM =
  ItemM of ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKFactor list |
  IdM of 'c metaVar |
  SUMapKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list
and ('a, 'b, 'c) suS = ItemS of ('a, 'b, 'c) suKFactor list | IdS of 'c metaVar
  | SUSetKItem of ('a, 'b, 'c) suKLabel * ('a, 'b, 'c) suKl list;;

let rec equal_suB _A _B _C =
  ({equal = equal_suBa _A _B _C} : ('a, 'b, 'c) suB equal)
and equal_suBigKWithBag _A _B _C
  x0 x1 = match x0, x1 with SUMap x4, SUBag x5 -> false
    | SUBag x5, SUMap x4 -> false
    | SUSet x3, SUBag x5 -> false
    | SUBag x5, SUSet x3 -> false
    | SUSet x3, SUMap x4 -> false
    | SUMap x4, SUSet x3 -> false
    | SUList x2, SUBag x5 -> false
    | SUBag x5, SUList x2 -> false
    | SUList x2, SUMap x4 -> false
    | SUMap x4, SUList x2 -> false
    | SUList x2, SUSet x3 -> false
    | SUSet x3, SUList x2 -> false
    | SUK x1, SUBag x5 -> false
    | SUBag x5, SUK x1 -> false
    | SUK x1, SUMap x4 -> false
    | SUMap x4, SUK x1 -> false
    | SUK x1, SUSet x3 -> false
    | SUSet x3, SUK x1 -> false
    | SUK x1, SUList x2 -> false
    | SUList x2, SUK x1 -> false
    | SUBag x5, SUBag y5 -> equal_lista (equal_suB _A _B _C) x5 y5
    | SUMap x4, SUMap y4 -> equal_lista (equal_suM _A _B _C) x4 y4
    | SUSet x3, SUSet y3 -> equal_lista (equal_suS _A _B _C) x3 y3
    | SUList x2, SUList y2 -> equal_lista (equal_suL _A _B _C) x2 y2
    | SUK x1, SUK y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suBa _A _B _C
  x0 x1 = match x0, x1 with ItemB (x11, x12, x13), IdB x2 -> false
    | IdB x2, ItemB (x11, x12, x13) -> false
    | IdB x2, IdB y2 -> equal_metaVara _C x2 y2
    | ItemB (x11, x12, x13), ItemB (y11, y12, y13) ->
        equal_vara _B x11 y11 &&
          (equal_lista equal_feature x12 y12 &&
            equal_suBigKWithBag _A _B _C x13 y13)
and equal_suBigKWithLabel _A _B _C
  x0 x1 = match x0, x1 with SUBigBag x1, SUBigLabel x2 -> false
    | SUBigLabel x2, SUBigBag x1 -> false
    | SUBigLabel x2, SUBigLabel y2 -> equal_suKLabel _A _B _C x2 y2
    | SUBigBag x1, SUBigBag y1 -> equal_suBigKWithBag _A _B _C x1 y1
and equal_suKla _A _B _C
  x0 x1 = match x0, x1 with ItemKl x1, IdKl x2 -> false
    | IdKl x2, ItemKl x1 -> false
    | IdKl x2, IdKl y2 -> equal_metaVara _C x2 y2
    | ItemKl x1, ItemKl y1 -> equal_suBigKWithLabel _A _B _C x1 y1
and equal_suKl _A _B _C =
  ({equal = equal_suKla _A _B _C} : ('a, 'b, 'c) suKl equal)
and equal_suKLabel _A _B _C
  x0 x1 = match x0, x1 with SUIdKLabel x2, SUKLabelFun (x31, x32) -> false
    | SUKLabelFun (x31, x32), SUIdKLabel x2 -> false
    | SUKLabel x1, SUKLabelFun (x31, x32) -> false
    | SUKLabelFun (x31, x32), SUKLabel x1 -> false
    | SUKLabel x1, SUIdKLabel x2 -> false
    | SUIdKLabel x2, SUKLabel x1 -> false
    | SUKLabelFun (x31, x32), SUKLabelFun (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | SUIdKLabel x2, SUIdKLabel y2 -> equal_metaVara _C x2 y2
    | SUKLabel x1, SUKLabel y1 -> equal_labela _A x1 y1
and equal_suKItema _A _B _C
  x0 x1 = match x0, x1 with SUIdKItem (x21, x22), SUHOLE x3 -> false
    | SUHOLE x3, SUIdKItem (x21, x22) -> false
    | SUKItem (x11, x12, x13), SUHOLE x3 -> false
    | SUHOLE x3, SUKItem (x11, x12, x13) -> false
    | SUKItem (x11, x12, x13), SUIdKItem (x21, x22) -> false
    | SUIdKItem (x21, x22), SUKItem (x11, x12, x13) -> false
    | SUHOLE x3, SUHOLE y3 -> equal_lista (equal_sort _A) x3 y3
    | SUIdKItem (x21, x22), SUIdKItem (y21, y22) ->
        equal_metaVara _C x21 y21 && equal_lista (equal_sort _A) x22 y22
    | SUKItem (x11, x12, x13), SUKItem (y11, y12, y13) ->
        equal_suKLabel _A _B _C x11 y11 &&
          (equal_lista (equal_suKl _A _B _C) x12 y12 &&
            equal_lista (equal_sort _A) x13 y13)
and equal_suKFactora _A _B _C
  x0 x1 = match x0, x1 with IdFactor x2, SUKKItem (x31, x32, x33) -> false
    | SUKKItem (x31, x32, x33), IdFactor x2 -> false
    | ItemFactor x1, SUKKItem (x31, x32, x33) -> false
    | SUKKItem (x31, x32, x33), ItemFactor x1 -> false
    | ItemFactor x1, IdFactor x2 -> false
    | IdFactor x2, ItemFactor x1 -> false
    | SUKKItem (x31, x32, x33), SUKKItem (y31, y32, y33) ->
        equal_suKLabel _A _B _C x31 y31 &&
          (equal_lista (equal_suKl _A _B _C) x32 y32 &&
            equal_lista (equal_sort _A) x33 y33)
    | IdFactor x2, IdFactor y2 -> equal_metaVara _C x2 y2
    | ItemFactor x1, ItemFactor y1 -> equal_suKItema _A _B _C x1 y1
and equal_suKFactor _A _B _C =
  ({equal = equal_suKFactora _A _B _C} : ('a, 'b, 'c) suKFactor equal)
and equal_suLa _A _B _C
  x0 x1 = match x0, x1 with IdL x2, SUListKItem (x31, x32) -> false
    | SUListKItem (x31, x32), IdL x2 -> false
    | ItemL x1, SUListKItem (x31, x32) -> false
    | SUListKItem (x31, x32), ItemL x1 -> false
    | ItemL x1, IdL x2 -> false
    | IdL x2, ItemL x1 -> false
    | SUListKItem (x31, x32), SUListKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdL x2, IdL y2 -> equal_metaVara _C x2 y2
    | ItemL x1, ItemL y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suL _A _B _C =
  ({equal = equal_suLa _A _B _C} : ('a, 'b, 'c) suL equal)
and equal_suMa _A _B _C
  x0 x1 = match x0, x1 with IdM x2, SUMapKItem (x31, x32) -> false
    | SUMapKItem (x31, x32), IdM x2 -> false
    | ItemM (x11, x12), SUMapKItem (x31, x32) -> false
    | SUMapKItem (x31, x32), ItemM (x11, x12) -> false
    | ItemM (x11, x12), IdM x2 -> false
    | IdM x2, ItemM (x11, x12) -> false
    | SUMapKItem (x31, x32), SUMapKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdM x2, IdM y2 -> equal_metaVara _C x2 y2
    | ItemM (x11, x12), ItemM (y11, y12) ->
        equal_lista (equal_suKFactor _A _B _C) x11 y11 &&
          equal_lista (equal_suKFactor _A _B _C) x12 y12
and equal_suM _A _B _C =
  ({equal = equal_suMa _A _B _C} : ('a, 'b, 'c) suM equal)
and equal_suSa _A _B _C
  x0 x1 = match x0, x1 with IdS x2, SUSetKItem (x31, x32) -> false
    | SUSetKItem (x31, x32), IdS x2 -> false
    | ItemS x1, SUSetKItem (x31, x32) -> false
    | SUSetKItem (x31, x32), ItemS x1 -> false
    | ItemS x1, IdS x2 -> false
    | IdS x2, ItemS x1 -> false
    | SUSetKItem (x31, x32), SUSetKItem (y31, y32) ->
        equal_suKLabel _A _B _C x31 y31 &&
          equal_lista (equal_suKl _A _B _C) x32 y32
    | IdS x2, IdS y2 -> equal_metaVara _C x2 y2
    | ItemS x1, ItemS y1 -> equal_lista (equal_suKFactor _A _B _C) x1 y1
and equal_suS _A _B _C =
  ({equal = equal_suSa _A _B _C} : ('a, 'b, 'c) suS equal);;

let rec equal_option _A = ({equal = equal_optiona _A} : ('a option) equal);;

let rec equal_label _A = ({equal = equal_labela _A} : 'a label equal);;

type 'a symbol = NonTerminal of 'a sort | Terminal of char list;;

let rec equal_symbola _A
  x0 x1 = match x0, x1 with NonTerminal x1, Terminal x2 -> false
    | Terminal x2, NonTerminal x1 -> false
    | Terminal x2, Terminal y2 -> equal_lista equal_char x2 y2
    | NonTerminal x1, NonTerminal y1 -> equal_sorta _A x1 y1;;

let rec equal_symbol _A = ({equal = equal_symbola _A} : 'a symbol equal);;

type 'a nelist = Single of 'a | Con of 'a * 'a nelist;;

let rec equal_nelist _A
  x0 x1 = match x0, x1 with Single x1, Con (x21, x22) -> false
    | Con (x21, x22), Single x1 -> false
    | Con (x21, x22), Con (y21, y22) -> eq _A x21 y21 && equal_nelist _A x22 y22
    | Single x1, Single y1 -> eq _A x1 y1;;

type reg = Eps | Sym of char | Alt of reg * reg | TheSeq of reg * reg |
  Rep of reg;;

let rec equal_reg
  x0 x1 = match x0, x1 with TheSeq (x41, x42), Rep x5 -> false
    | Rep x5, TheSeq (x41, x42) -> false
    | Alt (x31, x32), Rep x5 -> false
    | Rep x5, Alt (x31, x32) -> false
    | Alt (x31, x32), TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Alt (x31, x32) -> false
    | Sym x2, Rep x5 -> false
    | Rep x5, Sym x2 -> false
    | Sym x2, TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Sym x2 -> false
    | Sym x2, Alt (x31, x32) -> false
    | Alt (x31, x32), Sym x2 -> false
    | Eps, Rep x5 -> false
    | Rep x5, Eps -> false
    | Eps, TheSeq (x41, x42) -> false
    | TheSeq (x41, x42), Eps -> false
    | Eps, Alt (x31, x32) -> false
    | Alt (x31, x32), Eps -> false
    | Eps, Sym x2 -> false
    | Sym x2, Eps -> false
    | Rep x5, Rep y5 -> equal_reg x5 y5
    | TheSeq (x41, x42), TheSeq (y41, y42) ->
        equal_reg x41 y41 && equal_reg x42 y42
    | Alt (x31, x32), Alt (y31, y32) -> equal_reg x31 y31 && equal_reg x32 y32
    | Sym x2, Sym y2 -> equal_chara x2 y2
    | Eps, Eps -> true;;

type synAttrib = Strict of nat list | Seqstrict | Left | Right |
  Hook of char list | Function | Klabel of char list | Bracket | Tokena | Avoid
  | OnlyLabel | NotInRules | Regex of reg | NonAssoc |
  OtherSynAttr of char list;;

type 'a kSyntax = Syntax of 'a sort * 'a symbol nelist * synAttrib list |
  Subsort of 'a sort * 'a sort | Token of 'a sort * reg * synAttrib list |
  ListSyntax of 'a sort * 'a sort * char list * synAttrib list;;

let rec equal_synAttriba
  x0 x1 = match x0, x1 with NonAssoc, OtherSynAttr x15 -> false
    | OtherSynAttr x15, NonAssoc -> false
    | Regex x13, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Regex x13 -> false
    | Regex x13, NonAssoc -> false
    | NonAssoc, Regex x13 -> false
    | NotInRules, OtherSynAttr x15 -> false
    | OtherSynAttr x15, NotInRules -> false
    | NotInRules, NonAssoc -> false
    | NonAssoc, NotInRules -> false
    | NotInRules, Regex x13 -> false
    | Regex x13, NotInRules -> false
    | OnlyLabel, OtherSynAttr x15 -> false
    | OtherSynAttr x15, OnlyLabel -> false
    | OnlyLabel, NonAssoc -> false
    | NonAssoc, OnlyLabel -> false
    | OnlyLabel, Regex x13 -> false
    | Regex x13, OnlyLabel -> false
    | OnlyLabel, NotInRules -> false
    | NotInRules, OnlyLabel -> false
    | Avoid, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Avoid -> false
    | Avoid, NonAssoc -> false
    | NonAssoc, Avoid -> false
    | Avoid, Regex x13 -> false
    | Regex x13, Avoid -> false
    | Avoid, NotInRules -> false
    | NotInRules, Avoid -> false
    | Avoid, OnlyLabel -> false
    | OnlyLabel, Avoid -> false
    | Tokena, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Tokena -> false
    | Tokena, NonAssoc -> false
    | NonAssoc, Tokena -> false
    | Tokena, Regex x13 -> false
    | Regex x13, Tokena -> false
    | Tokena, NotInRules -> false
    | NotInRules, Tokena -> false
    | Tokena, OnlyLabel -> false
    | OnlyLabel, Tokena -> false
    | Tokena, Avoid -> false
    | Avoid, Tokena -> false
    | Bracket, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Bracket -> false
    | Bracket, NonAssoc -> false
    | NonAssoc, Bracket -> false
    | Bracket, Regex x13 -> false
    | Regex x13, Bracket -> false
    | Bracket, NotInRules -> false
    | NotInRules, Bracket -> false
    | Bracket, OnlyLabel -> false
    | OnlyLabel, Bracket -> false
    | Bracket, Avoid -> false
    | Avoid, Bracket -> false
    | Bracket, Tokena -> false
    | Tokena, Bracket -> false
    | Klabel x7, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Klabel x7 -> false
    | Klabel x7, NonAssoc -> false
    | NonAssoc, Klabel x7 -> false
    | Klabel x7, Regex x13 -> false
    | Regex x13, Klabel x7 -> false
    | Klabel x7, NotInRules -> false
    | NotInRules, Klabel x7 -> false
    | Klabel x7, OnlyLabel -> false
    | OnlyLabel, Klabel x7 -> false
    | Klabel x7, Avoid -> false
    | Avoid, Klabel x7 -> false
    | Klabel x7, Tokena -> false
    | Tokena, Klabel x7 -> false
    | Klabel x7, Bracket -> false
    | Bracket, Klabel x7 -> false
    | Function, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Function -> false
    | Function, NonAssoc -> false
    | NonAssoc, Function -> false
    | Function, Regex x13 -> false
    | Regex x13, Function -> false
    | Function, NotInRules -> false
    | NotInRules, Function -> false
    | Function, OnlyLabel -> false
    | OnlyLabel, Function -> false
    | Function, Avoid -> false
    | Avoid, Function -> false
    | Function, Tokena -> false
    | Tokena, Function -> false
    | Function, Bracket -> false
    | Bracket, Function -> false
    | Function, Klabel x7 -> false
    | Klabel x7, Function -> false
    | Hook x5, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Hook x5 -> false
    | Hook x5, NonAssoc -> false
    | NonAssoc, Hook x5 -> false
    | Hook x5, Regex x13 -> false
    | Regex x13, Hook x5 -> false
    | Hook x5, NotInRules -> false
    | NotInRules, Hook x5 -> false
    | Hook x5, OnlyLabel -> false
    | OnlyLabel, Hook x5 -> false
    | Hook x5, Avoid -> false
    | Avoid, Hook x5 -> false
    | Hook x5, Tokena -> false
    | Tokena, Hook x5 -> false
    | Hook x5, Bracket -> false
    | Bracket, Hook x5 -> false
    | Hook x5, Klabel x7 -> false
    | Klabel x7, Hook x5 -> false
    | Hook x5, Function -> false
    | Function, Hook x5 -> false
    | Right, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Right -> false
    | Right, NonAssoc -> false
    | NonAssoc, Right -> false
    | Right, Regex x13 -> false
    | Regex x13, Right -> false
    | Right, NotInRules -> false
    | NotInRules, Right -> false
    | Right, OnlyLabel -> false
    | OnlyLabel, Right -> false
    | Right, Avoid -> false
    | Avoid, Right -> false
    | Right, Tokena -> false
    | Tokena, Right -> false
    | Right, Bracket -> false
    | Bracket, Right -> false
    | Right, Klabel x7 -> false
    | Klabel x7, Right -> false
    | Right, Function -> false
    | Function, Right -> false
    | Right, Hook x5 -> false
    | Hook x5, Right -> false
    | Left, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Left -> false
    | Left, NonAssoc -> false
    | NonAssoc, Left -> false
    | Left, Regex x13 -> false
    | Regex x13, Left -> false
    | Left, NotInRules -> false
    | NotInRules, Left -> false
    | Left, OnlyLabel -> false
    | OnlyLabel, Left -> false
    | Left, Avoid -> false
    | Avoid, Left -> false
    | Left, Tokena -> false
    | Tokena, Left -> false
    | Left, Bracket -> false
    | Bracket, Left -> false
    | Left, Klabel x7 -> false
    | Klabel x7, Left -> false
    | Left, Function -> false
    | Function, Left -> false
    | Left, Hook x5 -> false
    | Hook x5, Left -> false
    | Left, Right -> false
    | Right, Left -> false
    | Seqstrict, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Seqstrict -> false
    | Seqstrict, NonAssoc -> false
    | NonAssoc, Seqstrict -> false
    | Seqstrict, Regex x13 -> false
    | Regex x13, Seqstrict -> false
    | Seqstrict, NotInRules -> false
    | NotInRules, Seqstrict -> false
    | Seqstrict, OnlyLabel -> false
    | OnlyLabel, Seqstrict -> false
    | Seqstrict, Avoid -> false
    | Avoid, Seqstrict -> false
    | Seqstrict, Tokena -> false
    | Tokena, Seqstrict -> false
    | Seqstrict, Bracket -> false
    | Bracket, Seqstrict -> false
    | Seqstrict, Klabel x7 -> false
    | Klabel x7, Seqstrict -> false
    | Seqstrict, Function -> false
    | Function, Seqstrict -> false
    | Seqstrict, Hook x5 -> false
    | Hook x5, Seqstrict -> false
    | Seqstrict, Right -> false
    | Right, Seqstrict -> false
    | Seqstrict, Left -> false
    | Left, Seqstrict -> false
    | Strict x1, OtherSynAttr x15 -> false
    | OtherSynAttr x15, Strict x1 -> false
    | Strict x1, NonAssoc -> false
    | NonAssoc, Strict x1 -> false
    | Strict x1, Regex x13 -> false
    | Regex x13, Strict x1 -> false
    | Strict x1, NotInRules -> false
    | NotInRules, Strict x1 -> false
    | Strict x1, OnlyLabel -> false
    | OnlyLabel, Strict x1 -> false
    | Strict x1, Avoid -> false
    | Avoid, Strict x1 -> false
    | Strict x1, Tokena -> false
    | Tokena, Strict x1 -> false
    | Strict x1, Bracket -> false
    | Bracket, Strict x1 -> false
    | Strict x1, Klabel x7 -> false
    | Klabel x7, Strict x1 -> false
    | Strict x1, Function -> false
    | Function, Strict x1 -> false
    | Strict x1, Hook x5 -> false
    | Hook x5, Strict x1 -> false
    | Strict x1, Right -> false
    | Right, Strict x1 -> false
    | Strict x1, Left -> false
    | Left, Strict x1 -> false
    | Strict x1, Seqstrict -> false
    | Seqstrict, Strict x1 -> false
    | OtherSynAttr x15, OtherSynAttr y15 -> equal_lista equal_char x15 y15
    | Regex x13, Regex y13 -> equal_reg x13 y13
    | Klabel x7, Klabel y7 -> equal_lista equal_char x7 y7
    | Hook x5, Hook y5 -> equal_lista equal_char x5 y5
    | Strict x1, Strict y1 -> equal_lista equal_nat x1 y1
    | NonAssoc, NonAssoc -> true
    | NotInRules, NotInRules -> true
    | OnlyLabel, OnlyLabel -> true
    | Avoid, Avoid -> true
    | Tokena, Tokena -> true
    | Bracket, Bracket -> true
    | Function, Function -> true
    | Right, Right -> true
    | Left, Left -> true
    | Seqstrict, Seqstrict -> true;;

let equal_synAttrib = ({equal = equal_synAttriba} : synAttrib equal);;

let rec equal_kSyntaxa _A
  x0 x1 = match x0, x1 with
    Token (x31, x32, x33), ListSyntax (x41, x42, x43, x44) -> false
    | ListSyntax (x41, x42, x43, x44), Token (x31, x32, x33) -> false
    | Subsort (x21, x22), ListSyntax (x41, x42, x43, x44) -> false
    | ListSyntax (x41, x42, x43, x44), Subsort (x21, x22) -> false
    | Subsort (x21, x22), Token (x31, x32, x33) -> false
    | Token (x31, x32, x33), Subsort (x21, x22) -> false
    | Syntax (x11, x12, x13), ListSyntax (x41, x42, x43, x44) -> false
    | ListSyntax (x41, x42, x43, x44), Syntax (x11, x12, x13) -> false
    | Syntax (x11, x12, x13), Token (x31, x32, x33) -> false
    | Token (x31, x32, x33), Syntax (x11, x12, x13) -> false
    | Syntax (x11, x12, x13), Subsort (x21, x22) -> false
    | Subsort (x21, x22), Syntax (x11, x12, x13) -> false
    | ListSyntax (x41, x42, x43, x44), ListSyntax (y41, y42, y43, y44) ->
        equal_sorta _A x41 y41 &&
          (equal_sorta _A x42 y42 &&
            (equal_lista equal_char x43 y43 &&
              equal_lista equal_synAttrib x44 y44))
    | Token (x31, x32, x33), Token (y31, y32, y33) ->
        equal_sorta _A x31 y31 &&
          (equal_reg x32 y32 && equal_lista equal_synAttrib x33 y33)
    | Subsort (x21, x22), Subsort (y21, y22) ->
        equal_sorta _A x21 y21 && equal_sorta _A x22 y22
    | Syntax (x11, x12, x13), Syntax (y11, y12, y13) ->
        equal_sorta _A x11 y11 &&
          (equal_nelist (equal_symbol _A) x12 y12 &&
            equal_lista equal_synAttrib x13 y13);;

let rec equal_kSyntax _A = ({equal = equal_kSyntaxa _A} : 'a kSyntax equal);;

type ('a, 'b, 'c) subsFactor = KLabelSubs of ('a, 'b, 'c) suKLabel |
  KItemSubs of ('a, 'b, 'c) suKItem | KListSubs of ('a, 'b, 'c) suKl list |
  KSubs of ('a, 'b, 'c) suKFactor list | ListSubs of ('a, 'b, 'c) suL list |
  SetSubs of ('a, 'b, 'c) suS list | MapSubs of ('a, 'b, 'c) suM list |
  BagSubs of ('a, 'b, 'c) suB list;;

type ('a, 'b, 'c) rulePat =
  FunPat of
    'a label *
      (('a, 'b, 'c) pat *
        (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) list *
      (('a, 'b, 'c) pat *
        (('a, 'b, 'c) subsFactor * ('a, 'b, 'c) suKItem)) option
  | MacroPat of 'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list |
  AnywherePat of
    'a label * ('a, 'b, 'c) irKList * ('a, 'b, 'c) suKFactor list *
      ('a, 'b, 'c) suKItem
  | KRulePat of
      ('a, 'b, 'c) irK * ('a, 'b, 'c) suKFactor list * ('a, 'b, 'c) suKItem *
        bool
  | BagRulePat of
      ('a, 'b, 'c) irBag * ('a, 'b, 'c) suB list * ('a, 'b, 'c) suKItem * bool;;

let rec equal_subsFactora _A _B _C
  x0 x1 = match x0, x1 with MapSubs x7, BagSubs x8 -> false
    | BagSubs x8, MapSubs x7 -> false
    | SetSubs x6, BagSubs x8 -> false
    | BagSubs x8, SetSubs x6 -> false
    | SetSubs x6, MapSubs x7 -> false
    | MapSubs x7, SetSubs x6 -> false
    | ListSubs x5, BagSubs x8 -> false
    | BagSubs x8, ListSubs x5 -> false
    | ListSubs x5, MapSubs x7 -> false
    | MapSubs x7, ListSubs x5 -> false
    | ListSubs x5, SetSubs x6 -> false
    | SetSubs x6, ListSubs x5 -> false
    | KSubs x4, BagSubs x8 -> false
    | BagSubs x8, KSubs x4 -> false
    | KSubs x4, MapSubs x7 -> false
    | MapSubs x7, KSubs x4 -> false
    | KSubs x4, SetSubs x6 -> false
    | SetSubs x6, KSubs x4 -> false
    | KSubs x4, ListSubs x5 -> false
    | ListSubs x5, KSubs x4 -> false
    | KListSubs x3, BagSubs x8 -> false
    | BagSubs x8, KListSubs x3 -> false
    | KListSubs x3, MapSubs x7 -> false
    | MapSubs x7, KListSubs x3 -> false
    | KListSubs x3, SetSubs x6 -> false
    | SetSubs x6, KListSubs x3 -> false
    | KListSubs x3, ListSubs x5 -> false
    | ListSubs x5, KListSubs x3 -> false
    | KListSubs x3, KSubs x4 -> false
    | KSubs x4, KListSubs x3 -> false
    | KItemSubs x2, BagSubs x8 -> false
    | BagSubs x8, KItemSubs x2 -> false
    | KItemSubs x2, MapSubs x7 -> false
    | MapSubs x7, KItemSubs x2 -> false
    | KItemSubs x2, SetSubs x6 -> false
    | SetSubs x6, KItemSubs x2 -> false
    | KItemSubs x2, ListSubs x5 -> false
    | ListSubs x5, KItemSubs x2 -> false
    | KItemSubs x2, KSubs x4 -> false
    | KSubs x4, KItemSubs x2 -> false
    | KItemSubs x2, KListSubs x3 -> false
    | KListSubs x3, KItemSubs x2 -> false
    | KLabelSubs x1, BagSubs x8 -> false
    | BagSubs x8, KLabelSubs x1 -> false
    | KLabelSubs x1, MapSubs x7 -> false
    | MapSubs x7, KLabelSubs x1 -> false
    | KLabelSubs x1, SetSubs x6 -> false
    | SetSubs x6, KLabelSubs x1 -> false
    | KLabelSubs x1, ListSubs x5 -> false
    | ListSubs x5, KLabelSubs x1 -> false
    | KLabelSubs x1, KSubs x4 -> false
    | KSubs x4, KLabelSubs x1 -> false
    | KLabelSubs x1, KListSubs x3 -> false
    | KListSubs x3, KLabelSubs x1 -> false
    | KLabelSubs x1, KItemSubs x2 -> false
    | KItemSubs x2, KLabelSubs x1 -> false
    | BagSubs x8, BagSubs y8 -> equal_lista (equal_suB _A _B _C) x8 y8
    | MapSubs x7, MapSubs y7 -> equal_lista (equal_suM _A _B _C) x7 y7
    | SetSubs x6, SetSubs y6 -> equal_lista (equal_suS _A _B _C) x6 y6
    | ListSubs x5, ListSubs y5 -> equal_lista (equal_suL _A _B _C) x5 y5
    | KSubs x4, KSubs y4 -> equal_lista (equal_suKFactor _A _B _C) x4 y4
    | KListSubs x3, KListSubs y3 -> equal_lista (equal_suKl _A _B _C) x3 y3
    | KItemSubs x2, KItemSubs y2 -> equal_suKItema _A _B _C x2 y2
    | KLabelSubs x1, KLabelSubs y1 -> equal_suKLabel _A _B _C x1 y1;;

let rec equal_subsFactor _A _B _C =
  ({equal = equal_subsFactora _A _B _C} : ('a, 'b, 'c) subsFactor equal);;

let rec equal_suKItem _A _B _C =
  ({equal = equal_suKItema _A _B _C} : ('a, 'b, 'c) suKItem equal);;

let rec equal_rulePata _A _B _C
  x0 x1 = match x0, x1 with
    KRulePat (x41, x42, x43, x44), BagRulePat (x51, x52, x53, x54) -> false
    | BagRulePat (x51, x52, x53, x54), KRulePat (x41, x42, x43, x44) -> false
    | AnywherePat (x31, x32, x33, x34), BagRulePat (x51, x52, x53, x54) -> false
    | BagRulePat (x51, x52, x53, x54), AnywherePat (x31, x32, x33, x34) -> false
    | AnywherePat (x31, x32, x33, x34), KRulePat (x41, x42, x43, x44) -> false
    | KRulePat (x41, x42, x43, x44), AnywherePat (x31, x32, x33, x34) -> false
    | MacroPat (x21, x22, x23), BagRulePat (x51, x52, x53, x54) -> false
    | BagRulePat (x51, x52, x53, x54), MacroPat (x21, x22, x23) -> false
    | MacroPat (x21, x22, x23), KRulePat (x41, x42, x43, x44) -> false
    | KRulePat (x41, x42, x43, x44), MacroPat (x21, x22, x23) -> false
    | MacroPat (x21, x22, x23), AnywherePat (x31, x32, x33, x34) -> false
    | AnywherePat (x31, x32, x33, x34), MacroPat (x21, x22, x23) -> false
    | FunPat (x11, x12, x13), BagRulePat (x51, x52, x53, x54) -> false
    | BagRulePat (x51, x52, x53, x54), FunPat (x11, x12, x13) -> false
    | FunPat (x11, x12, x13), KRulePat (x41, x42, x43, x44) -> false
    | KRulePat (x41, x42, x43, x44), FunPat (x11, x12, x13) -> false
    | FunPat (x11, x12, x13), AnywherePat (x31, x32, x33, x34) -> false
    | AnywherePat (x31, x32, x33, x34), FunPat (x11, x12, x13) -> false
    | FunPat (x11, x12, x13), MacroPat (x21, x22, x23) -> false
    | MacroPat (x21, x22, x23), FunPat (x11, x12, x13) -> false
    | BagRulePat (x51, x52, x53, x54), BagRulePat (y51, y52, y53, y54) ->
        equal_irBag _A _B _C x51 y51 &&
          (equal_lista (equal_suB _A _B _C) x52 y52 &&
            (equal_suKItema _A _B _C x53 y53 && equal_bool x54 y54))
    | KRulePat (x41, x42, x43, x44), KRulePat (y41, y42, y43, y44) ->
        equal_irKa _A _B _C x41 y41 &&
          (equal_lista (equal_suKFactor _A _B _C) x42 y42 &&
            (equal_suKItema _A _B _C x43 y43 && equal_bool x44 y44))
    | AnywherePat (x31, x32, x33, x34), AnywherePat (y31, y32, y33, y34) ->
        equal_labela _A x31 y31 &&
          (equal_irKList _A _B _C x32 y32 &&
            (equal_lista (equal_suKFactor _A _B _C) x33 y33 &&
              equal_suKItema _A _B _C x34 y34))
    | MacroPat (x21, x22, x23), MacroPat (y21, y22, y23) ->
        equal_labela _A x21 y21 &&
          (equal_irKList _A _B _C x22 y22 &&
            equal_lista (equal_suKFactor _A _B _C) x23 y23)
    | FunPat (x11, x12, x13), FunPat (y11, y12, y13) ->
        equal_labela _A x11 y11 &&
          (equal_lista
             (equal_prod (equal_pat _A _B _C)
               (equal_prod (equal_subsFactor _A _B _C)
                 (equal_suKItem _A _B _C)))
             x12 y12 &&
            equal_optiona
              (equal_prod (equal_pat _A _B _C)
                (equal_prod (equal_subsFactor _A _B _C)
                  (equal_suKItem _A _B _C)))
              x13 y13);;

let rec equal_rulePat _A _B _C =
  ({equal = equal_rulePata _A _B _C} : ('a, 'b, 'c) rulePat equal);;

let rec equal_unita u v = true;;

let equal_unit = ({equal = equal_unita} : unit equal);;

type kRequire = Requires of char list;;

let rec equal_kRequire
  (Requires x) (Requires ya) = equal_lista equal_char x ya;;

type ('a, 'b) ruleAttrib = Attr of 'a | Heat | Cool | Transition | Anywhere |
  Structural | Owise | Macro | Result of 'b sort;;

type ('a, 'b, 'c) kRule =
  Context of ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list |
  ContextWithCon of
    ('a, 'b, 'c) kItem * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KRule of ('a, 'b, 'c) k rewrite * ('b, 'a) ruleAttrib list |
  KRuleWithCon of
    ('a, 'b, 'c) k rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KItemRule of ('a, 'b, 'c) kItem rewrite * ('b, 'a) ruleAttrib list |
  KItemRuleWithCon of
    ('a, 'b, 'c) kItem rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | KLabelRule of ('a, 'b, 'c) kLabel rewrite * ('b, 'a) ruleAttrib list |
  KLabelRuleWithCon of
    ('a, 'b, 'c) kLabel rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | BagRule of ('a, 'b, 'c) bag rewrite * ('b, 'a) ruleAttrib list |
  BagRuleWithCon of
    ('a, 'b, 'c) bag rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | ListRule of ('a, 'b, 'c) theList rewrite * ('b, 'a) ruleAttrib list |
  ListRuleWithCon of
    ('a, 'b, 'c) theList rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | SetRule of ('a, 'b, 'c) theSet rewrite * ('b, 'a) ruleAttrib list |
  SetRuleWithCon of
    ('a, 'b, 'c) theSet rewrite * ('a, 'b, 'c) kItem * ('b, 'a) ruleAttrib list
  | MapRule of ('a, 'b, 'c) theMap rewrite * ('b, 'a) ruleAttrib list |
  MapRuleWithCon of
    ('a, 'b, 'c) theMap rewrite * ('a, 'b, 'c) kItem *
      ('b, 'a) ruleAttrib list;;

type ('a, 'b, 'c, 'd) kModuleItem = TheSyntax of 'a kSyntax | Imports of 'c |
  TheConfiguration of ('a, 'b, 'd) bag | TheRule of ('a, 'b, 'd) kRule;;

type ('a, 'b, 'c, 'd) kModule =
  Module of 'c * ('a, 'b, 'c, 'd) kModuleItem list;;

let rec equal_ruleAttriba _A _B
  x0 x1 = match x0, x1 with Macro, Result x9 -> false
    | Result x9, Macro -> false
    | Owise, Result x9 -> false
    | Result x9, Owise -> false
    | Owise, Macro -> false
    | Macro, Owise -> false
    | Structural, Result x9 -> false
    | Result x9, Structural -> false
    | Structural, Macro -> false
    | Macro, Structural -> false
    | Structural, Owise -> false
    | Owise, Structural -> false
    | Anywhere, Result x9 -> false
    | Result x9, Anywhere -> false
    | Anywhere, Macro -> false
    | Macro, Anywhere -> false
    | Anywhere, Owise -> false
    | Owise, Anywhere -> false
    | Anywhere, Structural -> false
    | Structural, Anywhere -> false
    | Transition, Result x9 -> false
    | Result x9, Transition -> false
    | Transition, Macro -> false
    | Macro, Transition -> false
    | Transition, Owise -> false
    | Owise, Transition -> false
    | Transition, Structural -> false
    | Structural, Transition -> false
    | Transition, Anywhere -> false
    | Anywhere, Transition -> false
    | Cool, Result x9 -> false
    | Result x9, Cool -> false
    | Cool, Macro -> false
    | Macro, Cool -> false
    | Cool, Owise -> false
    | Owise, Cool -> false
    | Cool, Structural -> false
    | Structural, Cool -> false
    | Cool, Anywhere -> false
    | Anywhere, Cool -> false
    | Cool, Transition -> false
    | Transition, Cool -> false
    | Heat, Result x9 -> false
    | Result x9, Heat -> false
    | Heat, Macro -> false
    | Macro, Heat -> false
    | Heat, Owise -> false
    | Owise, Heat -> false
    | Heat, Structural -> false
    | Structural, Heat -> false
    | Heat, Anywhere -> false
    | Anywhere, Heat -> false
    | Heat, Transition -> false
    | Transition, Heat -> false
    | Heat, Cool -> false
    | Cool, Heat -> false
    | Attr x1, Result x9 -> false
    | Result x9, Attr x1 -> false
    | Attr x1, Macro -> false
    | Macro, Attr x1 -> false
    | Attr x1, Owise -> false
    | Owise, Attr x1 -> false
    | Attr x1, Structural -> false
    | Structural, Attr x1 -> false
    | Attr x1, Anywhere -> false
    | Anywhere, Attr x1 -> false
    | Attr x1, Transition -> false
    | Transition, Attr x1 -> false
    | Attr x1, Cool -> false
    | Cool, Attr x1 -> false
    | Attr x1, Heat -> false
    | Heat, Attr x1 -> false
    | Result x9, Result y9 -> equal_sorta _B x9 y9
    | Attr x1, Attr y1 -> eq _A x1 y1
    | Macro, Macro -> true
    | Owise, Owise -> true
    | Structural, Structural -> true
    | Anywhere, Anywhere -> true
    | Transition, Transition -> true
    | Cool, Cool -> true
    | Heat, Heat -> true;;

let rec equal_ruleAttrib _A _B =
  ({equal = equal_ruleAttriba _A _B} : ('a, 'b) ruleAttrib equal);;

let rec equal_kRule _A _B _C
  x0 x1 = match x0, x1 with
    MapRule (x151, x152), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), MapRule (x151, x152) -> false
    | SetRuleWithCon (x141, x142, x143), MapRuleWithCon (x161, x162, x163) ->
        false
    | MapRuleWithCon (x161, x162, x163), SetRuleWithCon (x141, x142, x143) ->
        false
    | SetRuleWithCon (x141, x142, x143), MapRule (x151, x152) -> false
    | MapRule (x151, x152), SetRuleWithCon (x141, x142, x143) -> false
    | SetRule (x131, x132), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), SetRule (x131, x132) -> false
    | SetRule (x131, x132), MapRule (x151, x152) -> false
    | MapRule (x151, x152), SetRule (x131, x132) -> false
    | SetRule (x131, x132), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), SetRule (x131, x132) -> false
    | ListRuleWithCon (x121, x122, x123), MapRuleWithCon (x161, x162, x163) ->
        false
    | MapRuleWithCon (x161, x162, x163), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), MapRule (x151, x152) -> false
    | MapRule (x151, x152), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), SetRuleWithCon (x141, x142, x143) ->
        false
    | SetRuleWithCon (x141, x142, x143), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), SetRule (x131, x132) -> false
    | SetRule (x131, x132), ListRuleWithCon (x121, x122, x123) -> false
    | ListRule (x111, x112), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), ListRule (x111, x112) -> false
    | ListRule (x111, x112), MapRule (x151, x152) -> false
    | MapRule (x151, x152), ListRule (x111, x112) -> false
    | ListRule (x111, x112), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), ListRule (x111, x112) -> false
    | ListRule (x111, x112), SetRule (x131, x132) -> false
    | SetRule (x131, x132), ListRule (x111, x112) -> false
    | ListRule (x111, x112), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), ListRule (x111, x112) -> false
    | BagRuleWithCon (x101, x102, x103), MapRuleWithCon (x161, x162, x163) ->
        false
    | MapRuleWithCon (x161, x162, x163), BagRuleWithCon (x101, x102, x103) ->
        false
    | BagRuleWithCon (x101, x102, x103), MapRule (x151, x152) -> false
    | MapRule (x151, x152), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), SetRuleWithCon (x141, x142, x143) ->
        false
    | SetRuleWithCon (x141, x142, x143), BagRuleWithCon (x101, x102, x103) ->
        false
    | BagRuleWithCon (x101, x102, x103), SetRule (x131, x132) -> false
    | SetRule (x131, x132), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), BagRuleWithCon (x101, x102, x103) ->
        false
    | BagRuleWithCon (x101, x102, x103), ListRule (x111, x112) -> false
    | ListRule (x111, x112), BagRuleWithCon (x101, x102, x103) -> false
    | BagRule (x91, x92), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), BagRule (x91, x92) -> false
    | BagRule (x91, x92), MapRule (x151, x152) -> false
    | MapRule (x151, x152), BagRule (x91, x92) -> false
    | BagRule (x91, x92), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), BagRule (x91, x92) -> false
    | BagRule (x91, x92), SetRule (x131, x132) -> false
    | SetRule (x131, x132), BagRule (x91, x92) -> false
    | BagRule (x91, x92), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), BagRule (x91, x92) -> false
    | BagRule (x91, x92), ListRule (x111, x112) -> false
    | ListRule (x111, x112), BagRule (x91, x92) -> false
    | BagRule (x91, x92), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), BagRule (x91, x92) -> false
    | KLabelRuleWithCon (x81, x82, x83), MapRuleWithCon (x161, x162, x163) ->
        false
    | MapRuleWithCon (x161, x162, x163), KLabelRuleWithCon (x81, x82, x83) ->
        false
    | KLabelRuleWithCon (x81, x82, x83), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), SetRuleWithCon (x141, x142, x143) ->
        false
    | SetRuleWithCon (x141, x142, x143), KLabelRuleWithCon (x81, x82, x83) ->
        false
    | KLabelRuleWithCon (x81, x82, x83), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), KLabelRuleWithCon (x81, x82, x83) ->
        false
    | KLabelRuleWithCon (x81, x82, x83), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), BagRuleWithCon (x101, x102, x103) ->
        false
    | BagRuleWithCon (x101, x102, x103), KLabelRuleWithCon (x81, x82, x83) ->
        false
    | KLabelRuleWithCon (x81, x82, x83), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRule (x71, x72), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), KLabelRule (x71, x72) -> false
    | KItemRuleWithCon (x61, x62, x63), MapRuleWithCon (x161, x162, x163) ->
        false
    | MapRuleWithCon (x161, x162, x163), KItemRuleWithCon (x61, x62, x63) ->
        false
    | KItemRuleWithCon (x61, x62, x63), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), SetRuleWithCon (x141, x142, x143) ->
        false
    | SetRuleWithCon (x141, x142, x143), KItemRuleWithCon (x61, x62, x63) ->
        false
    | KItemRuleWithCon (x61, x62, x63), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), KItemRuleWithCon (x61, x62, x63) ->
        false
    | KItemRuleWithCon (x61, x62, x63), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), BagRuleWithCon (x101, x102, x103) ->
        false
    | BagRuleWithCon (x101, x102, x103), KItemRuleWithCon (x61, x62, x63) ->
        false
    | KItemRuleWithCon (x61, x62, x63), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), KLabelRuleWithCon (x81, x82, x83) ->
        false
    | KLabelRuleWithCon (x81, x82, x83), KItemRuleWithCon (x61, x62, x63) ->
        false
    | KItemRuleWithCon (x61, x62, x63), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRule (x51, x52), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), KItemRule (x51, x52) -> false
    | KRuleWithCon (x41, x42, x43), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), KRuleWithCon (x41, x42, x43) -> false
    | KRule (x31, x32), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), KRule (x31, x32) -> false
    | KRule (x31, x32), MapRule (x151, x152) -> false
    | MapRule (x151, x152), KRule (x31, x32) -> false
    | KRule (x31, x32), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), KRule (x31, x32) -> false
    | KRule (x31, x32), SetRule (x131, x132) -> false
    | SetRule (x131, x132), KRule (x31, x32) -> false
    | KRule (x31, x32), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), KRule (x31, x32) -> false
    | KRule (x31, x32), ListRule (x111, x112) -> false
    | ListRule (x111, x112), KRule (x31, x32) -> false
    | KRule (x31, x32), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), KRule (x31, x32) -> false
    | KRule (x31, x32), BagRule (x91, x92) -> false
    | BagRule (x91, x92), KRule (x31, x32) -> false
    | KRule (x31, x32), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), KRule (x31, x32) -> false
    | KRule (x31, x32), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), KRule (x31, x32) -> false
    | KRule (x31, x32), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), KRule (x31, x32) -> false
    | KRule (x31, x32), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), KRule (x31, x32) -> false
    | KRule (x31, x32), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), KRule (x31, x32) -> false
    | ContextWithCon (x21, x22, x23), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), MapRule (x151, x152) -> false
    | MapRule (x151, x152), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), SetRule (x131, x132) -> false
    | SetRule (x131, x132), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), ListRuleWithCon (x121, x122, x123) ->
        false
    | ListRuleWithCon (x121, x122, x123), ContextWithCon (x21, x22, x23) ->
        false
    | ContextWithCon (x21, x22, x23), ListRule (x111, x112) -> false
    | ListRule (x111, x112), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), BagRule (x91, x92) -> false
    | BagRule (x91, x92), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), KRule (x31, x32) -> false
    | KRule (x31, x32), ContextWithCon (x21, x22, x23) -> false
    | Context (x11, x12), MapRuleWithCon (x161, x162, x163) -> false
    | MapRuleWithCon (x161, x162, x163), Context (x11, x12) -> false
    | Context (x11, x12), MapRule (x151, x152) -> false
    | MapRule (x151, x152), Context (x11, x12) -> false
    | Context (x11, x12), SetRuleWithCon (x141, x142, x143) -> false
    | SetRuleWithCon (x141, x142, x143), Context (x11, x12) -> false
    | Context (x11, x12), SetRule (x131, x132) -> false
    | SetRule (x131, x132), Context (x11, x12) -> false
    | Context (x11, x12), ListRuleWithCon (x121, x122, x123) -> false
    | ListRuleWithCon (x121, x122, x123), Context (x11, x12) -> false
    | Context (x11, x12), ListRule (x111, x112) -> false
    | ListRule (x111, x112), Context (x11, x12) -> false
    | Context (x11, x12), BagRuleWithCon (x101, x102, x103) -> false
    | BagRuleWithCon (x101, x102, x103), Context (x11, x12) -> false
    | Context (x11, x12), BagRule (x91, x92) -> false
    | BagRule (x91, x92), Context (x11, x12) -> false
    | Context (x11, x12), KLabelRuleWithCon (x81, x82, x83) -> false
    | KLabelRuleWithCon (x81, x82, x83), Context (x11, x12) -> false
    | Context (x11, x12), KLabelRule (x71, x72) -> false
    | KLabelRule (x71, x72), Context (x11, x12) -> false
    | Context (x11, x12), KItemRuleWithCon (x61, x62, x63) -> false
    | KItemRuleWithCon (x61, x62, x63), Context (x11, x12) -> false
    | Context (x11, x12), KItemRule (x51, x52) -> false
    | KItemRule (x51, x52), Context (x11, x12) -> false
    | Context (x11, x12), KRuleWithCon (x41, x42, x43) -> false
    | KRuleWithCon (x41, x42, x43), Context (x11, x12) -> false
    | Context (x11, x12), KRule (x31, x32) -> false
    | KRule (x31, x32), Context (x11, x12) -> false
    | Context (x11, x12), ContextWithCon (x21, x22, x23) -> false
    | ContextWithCon (x21, x22, x23), Context (x11, x12) -> false
    | MapRuleWithCon (x161, x162, x163), MapRuleWithCon (y161, y162, y163) ->
        equal_rewrite (equal_theMap _A _B _C) x161 y161 &&
          (equal_kItema _A _B _C x162 y162 &&
            equal_lista (equal_ruleAttrib _B _A) x163 y163)
    | MapRule (x151, x152), MapRule (y151, y152) ->
        equal_rewrite (equal_theMap _A _B _C) x151 y151 &&
          equal_lista (equal_ruleAttrib _B _A) x152 y152
    | SetRuleWithCon (x141, x142, x143), SetRuleWithCon (y141, y142, y143) ->
        equal_rewrite (equal_theSet _A _B _C) x141 y141 &&
          (equal_kItema _A _B _C x142 y142 &&
            equal_lista (equal_ruleAttrib _B _A) x143 y143)
    | SetRule (x131, x132), SetRule (y131, y132) ->
        equal_rewrite (equal_theSet _A _B _C) x131 y131 &&
          equal_lista (equal_ruleAttrib _B _A) x132 y132
    | ListRuleWithCon (x121, x122, x123), ListRuleWithCon (y121, y122, y123) ->
        equal_rewrite (equal_theList _A _B _C) x121 y121 &&
          (equal_kItema _A _B _C x122 y122 &&
            equal_lista (equal_ruleAttrib _B _A) x123 y123)
    | ListRule (x111, x112), ListRule (y111, y112) ->
        equal_rewrite (equal_theList _A _B _C) x111 y111 &&
          equal_lista (equal_ruleAttrib _B _A) x112 y112
    | BagRuleWithCon (x101, x102, x103), BagRuleWithCon (y101, y102, y103) ->
        equal_rewrite (equal_bag _A _B _C) x101 y101 &&
          (equal_kItema _A _B _C x102 y102 &&
            equal_lista (equal_ruleAttrib _B _A) x103 y103)
    | BagRule (x91, x92), BagRule (y91, y92) ->
        equal_rewrite (equal_bag _A _B _C) x91 y91 &&
          equal_lista (equal_ruleAttrib _B _A) x92 y92
    | KLabelRuleWithCon (x81, x82, x83), KLabelRuleWithCon (y81, y82, y83) ->
        equal_rewrite (equal_kLabel _A _B _C) x81 y81 &&
          (equal_kItema _A _B _C x82 y82 &&
            equal_lista (equal_ruleAttrib _B _A) x83 y83)
    | KLabelRule (x71, x72), KLabelRule (y71, y72) ->
        equal_rewrite (equal_kLabel _A _B _C) x71 y71 &&
          equal_lista (equal_ruleAttrib _B _A) x72 y72
    | KItemRuleWithCon (x61, x62, x63), KItemRuleWithCon (y61, y62, y63) ->
        equal_rewrite (equal_kItem _A _B _C) x61 y61 &&
          (equal_kItema _A _B _C x62 y62 &&
            equal_lista (equal_ruleAttrib _B _A) x63 y63)
    | KItemRule (x51, x52), KItemRule (y51, y52) ->
        equal_rewrite (equal_kItem _A _B _C) x51 y51 &&
          equal_lista (equal_ruleAttrib _B _A) x52 y52
    | KRuleWithCon (x41, x42, x43), KRuleWithCon (y41, y42, y43) ->
        equal_rewrite (equal_k _A _B _C) x41 y41 &&
          (equal_kItema _A _B _C x42 y42 &&
            equal_lista (equal_ruleAttrib _B _A) x43 y43)
    | KRule (x31, x32), KRule (y31, y32) ->
        equal_rewrite (equal_k _A _B _C) x31 y31 &&
          equal_lista (equal_ruleAttrib _B _A) x32 y32
    | ContextWithCon (x21, x22, x23), ContextWithCon (y21, y22, y23) ->
        equal_kItema _A _B _C x21 y21 &&
          (equal_kItema _A _B _C x22 y22 &&
            equal_lista (equal_ruleAttrib _B _A) x23 y23)
    | Context (x11, x12), Context (y11, y12) ->
        equal_kItema _A _B _C x11 y11 &&
          equal_lista (equal_ruleAttrib _B _A) x12 y12;;

let rec equal_kModuleItema _A _B _C _D
  x0 x1 = match x0, x1 with TheConfiguration x3, TheRule x4 -> false
    | TheRule x4, TheConfiguration x3 -> false
    | Imports x2, TheRule x4 -> false
    | TheRule x4, Imports x2 -> false
    | Imports x2, TheConfiguration x3 -> false
    | TheConfiguration x3, Imports x2 -> false
    | TheSyntax x1, TheRule x4 -> false
    | TheRule x4, TheSyntax x1 -> false
    | TheSyntax x1, TheConfiguration x3 -> false
    | TheConfiguration x3, TheSyntax x1 -> false
    | TheSyntax x1, Imports x2 -> false
    | Imports x2, TheSyntax x1 -> false
    | TheRule x4, TheRule y4 -> equal_kRule _A _B _D x4 y4
    | TheConfiguration x3, TheConfiguration y3 -> equal_baga _A _B _D x3 y3
    | Imports x2, Imports y2 -> eq _C x2 y2
    | TheSyntax x1, TheSyntax y1 -> equal_kSyntaxa _A x1 y1;;

let rec equal_kModuleItem _A _B _C _D =
  ({equal = equal_kModuleItema _A _B _C _D} :
    ('a, 'b, 'c, 'd) kModuleItem equal);;

let rec equal_kModule _A _B _C _D
  (Module (x1, x2)) (Module (y1, y2)) =
    eq _C x1 y1 && equal_lista (equal_kModuleItem _A _B _C _D) x2 y2;;

type ('a, 'b, 'c, 'd) kFileItem = TheModule of ('a, 'b, 'c, 'd) kModule |
  TheRequires of kRequire;;

let rec equal_kFileItema _A _B _C _D
  x0 x1 = match x0, x1 with TheModule x1, TheRequires x2 -> false
    | TheRequires x2, TheModule x1 -> false
    | TheRequires x2, TheRequires y2 -> equal_kRequire x2 y2
    | TheModule x1, TheModule y1 -> equal_kModule _A _B _C _D x1 y1;;

let rec equal_kFileItem _A _B _C _D =
  ({equal = equal_kFileItema _A _B _C _D} : ('a, 'b, 'c, 'd) kFileItem equal);;

type 'a set = Set of 'a list | Coset of 'a list;;

type 'a seq = Empty | Insert of 'a * 'a pred | Join of 'a pred * 'a seq
and 'a pred = Seq of (unit -> 'a seq);;

type ('a, 'b, 'c, 'd) kFile = TheFile of ('a, 'b, 'c, 'd) kFileItem nelist;;

type 'a state = Continue of 'a | Stop of 'a | Div of 'a;;

type atoken = AChar of char | LBr | RBr | To | TheStar | Plus | OneOrMore;;

type ('a, 'b) oneStep = Success of 'a | Failure of 'b;;

type ruleLabel = FunTrans | AnywhereTrans | NormalTrans;;

type 'a kItemSyntax = SingleTon of 'a | SetTon of ('a -> bool);;

type ruleInString = ARule of char list | AContext of char list |
  AConfi of char list;;

type 'a theoryParsed =
  Parsed of ('a sort * ('a kSyntax list) list) list * ruleInString list;;

let rec eval _A (Seq f) = memberb _A (f ())
and memberb _A xa0 x = match xa0, x with Empty, x -> false
                 | Insert (y, p), x -> eq _A x y || eval _A p x
                 | Join (p, xq), x -> eval _A p x || memberb _A xq x;;

let rec holds p = eval equal_unit p ();;

let rec equal_kFile _A _B _C _D
  (TheFile x) (TheFile ya) = equal_nelist (equal_kFileItem _A _B _C _D) x ya;;

let rec sup_pred
  (Seq f) (Seq g) =
    Seq (fun _ ->
          (match f () with Empty -> g ()
            | Insert (x, p) -> Insert (x, sup_pred p (Seq g))
            | Join (p, xq) -> adjunct (Seq g) (Join (p, xq))))
and adjunct p x1 = match p, x1 with p, Empty -> Join (p, Empty)
              | p, Insert (x, q) -> Insert (x, sup_pred q p)
              | p, Join (q, xq) -> Join (q, adjunct p xq);;

let bot_pred : 'a pred = Seq (fun _ -> Empty);;

let rec getSUKLabelMeaning
  x = (match x with SUKLabel a -> Some a | SUIdKLabel _ -> None
        | SUKLabelFun (_, _) -> None);;

let rec getKLabelInSUKItem
  a = (match a with SUKItem (aa, _, _) -> getSUKLabelMeaning aa
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None);;

let rec getValueInMatchingMap _A
  a x1 = match a, x1 with a, [] -> None
    | a, b :: l ->
        (let (x, y) = b in
          (if eq _A a x then Some y else getValueInMatchingMap _A a l));;

let rec substitutionInSUKLabel _C
  x0 acc = match x0, acc with SUKLabel a, acc -> Some (SUKLabel a)
    | SUIdKLabel a, acc ->
        (match getValueInMatchingMap (equal_metaVar _C) a acc with None -> None
          | Some aa ->
            (match aa with KLabelSubs ab -> Some ab | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
    | SUKLabelFun (a, b), acc ->
        (match (substitutionInSUKLabel _C a acc, substitutionInSUKList _C b acc)
          with (None, _) -> None | (Some _, None) -> None
          | (Some x, Some y) -> Some (SUKLabelFun (x, y)))
and substitutionInSUBigKWithLabel _C
  x0 acc = match x0, acc with
    SUBigBag a, acc ->
      (match substitutionInSUBigKWithBag _C a acc with None -> None
        | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, acc ->
        (match substitutionInSUKLabel _C a acc with None -> None
          | Some aa -> Some (SUBigLabel aa))
and substitutionInSUKList _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemKl x ->
            (match substitutionInSUBigKWithLabel _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUKList _C l acc with None -> None
                  | Some la -> Some (ItemKl xa :: la)))
          | IdKl x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None
              | Some (KListSubs xa) ->
                (match substitutionInSUKList _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs _) -> None))
and substitutionInSUKItem _C
  x0 acc = match x0, acc with
    SUKItem (l, r, ty), acc ->
      (match (substitutionInSUKLabel _C l acc, substitutionInSUKList _C r acc)
        with (None, _) -> None | (Some _, None) -> None
        | (Some x, Some y) -> Some (SUKItem (x, y, ty)))
    | SUHOLE a, acc -> Some (SUHOLE a)
    | SUIdKItem (a, b), acc ->
        (match getValueInMatchingMap (equal_metaVar _C) a acc with None -> None
          | Some aa ->
            (match aa with KLabelSubs _ -> None | KItemSubs ab -> Some ab
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
and substitutionInSUK _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemFactor x ->
            (match substitutionInSUKItem _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUK _C l acc with None -> None
                  | Some la -> Some (ItemFactor xa :: la)))
          | IdFactor x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs xa) ->
                (match substitutionInSUK _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (ListSubs _) -> None | Some (SetSubs _) -> None
              | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
          | SUKKItem (x, y, ty) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUK _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUKKItem (xa, ya, ty) :: la)))
and substitutionInSUMap _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemM (x, y) ->
            (match
              (substitutionInSUK _C x acc,
                (substitutionInSUK _C y acc, substitutionInSUMap _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) -> Some (ItemM (xa, ya) :: la))
          | IdM x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None
              | Some (MapSubs xa) ->
                (match substitutionInSUMap _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (BagSubs _) -> None)
          | SUMapKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUMap _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUMapKItem (xa, ya) :: la)))
and substitutionInSUSet _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemS x ->
            (match substitutionInSUK _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUSet _C l acc with None -> None
                  | Some la -> Some (ItemS xa :: la)))
          | IdS x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs xa) ->
                (match substitutionInSUSet _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (MapSubs _) -> None | Some (BagSubs _) -> None)
          | SUSetKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUSet _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUSetKItem (xa, ya) :: la)))
and substitutionInSUList _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemL x ->
            (match substitutionInSUK _C x acc with None -> None
              | Some xa ->
                (match substitutionInSUList _C l acc with None -> None
                  | Some la -> Some (ItemL xa :: la)))
          | IdL x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None
              | Some (ListSubs xa) ->
                (match substitutionInSUList _C l acc with None -> None
                  | Some la -> Some (xa @ la))
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs _) -> None)
          | SUListKItem (x, y) ->
            (match
              (substitutionInSUKLabel _C x acc,
                (substitutionInSUKList _C y acc, substitutionInSUList _C l acc))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUListKItem (xa, ya) :: la)))
and substitutionInSUBigKWithBag _C
  x0 acc = match x0, acc with
    SUK a, acc ->
      (match substitutionInSUK _C a acc with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, acc ->
        (match substitutionInSUList _C a acc with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, acc ->
        (match substitutionInSUSet _C a acc with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, acc ->
        (match substitutionInSUMap _C a acc with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, acc ->
        (match substitutionInSUBag _C a acc with None -> None
          | Some aa -> Some (SUBag aa))
and substitutionInSUBag _C
  x0 acc = match x0, acc with [], acc -> Some []
    | b :: l, acc ->
        (match b
          with ItemB (x, y, z) ->
            (match substitutionInSUBigKWithBag _C z acc with None -> None
              | Some za ->
                (match substitutionInSUBag _C l acc with None -> None
                  | Some la -> Some (ItemB (x, y, za) :: la)))
          | IdB x ->
            (match getValueInMatchingMap (equal_metaVar _C) x acc
              with None -> None | Some (KLabelSubs _) -> None
              | Some (KItemSubs _) -> None | Some (KListSubs _) -> None
              | Some (KSubs _) -> None | Some (ListSubs _) -> None
              | Some (SetSubs _) -> None | Some (MapSubs _) -> None
              | Some (BagSubs xa) ->
                (match substitutionInSUBag _C l acc with None -> None
                  | Some la -> Some (xa @ la))));;

let rec substitutionInSubsFactor _C
  x0 acc = match x0, acc with
    KLabelSubs a, acc ->
      (match substitutionInSUKLabel _C a acc with None -> None
        | Some aa -> Some (KLabelSubs aa))
    | KItemSubs a, acc ->
        (match substitutionInSUKItem _C a acc with None -> None
          | Some aa -> Some (KItemSubs aa))
    | KListSubs a, acc ->
        (match substitutionInSUKList _C a acc with None -> None
          | Some aa -> Some (KListSubs aa))
    | KSubs a, acc ->
        (match substitutionInSUK _C a acc with None -> None
          | Some aa -> Some (KSubs aa))
    | ListSubs a, acc ->
        (match substitutionInSUList _C a acc with None -> None
          | Some aa -> Some (ListSubs aa))
    | SetSubs a, acc ->
        (match substitutionInSUSet _C a acc with None -> None
          | Some aa -> Some (SetSubs aa))
    | MapSubs a, acc ->
        (match substitutionInSUMap _C a acc with None -> None
          | Some aa -> Some (MapSubs aa))
    | BagSubs a, acc ->
        (match substitutionInSUBag _C a acc with None -> None
          | Some aa -> Some (BagSubs aa));;

let rec searchDataBaseByKey _A
  xa0 x = match xa0, x with [], x -> None
    | (x, y) :: l, a ->
        (if eq _A x a then Some y else searchDataBaseByKey _A l a);;

let rec deleteDataBaseByKey _A
  xa0 x = match xa0, x with [], x -> []
    | (x, y) :: l, a ->
        (if eq _A x a then l else (x, y) :: deleteDataBaseByKey _A l a);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec subsortAux _A
  a b s = match a, b, s with a, b, [] -> false
    | a, b, s ->
        (match searchDataBaseByKey _A s b with None -> false
          | Some l ->
            (if membera _A l a then true
              else subsortInList _A a l (deleteDataBaseByKey _A s b)))
and subsortInList _A
  a x1 s = match a, x1, s with a, [], s -> false
    | a, b :: l, s -> subsortAux _A a b s || subsortInList _A a l s;;

let rec subsort _A
  a b subG = (if eq _A a b then true else subsortAux _A a b subG);;

let rec insertSortInList _A
  a x1 subG = match a, x1, subG with a, [], subG -> [a]
    | a, b :: l, subG ->
        (if subsort _A a b subG then b :: l
          else (if subsort _A b a subG then insertSortInList _A a l subG
                 else b :: insertSortInList _A a l subG));;

let rec insertAllSortsInList _A
  x0 l subG = match x0, l, subG with [], l, subG -> l
    | x :: l, s, subG ->
        insertAllSortsInList _A l (insertSortInList _A x s subG) subG;;

let rec getValueTerm _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (a, b) :: l -> (if eq _A aa a then Some b else getValueTerm _A aa l);;

let rec getMaxSorts _A
  a x1 subG checked acc = match a, x1, subG, checked, acc with
    a, [], subG, checked, acc -> acc
    | a, c :: l, subG, checked, acc ->
        (if subsort _A c a subG
          then getMaxSorts _A a l subG (c :: checked)
                 (insertSortInList _A c acc subG)
          else (if membera _A checked c then getMaxSorts _A a l subG checked acc
                 else (match getValueTerm _A c subG
                        with None -> getMaxSorts _A a l subG (c :: checked) acc
                        | Some newl ->
                          getMaxSorts _A a l subG (c :: checked)
                            (getMaxSorts _A a newl subG (c :: checked) acc))));;

let rec meetAux _A
  a x1 subG = match a, x1, subG with a, [], subG -> []
    | a, x :: l, subG ->
        (if subsort _A a x subG
          then insertSortInList _A a (meetAux _A a l subG) subG
          else (if subsort _A x a subG
                 then insertSortInList _A x (meetAux _A a l subG) subG
                 else (match getValueTerm _A x subG
                        with None -> meetAux _A a l subG
                        | Some newl ->
                          insertAllSortsInList _A
                            (getMaxSorts _A a newl subG [x] [])
                            (meetAux _A a l subG) subG)));;

let rec meet _A
  x0 b subG = match x0, b, subG with [], b, subG -> []
    | x :: l, b, subG ->
        insertAllSortsInList _A (meetAux _A x b subG) (meet _A l b subG) subG;;

let rec syntacticMonoidInSUKLabel _A _B _C
  x0 s subG = match x0, s, subG with
    SUKLabel a, s, subG ->
      (match s
        with SUKLabel aa ->
          (if equal_labela _A a aa then Some (SUKLabel a) else None)
        | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None)
    | SUIdKLabel a, b, subG ->
        (match b with SUKLabel _ -> None
          | SUIdKLabel aa ->
            (if equal_metaVara _C a aa then Some (SUIdKLabel a) else None)
          | SUKLabelFun (_, _) -> None)
    | SUKLabelFun (a, ba), b, subG ->
        (match b with SUKLabel _ -> None | SUIdKLabel _ -> None
          | SUKLabelFun (aa, bb) ->
            (match syntacticMonoidInSUKLabel _A _B _C a aa subG
              with None -> None
              | Some a1 ->
                (match syntacticMonoidInSUKList _A _B _C ba bb subG
                  with None -> None
                  | Some baa -> Some (SUKLabelFun (a1, baa)))))
and syntacticMonoidInSUBigKWithLabel _A _B _C
  x0 b subG = match x0, b, subG with
    SUBigBag a, b, subG ->
      (match b
        with SUBigBag aa ->
          (match syntacticMonoidInSUBigKWithBag _A _B _C a aa subG
            with None -> None | Some aaa -> Some (SUBigBag aaa))
        | SUBigLabel _ -> None)
    | SUBigLabel a, b, subG ->
        (match b with SUBigBag _ -> None
          | SUBigLabel aa ->
            (match syntacticMonoidInSUKLabel _A _B _C a aa subG
              with None -> None | Some aaa -> Some (SUBigLabel aaa)))
and syntacticMonoidInSUKList _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemKl bs, ItemKl bsa) ->
                (match syntacticMonoidInSUBigKWithLabel _A _B _C bs bsa subG
                  with None -> None
                  | Some bsaa ->
                    (match syntacticMonoidInSUKList _A _B _C l la subG
                      with None -> None
                      | Some laa -> Some (ItemKl bsaa :: laa)))
              | (ItemKl _, IdKl _) -> None | (IdKl _, ItemKl _) -> None
              | (IdKl x, IdKl xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUKList _A _B _C l la subG
                         with None -> None | Some laa -> Some (IdKl x :: laa))
                  else None)))
and syntacticMonoidInSUKItem _A _B _C
  x0 s subG = match x0, s, subG with
    SUKItem (l, r, ty), s, subG ->
      (match s
        with SUKItem (la, ra, tya) ->
          (match
            (syntacticMonoidInSUKLabel _A _B _C l la subG,
              syntacticMonoidInSUKList _A _B _C r ra subG)
            with (None, _) -> None | (Some _, None) -> None
            | (Some laa, Some raa) ->
              (match meet (equal_sort _A) ty tya subG with [] -> None
                | x :: xl -> Some (SUKItem (laa, raa, x :: xl))))
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None)
    | SUHOLE a, s, subG ->
        (match s with SUKItem (_, _, _) -> None | SUIdKItem (_, _) -> None
          | SUHOLE aa ->
            (match meet (equal_sort _A) a aa subG with [] -> None
              | x :: xl -> Some (SUHOLE (x :: xl))))
    | SUIdKItem (a, ba), b, subG ->
        (match b with SUKItem (_, _, _) -> None
          | SUIdKItem (aa, bb) ->
            (if equal_metaVara _C a aa
              then (match meet (equal_sort _A) ba bb subG with [] -> None
                     | x :: xl -> Some (SUIdKItem (a, x :: xl)))
              else None)
          | SUHOLE _ -> None)
and syntacticMonoidInSUK _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemFactor (SUKItem (suKLabel, list1, list2)), ItemFactor x)
                -> (match
                     (syntacticMonoidInSUKItem _A _B _C
                        (SUKItem (suKLabel, list1, list2)) x subG,
                       syntacticMonoidInSUK _A _B _C l la subG)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUKItem (_, _, _)), IdFactor _) -> None
              | (ItemFactor (SUKItem (_, _, _)), SUKKItem (_, _, _)) -> None
              | (ItemFactor (SUIdKItem (metaVar, lista)), ItemFactor x) ->
                (match
                  (syntacticMonoidInSUKItem _A _B _C
                     (SUIdKItem (metaVar, lista)) x subG,
                    syntacticMonoidInSUK _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUIdKItem (metaVar, lista)), IdFactor x) ->
                (if equal_metaVara _C metaVar x
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa ->
                           Some (ItemFactor (SUIdKItem (metaVar, lista)) ::
                                  laa))
                  else None)
              | (ItemFactor (SUIdKItem (_, _)), SUKKItem (_, _, _)) -> None
              | (ItemFactor (SUHOLE lista), ItemFactor x) ->
                (match
                  (syntacticMonoidInSUKItem _A _B _C (SUHOLE lista) x subG,
                    syntacticMonoidInSUK _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xa, Some laa) -> Some (ItemFactor xa :: laa))
              | (ItemFactor (SUHOLE _), IdFactor _) -> None
              | (ItemFactor (SUHOLE _), SUKKItem (_, _, _)) -> None
              | (IdFactor _, ItemFactor (SUKItem (_, _, _))) -> None
              | (IdFactor x, ItemFactor (SUIdKItem (xa, ty))) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa ->
                           Some (ItemFactor (SUIdKItem (xa, ty)) :: laa))
                  else None)
              | (IdFactor _, ItemFactor (SUHOLE _)) -> None
              | (IdFactor x, IdFactor xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUK _A _B _C l la subG
                         with None -> None
                         | Some laa -> Some (IdFactor x :: laa))
                  else None)
              | (IdFactor _, SUKKItem (_, _, _)) -> None
              | (SUKKItem (_, _, _), ItemFactor _) -> None
              | (SUKKItem (_, _, _), IdFactor _) -> None
              | (SUKKItem (x, y, ty), SUKKItem (xa, ya, tya)) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    (syntacticMonoidInSUKList _A _B _C y ya subG,
                      syntacticMonoidInSUK _A _B _C l la subG))
                  with (None, _) -> None | (Some _, (None, _)) -> None
                  | (Some _, (Some _, None)) -> None
                  | (Some xaa, (Some yaa, Some laa)) ->
                    (match meet (equal_sort _A) ty tya subG with [] -> None
                      | newTy :: newTyl ->
                        Some (SUKKItem (xaa, yaa, newTy :: newTyl) :: laa)))))
and syntacticMonoidInSUList _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match s with [] -> None
          | ba :: la ->
            (match (b, ba)
              with (ItemL x, ItemL xa) ->
                (match
                  (syntacticMonoidInSUK _A _B _C x xa subG,
                    syntacticMonoidInSUList _A _B _C l la subG)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some xaa, Some laa) -> Some (ItemL xaa :: laa))
              | (ItemL _, IdL _) -> None | (ItemL _, SUListKItem (_, _)) -> None
              | (IdL _, ItemL _) -> None
              | (IdL x, IdL xa) ->
                (if equal_metaVara _C x xa
                  then (match syntacticMonoidInSUList _A _B _C l la subG
                         with None -> None | Some laa -> Some (IdL x :: laa))
                  else None)
              | (IdL _, SUListKItem (_, _)) -> None
              | (SUListKItem (_, _), ItemL _) -> None
              | (SUListKItem (_, _), IdL _) -> None
              | (SUListKItem (x, y), SUListKItem (xa, ya)) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    (syntacticMonoidInSUKList _A _B _C y ya subG,
                      syntacticMonoidInSUList _A _B _C l la subG))
                  with (None, _) -> None | (Some _, (None, _)) -> None
                  | (Some _, (Some _, None)) -> None
                  | (Some xaa, (Some yaa, Some laa)) ->
                    Some (SUListKItem (xaa, yaa) :: laa))))
and syntacticMonoidInSUMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemS x, ItemS xa) ->
            (match syntacticMonoidInSUK _A _B _C xa x subG
              with None -> syntacticMonoidInSUMember _A _B _C ba l subG
              | Some xaa -> Some (ItemS xaa))
          | (ItemS _, IdS _) -> None | (ItemS _, SUSetKItem (_, _)) -> None
          | (IdS _, ItemS _) -> None
          | (IdS x, IdS xa) ->
            (if equal_metaVara _C x xa then Some (IdS x)
              else syntacticMonoidInSUMember _A _B _C ba l subG)
          | (IdS _, SUSetKItem (_, _)) -> None
          | (SUSetKItem (_, _), ItemS _) -> None
          | (SUSetKItem (_, _), IdS _) -> None
          | (SUSetKItem (x, y), SUSetKItem (xa, ya)) ->
            (match
              (syntacticMonoidInSUKLabel _A _B _C xa x subG,
                syntacticMonoidInSUKList _A _B _C ya y subG)
              with (None, _) -> syntacticMonoidInSUMember _A _B _C ba l subG
              | (Some _, None) -> syntacticMonoidInSUMember _A _B _C ba l subG
              | (Some xaa, Some yaa) -> Some (SUSetKItem (xaa, yaa))))
and syntacticMonoidInSUSubSet _A _B _C
  x0 t subG = match x0, t, subG with [], t, subG -> Some []
    | b :: l, t, subG ->
        (match syntacticMonoidInSUMember _A _B _C b t subG with None -> None
          | Some ba ->
            (match syntacticMonoidInSUSubSet _A _B _C l t subG with None -> None
              | Some la -> Some (ba :: la)))
and syntacticMonoidInSUSet _A _B _C
  x0 s t subG = match x0, s, t, subG with
    [], s, t, subG -> syntacticMonoidInSUSubSet _A _B _C s t subG
    | b :: l, s, t, subG ->
        (match syntacticMonoidInSUMember _A _B _C b s subG with None -> None
          | Some _ -> syntacticMonoidInSUSet _A _B _C l s t subG)
and syntacticMonoidInSUMapMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemM (x, y), ItemM (xa, ya)) ->
            (match syntacticMonoidInSUK _A _B _C xa x subG
              with None -> syntacticMonoidInSUMapMember _A _B _C ba l subG
              | Some xaa ->
                (match syntacticMonoidInSUK _A _B _C ya y subG with None -> None
                  | Some yaa -> Some (ItemM (xaa, yaa))))
          | (ItemM (_, _), IdM _) -> None
          | (ItemM (_, _), SUMapKItem (_, _)) -> None
          | (IdM _, ItemM (_, _)) -> None
          | (IdM x, IdM xa) ->
            (if equal_metaVara _C x xa then Some (IdM x)
              else syntacticMonoidInSUMapMember _A _B _C ba l subG)
          | (IdM _, SUMapKItem (_, _)) -> None
          | (SUMapKItem (_, _), ItemM (_, _)) -> None
          | (SUMapKItem (_, _), IdM _) -> None
          | (SUMapKItem (x, y), SUMapKItem (xa, ya)) ->
            (match
              (syntacticMonoidInSUKLabel _A _B _C xa x subG,
                syntacticMonoidInSUKList _A _B _C ya y subG)
              with (None, _) -> syntacticMonoidInSUMapMember _A _B _C ba l subG
              | (Some _, None) ->
                syntacticMonoidInSUMapMember _A _B _C ba l subG
              | (Some xaa, Some yaa) -> Some (SUMapKItem (xaa, yaa))))
and syntacticMonoidInSUSubMap _A _B _C
  x0 t subG = match x0, t, subG with [], t, subG -> Some []
    | b :: l, t, subG ->
        (match syntacticMonoidInSUMapMember _A _B _C b t subG with None -> None
          | Some ba ->
            (match syntacticMonoidInSUSubMap _A _B _C l t subG with None -> None
              | Some la -> Some (ba :: la)))
and syntacticMonoidInSUMap _A _B _C
  x0 s t subG = match x0, s, t, subG with
    [], s, t, subG -> syntacticMonoidInSUSubMap _A _B _C s t subG
    | b :: l, s, t, subG ->
        (match syntacticMonoidInSUMapMember _A _B _C b s subG with None -> None
          | Some _ -> syntacticMonoidInSUMap _A _B _C l s t subG)
and syntacticMonoidInSUBigKWithBag _A _B _C
  x0 b subG = match x0, b, subG with
    SUK a, b, subG ->
      (match b
        with SUK aa ->
          (match syntacticMonoidInSUK _A _B _C a aa subG with None -> None
            | Some aaa -> Some (SUK aaa))
        | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
        | SUBag _ -> None)
    | SUList a, b, subG ->
        (match b with SUK _ -> None
          | SUList aa ->
            (match syntacticMonoidInSUList _A _B _C a aa subG with None -> None
              | Some aaa -> Some (SUList aaa))
          | SUSet _ -> None | SUMap _ -> None | SUBag _ -> None)
    | SUSet a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None
          | SUSet aa ->
            (match syntacticMonoidInSUSet _A _B _C a aa a subG with None -> None
              | Some aaa -> Some (SUSet aaa))
          | SUMap _ -> None | SUBag _ -> None)
    | SUMap a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap aa ->
            (match syntacticMonoidInSUMap _A _B _C a aa a subG with None -> None
              | Some aaa -> Some (SUMap aaa))
          | SUBag _ -> None)
    | SUBag a, b, subG ->
        (match b with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap _ -> None
          | SUBag aa ->
            (match syntacticMonoidInSUBag _A _B _C a aa subG with None -> None
              | Some aaa -> Some (SUBag aaa)))
and syntacticMonoidInSUBagMember _A _B _C
  b x1 subG = match b, x1, subG with b, [], subG -> None
    | ba, b :: l, subG ->
        (match (ba, b)
          with (ItemB (x, y, z), ItemB (xa, _, za)) ->
            (if equal_vara _B x xa
              then (match syntacticMonoidInSUBigKWithBag _A _B _C za z subG
                     with None -> None
                     | Some zaa -> Some (ItemB (x, y, zaa), l))
              else (match syntacticMonoidInSUBagMember _A _B _C ba l subG
                     with None -> None | Some (baa, la) -> Some (baa, b :: la)))
          | (ItemB (_, _, _), IdB _) ->
            (match syntacticMonoidInSUBagMember _A _B _C ba l subG
              with None -> None | Some (baa, la) -> Some (baa, b :: la))
          | (IdB _, ItemB (_, _, _)) ->
            (match syntacticMonoidInSUBagMember _A _B _C ba l subG
              with None -> None | Some (baa, la) -> Some (baa, b :: la))
          | (IdB x, IdB xa) ->
            (if equal_metaVara _C x xa then Some (IdB x, l)
              else (match syntacticMonoidInSUBagMember _A _B _C ba l subG
                     with None -> None
                     | Some (baa, la) -> Some (baa, IdB xa :: la))))
and syntacticMonoidInSUBag _A _B _C
  x0 s subG = match x0, s, subG with
    [], s, subG -> (match s with [] -> Some [] | _ :: _ -> None)
    | b :: l, s, subG ->
        (match syntacticMonoidInSUBagMember _A _B _C b s subG with None -> None
          | Some (ba, sa) ->
            (match syntacticMonoidInSUBag _A _B _C l sa subG with None -> None
              | Some la -> Some (ba :: la)));;

let rec macroEquality _A _B _C
  x0 x1 subG = match x0, x1, subG with
    KLabelSubs a, KLabelSubs b, subG ->
      (match syntacticMonoidInSUKLabel _A _B _C a b subG with None -> None
        | Some aa -> Some (KLabelSubs aa))
    | KItemSubs a, KItemSubs b, subG ->
        (match syntacticMonoidInSUKItem _A _B _C a b subG with None -> None
          | Some aa -> Some (KItemSubs aa))
    | KListSubs a, KListSubs b, subG ->
        (match syntacticMonoidInSUKList _A _B _C a b subG with None -> None
          | Some aa -> Some (KListSubs aa))
    | KSubs a, KSubs b, subG ->
        (match syntacticMonoidInSUK _A _B _C a b subG with None -> None
          | Some aa -> Some (KSubs aa))
    | ListSubs a, ListSubs b, subG ->
        (match syntacticMonoidInSUList _A _B _C a b subG with None -> None
          | Some aa -> Some (ListSubs aa))
    | SetSubs a, SetSubs b, subG ->
        (match syntacticMonoidInSUSet _A _B _C a b a subG with None -> None
          | Some aa -> Some (SetSubs aa))
    | MapSubs a, MapSubs b, subG ->
        (match syntacticMonoidInSUMap _A _B _C a b a subG with None -> None
          | Some aa -> Some (MapSubs aa))
    | BagSubs a, BagSubs b, subG ->
        (match syntacticMonoidInSUBag _A _B _C a b subG with None -> None
          | Some aa -> Some (BagSubs aa))
    | KItemSubs v, KLabelSubs va, subG -> None
    | KItemSubs v, KListSubs va, subG -> None
    | KItemSubs v, KSubs va, subG -> None
    | KItemSubs v, ListSubs va, subG -> None
    | KItemSubs v, SetSubs va, subG -> None
    | KItemSubs v, MapSubs va, subG -> None
    | KItemSubs v, BagSubs va, subG -> None
    | KListSubs v, KLabelSubs va, subG -> None
    | KListSubs v, KItemSubs va, subG -> None
    | KListSubs v, KSubs va, subG -> None
    | KListSubs v, ListSubs va, subG -> None
    | KListSubs v, SetSubs va, subG -> None
    | KListSubs v, MapSubs va, subG -> None
    | KListSubs v, BagSubs va, subG -> None
    | KSubs v, KLabelSubs va, subG -> None
    | KSubs v, KItemSubs va, subG -> None
    | KSubs v, KListSubs va, subG -> None
    | KSubs v, ListSubs va, subG -> None
    | KSubs v, SetSubs va, subG -> None
    | KSubs v, MapSubs va, subG -> None
    | KSubs v, BagSubs va, subG -> None
    | ListSubs v, KLabelSubs va, subG -> None
    | ListSubs v, KItemSubs va, subG -> None
    | ListSubs v, KListSubs va, subG -> None
    | ListSubs v, KSubs va, subG -> None
    | ListSubs v, SetSubs va, subG -> None
    | ListSubs v, MapSubs va, subG -> None
    | ListSubs v, BagSubs va, subG -> None
    | SetSubs v, KLabelSubs va, subG -> None
    | SetSubs v, KItemSubs va, subG -> None
    | SetSubs v, KListSubs va, subG -> None
    | SetSubs v, KSubs va, subG -> None
    | SetSubs v, ListSubs va, subG -> None
    | SetSubs v, MapSubs va, subG -> None
    | SetSubs v, BagSubs va, subG -> None
    | MapSubs v, KLabelSubs va, subG -> None
    | MapSubs v, KItemSubs va, subG -> None
    | MapSubs v, KListSubs va, subG -> None
    | MapSubs v, KSubs va, subG -> None
    | MapSubs v, ListSubs va, subG -> None
    | MapSubs v, SetSubs va, subG -> None
    | MapSubs v, BagSubs va, subG -> None
    | BagSubs v, KLabelSubs va, subG -> None
    | BagSubs v, KItemSubs va, subG -> None
    | BagSubs v, KListSubs va, subG -> None
    | BagSubs v, KSubs va, subG -> None
    | BagSubs v, ListSubs va, subG -> None
    | BagSubs v, SetSubs va, subG -> None
    | BagSubs v, MapSubs va, subG -> None
    | KLabelSubs va, KItemSubs v, subG -> None
    | KLabelSubs va, KListSubs v, subG -> None
    | KLabelSubs va, KSubs v, subG -> None
    | KLabelSubs va, ListSubs v, subG -> None
    | KLabelSubs va, SetSubs v, subG -> None
    | KLabelSubs va, MapSubs v, subG -> None
    | KLabelSubs va, BagSubs v, subG -> None;;

let rec updateMatchingMapMacro _A _B _C _D
  x y xa2 subG = match x, y, xa2, subG with x, y, [], subG -> Some [(x, y)]
    | x, y, (a, b) :: l, subG ->
        (if eq _A x a
          then (match macroEquality _B _C _D y b subG with None -> None
                 | Some ya -> Some ((a, ya) :: l))
          else (match updateMatchingMapMacro _A _B _C _D x y l subG
                 with None -> None | Some la -> Some ((a, b) :: la)));;

let rec patternMacroingInSUKLabel _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRKLabel a, s, acc, subG ->
      (match s
        with SUKLabel b -> (if equal_labela _A a b then Some acc else None)
        | SUIdKLabel _ -> None | SUKLabelFun (_, _) -> None)
    | IRIdKLabel a, s, acc, subG ->
        updateMatchingMapMacro (equal_metaVar _B) _A _C _D a (KLabelSubs s) acc
          subG;;

let rec subsortListAux _A
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, x :: l, subG ->
        (if subsort _A a x subG then true else subsortListAux _A a l subG);;

let rec subsortList _A
  x0 b subG = match x0, b, subG with [], b, subG -> true
    | x :: l, b, subG ->
        (if subsortListAux _A x b subG then subsortList _A l b subG
          else false);;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec rev xs = fold (fun a b -> a :: b) xs [];;

let rec searchAllNonTermsInSUSet
  = function [] -> []
    | a :: l ->
        (match a with ItemS _ -> searchAllNonTermsInSUSet l
          | IdS _ -> a :: searchAllNonTermsInSUSet l
          | SUSetKItem (_, _) -> a :: searchAllNonTermsInSUSet l);;

let rec mergePatMatchMap _A _B _C _D
  x0 s subG = match x0, s, subG with [], s, subG -> Some s
    | (a, b) :: l, s, subG ->
        (match updateMatchingMapMacro _A _B _C _D a b s subG with None -> None
          | Some sa -> mergePatMatchMap _A _B _C _D l sa subG);;

let rec mergeMapWithOnes _C _D _E _F
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some acc
    | (a, (b, c)) :: l, acc, subG ->
        (match mergePatMatchMap _C _D _E _F c acc subG with None -> None
          | Some acca -> mergeMapWithOnes _C _D _E _F l acca subG);;

let rec eliminateEntry _A
  a x1 = match a, x1 with a, [] -> []
    | a, (b, c) :: l ->
        (if eq _A a b then l else (b, c) :: eliminateEntry _A a l);;

let rec eliminateEntryList _A
  a x1 = match a, x1 with a, [] -> []
    | a, (b, c) :: l ->
        (b, eliminateEntry _A a c) :: eliminateEntryList _A a l;;

let rec eliminateEntryMap _B
  x0 s = match x0, s with [], s -> Some s
    | (a, (b, c)) :: l, s ->
        eliminateEntryMap _B l (eliminateEntryList _B b s);;

let rec searchOneAux
  = function [] -> ([], [])
    | (a, b) :: l ->
        (let (have, noHave) = searchOneAux l in
          (match b with [] -> (have, (a, b) :: noHave)
            | [ba] -> ((a, ba) :: have, noHave)
            | _ :: _ :: _ -> (have, (a, b) :: noHave)));;

let rec null = function [] -> true
               | x :: xs -> false;;

let rec searchZero
  = function [] -> ([], [])
    | (a, b) :: l ->
        (let (have, noHave) = searchZero l in
          (if null b then ((a, b) :: have, noHave)
            else (have, (a, b) :: noHave)));;

let rec searchOne _B
  l acc =
    (let (x, y) = searchZero l in
      (if null x
        then (let (u, v) = searchOneAux y in
               (if null u then Some (acc, v)
                 else (match eliminateEntryMap _B u v with None -> None
                        | Some va -> searchOne _B va (u @ acc))))
        else None));;

let rec findBijection _B
  l = (match searchOne _B l [] with None -> None
        | Some a ->
          (let (ones, aa) = a in
            (match aa with [] -> Some (ones, [])
              | (ab, b) :: al ->
                (if null al then Some (ones, b)
                  else findBijectionAux _B ab b al))))
and findBijectionAux _B
  a x1 s = match a, x1, s with a, [], s -> None
    | a, (b, c) :: al, s ->
        (match searchOne _B (eliminateEntryList _B b s) []
          with None -> findBijectionAux _B a al s
          | Some (ones, mores) ->
            (if null mores then Some ((a, (b, c)) :: ones, [])
              else (match findBijection _B mores with None -> None
                     | Some (onesa, remains) ->
                       Some ((a, (b, c)) :: ones @ onesa, remains))));;

let rec keys = function [] -> []
               | (a, b) :: l -> a :: keys l;;

let rec searchAllNonTermsInSUMap
  = function [] -> []
    | a :: l ->
        (match a with ItemM (_, _) -> searchAllNonTermsInSUMap l
          | IdM _ -> a :: searchAllNonTermsInSUMap l
          | SUMapKItem (_, _) -> a :: searchAllNonTermsInSUMap l);;

let rec searchAllNonTermsInSUBag
  = function [] -> []
    | a :: l ->
        (match a with ItemB (_, _, _) -> searchAllNonTermsInSUBag l
          | IdB _ -> a :: searchAllNonTermsInSUBag l);;

let rec patternMacroingInSUKList _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    KListPatNoVar l, s, acc, subG ->
      (match l with [] -> (match s with [] -> Some acc | _ :: _ -> None)
        | la :: ll ->
          (match s with [] -> None
            | ItemKl x :: sul ->
              (match patternMacroingInSUBigKWithLabel _A _B _C _D la x acc subG
                with None -> None
                | Some acca ->
                  (match
                    patternMacroingInSUKList _A _B _C _D (KListPatNoVar ll) sul
                      acca subG
                    with None -> None | Some a -> Some a))
            | IdKl _ :: _ -> None))
    | KListPat (l, n, r), s, acc, subG ->
        (match l
          with [] ->
            (match rev r
              with [] ->
                updateMatchingMapMacro (equal_metaVar _C) _A _B _D n
                  (KListSubs s) acc subG
              | ra :: rl ->
                (match rev s with [] -> None
                  | ItemKl x :: sul ->
                    (match
                      patternMacroingInSUBigKWithLabel _A _B _C _D ra x acc subG
                      with None -> None
                      | Some acca ->
                        (match
                          patternMacroingInSUKList _A _B _C _D
                            (KListPat (l, n, rev rl)) (rev sul) acca subG
                          with None -> None | Some a -> Some a))
                  | IdKl _ :: _ -> None))
          | la :: ll ->
            (match s with [] -> None
              | ItemKl x :: sul ->
                (match
                  patternMacroingInSUBigKWithLabel _A _B _C _D la x acc subG
                  with None -> None
                  | Some acca ->
                    (match
                      patternMacroingInSUKList _A _B _C _D (KListPat (ll, n, r))
                        sul acca subG
                      with None -> None | Some a -> Some a))
              | IdKl _ :: _ -> None))
and patternMacroingInSUKItem _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRKItem (l, r, ty), s, acc, subG ->
      (match s
        with SUKItem (la, ra, tya) ->
          (if subsortList (equal_sort _A) tya ty subG
            then (match patternMacroingInSUKLabel _A _C _B _D l la acc subG
                   with None -> None
                   | Some acca ->
                     (match patternMacroingInSUKList _A _B _C _D r ra acca subG
                       with None -> None | Some a -> Some a))
            else None)
        | SUIdKItem (_, _) -> None | SUHOLE _ -> None)
    | IRHOLE a, s, acc, subG ->
        (match s with SUKItem (_, _, _) -> None | SUIdKItem (_, _) -> None
          | SUHOLE aa ->
            (if subsortList (equal_sort _A) aa a subG then Some acc else None))
    | IRIdKItem (a, ba), b, acc, subG ->
        (match b
          with SUKItem (l, r, ty) ->
            (if subsortList (equal_sort _A) ty ba subG
              then updateMatchingMapMacro (equal_metaVar _C) _A _B _D a
                     (KItemSubs (SUKItem (l, r, ty))) acc subG
              else None)
          | SUIdKItem (aa, bb) ->
            (if subsortList (equal_sort _A) bb ba subG
              then updateMatchingMapMacro (equal_metaVar _C) _A _B _D a
                     (KItemSubs (SUIdKItem (aa, bb))) acc subG
              else None)
          | SUHOLE _ -> None)
and patternMacroingInSUK _A _B _C _D
  (KPat (l, n)) s acc subG =
    (match l
      with [] ->
        (match n with None -> (match s with [] -> Some acc | _ :: _ -> None)
          | Some v ->
            updateMatchingMapMacro (equal_metaVar _C) _A _B _D v (KSubs s) acc
              subG)
      | la :: ll ->
        (match s with [] -> None
          | ItemFactor x :: sul ->
            (match patternMacroingInSUKItem _A _B _C _D la x acc subG
              with None -> None
              | Some acca ->
                patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul acca subG)
          | IdFactor x :: sul ->
            (match la with IRKItem (_, _, _) -> None
              | IRIdKItem (xa, ty) ->
                (if equal_lista (equal_sort _A) ty [K]
                  then (match
                         updateMatchingMapMacro (equal_metaVar _C) _A _B _D xa
                           (KSubs [IdFactor x]) acc subG
                         with None -> None
                         | Some acca ->
                           patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul
                             acca subG)
                  else None)
              | IRHOLE _ -> None)
          | SUKKItem (x, y, ty) :: sul ->
            (match la with IRKItem (_, _, _) -> None
              | IRIdKItem (xa, _) ->
                (if equal_lista (equal_sort _A) ty [K]
                  then (match
                         updateMatchingMapMacro (equal_metaVar _C) _A _B _D xa
                           (KSubs [SUKKItem (x, y, ty)]) acc subG
                         with None -> None
                         | Some acca ->
                           patternMacroingInSUK _A _B _C _D (KPat (ll, n)) sul
                             acca subG)
                  else None)
              | IRHOLE _ -> None)))
and patternMacroingInSUList _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    ListPatNoVar l, s, acc, subG ->
      (match l with [] -> (match s with [] -> Some acc | _ :: _ -> None)
        | la :: ll ->
          (match s with [] -> None
            | ItemL x :: sul ->
              (match patternMacroingInSUK _A _B _C _D la x acc subG
                with None -> None
                | Some acca ->
                  patternMacroingInSUList _A _B _C _D (ListPatNoVar ll) sul acca
                    subG)
            | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
    | ListPat (l, n, r), s, acc, subG ->
        (match l
          with [] ->
            (match rev r
              with [] ->
                updateMatchingMapMacro (equal_metaVar _C) _A _B _D n
                  (ListSubs s) acc subG
              | ra :: rl ->
                (match rev s with [] -> None
                  | ItemL x :: sul ->
                    (match patternMacroingInSUK _A _B _C _D ra x acc subG
                      with None -> None
                      | Some acca ->
                        patternMacroingInSUList _A _B _C _D
                          (ListPat (l, n, rev rl)) (rev sul) acca subG)
                  | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
          | la :: ll ->
            (match s with [] -> None
              | ItemL x :: sul ->
                (match patternMacroingInSUK _A _B _C _D la x acc subG
                  with None -> None
                  | Some acca ->
                    patternMacroingInSUList _A _B _C _D (ListPat (ll, n, r)) sul
                      acca subG)
              | IdL _ :: _ -> None | SUListKItem (_, _) :: _ -> None))
and patternMacroingInSUMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (match t
          with ItemS x ->
            (match patternMacroingInSUK _A _B _C _D a x acc subG
              with None -> patternMacroingInSUMember _A _B _C _D a l acc subG
              | Some acca ->
                (let (u, v) = patternMacroingInSUMember _A _B _C _D a l acc subG
                   in
                  (u, (t, acca) :: v)))
          | IdS _ -> patternMacroingInSUMember _A _B _C _D a l acc subG
          | SUSetKItem (_, _) ->
            patternMacroingInSUMember _A _B _C _D a l acc subG)
and patternMacroingInSUSetAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUMember _A _B _C _D a s acc subG ::
          patternMacroingInSUSetAux _A _B _C _D l s acc subG
and patternMacroingInSUSet _A _B _C _D
  (SetPat (l, n)) s acc subG =
    (match
      findBijection (equal_suS _A _B _D)
        (patternMacroingInSUSetAux _A _B _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUSet s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (SetSubs (searchAllNonTermsInSUSet s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUMapMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (let (b, c) = a in
          (match t
            with ItemM (x, y) ->
              (match patternMacroingInSUK _A _B _C _D b x acc subG
                with None ->
                  patternMacroingInSUMapMember _A _B _C _D a l acc subG
                | Some acca ->
                  (match patternMacroingInSUK _A _B _C _D c y acca subG
                    with None ->
                      patternMacroingInSUMapMember _A _B _C _D a l acc subG
                    | Some accaa ->
                      (let (u, v) =
                         patternMacroingInSUMapMember _A _B _C _D a l acc subG
                         in
                        (u, (t, accaa) :: v))))
            | IdM _ -> patternMacroingInSUMapMember _A _B _C _D a l acc subG
            | SUMapKItem (_, _) ->
              patternMacroingInSUMapMember _A _B _C _D a l acc subG))
and patternMacroingInSUMapAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUMapMember _A _B _C _D a s acc subG ::
          patternMacroingInSUMapAux _A _B _C _D l s acc subG
and patternMacroingInSUMap _A _B _C _D
  (MapPat (l, n)) s acc subG =
    (match
      findBijection (equal_suM _A _B _D)
        (patternMacroingInSUMapAux _A _B _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUMap s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (MapSubs (searchAllNonTermsInSUMap s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUBigKWithBag _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRK t, s, acc, subG ->
      (match s with SUK r -> patternMacroingInSUK _A _B _C _D t r acc subG
        | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
        | SUBag _ -> None)
    | IRBag t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap _ -> None
          | SUBag r -> patternMacroingInSUBag _A _B _C _D t r acc subG)
    | IRList t, s, acc, subG ->
        (match s with SUK _ -> None
          | SUList r -> patternMacroingInSUList _A _B _C _D t r acc subG
          | SUSet _ -> None | SUMap _ -> None | SUBag _ -> None)
    | IRSet t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None
          | SUSet r -> patternMacroingInSUSet _A _B _C _D t r acc subG
          | SUMap _ -> None | SUBag _ -> None)
    | IRMap t, s, acc, subG ->
        (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap r -> patternMacroingInSUMap _A _B _C _D t r acc subG
          | SUBag _ -> None)
and patternMacroingInSUBagMember _A _B _C _D
  a x1 acc subG = match a, x1, acc, subG with a, [], acc, subG -> (a, [])
    | a, t :: l, acc, subG ->
        (let (b, (_, d)) = a in
          (match t
            with ItemB (x, _, z) ->
              (if equal_vara _A b x
                then (match
                       patternMacroingInSUBigKWithBag _B _A _C _D d z acc subG
                       with None ->
                         patternMacroingInSUBagMember _A _B _C _D a l acc subG
                       | Some acca ->
                         (let (u, v) =
                            patternMacroingInSUBagMember _A _B _C _D a l acc
                              subG
                            in
                           (u, (t, acca) :: v)))
                else patternMacroingInSUBagMember _A _B _C _D a l acc subG)
            | IdB _ -> patternMacroingInSUBagMember _A _B _C _D a l acc subG))
and patternMacroingInSUBagAux _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with [], s, acc, subG -> []
    | a :: l, s, acc, subG ->
        patternMacroingInSUBagMember _A _B _C _D a s acc subG ::
          patternMacroingInSUBagAux _A _B _C _D l s acc subG
and patternMacroingInSUBag _A _B _C _D
  (BagPat (l, n)) s acc subG =
    (match
      findBijection (equal_suB _A _B _D)
        (patternMacroingInSUBagAux _B _A _C _D l s acc subG)
      with None -> None
      | Some (ones, remains) ->
        (match n
          with None ->
            (if null (searchAllNonTermsInSUBag s) && null remains
              then mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acc subG
              else None)
          | Some var ->
            (match
              updateMatchingMapMacro (equal_metaVar _C) _A _B _D var
                (BagSubs (searchAllNonTermsInSUBag s @ keys remains)) acc subG
              with None -> None
              | Some acca ->
                mergeMapWithOnes (equal_metaVar _C) _A _B _D ones acca subG)))
and patternMacroingInSUBigKWithLabel _A _B _C _D
  x0 s acc subG = match x0, s, acc, subG with
    IRBigBag t, s, acc, subG ->
      (match s
        with SUBigBag ta ->
          patternMacroingInSUBigKWithBag _A _B _C _D t ta acc subG
        | SUBigLabel _ -> None)
    | IRBigLabel t, s, acc, subG ->
        (match s with SUBigBag _ -> None
          | SUBigLabel ta ->
            patternMacroingInSUKLabel _A _C _B _D t ta acc subG);;

let rec isGroundTermInSUKItem
  = function
    SUKItem (l, r, ty) -> isGroundTermInSUKLabel l && isGroundTermInSUKList r
    | SUIdKItem (a, b) -> false
    | SUHOLE a -> true
and isGroundTermInSUK
  = function [] -> true
    | b :: l ->
        (match b
          with ItemFactor x -> isGroundTermInSUKItem x && isGroundTermInSUK l
          | IdFactor _ -> false
          | SUKKItem (x, y, _) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUK l))
and isGroundTermInSUBigKWithBag = function SUK a -> isGroundTermInSUK a
                                  | SUList a -> isGroundTermInSUList a
                                  | SUSet a -> isGroundTermInSUSet a
                                  | SUMap a -> isGroundTermInSUMap a
                                  | SUBag a -> isGroundTermInSUBag a
and isGroundTermInSUBag
  = function [] -> true
    | b :: l ->
        (match b
          with ItemB (_, _, z) ->
            isGroundTermInSUBigKWithBag z && isGroundTermInSUBag l
          | IdB _ -> false)
and isGroundTermInSUBigKWithLabel
  = function SUBigBag a -> isGroundTermInSUBigKWithBag a
    | SUBigLabel a -> isGroundTermInSUKLabel a
and isGroundTermInSUKList
  = function [] -> true
    | b :: l ->
        (match b
          with ItemKl a ->
            isGroundTermInSUBigKWithLabel a && isGroundTermInSUKList l
          | IdKl _ -> false)
and isGroundTermInSUKLabel
  = function SUKLabel a -> true
    | SUKLabelFun (a, b) -> isGroundTermInSUKLabel a && isGroundTermInSUKList b
    | SUIdKLabel n -> false
and isGroundTermInSUMap
  = function [] -> true
    | b :: l ->
        (match b
          with ItemM (x, y) ->
            isGroundTermInSUK x &&
              (isGroundTermInSUK y && isGroundTermInSUMap l)
          | IdM _ -> false
          | SUMapKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUMap l))
and isGroundTermInSUSet
  = function [] -> true
    | b :: l ->
        (match b with ItemS x -> isGroundTermInSUK x && isGroundTermInSUSet l
          | IdS _ -> false
          | SUSetKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUSet l))
and isGroundTermInSUList
  = function [] -> true
    | b :: l ->
        (match b with ItemL x -> isGroundTermInSUK x && isGroundTermInSUList l
          | IdL _ -> false
          | SUListKItem (x, y) ->
            isGroundTermInSUKLabel x &&
              (isGroundTermInSUKList y && isGroundTermInSUList l));;

let rec isCommonElemInSUSet _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, b :: l, subG ->
        (match a
          with ItemS v ->
            (match b
              with ItemS va ->
                (match syntacticMonoidInSUK _A _B _C v va subG
                  with None -> isCommonElemInSUSet _A _B _C a l subG
                  | Some _ -> true)
              | IdS _ -> isCommonElemInSUSet _A _B _C a l subG
              | SUSetKItem (_, _) -> isCommonElemInSUSet _A _B _C a l subG)
          | IdS x ->
            (match b with ItemS _ -> isCommonElemInSUSet _A _B _C a l subG
              | IdS xa ->
                (if equal_metaVara _C x xa then true
                  else isCommonElemInSUSet _A _B _C a l subG)
              | SUSetKItem (_, _) -> isCommonElemInSUSet _A _B _C a l subG)
          | SUSetKItem (x, y) ->
            (match b with ItemS _ -> isCommonElemInSUSet _A _B _C a l subG
              | IdS _ -> isCommonElemInSUSet _A _B _C a l subG
              | SUSetKItem (xa, ya) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    syntacticMonoidInSUKList _A _B _C y ya subG)
                  with (None, _) -> isCommonElemInSUSet _A _B _C a l subG
                  | (Some _, None) -> isCommonElemInSUSet _A _B _C a l subG
                  | (Some _, Some _) -> true)));;

let rec isCommonElemInSUMap _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> false
    | a, b :: l, subG ->
        (match a
          with ItemM (v, w) ->
            (match b
              with ItemM (va, wa) ->
                (match syntacticMonoidInSUK _A _B _C v va subG
                  with None -> isCommonElemInSUMap _A _B _C a l subG
                  | Some _ ->
                    (match syntacticMonoidInSUK _A _B _C w wa subG
                      with None -> isCommonElemInSUMap _A _B _C a l subG
                      | Some _ -> true))
              | IdM _ -> isCommonElemInSUMap _A _B _C a l subG
              | SUMapKItem (_, _) -> isCommonElemInSUMap _A _B _C a l subG)
          | IdM x ->
            (match b with ItemM (_, _) -> isCommonElemInSUMap _A _B _C a l subG
              | IdM xa ->
                (if equal_metaVara _C x xa then true
                  else isCommonElemInSUMap _A _B _C a l subG)
              | SUMapKItem (_, _) -> isCommonElemInSUMap _A _B _C a l subG)
          | SUMapKItem (x, y) ->
            (match b with ItemM (_, _) -> isCommonElemInSUMap _A _B _C a l subG
              | IdM _ -> isCommonElemInSUMap _A _B _C a l subG
              | SUMapKItem (xa, ya) ->
                (match
                  (syntacticMonoidInSUKLabel _A _B _C x xa subG,
                    syntacticMonoidInSUKList _A _B _C y ya subG)
                  with (None, _) -> isCommonElemInSUMap _A _B _C a l subG
                  | (Some _, None) -> isCommonElemInSUMap _A _B _C a l subG
                  | (Some _, Some _) -> true)));;

let rec getValueInSUMap _A _B _C
  a x1 subG = match a, x1, subG with a, [], subG -> None
    | a, b :: l, subG ->
        (match b
          with ItemM (x, y) ->
            (match syntacticMonoidInSUK _A _B _C a x subG
              with None -> getValueInSUMap _A _B _C a l subG | Some _ -> Some y)
          | IdM _ -> getValueInSUMap _A _B _C a l subG
          | SUMapKItem (_, _) -> getValueInSUMap _A _B _C a l subG);;

let rec regularizeInSUKItem _A _B _C
  x0 subG = match x0, subG with
    SUKItem (l, r, ty), subG ->
      (match regularizeInSUKLabel _A _B _C l subG with None -> None
        | Some a ->
          (match regularizeInSUKList _A _B _C r subG with None -> None
            | Some b -> Some (SUKItem (a, b, ty))))
    | SUHOLE a, subG -> Some (SUHOLE a)
    | SUIdKItem (a, b), subG -> Some (SUIdKItem (a, b))
and regularizeInSUKElem _A _B _C
  x0 subG = match x0, subG with IdFactor x, subG -> Some (IdFactor x)
    | ItemFactor x, subG ->
        (match regularizeInSUKItem _A _B _C x subG with None -> None
          | Some xa -> Some (ItemFactor xa))
    | SUKKItem (x, y, z), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUKKItem (xa, ya, z))))
and regularizeInSUK _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUKElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUK _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUBigKWithBag _A _B _C
  x0 subG = match x0, subG with
    SUK a, subG ->
      (match regularizeInSUK _A _B _C a subG with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, subG ->
        (match regularizeInSUList _A _B _C a subG with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, subG ->
        (match regularizeInSUSet _A _B _C a subG with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, subG ->
        (match regularizeInSUMap _A _B _C a subG with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, subG ->
        (match regularizeInSUBag _A _B _C a subG with None -> None
          | Some aa -> Some (SUBag aa))
and regularizeInSUBagElem _A _B _C
  x0 subG = match x0, subG with IdB x, subG -> Some (IdB x)
    | ItemB (x, y, z), subG ->
        (match regularizeInSUBigKWithBag _A _B _C z subG with None -> None
          | Some za -> Some (ItemB (x, y, za)))
and regularizeInSUBag _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUBagElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUBag _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUBigKWithLabel _A _B _C
  x0 subG = match x0, subG with
    SUBigBag a, subG ->
      (match regularizeInSUBigKWithBag _A _B _C a subG with None -> None
        | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, subG ->
        (match regularizeInSUKLabel _A _B _C a subG with None -> None
          | Some aa -> Some (SUBigLabel aa))
and regularizeInSUKListElem _A _B _C
  x0 subG = match x0, subG with IdKl x, subG -> Some (IdKl x)
    | ItemKl x, subG ->
        (match regularizeInSUBigKWithLabel _A _B _C x subG with None -> None
          | Some xa -> Some (ItemKl xa))
and regularizeInSUKList _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUKListElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUKList _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)))
and regularizeInSUKLabel _A _B _C
  x0 subG = match x0, subG with SUKLabel a, subG -> Some (SUKLabel a)
    | SUIdKLabel a, subG -> Some (SUIdKLabel a)
    | SUKLabelFun (a, b), subG ->
        (match regularizeInSUKLabel _A _B _C a subG with None -> None
          | Some aa ->
            (match regularizeInSUKList _A _B _C b subG with None -> None
              | Some ba -> Some (SUKLabelFun (aa, ba))))
and regularizeInSUMapElem _A _B _C
  x0 subG = match x0, subG with IdM x, subG -> Some (IdM x)
    | ItemM (x, y), subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUK _A _B _C y subG with None -> None
              | Some ya -> Some (ItemM (xa, ya))))
    | SUMapKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUMapKItem (xa, ya))))
and regularizeInSUMap _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUMapElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUMap _A _B _C l subG with None -> None
              | Some la ->
                (if isCommonElemInSUMap _A _B _C ba la subG then Some la
                  else (match ba
                         with ItemM (x, _) ->
                           (match getValueInSUMap _A _B _C x la subG
                             with None -> Some (ba :: la) | Some _ -> None)
                         | IdM _ -> Some (ba :: la)
                         | SUMapKItem (_, _) -> Some (ba :: la)))))
and regularizeInSUSetElem _A _B _C
  x0 subG = match x0, subG with IdS x, subG -> Some (IdS x)
    | ItemS x, subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa -> Some (ItemS xa))
    | SUSetKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUSetKItem (xa, ya))))
and regularizeInSUSet _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUSetElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUSet _A _B _C l subG with None -> None
              | Some la ->
                (if isCommonElemInSUSet _A _B _C ba la subG then Some la
                  else Some (ba :: la))))
and regularizeInSUListElem _A _B _C
  x0 subG = match x0, subG with IdL x, subG -> Some (IdL x)
    | ItemL x, subG ->
        (match regularizeInSUK _A _B _C x subG with None -> None
          | Some xa -> Some (ItemL xa))
    | SUListKItem (x, y), subG ->
        (match regularizeInSUKLabel _A _B _C x subG with None -> None
          | Some xa ->
            (match regularizeInSUKList _A _B _C y subG with None -> None
              | Some ya -> Some (SUListKItem (xa, ya))))
and regularizeInSUList _A _B _C
  x0 subG = match x0, subG with [], subG -> Some []
    | b :: l, subG ->
        (match regularizeInSUListElem _A _B _C b subG with None -> None
          | Some ba ->
            (match regularizeInSUList _A _B _C l subG with None -> None
              | Some la -> Some (ba :: la)));;

let rec updateMap _A _B
  a b x2 subG = match a, b, x2, subG with a, b, [], subG -> Some [(a, b)]
    | a, b, x :: l, subG ->
        (let (aa, ba) = x in
          (if eq _A a aa
            then (match meet _B b ba subG with [] -> None
                   | ty :: tyl -> Some ((a, ty :: tyl) :: l))
            else (match updateMap _A _B a b l subG with None -> None
                   | Some la -> Some (x :: la))));;

let rec numberOfItemsInKList (_D1, _D2, _D3)
  = function [] -> zero _D3
    | x :: l ->
        (match x
          with ItemKl _ ->
            plus _D2 (one _D1) (numberOfItemsInKList (_D1, _D2, _D3) l)
          | IdKl _ -> numberOfItemsInKList (_D1, _D2, _D3) l);;

let rec gen_length n x1 = match n, x1 with n, x :: xs -> gen_length (Suc n) xs
                     | n, [] -> n;;

let rec size_list x = gen_length Zero_nat x;;

let rec hasIdInKList
  = function [] -> false
    | a :: l -> (match a with ItemKl _ -> hasIdInKList l | IdKl _ -> true);;

let rec getIdInSUKLabel = function SUIdKLabel a -> Some a
                          | SUKLabel v -> None
                          | SUKLabelFun (v, va) -> None;;

let rec isFunctionItemAux _C
  x0 s = match x0, s with [], s -> false
    | (a, (b, (SingleTon t, (nl, true)))) :: l, s ->
        (if eq _C t s then true else isFunctionItemAux _C l s)
    | (a, (b, (SetTon t, (nl, true)))) :: l, s ->
        (if t s then true else isFunctionItemAux _C l s)
    | (a, (b, (t, (nl, false)))) :: l, s -> isFunctionItemAux _C l s;;

let rec isFunctionItem _A s database = isFunctionItemAux _A database s;;

let rec getArgSortsMeaning _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (v, (vs, (SingleTon a, (nl, b)))) :: l ->
        (if eq _A aa a then Some vs else getArgSortsMeaning _A aa l)
    | a, (v, (vs, (SetTon s, (nl, b)))) :: l ->
        (if s a then Some vs else getArgSortsMeaning _A a l);;

let rec getArgSort _A a database = getArgSortsMeaning _A a database;;

let rec getSortMeaning _A
  a x1 = match a, x1 with a, [] -> None
    | aa, (v, (vs, (SingleTon a, (nl, b)))) :: l ->
        (if eq _A aa a then Some v else getSortMeaning _A aa l)
    | a, (v, (vs, (SetTon s, (nl, b)))) :: l ->
        (if s a then Some v else getSortMeaning _A a l);;

let rec getSort _A a database = getSortMeaning _A a database;;

let rec updateBeta _A _B
  a b x2 subG = match a, b, x2, subG with a, b, [], subG -> Some []
    | a, b, x :: l, subG ->
        (let (aa, ba) = x in
          (if eq _A a aa
            then (match meet _B b ba subG with [] -> None
                   | ty :: tyl -> Some ((a, ty :: tyl) :: l))
            else (match updateBeta _A _B a b l subG with None -> None
                   | Some la -> Some (x :: la))));;

let rec checkTermsInSUKItem _A _C
  x0 maxTy acc beta database subG = match x0, maxTy, acc, beta, database, subG
    with
    SUKItem (l, r, ty), maxTy, acc, beta, database, subG ->
      (if subsortList (equal_sort _A) maxTy [K] subG &&
            subsortList (equal_sort _A) ty [K] subG
        then (match getSUKLabelMeaning l
               with None ->
                 (match checkTermsInSUKLabel _A _C l acc beta database subG
                   with None -> None
                   | Some (acca, (betaa, la)) ->
                     (match
                       checkTermsInNoneSUKList _A _C r acca betaa database subG
                       with None -> None
                       | Some (accaa, (betaaa, ra)) ->
                         (match meet (equal_sort _A) ty maxTy subG
                           with [] -> None
                           | tya :: tyl ->
                             (match getIdInSUKLabel la
                               with None ->
                                 Some (accaa,
(betaaa, SUKItem (la, ra, tya :: tyl)))
                               | Some newId ->
                                 (match
                                   updateBeta (equal_metaVar _C) (equal_sort _A)
                                     newId (tya :: tyl) accaa subG
                                   with None -> None
                                   | Some betab ->
                                     Some (accaa,
    (betab, SUKItem (la, ra, tya :: tyl))))))))
               | Some s ->
                 (match getSort (equal_label _A) s database with None -> None
                   | Some theTy ->
                     (match getArgSort (equal_label _A) s database
                       with None -> None
                       | Some tyl ->
                         (match
                           checkTermsInSUKList _A _C r tyl acc beta database
                             subG
                           with None -> None
                           | Some (acca, (betaa, ra)) ->
                             (if isFunctionItem (equal_label _A) s database
                               then (match
                                      meet (equal_sort _A) theTy
(meet (equal_sort _A) ty maxTy subG) subG
                                      with [] -> None
                                      | a :: lista ->
Some (acca, (betaa, SUKItem (l, ra, a :: lista))))
                               else (if subsortList (equal_sort _A) theTy ty
  subG &&
  subsortList (equal_sort _A) theTy maxTy subG
                                      then Some (acca,
          (betaa, SUKItem (l, ra, theTy)))
                                      else None))))))
        else None)
    | SUIdKItem (a, b), maxTy, acc, beta, database, subG ->
        (match meet (equal_sort _A) b maxTy subG with [] -> None
          | aa :: lista ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) a (aa :: lista) acc
                subG
              with None -> None
              | Some acca -> Some (acca, (beta, SUIdKItem (a, aa :: lista)))))
    | SUHOLE a, maxTy, acc, beta, database, subG ->
        (match meet (equal_sort _A) a maxTy subG with [] -> None
          | aa :: lista -> Some (acc, (beta, SUHOLE (aa :: lista))))
and checkTermsInSUK _A _C
  l ty acc beta database subG =
    (if equal_lista (equal_sort _A) ty [K]
      then (match l with [] -> Some (acc, (beta, []))
             | ItemFactor x :: xl ->
               (match checkTermsInSUKItem _A _C x [K] acc beta database subG
                 with None -> None
                 | Some (acca, (betaa, xa)) ->
                   (match checkTermsInSUK _A _C xl ty acca betaa database subG
                     with None -> None
                     | Some (accaa, (betaaa, xla)) ->
                       Some (accaa, (betaaa, ItemFactor xa :: xla))))
             | IdFactor x :: xl ->
               (match
                 updateMap (equal_metaVar _C) (equal_sort _A) x [K] acc subG
                 with None -> None
                 | Some acca ->
                   (match checkTermsInSUK _A _C xl ty acca beta database subG
                     with None -> None
                     | Some (accaa, (betaa, xla)) ->
                       Some (accaa, (betaa, IdFactor x :: xla))))
             | SUKKItem (a, b, tya) :: xl ->
               (if subsortList (equal_sort _A) tya [K] subG
                 then (match getSUKLabelMeaning a
                        with None ->
                          (match
                            checkTermsInSUKLabel _A _C a acc beta database subG
                            with None -> None
                            | Some aa ->
                              (let (acca, ab) = aa in
                               let (betaa, ac) = ab in
                                (match
                                  checkTermsInNoneSUKList _A _C b acca betaa
                                    database subG
                                  with None -> None
                                  | Some ba ->
                                    (let (accaa, bb) = ba in
                                     let (betaaa, bc) = bb in
                                      (match
checkTermsInSUK _A _C xl ty accaa betaaa database subG with None -> None
| Some (accb, (betab, xla)) ->
  Some (accb, (betab, SUKKItem (ac, bc, tya) :: xla)))))))
                        | Some s ->
                          (if isFunctionItem (equal_label _A) s database
                            then (match
                                   (getSort (equal_label _A) s database,
                                     getArgSort (equal_label _A) s database)
                                   with (None, _) -> None
                                   | (Some _, None) -> None
                                   | (Some tyaa, Some tyl) ->
                                     (match meet (equal_sort _A) tya tyaa subG
                                       with [] -> None
                                       | aa :: lista ->
 (match checkTermsInSUKList _A _C b tyl acc beta database subG with None -> None
   | Some ba ->
     (let (acca, bb) = ba in
      let (betaa, bc) = bb in
       (match checkTermsInSUK _A _C xl ty acca betaa database subG
         with None -> None
         | Some (accaa, (betaaa, xla)) ->
           Some (accaa, (betaaa, SUKKItem (a, bc, aa :: lista) :: xla)))))))
                            else None))
                 else None))
      else (if subsortList (equal_sort _A) ty [KItem] subG
             then (match l
                    with [ItemFactor a] ->
                      (match
                        checkTermsInSUKItem _A _C a ty acc beta database subG
                        with None -> None
                        | Some aa ->
                          (let (acca, ab) = aa in
                           let (betaa, ac) = ab in
                            Some (acca, (betaa, [ItemFactor ac]))))
                    | [IdFactor a] ->
                      (match
                        updateMap (equal_metaVar _C) (equal_sort _A) a ty acc
                          subG
                        with None -> None
                        | Some acca ->
                          Some (acca, (beta, [ItemFactor (SUIdKItem (a, ty))])))
                    | [SUKKItem (a, b, tya)] ->
                      (if subsortList (equal_sort _A) tya [K] subG
                        then (match getSUKLabelMeaning a
                               with None ->
                                 (match
                                   checkTermsInSUKLabel _A _C a acc beta
                                     database subG
                                   with None -> None
                                   | Some aa ->
                                     (let (acca, ab) = aa in
                                      let (betaa, ac) = ab in
                                       (match
 checkTermsInNoneSUKList _A _C b acca betaa database subG with None -> None
 | Some ba ->
   (let (accaa, bb) = ba in
    let (betaaa, bc) = bb in
     (match meet (equal_sort _A) ty tya subG with [] -> None
       | aaa :: lista ->
         Some (accaa, (betaaa, [SUKKItem (ac, bc, aaa :: lista)])))))))
                               | Some s ->
                                 (if isFunctionItem (equal_label _A) s database
                                   then (let (Some theTy, Some tyl) =
   (getSort (equal_label _A) s database, getArgSort (equal_label _A) s database)
   in
  (match checkTermsInSUKList _A _C b tyl acc beta database subG
    with None -> None
    | Some ba ->
      (let (acca, bb) = ba in
       let (betaa, bc) = bb in
        (match
          meet (equal_sort _A) ty (meet (equal_sort _A) tya theTy subG) subG
          with [] -> None
          | aa :: lista ->
            Some (acca, (betaa, [SUKKItem (a, bc, aa :: lista)]))))))
                                   else None))
                        else None))
             else None))
and checkTermsInSUBigKWithBag _A _C
  x0 ty acc beta database subG = match x0, ty, acc, beta, database, subG with
    SUK a, ty, acc, beta, database, subG ->
      (match ty
        with None ->
          (match checkTermsInSUK _A _C a [K] acc beta database subG
            with None -> None
            | Some aa -> (let (acca, ab) = aa in
                          let (betaa, ac) = ab in
                           Some (acca, (betaa, SUK ac))))
        | Some tya ->
          (if subsortList (equal_sort _A) tya [K] subG
            then (match checkTermsInSUK _A _C a [K] acc beta database subG
                   with None -> None
                   | Some aa ->
                     (let (acca, ab) = aa in
                      let (betaa, ac) = ab in
                       Some (acca, (betaa, SUK ac))))
            else None))
    | SUList a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUList _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUList ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [List]
              then (match checkTermsInSUList _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUList ac))))
              else None))
    | SUSet a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUSet _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUSet ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Seta]
              then (match checkTermsInSUSet _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUSet ac))))
              else None))
    | SUMap a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUMap _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUMap ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Map]
              then (match checkTermsInSUMap _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUMap ac))))
              else None))
    | SUBag a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUBag _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUBag ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [Bag]
              then (match checkTermsInSUBag _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUBag ac))))
              else None))
and checkTermsInSUBag _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemB (x, y, z) ->
            (match checkTermsInSUBigKWithBag _A _C z None acc beta database subG
              with None -> None
              | Some (acca, (betaa, za)) ->
                (match checkTermsInSUBag _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemB (x, y, za) :: la))))
          | IdB x ->
            (match updateMap (equal_metaVar _C) (equal_sort _A) x [Bag] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUBag _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdB x :: la)))))
and checkTermsInSUBigKWithLabel _A _C
  x0 ty acc beta database subG = match x0, ty, acc, beta, database, subG with
    SUBigBag a, ty, acc, beta, database, subG ->
      (match checkTermsInSUBigKWithBag _A _C a ty acc beta database subG
        with None -> None
        | Some aa ->
          (let (acca, ab) = aa in
           let (betaa, ac) = ab in
            Some (acca, (betaa, SUBigBag ac))))
    | SUBigLabel a, ty, acc, beta, database, subG ->
        (match ty
          with None ->
            (match checkTermsInSUKLabel _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  Some (acca, (betaa, SUBigLabel ac))))
          | Some tya ->
            (if equal_lista (equal_sort _A) tya [KLabel]
              then (match checkTermsInSUKLabel _A _C a acc beta database subG
                     with None -> None
                     | Some aa ->
                       (let (acca, ab) = aa in
                        let (betaa, ac) = ab in
                         Some (acca, (betaa, SUBigLabel ac))))
              else None))
and checkTermsInSUKListAux _A _C
  x0 tyl acc beta database subG = match x0, tyl, acc, beta, database, subG with
    [], tyl, acc, beta, database, subG -> Some (acc, (beta, ([], [])))
    | b :: l, tyl, acc, beta, database, subG ->
        (match b
          with ItemKl x ->
            (match tyl with [] -> None
              | ty :: tyla ->
                (match
                  checkTermsInSUBigKWithLabel _A _C x (Some ty) acc beta
                    database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInSUKListAux _A _C l tyla acca betaa database
                        subG
                      with None -> None
                      | Some (accaa, (betaaa, (lb, la))) ->
                        Some (accaa, (betaaa, (ItemKl xa :: lb, la))))))
          | IdKl x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [KList] acc subG
              with None -> None
              | Some acca -> Some (acca, (beta, ([], b :: l)))))
and checkTermsInNoneSUKList _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | x :: l, acc, beta, database, subG ->
        (match x
          with ItemKl a ->
            (match
              checkTermsInSUBigKWithLabel _A _C a None acc beta database subG
              with None -> None
              | Some aa ->
                (let (_, ab) = aa in
                 let (_, ac) = ab in
                  (match checkTermsInNoneSUKList _A _C l acc beta database subG
                    with None -> None
                    | Some (acca, (betaa, la)) ->
                      Some (acca, (betaa, ItemKl ac :: la)))))
          | IdKl a ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) a [KList] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInNoneSUKList _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdKl a :: la)))))
and checkTermsInSUKList _A _C
  l tyl acc beta database subG =
    (if less_nat (size_list tyl)
          (numberOfItemsInKList (one_nat, plus_nat, zero_nat) l)
      then None
      else (if hasIdInKList l
             then (match
                    checkTermsInSUKListAux _A _C l tyl acc beta database subG
                    with None -> None
                    | Some (acca, (betaa, (la, lb))) ->
                      (match
                        checkTermsInSUKListAux _A _C (rev lb) (rev tyl) acca
                          betaa database subG
                        with None -> None
                        | Some (accaa, (betaaa, (laa, lba))) ->
                          (if null lba then Some (accaa, (betaaa, la @ rev laa))
                            else (match
                                   checkTermsInNoneSUKList _A _C (rev lba) accaa
                                     betaaa database subG
                                   with None -> None
                                   | Some (accb, (betab, lbb)) ->
                                     Some (accb,
    (betab, la @ lbb @ rev laa))))))
             else (if equal_nata
                        (numberOfItemsInKList (one_nat, plus_nat, zero_nat) l)
                        (size_list tyl)
                    then (match
                           checkTermsInSUKListAux _A _C l tyl acc beta database
                             subG
                           with None -> None
                           | Some (acca, (betaa, (la, []))) ->
                             Some (acca, (betaa, la))
                           | Some (_, (_, (_, _ :: _))) -> None)
                    else None)))
and checkTermsInSUKLabel _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    SUKLabel a, acc, beta, database, subG -> Some (acc, (beta, SUKLabel a))
    | SUKLabelFun (a, b), acc, beta, database, subG ->
        (match getSUKLabelMeaning a
          with None ->
            (match checkTermsInSUKLabel _A _C a acc beta database subG
              with None -> None
              | Some aa ->
                (let (acca, ab) = aa in
                 let (betaa, ac) = ab in
                  (match
                    checkTermsInNoneSUKList _A _C b acca betaa database subG
                    with None -> None
                    | Some ba ->
                      (let (accaa, bb) = ba in
                       let (betaaa, bc) = bb in
                        (match getIdInSUKLabel ac
                          with None ->
                            Some (accaa, (betaaa, SUKLabelFun (ac, bc)))
                          | Some x ->
                            (match
                              updateMap (equal_metaVar _C) (equal_sort _A) x
                                [KLabel] betaaa subG
                              with None -> None
                              | Some betab ->
                                Some (accaa,
                                       (betab, SUKLabelFun (ac, bc)))))))))
          | Some s ->
            (if isFunctionItem (equal_label _A) s database
              then (match getArgSort (equal_label _A) s database
                     with None -> None
                     | Some l ->
                       (match getSort (equal_label _A) s database
                         with None -> None
                         | Some ty ->
                           (if subsortList (equal_sort _A) ty [KLabel] subG
                             then (match
                                    checkTermsInSUKList _A _C b l acc beta
                                      database subG
                                    with None -> None
                                    | Some ba ->
                                      (let (acca, bb) = ba in
                                       let (betaa, bc) = bb in
Some (acca, (betaa, SUKLabelFun (a, bc)))))
                             else None)))
              else None))
    | SUIdKLabel n, acc, beta, database, subG ->
        (match updateMap (equal_metaVar _C) (equal_sort _A) n [KLabel] acc subG
          with None -> None | Some acca -> Some (acca, (beta, SUIdKLabel n)))
and checkTermsInSUMap _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemM (x, y) ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUK _A _C y [K] acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, ya)) ->
                    (match checkTermsInSUMap _A _C l accaa betaaa database subG
                      with None -> None
                      | Some (accb, (betab, la)) ->
                        Some (accb, (betab, ItemM (xa, ya) :: la)))))
          | IdM x ->
            (match updateMap (equal_metaVar _C) (equal_sort _A) x [Map] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUMap _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdM x :: la))))
          | SUMapKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUMap _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUMapKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [Map] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUMapKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Map] subG
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUMap _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUMapKItem (x, ya) :: la))))
                             else None))
                  else None)))
and checkTermsInSUSet _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemS x ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUSet _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemS xa :: la))))
          | IdS x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [Seta] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUSet _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdS x :: la))))
          | SUSetKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUSet _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUSetKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [Seta] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUSetKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Seta] subG
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUSet _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUSetKItem (x, ya) :: la))))
                             else None))
                  else None)))
and checkTermsInSUList _A _C
  x0 acc beta database subG = match x0, acc, beta, database, subG with
    [], acc, beta, database, subG -> Some (acc, (beta, []))
    | b :: l, acc, beta, database, subG ->
        (match b
          with ItemL x ->
            (match checkTermsInSUK _A _C x [K] acc beta database subG
              with None -> None
              | Some (acca, (betaa, xa)) ->
                (match checkTermsInSUList _A _C l acca betaa database subG
                  with None -> None
                  | Some (accaa, (betaaa, la)) ->
                    Some (accaa, (betaaa, ItemL xa :: la))))
          | IdL x ->
            (match
              updateMap (equal_metaVar _C) (equal_sort _A) x [List] acc subG
              with None -> None
              | Some acca ->
                (match checkTermsInSUList _A _C l acca beta database subG
                  with None -> None
                  | Some (accaa, (betaa, la)) ->
                    Some (accaa, (betaa, IdL x :: la))))
          | SUListKItem (x, y) ->
            (match getSUKLabelMeaning x
              with None ->
                (match checkTermsInSUKLabel _A _C x acc beta database subG
                  with None -> None
                  | Some (acca, (betaa, xa)) ->
                    (match
                      checkTermsInNoneSUKList _A _C y acca betaa database subG
                      with None -> None
                      | Some (accaa, (betaaa, ya)) ->
                        (match
                          checkTermsInSUList _A _C l accaa betaaa database subG
                          with None -> None
                          | Some (accb, (betab, la)) ->
                            (match getIdInSUKLabel xa
                              with None ->
                                Some (accb, (betab, SUListKItem (xa, ya) :: la))
                              | Some xx ->
                                (match
                                  updateMap (equal_metaVar _C) (equal_sort _A)
                                    xx [List] betab subG
                                  with None -> None
                                  | Some betac ->
                                    Some (accb,
   (betac, SUListKItem (xa, ya) :: la)))))))
              | Some s ->
                (if isFunctionItem (equal_label _A) s database
                  then (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if equal_lista (equal_sort _A) ty [List]
                             then (match
                                    checkTermsInSUKList _A _C y tyl acc beta
                                      database subG
                                    with None -> None
                                    | Some (acca, (betaa, ya)) ->
                                      (match
checkTermsInSUList _A _C l acca betaa database subG with None -> None
| Some (accaa, (betaaa, la)) ->
  Some (accaa, (betaaa, SUListKItem (x, ya) :: la))))
                             else None))
                  else None)));;

let rec typeCheckCondition _A _B _C
  a database subG =
    (if isGroundTermInSUKItem a
      then (match checkTermsInSUKItem _A _C a [Bool] [] [] database subG
             with None -> None
             | Some (_, (_, aa)) -> regularizeInSUKItem _A _B _C aa subG)
      else None);;

let rec single x = Seq (fun _ -> Insert (x, bot_pred));;

let rec bind (Seq g) f = Seq (fun _ -> apply f (g ()))
and apply f x1 = match f, x1 with f, Empty -> Empty
            | f, Insert (x, p) -> Join (f x, Join (bind p f, Empty))
            | f, Join (p, xq) -> Join (bind p f, apply f xq);;

let rec eq_i_o xa = bind (single xa) single;;

let rec eq_i_i _A
  xa xb =
    bind (single (xa, xb))
      (fun (x, xaa) -> (if eq _A x xaa then single () else bot_pred));;

let rec localteFunTermInSUKItem _A
  x0 database = match x0, database with
    SUKItem (x, y, z), database ->
      (match localteFunTermInSUKLabel _A x database
        with None ->
          (match localteFunTermInSUKList _A y database
            with None ->
              (match getSUKLabelMeaning x with None -> None
                | Some s ->
                  (if isFunctionItem (equal_label _A) s database
                    then Some (s, (y, (z, SUIdKItem (FunHole, z)))) else None))
            | Some (l, (funa, (ty, r))) ->
              Some (l, (funa, (ty, SUKItem (x, r, z)))))
        | Some (l, (funa, (ty, r))) ->
          Some (l, (funa, (ty, SUKItem (r, y, z)))))
    | SUIdKItem (x, y), database -> None
    | SUHOLE x, database -> None
and localteFunTermInSUK _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemFactor x ->
            (match localteFunTermInSUKItem _A x database
              with None ->
                (match localteFunTermInSUK _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemFactor r :: l))))
          | IdFactor _ ->
            (match localteFunTermInSUK _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUKKItem (x, y, z) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUK _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s,
  (y, (z, (if equal_lista (equal_sort _A) z [K] then IdFactor FunHole
            else ItemFactor (SUIdKItem (FunHole, z))) ::
            l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUKKItem (x, r, z) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUKKItem (r, y, z) :: l)))))
and localteFunTermInSUBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database ->
      (match localteFunTermInSUK _A a database with None -> None
        | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUK r))))
    | SUList a, database ->
        (match localteFunTermInSUList _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUList r))))
    | SUSet a, database ->
        (match localteFunTermInSUSet _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUSet r))))
    | SUMap a, database ->
        (match localteFunTermInSUMap _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUMap r))))
    | SUBag a, database ->
        (match localteFunTermInSUBag _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBag r))))
and localteFunTermInSUBag _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemB (x, y, z) ->
            (match localteFunTermInSUBigKWithBag _A z database
              with None ->
                (match localteFunTermInSUBag _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemB (x, y, r) :: l))))
          | IdB _ ->
            (match localteFunTermInSUBag _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r)))))
and localteFunTermInSUBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database ->
      (match localteFunTermInSUBigKWithBag _A a database with None -> None
        | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBigBag r))))
    | SUBigLabel a, database ->
        (match localteFunTermInSUKLabel _A a database with None -> None
          | Some (l, (funa, (ty, r))) -> Some (l, (funa, (ty, SUBigLabel r))))
and localteFunTermInSUKList _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemKl x ->
            (match localteFunTermInSUBigKWithLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemKl r :: l))))
          | IdKl _ ->
            (match localteFunTermInSUKList _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r)))))
and localteFunTermInSUKLabel _A
  x0 database = match x0, database with SUKLabel a, database -> None
    | SUIdKLabel a, database -> None
    | SUKLabelFun (x, y), database ->
        (match localteFunTermInSUKLabel _A x database
          with None ->
            (match localteFunTermInSUKList _A y database
              with None ->
                (match getSUKLabelMeaning x with None -> None
                  | Some s ->
                    (if isFunctionItem (equal_label _A) s database
                      then Some (s, (y, ([KLabel], SUIdKLabel FunHole)))
                      else None))
              | Some (l, (funa, (ty, r))) ->
                Some (l, (funa, (ty, SUKLabelFun (x, r)))))
          | Some (l, (funa, (ty, r))) ->
            Some (l, (funa, (ty, SUKLabelFun (r, y)))))
and localteFunTermInSUMap _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemM (x, y) ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUK _A y database
                  with None ->
                    (match localteFunTermInSUMap _A l database with None -> None
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, ItemM (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemM (r, y) :: l))))
          | IdM _ ->
            (match localteFunTermInSUMap _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUMapKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUMap _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([Map], IdM FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUMapKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUMapKItem (r, y) :: l)))))
and localteFunTermInSUSet _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemS x ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUSet _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemS r :: l))))
          | IdS _ ->
            (match localteFunTermInSUSet _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUSetKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUSet _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([Seta], IdS FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUSetKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUSetKItem (r, y) :: l)))))
and localteFunTermInSUList _A
  x0 database = match x0, database with [], database -> None
    | a :: l, database ->
        (match a
          with ItemL x ->
            (match localteFunTermInSUK _A x database
              with None ->
                (match localteFunTermInSUList _A l database with None -> None
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, a :: r))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, ItemL r :: l))))
          | IdL _ ->
            (match localteFunTermInSUList _A l database with None -> None
              | Some (la, (funa, (ty, r))) -> Some (la, (funa, (ty, a :: r))))
          | SUListKItem (x, y) ->
            (match localteFunTermInSUKLabel _A x database
              with None ->
                (match localteFunTermInSUKList _A y database
                  with None ->
                    (match localteFunTermInSUList _A l database
                      with None ->
                        (match getSUKLabelMeaning x with None -> None
                          | Some s ->
                            (if isFunctionItem (equal_label _A) s database
                              then Some (s, (y, ([List], IdL FunHole :: l)))
                              else None))
                      | Some (la, (funa, (ty, r))) ->
                        Some (la, (funa, (ty, a :: r))))
                  | Some (la, (funa, (ty, r))) ->
                    Some (la, (funa, (ty, SUListKItem (x, r) :: l))))
              | Some (la, (funa, (ty, r))) ->
                Some (la, (funa, (ty, SUListKItem (r, y) :: l)))));;

let rec hasFunLabelInSUKItem _A
  x0 database = match x0, database with
    SUKItem (x, y, z), database ->
      hasFunLabelInSUKLabel _A x database ||
        (hasFunLabelInSUKList _A y database ||
          (match getSUKLabelMeaning x with None -> false
            | Some s ->
              (if isFunctionItem (equal_label _A) s database then true
                else false)))
    | SUIdKItem (x, y), database -> false
    | SUHOLE x, database -> false
and hasFunLabelInSUK _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemFactor x ->
            hasFunLabelInSUKItem _A x database || hasFunLabelInSUK _A l database
          | IdFactor _ -> hasFunLabelInSUK _A l database
          | SUKKItem (x, y, _) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUK _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database -> hasFunLabelInSUK _A a database
    | SUList a, database -> hasFunLabelInSUList _A a database
    | SUSet a, database -> hasFunLabelInSUSet _A a database
    | SUMap a, database -> hasFunLabelInSUMap _A a database
    | SUBag a, database -> hasFunLabelInSUBag _A a database
and hasFunLabelInSUBag _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemB (_, _, z) ->
            hasFunLabelInSUBigKWithBag _A z database ||
              hasFunLabelInSUBag _A l database
          | IdB _ -> hasFunLabelInSUBag _A l database)
and hasFunLabelInSUBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database -> hasFunLabelInSUBigKWithBag _A a database
    | SUBigLabel a, database -> hasFunLabelInSUKLabel _A a database
and hasFunLabelInSUKList _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemKl x ->
            hasFunLabelInSUBigKWithLabel _A x database ||
              hasFunLabelInSUKList _A l database
          | IdKl _ -> hasFunLabelInSUKList _A l database)
and hasFunLabelInSUKLabel _A
  x0 database = match x0, database with SUKLabel a, database -> false
    | SUIdKLabel a, database -> false
    | SUKLabelFun (x, y), database ->
        hasFunLabelInSUKLabel _A x database ||
          (hasFunLabelInSUKList _A y database ||
            (match getSUKLabelMeaning x with None -> false
              | Some s ->
                (if isFunctionItem (equal_label _A) s database then true
                  else false)))
and hasFunLabelInSUMap _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemM (x, y) ->
            hasFunLabelInSUK _A x database ||
              (hasFunLabelInSUK _A y database ||
                hasFunLabelInSUMap _A l database)
          | IdM _ -> hasFunLabelInSUMap _A l database
          | SUMapKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUMap _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUSet _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemS x ->
            hasFunLabelInSUK _A x database || hasFunLabelInSUSet _A l database
          | IdS _ -> hasFunLabelInSUSet _A l database
          | SUSetKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUSet _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))))
and hasFunLabelInSUList _A
  x0 database = match x0, database with [], database -> false
    | a :: l, database ->
        (match a
          with ItemL x ->
            hasFunLabelInSUK _A x database || hasFunLabelInSUList _A l database
          | IdL _ -> hasFunLabelInSUList _A l database
          | SUListKItem (x, y) ->
            hasFunLabelInSUKLabel _A x database ||
              (hasFunLabelInSUKList _A y database ||
                (hasFunLabelInSUList _A l database ||
                  (match getSUKLabelMeaning x with None -> false
                    | Some s ->
                      (if isFunctionItem (equal_label _A) s database then true
                        else false)))));;

let rec if_pred b = (if b then single () else bot_pred);;

let rec getRidOfLabel
  = function [] -> Some []
    | (KLabelFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (KFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (KItemFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (ListFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (SetFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (MapFunPat (s, kl), (b, c)) :: l ->
        (match getRidOfLabel l with None -> None
          | Some la -> Some ((kl, (b, c)) :: la))
    | (NormalPat a, (b, c)) :: l -> None;;

let rec getFunRule _A
  s x1 = match s, x1 with s, [] -> None
    | sa, FunPat (s, fl, f) :: l ->
        (if equal_labela _A sa s
          then (match f with None -> getRidOfLabel fl
                 | Some fa -> getRidOfLabel (fl @ [fa]))
          else getFunRule _A sa l)
    | s, MacroPat (v, va, vb) :: l -> getFunRule _A s l
    | s, AnywherePat (v, va, vb, vc) :: l -> getFunRule _A s l
    | s, KRulePat (v, va, vb, vc) :: l -> getFunRule _A s l
    | s, BagRulePat (v, va, vb, vc) :: l -> getFunRule _A s l;;

let rec funEvaluationBool_i_i_i_i_o _A _B _C
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (_, (database, (_, Continue c))) ->
              bind (if_pred (not (hasFunLabelInSUKItem _A c database)))
                (fun () -> single (Stop c))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)))
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (allRules, (database, (subG, Continue c))) ->
              bind (if_pred (hasFunLabelInSUKItem _A c database))
                (fun () ->
                  bind (eq_i_o (localteFunTermInSUKItem _A c database))
                    (fun aa ->
                      (match aa with None -> bot_pred
                        | Some (l, (funa, (_, cr))) ->
                          bind (eq_i_o (getFunRule _A l allRules))
                            (fun ab ->
                              (match ab with None -> bot_pred
                                | Some fl ->
                                  bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B
 _C allRules database subG fl funa (Continue cr))
                                    (fun ac ->
                                      (match ac with Continue _ -> bot_pred
| Stop ca ->
  bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
         (Continue ca))
    (fun ad ->
      (match ad with Continue _ -> bot_pred | Stop cb -> single (Stop cb)
        | Div _ -> bot_pred))
| Div _ -> bot_pred)))))))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)))
and funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, ([], (_, Continue cr))))) -> single (Div cr)
            | (_, (_, (_, ([], (_, Stop _))))) -> bot_pred
            | (_, (_, (_, ([], (_, Div _))))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allRules,
                  (database, (subG, ((p, (_, _)) :: fl, (funa, Continue cr)))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUKList _A _B _C _C p funa [] subG)
                          None)
                     (fun () ->
                       bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C
                              allRules database subG fl funa (Continue cr))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop c -> single (Stop c) | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database,
                      (subG, ((p, (_, c)) :: fl, (funa, Continue cr)))))
                  -> bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B _C allRules
                            database subG fl funa (Continue cr))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop ca ->
                             bind (eq_i_o
                                    (patternMacroingInSUKList _A _B _C _C p funa
                                      [] subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C c acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop ca))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database, (subG, ((p, (r, c)) :: _, (funa, Continue cr)))))
                  -> bind (eq_i_o
                            (patternMacroingInSUKList _A _B _C _C p funa []
                              subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C c acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSubsFactor _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred
               | Some ra ->
                 bind (eq_i_o (substitutionInSUKItem _C cr [(FunHole, ra)]))
                   (fun ae ->
                     (match ae with None -> bot_pred
                       | Some ca ->
                         bind (eq_i_o
                                (typeCheckCondition _A _B _C ca database subG))
                           (fun af ->
                             (match af with None -> bot_pred
                               | Some cb -> single (Stop cb))))))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) ->
                  bot_pred)))));;

let rec oneStepBagRule_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, ([], Continue b)))) -> single (Stop b)
            | (_, (_, (_, ([], Stop _)))) -> bot_pred
            | (_, (_, (_, ([], Div _)))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allFunRules,
                  (database, (subG, ((p, (_, (_, _))) :: fl, Continue b))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUBag _A _B _C _C p b [] subG) None)
                     (fun () ->
                       bind (oneStepBagRule_i_i_i_i_i_o _A _B _C allFunRules
                              database subG fl (Continue b))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ba -> single (Stop ba)
                             | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
              | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (_, (con, _))) :: fl, Continue b))))
                  -> bind (oneStepBagRule_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl (Continue b))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop ba ->
                             bind (eq_i_o
                                    (patternMacroingInSUBag _A _B _C _C p b []
                                      subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C con acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop ba))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (r, (con, _))) :: _, Continue b))))
                  -> bind (eq_i_o
                            (patternMacroingInSUBag _A _B _C _C p b [] subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C con acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allFunRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSUBag _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred | Some ra -> single (Stop ra))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) ->
                  bot_pred)))));;

let rec oneStepBagRule_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a
            with (_, (_, (_, ([], ba)))) ->
              (match ba with (Continue _, Continue _) -> bot_pred
                | (Continue bab, Stop baa) ->
                  (if equal_lista (equal_suB _A _B _C) bab baa then single ()
                    else bot_pred)
                | (Continue _, Div _) -> bot_pred | (Stop _, _) -> bot_pred
                | (Div _, _) -> bot_pred)
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allFunRules, (database, (subG, ((p, (_, (_, _))) :: fl, ba))))
                -> (match ba
                     with (Continue baa, b) ->
                       (match b with Continue _ -> bot_pred
                         | Stop bb ->
                           bind (oneStepBagRule_i_i_i_i_i_i _A _B _C allFunRules
                                  database subG fl (Continue baa) (Stop bb))
                             (fun () ->
                               bind (eq_i_i
                                      (equal_option
(equal_list (equal_prod (equal_metaVar _C) (equal_subsFactor _A _B _C))))
                                      (patternMacroingInSUBag _A _B _C _C p baa
[] subG)
                                      None)
                                 (fun () -> single ()))
                         | Div _ -> bot_pred)
                     | (Stop _, _) -> bot_pred | (Div _, _) -> bot_pred))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (_, (con, _))) :: fl, ba))))
                  -> (match ba
                       with (Continue baa, b) ->
                         (match b with Continue _ -> bot_pred
                           | Stop bb ->
                             bind (oneStepBagRule_i_i_i_i_i_i _A _B _C
                                    allFunRules database subG fl (Continue baa)
                                    (Stop bb))
                               (fun () ->
                                 bind (eq_i_o
(patternMacroingInSUBag _A _B _C _C p baa [] subG))
                                   (fun aa ->
                                     (match aa with None -> bot_pred
                                       | Some acc ->
 bind (eq_i_o (substitutionInSUKItem _C con acc))
   (fun ab ->
     (match ab with None -> bot_pred
       | Some value ->
         bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
                (Continue value))
           (fun ac ->
             (match ac with Continue _ -> bot_pred
               | Stop valuea ->
                 bind (eq_i_i (equal_option (equal_label _A))
                        (getKLabelInSUKItem valuea)
                        (Some (ConstToLabel (BoolConst false))))
                   (fun () -> single ())
               | Div _ -> bot_pred)))))))
                           | Div _ -> bot_pred)
                       | (Stop _, _) -> bot_pred | (Div _, _) -> bot_pred))))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (r, (con, _))) :: _, ba))))
                  -> (match ba with (Continue _, Continue _) -> bot_pred
                       | (Continue baa, Stop ra) ->
                         bind (eq_i_o
                                (patternMacroingInSUBag _A _B _C _C p baa []
                                  subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_i
(equal_option (equal_list (equal_suB _A _B _C))) (substitutionInSUBag _C r acc)
(Some ra))
                                   (fun () ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C con acc))
                                       (fun ab ->
 (match ab with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
            (Continue value))
       (fun ac ->
         (match ac with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst true))))
               (fun () -> single ())
           | Div _ -> bot_pred)))))))
                       | (Continue _, Div _) -> bot_pred
                       | (Stop _, _) -> bot_pred
                       | (Div _, _) -> bot_pred))))));;

let rec minus_nat m n = match m, n with Suc m, Suc n -> minus_nat m n
                    | Zero_nat, n -> Zero_nat
                    | m, Zero_nat -> m;;

let rec oneStepKRuleAux_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, ([], Continue c)))) -> single (Stop c)
            | (_, (_, (_, ([], Stop _)))) -> bot_pred
            | (_, (_, (_, ([], Div _)))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allFunRules,
                  (database, (subG, ((p, (_, (_, _))) :: fl, Continue c))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUK _A _B _C _C p c [] subG) None)
                     (fun () ->
                       bind (oneStepKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                              database subG fl (Continue c))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ca -> single (Stop ca)
                             | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
              | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (_, (con, _))) :: fl, Continue c))))
                  -> bind (oneStepKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl (Continue c))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop ca ->
                             bind (eq_i_o
                                    (patternMacroingInSUK _A _B _C _C p c []
                                      subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C con acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop ca))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (r, (con, _))) :: _, Continue c))))
                  -> bind (eq_i_o
                            (patternMacroingInSUK _A _B _C _C p c [] subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C con acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allFunRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSUK _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred | Some ra -> single (Stop ra))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Stop _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, Div _)))) ->
                  bot_pred)))));;

let rec oneStepKRuleAux_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a
            with (_, (_, (_, ([], (Continue _, Continue _))))) -> bot_pred
            | (_, (_, (_, ([], (Continue c, Stop ca))))) ->
              (if equal_lista (equal_suKFactor _A _B _C) c ca then single ()
                else bot_pred)
            | (_, (_, (_, ([], (Continue _, Div _))))) -> bot_pred
            | (_, (_, (_, ([], (Stop _, _))))) -> bot_pred
            | (_, (_, (_, ([], (Div _, _))))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (_, (_, (_, ((_, (_, (_, _))) :: _, (Continue _, Continue _)))))
                -> bot_pred
              | (allFunRules,
                  (database,
                    (subG, ((p, (_, (_, _))) :: fl, (Continue c, Stop ca)))))
                -> bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                          database subG fl (Continue c) (Stop ca))
                     (fun () ->
                       bind (eq_i_i
                              (equal_option
                                (equal_list
                                  (equal_prod (equal_metaVar _C)
                                    (equal_subsFactor _A _B _C))))
                              (patternMacroingInSUK _A _B _C _C p c [] subG)
                              None)
                         (fun () -> single ()))
              | (_, (_, (_, ((_, (_, (_, _))) :: _, (Continue _, Div _))))) ->
                bot_pred
              | (_, (_, (_, ((_, (_, (_, _))) :: _, (Stop _, _))))) -> bot_pred
              | (_, (_, (_, ((_, (_, (_, _))) :: _, (Div _, _))))) ->
                bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _,
                                (Continue _, Continue _)))))
                  -> bot_pred
                | (allFunRules,
                    (database,
                      (subG,
                        ((p, (_, (con, _))) :: fl, (Continue c, Stop ca)))))
                  -> bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                            database subG fl (Continue c) (Stop ca))
                       (fun () ->
                         bind (eq_i_o
                                (patternMacroingInSUK _A _B _C _C p c [] subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst false))))
           (fun () -> single ())
       | Div _ -> bot_pred)))))))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Continue _, Div _))))) ->
                  bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Stop _, _))))) ->
                  bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Div _, _))))) ->
                  bot_pred)))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _,
                                (Continue _, Continue _)))))
                  -> bot_pred
                | (allFunRules,
                    (database,
                      (subG, ((p, (r, (con, _))) :: _, (Continue c, Stop ra)))))
                  -> bind (eq_i_o
                            (patternMacroingInSUK _A _B _C _C p c [] subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_i
                                    (equal_option
                                      (equal_list (equal_suKFactor _A _B _C)))
                                    (substitutionInSUK _C r acc) (Some ra))
                               (fun () ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst true))))
           (fun () -> single ())
       | Div _ -> bot_pred)))))))
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Continue _, Div _))))) ->
                  bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Stop _, _))))) ->
                  bot_pred
                | (_, (_, (_, ((_, (_, (_, _))) :: _, (Div _, _))))) ->
                  bot_pred)))));;

let rec oneStepKRule_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, (_, [])))) -> single None
            | (_, (_, (_, (_, _ :: _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, (_, [])))) -> bot_pred
              | (allFunRules, (database, (subG, (allKRule, c :: l)))) ->
                bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules database
                       subG allKRule (Continue c) (Stop c))
                  (fun () ->
                    bind (oneStepKRule_i_i_i_i_i_o _A _B _C allFunRules database
                           subG allKRule l)
                      single))))
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, (_, [])))) -> bot_pred
              | (allFunRules, (database, (subG, (allKRule, c :: _)))) ->
                bind (oneStepKRuleAux_i_i_i_i_i_o _A _B _C allFunRules database
                       subG allKRule (Continue c))
                  (fun aa ->
                    (match aa with Continue _ -> bot_pred
                      | Stop ca ->
                        bind (if_pred
                               (not (equal_lista (equal_suKFactor _A _B _C) c
                                      ca)))
                          (fun () -> single (Some (c, ca)))
                      | Div _ -> bot_pred))))));;

let rec oneStepKRule_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, (_, ([], None))))) -> single ()
            | (_, (_, (_, (_, ([], Some _))))) -> bot_pred
            | (_, (_, (_, (_, (_ :: _, _))))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, (_, ([], _))))) -> bot_pred
              | (allFunRules, (database, (subG, (allKRule, (c :: l, s))))) ->
                bind (oneStepKRule_i_i_i_i_i_i _A _B _C allFunRules database
                       subG allKRule l s)
                  (fun () ->
                    bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                           database subG allKRule (Continue c) (Stop c))
                      (fun () -> single ())))))
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, (_, ([], _))))) -> bot_pred
              | (_, (_, (_, (_, (_ :: _, None))))) -> bot_pred
              | (allFunRules,
                  (database, (subG, (allKRule, (c :: _, Some (ca, cb))))))
                -> (if equal_lista (equal_suKFactor _A _B _C) c ca
                     then bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                                 database subG allKRule (Continue c) (Stop cb))
                            (fun () ->
                              bind (if_pred
                                     (not (equal_lista
    (equal_suKFactor _A _B _C) c cb)))
                                (fun () -> single ()))
                     else bot_pred)))));;

let rec typeCheckProgramState _A _B _C
  a database subG =
    (if isGroundTermInSUBag a
      then (match checkTermsInSUBag _A _C a [] [] database subG
             with None -> None
             | Some (_, (_, aa)) -> regularizeInSUBag _A _B _C aa subG)
      else None);;

let rec funEvaluationAux_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, ([], (_, Continue br))))) -> single (Div br)
            | (_, (_, (_, ([], (_, Stop _))))) -> bot_pred
            | (_, (_, (_, ([], (_, Div _))))) -> bot_pred
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allRules,
                  (database, (subG, ((p, (_, _)) :: fl, (funa, Continue br)))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUKList _A _B _C _C p funa [] subG)
                          None)
                     (fun () ->
                       bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules
                              database subG fl funa (Continue br))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop b -> single (Stop b) | Div _ -> bot_pred)))
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
              | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database,
                      (subG, ((p, (_, c)) :: fl, (funa, Continue br)))))
                  -> bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules
                            database subG fl funa (Continue br))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop b ->
                             bind (eq_i_o
                                    (patternMacroingInSUKList _A _B _C _C p funa
                                      [] subG))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some acc ->
                                     bind (eq_i_o
    (substitutionInSUKItem _C c acc))
                                       (fun ac ->
 (match ac with None -> bot_pred
   | Some value ->
     bind (funEvaluationBool_i_i_i_i_o _A _B _C allRules database subG
            (Continue value))
       (fun ad ->
         (match ad with Continue _ -> bot_pred
           | Stop valuea ->
             bind (eq_i_i (equal_option (equal_label _A))
                    (getKLabelInSUKItem valuea)
                    (Some (ConstToLabel (BoolConst false))))
               (fun () -> single (Stop b))
           | Div _ -> bot_pred))))))
                           | Div _ -> bot_pred))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) -> bot_pred)))
          (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allRules,
                    (database, (subG, ((p, (r, c)) :: _, (funa, Continue br)))))
                  -> bind (eq_i_o
                            (patternMacroingInSUKList _A _B _C _C p funa []
                              subG))
                       (fun aa ->
                         (match aa with None -> bot_pred
                           | Some acc ->
                             bind (eq_i_o (substitutionInSUKItem _C c acc))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some value ->
                                     bind (funEvaluationBool_i_i_i_i_o _A _B _C
    allRules database subG (Continue value))
                                       (fun ac ->
 (match ac with Continue _ -> bot_pred
   | Stop valuea ->
     bind (eq_i_i (equal_option (equal_label _A)) (getKLabelInSUKItem valuea)
            (Some (ConstToLabel (BoolConst true))))
       (fun () ->
         bind (eq_i_o (substitutionInSubsFactor _C r acc))
           (fun ad ->
             (match ad with None -> bot_pred
               | Some ra ->
                 bind (eq_i_o (substitutionInSUBag _C br [(FunHole, ra)]))
                   (fun ae ->
                     (match ae with None -> bot_pred
                       | Some b ->
                         bind (eq_i_o
                                (typeCheckProgramState _A _B _C b database
                                  subG))
                           (fun af ->
                             (match af with None -> bot_pred
                               | Some ba -> single (Stop ba))))))))
   | Div _ -> bot_pred))))))
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Stop _))))) -> bot_pred
                | (_, (_, (_, ((_, (_, _)) :: _, (_, Div _))))) ->
                  bot_pred)))));;

let rec funEvaluation_i_i_i_i_o _A _B _C
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (_, (database, (_, Continue b))) ->
              bind (if_pred (not (hasFunLabelInSUBag _A b database)))
                (fun () -> single (Stop b))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)))
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a
            with (allRules, (database, (subG, Continue b))) ->
              bind (if_pred (hasFunLabelInSUBag _A b database))
                (fun () ->
                  bind (eq_i_o (localteFunTermInSUBag _A b database))
                    (fun aa ->
                      (match aa with None -> bot_pred
                        | Some (l, (funa, (_, br))) ->
                          bind (eq_i_o (getFunRule _A l allRules))
                            (fun ab ->
                              (match ab with None -> bot_pred
                                | Some fl ->
                                  bind (funEvaluationAux_i_i_i_i_i_i_o _A _B _C
 allRules database subG fl funa (Continue br))
                                    (fun ac ->
                                      (match ac with Continue _ -> bot_pred
| Stop ba ->
  bind (funEvaluation_i_i_i_i_o _A _B _C allRules database subG (Continue ba))
    (fun ad ->
      (match ad with Continue _ -> bot_pred | Stop bb -> single (Stop bb)
        | Div _ -> bot_pred))
| Div _ -> bot_pred)))))))
            | (_, (_, (_, Stop _))) -> bot_pred
            | (_, (_, (_, Div _))) -> bot_pred)));;

let rec funEvaluationBool_i_i_i_i_i _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, (Continue _, Continue _)))) -> bot_pred
            | (_, (database, (_, (Continue c, Stop ca)))) ->
              (if equal_suKItema _A _B _C c ca
                then bind (if_pred (not (hasFunLabelInSUKItem _A c database)))
                       (fun () -> single ())
                else bot_pred)
            | (_, (_, (_, (Continue _, Div _)))) -> bot_pred
            | (_, (_, (_, (Stop _, _)))) -> bot_pred
            | (_, (_, (_, (Div _, _)))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, (Continue _, Continue _)))) -> bot_pred
            | (allRules, (database, (subG, (Continue c, Stop ca)))) ->
              bind (if_pred (hasFunLabelInSUKItem _A c database))
                (fun () ->
                  bind (eq_i_o (localteFunTermInSUKItem _A c database))
                    (fun aa ->
                      (match aa with None -> bot_pred
                        | Some (l, (funa, (_, cr))) ->
                          bind (eq_i_o (getFunRule _A l allRules))
                            (fun ab ->
                              (match ab with None -> bot_pred
                                | Some fl ->
                                  bind (funEvaluationBoolAux_i_i_i_i_i_i_o _A _B
 _C allRules database subG fl funa (Continue cr))
                                    (fun ac ->
                                      (match ac with Continue _ -> bot_pred
| Stop cb ->
  bind (funEvaluationBool_i_i_i_i_i _A _B _C allRules database subG
         (Continue cb) (Stop ca))
    (fun () -> single ())
| Div _ -> bot_pred)))))))
            | (_, (_, (_, (Continue _, Div _)))) -> bot_pred
            | (_, (_, (_, (Stop _, _)))) -> bot_pred
            | (_, (_, (_, (Div _, _)))) -> bot_pred)));;

let rec funEvaluationBool _A _B _C
  x1 x2 x3 x4 x5 = holds (funEvaluationBool_i_i_i_i_i _A _B _C x1 x2 x3 x4 x5);;

let rec applyAnywhereRuleInSUBag _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemB (x, y, z) ->
            (match
              applyAnywhereRuleInSUBigKWithBag _A _B _C allRules database subG
                (s, (kl, (t, con))) z
              with None -> None
              | Some za ->
                (match
                  applyAnywhereRuleInSUBag _A _B _C allRules database subG
                    (s, (kl, (t, con))) l
                  with None -> None | Some la -> Some (ItemB (x, y, za) :: la)))
          | IdB _ -> None)
and applyAnywhereRuleInSUBigKWithBag _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), SUK a ->
      (match
        applyAnywhereRuleInSUK _A _B _C allRules database subG
          (s, (kl, (t, con))) a
        with None -> None | Some aa -> Some (SUK aa))
    | allRules, database, subG, (s, (kl, (t, con))), SUList a ->
        (match
          applyAnywhereRuleInSUList _A _B _C allRules database subG
            (s, (kl, (t, con))) a
          with None -> None | Some aa -> Some (SUList aa))
    | allRules, database, subG, (s, (kl, (t, con))), SUSet a ->
        (match
          applyAnywhereRuleInSUSet _A _B _C allRules database subG
            (s, (kl, (t, con))) a
          with None -> None | Some aa -> Some (SUSet aa))
    | allRules, database, subG, (s, (kl, (t, con))), SUMap a ->
        (match
          applyAnywhereRuleInSUMap _A _B _C allRules database subG
            (s, (kl, (t, con))) a
          with None -> None | Some aa -> Some (SUMap aa))
    | allRules, database, subG, (s, (kl, (t, con))), SUBag a ->
        (match
          applyAnywhereRuleInSUBag _A _B _C allRules database subG
            (s, (kl, (t, con))) a
          with None -> None | Some aa -> Some (SUBag aa))
and applyAnywhereRuleInSUBigKWithLabel _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), SUBigBag a ->
      (match
        applyAnywhereRuleInSUBigKWithBag _A _B _C allRules database subG
          (s, (kl, (t, con))) a
        with None -> None | Some aa -> Some (SUBigBag aa))
    | allRules, database, subG, (s, (kl, (t, con))), SUBigLabel a ->
        Some (SUBigLabel a)
and applyAnywhereRuleInSUKList _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemKl x ->
            (match
              applyAnywhereRuleInSUBigKWithLabel _A _B _C allRules database subG
                (s, (kl, (t, con))) x
              with None -> None
              | Some xa ->
                (match
                  applyAnywhereRuleInSUKList _A _B _C allRules database subG
                    (s, (kl, (t, con))) l
                  with None -> None | Some la -> Some (ItemKl xa :: la)))
          | IdKl _ -> None)
and applyAnywhereRuleInSUKItem _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), SUKItem (l, r, ty) ->
      (match getSUKLabelMeaning l with None -> None
        | Some sa ->
          (if isFunctionItem (equal_label _A) sa database then None
            else (match
                   applyAnywhereRuleInSUKList _A _B _C allRules database subG
                     (s, (kl, (t, con))) r
                   with None -> None
                   | Some ra ->
                     (if equal_lista (equal_suKl _A _B _C) r ra
                       then (if equal_labela _A s sa
                              then (match
                                     patternMacroingInSUKList _A _B _C _C kl r
                                       [] subG
                                     with None ->
                                       Some [ItemFactor (SUKItem (l, r, ty))]
                                     | Some acc ->
                                       (match substitutionInSUKItem _C con acc
 with None -> Some [ItemFactor (SUKItem (l, r, ty))]
 | Some value ->
   (if funEvaluationBool _A _B _C allRules database subG (Continue value)
         (Stop (SUKItem (SUKLabel (ConstToLabel (BoolConst true)), [], [Bool])))
     then (match substitutionInSUK _C t acc
            with None -> Some [ItemFactor (SUKItem (l, r, ty))]
            | Some a -> Some a)
     else Some [ItemFactor (SUKItem (l, r, ty))])))
                              else Some [ItemFactor (SUKItem (l, r, ty))])
                       else Some [ItemFactor (SUKItem (l, ra, ty))]))))
    | allRules, database, subG, (s, (kl, (t, con))), SUIdKItem (x, ty) -> None
    | allRules, database, subG, (s, (kl, (t, con))), SUHOLE ty ->
        Some [ItemFactor (SUHOLE ty)]
and applyAnywhereRuleInSUK _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemFactor x ->
            (match
              applyAnywhereRuleInSUKItem _A _B _C allRules database subG
                (s, (kl, (t, con))) x
              with None -> None
              | Some xa ->
                (match
                  applyAnywhereRuleInSUK _A _B _C allRules database subG
                    (s, (kl, (t, con))) l
                  with None -> None | Some la -> Some (xa @ la)))
          | IdFactor _ -> None | SUKKItem (_, _, _) -> None)
and applyAnywhereRuleInSUMap _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemM (x, y) ->
            (match
              applyAnywhereRuleInSUK _A _B _C allRules database subG
                (s, (kl, (t, con))) x
              with None -> None
              | Some xa ->
                (match
                  applyAnywhereRuleInSUK _A _B _C allRules database subG
                    (s, (kl, (t, con))) y
                  with None -> None
                  | Some ya ->
                    (match
                      applyAnywhereRuleInSUMap _A _B _C allRules database subG
                        (s, (kl, (t, con))) l
                      with None -> None
                      | Some la -> Some (ItemM (xa, ya) :: la))))
          | IdM _ -> None | SUMapKItem (_, _) -> None)
and applyAnywhereRuleInSUSet _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemS x ->
            (match
              applyAnywhereRuleInSUK _A _B _C allRules database subG
                (s, (kl, (t, con))) x
              with None -> None
              | Some xa ->
                (match
                  applyAnywhereRuleInSUSet _A _B _C allRules database subG
                    (s, (kl, (t, con))) l
                  with None -> None | Some la -> Some (ItemS xa :: la)))
          | IdS _ -> None | SUSetKItem (_, _) -> None)
and applyAnywhereRuleInSUList _A _B _C
  allRules database subG x3 x4 = match allRules, database, subG, x3, x4 with
    allRules, database, subG, (s, (kl, (t, con))), [] -> Some []
    | allRules, database, subG, (s, (kl, (t, con))), a :: l ->
        (match a
          with ItemL x ->
            (match
              applyAnywhereRuleInSUK _A _B _C allRules database subG
                (s, (kl, (t, con))) x
              with None -> None
              | Some xa ->
                (match
                  applyAnywhereRuleInSUList _A _B _C allRules database subG
                    (s, (kl, (t, con))) l
                  with None -> None | Some la -> Some (ItemL xa :: la)))
          | IdL _ -> None | SUListKItem (_, _) -> None);;

let rec applyAnywhereRules _A _B _C
  allRules database subG x3 b = match allRules, database, subG, x3, b with
    allRules, database, subG, [], b -> Some b
    | allRules, database, subG, f :: fl, b ->
        (match applyAnywhereRuleInSUBag _A _B _C allRules database subG f b
          with None -> None
          | Some ba ->
            (if equal_lista (equal_suB _A _B _C) b ba
              then applyAnywhereRules _A _B _C allRules database subG fl b
              else Some ba));;

let rec funAnywhere_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a
            with (allFunRules, (anywheres, (database, (subG, Continue b)))) ->
              bind (funEvaluation_i_i_i_i_o _A _B _C allFunRules database subG
                     (Continue b))
                (fun aa ->
                  (match aa with Continue _ -> bot_pred
                    | Stop ba ->
                      bind (eq_i_i
                             (equal_option (equal_list (equal_suB _A _B _C)))
                             (applyAnywhereRules _A _B _C allFunRules database
                               subG anywheres ba)
                             (Some ba))
                        (fun () -> single (Stop ba))
                    | Div _ -> bot_pred))
            | (_, (_, (_, (_, Stop _)))) -> bot_pred
            | (_, (_, (_, (_, Div _)))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a
            with (allFunRules, (anywheres, (database, (subG, Continue b)))) ->
              bind (funEvaluation_i_i_i_i_o _A _B _C allFunRules database subG
                     (Continue b))
                (fun aa ->
                  (match aa with Continue _ -> bot_pred
                    | Stop ba ->
                      bind (eq_i_o
                             (applyAnywhereRules _A _B _C allFunRules database
                               subG anywheres ba))
                        (fun ab ->
                          (match ab with None -> bot_pred
                            | Some baa ->
                              bind (if_pred
                                     (not (equal_lista (equal_suB _A _B _C) b
    baa)))
                                (fun () ->
                                  bind (funAnywhere_i_i_i_i_i_o _A _B _C
 allFunRules anywheres database subG (Continue baa))
                                    (fun ac ->
                                      (match ac with Continue _ -> bot_pred
| Stop bb -> single (Stop bb) | Div _ -> bot_pred)))))
                    | Div _ -> bot_pred))
            | (_, (_, (_, (_, Stop _)))) -> bot_pred
            | (_, (_, (_, (_, Div _)))) -> bot_pred)));;

let rec funEvaluation_i_i_i_i_i _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a
            with (_, (database, (_, (Continue b, ba)))) ->
              (match ba with Continue _ -> bot_pred
                | Stop baa ->
                  (if equal_lista (equal_suB _A _B _C) b baa
                    then bind (if_pred (not (hasFunLabelInSUBag _A b database)))
                           (fun () -> single ())
                    else bot_pred)
                | Div _ -> bot_pred)
            | (_, (_, (_, (Stop _, _)))) -> bot_pred
            | (_, (_, (_, (Div _, _)))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a
            with (allRules, (database, (subG, (Continue b, ba)))) ->
              (match ba with Continue _ -> bot_pred
                | Stop baa ->
                  bind (if_pred (hasFunLabelInSUBag _A b database))
                    (fun () ->
                      bind (eq_i_o (localteFunTermInSUBag _A b database))
                        (fun aa ->
                          (match aa with None -> bot_pred
                            | Some (l, (funa, (_, br))) ->
                              bind (eq_i_o (getFunRule _A l allRules))
                                (fun ab ->
                                  (match ab with None -> bot_pred
                                    | Some fl ->
                                      bind
(funEvaluationAux_i_i_i_i_i_i_o _A _B _C allRules database subG fl funa
  (Continue br))
(fun ac ->
  (match ac with Continue _ -> bot_pred
    | Stop bb ->
      bind (funEvaluation_i_i_i_i_i _A _B _C allRules database subG
             (Continue bb) (Stop baa))
        (fun () -> single ())
    | Div _ -> bot_pred)))))))
                | Div _ -> bot_pred)
            | (_, (_, (_, (Stop _, _)))) -> bot_pred
            | (_, (_, (_, (Div _, _)))) -> bot_pred)));;

let rec funAnywhere_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a
            with (allFunRules,
                   (anywheres, (database, (subG, (Continue ba, b)))))
              -> (match b with Continue _ -> bot_pred
                   | Stop bb ->
                     bind (funEvaluation_i_i_i_i_i _A _B _C allFunRules database
                            subG (Continue ba) (Stop bb))
                       (fun () ->
                         bind (eq_i_i
                                (equal_option (equal_list (equal_suB _A _B _C)))
                                (applyAnywhereRules _A _B _C allFunRules
                                  database subG anywheres bb)
                                (Some bb))
                           (fun () -> single ()))
                   | Div _ -> bot_pred)
            | (_, (_, (_, (_, (Stop _, _))))) -> bot_pred
            | (_, (_, (_, (_, (Div _, _))))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a
            with (allFunRules,
                   (anywheres, (database, (subG, (Continue ba, b)))))
              -> (match b with Continue _ -> bot_pred
                   | Stop bb ->
                     bind (funEvaluation_i_i_i_i_o _A _B _C allFunRules database
                            subG (Continue ba))
                       (fun aa ->
                         (match aa with Continue _ -> bot_pred
                           | Stop bba ->
                             bind (eq_i_o
                                    (applyAnywhereRules _A _B _C allFunRules
                                      database subG anywheres bba))
                               (fun ab ->
                                 (match ab with None -> bot_pred
                                   | Some bbb ->
                                     bind (funAnywhere_i_i_i_i_i_i _A _B _C
    allFunRules anywheres database subG (Continue bbb) (Stop bb))
                                       (fun () ->
 bind (if_pred (not (equal_lista (equal_suB _A _B _C) ba bbb)))
   (fun () -> single ()))))
                           | Div _ -> bot_pred))
                   | Div _ -> bot_pred)
            | (_, (_, (_, (_, (Stop _, _))))) -> bot_pred
            | (_, (_, (_, (_, (Div _, _))))) -> bot_pred)));;

let rec replaceKCells _A _B _C
  x0 t r = match x0, t, r with [], t, r -> Some []
    | IdB x :: l, t, r -> None
    | ItemB (x, y, z) :: l, t, r ->
        (if equal_vara _B x LittleK
          then (match z
                 with SUK a ->
                   (match replaceKCells _A _B _C l t r with None -> None
                     | Some la ->
                       (if equal_lista (equal_suKFactor _A _B _C) a t
                         then Some (ItemB (x, y, SUK r) :: la)
                         else Some (ItemB (x, y, z) :: la)))
                 | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
                 | SUBag _ -> None)
          else (match replaceKCellsAux _A _B _C z t r with None -> None
                 | Some za ->
                   (match replaceKCells _A _B _C l t r with None -> None
                     | Some la -> Some (ItemB (x, y, za) :: la))))
and replaceKCellsAux _A _B _C
  x0 t r = match x0, t, r with
    SUBag a, t, r ->
      (match replaceKCells _A _B _C a t r with None -> None
        | Some aa -> Some (SUBag aa))
    | SUK v, t, r -> Some (SUK v)
    | SUList v, t, r -> Some (SUList v)
    | SUSet v, t, r -> Some (SUSet v)
    | SUMap v, t, r -> Some (SUMap v);;

let rec getAllKCells _B
  = function [] -> Some []
    | IdB x :: l -> None
    | ItemB (x, y, z) :: l ->
        (if equal_vara _B x LittleK
          then (match z
                 with SUK a ->
                   (match getAllKCells _B l with None -> None
                     | Some la -> Some (a :: la))
                 | SUList _ -> None | SUSet _ -> None | SUMap _ -> None
                 | SUBag _ -> None)
          else (match getAllKCellsAux _B z with None -> None
                 | Some za ->
                   (match getAllKCells _B l with None -> None
                     | Some la -> Some (za @ la))))
and getAllKCellsAux _B = function SUBag a -> getAllKCells _B a
                         | SUK v -> Some []
                         | SUList v -> Some []
                         | SUSet v -> Some []
                         | SUMap v -> Some [];;

let rec krunAux_i_i_i_i_i_i_i_i_i _A _C _D
  x xa xb xc xd xe xf xg xh =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
        (fun (database,
               (subG, (xi, (allFunRules, (allAnywheres, (_, (_, (b, ba))))))))
          -> bind (funAnywhere_i_i_i_i_i_i _A _C _D allFunRules allAnywheres
                    database subG (Continue b) (Stop ba))
               (fun () ->
                 (if equal_nata xi Zero_nat then single () else bot_pred))))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
          (fun (database,
                 (subG,
                   (_, (allFunRules,
                         (allAnywheres, (allKRules, (allBagRules, (b, ba))))))))
            -> bind (funAnywhere_i_i_i_i_i_i _A _C _D allFunRules allAnywheres
                      database subG (Continue b) (Stop ba))
                 (fun () ->
                   bind (oneStepBagRule_i_i_i_i_i_i _A _C _D allFunRules
                          database subG allBagRules (Continue ba) (Stop ba))
                     (fun () ->
                       bind (eq_i_o (getAllKCells _C ba))
                         (fun a ->
                           (match a with None -> bot_pred
                             | Some cl ->
                               bind (oneStepKRule_i_i_i_i_i_i _A _C _D
                                      allFunRules database subG allKRules cl
                                      None)
                                 (fun () -> single ())))))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
            (fun (database,
                   (subG,
                     (n, (allFunRules,
                           (allAnywheres,
                             (allKRules, (allBagRules, (b, bb))))))))
              -> bind (if_pred (less_nat Zero_nat n))
                   (fun () ->
                     bind (funAnywhere_i_i_i_i_i_o _A _C _D allFunRules
                            allAnywheres database subG (Continue b))
                       (fun a ->
                         (match a with Continue _ -> bot_pred
                           | Stop ba ->
                             bind (eq_i_o (getAllKCells _C ba))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneStepKRule_i_i_i_i_i_o _A _C _D
    allFunRules database subG allKRules cl)
                                       (fun ab ->
 (match ab with None -> bot_pred
   | Some (c, ca) ->
     bind (eq_i_o (replaceKCells _A _C _D ba c ca))
       (fun ac ->
         (match ac with None -> bot_pred
           | Some bc ->
             bind (eq_i_o (typeCheckProgramState _A _C _D bc database subG))
               (fun ad ->
                 (match ad with None -> bot_pred
                   | Some baa ->
                     bind (krunAux_i_i_i_i_i_i_i_i_i _A _C _D database subG
                            (minus_nat n one_nata) allFunRules allAnywheres
                            allKRules allBagRules baa bb)
                       (fun () -> single ())))))))))
                           | Div _ -> bot_pred)))))
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
            (fun (database,
                   (subG,
                     (n, (allFunRules,
                           (allAnywheres,
                             (allKRules, (allBagRules, (b, bb))))))))
              -> bind (if_pred (less_nat Zero_nat n))
                   (fun () ->
                     bind (funAnywhere_i_i_i_i_i_o _A _C _D allFunRules
                            allAnywheres database subG (Continue b))
                       (fun a ->
                         (match a with Continue _ -> bot_pred
                           | Stop ba ->
                             bind (eq_i_o (getAllKCells _C ba))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneStepKRule_i_i_i_i_i_i _A _C _D
    allFunRules database subG allKRules cl None)
                                       (fun () ->
 bind (oneStepBagRule_i_i_i_i_i_o _A _C _D allFunRules database subG allBagRules
        (Continue ba))
   (fun ab ->
     (match ab with Continue _ -> bot_pred
       | Stop baa ->
         bind (if_pred (not (equal_lista (equal_suB _A _C _D) ba baa)))
           (fun () ->
             bind (eq_i_o (typeCheckProgramState _A _C _D baa database subG))
               (fun ac ->
                 (match ac with None -> bot_pred
                   | Some bab ->
                     bind (krunAux_i_i_i_i_i_i_i_i_i _A _C _D database subG
                            (minus_nat n one_nata) allFunRules allAnywheres
                            allKRules allBagRules bab bb)
                       (fun () -> single ()))))
       | Div _ -> bot_pred)))))
                           | Div _ -> bot_pred)))))));;

let rec replaceVarSortInSUKList _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUKListElem _A _C b acc beta subG
          with None -> None
          | Some ba ->
            (match replaceVarSortInSUKList _A _C l acc beta subG
              with None -> None | Some la -> Some (ba :: la)))
and replaceVarSortInSUKLabel _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    SUKLabel a, acc, beta, subG -> Some (SUKLabel a)
    | SUKLabelFun (a, b), acc, beta, subG ->
        (match replaceVarSortInSUKLabel _A _C a acc beta subG with None -> None
          | Some aa ->
            (match replaceVarSortInSUKList _A _C b acc beta subG
              with None -> None | Some ba -> Some (SUKLabelFun (aa, ba))))
    | SUIdKLabel n, acc, beta, subG -> Some (SUIdKLabel n)
and replaceVarSortInSUKItem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    SUKItem (l, r, ty), acc, beta, subG ->
      (match getIdInSUKLabel l
        with None ->
          (match replaceVarSortInSUKLabel _A _C l acc beta subG
            with None -> None
            | Some la ->
              (match replaceVarSortInSUKList _A _C r acc beta subG
                with None -> None | Some ra -> Some (SUKItem (la, ra, ty))))
        | Some lx ->
          (match getValueTerm (equal_metaVar _C) lx beta with None -> None
            | Some tya ->
              (match replaceVarSortInSUKList _A _C r acc beta subG
                with None -> None | Some ra -> Some (SUKItem (l, ra, tya)))))
    | SUIdKItem (a, b), acc, beta, subG ->
        (match getValueTerm (equal_metaVar _C) a acc with None -> None
          | Some ba -> Some (SUIdKItem (a, ba)))
    | SUHOLE a, acc, beta, subG -> Some (SUHOLE a)
and replaceVarSortInSUKElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdFactor x, acc, beta, subG ->
      (match getValueTerm (equal_metaVar _C) x acc with None -> None
        | Some ty ->
          (if equal_lista (equal_sort _A) ty [K] then Some (IdFactor x)
            else (if subsortList (equal_sort _A) ty [KItem] subG
                   then Some (ItemFactor (SUIdKItem (x, ty))) else None)))
    | ItemFactor x, acc, beta, subG ->
        (match replaceVarSortInSUKItem _A _C x acc beta subG with None -> None
          | Some xa -> Some (ItemFactor xa))
    | SUKKItem (x, y, ty), acc, beta, subG ->
        (match getIdInSUKLabel x
          with None ->
            (match replaceVarSortInSUKLabel _A _C x acc beta subG
              with None -> None
              | Some xa ->
                (match replaceVarSortInSUKList _A _C y acc beta subG
                  with None -> None | Some ya -> Some (SUKKItem (xa, ya, ty))))
          | Some xx ->
            (match getValueTerm (equal_metaVar _C) xx beta with None -> None
              | Some tya ->
                (match replaceVarSortInSUKList _A _C y acc beta subG
                  with None -> None | Some ya -> Some (SUKKItem (x, ya, tya)))))
and replaceVarSortInSUK _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUKElem _A _C b acc beta subG with None -> None
          | Some ba ->
            (match replaceVarSortInSUK _A _C l acc beta subG with None -> None
              | Some la -> Some (ba :: la)))
and replaceVarSortInSUMapElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdM x, acc, beta, subG -> Some (IdM x)
    | ItemM (x, y), acc, beta, subG ->
        (match replaceVarSortInSUK _A _C x acc beta subG with None -> None
          | Some xa ->
            (match replaceVarSortInSUK _A _C y acc beta subG with None -> None
              | Some ya -> Some (ItemM (xa, ya))))
    | SUMapKItem (x, y), acc, beta, subG ->
        (match replaceVarSortInSUKLabel _A _C x acc beta subG with None -> None
          | Some xa ->
            (match replaceVarSortInSUKList _A _C y acc beta subG
              with None -> None | Some ya -> Some (SUMapKItem (xa, ya))))
and replaceVarSortInSUMap _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUMapElem _A _C b acc beta subG with None -> None
          | Some ba ->
            (match replaceVarSortInSUMap _A _C l acc beta subG with None -> None
              | Some la -> Some (ba :: la)))
and replaceVarSortInSUSetElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdS x, acc, beta, subG -> Some (IdS x)
    | ItemS x, acc, beta, subG ->
        (match replaceVarSortInSUK _A _C x acc beta subG with None -> None
          | Some xa -> Some (ItemS xa))
    | SUSetKItem (x, y), acc, beta, subG ->
        (match replaceVarSortInSUKLabel _A _C x acc beta subG with None -> None
          | Some xa ->
            (match replaceVarSortInSUKList _A _C y acc beta subG
              with None -> None | Some ya -> Some (SUSetKItem (xa, ya))))
and replaceVarSortInSUSet _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUSetElem _A _C b acc beta subG with None -> None
          | Some ba ->
            (match replaceVarSortInSUSet _A _C l acc beta subG with None -> None
              | Some la -> Some (ba :: la)))
and replaceVarSortInSUListElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdL x, acc, beta, subG -> Some (IdL x)
    | ItemL x, acc, beta, subG ->
        (match replaceVarSortInSUK _A _C x acc beta subG with None -> None
          | Some xa -> Some (ItemL xa))
    | SUListKItem (x, y), acc, beta, subG ->
        (match replaceVarSortInSUKLabel _A _C x acc beta subG with None -> None
          | Some xa ->
            (match replaceVarSortInSUKList _A _C y acc beta subG
              with None -> None | Some ya -> Some (SUListKItem (xa, ya))))
and replaceVarSortInSUList _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUListElem _A _C b acc beta subG
          with None -> None
          | Some ba ->
            (match replaceVarSortInSUList _A _C l acc beta subG
              with None -> None | Some la -> Some (ba :: la)))
and replaceVarSortInSUBigKWithBag _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    SUK a, acc, beta, subG ->
      (match replaceVarSortInSUK _A _C a acc beta subG with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, acc, beta, subG ->
        (match replaceVarSortInSUList _A _C a acc beta subG with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, acc, beta, subG ->
        (match replaceVarSortInSUSet _A _C a acc beta subG with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, acc, beta, subG ->
        (match replaceVarSortInSUMap _A _C a acc beta subG with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, acc, beta, subG ->
        (match replaceVarSortInSUBag _A _C a acc beta subG with None -> None
          | Some aa -> Some (SUBag aa))
and replaceVarSortInSUBagElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdB x, acc, beta, subG -> Some (IdB x)
    | ItemB (x, y, z), acc, beta, subG ->
        (match replaceVarSortInSUBigKWithBag _A _C z acc beta subG
          with None -> None | Some za -> Some (ItemB (x, y, za)))
and replaceVarSortInSUBag _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    [], acc, beta, subG -> Some []
    | b :: l, acc, beta, subG ->
        (match replaceVarSortInSUBagElem _A _C b acc beta subG with None -> None
          | Some ba ->
            (match replaceVarSortInSUBag _A _C l acc beta subG with None -> None
              | Some la -> Some (ba :: la)))
and replaceVarSortInSUBigKWithLabel _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    SUBigBag a, acc, beta, subG ->
      (match replaceVarSortInSUBigKWithBag _A _C a acc beta subG
        with None -> None | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, acc, beta, subG ->
        (match replaceVarSortInSUKLabel _A _C a acc beta subG with None -> None
          | Some aa -> Some (SUBigLabel aa))
and replaceVarSortInSUKListElem _A _C
  x0 acc beta subG = match x0, acc, beta, subG with
    IdKl x, acc, beta, subG -> Some (IdKl x)
    | ItemKl x, acc, beta, subG ->
        (match replaceVarSortInSUBigKWithLabel _A _C x acc beta subG
          with None -> None | Some xa -> Some (ItemKl xa));;

let rec getType = function SUKItem (x, y, ty) -> ty
                  | SUIdKItem (a, ty) -> ty
                  | SUHOLE ty -> ty;;

let rec searchBagWithName _A
  x xa1 = match x, xa1 with x, [] -> ([], [])
    | a, b :: l ->
        (match b
          with ItemB (u, v, w) ->
            (let (q, t) = searchBagWithName _A a l in
              (if equal_vara _A a u then (ItemB (u, v, w) :: q, t)
                else (q, ItemB (u, v, w) :: t)))
          | IdB _ -> (let (u, _) = searchBagWithName _A a l in (u, b :: l)));;

let rec onlyIdInSUBag
  = function [] -> true
    | b :: l ->
        (match b with ItemB (_, _, _) -> false | IdB _ -> onlyIdInSUBag l);;

let rec hasIdInSUBag
  = function [] -> false
    | b :: l ->
        (match b with ItemB (_, _, _) -> hasIdInSUBag l | IdB _ -> true);;

let rec checkTermsWithConfi _A _B
  x0 a subG = match x0, a, subG with
    [], a, subG -> (if onlyIdInSUBag a then true else false)
    | b :: l, a, subG ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, ar) = searchBagWithName _B x a in
              (match al
                with [] ->
                  (if hasIdInSUBag a ||
                        membera equal_feature y (Multiplicity Question)
                    then checkTermsWithConfi _A _B l a subG else false)
                | [_] ->
                  checkTermsWithConfiList _A _B z al subG &&
                    checkTermsWithConfi _A _B l ar subG
                | _ :: _ :: _ ->
                  (if membera equal_feature y (Multiplicity Star)
                    then checkTermsWithConfiList _A _B z al subG &&
                           checkTermsWithConfi _A _B l ar subG
                    else false)))
          | IdB _ -> false)
and checkTermsWithConfiAux _A _B
  x0 y subG = match x0, y, subG with
    SUBag x, y, subG ->
      (match y with SUK _ -> false | SUList _ -> false | SUSet _ -> false
        | SUMap _ -> false | SUBag ya -> checkTermsWithConfi _A _B x ya subG)
    | SUK x, y, subG ->
        (match y
          with SUK ya ->
            (match x with [] -> true
              | [ItemFactor u] ->
                (match ya
                  with [] ->
                    (if equal_lista (equal_sort _A) (getType u) [K] then true
                      else false)
                  | [ItemFactor ua] ->
                    (if subsortList (equal_sort _A) (getType ua) (getType u)
                          subG
                      then true else false)
                  | ItemFactor _ :: _ :: _ ->
                    (if equal_lista (equal_sort _A) (getType u) [K] then true
                      else false)
                  | IdFactor _ :: _ ->
                    (if equal_lista (equal_sort _A) (getType u) [K] then true
                      else false)
                  | [SUKKItem (_, _, ty)] ->
                    (if subsortList (equal_sort _A) ty (getType u) subG
                      then true else false)
                  | SUKKItem (_, _, _) :: _ :: _ ->
                    (if equal_lista (equal_sort _A) (getType u) [K] then true
                      else false))
              | [IdFactor _] ->
                (match ya with [] -> true
                  | [ItemFactor u] ->
                    (if equal_lista (equal_sort _A) (getType u) [K] then true
                      else false)
                  | ItemFactor _ :: _ :: _ -> true | IdFactor _ :: _ -> true
                  | [SUKKItem (_, _, ty)] ->
                    (if equal_lista (equal_sort _A) ty [K] then true else false)
                  | SUKKItem (_, _, _) :: _ :: _ -> true)
              | [SUKKItem (_, _, xty)] ->
                (match ya
                  with [] ->
                    (if equal_lista (equal_sort _A) xty [K] then true
                      else false)
                  | [ItemFactor u] ->
                    (if subsortList (equal_sort _A) (getType u) xty subG
                      then true else false)
                  | ItemFactor _ :: _ :: _ ->
                    (if equal_lista (equal_sort _A) xty [K] then true
                      else false)
                  | IdFactor _ :: _ ->
                    (if equal_lista (equal_sort _A) xty [K] then true
                      else false)
                  | [SUKKItem (_, _, ty)] ->
                    (if subsortList (equal_sort _A) ty xty subG then true
                      else false)
                  | SUKKItem (_, _, _) :: _ :: _ ->
                    (if equal_lista (equal_sort _A) xty [K] then true
                      else false))
              | _ :: _ :: _ -> true)
          | SUList _ -> false | SUSet _ -> false | SUMap _ -> false
          | SUBag _ -> false)
    | SUList x, y, subG ->
        (match y with SUK _ -> false | SUList _ -> true | SUSet _ -> false
          | SUMap _ -> false | SUBag _ -> false)
    | SUSet x, y, subG ->
        (match y with SUK _ -> false | SUList _ -> false | SUSet _ -> true
          | SUMap _ -> false | SUBag _ -> false)
    | SUMap x, y, subG ->
        (match y with SUK _ -> false | SUList _ -> false | SUSet _ -> false
          | SUMap _ -> true | SUBag _ -> false)
and checkTermsWithConfiList _A _B
  p x1 subG = match p, x1, subG with p, [], subG -> true
    | p, b :: l, subG ->
        (match b
          with ItemB (_, _, z) ->
            checkTermsWithConfiAux _A _B p z subG &&
              checkTermsWithConfiList _A _B p l subG
          | IdB _ -> false);;

let rec getDomainInIRKList
  = function KListPatNoVar [] -> []
    | KListPatNoVar (x :: l) ->
        getDomainInIRBigKWithLabel x @ getDomainInIRKList (KListPatNoVar l)
    | KListPat ([], b, []) -> []
    | KListPat ([], b, x :: l) ->
        getDomainInIRBigKWithLabel x @ getDomainInIRKList (KListPat ([], b, l))
    | KListPat (x :: l, b, s) ->
        getDomainInIRBigKWithLabel x @ getDomainInIRKList (KListPat (l, b, s))
and getDomainInIRKItem
  = function
    IRKItem (a, b, ty) ->
      (match a with IRKLabel _ -> getDomainInIRKList b
        | IRIdKLabel x -> x :: getDomainInIRKList b)
    | IRIdKItem (a, ty) -> []
    | IRHOLE ty -> []
and getDomainInIRK
  = function KPat ([], b) -> []
    | KPat (x :: l, b) -> getDomainInIRKItem x @ getDomainInIRK (KPat (l, b))
and getDomainInIRMap
  = function MapPat ([], b) -> []
    | MapPat ((x, y) :: l, b) ->
        getDomainInIRK x @ getDomainInIRK y @ getDomainInIRMap (MapPat (l, b))
and getDomainInIRSet
  = function SetPat ([], b) -> []
    | SetPat (x :: l, b) -> getDomainInIRK x @ getDomainInIRSet (SetPat (l, b))
and getDomainInIRList
  = function ListPatNoVar [] -> []
    | ListPatNoVar (x :: l) ->
        getDomainInIRK x @ getDomainInIRList (ListPatNoVar l)
    | ListPat ([], b, []) -> []
    | ListPat ([], b, x :: l) ->
        getDomainInIRK x @ getDomainInIRList (ListPat ([], b, l))
    | ListPat (x :: l, b, s) ->
        getDomainInIRK x @ getDomainInIRList (ListPat (l, b, s))
and getDomainInIRBigKWithBag = function IRK a -> getDomainInIRK a
                               | IRList a -> getDomainInIRList a
                               | IRSet a -> getDomainInIRSet a
                               | IRMap a -> getDomainInIRMap a
                               | IRBag a -> getDomainInIRBag a
and getDomainInIRBag
  = function BagPat ([], b) -> []
    | BagPat ((x, (y, z)) :: l, b) ->
        getDomainInIRBigKWithBag z @ getDomainInIRBag (BagPat (l, b))
and getDomainInIRBigKWithLabel
  = function IRBigBag a -> getDomainInIRBigKWithBag a
    | IRBigLabel a -> [];;

let rec constructSortMap = function [] -> []
                           | a :: l -> (a, [Top]) :: constructSortMap l;;

let rec suToIRInKList _A
  x0 database = match x0, database with [], database -> Some (KListPatNoVar [])
    | b :: l, database ->
        (match suToIRInKList _A l database with None -> None
          | Some (KListPatNoVar la) ->
            (match b
              with ItemKl x ->
                (match suToIRInBigKWithLabel _A x database with None -> None
                  | Some xa -> Some (KListPatNoVar (xa :: la)))
              | IdKl x -> Some (KListPat ([], x, la)))
          | Some (KListPat (la, x, ra)) ->
            (match b
              with ItemKl u ->
                (match suToIRInBigKWithLabel _A u database with None -> None
                  | Some ua -> Some (KListPat (ua :: la, x, ra)))
              | IdKl _ -> None))
and suToIRInKLabel _A
  x0 database = match x0, database with
    SUKLabel a, database -> Some (NormalPat (KLabelMatching (IRKLabel a)))
    | SUKLabelFun (a, b), database ->
        (match getSUKLabelMeaning a with None -> None
          | Some s ->
            (match suToIRInKList _A b database with None -> None
              | Some ba -> Some (KLabelFunPat (s, ba))))
    | SUIdKLabel n, database -> Some (NormalPat (KLabelMatching (IRIdKLabel n)))
and suToIRInKItem _A
  x0 database = match x0, database with
    SUKItem (l, r, ty), database ->
      (match getSUKLabelMeaning l
        with None ->
          (match (suToIRInKLabel _A l database, suToIRInKList _A r database)
            with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
            | (Some (KFunPat (_, _)), _) -> None
            | (Some (KItemFunPat (_, _)), _) -> None
            | (Some (ListFunPat (_, _)), _) -> None
            | (Some (SetFunPat (_, _)), _) -> None
            | (Some (MapFunPat (_, _)), _) -> None
            | (Some (NormalPat (KLabelMatching _)), None) -> None
            | (Some (NormalPat (KLabelMatching la)), Some ra) ->
              Some (NormalPat (KItemMatching (IRKItem (la, ra, ty))))
            | (Some (NormalPat (KItemMatching _)), _) -> None
            | (Some (NormalPat (KListMatching _)), _) -> None
            | (Some (NormalPat (KMatching _)), _) -> None
            | (Some (NormalPat (ListMatching _)), _) -> None
            | (Some (NormalPat (SetMatching _)), _) -> None
            | (Some (NormalPat (MapMatching _)), _) -> None
            | (Some (NormalPat (BagMatching _)), _) -> None)
        | Some s ->
          (if isFunctionItem (equal_label _A) s database
            then (match suToIRInKList _A r database with None -> None
                   | Some ra -> Some (KFunPat (s, ra)))
            else (match
                   (suToIRInKLabel _A l database, suToIRInKList _A r database)
                   with (None, _) -> None
                   | (Some (KLabelFunPat (_, _)), _) -> None
                   | (Some (KFunPat (_, _)), _) -> None
                   | (Some (KItemFunPat (_, _)), _) -> None
                   | (Some (ListFunPat (_, _)), _) -> None
                   | (Some (SetFunPat (_, _)), _) -> None
                   | (Some (MapFunPat (_, _)), _) -> None
                   | (Some (NormalPat (KLabelMatching _)), None) -> None
                   | (Some (NormalPat (KLabelMatching la)), Some ra) ->
                     Some (NormalPat (KItemMatching (IRKItem (la, ra, ty))))
                   | (Some (NormalPat (KItemMatching _)), _) -> None
                   | (Some (NormalPat (KListMatching _)), _) -> None
                   | (Some (NormalPat (KMatching _)), _) -> None
                   | (Some (NormalPat (ListMatching _)), _) -> None
                   | (Some (NormalPat (SetMatching _)), _) -> None
                   | (Some (NormalPat (MapMatching _)), _) -> None
                   | (Some (NormalPat (BagMatching _)), _) -> None)))
    | SUIdKItem (a, b), database ->
        Some (NormalPat (KItemMatching (IRIdKItem (a, b))))
    | SUHOLE a, database -> Some (NormalPat (KItemMatching (IRHOLE a)))
and suToIRInK _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (KMatching (KPat ([], None))))
    | b :: l, database ->
        (match suToIRInK _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching (KPat (t, None)))) ->
            (match b
              with ItemFactor x ->
                (if null t
                  then (match x
                         with SUKItem (_, _, _) ->
                           (let Some (NormalPat (KItemMatching xa)) =
                              suToIRInKItem _A x database in
                             Some (NormalPat (KMatching (KPat ([xa], None)))))
                         | SUIdKItem (xa, xty) ->
                           (if equal_lista (equal_sort _A) xty [K]
                             then Some (NormalPat
 (KMatching (KPat ([], Some xa))))
                             else Some (NormalPat
 (KMatching (KPat ([IRIdKItem (xa, xty)], None)))))
                         | SUHOLE _ ->
                           (let Some (NormalPat (KItemMatching xa)) =
                              suToIRInKItem _A x database in
                             Some (NormalPat (KMatching (KPat ([xa], None))))))
                  else (match suToIRInKItem _A x database with None -> None
                         | Some (KLabelFunPat (_, _)) -> None
                         | Some (KFunPat (_, _)) -> None
                         | Some (KItemFunPat (_, _)) -> None
                         | Some (ListFunPat (_, _)) -> None
                         | Some (SetFunPat (_, _)) -> None
                         | Some (MapFunPat (_, _)) -> None
                         | Some (NormalPat (KLabelMatching _)) -> None
                         | Some (NormalPat (KItemMatching xa)) ->
                           Some (NormalPat (KMatching (KPat (xa :: t, None))))
                         | Some (NormalPat (KListMatching _)) -> None
                         | Some (NormalPat (KMatching _)) -> None
                         | Some (NormalPat (ListMatching _)) -> None
                         | Some (NormalPat (SetMatching _)) -> None
                         | Some (NormalPat (MapMatching _)) -> None
                         | Some (NormalPat (BagMatching _)) -> None))
              | IdFactor x ->
                (if null t then Some (NormalPat (KMatching (KPat ([], Some x))))
                  else Some (NormalPat
                              (KMatching
                                (KPat (IRIdKItem (x, [K]) :: t, None)))))
              | SUKKItem (u, v, _) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some s ->
                           (if isFunctionItem (equal_label _A) s database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (KFunPat (s, va)))
                             else None))
                  else None))
          | Some (NormalPat (KMatching (KPat (t, Some v)))) ->
            (match b
              with ItemFactor x ->
                (match suToIRInKItem _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching xa)) ->
                    Some (NormalPat (KMatching (KPat (xa :: t, None))))
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching _)) -> None
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdFactor x ->
                Some (NormalPat
                       (KMatching (KPat (IRIdKItem (x, [K]) :: t, Some v))))
              | SUKKItem (_, _, _) -> None)
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInMap _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (MapMatching (MapPat ([], None))))
    | b :: l, database ->
        (match suToIRInMap _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching (MapPat (t, None)))) ->
            (match b
              with ItemM (x, y) ->
                (match (suToIRInK _A x database, suToIRInK _A y database)
                  with (None, _) -> None
                  | (Some (KLabelFunPat (_, _)), _) -> None
                  | (Some (KFunPat (_, _)), _) -> None
                  | (Some (KItemFunPat (_, _)), _) -> None
                  | (Some (ListFunPat (_, _)), _) -> None
                  | (Some (SetFunPat (_, _)), _) -> None
                  | (Some (MapFunPat (_, _)), _) -> None
                  | (Some (NormalPat (KLabelMatching _)), _) -> None
                  | (Some (NormalPat (KItemMatching _)), _) -> None
                  | (Some (NormalPat (KListMatching _)), _) -> None
                  | (Some (NormalPat (KMatching _)), None) -> None
                  | (Some (NormalPat (KMatching _)), Some (KLabelFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (KFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (KItemFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (ListFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (SetFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (MapFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KLabelMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KItemMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching xa)),
                      Some (NormalPat (KMatching ya)))
                    -> Some (NormalPat
                              (MapMatching (MapPat ((xa, ya) :: t, None))))
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (ListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (SetMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (MapMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (BagMatching _)))
                    -> None
                  | (Some (NormalPat (ListMatching _)), _) -> None
                  | (Some (NormalPat (SetMatching _)), _) -> None
                  | (Some (NormalPat (MapMatching _)), _) -> None
                  | (Some (NormalPat (BagMatching _)), _) -> None)
              | IdM x -> Some (NormalPat (MapMatching (MapPat (t, Some x))))
              | SUMapKItem (u, v) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some ua ->
                           (if isFunctionItem (equal_label _A) ua database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (MapFunPat (ua, va)))
                             else None))
                  else None))
          | Some (NormalPat (MapMatching (MapPat (t, Some v)))) ->
            (match b
              with ItemM (x, y) ->
                (match (suToIRInK _A x database, suToIRInK _A y database)
                  with (None, _) -> None
                  | (Some (KLabelFunPat (_, _)), _) -> None
                  | (Some (KFunPat (_, _)), _) -> None
                  | (Some (KItemFunPat (_, _)), _) -> None
                  | (Some (ListFunPat (_, _)), _) -> None
                  | (Some (SetFunPat (_, _)), _) -> None
                  | (Some (MapFunPat (_, _)), _) -> None
                  | (Some (NormalPat (KLabelMatching _)), _) -> None
                  | (Some (NormalPat (KItemMatching _)), _) -> None
                  | (Some (NormalPat (KListMatching _)), _) -> None
                  | (Some (NormalPat (KMatching _)), None) -> None
                  | (Some (NormalPat (KMatching _)), Some (KLabelFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (KFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (KItemFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (ListFunPat (_, _)))
                    -> None
                  | (Some (NormalPat (KMatching _)), Some (SetFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)), Some (MapFunPat (_, _))) ->
                    None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KLabelMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KItemMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (KListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching xa)),
                      Some (NormalPat (KMatching ya)))
                    -> Some (NormalPat
                              (MapMatching (MapPat ((xa, ya) :: t, Some v))))
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (ListMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (SetMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (MapMatching _)))
                    -> None
                  | (Some (NormalPat (KMatching _)),
                      Some (NormalPat (BagMatching _)))
                    -> None
                  | (Some (NormalPat (ListMatching _)), _) -> None
                  | (Some (NormalPat (SetMatching _)), _) -> None
                  | (Some (NormalPat (MapMatching _)), _) -> None
                  | (Some (NormalPat (BagMatching _)), _) -> None)
              | IdM _ -> None | SUMapKItem (_, _) -> None)
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInSet _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (SetMatching (SetPat ([], None))))
    | b :: l, database ->
        (match suToIRInSet _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching (SetPat (t, None)))) ->
            (match b
              with ItemS x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (SetMatching (SetPat (xa :: t, None))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdS x -> Some (NormalPat (SetMatching (SetPat (t, Some x))))
              | SUSetKItem (u, v) ->
                (if null t
                  then (match getSUKLabelMeaning u with None -> None
                         | Some ua ->
                           (if isFunctionItem (equal_label _A) ua database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (SetFunPat (ua, va)))
                             else None))
                  else None))
          | Some (NormalPat (SetMatching (SetPat (t, Some v)))) ->
            (match b
              with ItemS x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (SetMatching (SetPat (xa :: t, Some v))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdS _ -> None | SUSetKItem (_, _) -> None)
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInList _A
  x0 database = match x0, database with
    [], database -> Some (NormalPat (ListMatching (ListPatNoVar [])))
    | b :: l, database ->
        (match suToIRInList _A l database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching (ListPatNoVar la))) ->
            (match b
              with ItemL x ->
                (match suToIRInK _A x database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching xa)) ->
                    Some (NormalPat (ListMatching (ListPatNoVar (xa :: la))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdL x -> Some (NormalPat (ListMatching (ListPat ([], x, la))))
              | SUListKItem (u, v) ->
                (if null la
                  then (match getSUKLabelMeaning u with None -> None
                         | Some s ->
                           (if isFunctionItem (equal_label _A) s database
                             then (match suToIRInKList _A v database
                                    with None -> None
                                    | Some va -> Some (ListFunPat (s, va)))
                             else None))
                  else None))
          | Some (NormalPat (ListMatching (ListPat (la, x, ra)))) ->
            (match b
              with ItemL u ->
                (match suToIRInK _A u database with None -> None
                  | Some (KLabelFunPat (_, _)) -> None
                  | Some (KFunPat (_, _)) -> None
                  | Some (KItemFunPat (_, _)) -> None
                  | Some (ListFunPat (_, _)) -> None
                  | Some (SetFunPat (_, _)) -> None
                  | Some (MapFunPat (_, _)) -> None
                  | Some (NormalPat (KLabelMatching _)) -> None
                  | Some (NormalPat (KItemMatching _)) -> None
                  | Some (NormalPat (KListMatching _)) -> None
                  | Some (NormalPat (KMatching ua)) ->
                    Some (NormalPat (ListMatching (ListPat (ua :: la, x, ra))))
                  | Some (NormalPat (ListMatching _)) -> None
                  | Some (NormalPat (SetMatching _)) -> None
                  | Some (NormalPat (MapMatching _)) -> None
                  | Some (NormalPat (BagMatching _)) -> None)
              | IdL _ -> None | SUListKItem (_, _) -> None)
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and suToIRInBigKWithBag _A
  x0 database = match x0, database with
    SUK a, database ->
      (match suToIRInK _A a database with None -> None
        | Some aa ->
          (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
            | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
            | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
            | NormalPat ab ->
              (match ab with KLabelMatching _ -> None | KItemMatching _ -> None
                | KListMatching _ -> None | KMatching ac -> Some (IRK ac)
                | ListMatching _ -> None | SetMatching _ -> None
                | MapMatching _ -> None | BagMatching _ -> None)))
    | SUList a, database ->
        (match suToIRInList _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching ac -> Some (IRList ac)
                  | SetMatching _ -> None | MapMatching _ -> None
                  | BagMatching _ -> None)))
    | SUSet a, database ->
        (match suToIRInSet _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching ac -> Some (IRSet ac) | MapMatching _ -> None
                  | BagMatching _ -> None)))
    | SUMap a, database ->
        (match suToIRInMap _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching _ -> None | MapMatching ac -> Some (IRMap ac)
                  | BagMatching _ -> None)))
    | SUBag a, database ->
        (match suToIRInBag _A a database with None -> None
          | Some aa -> Some (IRBag aa))
and suToIRInBag _A
  x0 database = match x0, database with [], database -> Some (BagPat ([], None))
    | b :: l, database ->
        (match suToIRInBag _A l database with None -> None
          | Some (BagPat (t, None)) ->
            (match b
              with ItemB (a, ba, c) ->
                (match suToIRInBigKWithBag _A c database with None -> None
                  | Some ca -> Some (BagPat ((a, (ba, ca)) :: t, None)))
              | IdB x -> Some (BagPat (t, Some x)))
          | Some (BagPat (t, Some v)) ->
            (match b
              with ItemB (a, ba, c) ->
                (match suToIRInBigKWithBag _A c database with None -> None
                  | Some ca -> Some (BagPat ((a, (ba, ca)) :: t, Some v)))
              | IdB _ -> None))
and suToIRInBigKWithLabel _A
  x0 database = match x0, database with
    SUBigBag a, database ->
      (match suToIRInBigKWithBag _A a database with None -> None
        | Some aa -> Some (IRBigBag aa))
    | SUBigLabel a, database ->
        (match suToIRInKLabel _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching ac -> Some (IRBigLabel ac)
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching _ -> None | ListMatching _ -> None
                  | SetMatching _ -> None | MapMatching _ -> None
                  | BagMatching _ -> None)));;

let rec irToSUInKLabel = function IRKLabel a -> SUKLabel a
                         | IRIdKLabel n -> SUIdKLabel n;;

let rec map f x1 = match f, x1 with f, [] -> []
              | f, x21 :: x22 -> f x21 :: map f x22;;

let rec irToSUInKList _A
  = function
    KListPatNoVar l -> map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) l
    | KListPat (l, a, r) ->
        map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) l @
          [IdKl a] @ map (fun x -> ItemKl (irToSUInBigKWithLabel _A x)) r
and irToSUInKItem _A
  = function
    IRKItem (l, r, ty) -> SUKItem (irToSUInKLabel l, irToSUInKList _A r, ty)
    | IRIdKItem (a, b) -> SUIdKItem (a, b)
    | IRHOLE a -> SUHOLE a
and irToSUInK _A
  (KPat (l, a)) =
    (match a
      with None ->
        map (fun x ->
              (match x with IRKItem (_, _, _) -> ItemFactor (irToSUInKItem _A x)
                | IRIdKItem (u, v) ->
                  (if equal_lista (equal_sort _A) v [K] then IdFactor u
                    else ItemFactor (irToSUInKItem _A x))
                | IRHOLE _ -> ItemFactor (irToSUInKItem _A x)))
          l
      | Some aa ->
        map (fun x ->
              (match x with IRKItem (_, _, _) -> ItemFactor (irToSUInKItem _A x)
                | IRIdKItem (u, v) ->
                  (if equal_lista (equal_sort _A) v [K] then IdFactor u
                    else ItemFactor (irToSUInKItem _A x))
                | IRHOLE _ -> ItemFactor (irToSUInKItem _A x)))
          l @
          [IdFactor aa])
and irToSUInMap _A
  (MapPat (l, a)) =
    (match a
      with None -> map (fun (x, y) -> ItemM (irToSUInK _A x, irToSUInK _A y)) l
      | Some aa ->
        map (fun (x, y) -> ItemM (irToSUInK _A x, irToSUInK _A y)) l @ [IdM aa])
and irToSUInSet _A
  (SetPat (l, a)) =
    (match a with None -> map (fun x -> ItemS (irToSUInK _A x)) l
      | Some aa -> map (fun x -> ItemS (irToSUInK _A x)) l @ [IdS aa])
and irToSUInList _A
  = function ListPatNoVar l -> map (fun x -> ItemL (irToSUInK _A x)) l
    | ListPat (l, a, r) ->
        map (fun x -> ItemL (irToSUInK _A x)) l @
          [IdL a] @ map (fun x -> ItemL (irToSUInK _A x)) r
and irToSUInBigKWithBag _A = function IRK a -> SUK (irToSUInK _A a)
                             | IRList a -> SUList (irToSUInList _A a)
                             | IRSet a -> SUSet (irToSUInSet _A a)
                             | IRMap a -> SUMap (irToSUInMap _A a)
                             | IRBag a -> SUBag (irToSUInBag _A a)
and irToSUInBag _A
  (BagPat (l, a)) =
    (match a
      with None ->
        map (fun (aa, b) ->
              (let (ba, c) = b in ItemB (aa, ba, irToSUInBigKWithBag _A c)))
          l
      | Some aa ->
        map (fun (ab, b) ->
              (let (ba, c) = b in ItemB (ab, ba, irToSUInBigKWithBag _A c)))
          l @
          [IdB aa])
and irToSUInBigKWithLabel _A
  = function IRBigBag a -> SUBigBag (irToSUInBigKWithBag _A a)
    | IRBigLabel a -> SUBigLabel (irToSUInKLabel a);;

let rec hasNoTop _B
  = function [] -> true
    | (a, b) :: l ->
        (if membera (equal_sort _B) b Top then false else hasNoTop _B l);;

let rec inferTypesInFunPat _A _B _C _D _E
  s x1 database subG = match s, x1, database, subG with
    s, [], database, subG -> Some []
    | s, b :: l, database, subG ->
        (match b
          with (KLabelFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y
                     with KLabelSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if equal_lista (equal_sort _A) ty [KLabel]
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUKLabel _A _C sl acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUKLabel _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUKLabel _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((KLabelFunPat (s, klba),
                                     (KLabelSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | KItemSubs _ -> None | KListSubs _ -> None
                     | KSubs _ -> None | ListSubs _ -> None | SetSubs _ -> None
                     | MapSubs _ -> None | BagSubs _ -> None)
              else None)
          | (KFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y with KLabelSubs _ -> None | KItemSubs _ -> None
                     | KListSubs _ -> None
                     | KSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [K] subG
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUK _A _C sl ty acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUK _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUK _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((KFunPat (s, klba), (KSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | ListSubs _ -> None | SetSubs _ -> None
                     | MapSubs _ -> None | BagSubs _ -> None)
              else None)
          | (KItemFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y with KLabelSubs _ -> None
                     | KItemSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [KItem] subG
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUKItem _A _C sl ty acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUKItem _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUKItem _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((KItemFunPat (s, klba),
                                     (KItemSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | KListSubs _ -> None | KSubs _ -> None
                     | ListSubs _ -> None | SetSubs _ -> None
                     | MapSubs _ -> None | BagSubs _ -> None)
              else None)
          | (ListFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y with KLabelSubs _ -> None | KItemSubs _ -> None
                     | KListSubs _ -> None | KSubs _ -> None
                     | ListSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [List] subG
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUList _A _C sl acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUList _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUList _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((ListFunPat (s, klba), (ListSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | SetSubs _ -> None | MapSubs _ -> None
                     | BagSubs _ -> None)
              else None)
          | (SetFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y with KLabelSubs _ -> None | KItemSubs _ -> None
                     | KListSubs _ -> None | KSubs _ -> None
                     | ListSubs _ -> None
                     | SetSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Seta] subG
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUSet _A _C sl acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUSet _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUSet _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((SetFunPat (s, klba), (SetSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | MapSubs _ -> None | BagSubs _ -> None)
              else None)
          | (MapFunPat (ss, kl), (y, z)) ->
            (if equal_labela _A ss s
              then (match y with KLabelSubs _ -> None | KItemSubs _ -> None
                     | KListSubs _ -> None | KSubs _ -> None
                     | ListSubs _ -> None | SetSubs _ -> None
                     | MapSubs sl ->
                       (match
                         (getSort (equal_label _A) s database,
                           getArgSort (equal_label _A) s database)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some ty, Some tyl) ->
                           (if subsortList (equal_sort _A) ty [Map] subG
                             then (match
                                    checkTermsInSUKList _A _C
                                      (irToSUInKList _A kl) tyl []
                                      (constructSortMap (getDomainInIRKList kl))
                                      database subG
                                    with None -> None
                                    | Some (acckl, (betakl, kla)) ->
                                      (match
checkTermsInSUMap _A _C sl acckl betakl database subG with None -> None
| Some (accsl, (betasl, sla)) ->
  (match checkTermsInSUKItem _A _C z [KItem] accsl betasl database subG
    with None -> None
    | Some (accz, (betaz, za)) ->
      (if hasNoTop _A accz && hasNoTop _A betaz
        then (match
               (replaceVarSortInSUKList _A _C kla accz betaz subG,
                 (replaceVarSortInSUMap _A _C sla accz betaz subG,
                   replaceVarSortInSUKItem _A _C za accz betaz subG))
               with (None, _) -> None | (Some _, (None, _)) -> None
               | (Some _, (Some _, None)) -> None
               | (Some klaa, (Some slaa, Some zaa)) ->
                 (match
                   (regularizeInSUKList _A _B _C klaa subG,
                     (regularizeInSUMap _A _D _C slaa subG,
                       regularizeInSUKItem _A _E _C zaa subG))
                   with (None, _) -> None | (Some _, (None, _)) -> None
                   | (Some _, (Some _, None)) -> None
                   | (Some klb, (Some slb, Some zb)) ->
                     (match suToIRInKList _A klb database with None -> None
                       | Some klba ->
                         (match
                           inferTypesInFunPat _A _B _C _D _E s l database subG
                           with None -> None
                           | Some la ->
                             Some ((MapFunPat (s, klba), (MapSubs slb, zb)) ::
                                    la)))))
        else None))))
                             else None))
                     | BagSubs _ -> None)
              else None)
          | (NormalPat _, (_, _)) -> None);;

let rec getConfigurationList
  = function [] -> []
    | TheSyntax x :: l -> getConfigurationList l
    | Imports x :: l -> getConfigurationList l
    | TheConfiguration x :: l -> x :: getConfigurationList l
    | TheRule x :: l -> getConfigurationList l;;

let rec getConListInModule (Module (a, l)) = getConfigurationList l;;

let rec getConfiguration
  = function TheFile (Single (TheRequires s)) -> []
    | TheFile (Single (TheModule m)) -> getConListInModule m
    | TheFile (Con (TheRequires s, l)) -> getConfiguration (TheFile l)
    | TheFile (Con (TheModule m, l)) ->
        getConListInModule m @ getConfiguration (TheFile l);;

let rec toSUInBag
  = function
    BagCon (a, b) ->
      (match (toSUInBagR a, toSUInBagR b) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitBag -> Some []
    | IdBag a -> Some [IdB a]
    | Xml (a, n, t) ->
        (match toSUInBagR t with None -> None
          | Some ta -> Some [ItemB (a, n, SUBag ta)])
    | SingleCell (a, n, t) ->
        (match toSUInBigK t with None -> None
          | Some ta -> Some [ItemB (a, n, ta)])
and toSUInBagR = function KTerm a -> toSUInBag a
                 | KRewrite (l, r) -> None
and toSUInBigKWithBag
  = function
    TheBigK a ->
      (match toSUInBigK a with None -> None | Some aa -> Some (SUBigBag aa))
    | TheBigBag b ->
        (match toSUInBagR b with None -> None
          | Some ba -> Some (SUBigBag (SUBag ba)))
    | TheLabel b ->
        (match toSUInKLabelR b with None -> None
          | Some ba -> Some (SUBigLabel ba))
and toSUInKList
  = function
    KListCon (b, t) ->
      (match (toSUInKListR b, toSUInKListR t) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitKList -> Some []
    | KListItem a ->
        (match toSUInBigKWithBag a with None -> None
          | Some aa -> Some [ItemKl aa])
    | IdKList a -> Some [IdKl a]
and toSUInKListR = function KTerm t -> toSUInKList t
                   | KRewrite (l, r) -> None
and toSUInKLabel
  = function KLabelC a -> Some (SUKLabel a)
    | KLabelFun (a, b) ->
        (match toSUInKLabel a with None -> None
          | Some aa ->
            (match toSUInKListR b with None -> None
              | Some ba -> Some (SUKLabelFun (aa, ba))))
    | IdKLabel n -> Some (SUIdKLabel n)
and toSUInKLabelR = function KTerm n -> toSUInKLabel n
                    | KRewrite (l, r) -> None
and toSUInKItem
  = function
    KItemC (l, r, ty) ->
      (match toSUInKLabelR l with None -> None
        | Some la ->
          (match toSUInKListR r with None -> None
            | Some ra -> Some (SUKItem (la, ra, [ty]))))
    | Constant (a, b) -> Some (SUKItem (SUKLabel (ConstToLabel a), [], [b]))
    | IdKItem (a, b) -> Some (SUIdKItem (a, [b]))
    | HOLE a -> Some (SUHOLE [a])
and toSUInKItemR = function KTerm t -> toSUInKItem t
                   | KRewrite (l, r) -> None
and toSUInK
  = function
    Tilda (a, b) ->
      (match (toSUInKR a, toSUInKR b) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitK -> Some []
    | SingleK a ->
        (match toSUInKItemR a with None -> None
          | Some aa -> Some [ItemFactor aa])
    | IdK a -> Some [IdFactor a]
    | KFun (l, r) ->
        (match toSUInKLabel l with None -> None
          | Some la ->
            (match toSUInKListR r with None -> None
              | Some ra -> Some [SUKKItem (la, ra, [K])]))
and toSUInKR = function KTerm a -> toSUInK a
               | KRewrite (l, r) -> None
and toSUInMap
  = function
    MapCon (a, b) ->
      (match (toSUInMapR a, toSUInMapR b) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitMap -> Some []
    | IdMap a -> Some [IdM a]
    | MapItem (l, r) ->
        (match (toSUInKR l, toSUInKR r) with (None, _) -> None
          | (Some _, None) -> None
          | (Some la, Some ra) -> Some [ItemM (la, ra)])
    | MapFun (l, r) ->
        (match toSUInKLabel l with None -> None
          | Some la ->
            (match toSUInKListR r with None -> None
              | Some ra -> Some [SUMapKItem (la, ra)]))
and toSUInMapR = function KTerm a -> toSUInMap a
                 | KRewrite (l, r) -> None
and toSUInSet
  = function
    SetCon (a, b) ->
      (match (toSUInSetR a, toSUInSetR b) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitSet -> Some []
    | IdSet a -> Some [IdS a]
    | SetItem a ->
        (match toSUInKR a with None -> None | Some aa -> Some [ItemS aa])
    | SetFun (l, r) ->
        (match toSUInKLabel l with None -> None
          | Some la ->
            (match toSUInKListR r with None -> None
              | Some ra -> Some [SUSetKItem (la, ra)]))
and toSUInSetR = function KTerm a -> toSUInSet a
                 | KRewrite (l, r) -> None
and toSUInList
  = function
    ListCon (a, b) ->
      (match (toSUInListR a, toSUInListR b) with (None, _) -> None
        | (Some _, None) -> None | (Some l, Some la) -> Some (l @ la))
    | UnitList -> Some []
    | IdList a -> Some [IdL a]
    | ListItem a ->
        (match toSUInKR a with None -> None | Some aa -> Some [ItemL aa])
    | ListFun (l, r) ->
        (match toSUInKLabel l with None -> None
          | Some la ->
            (match toSUInKListR r with None -> None
              | Some ra -> Some [SUListKItem (la, ra)]))
and toSUInListR = function KTerm a -> toSUInList a
                  | KRewrite (l, r) -> None
and toSUInBigK
  = function
    TheK t -> (match toSUInKR t with None -> None | Some ta -> Some (SUK ta))
    | TheList t ->
        (match toSUInListR t with None -> None | Some ta -> Some (SUList ta))
    | TheSet t ->
        (match toSUInSetR t with None -> None | Some ta -> Some (SUSet ta))
    | TheMap t ->
        (match toSUInMapR t with None -> None | Some ta -> Some (SUMap ta));;

let rec inferTypesInRules _A _B _C
  x0 theory database subG = match x0, theory, database, subG with
    [], theory, database, subG -> Some []
    | FunPat (s, kl, ow) :: l, theory, database, subG ->
        (match ow
          with None ->
            (match inferTypesInFunPat _A _B _C _B _B s kl database subG
              with None -> None
              | Some kla ->
                (match inferTypesInRules _A _B _C l theory database subG
                  with None -> None
                  | Some la -> Some (FunPat (s, kla, None) :: la)))
          | Some (x, (y, z)) ->
            (match
              inferTypesInFunPat _A _B _C _B _B s [(x, (y, z))] database subG
              with None -> None | Some [] -> None
              | Some [(xa, (ya, za))] ->
                (match inferTypesInFunPat _A _B _C _B _B s kl database subG
                  with None -> None
                  | Some kla ->
                    (match inferTypesInRules _A _B _C l theory database subG
                      with None -> None
                      | Some la ->
                        Some (FunPat (s, kla, Some (xa, (ya, za))) :: la)))
              | Some ((_, (_, _)) :: _ :: _) -> None))
    | MacroPat (s, kl, sl) :: l, theory, database, subG ->
        (match
          (getSort (equal_label _A) s database,
            getArgSort (equal_label _A) s database)
          with (None, _) -> None | (Some _, None) -> None
          | (Some ty, Some tyl) ->
            (if subsortList (equal_sort _A) ty [KItem] subG &&
                  not (isFunctionItem (equal_label _A) s database)
              then (match
                     checkTermsInSUKList _A _C (irToSUInKList _A kl) tyl []
                       (constructSortMap (getDomainInIRKList kl)) database subG
                     with None -> None
                     | Some (acckl, (betakl, kla)) ->
                       (match
                         checkTermsInSUK _A _C sl [K] acckl betakl database subG
                         with None -> None
                         | Some (accsl, (betasl, sla)) ->
                           (if hasNoTop _A accsl && hasNoTop _A betasl
                             then (match
                                    (replaceVarSortInSUKList _A _C kla accsl
                                       betasl subG,
                                      replaceVarSortInSUK _A _C sla accsl betasl
subG)
                                    with (None, _) -> None
                                    | (Some _, None) -> None
                                    | (Some klaa, Some slaa) ->
                                      (match
(regularizeInSUKList _A _B _C klaa subG, regularizeInSUK _A _B _C slaa subG)
with (None, _) -> None | (Some _, None) -> None
| (Some klb, Some slb) ->
  (match suToIRInKList _A klb database with None -> None
    | Some klba ->
      (match inferTypesInRules _A _B _C l theory database subG with None -> None
        | Some la -> Some (MacroPat (s, klba, slb) :: la)))))
                             else None)))
              else None))
    | AnywherePat (ss, kl, r, c) :: l, theory, database, subG ->
        (match
          (getSort (equal_label _A) ss database,
            getArgSort (equal_label _A) ss database)
          with (None, _) -> None | (Some _, None) -> None
          | (Some ty, Some tyl) ->
            (if subsortList (equal_sort _A) ty [KItem] subG &&
                  not (isFunctionItem (equal_label _A) ss database)
              then (match
                     checkTermsInSUKList _A _C (irToSUInKList _A kl) tyl []
                       (constructSortMap (getDomainInIRKList kl)) database subG
                     with None -> None
                     | Some (acckl, (betakl, kla)) ->
                       (match
                         checkTermsInSUK _A _C r [K] acckl betakl database subG
                         with None -> None
                         | Some (accr, (betar, ra)) ->
                           (match
                             checkTermsInSUKItem _A _C c [KItem] accr betar
                               database subG
                             with None -> None
                             | Some (accc, (betac, ca)) ->
                               (if hasNoTop _A accc && hasNoTop _A betac
                                 then (match
(replaceVarSortInSUKList _A _C kla accc betac subG,
  (replaceVarSortInSUK _A _C ra accc betac subG,
    replaceVarSortInSUKItem _A _C ca accc betac subG))
with (None, _) -> None | (Some _, (None, _)) -> None
| (Some _, (Some _, None)) -> None
| (Some klaa, (Some sla, Some za)) ->
  (match
    (regularizeInSUKList _A _B _C klaa subG,
      (regularizeInSUK _A _B _C sla subG, regularizeInSUKItem _A _B _C za subG))
    with (None, _) -> None | (Some _, (None, _)) -> None
    | (Some _, (Some _, None)) -> None
    | (Some klb, (Some slb, Some zb)) ->
      (match suToIRInKList _A klb database with None -> None
        | Some klba ->
          (match inferTypesInRules _A _B _C l theory database subG
            with None -> None
            | Some la -> Some (AnywherePat (ss, klba, slb, zb) :: la)))))
                                 else None))))
              else None))
    | KRulePat (kl, r, c, tb) :: l, theory, database, subG ->
        (match
          checkTermsInSUK _A _C (irToSUInK _A kl) [K] []
            (constructSortMap (getDomainInIRK kl)) database subG
          with None -> None
          | Some (acckl, (betakl, kla)) ->
            (match checkTermsInSUK _A _C r [K] acckl betakl database subG
              with None -> None
              | Some (accr, (betar, ra)) ->
                (match
                  checkTermsInSUKItem _A _C c [KItem] accr betar database subG
                  with None -> None
                  | Some (accc, (betac, ca)) ->
                    (if hasNoTop _A accc && hasNoTop _A betac
                      then (match
                             (replaceVarSortInSUK _A _C kla accc betac subG,
                               (replaceVarSortInSUK _A _C ra accc betac subG,
                                 replaceVarSortInSUKItem _A _C ca accc betac
                                   subG))
                             with (None, _) -> None
                             | (Some _, (None, _)) -> None
                             | (Some _, (Some _, None)) -> None
                             | (Some klaa, (Some sla, Some za)) ->
                               (match
                                 (regularizeInSUK _A _B _C klaa subG,
                                   (regularizeInSUK _A _B _C sla subG,
                                     regularizeInSUKItem _A _B _C za subG))
                                 with (None, _) -> None
                                 | (Some _, (None, _)) -> None
                                 | (Some _, (Some _, None)) -> None
                                 | (Some klb, (Some slb, Some zb)) ->
                                   (match suToIRInK _A klb database
                                     with None -> None
                                     | Some (NormalPat (KMatching klba)) ->
                                       (match
 inferTypesInRules _A _B _C l theory database subG with None -> None
 | Some la -> Some (KRulePat (klba, slb, zb, tb) :: la)))))
                      else None))))
    | BagRulePat (kl, r, c, tb) :: l, theory, database, subG ->
        (match getConfiguration theory with [] -> None
          | [confi] ->
            (match toSUInBag confi with None -> None
              | Some confia ->
                (if checkTermsWithConfi _A _B confia (irToSUInBag _A kl) subG &&
                      checkTermsWithConfi _A _B confia r subG
                  then (match
                         checkTermsInSUBag _A _C (irToSUInBag _A kl) []
                           (constructSortMap (getDomainInIRBag kl)) database
                           subG
                         with None -> None
                         | Some (acckl, (betakl, kla)) ->
                           (match
                             checkTermsInSUBag _A _C r acckl betakl database
                               subG
                             with None -> None
                             | Some (accr, (betar, ra)) ->
                               (match
                                 checkTermsInSUKItem _A _C c [KItem] accr betar
                                   database subG
                                 with None -> None
                                 | Some (accc, (betac, ca)) ->
                                   (if hasNoTop _A accc && hasNoTop _A betac
                                     then (match
    (replaceVarSortInSUBag _A _C kla accc betac subG,
      (replaceVarSortInSUBag _A _C ra accc betac subG,
        replaceVarSortInSUKItem _A _C ca accc betac subG))
    with (None, _) -> None | (Some _, (None, _)) -> None
    | (Some _, (Some _, None)) -> None
    | (Some klaa, (Some sla, Some za)) ->
      (match
        (regularizeInSUBag _A _B _C klaa subG,
          (regularizeInSUBag _A _B _C sla subG,
            regularizeInSUKItem _A _B _C za subG))
        with (None, _) -> None | (Some _, (None, _)) -> None
        | (Some _, (Some _, None)) -> None
        | (Some klb, (Some slb, Some zb)) ->
          (match suToIRInBag _A klb database with None -> None
            | Some klba ->
              (match inferTypesInRules _A _B _C l theory database subG
                with None -> None
                | Some la -> Some (BagRulePat (klba, slb, zb, tb) :: la)))))
                                     else None))))
                  else None))
          | _ :: _ :: _ -> None);;

let rec applyMacroRuleInSUBag _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemB (x, y, z) ->
            (match
              (applyMacroRuleInSUBigKWithBag _A _B _C s kl t z subG,
                applyMacroRuleInSUBag _A _B _C s kl t l subG)
              with (None, _) -> None | (Some _, None) -> None
              | (Some za, Some la) -> Some (ItemB (x, y, za) :: la))
          | IdB _ ->
            (match applyMacroRuleInSUBag _A _B _C s kl t l subG
              with None -> None | Some la -> Some (b :: la)))
and applyMacroRuleInSUBigKWithBag _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with
    s, kl, t, SUK a, subG ->
      (match applyMacroRuleInSUK _A _B _C s kl t a subG with None -> None
        | Some aa -> Some (SUK aa))
    | s, kl, t, SUList a, subG ->
        (match applyMacroRuleInSUList _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SUList aa))
    | s, kl, t, SUSet a, subG ->
        (match applyMacroRuleInSUSet _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SUSet aa))
    | s, kl, t, SUMap a, subG ->
        (match applyMacroRuleInSUMap _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SUMap aa))
    | s, kl, t, SUBag a, subG ->
        (match applyMacroRuleInSUBag _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SUBag aa))
and applyMacroRuleInSUBigKWithLabel _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with
    s, kl, t, SUBigBag a, subG ->
      (match applyMacroRuleInSUBigKWithBag _A _B _C s kl t a subG
        with None -> None | Some aa -> Some (SUBigBag aa))
    | s, kl, t, SUBigLabel a, subG ->
        (match applyMacroRuleInSUKLabel _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SUBigLabel aa))
and applyMacroRuleInSUKList _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemKl x ->
            (match
              (applyMacroRuleInSUBigKWithLabel _A _B _C s kl t x subG,
                applyMacroRuleInSUKList _A _B _C s kl t l subG)
              with (None, _) -> None | (Some _, None) -> None
              | (Some xa, Some la) -> Some (ItemKl xa :: la))
          | IdKl _ ->
            (match applyMacroRuleInSUKList _A _B _C s kl t l subG
              with None -> None | Some la -> Some (b :: la)))
and applyMacroRuleInSUKLabel _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with
    s, kl, t, SUKLabel a, subG -> Some (SUKLabel a)
    | s, kl, t, SUIdKLabel a, subG -> Some (SUIdKLabel a)
    | s, kl, t, SUKLabelFun (a, b), subG ->
        (let (aa, ba) =
           (applyMacroRuleInSUKLabel _A _B _C s kl t a subG,
             applyMacroRuleInSUKList _A _B _C s kl t b subG)
           in
          (match aa with None -> None
            | Some ab ->
              (match ba with None -> None
                | Some bb -> Some (SUKLabelFun (ab, bb)))))
and applyMacroRuleInSUKItem _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with
    s, kl, t, SUKItem (l, r, ty), subG ->
      (let (Some la, Some ra) =
         (applyMacroRuleInSUKLabel _A _B _C s kl t l subG,
           applyMacroRuleInSUKList _A _B _C s kl t r subG)
         in
        (match getSUKLabelMeaning la
          with None -> Some [ItemFactor (SUKItem (la, ra, ty))]
          | Some ss ->
            (if equal_labela _A s ss
              then (match patternMacroingInSUKList _A _B _C _C kl ra [] subG
                     with None -> Some [ItemFactor (SUKItem (la, ra, ty))]
                     | Some acc ->
                       (match substitutionInSUK _C t acc
                         with None -> Some [ItemFactor (SUKItem (la, ra, ty))]
                         | Some a -> Some a))
              else Some [ItemFactor (SUKItem (la, ra, ty))])))
    | s, kl, t, SUHOLE a, subG -> Some [ItemFactor (SUHOLE a)]
    | s, kl, t, SUIdKItem (a, b), subG -> Some [ItemFactor (SUIdKItem (a, b))]
and applyMacroRuleInSUK _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemFactor x ->
            (match
              (applyMacroRuleInSUKItem _A _B _C s kl t x subG,
                applyMacroRuleInSUK _A _B _C s kl t l subG)
              with (None, _) -> None | (Some _, None) -> None
              | (Some xa, Some la) -> Some (xa @ la))
          | IdFactor _ ->
            (match applyMacroRuleInSUK _A _B _C s kl t l subG with None -> None
              | Some la -> Some (b :: la))
          | SUKKItem (x, y, ty) ->
            (match
              (applyMacroRuleInSUKLabel _A _B _C s kl t x subG,
                (applyMacroRuleInSUKList _A _B _C s kl t y subG,
                  applyMacroRuleInSUK _A _B _C s kl t l subG))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUKKItem (xa, ya, ty) :: la)))
and applyMacroRuleInSUMap _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemM (x, _) ->
            (match
              (applyMacroRuleInSUK _A _B _C s kl t x subG,
                (applyMacroRuleInSUK _A _B _C s kl t x subG,
                  applyMacroRuleInSUMap _A _B _C s kl t l subG))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some y, Some la)) -> Some (ItemM (xa, y) :: la))
          | IdM _ ->
            (match applyMacroRuleInSUMap _A _B _C s kl t l subG
              with None -> None | Some la -> Some (b :: la))
          | SUMapKItem (x, y) ->
            (match
              (applyMacroRuleInSUKLabel _A _B _C s kl t x subG,
                (applyMacroRuleInSUKList _A _B _C s kl t y subG,
                  applyMacroRuleInSUMap _A _B _C s kl t l subG))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUMapKItem (xa, ya) :: la)))
and applyMacroRuleInSUSet _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemS x ->
            (match
              (applyMacroRuleInSUK _A _B _C s kl t x subG,
                applyMacroRuleInSUSet _A _B _C s kl t l subG)
              with (None, _) -> None | (Some _, None) -> None
              | (Some xa, Some la) -> Some (ItemS xa :: la))
          | IdS _ ->
            (match applyMacroRuleInSUSet _A _B _C s kl t l subG
              with None -> None | Some la -> Some (b :: la))
          | SUSetKItem (x, y) ->
            (match
              (applyMacroRuleInSUKLabel _A _B _C s kl t x subG,
                (applyMacroRuleInSUKList _A _B _C s kl t y subG,
                  applyMacroRuleInSUSet _A _B _C s kl t l subG))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUSetKItem (xa, ya) :: la)))
and applyMacroRuleInSUList _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with s, kl, t, [], subG -> Some []
    | s, kl, t, b :: l, subG ->
        (match b
          with ItemL x ->
            (match
              (applyMacroRuleInSUK _A _B _C s kl t x subG,
                applyMacroRuleInSUList _A _B _C s kl t l subG)
              with (None, _) -> None | (Some _, None) -> None
              | (Some xa, Some la) -> Some (ItemL xa :: la))
          | IdL _ ->
            (match applyMacroRuleInSUList _A _B _C s kl t l subG
              with None -> None | Some la -> Some (b :: la))
          | SUListKItem (x, y) ->
            (match
              (applyMacroRuleInSUKLabel _A _B _C s kl t x subG,
                (applyMacroRuleInSUKList _A _B _C s kl t y subG,
                  applyMacroRuleInSUList _A _B _C s kl t l subG))
              with (None, _) -> None | (Some _, (None, _)) -> None
              | (Some _, (Some _, None)) -> None
              | (Some xa, (Some ya, Some la)) ->
                Some (SUListKItem (xa, ya) :: la)));;

let rec applyMacroRuleInSubsFactor _A _B _C
  s kl t x3 subG = match s, kl, t, x3, subG with
    s, kl, t, KLabelSubs a, subG ->
      (match applyMacroRuleInSUKLabel _A _B _C s kl t a subG with None -> None
        | Some aa -> Some (KLabelSubs aa))
    | s, kl, t, KItemSubs a, subG ->
        (match applyMacroRuleInSUKItem _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (KSubs aa))
    | s, kl, t, KListSubs a, subG ->
        (match applyMacroRuleInSUKList _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (KListSubs aa))
    | s, kl, t, KSubs a, subG ->
        (match applyMacroRuleInSUK _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (KSubs aa))
    | s, kl, t, ListSubs a, subG ->
        (match applyMacroRuleInSUList _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (ListSubs aa))
    | s, kl, t, SetSubs a, subG ->
        (match applyMacroRuleInSUSet _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (SetSubs aa))
    | s, kl, t, MapSubs a, subG ->
        (match applyMacroRuleInSUMap _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (MapSubs aa))
    | s, kl, t, BagSubs a, subG ->
        (match applyMacroRuleInSUBag _A _B _C s kl t a subG with None -> None
          | Some aa -> Some (BagSubs aa));;

let rec suToIRInSubsFactor _A
  x0 database = match x0, database with
    KLabelSubs a, database -> suToIRInKLabel _A a database
    | KItemSubs a, database -> suToIRInKItem _A a database
    | KSubs a, database -> suToIRInK _A a database
    | KListSubs a, database ->
        (match suToIRInKList _A a database with None -> None
          | Some aa -> Some (NormalPat (KListMatching aa)))
    | ListSubs a, database -> suToIRInList _A a database
    | SetSubs a, database -> suToIRInSet _A a database
    | MapSubs a, database -> suToIRInMap _A a database
    | BagSubs a, database ->
        (match suToIRInBag _A a database with None -> None
          | Some aa -> Some (NormalPat (BagMatching aa)));;

let rec irToSUInMatchFactor _A
  = function KLabelMatching a -> KLabelSubs (irToSUInKLabel a)
    | KItemMatching a -> KItemSubs (irToSUInKItem _A a)
    | KMatching a -> KSubs (irToSUInK _A a)
    | KListMatching a -> KListSubs (irToSUInKList _A a)
    | ListMatching a -> ListSubs (irToSUInList _A a)
    | SetMatching a -> SetSubs (irToSUInSet _A a)
    | MapMatching a -> MapSubs (irToSUInMap _A a)
    | BagMatching a -> BagSubs (irToSUInBag _A a);;

let rec irToSUInPat _A
  x0 database = match x0, database with
    KLabelFunPat (s, l), database ->
      KLabelSubs (SUKLabelFun (SUKLabel s, irToSUInKList _A l))
    | KItemFunPat (s, l), database ->
        (match getSort (equal_label _A) s database
          with None ->
            KItemSubs (SUKItem (SUKLabel s, irToSUInKList _A l, [KItem]))
          | Some ty -> KItemSubs (SUKItem (SUKLabel s, irToSUInKList _A l, ty)))
    | KFunPat (s, l), database ->
        KSubs [SUKKItem (SUKLabel s, irToSUInKList _A l, [K])]
    | ListFunPat (s, l), database ->
        ListSubs [SUListKItem (SUKLabel s, irToSUInKList _A l)]
    | SetFunPat (s, l), database ->
        SetSubs [SUSetKItem (SUKLabel s, irToSUInKList _A l)]
    | MapFunPat (s, l), database ->
        MapSubs [SUMapKItem (SUKLabel s, irToSUInKList _A l)]
    | NormalPat a, database -> irToSUInMatchFactor _A a;;

let rec applyMacroRulesInFun _A _B _C
  s kl t x3 database subG = match s, kl, t, x3, database, subG with
    s, kl, t, [], database, subG -> Some []
    | s, kl, t, b :: l, database, subG ->
        (let (u, (v, w)) = b in
          (match
            (applyMacroRuleInSubsFactor _A _B _C s kl t
               (irToSUInPat _A u database) subG,
              (applyMacroRuleInSubsFactor _A _B _C s kl t v subG,
                applyMacroRuleInSUKItem _A _B _C s kl t w subG))
            with (None, _) -> None | (Some _, (None, _)) -> None
            | (Some _, (Some _, None)) -> None
            | (Some _, (Some _, Some [])) -> None
            | (Some ua, (Some va, Some [ItemFactor wa])) ->
              (match suToIRInSubsFactor _A ua database with None -> None
                | Some uaa ->
                  (match applyMacroRulesInFun _A _B _C s kl t l database subG
                    with None -> None
                    | Some la -> Some ((uaa, (va, wa)) :: la)))
            | (Some _, (Some _, Some (ItemFactor _ :: _ :: _))) -> None
            | (Some _, (Some _, Some (IdFactor _ :: _))) -> None
            | (Some _, (Some _, Some (SUKKItem (_, _, _) :: _))) -> None));;

let rec applyMacroRules _A _B _C
  s kl t x3 database subG = match s, kl, t, x3, database, subG with
    s, kl, t, [], database, subG -> Some []
    | s, kl, t, FunPat (ss, la, ow) :: l, database, subG ->
        (match applyMacroRulesInFun _A _B _C s kl t la database subG
          with None -> None
          | Some laa ->
            (match ow
              with None ->
                (match applyMacroRules _A _B _C s kl t l database subG
                  with None -> None
                  | Some lb -> Some (FunPat (ss, laa, ow) :: lb))
              | Some q ->
                (match applyMacroRulesInFun _A _B _C s kl t [q] database subG
                  with None -> None
                  | Some [qa] ->
                    (match applyMacroRules _A _B _C s kl t l database subG
                      with None -> None
                      | Some lb -> Some (FunPat (ss, laa, Some qa) :: lb)))))
    | s, kla, ta, MacroPat (ss, kl, t) :: l, database, subG ->
        (match getSort (equal_label _A) ss database with None -> None
          | Some ty ->
            (let (Some mla, Some taa) =
               (applyMacroRuleInSUKItem _A _B _C s kla ta
                  (SUKItem (SUKLabel ss, irToSUInKList _A kl, ty)) subG,
                 applyMacroRuleInSUK _A _B _C s kla ta t subG)
               in
              (match suToIRInK _A mla database with None -> None
                | Some (KLabelFunPat (_, _)) -> None
                | Some (KFunPat (_, _)) -> None
                | Some (KItemFunPat (_, _)) -> None
                | Some (ListFunPat (_, _)) -> None
                | Some (SetFunPat (_, _)) -> None
                | Some (MapFunPat (_, _)) -> None
                | Some (NormalPat (KLabelMatching _)) -> None
                | Some (NormalPat (KItemMatching _)) -> None
                | Some (NormalPat (KListMatching _)) -> None
                | Some (NormalPat (KMatching (KPat ([], _)))) -> None
                | Some (NormalPat
                         (KMatching
                           (KPat ([IRKItem (IRKLabel ssa, klaa, _)], None))))
                  -> (match applyMacroRules _A _B _C s kla ta l database subG
                       with None -> None
                       | Some la -> Some (MacroPat (ssa, klaa, taa) :: la))
                | Some (NormalPat
                         (KMatching
                           (KPat ([IRKItem (IRKLabel _, _, _)], Some _))))
                  -> None
                | Some (NormalPat
                         (KMatching
                           (KPat (IRKItem (IRKLabel _, _, _) :: _ :: _, _))))
                  -> None
                | Some (NormalPat
                         (KMatching
                           (KPat (IRKItem (IRIdKLabel _, _, _) :: _, _))))
                  -> None
                | Some (NormalPat (KMatching (KPat (IRIdKItem (_, _) :: _, _))))
                  -> None
                | Some (NormalPat (KMatching (KPat (IRHOLE _ :: _, _)))) -> None
                | Some (NormalPat (ListMatching _)) -> None
                | Some (NormalPat (SetMatching _)) -> None
                | Some (NormalPat (MapMatching _)) -> None
                | Some (NormalPat (BagMatching _)) -> None)))
    | s, kl, t, AnywherePat (ss, u, v, w) :: l, database, subG ->
        (match
          (applyMacroRuleInSUKList _A _B _C s kl t (irToSUInKList _A u) subG,
            (applyMacroRuleInSUK _A _B _C s kl t v subG,
              applyMacroRuleInSUKItem _A _B _C s kl t w subG))
          with (None, _) -> None | (Some _, (None, _)) -> None
          | (Some _, (Some _, None)) -> None
          | (Some _, (Some _, Some [])) -> None
          | (Some ua, (Some va, Some [ItemFactor wa])) ->
            (match suToIRInKList _A ua database with None -> None
              | Some uaa ->
                (match applyMacroRules _A _B _C s kl t l database subG
                  with None -> None
                  | Some la -> Some (AnywherePat (ss, uaa, va, wa) :: la)))
          | (Some _, (Some _, Some (ItemFactor _ :: _ :: _))) -> None
          | (Some _, (Some _, Some (IdFactor _ :: _))) -> None
          | (Some _, (Some _, Some (SUKKItem (_, _, _) :: _))) -> None)
    | s, kl, t, KRulePat (u, v, w, tb) :: l, database, subG ->
        (match
          (applyMacroRuleInSUK _A _B _C s kl t (irToSUInK _A u) subG,
            (applyMacroRuleInSUK _A _B _C s kl t v subG,
              applyMacroRuleInSUKItem _A _B _C s kl t w subG))
          with (None, _) -> None | (Some _, (None, _)) -> None
          | (Some _, (Some _, None)) -> None
          | (Some _, (Some _, Some [])) -> None
          | (Some ua, (Some va, Some [ItemFactor wa])) ->
            (match suToIRInK _A ua database with None -> None
              | Some (KLabelFunPat (_, _)) -> None
              | Some (KFunPat (_, _)) -> None
              | Some (KItemFunPat (_, _)) -> None
              | Some (ListFunPat (_, _)) -> None
              | Some (SetFunPat (_, _)) -> None
              | Some (MapFunPat (_, _)) -> None
              | Some (NormalPat (KLabelMatching _)) -> None
              | Some (NormalPat (KItemMatching _)) -> None
              | Some (NormalPat (KListMatching _)) -> None
              | Some (NormalPat (KMatching uaa)) ->
                (match applyMacroRules _A _B _C s kl t l database subG
                  with None -> None
                  | Some la -> Some (KRulePat (uaa, va, wa, tb) :: la))
              | Some (NormalPat (ListMatching _)) -> None
              | Some (NormalPat (SetMatching _)) -> None
              | Some (NormalPat (MapMatching _)) -> None
              | Some (NormalPat (BagMatching _)) -> None)
          | (Some _, (Some _, Some (ItemFactor _ :: _ :: _))) -> None
          | (Some _, (Some _, Some (IdFactor _ :: _))) -> None
          | (Some _, (Some _, Some (SUKKItem (_, _, _) :: _))) -> None)
    | s, kl, t, BagRulePat (u, v, w, tb) :: l, database, subG ->
        (match
          (applyMacroRuleInSUBag _A _B _C s kl t (irToSUInBag _A u) subG,
            (applyMacroRuleInSUBag _A _B _C s kl t v subG,
              applyMacroRuleInSUKItem _A _B _C s kl t w subG))
          with (None, _) -> None | (Some _, (None, _)) -> None
          | (Some _, (Some _, None)) -> None
          | (Some _, (Some _, Some [])) -> None
          | (Some ua, (Some va, Some [ItemFactor wa])) ->
            (match suToIRInBag _A ua database with None -> None
              | Some uaa ->
                (match applyMacroRules _A _B _C s kl t l database subG
                  with None -> None
                  | Some la -> Some (BagRulePat (uaa, va, wa, tb) :: la)))
          | (Some _, (Some _, Some (ItemFactor _ :: _ :: _))) -> None
          | (Some _, (Some _, Some (IdFactor _ :: _))) -> None
          | (Some _, (Some _, Some (SUKKItem (_, _, _) :: _))) -> None);;

let rec applyAllMacroRulesInList _A _B _C
  x0 l confi database subG = match x0, l, confi, database, subG with
    [], l, confi, database, subG ->
      (match l with None -> None | Some la -> Some (la, confi))
    | b :: la, l, confi, database, subG ->
        (match (b, l) with (None, _) -> None | (Some (_, (_, _)), None) -> None
          | (Some (x, (y, z)), Some lb) ->
            (match applyMacroRuleInSUBag _A _B _C x y z confi subG
              with None -> None
              | Some confia ->
                applyAllMacroRulesInList _A _B _C
                  (map (fun a ->
                         (match a with None -> None
                           | Some aa ->
                             (let (ab, ba) = aa in
                              let (bb, c) = ba in
                               (match
                                 applyMacroRules _A _B _C x y z
                                   [MacroPat (ab, bb, c)] database subG
                                 with None -> None
                                 | Some ac ->
                                   (match ac with [] -> None
                                     | FunPat (_, _, _) :: _ -> None
                                     | [MacroPat (ad, bc, ca)] ->
                                       Some (ad, (bc, ca))
                                     | MacroPat (_, _, _) :: _ :: _ -> None
                                     | AnywherePat (_, _, _, _) :: _ -> None
                                     | KRulePat (_, _, _, _) :: _ -> None
                                     | BagRulePat (_, _, _, _) :: _ -> None)))))
                    la)
                  (applyMacroRules _A _B _C x y z lb database subG) confia
                  database subG));;

let rec adjustKSortsInIRK
  = function KPat ([], b) -> KPat ([], b)
    | KPat (x :: l, b) ->
        (let KPat (la, ba) = adjustKSortsInIRK (KPat (l, b)) in
          (match x with IRKItem (_, _, _) -> KPat (x :: la, ba)
            | IRIdKItem (_, []) -> KPat (x :: la, ba)
            | IRIdKItem (_, Bool :: _) -> KPat (x :: la, ba)
            | IRIdKItem (a, [K]) -> KPat (IRIdKItem (a, [KItem]) :: la, ba)
            | IRIdKItem (_, K :: _ :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, KItem :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, KLabel :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, KResult :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, KList :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, List :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Seta :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Map :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Bag :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, OtherSort _ :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Top :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Int :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Float :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, Id :: _) -> KPat (x :: la, ba)
            | IRIdKItem (_, String :: _) -> KPat (x :: la, ba)
            | IRHOLE _ -> KPat (x :: la, ba)));;

let rec adjustKSortsInIRList
  = function
    ListPatNoVar l ->
      (match l with [] -> ListPatNoVar []
        | la :: ll ->
          (match adjustKSortsInIRList (ListPatNoVar ll)
            with ListPatNoVar lla -> ListPatNoVar (adjustKSortsInIRK la :: lla)
            | ListPat (_, _, _) -> ListPatNoVar l))
    | ListPat ([], y, []) -> ListPat ([], y, [])
    | ListPat ([], y, x :: l) ->
        (match adjustKSortsInIRList (ListPat ([], y, l))
          with ListPatNoVar _ -> ListPat ([], y, x :: l)
          | ListPat ([], ya, la) -> ListPat ([], ya, adjustKSortsInIRK x :: la)
          | ListPat (_ :: _, _, _) -> ListPat ([], y, x :: l))
    | ListPat (x :: l, y, s) ->
        (match adjustKSortsInIRList (ListPat (l, y, s))
          with ListPatNoVar _ -> ListPat (x :: l, y, s)
          | ListPat (la, a, b) -> ListPat (adjustKSortsInIRK x :: la, a, b));;

let rec adjustKSortsInIRSet
  = function SetPat ([], b) -> SetPat ([], b)
    | SetPat (x :: l, b) ->
        (let SetPat (la, a) = adjustKSortsInIRSet (SetPat (l, b)) in
          SetPat (adjustKSortsInIRK x :: la, a));;

let rec adjustKSortsInIRMap
  = function MapPat ([], b) -> MapPat ([], b)
    | MapPat ((x, y) :: l, b) ->
        (let MapPat (la, a) = adjustKSortsInIRMap (MapPat (l, b)) in
          MapPat ((adjustKSortsInIRK x, adjustKSortsInIRK y) :: la, a));;

let rec adjustKSortsInIRBigKWithBag
  = function IRK a -> IRK (adjustKSortsInIRK a)
    | IRList a -> IRList (adjustKSortsInIRList a)
    | IRSet a -> IRSet (adjustKSortsInIRSet a)
    | IRMap a -> IRMap (adjustKSortsInIRMap a)
    | IRBag a -> IRBag (adjustKSortsInIRBag a)
and adjustKSortsInIRBag
  = function BagPat ([], b) -> BagPat ([], b)
    | BagPat ((x, (y, z)) :: l, b) ->
        (let BagPat (la, a) = adjustKSortsInIRBag (BagPat (l, b)) in
          BagPat ((x, (y, adjustKSortsInIRBigKWithBag z)) :: la, a));;

let rec adjustKSortsInIRBigKWithLabel
  = function IRBigBag a -> IRBigBag (adjustKSortsInIRBigKWithBag a)
    | IRBigLabel a -> IRBigLabel a;;

let rec adjustKSortsInIRKList
  = function
    KListPatNoVar l ->
      (match l with [] -> KListPatNoVar []
        | la :: ll ->
          (match adjustKSortsInIRKList (KListPatNoVar ll)
            with KListPatNoVar lla ->
              KListPatNoVar (adjustKSortsInIRBigKWithLabel la :: lla)
            | KListPat (_, _, _) -> KListPatNoVar l))
    | KListPat ([], y, []) -> KListPat ([], y, [])
    | KListPat ([], y, x :: l) ->
        (match adjustKSortsInIRKList (KListPat ([], y, l))
          with KListPatNoVar _ -> KListPat ([], y, x :: l)
          | KListPat ([], ya, la) ->
            KListPat ([], ya, adjustKSortsInIRBigKWithLabel x :: la)
          | KListPat (_ :: _, _, _) -> KListPat ([], y, x :: l))
    | KListPat (x :: l, y, s) ->
        (match adjustKSortsInIRKList (KListPat (l, y, s))
          with KListPatNoVar _ -> KListPat (x :: l, y, s)
          | KListPat (la, a, b) ->
            KListPat (adjustKSortsInIRBigKWithLabel x :: la, a, b));;

let rec adjustKSortsInIRKItem
  = function IRKItem (a, b, ty) -> IRKItem (a, adjustKSortsInIRKList b, ty)
    | IRIdKItem (a, ty) -> IRIdKItem (a, ty)
    | IRHOLE ty -> IRHOLE ty;;

let rec adjustKSortsInMatchFactor
  = function KLabelMatching l -> KLabelMatching l
    | KItemMatching l -> KItemMatching (adjustKSortsInIRKItem l)
    | KListMatching l -> KListMatching (adjustKSortsInIRKList l)
    | KMatching l -> KMatching (adjustKSortsInIRK l)
    | ListMatching l -> ListMatching (adjustKSortsInIRList l)
    | SetMatching l -> SetMatching (adjustKSortsInIRSet l)
    | MapMatching l -> MapMatching (adjustKSortsInIRMap l)
    | BagMatching l -> BagMatching (adjustKSortsInIRBag l);;

let rec adjustKSortsInPat
  = function KLabelFunPat (x, y) -> KLabelFunPat (x, adjustKSortsInIRKList y)
    | KFunPat (x, y) -> KFunPat (x, adjustKSortsInIRKList y)
    | KItemFunPat (x, y) -> KItemFunPat (x, adjustKSortsInIRKList y)
    | ListFunPat (x, y) -> ListFunPat (x, adjustKSortsInIRKList y)
    | SetFunPat (x, y) -> SetFunPat (x, adjustKSortsInIRKList y)
    | MapFunPat (x, y) -> MapFunPat (x, adjustKSortsInIRKList y)
    | NormalPat x -> NormalPat (adjustKSortsInMatchFactor x);;

let rec adjustKSortsInFunPatList
  = function [] -> []
    | (x, (y, z)) :: l ->
        (adjustKSortsInPat x, (y, z)) :: adjustKSortsInFunPatList l;;

let rec adjustKSortsInRulePats
  = function [] -> []
    | FunPat (x, y, z) :: l ->
        (match z
          with None ->
            FunPat (x, adjustKSortsInFunPatList y, None) ::
              adjustKSortsInRulePats l
          | Some a ->
            (let (aa, b) = a in
             let (ba, c) = b in
              FunPat
                (x, adjustKSortsInFunPatList y,
                  Some (adjustKSortsInPat aa, (ba, c))) ::
                adjustKSortsInRulePats l))
    | MacroPat (x, y, z) :: l ->
        MacroPat (x, adjustKSortsInIRKList y, z) :: adjustKSortsInRulePats l
    | AnywherePat (a, b, c, d) :: l ->
        AnywherePat (a, adjustKSortsInIRKList b, c, d) ::
          adjustKSortsInRulePats l
    | KRulePat (a, b, c, d) :: l ->
        KRulePat (adjustKSortsInIRK a, b, c, d) :: adjustKSortsInRulePats l
    | BagRulePat (a, b, c, d) :: l ->
        BagRulePat (adjustKSortsInIRBag a, b, c, d) ::
          adjustKSortsInRulePats l;;

let rec composeConfiAndProgInSUBag _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUBagElem _A _C b acc subG with None -> None
          | Some ba ->
            (match composeConfiAndProgInSUBag _A _C l acc subG with None -> None
              | Some la -> Some (ba @ la)))
and composeConfiAndProgInSUBigKWithBag _A _C
  x0 acc subG = match x0, acc, subG with
    SUK a, acc, subG ->
      (match composeConfiAndProgInSUK _A _C a acc subG with None -> None
        | Some aa -> Some (SUK aa))
    | SUList a, acc, subG ->
        (match composeConfiAndProgInSUList _A _C a acc subG with None -> None
          | Some aa -> Some (SUList aa))
    | SUSet a, acc, subG ->
        (match composeConfiAndProgInSUSet _A _C a acc subG with None -> None
          | Some aa -> Some (SUSet aa))
    | SUMap a, acc, subG ->
        (match composeConfiAndProgInSUMap _A _C a acc subG with None -> None
          | Some aa -> Some (SUMap aa))
    | SUBag a, acc, subG ->
        (match composeConfiAndProgInSUBag _A _C a acc subG with None -> None
          | Some aa -> Some (SUBag aa))
and composeConfiAndProgInSUBagElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemB (x, y, z), acc, subG ->
      (match composeConfiAndProgInSUBigKWithBag _A _C z acc subG
        with None -> None | Some za -> Some [ItemB (x, y, za)])
    | IdB s, acc, subG ->
        (match getValueTerm (equal_metaVar _C) s acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs aa -> Some aa))
and composeConfiAndProgInSUBigKWithLabel _A _C
  x0 acc subG = match x0, acc, subG with
    SUBigBag a, acc, subG ->
      (match composeConfiAndProgInSUBigKWithBag _A _C a acc subG
        with None -> None | Some aa -> Some (SUBigBag aa))
    | SUBigLabel a, acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C a acc subG with None -> None
          | Some aa -> Some (SUBigLabel aa))
and composeConfiAndProgInSUKListElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemKl s, acc, subG ->
      (match composeConfiAndProgInSUBigKWithLabel _A _C s acc subG
        with None -> None | Some sa -> Some [ItemKl sa])
    | IdKl s, acc, subG ->
        (match getValueTerm (equal_metaVar _C) s acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None | KItemSubs _ -> None
              | KListSubs aa -> Some aa | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
and composeConfiAndProgInSUKList _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUKListElem _A _C b acc subG
          with None -> None
          | Some a ->
            (match composeConfiAndProgInSUKList _A _C l acc subG
              with None -> None | Some la -> Some (a @ la)))
and composeConfiAndProgInSUKLabel _A _C
  x0 acc subG = match x0, acc, subG with
    SUKLabel a, acc, subG -> Some (SUKLabel a)
    | SUKLabelFun (a, b), acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C a acc subG with None -> None
          | Some aa ->
            (match composeConfiAndProgInSUKList _A _C b acc subG
              with None -> None | Some ba -> Some (SUKLabelFun (aa, ba))))
    | SUIdKLabel n, acc, subG ->
        (match getValueTerm (equal_metaVar _C) n acc with None -> None
          | Some a ->
            (match a with KLabelSubs aa -> Some aa | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
and composeConfiAndProgInSUKItem _A _C
  x0 acc subG = match x0, acc, subG with
    SUKItem (l, r, ty), acc, subG ->
      (match composeConfiAndProgInSUKLabel _A _C l acc subG with None -> None
        | Some la ->
          (match composeConfiAndProgInSUKList _A _C r acc subG with None -> None
            | Some ra -> Some [ItemFactor (SUKItem (la, ra, ty))]))
    | SUIdKItem (a, b), acc, subG ->
        (match getValueTerm (equal_metaVar _C) a acc with None -> None
          | Some aa ->
            (match aa with KLabelSubs _ -> None
              | KItemSubs (SUKItem (l, r, ty)) ->
                (if subsortList (equal_sort _A) ty b subG
                  then Some [ItemFactor (SUKItem (l, r, ty))] else None)
              | KItemSubs (SUIdKItem (_, _)) -> None
              | KItemSubs (SUHOLE ty) ->
                (if subsortList (equal_sort _A) ty b subG
                  then Some [ItemFactor (SUHOLE ty)] else None)
              | KListSubs _ -> None
              | KSubs ab ->
                (if equal_lista (equal_sort _A) b [K] then Some ab else None)
              | ListSubs _ -> None | SetSubs _ -> None | MapSubs _ -> None
              | BagSubs _ -> None))
    | SUHOLE a, acc, subG -> Some [ItemFactor (SUHOLE a)]
and composeConfiAndProgInSUKElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemFactor x, acc, subG -> composeConfiAndProgInSUKItem _A _C x acc subG
    | IdFactor x, acc, subG ->
        (match getValueTerm (equal_metaVar _C) x acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None
              | KItemSubs aa -> Some [ItemFactor aa] | KListSubs _ -> None
              | KSubs aa -> Some aa | ListSubs _ -> None | SetSubs _ -> None
              | MapSubs _ -> None | BagSubs _ -> None))
    | SUKKItem (x, y, z), acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C x acc subG with None -> None
          | Some a ->
            (match composeConfiAndProgInSUKList _A _C y acc subG
              with None -> None | Some b -> Some [SUKKItem (a, b, z)]))
and composeConfiAndProgInSUK _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUKElem _A _C b acc subG with None -> None
          | Some ba ->
            (match composeConfiAndProgInSUK _A _C l acc subG with None -> None
              | Some la -> Some (ba @ la)))
and composeConfiAndProgInSUMapElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemM (x, y), acc, subG ->
      (match composeConfiAndProgInSUK _A _C x acc subG with None -> None
        | Some xa ->
          (match composeConfiAndProgInSUK _A _C x acc subG with None -> None
            | Some ya -> Some [ItemM (xa, ya)]))
    | IdM x, acc, subG ->
        (match getValueTerm (equal_metaVar _C) x acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs _ -> None | MapSubs aa -> Some aa | BagSubs _ -> None))
    | SUMapKItem (x, y), acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C x acc subG with None -> None
          | Some a ->
            (match composeConfiAndProgInSUKList _A _C y acc subG
              with None -> None | Some b -> Some [SUMapKItem (a, b)]))
and composeConfiAndProgInSUMap _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUMapElem _A _C b acc subG with None -> None
          | Some ba ->
            (match composeConfiAndProgInSUMap _A _C l acc subG with None -> None
              | Some la -> Some (ba @ la)))
and composeConfiAndProgInSUSetElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemS x, acc, subG ->
      (match composeConfiAndProgInSUK _A _C x acc subG with None -> None
        | Some xa -> Some [ItemS xa])
    | IdS x, acc, subG ->
        (match getValueTerm (equal_metaVar _C) x acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs _ -> None
              | SetSubs aa -> Some aa | MapSubs _ -> None | BagSubs _ -> None))
    | SUSetKItem (x, y), acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C x acc subG with None -> None
          | Some a ->
            (match composeConfiAndProgInSUKList _A _C y acc subG
              with None -> None | Some b -> Some [SUSetKItem (a, b)]))
and composeConfiAndProgInSUSet _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUSetElem _A _C b acc subG with None -> None
          | Some ba ->
            (match composeConfiAndProgInSUSet _A _C l acc subG with None -> None
              | Some la -> Some (ba @ la)))
and composeConfiAndProgInSUListElem _A _C
  x0 acc subG = match x0, acc, subG with
    ItemL x, acc, subG ->
      (match composeConfiAndProgInSUK _A _C x acc subG with None -> None
        | Some xa -> Some [ItemL xa])
    | IdL x, acc, subG ->
        (match getValueTerm (equal_metaVar _C) x acc with None -> None
          | Some a ->
            (match a with KLabelSubs _ -> None | KItemSubs _ -> None
              | KListSubs _ -> None | KSubs _ -> None | ListSubs aa -> Some aa
              | SetSubs _ -> None | MapSubs _ -> None | BagSubs _ -> None))
    | SUListKItem (x, y), acc, subG ->
        (match composeConfiAndProgInSUKLabel _A _C x acc subG with None -> None
          | Some a ->
            (match composeConfiAndProgInSUKList _A _C y acc subG
              with None -> None | Some b -> Some [SUListKItem (a, b)]))
and composeConfiAndProgInSUList _A _C
  x0 acc subG = match x0, acc, subG with [], acc, subG -> Some []
    | b :: l, acc, subG ->
        (match composeConfiAndProgInSUListElem _A _C b acc subG
          with None -> None
          | Some ba ->
            (match composeConfiAndProgInSUList _A _C l acc subG
              with None -> None | Some la -> Some (ba @ la)));;

let rec uniqueCellNameInSUBag _B
  x0 a = match x0, a with [], a -> Some a
    | b :: l, a ->
        (match b
          with ItemB (x, _, z) ->
            (if membera (equal_var _B) a x then None
              else (match uniqueCellNameInSUBigKWithBag _B z (x :: a)
                     with None -> None
                     | Some aa -> uniqueCellNameInSUBag _B l aa))
          | IdB _ -> uniqueCellNameInSUBag _B l a)
and uniqueCellNameInSUBigKWithBag _B
  x0 a = match x0, a with SUK aa, a -> Some a
    | SUList aa, a -> Some a
    | SUSet aa, a -> Some a
    | SUMap aa, a -> Some a
    | SUBag aa, a -> uniqueCellNameInSUBag _B aa a;;

let rec hasNoBagVarInSUBag
  = function [] -> true
    | b :: l ->
        (match b with ItemB (_, _, _) -> hasNoBagVarInSUBag l
          | IdB _ -> false);;

let rec noDotInSUBag
  = function [] -> true
    | b :: l ->
        (match b
          with ItemB (_, y, z) ->
            (if membera equal_feature y DotDotDot then false
              else noDotInSUBigKWithBag z && noDotInSUBag l)
          | IdB _ -> noDotInSUBag l)
and noDotInSUBigKWithBag = function SUBag a -> noDotInSUBag a
                           | SUK v -> true
                           | SUList v -> true
                           | SUSet v -> true
                           | SUMap v -> true;;

let rec validConfiguration _B
  a = (match uniqueCellNameInSUBag _B a [] with None -> false
        | Some _ -> noDotInSUBag a && hasNoBagVarInSUBag a);;

let rec realConfigurationTest _A _B _C _D
  l theory database subG =
    (let [a] = getConfiguration theory in
      (match toSUInBag a with None -> None
        | Some aa ->
          (if validConfiguration _C aa
            then (match composeConfiAndProgInSUBag _B _A aa l subG
                   with None -> None
                   | Some aaa ->
                     typeCheckProgramState _B _C _D aaa database subG)
            else None)));;

let rec getAllMetaVarsInSUKLabel
  = function SUKLabel a -> []
    | SUKLabelFun (a, b) -> getAllMetaVarsInSUKList b
    | SUIdKLabel n -> [n]
and getAllMetaVarsInSUBigKWithLabel
  = function SUBigBag t -> getAllMetaVarsInSUBigKWithBag t
    | SUBigLabel t -> getAllMetaVarsInSUKLabel t
and getAllMetaVarsInSUKList
  = function [] -> []
    | b :: l ->
        (match b with ItemKl a -> getAllMetaVarsInSUBigKWithLabel a
          | IdKl a -> [a])
and getAllMetaVarsInSUKItem
  = function
    SUKItem (l, r, ty) -> getAllMetaVarsInSUKLabel l @ getAllMetaVarsInSUKList r
    | SUIdKItem (a, b) -> [a]
    | SUHOLE a -> []
and getAllMetaVarsInSUK
  = function [] -> []
    | b :: l ->
        (match b with ItemFactor a -> getAllMetaVarsInSUKItem a
          | IdFactor x -> [x]
          | SUKKItem (la, r, _) ->
            getAllMetaVarsInSUKLabel la @ getAllMetaVarsInSUKList r)
and getAllMetaVarsInSUMap
  = function [] -> []
    | b :: l ->
        (match b
          with ItemM (x, y) -> getAllMetaVarsInSUK x @ getAllMetaVarsInSUK y
          | IdM x -> [x]
          | SUMapKItem (la, r) ->
            getAllMetaVarsInSUKLabel la @ getAllMetaVarsInSUKList r)
and getAllMetaVarsInSUSet
  = function [] -> []
    | b :: l ->
        (match b with ItemS a -> getAllMetaVarsInSUK a | IdS x -> [x]
          | SUSetKItem (la, r) ->
            getAllMetaVarsInSUKLabel la @ getAllMetaVarsInSUKList r)
and getAllMetaVarsInSUList
  = function [] -> []
    | b :: l ->
        (match b with ItemL a -> getAllMetaVarsInSUK a | IdL x -> [x]
          | SUListKItem (la, r) ->
            getAllMetaVarsInSUKLabel la @ getAllMetaVarsInSUKList r)
and getAllMetaVarsInSUBigKWithBag = function SUBag b -> getAllMetaVarsInSUBag b
                                    | SUK t -> getAllMetaVarsInSUK t
                                    | SUList t -> getAllMetaVarsInSUList t
                                    | SUSet t -> getAllMetaVarsInSUSet t
                                    | SUMap t -> getAllMetaVarsInSUMap t
and getAllMetaVarsInSUBag
  = function [] -> []
    | b :: l ->
        (match b with ItemB (_, _, a) -> getAllMetaVarsInSUBigKWithBag a
          | IdB x -> [x]);;

let rec getAllMetaVarsInSubsFactor
  = function KLabelSubs a -> getAllMetaVarsInSUKLabel a
    | KItemSubs a -> getAllMetaVarsInSUKItem a
    | KListSubs a -> getAllMetaVarsInSUKList a
    | KSubs a -> getAllMetaVarsInSUK a
    | ListSubs a -> getAllMetaVarsInSUList a
    | SetSubs a -> getAllMetaVarsInSUSet a
    | MapSubs a -> getAllMetaVarsInSUMap a
    | BagSubs a -> getAllMetaVarsInSUBag a;;

let rec getAllMetaVarsInIRKLabel = function IRKLabel a -> []
                                   | IRIdKLabel n -> [n];;

let rec foldl f a x2 = match f, a, x2 with f, a, [] -> a
                | f, a, x :: xs -> foldl f (f a x) xs;;

let rec getAllMetaVarsInIRKList
  = function
    KListPatNoVar a ->
      foldl (fun acc y -> getAllMetaVarsInIRBigKWithLabel y @ acc) [] a
    | KListPat (a, b, c) ->
        b :: foldl (fun acc y -> getAllMetaVarsInIRBigKWithLabel y @ acc) []
               (a @ c)
and getAllMetaVarsInIRKItem
  = function
    IRKItem (l, r, ty) -> getAllMetaVarsInIRKLabel l @ getAllMetaVarsInIRKList r
    | IRIdKItem (a, b) -> [a]
    | IRHOLE a -> []
and getAllMetaVarsInIRK
  (KPat (a, b)) =
    (match b
      with None -> foldl (fun acc y -> getAllMetaVarsInIRKItem y @ acc) [] a
      | Some x ->
        x :: foldl (fun acc y -> getAllMetaVarsInIRKItem y @ acc) [] a)
and getAllMetaVarsInIRMap
  (MapPat (a, b)) =
    (match b
      with None ->
        foldl (fun acc (x, y) ->
                getAllMetaVarsInIRK x @ getAllMetaVarsInIRK y @ acc)
          [] a
      | Some x ->
        x :: foldl (fun acc (xa, y) ->
                     getAllMetaVarsInIRK xa @ getAllMetaVarsInIRK y @ acc)
               [] a)
and getAllMetaVarsInIRSet
  (SetPat (a, b)) =
    (match b with None -> foldl (fun acc y -> getAllMetaVarsInIRK y @ acc) [] a
      | Some x -> x :: foldl (fun acc y -> getAllMetaVarsInIRK y @ acc) [] a)
and getAllMetaVarsInIRList
  = function
    ListPatNoVar a -> foldl (fun acc y -> getAllMetaVarsInIRK y @ acc) [] a
    | ListPat (a, b, c) ->
        b :: foldl (fun acc y -> getAllMetaVarsInIRK y @ acc) [] (a @ c)
and getAllMetaVarsInIRBigKWithBag = function IRBag b -> getAllMetaVarsInIRBag b
                                    | IRK t -> getAllMetaVarsInIRK t
                                    | IRList t -> getAllMetaVarsInIRList t
                                    | IRSet t -> getAllMetaVarsInIRSet t
                                    | IRMap t -> getAllMetaVarsInIRMap t
and getAllMetaVarsInIRBag
  (BagPat (a, b)) =
    (match b
      with None ->
        foldl (fun acc (_, (_, z)) -> getAllMetaVarsInIRBigKWithBag z @ acc) []
          a
      | Some x ->
        x :: foldl (fun acc (_, (_, z)) ->
                     getAllMetaVarsInIRBigKWithBag z @ acc)
               [] a)
and getAllMetaVarsInIRBigKWithLabel
  = function IRBigBag t -> getAllMetaVarsInIRBigKWithBag t
    | IRBigLabel t -> getAllMetaVarsInIRKLabel t;;

let rec getAllMetaVarsInMatchFactor
  = function KLabelMatching a -> getAllMetaVarsInIRKLabel a
    | KItemMatching a -> getAllMetaVarsInIRKItem a
    | KListMatching a -> getAllMetaVarsInIRKList a
    | KMatching a -> getAllMetaVarsInIRK a
    | ListMatching a -> getAllMetaVarsInIRList a
    | SetMatching a -> getAllMetaVarsInIRSet a
    | MapMatching a -> getAllMetaVarsInIRMap a
    | BagMatching a -> getAllMetaVarsInIRBag a;;

let rec getAllMetaVarsInPat
  = function KLabelFunPat (a, b) -> getAllMetaVarsInIRKList b
    | KFunPat (a, b) -> getAllMetaVarsInIRKList b
    | KItemFunPat (a, b) -> getAllMetaVarsInIRKList b
    | ListFunPat (a, b) -> getAllMetaVarsInIRKList b
    | SetFunPat (a, b) -> getAllMetaVarsInIRKList b
    | MapFunPat (a, b) -> getAllMetaVarsInIRKList b
    | NormalPat a -> getAllMetaVarsInMatchFactor a;;

let rec pred_list p x1 = match p, x1 with p, [] -> true
                    | p, x :: xs -> p x && pred_list p xs;;

let rec wellFormRules _C
  = function [] -> true
    | FunPat (s, rl, a) :: l ->
        foldl (fun b (x, (y, z)) ->
                b && pred_list
                       (membera (equal_metaVar _C) (getAllMetaVarsInPat x))
                       (getAllMetaVarsInSubsFactor y @
                         getAllMetaVarsInSUKItem z))
          true (match a with None -> rl | Some aa -> aa :: rl) &&
          wellFormRules _C l
    | MacroPat (s, a, b) :: l ->
        pred_list (membera (equal_metaVar _C) (getAllMetaVarsInIRKList a))
          (getAllMetaVarsInSUK b) &&
          wellFormRules _C l
    | AnywherePat (ss, a, b, c) :: l ->
        pred_list (membera (equal_metaVar _C) (getAllMetaVarsInIRKList a))
          (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c) &&
          wellFormRules _C l
    | KRulePat (a, b, c, tb) :: l ->
        pred_list (membera (equal_metaVar _C) (getAllMetaVarsInIRK a))
          (getAllMetaVarsInSUK b @ getAllMetaVarsInSUKItem c) &&
          wellFormRules _C l
    | BagRulePat (a, b, c, tb) :: l ->
        pred_list (membera (equal_metaVar _C) (getAllMetaVarsInIRBag a))
          (getAllMetaVarsInSUBag b @ getAllMetaVarsInSUKItem c) &&
          wellFormRules _C l;;

let rec subSyntaxInSUK _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUKElem _A _B _C s kl b subG ||
          subSyntaxInSUK _A _B _C s kl l subG
and subSyntaxInSUBigKWithBag _A _B _C
  s kl x2 subG = match s, kl, x2, subG with
    s, kl, SUK a, subG -> subSyntaxInSUK _A _B _C s kl a subG
    | s, kl, SUList a, subG -> subSyntaxInSUList _A _B _C s kl a subG
    | s, kl, SUSet a, subG -> subSyntaxInSUSet _A _B _C s kl a subG
    | s, kl, SUMap a, subG -> subSyntaxInSUMap _A _B _C s kl a subG
    | s, kl, SUBag a, subG -> subSyntaxInSUBag _A _B _C s kl a subG
and subSyntaxInSUBagElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdB x, subG -> false
    | s, kl, ItemB (x, y, z), subG ->
        subSyntaxInSUBigKWithBag _A _B _C s kl z subG
and subSyntaxInSUBag _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUBagElem _A _B _C s kl b subG ||
          subSyntaxInSUBag _A _B _C s kl l subG
and subSyntaxInSUBigKWithLabel _A _B _C
  s kl x2 subG = match s, kl, x2, subG with
    s, kl, SUBigBag a, subG -> subSyntaxInSUBigKWithBag _A _B _C s kl a subG
    | s, kl, SUBigLabel a, subG -> subSyntaxInSUKLabel _A _B _C s kl a subG
and subSyntaxInSUKListElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdKl x, subG -> false
    | s, kl, ItemKl x, subG -> subSyntaxInSUBigKWithLabel _A _B _C s kl x subG
and subSyntaxInSUKList _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUKListElem _A _B _C s kl b subG ||
          subSyntaxInSUKList _A _B _C s kl l subG
and subSyntaxInSUKLabel _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, SUKLabel a, subG -> false
    | s, kl, SUIdKLabel a, subG -> false
    | s, kl, SUKLabelFun (a, b), subG ->
        subSyntaxInSUKLabel _A _B _C s kl a subG ||
          subSyntaxInSUKList _A _B _C s kl b subG
and subSyntaxInSUKItem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with
    s, kl, SUKItem (l, r, ty), subG ->
      (match getSUKLabelMeaning l
        with None ->
          subSyntaxInSUKLabel _A _B _C s kl l subG ||
            subSyntaxInSUKList _A _B _C s kl r subG
        | Some ss ->
          (if equal_labela _A s ss
            then (match syntacticMonoidInSUKList _A _B _C kl r subG
                   with None -> subSyntaxInSUKList _A _B _C s kl r subG
                   | Some _ -> true)
            else subSyntaxInSUKList _A _B _C s kl r subG))
    | s, kl, SUHOLE a, subG -> false
    | s, kl, SUIdKItem (a, b), subG -> false
and subSyntaxInSUKElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdFactor x, subG -> false
    | s, kl, ItemFactor x, subG -> subSyntaxInSUKItem _A _B _C s kl x subG
    | s, kl, SUKKItem (x, y, ty), subG ->
        subSyntaxInSUKLabel _A _B _C s kl x subG ||
          subSyntaxInSUKList _A _B _C s kl y subG
and subSyntaxInSUMapElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdM x, subG -> false
    | s, kl, ItemM (x, y), subG ->
        subSyntaxInSUK _A _B _C s kl x subG ||
          subSyntaxInSUK _A _B _C s kl y subG
    | s, kl, SUMapKItem (x, y), subG ->
        subSyntaxInSUKLabel _A _B _C s kl x subG ||
          subSyntaxInSUKList _A _B _C s kl y subG
and subSyntaxInSUMap _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUMapElem _A _B _C s kl b subG ||
          subSyntaxInSUMap _A _B _C s kl l subG
and subSyntaxInSUSetElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdS x, subG -> false
    | s, kl, ItemS x, subG -> subSyntaxInSUK _A _B _C s kl x subG
    | s, kl, SUSetKItem (x, y), subG ->
        subSyntaxInSUKLabel _A _B _C s kl x subG ||
          subSyntaxInSUKList _A _B _C s kl y subG
and subSyntaxInSUSet _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUSetElem _A _B _C s kl b subG ||
          subSyntaxInSUSet _A _B _C s kl l subG
and subSyntaxInSUListElem _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, IdL x, subG -> false
    | s, kl, ItemL x, subG -> subSyntaxInSUK _A _B _C s kl x subG
    | s, kl, SUListKItem (x, y), subG ->
        subSyntaxInSUKLabel _A _B _C s kl x subG ||
          subSyntaxInSUKList _A _B _C s kl y subG
and subSyntaxInSUList _A _B _C
  s kl x2 subG = match s, kl, x2, subG with s, kl, [], subG -> false
    | s, kl, b :: l, subG ->
        subSyntaxInSUListElem _A _B _C s kl b subG ||
          subSyntaxInSUList _A _B _C s kl l subG;;

let rec divideMacroRules _A _B _C
  x0 subG = match x0, subG with [], subG -> Some ([], [])
    | MacroPat (x, y, z) :: l, subG ->
        (if subSyntaxInSUK _A _B _C x (irToSUInKList _A y) z subG
          then (match divideMacroRules _A _B _C l subG with None -> None
                 | Some (la, s) -> Some (Some (x, (y, z)) :: la, s))
          else None)
    | FunPat (v, va, vb) :: l, subG ->
        (match divideMacroRules _A _B _C l subG with None -> None
          | Some (la, s) -> Some (la, FunPat (v, va, vb) :: s))
    | AnywherePat (v, va, vb, vc) :: l, subG ->
        (match divideMacroRules _A _B _C l subG with None -> None
          | Some (la, s) -> Some (la, AnywherePat (v, va, vb, vc) :: s))
    | KRulePat (v, va, vb, vc) :: l, subG ->
        (match divideMacroRules _A _B _C l subG with None -> None
          | Some (la, s) -> Some (la, KRulePat (v, va, vb, vc) :: s))
    | BagRulePat (v, va, vb, vc) :: l, subG ->
        (match divideMacroRules _A _B _C l subG with None -> None
          | Some (la, s) -> Some (la, BagRulePat (v, va, vb, vc) :: s));;

let rec getAllMetaVarsInKItem
  = function
    KItemC (l, r, ty) -> getAllMetaVarsInKLabelR l @ getAllMetaVarsInKListR r
    | Constant (a, b) -> []
    | IdKItem (a, b) -> [a]
    | HOLE a -> []
and getAllMetaVarsInKItemR
  = function KTerm t -> getAllMetaVarsInKItem t
    | KRewrite (l, r) -> getAllMetaVarsInKItem l @ getAllMetaVarsInKItem r
and getAllMetaVarsInK
  = function Tilda (a, t) -> getAllMetaVarsInKR a @ getAllMetaVarsInKR t
    | UnitK -> []
    | IdK a -> [a]
    | SingleK a -> getAllMetaVarsInKItemR a
    | KFun (l, r) -> getAllMetaVarsInKLabel l @ getAllMetaVarsInKListR r
and getAllMetaVarsInKR
  = function KTerm a -> getAllMetaVarsInK a
    | KRewrite (l, r) -> getAllMetaVarsInK l @ getAllMetaVarsInK r
and getAllMetaVarsInList
  = function ListCon (l, r) -> getAllMetaVarsInListR l @ getAllMetaVarsInListR r
    | UnitList -> []
    | IdList a -> [a]
    | ListItem a -> getAllMetaVarsInKR a
    | ListFun (l, r) -> getAllMetaVarsInKLabel l @ getAllMetaVarsInKListR r
and getAllMetaVarsInListR
  = function KTerm a -> getAllMetaVarsInList a
    | KRewrite (l, r) -> getAllMetaVarsInList l @ getAllMetaVarsInList r
and getAllMetaVarsInBigK = function TheK t -> getAllMetaVarsInKR t
                           | TheList t -> getAllMetaVarsInListR t
                           | TheSet t -> getAllMetaVarsInSetR t
                           | TheMap t -> getAllMetaVarsInMapR t
and getAllMetaVarsInBag
  = function BagCon (l, r) -> getAllMetaVarsInBagR l @ getAllMetaVarsInBagR r
    | UnitBag -> []
    | IdBag a -> [a]
    | Xml (a, n, t) -> getAllMetaVarsInBagR t
    | SingleCell (a, n, t) -> getAllMetaVarsInBigK t
and getAllMetaVarsInBagR
  = function KTerm a -> getAllMetaVarsInBag a
    | KRewrite (l, r) -> getAllMetaVarsInBag l @ getAllMetaVarsInBag r
and getAllMetaVarsInBigKWithBag = function TheBigK a -> getAllMetaVarsInBigK a
                                  | TheBigBag b -> getAllMetaVarsInBagR b
                                  | TheLabel b -> getAllMetaVarsInKLabelR b
and getAllMetaVarsInKList
  = function
    KListCon (b, t) -> getAllMetaVarsInKListR b @ getAllMetaVarsInKListR t
    | UnitKList -> []
    | IdKList a -> [a]
    | KListItem a -> getAllMetaVarsInBigKWithBag a
and getAllMetaVarsInKListR
  = function KTerm t -> getAllMetaVarsInKList t
    | KRewrite (l, r) -> getAllMetaVarsInKList l @ getAllMetaVarsInKList r
and getAllMetaVarsInKLabel
  = function KLabelC a -> []
    | KLabelFun (a, b) -> getAllMetaVarsInKLabel a @ getAllMetaVarsInKListR b
    | IdKLabel n -> [n]
and getAllMetaVarsInMap
  = function MapCon (l, r) -> getAllMetaVarsInMapR l @ getAllMetaVarsInMapR r
    | UnitMap -> []
    | IdMap a -> [a]
    | MapItem (l, r) -> getAllMetaVarsInKR l @ getAllMetaVarsInKR r
    | MapFun (l, r) -> getAllMetaVarsInKLabel l @ getAllMetaVarsInKListR r
and getAllMetaVarsInMapR
  = function KTerm a -> getAllMetaVarsInMap a
    | KRewrite (l, r) -> getAllMetaVarsInMap l @ getAllMetaVarsInMap r
and getAllMetaVarsInSet
  = function SetCon (l, r) -> getAllMetaVarsInSetR l @ getAllMetaVarsInSetR r
    | UnitSet -> []
    | IdSet a -> [a]
    | SetItem a -> getAllMetaVarsInKR a
    | SetFun (l, r) -> getAllMetaVarsInKLabel l @ getAllMetaVarsInKListR r
and getAllMetaVarsInSetR
  = function KTerm a -> getAllMetaVarsInSet a
    | KRewrite (l, r) -> getAllMetaVarsInSet l @ getAllMetaVarsInSet r
and getAllMetaVarsInKLabelR
  = function KTerm n -> getAllMetaVarsInKLabel n
    | KRewrite (l, r) -> getAllMetaVarsInKLabel l @ getAllMetaVarsInKLabel r;;

let rec removeDotInFeatureList
  = function [] -> []
    | b :: l ->
        (match b with Multiplicity _ -> b :: removeDotInFeatureList l
          | Stream _ -> b :: removeDotInFeatureList l
          | DotDotDot -> removeDotInFeatureList l);;

let rec hasRewriteInBigK = function TheK t -> hasRewriteInKR t
                           | TheList t -> hasRewriteInListR t
                           | TheSet t -> hasRewriteInSetR t
                           | TheMap t -> hasRewriteInMapR t
and hasRewriteInBag
  = function BagCon (l, r) -> hasRewriteInBagR l || hasRewriteInBagR r
    | UnitBag -> false
    | IdBag a -> false
    | Xml (a, n, t) -> hasRewriteInBagR t
    | SingleCell (a, n, t) -> hasRewriteInBigK t
and hasRewriteInBagR = function KTerm a -> hasRewriteInBag a
                       | KRewrite (l, r) -> true
and hasRewriteInBigKWithBag = function TheBigK a -> hasRewriteInBigK a
                              | TheBigBag b -> hasRewriteInBagR b
                              | TheLabel b -> hasRewriteInKLabelR b
and hasRewriteInKList
  = function KListCon (b, t) -> hasRewriteInKListR b || hasRewriteInKListR t
    | UnitKList -> false
    | KListItem a -> hasRewriteInBigKWithBag a
    | IdKList a -> false
and hasRewriteInKListR = function KTerm t -> hasRewriteInKList t
                         | KRewrite (l, r) -> true
and hasRewriteInKLabel
  = function KLabelC a -> false
    | KLabelFun (a, b) -> hasRewriteInKLabel a || hasRewriteInKListR b
    | IdKLabel n -> false
and hasRewriteInKLabelR = function KTerm n -> hasRewriteInKLabel n
                          | KRewrite (l, r) -> true
and hasRewriteInKItem
  = function KItemC (l, r, ty) -> hasRewriteInKLabelR l || hasRewriteInKListR r
    | Constant (a, b) -> false
    | IdKItem (a, b) -> false
    | HOLE a -> false
and hasRewriteInKItemR = function KTerm t -> hasRewriteInKItem t
                         | KRewrite (l, r) -> true
and hasRewriteInK
  = function Tilda (a, t) -> hasRewriteInKR a || hasRewriteInKR t
    | UnitK -> false
    | SingleK a -> hasRewriteInKItemR a
    | IdK a -> false
    | KFun (l, r) -> hasRewriteInKLabel l || hasRewriteInKListR r
and hasRewriteInKR = function KTerm a -> hasRewriteInK a
                     | KRewrite (l, r) -> true
and hasRewriteInMap
  = function MapCon (l, r) -> hasRewriteInMapR l || hasRewriteInMapR r
    | UnitMap -> false
    | IdMap a -> false
    | MapItem (l, r) -> hasRewriteInKR l || hasRewriteInKR r
    | MapFun (l, r) -> hasRewriteInKLabel l || hasRewriteInKListR r
and hasRewriteInMapR = function KTerm a -> hasRewriteInMap a
                       | KRewrite (l, r) -> true
and hasRewriteInSet
  = function SetCon (l, r) -> hasRewriteInSetR l || hasRewriteInSetR r
    | UnitSet -> false
    | IdSet a -> false
    | SetItem a -> hasRewriteInKR a
    | SetFun (l, r) -> hasRewriteInKLabel l || hasRewriteInKListR r
and hasRewriteInSetR = function KTerm a -> hasRewriteInSet a
                       | KRewrite (l, r) -> true
and hasRewriteInList
  = function ListCon (l, r) -> hasRewriteInListR l || hasRewriteInListR r
    | UnitList -> false
    | IdList a -> false
    | ListItem a -> hasRewriteInKR a
    | ListFun (l, r) -> hasRewriteInKLabel l || hasRewriteInKListR r
and hasRewriteInListR = function KTerm a -> hasRewriteInList a
                        | KRewrite (l, r) -> true;;

let rec ditachBagRWithVars
  = function KTerm a -> ditachBagWithVars a
    | KRewrite (a, b) ->
        (if not (hasRewriteInBag a) && not (hasRewriteInBag b)
          then Some ([(a, b)], ([], [])) else None)
and ditachBagWithVars
  = function UnitBag -> Some ([], ([], []))
    | IdBag x -> None
    | Xml (x, y, z) ->
        (if hasRewriteInBagR z then Some ([], ([Xml (x, y, z)], []))
          else Some ([], ([], [Xml (x, y, z)])))
    | SingleCell (x, y, z) ->
        (if hasRewriteInBigK z then Some ([], ([SingleCell (x, y, z)], []))
          else Some ([], ([], [SingleCell (x, y, z)])))
    | BagCon (l, r) ->
        (match (ditachBagRWithVars l, ditachBagRWithVars r)
          with (None, _) -> None | (Some (_, (_, _)), None) -> None
          | (Some (x, (y, z)), Some (u, (v, w))) ->
            Some (x @ u, (y @ v, z @ w)));;

let rec completeSameBagsInSUBag _B
  f p x2 = match f, p, x2 with f, p, [] -> Some []
    | f, p, b :: l ->
        (match b
          with ItemB (x, y, z) ->
            (match completeBagInSUBigKWithBag _B f p z with None -> None
              | Some za ->
                (match completeSameBagsInSUBag _B f p l with None -> None
                  | Some la ->
                    Some (ItemB (x, removeDotInFeatureList y, za) :: la)))
          | IdB _ -> None)
and completeBagNoDotInSUBag _B
  x0 a postp = match x0, a, postp with
    [], a, postp ->
      (if null postp then (if onlyIdInSUBag a then Some a else None)
        else (if onlyIdInSUBag a && hasIdInSUBag a then Some a else None))
    | b :: l, a, postp ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, asa) = searchBagWithName _B x a in
              (if null al then completeBagNoDotInSUBag _B l a (postp @ [b])
                else (if membera equal_feature y (Multiplicity Star)
                       then (match completeSameBagsInSUBag _B y z al
                              with None -> None
                              | Some ala ->
                                (match completeBagNoDotInSUBag _B l asa postp
                                  with None -> None
                                  | Some la -> Some (ala @ la)))
                       else (if less_nat one_nata (size_list al) then None
                              else (match completeSameBagsInSUBag _B y z al
                                     with None -> None
                                     | Some ala ->
                                       (match
 completeBagNoDotInSUBag _B l asa postp with None -> None
 | Some la -> Some (ala @ la)))))))
          | IdB _ -> None)
and completeBagHasDotInSUBag _B
  x0 a postp acc = match x0, a, postp, acc with
    [], a, postp, acc -> completeNextBagsInSUBag _B postp a acc
    | b :: l, a, postp, acc ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, asa) = searchBagWithName _B x a in
              (if null al
                then completeBagHasDotInSUBag _B l a
                       (postp @ [ItemB (x, removeDotInFeatureList y, z)]) acc
                else (if membera equal_feature y (Multiplicity Star)
                       then (match completeSameBagsInSUBag _B y z al
                              with None -> None
                              | Some ala ->
                                completeBagHasDotInSUBag _B l asa postp
                                  (acc @ ala))
                       else (if less_nat one_nata (size_list al) then None
                              else (match completeSameBagsInSUBag _B y z al
                                     with None -> None
                                     | Some ala ->
                                       completeBagHasDotInSUBag _B l asa postp
 (acc @ ala))))))
          | IdB _ -> None)
and completeNextBagsInSUBag _B
  x0 a acc = match x0, a, acc with [], a, acc -> Some (acc, a)
    | b :: l, a, acc ->
        (if null a then Some (acc @ b :: l, [])
          else (match b
                 with ItemB (x, y, z) ->
                   (match z
                     with SUK _ ->
                       completeNextBagsInSUBag _B l a
                         (acc @ [ItemB (x, removeDotInFeatureList y, z)])
                     | SUList _ ->
                       completeNextBagsInSUBag _B l a
                         (acc @ [ItemB (x, removeDotInFeatureList y, z)])
                     | SUSet _ ->
                       completeNextBagsInSUBag _B l a
                         (acc @ [ItemB (x, removeDotInFeatureList y, z)])
                     | SUMap _ ->
                       completeNextBagsInSUBag _B l a
                         (acc @ [ItemB (x, removeDotInFeatureList y, z)])
                     | SUBag al ->
                       (match completeBagHasDotInSUBag _B al a [] []
                         with None -> None
                         | Some aa ->
                           (let (acca, ab) = aa in
                             completeNextBagsInSUBag _B l ab
                               (acc @
                                 [ItemB (x, removeDotInFeatureList y,
  SUBag acca)]))))
                 | IdB _ -> None))
and completeBagInSUBigKWithBag _B
  f x1 s = match f, x1, s with
    f, SUBag a, s ->
      (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
        | SUMap _ -> None
        | SUBag b ->
          (if membera equal_feature f DotDotDot
            then (match completeBagHasDotInSUBag _B a b [] [] with None -> None
                   | Some aa ->
                     (let (ab, still) = aa in
                       (if null still then Some (SUBag ab) else None)))
            else (match completeBagNoDotInSUBag _B a b [] with None -> None
                   | Some aa -> Some (SUBag aa))))
    | f, SUK a, s ->
        (match s with SUK b -> Some (SUK b) | SUList _ -> None | SUSet _ -> None
          | SUMap _ -> None | SUBag _ -> None)
    | f, SUList a, s ->
        (match s with SUK _ -> None | SUList b -> Some (SUList b)
          | SUSet _ -> None | SUMap _ -> None | SUBag _ -> None)
    | f, SUSet a, s ->
        (match s with SUK _ -> None | SUList _ -> None
          | SUSet b -> Some (SUSet b) | SUMap _ -> None | SUBag _ -> None)
    | f, SUMap a, s ->
        (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
          | SUMap b -> Some (SUMap b) | SUBag _ -> None);;

let rec completeBagBySearchBags _B
  x0 p acc = match x0, p, acc with [], p, acc -> Some (acc, p)
    | b :: l, p, acc ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, ar) = searchBagWithName _B x p in
              (if null al
                then (match completeBagBySearchBigKWithBag _B z p acc
                       with None -> None
                       | Some (acca, remain) ->
                         completeBagBySearchBags _B l remain acca)
                else (match completeSameBagsInSUBag _B y z al with None -> None
                       | Some ala ->
                         (match
                           completeBagBySearchBigKWithBag _B z ar (acc @ ala)
                           with None -> None
                           | Some (acca, remain) ->
                             completeBagBySearchBags _B l remain acca))))
          | IdB _ -> None)
and completeBagBySearchBigKWithBag _B
  x0 p acc = match x0, p, acc with
    SUBag x, p, acc -> completeBagBySearchBags _B x p acc
    | SUK v, p, acc -> Some (acc, p)
    | SUList v, p, acc -> Some (acc, p)
    | SUSet v, p, acc -> Some (acc, p)
    | SUMap v, p, acc -> Some (acc, p);;

let rec searchBagWithNameInIRBag _A
  x xa1 = match x, xa1 with x, [] -> ([], [])
    | a, b :: l ->
        (let (x, (y, z)) = b in
         let (q, t) = searchBagWithNameInIRBag _A a l in
          (if equal_vara _A a x then ((x, (y, z)) :: q, t)
            else (q, (x, (y, z)) :: t)));;

let rec getListInIRBag (BagPat (x, y)) = x;;

let rec getVarInIRBag (BagPat (x, y)) = y;;

let rec getMaxNum
  x0 n = match x0, n with [], n -> n
    | a :: l, n ->
        (match a with Defined _ -> getMaxNum l n
          | Generated x ->
            (if less_nat x n then getMaxNum l n else getMaxNum l x));;

let rec freshVar a = Generated (getMaxNum a Zero_nat);;

let rec mergeListToIRBag l (BagPat (x, y)) = BagPat (l @ x, y);;

let rec fillVarsSameBagsInIRBag _B
  f p x2 vars = match f, p, x2, vars with f, p, [], vars -> Some ([], vars)
    | f, p, b :: l, vars ->
        (let (x, (y, z)) = b in
          (match fillVarsInIRBigKWithBag _B f p z vars with None -> None
            | Some (za, varsa) ->
              (match fillVarsSameBagsInIRBag _B f p l varsa with None -> None
                | Some (la, varsaa) ->
                  Some ((x, (removeDotInFeatureList y, za)) :: la, varsaa))))
and fillVarsBagNoDotInIRBag _B
  x0 a postp vars = match x0, a, postp, vars with
    [], a, postp, vars ->
      (match a
        with BagPat ([], None) ->
          (if null postp then Some (BagPat ([], None), vars) else None)
        | BagPat ([], Some x) -> Some (BagPat ([], Some x), vars)
        | BagPat (_ :: _, _) -> None)
    | b :: l, a, postp, vars ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, asa) = searchBagWithNameInIRBag _B x (getListInIRBag a) in
              (if null al then fillVarsBagNoDotInIRBag _B l a (postp @ [b]) vars
                else (if membera equal_feature y (Multiplicity Star)
                       then (match fillVarsSameBagsInIRBag _B y z al vars
                              with None -> None
                              | Some (ala, varsa) ->
                                (match
                                  fillVarsBagNoDotInIRBag _B l
                                    (BagPat (asa, getVarInIRBag a)) postp varsa
                                  with None -> None
                                  | Some (la, varsaa) ->
                                    Some (mergeListToIRBag ala la, varsaa)))
                       else (if less_nat one_nata (size_list al) then None
                              else (match fillVarsSameBagsInIRBag _B y z al vars
                                     with None -> None
                                     | Some (ala, varsa) ->
                                       (match
 fillVarsBagNoDotInIRBag _B l (BagPat (asa, getVarInIRBag a)) postp varsa
 with None -> None
 | Some (la, varsaa) -> Some (mergeListToIRBag ala la, varsaa)))))))
          | IdB _ -> None)
and fillVarsBagHasDotInIRBag _B
  x0 a postp acc vars = match x0, a, postp, acc, vars with
    [], a, postp, acc, vars ->
      (match a
        with BagPat ([], None) ->
          Some (BagPat (acc, Some (freshVar vars)), ([], freshVar vars :: vars))
        | BagPat ([], Some _) -> None
        | BagPat (b :: l, None) ->
          (match fillVarsNextBagsInIRBag _B postp (b :: l) vars
            with None -> None
            | Some (acca, (remains, varsa)) ->
              Some (BagPat (acc @ acca, Some (freshVar varsa)),
                     (remains, freshVar varsa :: varsa)))
        | BagPat (_ :: _, Some _) -> None)
    | b :: l, a, postp, acc, vars ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, asa) = searchBagWithNameInIRBag _B x (getListInIRBag a) in
              (if null al
                then fillVarsBagHasDotInIRBag _B l a (postp @ [ItemB (x, y, z)])
                       acc vars
                else (if membera equal_feature y (Multiplicity Star)
                       then (match fillVarsSameBagsInIRBag _B y z al vars
                              with None -> None
                              | Some ba ->
                                (let (ala, bb) = ba in
                                  fillVarsBagHasDotInIRBag _B l
                                    (BagPat (asa, getVarInIRBag a)) postp
                                    (acc @ ala) bb))
                       else (if less_nat one_nata (size_list al) then None
                              else (match fillVarsSameBagsInIRBag _B y z al vars
                                     with None -> None
                                     | Some ba ->
                                       (let (ala, bb) = ba in
 fillVarsBagHasDotInIRBag _B l (BagPat (asa, getVarInIRBag a)) postp (acc @ ala)
   bb))))))
          | IdB _ -> None)
and fillVarsInIRBigKWithBag _B
  f x1 s vars = match f, x1, s, vars with
    f, SUBag a, s, vars ->
      (match s with IRK _ -> None | IRList _ -> None | IRSet _ -> None
        | IRMap _ -> None
        | IRBag b ->
          (if membera equal_feature f DotDotDot
            then (match fillVarsBagHasDotInIRBag _B a b [] [] vars
                   with None -> None
                   | Some aa ->
                     (let (ab, (still, varsa)) = aa in
                       (if null still then Some (IRBag ab, varsa) else None)))
            else (match fillVarsBagNoDotInIRBag _B a b [] vars with None -> None
                   | Some aa ->
                     (let (ab, varsa) = aa in Some (IRBag ab, varsa)))))
    | f, SUK a, s, vars ->
        (match s with IRK b -> Some (IRK b, vars) | IRList _ -> None
          | IRSet _ -> None | IRMap _ -> None | IRBag _ -> None)
    | f, SUList a, s, vars ->
        (match s with IRK _ -> None | IRList b -> Some (IRList b, vars)
          | IRSet _ -> None | IRMap _ -> None | IRBag _ -> None)
    | f, SUSet a, s, vars ->
        (match s with IRK _ -> None | IRList _ -> None
          | IRSet b -> Some (IRSet b, vars) | IRMap _ -> None | IRBag _ -> None)
    | f, SUMap a, s, vars ->
        (match s with IRK _ -> None | IRList _ -> None | IRSet _ -> None
          | IRMap b -> Some (IRMap b, vars) | IRBag _ -> None)
and fillVarsNextBagsInIRBag _B
  x0 a vars = match x0, a, vars with [], a, vars -> Some ([], (a, vars))
    | b :: l, a, vars ->
        (if null a then Some ([], ([], vars))
          else (match b
                 with ItemB (_, _, SUK _) -> fillVarsNextBagsInIRBag _B l a vars
                 | ItemB (_, _, SUList _) -> fillVarsNextBagsInIRBag _B l a vars
                 | ItemB (_, _, SUSet _) -> fillVarsNextBagsInIRBag _B l a vars
                 | ItemB (_, _, SUMap _) -> fillVarsNextBagsInIRBag _B l a vars
                 | ItemB (x, y, SUBag al) ->
                   (match
                     fillVarsBagHasDotInIRBag _B al (BagPat (a, None)) [] []
                       vars
                     with None -> None
                     | Some aa ->
                       (let (acc, ab) = aa in
                        let (ac, varsa) = ab in
                         (match fillVarsNextBagsInIRBag _B l ac varsa
                           with None -> None
                           | Some (acca, (aaa, varsaa)) ->
                             Some ((x, (removeDotInFeatureList y, IRBag acc)) ::
                                     acca,
                                    (aaa, varsaa)))))
                 | IdB _ -> None));;

let rec fillVarsBySearchBags _B
  x0 p acc vars = match x0, p, acc, vars with
    [], p, acc, vars -> Some (acc, (p, vars))
    | b :: l, p, acc, vars ->
        (match b
          with ItemB (x, y, z) ->
            (let (al, ar) = searchBagWithNameInIRBag _B x p in
              (if null al
                then (match fillVarsBySearchBigKWithBag _B z p acc vars
                       with None -> None
                       | Some a ->
                         (let (acca, aa) = a in
                          let (remain, ab) = aa in
                           fillVarsBySearchBags _B l remain acca ab))
                else (match fillVarsSameBagsInIRBag _B y z al vars
                       with None -> None
                       | Some (ala, varsa) ->
                         (match
                           fillVarsBySearchBigKWithBag _B z ar (acc @ ala) varsa
                           with None -> None
                           | Some a ->
                             (let (acca, aa) = a in
                              let (remain, ab) = aa in
                               fillVarsBySearchBags _B l remain acca ab)))))
          | IdB _ -> None)
and fillVarsBySearchBigKWithBag _B
  x0 p acc vars = match x0, p, acc, vars with
    SUBag x, p, acc, vars -> fillVarsBySearchBags _B x p acc vars
    | SUK v, p, acc, vars -> Some (acc, (p, vars))
    | SUList v, p, acc, vars -> Some (acc, (p, vars))
    | SUSet v, p, acc, vars -> Some (acc, (p, vars))
    | SUMap v, p, acc, vars -> Some (acc, (p, vars));;

let rec normalizeBagNoDot _B
  x0 t database = match x0, t, database with
    [], t, database ->
      (let (BagPat (u, v), y) = t in
        (if null u && onlyIdInSUBag y then Some (BagPat ([], v), y) else None))
    | b :: l, t, database ->
        (match b
          with ItemB (x, _, _) ->
            (let (BagPat (u, v), y) = t in
             let ((ul, ur), (yl, yr)) =
               (searchBagWithNameInIRBag _B x u, searchBagWithName _B x y) in
              (match normalizeBagNoDot _B l (BagPat (ur, v), yr) database
                with None -> None
                | Some (BagPat (ua, va), ya) ->
                  Some (BagPat (ul @ ua, va), yl @ ya)))
          | IdB _ -> None);;

let rec irToSUInIRBagList _B
  = function [] -> []
    | (x, (y, z)) :: l ->
        ItemB (x, y, irToSUInBigKWithBag _B z) :: irToSUInIRBagList _B l;;

let rec getRightInBigK
  = function
    TheK t ->
      (match getRightInKR t with None -> None | Some ta -> Some (TheK ta))
    | TheList t ->
        (match getRightInListR t with None -> None
          | Some ta -> Some (TheList ta))
    | TheSet t ->
        (match getRightInSetR t with None -> None | Some ta -> Some (TheSet ta))
    | TheMap t ->
        (match getRightInMapR t with None -> None | Some ta -> Some (TheMap ta))
and getRightInBag
  = function
    BagCon (l, r) ->
      (match getRightInBagR l with None -> None
        | Some la ->
          (match getRightInBagR r with None -> None
            | Some ra -> Some (BagCon (la, ra))))
    | UnitBag -> Some UnitBag
    | IdBag a -> Some (IdBag a)
    | Xml (a, n, t) ->
        (match getRightInBagR t with None -> None
          | Some ta -> Some (Xml (a, n, ta)))
    | SingleCell (a, n, t) ->
        (match getRightInBigK t with None -> None
          | Some ta -> Some (SingleCell (a, n, ta)))
and getRightInBagR
  = function
    KTerm a ->
      (match getRightInBag a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInBag l || hasRewriteInBag r then None
          else Some (KTerm r))
and getRightInBigKWithBag
  = function
    TheBigK a ->
      (match getRightInBigK a with None -> None | Some aa -> Some (TheBigK aa))
    | TheBigBag b ->
        (match getRightInBagR b with None -> None
          | Some ba -> Some (TheBigBag ba))
    | TheLabel b ->
        (match getRightInKLabelR b with None -> None
          | Some ba -> Some (TheLabel ba))
and getRightInKList
  = function
    KListCon (b, t) ->
      (match getRightInKListR b with None -> None
        | Some ba ->
          (match getRightInKListR t with None -> None
            | Some ta -> Some (KListCon (ba, ta))))
    | UnitKList -> Some UnitKList
    | KListItem a ->
        (match getRightInBigKWithBag a with None -> None
          | Some aa -> Some (KListItem aa))
    | IdKList a -> Some (IdKList a)
and getRightInKListR
  = function
    KTerm t ->
      (match getRightInKList t with None -> None | Some ta -> Some (KTerm ta))
    | KRewrite (l, r) ->
        (if hasRewriteInKList l || hasRewriteInKList r then None
          else Some (KTerm r))
and getRightInKLabel
  = function KLabelC a -> Some (KLabelC a)
    | KLabelFun (a, b) ->
        (match getRightInKLabel a with None -> None
          | Some aa ->
            (match getRightInKListR b with None -> None
              | Some ba -> Some (KLabelFun (aa, ba))))
    | IdKLabel n -> Some (IdKLabel n)
and getRightInKLabelR
  = function
    KTerm n ->
      (match getRightInKLabel n with None -> None | Some na -> Some (KTerm na))
    | KRewrite (l, r) ->
        (if hasRewriteInKLabel l || hasRewriteInKLabel r then None
          else Some (KTerm r))
and getRightInKItem
  = function
    KItemC (l, r, ty) ->
      (match getRightInKLabelR l with None -> None
        | Some la ->
          (match getRightInKListR r with None -> None
            | Some ra -> Some (KItemC (la, ra, ty))))
    | Constant (a, b) -> Some (Constant (a, b))
    | IdKItem (a, b) -> Some (IdKItem (a, b))
    | HOLE a -> Some (HOLE a)
and getRightInKItemR
  = function
    KTerm t ->
      (match getRightInKItem t with None -> None | Some ta -> Some (KTerm ta))
    | KRewrite (l, r) ->
        (if hasRewriteInKItem l || hasRewriteInKItem r then None
          else Some (KTerm r))
and getRightInK
  = function
    Tilda (a, t) ->
      (match getRightInKR a with None -> None
        | Some aa ->
          (match getRightInKR t with None -> None
            | Some ta -> Some (Tilda (aa, ta))))
    | UnitK -> Some UnitK
    | SingleK a ->
        (match getRightInKItemR a with None -> None
          | Some aa -> Some (SingleK aa))
    | IdK a -> Some (IdK a)
    | KFun (l, r) ->
        (match getRightInKLabel l with None -> None
          | Some la ->
            (match getRightInKListR r with None -> None
              | Some ra -> Some (KFun (la, ra))))
and getRightInKR
  = function
    KTerm a ->
      (match getRightInK a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInK l || hasRewriteInK r then None else Some (KTerm r))
and getRightInMap
  = function
    MapCon (l, r) ->
      (match getRightInMapR l with None -> None
        | Some la ->
          (match getRightInMapR r with None -> None
            | Some ra -> Some (MapCon (la, ra))))
    | UnitMap -> Some UnitMap
    | IdMap a -> Some (IdMap a)
    | MapFun (l, r) ->
        (match getRightInKLabel l with None -> None
          | Some la ->
            (match getRightInKListR r with None -> None
              | Some ra -> Some (MapFun (la, ra))))
    | MapItem (l, r) ->
        (match getRightInKR l with None -> None
          | Some la ->
            (match getRightInKR r with None -> None
              | Some ra -> Some (MapItem (la, ra))))
and getRightInMapR
  = function
    KTerm a ->
      (match getRightInMap a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInMap l || hasRewriteInMap r then None
          else Some (KTerm r))
and getRightInSet
  = function
    SetCon (l, r) ->
      (match getRightInSetR l with None -> None
        | Some la ->
          (match getRightInSetR r with None -> None
            | Some ra -> Some (SetCon (la, ra))))
    | UnitSet -> Some UnitSet
    | IdSet a -> Some (IdSet a)
    | SetFun (l, r) ->
        (match getRightInKLabel l with None -> None
          | Some la ->
            (match getRightInKListR r with None -> None
              | Some ra -> Some (SetFun (la, ra))))
    | SetItem a ->
        (match getRightInKR a with None -> None | Some aa -> Some (SetItem aa))
and getRightInSetR
  = function
    KTerm a ->
      (match getRightInSet a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInSet l || hasRewriteInSet r then None
          else Some (KTerm r))
and getRightInList
  = function
    ListCon (l, r) ->
      (match getRightInListR l with None -> None
        | Some la ->
          (match getRightInListR r with None -> None
            | Some ra -> Some (ListCon (la, ra))))
    | UnitList -> Some UnitList
    | IdList a -> Some (IdList a)
    | ListItem a ->
        (match getRightInKR a with None -> None | Some aa -> Some (ListItem aa))
    | ListFun (l, r) ->
        (match getRightInKLabel l with None -> None
          | Some la ->
            (match getRightInKListR r with None -> None
              | Some ra -> Some (ListFun (la, ra))))
and getRightInListR
  = function
    KTerm a ->
      (match getRightInList a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInList l || hasRewriteInList r then None
          else Some (KTerm r));;

let rec getLeftInBigK
  = function
    TheK t ->
      (match getLeftInKR t with None -> None | Some ta -> Some (TheK ta))
    | TheList t ->
        (match getLeftInListR t with None -> None
          | Some ta -> Some (TheList ta))
    | TheSet t ->
        (match getLeftInSetR t with None -> None | Some ta -> Some (TheSet ta))
    | TheMap t ->
        (match getLeftInMapR t with None -> None | Some ta -> Some (TheMap ta))
and getLeftInBag
  = function
    BagCon (l, r) ->
      (match getLeftInBagR l with None -> None
        | Some la ->
          (match getLeftInBagR r with None -> None
            | Some ra -> Some (BagCon (la, ra))))
    | UnitBag -> Some UnitBag
    | IdBag a -> Some (IdBag a)
    | Xml (a, n, t) ->
        (match getLeftInBagR t with None -> None
          | Some ta -> Some (Xml (a, n, ta)))
    | SingleCell (a, n, t) ->
        (match getLeftInBigK t with None -> None
          | Some ta -> Some (SingleCell (a, n, ta)))
and getLeftInBagR
  = function
    KTerm a ->
      (match getLeftInBag a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInBag l || hasRewriteInBag r then None
          else Some (KTerm l))
and getLeftInBigKWithBag
  = function
    TheBigK a ->
      (match getLeftInBigK a with None -> None | Some aa -> Some (TheBigK aa))
    | TheBigBag b ->
        (match getLeftInBagR b with None -> None
          | Some ba -> Some (TheBigBag ba))
    | TheLabel b ->
        (match getLeftInKLabelR b with None -> None
          | Some ba -> Some (TheLabel ba))
and getLeftInKList
  = function
    KListCon (b, t) ->
      (match getLeftInKListR b with None -> None
        | Some ba ->
          (match getLeftInKListR t with None -> None
            | Some ta -> Some (KListCon (ba, ta))))
    | UnitKList -> Some UnitKList
    | KListItem a ->
        (match getLeftInBigKWithBag a with None -> None
          | Some aa -> Some (KListItem aa))
    | IdKList a -> Some (IdKList a)
and getLeftInKListR
  = function
    KTerm t ->
      (match getLeftInKList t with None -> None | Some ta -> Some (KTerm ta))
    | KRewrite (l, r) ->
        (if hasRewriteInKList l || hasRewriteInKList r then None
          else Some (KTerm l))
and getLeftInKLabel
  = function KLabelC a -> Some (KLabelC a)
    | KLabelFun (a, b) ->
        (match getLeftInKLabel a with None -> None
          | Some aa ->
            (match getLeftInKListR b with None -> None
              | Some ba -> Some (KLabelFun (aa, ba))))
    | IdKLabel n -> Some (IdKLabel n)
and getLeftInKLabelR
  = function
    KTerm n ->
      (match getLeftInKLabel n with None -> None | Some na -> Some (KTerm na))
    | KRewrite (l, r) ->
        (if hasRewriteInKLabel l || hasRewriteInKLabel r then None
          else Some (KTerm l))
and getLeftInKItem
  = function
    KItemC (l, r, ty) ->
      (match getLeftInKLabelR l with None -> None
        | Some la ->
          (match getLeftInKListR r with None -> None
            | Some ra -> Some (KItemC (la, ra, ty))))
    | Constant (a, b) -> Some (Constant (a, b))
    | IdKItem (a, b) -> Some (IdKItem (a, b))
    | HOLE a -> Some (HOLE a)
and getLeftInKItemR
  = function
    KTerm t ->
      (match getLeftInKItem t with None -> None | Some ta -> Some (KTerm ta))
    | KRewrite (l, r) ->
        (if hasRewriteInKItem l || hasRewriteInKItem r then None
          else Some (KTerm l))
and getLeftInK
  = function
    Tilda (a, t) ->
      (match getLeftInKR a with None -> None
        | Some aa ->
          (match getLeftInKR t with None -> None
            | Some ta -> Some (Tilda (aa, ta))))
    | UnitK -> Some UnitK
    | SingleK a ->
        (match getLeftInKItemR a with None -> None
          | Some aa -> Some (SingleK aa))
    | IdK a -> Some (IdK a)
    | KFun (l, r) ->
        (match getLeftInKLabel l with None -> None
          | Some la ->
            (match getLeftInKListR r with None -> None
              | Some ra -> Some (KFun (la, ra))))
and getLeftInKR
  = function
    KTerm a ->
      (match getLeftInK a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInK l || hasRewriteInK r then None else Some (KTerm l))
and getLeftInMap
  = function
    MapCon (l, r) ->
      (match getLeftInMapR l with None -> None
        | Some la ->
          (match getLeftInMapR r with None -> None
            | Some ra -> Some (MapCon (la, ra))))
    | UnitMap -> Some UnitMap
    | IdMap a -> Some (IdMap a)
    | MapItem (l, r) ->
        (match getLeftInKR l with None -> None
          | Some la ->
            (match getLeftInKR r with None -> None
              | Some ra -> Some (MapItem (la, ra))))
    | MapFun (l, r) ->
        (match getLeftInKLabel l with None -> None
          | Some la ->
            (match getLeftInKListR r with None -> None
              | Some ra -> Some (MapFun (la, ra))))
and getLeftInMapR
  = function
    KTerm a ->
      (match getLeftInMap a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInMap l || hasRewriteInMap r then None
          else Some (KTerm l))
and getLeftInSet
  = function
    SetCon (l, r) ->
      (match getLeftInSetR l with None -> None
        | Some la ->
          (match getLeftInSetR r with None -> None
            | Some ra -> Some (SetCon (la, ra))))
    | UnitSet -> Some UnitSet
    | IdSet a -> Some (IdSet a)
    | SetItem a ->
        (match getLeftInKR a with None -> None | Some aa -> Some (SetItem aa))
    | SetFun (l, r) ->
        (match getLeftInKLabel l with None -> None
          | Some la ->
            (match getLeftInKListR r with None -> None
              | Some ra -> Some (SetFun (la, ra))))
and getLeftInSetR
  = function
    KTerm a ->
      (match getLeftInSet a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInSet l || hasRewriteInSet r then None
          else Some (KTerm l))
and getLeftInList
  = function
    ListCon (l, r) ->
      (match getLeftInListR l with None -> None
        | Some la ->
          (match getLeftInListR r with None -> None
            | Some ra -> Some (ListCon (la, ra))))
    | UnitList -> Some UnitList
    | IdList a -> Some (IdList a)
    | ListItem a ->
        (match getLeftInKR a with None -> None | Some aa -> Some (ListItem aa))
    | ListFun (l, r) ->
        (match getLeftInKLabel l with None -> None
          | Some la ->
            (match getLeftInKListR r with None -> None
              | Some ra -> Some (ListFun (la, ra))))
and getLeftInListR
  = function
    KTerm a ->
      (match getLeftInList a with None -> None | Some aa -> Some (KTerm aa))
    | KRewrite (l, r) ->
        (if hasRewriteInList l || hasRewriteInList r then None
          else Some (KTerm l));;

let rec mergeBagTuple
  a b t =
    (let (BagPat (l, v), y) = t in
     let BagPat (la, va) = a in
      (match (v, va) with (None, None) -> Some (BagPat (l @ la, None), y @ b)
        | (None, Some u) -> Some (BagPat (l @ la, Some u), y @ b)
        | (Some u, None) -> Some (BagPat (l @ la, Some u), y @ b)
        | (Some _, Some _) -> None));;

let rec getSubPattern _A
  x xa1 = match x, xa1 with x, [] -> None
    | x, b :: l ->
        (match b
          with ItemB (u, v, w) ->
            (if equal_vara _A u x then Some (v, w)
              else (match getSubPatternAux _A x w
                     with None -> getSubPattern _A x l | Some a -> Some a))
          | IdB _ -> None)
and getSubPatternAux _A
  x xa1 = match x, xa1 with x, SUBag y -> getSubPattern _A x y
    | x, SUK v -> None
    | x, SUList v -> None
    | x, SUSet v -> None
    | x, SUMap v -> None;;

let rec getKLabelMeaning
  x = (match x with KLabelC a -> Some a | KLabelFun (_, _) -> None
        | IdKLabel _ -> None);;

let rec getKLabelInKLabelR
  x = (match x
        with KTerm a ->
          (match a with KLabelC aa -> Some aa | KLabelFun (_, _) -> None
            | IdKLabel _ -> None)
        | KRewrite (_, _) -> None);;

let rec toIRInBigK _A
  x0 database = match x0, database with
    TheK t, database ->
      (match toIRInKR _A t database with None -> None
        | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
        | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
        | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
        | Some (NormalPat (KLabelMatching _)) -> None
        | Some (NormalPat (KItemMatching _)) -> None
        | Some (NormalPat (KListMatching _)) -> None
        | Some (NormalPat (KMatching ta)) -> Some (IRK ta)
        | Some (NormalPat (ListMatching _)) -> None
        | Some (NormalPat (SetMatching _)) -> None
        | Some (NormalPat (MapMatching _)) -> None
        | Some (NormalPat (BagMatching _)) -> None)
    | TheList t, database ->
        (match toIRInListR _A t database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching ta)) -> Some (IRList ta)
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
    | TheSet t, database ->
        (match toIRInSetR _A t database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching ta)) -> Some (IRSet ta)
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
    | TheMap t, database ->
        (match toIRInMapR _A t database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching _)) -> None
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching ta)) -> Some (IRMap ta)
          | Some (NormalPat (BagMatching _)) -> None)
and toIRInBag _A
  x0 database = match x0, database with
    BagCon (a, b), database ->
      (match (toIRInBagR _A a database, toIRInBagR _A b database)
        with (None, _) -> None | (Some (BagPat (_, None)), None) -> None
        | (Some (BagPat (_, None)), Some (BagPat (_, None))) -> None
        | (Some (BagPat (la, None)), Some (BagPat (lb, Some vb))) ->
          Some (BagPat (la @ lb, Some vb))
        | (Some (BagPat (_, Some _)), None) -> None
        | (Some (BagPat (la, Some va)), Some (BagPat (lb, None))) ->
          Some (BagPat (la @ lb, Some va))
        | (Some (BagPat (_, Some _)), Some (BagPat (_, Some _))) -> None)
    | UnitBag, database -> Some (BagPat ([], None))
    | IdBag a, database -> Some (BagPat ([], Some a))
    | Xml (a, n, t), database ->
        (match toIRInBagR _A t database with None -> None
          | Some ta -> Some (BagPat ([(a, (n, IRBag ta))], None)))
    | SingleCell (a, n, t), database ->
        (match toIRInBigK _A t database with None -> None
          | Some ta -> Some (BagPat ([(a, (n, ta))], None)))
and toIRInBagR _A
  x0 database = match x0, database with
    KTerm a, database -> toIRInBag _A a database
    | KRewrite (l, r), database -> None
and toIRInBigKWithBag _A
  x0 database = match x0, database with
    TheBigK a, database ->
      (match toIRInBigK _A a database with None -> None
        | Some aa -> Some (IRBigBag aa))
    | TheBigBag b, database ->
        (match toIRInBagR _A b database with None -> None
          | Some ba -> Some (IRBigBag (IRBag ba)))
    | TheLabel b, database ->
        (match toIRInKLabelR _A b database with None -> None
          | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
          | Some (KItemFunPat (_, _)) -> None | Some (ListFunPat (_, _)) -> None
          | Some (SetFunPat (_, _)) -> None | Some (MapFunPat (_, _)) -> None
          | Some (NormalPat (KLabelMatching ba)) -> Some (IRBigLabel ba)
          | Some (NormalPat (KItemMatching _)) -> None
          | Some (NormalPat (KListMatching _)) -> None
          | Some (NormalPat (KMatching _)) -> None
          | Some (NormalPat (ListMatching _)) -> None
          | Some (NormalPat (SetMatching _)) -> None
          | Some (NormalPat (MapMatching _)) -> None
          | Some (NormalPat (BagMatching _)) -> None)
and toIRInKList _A
  x0 database = match x0, database with
    KListCon (b, t), database ->
      (match (toIRInKListR _A b database, toIRInKListR _A t database)
        with (None, _) -> None | (Some (KListPatNoVar _), None) -> None
        | (Some (KListPatNoVar la), Some (KListPatNoVar lb)) ->
          Some (KListPatNoVar (la @ lb))
        | (Some (KListPatNoVar la), Some (KListPat (lb, y, rb))) ->
          Some (KListPat (la @ lb, y, rb))
        | (Some (KListPat (_, _, _)), None) -> None
        | (Some (KListPat (la, x, ra)), Some (KListPatNoVar lb)) ->
          Some (KListPat (la, x, ra @ lb))
        | (Some (KListPat (_, _, _)), Some (KListPat (_, _, _))) -> None)
    | UnitKList, database -> Some (KListPatNoVar [])
    | KListItem a, database ->
        (match toIRInBigKWithBag _A a database with None -> None
          | Some aa -> Some (KListPatNoVar [aa]))
    | IdKList a, database -> Some (KListPat ([], a, []))
and toIRInKListR _A
  x0 database = match x0, database with
    KTerm t, database -> toIRInKList _A t database
    | KRewrite (l, r), database -> None
and toIRInKLabel _A
  x0 database = match x0, database with
    KLabelC a, database -> Some (NormalPat (KLabelMatching (IRKLabel a)))
    | KLabelFun (a, b), database ->
        (match getKLabelMeaning a with None -> None
          | Some s ->
            (match toIRInKListR _A b database with None -> None
              | Some ba -> Some (KLabelFunPat (s, ba))))
    | IdKLabel n, database -> Some (NormalPat (KLabelMatching (IRIdKLabel n)))
and toIRInKLabelR _A
  x0 database = match x0, database with
    KTerm n, database -> toIRInKLabel _A n database
    | KRewrite (l, r), database -> None
and toIRInKItem _A
  x0 database = match x0, database with
    KItemC (l, r, ty), database ->
      (match getKLabelInKLabelR l
        with None ->
          (match toIRInKLabelR _A l database with None -> None
            | Some (KLabelFunPat (_, _)) -> None | Some (KFunPat (_, _)) -> None
            | Some (KItemFunPat (_, _)) -> None
            | Some (ListFunPat (_, _)) -> None | Some (SetFunPat (_, _)) -> None
            | Some (MapFunPat (_, _)) -> None
            | Some (NormalPat (KLabelMatching la)) ->
              (match toIRInKListR _A r database with None -> None
                | Some ra ->
                  Some (NormalPat (KItemMatching (IRKItem (la, ra, [ty])))))
            | Some (NormalPat (KItemMatching _)) -> None
            | Some (NormalPat (KListMatching _)) -> None
            | Some (NormalPat (KMatching _)) -> None
            | Some (NormalPat (ListMatching _)) -> None
            | Some (NormalPat (SetMatching _)) -> None
            | Some (NormalPat (MapMatching _)) -> None
            | Some (NormalPat (BagMatching _)) -> None)
        | Some s ->
          (if isFunctionItem (equal_label _A) s database
            then (match toIRInKListR _A r database with None -> None
                   | Some ra -> Some (KItemFunPat (s, ra)))
            else (match toIRInKLabelR _A l database with None -> None
                   | Some (KLabelFunPat (_, _)) -> None
                   | Some (KFunPat (_, _)) -> None
                   | Some (KItemFunPat (_, _)) -> None
                   | Some (ListFunPat (_, _)) -> None
                   | Some (SetFunPat (_, _)) -> None
                   | Some (MapFunPat (_, _)) -> None
                   | Some (NormalPat (KLabelMatching la)) ->
                     (match toIRInKListR _A r database with None -> None
                       | Some ra ->
                         Some (NormalPat
                                (KItemMatching (IRKItem (la, ra, [ty])))))
                   | Some (NormalPat (KItemMatching _)) -> None
                   | Some (NormalPat (KListMatching _)) -> None
                   | Some (NormalPat (KMatching _)) -> None
                   | Some (NormalPat (ListMatching _)) -> None
                   | Some (NormalPat (SetMatching _)) -> None
                   | Some (NormalPat (MapMatching _)) -> None
                   | Some (NormalPat (BagMatching _)) -> None)))
    | Constant (a, b), database ->
        Some (NormalPat
               (KItemMatching
                 (IRKItem (IRKLabel (ConstToLabel a), KListPatNoVar [], [b]))))
    | IdKItem (a, b), database ->
        Some (NormalPat (KItemMatching (IRIdKItem (a, [b]))))
    | HOLE a, database -> Some (NormalPat (KItemMatching (IRHOLE [a])))
and toIRInKItemR _A
  x0 database = match x0, database with
    KTerm t, database -> toIRInKItem _A t database
    | KRewrite (l, r), database -> None
and toIRInK _A
  x0 database = match x0, database with
    Tilda (a, b), database ->
      (match (toIRInKR _A a database, toIRInKR _A b database)
        with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
        | (Some (KFunPat (_, _)), _) -> None
        | (Some (KItemFunPat (_, _)), _) -> None
        | (Some (ListFunPat (_, _)), _) -> None
        | (Some (SetFunPat (_, _)), _) -> None
        | (Some (MapFunPat (_, _)), _) -> None
        | (Some (NormalPat (KLabelMatching _)), _) -> None
        | (Some (NormalPat (KItemMatching _)), _) -> None
        | (Some (NormalPat (KListMatching _)), _) -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))), None) -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))), Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (la, None)))),
            Some (NormalPat (KMatching (KPat (lb, None)))))
          -> Some (NormalPat (KMatching (KPat (la @ lb, None))))
        | (Some (NormalPat (KMatching (KPat (la, None)))),
            Some (NormalPat (KMatching (KPat (lb, Some vb)))))
          -> Some (NormalPat (KMatching (KPat (la @ lb, Some vb))))
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, None)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))), None) -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (la, Some va)))),
            Some (NormalPat (KMatching (KPat (lb, None)))))
          -> (if not (null lb)
               then Some (NormalPat
                           (KMatching
                             (KPat (la @ [IRIdKItem (va, [K])] @ lb, None))))
               else Some (NormalPat (KMatching (KPat (la @ lb, Some va)))))
        | (Some (NormalPat (KMatching (KPat (la, Some va)))),
            Some (NormalPat (KMatching (KPat (lb, Some vb)))))
          -> Some (NormalPat
                    (KMatching
                      (KPat (la @ [IRIdKItem (va, [K])] @ lb, Some vb))))
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (KMatching (KPat (_, Some _)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (ListMatching _)), _) -> None
        | (Some (NormalPat (SetMatching _)), _) -> None
        | (Some (NormalPat (MapMatching _)), _) -> None
        | (Some (NormalPat (BagMatching _)), _) -> None)
    | UnitK, database -> Some (NormalPat (KMatching (KPat ([], None))))
    | SingleK a, database ->
        (match toIRInKItemR _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching ac ->
                    Some (NormalPat (KMatching (KPat ([ac], None))))
                  | KListMatching _ -> None | KMatching _ -> None
                  | ListMatching _ -> None | SetMatching _ -> None
                  | MapMatching _ -> None | BagMatching _ -> None)))
    | IdK a, database -> Some (NormalPat (KMatching (KPat ([], Some a))))
    | KFun (l, r), database ->
        (match getKLabelMeaning l with None -> None
          | Some s ->
            (match toIRInKListR _A r database with None -> None
              | Some ra -> Some (KFunPat (s, ra))))
and toIRInKR _A
  x0 database = match x0, database with
    KTerm a, database -> toIRInK _A a database
    | KRewrite (l, r), database -> None
and toIRInMap _A
  x0 database = match x0, database with
    MapCon (a, b), database ->
      (match (toIRInMapR _A a database, toIRInMapR _A b database)
        with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
        | (Some (KFunPat (_, _)), _) -> None
        | (Some (KItemFunPat (_, _)), _) -> None
        | (Some (ListFunPat (_, _)), _) -> None
        | (Some (SetFunPat (_, _)), _) -> None
        | (Some (MapFunPat (_, _)), _) -> None
        | (Some (NormalPat (KLabelMatching _)), _) -> None
        | (Some (NormalPat (KItemMatching _)), _) -> None
        | (Some (NormalPat (KListMatching _)), _) -> None
        | (Some (NormalPat (KMatching _)), _) -> None
        | (Some (NormalPat (ListMatching _)), _) -> None
        | (Some (NormalPat (SetMatching _)), _) -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))), None) -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (MapMatching (MapPat (_, None)))))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (la, None)))),
            Some (NormalPat (MapMatching (MapPat (lb, Some vb)))))
          -> Some (NormalPat (MapMatching (MapPat (la @ lb, Some vb))))
        | (Some (NormalPat (MapMatching (MapPat (_, None)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))), None) -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (la, Some va)))),
            Some (NormalPat (MapMatching (MapPat (lb, None)))))
          -> Some (NormalPat (MapMatching (MapPat (la @ lb, Some va))))
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (MapMatching (MapPat (_, Some _)))))
          -> None
        | (Some (NormalPat (MapMatching (MapPat (_, Some _)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (BagMatching _)), _) -> None)
    | UnitMap, database -> Some (NormalPat (MapMatching (MapPat ([], None))))
    | IdMap a, database -> Some (NormalPat (MapMatching (MapPat ([], Some a))))
    | MapItem (l, r), database ->
        (match (toIRInKR _A l database, toIRInKR _A r database)
          with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
          | (Some (KFunPat (_, _)), _) -> None
          | (Some (KItemFunPat (_, _)), _) -> None
          | (Some (ListFunPat (_, _)), _) -> None
          | (Some (SetFunPat (_, _)), _) -> None
          | (Some (MapFunPat (_, _)), _) -> None
          | (Some (NormalPat (KLabelMatching _)), _) -> None
          | (Some (NormalPat (KItemMatching _)), _) -> None
          | (Some (NormalPat (KListMatching _)), _) -> None
          | (Some (NormalPat (KMatching _)), None) -> None
          | (Some (NormalPat (KMatching _)), Some (KLabelFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)), Some (KFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)), Some (KItemFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)), Some (ListFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)), Some (SetFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)), Some (MapFunPat (_, _))) -> None
          | (Some (NormalPat (KMatching _)),
              Some (NormalPat (KLabelMatching _)))
            -> None
          | (Some (NormalPat (KMatching _)), Some (NormalPat (KItemMatching _)))
            -> None
          | (Some (NormalPat (KMatching _)), Some (NormalPat (KListMatching _)))
            -> None
          | (Some (NormalPat (KMatching la)), Some (NormalPat (KMatching ra)))
            -> Some (NormalPat (MapMatching (MapPat ([(la, ra)], None))))
          | (Some (NormalPat (KMatching _)), Some (NormalPat (ListMatching _)))
            -> None
          | (Some (NormalPat (KMatching _)), Some (NormalPat (SetMatching _)))
            -> None
          | (Some (NormalPat (KMatching _)), Some (NormalPat (MapMatching _)))
            -> None
          | (Some (NormalPat (KMatching _)), Some (NormalPat (BagMatching _)))
            -> None
          | (Some (NormalPat (ListMatching _)), _) -> None
          | (Some (NormalPat (SetMatching _)), _) -> None
          | (Some (NormalPat (MapMatching _)), _) -> None
          | (Some (NormalPat (BagMatching _)), _) -> None)
    | MapFun (l, r), database ->
        (match getKLabelMeaning l with None -> None
          | Some s ->
            (match toIRInKListR _A r database with None -> None
              | Some ra -> Some (MapFunPat (s, ra))))
and toIRInMapR _A
  x0 database = match x0, database with
    KTerm a, database -> toIRInMap _A a database
    | KRewrite (l, r), database -> None
and toIRInSet _A
  x0 database = match x0, database with
    SetCon (a, b), database ->
      (match (toIRInSetR _A a database, toIRInSetR _A b database)
        with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
        | (Some (KFunPat (_, _)), _) -> None
        | (Some (KItemFunPat (_, _)), _) -> None
        | (Some (ListFunPat (_, _)), _) -> None
        | (Some (SetFunPat (_, _)), _) -> None
        | (Some (MapFunPat (_, _)), _) -> None
        | (Some (NormalPat (KLabelMatching _)), _) -> None
        | (Some (NormalPat (KItemMatching _)), _) -> None
        | (Some (NormalPat (KListMatching _)), _) -> None
        | (Some (NormalPat (KMatching _)), _) -> None
        | (Some (NormalPat (ListMatching _)), _) -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))), None) -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (SetMatching (SetPat (_, None)))))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (la, None)))),
            Some (NormalPat (SetMatching (SetPat (lb, Some vb)))))
          -> Some (NormalPat (SetMatching (SetPat (la @ lb, Some vb))))
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, None)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))), None) -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (ListMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (la, Some va)))),
            Some (NormalPat (SetMatching (SetPat (lb, None)))))
          -> Some (NormalPat (SetMatching (SetPat (la @ lb, Some va))))
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (SetMatching (SetPat (_, Some _)))))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (SetMatching (SetPat (_, Some _)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (MapMatching _)), _) -> None
        | (Some (NormalPat (BagMatching _)), _) -> None)
    | UnitSet, database -> Some (NormalPat (SetMatching (SetPat ([], None))))
    | IdSet a, database -> Some (NormalPat (SetMatching (SetPat ([], Some a))))
    | SetItem a, database ->
        (match toIRInKR _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching ac ->
                    Some (NormalPat (SetMatching (SetPat ([ac], None))))
                  | ListMatching _ -> None | SetMatching _ -> None
                  | MapMatching _ -> None | BagMatching _ -> None)))
    | SetFun (l, r), database ->
        (match getKLabelMeaning l with None -> None
          | Some s ->
            (match toIRInKListR _A r database with None -> None
              | Some ra -> Some (SetFunPat (s, ra))))
and toIRInSetR _A
  x0 database = match x0, database with
    KTerm a, database -> toIRInSet _A a database
    | KRewrite (l, r), database -> None
and toIRInList _A
  x0 database = match x0, database with
    ListCon (a, b), database ->
      (match (toIRInListR _A a database, toIRInListR _A b database)
        with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
        | (Some (KFunPat (_, _)), _) -> None
        | (Some (KItemFunPat (_, _)), _) -> None
        | (Some (ListFunPat (_, _)), _) -> None
        | (Some (SetFunPat (_, _)), _) -> None
        | (Some (MapFunPat (_, _)), _) -> None
        | (Some (NormalPat (KLabelMatching _)), _) -> None
        | (Some (NormalPat (KItemMatching _)), _) -> None
        | (Some (NormalPat (KListMatching _)), _) -> None
        | (Some (NormalPat (KMatching _)), _) -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))), None) -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar la))),
            Some (NormalPat (ListMatching (ListPatNoVar lb))))
          -> Some (NormalPat (ListMatching (ListPatNoVar (la @ lb))))
        | (Some (NormalPat (ListMatching (ListPatNoVar la))),
            Some (NormalPat (ListMatching (ListPat (lb, x, rb)))))
          -> Some (NormalPat (ListMatching (ListPat (la @ lb, x, rb))))
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPatNoVar _))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))), None) -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (KLabelFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (KFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (KItemFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (ListFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (SetFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (MapFunPat (_, _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (KLabelMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (KItemMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (KListMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (KMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (la, x, ra)))),
            Some (NormalPat (ListMatching (ListPatNoVar lb))))
          -> Some (NormalPat (ListMatching (ListPat (la, x, ra @ lb))))
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (ListMatching (ListPat (_, _, _)))))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (SetMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (MapMatching _)))
          -> None
        | (Some (NormalPat (ListMatching (ListPat (_, _, _)))),
            Some (NormalPat (BagMatching _)))
          -> None
        | (Some (NormalPat (SetMatching _)), _) -> None
        | (Some (NormalPat (MapMatching _)), _) -> None
        | (Some (NormalPat (BagMatching _)), _) -> None)
    | UnitList, database -> Some (NormalPat (ListMatching (ListPatNoVar [])))
    | IdList a, database ->
        Some (NormalPat (ListMatching (ListPat ([], a, []))))
    | ListItem a, database ->
        (match toIRInKR _A a database with None -> None
          | Some aa ->
            (match aa with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
              | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
              | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
              | NormalPat ab ->
                (match ab with KLabelMatching _ -> None
                  | KItemMatching _ -> None | KListMatching _ -> None
                  | KMatching ac ->
                    Some (NormalPat (ListMatching (ListPatNoVar [ac])))
                  | ListMatching _ -> None | SetMatching _ -> None
                  | MapMatching _ -> None | BagMatching _ -> None)))
    | ListFun (l, r), database ->
        (match getKLabelMeaning l with None -> None
          | Some s ->
            (match toIRInKListR _A r database with None -> None
              | Some ra -> Some (ListFunPat (s, ra))))
and toIRInListR _A
  x0 database = match x0, database with
    KTerm a, database -> toIRInList _A a database
    | KRewrite (l, r), database -> None;;

let rec ditachBagR
  = function KTerm a -> ditachBag a
    | KRewrite (a, b) ->
        (if not (hasRewriteInBag a) && not (hasRewriteInBag b)
          then Some ([(a, b)], ([], [])) else None)
and ditachBag
  = function UnitBag -> Some ([], ([], []))
    | IdBag x -> None
    | Xml (x, y, z) ->
        (if hasRewriteInBagR z then Some ([], ([Xml (x, y, z)], []))
          else Some ([], ([], [Xml (x, y, z)])))
    | SingleCell (x, y, z) ->
        (if hasRewriteInBigK z then Some ([], ([SingleCell (x, y, z)], []))
          else Some ([], ([], [SingleCell (x, y, z)])))
    | BagCon (l, r) ->
        (match (ditachBagR l, ditachBagR r) with (None, _) -> None
          | (Some (_, (_, _)), None) -> None
          | (Some (x, (y, z)), Some (u, (v, w))) ->
            Some (x @ u, (y @ v, z @ w)));;

let rec searchBagWithNameInList _A
  v x1 = match v, x1 with v, [] -> ([], ([], ([], [])))
    | v, b :: l ->
        (let (x, y) = b in
         let ((xl, xr), (yl, yr)) =
           (searchBagWithNameInIRBag _A v x, searchBagWithName _A v y) in
         let (left, (right, (acc, changeAcc))) = searchBagWithNameInList _A v l
           in
          (if null xl && null yl then (left, (right, (b :: acc, changeAcc)))
            else (if null xr && null yr
                   then (xl @ left, (yl @ right, (acc, changeAcc)))
                   else (xl @ left,
                          (yl @ right, (acc, (xr, yr) :: changeAcc))))));;

let rec normalizeBagTripleList _B
  x0 acc vars database = match x0, acc, vars, database with
    [], acc, vars, database -> Some ([], ([], (acc, vars)))
    | b :: l, acc, vars, database ->
        (match b
          with ItemB (x, y, z) ->
            (let (left, (right, (acca, accChange))) =
               searchBagWithNameInList _B x acc in
              (if null acca
                then (match normalizeBagTripleList _B l accChange vars database
                       with None -> None
                       | Some (lefta, (righta, (accaa, varsa))) ->
                         Some (left @ lefta, (right @ righta, (accaa, varsa))))
                else (match normalizeNextBag _B z acca vars database
                       with None -> None
                       | Some (lefta, (righta, (accaa, varsa))) ->
                         (match normalizeBagTripleList _B l accaa varsa database
                           with None -> None
                           | Some (leftaa, (rightaa, (accb, varsaa))) ->
                             (if null lefta && null righta
                               then Some (left @ leftaa,
   (right @ rightaa, (accb, varsaa)))
                               else Some (left @
    [(x, (removeDotInFeatureList y,
           IRBag (BagPat (lefta, Some (freshVar varsaa)))))] @
      leftaa,
   (right @ [ItemB (x, y, SUBag (righta @ [IdB (freshVar varsaa)]))] @ rightaa,
     (accb, varsaa))))))))
          | IdB _ -> None)
and normalizeNextBag _B
  a acc vars database =
    (match a with SUK _ -> Some ([], ([], (acc, vars)))
      | SUList _ -> Some ([], ([], (acc, vars)))
      | SUSet _ -> Some ([], ([], (acc, vars)))
      | SUMap _ -> Some ([], ([], (acc, vars)))
      | SUBag x -> normalizeBagTripleList _B x acc vars database);;

let rec prepareBagTripleList _A _B
  p x1 r l vars acc database = match p, x1, r, l, vars, acc, database with
    p, [], [], [], vars, acc, database ->
      (match normalizeBagTripleList _B p acc vars database with None -> None
        | Some (l, (r, (lrr, varsa))) ->
          (if null lrr && hasNoBagVarInSUBag r
            then Some (BagPat (l, Some (freshVar varsa)),
                        (r @ [IdB (freshVar varsa)], freshVar varsa :: varsa))
            else None))
    | p, [], [], b :: l, vars, acc, database ->
        (match toIRInBag _A b database with None -> None
          | Some (BagPat (x, None)) ->
            (match fillVarsBySearchBags _B p x [] vars with None -> None
              | Some (xa, (xr, varsa)) ->
                (if null xr
                  then prepareBagTripleList _A _B p [] [] l varsa
                         (acc @ [(xa, irToSUInIRBagList _A xa)]) database
                  else None))
          | Some (BagPat (_, Some _)) -> None)
    | p, [], b :: la, l, vars, acc, database ->
        (match b with BagCon (_, _) -> None | UnitBag -> None | IdBag _ -> None
          | Xml (x, y, z) ->
            (match getSubPattern _B x p with None -> None
              | Some (_, pa) ->
                (match normalizeInSUBigKWithBag _B _A x y pa z vars database
                  with None -> None
                  | Some (left, (right, varsa)) ->
                    prepareBagTripleList _A _B p [] la l varsa
                      (acc @ [([left], [right])]) database))
          | SingleCell (x, y, z) ->
            (match (getLeftInBigK z, getRightInBigK z) with (None, _) -> None
              | (Some _, None) -> None
              | (Some zl, Some zr) ->
                (match (toIRInBigK _A zl database, toSUInBigK zr)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some zla, Some zra) ->
                    prepareBagTripleList _A _B p [] la l vars
                      (acc @
                        [([(x, (removeDotInFeatureList y, zla))],
                           [ItemB (x, removeDotInFeatureList y, zra)])])
                      database)))
    | p, b :: la, r, l, vars, acc, database ->
        (let (x, y) = b in
          (match (toIRInBag _A x database, toSUInBag y) with (None, _) -> None
            | (Some (BagPat (_, None)), None) -> None
            | (Some (BagPat (xa, None)), Some ya) ->
              (match fillVarsBySearchBags _B p xa [] vars with None -> None
                | Some (xaa, (xr, varsa)) ->
                  (match completeBagBySearchBags _B ya p [] with None -> None
                    | Some (yaa, yr) ->
                      (if null xr && null yr
                        then prepareBagTripleList _A _B p la r l varsa
                               (acc @ [(xaa, yaa)]) database
                        else None)))
            | (Some (BagPat (_, Some _)), _) -> None))
and normalizeInSUBigKWithBag _A _B
  x y s b vars database =
    (match s with SUK _ -> None | SUList _ -> None | SUSet _ -> None
      | SUMap _ -> None
      | SUBag t ->
        (if membera equal_feature y DotDotDot
          then (match ditachBagR b with None -> None
                 | Some (u, (v, w)) ->
                   (match prepareBagTripleList _B _A t u v w vars [] database
                     with None -> None
                     | Some (left, (right, varsa)) ->
                       Some ((x, (removeDotInFeatureList y, IRBag left)),
                              (ItemB (x, removeDotInFeatureList y, SUBag right),
                                varsa))))
          else (match ditachBagRWithVars b with None -> None
                 | Some (u, (v, w)) ->
                   (match
                     prepareBagNoDot _B _A t u v w vars (BagPat ([], None), [])
                       database
                     with None -> None
                     | Some (left, (right, varsa)) ->
                       Some ((x, (y, IRBag left)),
                              (ItemB (x, y, SUBag right), varsa))))))
and prepareBagNoDot _A _B
  p x1 r l vars acc database = match p, x1, r, l, vars, acc, database with
    p, [], [], [], vars, acc, database ->
      (match normalizeBagNoDot _B p acc database with None -> None
        | Some (x, y) -> Some (x, (y, vars)))
    | p, [], [], b :: l, vars, acc, database ->
        (match toIRInBag _A b database with None -> None
          | Some (BagPat (x, y)) ->
            (match fillVarsBySearchBags _B p x [] vars with None -> None
              | Some (xa, (xr, varsa)) ->
                (if null xr
                  then (match
                         mergeBagTuple (BagPat (xa, y))
                           (irToSUInIRBagList _A xa) acc
                         with None -> None
                         | Some acca ->
                           prepareBagNoDot _A _B p [] [] l varsa acca database)
                  else None)))
    | p, [], b :: la, l, vars, acc, database ->
        (match b with BagCon (_, _) -> None | UnitBag -> None | IdBag _ -> None
          | Xml (x, y, z) ->
            (match getSubPattern _B x p with None -> None
              | Some (_, pa) ->
                (match normalizeInSUBigKWithBag _B _A x y pa z vars database
                  with None -> None
                  | Some (left, (right, varsa)) ->
                    (match mergeBagTuple (BagPat ([left], None)) [right] acc
                      with None -> None
                      | Some acca ->
                        prepareBagNoDot _A _B p [] la l varsa acca database)))
          | SingleCell (x, y, z) ->
            (match (getLeftInBigK z, getRightInBigK z) with (None, _) -> None
              | (Some _, None) -> None
              | (Some zl, Some zr) ->
                (match (toIRInBigK _A zl database, toSUInBigK zr)
                  with (None, _) -> None | (Some _, None) -> None
                  | (Some zla, Some zra) ->
                    (match
                      mergeBagTuple
                        (BagPat ([(x, (removeDotInFeatureList y, zla))], None))
                        [ItemB (x, removeDotInFeatureList y, zra)] acc
                      with None -> None
                      | Some acca ->
                        prepareBagNoDot _A _B p [] la l vars acca database))))
    | p, b :: la, r, l, vars, acc, database ->
        (let (x, y) = b in
          (match (toIRInBag _A x database, toSUInBag y) with (None, _) -> None
            | (Some (BagPat (_, _)), None) -> None
            | (Some (BagPat (xa, v)), Some ya) ->
              (match fillVarsBySearchBags _B p xa [] vars with None -> None
                | Some (xaa, (xr, varsa)) ->
                  (match completeBagBySearchBags _B ya p [] with None -> None
                    | Some (yaa, yr) ->
                      (if null xr && null yr
                        then (match mergeBagTuple (BagPat (xaa, v)) yaa acc
                               with None -> None
                               | Some acca ->
                                 prepareBagNoDot _A _B p la r l varsa acca
                                   database)
                        else None)))));;

let rec validContextInKItem
  = function
    KItemC (l, r, ty) -> validContextInKLabelR l && validContextInKListR r
    | Constant (a, b) -> true
    | IdKItem (a, b) -> true
    | HOLE a -> true
and validContextInKItemR
  = function KTerm t -> validContextInKItem t
    | KRewrite (l, r) ->
        (match l with KItemC (_, _, _) -> false | Constant (_, _) -> false
          | IdKItem (_, _) -> false | HOLE _ -> true)
and validContextInK
  = function Tilda (a, t) -> validContextInKR a && validContextInKR t
    | UnitK -> true
    | SingleK a -> validContextInKItemR a
    | IdK a -> true
    | KFun (l, r) -> validContextInKLabel l && validContextInKListR r
and validContextInKR = function KTerm a -> validContextInK a
                       | KRewrite (l, r) -> false
and validContextInList
  = function ListCon (l, r) -> validContextInListR l && validContextInListR r
    | UnitList -> true
    | IdList a -> true
    | ListItem a -> validContextInKR a
    | ListFun (l, r) -> validContextInKLabel l && validContextInKListR r
and validContextInListR = function KTerm a -> validContextInList a
                          | KRewrite (l, r) -> false
and validContextInBigK = function TheK t -> validContextInKR t
                         | TheList t -> validContextInListR t
                         | TheSet t -> validContextInSetR t
                         | TheMap t -> validContextInMapR t
and validContextInBag
  = function BagCon (l, r) -> validContextInBagR l && validContextInBagR r
    | UnitBag -> true
    | IdBag a -> true
    | Xml (a, n, t) -> validContextInBagR t
    | SingleCell (a, n, t) -> validContextInBigK t
and validContextInBagR = function KTerm a -> validContextInBag a
                         | KRewrite (l, r) -> false
and validContextInBigKWithBag = function TheBigK a -> validContextInBigK a
                                | TheBigBag b -> validContextInBagR b
                                | TheLabel b -> validContextInKLabelR b
and validContextInKList
  = function KListCon (b, t) -> validContextInKListR b && validContextInKListR t
    | UnitKList -> true
    | KListItem a -> validContextInBigKWithBag a
    | IdKList a -> true
and validContextInKListR = function KTerm t -> validContextInKList t
                           | KRewrite (l, r) -> false
and validContextInKLabel
  = function KLabelC a -> true
    | KLabelFun (a, b) -> validContextInKLabel a && validContextInKListR b
    | IdKLabel n -> true
and validContextInMap
  = function MapCon (l, r) -> validContextInMapR l && validContextInMapR r
    | UnitMap -> true
    | IdMap a -> true
    | MapItem (l, r) -> validContextInKR l && validContextInKR r
    | MapFun (l, r) -> validContextInKLabel l && validContextInKListR r
and validContextInMapR = function KTerm a -> validContextInMap a
                         | KRewrite (l, r) -> false
and validContextInSet
  = function SetCon (l, r) -> validContextInSetR l && validContextInSetR r
    | UnitSet -> true
    | IdSet a -> true
    | SetItem a -> validContextInKR a
    | SetFun (l, r) -> validContextInKLabel l && validContextInKListR r
and validContextInSetR = function KTerm a -> validContextInSet a
                         | KRewrite (l, r) -> false
and validContextInKLabelR = function KTerm n -> validContextInKLabel n
                            | KRewrite (l, r) -> false;;

let rec getResultSortInAttrs
  = function [] -> None
    | Result a :: l ->
        (match getResultSortInAttrs l with None -> Some a | Some _ -> None)
    | Attr v :: l -> getResultSortInAttrs l
    | Heat :: l -> getResultSortInAttrs l
    | Cool :: l -> getResultSortInAttrs l
    | Transition :: l -> getResultSortInAttrs l
    | Anywhere :: l -> getResultSortInAttrs l
    | Structural :: l -> getResultSortInAttrs l
    | Owise :: l -> getResultSortInAttrs l
    | Macro :: l -> getResultSortInAttrs l;;

let rec locateHoleInKItem
  = function
    KItemC (l, r, ty) ->
      (match locateHoleInKLabelR l
        with None ->
          (match locateHoleInKListR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInKListR r with None -> Some a | Some _ -> None))
    | Constant (a, b) -> None
    | IdKItem (a, b) -> None
    | HOLE a -> Some a
and locateHoleInKItemR
  = function KTerm t -> locateHoleInKItem t
    | KRewrite (l, r) ->
        (match locateHoleInKItem l
          with None ->
            (match locateHoleInKItem r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKItem r with None -> Some a | Some _ -> None))
and locateHoleInK
  = function
    Tilda (l, r) ->
      (match locateHoleInKR l
        with None ->
          (match locateHoleInKR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInKR r with None -> Some a | Some _ -> None))
    | UnitK -> None
    | IdK a -> None
    | SingleK a -> locateHoleInKItemR a
    | KFun (l, r) ->
        (match locateHoleInKLabel l
          with None ->
            (match locateHoleInKListR r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKListR r with None -> Some a | Some _ -> None))
and locateHoleInKR
  = function KTerm a -> locateHoleInK a
    | KRewrite (l, r) ->
        (match locateHoleInK l
          with None ->
            (match locateHoleInK r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInK r with None -> Some a | Some _ -> None))
and locateHoleInList
  = function
    ListCon (l, r) ->
      (match locateHoleInListR l
        with None ->
          (match locateHoleInListR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInListR r with None -> Some a | Some _ -> None))
    | UnitList -> None
    | IdList a -> None
    | ListItem a -> locateHoleInKR a
    | ListFun (l, r) ->
        (match locateHoleInKLabel l
          with None ->
            (match locateHoleInKListR r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKListR r with None -> Some a | Some _ -> None))
and locateHoleInListR
  = function KTerm a -> locateHoleInList a
    | KRewrite (l, r) ->
        (match locateHoleInList l
          with None ->
            (match locateHoleInList r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInList r with None -> Some a | Some _ -> None))
and locateHoleInBigK = function TheK t -> locateHoleInKR t
                       | TheList t -> locateHoleInListR t
                       | TheSet t -> locateHoleInSetR t
                       | TheMap t -> locateHoleInMapR t
and locateHoleInBag
  = function
    BagCon (l, r) ->
      (match locateHoleInBagR l
        with None ->
          (match locateHoleInBagR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInBagR r with None -> Some a | Some _ -> None))
    | UnitBag -> None
    | IdBag a -> None
    | Xml (a, n, t) -> locateHoleInBagR t
    | SingleCell (a, n, t) -> locateHoleInBigK t
and locateHoleInBagR
  = function KTerm a -> locateHoleInBag a
    | KRewrite (l, r) ->
        (match locateHoleInBag l
          with None ->
            (match locateHoleInBag r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInBag r with None -> Some a | Some _ -> None))
and locateHoleInBigKWithBag = function TheBigK a -> locateHoleInBigK a
                              | TheLabel a -> locateHoleInKLabelR a
                              | TheBigBag b -> locateHoleInBagR b
and locateHoleInKList
  = function
    KListCon (l, r) ->
      (match locateHoleInKListR l
        with None ->
          (match locateHoleInKListR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInKListR r with None -> Some a | Some _ -> None))
    | UnitKList -> None
    | IdKList a -> None
    | KListItem a -> locateHoleInBigKWithBag a
and locateHoleInKListR
  = function KTerm t -> locateHoleInKList t
    | KRewrite (l, r) ->
        (match locateHoleInKList l
          with None ->
            (match locateHoleInKList r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKList r with None -> Some a | Some _ -> None))
and locateHoleInKLabel
  = function KLabelC a -> None
    | KLabelFun (a, b) ->
        (match locateHoleInKLabel a with None -> locateHoleInKListR b
          | Some ty ->
            (match locateHoleInKListR b with None -> Some ty | Some _ -> None))
    | IdKLabel n -> None
and locateHoleInMap
  = function
    MapCon (l, r) ->
      (match locateHoleInMapR l
        with None ->
          (match locateHoleInMapR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInMapR r with None -> Some a | Some _ -> None))
    | UnitMap -> None
    | IdMap a -> None
    | MapItem (l, r) ->
        (match locateHoleInKR l
          with None ->
            (match locateHoleInKR r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKR r with None -> Some a | Some _ -> None))
    | MapFun (l, r) ->
        (match locateHoleInKLabel l
          with None ->
            (match locateHoleInKListR r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKListR r with None -> Some a | Some _ -> None))
and locateHoleInMapR
  = function KTerm a -> locateHoleInMap a
    | KRewrite (l, r) ->
        (match locateHoleInMap l
          with None ->
            (match locateHoleInMap r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInMap r with None -> Some a | Some _ -> None))
and locateHoleInSet
  = function
    SetCon (l, r) ->
      (match locateHoleInSetR l
        with None ->
          (match locateHoleInSetR r with None -> None | Some a -> Some a)
        | Some a ->
          (match locateHoleInSetR r with None -> Some a | Some _ -> None))
    | UnitSet -> None
    | IdSet a -> None
    | SetItem a -> locateHoleInKR a
    | SetFun (l, r) ->
        (match locateHoleInKLabel l
          with None ->
            (match locateHoleInKListR r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKListR r with None -> Some a | Some _ -> None))
and locateHoleInSetR
  = function KTerm a -> locateHoleInSet a
    | KRewrite (l, r) ->
        (match locateHoleInSet l
          with None ->
            (match locateHoleInSet r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInSet r with None -> Some a | Some _ -> None))
and locateHoleInKLabelR
  = function KTerm n -> locateHoleInKLabel n
    | KRewrite (l, r) ->
        (match locateHoleInKLabel l
          with None ->
            (match locateHoleInKLabel r with None -> None | Some a -> Some a)
          | Some a ->
            (match locateHoleInKLabel r with None -> Some a | Some _ -> None));;

let rec hasHoleInSUKLabel = function SUKLabel a -> false
                            | SUKLabelFun (a, b) -> hasHoleInSUKList b
                            | SUIdKLabel n -> false
and hasHoleInSUBigKWithLabel = function SUBigBag a -> hasHoleInSUBigKWithBag a
                               | SUBigLabel a -> hasHoleInSUKLabel a
and hasHoleInSUKList
  = function [] -> false
    | ItemKl t :: l -> hasHoleInSUBigKWithLabel t || hasHoleInSUKList l
    | IdKl t :: l -> hasHoleInSUKList l
and hasHoleInSUKItem
  = function SUKItem (l, r, ty) -> hasHoleInSUKLabel l || hasHoleInSUKList r
    | SUIdKItem (a, b) -> false
    | SUHOLE a -> true
and hasHoleInSUK
  = function [] -> false
    | IdFactor t :: l -> hasHoleInSUK l
    | ItemFactor t :: l -> hasHoleInSUKItem t || hasHoleInSUK l
    | SUKKItem (a, b, ty) :: l ->
        hasHoleInSUKLabel a || (hasHoleInSUKList b || hasHoleInSUK l)
and hasHoleInSUMap
  = function [] -> false
    | IdM t :: l -> hasHoleInSUMap l
    | ItemM (a, b) :: l ->
        hasHoleInSUK a || (hasHoleInSUK b || hasHoleInSUMap l)
    | SUMapKItem (a, b) :: l ->
        hasHoleInSUKLabel a || (hasHoleInSUKList b || hasHoleInSUMap l)
and hasHoleInSUSet
  = function [] -> false
    | IdS t :: l -> hasHoleInSUSet l
    | ItemS t :: l -> hasHoleInSUK t || hasHoleInSUSet l
    | SUSetKItem (a, b) :: l ->
        hasHoleInSUKLabel a || (hasHoleInSUKList b || hasHoleInSUSet l)
and hasHoleInSUList
  = function [] -> false
    | IdL t :: l -> hasHoleInSUList l
    | ItemL t :: l -> hasHoleInSUK t || hasHoleInSUList l
    | SUListKItem (a, b) :: l ->
        hasHoleInSUKLabel a || (hasHoleInSUKList b || hasHoleInSUList l)
and hasHoleInSUBigKWithBag = function SUK a -> hasHoleInSUK a
                             | SUList a -> hasHoleInSUList a
                             | SUSet a -> hasHoleInSUSet a
                             | SUMap a -> hasHoleInSUMap a
                             | SUBag a -> hasHoleInSUBag a
and hasHoleInSUBag
  = function [] -> false
    | IdB t :: l -> hasHoleInSUBag l
    | ItemB (x, y, z) :: l -> hasHoleInSUBigKWithBag z || hasHoleInSUBag l;;

let rec updateFunInRules _A _D _E
  a x1 = match a, x1 with
    a, [] ->
      (let (s, (x, (y, (z, rs)))) = a in
        (if membera (equal_ruleAttrib _D _E) rs Owise
          then Some [FunPat (s, [], Some (x, (y, z)))]
          else Some [FunPat (s, [(x, (y, z))], None)]))
    | a, b :: l ->
        (match b
          with FunPat (s, rl, None) ->
            (let (sa, (x, (y, (z, rs)))) = a in
              (if equal_labela _A s sa
                then (if membera (equal_ruleAttrib _D _E) rs Owise
                       then Some (FunPat (s, rl, Some (x, (y, z))) :: l)
                       else Some (FunPat (s, rl @ [(x, (y, z))], None) :: l))
                else (match updateFunInRules _A _D _E a l with None -> None
                       | Some la -> Some (b :: la))))
          | FunPat (s, rl, Some r) ->
            (let (sa, (x, (y, (z, rs)))) = a in
              (if equal_labela _A s sa
                then (if membera (equal_ruleAttrib _D _E) rs Owise then None
                       else Some (FunPat (s, rl @ [(x, (y, z))], Some r) :: l))
                else (match updateFunInRules _A _D _E a l with None -> None
                       | Some la -> Some (b :: la))))
          | MacroPat (_, _, _) -> None | AnywherePat (_, _, _, _) -> None
          | KRulePat (_, _, _, _) -> None | BagRulePat (_, _, _, _) -> None);;

let rec fillHoleInKItem
  xa0 x tya = match xa0, x, tya with
    KItemC (l, r, ty), x, tya ->
      KItemC (fillHoleInKLabelR l x tya, fillHoleInKListR r x tya, ty)
    | Constant (a, b), x, ty -> Constant (a, b)
    | IdKItem (a, b), x, ty -> IdKItem (a, b)
    | HOLE a, x, ty -> IdKItem (x, ty)
and fillHoleInKItemR
  xa0 x ty = match xa0, x, ty with
    KTerm t, x, ty -> KTerm (fillHoleInKItem t x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInKItem l x ty, fillHoleInKItem r x ty)
and fillHoleInK
  xa0 x ty = match xa0, x, ty with
    Tilda (l, r), x, ty -> Tilda (fillHoleInKR l x ty, fillHoleInKR r x ty)
    | UnitK, x, ty -> UnitK
    | IdK a, x, ty -> IdK a
    | SingleK a, x, ty -> SingleK (fillHoleInKItemR a x ty)
    | KFun (l, r), x, ty ->
        KFun (fillHoleInKLabel l x ty, fillHoleInKListR r x ty)
and fillHoleInKR
  xa0 x ty = match xa0, x, ty with KTerm a, x, ty -> KTerm (fillHoleInK a x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInK l x ty, fillHoleInK r x ty)
and fillHoleInList
  xa0 x ty = match xa0, x, ty with
    ListCon (l, r), x, ty ->
      ListCon (fillHoleInListR l x ty, fillHoleInListR r x ty)
    | UnitList, x, ty -> UnitList
    | IdList a, x, ty -> IdList a
    | ListItem a, x, ty -> ListItem (fillHoleInKR a x ty)
    | ListFun (l, r), x, ty ->
        ListFun (fillHoleInKLabel l x ty, fillHoleInKListR r x ty)
and fillHoleInListR
  xa0 x ty = match xa0, x, ty with
    KTerm a, x, ty -> KTerm (fillHoleInList a x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInList l x ty, fillHoleInList r x ty)
and fillHoleInBigK
  xa0 x ty = match xa0, x, ty with TheK t, x, ty -> TheK (fillHoleInKR t x ty)
    | TheList t, x, ty -> TheList (fillHoleInListR t x ty)
    | TheSet t, x, ty -> TheSet (fillHoleInSetR t x ty)
    | TheMap t, x, ty -> TheMap (fillHoleInMapR t x ty)
and fillHoleInBag
  xa0 x ty = match xa0, x, ty with
    BagCon (l, r), x, ty ->
      BagCon (fillHoleInBagR l x ty, fillHoleInBagR r x ty)
    | UnitBag, x, ty -> UnitBag
    | IdBag a, x, ty -> IdBag a
    | Xml (a, n, t), x, ty -> Xml (a, n, fillHoleInBagR t x ty)
    | SingleCell (a, n, t), x, ty -> SingleCell (a, n, fillHoleInBigK t x ty)
and fillHoleInBagR
  xa0 x ty = match xa0, x, ty with
    KTerm a, x, ty -> KTerm (fillHoleInBag a x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInBag l x ty, fillHoleInBag r x ty)
and fillHoleInBigKWithBag
  xa0 x ty = match xa0, x, ty with
    TheBigK a, x, ty -> TheBigK (fillHoleInBigK a x ty)
    | TheBigBag b, x, ty -> TheBigBag (fillHoleInBagR b x ty)
    | TheLabel b, x, ty -> TheLabel (fillHoleInKLabelR b x ty)
and fillHoleInKList
  xa0 x ty = match xa0, x, ty with
    KListCon (l, r), x, ty ->
      KListCon (fillHoleInKListR l x ty, fillHoleInKListR r x ty)
    | UnitKList, x, ty -> UnitKList
    | IdKList a, x, ty -> IdKList a
    | KListItem a, x, ty -> KListItem (fillHoleInBigKWithBag a x ty)
and fillHoleInKListR
  xa0 x ty = match xa0, x, ty with
    KTerm t, x, ty -> KTerm (fillHoleInKList t x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInKList l x ty, fillHoleInKList r x ty)
and fillHoleInKLabel
  xa0 x ty = match xa0, x, ty with KLabelC a, x, ty -> KLabelC a
    | KLabelFun (a, b), x, ty ->
        KLabelFun (fillHoleInKLabel a x ty, fillHoleInKListR b x ty)
    | IdKLabel n, x, ty -> IdKLabel n
and fillHoleInMap
  xa0 x ty = match xa0, x, ty with
    MapCon (l, r), x, ty ->
      MapCon (fillHoleInMapR l x ty, fillHoleInMapR r x ty)
    | UnitMap, x, ty -> UnitMap
    | IdMap a, x, ty -> IdMap a
    | MapItem (l, r), x, ty ->
        MapItem (fillHoleInKR l x ty, fillHoleInKR r x ty)
    | MapFun (l, r), x, ty ->
        MapFun (fillHoleInKLabel l x ty, fillHoleInKListR r x ty)
and fillHoleInMapR
  xa0 x ty = match xa0, x, ty with
    KTerm a, x, ty -> KTerm (fillHoleInMap a x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInMap l x ty, fillHoleInMap r x ty)
and fillHoleInSet
  xa0 x ty = match xa0, x, ty with
    SetCon (l, r), x, ty ->
      SetCon (fillHoleInSetR l x ty, fillHoleInSetR r x ty)
    | UnitSet, x, ty -> UnitSet
    | IdSet a, x, ty -> IdSet a
    | SetItem a, x, ty -> SetItem (fillHoleInKR a x ty)
    | SetFun (l, r), x, ty ->
        SetFun (fillHoleInKLabel l x ty, fillHoleInKListR r x ty)
and fillHoleInSetR
  xa0 x ty = match xa0, x, ty with
    KTerm a, x, ty -> KTerm (fillHoleInSet a x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInSet l x ty, fillHoleInSet r x ty)
and fillHoleInKLabelR
  xa0 x ty = match xa0, x, ty with
    KTerm n, x, ty -> KTerm (fillHoleInKLabel n x ty)
    | KRewrite (l, r), x, ty ->
        KRewrite (fillHoleInKLabel l x ty, fillHoleInKLabel r x ty);;

let rec hasHoleInIRBag
  (BagPat (l, a)) =
    foldl (fun b (_, (_, z)) -> b || hasHoleInIRBigKWithBag z) false l
and hasHoleInIRBigKWithBag = function IRK a -> hasHoleInIRK a
                             | IRList a -> hasHoleInIRList a
                             | IRSet a -> hasHoleInIRSet a
                             | IRMap a -> hasHoleInIRMap a
                             | IRBag a -> hasHoleInIRBag a
and hasHoleInIRBigKWithLabel = function IRBigBag a -> hasHoleInIRBigKWithBag a
                               | IRBigLabel a -> false
and hasHoleInIRKList
  = function
    KListPatNoVar l ->
      foldl (fun b t -> b || hasHoleInIRBigKWithLabel t) false l
    | KListPat (l, a, r) ->
        foldl (fun b t -> b || hasHoleInIRBigKWithLabel t) false (l @ r)
and hasHoleInIRKItem = function IRKItem (l, r, ty) -> hasHoleInIRKList r
                       | IRIdKItem (a, b) -> false
                       | IRHOLE a -> true
and hasHoleInIRK
  (KPat (l, a)) = foldl (fun b t -> b || hasHoleInIRKItem t) false l
and hasHoleInIRMap
  (MapPat (l, a)) =
    foldl (fun b (x, y) -> b || (hasHoleInIRK x || hasHoleInIRK y)) false l
and hasHoleInIRSet
  (SetPat (l, a)) = foldl (fun b t -> b || hasHoleInIRK t) false l
and hasHoleInIRList
  = function ListPatNoVar l -> foldl (fun b t -> b || hasHoleInIRK t) false l
    | ListPat (l, a, r) ->
        foldl (fun b t -> b || hasHoleInIRK t) false (l @ r);;

let rec hasHoleInMatchFactor = function KLabelMatching a -> false
                               | KItemMatching a -> hasHoleInIRKItem a
                               | KListMatching a -> hasHoleInIRKList a
                               | KMatching a -> hasHoleInIRK a
                               | ListMatching a -> hasHoleInIRList a
                               | SetMatching a -> hasHoleInIRSet a
                               | MapMatching a -> hasHoleInIRMap a
                               | BagMatching a -> hasHoleInIRBag a;;

let rec hasHoleInPat = function KLabelFunPat (a, b) -> hasHoleInIRKList b
                       | KFunPat (a, b) -> hasHoleInIRKList b
                       | KItemFunPat (a, b) -> hasHoleInIRKList b
                       | ListFunPat (a, b) -> hasHoleInIRKList b
                       | SetFunPat (a, b) -> hasHoleInIRKList b
                       | MapFunPat (a, b) -> hasHoleInIRKList b
                       | NormalPat b -> hasHoleInMatchFactor b;;

let rec getIRKLabel
  x = (match x with IRKLabel a -> Some a | IRIdKLabel _ -> None);;

let rec normalizeRules _A _B
  x0 theory database subG = match x0, theory, database, subG with
    [], theory, database, subG -> Some []
    | KRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInKR a
          then (match (getLeftInKR a, getRightInKR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInKR _A al database, toSUInKR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUK ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then (match ala with KLabelFunPat (_, _) -> None
                                       | KFunPat (_, _) -> None
                                       | KItemFunPat (_, _) -> None
                                       | ListFunPat (_, _) -> None
                                       | SetFunPat (_, _) -> None
                                       | MapFunPat (_, _) -> None
                                       | NormalPat (KLabelMatching _) -> None
                                       | NormalPat (KItemMatching _) -> None
                                       | NormalPat (KListMatching _) -> None
                                       | NormalPat (KMatching (KPat ([], _))) ->
 None
                                       |
 NormalPat (KMatching (KPat ([IRKItem (alaa, alb, _)], None))) ->
 (match normalizeRules _A _B l theory database subG with None -> None
   | Some la ->
     (match getIRKLabel alaa with None -> None
       | Some ss ->
         (if isFunctionItem (equal_label _A) ss database then None
           else Some (MacroPat (ss, alb, ara) :: la))))
                                       |
 NormalPat (KMatching (KPat ([IRKItem (_, _, _)], Some _))) -> None
                                       |
 NormalPat (KMatching (KPat (IRKItem (_, _, _) :: _ :: _, _))) -> None
                                       |
 NormalPat (KMatching (KPat (IRIdKItem (_, _) :: _, _))) -> None
                                       |
 NormalPat (KMatching (KPat (IRHOLE _ :: _, _))) -> None
                                       | NormalPat (ListMatching _) -> None
                                       | NormalPat (SetMatching _) -> None
                                       | NormalPat (MapMatching _) -> None
                                       | NormalPat (BagMatching _) -> None)
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat (KLabelMatching _) -> None
      | NormalPat (KItemMatching _) -> None
      | NormalPat (KListMatching _) -> None
      | NormalPat (KMatching (KPat ([], _))) -> None
      | NormalPat (KMatching (KPat ([IRKItem (IRKLabel ss, alb, _)], None))) ->
        (match normalizeRules _A _B l theory database subG with None -> None
          | Some la ->
            Some (AnywherePat
                    (ss, alb, ara,
                      SUKItem
                        (SUKLabel (ConstToLabel (BoolConst true)), [],
                          [Bool])) ::
                   la))
      | NormalPat (KMatching (KPat ([IRKItem (IRKLabel _, _, _)], Some _))) ->
        None
      | NormalPat (KMatching (KPat (IRKItem (IRKLabel _, _, _) :: _ :: _, _)))
        -> None
      | NormalPat (KMatching (KPat (IRKItem (IRIdKLabel _, _, _) :: _, _))) ->
        None
      | NormalPat (KMatching (KPat (IRIdKItem (_, _) :: _, _))) -> None
      | NormalPat (KMatching (KPat (IRHOLE _ :: _, _))) -> None
      | NormalPat (ListMatching _) -> None | NormalPat (SetMatching _) -> None
      | NormalPat (MapMatching _) -> None | NormalPat (BagMatching _) -> None)
                                       else (match ala
      with KLabelFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | KFunPat (ss, alb) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (KFunPat (ss, alb),
                            (KSubs ara,
                              (SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                                b))))
                     aa)
          else None)
      | KItemFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | ListFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | SetFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | MapFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | NormalPat _ ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (KRulePat
                               (alaa, ara,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)))))))
          else None)
    | KRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInKR a
          then (match (getLeftInKR a, getRightInKR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInKR _A al database, (toSUInKR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUK ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat (KLabelMatching _) -> None
      | NormalPat (KItemMatching _) -> None
      | NormalPat (KListMatching _) -> None
      | NormalPat (KMatching (KPat ([], _))) -> None
      | NormalPat (KMatching (KPat ([IRKItem (IRKLabel ss, alb, _)], None))) ->
        (match normalizeRules _A _B l theory database subG with None -> None
          | Some la -> Some (AnywherePat (ss, alb, ara, ca) :: la))
      | NormalPat (KMatching (KPat ([IRKItem (IRKLabel _, _, _)], Some _))) ->
        None
      | NormalPat (KMatching (KPat (IRKItem (IRKLabel _, _, _) :: _ :: _, _)))
        -> None
      | NormalPat (KMatching (KPat (IRKItem (IRIdKLabel _, _, _) :: _, _))) ->
        None
      | NormalPat (KMatching (KPat (IRIdKItem (_, _) :: _, _))) -> None
      | NormalPat (KMatching (KPat (IRHOLE _ :: _, _))) -> None
      | NormalPat (ListMatching _) -> None | NormalPat (SetMatching _) -> None
      | NormalPat (MapMatching _) -> None | NormalPat (BagMatching _) -> None)
                                       else (match ala
      with KLabelFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | KFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A (ss, (ala, (KSubs ara, (ca, b))))
                     aa)
          else None)
      | KItemFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | ListFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | SetFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | MapFunPat (_, _) ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)
      | NormalPat _ ->
        (match ala with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
          | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
          | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
          | NormalPat (KLabelMatching _) -> None
          | NormalPat (KItemMatching _) -> None
          | NormalPat (KListMatching _) -> None
          | NormalPat (KMatching alaa) ->
            (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat (alaa, ara, ca, true) :: la)
                  else Some (KRulePat (alaa, ara, ca, false) :: la)))
          | NormalPat (ListMatching _) -> None
          | NormalPat (SetMatching _) -> None
          | NormalPat (MapMatching _) -> None
          | NormalPat (BagMatching _) -> None)))))))
          else None)
    | KItemRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInKItemR a
          then (match (getLeftInKItemR a, getRightInKItemR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInKItemR _A al database, toSUInKItemR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUKItem ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then (match ala with KLabelFunPat (_, _) -> None
                                       | KFunPat (_, _) -> None
                                       | KItemFunPat (_, _) -> None
                                       | ListFunPat (_, _) -> None
                                       | SetFunPat (_, _) -> None
                                       | MapFunPat (_, _) -> None
                                       | NormalPat (KLabelMatching _) -> None
                                       |
 NormalPat (KItemMatching (IRKItem (alaa, alb, _))) ->
 (match normalizeRules _A _B l theory database subG with None -> None
   | Some la ->
     (match getIRKLabel alaa with None -> None
       | Some ss ->
         (if isFunctionItem (equal_label _A) ss database then None
           else Some (MacroPat (ss, alb, [ItemFactor ara]) :: la))))
                                       |
 NormalPat (KItemMatching (IRIdKItem (_, _))) -> None
                                       | NormalPat (KItemMatching (IRHOLE _)) ->
 None
                                       | NormalPat (KListMatching _) -> None
                                       | NormalPat (KMatching _) -> None
                                       | NormalPat (ListMatching _) -> None
                                       | NormalPat (SetMatching _) -> None
                                       | NormalPat (MapMatching _) -> None
                                       | NormalPat (BagMatching _) -> None)
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat (KLabelMatching _) -> None
      | NormalPat (KItemMatching (IRKItem (IRKLabel ss, alb, _))) ->
        (match normalizeRules _A _B l theory database subG with None -> None
          | Some la ->
            Some (AnywherePat
                    (ss, alb, [ItemFactor ara],
                      SUKItem
                        (SUKLabel (ConstToLabel (BoolConst true)), [],
                          [Bool])) ::
                   la))
      | NormalPat (KItemMatching (IRKItem (IRIdKLabel _, _, _))) -> None
      | NormalPat (KItemMatching (IRIdKItem (_, _))) -> None
      | NormalPat (KItemMatching (IRHOLE _)) -> None
      | NormalPat (KListMatching _) -> None | NormalPat (KMatching _) -> None
      | NormalPat (ListMatching _) -> None | NormalPat (SetMatching _) -> None
      | NormalPat (MapMatching _) -> None | NormalPat (BagMatching _) -> None)
                                       else (match ala
      with KLabelFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))
      | KFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))
      | KItemFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (KItemSubs ara,
                                  (SUKItem
                                     (SUKLabel (ConstToLabel (BoolConst true)),
                                       [], [Bool]),
                                    b))))
                     aa)
          else None)
      | ListFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))
      | SetFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))
      | MapFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))
      | NormalPat _ ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                            la))))))))))
          else None)
    | KItemRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInKItemR a
          then (match (getLeftInKItemR a, getRightInKItemR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInKItemR _A al database,
                       (toSUInKItemR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUKItem ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat (KLabelMatching _) -> None
      | NormalPat (KItemMatching (IRKItem (IRKLabel ss, alb, _))) ->
        (match normalizeRules _A _B l theory database subG with None -> None
          | Some la -> Some (AnywherePat (ss, alb, [ItemFactor ara], ca) :: la))
      | NormalPat (KItemMatching (IRKItem (IRIdKLabel _, _, _))) -> None
      | NormalPat (KItemMatching (IRIdKItem (_, _))) -> None
      | NormalPat (KItemMatching (IRHOLE _)) -> None
      | NormalPat (KListMatching _) -> None | NormalPat (KMatching _) -> None
      | NormalPat (ListMatching _) -> None | NormalPat (SetMatching _) -> None
      | NormalPat (MapMatching _) -> None | NormalPat (BagMatching _) -> None)
                                       else (match ala
      with KLabelFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))
      | KFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))
      | KItemFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (KItemSubs ara, (ca, b)))) aa)
          else None)
      | ListFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))
      | SetFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))
      | MapFunPat (_, _) ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))
      | NormalPat _ ->
        (let NormalPat (KItemMatching alaa) = ala in
          (match normalizeRules _A _B l theory database subG with None -> None
            | Some la ->
              (if membera (equal_ruleAttrib _B _A) b Transition
                then Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               true) ::
                            la)
                else Some (KRulePat
                             (KPat ([alaa], None), [ItemFactor ara], ca,
                               false) ::
                            la))))))))))
          else None)
    | KLabelRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInKLabelR a
          then (match (getLeftInKLabelR a, getRightInKLabelR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInKLabelR _A al database, toSUInKLabelR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUKLabel ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (KLabelSubs ara,
                                  (SUKItem
                                     (SUKLabel (ConstToLabel (BoolConst true)),
                                       [], [Bool]),
                                    b))))
                     aa)
          else None)
      | KFunPat (_, _) -> None | KItemFunPat (_, _) -> None
      | ListFunPat (_, _) -> None | SetFunPat (_, _) -> None
      | MapFunPat (_, _) -> None | NormalPat _ -> None))))))
          else None)
    | KLabelRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInKLabelR a
          then (match (getLeftInKLabelR a, getRightInKLabelR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInKLabelR _A al database,
                       (toSUInKLabelR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUKLabel ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (KLabelSubs ara, (ca, b)))) aa)
          else None)
      | KFunPat (_, _) -> None | KItemFunPat (_, _) -> None
      | ListFunPat (_, _) -> None | SetFunPat (_, _) -> None
      | MapFunPat (_, _) -> None | NormalPat _ -> None))))))
          else None)
    | BagRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInBagR a
          then (match ditachBagR a with None -> None
                 | Some (u, (v, w)) ->
                   (match getConfiguration theory with [] -> None
                     | [p] ->
                       (match toSUInBag p with None -> None
                         | Some pa ->
                           (match
                             prepareBagTripleList _A _B pa u v w
                               (getAllMetaVarsInBagR a) [] database
                             with None -> None
                             | Some (al, (ar, _)) ->
                               (if hasHoleInIRBag al || hasHoleInSUBag ar
                                 then None
                                 else (if membera (equal_ruleAttrib _B _A) b
    Macro
then None
else (if membera (equal_ruleAttrib _B _A) b Anywhere then None
       else (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (BagRulePat
                               (al, ar,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 true) ::
                              la)
                  else Some (BagRulePat
                               (al, ar,
                                 SUKItem
                                   (SUKLabel (ConstToLabel (BoolConst true)),
                                     [], [Bool]),
                                 false) ::
                              la))))))))
                     | _ :: _ :: _ -> None))
          else None)
    | BagRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInBagR a
          then (match ditachBagR a with None -> None
                 | Some (u, (v, w)) ->
                   (match getConfiguration theory with [] -> None
                     | [p] ->
                       (match (toSUInBag p, toSUInKItem c)
                         with (None, _) -> None | (Some _, None) -> None
                         | (Some pa, Some ca) ->
                           (match
                             prepareBagTripleList _A _B pa u v w
                               (getAllMetaVarsInBagR a) [] database
                             with None -> None
                             | Some (al, (ar, _)) ->
                               (if hasHoleInIRBag al || hasHoleInSUBag ar
                                 then None
                                 else (if membera (equal_ruleAttrib _B _A) b
    Macro
then None
else (if membera (equal_ruleAttrib _B _A) b Anywhere then None
       else (match normalizeRules _A _B l theory database subG with None -> None
              | Some la ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (BagRulePat (al, ar, ca, true) :: la)
                  else Some (BagRulePat (al, ar, ca, false) :: la))))))))
                     | _ :: _ :: _ -> None))
          else None)
    | ListRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInListR a
          then (match (getLeftInListR a, getRightInListR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInListR _A al database, toSUInListR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUList ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None
      | ListFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (ListSubs ara,
                                  (SUKItem
                                     (SUKLabel (ConstToLabel (BoolConst true)),
                                       [], [Bool]),
                                    b))))
                     aa)
          else None)
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat _ -> None))))))
          else None)
    | ListRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInListR a
          then (match (getLeftInListR a, getRightInListR a)
                 with (None, _) -> None | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInListR _A al database,
                       (toSUInListR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUList ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None
      | ListFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (ListSubs ara, (ca, b)))) aa)
          else None)
      | SetFunPat (_, _) -> None | MapFunPat (_, _) -> None
      | NormalPat _ -> None))))))
          else None)
    | SetRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInSetR a
          then (match (getLeftInSetR a, getRightInSetR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInSetR _A al database, toSUInSetR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUSet ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (SetSubs ara,
                                  (SUKItem
                                     (SUKLabel (ConstToLabel (BoolConst true)),
                                       [], [Bool]),
                                    b))))
                     aa)
          else None)
      | MapFunPat (_, _) -> None | NormalPat _ -> None))))))
          else None)
    | SetRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInSetR a
          then (match (getLeftInSetR a, getRightInSetR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInSetR _A al database, (toSUInSetR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUSet ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A (ss, (ala, (SetSubs ara, (ca, b))))
                     aa)
          else None)
      | MapFunPat (_, _) -> None | NormalPat _ -> None))))))
          else None)
    | MapRule (a, b) :: l, theory, database, subG ->
        (if hasRewriteInMapR a
          then (match (getLeftInMapR a, getRightInMapR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match (toIRInMapR _A al database, toSUInMapR ar)
                     with (None, _) -> None | (Some _, None) -> None
                     | (Some ala, Some ara) ->
                       (if hasHoleInPat ala || hasHoleInSUMap ara then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None
      | MapFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A
                     (ss, (ala, (MapSubs ara,
                                  (SUKItem
                                     (SUKLabel (ConstToLabel (BoolConst true)),
                                       [], [Bool]),
                                    b))))
                     aa)
          else None)
      | NormalPat _ -> None))))))
          else None)
    | MapRuleWithCon (a, c, b) :: l, theory, database, subG ->
        (if hasRewriteInMapR a
          then (match (getLeftInMapR a, getRightInMapR a) with (None, _) -> None
                 | (Some _, None) -> None
                 | (Some al, Some ar) ->
                   (match
                     (toIRInMapR _A al database, (toSUInMapR ar, toSUInKItem c))
                     with (None, _) -> None | (Some _, (None, _)) -> None
                     | (Some _, (Some _, None)) -> None
                     | (Some ala, (Some ara, Some ca)) ->
                       (if hasHoleInPat ala ||
                             (hasHoleInSUMap ara || hasHoleInSUKItem ca)
                         then None
                         else (if membera (equal_ruleAttrib _B _A) b Macro
                                then None
                                else (if membera (equal_ruleAttrib _B _A) b
   Anywhere
                                       then None
                                       else (match ala
      with KLabelFunPat (_, _) -> None | KFunPat (_, _) -> None
      | KItemFunPat (_, _) -> None | ListFunPat (_, _) -> None
      | SetFunPat (_, _) -> None
      | MapFunPat (ss, _) ->
        (if isFunctionItem (equal_label _A) ss database
          then (match normalizeRules _A _B l theory database subG
                 with None -> None
                 | Some aa ->
                   updateFunInRules _A _B _A (ss, (ala, (MapSubs ara, (ca, b))))
                     aa)
          else None)
      | NormalPat _ -> None))))))
          else None)
    | Context (a, b) :: l, theory, database, subG ->
        (match a
          with KItemC (KTerm (KLabelC ss), _, _) ->
            (if isFunctionItem (equal_label _A) ss database ||
                  (not (validContextInKItem a) ||
                    (membera (equal_ruleAttrib _B _A) b Macro ||
                      membera (equal_ruleAttrib _B _A) b Anywhere))
              then None
              else (match locateHoleInKItem a with None -> None
                     | Some ty ->
                       (if subsort (equal_sort _A) ty KItem subG
                         then (match (getLeftInKItem a, getRightInKItem a)
                                with (None, _) -> None | (Some _, None) -> None
                                | (Some al, Some ar) ->
                                  (match
                                    (toIRInKItem _A al database,
                                      (toIRInKItem _A
 (fillHoleInKItem al (freshVar (getAllMetaVarsInKItem al)) ty) database,
toSUInKItem (fillHoleInKItem ar (freshVar (getAllMetaVarsInKItem al)) KResult)))
                                    with (None, _) -> None
                                    | (Some (KLabelFunPat (_, _)), _) -> None
                                    | (Some (KFunPat (_, _)), _) -> None
                                    | (Some (KItemFunPat (_, _)), _) -> None
                                    | (Some (ListFunPat (_, _)), _) -> None
                                    | (Some (SetFunPat (_, _)), _) -> None
                                    | (Some (MapFunPat (_, _)), _) -> None
                                    | (Some (NormalPat (KLabelMatching _)), _)
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(None, _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (KLabelFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (KFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (KItemFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (ListFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (SetFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (MapFunPat (_, _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (KLabelMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (KItemMatching _)), None))
                                      -> None
                                    | (Some (NormalPat (KItemMatching alHole)),
(Some (NormalPat (KItemMatching ala)), Some ara))
                                      -> (match
   normalizeRules _A _B l theory database subG with None -> None
   | Some la ->
     (match getResultSortInAttrs b
       with None ->
         (if membera (equal_ruleAttrib _B _A) b Transition
           then Some (KRulePat
                        (KPat ([ala], None),
                          [ItemFactor
                             (SUIdKItem
                               (freshVar (getAllMetaVarsInKItem al), [ty]));
                            ItemFactor (irToSUInKItem _A alHole)],
                          SUKItem
                            (SUKLabel NotBool,
                              [ItemKl
                                 (SUBigBag
                                   (SUK [ItemFactor
   (SUKItem
     (SUKLabel IsKResult,
       [ItemKl
          (SUBigBag
            (SUK [ItemFactor
                    (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
       [Bool]))]))],
                              [Bool]),
                          true) ::
                       KRulePat
                         (KPat ([IRIdKItem
                                   (freshVar (getAllMetaVarsInKItem al),
                                     [KResult]);
                                  alHole],
                                 None),
                           [ItemFactor ara],
                           SUKItem
                             (SUKLabel (ConstToLabel (BoolConst true)), [],
                               [Bool]),
                           true) ::
                         la)
           else Some (KRulePat
                        (KPat ([ala], None),
                          [ItemFactor
                             (SUIdKItem
                               (freshVar (getAllMetaVarsInKItem al), [ty]));
                            ItemFactor (irToSUInKItem _A alHole)],
                          SUKItem
                            (SUKLabel NotBool,
                              [ItemKl
                                 (SUBigBag
                                   (SUK [ItemFactor
   (SUKItem
     (SUKLabel IsKResult,
       [ItemKl
          (SUBigBag
            (SUK [ItemFactor
                    (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
       [Bool]))]))],
                              [Bool]),
                          false) ::
                       KRulePat
                         (KPat ([IRIdKItem
                                   (freshVar (getAllMetaVarsInKItem al),
                                     [KResult]);
                                  alHole],
                                 None),
                           [ItemFactor ara],
                           SUKItem
                             (SUKLabel (ConstToLabel (BoolConst true)), [],
                               [Bool]),
                           false) ::
                         la))
       | Some resultT ->
         (match meet (equal_sort _A) [KResult] [resultT] subG with [] -> None
           | aa :: lista ->
             (if membera (equal_ruleAttrib _B _A) b Transition
               then Some (KRulePat
                            (KPat ([ala], None),
                              [ItemFactor
                                 (SUIdKItem
                                   (freshVar (getAllMetaVarsInKItem al), [ty]));
                                ItemFactor (irToSUInKItem _A alHole)],
                              SUKItem
                                (SUKLabel NotBool,
                                  [ItemKl
                                     (SUBigBag
                                       (SUK
 [ItemFactor
    (SUKItem
      (SUKLabel IsKResult,
        [ItemKl
           (SUBigBag
             (SUK [ItemFactor
                     (SUIdKItem
                       (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
        [Bool]))]))],
                                  [Bool]),
                              true) ::
                           KRulePat
                             (KPat ([IRIdKItem
                                       (freshVar (getAllMetaVarsInKItem al),
 aa :: lista);
                                      alHole],
                                     None),
                               [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               true) ::
                             la)
               else Some (KRulePat
                            (KPat ([ala], None),
                              [ItemFactor
                                 (SUIdKItem
                                   (freshVar (getAllMetaVarsInKItem al), [ty]));
                                ItemFactor (irToSUInKItem _A alHole)],
                              SUKItem
                                (SUKLabel NotBool,
                                  [ItemKl
                                     (SUBigBag
                                       (SUK
 [ItemFactor
    (SUKItem
      (SUKLabel IsKResult,
        [ItemKl
           (SUBigBag
             (SUK [ItemFactor
                     (SUIdKItem
                       (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
        [Bool]))]))],
                                  [Bool]),
                              false) ::
                           KRulePat
                             (KPat ([IRIdKItem
                                       (freshVar (getAllMetaVarsInKItem al),
 aa :: lista);
                                      alHole],
                                     None),
                               [ItemFactor ara],
                               SUKItem
                                 (SUKLabel (ConstToLabel (BoolConst true)), [],
                                   [Bool]),
                               false) ::
                             la)))))
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (KListMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (KMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (ListMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (SetMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (MapMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KItemMatching _)),
(Some (NormalPat (BagMatching _)), _))
                                      -> None
                                    | (Some (NormalPat (KListMatching _)), _) ->
                                      None
                                    | (Some (NormalPat (KMatching _)), _) ->
                                      None
                                    | (Some (NormalPat (ListMatching _)), _) ->
                                      None
                                    | (Some (NormalPat (SetMatching _)), _) ->
                                      None
                                    | (Some (NormalPat (MapMatching _)), _) ->
                                      None
                                    | (Some (NormalPat (BagMatching _)), _) ->
                                      None))
                         else None)))
          | KItemC (KTerm (KLabelFun (_, _)), _, _) -> None
          | KItemC (KTerm (IdKLabel _), _, _) -> None
          | KItemC (KRewrite (_, _), _, _) -> None | Constant (_, _) -> None
          | IdKItem (_, _) -> None | HOLE _ -> None)
    | ContextWithCon (a, c, b) :: l, theory, database, subG ->
        (match a
          with KItemC (KTerm (KLabelC ss), _, _) ->
            (if isFunctionItem (equal_label _A) ss database ||
                  (not (validContextInKItem a) ||
                    (membera (equal_ruleAttrib _B _A) b Macro ||
                      membera (equal_ruleAttrib _B _A) b Anywhere))
              then None
              else (match locateHoleInKItem a with None -> None
                     | Some ty ->
                       (if subsort (equal_sort _A) ty KItem subG
                         then (match
                                (getLeftInKItem a,
                                  (getRightInKItem a, toSUInKItem c))
                                with (None, _) -> None
                                | (Some _, (None, _)) -> None
                                | (Some _, (Some _, None)) -> None
                                | (Some al, (Some ar, Some ca)) ->
                                  (if hasHoleInSUKItem ca then None
                                    else (match
   (toIRInKItem _A al database,
     (toIRInKItem _A
        (fillHoleInKItem al (freshVar (getAllMetaVarsInKItem al)) ty) database,
       toSUInKItem
         (fillHoleInKItem ar (freshVar (getAllMetaVarsInKItem al)) KResult)))
   with (None, _) -> None | (Some (KLabelFunPat (_, _)), _) -> None
   | (Some (KFunPat (_, _)), _) -> None | (Some (KItemFunPat (_, _)), _) -> None
   | (Some (ListFunPat (_, _)), _) -> None
   | (Some (SetFunPat (_, _)), _) -> None | (Some (MapFunPat (_, _)), _) -> None
   | (Some (NormalPat (KLabelMatching _)), _) -> None
   | (Some (NormalPat (KItemMatching _)), (None, _)) -> None
   | (Some (NormalPat (KItemMatching _)), (Some (KLabelFunPat (_, _)), _)) ->
     None
   | (Some (NormalPat (KItemMatching _)), (Some (KFunPat (_, _)), _)) -> None
   | (Some (NormalPat (KItemMatching _)), (Some (KItemFunPat (_, _)), _)) ->
     None
   | (Some (NormalPat (KItemMatching _)), (Some (ListFunPat (_, _)), _)) -> None
   | (Some (NormalPat (KItemMatching _)), (Some (SetFunPat (_, _)), _)) -> None
   | (Some (NormalPat (KItemMatching _)), (Some (MapFunPat (_, _)), _)) -> None
   | (Some (NormalPat (KItemMatching _)),
       (Some (NormalPat (KLabelMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)),
       (Some (NormalPat (KItemMatching _)), None))
     -> None
   | (Some (NormalPat (KItemMatching alHole)),
       (Some (NormalPat (KItemMatching ala)), Some ara))
     -> (match normalizeRules _A _B l theory database subG with None -> None
          | Some la ->
            (match getResultSortInAttrs b
              with None ->
                (if membera (equal_ruleAttrib _B _A) b Transition
                  then Some (KRulePat
                               (KPat ([ala], None),
                                 [ItemFactor
                                    (SUIdKItem
                                      (freshVar (getAllMetaVarsInKItem al),
[ty]));
                                   ItemFactor (irToSUInKItem _A alHole)],
                                 SUKItem
                                   (SUKLabel AndBool,
                                     [ItemKl (SUBigBag (SUK [ItemFactor ca]));
                                       ItemKl
 (SUBigBag
   (SUK [ItemFactor
           (SUKItem
             (SUKLabel NotBool,
               [ItemKl
                  (SUBigBag
                    (SUK [ItemFactor
                            (SUKItem
                              (SUKLabel IsKResult,
                                [ItemKl
                                   (SUBigBag
                                     (SUK [ItemFactor
     (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
                                [Bool]))]))],
               [Bool]))]))],
                                     [Bool]),
                                 true) ::
                              KRulePat
                                (KPat ([IRIdKItem
  (freshVar (getAllMetaVarsInKItem al), [KResult]);
 alHole],
None),
                                  [ItemFactor ara],
                                  SUKItem
                                    (SUKLabel (ConstToLabel (BoolConst true)),
                                      [], [Bool]),
                                  true) ::
                                la)
                  else Some (KRulePat
                               (KPat ([ala], None),
                                 [ItemFactor
                                    (SUIdKItem
                                      (freshVar (getAllMetaVarsInKItem al),
[ty]));
                                   ItemFactor (irToSUInKItem _A alHole)],
                                 SUKItem
                                   (SUKLabel AndBool,
                                     [ItemKl (SUBigBag (SUK [ItemFactor ca]));
                                       ItemKl
 (SUBigBag
   (SUK [ItemFactor
           (SUKItem
             (SUKLabel NotBool,
               [ItemKl
                  (SUBigBag
                    (SUK [ItemFactor
                            (SUKItem
                              (SUKLabel IsKResult,
                                [ItemKl
                                   (SUBigBag
                                     (SUK [ItemFactor
     (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
                                [Bool]))]))],
               [Bool]))]))],
                                     [Bool]),
                                 false) ::
                              KRulePat
                                (KPat ([IRIdKItem
  (freshVar (getAllMetaVarsInKItem al), [KResult]);
 alHole],
None),
                                  [ItemFactor ara],
                                  SUKItem
                                    (SUKLabel (ConstToLabel (BoolConst true)),
                                      [], [Bool]),
                                  false) ::
                                la))
              | Some resultT ->
                (match meet (equal_sort _A) [KResult] [resultT] subG
                  with [] -> None
                  | aa :: lista ->
                    (if membera (equal_ruleAttrib _B _A) b Transition
                      then Some (KRulePat
                                   (KPat ([ala], None),
                                     [ItemFactor
(SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]));
                                       ItemFactor (irToSUInKItem _A alHole)],
                                     SUKItem
                                       (SUKLabel AndBool,
 [ItemKl (SUBigBag (SUK [ItemFactor ca]));
   ItemKl
     (SUBigBag
       (SUK [ItemFactor
               (SUKItem
                 (SUKLabel NotBool,
                   [ItemKl
                      (SUBigBag
                        (SUK [ItemFactor
                                (SUKItem
                                  (SUKLabel IsKResult,
                                    [ItemKl
                                       (SUBigBag
 (SUK [ItemFactor (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
                                    [Bool]))]))],
                   [Bool]))]))],
 [Bool]),
                                     true) ::
                                  KRulePat
                                    (KPat ([IRIdKItem
      (freshVar (getAllMetaVarsInKItem al), aa :: lista);
     alHole],
    None),
                                      [ItemFactor ara],
                                      SUKItem
(SUKLabel (ConstToLabel (BoolConst true)), [], [Bool]),
                                      true) ::
                                    la)
                      else Some (KRulePat
                                   (KPat ([ala], None),
                                     [ItemFactor
(SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]));
                                       ItemFactor (irToSUInKItem _A alHole)],
                                     SUKItem
                                       (SUKLabel AndBool,
 [ItemKl (SUBigBag (SUK [ItemFactor ca]));
   ItemKl
     (SUBigBag
       (SUK [ItemFactor
               (SUKItem
                 (SUKLabel NotBool,
                   [ItemKl
                      (SUBigBag
                        (SUK [ItemFactor
                                (SUKItem
                                  (SUKLabel IsKResult,
                                    [ItemKl
                                       (SUBigBag
 (SUK [ItemFactor (SUIdKItem (freshVar (getAllMetaVarsInKItem al), [ty]))]))],
                                    [Bool]))]))],
                   [Bool]))]))],
 [Bool]),
                                     false) ::
                                  KRulePat
                                    (KPat ([IRIdKItem
      (freshVar (getAllMetaVarsInKItem al), aa :: lista);
     alHole],
    None),
                                      [ItemFactor ara],
                                      SUKItem
(SUKLabel (ConstToLabel (BoolConst true)), [], [Bool]),
                                      false) ::
                                    la)))))
   | (Some (NormalPat (KItemMatching _)),
       (Some (NormalPat (KListMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)), (Some (NormalPat (KMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)),
       (Some (NormalPat (ListMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)), (Some (NormalPat (SetMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)), (Some (NormalPat (MapMatching _)), _))
     -> None
   | (Some (NormalPat (KItemMatching _)), (Some (NormalPat (BagMatching _)), _))
     -> None
   | (Some (NormalPat (KListMatching _)), _) -> None
   | (Some (NormalPat (KMatching _)), _) -> None
   | (Some (NormalPat (ListMatching _)), _) -> None
   | (Some (NormalPat (SetMatching _)), _) -> None
   | (Some (NormalPat (MapMatching _)), _) -> None
   | (Some (NormalPat (BagMatching _)), _) -> None)))
                         else None)))
          | KItemC (KTerm (KLabelFun (_, _)), _, _) -> None
          | KItemC (KTerm (IdKLabel _), _, _) -> None
          | KItemC (KRewrite (_, _), _, _) -> None | Constant (_, _) -> None
          | IdKItem (_, _) -> None | HOLE _ -> None);;

let rec getAllRulesInKModuleItemList
  = function [] -> []
    | TheSyntax x :: l -> getAllRulesInKModuleItemList l
    | Imports x :: l -> getAllRulesInKModuleItemList l
    | TheConfiguration x :: l -> getAllRulesInKModuleItemList l
    | TheRule x :: l -> x :: getAllRulesInKModuleItemList l;;

let rec getAllRulesInKModule (Module (a, l)) = getAllRulesInKModuleItemList l;;

let rec getAllRules
  = function TheFile (Single (TheRequires s)) -> []
    | TheFile (Single (TheModule m)) -> getAllRulesInKModule m
    | TheFile (Con (TheRequires s, l)) -> getAllRules (TheFile l)
    | TheFile (Con (TheModule m, l)) ->
        getAllRulesInKModule m @ getAllRules (TheFile l);;

let rec typeCheckRules _A _B _D
  theory database subG =
    (match normalizeRules _A _B (getAllRules theory) theory database subG
      with None -> None
      | Some l ->
        (if wellFormRules _D l
          then inferTypesInRules _A _B _D l theory database subG else None));;

let rec applyAllMacroRulesCheck _A _B _C
  stl theory database subG =
    (match typeCheckRules _B _C _A theory database subG with None -> None
      | Some l ->
        (match realConfigurationTest _A _B _C _A stl theory database subG
          with None -> None
          | Some bl ->
            (let Some (x, y) = divideMacroRules _B _C _A l subG in
              (match
                applyAllMacroRulesInList _B _C _A x (Some y) bl database subG
                with None -> None
                | Some (la, confi) ->
                  (if wellFormRules _A la
                    then (match
                           inferTypesInRules _B _C _A la theory database subG
                           with None -> None
                           | Some laa ->
                             (match
                               inferTypesInRules _B _C _A
                                 (adjustKSortsInRulePats laa) theory database
                                 subG
                               with None -> None
                               | Some lb ->
                                 (match
                                   typeCheckProgramState _B _C _A confi database
                                     subG
                                   with None -> None
                                   | Some confia -> Some (lb, confia))))
                    else None)))));;

let rec fst (x1, x2) = x1;;

let rec divmod_nat
  m n = (if equal_nata n Zero_nat || less_nat m n then (Zero_nat, m)
          else (let a = divmod_nat (minus_nat m n) n in
                let (q, aa) = a in
                 (Suc q, aa)));;

let rec divide_nat m n = fst (divmod_nat m n);;

let enum_nibble : nibble list
  = [Nibble0; Nibble1; Nibble2; Nibble3; Nibble4; Nibble5; Nibble6; Nibble7;
      Nibble8; Nibble9; NibbleA; NibbleB; NibbleC; NibbleD; NibbleE; NibbleF];;

let rec snd (x1, x2) = x2;;

let rec mod_nat m n = snd (divmod_nat m n);;

let rec nat_of_num
  = function Bit1 n -> (let m = nat_of_num n in Suc (plus_nata m m))
    | Bit0 n -> (let m = nat_of_num n in plus_nata m m)
    | One -> one_nata;;

let rec nth x0 x1 = match x0, x1 with x :: xs, Suc n -> nth xs n
              | x :: xs, Zero_nat -> x;;

let rec nibble_of_nat
  n = nth enum_nibble (mod_nat n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))));;

let rec nat_of_char
  = function
    Char (NibbleF, NibbleF) ->
      nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleF, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleE, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))))
    | Char (NibbleD, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleD, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleC, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))))
    | Char (NibbleB, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleB, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (NibbleA, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
    | Char (Nibble9, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble9, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble8, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
    | Char (Nibble7, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble7, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One))))))
    | Char (Nibble6, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble6, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One))))))
    | Char (Nibble5, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble5, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One))))))
    | Char (Nibble4, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble4, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One))))))
    | Char (Nibble3, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit1 One)))))
    | Char (Nibble3, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit1 One)))))
    | Char (Nibble3, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit1 One)))))
    | Char (Nibble3, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit1 One)))))
    | Char (Nibble3, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit1 One)))))
    | Char (Nibble3, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit1 One)))))
    | Char (Nibble3, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit1 One)))))
    | Char (Nibble3, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit1 One)))))
    | Char (Nibble3, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit1 One)))))
    | Char (Nibble3, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit1 One)))))
    | Char (Nibble2, NibbleF) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 (Bit0 One)))))
    | Char (Nibble2, NibbleE) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 (Bit0 One)))))
    | Char (Nibble2, NibbleD) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 (Bit0 One)))))
    | Char (Nibble2, NibbleC) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 (Bit0 One)))))
    | Char (Nibble2, NibbleB) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 (Bit0 One)))))
    | Char (Nibble2, NibbleA) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 (Bit0 One)))))
    | Char (Nibble2, Nibble9) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 (Bit0 One)))))
    | Char (Nibble2, Nibble8) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 (Bit0 One)))))
    | Char (Nibble2, Nibble7) ->
        nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble6) ->
        nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble5) ->
        nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble4) ->
        nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble3) ->
        nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble2) ->
        nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble1) ->
        nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
    | Char (Nibble2, Nibble0) ->
        nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 (Bit0 One)))))
    | Char (Nibble1, NibbleF) -> nat_of_num (Bit1 (Bit1 (Bit1 (Bit1 One))))
    | Char (Nibble1, NibbleE) -> nat_of_num (Bit0 (Bit1 (Bit1 (Bit1 One))))
    | Char (Nibble1, NibbleD) -> nat_of_num (Bit1 (Bit0 (Bit1 (Bit1 One))))
    | Char (Nibble1, NibbleC) -> nat_of_num (Bit0 (Bit0 (Bit1 (Bit1 One))))
    | Char (Nibble1, NibbleB) -> nat_of_num (Bit1 (Bit1 (Bit0 (Bit1 One))))
    | Char (Nibble1, NibbleA) -> nat_of_num (Bit0 (Bit1 (Bit0 (Bit1 One))))
    | Char (Nibble1, Nibble9) -> nat_of_num (Bit1 (Bit0 (Bit0 (Bit1 One))))
    | Char (Nibble1, Nibble8) -> nat_of_num (Bit0 (Bit0 (Bit0 (Bit1 One))))
    | Char (Nibble1, Nibble7) -> nat_of_num (Bit1 (Bit1 (Bit1 (Bit0 One))))
    | Char (Nibble1, Nibble6) -> nat_of_num (Bit0 (Bit1 (Bit1 (Bit0 One))))
    | Char (Nibble1, Nibble5) -> nat_of_num (Bit1 (Bit0 (Bit1 (Bit0 One))))
    | Char (Nibble1, Nibble4) -> nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 One))))
    | Char (Nibble1, Nibble3) -> nat_of_num (Bit1 (Bit1 (Bit0 (Bit0 One))))
    | Char (Nibble1, Nibble2) -> nat_of_num (Bit0 (Bit1 (Bit0 (Bit0 One))))
    | Char (Nibble1, Nibble1) -> nat_of_num (Bit1 (Bit0 (Bit0 (Bit0 One))))
    | Char (Nibble1, Nibble0) -> nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One))))
    | Char (Nibble0, NibbleF) -> nat_of_num (Bit1 (Bit1 (Bit1 One)))
    | Char (Nibble0, NibbleE) -> nat_of_num (Bit0 (Bit1 (Bit1 One)))
    | Char (Nibble0, NibbleD) -> nat_of_num (Bit1 (Bit0 (Bit1 One)))
    | Char (Nibble0, NibbleC) -> nat_of_num (Bit0 (Bit0 (Bit1 One)))
    | Char (Nibble0, NibbleB) -> nat_of_num (Bit1 (Bit1 (Bit0 One)))
    | Char (Nibble0, NibbleA) -> nat_of_num (Bit0 (Bit1 (Bit0 One)))
    | Char (Nibble0, Nibble9) -> nat_of_num (Bit1 (Bit0 (Bit0 One)))
    | Char (Nibble0, Nibble8) -> nat_of_num (Bit0 (Bit0 (Bit0 One)))
    | Char (Nibble0, Nibble7) -> nat_of_num (Bit1 (Bit1 One))
    | Char (Nibble0, Nibble6) -> nat_of_num (Bit0 (Bit1 One))
    | Char (Nibble0, Nibble5) -> nat_of_num (Bit1 (Bit0 One))
    | Char (Nibble0, Nibble4) -> nat_of_num (Bit0 (Bit0 One))
    | Char (Nibble0, Nibble3) -> nat_of_num (Bit1 One)
    | Char (Nibble0, Nibble2) -> nat_of_num (Bit0 One)
    | Char (Nibble0, Nibble1) -> one_nata
    | Char (Nibble0, Nibble0) -> Zero_nat;;

let rec case_char
  f c = (let n = nat_of_char c in
          f (nibble_of_nat
              (divide_nat n (nat_of_num (Bit0 (Bit0 (Bit0 (Bit0 One)))))))
            (nibble_of_nat n));;

let rec getAnywhereRules
  = function [] -> []
    | AnywherePat (s, pl, right, con) :: l ->
        (s, (pl, (right, con))) :: getAnywhereRules l
    | FunPat (v, va, vb) :: l -> getAnywhereRules l
    | MacroPat (v, va, vb) :: l -> getAnywhereRules l
    | KRulePat (v, va, vb, vc) :: l -> getAnywhereRules l
    | BagRulePat (v, va, vb, vc) :: l -> getAnywhereRules l;;

let rec getAllBagRules
  = function [] -> []
    | BagRulePat (a, b, c, d) :: l -> (a, (b, (c, d))) :: getAllBagRules l
    | FunPat (v, va, vb) :: l -> getAllBagRules l
    | MacroPat (v, va, vb) :: l -> getAllBagRules l
    | AnywherePat (v, va, vb, vc) :: l -> getAllBagRules l
    | KRulePat (v, va, vb, vc) :: l -> getAllBagRules l;;

let rec getAllKRules
  = function [] -> []
    | KRulePat (a, b, c, d) :: l -> (a, (b, (c, d))) :: getAllKRules l
    | FunPat (v, va, vb) :: l -> getAllKRules l
    | MacroPat (v, va, vb) :: l -> getAllKRules l
    | AnywherePat (v, va, vb, vc) :: l -> getAllKRules l
    | BagRulePat (v, va, vb, vc) :: l -> getAllKRules l;;

let rec getFunRules
  = function [] -> []
    | FunPat (s, fl, f) :: l -> FunPat (s, fl, f) :: getFunRules l
    | MacroPat (v, va, vb) :: l -> getFunRules l
    | AnywherePat (v, va, vb, vc) :: l -> getFunRules l
    | KRulePat (v, va, vb, vc) :: l -> getFunRules l
    | BagRulePat (v, va, vb, vc) :: l -> getFunRules l;;

let rec hasOutOfPositionStrict
  x0 l = match x0, l with [], l -> false
    | n :: la, l ->
        (if less_nat (size_list l) n then true
          else hasOutOfPositionStrict la l);;

let rec getArgSortsInSyntax
  = function Single (NonTerminal a) -> [[a]]
    | Single (Terminal a) -> []
    | Con (NonTerminal a, l) -> [a] :: getArgSortsInSyntax l
    | Con (Terminal a, l) -> getArgSortsInSyntax l;;

let rec getRidStrictAttrs
  = function [] -> []
    | b :: l ->
        (match b with Strict _ -> getRidStrictAttrs l
          | Seqstrict -> getRidStrictAttrs l | Left -> b :: getRidStrictAttrs l
          | Right -> b :: getRidStrictAttrs l
          | Hook _ -> b :: getRidStrictAttrs l
          | Function -> b :: getRidStrictAttrs l
          | Klabel _ -> b :: getRidStrictAttrs l
          | Bracket -> b :: getRidStrictAttrs l
          | Tokena -> b :: getRidStrictAttrs l
          | Avoid -> b :: getRidStrictAttrs l
          | OnlyLabel -> b :: getRidStrictAttrs l
          | NotInRules -> b :: getRidStrictAttrs l
          | Regex _ -> b :: getRidStrictAttrs l
          | NonAssoc -> b :: getRidStrictAttrs l
          | OtherSynAttr _ -> b :: getRidStrictAttrs l);;

let rec symbolsToKLabelAux
  = function Single (Terminal s) -> s
    | Single (NonTerminal v) -> [Char (Nibble5, NibbleF)]
    | Con (NonTerminal v, l) -> [Char (Nibble5, NibbleF)] @ symbolsToKLabelAux l
    | Con (Terminal s, l) -> s @ symbolsToKLabelAux l;;

let rec symbolsToKLabel
  a = OtherLabel ([Char (Nibble2, NibbleF)] @ symbolsToKLabelAux a);;

let rec getStrictInAttributes
  = function [] -> None
    | b :: l ->
        (match b with Strict a -> Some a | Seqstrict -> getStrictInAttributes l
          | Left -> getStrictInAttributes l | Right -> getStrictInAttributes l
          | Hook _ -> getStrictInAttributes l
          | Function -> getStrictInAttributes l
          | Klabel _ -> getStrictInAttributes l
          | Bracket -> getStrictInAttributes l
          | Tokena -> getStrictInAttributes l | Avoid -> getStrictInAttributes l
          | OnlyLabel -> getStrictInAttributes l
          | NotInRules -> getStrictInAttributes l
          | Regex _ -> getStrictInAttributes l
          | NonAssoc -> getStrictInAttributes l
          | OtherSynAttr _ -> getStrictInAttributes l);;

let rec generatingStrict
  x0 n = match x0, n with [], n -> []
    | b :: l, n -> n :: generatingStrict l (plus_nata n one_nata);;

let rec getStrictList
  sl tyl =
    (match getStrictInAttributes sl with None -> []
      | Some nl -> (if null nl then generatingStrict tyl one_nata else nl));;

let rec getKLabelName = function [] -> None
                        | Klabel a :: l -> Some (OtherLabel a)
                        | Strict v :: l -> getKLabelName l
                        | Seqstrict :: l -> getKLabelName l
                        | Left :: l -> getKLabelName l
                        | Right :: l -> getKLabelName l
                        | Hook v :: l -> getKLabelName l
                        | Function :: l -> getKLabelName l
                        | Bracket :: l -> getKLabelName l
                        | Tokena :: l -> getKLabelName l
                        | Avoid :: l -> getKLabelName l
                        | OnlyLabel :: l -> getKLabelName l
                        | NotInRules :: l -> getKLabelName l
                        | Regex v :: l -> getKLabelName l
                        | NonAssoc :: l -> getKLabelName l
                        | OtherSynAttr v :: l -> getKLabelName l;;

let rec isBracket = function [] -> false
                    | Bracket :: l -> true
                    | Strict v :: l -> isBracket l
                    | Seqstrict :: l -> isBracket l
                    | Left :: l -> isBracket l
                    | Right :: l -> isBracket l
                    | Hook v :: l -> isBracket l
                    | Function :: l -> isBracket l
                    | Klabel v :: l -> isBracket l
                    | Tokena :: l -> isBracket l
                    | Avoid :: l -> isBracket l
                    | OnlyLabel :: l -> isBracket l
                    | NotInRules :: l -> isBracket l
                    | Regex v :: l -> isBracket l
                    | NonAssoc :: l -> isBracket l
                    | OtherSynAttr v :: l -> isBracket l;;

let rec regMatch
  a s = (match a with Eps -> null s | Sym x -> equal_lista equal_char s [x]
          | Alt (x, y) -> regMatch x s || regMatch y s
          | TheSeq (x, y) -> regSplit x y [] s
          | Rep x -> (match s with [] -> true | b :: aa -> regPart x [b] aa))
and regPart
  x a xa2 = match x, a, xa2 with x, a, [] -> regMatch x a
    | x, a, s :: l ->
        (if regMatch x a then regMatch (Rep x) (s :: l)
          else regPart x (a @ [s]) l)
and regSplit
  x y s xa3 = match x, y, s, xa3 with x, y, s, [] -> false
    | x, y, s, a :: al ->
        (if regMatch x s then regMatch y (a :: al)
          else regSplit x y (s @ [a]) al);;

let rec syntaxToKItem
  = function
    Syntax (a, b, c) ->
      (if isBracket c then None
        else (match getKLabelName c
               with None ->
                 (if membera equal_synAttrib c Function
                   then Some [([a], (getArgSortsInSyntax b,
                                      (SingleTon (symbolsToKLabel b),
(getRidStrictAttrs c, true))))]
                   else (if hasOutOfPositionStrict
                              (getStrictList c (getArgSortsInSyntax b))
                              (getArgSortsInSyntax b)
                          then None
                          else Some [([a], (getArgSortsInSyntax b,
     (SingleTon (symbolsToKLabel b), (c, false))))]))
               | Some t ->
                 (if membera equal_synAttrib c Function
                   then Some [([a], (getArgSortsInSyntax b,
                                      (SingleTon t,
(getRidStrictAttrs c, true))))]
                   else (if hasOutOfPositionStrict
                              (getStrictList c (getArgSortsInSyntax b))
                              (getArgSortsInSyntax b)
                          then None
                          else Some [([a], (getArgSortsInSyntax b,
     (SingleTon t, (c, false))))]))))
    | Token (a, s, c) ->
        Some [([a], ([], (SetTon
                            (fun aa ->
                              (match aa with UnitLabel _ -> false
                                | ConstToLabel _ -> false | Sort -> false
                                | GetKLabel -> false | IsKResult -> false
                                | AndBool -> false | NotBool -> false
                                | OtherLabel _ -> false
                                | TokenLabel ab -> regMatch s ab)),
                           (getRidStrictAttrs c,
                             membera equal_synAttrib c Function))))]
    | Subsort (a, b) -> None
    | ListSyntax (a, b, s, c) ->
        (match getKLabelName c
          with None ->
            (if hasOutOfPositionStrict (getStrictList c [[b]; [a]]) [[b]; [a]]
              then None
              else Some [([a], ([[b]; [a]],
                                 (SingleTon
                                    (symbolsToKLabel
                                      (Con
(NonTerminal b, Con (Terminal s, Single (NonTerminal a))))),
                                   (c, false))));
                          ([a], ([], (SingleTon (UnitLabel a),
                                       (getRidStrictAttrs c, false))))])
          | Some t ->
            (if hasOutOfPositionStrict (getStrictList c [[b]; [a]]) [[b]; [a]]
              then None
              else Some [([a], ([[b]; [a]], (SingleTon t, (c, false))));
                          ([a], ([], (SingleTon (UnitLabel a),
                                       (getRidStrictAttrs c, false))))]));;

let rec syntaxSetToKItemSetAux
  x0 order = match x0, order with [], order -> Some []
    | a :: l, order ->
        (match syntaxToKItem a with None -> None
          | Some la ->
            (match syntaxSetToKItemSetAux l (order @ [a]) with None -> None
              | Some laa -> Some (la @ laa)));;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec getAllSyntaxInKModuleItemList _A
  = function [] -> []
    | TheSyntax x :: l ->
        inserta (equal_kSyntax _A) x (getAllSyntaxInKModuleItemList _A l)
    | Imports x :: l -> getAllSyntaxInKModuleItemList _A l
    | TheConfiguration x :: l -> getAllSyntaxInKModuleItemList _A l
    | TheRule x :: l -> getAllSyntaxInKModuleItemList _A l;;

let rec insertAll _A a x1 = match a, x1 with a, [] -> a
                       | a, b :: l -> insertAll _A (inserta _A b a) l;;

let rec getAllSyntaxInKFile _A
  = function TheFile (Single (TheRequires m)) -> []
    | TheFile (Single (TheModule (Module (a, m)))) ->
        getAllSyntaxInKModuleItemList _A m
    | TheFile (Con (TheRequires m, xs)) -> getAllSyntaxInKFile _A (TheFile xs)
    | TheFile (Con (TheModule (Module (a, m)), xs)) ->
        insertAll (equal_kSyntax _A) (getAllSyntaxInKModuleItemList _A m)
          (getAllSyntaxInKFile _A (TheFile xs));;

let rec syntaxSetToKItemTest _A
  theory = syntaxSetToKItemSetAux (getAllSyntaxInKFile _A theory) [];;

let rec genKListByTypeListFactor _A
  ty newVar subG =
    (if subsortList (equal_sort _A) ty [List] subG
      then ItemKl (SUBigBag (SUList [IdL newVar]))
      else (if subsortList (equal_sort _A) ty [Seta] subG
             then ItemKl (SUBigBag (SUSet [IdS newVar]))
             else (if subsortList (equal_sort _A) ty [Map] subG
                    then ItemKl (SUBigBag (SUMap [IdM newVar]))
                    else (if subsortList (equal_sort _A) ty [Bag] subG
                           then ItemKl (SUBigLabel (SUIdKLabel newVar))
                           else (if subsortList (equal_sort _A) ty [KLabel] subG
                                  then ItemKl (SUBigBag (SUBag [IdB newVar]))
                                  else (if equal_lista (equal_sort _A) ty [K]
 then ItemKl (SUBigBag (SUK [IdFactor newVar]))
 else ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (newVar, ty))]))))))));;

let rec genKListByTypeList _A
  x0 vars subG = match x0, vars, subG with [], vars, subG -> []
    | ty :: l, vars, subG ->
        genKListByTypeListFactor _A ty (freshVar vars) subG ::
          genKListByTypeList _A l (freshVar vars :: vars) subG;;

let rec genKListByTypeListInSeq (_A1, _A2, _A3) _B
  c n x2 vars subG = match c, n, x2, vars, subG with c, n, [], vars, subG -> []
    | c, n, ty :: l, vars, subG ->
        (if less _A3 c n && subsortList (equal_sort _B) ty [K] subG
          then ItemKl
                 (SUBigBag
                   (SUK [ItemFactor (SUIdKItem (freshVar vars, [KResult]))])) ::
                 genKListByTypeListInSeq (_A1, _A2, _A3) _B
                   (plus _A2 c (one _A1)) n l (freshVar vars :: vars) subG
          else genKListByTypeListFactor _B ty (freshVar vars) subG ::
                 genKListByTypeListInSeq (_A1, _A2, _A3) _B
                   (plus _A2 c (one _A1)) n l (freshVar vars :: vars) subG);;

let rec splitHoleFromKList
  c n x2 = match c, n, x2 with c, n, [] -> None
    | c, n, b :: l ->
        (if equal_nata c n
          then (match b with ItemKl (SUBigBag (SUK [])) -> None
                 | ItemKl (SUBigBag (SUK (ItemFactor (SUKItem (_, _, _)) :: _)))
                   -> None
                 | ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (u, ty))])) ->
                   Some (ItemFactor (SUIdKItem (u, ty)),
                          ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE ty)])) :: l)
                 | ItemKl
                     (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _ :: _)))
                   -> None
                 | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) -> None
                 | ItemKl (SUBigBag (SUK [IdFactor u])) ->
                   Some (IdFactor u,
                          ItemKl (SUBigBag (SUK [ItemFactor (SUHOLE [K])])) ::
                            l)
                 | ItemKl (SUBigBag (SUK (IdFactor _ :: _ :: _))) -> None
                 | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) -> None
                 | ItemKl (SUBigBag (SUList _)) -> None
                 | ItemKl (SUBigBag (SUSet _)) -> None
                 | ItemKl (SUBigBag (SUMap _)) -> None
                 | ItemKl (SUBigBag (SUBag _)) -> None
                 | ItemKl (SUBigLabel _) -> None | IdKl _ -> None)
          else (match splitHoleFromKList (plus_nata c one_nata) n l
                 with None -> None | Some (u, v) -> Some (u, b :: v)));;

let rec getMetaVar
  = function IdFactor x -> Some x
    | ItemFactor x ->
        (match x with SUKItem (_, _, _) -> None | SUIdKItem (a, _) -> Some a
          | SUHOLE _ -> None)
    | SUKKItem (v, va, vb) -> None;;

let rec genStrictRulesSeq _A
  s sty tyl n x4 database subG = match s, sty, tyl, n, x4, database, subG with
    s, sty, tyl, n, [], database, subG -> Some []
    | s, sty, tyl, n, b :: l, database, subG ->
        (if subsortList (equal_sort _A) b [K] subG
          then genStrictRulesSeq _A s sty tyl (plus_nata n one_nata) l database
                 subG
          else (match
                 splitHoleFromKList one_nata n
                   (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A
                     one_nata n tyl [] subG)
                 with None -> None
                 | Some (front, kl) ->
                   (match
                     genStrictRulesSeq _A s sty tyl (plus_nata n one_nata) l
                       database subG
                     with None -> None
                     | Some rl ->
                       (match
                         suToIRInKList _A
                           (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat)
                             _A one_nata n tyl [] subG)
                           database
                         with None -> None
                         | Some left ->
                           (match suToIRInKList _A kl database with None -> None
                             | Some lefta ->
                               (match getMetaVar front with None -> None
                                 | Some frontVar ->
                                   Some (KRulePat
   (KPat ([IRKItem (IRKLabel s, left, sty)],
           Some (freshVar
                  (getAllMetaVarsInSUKList
                    (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A
                      one_nata n tyl [] subG)))),
     [front; ItemFactor (SUKItem (SUKLabel s, kl, sty));
       IdFactor
         (freshVar
           (getAllMetaVarsInSUKList
             (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A one_nata n
               tyl [] subG)))],
     SUKItem
       (SUKLabel NotBool,
         [ItemKl
            (SUBigBag
              (SUK [ItemFactor
                      (SUKItem
                        (SUKLabel IsKResult, [ItemKl (SUBigBag (SUK [front]))],
                          [Bool]))]))],
         [Bool]),
     false) ::
  KRulePat
    (KPat ([IRIdKItem (frontVar, [KResult]); IRKItem (IRKLabel s, lefta, sty)],
            Some (freshVar
                   (getAllMetaVarsInSUKList
                     (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A
                       one_nata n tyl [] subG)))),
      [ItemFactor
         (SUKItem
           (SUKLabel s,
             genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A one_nata n
               tyl [] subG,
             sty));
        IdFactor
          (freshVar
            (getAllMetaVarsInSUKList
              (genKListByTypeListInSeq (one_nat, plus_nat, ord_nat) _A one_nata
                n tyl [] subG)))],
      SUKItem (SUKLabel (ConstToLabel (BoolConst true)), [], [Bool]), false) ::
    rl)))))));;

let rec getTypeFromKList
  c n x2 = match c, n, x2 with c, n, [] -> None
    | c, n, b :: l ->
        (if equal_nata c n
          then (match b with ItemKl (SUBigBag (SUK [])) -> None
                 | ItemKl (SUBigBag (SUK (ItemFactor (SUKItem (_, _, _)) :: _)))
                   -> None
                 | ItemKl (SUBigBag (SUK [ItemFactor (SUIdKItem (_, ty))])) ->
                   Some ty
                 | ItemKl
                     (SUBigBag (SUK (ItemFactor (SUIdKItem (_, _)) :: _ :: _)))
                   -> None
                 | ItemKl (SUBigBag (SUK (ItemFactor (SUHOLE _) :: _))) -> None
                 | ItemKl (SUBigBag (SUK [IdFactor _])) -> Some [K]
                 | ItemKl (SUBigBag (SUK (IdFactor _ :: _ :: _))) -> None
                 | ItemKl (SUBigBag (SUK (SUKKItem (_, _, _) :: _))) -> None
                 | ItemKl (SUBigBag (SUList _)) -> Some [List]
                 | ItemKl (SUBigBag (SUSet _)) -> Some [Seta]
                 | ItemKl (SUBigBag (SUMap _)) -> Some [Map]
                 | ItemKl (SUBigBag (SUBag _)) -> Some [Bag]
                 | ItemKl (SUBigLabel _) -> Some [KLabel] | IdKl _ -> None)
          else getTypeFromKList c n l);;

let rec genStrictRulesAux _A
  s sty x2 newKList database subG = match s, sty, x2, newKList, database, subG
    with s, sty, [], newKList, database, subG -> Some []
    | s, sty, n :: l, newKList, database, subG ->
        (match getTypeFromKList one_nata n newKList with None -> None
          | Some newTy ->
            (if subsortList (equal_sort _A) newTy [K] subG
              then (match splitHoleFromKList one_nata n newKList
                     with None -> None
                     | Some (front, kl) ->
                       (match
                         genStrictRulesAux _A s sty l newKList database subG
                         with None -> None
                         | Some rl ->
                           (match suToIRInKList _A newKList database
                             with None -> None
                             | Some left ->
                               (match suToIRInKList _A kl database
                                 with None -> None
                                 | Some lefta ->
                                   (match getMetaVar front with None -> None
                                     | Some frontVar ->
                                       Some (KRulePat
       (KPat ([IRKItem (IRKLabel s, left, sty)],
               Some (freshVar (getAllMetaVarsInSUKList newKList))),
         [front; ItemFactor (SUKItem (SUKLabel s, kl, sty));
           IdFactor (freshVar (getAllMetaVarsInSUKList newKList))],
         SUKItem
           (SUKLabel NotBool,
             [ItemKl
                (SUBigBag
                  (SUK [ItemFactor
                          (SUKItem
                            (SUKLabel IsKResult,
                              [ItemKl (SUBigBag (SUK [front]))], [Bool]))]))],
             [Bool]),
         false) ::
      KRulePat
        (KPat ([IRIdKItem (frontVar, [KResult]);
                 IRKItem (IRKLabel s, lefta, sty)],
                Some (freshVar (getAllMetaVarsInSUKList newKList))),
          [ItemFactor (SUKItem (SUKLabel s, newKList, sty));
            IdFactor (freshVar (getAllMetaVarsInSUKList newKList))],
          SUKItem (SUKLabel (ConstToLabel (BoolConst true)), [], [Bool]),
          false) ::
        rl))))))
              else genStrictRulesAux _A s sty l newKList database subG));;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec genStrictRules _B
  s x1 database subG = match s, x1, database, subG with
    s, [], database, subG -> Some []
    | s, b :: l, database, subG ->
        (let (ty, (tyl, (SingleTon sa, (stl, true)))) = b in
          (if membera equal_synAttrib stl Seqstrict
            then (if is_none (getStrictInAttributes stl)
                   then (match
                          genStrictRulesSeq _B sa ty tyl one_nata tyl database
                            subG
                          with None -> None
                          | Some rl ->
                            (match genStrictRules _B s l database subG
                              with None -> None | Some rla -> Some (rl @ rla)))
                   else None)
            else (match getStrictList stl tyl
                   with [] -> genStrictRules _B s l database subG
                   | n :: nl ->
                     (match
                       genStrictRulesAux _B sa ty (n :: nl)
                         (genKListByTypeList _B tyl [] subG) database subG
                       with None -> None
                       | Some rl ->
                         (match genStrictRules _B s l database subG
                           with None -> None
                           | Some rla -> Some (rl @ rla))))));;

let rec strictRuleTest _B
  vars theory subG =
    (match syntaxSetToKItemTest _B theory with None -> None
      | Some database ->
        (match genStrictRules _B vars database database subG with None -> None
          | Some a -> Some a));;

let bot_set : 'a set = Set [];;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec validArgSyntaxAux _A
  = function [] -> true
    | a :: l ->
        (if member (equal_list (equal_sort _A)) a
              (insert (equal_list (equal_sort _A)) [Top]
                (insert (equal_list (equal_sort _A)) [KList]
                  (insert (equal_list (equal_sort _A)) [KResult] bot_set)))
          then false else validArgSyntaxAux _A l);;

let rec validArgSynax _B
  = function [] -> true
    | (a, (b, c)) :: l -> validArgSyntaxAux _B b && validArgSynax _B l;;

let rec validSyntaxs _A
  = function [] -> true
    | (a, (b, (c, (nl, true)))) :: l ->
        not (member (equal_list (equal_sort _A)) a
              (insert (equal_list (equal_sort _A)) [Top]
                (insert (equal_list (equal_sort _A)) [KList]
                  (insert (equal_list (equal_sort _A)) [Bag] bot_set)))) &&
          validSyntaxs _A l
    | (a, (b, (c, (nl, false)))) :: l ->
        not (member (equal_list (equal_sort _A)) a
              (insert (equal_list (equal_sort _A)) [Top]
                (insert (equal_list (equal_sort _A)) [KList]
                  (insert (equal_list (equal_sort _A)) [Bag]
                    (insert (equal_list (equal_sort _A)) [List]
                      (insert (equal_list (equal_sort _A)) [Seta]
                        (insert (equal_list (equal_sort _A)) [Map]
                          (insert (equal_list (equal_sort _A)) [KLabel]
                            (insert (equal_list (equal_sort _A)) [K]
                              bot_set))))))))) &&
          validSyntaxs _A l;;

let rec validSyntaxSort _B
  metaVars theory database subG =
    validSyntaxs _B database &&
      (validArgSynax _B database &&
        (not (is_none (syntaxSetToKItemTest _B theory)) &&
          not (is_none (strictRuleTest _B metaVars theory subG))));;

let rec hasInvalidTranstiveClosureInList _A
  g a x2 acc = match g, a, x2, acc with g, a, [], acc -> true
    | g, a, x :: l, acc ->
        (if membera _A acc x then false
          else hasInvalidTranstiveClosureAux _A g g x acc &&
                 hasInvalidTranstiveClosureInList _A g a l acc)
and hasInvalidTranstiveClosureAux _A
  g xa1 x acc = match g, xa1, x, acc with g, [], x, acc -> true
    | g, en :: l, x, acc ->
        (let (a, b) = en in
          (if eq _A a x
            then hasInvalidTranstiveClosureInList _A g x b (x :: acc)
            else hasInvalidTranstiveClosureAux _A g l x acc));;

let rec hasInvalidTranstiveClosure _A
  g x1 = match g, x1 with g, [] -> true
    | g, (x, y) :: l ->
        hasInvalidTranstiveClosureInList _A g x y [x] &&
          hasInvalidTranstiveClosure _A g l;;

let rec getAllSubsortInKModuleItemList _A
  = function [] -> []
    | TheSyntax (Subsort (a, b)) :: l ->
        inserta (equal_prod (equal_sort _A) (equal_sort _A)) (a, b)
          (getAllSubsortInKModuleItemList _A l)
    | TheSyntax (Syntax (v, va, vb)) :: l -> getAllSubsortInKModuleItemList _A l
    | TheSyntax (Token (v, va, vb)) :: l -> getAllSubsortInKModuleItemList _A l
    | TheSyntax (ListSyntax (v, va, vb, vc)) :: l ->
        getAllSubsortInKModuleItemList _A l
    | Imports x :: l -> getAllSubsortInKModuleItemList _A l
    | TheConfiguration x :: l -> getAllSubsortInKModuleItemList _A l
    | TheRule x :: l -> getAllSubsortInKModuleItemList _A l;;

let rec getAllSubsortInKFile _A
  = function TheFile (Single (TheRequires m)) -> []
    | TheFile (Single (TheModule (Module (a, m)))) ->
        getAllSubsortInKModuleItemList _A m
    | TheFile (Con (TheRequires m, xs)) -> getAllSubsortInKFile _A (TheFile xs)
    | TheFile (Con (TheModule (Module (a, m)), xs)) ->
        insertAll (equal_prod (equal_sort _A) (equal_sort _A))
          (getAllSubsortInKModuleItemList _A m)
          (getAllSubsortInKFile _A (TheFile xs));;

let rec inValidBuiltinSubsortOne _A
  a b = equal_sorta _A a KResult || equal_sorta _A a KItem;;

let rec inValidBuiltinSubsort _A _B
  a b = member (equal_sort _A) a
          (insert (equal_sort _A) K
            (insert (equal_sort _A) KList
              (insert (equal_sort _A) List
                (insert (equal_sort _A) Seta
                  (insert (equal_sort _A) Bag
                    (insert (equal_sort _A) Map
                      (insert (equal_sort _A) KLabel bot_set))))))) ||
          member (equal_sort _B) b
            (insert (equal_sort _B) K
              (insert (equal_sort _B) KList
                (insert (equal_sort _B) List
                  (insert (equal_sort _B) Seta
                    (insert (equal_sort _B) Bag
                      (insert (equal_sort _B) Map
                        (insert (equal_sort _B) KLabel bot_set)))))));;

let rec inValidFactorOne _A a b = eq _A a b;;

let rec invalidSubsortFactor _A
  a b = inValidBuiltinSubsort _A _A a b ||
          (inValidBuiltinSubsortOne _A a b ||
            inValidFactorOne (equal_sort _A) a b);;

let rec hasInvalidSubsort _A
  = function [] -> false
    | a :: l ->
        (let (x, y) = a in
          (if invalidSubsortFactor _A x y then true
            else hasInvalidSubsort _A l));;

let builtinSorts : 'a sort list
  = [KItem; K; KList; List; Seta; Bag; Map; KResult; KLabel];;

let rec getAllSorts _A
  = function [] -> []
    | Syntax (x, pros, l) :: xs -> inserta (equal_sort _A) x (getAllSorts _A xs)
    | ListSyntax (a, b, pros, l) :: xs ->
        inserta (equal_sort _A) a (getAllSorts _A xs)
    | Token (a, s, l) :: xs -> inserta (equal_sort _A) a (getAllSorts _A xs)
    | Subsort (v, va) :: xs -> getAllSorts _A xs;;

let rec addImplicitSubsorts _A
  x s xa2 = match x, s, xa2 with x, s, [] -> []
    | x, s, a :: l ->
        (if membera _A s a then addImplicitSubsorts _A x s l
          else (x, a) :: addImplicitSubsorts _A x s l);;

let rec getKResultSubsorts _A
  x0 subG = match x0, subG with [], subG -> []
    | a :: l, subG ->
        (if membera (equal_sort _A) builtinSorts a
          then getKResultSubsorts _A l subG
          else (if subsortAux (equal_sort _A) KResult a subG
                 then getKResultSubsorts _A l subG
                 else (KResult, a) :: getKResultSubsorts _A l subG));;

let topSubsort : ('a sort * 'b sort) list
  = [(K, Top); (KList, Top); (List, Top); (Seta, Top); (Bag, Top); (Map, Top);
      (KLabel, Top)];;

let rec preAllSubsorts _A
  theory =
    getAllSubsortInKFile _A theory @
      addImplicitSubsorts (equal_sort _A) KItem builtinSorts
        (getAllSorts _A (getAllSyntaxInKFile _A theory)) @
        [(KResult, KItem); (KItem, K)] @ topSubsort;;

let rec getAllSubsortOnItem _A
  x0 a = match x0, a with [], a -> []
    | (x, y) :: l, a ->
        (if eq _A y a then x :: getAllSubsortOnItem _A l a
          else getAllSubsortOnItem _A l a);;

let rec formGraph _A
  x0 s = match x0, s with [], s -> []
    | a :: l, s -> (a, getAllSubsortOnItem _A s a) :: formGraph _A l s;;

let rec preSubsortGraph _A
  theory =
    formGraph (equal_sort _A)
      (insertAll (equal_sort _A)
        (getAllSorts _A (getAllSyntaxInKFile _A theory)) builtinSorts)
      (preAllSubsorts _A theory);;

let rec kResultSubsorts _A
  theory =
    getKResultSubsorts _A (getAllSorts _A (getAllSyntaxInKFile _A theory))
      (preSubsortGraph _A theory);;

let rec allSubsorts _A
  theory =
    getAllSubsortInKFile _A theory @
      addImplicitSubsorts (equal_sort _A) KItem builtinSorts
        (getAllSorts _A (getAllSyntaxInKFile _A theory)) @
        [(KResult, KItem); (KItem, K)] @
          topSubsort @ kResultSubsorts _A theory;;

let rec subsortGraph _A
  theory =
    formGraph (equal_sort _A)
      (insertAll (equal_sort _A)
        (getAllSorts _A (getAllSyntaxInKFile _A theory)) builtinSorts)
      (allSubsorts _A theory);;

let rec invalidSortChecks _A
  theory =
    not (hasInvalidSubsort _A (getAllSubsortInKFile _A theory)) &&
      not (hasInvalidTranstiveClosure (equal_sort _A) (subsortGraph _A theory)
            (subsortGraph _A theory));;

let rec syntaxSetToKItemSet _A
  theory =
    (match syntaxSetToKItemTest _A theory with None -> [] | Some l -> l);;

let rec isUnitLabelInList _A
  s x1 = match s, x1 with s, [] -> true
    | SingleTon s, (a, (b, (SingleTon c, (nl, d)))) :: l ->
        (if eq _A s c then false else isUnitLabelInList _A (SingleTon s) l)
    | SingleTon s, (a, (b, (SetTon c, (nl, d)))) :: l ->
        (if c s then false else isUnitLabelInList _A (SingleTon s) l)
    | SetTon s, (a, (b, (SingleTon c, (nl, d)))) :: l ->
        (if s c then false else isUnitLabelInList _A (SetTon s) l)
    | SetTon s, (a, (b, (SetTon c, (nl, d)))) :: l ->
        isUnitLabelInList _A (SetTon s) l;;

let rec isUnitLabel _C
  = function [] -> true
    | a :: l ->
        (let (_, (_, (w, (_, _)))) = a in
          isUnitLabelInList _C w l && isUnitLabel _C l);;

let rec uniqueKLabelSyntax _A
  theory = isUnitLabel (equal_label _A) (syntaxSetToKItemSet _A theory);;

let rec getDomainInSUBag
  = function [] -> []
    | x :: l ->
        (match x
          with ItemB (_, _, z) ->
            getDomainInSUBigKWithBag z @ getDomainInSUBag l
          | IdB _ -> getDomainInSUBag l)
and getDomainInSUBigKWithBag = function SUK a -> getDomainInSUK a
                               | SUList a -> getDomainInSUList a
                               | SUSet a -> getDomainInSUSet a
                               | SUMap a -> getDomainInSUMap a
                               | SUBag a -> getDomainInSUBag a
and getDomainInSUBigKWithLabel
  = function SUBigBag a -> getDomainInSUBigKWithBag a
    | SUBigLabel a -> []
and getDomainInSUKList
  = function [] -> []
    | x :: l ->
        (match x
          with ItemKl xa -> getDomainInSUBigKWithLabel xa @ getDomainInSUKList l
          | IdKl _ -> getDomainInSUKList l)
and getDomainInSUKItem
  = function
    SUKItem (a, b, ty) ->
      (match a with SUKLabel _ -> getDomainInSUKList b
        | SUIdKLabel x -> x :: getDomainInSUKList b
        | SUKLabelFun (_, _) -> getDomainInSUKList b)
    | SUIdKItem (a, ty) -> []
    | SUHOLE ty -> []
and getDomainInSUK
  = function [] -> []
    | x :: l ->
        (match x with ItemFactor xa -> getDomainInSUKItem xa @ getDomainInSUK l
          | IdFactor _ -> getDomainInSUK l
          | SUKKItem (SUKLabel _, _, _) -> getDomainInSUK l
          | SUKKItem (SUIdKLabel xa, _, _) -> xa :: getDomainInSUK l
          | SUKKItem (SUKLabelFun (_, _), _, _) -> getDomainInSUK l)
and getDomainInSUMap
  = function [] -> []
    | x :: l ->
        (match x
          with ItemM (xa, y) ->
            getDomainInSUK xa @ getDomainInSUK y @ getDomainInSUMap l
          | IdM _ -> getDomainInSUMap l
          | SUMapKItem (SUKLabel _, _) -> getDomainInSUMap l
          | SUMapKItem (SUIdKLabel xa, _) -> xa :: getDomainInSUMap l
          | SUMapKItem (SUKLabelFun (_, _), _) -> getDomainInSUMap l)
and getDomainInSUSet
  = function [] -> []
    | x :: l ->
        (match x with ItemS xa -> getDomainInSUK xa @ getDomainInSUSet l
          | IdS _ -> getDomainInSUSet l
          | SUSetKItem (SUKLabel _, _) -> getDomainInSUSet l
          | SUSetKItem (SUIdKLabel xa, _) -> xa :: getDomainInSUSet l
          | SUSetKItem (SUKLabelFun (_, _), _) -> getDomainInSUSet l)
and getDomainInSUList
  = function [] -> []
    | x :: l ->
        (match x with ItemL xa -> getDomainInSUK xa @ getDomainInSUList l
          | IdL _ -> getDomainInSUList l
          | SUListKItem (SUKLabel _, _) -> getDomainInSUList l
          | SUListKItem (SUIdKLabel xa, _) -> xa :: getDomainInSUList l
          | SUListKItem (SUKLabelFun (_, _), _) -> getDomainInSUList l);;

let rec configurationTest _A _B _D
  theory database subG =
    (match getConfiguration theory with [] -> None
      | [a] ->
        (match toSUInBag a with None -> None
          | Some aa ->
            (if validConfiguration _B aa
              then (match
                     checkTermsInSUBag _A _D aa []
                       (constructSortMap (getDomainInSUBag aa)) database subG
                     with None -> None
                     | Some (acc, (beta, akl)) ->
                       (if hasNoTop _A acc && hasNoTop _A beta
                         then (match
                                replaceVarSortInSUBag _A _D akl acc beta subG
                                with None -> None
                                | Some kla ->
                                  regularizeInSUBag _A _B _D kla subG)
                         else None))
              else None))
      | _ :: _ :: _ -> None);;

let rec kcompile _A _B _D
  theory =
    (match syntaxSetToKItemTest _A theory
      with None ->
        Failure
          [Char (Nibble4, NibbleE); Char (Nibble6, NibbleF);
            Char (Nibble7, Nibble4); Char (Nibble2, Nibble0);
            Char (Nibble6, Nibble1); Char (Nibble2, Nibble0);
            Char (Nibble7, Nibble6); Char (Nibble6, Nibble1);
            Char (Nibble6, NibbleC); Char (Nibble6, Nibble9);
            Char (Nibble6, Nibble4); Char (Nibble2, Nibble0);
            Char (Nibble4, NibbleB); Char (Nibble2, Nibble0);
            Char (Nibble7, Nibble4); Char (Nibble6, Nibble8);
            Char (Nibble6, Nibble5); Char (Nibble6, NibbleF);
            Char (Nibble7, Nibble2); Char (Nibble7, Nibble9);
            Char (Nibble2, NibbleE)]
      | Some database ->
        (if invalidSortChecks _A theory
          then (if uniqueKLabelSyntax _A theory
                 then (if validSyntaxSort _A [] theory database
                            (subsortGraph _A theory)
                        then (match
                               configurationTest _A _B _D theory database
                                 (subsortGraph _A theory)
                               with None ->
                                 Failure
                                   [Char (Nibble5, Nibble4);
                                     Char (Nibble6, Nibble8);
                                     Char (Nibble6, Nibble5);
                                     Char (Nibble2, Nibble0);
                                     Char (Nibble6, Nibble3);
                                     Char (Nibble6, NibbleF);
                                     Char (Nibble6, NibbleE);
                                     Char (Nibble6, Nibble6);
                                     Char (Nibble6, Nibble9);
                                     Char (Nibble6, Nibble7);
                                     Char (Nibble7, Nibble5);
                                     Char (Nibble7, Nibble2);
                                     Char (Nibble6, Nibble1);
                                     Char (Nibble7, Nibble4);
                                     Char (Nibble6, Nibble9);
                                     Char (Nibble6, NibbleF);
                                     Char (Nibble6, NibbleE);
                                     Char (Nibble2, Nibble0);
                                     Char (Nibble6, Nibble9);
                                     Char (Nibble7, Nibble3);
                                     Char (Nibble2, Nibble0);
                                     Char (Nibble6, NibbleE);
                                     Char (Nibble6, NibbleF);
                                     Char (Nibble7, Nibble4);
                                     Char (Nibble2, Nibble0);
                                     Char (Nibble7, Nibble6);
                                     Char (Nibble6, Nibble1);
                                     Char (Nibble6, NibbleC);
                                     Char (Nibble6, Nibble9);
                                     Char (Nibble6, Nibble4);
                                     Char (Nibble2, NibbleE)]
                               | Some confi ->
                                 (match
                                   typeCheckRules _A _B _D theory database
                                     (subsortGraph _A theory)
                                   with None ->
                                     Failure
                                       [Char (Nibble5, Nibble4);
 Char (Nibble6, Nibble8); Char (Nibble6, Nibble5); Char (Nibble2, Nibble0);
 Char (Nibble7, Nibble4); Char (Nibble6, Nibble8); Char (Nibble6, Nibble5);
 Char (Nibble6, NibbleF); Char (Nibble7, Nibble2); Char (Nibble7, Nibble9);
 Char (Nibble2, Nibble0); Char (Nibble6, Nibble8); Char (Nibble6, Nibble1);
 Char (Nibble7, Nibble3); Char (Nibble2, Nibble0); Char (Nibble6, Nibble9);
 Char (Nibble6, NibbleE); Char (Nibble7, Nibble6); Char (Nibble6, Nibble1);
 Char (Nibble6, NibbleC); Char (Nibble6, Nibble9); Char (Nibble6, Nibble4);
 Char (Nibble2, Nibble0); Char (Nibble7, Nibble2); Char (Nibble7, Nibble5);
 Char (Nibble6, NibbleC); Char (Nibble6, Nibble5); Char (Nibble7, Nibble3);
 Char (Nibble2, NibbleE)]
                                   | Some allRules ->
                                     (match
                                       strictRuleTest _A [] theory
 (subsortGraph _A theory)
                                       with None ->
 Failure
   [Char (Nibble5, Nibble4); Char (Nibble6, Nibble8); Char (Nibble6, Nibble5);
     Char (Nibble2, Nibble0); Char (Nibble7, Nibble4); Char (Nibble6, Nibble8);
     Char (Nibble6, Nibble5); Char (Nibble6, NibbleF); Char (Nibble7, Nibble2);
     Char (Nibble7, Nibble9); Char (Nibble2, Nibble0); Char (Nibble6, Nibble8);
     Char (Nibble6, Nibble1); Char (Nibble7, Nibble3); Char (Nibble2, Nibble0);
     Char (Nibble6, Nibble9); Char (Nibble6, NibbleE); Char (Nibble7, Nibble6);
     Char (Nibble6, Nibble1); Char (Nibble6, NibbleC); Char (Nibble6, Nibble9);
     Char (Nibble6, Nibble4); Char (Nibble2, Nibble0); Char (Nibble7, Nibble3);
     Char (Nibble7, Nibble4); Char (Nibble7, Nibble2); Char (Nibble6, Nibble9);
     Char (Nibble6, Nibble3); Char (Nibble7, Nibble4); Char (Nibble2, Nibble0);
     Char (Nibble6, Nibble1); Char (Nibble7, Nibble4); Char (Nibble7, Nibble4);
     Char (Nibble7, Nibble2); Char (Nibble6, Nibble9); Char (Nibble6, Nibble2);
     Char (Nibble7, Nibble5); Char (Nibble7, Nibble4); Char (Nibble6, Nibble5);
     Char (Nibble7, Nibble3); Char (Nibble2, NibbleE)]
                                       | Some stl ->
 Success
   (theory, (database, (subsortGraph _A theory, (confi, allRules @ stl)))))))
                        else Failure
                               [Char (Nibble4, NibbleB);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble6, Nibble8);
                                 Char (Nibble6, Nibble5);
                                 Char (Nibble6, NibbleF);
                                 Char (Nibble7, Nibble2);
                                 Char (Nibble7, Nibble9);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble6, Nibble8);
                                 Char (Nibble6, Nibble1);
                                 Char (Nibble7, Nibble3);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble6, Nibble9);
                                 Char (Nibble6, NibbleE);
                                 Char (Nibble7, Nibble6);
                                 Char (Nibble6, Nibble1);
                                 Char (Nibble6, NibbleC);
                                 Char (Nibble6, Nibble9);
                                 Char (Nibble6, Nibble4);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble7, Nibble3);
                                 Char (Nibble7, Nibble9);
                                 Char (Nibble6, NibbleE);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble6, Nibble1);
                                 Char (Nibble7, Nibble8);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble6, NibbleF);
                                 Char (Nibble7, Nibble2);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble7, Nibble3);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble7, Nibble2);
                                 Char (Nibble6, Nibble9);
                                 Char (Nibble6, Nibble3);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble6, Nibble1);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble7, Nibble2);
                                 Char (Nibble6, Nibble9);
                                 Char (Nibble6, Nibble2);
                                 Char (Nibble7, Nibble5);
                                 Char (Nibble7, Nibble4);
                                 Char (Nibble6, Nibble5);
                                 Char (Nibble7, Nibble3);
                                 Char (Nibble2, Nibble0);
                                 Char (Nibble6, Nibble6);
                                 Char (Nibble6, Nibble1);
                                 Char (Nibble6, Nibble9);
                                 Char (Nibble6, NibbleC);
                                 Char (Nibble6, Nibble5);
                                 Char (Nibble6, Nibble4);
                                 Char (Nibble2, NibbleE)])
                 else Failure
                        [Char (Nibble6, NibbleB); Char (Nibble4, NibbleC);
                          Char (Nibble6, Nibble1); Char (Nibble6, Nibble2);
                          Char (Nibble6, Nibble5); Char (Nibble6, NibbleC);
                          Char (Nibble7, Nibble3); Char (Nibble2, Nibble0);
                          Char (Nibble6, Nibble1); Char (Nibble7, Nibble2);
                          Char (Nibble6, Nibble5); Char (Nibble2, Nibble0);
                          Char (Nibble6, NibbleE); Char (Nibble6, NibbleF);
                          Char (Nibble7, Nibble4); Char (Nibble2, Nibble0);
                          Char (Nibble7, Nibble5); Char (Nibble6, NibbleE);
                          Char (Nibble6, Nibble9); Char (Nibble7, Nibble1);
                          Char (Nibble7, Nibble5); Char (Nibble6, Nibble5);
                          Char (Nibble6, NibbleC); Char (Nibble7, Nibble9);
                          Char (Nibble2, Nibble0); Char (Nibble6, Nibble4);
                          Char (Nibble6, Nibble5); Char (Nibble6, Nibble6);
                          Char (Nibble6, Nibble9); Char (Nibble6, NibbleE);
                          Char (Nibble6, Nibble5); Char (Nibble6, Nibble4);
                          Char (Nibble2, Nibble0); Char (Nibble6, Nibble9);
                          Char (Nibble6, NibbleE); Char (Nibble2, Nibble0);
                          Char (Nibble7, Nibble4); Char (Nibble6, Nibble8);
                          Char (Nibble6, Nibble9); Char (Nibble7, Nibble3);
                          Char (Nibble2, Nibble0); Char (Nibble4, NibbleB);
                          Char (Nibble2, Nibble0); Char (Nibble7, Nibble4);
                          Char (Nibble6, Nibble8); Char (Nibble6, Nibble5);
                          Char (Nibble6, NibbleF); Char (Nibble7, Nibble2);
                          Char (Nibble7, Nibble9); Char (Nibble2, NibbleE)])
          else Failure
                 [Char (Nibble4, NibbleB); Char (Nibble2, Nibble0);
                   Char (Nibble7, Nibble4); Char (Nibble6, Nibble8);
                   Char (Nibble6, Nibble5); Char (Nibble6, NibbleF);
                   Char (Nibble7, Nibble2); Char (Nibble7, Nibble9);
                   Char (Nibble2, Nibble0); Char (Nibble6, Nibble8);
                   Char (Nibble6, Nibble1); Char (Nibble7, Nibble3);
                   Char (Nibble2, Nibble0); Char (Nibble6, Nibble9);
                   Char (Nibble6, NibbleE); Char (Nibble7, Nibble6);
                   Char (Nibble6, Nibble1); Char (Nibble6, NibbleC);
                   Char (Nibble6, Nibble9); Char (Nibble6, Nibble4);
                   Char (Nibble2, Nibble0); Char (Nibble7, Nibble3);
                   Char (Nibble7, Nibble5); Char (Nibble6, Nibble2);
                   Char (Nibble7, Nibble3); Char (Nibble6, NibbleF);
                   Char (Nibble7, Nibble2); Char (Nibble7, Nibble4);
                   Char (Nibble2, NibbleE)]));;

let rec krun_i_i_i_i _A _B _C _D
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a with (_, (_, (_, Success _))) -> bot_pred
            | (theory, (_, (_, Failure xd))) ->
              bind (eq_i_o (kcompile _A _B _D theory))
                (fun aa ->
                  (match aa with Success _ -> bot_pred
                    | Failure s ->
                      (if equal_lista equal_char xd
                            ([Char (Nibble4, Nibble2); Char (Nibble6, Nibble1);
                               Char (Nibble6, Nibble4); Char (Nibble2, Nibble0);
                               Char (Nibble7, Nibble2); Char (Nibble6, Nibble5);
                               Char (Nibble7, Nibble3); Char (Nibble7, Nibble5);
                               Char (Nibble6, NibbleC); Char (Nibble7, Nibble4);
                               Char (Nibble3, NibbleA);
                               Char (Nibble2, Nibble0)] @
                              s)
                        then single () else bot_pred))))))
      (sup_pred
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a with (_, (_, (_, Success _))) -> bot_pred
              | (_, (_, (_, Failure []))) -> bot_pred
              | (theory, (_, (l, Failure (ac :: lista)))) ->
                case_char
                  (fun nibble1 nibble2 ->
                    (match nibble1 with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred
                      | Nibble4 ->
                        (match nibble2 with Nibble0 -> bot_pred
                          | Nibble1 -> bot_pred
                          | Nibble2 ->
                            (match lista with [] -> bot_pred
                              | aca :: listaa ->
                                case_char
                                  (fun nibble1a nibble2a ->
                                    (match nibble1a with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 ->
(match nibble2a with Nibble0 -> bot_pred
  | Nibble1 ->
    (match listaa with [] -> bot_pred
      | acb :: listb ->
        case_char
          (fun nibble1b nibble2b ->
            (match nibble1b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred
              | Nibble6 ->
                (match nibble2b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 ->
                    (match listb with [] -> bot_pred
                      | acc :: listab ->
                        case_char
                          (fun nibble1c nibble2c ->
                            (match nibble1c with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred
                              | Nibble2 ->
                                (match nibble2c
                                  with Nibble0 ->
                                    (match listab with [] -> bot_pred
                                      | acd :: listc ->
case_char
  (fun nibble1d nibble2d ->
    (match nibble1d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
      | Nibble5 -> bot_pred
      | Nibble6 ->
        (match nibble2d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
          | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
          | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
          | Nibble8 -> bot_pred
          | Nibble9 ->
            (match listc with [] -> bot_pred
              | ace :: listac ->
                case_char
                  (fun nibble1e nibble2e ->
                    (match nibble1e with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred
                      | Nibble6 ->
                        (match nibble2e with Nibble0 -> bot_pred
                          | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred
                          | NibbleE ->
                            (match listac with [] -> bot_pred
                              | acf :: listd ->
                                case_char
                                  (fun nibble1f nibble2f ->
                                    (match nibble1f with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 -> bot_pred
                                      | Nibble7 ->
(match nibble2f
  with Nibble0 ->
    (match listd with [] -> bot_pred
      | acg :: listad ->
        case_char
          (fun nibble1g nibble2g ->
            (match nibble1g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
              | Nibble7 ->
                (match nibble2g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred
                  | Nibble5 ->
                    (match listad with [] -> bot_pred
                      | ach :: liste ->
                        case_char
                          (fun nibble1h nibble2h ->
                            (match nibble1h with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                              | Nibble7 ->
                                (match nibble2h with Nibble0 -> bot_pred
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred
                                  | Nibble4 ->
                                    (match liste with [] -> bot_pred
                                      | aci :: listae ->
case_char
  (fun nibble1i nibble2i ->
    (match nibble1i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 ->
        (match nibble2i
          with Nibble0 ->
            (match listae with [] -> bot_pred
              | acj :: listf ->
                case_char
                  (fun nibble1j nibble2j ->
                    (match nibble1j with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                      | Nibble7 ->
                        (match nibble2j
                          with Nibble0 ->
                            (match listf with [] -> bot_pred
                              | ack :: listaf ->
                                case_char
                                  (fun nibble1k nibble2k ->
                                    (match nibble1k with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 -> bot_pred
                                      | Nibble7 ->
(match nibble2k with Nibble0 -> bot_pred | Nibble1 -> bot_pred
  | Nibble2 ->
    (match listaf with [] -> bot_pred
      | acl :: listg ->
        case_char
          (fun nibble1l nibble2l ->
            (match nibble1l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred
              | Nibble6 ->
                (match nibble2l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE -> bot_pred
                  | NibbleF ->
                    (match listg with [] -> bot_pred
                      | acm :: listag ->
                        case_char
                          (fun nibble1m nibble2m ->
                            (match nibble1m with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred
                              | Nibble6 ->
                                (match nibble2m with Nibble0 -> bot_pred
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 ->
                                    (match listag with [] -> bot_pred
                                      | acn :: listh ->
case_char
  (fun nibble1n nibble2n ->
    (match nibble1n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
      | Nibble7 ->
        (match nibble2n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
          | Nibble2 ->
            (match listh with [] -> bot_pred
              | aco :: listah ->
                case_char
                  (fun nibble1o nibble2o ->
                    (match nibble1o with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred
                      | Nibble6 ->
                        (match nibble2o with Nibble0 -> bot_pred
                          | Nibble1 ->
                            (match listah with [] -> bot_pred
                              | acp :: listi ->
                                case_char
                                  (fun nibble1p nibble2p ->
                                    (match nibble1p with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 ->
(match nibble2p with Nibble0 -> bot_pred | Nibble1 -> bot_pred
  | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
  | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
  | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
  | NibbleB -> bot_pred | NibbleC -> bot_pred
  | NibbleD ->
    (match listi with [] -> bot_pred
      | acq :: listai ->
        case_char
          (fun nibble1q nibble2q ->
            (match nibble1q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 ->
                (match nibble2q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE ->
                    (match listai
                      with [] ->
                        bind (eq_i_o (kcompile _A _B _D theory))
                          (fun aa ->
                            (match aa
                              with Success (theorya, (database, (subG, (_, _))))
                                -> (if equal_kFile _A _B _C _D theory theorya
                                     then bind
    (eq_i_i (equal_option (equal_list (equal_suB _A _B _D)))
      (realConfigurationTest _D _A _B _D l theory database subG) None)
    (fun () -> single ())
                                     else bot_pred)
                              | Failure _ -> bot_pred))
                      | _ :: _ -> bot_pred)
                  | NibbleF -> bot_pred)
              | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
              | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
              | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
              | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acq)
  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble7 -> bot_pred
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  acp)
                          | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                          | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                          | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                          | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                          | NibbleA -> bot_pred | NibbleB -> bot_pred
                          | NibbleC -> bot_pred | NibbleD -> bot_pred
                          | NibbleE -> bot_pred | NibbleF -> bot_pred)
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  aco)
          | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
          | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
          | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
          | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
          | NibbleF -> bot_pred)
      | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
      | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
      | NibbleE -> bot_pred | NibbleF -> bot_pred))
  acn)
                                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                                  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                              | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                              | Nibble9 -> bot_pred | NibbleA -> bot_pred
                              | NibbleB -> bot_pred | NibbleC -> bot_pred
                              | NibbleD -> bot_pred | NibbleE -> bot_pred
                              | NibbleF -> bot_pred))
                          acm))
              | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
              | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
              | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acl)
  | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
  | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
  | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
  | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
  | NibbleF -> bot_pred)
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  ack)
                          | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred | NibbleE -> bot_pred
                          | NibbleF -> bot_pred)
                      | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                      | NibbleA -> bot_pred | NibbleB -> bot_pred
                      | NibbleC -> bot_pred | NibbleD -> bot_pred
                      | NibbleE -> bot_pred | NibbleF -> bot_pred))
                  acj)
          | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
          | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
          | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
          | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
          | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
      | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
      | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
      | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
      | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
      | NibbleF -> bot_pred))
  aci)
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                                  | NibbleF -> bot_pred)
                              | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                              | NibbleA -> bot_pred | NibbleB -> bot_pred
                              | NibbleC -> bot_pred | NibbleD -> bot_pred
                              | NibbleE -> bot_pred | NibbleF -> bot_pred))
                          ach)
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE -> bot_pred | NibbleF -> bot_pred)
              | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
              | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
              | NibbleE -> bot_pred | NibbleF -> bot_pred))
          acg)
  | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
  | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
  | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
  | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
  | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  acf)
                          | NibbleF -> bot_pred)
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  ace)
          | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
          | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
      | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
      | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
      | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
  acd)
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                                  | NibbleF -> bot_pred)
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                              | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                              | Nibble9 -> bot_pred | NibbleA -> bot_pred
                              | NibbleB -> bot_pred | NibbleC -> bot_pred
                              | NibbleD -> bot_pred | NibbleE -> bot_pred
                              | NibbleF -> bot_pred))
                          acc)
                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                  | NibbleF -> bot_pred)
              | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
              | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
              | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acb)
  | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
  | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
  | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
  | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble7 -> bot_pred
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  aca)
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred | NibbleE -> bot_pred
                          | NibbleF -> bot_pred)
                      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  ac)))
        (sup_pred
          (bind (single (x, (xa, (xb, xc))))
            (fun a ->
              (match a with (_, (_, (_, Success _))) -> bot_pred
                | (_, (_, (_, Failure []))) -> bot_pred
                | (theory, (_, (l, Failure (ac :: lista)))) ->
                  case_char
                    (fun nibble1 nibble2 ->
                      (match nibble1 with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred
                        | Nibble4 ->
                          (match nibble2 with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD ->
                              (match lista with [] -> bot_pred
                                | aca :: listaa ->
                                  case_char
                                    (fun nibble1a nibble2a ->
                                      (match nibble1a with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 ->
  (match nibble2a with Nibble0 -> bot_pred
    | Nibble1 ->
      (match listaa with [] -> bot_pred
        | acb :: listb ->
          case_char
            (fun nibble1b nibble2b ->
              (match nibble1b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred
                    | Nibble3 ->
                      (match listb with [] -> bot_pred
                        | acc :: listab ->
                          case_char
                            (fun nibble1c nibble2c ->
                              (match nibble1c with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                | Nibble7 ->
                                  (match nibble2c with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred
                                    | Nibble2 ->
                                      (match listab with [] -> bot_pred
| acd :: listc ->
  case_char
    (fun nibble1d nibble2d ->
      (match nibble1d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
            | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
            | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
            | NibbleE -> bot_pred
            | NibbleF ->
              (match listc with [] -> bot_pred
                | ace :: listac ->
                  case_char
                    (fun nibble1e nibble2e ->
                      (match nibble1e with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred
                        | Nibble2 ->
                          (match nibble2e
                            with Nibble0 ->
                              (match listac with [] -> bot_pred
                                | acf :: listd ->
                                  case_char
                                    (fun nibble1f nibble2f ->
                                      (match nibble1f with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
| Nibble7 ->
  (match nibble2f with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 ->
      (match listd with [] -> bot_pred
        | acg :: listad ->
          case_char
            (fun nibble1g nibble2g ->
              (match nibble1g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 -> bot_pred
                | Nibble7 ->
                  (match nibble2g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred
                    | Nibble5 ->
                      (match listad with [] -> bot_pred
                        | ach :: liste ->
                          case_char
                            (fun nibble1h nibble2h ->
                              (match nibble1h with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2h with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred
                                    | NibbleC ->
                                      (match liste with [] -> bot_pred
| aci :: listae ->
  case_char
    (fun nibble1i nibble2i ->
      (match nibble1i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 ->
              (match listae with [] -> bot_pred
                | acj :: listf ->
                  case_char
                    (fun nibble1j nibble2j ->
                      (match nibble1j with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 ->
                          (match nibble2j with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 ->
                              (match listf with [] -> bot_pred
                                | ack :: listaf ->
                                  case_char
                                    (fun nibble1k nibble2k ->
                                      (match nibble1k with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2k
    with Nibble0 ->
      (match listaf with [] -> bot_pred
        | acl :: listg ->
          case_char
            (fun nibble1l nibble2l ->
              (match nibble1l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 ->
                      (match listg with [] -> bot_pred
                        | acm :: listag ->
                          case_char
                            (fun nibble1m nibble2m ->
                              (match nibble1m with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2m with Nibble0 -> bot_pred
                                    | Nibble1 ->
                                      (match listag with [] -> bot_pred
| acn :: listh ->
  case_char
    (fun nibble1n nibble2n ->
      (match nibble1n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
        | Nibble7 ->
          (match nibble2n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 -> bot_pred
            | Nibble6 ->
              (match listh with [] -> bot_pred
                | aco :: listah ->
                  case_char
                    (fun nibble1o nibble2o ->
                      (match nibble1o with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred
                        | Nibble6 ->
                          (match nibble2o with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 ->
                              (match listah with [] -> bot_pred
                                | acp :: listi ->
                                  case_char
                                    (fun nibble1p nibble2p ->
                                      (match nibble1p with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2p
    with Nibble0 ->
      (match listi with [] -> bot_pred
        | acq :: listai ->
          case_char
            (fun nibble1q nibble2q ->
              (match nibble1q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2q with Nibble0 -> bot_pred
                    | Nibble1 ->
                      (match listai with [] -> bot_pred
                        | acr :: listj ->
                          case_char
                            (fun nibble1r nibble2r ->
                              (match nibble1r with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred
                                | Nibble2 ->
                                  (match nibble2r
                                    with Nibble0 ->
                                      (match listj with [] -> bot_pred
| acs :: listaj ->
  case_char
    (fun nibble1s nibble2s ->
      (match nibble1s with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
        | Nibble7 ->
          (match nibble2s
            with Nibble0 ->
              (match listaj with [] -> bot_pred
                | act :: listk ->
                  case_char
                    (fun nibble1t nibble2t ->
                      (match nibble1t with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 ->
                          (match nibble2t with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred
                            | Nibble2 ->
                              (match listk with [] -> bot_pred
                                | acu :: listak ->
                                  case_char
                                    (fun nibble1u nibble2u ->
                                      (match nibble1u with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 ->
  (match nibble2u with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE -> bot_pred
    | NibbleF ->
      (match listak with [] -> bot_pred
        | acv :: listl ->
          case_char
            (fun nibble1v nibble2v ->
              (match nibble1v with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2v with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 ->
                      (match listl with [] -> bot_pred
                        | acw :: listal ->
                          case_char
                            (fun nibble1w nibble2w ->
                              (match nibble1w with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2w with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred
                                    | NibbleC ->
                                      (match listal with [] -> bot_pred
| acx :: listm ->
  case_char
    (fun nibble1x nibble2x ->
      (match nibble1x with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2x with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 ->
              (match listm with [] -> bot_pred
                | acy :: listam ->
                  case_char
                    (fun nibble1y nibble2y ->
                      (match nibble1y with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred
                        | Nibble6 ->
                          (match nibble2y with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD ->
                              (match listam with [] -> bot_pred
                                | acz :: listn ->
                                  case_char
                                    (fun nibble1z nibble2z ->
                                      (match nibble1z with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2z with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE ->
      (match listn
        with [] ->
          bind (eq_i_o (kcompile _A _B _D theory))
            (fun aa ->
              (match aa
                with Success (theorya, (database, (subG, (_, _)))) ->
                  (if equal_kFile _A _B _C _D theory theorya
                    then bind (eq_i_i
                                (equal_option
                                  (equal_prod
                                    (equal_list (equal_rulePat _A _B _D))
                                    (equal_list (equal_suB _A _B _D))))
                                (applyAllMacroRulesCheck _D _A _B l theory
                                  database subG)
                                None)
                           (fun () -> single ())
                    else bot_pred)
                | Failure _ -> bot_pred))
        | _ :: _ -> bot_pred)
    | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    acz)
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    acy)
            | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
            | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
            | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
            | NibbleF -> bot_pred)
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acx)
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acw)
                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                    | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acv))
| Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
| NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
| NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    acu)
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD -> bot_pred | NibbleE -> bot_pred
                            | NibbleF -> bot_pred)
                        | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                        | NibbleA -> bot_pred | NibbleB -> bot_pred
                        | NibbleC -> bot_pred | NibbleD -> bot_pred
                        | NibbleE -> bot_pred | NibbleF -> bot_pred))
                    act)
            | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
            | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
            | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
            | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
            | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
        | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
        | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
        | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acs)
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acr)
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acq)
    | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
    | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
    | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
    | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
    | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    acp)
                            | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                            | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                            | NibbleA -> bot_pred | NibbleB -> bot_pred
                            | NibbleC -> bot_pred | NibbleD -> bot_pred
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    aco)
            | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
            | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
            | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
        | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
        | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
        | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acn)
                                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acm)
                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                    | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acl)
    | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
    | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
    | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
    | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
    | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    ack)
                            | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                            | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                            | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                            | NibbleA -> bot_pred | NibbleB -> bot_pred
                            | NibbleC -> bot_pred | NibbleD -> bot_pred
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                        | NibbleA -> bot_pred | NibbleB -> bot_pred
                        | NibbleC -> bot_pred | NibbleD -> bot_pred
                        | NibbleE -> bot_pred | NibbleF -> bot_pred))
                    acj)
            | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
            | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
            | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
            | NibbleF -> bot_pred)
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    aci)
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            ach)
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                | NibbleA -> bot_pred | NibbleB -> bot_pred
                | NibbleC -> bot_pred | NibbleD -> bot_pred
                | NibbleE -> bot_pred | NibbleF -> bot_pred))
            acg)
    | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
    | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
    | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
    | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
    | NibbleF -> bot_pred)
| Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
| NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
| NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    acf)
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD -> bot_pred | NibbleE -> bot_pred
                            | NibbleF -> bot_pred)
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    ace))
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acd)
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                | NibbleA -> bot_pred | NibbleB -> bot_pred
                                | NibbleC -> bot_pred | NibbleD -> bot_pred
                                | NibbleE -> bot_pred | NibbleF -> bot_pred))
                            acc)
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acb)
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
| NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
| NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    aca)
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    ac)))
          (bind (single (x, (xa, (xb, xc))))
            (fun a ->
              (match a
                with (theory, (n, (l, Success b))) ->
                  bind (eq_i_o (kcompile _A _B _D theory))
                    (fun aa ->
                      (match aa
                        with Success (theorya, (database, (subG, (_, _)))) ->
                          (if equal_kFile _A _B _C _D theory theorya
                            then bind (eq_i_o
(applyAllMacroRulesCheck _D _A _B l theory database subG))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some (noMacroRules, ba) ->
 bind (eq_i_o (getFunRules noMacroRules))
   (fun xd ->
     bind (eq_i_o (getAnywhereRules noMacroRules))
       (fun xaa ->
         bind (eq_i_o (getAllKRules noMacroRules))
           (fun xba ->
             bind (eq_i_o (getAllBagRules noMacroRules))
               (fun xca ->
                 bind (krunAux_i_i_i_i_i_i_i_i_i _A _B _D database subG n xd xaa
                        xba xca ba b)
                   (fun () -> single ())))))))
                            else bot_pred)
                        | Failure _ -> bot_pred))
                | (_, (_, (_, Failure _))) -> bot_pred)))));;

let rec krun _A _B _C _D
  x1 x2 x3 x4 = holds (krun_i_i_i_i _A _B _C _D x1 x2 x3 x4);;

let rec inc = function One -> Bit0 One
              | Bit0 x -> Bit1 x
              | Bit1 x -> Bit0 (inc x);;

let rec oneTransKRuleAux_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, ([], _)))) -> single []
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allFunRules, (database, (subG, ((p, (_, (_, _))) :: fl, c))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUK _A _B _C _C p c [] subG) None)
                     (fun () ->
                       bind (oneTransKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                              database subG fl c)
                         single))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (_, (con, _))) :: fl, c))))
                  -> bind (oneTransKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl c)
                       (fun xe ->
                         bind (eq_i_o
                                (patternMacroingInSUK _A _B _C _C p c [] subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst false))))
           (fun () -> single xe)
       | Div _ -> bot_pred))))))))))
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (r, (con, _))) :: fl, c))))
                  -> bind (oneTransKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl c)
                       (fun xe ->
                         bind (eq_i_o
                                (patternMacroingInSUK _A _B _C _C p c [] subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst true))))
           (fun () ->
             bind (eq_i_o (substitutionInSUK _C r acc))
               (fun ad ->
                 (match ad with None -> bot_pred
                   | Some ra ->
                     single
                       (inserta
                         (equal_prod (equal_list (equal_suKFactor _A _B _C))
                           (equal_list (equal_suKFactor _A _B _C)))
                         (c, ra) xe))))
       | Div _ -> bot_pred))))))))))));;

let rec oneTransKRule_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, (_, (_, []))))) -> single []
            | (_, (_, (_, (_, (_, _ :: _))))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, []))))) -> bot_pred
              | (allFunRules,
                  (database, (subG, (allKRule, (transKRule, c :: l)))))
                -> bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C allFunRules
                          database subG allKRule transKRule l)
                     (fun xf ->
                       bind (oneStepKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allKRule (Continue c))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ca ->
                               bind (if_pred
                                      (not
(equal_lista (equal_suKFactor _A _B _C) c ca)))
                                 (fun () ->
                                   single
                                     (inserta
                                       (equal_prod
 (equal_list (equal_suKFactor _A _B _C))
 (equal_list (equal_suKFactor _A _B _C)))
                                       (c, ca) xf))
                             | Div _ -> bot_pred))))))
        (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, []))))) -> bot_pred
              | (allFunRules,
                  (database, (subG, (allKRule, (transKRule, c :: l)))))
                -> bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                          database subG allKRule (Continue c) (Stop c))
                     (fun () ->
                       bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allKRule transKRule l)
                         (fun xf ->
                           bind (oneTransKRuleAux_i_i_i_i_i_o _A _B _C
                                  allFunRules database subG transKRule c)
                             (fun xaa ->
                               single
                                 (insertAll
                                   (equal_prod
                                     (equal_list (equal_suKFactor _A _B _C))
                                     (equal_list (equal_suKFactor _A _B _C)))
                                   xaa xf))))))));;

let rec oneTransKRule_i_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe xf =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, (xe, xf)))))))
        (fun a ->
          (match a with (_, (_, (_, (_, (_, ([], [])))))) -> single ()
            | (_, (_, (_, (_, (_, ([], _ :: _)))))) -> bot_pred
            | (_, (_, (_, (_, (_, (_ :: _, _)))))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, (xe, xf)))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, ([], _)))))) -> bot_pred
              | (allFunRules,
                  (database, (subG, (allKRule, (transKRule, (c :: l, xg))))))
                -> bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C allFunRules
                          database subG allKRule transKRule l)
                     (fun xaa ->
                       bind (oneStepKRuleAux_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allKRule (Continue c))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ca ->
                               bind (if_pred
                                      (not
(equal_lista (equal_suKFactor _A _B _C) c ca)))
                                 (fun () ->
                                   (if equal_lista
 (equal_prod (equal_list (equal_suKFactor _A _B _C))
   (equal_list (equal_suKFactor _A _B _C)))
 xg (inserta
      (equal_prod (equal_list (equal_suKFactor _A _B _C))
        (equal_list (equal_suKFactor _A _B _C)))
      (c, ca) xaa)
                                     then single () else bot_pred))
                             | Div _ -> bot_pred))))))
        (bind (single (x, (xa, (xb, (xc, (xd, (xe, xf)))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, ([], _)))))) -> bot_pred
              | (allFunRules,
                  (database, (subG, (allKRule, (transKRule, (c :: l, xg))))))
                -> bind (oneStepKRuleAux_i_i_i_i_i_i _A _B _C allFunRules
                          database subG allKRule (Continue c) (Stop c))
                     (fun () ->
                       bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allKRule transKRule l)
                         (fun xaa ->
                           bind (oneTransKRuleAux_i_i_i_i_i_o _A _B _C
                                  allFunRules database subG transKRule c)
                             (fun xaaa ->
                               (if equal_lista
                                     (equal_prod
                                       (equal_list (equal_suKFactor _A _B _C))
                                       (equal_list (equal_suKFactor _A _B _C)))
                                     xg (insertAll
  (equal_prod (equal_list (equal_suKFactor _A _B _C))
    (equal_list (equal_suKFactor _A _B _C)))
  xaaa xaa)
                                 then single () else bot_pred))))))));;

let rec oneTransBagRule_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, ([], _)))) -> single []
            | (_, (_, (_, (_ :: _, _)))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, xd)))))
          (fun a ->
            (match a with (_, (_, (_, ([], _)))) -> bot_pred
              | (allFunRules, (database, (subG, ((p, (_, (_, _))) :: fl, b))))
                -> bind (eq_i_i
                          (equal_option
                            (equal_list
                              (equal_prod (equal_metaVar _C)
                                (equal_subsFactor _A _B _C))))
                          (patternMacroingInSUBag _A _B _C _C p b [] subG) None)
                     (fun () ->
                       bind (oneTransBagRule_i_i_i_i_i_o _A _B _C allFunRules
                              database subG fl b)
                         single))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (_, (con, _))) :: fl, b))))
                  -> bind (oneTransBagRule_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl b)
                       (fun xe ->
                         bind (eq_i_o
                                (patternMacroingInSUBag _A _B _C _C p b []
                                  subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst false))))
           (fun () -> single xe)
       | Div _ -> bot_pred))))))))))
          (bind (single (x, (xa, (xb, (xc, xd)))))
            (fun a ->
              (match a with (_, (_, (_, ([], _)))) -> bot_pred
                | (allFunRules,
                    (database, (subG, ((p, (r, (con, _))) :: fl, b))))
                  -> bind (oneTransBagRule_i_i_i_i_i_o _A _B _C allFunRules
                            database subG fl b)
                       (fun xe ->
                         bind (eq_i_o
                                (patternMacroingInSUBag _A _B _C _C p b []
                                  subG))
                           (fun aa ->
                             (match aa with None -> bot_pred
                               | Some acc ->
                                 bind (eq_i_o
(substitutionInSUKItem _C con acc))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some value ->
 bind (funEvaluationBool_i_i_i_i_o _A _B _C allFunRules database subG
        (Continue value))
   (fun ac ->
     (match ac with Continue _ -> bot_pred
       | Stop valuea ->
         bind (eq_i_i (equal_option (equal_label _A))
                (getKLabelInSUKItem valuea)
                (Some (ConstToLabel (BoolConst true))))
           (fun () ->
             bind (eq_i_o (substitutionInSUBag _C r acc))
               (fun ad ->
                 (match ad with None -> bot_pred
                   | Some ra ->
                     single (inserta (equal_list (equal_suB _A _B _C)) ra xe))))
       | Div _ -> bot_pred))))))))))));;

let rec replaceKCellsInList _A _B _C
  b x1 = match b, x1 with b, [] -> []
    | ba, (a, b) :: l ->
        (match replaceKCells _A _B _C ba a b
          with None -> replaceKCellsInList _A _B _C ba l
          | Some bb ->
            inserta (equal_list (equal_suB _A _B _C)) bb
              (replaceKCellsInList _A _B _C ba l));;

let rec oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C
  x xa xb xc xd xe xf xg =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, xg))))))))
        (fun a ->
          (match a with (_, (_, (_, (_, (_, (_, (_, []))))))) -> single []
            | (_, (_, (_, (_, (_, (_, (_, _ :: _))))))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, xg))))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, (_, (_, []))))))) -> bot_pred
              | (allFunRules,
                  (database,
                    (subG,
                      (allKRules,
                        (allBagRules,
                          (transKRules, (transBagRules, b :: l)))))))
                -> bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C allFunRules
                          database subG allKRules allBagRules transKRules
                          transBagRules l)
                     (fun xh ->
                       bind (oneStepBagRule_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allBagRules (Continue b))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ba ->
                               bind (if_pred
                                      (not
(equal_lista (equal_suB _A _B _C) b ba)))
                                 (fun () ->
                                   single
                                     (inserta (equal_list (equal_suB _A _B _C))
                                       ba xh))
                             | Div _ -> bot_pred))))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, xg))))))))
            (fun a ->
              (match a with (_, (_, (_, (_, (_, (_, (_, []))))))) -> bot_pred
                | (allFunRules,
                    (database,
                      (subG,
                        (allKRules,
                          (allBagRules,
                            (transKRules, (transBagRules, b :: l)))))))
                  -> bind (oneStepBagRule_i_i_i_i_i_i _A _B _C allFunRules
                            database subG allBagRules (Continue b) (Stop b))
                       (fun () ->
                         bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C
                                allFunRules database subG allKRules allBagRules
                                transKRules transBagRules l)
                           (fun xh ->
                             bind (eq_i_o (getAllKCells _B b))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C
    allFunRules database subG allKRules transKRules cl)
                                       (fun xaa ->
 bind (eq_i_o (replaceKCellsInList _A _B _C b xaa))
   (fun xab ->
     single (insertAll (equal_list (equal_suB _A _B _C)) xab xh))))))))))
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, xg))))))))
            (fun a ->
              (match a with (_, (_, (_, (_, (_, (_, (_, []))))))) -> bot_pred
                | (allFunRules,
                    (database,
                      (subG,
                        (allKRules,
                          (allBagRules,
                            (transKRules, (transBagRules, b :: l)))))))
                  -> bind (oneStepBagRule_i_i_i_i_i_i _A _B _C allFunRules
                            database subG allBagRules (Continue b) (Stop b))
                       (fun () ->
                         bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C
                                allFunRules database subG allKRules allBagRules
                                transKRules transBagRules l)
                           (fun xh ->
                             bind (eq_i_o (getAllKCells _B b))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneTransKRule_i_i_i_i_i_i_i _A _B _C
    allFunRules database subG allKRules transKRules cl [])
                                       (fun () ->
 bind (oneTransBagRule_i_i_i_i_i_o _A _B _C allFunRules database subG
        transBagRules b)
   (fun xaa ->
     single (insertAll (equal_list (equal_suB _A _B _C)) xaa xh))))))))))));;

let rec oneTransKSearch_i_i_i_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe xf xg xh =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
        (fun a ->
          (match a with (_, (_, (_, (_, (_, (_, (_, ([], [])))))))) -> single ()
            | (_, (_, (_, (_, (_, (_, (_, ([], _ :: _)))))))) -> bot_pred
            | (_, (_, (_, (_, (_, (_, (_, (_ :: _, _)))))))) -> bot_pred)))
      (sup_pred
        (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
          (fun a ->
            (match a with (_, (_, (_, (_, (_, (_, (_, ([], _)))))))) -> bot_pred
              | (allFunRules,
                  (database,
                    (subG,
                      (allKRules,
                        (allBagRules,
                          (transKRules, (transBagRules, (b :: l, xi))))))))
                -> bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C allFunRules
                          database subG allKRules allBagRules transKRules
                          transBagRules l)
                     (fun xaa ->
                       bind (oneStepBagRule_i_i_i_i_i_o _A _B _C allFunRules
                              database subG allBagRules (Continue b))
                         (fun aa ->
                           (match aa with Continue _ -> bot_pred
                             | Stop ba ->
                               bind (if_pred
                                      (not
(equal_lista (equal_suB _A _B _C) b ba)))
                                 (fun () ->
                                   (if equal_lista
 (equal_list (equal_suB _A _B _C)) xi
 (inserta (equal_list (equal_suB _A _B _C)) ba xaa)
                                     then single () else bot_pred))
                             | Div _ -> bot_pred))))))
        (sup_pred
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
            (fun a ->
              (match a
                with (_, (_, (_, (_, (_, (_, (_, ([], _)))))))) -> bot_pred
                | (allFunRules,
                    (database,
                      (subG,
                        (allKRules,
                          (allBagRules,
                            (transKRules, (transBagRules, (b :: l, xi))))))))
                  -> bind (oneStepBagRule_i_i_i_i_i_i _A _B _C allFunRules
                            database subG allBagRules (Continue b) (Stop b))
                       (fun () ->
                         bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C
                                allFunRules database subG allKRules allBagRules
                                transKRules transBagRules l)
                           (fun xaa ->
                             bind (eq_i_o (getAllKCells _B b))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneTransKRule_i_i_i_i_i_i_o _A _B _C
    allFunRules database subG allKRules transKRules cl)
                                       (fun xaaa ->
 bind (eq_i_o (replaceKCellsInList _A _B _C b xaaa))
   (fun xaab ->
     (if equal_lista (equal_list (equal_suB _A _B _C)) xi
           (insertAll (equal_list (equal_suB _A _B _C)) xaab xaa)
       then single () else bot_pred))))))))))
          (bind (single (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, xh)))))))))
            (fun a ->
              (match a
                with (_, (_, (_, (_, (_, (_, (_, ([], _)))))))) -> bot_pred
                | (allFunRules,
                    (database,
                      (subG,
                        (allKRules,
                          (allBagRules,
                            (transKRules, (transBagRules, (b :: l, xi))))))))
                  -> bind (oneStepBagRule_i_i_i_i_i_i _A _B _C allFunRules
                            database subG allBagRules (Continue b) (Stop b))
                       (fun () ->
                         bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _B _C
                                allFunRules database subG allKRules allBagRules
                                transKRules transBagRules l)
                           (fun xaa ->
                             bind (eq_i_o (getAllKCells _B b))
                               (fun aa ->
                                 (match aa with None -> bot_pred
                                   | Some cl ->
                                     bind (oneTransKRule_i_i_i_i_i_i_i _A _B _C
    allFunRules database subG allKRules transKRules cl [])
                                       (fun () ->
 bind (oneTransBagRule_i_i_i_i_i_o _A _B _C allFunRules database subG
        transBagRules b)
   (fun xaaa ->
     (if equal_lista (equal_list (equal_suB _A _B _C)) xi
           (insertAll (equal_list (equal_suB _A _B _C)) xaaa xaa)
       then single () else bot_pred))))))))))));;

let rec allAllFunAnywhere_i_i_i_i_i_o _A _B _C
  x xa xb xc xd =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, (_, [])))) -> single []
            | (_, (_, (_, (_, _ :: _)))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, xd)))))
        (fun a ->
          (match a with (_, (_, (_, (_, [])))) -> bot_pred
            | (allFunRules, (allAnywheres, (database, (subG, b :: l)))) ->
              bind (allAllFunAnywhere_i_i_i_i_i_o _A _B _C allFunRules
                     allAnywheres database subG l)
                (fun xe ->
                  bind (funAnywhere_i_i_i_i_i_o _A _B _C allFunRules
                         allAnywheres database subG (Continue b))
                    (fun aa ->
                      (match aa with Continue _ -> bot_pred
                        | Stop ba -> single (ba :: xe)
                        | Div _ -> bot_pred))))));;

let rec allAllFunAnywhere_i_i_i_i_i_i _A _B _C
  x xa xb xc xd xe =
    sup_pred
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, (_, ([], []))))) -> single ()
            | (_, (_, (_, (_, ([], _ :: _))))) -> bot_pred
            | (_, (_, (_, (_, (_ :: _, _))))) -> bot_pred)))
      (bind (single (x, (xa, (xb, (xc, (xd, xe))))))
        (fun a ->
          (match a with (_, (_, (_, (_, ([], _))))) -> bot_pred
            | (allFunRules, (allAnywheres, (database, (subG, (ba :: l, b))))) ->
              (match b with [] -> bot_pred
                | bb :: bl ->
                  bind (allAllFunAnywhere_i_i_i_i_i_i _A _B _C allFunRules
                         allAnywheres database subG l bl)
                    (fun () ->
                      bind (funAnywhere_i_i_i_i_i_i _A _B _C allFunRules
                             allAnywheres database subG (Continue ba) (Stop bb))
                        (fun () -> single ()))))));;

let rec ksearchAux_i_i_i_i_i_i_i_i_i_i_i _A _C _D
  x xa xb xc xd xe xf xg xh xi xj =
    sup_pred
      (bind (single
              (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, (xh, (xi, xj)))))))))))
        (fun (database,
               (subG,
                 (xk, (allFunRules,
                        (allAnywheres, (_, (_, (_, (_, (bl, bla))))))))))
          -> bind (allAllFunAnywhere_i_i_i_i_i_i _A _C _D allFunRules
                    allAnywheres database subG bl bla)
               (fun () ->
                 (if equal_nata xk Zero_nat then single () else bot_pred))))
      (sup_pred
        (bind (single
                (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, (xh, (xi, xj)))))))))))
          (fun a ->
            (match a
              with (database,
                     (subG,
                       (_, (allFunRules,
                             (allAnywheres,
                               (allKRules,
                                 (allBagRules,
                                   (transKRules,
                                     (transBagRules, (bl, []))))))))))
                -> bind (allAllFunAnywhere_i_i_i_i_i_o _A _C _D allFunRules
                          allAnywheres database subG bl)
                     (fun xk ->
                       bind (oneTransKSearch_i_i_i_i_i_i_i_i_i _A _C _D
                              allFunRules database subG allKRules allBagRules
                              transKRules transBagRules xk [])
                         (fun () -> single ()))
              | (_, (_, (_, (_, (_, (_, (_, (_, (_, (_, _ :: _)))))))))) ->
                bot_pred)))
        (bind (single
                (x, (xa, (xb, (xc, (xd, (xe, (xf, (xg, (xh, (xi, xj)))))))))))
          (fun (database,
                 (subG,
                   (n, (allFunRules,
                         (allAnywheres,
                           (allKRules,
                             (allBagRules,
                               (transKRules, (transBagRules, (bl, bla))))))))))
            -> bind (if_pred (less_nat Zero_nat n))
                 (fun () ->
                   bind (allAllFunAnywhere_i_i_i_i_i_o _A _C _D allFunRules
                          allAnywheres database subG bl)
                     (fun xk ->
                       bind (oneTransKSearch_i_i_i_i_i_i_i_i_o _A _C _D
                              allFunRules database subG allKRules allBagRules
                              transKRules transBagRules xk)
                         (fun xl ->
                           bind (ksearchAux_i_i_i_i_i_i_i_i_i_i_i _A _C _D
                                  database subG (minus_nat n one_nata)
                                  allFunRules allAnywheres allKRules allBagRules
                                  transKRules transBagRules xl bla)
                             (fun () ->
                               bind (if_pred (less_nat Zero_nat (size_list xl)))
                                 (fun () -> single ()))))))));;

let rec divideAllBagRules
  = function [] -> ([], [])
    | BagRulePat (a, b, c, d) :: l ->
        (let (left, right) = divideAllBagRules l in
          (if d then ((a, (b, (c, d))) :: left, right)
            else (left, (a, (b, (c, d))) :: right)))
    | FunPat (v, va, vb) :: l -> divideAllBagRules l
    | MacroPat (v, va, vb) :: l -> divideAllBagRules l
    | AnywherePat (v, va, vb, vc) :: l -> divideAllBagRules l
    | KRulePat (v, va, vb, vc) :: l -> divideAllBagRules l;;

let rec divideAllKRules
  = function [] -> ([], [])
    | KRulePat (a, b, c, d) :: l ->
        (let (left, right) = divideAllKRules l in
          (if d then ((a, (b, (c, d))) :: left, right)
            else (left, (a, (b, (c, d))) :: right)))
    | FunPat (v, va, vb) :: l -> divideAllKRules l
    | MacroPat (v, va, vb) :: l -> divideAllKRules l
    | AnywherePat (v, va, vb, vc) :: l -> divideAllKRules l
    | BagRulePat (v, va, vb, vc) :: l -> divideAllKRules l;;

let rec ksearch_i_i_i_i _A _B _C _D
  x xa xb xc =
    sup_pred
      (bind (single (x, (xa, (xb, xc))))
        (fun a ->
          (match a with (_, (_, (_, Success _))) -> bot_pred
            | (theory, (_, (_, Failure xd))) ->
              bind (eq_i_o (kcompile _A _B _D theory))
                (fun aa ->
                  (match aa with Success _ -> bot_pred
                    | Failure s ->
                      (if equal_lista equal_char xd
                            ([Char (Nibble4, Nibble2); Char (Nibble6, Nibble1);
                               Char (Nibble6, Nibble4); Char (Nibble2, Nibble0);
                               Char (Nibble7, Nibble2); Char (Nibble6, Nibble5);
                               Char (Nibble7, Nibble3); Char (Nibble7, Nibble5);
                               Char (Nibble6, NibbleC); Char (Nibble7, Nibble4);
                               Char (Nibble3, NibbleA);
                               Char (Nibble2, Nibble0)] @
                              s)
                        then single () else bot_pred))))))
      (sup_pred
        (bind (single (x, (xa, (xb, xc))))
          (fun a ->
            (match a with (_, (_, (_, Success _))) -> bot_pred
              | (_, (_, (_, Failure []))) -> bot_pred
              | (theory, (_, (l, Failure (ac :: lista)))) ->
                case_char
                  (fun nibble1 nibble2 ->
                    (match nibble1 with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred
                      | Nibble4 ->
                        (match nibble2 with Nibble0 -> bot_pred
                          | Nibble1 -> bot_pred
                          | Nibble2 ->
                            (match lista with [] -> bot_pred
                              | aca :: listaa ->
                                case_char
                                  (fun nibble1a nibble2a ->
                                    (match nibble1a with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 ->
(match nibble2a with Nibble0 -> bot_pred
  | Nibble1 ->
    (match listaa with [] -> bot_pred
      | acb :: listb ->
        case_char
          (fun nibble1b nibble2b ->
            (match nibble1b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred
              | Nibble6 ->
                (match nibble2b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 ->
                    (match listb with [] -> bot_pred
                      | acc :: listab ->
                        case_char
                          (fun nibble1c nibble2c ->
                            (match nibble1c with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred
                              | Nibble2 ->
                                (match nibble2c
                                  with Nibble0 ->
                                    (match listab with [] -> bot_pred
                                      | acd :: listc ->
case_char
  (fun nibble1d nibble2d ->
    (match nibble1d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
      | Nibble5 -> bot_pred
      | Nibble6 ->
        (match nibble2d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
          | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
          | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
          | Nibble8 -> bot_pred
          | Nibble9 ->
            (match listc with [] -> bot_pred
              | ace :: listac ->
                case_char
                  (fun nibble1e nibble2e ->
                    (match nibble1e with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred
                      | Nibble6 ->
                        (match nibble2e with Nibble0 -> bot_pred
                          | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred
                          | NibbleE ->
                            (match listac with [] -> bot_pred
                              | acf :: listd ->
                                case_char
                                  (fun nibble1f nibble2f ->
                                    (match nibble1f with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 -> bot_pred
                                      | Nibble7 ->
(match nibble2f
  with Nibble0 ->
    (match listd with [] -> bot_pred
      | acg :: listad ->
        case_char
          (fun nibble1g nibble2g ->
            (match nibble1g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
              | Nibble7 ->
                (match nibble2g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred
                  | Nibble5 ->
                    (match listad with [] -> bot_pred
                      | ach :: liste ->
                        case_char
                          (fun nibble1h nibble2h ->
                            (match nibble1h with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                              | Nibble7 ->
                                (match nibble2h with Nibble0 -> bot_pred
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred
                                  | Nibble4 ->
                                    (match liste with [] -> bot_pred
                                      | aci :: listae ->
case_char
  (fun nibble1i nibble2i ->
    (match nibble1i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 ->
        (match nibble2i
          with Nibble0 ->
            (match listae with [] -> bot_pred
              | acj :: listf ->
                case_char
                  (fun nibble1j nibble2j ->
                    (match nibble1j with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                      | Nibble7 ->
                        (match nibble2j
                          with Nibble0 ->
                            (match listf with [] -> bot_pred
                              | ack :: listaf ->
                                case_char
                                  (fun nibble1k nibble2k ->
                                    (match nibble1k with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 -> bot_pred
                                      | Nibble7 ->
(match nibble2k with Nibble0 -> bot_pred | Nibble1 -> bot_pred
  | Nibble2 ->
    (match listaf with [] -> bot_pred
      | acl :: listg ->
        case_char
          (fun nibble1l nibble2l ->
            (match nibble1l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
              | Nibble5 -> bot_pred
              | Nibble6 ->
                (match nibble2l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE -> bot_pred
                  | NibbleF ->
                    (match listg with [] -> bot_pred
                      | acm :: listag ->
                        case_char
                          (fun nibble1m nibble2m ->
                            (match nibble1m with Nibble0 -> bot_pred
                              | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred
                              | Nibble6 ->
                                (match nibble2m with Nibble0 -> bot_pred
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 ->
                                    (match listag with [] -> bot_pred
                                      | acn :: listh ->
case_char
  (fun nibble1n nibble2n ->
    (match nibble1n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
      | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
      | Nibble7 ->
        (match nibble2n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
          | Nibble2 ->
            (match listh with [] -> bot_pred
              | aco :: listah ->
                case_char
                  (fun nibble1o nibble2o ->
                    (match nibble1o with Nibble0 -> bot_pred
                      | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                      | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                      | Nibble5 -> bot_pred
                      | Nibble6 ->
                        (match nibble2o with Nibble0 -> bot_pred
                          | Nibble1 ->
                            (match listah with [] -> bot_pred
                              | acp :: listi ->
                                case_char
                                  (fun nibble1p nibble2p ->
                                    (match nibble1p with Nibble0 -> bot_pred
                                      | Nibble1 -> bot_pred
                                      | Nibble2 -> bot_pred
                                      | Nibble3 -> bot_pred
                                      | Nibble4 -> bot_pred
                                      | Nibble5 -> bot_pred
                                      | Nibble6 ->
(match nibble2p with Nibble0 -> bot_pred | Nibble1 -> bot_pred
  | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
  | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
  | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
  | NibbleB -> bot_pred | NibbleC -> bot_pred
  | NibbleD ->
    (match listi with [] -> bot_pred
      | acq :: listai ->
        case_char
          (fun nibble1q nibble2q ->
            (match nibble1q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
              | Nibble2 ->
                (match nibble2q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                  | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                  | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE ->
                    (match listai
                      with [] ->
                        bind (eq_i_o (kcompile _A _B _D theory))
                          (fun aa ->
                            (match aa
                              with Success (theorya, (database, (subG, (_, _))))
                                -> (if equal_kFile _A _B _C _D theory theorya
                                     then bind
    (eq_i_i (equal_option (equal_list (equal_suB _A _B _D)))
      (realConfigurationTest _D _A _B _D l theory database subG) None)
    (fun () -> single ())
                                     else bot_pred)
                              | Failure _ -> bot_pred))
                      | _ :: _ -> bot_pred)
                  | NibbleF -> bot_pred)
              | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
              | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
              | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
              | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acq)
  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble7 -> bot_pred
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  acp)
                          | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                          | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                          | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                          | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                          | NibbleA -> bot_pred | NibbleB -> bot_pred
                          | NibbleC -> bot_pred | NibbleD -> bot_pred
                          | NibbleE -> bot_pred | NibbleF -> bot_pred)
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  aco)
          | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
          | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
          | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
          | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
          | NibbleF -> bot_pred)
      | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
      | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
      | NibbleE -> bot_pred | NibbleF -> bot_pred))
  acn)
                                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                                  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                              | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                              | Nibble9 -> bot_pred | NibbleA -> bot_pred
                              | NibbleB -> bot_pred | NibbleC -> bot_pred
                              | NibbleD -> bot_pred | NibbleE -> bot_pred
                              | NibbleF -> bot_pred))
                          acm))
              | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
              | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
              | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acl)
  | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
  | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
  | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
  | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
  | NibbleF -> bot_pred)
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  ack)
                          | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred | NibbleE -> bot_pred
                          | NibbleF -> bot_pred)
                      | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                      | NibbleA -> bot_pred | NibbleB -> bot_pred
                      | NibbleC -> bot_pred | NibbleD -> bot_pred
                      | NibbleE -> bot_pred | NibbleF -> bot_pred))
                  acj)
          | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
          | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
          | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
          | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
          | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
      | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
      | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
      | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
      | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
      | NibbleF -> bot_pred))
  aci)
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                                  | NibbleF -> bot_pred)
                              | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                              | NibbleA -> bot_pred | NibbleB -> bot_pred
                              | NibbleC -> bot_pred | NibbleD -> bot_pred
                              | NibbleE -> bot_pred | NibbleF -> bot_pred))
                          ach)
                  | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                  | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                  | NibbleA -> bot_pred | NibbleB -> bot_pred
                  | NibbleC -> bot_pred | NibbleD -> bot_pred
                  | NibbleE -> bot_pred | NibbleF -> bot_pred)
              | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
              | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
              | NibbleE -> bot_pred | NibbleF -> bot_pred))
          acg)
  | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
  | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
  | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
  | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
  | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  acf)
                          | NibbleF -> bot_pred)
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  ace)
          | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
          | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
      | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
      | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
      | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
  acd)
                                  | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                  | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                                  | NibbleF -> bot_pred)
                              | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                              | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                              | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                              | Nibble9 -> bot_pred | NibbleA -> bot_pred
                              | NibbleB -> bot_pred | NibbleC -> bot_pred
                              | NibbleD -> bot_pred | NibbleE -> bot_pred
                              | NibbleF -> bot_pred))
                          acc)
                  | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                  | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                  | Nibble9 -> bot_pred | NibbleA -> bot_pred
                  | NibbleB -> bot_pred | NibbleC -> bot_pred
                  | NibbleD -> bot_pred | NibbleE -> bot_pred
                  | NibbleF -> bot_pred)
              | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
              | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
              | NibbleD -> bot_pred | NibbleE -> bot_pred
              | NibbleF -> bot_pred))
          acb)
  | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
  | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
  | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
  | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
  | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                      | Nibble7 -> bot_pred
                                      | Nibble8 -> bot_pred
                                      | Nibble9 -> bot_pred
                                      | NibbleA -> bot_pred
                                      | NibbleB -> bot_pred
                                      | NibbleC -> bot_pred
                                      | NibbleD -> bot_pred
                                      | NibbleE -> bot_pred
                                      | NibbleF -> bot_pred))
                                  aca)
                          | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                          | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                          | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                          | Nibble9 -> bot_pred | NibbleA -> bot_pred
                          | NibbleB -> bot_pred | NibbleC -> bot_pred
                          | NibbleD -> bot_pred | NibbleE -> bot_pred
                          | NibbleF -> bot_pred)
                      | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                      | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                      | Nibble9 -> bot_pred | NibbleA -> bot_pred
                      | NibbleB -> bot_pred | NibbleC -> bot_pred
                      | NibbleD -> bot_pred | NibbleE -> bot_pred
                      | NibbleF -> bot_pred))
                  ac)))
        (sup_pred
          (bind (single (x, (xa, (xb, xc))))
            (fun a ->
              (match a with (_, (_, (_, Success _))) -> bot_pred
                | (_, (_, (_, Failure []))) -> bot_pred
                | (theory, (_, (l, Failure (ac :: lista)))) ->
                  case_char
                    (fun nibble1 nibble2 ->
                      (match nibble1 with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred
                        | Nibble4 ->
                          (match nibble2 with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD ->
                              (match lista with [] -> bot_pred
                                | aca :: listaa ->
                                  case_char
                                    (fun nibble1a nibble2a ->
                                      (match nibble1a with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 ->
  (match nibble2a with Nibble0 -> bot_pred
    | Nibble1 ->
      (match listaa with [] -> bot_pred
        | acb :: listb ->
          case_char
            (fun nibble1b nibble2b ->
              (match nibble1b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2b with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred
                    | Nibble3 ->
                      (match listb with [] -> bot_pred
                        | acc :: listab ->
                          case_char
                            (fun nibble1c nibble2c ->
                              (match nibble1c with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                | Nibble7 ->
                                  (match nibble2c with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred
                                    | Nibble2 ->
                                      (match listab with [] -> bot_pred
| acd :: listc ->
  case_char
    (fun nibble1d nibble2d ->
      (match nibble1d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2d with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
            | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
            | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
            | NibbleE -> bot_pred
            | NibbleF ->
              (match listc with [] -> bot_pred
                | ace :: listac ->
                  case_char
                    (fun nibble1e nibble2e ->
                      (match nibble1e with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred
                        | Nibble2 ->
                          (match nibble2e
                            with Nibble0 ->
                              (match listac with [] -> bot_pred
                                | acf :: listd ->
                                  case_char
                                    (fun nibble1f nibble2f ->
                                      (match nibble1f with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
| Nibble7 ->
  (match nibble2f with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 ->
      (match listd with [] -> bot_pred
        | acg :: listad ->
          case_char
            (fun nibble1g nibble2g ->
              (match nibble1g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 -> bot_pred
                | Nibble7 ->
                  (match nibble2g with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred
                    | Nibble5 ->
                      (match listad with [] -> bot_pred
                        | ach :: liste ->
                          case_char
                            (fun nibble1h nibble2h ->
                              (match nibble1h with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2h with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred
                                    | NibbleC ->
                                      (match liste with [] -> bot_pred
| aci :: listae ->
  case_char
    (fun nibble1i nibble2i ->
      (match nibble1i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2i with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 ->
              (match listae with [] -> bot_pred
                | acj :: listf ->
                  case_char
                    (fun nibble1j nibble2j ->
                      (match nibble1j with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 ->
                          (match nibble2j with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 ->
                              (match listf with [] -> bot_pred
                                | ack :: listaf ->
                                  case_char
                                    (fun nibble1k nibble2k ->
                                      (match nibble1k with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2k
    with Nibble0 ->
      (match listaf with [] -> bot_pred
        | acl :: listg ->
          case_char
            (fun nibble1l nibble2l ->
              (match nibble1l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2l with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 ->
                      (match listg with [] -> bot_pred
                        | acm :: listag ->
                          case_char
                            (fun nibble1m nibble2m ->
                              (match nibble1m with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2m with Nibble0 -> bot_pred
                                    | Nibble1 ->
                                      (match listag with [] -> bot_pred
| acn :: listh ->
  case_char
    (fun nibble1n nibble2n ->
      (match nibble1n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
        | Nibble7 ->
          (match nibble2n with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 -> bot_pred
            | Nibble6 ->
              (match listh with [] -> bot_pred
                | aco :: listah ->
                  case_char
                    (fun nibble1o nibble2o ->
                      (match nibble1o with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred
                        | Nibble6 ->
                          (match nibble2o with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 ->
                              (match listah with [] -> bot_pred
                                | acp :: listi ->
                                  case_char
                                    (fun nibble1p nibble2p ->
                                      (match nibble1p with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2p
    with Nibble0 ->
      (match listi with [] -> bot_pred
        | acq :: listai ->
          case_char
            (fun nibble1q nibble2q ->
              (match nibble1q with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2q with Nibble0 -> bot_pred
                    | Nibble1 ->
                      (match listai with [] -> bot_pred
                        | acr :: listj ->
                          case_char
                            (fun nibble1r nibble2r ->
                              (match nibble1r with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred
                                | Nibble2 ->
                                  (match nibble2r
                                    with Nibble0 ->
                                      (match listj with [] -> bot_pred
| acs :: listaj ->
  case_char
    (fun nibble1s nibble2s ->
      (match nibble1s with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
        | Nibble7 ->
          (match nibble2s
            with Nibble0 ->
              (match listaj with [] -> bot_pred
                | act :: listk ->
                  case_char
                    (fun nibble1t nibble2t ->
                      (match nibble1t with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 ->
                          (match nibble2t with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred
                            | Nibble2 ->
                              (match listk with [] -> bot_pred
                                | acu :: listak ->
                                  case_char
                                    (fun nibble1u nibble2u ->
                                      (match nibble1u with Nibble0 -> bot_pred
| Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
| Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 ->
  (match nibble2u with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE -> bot_pred
    | NibbleF ->
      (match listak with [] -> bot_pred
        | acv :: listl ->
          case_char
            (fun nibble1v nibble2v ->
              (match nibble1v with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                | Nibble6 ->
                  (match nibble2v with Nibble0 -> bot_pred | Nibble1 -> bot_pred
                    | Nibble2 ->
                      (match listl with [] -> bot_pred
                        | acw :: listal ->
                          case_char
                            (fun nibble1w nibble2w ->
                              (match nibble1w with Nibble0 -> bot_pred
                                | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred
                                | Nibble6 ->
                                  (match nibble2w with Nibble0 -> bot_pred
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred
                                    | NibbleC ->
                                      (match listal with [] -> bot_pred
| acx :: listm ->
  case_char
    (fun nibble1x nibble2x ->
      (match nibble1x with Nibble0 -> bot_pred | Nibble1 -> bot_pred
        | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
        | Nibble5 -> bot_pred
        | Nibble6 ->
          (match nibble2x with Nibble0 -> bot_pred | Nibble1 -> bot_pred
            | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
            | Nibble5 ->
              (match listm with [] -> bot_pred
                | acy :: listam ->
                  case_char
                    (fun nibble1y nibble2y ->
                      (match nibble1y with Nibble0 -> bot_pred
                        | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred
                        | Nibble6 ->
                          (match nibble2y with Nibble0 -> bot_pred
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD ->
                              (match listam with [] -> bot_pred
                                | acz :: listn ->
                                  case_char
                                    (fun nibble1z nibble2z ->
                                      (match nibble1z with Nibble0 -> bot_pred
| Nibble1 -> bot_pred
| Nibble2 ->
  (match nibble2z with Nibble0 -> bot_pred | Nibble1 -> bot_pred
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE ->
      (match listn
        with [] ->
          bind (eq_i_o (kcompile _A _B _D theory))
            (fun aa ->
              (match aa
                with Success (theorya, (database, (subG, (_, _)))) ->
                  (if equal_kFile _A _B _C _D theory theorya
                    then bind (eq_i_i
                                (equal_option
                                  (equal_prod
                                    (equal_list (equal_rulePat _A _B _D))
                                    (equal_list (equal_suB _A _B _D))))
                                (applyAllMacroRulesCheck _D _A _B l theory
                                  database subG)
                                None)
                           (fun () -> single ())
                    else bot_pred)
                | Failure _ -> bot_pred))
        | _ :: _ -> bot_pred)
    | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    acz)
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    acy)
            | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
            | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
            | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
            | NibbleF -> bot_pred)
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acx)
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acw)
                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                    | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acv))
| Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
| NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
| NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    acu)
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD -> bot_pred | NibbleE -> bot_pred
                            | NibbleF -> bot_pred)
                        | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                        | NibbleA -> bot_pred | NibbleB -> bot_pred
                        | NibbleC -> bot_pred | NibbleD -> bot_pred
                        | NibbleE -> bot_pred | NibbleF -> bot_pred))
                    act)
            | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
            | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
            | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
            | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
            | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
        | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
        | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
        | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acs)
                                    | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acr)
                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acq)
    | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
    | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
    | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
    | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
    | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    acp)
                            | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                            | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                            | NibbleA -> bot_pred | NibbleB -> bot_pred
                            | NibbleC -> bot_pred | NibbleD -> bot_pred
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    aco)
            | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
            | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
            | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
        | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
        | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
        | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acn)
                                    | Nibble2 -> bot_pred | Nibble3 -> bot_pred
                                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            acm)
                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                    | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acl)
    | Nibble1 -> bot_pred | Nibble2 -> bot_pred | Nibble3 -> bot_pred
    | Nibble4 -> bot_pred | Nibble5 -> bot_pred | Nibble6 -> bot_pred
    | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
    | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
    | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
| Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
| Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
| NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
| NibbleF -> bot_pred))
                                    ack)
                            | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                            | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                            | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                            | NibbleA -> bot_pred | NibbleB -> bot_pred
                            | NibbleC -> bot_pred | NibbleD -> bot_pred
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                        | NibbleA -> bot_pred | NibbleB -> bot_pred
                        | NibbleC -> bot_pred | NibbleD -> bot_pred
                        | NibbleE -> bot_pred | NibbleF -> bot_pred))
                    acj)
            | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
            | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
            | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
            | NibbleF -> bot_pred)
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    aci)
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                | NibbleB -> bot_pred | NibbleC -> bot_pred
                                | NibbleD -> bot_pred | NibbleE -> bot_pred
                                | NibbleF -> bot_pred))
                            ach)
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                | NibbleA -> bot_pred | NibbleB -> bot_pred
                | NibbleC -> bot_pred | NibbleD -> bot_pred
                | NibbleE -> bot_pred | NibbleF -> bot_pred))
            acg)
    | Nibble3 -> bot_pred | Nibble4 -> bot_pred | Nibble5 -> bot_pred
    | Nibble6 -> bot_pred | Nibble7 -> bot_pred | Nibble8 -> bot_pred
    | Nibble9 -> bot_pred | NibbleA -> bot_pred | NibbleB -> bot_pred
    | NibbleC -> bot_pred | NibbleD -> bot_pred | NibbleE -> bot_pred
    | NibbleF -> bot_pred)
| Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
| NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
| NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    acf)
                            | Nibble1 -> bot_pred | Nibble2 -> bot_pred
                            | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                            | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                            | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                            | Nibble9 -> bot_pred | NibbleA -> bot_pred
                            | NibbleB -> bot_pred | NibbleC -> bot_pred
                            | NibbleD -> bot_pred | NibbleE -> bot_pred
                            | NibbleF -> bot_pred)
                        | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    ace))
        | Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
        | NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
        | NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
    acd)
                                    | Nibble3 -> bot_pred | Nibble4 -> bot_pred
                                    | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                                    | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                                    | Nibble9 -> bot_pred | NibbleA -> bot_pred
                                    | NibbleB -> bot_pred | NibbleC -> bot_pred
                                    | NibbleD -> bot_pred | NibbleE -> bot_pred
                                    | NibbleF -> bot_pred)
                                | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                                | NibbleA -> bot_pred | NibbleB -> bot_pred
                                | NibbleC -> bot_pred | NibbleD -> bot_pred
                                | NibbleE -> bot_pred | NibbleF -> bot_pred))
                            acc)
                    | Nibble4 -> bot_pred | Nibble5 -> bot_pred
                    | Nibble6 -> bot_pred | Nibble7 -> bot_pred
                    | Nibble8 -> bot_pred | Nibble9 -> bot_pred
                    | NibbleA -> bot_pred | NibbleB -> bot_pred
                    | NibbleC -> bot_pred | NibbleD -> bot_pred
                    | NibbleE -> bot_pred | NibbleF -> bot_pred)
                | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                | Nibble9 -> bot_pred | NibbleA -> bot_pred
                | NibbleB -> bot_pred | NibbleC -> bot_pred
                | NibbleD -> bot_pred | NibbleE -> bot_pred
                | NibbleF -> bot_pred))
            acb)
    | Nibble2 -> bot_pred | Nibble3 -> bot_pred | Nibble4 -> bot_pred
    | Nibble5 -> bot_pred | Nibble6 -> bot_pred | Nibble7 -> bot_pred
    | Nibble8 -> bot_pred | Nibble9 -> bot_pred | NibbleA -> bot_pred
    | NibbleB -> bot_pred | NibbleC -> bot_pred | NibbleD -> bot_pred
    | NibbleE -> bot_pred | NibbleF -> bot_pred)
| Nibble7 -> bot_pred | Nibble8 -> bot_pred | Nibble9 -> bot_pred
| NibbleA -> bot_pred | NibbleB -> bot_pred | NibbleC -> bot_pred
| NibbleD -> bot_pred | NibbleE -> bot_pred | NibbleF -> bot_pred))
                                    aca)
                            | NibbleE -> bot_pred | NibbleF -> bot_pred)
                        | Nibble5 -> bot_pred | Nibble6 -> bot_pred
                        | Nibble7 -> bot_pred | Nibble8 -> bot_pred
                        | Nibble9 -> bot_pred | NibbleA -> bot_pred
                        | NibbleB -> bot_pred | NibbleC -> bot_pred
                        | NibbleD -> bot_pred | NibbleE -> bot_pred
                        | NibbleF -> bot_pred))
                    ac)))
          (bind (single (x, (xa, (xb, xc))))
            (fun a ->
              (match a
                with (theory, (n, (l, Success bl))) ->
                  bind (eq_i_o (kcompile _A _B _D theory))
                    (fun aa ->
                      (match aa
                        with Success (theorya, (database, (subG, (_, _)))) ->
                          (if equal_kFile _A _B _C _D theory theorya
                            then bind (eq_i_o
(applyAllMacroRulesCheck _D _A _B l theory database subG))
                                   (fun ab ->
                                     (match ab with None -> bot_pred
                                       | Some (noMacroRules, b) ->
 bind (eq_i_o (getFunRules noMacroRules))
   (fun xd ->
     bind (eq_i_o (getAnywhereRules noMacroRules))
       (fun xaa ->
         bind (eq_i_o (divideAllKRules noMacroRules))
           (fun (transKRules, allKRules) ->
             bind (eq_i_o (divideAllBagRules noMacroRules))
               (fun (transBagRules, allBagRules) ->
                 bind (ksearchAux_i_i_i_i_i_i_i_i_i_i_i _A _B _D database subG n
                        xd xaa allKRules allBagRules transKRules transBagRules
                        [b] bl)
                   (fun () -> single ())))))))
                            else bot_pred)
                        | Failure _ -> bot_pred))
                | (_, (_, (_, Failure _))) -> bot_pred)))));;

let rec ksearch _A _B _C _D
  x1 x2 x3 x4 = holds (ksearch_i_i_i_i _A _B _C _D x1 x2 x3 x4);;

let rec getNonTerminalInList
  = function Single (Terminal a) -> []
    | Single (NonTerminal a) -> [a]
    | Con (Terminal a, l) -> getNonTerminalInList l
    | Con (NonTerminal a, l) -> a :: getNonTerminalInList l;;

end;; (*struct K*)
