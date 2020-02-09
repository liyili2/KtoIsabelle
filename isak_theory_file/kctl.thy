theory kctl
imports Main Real List k
begin

(* defining functions for checking if two program states are equal 
   by giving a set of names the users are caring about *)
primrec findCellByName and findCellByNameInSUB 
     and findCellByNameInSUBigKWithBag where
"findCellByName s [] = []"
| "findCellByName s (a#l) = (findCellByNameInSUB s a)@(findCellByName s l)"
| "findCellByNameInSUB s (ItemB x y z) =
           (if s = x then [z] else (findCellByNameInSUBigKWithBag s z))"
| "findCellByNameInSUB s (IdB x) = []"
| "findCellByNameInSUBigKWithBag s (SUK a) = []"
| "findCellByNameInSUBigKWithBag s (SUList a) = []"
| "findCellByNameInSUBigKWithBag s (SUSet a) = []"
| "findCellByNameInSUBigKWithBag s (SUMap a) = []"
| "findCellByNameInSUBigKWithBag s (SUBag a) = findCellByName s a"

primrec findCellByNameList where
"findCellByNameList [] B = []"
| "findCellByNameList (s#l) B = (case (findCellByName s B) of S' \<Rightarrow>
          (s,S')#(findCellByNameList l B))"

primrec findCellEqual where
"findCellEqual a [] subG = None"
| "findCellEqual a (x#l) subG = (case syntacticMonoidInSUBigKWithBag a x subG of None \<Rightarrow> 
        (case findCellEqual a l subG of None \<Rightarrow> None
           | Some (a',l') \<Rightarrow> Some (a', x#l'))
      | Some a' \<Rightarrow> Some (a',l))"

primrec cellsEqual where
"cellsEqual [] S subG = (if S = [] then True else False)"
| "cellsEqual (a#l) S subG = (case findCellEqual a S subG of None \<Rightarrow> False
       | Some (x,xl) \<Rightarrow> cellsEqual l xl subG)"

fun cellsEqualWithName where
"cellsEqualWithName a l [] subG = False"
| "cellsEqualWithName a l ((b,bl)#S) subG =
        (if a = b then cellsEqual l bl subG else cellsEqualWithName a l S subG)"

primrec userDefinedCellsEqual where
"userDefinedCellsEqual [] S subG = (if S = [] then True else False)"
| "userDefinedCellsEqual (a#l) S subG = (case a of (x,xl) \<Rightarrow>
       cellsEqualWithName x xl S subG \<and> userDefinedCellsEqual l S subG)"

definition cellEqualInLimitedSet where
"cellEqualInLimitedSet l B B' subG =
        userDefinedCellsEqual (findCellByNameList l B) (findCellByNameList l B') subG"

(* a version of update graph without focusing on names *)
primrec insertBagToList where
"insertBagToList subG B [] = [B]"
| "insertBagToList subG B (a#l) = (case syntacticMonoidInSUBag B a subG of None
     \<Rightarrow> a#(insertBagToList subG B l)
    | Some a' \<Rightarrow> (a'#l))"

fun insertPairToGraph where
"insertPairToGraph subG x y [] = [(x,[y])]"
| "insertPairToGraph subG x y ((a,al)#l) = (case syntacticMonoidInSUBag x a subG of None \<Rightarrow>
    (a,al)#(insertPairToGraph subG x y l)
   | Some a' \<Rightarrow> ((a',insertBagToList subG y al)#l))"

fun createEntry where
"createEntry subG x [] = [(x,[])]"
| "createEntry subG x ((a,al)#l) =
   (case syntacticMonoidInSUBag x a subG of None \<Rightarrow> ((a,al)#(createEntry subG x l))
   | Some a' \<Rightarrow> ((a',al)#l))"

definition updatePairInGraph where
"updatePairInGraph subG x y G =
        (insertPairToGraph subG x y (createEntry subG x G))"

primrec updateAllPairsInGraph where
"updateAllPairsInGraph subG x [] G = G"
| "updateAllPairsInGraph subG x (y#l) G =
       updateAllPairsInGraph subG x l (updatePairInGraph subG x y G)"

inductive oneTransKCtl where
zeroStep : "oneTransKCtl allFunRules database subG
            allKRules allBagRules transKRules tranBagRules Gl [] Gl"
| oneBagStep : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B');
    B \<noteq> B'; oneTransKCtl allFunRules database subG
            allKRules allBagRules transKRules transBagRules Gl l Gl' \<rbrakk>
     \<Longrightarrow> oneTransKCtl allFunRules database subG allKRules allBagRules
       transKRules transBagRules Gl (B#l) (updatePairInGraph subG B B' Gl')"
| oneKTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl acc;
  replaceKCellsInList B acc = Bl; oneTransKCtl allFunRules database subG allKRules allBagRules
      transKRules transBagRules Gl l Gl' \<rbrakk>
     \<Longrightarrow> oneTransKCtl allFunRules database subG allKRules allBagRules
      transKRules transBagRules Gl (B#l) (updateAllPairsInGraph subG B Bl Gl')"
| oneBagTrans : "\<lbrakk> oneStepBagRule allFunRules database subG allBagRules (Continue B) (Stop B);
   getAllKCells B = Some cl; oneTransKRule allFunRules database subG allKRules transKRules cl [];
  oneTransBagRule allFunRules database subG transBagRules B Bl;
  oneTransKCtl allFunRules database subG allKRules allBagRules transKRules
      transBagRules Gl l Gl' \<rbrakk>
     \<Longrightarrow> oneTransKCtl allFunRules database subG allKRules allBagRules
       transKRules transBagRules Gl (B#l) (updateAllPairsInGraph subG B Bl Gl')"

code_pred oneTransKCtl .

(* defining K CTL helper function *)
inductive kctlAux where
zeroStep : "allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl'
           \<Longrightarrow> kctlAux database subG (0::nat) allFunRules allAnywheres allKRules
            allBagRules transKRules transBagRules Gl Bl Gl"
| noStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKCtl allFunRules database subG allKRules allBagRules transKRules transBagRules
         Gl Bl' Gl \<rbrakk>
    \<Longrightarrow> kctlAux database subG n allFunRules allAnywheres allKRules allBagRules
      transKRules transBagRules Gl Bl Gl"
| oneStep : "\<lbrakk> allAllFunAnywhere allFunRules allAnywheres database subG Bl Bl';
    oneTransKCtl allFunRules database subG allKRules allBagRules transKRules transBagRules
           Gl Bl' Gl'; n > 0; Gl \<noteq> Gl';
    kctlAux database subG (n - 1) allFunRules allAnywheres allKRules allBagRules transKRules
      transBagRules Gl' Bl' Gl'' \<rbrakk>
    \<Longrightarrow> kctlAux database subG n allFunRules allAnywheres allKRules allBagRules
      transKRules transBagRules Gl Bl Gl''"

code_pred kctlAux .

(* defining CTL formula *)
datatype 'a ctlForm = TrueCtl
      | PredCtl 'a
      | NotCtl "'a ctlForm"
      | AndCtl "'a ctlForm" "'a ctlForm" 
      | EXCtl "'a ctlForm" | EACtl "'a ctlForm" | EUCtl "'a ctlForm" "'a ctlForm"


(* input a list of (cellName, pattern (in suBigKWithBag form)) pair, 
  kctl tries to find a substitution to match all patterns in the program state
   and return true if it is a such one *)
primrec findPatternInCell where
"findPatternInCell subG a [] acc = []"
| "findPatternInCell subG a (b#l) acc =
     (case patternMacroingInSUBigKWithBag a b acc subG of None \<Rightarrow> 
       findPatternInCell subG a l acc | Some acc' \<Rightarrow> 
       acc'#(findPatternInCell subG a l acc))"

primrec findPatternInCellWithList where
"findPatternInCellWithList subG a S [] = []"
| "findPatternInCellWithList subG a S (acc#l) =
     (findPatternInCell subG a S acc)@(findPatternInCellWithList subG a S l)"

fun patternMatchInCells where
"patternMatchInCells subG [] G accs = True"
| "patternMatchInCells subG ((s,a)#l) G accs =
    (case getValueTerm s G of None \<Rightarrow> False
        | Some bl \<Rightarrow>
      patternMatchInCells subG l G (findPatternInCellWithList subG a bl accs))"

definition ctlStateCheck where
"ctlStateCheck subG l G = (case l of [] \<Rightarrow> True
        | ((s,a)#l) \<Rightarrow> (case getValueTerm s G of None \<Rightarrow> False
        | Some bl \<Rightarrow> 
   patternMatchInCells subG l G (findPatternInCell subG a bl [])))"

primrec ctlStateCheckInList where
"ctlStateCheckInList subG l [] = []"
| "ctlStateCheckInList subG l (a#al) = (if ctlStateCheck subG l a then
    a#ctlStateCheckInList subG l al else ctlStateCheckInList subG l al)"

primrec minusList where
"minusList S [] = S"
| "minusList S (a#l) = (minusList (removeAll a S) l)"

primrec intersetList where
"intersetList A [] = []"
| "intersetList A (a#l) = (if a \<in> set A then a#(intersetList A l) else intersetList A l)"

primrec existInstance where
"existInstance [] G = False"
| "existInstance (a#l) G = (if a \<in> set G then True else existInstance l G)"

fun collectNextTrueState where
"collectNextTrueState [] G = []"
| "collectNextTrueState ((a,bl)#l) G = (if existInstance bl G then
     a#(collectNextTrueState l G) else collectNextTrueState l G)"

primrec euCheckFactor where
"euCheckFactor LS E T [] = (E,T)"
| "euCheckFactor LS E T (a#l) = (if (a \<in> set LS \<and> a \<notin> set T)
         then euCheckFactor LS (List.insert a E) (List.insert a T) l
          else euCheckFactor LS E T l)"

function euCheck where
"euCheck PG LS [] T = T"
| "euCheck PG LS (a#l) T = (case getValueTerm a PG of None \<Rightarrow> 
    euCheck PG LS l T | Some al \<Rightarrow> 
      (case euCheckFactor LS l T al of (E',T') \<Rightarrow> 
       euCheck PG LS E' T'))"
by pat_completeness auto

termination sorry

(* helper function to deal with EA formula *)
fun edgeNumsInGraph where
"edgeNumsInGraph [] = []"
| "edgeNumsInGraph ((a,b)#l) = (a,length b)#(edgeNumsInGraph l)"

fun updateNumGraph where
"updateNumGraph [] a = []"
| "updateNumGraph ((a,n)#l) b = (if a = b then ((a,n-1)#l)
                       else (a,n)#(updateNumGraph l b))"

fun eaCheckFactor where
"eaCheckFactor CS E T [] = (CS,E,T)"
| "eaCheckFactor CS E T (a#l) = (case getValueTerm a CS of None 
    \<Rightarrow> eaCheckFactor CS (List.insert a E) (minusList T [a]) l
   | Some n \<Rightarrow> (if n = 0 then
            eaCheckFactor CS (List.insert a E) (minusList T [a]) l
   else if a \<in> set T then eaCheckFactor (updateNumGraph CS a) E T l
        else eaCheckFactor CS E T l))"

function eaCheckAux where
"eaCheckAux CS PG [] T = T"
| "eaCheckAux CS PG (a#l) T =
      (case getValueTerm a PG of None \<Rightarrow> eaCheckAux CS PG l T
        | Some E' \<Rightarrow> (case eaCheckFactor CS l T E' of (CSa, Ea, Ta)
           \<Rightarrow> eaCheckAux CSa PG Ea Ta))"
by pat_completeness auto

termination sorry

primrec ctlModelCheck where
"ctlModelCheck subG Vs Gl PG TrueCtl = Vs"
| "ctlModelCheck subG Vs Gl PG (PredCtl l) = ctlStateCheckInList subG l Vs"
| "ctlModelCheck subG Vs Gl PG (NotCtl f) = minusList Vs (ctlModelCheck subG Vs Gl PG f)"
| "ctlModelCheck subG Vs Gl PG (AndCtl a b) =
     intersetList (ctlModelCheck subG Vs Gl PG a) (ctlModelCheck subG Vs Gl PG b)"
| "ctlModelCheck subG Vs Gl PG (EXCtl f) = collectNextTrueState Gl (ctlModelCheck subG Vs Gl PG f)"
| "ctlModelCheck subG Vs Gl PG (EUCtl a b) =
  (case (ctlModelCheck subG Vs Gl PG b) of E \<Rightarrow>
    euCheck PG (ctlModelCheck subG Vs Gl PG a) E E)"
| "ctlModelCheck subG Vs Gl PG (EACtl a) = (case ctlModelCheck subG Vs Gl PG a
       of news  \<Rightarrow> eaCheckAux (edgeNumsInGraph Gl) PG (minusList Vs news) news)"

(* calculate reverse graph of a given graph *)
primrec collectPairsAux where
"collectPairsAux a [] = []"
| "collectPairsAux a (b#l) = (a,b)#(collectPairsAux a l)"

fun collectPairs where
"collectPairs [] = []"
| "collectPairs ((a,al)#l) = (collectPairsAux a al)@(collectPairs l)"

fun reversePairs where
"reversePairs [] = []"
| "reversePairs ((a,b)#l) = (b,a)#(reversePairs l)"

fun getAllVertex where
"getAllVertex [] = []"
| "getAllVertex ((a,b)#l) = (List.insert a (List.insert b (getAllVertex l)))"

definition reverseGraph where
"reverseGraph G = (case reversePairs (collectPairs G) of pairs \<Rightarrow>
    formGraph (getAllVertex pairs) pairs)"

primrec getCaresList where
"getCaresList sl [] = []"
| "getCaresList sl (B#l) = (findCellByNameList sl B)#(getCaresList sl l)"

fun getCaresGraph where
"getCaresGraph sl [] = []"
| "getCaresGraph sl ((B,Bl)#l) = (findCellByNameList sl B,(getCaresList sl Bl))#(getCaresGraph sl l)"

inductive kctl where
theoryFail : "kcompile Theory = Failure s \<Longrightarrow>
      kctl Theory n l names f (Failure (''Bad result: ''@s))"
| programFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG, confi, allRules);
   realConfigurationTest l Theory database subG = None \<rbrakk>
   \<Longrightarrow> kctl Theory n l names f (Failure ''Bad input program.'')"
| macroRuleFail : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
   applyAllMacroRulesCheck l Theory database subG = None \<rbrakk>
   \<Longrightarrow> kctl Theory n l names f (Failure ''Macro rules have a problem.'')"
| goodRun : "\<lbrakk> kcompile Theory = Success (Theory, database, subG,confi, allRules);
      applyAllMacroRulesCheck l Theory database subG = Some (noMacroRules, B);
    getFunRules noMacroRules = allFunRules; getAnywhereRules noMacroRules = allAnywheres;
    divideAllKRules noMacroRules = (transKRules,allKRules);
     divideAllBagRules noMacroRules = (transBagRules,allBagRules);
     kctlAux database subG n allFunRules allAnywheres allKRules
                  allBagRules transKRules transBagRules [(B,[B])] [B] Gl;
      getCaresGraph names Gl = CGl; getAllVertex (collectPairs CGl) = Vs; reverseGraph CGl = PG;
     ctlModelCheck subG Vs CGl PG f = Rs ; findCellByNameList names B = CB \<rbrakk>
\<Longrightarrow> kctl Theory n l names f (Success (CB \<in> set Rs))"

code_pred kctl .

export_code kctl
  in OCaml
  module_name Kctl file "kctl.ml"

end