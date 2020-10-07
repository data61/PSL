section "Completeness"

theory Completeness
imports Tree Sequents
begin


subsection "pseq: type represents a processed sequent"

type_synonym "atom"  = "(signs * predicate * vbl list)"
type_synonym nform = "(nat * formula)"
type_synonym pseq  = "(atom list * nform list)"

definition
  sequent :: "pseq => formula list" where
  "sequent = (%(atoms,nforms) . map snd nforms @ map (% (z,p,vs) . FAtom z p vs) atoms)"

definition
  pseq :: "formula list => pseq" where
  "pseq fs = ([],map (%f.(0,f)) fs)"

definition atoms :: "pseq => atom list" where "atoms = fst"
definition nforms :: "pseq => nform list" where "nforms = snd"


subsection "subs: SATAxiom"

definition
  SATAxiom :: "formula list => bool" where
  "SATAxiom fs \<longleftrightarrow> (? n vs . FAtom Pos n vs : set fs & FAtom Neg n vs : set fs)"


subsection "subs: a CutFreePC justifiable backwards proof step"

definition
  subsFAtom :: "[atom list,(nat * formula) list,signs,predicate,vbl list] => pseq set" where
  "subsFAtom atms nAs z P vs = { ((z,P,vs)#atms,nAs) }"

definition
  subsFConj :: "[atom list,(nat * formula) list,signs,formula,formula] => pseq set" where
  "subsFConj atms nAs z A0 A1 =
    (case z of
      Pos => { (atms,(0,A0)#nAs),(atms,(0,A1)#nAs) }
    | Neg => { (atms,(0,A0)#(0,A1)#nAs) })"

definition
  subsFAll :: "[atom list,(nat * formula) list,nat,signs,formula,vbl set] => pseq set" where
  "subsFAll atms nAs n z A frees =
    (case z of
      Pos => { let v = freshVar frees in  (atms,(0,instanceF v A)#nAs) }
    | Neg => { (atms,(0,instanceF (X n) A)#nAs @ [(Suc n,FAll Neg A)]) })"
    
definition
  subs :: "pseq => pseq set" where
  "subs = (% pseq .
             if SATAxiom (sequent pseq) then
                 {}
             else let (atms,nforms) = pseq
                  in  case nforms of
                         []     => {}
                       | nA#nAs => let (n,A) = nA
                                   in  (case A of
                                            FAtom z P vs  => subsFAtom atms nAs z P vs
                                          | FConj z A0 A1 => subsFConj atms nAs z A0 A1
                                          | FAll  z A     => subsFAll  atms nAs n z A (freeVarsFL (sequent pseq))))"


subsection "proofTree(Gamma) says whether tree(Gamma) is a proof"

definition
  proofTree :: "(nat * pseq) set => bool" where
  "proofTree A \<longleftrightarrow> bounded A & founded subs (SATAxiom o sequent) A"


subsection "path: considers, contains, costBarrier"

definition
  considers :: "[nat => pseq,nat * formula,nat] => bool" where
  "considers f nA n = (case (snd (f n)) of [] => False | x#xs => x=nA)"

definition
  "contains" :: "[nat => pseq,nat * formula,nat] => bool" where
  "contains f nA n \<longleftrightarrow> nA : set (snd (f n))"

definition
  costBarrier :: "[nat * formula,pseq] => nat" where
    (******
     costBarrier justifies: eventually contains ==> eventually considers
     with a termination thm, (barrier strictly decreases in |N).
     ******)
  "costBarrier nA = (%(atms,nAs).
    let barrier = takeWhile (%x. nA ~= x) nAs
    in  let costs = map (exp 3 o size o snd) barrier
    in  sumList costs)"


subsection "path: eventually"

(******
 Could do this with composable temporal operators, but following paper proof first.
 ******)

definition
  EV :: "[nat => bool] => bool" where
  "EV f == (? n . f n)"
        (****** 
         This allows blast_tac like searching to be done without hassle
         of removing exists rules. (hopefully).
         ******)


subsection "path: counter model"

definition
  counterM :: "(nat => pseq) => object set" where
  "counterM f = range obj"

definition
  counterEvalP :: "(nat => pseq) => predicate => object list => bool" where
  "counterEvalP f = (%p args . ! i . ~(EV (contains f (i,FAtom Pos p (map (X o inv obj) args)))))"

definition
  counterModel :: "(nat => pseq) => model" where
  "counterModel f = Abs_model (counterM f, counterEvalP f)"


primrec counterAssign :: "vbl => object"
where "counterAssign (X n) = obj n"  (* just deX *)


subsection "subs: finite"
  
lemma finite_subs: "finite (subs gamma)"
  apply(simp add: subs_def subsFAtom_def subsFConj_def subsFAll_def Let_def split_beta split: if_splits list.split formula.split signs.split)
  done

lemma fansSubs: "fans subs"
  apply(rule fansI) apply(rule, rule finite_subs) done

lemma subs_def2:  
"!!gamma.
   ~ SATAxiom (sequent gamma) ==> 
   subs gamma = (case nforms gamma of 
                     []     => {} 
                   | nA#nAs => let (n,A) = nA 
                               in  (case A of 
                                        FAtom z P vs  => subsFAtom (atoms gamma) nAs z P vs 
                                      | FConj z A0 A1 => subsFConj (atoms gamma) nAs z A0 A1 
                                      | FAll  z A     => subsFAll  (atoms gamma) nAs n z A (freeVarsFL (sequent gamma))))"
  apply(simp add: subs_def Let_def nforms_def atoms_def split_beta split: list.split)
  done


subsection "inherited: proofTree"

lemma proofTree_def2: "proofTree = ( % x . bounded x & founded subs (SATAxiom o sequent) x)"
  apply(rule ext)
  apply(simp add: proofTree_def) done

lemma inheritedProofTree: "inherited subs proofTree"
  apply(simp add: proofTree_def2)
  apply(auto intro: inheritedJoinI inheritedBounded inheritedFounded)
  done

lemma proofTreeI: "[| bounded A; founded subs (SATAxiom o sequent) A |] ==> proofTree A"
  apply(simp add: proofTree_def) done

lemma proofTreeBounded: "proofTree A ==> bounded A"
  apply(simp add: proofTree_def) done

lemma proofTreeTerminal: "proofTree A ==> (n,delta) : A ==> terminal subs delta ==> SATAxiom (sequent delta)"
  apply(simp add: proofTree_def founded_def) apply blast done


subsection "pseq: lemma"

lemma snd_o_Pair: "(snd o (Pair x)) = (% x. x)"
  apply(rule ext) 
  by simp

lemma sequent_pseq: "sequent (pseq fs) = fs"
  by (simp add: pseq_def sequent_def snd_o_Pair)

subsection "SATAxiom: proofTree"
    
lemma SATAxiomTerminal[rule_format]: "SATAxiom (sequent gamma) --> terminal subs gamma"
  apply(simp add: subs_def proofTree_def terminal_def founded_def bounded_def)
  done

lemma SATAxiomBounded:"SATAxiom (sequent gamma) ==> bounded (tree subs gamma)"
  apply(frule SATAxiomTerminal)
  apply(subst treeEquation)
  apply(simp add: subs_def proofTree_def terminal_def founded_def bounded_def)
  apply(force simp add: boundedByInsert boundedByEmpty)
  done

lemma SATAxiomFounded: "SATAxiom (sequent gamma) ==> founded subs (SATAxiom o sequent) (tree subs gamma)"
  apply(frule SATAxiomTerminal)
  apply(subst treeEquation)
  apply(simp add: subs_def proofTree_def terminal_def founded_def bounded_def)
  done

lemma SATAxiomProofTree[rule_format]: "SATAxiom (sequent gamma) --> proofTree (tree subs gamma)"
  apply(blast intro: proofTreeI SATAxiomBounded SATAxiomFounded)
  done

lemma SATAxiomEq: "(proofTree (tree subs gamma) & terminal subs gamma) = SATAxiom (sequent gamma)"
  apply(blast intro: SATAxiomProofTree proofTreeTerminal tree.tree0  SATAxiomTerminal)
  done
    \<comment> \<open>FIXME tjr blast sensitive to obj imp vs meta imp for pTT\<close>


subsection "SATAxioms are deductions: - needed"

lemma SAT_deduction: "SATAxiom x ==> x : deductions CutFreePC"
  apply(simp add: SATAxiom_def)
  apply(elim exE)
  apply(rule_tac x="[FAtom Pos n vs,FAtom Neg n vs]" in inDed_mono)
   apply (blast intro!: SATAxiomI rulesInPCs, force)
  done
  

subsection "proofTrees are deductions: subs respects rules - messy start and end"

lemma subsJustified': 
  notes ss = subs_def2 nforms_def Let_def atoms_def sequent_def subsFAtom_def subsFConj_def subsFAll_def
  shows "\<not> SATAxiom (sequent (ats, (n, f) # list)) --> \<not> terminal subs (ats, (n, f) # list) 
  --> (\<forall>sigma\<in>subs (ats, (n, f) # list). sequent sigma \<in> deductions CutFreePC) 
  --> sequent (ats, (n, f) # list) \<in> deductions CutFreePC"
  apply (rule_tac A=f in formula_signs_cases, clarify) apply(simp add: ss)
       apply(rule PermI) apply assumption apply(rule perm_append_Cons) apply (rule rulesInPCs, clarify) apply(simp add: ss)
      apply(rule PermI) apply assumption apply(rule perm_append_Cons) apply (rule rulesInPCs, clarify) apply(simp add: ss) apply(elim conjE)
     apply(rule ConjI') apply assumption apply assumption apply(rule rulesInPCs)+
    apply clarify apply(simp add: ss)
    apply(rule DisjI) apply assumption apply(rule rulesInPCs)+
   apply clarify apply(simp add: ss)
   apply(rule AllI) apply assumption apply(rule finiteFreshVar) apply(rule finite_freeVarsFL) apply (rule rulesInPCs, clarify) apply(simp add: ss)
  apply(rule ContrI) \<comment> \<open>!\<close>
  apply(rule_tac w = "X n" in ExI) apply(rule inDed_mono) apply assumption apply force apply(rule rulesInPCs)+
  done

lemma subsJustified: "!! gamma. ~ terminal subs gamma
  ==> ! sigma : subs gamma . sequent sigma : deductions (CutFreePC)
  ==> sequent gamma : deductions (CutFreePC)"
  apply(case_tac "SATAxiom (sequent gamma)")
   apply(erule SAT_deduction)
  apply(case_tac gamma) apply(rename_tac ats nfs)
  apply(case_tac nfs)
   apply(simp add: terminal_def subs_def sequent_def Let_def)
  apply(case_tac a)
   apply(blast intro: subsJustified'[rule_format])
  done


subsection "proofTrees are deductions: instance of boundedTreeInduction"

lemmas proofTreeD = proofTree_def [THEN iffD1]

lemma proofTreeDeductionD[rule_format]: "proofTree(tree subs gamma) \<Longrightarrow> sequent gamma : deductions (CutFreePC)"
  apply(rule boundedTreeInduction[OF fansSubs]) 
    apply(erule proofTreeBounded)
   apply(rule foundedMono) 
    apply (force dest: proofTreeD, simp) 
   apply(blast intro: SAT_deduction foundedMono subsJustified) 
  apply(blast intro:  subsJustified)
  done


subsection "contains, considers:"

lemma contains_def2: "contains f iA n = (iA : set (nforms (f n)))"
  apply(simp add: contains_def nforms_def) done

lemma considers_def2: "considers f iA n = ( ? nAs . nforms (f n) = iA#nAs)"
  apply(simp add: considers_def nforms_def split: list.split) done

lemmas containsI = contains_def2[THEN iffD2]


subsection "path: nforms = [] implies"

lemma nformsNoContains: "[| branch subs gamma f; !n . ~proofTree (tree subs (f n)); nforms (f n) = []  |] ==> ~ contains f iA n"
  apply(simp add: contains_def2) done
    \<comment> \<open>FIXME tjr assumptions not required\<close>

lemma nformsTerminal: "nforms (f n) = [] ==> terminal subs (f n)"
  apply(simp add: subs_def Let_def terminal_def nforms_def split_beta)
  done

lemma nformsStops: "!!f.
  [| branch subs gamma f; !n . ~proofTree (tree subs (f n));
     nforms (f n) = [] |]
  ==> nforms (f (Suc n)) = [] & atoms (f (Suc n)) = atoms (f n)"
  apply(subgoal_tac "f (Suc n) = f n")
  apply simp
  apply(blast intro: branchStops nformsTerminal)
  done


subsection "path: cases"

lemma terminalNFormCases: "!!f. terminal subs (f n) | (? i A nAs . nforms (f n) = (i,A)#nAs)"
  apply (rule disjCI, simp)
  apply(rule nformsTerminal)
  apply(case_tac "nforms (f n)")
  apply simp
  apply force
  done

lemma cases[elim_format]: "terminal subs (f n) | (\<not> (terminal subs (f n) \<and> (? i A nAs . nforms (f n) = (i,A)#nAs)))"
  apply(auto elim: terminalNFormCases[elim_format])
  done


subsection "path: contains not terminal and propagate condition"
    
lemma containsNotTerminal: "[| branch subs gamma f; !n . ~proofTree (tree subs (f n)); contains f iA n |] ==> ~ (terminal subs (f n))"
  apply(case_tac "SATAxiom (sequent (f n))")
  apply(blast dest: SATAxiomEq[THEN iffD2])
  apply(drule_tac x=n in spec)
  apply (simp add:  subs_def subs_def subsFAtom_def subsFConj_def subsFAll_def Let_def contains_def terminal_def nforms_def split_beta branch_def split: list.split signs.split expand_case_formula, force)
  done

lemma containsPropagates: "!!f.
  [| branch subs gamma f; !n . ~proofTree (tree subs (f n));
     contains f iA n |]
  ==> contains f iA (Suc n) | considers f iA n"
  apply(frule_tac containsNotTerminal) apply force apply force
  apply(frule_tac branchSubs) apply assumption
  apply(case_tac "considers f iA n") apply simp
  apply simp
  apply(simp add: contains_def) apply(case_tac "f n") apply simp apply(drule split_list) apply(elim exE conjE) apply simp
  apply(case_tac ys)
   apply (simp add: considers_def, simp)
  apply(case_tac "SATAxiom (sequent (f n))") apply(blast dest: iffD2[OF SATAxiomEq])
  apply(simp add: subs_def2 nforms_def Let_def)
  apply (case_tac aa, simp)
  apply(case_tac ba)
    apply(simp add: subsFAtom_def)
   apply(rename_tac signs a b)
   apply(case_tac signs) apply(simp add: subsFConj_def) apply force apply(simp add: subsFConj_def)
  apply(rename_tac signs a)
  apply(case_tac signs) apply(simp add: subsFAll_def Let_def) apply(simp add: subsFAll_def Let_def)
  done


subsection "path: no consider lemmas"

lemma noConsidersD: "!!f. ~considers f iA n ==> nforms (f n) = x#xs ==> iA ~= x"
  by(simp add: considers_def2)

lemma considersD: "!!f. considers f iA n ==> ? xs . nforms (f n) = iA#xs"
  by(simp add: considers_def2)


subsection "path: contains initially"

lemma contains_initially: 
  "branch subs (pseq gamma) f \<Longrightarrow> A : set gamma \<Longrightarrow> (contains f (0,A) 0)"
  apply(drule branch0)
  apply(simp add: contains_def pseq_def) done

lemma contains_initialEVs: 
  "branch subs (pseq gamma) f \<Longrightarrow>  A : set gamma \<Longrightarrow> EV (contains f (0,A))"
  apply(simp add: EV_def)
  apply(fast dest: contains_initially) done


subsection "termination: (for EV contains implies EV considers)"

lemmas r = wf_induct[of "measure msrFn", OF wf_measure] for msrFn
lemmas r' = r[simplified measure_def inv_image_def less_than_def less_eq mem_Collect_eq]

lemma r'': "(\<forall> x. (\<forall> y. ( ((msrFn::'a \<Rightarrow> nat) y) < ((msrFn :: 'a \<Rightarrow> nat) x)) \<longrightarrow> P y) \<longrightarrow> P x) \<Longrightarrow> P a"
  by (blast intro: r' [of _ P])

lemma terminationRule [rule_format]:
  "! n. P n --> (~(P (Suc n)) | (P (Suc n) & msrFn (Suc n) < (msrFn::nat => nat) n)) ==> P m --> (? n . P n & ~(P (Suc n)))"
  (is "_ \<Longrightarrow> ?P m") 
  apply (rule r''[of msrFn "?P" m], blast)
  done
    \<comment> \<open>FIXME ugly\<close>


subsection "costBarrier: lemmas"

subsection "costBarrier: exp3 lemmas - bit specific..."

lemma exp3Min: "exp 3 a > 0"
by (induct a, simp, simp)

lemma exp1: "exp 3 (A) + exp 3 (B) < 3 * ((exp 3 A) * (exp 3 B))" 
  using exp3Min[of A] exp3Min[of B] 
  apply(case_tac "exp 3 A") apply(simp add: exp3Min)
  apply(case_tac "exp 3 B") apply (simp add: exp3Min, simp)
  done

lemma exp1': "exp 3 (A) < 3 * ((exp 3 A) * (exp 3 B)) + C"
  apply(subgoal_tac "exp 3 (A) < 3 * ((exp 3 A) * (exp 3 B))")
  apply arith
  apply(case_tac "exp 3 A") using exp3Min[of A] apply arith 
  apply(case_tac "exp 3 B") using exp3Min[of B] apply arith 
  apply simp
  done

lemma exp2: "Suc 0 < 3 * exp 3 (B)" 
  using exp3Min[of B] 
  apply arith
  done

lemma expSum: "exp x (a+b) = (exp x a) * (exp x b)"
  apply(induct a, auto) done


subsection "costBarrier: decreases whilst contains and unconsiders"

lemma costBarrierDecreases':
  notes ss = subs_def2 nforms_def Let_def subsFAtom_def subsFConj_def subsFAll_def costBarrier_def atoms_def exp3Min expSum
  shows "~SATAxiom (sequent 
(a, (num,fm) # list)) --> iA ~= (num, fm) --> \<not> proofTree (tree subs (a, (num, fm) # list)) --> fSucn : subs (a, (num, fm) # list) --> iA \<in> set list --> costBarrier iA (fSucn) < costBarrier iA (a, (num, fm) # list)"
  apply(rule_tac A=fm in formula_signs_cases)
    \<comment> \<open>atoms\<close>
       apply(simp add: ss)
      apply(simp add: ss)
        \<comment> \<open>conj\<close>
     apply clarify
     apply(simp add: ss)
     apply(erule disjE)
      apply(simp add: ss exp2)
     apply(simp add: ss exp2)
    \<comment> \<open>disj\<close>
    apply clarify
    apply(simp add: ss exp1 exp1')
    \<comment> \<open>all\<close>
   apply clarify
   apply(simp add: ss size_instance)
  \<comment> \<open>ex\<close>
  apply clarify
  apply(simp add: ss size_instance)
  done

lemma costBarrierDecreases: 
  "[| branch subs gamma f;
  !n . ~proofTree (tree subs (f n));
  contains f iA n;
  ~(considers f iA) n
  |] ==> costBarrier iA (f (Suc n)) < costBarrier iA (f n)"
  apply(subgoal_tac "\<not> terminal subs (f n)")
   apply(subgoal_tac "\<not> SATAxiom (sequent (f n))")
    apply(subgoal_tac "f (Suc n) \<in> subs (f n)")
     apply(frule_tac x=n in spec)
     apply(case_tac "f n", simp)
     apply(case_tac b, simp)
      apply(simp add: contains_def)
     apply(case_tac aa) apply(rename_tac num fm) apply simp apply(simp add: contains_def considers_def)
     apply(rule costBarrierDecreases'[rule_format]) apply force+
    apply(rule branchSubs) apply assumption apply assumption
   apply(blast dest: SATAxiomTerminal)
  apply(blast dest: containsNotTerminal)
  done
  \<comment> \<open>FIXME boring splitting etc.\<close>


subsection "path: EV contains implies EV considers"

lemma considersContains: "considers f iA n \<Longrightarrow> contains f iA n"
  apply(simp add: considers_def contains_def)
  apply(cases "snd (f n)", auto) done

lemma containsConsiders: "[| branch subs gamma f; !n . ~ proofTree (tree subs (f n));
     EV (contains f iA) |]
  ==> EV (considers f iA)"
  apply(simp add: EV_def)
  apply(erule exE)
  apply(case_tac "considers f iA n") apply force
  apply(subgoal_tac "\<exists>n. (contains f iA n \<and> \<not> considers f iA n) \<and>
    \<not> (contains f iA (Suc n) \<and> \<not> considers f iA (Suc n))")
   apply(erule exE) 
   apply(simp, clarify)
   apply(case_tac "contains f iA (Suc na)")
    apply force apply(force dest!: containsPropagates)
  apply(rule_tac msrFn = "%n. costBarrier iA (f n)" and P = "%n. contains f iA n & ~ considers f iA n" in terminationRule)
  prefer 2 apply force
  apply(case_tac "(contains f iA (Suc na) \<and> \<not> considers f iA (Suc na))")
  apply simp apply(erule costBarrierDecreases) apply simp_all
  done



subsection "EV contains: common lemma"

lemma lemmA: 
  "[| branch subs gamma f; ! n. ~ proofTree (tree subs (f n));
    EV (contains f (i,A)) |]
 ==> ? n nAs. ~SATAxiom (sequent (f n)) & (nforms (f n) = (i,A) # nAs & f (Suc n) : subs (f n))"
  apply(frule containsConsiders) apply(assumption+)
  apply(unfold EV_def)
  apply(erule exE, frule considersContains)
  apply(unfold considers_def)
  apply(case_tac "snd (f n)") 
  apply force
  apply simp
  apply(rule_tac x=n in exI)
  apply (intro conjI, rule)
  apply(blast dest!: SATAxiomEq[THEN iffD2])
  apply(rule_tac x=list in exI) apply(simp add: nforms_def)
  apply(frule containsNotTerminal) apply force apply(assumption+)
  apply(blast dest!: branchSubs)
  done


subsection "EV contains: FConj,FDisj,FAll"

lemma EV_disj: "(EV P | EV Q) = EV (\<lambda>n. P n | Q n)"
  apply (unfold EV_def, force) done

lemma evContainsConj: "[| EV (contains f (i,FConj Pos A0 A1)); 
  branch subs gamma f; !n . ~ proofTree (tree subs (f n))
  |] ==> EV (contains f (0,A0)) | EV (contains f (0,A1))"
  apply(drule lemmA) apply(assumption+)
  apply(subgoal_tac "EV (\<lambda> n. contains f (0,A0) n | contains f (0,A1) n)")
  apply(simp add: EV_disj)
  apply(unfold EV_def)
  apply clarify
  apply(rename_tac n n' nAs, rule_tac x="Suc n'" in exI)
  apply(simp add: subs_def2 Let_def)
  apply(simp add: subsFConj_def)
  apply (simp add: contains_def nforms_def, auto) 
  done

lemma evContainsDisj: "[| EV (contains f (i,FConj Neg A0 A1)); 
  branch subs gamma f; !n . ~ proofTree (tree subs (f n))
  |] ==> EV (contains f (0,A0)) & EV (contains f (0,A1))"
  apply(drule lemmA) apply(assumption+)
  apply(rule conjI)
  apply(unfold EV_def)
  apply(erule exE) back 
  apply(rule_tac x="Suc n" in exI)
  apply(clarify, simp add: subs_def2 Let_def)
  apply(simp add: subsFConj_def)
  apply(simp add: contains_def nforms_def)
  apply(erule exE) back 
  apply(rule_tac x="Suc n" in exI)
  apply(clarify, simp add: subs_def2 Let_def)
  apply(simp add: subsFConj_def)
  apply(simp add: contains_def nforms_def)
  done
    
lemma evContainsAll: 
  "[| EV (contains f (i,FAll Pos body)); branch subs gamma f; !n . ~ proofTree (tree subs (f n))
     |]
   ==> ? v . EV (contains f (0,instanceF v body))"
  apply(drule lemmA) apply(assumption+)
  apply(erule exE) 
  apply(rule_tac x="freshVar(freeVarsFL (sequent (f n)))" in exI)
  apply(unfold EV_def)
  apply(rule_tac x="Suc n" in exI)
  apply(clarify, simp add: subs_def2 Let_def)
  apply(simp add: subsFAll_def Let_def)
  apply(simp add: contains_def nforms_def)
  done
    
lemma evContainsEx_instance: 
  "[| EV (contains f (i,FAll Neg body)); branch subs gamma f; !n . ~ proofTree (tree subs (f n))
      |]
  ==> EV (contains f (0,instanceF (X i) body))"
  apply(drule lemmA) apply(assumption+)
  apply(erule exE) 
  apply(unfold EV_def)
  apply(rule_tac x="Suc n" in exI)
  apply(clarify, simp add: subs_def2 Let_def)
  apply(simp add: subsFAll_def Let_def)
  apply(simp add: contains_def nforms_def)
  done

lemma evContainsEx_repeat: "
  [| branch subs gamma f; !n . ~ proofTree (tree subs (f n));
     EV (contains f (i,FAll Neg body)) |]
   ==> EV (contains f (Suc i,FAll Neg body))"
  apply(drule lemmA) apply(assumption+)
  apply(erule exE) 
  apply(unfold EV_def)
  apply(rule_tac x="Suc n" in exI)
  apply(clarify, simp add: subs_def2 Let_def)
  apply(simp add: subsFAll_def Let_def)
  apply(simp add: contains_def nforms_def)
  done


subsection "EV contains: lemmas (temporal related)"

(******
 Should have abstracted to have temporal ops:
    EV   : (nat -> bool) -> nat -> bool
    AW   : (nat -> bool) -> nat -> bool
    NEXT : (nat -> bool) -> nat -> bool
 then require:
    EV P and EV B imp (\n. A n & B n)

 already think have done similar proofs to this one elsewhere,
 Q: where? share proofs?
 ******)

lemma lemma1: "[| P A n ; !A n. P A n --> P A (Suc n) |]
   ==> P A (n + m)"
  apply (induct m, simp, simp)
  done

lemma lemma2: 
  "[| P A n ; P B m ; ! A n. P A n --> P A (Suc n) |]
  ==> ? n . P A n & P B n"
  apply (rule exI[of _ "n+m"], rule)
  apply(blast intro!: lemma1)
  apply(rule subst[OF add.commute]) 
  apply(blast intro!: lemma1)
  done


subsection "EV contains: FAtoms"

lemma notTerminalNotSATAxiom: "\<not> terminal subs gamma \<Longrightarrow> \<not> SATAxiom (sequent gamma)"
  apply(erule contrapos_nn) apply(erule SATAxiomTerminal) done

lemma notTerminalNforms: "\<not> terminal subs (f n) \<Longrightarrow> nforms (f n) \<noteq> []"
  apply(erule contrapos_nn) apply(erule nformsTerminal) done
    
lemma atomsPropagate: "[| branch subs gamma f |]
   ==> x : set (atoms (f n)) --> x : set (atoms (f (Suc n)))"
  apply(cases "terminal subs (f n)")
   apply(drule branchStops) apply assumption apply simp
  apply(drule branchSubs) apply assumption
  apply rule apply(frule notTerminalNotSATAxiom)
  apply(frule notTerminalNforms)
  apply(simp add: subs_def2) 
  apply(cases "nforms (f n)") apply simp
  apply(simp add: Let_def)
  apply(case_tac a, auto)
  apply(case_tac ba, auto)
    apply(simp add: subsFAtom_def atoms_def)
   apply(simp add: subsFConj_def atoms_def)
   apply(rename_tac signs a b)
   apply(case_tac signs) apply force apply force
  apply(simp add: subsFAll_def atoms_def)
  apply(rename_tac signs a)
  apply(case_tac signs) apply(force simp: Let_def) apply force
  done


subsection "EV contains: FEx cases"

lemma evContainsEx0_allRepeats: 
  "[| branch subs gamma f; !n . ~ proofTree (tree subs (f n));
     EV (contains f (0,FAll Neg A)) |]
  ==> EV (contains f (i,FAll Neg A))"
  apply (induct i, simp)
  apply(blast dest!: evContainsEx_repeat)
  done

lemma evContainsEx0_allInstances:
  "[| branch subs gamma f; !n . ~ proofTree (tree subs (f n));
     EV (contains f (0,FAll Neg A)) |]
  ==> EV (contains f (0,instanceF (X i) A))"
  apply(blast dest!: evContainsEx0_allRepeats intro!: evContainsEx_instance)
  done

subsection "pseq: creates initial pseq"
    
lemma containsPSeq0D: "branch subs (pseq fs) f \<Longrightarrow> contains f (i,A) 0 \<Longrightarrow> i=0"
  apply(drule branch0)
  apply (simp add: pseq_def contains_def, blast)
  done


subsection "EV contains: contain any (i,FEx y) means contain all (i,FEx y)"
    
(******
 Now, show (Suc i,FEx v A) present means (i,FEx v A) present (or at start).
 Assumes initial pseq contains only (0,form) pairs.
 ------
 Show that only way of introducing a (Suc i,FEx_) was from (i,FEx_).
 contains n == considers n or contains n+.

 Want to find the point where it was introduced.
 Have, P true all n or fails at 0 or for a (first) successor.

     (!n. P n) | (~P 0) | (P n & ~ P (Suc n))

 Instance this with P n = ~(contains ..FEx.. n).
 ******)

lemma claim: "(A | B | C) = (~C --> ~B --> A)" by auto

lemma natPredCases: "(!n. P n) | (~P 0) | (? n . P n & ~ P (Suc n))"
  apply(rule claim[THEN iffD2])
  apply(intro impI) apply simp
  apply rule apply(induct_tac n) apply auto
  done

lemma containsNotTerminal': 
  "\<lbrakk> branch subs gamma f; !n . ~proofTree (tree subs (f n)); contains f iA n \<rbrakk> \<Longrightarrow> ~ (terminal subs (f n))"
  apply (rule containsNotTerminal, auto)
  done

lemma notTerminalSucNotTerminal: "\<lbrakk> \<not> terminal subs (f (Suc n)); branch subs gamma f \<rbrakk> \<Longrightarrow> \<not> terminal subs (f n)"
  apply(erule contrapos_nn)
  apply(rule_tac branchTerminalPropagates[of _ _ _ _ 1, simplified])
  apply(assumption+) done
    \<comment> \<open>FIXME move to Tree?\<close>

lemma evContainsExSuc_containsEx:
  "[| branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n));
     EV (contains f (Suc i,FAll Neg body)) |]
  ==> EV (contains f (i,FAll Neg body))"
  apply(cut_tac P="%n. ~ contains f (Suc i,FAll Neg body) n" in natPredCases)
  apply simp apply(erule disjE)
  apply(simp add: EV_def)
  apply(erule disjE)
  apply(blast dest!: containsPSeq0D)
  apply(thin_tac "EV _")
  apply(erule exE) 
  apply(erule conjE)
  apply(unfold EV_def) apply(rule_tac x=n in exI)
  apply(rule considersContains)
  apply(frule containsNotTerminal') apply(assumption+)
  apply(frule notTerminalSucNotTerminal) apply assumption
  apply(thin_tac "\<not> terminal x y" for x y)
  apply(frule branchSubs) apply assumption
  apply(frule notTerminalNforms)
  apply(case_tac "SATAxiom (sequent (f n))")
  apply(drule SATAxiomTerminal) apply simp
  apply(subgoal_tac "(\<exists>i A nAs. nforms (f n) = (i, A) # nAs)")
  prefer 2 apply(rule_tac f=f and n=n in cases) apply simp
  apply(case_tac "nforms (f n)") apply simp apply(case_tac a, force)
  apply(erule exE)+
  apply(unfold considers_def) apply(simp add: nforms_def)
  \<comment> \<open>shift A into succedent\<close>
  apply(rule_tac P="snd (f n) = (ia, A) # nAs" in rev_mp) apply assumption apply(thin_tac "snd (f n) = (ia, A) # nAs")
  apply(rule_tac A=A in formula_signs_cases)
  apply(auto simp add: subs_def2 nforms_def Let_def subsFAtom_def subsFConj_def subsFAll_def contains_def2 Let_def)
  done
    \<comment> \<open>phew, bit precarious, but not too much going on besides unfolding defns. and computing a bit. Need to set simps up\<close>


subsection "EV contains: contain any (i,FEx y) means contain all (i,FEx y)"

lemma evContainsEx_containsEx0: 
  "[| branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n)) |]
  ==> EV (contains f (i,FAll Neg A)) -->
      EV (contains f (0,FAll Neg A))"
  apply (induct i, simp)
  apply(blast dest!: evContainsExSuc_containsEx)
  done

lemma evContainsExval: 
  "[| EV (contains f (i,FAll Neg body)); branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n))
  |] 
  ==> ! v . EV (contains f (0,instanceF v body))"
  apply rule apply(induct_tac v) 
  apply(blast intro!: evContainsEx0_allInstances dest!: evContainsEx_containsEx0)
  done


subsection "EV contains: atoms"

lemma atomsInSequentI[rule_format]: "  (z,P,vs) : set (fst ps) -->
     FAtom z P vs : set (sequent ps)"
  apply(simp add: sequent_def)
  apply(cases ps, force)
  done
    
lemma evContainsAtom1: 
  "[| branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n));
     EV (contains f (i,FAtom z P vs)) |]
  ==> ? n . (z,P,vs) : set (fst (f n))"
  apply(drule lemmA) apply(assumption+)
  apply(erule exE) apply(rule_tac x="Suc n" in exI)
  apply(simp add: subs_def2) apply clarify apply(simp add: subs_def2 Let_def)
  apply(simp add: subsFAtom_def) done
    
lemmas atomsPropagate'' = atomsPropagate[rule_format]
lemmas atomsPropagate' = atomsPropagate''[simplified atoms_def, simplified]

lemma evContainsAtom: 
  "[| branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n));
   EV (contains f (i,FAtom z P vs)) |]
  ==> ? n . (! m . FAtom z P vs : set (sequent (f (n + m))))"
  apply(frule evContainsAtom1) apply(assumption+)
  apply(erule exE)
  apply (rule_tac x=n in exI, rule)
  apply(rule atomsInSequentI)
  apply (induct_tac m, simp, simp)
  apply(rule atomsPropagate') apply(assumption+) done

lemma notEvContainsBothAtoms: 
  "[| branch subs (pseq fs) f; !n . ~ proofTree (tree subs (f n)) |]
  ==> ~ EV (contains f (i,FAtom Pos p vs)) |
      ~ EV (contains f (j,FAtom Neg p vs))"
  apply clarify
  apply(frule evContainsAtom) apply(assumption+) apply(thin_tac "EV (contains f (j, FAtom Neg p vs))")
  apply(frule evContainsAtom) apply(assumption+) apply(thin_tac "EV (contains f (i, FAtom Pos p vs))")
  apply(erule_tac exE)+
  apply(drule_tac x=na in spec) back
  apply(drule_tac x=n in spec) back
  apply(simp add: ac_simps)
  apply(subgoal_tac "SATAxiom (sequent (f (n+na)))")
  apply(force dest: SATAxiomProofTree)
  apply(force simp add: SATAxiom_def) done
    

subsection "counterModel: lemmas"
  
lemma counterModelInRepn: "(counterM f,counterEvalP f) : model"
  apply(simp add: model_def counterM_def) done

lemmas Abs_counterModel_inverse = counterModelInRepn[THEN Abs_model_inverse]

lemma inv_obj_obj: "inv obj (obj n) = n"
  using inj_obj apply simp done

lemma map_X_map_counterAssign: "map X (map (inv obj) (map counterAssign xs)) = xs"
  apply(simp)
  apply(subgoal_tac "(X \<circ> (inv obj \<circ> counterAssign)) = (% x . x)")
  apply simp
  apply(rule ext)
  apply(case_tac x)
  apply(simp add: inv_obj_obj)
  done
      
lemma objectsCounterModel: "objects (counterModel f) =  { z . ? i . z = obj i }"
  apply(simp add: objects_def counterModel_def)
  apply(simp add: Abs_counterModel_inverse)
  apply(simp add: counterM_def) 
  by force

lemma inCounterM: "counterAssign v : objects (counterModel f)"
  apply(induct v) 
  apply(simp add: objectsCounterModel) 
  by blast

lemma counterAssign_eqI[rule_format]: "x : objects (counterModel f) --> z = X (inv obj x) --> counterAssign z = x"
  apply(force simp: objectsCounterModel inj_obj) done

lemma evalPCounterModel: "M = counterModel f ==> evalP M = counterEvalP f"
  apply(simp add: evalP_def counterModel_def Abs_counterModel_inverse) done


subsection "counterModel: all path formula value false - step by step"

lemma path_evalF': 
  notes ss = evalPCounterModel counterEvalP_def map_X_map_counterAssign map_map[symmetric]
  and ss1 = instanceF_def evalF_subF_eq comp_vblcase id_def[symmetric]
  shows "[| branch subs (pseq fs) f; 
  !n . ~ proofTree (tree subs (f n))
  |] ==> (? i . EV (contains f (i,A))) \<longrightarrow> ~(evalF (counterModel f) counterAssign A)"
  apply (rule_tac strong_formula_induct, rule) 
  apply(rule formula_signs_cases)
       \<comment> \<open>atom\<close>
       apply(simp add: ss del: map_map)
      apply(rule, rule)
      apply(simp add: ss del: map_map)
      apply(force dest: notEvContainsBothAtoms)
     \<comment> \<open>conj\<close>
     apply(force dest: evContainsConj)
     \<comment> \<open>disj\<close>
    apply(force dest: evContainsDisj)
   \<comment> \<open>all\<close>
   apply(rule, rule)
   apply(erule exE)
   apply(drule_tac evContainsAll) apply assumption apply assumption
   apply(erule exE)
   apply(drule_tac x="(instanceF v f1)" in spec)
   apply(erule impE, force simp: size_instance)+
   apply simp
   apply(simp add: ss1)
   apply(rule_tac x="counterAssign v" in bexI) apply simp apply(simp add: inCounterM) 
  \<comment> \<open>ex\<close>
  apply(rule, rule)
  apply(erule exE)
  apply(drule_tac evContainsExval) apply assumption apply assumption
  apply simp
  apply rule 
  apply(simp add: objectsCounterModel) apply(erule exE) 
  apply(drule_tac x="X i" in spec)
  apply(drule_tac x="(instanceF (X i) f1)" in spec)
  apply(erule impE, force simp: size_instance)+
  apply(simp add: ss1)
  done 

lemmas path_evalF'' = mp[OF path_evalF']


subsection "adequacy"

lemma counterAssignModelAssign: "counterAssign : modelAssigns (counterModel gamma)"
  apply (simp add: modelAssigns_def, rule)
  apply (erule rangeE, simp)
  apply(rule inCounterM)
  done

lemma branch_contains_initially: "branch subs (pseq fs) f \<Longrightarrow> x : set fs \<Longrightarrow> contains f (0,x) 0"
  apply(simp add: contains_def branch0 pseq_def)
  done

lemma path_evalF: 
  "[| branch subs (pseq fs) f;
  \<forall>n. \<not> proofTree (tree subs (f n)); 
  x \<in> set fs
  |] ==> \<not> evalF (counterModel f) counterAssign x"
  apply (rule path_evalF'', assumption, assumption)
  apply(rule_tac x=0 in exI) apply(simp add: EV_def) 
  apply(rule_tac x=0 in exI) apply(simp add: branch_contains_initially) 
  done

lemma validProofTree: "~proofTree (tree subs (pseq fs)) ==> ~(validS fs)"
  apply(simp add: validS_def evalS_def)
  apply(subgoal_tac "\<exists>f. branch subs (pseq fs) f \<and> (\<forall>n. \<not> proofTree (tree subs (f n)))")
   apply(elim exE conjE)
   apply(rule_tac x="counterModel f" in exI)
   apply(rule_tac x=counterAssign in bexI)
    apply(force dest!: path_evalF) 
   apply(rule counterAssignModelAssign)
  apply(rule failingBranchExistence)
    apply(rule inheritedProofTree)
   apply (rule fansSubs, assumption)
  done

lemma adequacy[simplified sequent_pseq]: "validS fs ==> (sequent (pseq fs)) : deductions CutFreePC"
  apply(rule proofTreeDeductionD)
  apply(rule ccontr)
  apply(force dest!: validProofTree)
  done

end
