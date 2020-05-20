theory "Proof_Checker" 
imports
  Ordinary_Differential_Equations.ODE_Analysis
  "Ids"
  "Lib"
  "Syntax"
  "Denotational_Semantics"
  "Axioms"
  "Differential_Axioms"
  "Frechet_Correctness"
  "Static_Semantics"
  "Coincidence"
  "Bound_Effect"
  "Uniform_Renaming"
  "USubst_Lemma"
  "Pretty_Printer"
  
begin context ids begin
section \<open>Proof Checker\<close>
text \<open>This proof checker defines a datatype for proof terms in dL and a function for checking proof
 terms, with a soundness proof that any proof accepted by the checker is a proof of a sound rule or
 valid formula.

 A simple concrete hybrid system and a differential invariant rule for conjunctions are provided
 as example proofs.
\<close>
  
lemma sound_weaken_gen:"\<And>A B C. sublist A B \<Longrightarrow> sound (A, C) \<Longrightarrow> sound (B,C)"
proof (rule soundI_mem)
  fix A B::"('sf,'sc,'sz) sequent list" 
    and C::"('sf,'sc,'sz) sequent" 
    and I::"('sf,'sc,'sz) interp"
  assume sub:"sublist A B"
  assume good:"is_interp I"
  assume "sound (A, C)"
  then have soundC:"(\<And>\<phi>. List.member A \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV) \<Longrightarrow> seq_sem I C = UNIV"
    apply simp
    apply(drule soundD_mem)
      by (auto simp add: good)
  assume SG:"(\<And>\<phi>. List.member B \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
  show "seq_sem I C = UNIV"
    using soundC SG sub unfolding sublist_def by auto
qed
  
lemma sound_weaken:"\<And>SG SGS C. sound (SGS, C) \<Longrightarrow> sound (SG # SGS, C)"
  subgoal for SG SGS C
    apply(induction SGS)
     subgoal unfolding sound_def by auto
    subgoal for SG2 SGS
      unfolding sound_def 
      by (metis fst_conv le0 length_Cons not_less_eq nth_Cons_Suc snd_conv)
    done
  done

lemma member_filter:"\<And>P. List.member (filter P L) x \<Longrightarrow> List.member L x"
  apply(induction L, auto)
  by(metis (full_types) member_rec(1))

lemma nth_member:"n < List.length L \<Longrightarrow> List.member L (List.nth L n)"
  apply(induction L, auto simp add: member_rec)
  by (metis in_set_member length_Cons nth_mem set_ConsD)

lemma mem_appL:"List.member A x \<Longrightarrow> List.member (A @ B) x"
  by(induction A, auto simp add: member_rec)

lemma sound_weaken_appR:"\<And>SG SGS C. sound (SG, C) \<Longrightarrow> sound (SG @ SGS, C)"
  subgoal for SG SGS C
    apply(rule sound_weaken_gen)
     apply(auto)
    unfolding sublist_def apply(rule allI)
    subgoal for x
      using mem_appL[of SG x SGS] by auto 
    done
  done

fun start_proof::"('sf,'sc,'sz) sequent \<Rightarrow> ('sf,'sc,'sz) rule"
where "start_proof S = ([S], S)"
  
lemma start_proof_sound:"sound (start_proof S)"
  unfolding sound_def by auto
  
section \<open>Proof Checker Implementation\<close>

datatype axiom =
  AloopIter | AI | Atest | Abox | Achoice | AK | AV | Aassign | Adassign
| AdConst | AdPlus | AdMult
| ADW | ADE | ADC | ADS | ADIGeq | ADIGr | ADG
  
fun get_axiom:: "axiom \<Rightarrow> ('sf,'sc,'sz) formula"
where 
  "get_axiom AloopIter = loop_iterate_axiom"
| "get_axiom AI = Iaxiom"
| "get_axiom Atest = test_axiom"
| "get_axiom Abox = box_axiom"
| "get_axiom Achoice = choice_axiom"
| "get_axiom AK = Kaxiom"
| "get_axiom AV = Vaxiom"
| "get_axiom Aassign = assign_axiom"
| "get_axiom Adassign = diff_assign_axiom" 
| "get_axiom AdConst = diff_const_axiom"
| "get_axiom AdPlus = diff_plus_axiom"
| "get_axiom AdMult = diff_times_axiom"
| "get_axiom ADW = DWaxiom"
| "get_axiom ADE = DEaxiom"
| "get_axiom ADC = DCaxiom"
| "get_axiom ADS = DSaxiom"
| "get_axiom ADIGeq = DIGeqaxiom"
| "get_axiom ADIGr = DIGraxiom"
| "get_axiom ADG = DGaxiom"
  
lemma axiom_safe:"fsafe (get_axiom a)"
  by(cases a, auto simp add: axiom_defs Box_def Or_def Equiv_def Implies_def empty_def Equals_def f1_def p1_def P_def f0_def expand_singleton Forall_def Greater_def id_simps)
  (*apply(cases a)
  prefer 9
  subgoal
    apply(simp only: get_axiom.simps diff_assign_axiom_def Equiv_def Or_def Box_def)
    apply(simp only: fsafe_Not_simps fsafe_Diamond_simps fsafe_And_simps)
    apply(rule conjI)+
    subgoal apply(simp only: hpsafe_DiffAssign_simps dsafe_Fun_simps empty_def dsafe_Const) by auto
    
    *)
   (*auto simp add: loop_iterate_axiom_def Iaxiom_def diff_assign_axiom_def test_axiom_def choice_axiom_def box_axiom_def empty_def Kaxiom_def Vaxiom_def assign_axiom_def diff_const_axiom_def diff_plus_axiom_def diff_times_axiom_def DWaxiom_def Equals_def state_fun_def DEaxiom_def DCaxiom_def DSaxiom_def DIGeqaxiom_def DIGraxiom_def f1_def p1_def P_def expand_singleton f0_def Forall_def DGaxiom_def Equiv_def Implies_def Or_def Box_def Greater_def vne12*)
lemma axiom_valid:"valid (get_axiom a)"
proof (cases a)
  case AloopIter
  then show ?thesis by (simp add: loop_valid) 
next
  case AI
  then show ?thesis by (simp add: I_valid)
next
  case Atest
  then show ?thesis by (simp add: test_valid)
next
  case Abox
  then show ?thesis by (simp add: box_valid)
next
  case Achoice
  then show ?thesis by (simp add: choice_valid)
next
  case AK
  then show ?thesis by (simp add: K_valid)
next
  case AV
  then show ?thesis by (simp add: V_valid)
next
  case Aassign
  then show ?thesis by (simp add: assign_valid)
next
  case Adassign
  then show ?thesis by (simp add: diff_assign_valid)
next
  case AdConst
  then show ?thesis by (simp add: diff_const_axiom_valid)
next
  case AdPlus
  then show ?thesis by (simp add: diff_plus_axiom_valid)
next
  case AdMult
  then show ?thesis by (simp add: diff_times_axiom_valid)
next
  case ADW
  then show ?thesis by (simp add: DW_valid)
next
  case ADE
  then show ?thesis by (simp add: DE_valid)
next
  case ADC
  then show ?thesis by (simp add: DC_valid)
next
  case ADS
  then show ?thesis by (simp add: DS_valid)
next
  case ADIGeq
  then show ?thesis by (simp add: DIGeq_valid)
next
  case ADIGr
  then show ?thesis by (simp add: DIGr_valid)
next
  case ADG
  then show ?thesis by (simp add: DG_valid)
qed

datatype rrule = ImplyR | AndR | CohideR | CohideRR | TrueR | EquivR
datatype lrule = ImplyL | AndL | EquivForwardL | EquivBackwardL
  
datatype ('a, 'b, 'c) step =
  Axiom axiom
| MP
| G
| CT
| CQ  "('a, 'c) trm" "('a, 'c) trm" "('a, 'b, 'c) subst"
| CE  "('a, 'b, 'c) formula" "('a, 'b, 'c) formula" "('a, 'b, 'c) subst"
| Skolem
\<comment> \<open>Apply \<open>Usubst\<close> to some other (valid) formula\<close>
| VSubst "('a, 'b, 'c) formula" "('a, 'b, 'c) subst"
| AxSubst axiom "('a, 'b, 'c) subst"
| URename
| BRename
| Rrule rrule nat
| Lrule lrule nat
| CloseId nat nat
| Cut "('a, 'b, 'c) formula"
| DEAxiomSchema "('a,'c) ODE" "('a, 'b, 'c) subst"
  
type_synonym ('a, 'b, 'c) derivation = "(nat * ('a, 'b, 'c) step) list"
type_synonym ('a, 'b, 'c) pf = "('a,'b,'c) sequent * ('a, 'b, 'c) derivation"

fun seq_to_string :: "('sf, 'sc, 'sz) sequent \<Rightarrow> char list"
where "seq_to_string (A,S) = join '', '' (map fml_to_string A) @ '' |- '' @ join '', '' (map fml_to_string S)"
  
fun rule_to_string :: "('sf, 'sc, 'sz) rule \<Rightarrow> char list"
where "rule_to_string (SG, C) = (join '';;   '' (map seq_to_string SG)) @ ''            '' @  \<^cancel>\<open>[char_of_nat 10] @\<close> seq_to_string C"

fun close :: "'a list \<Rightarrow> 'a \<Rightarrow>'a list"
where "close L x = filter (\<lambda>y. y \<noteq> x) L"

fun closeI ::"'a list \<Rightarrow> nat \<Rightarrow>'a list"
where "closeI L i = close L (nth L i)"

lemma close_sub:"sublist (close \<Gamma> \<phi>) \<Gamma>"
  apply (auto simp add: sublist_def)
  using member_filter by fastforce

lemma close_app_comm:"close (A @ B) x  = close A x @ close B x"
  by auto

lemma close_provable_sound:"sound (SG, C) \<Longrightarrow> sound (close SG \<phi>, \<phi>) \<Longrightarrow> sound (close SG \<phi>, C)"
proof (rule soundI_mem)
  fix I::"('sf,'sc,'sz) interp"
  assume S1:"sound (SG, C)"
  assume S2:"sound (close SG \<phi>, \<phi>)"
  assume good:"is_interp I"
  assume SGCs:"(\<And>\<phi>'. List.member (close SG \<phi>) \<phi>' \<Longrightarrow> seq_sem I \<phi>' = UNIV)"
  have S\<phi>:"seq_sem I \<phi> = UNIV"
    using S2 apply simp
    apply(drule soundD_mem)
      using good apply auto
    using SGCs UNIV_I by fastforce
  have mem_close:"\<And>P. List.member SG P \<Longrightarrow> P \<noteq> \<phi> \<Longrightarrow> List.member (close SG \<phi>) P"
    by(induction SG, auto simp add: member_rec)
  have SGs:"\<And>P. List.member SG P \<Longrightarrow> seq_sem I P = UNIV"
    subgoal for P
      apply(cases "P = \<phi>")
       subgoal using S\<phi> by auto
      subgoal using mem_close[of P] SGCs by auto
      done
    done
  show "seq_sem I C = UNIV"
    using S1 apply simp
    apply(drule soundD_mem)
      using good apply auto
    using SGs apply auto
    using impl_sem by blast
  qed

fun Lrule_result :: "lrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where "Lrule_result AndL j (A,S) = (case (nth A j) of And p q \<Rightarrow> [(close ([p, q] @ A) (nth A j), S)])"
| "Lrule_result ImplyL j (A,S) = (case (nth A j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> 
   [(close (q # A) (nth A j), S), (close A (nth A j), p # S)])"
| "Lrule_result EquivForwardL j (A,S) = (case (nth A j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow>
   [(close (q # A) (nth A j), S), (close A (nth A j), p # S)])"
| "Lrule_result EquivBackwardL j (A,S) = (case (nth A j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow>
   [(close (p # A) (nth A j), S), (close A (nth A j), q # S)])"

\<comment> \<open>Note: Some of the pattern-matching here is... interesting. The reason for this is that we can only\<close>
\<comment> \<open>match on things in the base grammar, when we would quite like to check things in the derived grammar.\<close>
\<comment> \<open>So all the pattern-matches have the definitions expanded, sometimes in a silly way.\<close>
fun Rrule_result :: "rrule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) sequent \<Rightarrow> ('sf, 'sc, 'sz) sequent list"
where 
  Rstep_Imply:"Rrule_result ImplyR j (A,S) = (case (nth S j) of Not (And (Not q) (Not (Not p))) \<Rightarrow> [(p # A, q # (closeI S j))] | _ \<Rightarrow> undefined)"
| Rstep_And:"Rrule_result AndR j (A,S) = (case (nth S j) of (And p q) \<Rightarrow> [(A, p # (closeI S j )), (A, q # (closeI S j))])"
| Rstep_EquivR:"Rrule_result EquivR j (A,S) =
   (case (nth S j) of Not(And (Not (And p q)) (Not (And (Not p') (Not q')))) \<Rightarrow> 
                (if (p = p' \<and> q = q') then [(p # A, q # (closeI S j)), (q # A, p # (closeI S j))]
                else undefined))"
| Rstep_CohideR:"Rrule_result CohideR j (A,S) = [(A, [nth S j])]"
| Rstep_CohideRR:"Rrule_result CohideRR j (A,S) = [([], [nth S j])]"
| Rstep_TrueR:"Rrule_result TrueR j (A,S) = []"

fun step_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> (nat * ('sf, 'sc, 'sz) step) \<Rightarrow>  ('sf, 'sc, 'sz) rule"
where
  Step_axiom:"step_result (SG,C) (i,Axiom a)   = (closeI SG i, C)"
| Step_AxSubst:"step_result (SG,C) (i,AxSubst a \<sigma>)   = (closeI SG i, C)"
| Step_Lrule:"step_result (SG,C) (i,Lrule L j) = (close (append SG (Lrule_result L j (nth SG i))) (nth SG i), C)"
| Step_Rrule:"step_result (SG,C) (i,Rrule L j) = (close (append SG (Rrule_result L j (nth SG i))) (nth SG i), C)" 
| Step_Cut:"step_result (SG,C) (i,Cut \<phi>) = (let (A,S) = nth SG i in ((\<phi> # A, S) # ((A, \<phi> # S) # (closeI SG i)), C))"
| Step_Vsubst:"step_result (SG,C) (i,VSubst \<phi> \<sigma>) = (closeI SG i, C)"
| Step_CloseId:"step_result (SG,C) (i,CloseId j k) = (closeI SG i, C)"
| Step_G:"step_result (SG,C) (i,G) = (case nth SG i of (_, (Not (Diamond q (Not p))) # Nil) \<Rightarrow> (([], [p]) # closeI SG i, C))"
| Step_DEAxiomSchema:"step_result (SG,C) (i,DEAxiomSchema ODE \<sigma>) = (closeI SG i, C)"
| Step_CE:"step_result (SG,C) (i, CE \<phi> \<psi> \<sigma>) =  (closeI SG i, C)"
| Step_CQ:"step_result (SG,C) (i, CQ \<theta>\<^sub>1 \<theta>\<^sub>2 \<sigma>) =  (closeI SG i, C)"
| Step_default:"step_result R (i,S) = R"
  
fun deriv_result :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> ('sf, 'sc, 'sz) rule"
where 
  "deriv_result R [] = R"
| "deriv_result R (s # ss) = deriv_result (step_result R s) (ss)" 
  
fun proof_result :: "('sf, 'sc, 'sz) pf \<Rightarrow> ('sf, 'sc, 'sz) rule"
where "proof_result (D,S) = deriv_result (start_proof D) S"
  
inductive lrule_ok ::"('sf,'sc,'sz) sequent list \<Rightarrow> ('sf,'sc,'sz) sequent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> lrule \<Rightarrow> bool"
where
  Lrule_And:"\<And>p q. nth (fst (nth SG i)) j = (p && q) \<Longrightarrow> lrule_ok SG C i j AndL"
| Lrule_Imply:"\<And>p q. nth (fst (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> lrule_ok SG C i j ImplyL"
| Lrule_EquivForward:"\<And>p q. nth (fst (nth SG i)) j = (p \<leftrightarrow> q) \<Longrightarrow> lrule_ok SG C i j EquivForwardL"
| Lrule_EquivBackward:"\<And>p q. nth (fst (nth SG i)) j = (p \<leftrightarrow> q) \<Longrightarrow> lrule_ok SG C i j EquivBackwardL"

named_theorems prover "Simplification rules for checking validity of proof certificates" 
lemmas [prover] = axiom_defs Box_def Or_def Implies_def filter_append ssafe_def SDom_def FUadmit_def PFUadmit_def id_simps

inductive_simps 
    Lrule_And[prover]: "lrule_ok SG C i j AndL"
and Lrule_Imply[prover]: "lrule_ok SG C i j ImplyL"
and Lrule_Forward[prover]: "lrule_ok SG C i j EquivForwardL"
and Lrule_EquivBackward[prover]: "lrule_ok SG C i j EquivBackwardL"

inductive rrule_ok ::"('sf,'sc,'sz) sequent list \<Rightarrow> ('sf,'sc,'sz) sequent \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> rrule \<Rightarrow> bool"
where
  Rrule_And:"\<And>p q. nth (snd (nth SG i)) j = (p && q) \<Longrightarrow> rrule_ok SG C i j AndR"
| Rrule_Imply:"\<And>p q. nth (snd (nth SG i)) j = (p \<rightarrow> q) \<Longrightarrow> rrule_ok SG C i j ImplyR"
| Rrule_Equiv:"\<And>p q. nth (snd (nth SG i)) j = (p \<leftrightarrow> q) \<Longrightarrow> rrule_ok SG C i j EquivR"
| Rrule_Cohide:"length (snd (nth SG i)) > j \<Longrightarrow> (\<And>\<Gamma> q. (nth SG i) \<noteq> (\<Gamma>, [q])) \<Longrightarrow> rrule_ok SG C i j CohideR"
| Rrule_CohideRR:"length (snd (nth SG i)) > j  \<Longrightarrow> (\<And>q. (nth SG i) \<noteq> ([], [q])) \<Longrightarrow> rrule_ok SG C i j CohideRR"
| Rrule_True:"nth (snd (nth SG i)) j = TT \<Longrightarrow> rrule_ok SG C i j TrueR"
  
inductive_simps 
    Rrule_And_simps[prover]: "rrule_ok SG C i j AndR"
and Rrule_Imply_simps[prover]: "rrule_ok SG C i j ImplyR"
and Rrule_Equiv_simps[prover]: "rrule_ok SG C i j EquivR"
and Rrule_CohideR_simps[prover]: "rrule_ok SG C i j CohideR"
and Rrule_CohideRR_simps[prover]: "rrule_ok SG C i j CohideRR"
and Rrule_TrueR_simps[prover]: "rrule_ok SG C i j TrueR"

inductive step_ok  :: "('sf, 'sc, 'sz) rule \<Rightarrow> nat \<Rightarrow> ('sf, 'sc, 'sz) step \<Rightarrow> bool"
where
  Step_Axiom:"(nth SG i) = ([], [get_axiom a]) \<Longrightarrow> step_ok (SG,C) i (Axiom a)"
| Step_AxSubst:"(nth SG i) = ([], [Fsubst (get_axiom a) \<sigma>]) \<Longrightarrow> Fadmit \<sigma> (get_axiom a) \<Longrightarrow> ssafe \<sigma> \<Longrightarrow> step_ok (SG,C) i (AxSubst a \<sigma>)"
| Step_Lrule:"lrule_ok SG C i j L \<Longrightarrow> j < length (fst (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (Lrule L j)"
| Step_Rrule:"rrule_ok SG C i j L \<Longrightarrow> j < length (snd (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (Rrule L j)"
| Step_Cut:"fsafe \<phi> \<Longrightarrow> i < length SG \<Longrightarrow> step_ok (SG,C) i (Cut \<phi>)"
| Step_CloseId:"nth (fst (nth SG i)) j = nth (snd (nth SG i)) k \<Longrightarrow> j < length (fst (nth SG i)) \<Longrightarrow> k < length (snd (nth SG i)) \<Longrightarrow> step_ok (SG,C) i (CloseId j k) "
| Step_G:"\<And>a p. nth SG i = ([], [([[a]]p)]) \<Longrightarrow> step_ok (SG,C) i G"
| Step_DEAxiom_schema:
  " nth SG i = 
  ([], [Fsubst ((([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) ODE) (p1 vid2 vid1)]] (P pid1)) \<leftrightarrow>
          ([[EvolveODE ((OProd  (OSing vid1 (f1 fid1 vid1))) ODE) (p1 vid2 vid1)]]
               [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))) \<sigma>])
    \<Longrightarrow> ssafe \<sigma>
    \<Longrightarrow> osafe ODE
    \<Longrightarrow> {Inl vid1, Inr vid1} \<inter> BVO ODE = {}
    \<Longrightarrow> Fadmit \<sigma> ((([[EvolveODE (OProd  (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]] (P pid1)) \<leftrightarrow>
          ([[EvolveODE ((OProd  (OSing vid1 (f1 fid1 vid1))ODE)) (p1 vid2 vid1)]]
               [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))) 
    \<Longrightarrow> step_ok (SG,C) i (DEAxiomSchema ODE \<sigma>)"
| Step_CE:"nth SG i = ([], [Fsubst (Equiv (InContext pid1 \<phi>) (InContext pid1 \<psi>)) \<sigma>]) 
    \<Longrightarrow> valid (Equiv \<phi> \<psi>) 
    \<Longrightarrow> fsafe \<phi>
    \<Longrightarrow> fsafe \<psi>
    \<Longrightarrow> ssafe \<sigma>
    \<Longrightarrow> Fadmit \<sigma> (Equiv (InContext pid1 \<phi>) (InContext pid1 \<psi>))
    \<Longrightarrow> step_ok (SG,C) i (CE \<phi> \<psi> \<sigma>)"
| Step_CQ:"nth SG i = ([], [Fsubst (Equiv (Prop p (singleton \<theta>)) (Prop p (singleton \<theta>'))) \<sigma>]) 
    \<Longrightarrow> valid (Equals \<theta> \<theta>') 
    \<Longrightarrow> dsafe \<theta>
    \<Longrightarrow> dsafe \<theta>'
    \<Longrightarrow> ssafe \<sigma>
    \<Longrightarrow> Fadmit \<sigma> (Equiv (Prop p (singleton \<theta>)) (Prop p (singleton \<theta>')))
    \<Longrightarrow> step_ok (SG,C) i (CQ \<theta> \<theta>' \<sigma>)"  
  
inductive_simps 
    Step_G_simps[prover]: "step_ok (SG,C) i G"
and Step_CloseId_simps[prover]: "step_ok (SG,C) i (CloseId j k)"
and Step_Cut_simps[prover]: "step_ok (SG,C) i (Cut \<phi>)"
and Step_Rrule_simps[prover]: "step_ok (SG,C) i (Rrule j L)"
and Step_Lrule_simps[prover]: "step_ok (SG,C) i (Lrule j L)"
and Step_Axiom_simps[prover]: "step_ok (SG,C) i (Axiom a)"
and Step_AxSubst_simps[prover]: "step_ok (SG,C) i (AxSubst a \<sigma>)"
and Step_DEAxiom_schema_simps[prover]: "step_ok (SG,C) i (DEAxiomSchema ODE \<sigma>)"
and Step_CE_simps[prover]: "step_ok (SG,C) i (CE \<phi> \<psi> \<sigma>)"
and Step_CQ_simps[prover]: "step_ok (SG,C) i (CQ \<theta> \<theta>' \<sigma>)"

inductive deriv_ok :: "('sf, 'sc, 'sz) rule \<Rightarrow> ('sf, 'sc, 'sz) derivation \<Rightarrow> bool"
where 
  Deriv_Nil:"deriv_ok R Nil"
| Deriv_Cons:"step_ok R i S \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length (fst R) \<Longrightarrow> deriv_ok (step_result R (i,S)) SS \<Longrightarrow> deriv_ok R ((i,S) # SS)"
  
inductive_simps 
    Deriv_nil_simps[prover]: "deriv_ok R Nil"
and Deriv_cons_simps[prover]: "deriv_ok R ((i,S)#SS)"

inductive proof_ok :: "('sf, 'sc, 'sz) pf \<Rightarrow> bool"
where
  Proof_ok:"deriv_ok (start_proof D) S \<Longrightarrow> proof_ok (D,S)"

inductive_simps Proof_ok_simps[prover]: "proof_ok (D,S)"

subsection \<open>Soundness\<close>

named_theorems member_intros "Prove that stuff is in lists"

lemma mem_sing[member_intros]:"\<And>x. List.member [x] x"
  by(auto simp add: member_rec)

lemma mem_appR[member_intros]:"\<And>A B x. List.member B x \<Longrightarrow> List.member (A @ B) x"
  subgoal for A by(induction A, auto simp add: member_rec) done

lemma mem_filter[member_intros]:"\<And>A P x. P x \<Longrightarrow> List.member A x \<Longrightarrow> List.member (filter P A) x"
  subgoal for A
    by(induction A, auto simp add: member_rec)
  done

lemma sound_weaken_appL:"\<And>SG SGS C. sound (SGS, C) \<Longrightarrow> sound (SG @ SGS, C)"
  subgoal for SG SGS C
    apply(rule sound_weaken_gen)
     apply(auto)
    unfolding sublist_def apply(rule allI)
    subgoal for x
      using mem_appR[of SGS x SG] by auto
    done
  done

lemma fml_seq_valid:"valid \<phi> \<Longrightarrow> seq_valid ([], [\<phi>])"
  unfolding seq_valid_def valid_def by auto

lemma closeI_provable_sound:"\<And>i. sound (SG, C) \<Longrightarrow> sound (closeI SG i, (nth SG i)) \<Longrightarrow> sound (closeI SG i, C)"
  using close_provable_sound by auto

lemma valid_to_sound:"seq_valid A \<Longrightarrow> sound (B, A)"
  unfolding seq_valid_def sound_def by auto

lemma closeI_valid_sound:"\<And>i. sound (SG, C) \<Longrightarrow> seq_valid (nth SG i) \<Longrightarrow> sound (closeI SG i, C)"
  using valid_to_sound closeI_provable_sound by auto
  
lemma close_nonmember_eq:"\<not>(List.member A a) \<Longrightarrow> close A a = A"
  by (induction A, auto simp add: member_rec)

lemma close_noneq_nonempty:"List.member A x \<Longrightarrow> x \<noteq> a \<Longrightarrow> close A a \<noteq> []"
  by(induction A, auto simp add: member_rec)

lemma close_app_neq:"List.member A x \<Longrightarrow> x \<noteq> a \<Longrightarrow> close (A @ B) a \<noteq> B" 
  using append_self_conv2[of "close A a" "close B a"] append_self_conv2[of "close A a" "B"] close_app_comm[of A B a] close_noneq_nonempty[of A x a]
  apply(cases "close B a = B")
   apply (auto)
  by (metis (no_types, lifting) filter_True filter_append mem_Collect_eq set_filter)
  
lemma member_singD:"\<And>x P. P x \<Longrightarrow> (\<And>y. List.member [x] y \<Longrightarrow> P y)"
  by (metis member_rec(1) member_rec(2))

lemma fst_neq:"A \<noteq> B \<Longrightarrow> (A,C) \<noteq> (B,D)"
  by auto
  
lemma lrule_sound: "lrule_ok SG C i j L \<Longrightarrow> i < length SG \<Longrightarrow> j < length (fst (SG ! i)) \<Longrightarrow> sound (SG,C) \<Longrightarrow> sound (close (append SG (Lrule_result L j (nth SG i))) (nth SG i), C)"
proof(induction rule: lrule_ok.induct)
  case (Lrule_And SG i j C p q)
  assume eq:"fst (SG ! i) ! j = (p && q)"
  assume sound:"sound (SG, C)"
  obtain AI and SI where SG_dec:"(AI,SI) = (SG ! i)"
    by (metis seq2fml.cases)
  have AIjeq:"AI ! j = (p && q)" using SG_dec eq
    by (metis fst_conv)
  have sub:"sublist [(close ([p, q] @ AI) (p && q),SI)] ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)])"
    apply (rule sublistI)
    using member_singD [of "\<lambda>y. List.member ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close ([p, q] @ AI) (p && q), SI)] . y \<noteq> (AI, SI)]) y" "(close ([p, q] @ AI) (p && q),SI)"]
    using close_app_neq[of "[p, q]" p "p && q" AI] 
    by(auto intro: member_intros fst_neq simp add: member_rec expr_diseq)
  have cool:"sound ([y\<leftarrow>SG . y \<noteq> (AI, SI)] @ [y\<leftarrow> [(close (p # q # AI) (p && q), SI)] . y \<noteq> (AI, SI)], AI, SI)"
    apply(rule sound_weaken_gen[OF sub] )
    apply(auto simp add: member_rec expr_diseq)
    unfolding seq_valid_def
  proof (rule soundI_mem)
    fix I::"('sf,'sc,'sz) interp"
    assume good:"is_interp I"
    assume sgs:"(\<And>\<phi>. List.member [(p # q # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)] \<phi> \<Longrightarrow> seq_sem I \<phi> = UNIV)"
    have theSg:"seq_sem I (p # q # [y\<leftarrow>AI . y \<noteq> (p && q)], SI) = UNIV"
      apply(rule sgs)
      by(auto intro: member_intros)
    then have sgIn:"\<And>\<nu>. \<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
      by auto
    { fix \<nu>
      assume sem:"\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
      have mem_eq:"\<And>x. List.member ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)]) x = List.member AI x"
        by (metis (mono_tags, lifting) Lrule_And.prems(2) SG_dec eq fst_conv local.member_filter mem_filter member_rec(1) nth_member)
      have myeq:"\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI) \<Longrightarrow>  \<nu> \<in> seq_sem I (AI, SI)"
        using and_foldl_sem and_foldl_sem_conv seq_semI Lrule_And.prems(2) SG_dec eq  seq_MP seq_semI' mem_eq
        by (metis (no_types, lifting))
      have "\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
        using sem by auto
      then have "\<nu> \<in> seq_sem I ((p && q) # [y\<leftarrow>AI . y \<noteq> (p && q)], SI)"
        by blast
      then have "\<nu> \<in> seq_sem I (AI, SI)"
        using myeq by auto}
      then show "seq_sem I (AI, SI) = UNIV"
        using sgIn by blast
    qed
  have res_sound:"sound ([y\<leftarrow>SG . y \<noteq> (AI,SI)] @ [y\<leftarrow>Lrule_result AndL j (AI,SI) . y \<noteq> (AI,SI)],(AI,SI))"
    apply (simp)
    using cool AIjeq by auto
 show "?case"
  apply(rule close_provable_sound)
   apply(rule sound_weaken_appR)
   apply(rule sound)
  using res_sound SG_dec by auto
next
  case (Lrule_Imply SG i j C p q)
  have implyL_simp:"\<And>AI SI SS p q. 
    (nth AI  j) = (Not (And (Not q) (Not (Not p)))) \<Longrightarrow> 
    (AI,SI) = SS \<Longrightarrow> 
    Lrule_result ImplyL j SS = [(close (q # AI) (nth AI j), SI), (close AI (nth AI j), p # SI)]"
    subgoal for AI SI SS p q apply(cases SS) by auto done
  assume eq:"fst (SG ! i) ! j = (p \<rightarrow> q)"
  assume iL:"i < length SG"
  assume jL:"j < length (fst (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have res_eq:"Lrule_result ImplyL j (SG ! i) = 
    [(close (q # \<Gamma>) (nth \<Gamma> j), \<Delta>), 
     (close \<Gamma> (nth \<Gamma> j), p # \<Delta>)]"
    apply(rule implyL_simp)
    using SG_dec eq Implies_def Or_def 
    by (metis fstI)+
  have AIjeq:"\<Gamma> ! j = (p \<rightarrow> q)" 
    using SG_dec eq unfolding Implies_def Or_def
    by (metis fst_conv)
  have big_sound:"sound ([(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] \<Longrightarrow>
             \<nu> \<in> seq_sem I ([(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] ! i))"
    have sg1:"\<nu> \<in> seq_sem I (close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>)" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)" using sgs[of "Suc 0"] by auto
    assume \<Gamma>:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
    have \<Gamma>_proj:"\<And>\<phi> \<Gamma>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>"
      apply(induction \<Gamma>, auto simp add: member_rec)
      using and_foldl_sem by blast
    have imp:"\<nu> \<in> fml_sem I (p \<rightarrow> q)" 
      apply(rule \<Gamma>_proj[of \<Gamma>])
      using AIjeq  jL SG_dec nth_member
      apply (metis fst_conv)
      by (rule \<Gamma>)
    have sub:"sublist (close \<Gamma> (p \<rightarrow> q)) \<Gamma>"
      by (rule close_sub)
    have \<Gamma>C:"\<nu> \<in> fml_sem I (foldr And (close \<Gamma> (p \<rightarrow> q)) TT)"
      by (rule \<Gamma>_sub_sem[OF sub \<Gamma>])
    have "\<nu> \<in> fml_sem I (foldr (||) (p # \<Delta>) FF)"
      by(rule seq_MP[OF sg2 \<Gamma>C])
    then have disj:"\<nu> \<in> fml_sem I p \<or> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      by auto 
    { assume p:"\<nu> \<in> fml_sem I p"
      have q:"\<nu> \<in> fml_sem I q" using p imp by simp
      have res: "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using disj \<Gamma> seq_semI
        proof -
          have "\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
            using \<Gamma> q by auto
          then show ?thesis
            by (meson \<Gamma>_sub_sem close_sub seq_MP sg1)
        qed
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
        using q \<Gamma> by auto
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (close (q # \<Gamma>) (p \<rightarrow> q)) TT)"
        apply(rule \<Gamma>_sub_sem)
        defer
        apply(rule conj)
        by(rule close_sub)
      have \<Delta>1:"\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        by(rule seq_MP[OF sg1 conj])
      }
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using disj by auto
    qed
    have neq1:"close ([q] @ \<Gamma>) (p \<rightarrow> q) \<noteq> \<Gamma>"
      apply(rule close_app_neq)
       apply(rule mem_sing)
      by (auto simp add: expr_diseq)
    have neq2:"p # \<Delta> \<noteq> \<Delta>"
      by(induction p, auto)
    have close_eq:"close [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)] (\<Gamma>,\<Delta>) = [(close (q # \<Gamma>) (p \<rightarrow> q), \<Delta>), (close \<Gamma> (p \<rightarrow> q), p # \<Delta>)]"
      apply(rule close_nonmember_eq)
      apply auto
       using neq1 neq2  
       apply (simp add: member_rec)
    proof -
      assume a1: "q = (p \<rightarrow> q)"
      assume "List.member [([y\<leftarrow>\<Gamma> . y \<noteq> q], \<Delta>), ([y\<leftarrow>\<Gamma> . y \<noteq> q], p # \<Delta>)] (\<Gamma>, \<Delta>)"
        then have "[f\<leftarrow>\<Gamma> . f \<noteq> q] = \<Gamma>"
      by (simp add: member_rec)
      then show False
        using a1 neq1 by fastforce
    qed       
  show ?case 
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec   
    by simp
next
  case (Lrule_EquivBackward SG i j C p q)
  have equivLBackward_simp:"\<And>AI SI SS p q. 
    (nth AI  j) = Not (And (Not (And p q)) (Not (And (Not p) (Not q)))) \<Longrightarrow> 
    (AI,SI) = SS \<Longrightarrow> 
    Lrule_result EquivBackwardL j SS = [(close (p # AI) (nth AI j), SI), (close AI (nth AI j), q # SI)]"
    subgoal for AI SI SS p q apply(cases SS) by auto done
  assume eq:"fst (SG ! i) ! j = (p \<leftrightarrow> q)"
  assume iL:"i < length SG"
  assume jL:"j < length (fst (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have res_eq:"Lrule_result EquivBackwardL j (SG ! i) = 
    [(close (p # \<Gamma>) (nth \<Gamma> j), \<Delta>), 
     (close \<Gamma> (nth \<Gamma> j), q # \<Delta>)]"
    apply(rule equivLBackward_simp)
     using SG_dec eq Equiv_def Or_def 
     by (metis fstI)+
  have AIjeq:"\<Gamma> ! j = (p \<leftrightarrow> q)" 
    using SG_dec eq unfolding Implies_def Or_def
    by (metis fst_conv)
  have big_sound:"sound ([(close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)] \<Longrightarrow>
             \<nu> \<in> seq_sem I ([(close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)] ! i))"
    have sg1:"\<nu> \<in> seq_sem I (close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>)" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)" using sgs[of "Suc 0"] by auto 
    assume \<Gamma>:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
    have \<Gamma>_proj:"\<And>\<phi> \<Gamma>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>"
      apply(induction \<Gamma>, auto simp add: member_rec)
      using and_foldl_sem by blast
    have imp:"\<nu> \<in> fml_sem I (p \<leftrightarrow> q)" 
      apply(rule \<Gamma>_proj[of \<Gamma>])
      using AIjeq  jL SG_dec nth_member
      apply (metis fst_conv)
      by (rule \<Gamma>)
    have sub:"sublist (close \<Gamma> (p \<rightarrow> q)) \<Gamma>"
      by (rule close_sub)
    have \<Gamma>C:"\<nu> \<in> fml_sem I (foldr And (close \<Gamma> (p \<rightarrow> q)) TT)"
      by (rule \<Gamma>_sub_sem[OF sub \<Gamma>])
    have "\<nu> \<in> fml_sem I (foldr (||) (p # \<Delta>) FF)"
      by (metis \<Gamma> \<Gamma>_sub_sem close_sub iff_sem imp member_rec(1) or_foldl_sem or_foldl_sem_conv seq_MP sg2)
    then have disj:"\<nu> \<in> fml_sem I p \<or> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      by auto 
    { assume p:"\<nu> \<in> fml_sem I p"
      have q:"\<nu> \<in> fml_sem I q" using p imp by simp
      have res: "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using disj \<Gamma> seq_semI
        proof -
          have "\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
            using \<Gamma> q by auto
          then show ?thesis
            proof -
              have "\<forall>fs p i. (\<exists>f. List.member fs (f::('sf, 'sc, 'sz) formula) \<and> p \<notin> fml_sem i f) \<or> p \<in> fml_sem i (foldr (&&) fs TT)"
                using and_foldl_sem_conv by blast
              then obtain ff :: "('sf, 'sc, 'sz) formula list \<Rightarrow> (real, 'sz) vec \<times> (real, 'sz) vec \<Rightarrow> ('sf, 'sc, 'sz) interp \<Rightarrow> ('sf, 'sc, 'sz) formula" where
                f1: "\<forall>fs p i. List.member fs (ff fs p i) \<and> p \<notin> fml_sem i (ff fs p i) \<or> p \<in> fml_sem i (foldr (&&) fs TT)"
                by metis
              have "\<And>f. \<nu> \<in> fml_sem I f \<or> \<not> List.member \<Gamma> f"
                by (meson \<open>\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)\<close> and_foldl_sem member_rec(1))
              then have "\<nu> \<in> fml_sem I (foldr (&&) (close (p # \<Gamma>) (p \<leftrightarrow> q)) TT)"
                using f1 by (metis (no_types) close_sub local.sublist_def member_rec(1) p)
              then show ?thesis
                using seq_MP sg1 by blast
            qed
        qed
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
        using q \<Gamma> by auto
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (close (q # \<Gamma>) (p \<rightarrow> q)) TT)"
        apply(rule \<Gamma>_sub_sem)
        defer
        apply(rule conj)
        by(rule close_sub)
      have \<Delta>1:"\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using res by blast
      }
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using disj by auto
  qed
  have neq1:"close ([q] @ \<Gamma>) (p \<leftrightarrow> q) \<noteq> \<Gamma>"
    apply(rule close_app_neq)
     apply(rule mem_sing)
    by (auto simp add: expr_diseq)
  have neq2:"p # \<Delta> \<noteq> \<Delta>"
    by(induction p, auto)                 
  have close_eq:"close [(close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)] (\<Gamma>,\<Delta>) = [(close (p # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), q # \<Delta>)]"
    apply(rule close_nonmember_eq)
    apply auto
     using neq1 neq2  
     apply (simp add: member_rec)
     apply (metis append_Cons append_Nil close.simps close_app_neq member_rec(1))
    proof -
       assume a1:"p = (p \<leftrightarrow> q)"
       then show False
         by (simp add: expr_diseq)
    qed
  show ?case 
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec   
    by simp
next
  case (Lrule_EquivForward SG i j C p q)
  have equivLForward_simp:"\<And>AI SI SS p q. 
    (nth AI  j) = Not (And (Not (And p q)) (Not (And (Not p) (Not q)))) \<Longrightarrow> 
    (AI,SI) = SS \<Longrightarrow> 
    Lrule_result EquivForwardL j SS = [(close (q # AI) (nth AI j), SI), (close AI (nth AI j), p # SI)]"
    subgoal for AI SI SS p q apply(cases SS) by auto done
  assume eq:"fst (SG ! i) ! j = (p \<leftrightarrow> q)"
  assume iL:"i < length SG"
  assume jL:"j < length (fst (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have res_eq:"Lrule_result EquivForwardL j (SG ! i) = 
    [(close (q # \<Gamma>) (nth \<Gamma> j), \<Delta>), 
     (close \<Gamma> (nth \<Gamma> j), p # \<Delta>)]"
    apply(rule equivLForward_simp)
    using SG_dec eq Equiv_def Or_def 
    by (metis fstI)+
  have AIjeq:"\<Gamma> ! j = (p \<leftrightarrow> q)" 
    using SG_dec eq unfolding Implies_def Or_def
    by (metis fst_conv)
  have big_sound:"sound ([(close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)] \<Longrightarrow>
             \<nu> \<in> seq_sem I ([(close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)] ! i))"
    have sg1:"\<nu> \<in> seq_sem I (close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>)" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)" using sgs[of "Suc 0"] by auto 
    assume \<Gamma>:"\<nu> \<in> fml_sem I (foldr And \<Gamma> TT)"
    have \<Gamma>_proj:"\<And>\<phi> \<Gamma>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr And \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>"
      apply(induction \<Gamma>, auto simp add: member_rec)
      using and_foldl_sem by blast
    have imp:"\<nu> \<in> fml_sem I (p \<leftrightarrow> q)" 
      apply(rule \<Gamma>_proj[of \<Gamma>])
       using AIjeq  jL SG_dec nth_member
       apply (metis fst_conv)
      by (rule \<Gamma>)
    have sub:"sublist (close \<Gamma> (p \<rightarrow> q)) \<Gamma>"
      by (rule close_sub)
    have \<Gamma>C:"\<nu> \<in> fml_sem I (foldr And (close \<Gamma> (p \<rightarrow> q)) TT)"
      by (rule \<Gamma>_sub_sem[OF sub \<Gamma>])
    have "\<nu> \<in> fml_sem I (foldr (||) (p # \<Delta>) FF)"
      by (metis \<Gamma> \<Gamma>_sub_sem close_sub iff_sem imp member_rec(1) or_foldl_sem or_foldl_sem_conv seq_MP sg2)
    then have disj:"\<nu> \<in> fml_sem I p \<or> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      by auto 
    { assume p:"\<nu> \<in> fml_sem I p"
      have q:"\<nu> \<in> fml_sem I q" using p imp by simp
      have res: "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)" 
        using disj \<Gamma> seq_semI
        proof -
          have "\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
            using \<Gamma> q by auto
          then show ?thesis
            by (meson \<open>\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)\<close> and_foldl_sem and_foldl_sem_conv close_sub local.sublist_def seq_MP sg1)
        qed
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT)"
        using q \<Gamma> by auto
      have conj:"\<nu> \<in> fml_sem I (foldr (&&) (close (q # \<Gamma>) (p \<rightarrow> q)) TT)"
        apply(rule \<Gamma>_sub_sem)
        defer
        apply(rule conj)
        by(rule close_sub)
      have \<Delta>1:"\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using res by blast
      }
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using disj by auto
  qed
  have neq1:"close ([q] @ \<Gamma>) (p \<leftrightarrow> q) \<noteq> \<Gamma>"
    apply(rule close_app_neq)
    apply(rule mem_sing)
    by (auto simp add: expr_diseq)
  have neq2:"p # \<Delta> \<noteq> \<Delta>"
    by(induction p, auto)
  have close_eq:"close [(close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)] (\<Gamma>,\<Delta>) = [(close (q # \<Gamma>) (p \<leftrightarrow> q), \<Delta>), (close \<Gamma> (p \<leftrightarrow> q), p # \<Delta>)]"
    apply(rule close_nonmember_eq)
    apply auto
     using neq1 neq2  
     apply (simp add: member_rec)
  proof -
     assume a1:"q = (p \<leftrightarrow> q)"
     then show False
       by (simp add: expr_diseq)
  qed
  show ?case 
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec   
  by simp
qed

lemma rrule_sound: "rrule_ok SG C i j L \<Longrightarrow> i < length SG \<Longrightarrow> j < length (snd (SG ! i)) \<Longrightarrow> sound (SG,C) \<Longrightarrow> sound (close (append SG (Rrule_result L j (nth SG i))) (nth SG i), C)"
proof(induction rule: rrule_ok.induct)
  case (Rrule_And SG i j C p q)
  assume eq:"snd (SG ! i) ! j = (p && q)"
  assume "i < length SG"
  assume "j < length (snd (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have andR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = And p q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    Rrule_result AndR j SS = [(\<Gamma>, p # (close \<Delta> (nth \<Delta> j))), (\<Gamma>, q # (close \<Delta> (nth \<Delta> j)))]"
    subgoal for AI SI SS p q apply(cases SS) by auto done
  have res_eq:"Rrule_result AndR j (SG ! i) = 
    [(\<Gamma>, p # (close \<Delta> (nth \<Delta> j))), (\<Gamma>, q # (close \<Delta> (nth \<Delta> j)))]"
    using SG_dec andR_simp apply auto
    using SG_dec eq Implies_def Or_def
    using fstI
    by (metis andR_simp close.simps snd_conv)
  have AIjeq:"\<Delta> ! j = (p && q)" 
    using SG_dec eq snd_conv
    by metis
  have big_sound:"sound ([(\<Gamma>, p # (close \<Delta> (nth \<Delta> j))), (\<Gamma>, q # (close \<Delta> (nth \<Delta> j)))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow>
             i < length [(\<Gamma>, p # close \<Delta> (nth \<Delta>  j)), (\<Gamma>, q # close \<Delta> (nth \<Delta>  j))] \<Longrightarrow>
             \<nu> \<in> seq_sem I (nth [(\<Gamma>, p # close \<Delta> (nth \<Delta>  j)), (\<Gamma>, q # close \<Delta> (nth \<Delta> j))] i))"
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have sg1:"\<nu> \<in> seq_sem I (\<Gamma>, p # close \<Delta> (nth \<Delta> j))" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (\<Gamma>, q # close \<Delta> (nth \<Delta> j))" using sgs[of 1] by auto
    have \<Delta>1:"\<nu> \<in> fml_sem I (foldr (||) (p # close \<Delta> (nth \<Delta> j)) FF)"
      by(rule seq_MP[OF sg1 \<Gamma>_sem])
    have \<Delta>2:"\<nu> \<in> fml_sem I (foldr (||) (q # close \<Delta> (nth \<Delta> j)) FF)"
      by(rule seq_MP[OF sg2 \<Gamma>_sem])
    have \<Delta>':"\<nu> \<in> fml_sem I (foldr (||) ((p && q) # close \<Delta> (nth \<Delta> j)) FF)"
      using \<Delta>1 \<Delta>2 by auto
    have mem_eq:"\<And>x. List.member ((p && q) # close \<Delta> (nth \<Delta> j)) x \<Longrightarrow> List.member \<Delta> x"
      using Rrule_And.prems SG_dec eq  member_rec(1) nth_member
      by (metis close_sub local.sublist_def snd_conv)
    have myeq:"\<nu> \<in> fml_sem I (foldr (||) ((p && q) # close \<Delta> (nth \<Delta> j)) FF) \<Longrightarrow>  \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using  seq_semI Rrule_And.prems SG_dec eq  seq_MP seq_semI' mem_eq
        or_foldl_sem or_foldl_sem_conv
        by metis
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using \<Delta>' by auto  
  qed
  have list_neqI1:"\<And>L1 L2 x. List.member L1 x \<Longrightarrow> \<not>(List.member L2 x) \<Longrightarrow> L1 \<noteq> L2"
    by(auto)
  have list_neqI2:"\<And>L1 L2 x. \<not>(List.member L1 x) \<Longrightarrow> (List.member L2 x) \<Longrightarrow> L1 \<noteq> L2"
    by(auto)
  have notin_cons:"\<And>x y ys. x \<noteq> y \<Longrightarrow> \<not>(List.member ys x) \<Longrightarrow> \<not>(List.member (y # ys) x)"
    subgoal for x y ys
      by(induction ys, auto simp add: member_rec)
    done
  have notin_close:"\<And>L x. \<not>(List.member (close L x) x)"
    subgoal for L x
      by(induction L, auto simp add: member_rec)
    done
  have neq_lemma:"\<And>L x y. List.member L x \<Longrightarrow> y \<noteq> x \<Longrightarrow> (y # (close L x)) \<noteq> L"
    subgoal for L x y
      apply(cases "List.member L y")
       subgoal
         apply(rule list_neqI2[of "y # close L x" x])
          apply(rule notin_cons)
           defer
           apply(rule notin_close)
          by(auto)
      subgoal
        apply(rule list_neqI2[of "y # close L x" x])
         apply(rule notin_cons)
          defer
          apply(rule notin_close)
         by(auto)
      done
    done
  have neq1:"p # close \<Delta> (p && q) \<noteq> \<Delta>"
    apply(rule neq_lemma)
     apply (metis Rrule_And.prems(2) SG_dec eq nth_member sndI)
    by(auto simp add: expr_diseq) 
  have neq2:"q # close \<Delta> (p && q) \<noteq> \<Delta>"
    apply(rule neq_lemma)
     apply (metis Rrule_And.prems(2) SG_dec eq nth_member sndI)
    by(auto simp add: expr_diseq)
  have close_eq:"close [(\<Gamma>, p # close \<Delta> (p && q)), (\<Gamma>, q # close \<Delta> (p && q))] (\<Gamma>,\<Delta>) = [(\<Gamma>, p # close \<Delta> (p && q)), (\<Gamma>, q # close \<Delta> (p && q))]"
    apply(rule close_nonmember_eq)
    apply auto
    using neq1 neq2  
    by (simp add: member_rec)
  show " sound (close (SG @ Rrule_result AndR j (SG ! i)) (SG ! i), C)" 
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec   
    by (simp add: AIjeq)
next
  case (Rrule_Imply SG i j C p q)
  assume eq:"snd (SG ! i) ! j = (p \<rightarrow> q)"
  assume "i < length SG"
  assume "j < length (snd (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have impR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Implies p q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    Rrule_result ImplyR j SS = [(p # \<Gamma>, q # (close \<Delta> (nth \<Delta> j)))]"
    subgoal for AI SI SS p q apply(cases SS) by (auto simp add: Implies_def Or_def) done
  have res_eq:"Rrule_result ImplyR j (SG ! i) = 
    [(p # \<Gamma>, q # (close \<Delta> (nth \<Delta> j)))]"
    using SG_dec impR_simp apply auto
    using SG_dec eq Implies_def Or_def
    using fstI
    by (metis impR_simp close.simps snd_conv)
  have AIjeq:"\<Delta> ! j = (p \<rightarrow> q)" 
    using SG_dec eq snd_conv
    by metis
  have close_eq:"close [(p # \<Gamma>, q # (close \<Delta> (nth \<Delta> j)))] (\<Gamma>,\<Delta>) = [(p # \<Gamma>, q # (close \<Delta> (nth \<Delta> j)))]"
    apply(rule close_nonmember_eq)
    by (simp add: member_rec)
  have big_sound:"sound ([(p # \<Gamma>, q # close \<Delta> (\<Delta> ! j))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume "is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(p # \<Gamma>, q # close \<Delta> (\<Delta> ! j))] \<Longrightarrow> \<nu> \<in> seq_sem I ([(p # \<Gamma>, q # close \<Delta> (\<Delta> ! j))] ! i))"
      have sg:"\<nu> \<in> seq_sem I (p # \<Gamma>, q # close \<Delta> (\<Delta> ! j))" using sgs[of 0] by auto
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using \<Gamma>_sem sg 
        AIjeq Rrule_Imply.prems(2) SG_dec and_foldl_sem_conv close_sub impl_sem local.sublist_def member_rec(1) nth_member or_foldl_sem_conv seq_MP seq_semI snd_conv
        \<Gamma>_sub_sem and_foldl_sem or_foldl_sem seq_sem.simps sublistI
    proof -
      have f1: "\<forall>fs p i. \<exists>f. (p \<in> fml_sem i (foldr (&&) fs (TT::('sf, 'sc, 'sz) formula)) \<or> List.member fs f) \<and> (p \<notin> fml_sem i f \<or> p \<in> fml_sem i (foldr (&&) fs TT))"
        using and_foldl_sem_conv by blast
      have "\<forall>p i fs. \<exists>f. \<forall>pa ia fa fb pb ib fc fd. p \<in> fml_sem i (f::('sf, 'sc, 'sz) formula) \<and> (pa \<in> fml_sem ia (fa::('sf, 'sc, 'sz) formula) \<or> pa \<in> fml_sem ia (fa \<rightarrow> fb)) \<and> (pb \<notin> fml_sem ib (fc::('sf, 'sc, 'sz) formula) \<or> pb \<in> fml_sem ib (fd \<rightarrow> fc)) \<and> (p \<notin> fml_sem i (foldr (||) fs FF) \<or> List.member fs f)"
        by (metis impl_sem or_foldl_sem_conv)
      then obtain ff :: "(real, 'sz) vec \<times> (real, 'sz) vec \<Rightarrow> ('sf, 'sc, 'sz) interp \<Rightarrow> ('sf, 'sc, 'sz) formula list \<Rightarrow> ('sf, 'sc, 'sz) formula" where
        f2: "\<And>p i fs pa ia f fa pb ib fb fc. p \<in> fml_sem i (ff p i fs) \<and> (pa \<in> fml_sem ia (f::('sf, 'sc, 'sz) formula) \<or> pa \<in> fml_sem ia (f \<rightarrow> fa)) \<and> (pb \<notin> fml_sem ib (fb::('sf, 'sc, 'sz) formula) \<or> pb \<in> fml_sem ib (fc \<rightarrow> fb)) \<and> (p \<notin> fml_sem i (foldr (||) fs FF) \<or> List.member fs (ff p i fs))"
        by metis
      then have "\<And>fs. \<nu> \<notin> fml_sem I (foldr (&&) (p # \<Gamma>) TT) \<or> \<not> local.sublist (close \<Delta> (p \<rightarrow> q)) fs \<or> ff \<nu> I (q # close \<Delta> (p \<rightarrow> q)) = q \<or> List.member fs (ff \<nu> I (q # close \<Delta> (p \<rightarrow> q)))"
        by (metis (no_types) AIjeq local.sublist_def member_rec(1) seq_MP sg)
      then have "\<exists>f. List.member \<Delta> f \<and> \<nu> \<in> fml_sem I f"
        using f2 f1 by (metis (no_types) AIjeq Rrule_Imply.prems(2) SG_dec \<Gamma>_sem and_foldl_sem close_sub member_rec(1) nth_member snd_conv)
      then show ?thesis
        using or_foldl_sem by blast
    qed
  qed
  show ?case
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    using res_eq
    apply(unfold res_eq)
    apply(unfold AIjeq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec AIjeq
    by (simp add: AIjeq)
next
  case (Rrule_Cohide SG i j C)
  assume "i < length SG"
  assume "j < length (snd (SG ! i))"
  assume chg:"(\<And>\<Gamma> q. (nth SG i) \<noteq> (\<Gamma>, [q]))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have cohideR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    Rrule_result CohideR j SS = [(\<Gamma>, [nth \<Delta> j])]"
    subgoal for AI SI SS p q by(cases SS, auto) done
  have res_eq:"Rrule_result CohideR j (SG ! i) =  [(\<Gamma>, [nth \<Delta> j])]"
    using SG_dec cohideR_simp by auto
  have close_eq:"close [(\<Gamma>, [nth \<Delta> j])] (\<Gamma>,\<Delta>) = [(\<Gamma>, [nth \<Delta> j])]"
    using chg 
    by (metis SG_dec close_nonmember_eq member_rec(1) member_rec(2))
  have big_sound:"sound ([(\<Gamma>, [nth \<Delta> j])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
    by (metis (no_types, lifting) Rrule_Cohide.prems(2) SG_dec length_greater_0_conv less_or_eq_imp_le list.distinct(1) member_singD nth_Cons_0 nth_member or_foldl_sem or_foldl_sem_conv seq_MP snd_conv)
  show ?case
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    using res_eq
    apply(unfold res_eq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using big_sound SG_dec
    apply(cases "[nth \<Delta> j] = \<Delta>")
     apply(auto)
    using chg by (metis)+
next
  case (Rrule_CohideRR SG i j C)
  assume "i < length SG"
  assume "j < length (snd (SG ! i))"
  assume chg:"(\<And>q. (nth SG i) \<noteq> ([], [q]))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have cohideRR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    Rrule_result CohideRR j SS = [([], [nth \<Delta> j])]"
    subgoal for AI SI SS p q by(cases SS, auto) done
  have res_eq:"Rrule_result CohideRR j (SG ! i) =  [([], [nth \<Delta> j])]"
    using SG_dec cohideRR_simp by auto
  have close_eq:"close [([], [nth \<Delta> j])] (\<Gamma>,\<Delta>) = [([], [nth \<Delta> j])]"
    using chg 
    by (metis SG_dec close_nonmember_eq member_rec(1) member_rec(2))
  have big_sound:"sound ([([], [nth \<Delta> j])], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
    by (metis (no_types, lifting) Rrule_CohideRR.prems(2) SG_dec and_foldl_sem_conv length_greater_0_conv less_or_eq_imp_le list.distinct(1) member_rec(2) member_singD nth_Cons_0 nth_member or_foldl_sem or_foldl_sem_conv seq_MP snd_conv)
  show ?case
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    using res_eq
    apply(unfold res_eq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using big_sound SG_dec
    apply(cases "[nth \<Delta> j] = \<Delta>")
     apply(auto)
     using chg by (metis)+
next
  case (Rrule_True SG i j C)
  assume tt:"snd (SG ! i) ! j = TT"
  assume iL:"i < length SG"
  assume iJ:"j < length (snd (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have "\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      fix I::"('sf,'sc,'sz)interp" and \<nu>::"'sz state"
      assume good:"is_interp I"
      have mem2:"List.member \<Delta> (\<Delta> ! j)"
        using iJ nth_member 
        by (metis SG_dec snd_conv)
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using mem2
        using or_foldl_sem 
        by (metis SG_dec UNIV_I snd_conv tt tt_sem)
    qed
  then have seq_valid:"seq_valid (SG ! i)"
    unfolding seq_valid_def using SG_dec
    by (metis UNIV_eq_I seq_semI')
  show ?case
    using closeI_valid_sound[OF sound seq_valid]
    by (simp add: sound_weaken_appR)
next
  case (Rrule_Equiv SG i j C p q)
  assume eq:"snd (SG ! i) ! j = (p \<leftrightarrow> q)"
  assume iL:"i < length SG"
  assume jL:"j < length (snd (SG ! i))"
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have equivR_simp:"\<And>\<Gamma> \<Delta> SS p q. 
    (nth \<Delta> j) = Equiv p q \<Longrightarrow> 
    (\<Gamma>,\<Delta>) = SS \<Longrightarrow> 
    Rrule_result EquivR j SS = [(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))]"
    subgoal for AI SI SS p q apply(cases SS) by (auto simp add: Equiv_def Implies_def Or_def) done
  have res_eq:"Rrule_result EquivR j (SG ! i) = 
    [(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))]"
    apply(rule equivR_simp)
    subgoal using eq SG_dec by (metis snd_conv)
    by (rule SG_dec) 
  have AIjeq:"\<Delta> ! j = (p \<leftrightarrow> q)" 
    using SG_dec eq snd_conv
    by metis
  have close_eq:"close [(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))] (\<Gamma>,\<Delta>) = [(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))]"
    apply(rule close_nonmember_eq)
    by (simp add: member_rec)
  have big_sound:"sound ([(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))], (\<Gamma>,\<Delta>))"
    apply(rule soundI')
    apply(rule seq_semI')
  proof -
    fix I ::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume sgs:"(\<And>i. 0 \<le> i \<Longrightarrow> i < length [(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))] \<Longrightarrow> \<nu> \<in> seq_sem I ([(p # \<Gamma>, q # (closeI \<Delta> j)), (q # \<Gamma>, p # (closeI \<Delta> j))] ! i))"
    have sg1:"\<nu> \<in> seq_sem I (p # \<Gamma>, q # close \<Delta> (\<Delta> ! j))" using sgs[of 0] by auto
    have sg2:"\<nu> \<in> seq_sem I (q # \<Gamma>, p # (closeI \<Delta> j))" using sgs[of 1] by auto
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have case1:"\<nu> \<in> fml_sem I p \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      assume sem:"\<nu> \<in> fml_sem I p"
      have "\<nu> \<in> fml_sem I (foldr (||) (q # (close \<Delta> (nth \<Delta> j))) FF)"
        using sem \<Gamma>_sem sg1 by auto
      then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        using AIjeq SG_dec close_sub[of \<Delta> "nth \<Delta> j"] iff_sem[of "\<nu>" I p q] jL local.sublist_def
        member_rec(1)[of q "close \<Delta> (nth \<Delta> j)"] sem snd_conv
        or_foldl_sem_conv[of \<nu> I "q # close \<Delta> (nth \<Delta> j)"]
        or_foldl_sem[of "\<Delta>", where I=I and \<nu>=\<nu>]
        nth_member[of j "snd (SG ! i)"]
        by metis
    qed
    have case2:"\<nu> \<notin> fml_sem I p \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
    proof -
      assume sem:"\<nu> \<notin> fml_sem I p"
      have "\<nu> \<in> fml_sem I q \<Longrightarrow>  \<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF) \<Longrightarrow> False"
        using  
          and_foldl_sem[OF \<Gamma>_sem]
          and_foldl_sem_conv
          closeI.simps
          close_sub
          local.sublist_def
          member_rec(1)[of "p" "closeI \<Delta> j"]
          member_rec(1)[of "q" "\<Gamma>"]
          or_foldl_sem[of "\<Delta>"]
          or_foldl_sem_conv[of \<nu>  I "p # closeI \<Delta> j"]
          sem
          sg2
          seq_MP[of \<nu> I "q # \<Gamma>" "p # closeI \<Delta> j", OF sg2]
      proof -
        assume a1: "\<nu> \<in> fml_sem I q"
        assume a2: "\<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF)"
        obtain ff :: "('sf, 'sc, 'sz) formula" where
          "\<nu> \<in> fml_sem I ff \<and> List.member (p # close \<Delta> (\<Delta> ! j)) ff"
          using a1 by (metis (no_types) \<open>\<And>\<phi>. List.member \<Gamma> \<phi> \<Longrightarrow> \<nu> \<in> fml_sem I \<phi>\<close> \<open>\<And>y. List.member (q # \<Gamma>) y = (q = y \<or> List.member \<Gamma> y)\<close> \<open>\<nu> \<in> fml_sem I (foldr (&&) (q # \<Gamma>) TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF)\<close> \<open>\<nu> \<in> fml_sem I (foldr (||) (p # closeI \<Delta> j) FF) \<Longrightarrow> \<exists>\<phi>. \<nu> \<in> fml_sem I \<phi> \<and> List.member (p # closeI \<Delta> j) \<phi>\<close> and_foldl_sem_conv closeI.simps)
        then show ?thesis
          using a2 by (metis (no_types) \<open>\<And>\<phi> \<nu> I. \<lbrakk>List.member \<Delta> \<phi>; \<nu> \<in> fml_sem I \<phi>\<rbrakk> \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)\<close> \<open>\<And>y. List.member (p # closeI \<Delta> j) y = (p = y \<or> List.member (closeI \<Delta> j) y)\<close> closeI.simps close_sub local.sublist_def sem)
      qed
      show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
        by (metis AIjeq SG_dec \<open>\<lbrakk>\<nu> \<in> fml_sem I q; \<nu> \<notin> fml_sem I (foldr (||) \<Delta> FF)\<rbrakk> \<Longrightarrow> False\<close> iff_sem jL nth_member or_foldl_sem sem snd_eqD)
    qed
    show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      by(cases "\<nu> \<in> fml_sem I p", (simp add: case1 case2)+)
    qed
  show ?case
    apply(rule close_provable_sound)
     apply(rule sound_weaken_appR)
     apply(rule sound)
    using res_eq
    apply(unfold res_eq)
    unfolding close_app_comm
    apply (rule sound_weaken_appL)
    using close_eq big_sound SG_dec AIjeq
    by (simp add: AIjeq)
qed

lemma step_sound:"step_ok R i S \<Longrightarrow> i \<ge> 0 \<Longrightarrow> i < length (fst R) \<Longrightarrow> sound R \<Longrightarrow> sound (step_result R (i,S))"
proof(induction rule: step_ok.induct)
  case (Step_Axiom SG i a C)
  assume is_axiom:"SG ! i = ([], [get_axiom a])"
  assume sound:"sound (SG, C)"
  assume i0:"0 \<le> i"
  assume "i < length (fst (SG, C))"
  then have iL:"i < length (SG)" 
    by auto
  have "seq_valid ([], [get_axiom a])"
    apply(rule fml_seq_valid)
    by(rule axiom_valid)
  then have seq_valid:"seq_valid (SG ! i)"
    using is_axiom by auto
  \<comment> \<open>\<open>i0 iL\<close>\<close>
  then show ?case 
    using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_AxSubst SG i a \<sigma> C)
  assume is_axiom:"SG ! i = ([], [Fsubst (get_axiom a) \<sigma>])"
  assume sound:"sound (SG, C)"
  assume ssafe:"ssafe \<sigma>"
  assume i0:"0 \<le> i"
  assume Fadmit:"Fadmit \<sigma> (get_axiom a)"
  assume "i < length (fst (SG, C))"
  then have iL:"i < length (SG)" 
    by auto
  have valid_axiom:"valid (get_axiom a)"
    by(rule axiom_valid)
  have subst_valid:"valid (Fsubst (get_axiom a) \<sigma>)"
    apply(rule subst_fml_valid)
       apply(rule Fadmit)
      apply(rule axiom_safe)
     apply(rule ssafe)
    by(rule valid_axiom)
  have "seq_valid ([], [(Fsubst (get_axiom a) \<sigma>)])"
    apply(rule fml_seq_valid)
    by(rule subst_valid)
  then have seq_valid:"seq_valid (SG ! i)"
    using is_axiom by auto
  \<comment> \<open>\<open>i0 iL\<close>\<close>
  then show ?case 
    using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_Lrule R i j L)
  then show ?case
    using lrule_sound
    using step_result.simps(2) surj_pair
    by simp
next
  case (Step_Rrule R i SG j L)
  then show ?case 
    using rrule_sound
    using step_result.simps(2) surj_pair
    by simp
next
  case (Step_Cut \<phi> i SG C)
  assume safe:"fsafe \<phi>"
  assume "i < length (fst (SG, C))"
  then have iL:"i < length SG" by auto
  assume sound:"sound (SG, C)"
  obtain \<Gamma> and \<Delta> where SG_dec:"(\<Gamma>,\<Delta>) = (SG ! i)"
    by (metis seq2fml.cases)
  have "sound ((\<phi> # \<Gamma>, \<Delta>) # (\<Gamma>, \<phi> # \<Delta>) # [y\<leftarrow>SG . y \<noteq> SG ! i], C)"
    apply(rule soundI_memv)
  proof -
    fix I::"('sf,'sc,'sz) interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume sgs:"(\<And>\<phi>' \<nu>. List.member ((\<phi> # \<Gamma>, \<Delta>) # (\<Gamma>, \<phi> # \<Delta>) # [y\<leftarrow>SG . y \<noteq> SG ! i]) \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
    have sg1:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<phi> # \<Gamma>, \<Delta>)" using sgs by (meson member_rec(1))
    have sg2:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma>, \<phi> # \<Delta>)" using sgs by (meson member_rec(1))
    have sgs:"\<And>\<phi> \<nu>. (List.member (close SG (nth SG i)) \<phi>) \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>"
      using sgs  by (simp add: member_rec(1))
    then have sgs:"\<And>\<phi> \<nu>. (List.member (close SG (\<Gamma>,\<Delta>)) \<phi>) \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>"
      using SG_dec by auto
    have sgNew:"\<And>\<nu>. \<nu> \<in> seq_sem I (\<Gamma>, \<Delta>)"
      using sg1 sg2 by auto
    have same_mem:"\<And>x. List.member SG x \<Longrightarrow> List.member ((\<Gamma>,\<Delta>) # close SG (\<Gamma>,\<Delta>)) x"
      subgoal for s
        by(induction SG, auto simp add: member_rec)
      done
    have SGS:"(\<And>\<phi>' \<nu>. List.member SG \<phi>' \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>')"
      using sgNew sgs same_mem member_rec(1) seq_MP
      by metis
    show "\<nu> \<in> seq_sem I C"
      using sound apply simp
      apply(drule soundD_memv)
        apply(rule good)
       using SGS 
       apply blast
      by auto
  qed
  then show ?case 
    using SG_dec case_prod_conv
  proof -
    have "(\<And>f. ((case nth SG i of (x, xa) \<Rightarrow> ((f x xa)::('sf, 'sc, 'sz) rule)) = (f \<Gamma> \<Delta>)))"
      by (metis (no_types) SG_dec case_prod_conv)
    then show ?thesis
      by (simp add: \<open>sound ((\<phi> # \<Gamma>, \<Delta>) # (\<Gamma>, \<phi> # \<Delta>) # [y\<leftarrow>SG . y \<noteq> SG ! i], C)\<close>)
  qed
next
  case (Step_G SG i C a p)
  assume eq:"SG ! i = ([], [([[a]]p)])"
  assume iL:"i < length (fst (SG, C))"
  assume sound:"sound (SG, C)"
  have "sound (([], [p]) # (close SG ([], [([[ a ]] p)])), C)"
    apply(rule soundI_memv)
  proof -
    fix I::"('sf,'sc,'sz) interp" and  \<nu>::"'sz state"
    assume "is_interp I"
    assume sgs:"(\<And>\<phi> \<nu>. List.member (([], [p]) # close SG ([], [([[a]]p)])) \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>)"
    have sg0:"(\<And>\<nu>. \<nu> \<in> seq_sem I ([], [p]))"
      using sgs by (meson member_rec(1))
    then have sg0':"(\<And>\<nu>. \<nu> \<in> seq_sem I ([], [([[a]]p)]))"
      by auto
    have sgTail:"(\<And>\<phi> \<nu>. List.member (close SG ([], [([[a]]p)])) \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>)"
      using sgs by (simp add: member_rec(1))
    have same_mem:"\<And>x. List.member SG x \<Longrightarrow> List.member (([], [([[a]]p)]) # close SG ([], [([[a]]p)])) x"
      subgoal for s
        by(induction SG, auto simp add: member_rec)
      done
    have sgsC:"(\<And>\<phi> \<nu>. List.member SG \<phi> \<Longrightarrow> \<nu> \<in> seq_sem I \<phi>)"
      apply auto
      using sgTail sg0' same_mem member_rec
      by (metis seq_MP)
    then show "\<nu> \<in> seq_sem I C"
      using sound
      by (metis UNIV_eq_I \<open>is_interp I\<close> iso_tuple_UNIV_I soundD_mem)
  qed
  then show ?case 
    by(auto simp add: eq Box_def)
next
  case (Step_CloseId SG i j k C)
  assume match:"fst (SG ! i) ! j = snd (SG ! i) ! k"
  assume jL:"j < length (fst (SG ! i))"
  assume kL:"k < length (snd (SG ! i))"
  assume iL:"i < length (fst (SG, C))"
  then have iL:"i < length (SG)" 
    by auto
  assume sound:"sound (SG, C)"
  obtain \<Gamma> \<Delta> where SG_dec:"(\<Gamma>, \<Delta>) = SG ! i" 
    using prod.collapse by blast
  have j\<Gamma>:"j < length \<Gamma>"
    using SG_dec jL
    by (metis fst_conv)
  have k\<Delta>:"k < length \<Delta>"
    using SG_dec kL
    by (metis snd_conv)
  have "\<And>I \<nu>. is_interp I \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT) \<Longrightarrow> \<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
  proof -
    fix I::"('sf,'sc,'sz)interp" and \<nu>::"'sz state"
    assume good:"is_interp I"
    assume \<Gamma>_sem:"\<nu> \<in> fml_sem I (foldr (&&) \<Gamma> TT)"
    have mem:"List.member \<Gamma> (\<Gamma> ! j)"
      using j\<Gamma> nth_member by blast
    have mem2:"List.member \<Delta> (\<Delta> ! k)"
      using k\<Delta> nth_member by blast
    have "\<nu> \<in> fml_sem I (\<Gamma> ! j)"
      using \<Gamma>_sem mem
      using and_foldl_sem by blast
    then have "\<nu> \<in> fml_sem I (\<Delta> ! k)"
      using match SG_dec
      by (metis fst_conv snd_conv)
    then show "\<nu> \<in> fml_sem I (foldr (||) \<Delta> FF)"
      using mem2
      using or_foldl_sem by blast
  qed
  then have seq_valid:"seq_valid (SG ! i)"
    unfolding seq_valid_def using SG_dec
    by (metis UNIV_eq_I seq_semI')
  then show "sound (step_result (SG, C) (i, CloseId j k))" 
    using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_DEAxiom_schema SG i ODE \<sigma> C )
  assume isNth:"nth SG i =
  ([], [Fsubst (([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]]P pid1) \<leftrightarrow>
                ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]][[DiffAssign vid1 (f1 fid1 vid1)]]P pid1)) \<sigma>])"
  assume FA:"Fadmit \<sigma>
   (([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]]P pid1) \<leftrightarrow>
    ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]][[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))"
  assume disj:"{Inl vid1, Inr vid1} \<inter> BVO ODE = {}"
  have schem_valid:"valid (([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]] (P pid1)) \<leftrightarrow>
    ([[EvolveODE ((OProd (OSing vid1 (f1 fid1 vid1))ODE)) (p1 vid2 vid1)]]
    [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))"
    using DE_sys_valid[OF disj] by auto
  assume ssafe:"ssafe \<sigma>"
  assume osafe:"osafe ODE"
  have subst_valid:"valid (Fsubst (([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]]P pid1) \<leftrightarrow>
                ([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]][[DiffAssign vid1 (f1 fid1 vid1)]]P pid1)) \<sigma>)"
    apply(rule subst_fml_valid)
       apply(rule FA)
      subgoal using disj by(auto simp add: f1_def Box_def p1_def P_def Equiv_def Or_def expand_singleton osafe, induction ODE, auto)
     subgoal by (rule ssafe)
    by (rule schem_valid)
  assume "0 \<le> i" 
  assume "i < length (fst (SG, C))" 
  assume sound:"sound (SG, C)"
  have "seq_valid ([], [(Fsubst (([[EvolveODE (OProd  (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]]P pid1) \<leftrightarrow>
                ([[EvolveODE (OProd  (OSing vid1 (f1 fid1 vid1))ODE) (p1 vid2 vid1)]][[DiffAssign vid1 (f1 fid1 vid1)]]P pid1)) \<sigma>)])"
    apply(rule fml_seq_valid)
    by(rule subst_valid)
  then have seq_valid:"seq_valid (SG ! i)"
    using isNth by auto
  \<comment> \<open>\<open>i0 iL\<close>\<close>
  then show ?case 
  using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_CE SG i \<phi> \<psi> \<sigma> C)
  assume isNth:"SG ! i = ([], [Fsubst (InContext pid1 \<phi> \<leftrightarrow> InContext pid1 \<psi>) \<sigma>])"
  assume valid:"valid (\<phi> \<leftrightarrow> \<psi>)"
  assume FA:"Fadmit \<sigma> (InContext pid1 \<phi> \<leftrightarrow> InContext pid1 \<psi>)"
  assume "0 \<le> i"
  assume "i < length (fst (SG, C))"
  assume sound:"sound (SG, C)"
  assume fsafe1:"fsafe \<phi>"
  assume fsafe2:"fsafe \<psi>"
  assume ssafe:"ssafe \<sigma>"
  have schem_valid:"valid (InContext pid1 \<phi> \<leftrightarrow> InContext pid1 \<psi>)"
    using valid unfolding valid_def 
    by (metis CE_holds_def CE_sound fml_sem.simps(7) iff_sem surj_pair valid_def)+
  have subst_valid:"valid (Fsubst (InContext pid1 \<phi> \<leftrightarrow> InContext pid1 \<psi>) \<sigma>)"
    apply(rule subst_fml_valid)
       apply(rule FA)
      subgoal by(auto simp add: f1_def Box_def p1_def P_def Equiv_def Or_def expand_singleton fsafe1 fsafe2)
     subgoal by (rule ssafe)
    by (rule schem_valid)
  have "seq_valid ([], [Fsubst (InContext pid1 \<phi> \<leftrightarrow> InContext pid1 \<psi>) \<sigma>])"
    apply(rule fml_seq_valid)
    by(rule subst_valid)
  then have seq_valid:"seq_valid (SG ! i)"
    using isNth by auto
  show "sound (step_result (SG, C) (i, CE \<phi> \<psi> \<sigma>))"
    using closeI_valid_sound[OF sound seq_valid] by simp
next
  case (Step_CQ SG i p \<theta> \<theta>' \<sigma> C)
  assume isNth:"nth SG  i = ([], [Fsubst (Equiv (Prop p (singleton \<theta>)) (Prop p (singleton \<theta>'))) \<sigma>])"
  assume valid:"valid (Equals \<theta> \<theta>')"
  assume FA:"Fadmit \<sigma> ($\<phi> p (singleton \<theta>) \<leftrightarrow> $\<phi> p (singleton \<theta>'))"
  assume "0 \<le> i"
  assume "i < length (fst (SG, C))"
  assume sound:"sound (SG, C)"
  assume dsafe1:"dsafe \<theta>"
  assume dsafe2:"dsafe \<theta>'"
  assume ssafe:"ssafe \<sigma>"
  have schem_valid:"valid ($\<phi> p (singleton \<theta>) \<leftrightarrow> $\<phi> p (singleton \<theta>'))"
    using valid unfolding valid_def 
    by (metis CQ_holds_def CQ_sound fml_sem.simps(7) iff_sem surj_pair valid_def)+
  have subst_valid:"valid (Fsubst ($\<phi> p (singleton \<theta>) \<leftrightarrow> $\<phi> p (singleton \<theta>')) \<sigma>)"
    apply(rule subst_fml_valid)
       apply(rule FA)
      using schem_valid ssafe by (auto simp add: f1_def Box_def p1_def P_def Equiv_def Or_def expand_singleton dsafe1 dsafe2 expand_singleton) 
  have "seq_valid ([], [Fsubst ($\<phi> p (singleton \<theta>) \<leftrightarrow> $\<phi> p (singleton \<theta>')) \<sigma>])"
    apply(rule fml_seq_valid)
    by(rule subst_valid)
  then have seq_valid:"seq_valid (SG ! i)"
    using isNth by auto
  show "sound (step_result (SG, C) (i, CQ \<theta> \<theta>' \<sigma>))"
    using closeI_valid_sound[OF sound seq_valid] by simp
qed

lemma deriv_sound:"deriv_ok R D \<Longrightarrow> sound R \<Longrightarrow> sound (deriv_result R D)"
  apply(induction rule: deriv_ok.induct)
   using step_sound by auto

lemma proof_sound:"proof_ok Pf \<Longrightarrow> sound (proof_result Pf)"
  apply(induct rule: proof_ok.induct)
  unfolding proof_result.simps  apply(rule deriv_sound)
  apply assumption
  by(rule start_proof_sound)
  
section \<open>Example 1: Differential Invariants\<close>

definition DIAndConcl::"('sf,'sc,'sz) sequent"
where "DIAndConcl = ([], [Implies (And (Predicational pid1) (Predicational pid2)) 
       (Implies ([[Pvar vid1]](And (Predicational pid3) (Predicational pid4))) 
                ([[Pvar vid1]](And (Predicational pid1) (Predicational pid2))))])"

definition DIAndSG1::"('sf,'sc,'sz) formula"
where "DIAndSG1 = (Implies (Predicational pid1) (Implies ([[Pvar vid1]](Predicational pid3)) ([[Pvar vid1]](Predicational pid1))))"

definition DIAndSG2::"('sf,'sc,'sz) formula"
where "DIAndSG2 = (Implies (Predicational pid2) (Implies ([[Pvar vid1]](Predicational pid4)) ([[Pvar vid1]](Predicational pid2))))"

definition DIAndCut::"('sf,'sc,'sz) formula"
where "DIAndCut = 
  (([[$\<alpha> vid1]]((And (Predicational ( pid3)) (Predicational ( pid4)))) \<rightarrow> (And (Predicational ( pid1)) (Predicational ( pid2))))
    \<rightarrow> ([[$\<alpha> vid1]](And (Predicational ( pid3)) (Predicational ( pid4)))) \<rightarrow> ([[$\<alpha> vid1]](And (Predicational (pid1)) (Predicational ( pid2)))))"
  
definition DIAndSubst::"('sf,'sc,'sz) subst"
where "DIAndSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(And (Predicational (Inl pid1)) (Predicational (Inl pid2))) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
\<comment> \<open>\<open>[a]R&H->R->[a]R&H->[a]R DIAndSubst34\<close>\<close>
definition DIAndSubst341::"('sf,'sc,'sz) subst"
where "DIAndSubst341 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(Predicational (Inl pid3)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
definition DIAndSubst342::"('sf,'sc,'sz) subst"
where "DIAndSubst342 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(And (Predicational (Inl pid3)) (Predicational (Inl pid4))) 
                else (if C = pid2 then Some(Predicational (Inl pid4)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
\<comment> \<open>\<open>[a]P, [a]R&H, P, Q |- [a]Q->P&Q->[a]Q->[a]P&Q, [a]P&Q;;\<close>\<close>
definition DIAndSubst12::"('sf,'sc,'sz) subst"
where "DIAndSubst12 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(Predicational (Inl pid2)) 
                else (if C = pid2 then Some(Predicational (Inl pid1) && Predicational (Inl pid2)) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

\<comment> \<open>\<open>P ->  Q->P&Q\<close>\<close>
definition DIAndCurry12::"('sf,'sc,'sz) subst"
where "DIAndCurry12 = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. (if C = pid1 then Some(Predicational (Inl pid1)) 
                else (if C = pid2 then Some(Predicational (Inl pid2) \<rightarrow> (Predicational (Inl pid1) && Predicational (Inl pid2))) else None))),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"
  
definition DIAnd :: "('sf,'sc,'sz) rule" 
where "DIAnd = 
  ([([],[DIAndSG1]),([],[DIAndSG2])], 
  DIAndConcl)"

definition DIAndCutP1 :: "('sf,'sc,'sz) formula"
where "DIAndCutP1 = ([[Pvar vid1]](Predicational pid1))" 

definition DIAndCutP2 :: "('sf,'sc,'sz) formula"
where "DIAndCutP2 = ([[Pvar vid1]](Predicational pid2))" 

definition DIAndCutP12 :: "('sf,'sc,'sz) formula"
where "DIAndCutP12 = (([[Pvar vid1]](Pc pid1) \<rightarrow> (Pc pid2 \<rightarrow> (And (Pc pid1) (Pc pid2))))
  \<rightarrow> (([[Pvar vid1]]Pc pid1) \<rightarrow> ([[Pvar vid1]](Pc pid2 \<rightarrow> (And (Pc pid1) (Pc pid2))))))" 

definition DIAndCut34Elim1 :: "('sf,'sc,'sz) formula"
where "DIAndCut34Elim1 = (([[Pvar vid1]](Pc pid3 && Pc pid4) \<rightarrow> (Pc pid3))
  \<rightarrow> (([[Pvar vid1]](Pc pid3 && Pc pid4)) \<rightarrow> ([[Pvar vid1]](Pc pid3))))" 

definition DIAndCut34Elim2 :: "('sf,'sc,'sz) formula"
where "DIAndCut34Elim2 = (([[Pvar vid1]](Pc pid3 && Pc pid4) \<rightarrow> (Pc pid4))
  \<rightarrow> (([[Pvar vid1]](Pc pid3 && Pc pid4)) \<rightarrow> ([[Pvar vid1]](Pc pid4))))" 

definition DIAndCut12Intro :: "('sf,'sc,'sz) formula"
where "DIAndCut12Intro = (([[Pvar vid1]](Pc pid2  \<rightarrow> (Pc pid1 && Pc pid2)))
  \<rightarrow> (([[Pvar vid1]](Pc pid2)) \<rightarrow> ([[Pvar vid1]](Pc pid1 && Pc pid2))))" 

definition DIAndProof :: "('sf, 'sc, 'sz) pf"
where "DIAndProof =
  (DIAndConcl, [
   (0, Rrule ImplyR 0)  \<comment> \<open>1\<close>
  ,(0, Lrule AndL 0)
  ,(0, Rrule ImplyR 0)
  ,(0, Cut DIAndCutP1)
  ,(1, Cut DIAndSG1)
  ,(0, Rrule CohideR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc (Suc 0), Cut DIAndCut34Elim1) \<comment> \<open>11\<close>
  ,(0, Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc 0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), G)  
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), Lrule AndL 0)
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), AxSubst AK DIAndSubst341) \<comment> \<open>21\<close>
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, CloseId 0 0)
  ,(0, Cut DIAndCut12Intro)
  ,(Suc 0, Rrule CohideRR 0)
  ,(Suc (Suc 0), AxSubst AK DIAndSubst12)
  ,(0, Lrule ImplyL 0)
  ,(1, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, Cut DIAndCutP12)
  ,(0, Lrule ImplyL 0) \<comment> \<open>31\<close>
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndCurry12)
  ,(Suc (Suc (Suc 0)), Rrule CohideRR 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc 0), G)  
  ,(0, Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule ImplyR 0)  
  ,(Suc (Suc (Suc (Suc 0))), Rrule AndR 0)  
  ,(Suc (Suc (Suc (Suc (Suc 0)))), CloseId 0 0)
  ,(Suc (Suc (Suc (Suc 0))), CloseId 1 0) \<comment> \<open>41\<close>
  ,(Suc (Suc  0), CloseId 0 0)   
  ,(Suc 0, Cut DIAndCut34Elim2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc (Suc 0))), AxSubst AK DIAndSubst342) \<comment> \<open>46\<close>
  ,(Suc (Suc (Suc 0)), Rrule CohideRR 0)
  ,(Suc (Suc (Suc 0)), G) \<comment> \<open>48\<close>
  ,(0, Rrule ImplyR 0)
  ,(Suc (Suc (Suc 0)), Lrule AndL 0) \<comment> \<open>50\<close>
  ,(Suc (Suc (Suc 0)), CloseId 1 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc 0, CloseId 0 0)
  ,(1, Cut DIAndSG2)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc (Suc (Suc 0)), CloseId 4 0)
  ,(Suc (Suc 0), Lrule ImplyL 0)
  ,(Suc (Suc (Suc 0)), CloseId 0 0)
  ,(Suc (Suc (Suc 0)), CloseId 0 0)
  ,(1, CloseId 1 0)
  ])
  "

fun proof_take :: "nat \<Rightarrow> ('sf,'sc,'sz) pf \<Rightarrow> ('sf,'sc,'sz) pf"
where "proof_take n (C,D) = (C,List.take n D)"

fun last_step::"('sf,'sc,'sz) pf \<Rightarrow> nat \<Rightarrow> nat * ('sf,'sc,'sz ) step"
where "last_step (C,D) n = List.last (take n D)"

lemma DIAndSound_lemma:"sound (proof_result (proof_take 61 DIAndProof))"
  apply(rule proof_sound)
  unfolding DIAndProof_def DIAndConcl_def  DIAndCutP1_def DIAndSG1_def DIAndCut34Elim1_def  DIAndSubst341_def DIAndCut12Intro_def DIAndSubst12_def
    DIAndCutP12_def DIAndCurry12_def DIAndSubst342_def
    DIAndCut34Elim2_def \<comment> \<open>43\<close>
    DIAndSG2_def \<comment> \<open>54\<close> (* slow *)
  apply (auto simp add: prover)
  done
  
section \<open>Example 2: Concrete Hybrid System\<close>

\<comment> \<open>\<open>v \<ge> 0 \<and> A() \<ge> 0 \<longrightarrow> [v' = A, x' = v]v' \<ge> 0\<close>\<close>
definition SystemConcl::"('sf,'sc,'sz) sequent"
where "SystemConcl = 
  ([],[
  Implies (And (Geq (Var vid1) (Const 0)) (Geq (f0 fid1) (Const 0)))
  ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) (Const 0))
  ])"

definition SystemDICut :: "('sf,'sc,'sz) formula"
where "SystemDICut =
  Implies
  (Implies TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
     (Geq (Differential (Var vid1)) (Differential (Const 0)))))
  (Implies
     (Implies TT (Geq (Var vid1) (Const 0)))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0))))"
(*
    (Implies (Geq (Var vid1) (Const 0)) 
      (Implies (And TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
                  (Geq (Differential (Var vid1)) (Differential (Const 0)))
   )) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0)))))"
*)  
definition SystemDCCut::"('sf,'sc,'sz) formula"
where "SystemDCCut =
(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) (Const 0))) \<rightarrow>
   (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]((Geq (Differential (Var vid1)) (Differential (Const 0))))) 
   \<leftrightarrow>  
   ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]](Geq (Differential (Var vid1)) (Differential (Const 0))))))"
  
definition SystemVCut::"('sf,'sc,'sz) formula"
where "SystemVCut = 
  Implies (Geq (f0 fid1) (Const 0)) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]](Geq (f0 fid1) (Const 0)))" 

definition SystemVCut2::"('sf,'sc,'sz) formula"
where "SystemVCut2 = 
  Implies (Geq (f0 fid1) (Const 0)) ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (f0 fid1) (Const 0)))" 

definition SystemDECut::"('sf,'sc,'sz) formula"
where "SystemDECut = (([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((Geq (Differential (Var vid1)) (Differential (Const 0))))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))"

definition SystemKCut::"('sf,'sc,'sz) formula"
where "SystemKCut =
  (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
                (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0))))))
      (Implies ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((And TT (Geq (f0 fid1) (Const 0)))))
               ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))))"

definition SystemEquivCut::"('sf,'sc,'sz) formula"
where "SystemEquivCut =
  (Equiv (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))
         (Implies ((And TT (Geq (f0 fid1) (Const 0)))) ([[DiffAssign vid1 (f0 fid1)]](Geq (DiffVar vid1) (Const 0)))))"

definition SystemDiffAssignCut::"('sf,'sc,'sz) formula"
where "SystemDiffAssignCut =
  (([[DiffAssign vid1  ($f fid1 empty)]] (Geq (DiffVar vid1) (Const 0)))
\<leftrightarrow> (Geq ($f fid1 empty) (Const 0)))"
  
definition SystemCEFml1::"('sf,'sc,'sz) formula"
where "SystemCEFml1 = Geq (Differential (Var vid1)) (Differential (Const 0))"

definition SystemCEFml2::"('sf,'sc,'sz) formula"
where "SystemCEFml2 = Geq (DiffVar vid1) (Const 0)"


(*
definition diff_const_axiom :: "('sf, 'sc, 'sz) formula"
  where [axiom_defs]:"diff_const_axiom \<equiv> Equals (Differential ($f fid1 empty)) (Const 0)"

definition diff_var_axiom :: "('sf, 'sc, 'sz) formula"
  where [axiom_defs]:"diff_var_axiom \<equiv> Equals (Differential (Var vid1)) (DiffVar vid1)"*)

  
definition CQ1Concl::"('sf,'sc,'sz) formula"
where "CQ1Concl = (Geq (Differential (Var vid1)) (Differential (Const 0)) \<leftrightarrow> Geq (DiffVar vid1) (Differential (Const 0)))"

definition CQ2Concl::"('sf,'sc,'sz) formula"
where "CQ2Concl = (Geq (DiffVar vid1) (Differential (Const 0)) \<leftrightarrow> Geq ($' vid1) (Const 0))"

definition CEReq::"('sf,'sc,'sz) formula"
where "CEReq = (Geq (Differential (trm.Var vid1)) (Differential (Const 0)) \<leftrightarrow> Geq ($' vid1) (Const 0))"

definition CQRightSubst::"('sf,'sc,'sz) subst"
where "CQRightSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>p. (if p = vid1 then (Some (Geq (DiffVar vid1) (Function  (Inr vid1)  empty))) else None)),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"


definition CQLeftSubst::"('sf,'sc,'sz) subst"
where "CQLeftSubst = 
  \<lparr> SFunctions = (\<lambda>_. None),
    SPredicates = (\<lambda>p. (if p = vid1 then (Some (Geq  (Function  (Inr vid1)  empty) (Differential (Const 0)))) else None)),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition CEProof::"('sf,'sc,'sz) pf"
where "CEProof = (([],[CEReq]), [
  (0, Cut CQ1Concl)
 ,(0, Cut CQ2Concl)
 ,(1, Rrule CohideRR 0)
 ,(Suc (Suc 0), CQ (Differential (Const 0)) (Const 0) CQRightSubst)
 ,(1, Rrule CohideRR 0)
 ,(1, CQ (Differential (Var vid1)) (DiffVar vid1) CQLeftSubst)
 ,(0, Rrule EquivR 0)
 ,(0, Lrule EquivForwardL 1)
 ,(Suc (Suc 0), Lrule EquivForwardL 1)
 ,(Suc (Suc (Suc 0)), CloseId 0 0)
 ,(Suc (Suc 0), CloseId 0 0)
 ,(Suc 0, CloseId 0 0)
 ,(0, Lrule EquivBackwardL (Suc (Suc 0)))
 ,(0, CloseId 0 0)
 ,(0, Lrule EquivBackwardL (Suc 0))
 ,(0, CloseId 0 0)
 ,(0, CloseId 0 0)
 ])"  

lemma CE_result_correct:"proof_result CEProof = ([],([],[CEReq]))"
  unfolding CEProof_def CEReq_def CQ1Concl_def  CQ2Concl_def Implies_def Or_def f0_def TT_def Equiv_def Box_def CQRightSubst_def
  by (auto simp add: id_simps)

definition DiffConstSubst::"('sf,'sc,'sz) subst"
where "DiffConstSubst = \<lparr>
    SFunctions = (\<lambda>f. (if f = fid1 then (Some (Const 0)) else None)),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition DiffConstProof::"('sf,'sc,'sz) pf"
where "DiffConstProof = (([],[(Equals (Differential (Const 0)) (Const 0))]), [
  (0, AxSubst AdConst DiffConstSubst)])"

lemma diffconst_result_correct:"proof_result DiffConstProof = ([], ([],[Equals (Differential (Const 0)) (Const 0)]))"
  by(auto simp add: prover DiffConstProof_def)

lemma diffconst_sound_lemma:"sound (proof_result DiffConstProof)"
  apply(rule proof_sound)
  unfolding DiffConstProof_def
  by (auto simp add: prover DiffConstProof_def DiffConstSubst_def Equals_def empty_def TUadmit_def)
  
lemma valid_of_sound:"sound ([], ([],[\<phi>])) \<Longrightarrow> valid \<phi>"
  unfolding valid_def sound_def TT_def FF_def 
  apply (auto simp add: TT_def FF_def Or_def)
  subgoal for I a b
    apply(erule allE[where x=I])
    by(auto)
  done

lemma almost_diff_const_sound:"sound ([], ([], [Equals (Differential (Const 0)) (Const 0)]))"
  using diffconst_result_correct diffconst_sound_lemma by simp

lemma almost_diff_const:"valid (Equals (Differential (Const 0)) (Const 0))"
  using almost_diff_const_sound valid_of_sound by auto

\<comment> \<open>Note: this is just unpacking the definition: the axiom is defined as literally this formula\<close>
lemma almost_diff_var:"valid (Equals (Differential (trm.Var vid1)) ($' vid1))"
  using diff_var_axiom_valid unfolding diff_var_axiom_def by auto

lemma CESound_lemma:"sound (proof_result CEProof)"
  apply(rule proof_sound)
  unfolding CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
  diff_var_axiom_def
  by (auto simp add: prover CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def
    CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
    TUadmit_def NTUadmit_def almost_diff_const CQLeftSubst_def almost_diff_var)

lemma sound_to_valid:"sound ([], ([], [\<phi>])) \<Longrightarrow> valid \<phi>"
  unfolding  valid_def apply auto
  apply(drule soundD_mem)
  by (auto simp add: member_rec(2))
  
lemma CE1pre:"sound ([], ([], [CEReq]))"  
  using CE_result_correct CESound_lemma 
  by simp
                            
lemma CE1pre_valid:"valid CEReq"
  by (rule sound_to_valid[OF CE1pre])
    
lemma CE1pre_valid2:"valid (! (! (Geq (Differential (trm.Var vid1)) (Differential (Const 0)) && Geq ($' vid1) (Const 0)) &&
              ! (! (Geq (Differential (trm.Var vid1)) (Differential (Const 0))) && ! (Geq ($' vid1) (Const 0))))) "
  using CE1pre_valid unfolding CEReq_def Equiv_def Or_def by auto

definition SystemDISubst::"('sf,'sc,'sz) subst"
where "SystemDISubst = 
  \<lparr> SFunctions = (\<lambda>f. 
    (     if f = fid1 then Some(Function (Inr vid1) empty)
     else if f = fid2 then Some(Const 0)
     else None)),
    SPredicates = (\<lambda>p. if p = vid1 then Some TT else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (trm.Var vid1))) else None)
  \<rparr>"
  
  (*
  Implies 
  (Implies (Prop vid1 empty) ([[EvolveODE (OVar vid1) (Prop vid1 empty)]](Geq (Differential (f1 fid1 vid1)) (Differential (f1 fid2 vid1)))))
  (Implies
     (Implies(Prop vid1 empty) (Geq (f1 fid1 vid1) (f1 fid2 vid1)))
     ([[EvolveODE (OVar vid1) (Prop vid1 empty)]](Geq (f1 fid1 vid1) (f1 fid2 vid1))))"
*)
(*
Implies
  (Implies TT ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]]
     (Geq (Differential (Var vid1)) (Differential (Const 0)))))
  (Implies
     (Implies TT (Geq (Var vid1) (Const 0)))
     ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) TT]](Geq (Var vid1) (Const 0))))
*)

definition SystemDCSubst::"('sf,'sc,'sz) subst"
where "SystemDCSubst = 
  \<lparr> SFunctions = (\<lambda>
  f.  None),
    SPredicates = (\<lambda>p.  None),
    SContexts = (\<lambda>C. 
    if C = pid1 then
      Some TT
    else if C = pid2 then
      Some (Geq (Differential (Var vid1)) (Differential (Const 0)))
    else if C = pid3 then
      Some (Geq (Function fid1 empty) (Const 0)) 
    else 
     None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (trm.Var vid1))) else None)
  \<rparr>"

definition SystemVSubst::"('sf,'sc,'sz) subst"
where "SystemVSubst = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>a. if a = vid1 then 
      Some (EvolveODE (OProd 
                         (OSing vid1 (Function fid1 empty)) 
                         (OSing vid2 (Var vid1))) 
                      (And TT (Geq (Function fid1 empty) (Const 0)))) 
                      else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition SystemVSubst2::"('sf,'sc,'sz) subst"
where "SystemVSubst2 = 
  \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inl fid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>a. if a = vid1 then 
      Some (EvolveODE (OProd 
                         (OSing vid1 (Function fid1 empty)) 
                         (OSing vid2 (Var vid1))) 
                      TT) 
                      else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

definition SystemDESubst::"('sf,'sc,'sz) subst"
where "SystemDESubst = 
  \<lparr> SFunctions = (\<lambda>f. if f = fid1 then Some(Function (Inl fid1) empty) else None),
    SPredicates = (\<lambda>p. if p = vid2 then Some(And TT (Geq (Function (Inl fid1) empty) (Const 0))) else None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Geq (Differential (Var vid1)) (Differential (Const 0))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma systemdesubst_correct:"\<exists> ODE.(([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]] ((Geq (Differential (Var vid1)) (Differential (Const 0))))) \<leftrightarrow>
 ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (And TT (Geq (f0 fid1) (Const 0)))]]
    [[DiffAssign vid1 (f0 fid1)]](Geq (Differential (Var vid1)) (Differential (Const 0)))))
    = Fsubst ((([[EvolveODE (OProd (OSing vid1 (f1 fid1 vid1)) ODE) (p1 vid2 vid1)]] (P pid1)) \<leftrightarrow>
          ([[EvolveODE ((OProd  (OSing vid1 (f1 fid1 vid1))) ODE) (p1 vid2 vid1)]]
               [[DiffAssign vid1 (f1 fid1 vid1)]]P pid1))) SystemDESubst"
  apply(rule exI[where x="OSing vid2 (trm.Var vid1)"])
  by(auto simp add: f0_def f1_def Box_def Or_def Equiv_def empty_def TT_def P_def p1_def SystemDESubst_def empty_def)
  
\<comment> \<open>\<open>[{dx=, dy=x&r>=r&>=r}]r>=r&>=r->[D{x}:=]D{x}>=D{r}->\<close>\<close>
\<comment> \<open>\<open>[{dx=, dy=x&r>=r&>=r}]r>=r&>=r->\<close>\<close>
\<comment> \<open>\<open>[{dx=, dy=x&r>=r&>=r}][D{x}:=]D{x}>=D{r}\<close>\<close>
\<comment> \<open>\<open>([[$\<alpha> vid1]]((Predicational pid1) \<rightarrow> (Predicational pid2)))\<close>\<close>
\<comment> \<open>\<open>\<rightarrow> ([[$\<alpha> vid1]]Predicational pid1) \<rightarrow> ([[$\<alpha> vid1]]Predicational pid2)\<close>\<close>
definition SystemKSubst::"('sf,'sc,'sz) subst"
where "SystemKSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then 
        (Some (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0)))) 
      else if C = pid2 then 
        (Some ([[DiffAssign vid1 (Function fid1 empty)]](Geq (Differential (Var vid1)) (Differential (Const 0))))) else None),
    SPrograms = (\<lambda>c. if c = vid1 then Some (EvolveODE (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0)))) else None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma subst_imp_simp:"Fsubst (Implies p q) \<sigma> = (Implies (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Implies_def Or_def by auto

lemma subst_equiv_simp:"Fsubst (Equiv p q) \<sigma> = (Equiv (Fsubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Implies_def Or_def Equiv_def by auto

lemma subst_box_simp:"Fsubst (Box p q) \<sigma> = (Box (Psubst p \<sigma>) (Fsubst q \<sigma>))"
  unfolding Box_def Or_def by auto

lemma pfsubst_box_simp:"PFsubst (Box p q) \<sigma> = (Box (PPsubst p \<sigma>) (PFsubst q \<sigma>))"
  unfolding Box_def Or_def by auto

lemma pfsubst_imp_simp:"PFsubst (Implies p q) \<sigma> = (Implies (PFsubst p \<sigma>) (PFsubst q \<sigma>))"
  unfolding Box_def Implies_def Or_def by auto

definition SystemDWSubst::"('sf,'sc,'sz) subst"
where "SystemDWSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then Some (And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>c. if c = vid1 then Some (OProd (OSing vid1 (Function fid1 empty)) (OSing vid2 (Var vid1))) else None)
  \<rparr>"

definition SystemCESubst::"('sf,'sc,'sz) subst"
where "SystemCESubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>_. None),
    SContexts = (\<lambda>C. if C = pid1 then Some(Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]](Predicational (Inr ())))) else None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma SystemCESubstOK:
  "step_ok 
  ([([],[Equiv (Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]]( SystemCEFml1))) 
         (Implies(And (Geq (Const 0) (Const 0)) (Geq (Function fid1 empty) (Const 0))) ([[DiffAssign vid1 (Function fid1 empty)]]( (SystemCEFml2))))
         ])],
         ([],[]))
         
         0 
         (CE SystemCEFml1 SystemCEFml2 SystemCESubst)"
  apply(rule Step_CE)
       subgoal by(auto simp add: subst_equiv_simp subst_imp_simp subst_box_simp SystemCESubst_def SystemCEFml1_def SystemCEFml2_def pfsubst_imp_simp pfsubst_box_simp)
      subgoal using CE1pre_valid 
        by (auto simp add: CEReq_def SystemCEFml1_def SystemCEFml2_def CE1pre_valid)
     subgoal unfolding SystemCEFml1_def by auto
    subgoal unfolding SystemCEFml2_def by auto
   subgoal unfolding SystemCESubst_def ssafe_def Implies_def Box_def Or_def empty_def by auto
  unfolding SystemCESubst_def Equiv_def Or_def SystemCEFml1_def SystemCEFml2_def TUadmit_def apply (auto simp add: TUadmit_def FUadmit_def Box_def Implies_def Or_def)
     unfolding PFUadmit_def by auto
  
\<comment> \<open>\<open>[D{x}:=f]Dv{x}>=r<->f>=r\<close>\<close>
\<comment> \<open>\<open>[[DiffAssign vid1  ($f fid1 empty)]] (Prop vid1 (singleton (DiffVar vid1))))\<close>\<close>
\<comment> \<open>\<open>\<leftrightarrow> Prop vid1 (singleton ($f fid1 empty))\<close>\<close>
definition SystemDiffAssignSubst::"('sf,'sc,'sz) subst"
where "SystemDiffAssignSubst = \<lparr> SFunctions = (\<lambda>f.  None),
    SPredicates = (\<lambda>p. if p = vid1 then Some (Geq (Function (Inr vid1) empty) (Const 0)) else None),
    SContexts = (\<lambda>_. None),
    SPrograms = (\<lambda>_. None),
    SODEs = (\<lambda>_. None)
  \<rparr>"

lemma SystemDICutCorrect:"SystemDICut = Fsubst DIGeqaxiom SystemDISubst"
  unfolding SystemDICut_def DIGeqaxiom_def SystemDISubst_def 
  by (auto simp add: f1_def p1_def f0_def Implies_def Or_def id_simps TT_def Box_def empty_def)

\<comment> \<open>\<open>v\<ge>0 \<and> A()\<ge>0 \<rightarrow> [{x'=v, v'=A()}]v\<ge>0\<close>\<close>
definition SystemProof :: "('sf, 'sc, 'sz) pf"
where "SystemProof =
  (SystemConcl, [
  (0, Rrule ImplyR 0)
  ,(0, Lrule AndL 0)
  ,(0, Cut SystemDICut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule ImplyL 0)
  ,(Suc (Suc 0), CloseId 0 0)
  ,(Suc 0, AxSubst ADIGeq SystemDISubst) \<comment> \<open>8\<close>
  ,(Suc 0, Rrule ImplyR 0)
  \<^cancel>\<open>,(0, CloseId 0 0)\<close>
  ,(Suc 0, CloseId 1 0)        
  \<^cancel>\<open>,(0, Rrule AndR 0)\<close>
  ,(0, Rrule ImplyR 0)   
  ,(0, Cut SystemDCCut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideR 0)
  ,(0, AxSubst ADC SystemDCSubst) \<comment> \<open>17\<close>
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Cut SystemVCut)
  ,(0, Lrule ImplyL 0) 
  ,(0, Rrule CohideRR 0)
  ,(0, Cut SystemDECut)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideRR 0)
  ,(1, CloseId (Suc 1) 0) \<comment> \<open>Last step\<close>
  ,(Suc 1, CloseId 0 0)
  ,(1, AxSubst AV SystemVSubst) \<comment> \<open>28\<close>
  ,(0, Cut SystemVCut2)
  
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(Suc 1, CloseId 0 0)
  ,(Suc 1, CloseId (Suc 2) 0)
  
  ,(Suc 1, AxSubst AV SystemVSubst2) \<comment> \<open>34\<close>
  ,(0, Rrule CohideRR 0)
  ,(0, DEAxiomSchema (OSing vid2 (trm.Var vid1)) SystemDESubst) \<comment> \<open>36\<close>
  ,(0, Cut SystemKCut)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, Lrule ImplyL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, AxSubst AK SystemKSubst) \<comment> \<open>42\<close>
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideR 0)
  ,(1, AxSubst ADW SystemDWSubst) \<comment> \<open>45\<close>
  ,(0, G)
  ,(0, Cut SystemEquivCut)
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideR 0)
  ,(0, CloseId 0 0)
  ,(0, Rrule CohideR 0)
  ,(0, CE SystemCEFml1 SystemCEFml2 SystemCESubst) \<comment> \<open>52\<close>
  ,(0, Rrule ImplyR 0)
  ,(0, Lrule AndL 0)
  ,(0, Cut SystemDiffAssignCut) 
  ,(0, Lrule EquivBackwardL 0)
  ,(0, Rrule CohideRR 0)
  ,(0, CloseId 0 0)
  ,(0, CloseId 1 0)
  ,(0, AxSubst Adassign SystemDiffAssignSubst) \<comment> \<open>60\<close>
  ])"
  
lemma system_result_correct:"proof_result SystemProof = 
  ([],
  ([],[Implies (And (Geq (Var vid1) (Const 0)) (Geq (f0 fid1) (Const 0)))
        ([[EvolveODE (OProd (OSing vid1 (f0 fid1)) (OSing vid2 (Var vid1))) (TT)]]Geq (Var vid1) (Const 0))]))"
  unfolding SystemProof_def SystemConcl_def Implies_def Or_def f0_def TT_def Equiv_def SystemDICut_def SystemDCCut_def
  proof_result.simps deriv_result.simps start_proof.simps  Box_def SystemDCSubst_def SystemVCut_def SystemDECut_def SystemKCut_def SystemEquivCut_def
  SystemDiffAssignCut_def SystemVCut2_def
    (* slow *)
  apply( simp add:  prover)
  done

lemma SystemSound_lemma:"sound (proof_result SystemProof)"
  apply(rule proof_sound)
  unfolding SystemProof_def SystemConcl_def CQ1Concl_def CQ2Concl_def Equiv_def CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
  diff_var_axiom_def SystemDICut_def
  (* slow *)
  apply (auto simp add: prover CEProof_def CEReq_def CQ1Concl_def CQ2Concl_def Equiv_def
    CQRightSubst_def diff_const_axiom_valid diff_var_axiom_valid empty_def Or_def expand_singleton 
    TUadmit_def NTUadmit_def almost_diff_const CQLeftSubst_def almost_diff_var f0_def TT_def SystemDISubst_def f1_def p1_def SystemDCCut_def SystemDCSubst_def
    SystemVCut_def SystemDECut_def SystemVSubst_def
    SystemVCut2_def SystemVSubst2_def  SystemDESubst_def P_def SystemKCut_def  SystemKSubst_def SystemDWSubst_def SystemEquivCut_def
    SystemCESubst_def SystemCEFml1_def SystemCEFml2_def CE1pre_valid2 SystemDiffAssignCut_def SystemDiffAssignSubst_def)
  done

lemma system_sound:"sound ([], SystemConcl)"
  using SystemSound_lemma system_result_correct unfolding SystemConcl_def by auto
  
lemma DIAnd_result_correct:"proof_result (proof_take 61 DIAndProof) = DIAnd"
  unfolding DIAndProof_def DIAndConcl_def Implies_def Or_def 
  proof_result.simps deriv_result.simps start_proof.simps DIAndCutP12_def  DIAndSG1_def DIAndSG2_def DIAndCutP1_def Box_def DIAndCut34Elim1_def DIAndCut12Intro_def DIAndCut34Elim2_def DIAnd_def
  using pne12 pne13 pne14 pne23 pne24 pne34 by (auto)

theorem DIAnd_sound: "sound DIAnd"
  using DIAndSound_lemma DIAnd_result_correct by auto

end end
 
