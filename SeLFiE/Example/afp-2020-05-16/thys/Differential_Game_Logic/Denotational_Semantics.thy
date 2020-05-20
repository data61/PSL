theory "Denotational_Semantics" 
imports
  "HOL-Analysis.Derivative"
  "Syntax"         
begin
section \<open>Denotational Semantics\<close>

text \<open>Defines the denotational semantics of Differential Game Logic. \<^url>\<open>https://doi.org/10.1145/2817824\<close> \<^url>\<open>https://doi.org/10.1007/978-3-319-94205-6_15\<close>\<close>

subsection \<open>States\<close>

text \<open>Vector of reals over ident\<close>
type_synonym Rvec = "variable \<Rightarrow> real"
type_synonym state = "Rvec"


text \<open>the set of all worlds\<close>
definition worlds:: "state set"
  where "worlds = {\<nu>. True}"

text \<open>the set of all variables\<close>
abbreviation allvars:: "variable set"
  where "allvars \<equiv> {x::variable. True}"

text \<open>the set of all real variables\<close>
abbreviation allrvars:: "variable set"
  where "allrvars \<equiv> {RVar x | x. True}"

text \<open>the set of all differential variables\<close>
abbreviation alldvars:: "variable set"
  where "alldvars \<equiv> {DVar x | x. True}"

  
lemma ident_finite: "finite({x::ident. True})"
  by auto

lemma allvar_cases: "allvars = allrvars \<union> alldvars"
  using variable.exhaust by blast 

lemma rvar_finite: "finite allrvars"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>x. RVar x\<close>] by (simp add: full_SetCompr_eq) 

lemma dvar_finite: "finite alldvars"
  using finite_imageI[OF ident_finite, where h=\<open>\<lambda>x. DVar x\<close>] by (simp add: full_SetCompr_eq) 

lemma allvars_finite [simp]: "finite(allvars)"
  using allvar_cases dvar_finite rvar_finite by (metis finite_Un) 
  
  
definition Vagree :: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> bool"
  where "Vagree \<nu> \<nu>' V \<equiv> (\<forall>i. i\<in>V \<longrightarrow> \<nu>(i) = \<nu>'(i))"

definition Uvariation :: "state \<Rightarrow> state \<Rightarrow> variable set \<Rightarrow> bool"
  where "Uvariation \<nu> \<nu>' U \<equiv> (\<forall>i. ~(i\<in>U) \<longrightarrow> \<nu>(i) = \<nu>'(i))"

lemma Uvariation_Vagree [simp]: "Uvariation \<nu> \<nu>' (-V) = Vagree \<nu> \<nu>' V"
  unfolding Vagree_def Uvariation_def by simp

  
lemma Vagree_refl [simp]: "Vagree \<nu> \<nu> V"
  by (auto simp add: Vagree_def)

lemma Vagree_sym: "Vagree \<nu> \<nu>' V = Vagree \<nu>' \<nu> V"
  by (auto simp add: Vagree_def)

lemma Vagree_sym_rel [sym]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu>' \<nu> V"
  using Vagree_sym by auto

lemma Vagree_union [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree \<nu> \<nu>' W \<Longrightarrow> Vagree \<nu> \<nu>' (V\<union>W)"
  by (auto simp add: Vagree_def)

lemma Vagree_trans [trans]: "Vagree \<nu> \<nu>' V \<Longrightarrow> Vagree  \<nu>' \<nu>'' W \<Longrightarrow> Vagree \<nu> \<nu>'' (V\<inter>W)"
  by (auto simp add: Vagree_def)

lemma Vagree_antimon [simp]: "Vagree \<nu> \<nu>' V \<and> W\<subseteq>V \<longrightarrow> Vagree \<nu> \<nu>' W"
  by (auto simp add: Vagree_def)

lemma Vagree_empty [simp]: "Vagree \<nu> \<nu>' {}"
  by (auto simp add: Vagree_def)

lemma Uvariation_empty [simp]: "Uvariation \<nu> \<nu>' {} = (\<nu>=\<nu>')"
  by (auto simp add: Uvariation_def)

lemma Vagree_univ [simp]: "Vagree \<nu> \<nu>' allvars = (\<nu>=\<nu>')"
  by (auto simp add: Vagree_def)

lemma Uvariation_univ [simp]: "Uvariation \<nu> \<nu>' allvars"
  by (auto simp add: Uvariation_def)

lemma Vagree_and [simp]: "Vagree \<nu> \<nu>' V \<and> Vagree \<nu> \<nu>' W \<longleftrightarrow> Vagree \<nu> \<nu>' (V\<union>W)"
  by (auto simp add: Vagree_def)

lemma Vagree_or: "Vagree \<nu> \<nu>' V \<or> Vagree \<nu> \<nu>' W \<longrightarrow> Vagree \<nu> \<nu>' (V\<inter>W)"
  by (auto simp add: Vagree_def)

lemma Uvariation_refl [simp]: "Uvariation \<nu> \<nu> V"
  by (auto simp add: Uvariation_def)

lemma Uvariation_sym: "Uvariation \<omega> \<nu> U = Uvariation \<nu> \<omega> U"
  unfolding Uvariation_def by auto

lemma Uvariation_sym_rel [sym]: "Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<nu> \<omega> U"
  using Uvariation_sym by auto

lemma Uvariation_trans [trans]: "Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<nu> \<mu> V \<Longrightarrow> Uvariation \<omega> \<mu> (U\<union>V)"
  unfolding Uvariation_def by simp

lemma Uvariation_mon [simp]: "V \<supseteq> U \<Longrightarrow> Uvariation \<omega> \<nu> U \<Longrightarrow> Uvariation \<omega> \<nu> V"
  unfolding Uvariation_def by auto


  
subsection Interpretations

lemma mon_mono: "mono r = ((\<forall>X Y. (X\<subseteq>Y \<longrightarrow> r(X)\<subseteq>r(Y))))"
  unfolding mono_def by simp
 
text \<open>interpretations of symbols in ident\<close>
type_synonym interp_rep =
 "(ident \<Rightarrow> real) \<times> (ident \<Rightarrow> (real \<Rightarrow> real)) \<times> (ident \<Rightarrow> (real \<Rightarrow> bool)) \<times> (ident \<Rightarrow> (state set \<Rightarrow> state set))"

definition is_interp :: "interp_rep \<Rightarrow> bool"
 where "is_interp I \<equiv> case I of (_, _, _, G) \<Rightarrow> (\<forall>a. mono (G a))"

typedef interp = "{I:: interp_rep. is_interp I}"
  morphisms raw_interp well_interp
proof
 show "(\<lambda>f. 0, \<lambda>f x. 0, \<lambda>p x. True, \<lambda>a. \<lambda>X. X) \<in> {I. is_interp I}" unfolding is_interp_def mono_def by simp
qed

setup_lifting type_definition_interp

lift_definition Consts::"interp \<Rightarrow> ident \<Rightarrow> (real)" is "\<lambda>(F0, _, _, _). F0" .
lift_definition Funcs:: "interp \<Rightarrow> ident \<Rightarrow> (real \<Rightarrow> real)" is "\<lambda>(_, F, _, _). F" .
lift_definition Preds:: "interp \<Rightarrow> ident \<Rightarrow> (real \<Rightarrow> bool)" is "\<lambda>(_, _, P, _). P" .
lift_definition Games:: "interp \<Rightarrow> ident \<Rightarrow> (state set \<Rightarrow> state set)" is "\<lambda>(_, _, _, G). G" .

text \<open>make interpretations\<close>
lift_definition mkinterp:: "(ident \<Rightarrow> real) \<times> (ident \<Rightarrow> (real \<Rightarrow> real)) \<times> (ident \<Rightarrow> (real \<Rightarrow> bool)) \<times> (ident \<Rightarrow> (state set \<Rightarrow> state set))
\<Rightarrow> interp" 
  is "\<lambda>(C, F, P, G). if \<forall>a. mono (G a) then (C, F, P, G) else (C, F, P, \<lambda>_ _. {})"
  by (auto split: prod.splits simp: mono_def is_interp_def)

lemma Consts_mkinterp [simp]: "Consts (mkinterp(C,F,P,G)) = C"
  apply (transfer fixing: C F P G)
  apply (auto simp add: is_interp_def mono_def)
  done

lemma Funcs_mkinterp [simp]: "Funcs (mkinterp(C,F,P,G)) = F"
  apply (transfer fixing: C F P G)
  apply (auto simp add: is_interp_def mono_def)
  done
  
lemma Preds_mkinterp [simp]: "Preds (mkinterp(C,F,P,G)) = P"
  apply (transfer fixing: C F P G)
  apply (auto simp add: is_interp_def mono_def)
  done

lemma Games_mkinterp [simp]: "(\<And>a. mono (G a) ) \<Longrightarrow> Games (mkinterp(C,F,P,G)) = G"
  apply (transfer fixing: C F P G)
  apply (auto simp add: is_interp_def mono_def)
  done

lemma mkinterp_eq [iff]: "(Consts I = Consts J \<and> Funcs I = Funcs J \<and> Preds I = Preds J \<and> Games I = Games J) = (I=J)"
  apply (transfer fixing: C F P G)
  apply (auto simp add: is_interp_def mono_def)
  done
  
lemma [simp]: "X\<subseteq>Y \<Longrightarrow> (Games I a)(X)\<subseteq>(Games I a)(Y)"
  apply (transfer fixing: a X Y)
  apply (auto simp add: is_interp_def mono_def)
  apply (blast)
  done

lifting_update interp.lifting
lifting_forget interp.lifting


subsection Semantics

text \<open>Semantic modification \<open>repv \<omega> x r\<close> replaces the value of variable \<open>x\<close> in the state \<open>\<omega>\<close> with r\<close>
definition repv :: "state \<Rightarrow> variable \<Rightarrow> real \<Rightarrow> state"
  where "repv \<omega> x r = fun_upd \<omega> x r"

lemma repv_def_correct: "repv \<omega> x r = (\<lambda>y. if x = y then r else \<omega>(y))"
  unfolding repv_def by auto 

lemma repv_access [simp]: "(repv \<omega> x r)(y) = (if (x=y) then r else \<omega>(y))"
  unfolding repv_def by simp

lemma repv_self [simp]: "repv \<omega> x (\<omega>(x)) = \<omega>"
  unfolding repv_def by auto

lemma Vagree_repv: "Vagree \<omega> (repv \<omega> x d) (-{x})"
  unfolding repv_def Vagree_def by simp

lemma Vagree_repv_self: "Vagree \<omega> (repv \<omega> x d) {x} = (d=\<omega>(x))"
  unfolding repv_def Vagree_def by auto

lemma Uvariation_repv: "Uvariation \<omega> (repv \<omega> x d) {x}"
  unfolding repv_def Uvariation_def by simp

paragraph \<open>Semantics of Terms\<close>

fun term_sem :: "interp \<Rightarrow> trm \<Rightarrow> (state \<Rightarrow> real)"
where
  "term_sem I (Var x) = (\<lambda>\<omega>. \<omega>(x))"
| "term_sem I (Number r) = (\<lambda>\<omega>. r)"
| "term_sem I (Const f) = (\<lambda>\<omega>. (Consts I f))"
| "term_sem I (Func f \<theta>) = (\<lambda>\<omega>. (Funcs I f)(term_sem I \<theta> \<omega>))"
| "term_sem I (Plus \<theta> \<eta>) = (\<lambda>\<omega>. term_sem I \<theta> \<omega> + term_sem I \<eta> \<omega>)"
| "term_sem I (Times \<theta> \<eta>) = (\<lambda>\<omega>. term_sem I \<theta> \<omega> * term_sem I \<eta> \<omega>)"
| "term_sem I (Differential \<theta>) = (\<lambda>\<omega>. sum(\<lambda>x. \<omega>(DVar x)*deriv(\<lambda>X. term_sem I \<theta> (repv \<omega> (RVar x) X))(\<omega>(RVar x)))(allidents))"
  
paragraph \<open>Solutions of Differential Equations\<close>

(*@note For simplicity, solutions are not limited to a smaller interval of existence*)
type_synonym solution = "real \<Rightarrow> state"

definition solves_ODE :: "interp \<Rightarrow> solution \<Rightarrow> ident \<Rightarrow> trm \<Rightarrow> bool"
where "solves_ODE I F x \<theta> \<equiv> (\<forall>\<zeta>::real.
     Vagree (F(0)) (F(\<zeta>)) (-{RVar x, DVar x})
   \<and> F(\<zeta>)(DVar x) = deriv(\<lambda>t. F(t)(RVar x))(\<zeta>)
   \<and> F(\<zeta>)(DVar x) = term_sem I \<theta> (F(\<zeta>)))"

paragraph \<open>Semantics of Formulas and Games\<close>
  
fun fml_sem :: "interp \<Rightarrow> fml \<Rightarrow> (state set)" and
   game_sem :: "interp \<Rightarrow> game \<Rightarrow> (state set \<Rightarrow> state set)"
where
  "fml_sem I (Pred p \<theta>) = {\<omega>. (Preds I p)(term_sem I \<theta> \<omega>)}"
| "fml_sem I (Geq \<theta> \<eta>) = {\<omega>. term_sem I \<theta> \<omega> \<ge> term_sem I \<eta> \<omega>}"
| "fml_sem I (Not \<phi>) = {\<omega>. \<omega> \<notin> fml_sem I \<phi>}"
| "fml_sem I (And \<phi> \<psi>) = fml_sem I \<phi> \<inter> fml_sem I \<psi>"
| "fml_sem I (Exists x \<phi>) = {\<omega>. \<exists>r. (repv \<omega> x r) \<in> fml_sem I \<phi>}"
| "fml_sem I (Diamond \<alpha> \<phi>) = game_sem I \<alpha> (fml_sem I \<phi>)"

| "game_sem I (Game a) = (\<lambda>X. (Games I a)(X))"
| "game_sem I (Assign x \<theta>) = (\<lambda>X. {\<omega>. (repv \<omega> x (term_sem I \<theta> \<omega>)) \<in> X})"
| "game_sem I (Test \<phi>) = (\<lambda>X. fml_sem I \<phi> \<inter> X)"
| "game_sem I (Choice \<alpha> \<beta>) = (\<lambda>X. game_sem I \<alpha> X \<union> game_sem I \<beta> X)"
| "game_sem I (Compose \<alpha> \<beta>) = (\<lambda>X. game_sem I \<alpha> (game_sem I \<beta> X))"
| "game_sem I (Loop \<alpha>) = (\<lambda>X. \<Inter>{Z. X \<union> game_sem I \<alpha> Z \<subseteq> Z})"
| "game_sem I (Dual \<alpha>) = (\<lambda>X. -(game_sem I \<alpha> (-X)))"
| "game_sem I (ODE x \<theta>) = (\<lambda>X. {\<omega>. \<exists>F T. Vagree \<omega> (F(0)) (-{DVar x}) \<and> F(T) \<in> X \<and> solves_ODE I F x \<theta>})"


text \<open>Validity\<close>

definition valid_in :: "interp \<Rightarrow> fml \<Rightarrow> bool"
where "valid_in I \<phi> \<equiv> (\<forall>\<omega>. \<omega> \<in> fml_sem I \<phi>)"

definition valid :: "fml \<Rightarrow> bool"
  where "valid \<phi> \<equiv> (\<forall>I.\<forall>\<omega>. \<omega> \<in> fml_sem I \<phi>)"

lemma valid_is_valid_in_all: "valid \<phi> = (\<forall>I. valid_in I \<phi>)"
  unfolding valid_def valid_in_def by auto

definition locally_sound :: "inference \<Rightarrow> bool"
  where "locally_sound R \<equiv>
  (\<forall>I. (\<forall>k. 0\<le>k \<longrightarrow> k<length (fst R) \<longrightarrow> valid_in I (nth (fst R) k)) \<longrightarrow> valid_in I (snd R))"

definition sound :: "inference \<Rightarrow> bool"
  where "sound R \<equiv>
  (\<forall>k. 0\<le>k \<longrightarrow> k<length (fst R) \<longrightarrow> valid (nth (fst R) k)) \<longrightarrow> valid (snd R)"

lemma locally_sound_is_sound: "locally_sound R \<Longrightarrow> sound R"
  unfolding locally_sound_def sound_def using valid_is_valid_in_all by auto


subsection \<open>Monotone Semantics\<close>

lemma monotone_Test [simp]: "X\<subseteq>Y \<Longrightarrow> game_sem I (Test \<phi>) X \<subseteq> game_sem I (Test \<phi>) Y"
  by auto

lemma monotone [simp]: "X\<subseteq>Y \<Longrightarrow> game_sem I \<alpha> X \<subseteq> game_sem I \<alpha> Y"
proof (induction \<alpha> arbitrary: X Y rule: game_induct)
  case (Game a)
  then show ?case by simp
next
  case (Assign x \<theta>)
  then show ?case by auto
next
  case (Test \<phi>)
  then show ?case by auto
next
  case (Choice \<alpha>1 \<alpha>2)
  then show ?case by (metis Un_mono game_sem.simps(4))
next
  case (Compose \<alpha>1 \<alpha>2)
  then show ?case by auto
next
  case (Loop \<alpha>)
  then show ?case by auto
next
  case (Dual \<alpha>)
  then show ?case by auto
next
  case (ODE x \<theta>)
  then show ?case by auto
qed

corollary game_sem_mono [simp]: "mono (\<lambda>X. game_sem I \<alpha> X)"
  by (simp add: mon_mono)

corollary game_union: "game_sem I \<alpha> (X\<union>Y) \<supseteq> game_sem I \<alpha> X \<union> game_sem I \<alpha> Y"
  by simp

lemmas game_sem_union = game_union


subsection \<open>Fixpoint Semantics Alternative for Loops\<close>

lemma game_sem_loop_fixpoint_mono: "mono (\<lambda>Z. X \<union> game_sem I \<alpha> Z)"
  using game_sem_mono by (metis Un_mono mon_mono order_refl) 

text \<open>Consequence of Knaster-Tarski Theorem 3.5 of \<^url>\<open>https://doi.org/10.1145/2817824\<close>\<close>

lemma game_sem_loop: "game_sem I (Loop \<alpha>) = (\<lambda>X. lfp(\<lambda>Z. X \<union> game_sem I \<alpha> Z))"
proof-
  have "\<Inter>{Z. X \<union> game_sem I \<alpha> Z \<subseteq> Z} = lfp(\<lambda>Z. X \<union> game_sem I \<alpha> Z)" by (simp add: lfp_def)
  then show ?thesis by (simp add: lfp_def)
qed

corollary game_sem_loop_back: "(\<lambda>X. lfp(\<lambda>Z. X \<union> game_sem I \<alpha> Z)) = game_sem I (Loop \<alpha>)"
  using game_sem_loop by simp

corollary game_sem_loop_iterate: "game_sem I (Loop \<alpha>) = (\<lambda>X. X \<union> game_sem I \<alpha> (game_sem I (Loop \<alpha>) X))"
  by (metis (no_types) game_sem_loop game_sem_loop_fixpoint_mono lfp_fixpoint)

corollary game_sem_loop_unwind: "game_sem I (Loop \<alpha>) = (\<lambda>X. X \<union> game_sem I (Compose \<alpha> (Loop \<alpha>)) X)"
using game_sem_loop_iterate by (metis game_sem.simps(5))

corollary game_sem_loop_unwind_reduce: "(\<lambda>X. X \<union> game_sem I (Compose \<alpha> (Loop \<alpha>)) X) = game_sem I (Loop \<alpha>)"
  using game_sem_loop_unwind by (rule sym)

lemmas lfp_ordinal_induct_set_cases = lfp_ordinal_induct_set [case_names mono step union]

(* Read off a fixpoint induction scheme from the fact that loops have a least fixpoint semantics *)
lemma game_loop_induct [case_names step union]: 
  "(\<And>Z. Z \<subseteq> game_sem I (Loop \<alpha>) X \<Longrightarrow> P(Z) \<Longrightarrow> P(X \<union> game_sem I \<alpha> Z))
  \<Longrightarrow> (\<And>M. (\<forall>Z\<in>M. P(Z)) \<Longrightarrow> P(Sup M))
  \<Longrightarrow> P(game_sem I (Loop \<alpha>) X)"
proof-
  assume loopstep: "\<And>Z. Z \<subseteq> game_sem I (Loop \<alpha>) X \<Longrightarrow> P(Z) \<Longrightarrow>  P(X \<union> game_sem I \<alpha> Z)"
  assume loopsup: "\<And>M. (\<forall>Z\<in>M. P(Z)) \<Longrightarrow> P(Sup M)"
  have "P(lfp(\<lambda>Z. X \<union> game_sem I \<alpha> Z))"
  proof (induction rule: lfp_ordinal_induct[where f=\<open>\<lambda>Z. X \<union> game_sem I \<alpha> Z\<close>])
    case mono
    then show ?case using game_sem_loop_fixpoint_mono by simp
  next
    case (step S)
    then show ?case using loopstep[where Z=S] game_sem_loop[where I=I and \<alpha>=\<alpha>] by (simp add: loopstep)
  next
    case (union M)
    then show ?case using loopsup game_sem_loop by auto
  qed
  then show "P(game_sem I (Loop \<alpha>) X)" using game_sem_loop by simp
  (*proof (induction rule: lfp_ordinal_induct_set_cases[where f=\<open>\<lambda>Z. X \<union> game_sem I \<alpha> Z\<close>])
    case mono
    then show ?case using game_sem_loop_fixpoint_mono by simp
  next
    case (step S)
    then show ?case using loopstep by auto
  next
    case (union M)
    then show ?case using loopsup game_sem_loop by auto
  qed*)
qed


subsection \<open>Some Simple Obvious Observations\<close>

lemma fml_sem_not [simp]: "fml_sem I (Not \<phi>) = -fml_sem I \<phi>"
  by auto

lemma fml_sem_not_not [simp]: "fml_sem I (Not (Not \<phi>)) = fml_sem I \<phi>"
  by simp

lemma fml_sem_or [simp]: "fml_sem I (Or \<phi> \<psi>) = fml_sem I \<phi> \<union> fml_sem I \<psi>"
  unfolding Or_def by auto

lemma fml_sem_implies [simp]: "fml_sem I (Implies \<phi> \<psi>) = (-fml_sem I \<phi>) \<union> fml_sem I \<psi>"
  unfolding Implies_def by auto

lemma TT_valid [simp]: "valid TT"
  unfolding valid_def TT_def by simp

paragraph \<open>Semantic equivalence of formulas\<close>

definition fml_equiv:: "fml => fml => bool"
  where "fml_equiv \<phi> \<psi> \<equiv> (\<forall>I. fml_sem I \<phi> = fml_sem I \<psi>)"

text \<open>Substitutionality for Equivalent Formulas\<close>

lemma fml_equiv_subst: "fml_equiv \<phi> \<psi> \<Longrightarrow> P (fml_sem I \<phi>) \<Longrightarrow> P (fml_sem I \<psi>)"
proof-
  assume a1: "fml_equiv \<phi> \<psi>"
  assume a2: "P (fml_sem I \<phi>)"
  from a1 have "fml_sem I \<phi> = fml_sem I \<psi>" using fml_equiv_def by blast
  then show ?thesis using forw_subst a2 by simp
qed
  
lemma valid_fml_equiv: "valid (\<phi> \<leftrightarrow> \<psi>) = fml_equiv \<phi> \<psi>"
  unfolding valid_def Equiv_def Or_def fml_equiv_def by auto

lemma valid_in_equiv: "valid_in I (\<phi> \<leftrightarrow> \<psi>) = ((fml_sem I \<phi>) = (fml_sem I \<psi>))"
  using valid_in_def Equiv_def Or_def by auto

lemma valid_in_impl: "valid_in I (\<phi> \<rightarrow> \<psi>) = ((fml_sem I \<phi>) \<subseteq> (fml_sem I \<psi>))"
  unfolding valid_in_def Implies_def Or_def by auto

lemma valid_equiv: "valid (\<phi> \<leftrightarrow> \<psi>) = (\<forall>I. fml_sem I \<phi> = fml_sem I \<psi>)"
  using valid_fml_equiv fml_equiv_def by auto

lemma valid_impl: "valid (\<phi> \<rightarrow> \<psi>) = (\<forall>I. (fml_sem I \<phi>) \<subseteq> (fml_sem I \<psi>))"
  unfolding valid_def Implies_def Or_def by auto

lemma fml_sem_equals [simp]: "(\<omega> \<in> fml_sem I (Equals \<theta> \<eta>)) = (term_sem I \<theta> \<omega> = term_sem I \<eta> \<omega>)"
  unfolding valid_def Equals_def Or_def by auto

lemma equiv_refl_valid [simp]: "valid (\<phi> \<leftrightarrow> \<phi>)"
  unfolding valid_def Equiv_def Or_def by simp

lemma equal_refl_valid [simp]: "valid (Equals \<theta> \<theta>)"
  unfolding valid_def Equals_def Or_def by simp

lemma solves_ODE_alt : "solves_ODE I F x \<theta> \<equiv> (\<forall>\<zeta>::real.
     Vagree (F(0)) (F(\<zeta>)) (-{RVar x, DVar x})
   \<and> F(\<zeta>)(DVar x) = deriv(\<lambda>t. F(t)(RVar x))(\<zeta>)
   \<and> F(\<zeta>) \<in> fml_sem I (Equals (Var (DVar x)) \<theta>))"
   unfolding solves_ODE_def using fml_sem_equals by simp

paragraph \<open>Semantic equivalence of games\<close>

definition game_equiv:: "game => game => bool"
  where "game_equiv \<alpha> \<beta> \<equiv> (\<forall>I X. game_sem I \<alpha> X = game_sem I \<beta> X)"


text \<open>Substitutionality for Equivalent Games\<close>
  
lemma game_equiv_subst: "game_equiv \<alpha> \<beta> \<Longrightarrow> P (game_sem I \<alpha> X) \<Longrightarrow> P (game_sem I \<beta> X)"
proof-
  assume a1: "game_equiv \<alpha> \<beta>"
  assume a2: "P (game_sem I \<alpha> X)"
  from a1 have "game_sem I \<alpha> X = game_sem I \<beta> X" using game_equiv_def by blast
  then show ?thesis using forw_subst a2 by simp
qed

lemma game_equiv_subst_eq: "game_equiv \<alpha> \<beta> \<Longrightarrow> P (game_sem I \<alpha> X) == P (game_sem I \<beta> X)"
  by (simp add: game_equiv_def)

lemma skip_id [simp]: "game_sem I Skip X = X"
  unfolding Skip_def TT_def by auto

lemma loop_iterate_equiv: "game_equiv (Loop \<alpha>) (Choice Skip (Compose \<alpha> (Loop \<alpha>)))"
unfolding game_equiv_def  
proof (clarify)
  fix I X
  from game_sem_loop_unwind_reduce have "X \<union> game_sem I (Compose \<alpha> (Loop \<alpha>)) X = game_sem I (Loop \<alpha>) X" by metis
  then show "game_sem I (Loop \<alpha>) X = game_sem I (Choice Skip (Compose \<alpha> (Loop \<alpha>))) X" using skip_id by auto
qed


lemma fml_equiv_valid: "fml_equiv \<phi> \<psi> \<Longrightarrow> valid \<phi> = valid \<psi>"
  unfolding valid_def using fml_equiv_subst by blast

lemma solves_Vagree: "solves_ODE I F x \<theta> \<Longrightarrow> (\<And>\<zeta>. Vagree (F(\<zeta>)) (F(0)) (-{RVar x,DVar x}))"
  using solves_ODE_def Vagree_sym_rel by blast 

lemma solves_Vagree_trans: "Uvariation (F(0)) \<omega> U \<Longrightarrow> solves_ODE I F x \<theta> \<Longrightarrow> Uvariation (F(\<zeta>)) \<omega> (U\<union>{RVar x,DVar x})"
  using solves_Vagree Uvariation_Vagree solves_ODE_def
  by (metis Uvariation_sym_rel Uvariation_trans double_complement)  

end
