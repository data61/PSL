(* Author: Tobias Nipkow *)

section "Backward Analysis of Expressions"

theory Abs_Int2
imports Abs_Int1 "HOL-IMP.Vars"
begin

instantiation prod :: (preord,preord) preord
begin

definition "le_prod p1 p2 = (fst p1 \<sqsubseteq> fst p2 \<and> snd p1 \<sqsubseteq> snd p2)"

instance
proof (standard, goal_cases)
  case 1 show ?case by(simp add: le_prod_def)
next
  case 2 thus ?case unfolding le_prod_def by(metis le_trans)
qed

end

hide_const bot

class L_top_bot = SL_top +
fixes meet :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<sqinter>" 65)
and bot :: "'a" ("\<bottom>")
assumes meet_le1 [simp]: "x \<sqinter> y \<sqsubseteq> x"
and meet_le2 [simp]: "x \<sqinter> y \<sqsubseteq> y"
and meet_greatest: "x \<sqsubseteq> y \<Longrightarrow> x \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> y \<sqinter> z"
assumes bot[simp]: "\<bottom> \<sqsubseteq> x"
begin

lemma mono_meet: "x \<sqsubseteq> x' \<Longrightarrow> y \<sqsubseteq> y' \<Longrightarrow> x \<sqinter> y \<sqsubseteq> x' \<sqinter> y'"
by (metis meet_greatest meet_le1 meet_le2 le_trans)

end

locale Val_abs1_gamma =
  Gamma where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set" +
assumes inter_gamma_subset_gamma_meet:
  "\<gamma> a1 \<inter> \<gamma> a2 \<subseteq> \<gamma>(a1 \<sqinter> a2)"
and gamma_Bot[simp]: "\<gamma> \<bottom> = {}"
begin

lemma in_gamma_meet: "x : \<gamma> a1 \<Longrightarrow> x : \<gamma> a2 \<Longrightarrow> x : \<gamma>(a1 \<sqinter> a2)"
by (metis IntI inter_gamma_subset_gamma_meet subsetD)

lemma gamma_meet[simp]: "\<gamma>(a1 \<sqinter> a2) = \<gamma> a1 \<inter> \<gamma> a2"
by (metis equalityI inter_gamma_subset_gamma_meet le_inf_iff mono_gamma meet_le1 meet_le2)

end


locale Val_abs1 =
  Val_abs1_gamma where \<gamma> = \<gamma>
   for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set" +
fixes test_num' :: "val \<Rightarrow> 'av \<Rightarrow> bool"
and filter_plus' :: "'av \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
and filter_less' :: "bool \<Rightarrow> 'av \<Rightarrow> 'av \<Rightarrow> 'av * 'av"
assumes test_num': "test_num' n a = (n : \<gamma> a)"
and filter_plus': "filter_plus' a a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1+n2 : \<gamma> a \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"
and filter_less': "filter_less' (n1<n2) a1 a2 = (b1,b2) \<Longrightarrow>
  n1 : \<gamma> a1 \<Longrightarrow> n2 : \<gamma> a2 \<Longrightarrow> n1 : \<gamma> b1 \<and> n2 : \<gamma> b2"


locale Abs_Int1 =
  Val_abs1 where \<gamma> = \<gamma> for \<gamma> :: "'av::L_top_bot \<Rightarrow> val set"
begin

lemma in_gamma_join_UpI: "s : \<gamma>\<^sub>o S1 \<or> s : \<gamma>\<^sub>o S2 \<Longrightarrow> s : \<gamma>\<^sub>o(S1 \<squnion> S2)"
by (metis (no_types) join_ge1 join_ge2 mono_gamma_o rev_subsetD)

fun aval'' :: "aexp \<Rightarrow> 'av st option \<Rightarrow> 'av" where
"aval'' e None = \<bottom>" |
"aval'' e (Some sa) = aval' e sa"

lemma aval''_sound: "s : \<gamma>\<^sub>o S \<Longrightarrow> aval a s : \<gamma>(aval'' a S)"
by(cases S)(simp add: aval'_sound)+

subsection "Backward analysis"

fun afilter :: "aexp \<Rightarrow> 'av \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"afilter (N n) a S = (if test_num' n a then S else None)" |
"afilter (V x) a S = (case S of None \<Rightarrow> None | Some S \<Rightarrow>
  let a' = lookup S x \<sqinter> a in
  if a' \<sqsubseteq> \<bottom> then None else Some(update S x a'))" |
"afilter (Plus e1 e2) a S =
 (let (a1,a2) = filter_plus' a (aval'' e1 S) (aval'' e2 S)
  in afilter e1 a1 (afilter e2 a2 S))"

text\<open>The test for @{const bot} in the @{const V}-case is important: @{const
bot} indicates that a variable has no possible values, i.e.\ that the current
program point is unreachable. But then the abstract state should collapse to
@{const None}. Put differently, we maintain the invariant that in an abstract
state of the form @{term"Some s"}, all variables are mapped to non-@{const
bot} values. Otherwise the (pointwise) join of two abstract states, one of
which contains @{const bot} values, may produce too large a result, thus
making the analysis less precise.\<close>


fun bfilter :: "bexp \<Rightarrow> bool \<Rightarrow> 'av st option \<Rightarrow> 'av st option" where
"bfilter (Bc v) res S = (if v=res then S else None)" |
"bfilter (Not b) res S = bfilter b (\<not> res) S" |
"bfilter (And b1 b2) res S =
  (if res then bfilter b1 True (bfilter b2 True S)
   else bfilter b1 False S \<squnion> bfilter b2 False S)" |
"bfilter (Less e1 e2) res S =
  (let (res1,res2) = filter_less' res (aval'' e1 S) (aval'' e2 S)
   in afilter e1 res1 (afilter e2 res2 S))"

lemma afilter_sound: "s : \<gamma>\<^sub>o S \<Longrightarrow> aval e s : \<gamma> a \<Longrightarrow> s : \<gamma>\<^sub>o (afilter e a S)"
proof(induction e arbitrary: a S)
  case N thus ?case by simp (metis test_num')
next
  case (V x)
  obtain S' where "S = Some S'" and "s : \<gamma>\<^sub>f S'" using \<open>s : \<gamma>\<^sub>o S\<close>
    by(auto simp: in_gamma_option_iff)
  moreover hence "s x : \<gamma> (lookup S' x)" by(simp add: \<gamma>_st_def)
  moreover have "s x : \<gamma> a" using V by simp
  ultimately show ?case using V(1)
    by(simp add: lookup_update Let_def \<gamma>_st_def)
      (metis mono_gamma emptyE in_gamma_meet gamma_Bot subset_empty)
next
  case (Plus e1 e2) thus ?case
    using filter_plus'[OF _ aval''_sound[OF Plus(3)] aval''_sound[OF Plus(3)]]
    by (auto split: prod.split)
qed

lemma bfilter_sound: "s : \<gamma>\<^sub>o S \<Longrightarrow> bv = bval b s \<Longrightarrow> s : \<gamma>\<^sub>o(bfilter b bv S)"
proof(induction b arbitrary: S bv)
  case Bc thus ?case by simp
next
  case (Not b) thus ?case by simp
next
  case (And b1 b2) thus ?case
    apply hypsubst_thin
    apply (fastforce simp: in_gamma_join_UpI)
    done
next
  case (Less e1 e2) thus ?case
    apply hypsubst_thin
    apply (auto split: prod.split)
    apply (metis afilter_sound filter_less' aval''_sound Less(1))
    done
qed


fun step' :: "'av st option \<Rightarrow> 'av st option acom \<Rightarrow> 'av st option acom"
 where
"step' S (SKIP {P}) = (SKIP {S})" |
"step' S (x ::= e {P}) =
  x ::= e {case S of None \<Rightarrow> None | Some S \<Rightarrow> Some(update S x (aval' e S))}" |
"step' S (c1;; c2) = step' S c1;; step' (post c1) c2" |
"step' S (IF b THEN c1 ELSE c2 {P}) =
  (let c1' = step' (bfilter b True S) c1; c2' = step' (bfilter b False S) c2
   in IF b THEN c1' ELSE c2' {post c1 \<squnion> post c2})" |
"step' S ({Inv} WHILE b DO c {P}) =
   {S \<squnion> post c}
   WHILE b DO step' (bfilter b True Inv) c
   {bfilter b False Inv}"

definition AI :: "com \<Rightarrow> 'av st option acom option" where
"AI = lpfp\<^sub>c (step' \<top>)"

lemma strip_step'[simp]: "strip(step' S c) = strip c"
by(induct c arbitrary: S) (simp_all add: Let_def)


subsection "Soundness"

lemma in_gamma_update:
  "\<lbrakk> s : \<gamma>\<^sub>f S; i : \<gamma> a \<rbrakk> \<Longrightarrow> s(x := i) : \<gamma>\<^sub>f(update S x a)"
by(simp add: \<gamma>_st_def lookup_update)

lemma step_preserves_le:
  "\<lbrakk> S \<subseteq> \<gamma>\<^sub>o S'; cs \<le> \<gamma>\<^sub>c ca \<rbrakk> \<Longrightarrow> step S cs \<le> \<gamma>\<^sub>c (step' S' ca)"
proof(induction cs arbitrary: ca S S')
  case SKIP thus ?case by(auto simp:SKIP_le map_acom_SKIP)
next
  case Assign thus ?case
    by (fastforce simp: Assign_le  map_acom_Assign intro: aval'_sound in_gamma_update
      split: option.splits del:subsetD)
next
  case Seq thus ?case apply (auto simp: Seq_le map_acom_Seq)
    by (metis le_post post_map_acom)
next
  case (If b cs1 cs2 P)
  then obtain ca1 ca2 Pa where
      "ca= IF b THEN ca1 ELSE ca2 {Pa}"
      "P \<subseteq> \<gamma>\<^sub>o Pa" "cs1 \<le> \<gamma>\<^sub>c ca1" "cs2 \<le> \<gamma>\<^sub>c ca2"
    by (fastforce simp: If_le map_acom_If)
  moreover have "post cs1 \<subseteq> \<gamma>\<^sub>o(post ca1 \<squnion> post ca2)"
    by (metis (no_types) \<open>cs1 \<le> \<gamma>\<^sub>c ca1\<close> join_ge1 le_post mono_gamma_o order_trans post_map_acom)
  moreover have "post cs2 \<subseteq> \<gamma>\<^sub>o(post ca1 \<squnion> post ca2)"
    by (metis (no_types) \<open>cs2 \<le> \<gamma>\<^sub>c ca2\<close> join_ge2 le_post mono_gamma_o order_trans post_map_acom)
  ultimately show ?case using \<open>S \<subseteq> \<gamma>\<^sub>o S'\<close>
    by (simp add: If.IH subset_iff bfilter_sound)
next
  case (While I b cs1 P)
  then obtain ca1 Ia Pa where
    "ca = {Ia} WHILE b DO ca1 {Pa}"
    "I \<subseteq> \<gamma>\<^sub>o Ia" "P \<subseteq> \<gamma>\<^sub>o Pa" "cs1 \<le> \<gamma>\<^sub>c ca1"
    by (fastforce simp: map_acom_While While_le)
  moreover have "S \<union> post cs1 \<subseteq> \<gamma>\<^sub>o (S' \<squnion> post ca1)"
    using \<open>S \<subseteq> \<gamma>\<^sub>o S'\<close> le_post[OF \<open>cs1 \<le> \<gamma>\<^sub>c ca1\<close>, simplified]
    by (metis (no_types) join_ge1 join_ge2 le_sup_iff mono_gamma_o order_trans)
  ultimately show ?case by (simp add: While.IH subset_iff bfilter_sound)
qed

lemma AI_sound: "AI c = Some c' \<Longrightarrow> CS c \<le> \<gamma>\<^sub>c c'"
proof(simp add: CS_def AI_def)
  assume 1: "lpfp\<^sub>c (step' \<top>) c = Some c'"
  have 2: "step' \<top> c' \<sqsubseteq> c'" by(rule lpfpc_pfp[OF 1])
  have 3: "strip (\<gamma>\<^sub>c (step' \<top> c')) = c"
    by(simp add: strip_lpfpc[OF _ 1])
  have "lfp (step UNIV) c \<le> \<gamma>\<^sub>c (step' \<top> c')"
  proof(rule lfp_lowerbound[simplified,OF 3])
    show "step UNIV (\<gamma>\<^sub>c (step' \<top> c')) \<le> \<gamma>\<^sub>c (step' \<top> c')"
    proof(rule step_preserves_le[OF _ _])
      show "UNIV \<subseteq> \<gamma>\<^sub>o \<top>" by simp
      show "\<gamma>\<^sub>c (step' \<top> c') \<le> \<gamma>\<^sub>c c'" by(rule mono_gamma_c[OF 2])
    qed
  qed
  from this 2 show "lfp (step UNIV) c \<le> \<gamma>\<^sub>c c'"
    by (blast intro: mono_gamma_c order_trans)
qed


subsection "Commands over a set of variables"

text\<open>Key invariant: the domains of all abstract states are subsets of the
set of variables of the program.\<close>

definition "domo S = (case S of None \<Rightarrow> {} | Some S' \<Rightarrow> set(dom S'))"

definition Com :: "vname set \<Rightarrow> 'a st option acom set" where
"Com X = {c. \<forall>S \<in> set(annos c). domo S \<subseteq> X}"

lemma domo_Top[simp]: "domo \<top> = {}"
by(simp add: domo_def Top_st_def Top_option_def)

lemma bot_acom_Com[simp]: "\<bottom>\<^sub>c c \<in> Com X"
by(simp add: bot_acom_def Com_def domo_def)

lemma post_in_annos: "post c : set(annos c)"
by(induction c) simp_all

lemma domo_join: "domo (S \<squnion> T) \<subseteq> domo S \<union> domo T"
by(auto simp: domo_def join_st_def split: option.split)

lemma domo_afilter: "vars a \<subseteq> X \<Longrightarrow> domo S \<subseteq> X \<Longrightarrow> domo(afilter a i S) \<subseteq> X"
apply(induction a arbitrary: i S)
apply(simp add: domo_def)
apply(simp add: domo_def Let_def update_def lookup_def split: option.splits)
apply blast
apply(simp split: prod.split)
done

lemma domo_bfilter: "vars b \<subseteq> X \<Longrightarrow> domo S \<subseteq> X \<Longrightarrow> domo(bfilter b bv S) \<subseteq> X"
apply(induction b arbitrary: bv S)
apply(simp add: domo_def)
apply(simp)
apply(simp)
apply rule
apply (metis le_sup_iff subset_trans[OF domo_join])
apply(simp split: prod.split)
by (metis domo_afilter)

lemma step'_Com:
  "domo S \<subseteq> X \<Longrightarrow> vars(strip c) \<subseteq> X \<Longrightarrow> c : Com X \<Longrightarrow> step' S c : Com X"
apply(induction c arbitrary: S)
apply(simp add: Com_def)
apply(simp add: Com_def domo_def update_def split: option.splits)
apply(simp (no_asm_use) add: Com_def ball_Un)
apply (metis post_in_annos)
apply(simp (no_asm_use) add: Com_def ball_Un)
apply rule
apply (metis Un_assoc domo_join order_trans post_in_annos subset_Un_eq)
apply (metis domo_bfilter)
apply(simp (no_asm_use) add: Com_def)
apply rule
apply (metis domo_join le_sup_iff post_in_annos subset_trans)
apply rule
apply (metis domo_bfilter)
by (metis domo_bfilter)

end


subsection "Monotonicity"

locale Abs_Int1_mono = Abs_Int1 +
assumes mono_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> plus' a1 a2 \<sqsubseteq> plus' b1 b2"
and mono_filter_plus': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow> r \<sqsubseteq> r' \<Longrightarrow>
  filter_plus' r a1 a2 \<sqsubseteq> filter_plus' r' b1 b2"
and mono_filter_less': "a1 \<sqsubseteq> b1 \<Longrightarrow> a2 \<sqsubseteq> b2 \<Longrightarrow>
  filter_less' bv a1 a2 \<sqsubseteq> filter_less' bv b1 b2"
begin

lemma mono_aval': "S \<sqsubseteq> S' \<Longrightarrow> aval' e S \<sqsubseteq> aval' e S'"
by(induction e) (auto simp: le_st_def lookup_def mono_plus')

lemma mono_aval'': "S \<sqsubseteq> S' \<Longrightarrow> aval'' e S \<sqsubseteq> aval'' e S'"
apply(cases S)
 apply simp
apply(cases S')
 apply simp
by (simp add: mono_aval')

lemma mono_afilter: "r \<sqsubseteq> r' \<Longrightarrow> S \<sqsubseteq> S' \<Longrightarrow> afilter e r S \<sqsubseteq> afilter e r' S'"
apply(induction e arbitrary: r r' S S')
apply(auto simp: test_num' Let_def split: option.splits prod.splits)
apply (metis mono_gamma subsetD)
apply(rename_tac list a b c d, drule_tac x = "list" in mono_lookup)
apply (metis mono_meet le_trans)
apply (metis mono_meet mono_lookup mono_update)
apply(metis mono_aval'' mono_filter_plus'[simplified le_prod_def] fst_conv snd_conv)
done

lemma mono_bfilter: "S \<sqsubseteq> S' \<Longrightarrow> bfilter b r S \<sqsubseteq> bfilter b r S'"
apply(induction b arbitrary: r S S')
apply(auto simp: le_trans[OF _ join_ge1] le_trans[OF _ join_ge2] split: prod.splits)
apply(metis mono_aval'' mono_afilter mono_filter_less'[simplified le_prod_def] fst_conv snd_conv)
done

lemma mono_step': "S \<sqsubseteq> S' \<Longrightarrow> c \<sqsubseteq> c' \<Longrightarrow> step' S c \<sqsubseteq> step' S' c'"
apply(induction c c' arbitrary: S S' rule: le_acom.induct)
apply (auto simp: mono_post mono_bfilter mono_update mono_aval' Let_def le_join_disj
  split: option.split)
done

lemma mono_step'2: "mono (step' S)"
by(simp add: mono_def mono_step'[OF le_refl])

end

end
