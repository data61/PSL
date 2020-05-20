section \<open>Program statements, Hoare and refinement rules\<close>

theory Statements
imports Assertion_Algebra
begin

text \<open>In this section we introduce assume, if, and while program statements
as well as Hoare triples, and data refienment. We prove Hoare correctness
rules for the program statements and we prove some theorems linking Hoare
correctness statement to (data) refinement. Most of the theorems assume
a monotonic boolean transformers algebra. The theorem stating the 
equivalence between a Hoare
correctness triple and a refinement statement holds under the
assumption that we have a monotonic boolean transformers algebra with
post condition statement.\<close>

definition
  "assume" :: "'a::mbt_algebra Assertion \<Rightarrow> 'a"  ("[\<cdot> _ ]" [0] 1000) where
  "[\<cdot>p] =  {\<cdot>p} ^ o"

lemma [simp]: "{\<cdot>p} * \<top> \<sqinter> [\<cdot>p] = {\<cdot>p}"
  apply (subgoal_tac "{\<cdot>p} \<in> assertion")
  apply (subst (asm) assertion_def, simp add: assume_def)
  by simp

lemma [simp]: "[\<cdot>p] * x \<squnion> {\<cdot>-p} * \<top> = [\<cdot>p] * x"
  by (simp add: assume_def  uminus_Assertion_def)

lemma [simp]: "{\<cdot>p} * \<top> \<squnion> [\<cdot>-p] * x = [\<cdot>-p] * x"
  by (simp add: assume_def  uminus_Assertion_def)

lemma assert_sup: "{\<cdot>p \<squnion> q} = {\<cdot>p} \<squnion> {\<cdot>q}"
  by (simp add: sup_Assertion_def)

lemma assert_inf: "{\<cdot>p \<sqinter> q} = {\<cdot>p} \<sqinter> {\<cdot>q}"
  by (simp add: inf_Assertion_def)

lemma assert_neg: "{\<cdot>-p} = neg_assert {\<cdot>p}"
  by (simp add: uminus_Assertion_def)

lemma assert_false [simp]: "{\<cdot>\<bottom>} = \<bottom>"
  by (simp add: bot_Assertion_def)

lemma if_Assertion_assumption: "({\<cdot>p} * x) \<squnion> ({\<cdot>-p} * y) = ([\<cdot>p] * x) \<sqinter> ([\<cdot>-p] * y)"
proof -
    have "({\<cdot>p} * x) \<squnion> {\<cdot>-p} * y = ({\<cdot>p} * \<top> \<sqinter> [\<cdot>p]) * x \<squnion> ({\<cdot>-p} * \<top> \<sqinter> [\<cdot>-p]) * y" by simp
    also have "\<dots> = ({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ({\<cdot>-p} * \<top> \<sqinter> ([\<cdot>-p] * y))" by (unfold inf_comp, simp)
    also have "\<dots> = (({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ({\<cdot>-p} * \<top>)) \<sqinter> (({\<cdot>p} * \<top> \<sqinter> ([\<cdot>p] * x)) \<squnion> ([\<cdot>-p] * y))" by (simp add: sup_inf_distrib)
    also have "\<dots> = (({\<cdot>p} * \<top>  \<squnion> ({\<cdot>-p} * \<top>)) \<sqinter> (([\<cdot>p] * x))) \<sqinter> (([\<cdot>-p] * y) \<sqinter> (([\<cdot>p] * x) \<squnion> ([\<cdot>-p] * y)))"
      by (simp add: sup_inf_distrib2)
    also have "\<dots> = ([\<cdot>p] * x) \<sqinter>  ([\<cdot>-p] * y) \<sqinter> (([\<cdot>p] * x) \<squnion> ([\<cdot>-p] * y))"
      apply (simp add: sup_comp [THEN sym] )
      by (simp add: assert_sup [THEN sym] inf_assoc)
    also have "\<dots> = ([\<cdot>p] * x) \<sqinter>  ([\<cdot>-p] * y)"
      by (rule antisym, simp_all add: inf_assoc)
    finally show ?thesis .
  qed

definition
  "wp x p = abs_wpt (x * {\<cdot>p})"

lemma wp_assume: "wp [\<cdot>p] q = -p \<squnion> q"
  apply (simp add: wp_def abs_wpt_def)
  apply (rule assert_injective)
  apply simp
  by (simp add: assert_sup assert_neg assume_def wpt_dual_assertion_comp)

lemma assert_commute: "y \<in> conjunctive \<Longrightarrow> y * {\<cdot>p} = {\<cdot> wp y p } * y"
  apply (simp add: wp_def abs_wpt_def)
  by (rule assertion_commute, simp_all)

lemma wp_assert: "wp {\<cdot>p} q = p \<sqinter> q"
  by (simp add: wp_def assertion_inf_comp_eq [THEN sym] assert_inf [THEN sym])

lemma wp_mono [simp]: "mono (wp x)"
  apply (simp add: le_fun_def wp_def abs_wpt_def less_eq_Assertion_def mono_def)
  apply (simp add: wpt_def, safe)
  apply (rule_tac y = " x * {\<cdot> xa } * \<top>" in order_trans, simp_all)
  apply (rule le_comp_right)
  by (rule le_comp, simp)

lemma wp_mono2: "p \<le> q \<Longrightarrow> wp x p \<le> wp x q"
  apply (cut_tac x = x in wp_mono)
  apply (unfold mono_def)
  by blast

lemma wp_fun_mono [simp]: "mono wp"
  apply (simp add: le_fun_def wp_def abs_wpt_def less_eq_Assertion_def mono_def)
  apply (simp add: wpt_def, safe)
  apply (rule_tac y = " x * {\<cdot> xa } * \<top>" in order_trans, simp_all)
  apply (rule le_comp_right)
  by (rule le_comp_right, simp) 


lemma wp_fun_mono2: "x \<le> y \<Longrightarrow> wp x p \<le> wp y p"
  apply (cut_tac wp_fun_mono)
  apply (unfold mono_def)
  apply (simp add: le_fun_def)
  by blast


lemma wp_comp: "wp (x * y) p = wp x (wp y p)"
  apply (simp add: wp_def abs_wpt_def)
  by (unfold wpt_comp_2 [THEN sym] mult.assoc, simp)

lemma wp_choice: "wp (x \<sqinter> y) = wp x \<sqinter> wp y"
  apply (simp add: fun_eq_iff wp_def inf_fun_def inf_comp inf_Assertion_def abs_wpt_def)
  by (simp add: wpt_choice)

lemma [simp]: "wp 1 = id"
  apply (unfold fun_eq_iff, safe)
  apply (rule assert_injective)
  by (simp add: wp_def abs_wpt_def)

lemma wp_omega_fix: "wp (x ^ \<omega>) p = wp x (wp (x ^ \<omega>) p) \<sqinter> p"
  apply (subst omega_fix)
  by (simp add: wp_choice wp_comp)

lemma wp_omega_least: "(wp x r) \<sqinter> p \<le> r \<Longrightarrow> wp (x ^ \<omega>) p \<le> r"
  apply (simp add: wp_def abs_wpt_def inf_Assertion_def less_eq_Assertion_def)
  apply (simp add: wpt_def)
  apply (rule_tac y = "{\<cdot>r} * \<top> \<sqinter> 1" in order_trans)
  apply simp
  apply (rule_tac y = "x ^ \<omega> * {\<cdot> p } * \<top>" in order_trans, simp)
  apply (simp add: mult.assoc)
  apply (rule omega_least)
  apply (drule_tac z = \<top> in le_comp_right)
  apply (simp add: inf_comp mult.assoc [THEN sym])
  by (simp add: assertion_prop)

lemma Assertion_wp: "{\<cdot>wp x p} = (x * {\<cdot>p} * \<top>) \<sqinter> 1"
  apply (simp add: wp_def abs_wpt_def)
  by (simp add: wpt_def)

definition
  "hoare p S q = (p \<le> wp S q)"

definition
  "grd x = - (wp x \<bottom>)"

lemma grd_comp: "[\<cdot>grd x] * x = x"
  apply (simp add: grd_def wp_def uminus_Assertion_def assume_def neg_assert_def abs_wpt_def dual_sup sup_comp)
  apply (simp add: wpt_def dual_inf sup_comp dual_comp bot_Assertion_def)
  by (rule antisym, simp_all)

lemma assert_assume: "{\<cdot>p} * [\<cdot>p] = {\<cdot> p}"
  by (simp add: assume_def)

lemma dual_assume: "[\<cdot>p] ^ o = {\<cdot>p}"
  by (simp add: assume_def)

lemma assume_prop: "([\<cdot>p] * \<bottom>) \<squnion> 1 = [\<cdot>p]"
  by (simp add: assume_def dual_assertion_prop)

text\<open>An alternative definition of a Hoare triple\<close>

definition "hoare1 p S q = ([\<cdot> p ] * S * [\<cdot> -q ] = \<top>)"

lemma "hoare1  p S q = hoare p S q"
  apply (simp add: hoare1_def dual_inf dual_comp)
  apply (simp add: hoare_def wp_def less_eq_Assertion_def abs_wpt_def)
  apply (simp add: wpt_def)
  apply safe
  proof -
    assume A: "[\<cdot> p ] * S * [\<cdot> - q ] = \<top>"
    have "{\<cdot>p} \<le> {\<cdot>p} * \<top>" by simp
    also have "... \<le> {\<cdot>p} * \<top> * \<bottom>" by (unfold mult.assoc, simp)
    also have "... = {\<cdot>p} * [\<cdot> p ] * S * [\<cdot> - q ] * \<bottom>" by (subst A [THEN sym], simp add: mult.assoc)
    also have "... = {\<cdot>p} * S * [\<cdot> - q ] * \<bottom>" by (simp add: assert_assume)
    also have "... \<le> {\<cdot>p} * S * {\<cdot> q } * \<top>"
      apply (simp add: mult.assoc)
      apply (rule le_comp, rule le_comp)
      apply (simp add: assume_def uminus_Assertion_def)
      by (simp add: neg_assert_def dual_inf dual_comp sup_comp)
    also have "... \<le> S * {\<cdot> q } * \<top>" by (simp add: mult.assoc)
    finally show "{\<cdot>p} \<le> S * {\<cdot> q } * \<top>" .
  next
    assume A: "{\<cdot> p } \<le> S * {\<cdot> q } * \<top>"
    have "\<top> = ((S * {\<cdot>q}) ^ o) * \<bottom> \<squnion> S * {\<cdot>q} * \<top>" by simp
    also have "\<dots> \<le> [\<cdot>p] * \<bottom> \<squnion> S * {\<cdot>q} * \<top>"
      apply (simp del: dual_neg_top)
      apply (rule_tac y = "[\<cdot>p] * \<bottom>" in order_trans, simp_all)
      apply (subst dual_le)
      apply (simp add: dual_comp dual_assume)
      apply (cut_tac x = "{\<cdot>p}" and y = "S * {\<cdot>q} * \<top>" and z = \<top> in le_comp_right)
      apply (rule A)
      by (simp add: mult.assoc)
    also have "\<dots> = [\<cdot>p] * S * ({\<cdot>q} * \<top>)"
      apply (subst (2) assume_prop [THEN sym])
      by (simp_all add: sup_comp mult.assoc)
    also have "\<dots> \<le> [\<cdot>p] * S * ({\<cdot>q} * \<top> \<squnion> 1)"
      by (rule le_comp, simp)
    also have "\<dots> = [\<cdot>p] * S * [\<cdot>-q]"
      apply (simp add: assume_def uminus_Assertion_def)
      by (simp add: neg_assert_def dual_inf dual_comp)
    finally show "[\<cdot>p] * S * [\<cdot> - q] = \<top>"
      by (rule_tac antisym, simp_all)
  qed

lemma hoare_choice: "hoare p (x \<sqinter> y) q = ((hoare p) x q & (hoare p y q))"
  apply (unfold hoare_def wp_choice inf_fun_def)
  by auto

definition
  if_stm:: "'a::mbt_algebra Assertion \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" ("(If (_)/ then (_)/ else (_))" [0, 0, 10] 10) where
  "if_stm b x y = (([\<cdot> b ] * x) \<sqinter> ([\<cdot> -b ] * y))"

lemma if_assertion: "(If p then x else y) = {\<cdot>p} * x \<squnion> {\<cdot> -p} * y"
  by (simp add: if_stm_def if_Assertion_assumption)

lemma (in boolean_algebra) sup_neg_inf:
  "(p \<le> q \<squnion> r) = (p \<sqinter> -q \<le> r)"
  apply (safe)
  apply(cut_tac a = p and c = "q \<squnion> r" and b = "-q" and d = "-q" in inf_mono)
  apply simp apply simp apply (simp add: inf_sup_distrib2)
  apply(cut_tac b = "p \<sqinter> - q" and d = "r" and a = "q" and c = "q" in sup_mono)
  apply simp apply simp  by (simp add: sup_inf_distrib)

lemma hoare_if: "hoare p (If b then x else y) q = (hoare (p \<sqinter> b) x q \<and> hoare (p \<sqinter> -b) y q)"
  by (simp add: hoare_def if_stm_def wp_choice inf_fun_def wp_comp wp_assume sup_neg_inf)

lemma hoare_comp: "hoare p (x * y) q = (\<exists> r . (hoare p x r) \<and> (hoare r y q))"
   apply (simp add: hoare_def wp_comp)
   apply safe
   apply (rule_tac x = "wp y q" in exI, simp)
   apply (rule_tac y = "wp x r" in order_trans, simp)
   apply (rule_tac f = "wp x" in monoD)
   by simp_all

lemma hoare_refinement: "hoare p S q = ({\<cdot>p} * (post {\<cdot>q}) \<le> S)"
  apply (simp add: hoare_def less_eq_Assertion_def Assertion_wp)
  proof
    assume A: "{\<cdot>p} \<le> S * {\<cdot>q} * \<top>"
    have "{\<cdot>p} * post {\<cdot>q} = ({\<cdot>p} * \<top> \<sqinter> 1) * post {\<cdot>q}" by (simp add: assertion_prop)
    also have "\<dots> = {\<cdot>p} * \<top> \<sqinter> post {\<cdot>q}" by (simp add: inf_comp)
    also have "\<dots> \<le> S * {\<cdot>q} * \<top> \<sqinter> post {\<cdot>q}" apply simp
      apply (rule_tac y = "{\<cdot>p} * \<top>" in order_trans, simp_all)
      apply (cut_tac x = "{\<cdot>p}" and y = "S * {\<cdot>q} * \<top>" and z = \<top> in le_comp_right)
      by (rule A, simp)
    also have "\<dots> \<le> S" by (simp add: post_2)
    finally show "{\<cdot>p} * post {\<cdot>q} \<le> S".
  next
    assume A: "{\<cdot>p} * post {\<cdot>q} \<le> S"
    have "{\<cdot>p} = {\<cdot>p} * \<top> \<sqinter> 1" by (simp add: assertion_prop)
    also have "\<dots> = {\<cdot>p} * ((post {\<cdot>q}) * {\<cdot>q} * \<top>) \<sqinter> 1" by (simp add: post_1)
    also have "\<dots> \<le> {\<cdot>p} * ((post {\<cdot>q}) * {\<cdot>q} * \<top>)" by simp
    also have "\<dots> \<le> S * {\<cdot>q} * \<top>" 
      apply (cut_tac x = "{\<cdot>p} * post {\<cdot>q}" and y = S and z = "{\<cdot>q} * \<top>" in le_comp_right)
      apply (simp add: A)
      by (simp add: mult.assoc)
    finally show "{\<cdot>p} \<le> S * {\<cdot>q} * \<top>" .
  qed

 theorem hoare_fixpoint_mbt:
  "F x = x
     \<Longrightarrow> (!! (w::'a::well_founded) f . (\<And>v. v < w \<Longrightarrow> hoare (p v) f q) \<Longrightarrow> hoare (p w) (F f) q) 
     \<Longrightarrow> hoare (p u) x q"
  apply (rule less_induct1)
  proof -
    fix xa
    assume A: "\<And> w f. (\<And> v . v < w \<Longrightarrow> hoare (p v) f q) \<Longrightarrow> hoare (p w) (F f) q"
    assume B: "F x  = x"
    assume C: "\<And>y . y < xa \<Longrightarrow> hoare (p y) x q"
    have D: "hoare (p xa) (F x) q"
      apply (rule A)
      by (rule C, simp)
    show "hoare (p xa) x q"
      by (cut_tac D, simp add: B)
    qed

lemma hoare_Sup: "hoare (Sup P) x q = (\<forall> p \<in> P . hoare p x q)" 
  apply (simp add: hoare_def)
  apply auto
  apply (rule_tac y = "Sup P" in order_trans, simp_all add: Sup_upper)
  apply (rule Sup_least)
  by simp

theorem hoare_fixpoint_complete_mbt:
  "F x = x
     \<Longrightarrow> (!! w f . hoare (Sup_less p w) f q \<Longrightarrow> hoare (p w) (F f) q) 
     \<Longrightarrow> hoare (Sup (range p)) x q"
  apply (simp add: hoare_Sup Sup_less_def, safe)
  apply (rule_tac F = F in hoare_fixpoint_mbt)
  by auto

definition
  while:: "'a::mbt_algebra Assertion \<Rightarrow> 'a \<Rightarrow> 'a" ("(While (_)/ do (_))" [0, 10] 10) where
  "while p x = ([\<cdot> p] * x) ^ \<omega> * [\<cdot> -p ]"

lemma while_false: "(While \<bottom> do x) = 1"
  apply (unfold while_def)
  apply (subst omega_fix)
  by (simp_all add: assume_def)

lemma while_true: "(While \<top> do 1) = \<bottom>"
  apply (unfold while_def)
  by (rule antisym, simp_all add: assume_def)

lemma hoare_wp [simp]: "hoare (wp x q) x q"
  by (simp add: hoare_def)

lemma hoare_comp_wp: "hoare p (x * y) q = hoare p x (wp y q)"
  apply (unfold hoare_comp, safe)
  apply (simp add: hoare_def)
  apply (rule_tac y = "wp x r" in order_trans, simp)
  apply (rule wp_mono2, simp)
  by (rule_tac x = "wp y q" in exI, simp)

lemma (in mbt_algebra) hoare_assume: "hoare p [\<cdot>b] q = (p \<sqinter> b \<le> q)"
  by (simp add: hoare_def wp_assume sup_neg_inf)

lemma (in mbt_algebra) hoare_assume_comp: "hoare p ([\<cdot>b] * x) q = hoare (p \<sqinter> b) x q"
  apply (simp add: hoare_comp_wp hoare_assume)
  by (simp add: hoare_def)

lemma hoare_while_mbt:
  "(\<forall> (w::'b::well_founded) r . (\<forall> v . v < w \<longrightarrow> p v \<le> r) \<longrightarrow> hoare ((p w) \<sqinter> b) x r) \<Longrightarrow> 
       (\<forall> u . p u \<le> q) \<Longrightarrow> hoare  (p w) (While b do x) (q \<sqinter> -b)"
  apply (unfold while_def)
  apply (rule_tac F = "\<lambda>z. [\<cdot> b ] * x * z \<sqinter> [\<cdot> - b ]" in hoare_fixpoint_mbt)
  apply (simp add: mult.assoc [THEN sym])
  apply (simp add: omega_comp_fix)
  apply (unfold hoare_choice)
  apply safe
  apply (subst hoare_comp_wp)
  apply (subst hoare_assume_comp)
  apply (drule_tac x = w in spec)
  apply (drule_tac x = "wp f (q \<sqinter> - b)" in spec)
  apply (auto simp add: hoare_def) [1]
  apply (auto simp add: hoare_assume)
  apply (rule_tac y = "p w" in order_trans)
  by simp_all

lemma hoare_while_complete_mbt:
  "(\<forall> w::'b::well_founded . hoare ((p w) \<sqinter> b) x (Sup_less p w)) \<Longrightarrow> 
       hoare  (Sup (range p)) (While b do x) ((Sup (range p)) \<sqinter> -b)"
  apply (simp add: hoare_Sup, safe)
  apply (rule hoare_while_mbt)
  apply safe
  apply (drule_tac x = w in spec)
  apply (simp add: hoare_def)
  apply (rule_tac y = "wp x (Sup_less p w)" in order_trans, simp_all)
  apply (rule wp_mono2)
  apply (simp add: Sup_less_def)
  apply (rule Sup_least, auto)
  by (rule SUP_upper, simp)

definition 
  "datarefin S S1 D D1 = (D * S \<le> S1 * D1)"

lemma "hoare p S q \<Longrightarrow> datarefin S S1 D D1 \<Longrightarrow> hoare (wp D p) S1 (wp D1 q)"
  apply (simp add: hoare_def datarefin_def)
  apply (simp add: wp_comp [THEN sym] mult.assoc [THEN sym])
  apply (rule_tac y = "wp (D * S) q" in order_trans)
  apply (subst wp_comp)
  apply (rule monoD, simp_all)
  by (rule wp_fun_mono2, simp_all)

lemma "hoare p S q \<Longrightarrow> datarefin ({\<cdot>p} * S) S1 D D1 \<Longrightarrow> hoare (wp D p) S1 (wp D1 q)"
  apply (simp add: hoare_def datarefin_def)
  apply (rule_tac y = "wp (D * {\<cdot>p} * S) q" in order_trans)
  apply (simp add: mult.assoc)
  apply (subst wp_comp)
  apply (rule monoD, simp_all)
  apply (subst wp_comp)
  apply (unfold wp_assert, simp)
  apply (unfold wp_comp [THEN sym])
  apply (rule wp_fun_mono2)
  by (simp add: mult.assoc)

lemma inf_pres_conj: "x \<in> conjunctive \<Longrightarrow> y \<in> conjunctive \<Longrightarrow> x \<sqinter> y \<in> conjunctive"
  apply (subst conjunctive_def, safe)
  apply (simp add: inf_comp conjunctiveD)
  by (metis (hide_lams, no_types) inf_assoc inf_left_commute)

lemma sup_pres_disj: "x \<in> disjunctive \<Longrightarrow> y \<in> disjunctive \<Longrightarrow> x \<squnion> y \<in> disjunctive"
  apply (subst disjunctive_def, safe)
  apply (simp add: sup_comp disjunctiveD)
  by (metis (hide_lams, no_types) sup_assoc sup_left_commute)

lemma assumption_conjuncive [simp]: "[\<cdot>p] \<in> conjunctive"
  by (simp add: assume_def dual_disjunctive assertion_disjunctive)

lemma assumption_disjuncive [simp]: "[\<cdot>p] \<in> disjunctive"
  by (simp add: assume_def dual_conjunctive assertion_conjunctive)

lemma if_pres_conj: "x \<in> conjunctive \<Longrightarrow> y \<in> conjunctive \<Longrightarrow> (If p then x else y) \<in> conjunctive"
  apply (unfold if_stm_def)
  by (simp add: inf_pres_conj comp_pres_conj)

lemma if_pres_disj: "x \<in> disjunctive \<Longrightarrow> y \<in> disjunctive \<Longrightarrow> (If p then x else y) \<in> disjunctive"
  apply (unfold if_assertion)
  by (simp add: sup_pres_disj comp_pres_disj assertion_disjunctive)

lemma while_dual_star: "(While p do (x::'a::mbt_algebra)) = (({\<cdot> p} * x)^\<otimes> * {\<cdot> -p })"
  apply (simp add: while_def)
  apply (rule antisym)
  apply (rule omega_least)
   proof -
     have "([\<cdot> p] * x * (({\<cdot> p} * x)^\<otimes> * {\<cdot>-p}) \<sqinter> [\<cdot>-p]) = ({\<cdot> p} * x * (({\<cdot> p} * x)^\<otimes> * {\<cdot>-p})) \<squnion> {\<cdot>-p}"
        apply (unfold mult.assoc)
        by (cut_tac p = p and x = "(x * (({\<cdot> p } * x)^\<otimes> * {\<cdot> -p }))" and y = 1 in if_Assertion_assumption, simp)
     also have "\<dots> = ({\<cdot> p} * x)^\<otimes> * {\<cdot>-p}"
        by (simp add: mult.assoc [THEN sym], simp add: dual_star_comp_fix [THEN sym])
     finally show "[\<cdot> p ] * x * (({\<cdot> p } * x)^\<otimes> * {\<cdot> - p }) \<sqinter> [\<cdot> - p ] \<le> ({\<cdot> p } * x)^\<otimes> * {\<cdot> - p }" by simp
   next
     show "({\<cdot> p } * x)^\<otimes> * {\<cdot> - p } \<le> ([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ]"
       apply (rule dual_star_least)
       proof -
        have "{\<cdot> p } * x * (([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ]) \<squnion> {\<cdot> - p } = [\<cdot> p ] * x * (([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ]) \<sqinter> [\<cdot> - p ]"
        apply (unfold mult.assoc)
        by (cut_tac p = p and x = "(x * (([\<cdot>p] * x)^\<omega> * [\<cdot>-p]))" and y = 1 in if_Assertion_assumption, simp)
        also have "... = ([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ]"
          apply (simp add: mult.assoc [THEN sym])
          by (metis omega_comp_fix)
        finally show "{\<cdot> p } * x * (([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ]) \<squnion> {\<cdot> - p } \<le> ([\<cdot> p ] * x) ^ \<omega> * [\<cdot> - p ] " by simp
     qed
   qed

lemma while_pres_disj: "(x::'a::mbt_algebra) \<in> disjunctive \<Longrightarrow> (While p do x) \<in> disjunctive"
  apply (unfold while_dual_star)
  apply (rule comp_pres_disj)
  apply (rule dual_star_pres_disj)
  by (rule comp_pres_disj, simp_all add: assertion_disjunctive)

lemma while_pres_conj: "(x::'a::mbt_algebra_fusion) \<in> conjunctive \<Longrightarrow> (While p do x) \<in> conjunctive"
  apply(unfold while_def)
  by (simp add: comp_pres_conj omega_pres_conj)

no_notation
  bot  ("\<bottom>") and
  top  ("\<top>") and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

no_syntax
  "_INF1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Sqinter>_./ _)" [0, 10] 10)
  "_INF"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Sqinter>_\<in>_./ _)" [0, 0, 10] 10)
  "_SUP1"     :: "pttrns \<Rightarrow> 'b \<Rightarrow> 'b"           ("(3\<Squnion>_./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn \<Rightarrow> 'a set \<Rightarrow> 'b \<Rightarrow> 'b"  ("(3\<Squnion>_\<in>_./ _)" [0, 0, 10] 10)

end

