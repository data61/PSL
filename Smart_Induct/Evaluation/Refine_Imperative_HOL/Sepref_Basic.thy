section \<open>Basic Definitions\<close>
theory Sepref_Basic
imports 
  "HOL-Eisbach.Eisbach"
  Separation_Logic_Imperative_HOL.Sep_Main
  Refine_Monadic.Refine_Monadic
  "Lib/Sepref_Misc"
  "Lib/Structured_Apply"
  Sepref_Id_Op
begin
no_notation i_ANNOT (infixr ":::\<^sub>i" 10)
no_notation CONST_INTF (infixr "::\<^sub>i" 10)

text \<open>
  In this theory, we define the basic concept of refinement 
  from a nondeterministic program specified in the 
  Isabelle Refinement Framework to an imperative deterministic one 
  specified in Imperative/HOL.
\<close>

subsection \<open>Values on Heap\<close>
text \<open>We tag every refinement assertion with the tag \<open>hn_ctxt\<close>, to
  avoid higher-order unification problems when the refinement assertion 
  is schematic.\<close>
definition hn_ctxt :: "('a\<Rightarrow>'c\<Rightarrow>assn) \<Rightarrow> 'a \<Rightarrow> 'c \<Rightarrow> assn" 
  \<comment> \<open>Tag for refinement assertion\<close>
  where
  "hn_ctxt P a c \<equiv> P a c"

definition pure :: "('b \<times> 'a) set \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> assn"
  \<comment> \<open>Pure binding, not involving the heap\<close>
  where "pure R \<equiv> (\<lambda>a c. \<up>((c,a)\<in>R))"

lemma pure_app_eq: "pure R a c = \<up>((c,a)\<in>R)" by (auto simp: pure_def)

lemma pure_eq_conv[simp]: "pure R = pure R' \<longleftrightarrow> R=R'"
  unfolding pure_def 
  apply (rule iffI)
  apply safe
  apply (meson pure_assn_eq_conv)
  apply (meson pure_assn_eq_conv)
  done

lemma pure_rel_eq_false_iff: "pure R x y = false \<longleftrightarrow> (y,x)\<notin>R"
  by (auto simp: pure_def)
    
    
definition "is_pure P \<equiv> \<exists>P'. \<forall>x x'. P x x'=\<up>(P' x x')"
lemma is_pureI[intro?]: 
  assumes "\<And>x x'. P x x' = \<up>(P' x x')"
  shows "is_pure P"
  using assms unfolding is_pure_def by blast

lemma is_pureE:
  assumes "is_pure P"
  obtains P' where "\<And>x x'. P x x' = \<up>(P' x x')"
  using assms unfolding is_pure_def by blast

lemma pure_pure[simp]: "is_pure (pure P)"
  unfolding pure_def by rule blast
lemma pure_hn_ctxt[intro!]: "is_pure P \<Longrightarrow> is_pure (hn_ctxt P)"
  unfolding hn_ctxt_def[abs_def] .


definition "the_pure P \<equiv> THE P'. \<forall>x x'. P x x'=\<up>((x',x)\<in>P')"

lemma the_pure_pure[simp]: "the_pure (pure R) = R"
  unfolding pure_def the_pure_def
  by (rule theI2[where a=R]) auto

lemma is_pure_alt_def: "is_pure R \<longleftrightarrow> (\<exists>Ri. \<forall>x y. R x y = \<up>((y,x)\<in>Ri))"
  unfolding is_pure_def
  apply auto
  apply (rename_tac P')
  apply (rule_tac x="{(x,y). P' y x}" in exI)
  apply auto
  done

lemma pure_the_pure[simp]: "is_pure R \<Longrightarrow> pure (the_pure R) = R"
  unfolding is_pure_alt_def pure_def the_pure_def
  apply (intro ext)
  apply clarsimp
  apply (rename_tac a c Ri)
  apply (rule_tac a=Ri in theI2)
  apply auto
  done
  
lemma is_pure_conv: "is_pure R \<longleftrightarrow> (\<exists>R'. R = pure R')"
  unfolding pure_def is_pure_alt_def by force

lemma is_pure_the_pure_id_eq[simp]: "is_pure R \<Longrightarrow> the_pure R = Id \<longleftrightarrow> R=pure Id"  
  by (auto simp: is_pure_conv)

lemma is_pure_iff_pure_assn: "is_pure P = (\<forall>x x'. is_pure_assn (P x x'))"
  unfolding is_pure_def is_pure_assn_def by metis



abbreviation "hn_val R \<equiv> hn_ctxt (pure R)"

lemma hn_val_unfold: "hn_val R a b = \<up>((b,a)\<in>R)"
  by (simp add: hn_ctxt_def pure_def)


definition "invalid_assn R x y \<equiv> \<up>(\<exists>h. h\<Turnstile>R x y) * true"

abbreviation "hn_invalid R \<equiv> hn_ctxt (invalid_assn R)"

lemma invalidate_clone: "R x y \<Longrightarrow>\<^sub>A invalid_assn R x y * R x y"
  apply (rule entailsI)
  unfolding invalid_assn_def
  apply (auto simp: models_in_range mod_star_trueI)
  done

lemma invalidate_clone': "R x y \<Longrightarrow>\<^sub>A invalid_assn R x y * R x y * true"
  apply (rule entailsI)
  unfolding invalid_assn_def
  apply (auto simp: models_in_range mod_star_trueI)
  done

lemma invalidate: "R x y \<Longrightarrow>\<^sub>A invalid_assn R x y"
  apply (rule entailsI)
  unfolding invalid_assn_def
  apply (auto simp: models_in_range mod_star_trueI)
  done

lemma invalid_pure_recover: "invalid_assn (pure R) x y = pure R x y * true"
  apply (rule ent_iffI) 
  subgoal
    apply (rule entailsI)
    unfolding invalid_assn_def
    by (auto simp: pure_def)
  subgoal
    unfolding invalid_assn_def
    by (auto simp: pure_def)
  done    

lemma hn_invalidI: "h\<Turnstile>hn_ctxt P x y \<Longrightarrow> hn_invalid P x y = true"
  apply (cases h)
  apply (rule ent_iffI)
  apply (auto simp: invalid_assn_def hn_ctxt_def)
  done

lemma invalid_assn_cong[cong]:
  assumes "x\<equiv>x'"
  assumes "y\<equiv>y'"
  assumes "R x' y' \<equiv> R' x' y'"
  shows "invalid_assn R x y = invalid_assn R' x' y'"
  using assms unfolding invalid_assn_def
  by simp

subsection \<open>Constraints in Refinement Relations\<close>

lemma mod_pure_conv[simp]: "(h,as)\<Turnstile>pure R a b \<longleftrightarrow> (as={} \<and> (b,a)\<in>R)"
  by (auto simp: pure_def)

definition rdomp :: "('a \<Rightarrow> 'c \<Rightarrow> assn) \<Rightarrow> 'a \<Rightarrow> bool" where
  "rdomp R a \<equiv> \<exists>h c. h \<Turnstile> R a c"

abbreviation "rdom R \<equiv> Collect (rdomp R)"

lemma rdomp_ctxt[simp]: "rdomp (hn_ctxt R) = rdomp R"
  by (simp add: hn_ctxt_def[abs_def])  

lemma rdomp_pure[simp]: "rdomp (pure R) a \<longleftrightarrow> a\<in>Range R"
  unfolding rdomp_def pure_def by auto

lemma rdom_pure[simp]: "rdom (pure R) = Range R"
  unfolding rdomp_def[abs_def] pure_def by auto

lemma Range_of_constraint_conv[simp]: "Range (A\<inter>UNIV\<times>C) = Range A \<inter> C"
  by auto


subsection \<open>Heap-Nres Refinement Calculus\<close>

text \<open>Predicate that expresses refinement. Given a heap
  \<open>\<Gamma>\<close>, program \<open>c\<close> produces a heap \<open>\<Gamma>'\<close> and
  a concrete result that is related with predicate \<open>R\<close> to some
  abstract result from \<open>m\<close>\<close>
definition "hn_refine \<Gamma> c \<Gamma>' R m \<equiv> nofail m \<longrightarrow>
  <\<Gamma>> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(RETURN x \<le> m)) >\<^sub>t"

(* TODO: Can we change the patterns of assn_simproc to add this pattern? *)
simproc_setup assn_simproc_hnr ("hn_refine \<Gamma> c \<Gamma>'")
  = \<open>K Seplogic_Auto.assn_simproc_fun\<close>

lemma hn_refineI[intro?]:
  assumes "nofail m 
    \<Longrightarrow> <\<Gamma>> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(RETURN x \<le> m)) >\<^sub>t"
  shows "hn_refine \<Gamma> c \<Gamma>' R m"
  using assms unfolding hn_refine_def by blast

lemma hn_refineD:
  assumes "hn_refine \<Gamma> c \<Gamma>' R m"
  assumes "nofail m"
  shows "<\<Gamma>> c <\<lambda>r. \<Gamma>' * (\<exists>\<^sub>Ax. R x r * \<up>(RETURN x \<le> m)) >\<^sub>t"
  using assms unfolding hn_refine_def by blast

lemma hn_refine_preI: 
  assumes "\<And>h. h\<Turnstile>\<Gamma> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms unfolding hn_refine_def
  by (auto intro: hoare_triple_preI)

lemma hn_refine_nofailI: 
  assumes "nofail a \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a"  
  shows "hn_refine \<Gamma> c \<Gamma>' R a"
  using assms by (auto simp: hn_refine_def)

lemma hn_refine_false[simp]: "hn_refine false c \<Gamma>' R m"
  by rule auto

lemma hn_refine_fail[simp]: "hn_refine \<Gamma> c \<Gamma>' R FAIL"
  by rule auto

lemma hn_refine_frame:
  assumes "hn_refine P' c Q' R m"
  assumes "P \<Longrightarrow>\<^sub>t F * P'"
  shows "hn_refine P c (F * Q') R m"
  using assms
  unfolding hn_refine_def entailst_def
  apply clarsimp
  apply (erule cons_pre_rule)
  apply (rule cons_post_rule)
  apply (erule fi_rule, frame_inference)
  apply (simp only: star_aci)
  apply simp
  done

lemma hn_refine_cons:
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>tQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>t R' x y"
  shows "hn_refine P c Q' R' m"
  using R unfolding hn_refine_def
  apply clarify
  apply (rule cons_pre_rulet[OF I])
  apply (rule cons_post_rulet)
  apply assumption
  apply (sep_auto simp: entailst_def)
  apply (rule enttD)
  apply (intro entt_star_mono I' R')
  done

(*lemma hn_refine_cons:
  assumes I: "P\<Longrightarrow>\<^sub>AP'"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>AQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>A R' x y"
  shows "hn_refine P c Q' R' m"
  using R unfolding hn_refine_def
  apply clarsimp
  apply (rule cons_pre_rule[OF I])
  apply (erule cons_post_rule)
  apply (rule ent_star_mono ent_refl I' R' ent_ex_preI ent_ex_postI)+
  done
*)
lemma hn_refine_cons_pre:
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refine P' c Q R m"
  shows "hn_refine P c Q R m"
  by (rule hn_refine_cons[OF I R]) sep_auto+

lemma hn_refine_cons_post:
  assumes R: "hn_refine P c Q R m"
  assumes I: "Q\<Longrightarrow>\<^sub>tQ'"
  shows "hn_refine P c Q' R m"
  using assms
  by (rule hn_refine_cons[OF entt_refl _ _ entt_refl])

lemma hn_refine_cons_res: 
  "\<lbrakk> hn_refine \<Gamma> f \<Gamma>' R g; \<And>a c. R a c \<Longrightarrow>\<^sub>t R' a c \<rbrakk> \<Longrightarrow> hn_refine \<Gamma> f \<Gamma>' R' g"
  by (erule hn_refine_cons[OF entt_refl]) sep_auto+

lemma hn_refine_ref:
  assumes LE: "m\<le>m'"
  assumes R: "hn_refine P c Q R m"
  shows "hn_refine P c Q R m'"
  apply rule
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  using LE apply (simp add: pw_le_iff)
  apply (sep_auto intro: order_trans[OF _ LE])
  done

lemma hn_refine_cons_complete:
  assumes I: "P\<Longrightarrow>\<^sub>tP'"
  assumes R: "hn_refine P' c Q R m"
  assumes I': "Q\<Longrightarrow>\<^sub>tQ'"
  assumes R': "\<And>x y. R x y \<Longrightarrow>\<^sub>t R' x y"
  assumes LE: "m\<le>m'"
  shows "hn_refine P c Q' R' m'"
  apply (rule hn_refine_ref[OF LE])
  apply (rule hn_refine_cons[OF I R I' R'])
  done
 
lemma hn_refine_augment_res:
  assumes A: "hn_refine \<Gamma> f \<Gamma>' R g"
  assumes B: "g \<le>\<^sub>n SPEC \<Phi>"
  shows "hn_refine \<Gamma> f \<Gamma>' (\<lambda>a c. R a c * \<up>(\<Phi> a)) g"
  apply (rule hn_refineI)
  apply (rule cons_post_rule)
  apply (erule A[THEN hn_refineD])
  using B
  apply (sep_auto simp: pw_le_iff pw_leof_iff)
  done


subsection \<open>Product Types\<close>
text \<open>Some notion for product types is already defined here, as it is used 
  for currying and uncurrying, which is fundamental for the sepref tool\<close>
definition prod_assn :: "('a1\<Rightarrow>'c1\<Rightarrow>assn) \<Rightarrow> ('a2\<Rightarrow>'c2\<Rightarrow>assn) 
  \<Rightarrow> 'a1*'a2 \<Rightarrow> 'c1*'c2 \<Rightarrow> assn" where
  "prod_assn P1 P2 a c \<equiv> case (a,c) of ((a1,a2),(c1,c2)) \<Rightarrow>
  P1 a1 c1 * P2 a2 c2"

notation prod_assn (infixr "\<times>\<^sub>a" 70)
  
lemma prod_assn_pure_conv[simp]: "prod_assn (pure R1) (pure R2) = pure (R1 \<times>\<^sub>r R2)"
  by (auto simp: pure_def prod_assn_def intro!: ext)

lemma prod_assn_pair_conv[simp]: 
  "prod_assn A B (a1,b1) (a2,b2) = A a1 a2 * B b1 b2"
  unfolding prod_assn_def by auto

lemma prod_assn_true[simp]: "prod_assn (\<lambda>_ _. true) (\<lambda>_ _. true) = (\<lambda>_ _. true)"
  by (auto intro!: ext simp: hn_ctxt_def prod_assn_def)

subsection "Convenience Lemmas"

lemma hn_refine_guessI:
  assumes "hn_refine P f P' R f'"
  assumes "f=f_conc"
  shows "hn_refine P f_conc P' R f'"
  \<comment> \<open>To prove a refinement, first synthesize one, and then prove equality\<close>
  using assms by simp


lemma imp_correctI:
  assumes R: "hn_refine \<Gamma> c \<Gamma>' R a"
  assumes C: "a \<le> SPEC \<Phi>"
  shows "<\<Gamma>> c <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>' * R r r' * \<up>(\<Phi> r)>\<^sub>t"
  apply (rule cons_post_rule)
  apply (rule hn_refineD[OF R])
  apply (rule le_RES_nofailI[OF C])
  apply (sep_auto dest: order_trans[OF _ C])
  done

lemma hnr_pre_ex_conv: 
  shows "hn_refine (\<exists>\<^sub>Ax. \<Gamma> x) c \<Gamma>' R a \<longleftrightarrow> (\<forall>x. hn_refine (\<Gamma> x) c \<Gamma>' R a)"
  unfolding hn_refine_def
  apply safe
  apply (erule cons_pre_rule[rotated])
  apply (rule ent_ex_postI)
  apply (rule ent_refl)
  apply sep_auto
  done

lemma hnr_pre_pure_conv:  
  shows "hn_refine (\<Gamma> * \<up>P) c \<Gamma>' R a \<longleftrightarrow> (P \<longrightarrow> hn_refine \<Gamma> c \<Gamma>' R a)"
  unfolding hn_refine_def
  by auto

lemma hn_refine_split_post:
  assumes "hn_refine \<Gamma> c \<Gamma>' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' \<or>\<^sub>A \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  by (rule entt_disjI1_direct)

lemma hn_refine_post_other: 
  assumes "hn_refine \<Gamma> c \<Gamma>'' R a"
  shows "hn_refine \<Gamma> c (\<Gamma>' \<or>\<^sub>A \<Gamma>'') R a"
  apply (rule hn_refine_cons_post[OF assms])
  by (rule entt_disjI2_direct)


subsubsection \<open>Return\<close>

lemma hnr_RETURN_pass:
  "hn_refine (hn_ctxt R x p) (return p) (hn_invalid R x p) R (RETURN x)"
  \<comment> \<open>Pass on a value from the heap as return value\<close>
  apply rule 
  apply (sep_auto simp: hn_ctxt_def eintros: invalidate_clone')
  done

lemma hnr_RETURN_pure:
  assumes "(c,a)\<in>R"
  shows "hn_refine emp (return c) emp (pure R) (RETURN a)"
  \<comment> \<open>Return pure value\<close>
  unfolding hn_refine_def using assms
  by (sep_auto simp: pure_def)
  
subsubsection \<open>Assertion\<close>
lemma hnr_FAIL[simp, intro!]: "hn_refine \<Gamma> c \<Gamma>' R FAIL"
  unfolding hn_refine_def
  by simp

lemma hnr_ASSERT:
  assumes "\<Phi> \<Longrightarrow> hn_refine \<Gamma> c \<Gamma>' R c'"
  shows "hn_refine \<Gamma> c \<Gamma>' R (do { ASSERT \<Phi>; c'})"
  using assms
  apply (cases \<Phi>)
  by auto

subsubsection \<open>Bind\<close>
lemma bind_det_aux: "\<lbrakk> RETURN x \<le> m; RETURN y \<le> f x \<rbrakk> \<Longrightarrow> RETURN y \<le> m \<bind> f"
  apply (rule order_trans[rotated])
  apply (rule Refine_Basic.bind_mono)
  apply assumption
  apply (rule order_refl)
  apply simp
  done

lemma hnr_bind:
  assumes D1: "hn_refine \<Gamma> m' \<Gamma>1 Rh m"
  assumes D2: 
    "\<And>x x'. RETURN x \<le> m \<Longrightarrow> hn_refine (\<Gamma>1 * hn_ctxt Rh x x') (f' x') (\<Gamma>2 x x') R (f x)"
  assumes IMP: "\<And>x x'. \<Gamma>2 x x' \<Longrightarrow>\<^sub>t \<Gamma>' * hn_ctxt Rx x x'"
  shows "hn_refine \<Gamma> (m'\<bind>f') \<Gamma>' R (m\<bind>f)"
  using assms
  unfolding hn_refine_def
  apply (clarsimp simp add: pw_bind_nofail)
  apply (rule Hoare_Triple.bind_rule)
  apply assumption
  apply (clarsimp intro!: normalize_rules simp: hn_ctxt_def)
proof -
  fix x' x
  assume 1: "RETURN x \<le> m" 
    and "nofail m" "\<forall>x. inres m x \<longrightarrow> nofail (f x)"
  hence "nofail (f x)" by (auto simp: pw_le_iff)
  moreover assume "\<And>x x'. RETURN x \<le> m \<Longrightarrow>
           nofail (f x) \<longrightarrow> <\<Gamma>1 * Rh x x'> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * R r r' * true * \<up> (RETURN r \<le> f x)>"
  ultimately have "\<And>x'. <\<Gamma>1 * Rh x x'> f' x'
           <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * R r r' * true * \<up> (RETURN r \<le> f x)>"
    using 1 by simp
  also have "\<And>r'. \<exists>\<^sub>Ar. \<Gamma>2 x x' * R r r' * true * \<up> (RETURN r \<le> f x) \<Longrightarrow>\<^sub>A
    \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up> (RETURN r \<le> f x)"
    apply (sep_auto)
    apply (rule ent_frame_fwd[OF IMP[THEN enttD]])
    apply frame_inference
    apply (solve_entails)
    done
  finally (cons_post_rule) have 
    R: "<\<Gamma>1 * Rh x x'> f' x' 
        <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up>(RETURN r \<le> f x)>"
    .
  show "<\<Gamma>1 * Rh x x' * true> f' x'
          <\<lambda>r'. \<exists>\<^sub>Ar. \<Gamma>' * R r r' * true * \<up> (RETURN r \<le> m \<bind> f)>"
    by (sep_auto heap: R intro: bind_det_aux[OF 1])
qed

subsubsection \<open>Recursion\<close>

definition "hn_rel P m \<equiv> \<lambda>r. \<exists>\<^sub>Ax. P x r * \<up>(RETURN x \<le> m)"

lemma hn_refine_alt: "hn_refine Fpre c Fpost P m \<equiv> nofail m \<longrightarrow>
  <Fpre> c <\<lambda>r. hn_rel P m r * Fpost>\<^sub>t"
  apply (rule eq_reflection)
  unfolding hn_refine_def hn_rel_def
  apply (simp add: hn_ctxt_def)
  apply (simp only: star_aci)
  done

lemma wit_swap_forall:
  assumes W: "<P> c <\<lambda>_. true>"
  assumes T: "(\<forall>x. A x \<longrightarrow> <P> c <Q x>)"
  shows "<P> c <\<lambda>r. \<not>\<^sub>A (\<exists>\<^sub>Ax. \<up>(A x) * \<not>\<^sub>A Q x r)>"
  unfolding hoare_triple_def Let_def
  apply (intro conjI impI allI)
  subgoal by (elim conjE) (rule hoare_tripleD[OF W], assumption+) []

  subgoal
    apply (clarsimp, intro conjI allI)
    apply1 (rule models_in_range)
    applyS (rule hoare_tripleD[OF W]; assumption; fail)
    apply1 (simp only: disj_not2, intro impI)
    apply1 (drule spec[OF T, THEN mp])
    apply1 (drule (2) hoare_tripleD(2))
    by assumption

  subgoal by (elim conjE) (rule hoare_tripleD[OF W], assumption+)

  subgoal by (elim conjE) (rule hoare_tripleD[OF W], assumption+) 
  done

lemma hn_admissible:
  assumes PREC: "precise Ry"
  assumes E: "\<forall>f\<in>A. nofail (f x) \<longrightarrow> <P> c <\<lambda>r. hn_rel Ry (f x) r * F>"
  assumes NF: "nofail (INF f\<in>A. f x)"
  shows "<P> c <\<lambda>r. hn_rel Ry (INF f\<in>A. f x) r * F>"
proof -
  from NF obtain f where "f\<in>A" and "nofail (f x)"
    by (simp only: refine_pw_simps) blast

  with E have "<P> c <\<lambda>r. hn_rel Ry (f x) r * F>" by blast
  hence W: "<P> c <\<lambda>_. true>" by (rule cons_post_rule, simp)

  from E have 
    E': "\<forall>f. f\<in>A \<and> nofail (f x) \<longrightarrow> <P> c <\<lambda>r. hn_rel Ry (f x) r * F>"
    by blast
  from wit_swap_forall[OF W E'] have 
    E'': "<P> c
     <\<lambda>r. \<not>\<^sub>A (\<exists>\<^sub>Axa. \<up> (xa \<in> A \<and> nofail (xa x)) *
                \<not>\<^sub>A (hn_rel Ry (xa x) r * F))>" .
  
  thus ?thesis
    apply (rule cons_post_rule)
    unfolding entails_def hn_rel_def
    apply clarsimp
  proof -
    fix h as p
    assume A: "\<forall>f. f\<in>A \<longrightarrow> (\<exists>a.
      ((h, as) \<Turnstile> Ry a p * F \<and> RETURN a \<le> f x)) \<or> \<not> nofail (f x)"
    with \<open>f\<in>A\<close> and \<open>nofail (f x)\<close> obtain a where 
      1: "(h, as) \<Turnstile> Ry a p * F" and "RETURN a \<le> f x"
      by blast
    have
      "\<forall>f\<in>A. nofail (f x) \<longrightarrow> (h, as) \<Turnstile> Ry a p * F \<and> RETURN a \<le> f x"
    proof clarsimp
      fix f'
      assume "f'\<in>A" and "nofail (f' x)"
      with A obtain a' where 
        2: "(h, as) \<Turnstile> Ry a' p * F" and "RETURN a' \<le> f' x"
        by blast

      moreover note preciseD'[OF PREC 1 2] 
      ultimately show "(h, as) \<Turnstile> Ry a p * F \<and> RETURN a \<le> f' x" by simp
    qed
    hence "RETURN a \<le> (INF f\<in>A. f x)"
      by (metis (mono_tags) le_INF_iff le_nofailI)
    with 1 show "\<exists>a. (h, as) \<Turnstile> Ry a p * F \<and> RETURN a \<le> (INF f\<in>A. f x)"
      by blast
  qed
qed

lemma hn_admissible':
  assumes PREC: "precise Ry"
  assumes E: "\<forall>f\<in>A. nofail (f x) \<longrightarrow> <P> c <\<lambda>r. hn_rel Ry (f x) r * F>\<^sub>t"
  assumes NF: "nofail (INF f\<in>A. f x)"
  shows "<P> c <\<lambda>r. hn_rel Ry (INF f\<in>A. f x) r * F>\<^sub>t"
  apply (rule hn_admissible[OF PREC, where F="F*true", simplified])
  apply simp
  by fact+

lemma hnr_RECT_old:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px * F) (cf px) (F' ax px) Ry (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px * F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(\<And>x. mono_Heap (\<lambda>f. cB f x))"
  assumes PREC: "precise Ry"
  shows "hn_refine 
    (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry (RECT aB ax)"
  unfolding RECT_gfp_def
proof (simp, intro conjI impI)
  assume "trimono aB"
  hence "mono aB" by (simp add: trimonoD)
  have "\<forall>ax px. 
    hn_refine (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry 
      (gfp aB ax)"
    apply (rule gfp_cadm_induct[OF _ _ \<open>mono aB\<close>])

    apply rule
    apply (auto simp: hn_refine_alt intro: hn_admissible'[OF PREC]) []

    apply (auto simp: hn_refine_alt) []

    apply clarsimp
    apply (subst heap.mono_body_fixp[of cB, OF M])
    apply (rule S)
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px * F)
     (ccpo.fixp (fun_lub Heap_lub) (fun_ord Heap_ord) cB px) (F' ax px) Ry
     (gfp aB ax)" by simp
qed

lemma hnr_RECT:
  assumes S: "\<And>cf af ax px. \<lbrakk>
    \<And>ax px. hn_refine (hn_ctxt Rx ax px * F) (cf px) (F' ax px) Ry (af ax)\<rbrakk> 
    \<Longrightarrow> hn_refine (hn_ctxt Rx ax px * F) (cB cf px) (F' ax px) Ry (aB af ax)"
  assumes M: "(\<And>x. mono_Heap (\<lambda>f. cB f x))"
  shows "hn_refine 
    (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry (RECT aB ax)"
  unfolding RECT_def
proof (simp, intro conjI impI)
  assume "trimono aB"
  hence "flatf_mono_ge aB" by (simp add: trimonoD)
  have "\<forall>ax px. 
    hn_refine (hn_ctxt Rx ax px * F) (heap.fixp_fun cB px) (F' ax px) Ry 
      (flatf_gfp aB ax)"
      
    apply (rule flatf_ord.fixp_induct[OF _ \<open>flatf_mono_ge aB\<close>])  

    apply (rule flatf_admissible_pointwise)
    apply simp

    apply (auto simp: hn_refine_alt) []

    apply clarsimp
    apply (subst heap.mono_body_fixp[of cB, OF M])
    apply (rule S)
    apply blast
    done
  thus "hn_refine (hn_ctxt Rx ax px * F)
     (ccpo.fixp (fun_lub Heap_lub) (fun_ord Heap_ord) cB px) (F' ax px) Ry
     (flatf_gfp aB ax)" by simp
qed

lemma hnr_If:
  assumes P: "\<Gamma> \<Longrightarrow>\<^sub>t \<Gamma>1 * hn_val bool_rel a a'"
  assumes RT: "a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') b' \<Gamma>2b R b"
  assumes RE: "\<not>a \<Longrightarrow> hn_refine (\<Gamma>1 * hn_val bool_rel a a') c' \<Gamma>2c R c"
  assumes IMP: "\<Gamma>2b \<or>\<^sub>A \<Gamma>2c \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (if a' then b' else c') \<Gamma>' R (if a then b else c)"
  apply (rule hn_refine_cons[OF P])
  apply1 (rule hn_refine_preI)
  applyF (cases a; simp add: hn_ctxt_def pure_def)
    focus
      apply1 (rule hn_refine_split_post)
      applyF (rule hn_refine_cons_pre[OF _ RT])
        applyS (simp add: hn_ctxt_def pure_def)
        applyS simp
      solved
    solved
    apply1 (rule hn_refine_post_other)
    applyF (rule hn_refine_cons_pre[OF _ RE])
      applyS (simp add: hn_ctxt_def pure_def)
      applyS simp
    solved
  solved
  applyS (rule IMP)
  applyS (rule entt_refl)
  done


subsection \<open>ML-Level Utilities\<close>
ML \<open>
  signature SEPREF_BASIC = sig
    (* Destroy lambda term, return function to reconstruct. Bound var is replaced by free. *)
    val dest_lambda_rc: Proof.context -> term -> ((term * (term -> term)) * Proof.context)
    (* Apply function under lambda. Bound var is replaced by free. *)
    val apply_under_lambda: (Proof.context -> term -> term) -> Proof.context -> term -> term

    (* 'a nres type *)
    val is_nresT: typ -> bool
    val mk_nresT: typ -> typ
    val dest_nresT: typ -> typ

    (* Make certified == *)
    val mk_cequals: cterm * cterm -> cterm
    (* Make \<Longrightarrow>\<^sub>A *)
    val mk_entails: term * term -> term


    (* Operations on pre-terms *)
    val constrain_type_pre: typ -> term -> term (* t::T *)

    val mk_pair_in_pre: term -> term -> term -> term (* (c,a) \<in> R *)

    val mk_compN_pre: int -> term -> term -> term  (* f o...o g*)

    val mk_curry0_pre: term -> term                (* curry0 f *) 
    val mk_curry_pre: term -> term                 (* curry f *) 
    val mk_curryN_pre: int -> term -> term         (* curry (...(curry f)...) *) 

    val mk_uncurry0_pre: term -> term              (* uncurry0 f *)       
    val mk_uncurry_pre: term -> term               (* uncurry f *)
    val mk_uncurryN_pre: int -> term -> term       (* uncurry (...(uncurry f)...) *)



    (* Conversion for hn_refine - term*)
    val hn_refine_conv: conv -> conv -> conv -> conv -> conv -> conv

    (* Conversion on abstract value (last argument) of hn_refine - term *)
    val hn_refine_conv_a: conv -> conv

    (* Conversion on abstract value of hn_refine term in conclusion of theorem *)
    val hn_refine_concl_conv_a: (Proof.context -> conv) -> Proof.context -> conv

    (* Destruct hn_refine term *)
    val dest_hn_refine: term -> term * term * term * term * term 
    (* Make hn_refine term *)
    val mk_hn_refine: term * term * term * term * term -> term
    (* Check if given term is Trueprop (hn_refine ...). Use with CONCL_COND'. *)
    val is_hn_refine_concl: term -> bool

    (* Destruct abs-fun, returns RETURN-flag, (f, args) *)
    val dest_hnr_absfun: term -> bool * (term * term list)
    (* Make abs-fun. *)
    val mk_hnr_absfun: bool * (term * term list) -> term
    (* Make abs-fun. Guess RETURN-flag from type. *)
    val mk_hnr_absfun': (term * term list) -> term
    
    (* Prove permutation of *. To be used with f_tac_conv. *)
    val star_permute_tac: Proof.context -> tactic

    (* Make separation conjunction *)
    val mk_star: term * term -> term
    (* Make separation conjunction from list. "[]" yields "emp". *)
    val list_star: term list -> term
    (* Decompose separation conjunction. "emp" yields "[]". *)
    val strip_star: term -> term list

    (* Check if true-assertion *)
    val is_true: term -> bool

    (* Check if term is hn_ctxt-assertion *)
    val is_hn_ctxt: term -> bool 
    (* Decompose hn_ctxt-assertion *)
    val dest_hn_ctxt: term -> term * term * term
    (* Decompose hn_ctxt-assertion, NONE if term has wrong format *)
    val dest_hn_ctxt_opt: term -> (term * term * term) option
      

    type phases_ctrl = {
      trace: bool,            (* Trace phases *)
      int_res: bool,          (* Stop with intermediate result *)
      start: string option,   (* Start with this phase. NONE: First phase *)
      stop: string option     (* Stop after this phase. NONE: Last phase *)
    }

    (* No tracing or intermediate result, all phases *)
    val dflt_phases_ctrl: phases_ctrl 
    (* Tracing, intermediate result, all phases *)
    val dbg_phases_ctrl: phases_ctrl
    val flag_phases_ctrl: bool -> phases_ctrl

    (* Name, tactic, expected number of created goals (may be negative for solved goals) *)
    type phase = string * (Proof.context -> tactic') * int

    (* Perform sequence of tactics (tac,n), each expected to create n new goals, 
       or solve goals if n is negative. 
       Debug-flag: Stop with intermediate state after tactic 
       fails or produces less/more goals as expected. *)   
    val PHASES': phase list -> phases_ctrl -> Proof.context -> tactic'

  end

  structure Sepref_Basic: SEPREF_BASIC = struct

    fun is_nresT (Type (@{type_name nres},[_])) = true | is_nresT _ = false
    fun mk_nresT T = Type(@{type_name nres},[T])
    fun dest_nresT (Type (@{type_name nres},[T])) = T | dest_nresT T = raise TYPE("dest_nresT",[T],[])


    fun dest_lambda_rc ctxt (Abs (x,T,t)) = let
        val (u,ctxt) = yield_singleton Variable.variant_fixes x ctxt
        val u = Free (u,T)
        val t = subst_bound (u,t)
        val reconstruct = Term.lambda_name (x,u)
      in
        ((t,reconstruct),ctxt)
      end
    | dest_lambda_rc _ t = raise TERM("dest_lambda_rc",[t])

    fun apply_under_lambda f ctxt t = let
      val ((t,rc),ctxt) = dest_lambda_rc ctxt t
      val t = f ctxt t
    in
      rc t
    end


    (* Functions on pre-terms *)
    fun mk_pair_in_pre x y r = Const (@{const_name Set.member}, dummyT) $
      (Const (@{const_name Product_Type.Pair}, dummyT) $ x $ y) $ r


    fun mk_uncurry_pre t = Const(@{const_name uncurry}, dummyT)$t
    fun mk_uncurry0_pre t = Const(@{const_name uncurry0}, dummyT)$t
    fun mk_uncurryN_pre 0 = mk_uncurry0_pre
      | mk_uncurryN_pre 1 = I
      | mk_uncurryN_pre n = mk_uncurry_pre o mk_uncurryN_pre (n-1)

    fun mk_curry_pre t = Const(@{const_name curry}, dummyT)$t
    fun mk_curry0_pre t = Const(@{const_name curry0}, dummyT)$t
    fun mk_curryN_pre 0 = mk_curry0_pre
      | mk_curryN_pre 1 = I
      | mk_curryN_pre n = mk_curry_pre o mk_curryN_pre (n-1)


    fun mk_compN_pre 0 f g = f $ g
      | mk_compN_pre n f g = let
          val g = fold (fn i => fn t => t$Bound i) (n-2 downto 0) g
          val t = Const(@{const_name "Fun.comp"},dummyT) $ f $ g

          val t = fold (fn i => fn t => Abs ("x"^string_of_int i,dummyT,t)) (n-1 downto 1) t
        in
          t
        end

    fun constrain_type_pre T t = Const(@{syntax_const "_type_constraint_"},T-->T) $ t




    local open Conv in
      fun hn_refine_conv c1 c2 c3 c4 c5 ct = case Thm.term_of ct of
        @{mpat "hn_refine _ _ _ _ _"} => let
          val cc = combination_conv
        in
          cc (cc (cc (cc (cc all_conv c1) c2) c3) c4) c5 ct
        end
      | _ => raise CTERM ("hn_refine_conv",[ct])
  
      val hn_refine_conv_a = hn_refine_conv all_conv all_conv all_conv all_conv
  
      fun hn_refine_concl_conv_a conv ctxt = Refine_Util.HOL_concl_conv 
        (fn ctxt => hn_refine_conv_a (conv ctxt)) ctxt
  
    end

    (* FIXME: Strange dependency! *)
    val mk_cequals = uncurry SMT_Util.mk_cequals
  
    val mk_entails = HOLogic.mk_binrel @{const_name "entails"}
  
    val mk_star = HOLogic.mk_binop @{const_name "Groups.times_class.times"}

    fun list_star [] = @{term "emp::assn"}
      | list_star [a] = a
      | list_star (a::l) = mk_star (list_star l,a)

    fun strip_star @{mpat "?a*?b"} = strip_star a @ strip_star b
      | strip_star @{mpat "emp"} = []
      | strip_star t = [t]

    fun is_true @{mpat "true"} = true | is_true _ = false
  
    fun is_hn_ctxt @{mpat "hn_ctxt _ _ _"} = true | is_hn_ctxt _ = false
    fun dest_hn_ctxt @{mpat "hn_ctxt ?R ?a ?p"} = (R,a,p) 
      | dest_hn_ctxt t = raise TERM("dest_hn_ctxt",[t])
  
    fun dest_hn_ctxt_opt @{mpat "hn_ctxt ?R ?a ?p"} = SOME (R,a,p) 
      | dest_hn_ctxt_opt _ = NONE
  
    fun strip_abs_args (t as @{mpat "PR_CONST _"}) = (t,[])
      | strip_abs_args @{mpat "?f$?a"} = (case strip_abs_args f of (f,args) => (f,args@[a]))
      | strip_abs_args t = (t,[])
  
    fun dest_hnr_absfun @{mpat "RETURN$?a"} = (true, strip_abs_args a)
      | dest_hnr_absfun f = (false, strip_abs_args f)
  
    fun mk_hnr_absfun (true,fa) = Autoref_Tagging.list_APP fa |> (fn a => @{mk_term "RETURN$?a"})
      | mk_hnr_absfun (false,fa) = Autoref_Tagging.list_APP fa
  
    fun mk_hnr_absfun' fa = let
      val t = Autoref_Tagging.list_APP fa
      val T = fastype_of t
    in
      case T of
        Type (@{type_name nres},_) => t
      | _ => @{mk_term "RETURN$?t"}
  
    end  
  
    fun dest_hn_refine @{mpat "hn_refine ?P ?c ?Q ?R ?a"} = (P,c,Q,R,a)
      | dest_hn_refine t = raise TERM("dest_hn_refine",[t])
  
    fun mk_hn_refine (P,c,Q,R,a) = @{mk_term "hn_refine ?P ?c ?Q ?R ?a"}
  
    val is_hn_refine_concl = can (HOLogic.dest_Trueprop #> dest_hn_refine)
  
    fun star_permute_tac ctxt = ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms star_aci}))
      

    type phases_ctrl = {
      trace: bool,            
      int_res: bool,          
      start: string option,   
      stop: string option     
    }

    val dflt_phases_ctrl = {trace=false,int_res=false,start=NONE,stop=NONE} 
    val dbg_phases_ctrl = {trace=true,int_res=true,start=NONE,stop=NONE}
    fun flag_phases_ctrl dbg = if dbg then dbg_phases_ctrl else dflt_phases_ctrl

    type phase = string * (Proof.context -> tactic') * int

    local
      fun ph_range phases start stop = let
        fun find_phase name = let
          val i = find_index (fn (n,_,_) => n=name) phases
          val _ = if i<0 then error ("No such phase: " ^ name) else ()
        in
          i
        end

        val i = case start of NONE => 0 | SOME n => find_phase n
        val j = case stop of NONE => length phases - 1 | SOME n => find_phase n

        val phases = take (j+1) phases |> drop i

        val _ = case phases of [] => error "No phases selected, range is empty" | _ => ()
      in
        phases
      end
    in  
  
      fun PHASES' phases ctrl ctxt = let
        val phases = ph_range phases (#start ctrl) (#stop ctrl)
        val phases = map (fn (n,tac,d) => (n,tac ctxt,d)) phases
  
        fun r [] _ st = Seq.single st
          | r ((name,tac,d)::tacs) i st = let
              val n = Thm.nprems_of st
              val bailout_tac = if #int_res ctrl then all_tac else no_tac
              fun trace_tac msg st = (if #trace ctrl then tracing msg else (); Seq.single st)
              val trace_start_tac = trace_tac ("Phase " ^ name)
            in
              K trace_start_tac THEN' IF_EXGOAL (tac)
              THEN_ELSE' (
                fn i => fn st => 
                  (* Bail out if a phase does not solve/create exactly the expected subgoals *)
                  if Thm.nprems_of st = n+d then
                    ((trace_tac "  Done" THEN r tacs i) st)
                  else
                    (trace_tac "*** Wrong number of produced goals" THEN bailout_tac) st
              , 
                K (trace_tac "*** Phase tactic failed" THEN bailout_tac))
            end i st
  
      in
        r phases
      end


    end

(*    (* Perform sequence of tactics (tac,n), each expected to create n new goals, 
       or solve goals if n is negative. 
       Debug-flag: Stop with intermediate state after tactic 
       fails or produces less/more goals as expected. *)   
    val PHASES': phase list -> phases_ctrl -> Proof.context -> tactic'
*)



(*

    fun xPHASES' dbg tacs ctxt = let
      val tacs = map (fn (tac,d) => (tac ctxt,d)) tacs

      fun r [] _ st = Seq.single st
        | r ((tac,d)::tacs) i st = let
            val n = Thm.nprems_of st
            val bailout_tac = if dbg then all_tac else no_tac
          in
            IF_EXGOAL (tac)
            THEN_ELSE' (
              fn i => fn st => 
                (* Bail out if a phase does not solve/create exactly the expected subgoals *)
                if Thm.nprems_of st = n+d then
                  (r tacs i st)
                else
                  bailout_tac st
            , 
              K bailout_tac)
          end i st

    in
      r tacs
    end
*)
  end


  signature SEPREF_DEBUGGING = sig
    (*************************)
    (* Debugging *)
    (* Centralized debugging mode flag *)
    val cfg_debug_all: bool Config.T

    val is_debug: bool Config.T -> Proof.context -> bool
    val is_debug': Proof.context -> bool

    (* Conversion, trace errors if custom or central debugging flag is activated *)
    val DBG_CONVERSION: bool Config.T -> Proof.context -> conv -> tactic'

    (* Conversion, trace errors if central debugging flag is activated *)
    val DBG_CONVERSION': Proof.context -> conv -> tactic'

    (* Tracing message and current subgoal *)
    val tracing_tac': string -> Proof.context -> tactic'
    (* Warning message and current subgoal *)
    val warning_tac': string -> Proof.context -> tactic'
    (* Error message and current subgoal *)
    val error_tac': string -> Proof.context -> tactic'

    (* Trace debug message *)
    val dbg_trace_msg: bool Config.T -> Proof.context -> string -> unit
    val dbg_trace_msg': Proof.context -> string -> unit

    val dbg_msg_tac: bool Config.T -> (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'
    val dbg_msg_tac': (Proof.context -> int -> thm -> string) -> Proof.context -> tactic'

    val msg_text: string -> Proof.context -> int -> thm -> string
    val msg_subgoal: string -> Proof.context -> int -> thm -> string
    val msg_from_subgoal: string -> (term -> Proof.context -> string) -> Proof.context -> int -> thm -> string
    val msg_allgoals: string -> Proof.context -> int -> thm -> string

  end

  structure Sepref_Debugging: SEPREF_DEBUGGING = struct

    val cfg_debug_all = 
      Attrib.setup_config_bool @{binding sepref_debug_all} (K false)

    fun is_debug cfg ctxt = Config.get ctxt cfg orelse Config.get ctxt cfg_debug_all
    fun is_debug' ctxt = Config.get ctxt cfg_debug_all

    fun dbg_trace cfg ctxt obj = 
      if is_debug cfg ctxt then  
        tracing (@{make_string} obj)
      else ()

    fun dbg_trace' ctxt obj = 
      if is_debug' ctxt then  
        tracing (@{make_string} obj)
      else ()

    fun dbg_trace_msg cfg ctxt msg =   
      if is_debug cfg ctxt then  
        tracing msg
      else ()
    fun dbg_trace_msg' ctxt msg = 
      if is_debug' ctxt then  
        tracing msg
      else ()

    fun DBG_CONVERSION cfg ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _ => (dbg_trace cfg ctxt e; Seq.empty)
           | e as CTERM _ => (dbg_trace cfg ctxt e; Seq.empty)
           | e as TERM _ => (dbg_trace cfg ctxt e; Seq.empty)
           | e as TYPE _ => (dbg_trace cfg ctxt e; Seq.empty);

    fun DBG_CONVERSION' ctxt cv i st = 
      Seq.single (Conv.gconv_rule cv i st)
      handle e as THM _ => (dbg_trace' ctxt e; Seq.empty)
           | e as CTERM _ => (dbg_trace' ctxt e; Seq.empty)
           | e as TERM _ => (dbg_trace' ctxt e; Seq.empty)
           | e as TYPE _ => (dbg_trace' ctxt e; Seq.empty);


    local 
      fun gen_subgoal_msg_tac do_msg msg ctxt = IF_EXGOAL (fn i => fn st => let
        val t = nth (Thm.prems_of st) (i-1)
        val _ = Pretty.block [Pretty.str msg, Pretty.fbrk, Syntax.pretty_term ctxt t]
          |> Pretty.string_of |> do_msg

      in
        Seq.single st
      end)
    in       
      val tracing_tac' = gen_subgoal_msg_tac tracing
      val warning_tac' = gen_subgoal_msg_tac warning
      val error_tac' = gen_subgoal_msg_tac error
    end


    fun dbg_msg_tac cfg msg ctxt =
      if is_debug cfg ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac
    fun dbg_msg_tac' msg ctxt =
      if is_debug' ctxt then (fn i => fn st => (tracing (msg ctxt i st); Seq.single st))
      else K all_tac

    fun msg_text msg _ _ _ = msg

    fun msg_from_subgoal msg sgmsg ctxt i st = 
      case try (nth (Thm.prems_of st)) (i-1) of
        NONE => msg ^ "\n" ^ "Subgoal out of range"
      | SOME t => msg ^ "\n" ^ sgmsg t ctxt

    fun msg_subgoal msg = msg_from_subgoal msg (fn t => fn ctxt =>
      Syntax.pretty_term ctxt t |> Pretty.string_of
    )

    fun msg_allgoals msg ctxt _ st = 
      msg ^ "\n" ^ Pretty.string_of (Pretty.chunks (Goal_Display.pretty_goals ctxt st))

  end
\<close>


ML \<open>
  (* Tactics for produced subgoals *)
  infix 1 THEN_NEXT THEN_ALL_NEW_LIST THEN_ALL_NEW_LIST'
  signature STACTICAL = sig
    (* Apply first tactic on this subgoal, and then second tactic on next subgoal *)
    val THEN_NEXT: tactic' * tactic' -> tactic'
    (* Apply tactics to the current and following subgoals *)
    val APPLY_LIST: tactic' list -> tactic'
    (* Apply list of tactics on subgoals emerging from tactic. 
      Requires exactly one tactic per emerging subgoal.*)
    val THEN_ALL_NEW_LIST: tactic' * tactic' list -> tactic'
    (* Apply list of tactics to subgoals emerging from tactic, use fallback for additional subgoals. *)
    val THEN_ALL_NEW_LIST': tactic' * (tactic' list * tactic') -> tactic'

  end

  structure STactical : STACTICAL = struct
    infix 1 THEN_WITH_GOALDIFF
    fun (tac1 THEN_WITH_GOALDIFF tac2) st = let
      val n1 = Thm.nprems_of st
    in
      st |> (tac1 THEN (fn st => tac2 (Thm.nprems_of st - n1) st ))
    end

    fun (tac1 THEN_NEXT tac2) i = 
      tac1 i THEN_WITH_GOALDIFF (fn d => (
        if d < ~1 then 
          (error "THEN_NEXT: Tactic solved more than one goal"; no_tac) 
        else 
          tac2 (i+1+d)
      ))

    fun APPLY_LIST [] = K all_tac
      | APPLY_LIST (tac::tacs) = tac THEN_NEXT APPLY_LIST tacs
            
    fun (tac1 THEN_ALL_NEW_LIST tacs) i = 
      tac1 i 
      THEN_WITH_GOALDIFF (fn d =>
        if d+1 <> length tacs then (
          error "THEN_ALL_NEW_LIST: Tactic produced wrong number of goals"; no_tac
        ) else APPLY_LIST tacs i
      )

    fun (tac1 THEN_ALL_NEW_LIST' (tacs,rtac)) i =  
      tac1 i 
      THEN_WITH_GOALDIFF (fn d => let
        val _ = if d+1 < length tacs then error "THEN_ALL_NEW_LIST': Tactic produced too few goals" else ();
        val tacs' = tacs @ replicate (d + 1 - length tacs) rtac
      in    
        APPLY_LIST tacs' i
      end)


  end


  open STactical
\<close>

end
