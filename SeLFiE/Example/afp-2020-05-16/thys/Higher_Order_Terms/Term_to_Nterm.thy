chapter \<open>Converting between \<open>term\<close>s and \<open>nterm\<close>s\<close>

theory Term_to_Nterm
imports
  Fresh_Class
  Find_First
  Term
  Nterm
begin

section \<open>\<open>\<alpha>\<close>-equivalence\<close>

inductive alpha_equiv :: "(name, name) fmap \<Rightarrow> nterm \<Rightarrow> nterm \<Rightarrow> bool" where
const: "alpha_equiv env (Nconst x) (Nconst x)" |
var1: "x |\<notin>| fmdom env \<Longrightarrow> x |\<notin>| fmran env \<Longrightarrow> alpha_equiv env (Nvar x) (Nvar x)" |
var2: "fmlookup env x = Some y \<Longrightarrow> alpha_equiv env (Nvar x) (Nvar y)" |
abs: "alpha_equiv (fmupd x y env) n1 n2 \<Longrightarrow> alpha_equiv env (\<Lambda>\<^sub>n x. n1) (\<Lambda>\<^sub>n y. n2)" |
app: "alpha_equiv env n1 n2 \<Longrightarrow> alpha_equiv env m1 m2 \<Longrightarrow> alpha_equiv env (n1 $\<^sub>n m1) (n2 $\<^sub>n m2)"

code_pred alpha_equiv .

abbreviation alpha_eq :: "nterm \<Rightarrow> nterm \<Rightarrow> bool" (infixl "\<approx>\<^sub>\<alpha>" 50) where
"alpha_eq n1 n2 \<equiv> alpha_equiv fmempty n1 n2"

lemma alpha_equiv_refl[intro?]:
  assumes "fmpred (=) \<Gamma>"
  shows "alpha_equiv \<Gamma> t t"
using assms proof (induction t arbitrary: \<Gamma>)
  case Napp
  show ?case
    apply (rule alpha_equiv.app; rule Napp)
    using Napp.prems unfolding fdisjnt_alt_def by auto
qed (auto simp: fdisjnt_alt_def intro: alpha_equiv.intros)

corollary alpha_eq_refl: "alpha_eq t t"
by (auto intro: alpha_equiv_refl)

section \<open>From @{typ term} to @{typ nterm}\<close>

fun term_to_nterm :: "name list \<Rightarrow> term \<Rightarrow> (name, nterm) state" where
"term_to_nterm _ (Const name) = State_Monad.return (Nconst name)" |
"term_to_nterm _ (Free name) = State_Monad.return (Nvar name)" |
"term_to_nterm \<Gamma> (Bound n) = State_Monad.return (Nvar (\<Gamma> ! n))" |
"term_to_nterm \<Gamma> (\<Lambda> t) = do {
  n \<leftarrow> fresh_create;
  e \<leftarrow> term_to_nterm (n # \<Gamma>) t;
  State_Monad.return (\<Lambda>\<^sub>n n. e)
}" |
"term_to_nterm \<Gamma> (t\<^sub>1 $ t\<^sub>2) = do {
  e\<^sub>1 \<leftarrow> term_to_nterm \<Gamma> t\<^sub>1;
  e\<^sub>2 \<leftarrow> term_to_nterm \<Gamma> t\<^sub>2;
  State_Monad.return (e\<^sub>1 $\<^sub>n e\<^sub>2)
}"

lemmas term_to_nterm_induct = term_to_nterm.induct[case_names const free bound abs app]

lemma term_to_nterm:
  assumes "no_abs t"
  shows "fst (run_state (term_to_nterm \<Gamma> t) x) = convert_term t"
using assms
apply (induction arbitrary: x)
apply auto
by (auto simp: free_term_def free_nterm_def const_term_def const_nterm_def app_term_def app_nterm_def split_beta split: prod.splits)

definition term_to_nterm' :: "term \<Rightarrow> nterm" where
"term_to_nterm' t = frun_fresh (term_to_nterm [] t) (frees t)"

lemma term_to_nterm_mono: "mono_state (term_to_nterm \<Gamma> x)"
by (induction \<Gamma> x rule: term_to_nterm.induct) (auto intro: bind_mono_strong)

lemma term_to_nterm_vars0:
  assumes "wellformed' (length \<Gamma>) t"
  shows "frees (fst (run_state (term_to_nterm \<Gamma> t) s)) |\<subseteq>| frees t |\<union>| fset_of_list \<Gamma>"
using assms proof (induction \<Gamma> t arbitrary: s rule: term_to_nterm_induct)
  case (bound \<Gamma> i)
  hence "\<Gamma> ! i |\<in>| fset_of_list \<Gamma>"
    including fset.lifting by transfer auto
  thus ?case
    by (auto simp: State_Monad.return_def)
next
  case (abs \<Gamma> t)
  let ?x = "next s"

  from abs have "frees (fst (run_state (term_to_nterm (?x # \<Gamma>) t) ?x)) |\<subseteq>| frees t |\<union>| {|?x|} |\<union>| fset_of_list \<Gamma>"
    by simp
  thus ?case
    by (auto simp: create_alt_def split_beta)
qed (auto simp: split_beta)

corollary term_to_nterm_vars:
  assumes "wellformed t"
  shows "frees (fresh_frun (term_to_nterm [] t) F) |\<subseteq>| frees t"
proof -
  let ?\<Gamma> = "[]"
  from assms have "wellformed' (length ?\<Gamma>) t"
    by simp
  hence "frees (fst (run_state (term_to_nterm ?\<Gamma> t) (fNext F))) |\<subseteq>| (frees t |\<union>| fset_of_list ?\<Gamma>)"
    by (rule term_to_nterm_vars0)
  thus ?thesis
    by (simp add: fresh_fNext_def fresh_frun_def)
qed

corollary term_to_nterm_closed: "closed t \<Longrightarrow> wellformed t \<Longrightarrow> closed (term_to_nterm' t)"
using term_to_nterm_vars[where F = "frees t" and t = t, simplified]
unfolding closed_except_def term_to_nterm'_def
by (simp add: fresh_frun_def)

lemma term_to_nterm_consts: "pred_state (\<lambda>t'. consts t' = consts t) (term_to_nterm \<Gamma> t)"
apply (rule pred_stateI)
apply (induction t arbitrary: \<Gamma>)
apply (auto split: prod.splits)
done

section \<open>From @{typ nterm} to @{typ term}\<close>

fun nterm_to_term :: "name list \<Rightarrow> nterm \<Rightarrow> term" where
"nterm_to_term \<Gamma> (Nconst name) = Const name" |
"nterm_to_term \<Gamma> (Nvar name) = (case find_first name \<Gamma> of Some n \<Rightarrow> Bound n | None \<Rightarrow> Free name)" |
"nterm_to_term \<Gamma> (t $\<^sub>n u) = nterm_to_term \<Gamma> t $ nterm_to_term \<Gamma> u" |
"nterm_to_term \<Gamma> (\<Lambda>\<^sub>n x. t) = \<Lambda> nterm_to_term (x # \<Gamma>) t"

lemma nterm_to_term:
  assumes "no_abs t" "fdisjnt (fset_of_list \<Gamma>) (frees t)"
  shows "nterm_to_term \<Gamma> t = convert_term t"
using assms proof (induction arbitrary: \<Gamma>)
  case (free name)
  then show ?case
    apply simp
    apply (auto simp: free_nterm_def free_term_def fdisjnt_alt_def split: option.splits)
    apply (rule find_first_none)
    by (metis fset_of_list_elem)
next
  case (const name)
  show ?case
    apply simp
    by (simp add: const_nterm_def const_term_def)
next
  case (app t\<^sub>1 t\<^sub>2)
  then have "nterm_to_term \<Gamma> t\<^sub>1 = convert_term t\<^sub>1" "nterm_to_term \<Gamma> t\<^sub>2 = convert_term t\<^sub>2"
    by (auto simp: fdisjnt_alt_def finter_funion_distrib)
  then show ?case
    apply simp
    by (simp add: app_nterm_def app_term_def)
qed

abbreviation "nterm_to_term' \<equiv> nterm_to_term []"

lemma nterm_to_term': "no_abs t \<Longrightarrow> nterm_to_term' t = convert_term t"
by (auto simp: fdisjnt_alt_def nterm_to_term)

lemma nterm_to_term_frees[simp]: "frees (nterm_to_term \<Gamma> t) = frees t - fset_of_list \<Gamma>"
proof (induction t arbitrary: \<Gamma>)
  case (Nvar name)
  show ?case
    proof (cases "find_first name \<Gamma>")
      case None
      hence "name |\<notin>| fset_of_list \<Gamma>"
        including fset.lifting
        by transfer (metis find_first_some option.distinct(1))
      with None show ?thesis
        by auto
    next
      case (Some u)
      hence "name |\<in>| fset_of_list \<Gamma>"
        including fset.lifting
        by transfer (metis find_first_none option.distinct(1))
      with Some show ?thesis
        by auto
    qed
  qed (auto split: option.splits)

section \<open>Correctness\<close>

text \<open>Some proofs in this section have been contributed by Yu Zhang.\<close>

lemma term_to_nterm_nterm_to_term0:
  assumes "wellformed' (length \<Gamma>) t" "fdisjnt (fset_of_list \<Gamma>) (frees t)" "distinct \<Gamma>"
  assumes "fBall (frees t |\<union>| fset_of_list \<Gamma>) (\<lambda>x. x \<le> s)"
  shows "nterm_to_term \<Gamma> (fst (run_state (term_to_nterm \<Gamma> t) s)) = t"
using assms proof (induction \<Gamma> t arbitrary: s rule: term_to_nterm_induct)
  case (free \<Gamma> name)
  hence "fdisjnt (fset_of_list \<Gamma>) {|name|}"
    by simp
  hence "name \<notin> set \<Gamma>"
    including fset.lifting by transfer' (simp add: disjnt_def)
  hence "find_first name \<Gamma> = None"
    by (rule find_first_none)
  thus ?case
    by (simp add: State_Monad.return_def)
next
  case (bound \<Gamma> i)
  thus ?case
    by (simp add: State_Monad.return_def find_first_some_index)
next
  case (app \<Gamma> t\<^sub>1 t\<^sub>2)
  have "fdisjnt (fset_of_list \<Gamma>) (frees t\<^sub>1)"
    apply (rule fdisjnt_subset_right[where N = "frees t\<^sub>1 |\<union>| frees t\<^sub>2"])
    using app by auto
  have "fdisjnt (fset_of_list \<Gamma>) (frees t\<^sub>2)"
    apply (rule fdisjnt_subset_right[where N = "frees t\<^sub>1 |\<union>| frees t\<^sub>2"])
    using app by auto

  have s: "s \<le> snd (run_state (term_to_nterm \<Gamma> t\<^sub>1) s)"
    apply (rule state_io_relD[OF term_to_nterm_mono])
    apply (rule surjective_pairing)
    done

  show ?case
    apply (auto simp: split_beta)
    subgoal
      apply (rule app)
      subgoal using app by simp
      subgoal by fact
      subgoal by fact
      using app by auto
    subgoal
      apply (rule app)
      subgoal using app by simp
      subgoal by fact
      subgoal by fact
      using app s by force+
    done
next
  case (abs \<Gamma> t)

  have "next s |\<notin>| frees t |\<union>| fset_of_list \<Gamma>"
    using abs(5)[simplified]
    by (rule next_ge_fall)

  have "nterm_to_term (next s # \<Gamma>) (fst (run_state (term_to_nterm (next s # \<Gamma>) t) (next s))) = t"
    proof (subst abs)
      show "wellformed' (length (next s # \<Gamma>)) t"
        using abs by auto
      show "fdisjnt (fset_of_list (next s # \<Gamma>)) (frees t)"
        apply simp
        apply (rule fdisjnt_insert)
        using \<open>next s |\<notin>| frees t |\<union>| fset_of_list \<Gamma>\<close> abs by auto
      show "distinct (next s # \<Gamma>)"
        apply simp
        apply rule
        using \<open>next s |\<notin>| frees t |\<union>| fset_of_list \<Gamma>\<close> apply (simp add: fset_of_list_elem)
        apply fact
        done
      show "fBall (frees t |\<union>| fset_of_list (next s # \<Gamma>)) (\<lambda>x. x \<le> next s)"
        using abs(5) apply simp
        apply (rule fBall_pred_weaken[where P = "\<lambda>x. x \<le> s"])
        subgoal
          apply simp
          by (meson dual_order.strict_implies_order dual_order.strict_trans2 fresh_class.next_ge)
        subgoal by assumption
        done
    qed auto

  thus ?case
    by (auto simp: split_beta create_alt_def)
qed (auto simp: State_Monad.return_def)

lemma term_to_nterm_nterm_to_term:
  assumes "wellformed t" "frees t |\<subseteq>| S"
  shows "nterm_to_term' (frun_fresh (term_to_nterm [] t) (S |\<union>| Q)) = t"
proof (rule term_to_nterm_nterm_to_term0)
  show "wellformed' (length []) t"
    using assms by simp
next
  show "fdisjnt (fset_of_list []) (frees t)"
    unfolding fdisjnt_alt_def by simp
next
  have "fBall (S |\<union>| Q) (\<lambda>x. x < fresh.fNext next default (S |\<union>| Q))"
    by (metis fNext_geq_not_member fresh_fNext_def le_less_linear fBallI)
  hence "fBall (S |\<union>| Q) (\<lambda>x. x \<le> fresh.fNext next default (S |\<union>| Q))"
    by (meson fBall_pred_weaken less_eq_name_def)
  thus "fBall (frees t |\<union>| fset_of_list []) (\<lambda>x. x \<le> fresh.fNext next default (S |\<union>| Q))"
    using \<open>frees t |\<subseteq>| S\<close>
    by auto
qed simp

corollary term_to_nterm_nterm_to_term_simple:
  assumes "wellformed t"
  shows "nterm_to_term' (term_to_nterm' t) = t"
unfolding term_to_nterm'_def using assms
by (metis order_refl sup.idem term_to_nterm_nterm_to_term)

lemma nterm_to_term_eq:
  assumes "frees u |\<subseteq>| fset_of_list (common_prefix \<Gamma> \<Gamma>')"
  shows "nterm_to_term \<Gamma> u = nterm_to_term \<Gamma>' u"
using assms
proof (induction u arbitrary: \<Gamma> \<Gamma>')
  case (Nvar name)
  hence "name \<in> set (common_prefix \<Gamma> \<Gamma>')"
    unfolding frees_nterm.simps
    including fset.lifting
    by transfer' simp
  thus ?case
    by (auto simp: common_prefix_find)
next
  case (Nabs x t)
  hence *: "frees t - {|x|} |\<subseteq>| fset_of_list (common_prefix \<Gamma> \<Gamma>')"
    by simp

  show ?case
    apply simp
    apply (rule Nabs)
    using * Nabs by auto
qed auto

corollary nterm_to_term_eq_closed: "closed t \<Longrightarrow> nterm_to_term \<Gamma> t = nterm_to_term \<Gamma>' t"
by (rule nterm_to_term_eq) (auto simp: closed_except_def)

lemma nterm_to_term_wellformed: "wellformed' (length \<Gamma>) (nterm_to_term \<Gamma> t)"
proof (induction t arbitrary: \<Gamma>)
  case (Nabs x t)
  hence "wellformed' (Suc (length \<Gamma>)) (nterm_to_term (x # \<Gamma>) t)"
    by (metis length_Cons)
  thus ?case
    by auto
qed (auto simp: find_first_correct split: option.splits)

corollary nterm_to_term_closed_wellformed: "closed t \<Longrightarrow> wellformed (nterm_to_term \<Gamma> t)"
by (metis Ex_list_of_length nterm_to_term_eq_closed nterm_to_term_wellformed)

lemma nterm_to_term_term_to_nterm:
  assumes "frees t |\<subseteq>| fset_of_list \<Gamma>" "length \<Gamma> = length \<Gamma>'"
  shows "alpha_equiv (fmap_of_list (zip \<Gamma> \<Gamma>')) t (fst (run_state (term_to_nterm \<Gamma>' (nterm_to_term \<Gamma> t)) s))"
using assms proof (induction \<Gamma> t arbitrary: s \<Gamma>' rule:nterm_to_term.induct)
  case (4 \<Gamma> x t)
  show ?case
    apply (simp add: split_beta)
    apply (rule alpha_equiv.abs)
    using "4.IH"[where \<Gamma>' = "next s # \<Gamma>'"] "4.prems"
    by (fastforce simp: create_alt_def intro: alpha_equiv.intros)
qed
  (force split: option.splits intro: find_first_some intro!: alpha_equiv.intros
         simp: fset_of_list_elem find_first_in_map split_beta fdisjnt_alt_def)+

corollary nterm_to_term_term_to_nterm': "closed t \<Longrightarrow> t \<approx>\<^sub>\<alpha> term_to_nterm' (nterm_to_term' t)"
unfolding term_to_nterm'_def closed_except_def
apply (rule nterm_to_term_term_to_nterm[where \<Gamma> = "[]" and \<Gamma>' = "[]", simplified])
by auto

context begin

private lemma term_to_nterm_alpha_equiv0:
  "length \<Gamma>1 = length \<Gamma>2 \<Longrightarrow> distinct \<Gamma>1 \<Longrightarrow> distinct \<Gamma>2 \<Longrightarrow> wellformed' (length \<Gamma>1) t1 \<Longrightarrow>
   fresh_fin (frees t1 |\<union>| fset_of_list \<Gamma>1) s1 \<Longrightarrow> fdisjnt (fset_of_list \<Gamma>1) (frees t1) \<Longrightarrow>
   fresh_fin (frees t1 |\<union>| fset_of_list \<Gamma>2) s2 \<Longrightarrow> fdisjnt (fset_of_list \<Gamma>2) (frees t1) \<Longrightarrow>
   alpha_equiv (fmap_of_list (zip \<Gamma>1 \<Gamma>2)) (fst( run_state (term_to_nterm \<Gamma>1 t1) s1)) (fst ( run_state (term_to_nterm \<Gamma>2 t1) s2))"
proof (induction \<Gamma>1 t1 arbitrary: \<Gamma>2 s1 s2 rule:term_to_nterm_induct)
  case (free \<Gamma>1 name)
  then have "name |\<notin>| fmdom (fmap_of_list (zip \<Gamma>1 \<Gamma>2))"
    unfolding fdisjnt_alt_def
    by force
  moreover have "name |\<notin>| fmran (fmap_of_list (zip \<Gamma>1 \<Gamma>2))"
    apply rule
    apply (subst (asm) fmran_of_list)
    apply (subst (asm) fset_of_list_map[symmetric])
    apply (subst (asm) distinct_clearjunk_id)
    subgoal
      apply (subst map_fst_zip)
      apply fact
      apply fact
      done
    apply (subst (asm) map_snd_zip)
    apply fact
    using free unfolding fdisjnt_alt_def
    by fastforce
  ultimately show ?case
    by (force intro:alpha_equiv.intros)
next
  case (abs \<Gamma> t)
  have *: "next s1 > s1" "next s2 > s2"
    using next_ge by force+
  with abs have "next s1 \<notin> set \<Gamma>" "next s2 \<notin> set \<Gamma>2"
    by (metis fBall_funion fset_of_list_elem next_ge_fall)+
  have "fresh_fin (frees t |\<union>| fset_of_list \<Gamma>) (next s1)"
       "fresh_fin (frees t |\<union>| fset_of_list \<Gamma>2) (next s2)"
    using * abs
    by (smt dual_order.trans fBall_pred_weaken frees_term.simps(3) less_imp_le)+
  have "fdisjnt (finsert (next s1) (fset_of_list \<Gamma>)) (frees t)"
       "fdisjnt (finsert (next s2) (fset_of_list \<Gamma>2)) (frees t)"
    unfolding fdisjnt_alt_def using abs frees_term.simps
    by (metis fdisjnt_alt_def finter_finsert_right funionCI inf_commute next_ge_fall)+
  have "wellformed' (Suc (length \<Gamma>2)) t"
    using wellformed'.simps abs
    by (metis Suc_eq_plus1)
  show ?case
    apply (auto simp: split_beta create_alt_def)
    apply rule
    apply (rule abs.IH[of _ "next s2 # \<Gamma>2", simplified])
    by (fact | rule)+
next
  case (app \<Gamma>1 t\<^sub>1 t\<^sub>2)
  hence "wellformed' (length \<Gamma>1) t\<^sub>1" "wellformed' (length \<Gamma>1) t\<^sub>2"
  and "fresh_fin (frees t\<^sub>1 |\<union>| fset_of_list \<Gamma>1) s1" "fresh_fin (frees t\<^sub>1 |\<union>| fset_of_list \<Gamma>2) s2"
  and "fdisjnt (fset_of_list \<Gamma>1) (frees t\<^sub>1)" "fdisjnt (fset_of_list \<Gamma>2) (frees t\<^sub>1)"
  and "fdisjnt (fset_of_list \<Gamma>1) (frees t\<^sub>2)" "fdisjnt (fset_of_list \<Gamma>2) (frees t\<^sub>2)"
    using app
    unfolding fdisjnt_alt_def
    by (auto simp: inf_sup_distrib1)
  have "s1 \<le> snd (run_state (term_to_nterm \<Gamma>1 t\<^sub>1) s1)" "s2 \<le> snd (run_state (term_to_nterm \<Gamma>2 t\<^sub>1) s2)"
    using term_to_nterm_mono
    by (simp add: state_io_rel_def)+
  hence "fresh_fin (frees t\<^sub>2 |\<union>| fset_of_list \<Gamma>1) (snd (run_state (term_to_nterm \<Gamma>1 t\<^sub>1) s1))"
    using \<open>fresh_fin (frees (t\<^sub>1 $ t\<^sub>2) |\<union>| fset_of_list \<Gamma>1) s1\<close>
    by force

  have "fresh_fin (frees t\<^sub>2 |\<union>| fset_of_list \<Gamma>2) (snd (run_state (term_to_nterm \<Gamma>2 t\<^sub>1) s2))"
    apply rule
    using app frees_term.simps \<open>s2 \<le> _\<close> dual_order.trans
    by (metis fbspec funion_iff)

  show ?case
    apply (auto simp: split_beta create_alt_def)
    apply (rule alpha_equiv.app)
    subgoal
      apply (rule app)
      apply (simp | fact)+
      done
    subgoal
      apply (rule app)
      apply (simp | fact)+
      done
    done
qed (force intro: alpha_equiv.intros simp: fmlookup_of_list in_set_zip)+

lemma term_to_nterm_alpha_equiv:
  assumes "length \<Gamma>1 = length \<Gamma>2" "distinct \<Gamma>1" "distinct \<Gamma>2" "closed t"
  assumes "wellformed' (length \<Gamma>1) t"
  assumes "fresh_fin (fset_of_list \<Gamma>1) s1" "fresh_fin (fset_of_list \<Gamma>2) s2"
  shows "alpha_equiv (fmap_of_list (zip \<Gamma>1 \<Gamma>2)) (fst (run_state (term_to_nterm \<Gamma>1 t) s1)) (fst (run_state (term_to_nterm \<Gamma>2 t) s2))"
  \<comment> \<open>An instantiated version of this lemma with @{prop \<open>\<Gamma>1 = []\<close>} and @{prop \<open>\<Gamma>2 = []\<close>}
      would not make sense because then it would just be a special case of
      @{thm [source=true] alpha_eq_refl}.\<close>
using assms
by (simp add: fdisjnt_alt_def closed_except_def term_to_nterm_alpha_equiv0)

end

global_interpretation nrelated: term_struct_rel_strong "(\<lambda>t n. t = nterm_to_term \<Gamma> n)" for \<Gamma>
proof (standard, goal_cases)
  case (5 name t)
  then show ?case by (cases t) (auto simp: const_term_def const_nterm_def split: option.splits)
next
  case (6 u\<^sub>1 u\<^sub>2 t)
  then show ?case by (cases t) (auto simp: app_term_def app_nterm_def split: option.splits)
qed (auto simp: const_term_def const_nterm_def app_term_def app_nterm_def)

lemma env_nrelated_closed:
  assumes "nrelated.P_env \<Gamma> env nenv" "closed_env nenv"
  shows "nrelated.P_env \<Gamma>' env nenv"
proof
  fix x
  from assms have "rel_option (\<lambda>t n. t = nterm_to_term \<Gamma> n) (fmlookup env x) (fmlookup nenv x)"
    by auto
  thus "rel_option (\<lambda>t n. t = nterm_to_term \<Gamma>' n) (fmlookup env x) (fmlookup nenv x)"
    using assms
    by (cases rule: option.rel_cases) (auto dest: fmdomI simp: nterm_to_term_eq_closed)
qed

lemma nrelated_subst:
  assumes "nrelated.P_env \<Gamma> env nenv" "closed_env nenv" "fdisjnt (fset_of_list \<Gamma>) (fmdom nenv)"
  shows "subst (nterm_to_term \<Gamma> t) env = nterm_to_term \<Gamma> (subst t nenv)"
using assms
proof (induction t arbitrary: \<Gamma> env nenv)
  case (Nvar name)
  thus ?case
    proof (cases rule: fmrel_cases[where x = name])
      case (some t\<^sub>1 t\<^sub>2)
      with Nvar have "name |\<notin>| fset_of_list \<Gamma>"
        unfolding fdisjnt_alt_def by (auto dest: fmdomI)
      hence "find_first name \<Gamma> = None"
        including fset.lifting by transfer' (simp add: find_first_none)
      with some show ?thesis
        by auto
    qed (auto split: option.splits)
next
  case (Nabs x t)
  show ?case
    apply simp
    apply (subst subst_drop[symmetric, where x = x])
    subgoal by simp
    apply (rule Nabs)
    using Nabs unfolding fdisjnt_alt_def
    by (auto intro: env_nrelated_closed)
qed auto

lemma nterm_to_term_insert_dupl:
  assumes "y \<in> set (take n \<Gamma>)" "n \<le> length \<Gamma>"
  shows "nterm_to_term \<Gamma> t = incr_bounds (- 1) (Suc n) (nterm_to_term (insert_nth n y \<Gamma>) t)"
using assms
proof (induction t arbitrary: n \<Gamma>)
  case (Nvar name)
  show ?case
    proof (cases "y = name")
      case True
      with Nvar obtain i where "find_first name \<Gamma> = Some i" "i < n"
        by (auto elim: find_first_some_strong)

      hence "find_first name (take n \<Gamma>) = Some i"
        by (rule find_first_prefix)

      show ?thesis
        apply simp
        apply (subst \<open>find_first name \<Gamma> = Some i\<close>)
        apply simp
        apply (subst find_first_append)
        apply (subst \<open>find_first name (take n \<Gamma>) = Some i\<close>)
        apply simp
        using \<open>i < n\<close> by simp
    next
      case False
      show ?thesis
        apply (simp del: insert_nth_take_drop)
        apply (subst find_first_insert_nth_neq)
        subgoal using False by simp
        by (cases "find_first name \<Gamma>") auto
    qed
next
  case (Nabs x t)
  show ?case
    apply simp
    apply (subst Nabs(1)[where n = "Suc n"])
    using Nabs by auto
qed auto

lemma nterm_to_term_bounds_dupl:
  assumes "i < length \<Gamma>" "j < length \<Gamma>" "i < j"
  assumes "\<Gamma> ! i = \<Gamma> ! j"
  shows "j |\<notin>| bounds (nterm_to_term \<Gamma> t)"
using assms
proof (induction t arbitrary: \<Gamma> i j)
  case (Nvar name)
  show ?case
    proof (cases "find_first name \<Gamma>")
      case (Some k)
      show ?thesis
        proof
          assume "j |\<in>| bounds (nterm_to_term \<Gamma> (Nvar name))"
          with Some have "find_first name \<Gamma> = Some j"
            by simp

          moreover have "find_first name \<Gamma> \<noteq> Some j"
            proof (rule find_first_later)
              show "i < length \<Gamma>" "j < length \<Gamma>" "i < j"
                by fact+
            next
              show "\<Gamma> ! j = name"
                by (rule find_first_correct) fact
              thus "\<Gamma> ! i = name"
                using Nvar by simp
            qed

          ultimately show False
            by blast
        qed
    qed simp
next
  case (Nabs x t)
  show ?case
    proof
      assume "j |\<in>| bounds (nterm_to_term \<Gamma> (\<Lambda>\<^sub>n x. t))"
      then obtain j' where "j' |\<in>| bounds (nterm_to_term (x # \<Gamma>) t)" "j' > 0" "j = j' - 1"
        by auto
      hence "Suc j |\<in>| bounds (nterm_to_term (x # \<Gamma>) t)"
        by simp

      moreover have "Suc j |\<notin>| bounds (nterm_to_term (x # \<Gamma>) t)"
        proof (rule Nabs)
          show "Suc i < length (x # \<Gamma>)" "Suc j < length (x # \<Gamma>)" "Suc i < Suc j" "(x # \<Gamma>) ! Suc i = (x # \<Gamma>) ! Suc j"
            using Nabs by simp+
        qed

      ultimately show False
        by blast
    qed
  qed auto

fun subst_single :: "nterm \<Rightarrow> name \<Rightarrow> nterm \<Rightarrow> nterm" where
"subst_single (Nvar s) s' t' = (if s = s' then t' else Nvar s)" |
"subst_single (t\<^sub>1 $\<^sub>n t\<^sub>2) s' t' = subst_single t\<^sub>1 s' t' $\<^sub>n subst_single t\<^sub>2 s' t'" |
"subst_single (\<Lambda>\<^sub>n x. t) s' t' = (\<Lambda>\<^sub>n x. (if x = s' then t else subst_single t s' t'))" |
"subst_single t _ _ = t"

lemma subst_single_eq: "subst_single t s t' = subst t (fmap_of_list [(s, t')])"
proof (induction t)
  case (Nabs x t)
  then show ?case
    by (cases "x = s") (simp add: fmfilter_alt_defs)+
qed auto

lemma nterm_to_term_subst_replace_bound:
  assumes "closed u'" "n \<le> length \<Gamma>" "x \<notin> set (take n \<Gamma>)"
  shows "nterm_to_term \<Gamma> (subst_single u x u') = replace_bound n (nterm_to_term (insert_nth n x \<Gamma>) u) (nterm_to_term \<Gamma> u')"
using assms
proof (induction u arbitrary: n \<Gamma>)
  case (Nvar name)
  note insert_nth_take_drop[simp del]
  show ?case
    proof (cases "name = x")
      case True
      thus ?thesis
        using Nvar
        apply (simp add: find_first_insert_nth_eq)
        apply (subst incr_bounds_eq[where k = 0])
        subgoal by simp
        apply (rule nterm_to_term_closed_wellformed)
        by auto
    next
      case False
      thus ?thesis
        apply auto
        apply (subst find_first_insert_nth_neq)
        subgoal by simp
        by (cases "find_first name \<Gamma>") auto
    qed
next
  case (Nabs y t)
  note insert_nth_take_drop[simp del]
  show ?case
    proof (cases "x = y")
      case True
      have "nterm_to_term (y # \<Gamma>) t = replace_bound (Suc n) (nterm_to_term (y # insert_nth n y \<Gamma>) t) (nterm_to_term \<Gamma> u')"
        proof (subst replace_bound_eq)
          show "Suc n |\<notin>| bounds (nterm_to_term (y # insert_nth n y \<Gamma>) t)"
            apply (rule nterm_to_term_bounds_dupl[where i = 0])
            subgoal by simp
            subgoal using Nabs(3) by (simp add: insert_nth_take_drop)
            subgoal by simp
            apply simp
            apply (subst nth_insert_nth_index_eq)
            using Nabs by auto
          show "nterm_to_term (y # \<Gamma>) t = incr_bounds (- 1) (Suc n + 1) (nterm_to_term (y # insert_nth n y \<Gamma>) t)"
            apply (subst nterm_to_term_insert_dupl[where \<Gamma> = "y # \<Gamma>" and y = y and n = "Suc n"])
            using Nabs by auto
        qed
      with True show ?thesis
        by auto
    next
      case False
      have "nterm_to_term (y # \<Gamma>) (subst_single t x u') = replace_bound (Suc n) (nterm_to_term (y # insert_nth n x \<Gamma>) t) (nterm_to_term \<Gamma> u')"
        apply (subst Nabs(1)[of "Suc n"])
        subgoal by fact
        subgoal using Nabs by simp
        subgoal using False Nabs by simp
        apply (subst nterm_to_term_eq_closed[where t = u'])
        using Nabs by auto
      with False show ?thesis
        by auto
    qed
qed auto

corollary nterm_to_term_subst_\<beta>:
  assumes "closed u'"
  shows "nterm_to_term \<Gamma> (subst u (fmap_of_list [(x, u')])) = nterm_to_term (x # \<Gamma>) u [nterm_to_term \<Gamma> u']\<^sub>\<beta>"
using assms
by (rule nterm_to_term_subst_replace_bound[where n = 0, simplified, unfolded subst_single_eq])

end