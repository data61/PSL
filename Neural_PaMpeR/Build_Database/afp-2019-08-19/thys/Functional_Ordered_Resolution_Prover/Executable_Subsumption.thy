(*  Title:       An Executable Algorithm for Clause Subsumption
    Author:      Dmitriy Traytel <traytel at inf.ethz.ch>, 2017
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>An Executable Algorithm for Clause Subsumption\<close>

text \<open>
This theory provides a functional implementation of clause subsumption, building
on the \textsf{IsaFoR} library (part of the AFP entry \<open>First_Order_Terms\<close>).
\<close>

theory Executable_Subsumption
  imports IsaFoR_Term First_Order_Terms.Matching
begin


subsection \<open>Naive Implementation of Clause Subsumption\<close>

fun subsumes_list where
  "subsumes_list [] Ks \<sigma> = True"
| "subsumes_list (L # Ls) Ks \<sigma> =
     (\<exists>K \<in> set Ks. is_pos K = is_pos L \<and>
       (case match_term_list [(atm_of L, atm_of K)] \<sigma> of
         None \<Rightarrow> False
       | Some \<rho> \<Rightarrow> subsumes_list Ls (remove1 K Ks) \<rho>))"

lemma atm_of_map_literal[simp]: "atm_of (map_literal f l) = f (atm_of l)"
  by (cases l; simp)

definition "extends_subst \<sigma> \<tau> = (\<forall>x \<in> dom \<sigma>. \<sigma> x = \<tau> x)"

lemma extends_subst_refl[simp]: "extends_subst \<sigma> \<sigma>"
  unfolding extends_subst_def by auto

lemma extends_subst_trans: "extends_subst \<sigma> \<tau> \<Longrightarrow> extends_subst \<tau> \<rho> \<Longrightarrow> extends_subst \<sigma> \<rho>"
  unfolding extends_subst_def dom_def by (metis mem_Collect_eq)

lemma extends_subst_dom: "extends_subst \<sigma> \<tau> \<Longrightarrow> dom \<sigma> \<subseteq> dom \<tau>"
  unfolding extends_subst_def dom_def by auto

lemma extends_subst_extends: "extends_subst \<sigma> \<tau> \<Longrightarrow> x \<in> dom \<sigma> \<Longrightarrow> \<tau> x = \<sigma> x"
  unfolding extends_subst_def dom_def by auto

lemma extends_subst_fun_upd_new:
  "\<sigma> x = None \<Longrightarrow> extends_subst (\<sigma>(x \<mapsto> t)) \<tau> \<longleftrightarrow> extends_subst \<sigma> \<tau> \<and> \<tau> x = Some t"
  unfolding extends_subst_def dom_fun_upd subst_of_map_def
  by (force simp add: dom_def split: option.splits)

lemma extends_subst_fun_upd_matching:
  "\<sigma> x = Some t \<Longrightarrow> extends_subst (\<sigma>(x \<mapsto> t)) \<tau> \<longleftrightarrow> extends_subst \<sigma> \<tau>"
  unfolding extends_subst_def dom_fun_upd subst_of_map_def
  by (auto simp add: dom_def split: option.splits)

lemma extends_subst_empty[simp]: "extends_subst Map.empty \<tau>"
  unfolding extends_subst_def by auto

lemma extends_subst_cong_term:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_term t \<subseteq> dom \<sigma> \<Longrightarrow> t \<cdot> subst_of_map Var \<sigma> = t \<cdot> subst_of_map Var \<tau>"
  by (force simp: extends_subst_def subst_of_map_def split: option.splits intro!: term_subst_eq)

lemma extends_subst_cong_lit:
  "extends_subst \<sigma> \<tau> \<Longrightarrow> vars_lit L \<subseteq> dom \<sigma> \<Longrightarrow> L \<cdot>lit subst_of_map Var \<sigma> = L \<cdot>lit subst_of_map Var \<tau>"
  by (cases L) (auto simp: extends_subst_cong_term)

definition "subsumes_modulo C D \<sigma> =
   (\<exists>\<tau>. dom \<tau> = vars_clause C \<union> dom \<sigma> \<and> extends_subst \<sigma> \<tau> \<and> subst_cls C (subst_of_map Var \<tau>) \<subseteq># D)"

abbreviation subsumes_list_modulo where
  "subsumes_list_modulo Ls Ks \<sigma> \<equiv> subsumes_modulo (mset Ls) (mset Ks) \<sigma>"

lemma vars_clause_add_mset[simp]: "vars_clause (add_mset L C) = vars_lit L \<union> vars_clause C"
  unfolding vars_clause_def by auto

lemma subsumes_list_modulo_Cons: "subsumes_list_modulo (L # Ls) Ks \<sigma> \<longleftrightarrow>
  (\<exists>K \<in> set Ks. \<exists>\<tau>. extends_subst \<sigma> \<tau> \<and> dom \<tau> = vars_lit L \<union> dom \<sigma> \<and> L \<cdot>lit (subst_of_map Var \<tau>) = K
     \<and> subsumes_list_modulo Ls (remove1 K Ks) \<tau>)"
  unfolding subsumes_modulo_def
proof (safe, goal_cases left_right right_left)
  case (left_right \<tau>)
  then show ?case
    by (intro bexI[of _ "L \<cdot>lit subst_of_map Var \<tau>"]
      exI[of _ "\<lambda>x. if x \<in> vars_lit L \<union> dom \<sigma> then \<tau> x else None"], intro conjI exI[of _ \<tau>])
      (auto 0 3 simp: extends_subst_def dom_def split: if_splits
      simp: insert_subset_eq_iff subst_lit_def  intro!: extends_subst_cong_lit)
next
  case (right_left K \<tau> \<tau>')
  then show ?case 
    by (intro bexI[of _ "L \<cdot>lit subst_of_map Var \<tau>"] exI[of _ \<tau>'], intro conjI exI[of _ \<tau>])
     (auto simp: insert_subset_eq_iff subst_lit_def extends_subst_cong_lit
       intro: extends_subst_trans)
qed

lemma decompose_Some_var_terms: "decompose (Fun f ss) (Fun g ts) = Some eqs \<Longrightarrow>
   f = g \<and> length ss = length ts \<and> eqs = zip ss ts \<and>
   (\<Union>(t, u)\<in>set ((Fun f ss, Fun g ts) # P). vars_term t) =
   (\<Union>(t, u)\<in>set (eqs @ P). vars_term t)"
  by (drule decompose_Some)
    (fastforce simp: in_set_zip in_set_conv_nth Bex_def image_iff)

lemma match_term_list_sound: "match_term_list tus \<sigma> = Some \<tau> \<Longrightarrow>
  extends_subst \<sigma> \<tau> \<and> dom \<tau> = (\<Union>(t, u)\<in>set tus. vars_term t) \<union> dom \<sigma> \<and>
  (\<forall>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> = u)"
proof (induct tus \<sigma> rule: match_term_list.induct)
  case (2 x t P \<sigma>)
  then show ?case
    by (auto 0 3 simp: extends_subst_fun_upd_new extends_subst_fun_upd_matching 
      subst_of_map_def dest: extends_subst_extends simp del: fun_upd_apply
      split: if_splits option.splits)
next
  case (3 f ss g ts P \<sigma>)
  from 3(2) obtain eqs where "decompose (Fun f ss) (Fun g ts) = Some eqs"
    "match_term_list (eqs @ P) \<sigma> = Some \<tau>" by (auto split: option.splits)
  with 3(1)[OF this] show ?case
  proof (elim decompose_Some_var_terms[where P = P, elim_format] conjE, intro conjI, goal_cases extend dom subst)
    case subst
    from subst(3,5,6,7) show ?case
      by (auto 0 6 simp: in_set_conv_nth list_eq_iff_nth_eq Ball_def)
  qed auto
qed auto

lemma match_term_list_complete: "match_term_list tus \<sigma> = None \<Longrightarrow>
   extends_subst \<sigma> \<tau> \<Longrightarrow> dom \<tau> = (\<Union>(t, u)\<in>set tus. vars_term t) \<union> dom \<sigma> \<Longrightarrow>
    (\<exists>(t,u)\<in>set tus. t \<cdot> subst_of_map Var \<tau> \<noteq> u)"
proof (induct tus \<sigma> arbitrary: \<tau> rule: match_term_list.induct)
  case (2 x t P \<sigma>)
  then show ?case
    by (auto simp: extends_subst_fun_upd_new extends_subst_fun_upd_matching 
      subst_of_map_def dest: extends_subst_extends simp del: fun_upd_apply
      split: if_splits option.splits)
next
  case (3 f ss g ts P \<sigma>)
  show ?case
  proof (cases "decompose (Fun f ss) (Fun g ts) = None")
    case False
    with 3(2) obtain eqs where "decompose (Fun f ss) (Fun g ts) = Some eqs"
      "match_term_list (eqs @ P) \<sigma> = None" by (auto split: option.splits)
    with 3(1)[OF this 3(3) trans[OF 3(4) arg_cong[of _ _ "\<lambda>x. x \<union> dom \<sigma>"]]] show ?thesis
    proof (elim decompose_Some_var_terms[where P = P, elim_format] conjE, goal_cases subst)
      case subst
      from subst(1)[OF subst(6)] subst(4,5) show ?case
        by (auto 0 3 simp: in_set_conv_nth list_eq_iff_nth_eq Ball_def)
    qed
  qed auto
qed auto

lemma unique_extends_subst:
  assumes extends: "extends_subst \<sigma> \<tau>" "extends_subst \<sigma> \<rho>" and
    dom: "dom \<tau> = vars_term t \<union> dom \<sigma>" "dom \<rho> = vars_term t \<union> dom \<sigma>" and
    eq: "t \<cdot> subst_of_map Var \<rho> = t \<cdot> subst_of_map Var \<tau>"
  shows "\<rho> = \<tau>"
proof
  fix x
  consider (a) "x \<in> dom \<sigma>" | (b) "x \<in> vars_term t" | (c) "x \<notin> dom \<tau>" using assms by auto
  then show "\<rho> x = \<tau> x"
  proof cases
    case a
    then show ?thesis using extends unfolding extends_subst_def by auto
  next
    case b
    with eq show ?thesis
    proof (induct t)
      case (Var x)
      with trans[OF dom(1) dom(2)[symmetric]] show ?case
        by (auto simp: subst_of_map_def split: option.splits)
    qed auto
  next
    case c
    then have "\<rho> x = None" "\<tau> x = None" using dom by auto
    then show ?thesis by simp
  qed
qed

lemma subsumes_list_alt:
  "subsumes_list Ls Ks \<sigma> \<longleftrightarrow> subsumes_list_modulo Ls Ks \<sigma>"
proof (induction Ls Ks \<sigma> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks \<sigma>)
  show ?case
    unfolding subsumes_list_modulo_Cons subsumes_list.simps
  proof ((intro bex_cong[OF refl] ext iffI; elim exE conjE), goal_cases LR RL)
    case (LR K)
    show ?case
      by (insert LR; cases K; cases L; auto simp: Cons.IH split: option.splits dest!: match_term_list_sound)
  next
    case (RL K \<tau>)
    then show ?case
    proof (cases "match_term_list [(atm_of L, atm_of K)] \<sigma>")
      case None
      with RL show ?thesis
        by (auto simp: Cons.IH dest!: match_term_list_complete)
    next
      case (Some \<tau>')
      with RL show ?thesis
        using unique_extends_subst[of \<sigma> \<tau> \<tau>' "atm_of L"]
        by (auto simp: Cons.IH dest!: match_term_list_sound)
    qed
  qed
qed (auto simp: subsumes_modulo_def subst_cls_def vars_clause_def intro: extends_subst_refl)

lemma subsumes_subsumes_list[code_unfold]:
  "subsumes (mset Ls) (mset Ks) = subsumes_list Ls Ks Map.empty"
unfolding subsumes_list_alt[of Ls Ks Map.empty]
proof
  assume "subsumes (mset Ls) (mset Ks)"
  then obtain \<sigma> where "subst_cls (mset Ls) \<sigma> \<subseteq># mset Ks" unfolding subsumes_def by blast
  moreover define \<tau> where "\<tau> = (\<lambda>x. if x \<in> vars_clause (mset Ls) then Some (\<sigma> x) else None)"
  ultimately show "subsumes_list_modulo Ls Ks Map.empty"
    unfolding subsumes_modulo_def
    by (subst (asm) same_on_vars_clause[of _ \<sigma> "subst_of_map Var \<tau>"])
      (auto intro!: exI[of _ \<tau>] simp: subst_of_map_def[abs_def] split: if_splits)
qed (auto simp: subsumes_modulo_def subst_lit_def subsumes_def)

lemma strictly_subsumes_subsumes_list[code_unfold]:
  "strictly_subsumes (mset Ls) (mset Ks) =
    (subsumes_list Ls Ks Map.empty \<and> \<not> subsumes_list Ks Ls Map.empty)"
  unfolding strictly_subsumes_def subsumes_subsumes_list by simp

lemma subsumes_list_filterD: "subsumes_list Ls (filter P Ks) \<sigma> \<Longrightarrow> subsumes_list Ls Ks \<sigma>"
proof (induction Ls arbitrary: Ks \<sigma>)
  case (Cons L Ls)
  from Cons.prems show ?case
    by (auto dest!: Cons.IH simp: filter_remove1[symmetric] split: option.splits)
qed simp

lemma subsumes_list_filterI:
  assumes match: "(\<And>L K \<sigma> \<tau>. L \<in> set Ls \<Longrightarrow>
    match_term_list [(atm_of L, atm_of K)] \<sigma> = Some \<tau> \<Longrightarrow> is_pos L = is_pos K \<Longrightarrow> P K)"
  shows "subsumes_list Ls Ks \<sigma> \<Longrightarrow> subsumes_list Ls (filter P Ks) \<sigma>"
using assms proof (induction Ls Ks \<sigma> rule: subsumes_list.induct[case_names Nil Cons])
  case (Cons L Ls Ks \<sigma>)
  from Cons.prems show ?case
    unfolding subsumes_list.simps set_filter bex_simps conj_assoc
    by (elim bexE conjE)
      (rule exI, rule conjI, assumption,
        auto split: option.splits simp: filter_remove1[symmetric] intro!: Cons.IH)
qed simp

lemma subsumes_list_Cons_filter_iff:
  assumes sorted_wrt: "sorted_wrt leq (L # Ls)" and trans: "transp leq"
  and match: "(\<And>L K \<sigma> \<tau>.
    match_term_list [(atm_of L, atm_of K)] \<sigma> = Some \<tau> \<Longrightarrow> is_pos L = is_pos K \<Longrightarrow> leq L K)"
shows "subsumes_list (L # Ls) (filter (leq L) Ks) \<sigma> \<longleftrightarrow> subsumes_list (L # Ls) Ks \<sigma>"
  apply (rule iffI[OF subsumes_list_filterD subsumes_list_filterI]; assumption?)
  unfolding list.set insert_iff
  apply (elim disjE)
  subgoal by (auto split: option.splits elim!: match)
  subgoal for L K \<sigma> \<tau>
    using sorted_wrt unfolding List.sorted_wrt.simps(2)
    apply (elim conjE)
    apply (drule bspec, assumption)
    apply (erule transpD[OF trans])
    apply (erule match)
    by auto
  done

definition leq_head  :: "('f::linorder, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "leq_head t u = (case (root t, root u) of
    (None, _) \<Rightarrow> True
  | (_, None) \<Rightarrow> False
  | (Some f, Some g) \<Rightarrow> f \<le> g)"
definition "leq_lit L K = (case (K, L) of
    (Neg _, Pos _) \<Rightarrow> True
  | (Pos _, Neg _) \<Rightarrow> False
  | _ \<Rightarrow> leq_head (atm_of L) (atm_of K))"

lemma transp_leq_lit[simp]: "transp leq_lit"
  unfolding transp_def leq_lit_def leq_head_def by (force split: option.splits literal.splits)

lemma reflp_leq_lit[simp]: "reflp_on leq_lit A"
  unfolding reflp_on_def leq_lit_def leq_head_def by (auto split: option.splits literal.splits)

lemma total_leq_lit[simp]: "total_on leq_lit A"
  unfolding total_on_def leq_lit_def leq_head_def by (auto split: option.splits literal.splits)

lemma leq_head_subst[simp]: "leq_head t (t \<cdot> \<sigma>)"
  by (induct t) (auto simp: leq_head_def)

lemma leq_lit_match:
  fixes L K :: "('f :: linorder, 'v) term literal"
  shows "match_term_list [(atm_of L, atm_of K)] \<sigma> = Some \<tau> \<Longrightarrow> is_pos L = is_pos K \<Longrightarrow> leq_lit L K"
  by (cases L; cases K)
    (auto simp: leq_lit_def dest!: match_term_list_sound split: option.splits)


subsection \<open>Optimized Implementation of Clause Subsumption\<close>

fun subsumes_list_filter where
  "subsumes_list_filter [] Ks \<sigma> = True"
| "subsumes_list_filter (L # Ls) Ks \<sigma> =
     (let Ks = filter (leq_lit L) Ks in
     (\<exists>K \<in> set Ks. is_pos K = is_pos L \<and>
       (case match_term_list [(atm_of L, atm_of K)] \<sigma> of
         None \<Rightarrow> False
       | Some \<rho> \<Rightarrow> subsumes_list_filter Ls (remove1 K Ks) \<rho>)))"

lemma sorted_wrt_subsumes_list_subsumes_list_filter:
  "sorted_wrt leq_lit Ls \<Longrightarrow> subsumes_list Ls Ks \<sigma> = subsumes_list_filter Ls Ks \<sigma>"
proof (induction Ls arbitrary: Ks \<sigma>)
  case (Cons L Ls)
  from Cons.prems have "subsumes_list (L # Ls) Ks \<sigma> = subsumes_list (L # Ls) (filter (leq_lit L) Ks) \<sigma>"
    by (intro subsumes_list_Cons_filter_iff[symmetric]) (auto dest: leq_lit_match)
  also have "subsumes_list (L # Ls) (filter (leq_lit L) Ks) \<sigma> = subsumes_list_filter (L # Ls) Ks \<sigma>"
    using Cons.prems by (auto simp: Cons.IH split: option.splits)
  finally show ?case .
qed simp


subsection \<open>Definition of Deterministic QuickSort\<close>

text \<open>
  This is the functional description of the standard variant of deterministic
  QuickSort that always chooses the first list element as the pivot as given
  by Hoare in 1962. For a list that is already sorted, this leads to $n(n-1)$
  comparisons, but as is well known, the average case is much better.

  The code below is adapted from Manuel Eberl's \<open>Quick_Sort_Cost\<close> AFP
  entry, but without invoking probability theory and using a predicate instead
  of a set.
\<close>

fun quicksort :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "quicksort _ [] = []"
| "quicksort R (x # xs) =
     quicksort R (filter (\<lambda>y. R y x) xs) @ [x] @ quicksort R (filter (\<lambda>y. \<not> R y x) xs)"

text \<open>
  We can easily show that this QuickSort is correct:
\<close>

theorem mset_quicksort [simp]: "mset (quicksort R xs) = mset xs"
  by (induction R xs rule: quicksort.induct) simp_all

corollary set_quicksort [simp]: "set (quicksort R xs) = set xs"
  by (induction R xs rule: quicksort.induct) auto

theorem sorted_wrt_quicksort:
  assumes "transp R" and "total_on R (set xs)" and "reflp_on R (set xs)"
  shows   "sorted_wrt R (quicksort R xs)"
using assms
proof (induction R xs rule: quicksort.induct)
  case (2 R x xs)
  have total: "R a b" if "\<not> R b a" "a \<in> set (x#xs)" "b \<in> set (x#xs)" for a b
    using "2.prems" that unfolding total_on_def reflp_on_def by (cases "a = b") auto

  have "sorted_wrt R (quicksort R (filter (\<lambda>y. R y x) xs))"
          "sorted_wrt R (quicksort R (filter (\<lambda>y. \<not> R y x) xs))"
    using "2.prems" by (intro "2.IH"; auto simp: total_on_def reflp_on_def)+
  then show ?case
    by (auto simp: sorted_wrt_append \<open>transp R\<close>
     intro: transpD[OF \<open>transp R\<close>] dest!: total)
qed auto

text \<open>
End of the material adapted from Eberl's \<open>Quick_Sort_Cost\<close>.
\<close>

lemma subsumes_list_subsumes_list_filter[abs_def, code_unfold]:
  "subsumes_list Ls Ks \<sigma> = subsumes_list_filter (quicksort leq_lit Ls) Ks \<sigma>"
  by (rule trans[OF box_equals[OF _ subsumes_list_alt[symmetric] subsumes_list_alt[symmetric]]
    sorted_wrt_subsumes_list_subsumes_list_filter])
    (auto simp: sorted_wrt_quicksort)

end
