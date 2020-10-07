(*  Title:      Presburger-Automata/DFS.thy
    Author:     Toshiaki Nishihara and Yasuhiko Minamide
    Author:     Stefan Berghofer and Alex Krauss, TU Muenchen, 2008-2009
*)

section \<open>Depth First Search\<close>

theory DFS
imports Main
begin

definition "succsr succs = {(x, y). y \<in> set (succs x)}"

partial_function (tailrec) gen_dfs
where
  "gen_dfs succs ins memb S wl =
    (case wl of
      [] \<Rightarrow> S
    | x # xs \<Rightarrow>
        if memb x S then gen_dfs succs ins memb S xs
        else gen_dfs succs ins memb (ins x S) (succs x @ xs))"

lemma gen_dfs_simps[simp]:
  "gen_dfs succs ins memb S [] = S"
  "gen_dfs succs ins memb S (x # xs) =
    (if memb x S then gen_dfs succs ins memb S xs
     else gen_dfs succs ins memb (ins x S) (succs x @ xs))"
  by (simp_all add: gen_dfs.simps)

locale DFS =
  fixes succs :: "'a \<Rightarrow> 'a list"
    and is_node :: "'a \<Rightarrow> bool"
    and invariant :: "'b \<Rightarrow> bool"
    and ins :: "'a \<Rightarrow> 'b \<Rightarrow> 'b"
    and memb :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
    and empt :: 'b
  assumes ins_eq: "\<And>x y S. is_node x \<Longrightarrow> is_node y \<Longrightarrow> invariant S \<Longrightarrow> \<not> memb y S \<Longrightarrow>
      memb x (ins y S) = ((x = y) \<or> memb x S)"
    and empt: "\<And>x. is_node x \<Longrightarrow> \<not> memb x empt"
    and succs_is_node: "\<And>x. is_node x \<Longrightarrow> list_all is_node (succs x)"
    and empt_invariant: "invariant empt"
    and ins_invariant: "\<And>x S. is_node x \<Longrightarrow> invariant S \<Longrightarrow> \<not> memb x S \<Longrightarrow> invariant (ins x S)"
    and graph_finite: "finite {x. is_node x}"
begin

definition rel where
  "rel = inv_image finite_psubset (\<lambda>S. {n. is_node n \<and> \<not> memb n S})"

abbreviation "dfs \<equiv> gen_dfs succs ins memb"

lemma dfs_induct [consumes 2, case_names base step]:
  assumes S: "invariant S"
    and xs: "list_all is_node xs"
    and I1: "\<And>S. invariant S \<Longrightarrow> P S []"
    and I2: "\<And>S x xs. invariant S \<Longrightarrow> is_node x \<Longrightarrow> list_all is_node xs \<Longrightarrow>
      (memb x S \<Longrightarrow> P S xs) \<Longrightarrow> (\<not> memb x S \<Longrightarrow> P (ins x S) (succs x @ xs)) \<Longrightarrow> P S (x # xs)"
  shows "P S xs" using I1 I2 S xs
  apply induction_schema
  apply atomize_elim
  apply (case_tac xs, simp+)
  apply atomize_elim
  apply (rule conjI)
  apply (rule ins_invariant, assumption+)
  apply (rule succs_is_node, assumption)
  apply (relation "rel <*lex*> measure length")
  apply (simp add: wf_lex_prod rel_def)
  apply simp
  apply simp
  apply (rule disjI1)
  apply (simp add: rel_def finite_psubset_def)
  apply (rule conjI)
  apply (auto simp add: ins_eq graph_finite cong: conj_cong)
  done

definition "succss xs = (\<Union>x\<in>xs. set (succs x))"

definition "set_of S = {x. is_node x \<and> memb x S}"

definition "reachable xs = {(x, y). y \<in> set (succs x)}\<^sup>* `` xs"

lemma visit_subset_dfs: "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow>
    is_node y \<Longrightarrow> memb y S \<Longrightarrow> memb y (dfs S xs)"
  by (induct S xs rule: dfs_induct) (simp_all add: ins_eq)

lemma next_subset_dfs: "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow>
    x \<in> set xs \<Longrightarrow> memb x (dfs S xs)"
proof (induct S xs rule: dfs_induct)
  case base
  then show ?case by simp
next
  case (step S y xs)
  then show ?case
    by (auto simp add: visit_subset_dfs ins_eq ins_invariant succs_is_node)
qed

lemma succss_closed_dfs':
  "invariant ys \<Longrightarrow> list_all is_node xs \<Longrightarrow>
    succss (set_of ys) \<subseteq> set xs \<union> set_of ys \<Longrightarrow>
    succss (set_of (dfs ys xs)) \<subseteq> set_of (dfs ys xs)"
  by (induct ys xs rule: dfs_induct)
    (auto simp add: ins_eq succss_def set_of_def cong: conj_cong)

lemma succss_closed_dfs: "list_all is_node xs \<Longrightarrow>
    succss (set_of (dfs empt xs)) \<subseteq> set_of (dfs empt xs)"
  apply (rule succss_closed_dfs')
  apply (rule empt_invariant)
  apply assumption
  apply (simp add: succss_def)
  apply (rule subsetI)
  apply (erule UN_E)
  apply (simp add: set_of_def empt cong: conj_cong)
  done

lemma Image_closed_trancl: assumes "r `` X \<subseteq> X" shows "r\<^sup>* `` X = X"
proof
  show "X \<subseteq> r\<^sup>* `` X" by auto
  show "r\<^sup>* `` X \<subseteq> X"
  proof -
    { fix x y
      assume y: "y \<in> X"
      assume "(y,x) \<in> r\<^sup>*"
      then have "x \<in> X" using assms y
        by induct (auto simp add: Image_def)
    } then show ?thesis by auto
  qed
qed

lemma reachable_closed_dfs:
  assumes "list_all is_node xs"
  shows "reachable (set xs) \<subseteq> set_of (dfs empt xs)"
proof -
  from assms have "reachable (set xs) \<subseteq> reachable (set_of (dfs empt xs))"
    apply (unfold reachable_def)
    apply (rule Image_mono)
    apply (auto simp add: set_of_def next_subset_dfs empt_invariant list_all_iff)
    done
  also from succss_closed_dfs assms have "\<dots> = set_of (dfs empt xs)"
    apply (unfold reachable_def)
    apply (rule Image_closed_trancl)
    apply (auto simp add: succss_def set_of_def)
    done
  finally show ?thesis .
qed

lemma reachable_succs: "reachable (set (succs x)) \<subseteq> reachable {x}"
  by (auto simp add: reachable_def intro: converse_rtrancl_into_rtrancl)

lemma dfs_subset_reachable_visit_nodes:
  "invariant ys \<Longrightarrow> list_all is_node xs \<Longrightarrow>
     set_of (dfs ys xs) \<subseteq> reachable (set xs) \<union> set_of ys"
proof (induct ys xs rule: dfs_induct)
  case base
  then show ?case by (simp add: reachable_def)
next
  case (step S x xs)
  show ?case
  proof (cases "memb x S")
    case True
    with step show ?thesis
      by (auto simp add: reachable_def)
  next
    case False
    have "reachable (set (succs x)) \<subseteq> reachable {x}"
      by (rule reachable_succs)
    then have "reachable (set (succs x @ xs)) \<subseteq> reachable (set (x # xs))"
      by (auto simp add: reachable_def)
    then show ?thesis using step
      by (auto simp add: reachable_def ins_eq set_of_def cong: conj_cong)
  qed
qed

theorem dfs_eq_reachable:
  assumes y: "is_node y"
    and xs: "list_all is_node xs"
  shows "memb y (dfs empt xs) = (y \<in> reachable (set xs))"
proof
  assume "memb y (dfs empt xs)"
  with dfs_subset_reachable_visit_nodes [OF empt_invariant xs] y
  show "y \<in> reachable (set xs)"
    by (auto simp add: empt set_of_def)
next
  assume "y \<in> reachable (set xs)"
  with reachable_closed_dfs [OF xs] show "memb y (dfs empt xs)"
    by (auto simp add: set_of_def)
qed

theorem dfs_eq_rtrancl:
  assumes y: "is_node y"
    and x: "is_node x"
  shows "memb y (dfs empt [x]) = ((x,y) \<in> (succsr succs)\<^sup>*)"
proof -
  from x have x': "list_all is_node [x]" by simp
  show ?thesis
    by (simp only: dfs_eq_reachable [OF y x'] reachable_def succsr_def) (auto simp add: empt)
qed

theorem dfs_invariant [consumes 2, case_names base step]:
  assumes S: "invariant S"
    and xs: "list_all is_node xs"
    and H: "I S"
    and I: "\<And>S x. \<not> memb x S \<Longrightarrow> is_node x \<Longrightarrow> invariant S \<Longrightarrow> I S \<Longrightarrow> I (ins x S)"
  shows "I (dfs S xs)"
proof -
  from S xs H
  have "I (dfs S xs) \<and> invariant (dfs S xs)"
  proof (induct S xs rule: dfs_induct)
    case base
    then show ?case by simp
  next
    case (step S x xs)
    show ?case
    proof (cases "memb x S")
      case True
      then show ?thesis by (simp add: step)
    next
      case False
      then show ?thesis
        apply simp
        apply (rule step)
        apply assumption
        apply (rule I)
        apply assumption
        apply (rule step)+
        done
    qed
  qed
  then show ?thesis ..
qed

theorem dfs_invariant': "invariant S \<Longrightarrow> list_all is_node xs \<Longrightarrow> invariant (dfs S xs)"
  by (induct S xs rule: dfs_induct) auto

theorem succsr_is_node:
  assumes "(x, y) \<in> (succsr succs)\<^sup>*"
  shows "is_node x \<Longrightarrow> is_node y" using assms
proof induct
  case base
  then show ?case .
next
  case (step y z)
  then have "is_node y" by simp
  then have "list_all is_node (succs y)"
    by (rule succs_is_node)
  with step show ?case
    by (simp add: succsr_def list_all_iff)
qed

end

declare gen_dfs_simps [simp del]

end
