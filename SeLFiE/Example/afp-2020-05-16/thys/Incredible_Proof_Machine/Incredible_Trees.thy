theory Incredible_Trees
imports
  "HOL-Library.Sublist" 
  "HOL-Library.Countable"
  Entailment
  Rose_Tree
  Abstract_Rules_To_Incredible
begin

text \<open>This theory defines incredible trees, which carry roughly the same information
as a (tree-shaped) incredible graph, but where the structure is still given by the data type, 
and not by a set of edges etc.\<close>


text \<open>
Tree-shape, but incredible-graph-like content (port names, explicit annotation and substitution)
\<close>

datatype ('form,'rule,'subst,'var) itnode =
    I (iNodeOf': "('form, 'rule) graph_node")
      (iOutPort': "'form reg_out_port")
      (iAnnot': "nat")
      (iSubst': "'subst")
  | H (iAnnot': "nat")
      (iSubst': "'subst")

abbreviation "INode n p i s ants \<equiv> RNode (I n p i s) ants"
abbreviation "HNode i s ants \<equiv> RNode (H i s) ants"

type_synonym ('form,'rule,'subst,'var) itree = "('form,'rule,'subst,'var) itnode rose_tree"

fun iNodeOf where
   "iNodeOf (INode n p i s ants) = n"
 | "iNodeOf (HNode i s ants) = Helper"

context Abstract_Formulas begin
fun iOutPort where
   "iOutPort (INode n p i s ants) = p"
 | "iOutPort (HNode i s ants) = anyP"
end

fun iAnnot where "iAnnot it = iAnnot' (root it)"
fun iSubst where "iSubst it = iSubst' (root it)"
fun iAnts where "iAnts it = children it"

type_synonym ('form, 'rule, 'subst) fresh_check = "('form, 'rule) graph_node \<Rightarrow> nat \<Rightarrow> 'subst \<Rightarrow> 'form entailment \<Rightarrow> bool"

context  Abstract_Task
begin

  text \<open>The well-formedness of the tree. The first argument can be varied, depending on whether we
  are interested in the local freshness side-conditions or not.\<close>

  inductive iwf :: "('form, 'rule, 'subst) fresh_check \<Rightarrow> ('form,'rule,'subst,'var) itree \<Rightarrow> 'form entailment \<Rightarrow> bool"
    for fc
    where
    iwf: "\<lbrakk>
       n \<in> sset nodes;
       Reg p |\<in>| outPorts n;
       list_all2 (\<lambda> ip t. iwf fc t ((\<lambda> h . subst s (freshen i (labelsOut n h))) |`| hyps_for n ip |\<union>| \<Gamma> \<turnstile> subst s (freshen i (labelsIn n ip))))
                (inPorts' n) ants;
       fc n i s (\<Gamma> \<turnstile> c);
       c = subst s (freshen i p)
      \<rbrakk> \<Longrightarrow> iwf fc (INode n p i s ants) (\<Gamma> \<turnstile> c)"  
  | iwfH: "\<lbrakk>
       c |\<notin>| ass_forms;
       c |\<in>| \<Gamma>;
       c = subst s (freshen i anyP)
      \<rbrakk> \<Longrightarrow> iwf fc (HNode i s []) (\<Gamma> \<turnstile> c)"  

lemma iwf_subst_freshen_outPort:
  "iwf lc ts ent \<Longrightarrow>
  snd ent = subst (iSubst ts) (freshen (iAnnot ts) (iOutPort ts))"
  by (auto elim: iwf.cases)

definition all_local_vars :: "('form, 'rule) graph_node \<Rightarrow> 'var set" where
  "all_local_vars n = \<Union>(local_vars n ` fset (inPorts n))"

lemma all_local_vars_Helper[simp]:
  "all_local_vars Helper = {}"
  unfolding all_local_vars_def by simp

lemma all_local_vars_Assumption[simp]:
  "all_local_vars (Assumption c) = {}"
  unfolding all_local_vars_def by simp

text \<open>Local freshness side-conditions, corresponding what we have in the
theory \<open>Natural_Deduction\<close>.\<close>

inductive local_fresh_check :: "('form, 'rule, 'subst) fresh_check" where
  "\<lbrakk>\<And> f. f |\<in>| \<Gamma> \<Longrightarrow> freshenLC i ` (all_local_vars n) \<inter> lconsts f = {};
    freshenLC i ` (all_local_vars n) \<inter> subst_lconsts s = {}
   \<rbrakk> \<Longrightarrow> local_fresh_check n i s (\<Gamma> \<turnstile> c)"

abbreviation "local_iwf \<equiv> iwf local_fresh_check"

text \<open>No freshness side-conditions. Used with the tree that comes out of
\<open>globalize\<close>, where we establish the (global) freshness conditions
separately.\<close>

inductive no_fresh_check :: "('form, 'rule, 'subst) fresh_check" where
  "no_fresh_check n i s (\<Gamma> \<turnstile> c)"

abbreviation "plain_iwf \<equiv> iwf no_fresh_check"

fun isHNode where
  "isHNode (HNode _ _ _ ) = True"
 |"isHNode _ = False"

lemma iwf_edge_match:
  assumes "iwf fc t ent"
  assumes "is@[i] \<in> it_paths t"
  shows "subst (iSubst (tree_at t (is@[i]))) (freshen (iAnnot (tree_at t (is@[i]))) (iOutPort (tree_at t (is@[i]))))
     = subst (iSubst (tree_at t is)) (freshen (iAnnot (tree_at t is)) (a_conc (inPorts' (iNodeOf (tree_at t is)) ! i)))"
  using assms
  apply (induction arbitrary: "is" i)
   apply (auto elim!: it_paths_SnocE)[1]
   apply (rename_tac "is" i)
   apply (case_tac "is")
    apply (auto dest!: list_all2_nthD2)[1]
    using iwf_subst_freshen_outPort
    apply (solves \<open>(auto)[1]\<close>)
   apply (auto elim!: it_paths_ConsE dest!: list_all2_nthD2)[1]
   using it_path_SnocI
   apply (solves blast)
  apply (solves auto)
  done

lemma iwf_length_inPorts:
  assumes "iwf fc t ent"
  assumes "is \<in> it_paths t"
  shows "length (iAnts (tree_at t is)) \<le> length (inPorts' (iNodeOf (tree_at t is)))"
  using assms
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto elim!: it_paths_RNodeE dest: list_all2_lengthD list_all2_nthD2)

lemma iwf_local_not_in_subst:
  assumes "local_iwf t ent"
  assumes "is \<in> it_paths t"
  assumes "var \<in> all_local_vars (iNodeOf (tree_at t is))"
  shows "freshenLC (iAnnot (tree_at t is)) var \<notin> subst_lconsts (iSubst (tree_at t is))"
  using assms
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto 4 4 elim!: it_paths_RNodeE local_fresh_check.cases dest: list_all2_lengthD list_all2_nthD2)
  
lemma iwf_length_inPorts_not_HNode:
  assumes "iwf fc t ent"
  assumes "is \<in> it_paths t"
  assumes "\<not> (isHNode (tree_at t is))"
  shows "length (iAnts (tree_at t is)) = length (inPorts' (iNodeOf (tree_at t is)))"
  using assms
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto 4 4 elim!: it_paths_RNodeE  dest: list_all2_lengthD list_all2_nthD2)

lemma iNodeOf_outPorts:
  "iwf fc t ent \<Longrightarrow> is \<in> it_paths t \<Longrightarrow> outPorts (iNodeOf (tree_at t is)) = {||} \<Longrightarrow> False"
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto 4 4 elim!: it_paths_RNodeE  dest: list_all2_lengthD list_all2_nthD2)

lemma iNodeOf_tree_at:
  "iwf fc t ent \<Longrightarrow> is \<in> it_paths t \<Longrightarrow> iNodeOf (tree_at t is) \<in> sset nodes"
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto 4 4 elim!: it_paths_RNodeE  dest: list_all2_lengthD list_all2_nthD2)

lemma iwf_outPort: 
  assumes "iwf fc t ent"
  assumes "is \<in> it_paths t"
  shows "Reg (iOutPort (tree_at t is)) |\<in>| outPorts (iNodeOf (tree_at t is))"
  using assms
  by (induction arbitrary: "is" rule: iwf.induct)
     (auto 4 4 elim!: it_paths_RNodeE  dest: list_all2_lengthD list_all2_nthD2)

inductive_set hyps_along for t "is" where
 "prefix (is'@[i]) is \<Longrightarrow>
  i < length (inPorts' (iNodeOf (tree_at t is'))) \<Longrightarrow>
  hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<Longrightarrow>
  subst (iSubst (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)) \<in> hyps_along t is"

lemma hyps_along_Nil[simp]: "hyps_along t [] = {}"
  by (auto simp add: hyps_along.simps)

lemma prefix_app_Cons_elim:
  assumes "prefix (xs@[y]) (z#zs)"
  obtains "xs = []" and "y = z"
   | xs' where "xs = z#xs'" and "prefix (xs'@[y]) zs"
using assms by (cases xs) auto

lemma hyps_along_Cons:
  assumes "iwf fc t ent"
  assumes "i#is \<in> it_paths t"
  shows "hyps_along t (i#is) =
    (\<lambda>h. subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))) ` fset (hyps_for (iNodeOf t) (inPorts' (iNodeOf t) ! i))
    \<union> hyps_along (iAnts t ! i) is" (is "?S1 = ?S2 \<union> ?S3")
proof-
  from assms
  have "i < length (iAnts t)" and "is \<in> it_paths (iAnts t ! i)" 
    by (auto elim: it_paths_ConsE)
  let "?t'" = "iAnts t ! i"

  show ?thesis
  proof (rule; rule)
    fix x
    assume "x \<in> hyps_along t (i # is)"
    then obtain is' i' h where
      "prefix (is'@[i']) (i#is)"
      and "i' < length (inPorts' (iNodeOf (tree_at t is')))"
      and "hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i')"
      and [simp]: "x = subst (iSubst (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))"
    by (auto elim!: hyps_along.cases)
    from this(1)
    show "x \<in> ?S2 \<union> ?S3"
    proof(cases rule: prefix_app_Cons_elim)
      assume "is' = []" and "i' = i"
      with \<open>hyps (iNodeOf (tree_at t is')) h = Some _\<close>
      have "x \<in> ?S2" by auto
      thus ?thesis..
    next
      fix is''
      assume [simp]: "is' = i # is''" and "prefix (is'' @ [i']) is"
      have "tree_at t is' = tree_at ?t' is''" by simp

      note \<open>prefix (is'' @ [i']) is\<close>
           \<open>i' < length (inPorts' (iNodeOf (tree_at t is')))\<close>
           \<open>hyps (iNodeOf (tree_at t is')) h = Some (inPorts' (iNodeOf (tree_at t is')) ! i')\<close>
      from this[unfolded \<open>tree_at t is' = tree_at ?t' is''\<close>]
      have "subst (iSubst (tree_at (iAnts t ! i) is'')) (freshen (iAnnot (tree_at (iAnts t ! i) is'')) (labelsOut (iNodeOf (tree_at (iAnts t ! i) is'')) h))
          \<in> hyps_along (iAnts t ! i) is" by (rule hyps_along.intros)
      hence "x \<in> ?S3" by simp
      thus ?thesis..
    qed
  next
    fix x
    assume "x \<in> ?S2 \<union> ?S3"
    thus "x \<in> ?S1"
    proof
      have "prefix ([]@[i]) (i#is)" by simp
      moreover
      from \<open>iwf _ t _\<close>
      have "length (iAnts t) \<le> length (inPorts' (iNodeOf (tree_at t []))) "
        by cases (auto dest: list_all2_lengthD)
      with \<open>i < _\<close>
      have "i < length (inPorts' (iNodeOf (tree_at t [])))" by simp
      moreover
      assume "x \<in> ?S2"
      then obtain h where "h |\<in>| hyps_for (iNodeOf t) (inPorts' (iNodeOf t) ! i)"
        and [simp]: "x = subst (iSubst t) (freshen (iAnnot t) (labelsOut (iNodeOf t) h))" by auto
      from this(1)
      have "hyps (iNodeOf (tree_at t [])) h = Some (inPorts' (iNodeOf (tree_at t [])) ! i)" by simp
      ultimately
      have "subst (iSubst (tree_at t [])) (freshen (iAnnot (tree_at t [])) (labelsOut (iNodeOf (tree_at t [])) h)) \<in> hyps_along t (i # is)"
        by (rule hyps_along.intros)
      thus "x \<in> hyps_along t (i # is)" by simp
    next
      assume "x \<in> ?S3"
      thus "x \<in> ?S1"
        apply (auto simp add: hyps_along.simps)
        apply (rule_tac x = "i#is'" in exI)
        apply auto
        done
    qed
  qed
qed

lemma iwf_hyps_exist:
  assumes "iwf lc it ent"
  assumes "is \<in> it_paths it"
  assumes "tree_at it is = (HNode i s ants')"
  assumes "fst ent |\<subseteq>| ass_forms"
  shows "subst s (freshen i anyP) \<in> hyps_along it is"
proof-
  from assms(1,2,3)
  have "subst s (freshen i anyP) \<in> hyps_along it is 
     \<or> subst s (freshen i anyP) |\<in>| fst ent
       \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
  proof(induction arbitrary: "is" rule: iwf.induct)
    case (iwf n p  s' a' \<Gamma> ants c "is")

    have "iwf lc (INode n p a' s' ants) (\<Gamma> \<turnstile> c)"
      using iwf(1,2,3,4,5)
      by (auto intro!: iwf.intros elim!: list_all2_mono)

    show ?case
    proof(cases "is")
      case Nil
      with \<open>tree_at (INode n p a' s' ants) is = HNode i s ants'\<close>
      show ?thesis by auto
    next
      case (Cons i' "is'")
      with \<open>is \<in> it_paths (INode n p a' s' ants)\<close>
      have "i' < length ants" and "is' \<in> it_paths (ants ! i')"
        by (auto elim: it_paths_ConsE)

      let ?\<Gamma>' = "(\<lambda>h. subst s' (freshen a' (labelsOut n h))) |`| hyps_for n (inPorts' n ! i')"

      from \<open>tree_at (INode n p a' s' ants) is = HNode i s ants'\<close>
      have "tree_at (ants ! i') is' = HNode i s ants'" using Cons by simp

      from  iwf.IH \<open>i' < length ants\<close>  \<open>is' \<in> it_paths (ants ! i')\<close> this
      have  "subst s (freshen i anyP) \<in> hyps_along (ants ! i') is'
        \<or> subst s (freshen i anyP) |\<in>| ?\<Gamma>' |\<union>| \<Gamma> \<and> subst s (freshen i anyP) |\<notin>| ass_forms"
        by (auto dest: list_all2_nthD2)
      moreover
      from  \<open>is \<in> it_paths (INode n p a' s' ants)\<close>
      have "hyps_along (INode n p a' s' ants) is = fset ?\<Gamma>' \<union> hyps_along (ants ! i') is'"
        using \<open>is = _\<close>
        by (simp add: hyps_along_Cons[OF \<open>iwf lc (INode n p a' s' ants) (\<Gamma> \<turnstile> c)\<close>])
      ultimately
      show ?thesis by auto
    qed
  next
    case (iwfH c  \<Gamma> s' i' "is")
    hence [simp]: "is = []" "i' = i" "s' = s" by simp_all
    from \<open>c = subst s' (freshen i' anyP)\<close> \<open>c |\<in>| \<Gamma>\<close> \<open>c |\<notin>| ass_forms\<close>
    show ?case by simp
  qed
  with assms(4)
  show ?thesis by blast
qed

definition hyp_port_for' :: "('form, 'rule, 'subst, 'var) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat list \<times> nat \<times> ('form, 'var) out_port" where
  "hyp_port_for' t is f = (SOME x.
   (case x of (is', i, h) \<Rightarrow> 
      prefix (is' @ [i]) is \<and>
      i < length (inPorts' (iNodeOf (tree_at t is'))) \<and>
      hyps (iNodeOf (tree_at t is')) h =  Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h))
   ))"

lemma hyp_port_for_spec':
  assumes "f \<in> hyps_along t is"
  shows "(case hyp_port_for' t is f of (is', i, h) \<Rightarrow> 
      prefix (is' @ [i]) is \<and>
      i < length (inPorts' (iNodeOf (tree_at t is'))) \<and>
      hyps (iNodeOf (tree_at t is')) h =  Some (inPorts' (iNodeOf (tree_at t is')) ! i) \<and>
      f = subst (iSubst  (tree_at t is')) (freshen (iAnnot (tree_at t is')) (labelsOut (iNodeOf (tree_at t is')) h)))"
using assms unfolding hyps_along.simps hyp_port_for'_def by -(rule someI_ex, blast)

definition hyp_port_path_for :: "('form, 'rule, 'subst, 'var) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat list"
  where "hyp_port_path_for t is f = fst (hyp_port_for' t is f)"
definition hyp_port_i_for ::  "('form, 'rule, 'subst, 'var) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> nat"
  where "hyp_port_i_for t is f = fst (snd (hyp_port_for' t is f))"
definition hyp_port_h_for :: "('form, 'rule, 'subst, 'var) itree \<Rightarrow> nat list \<Rightarrow> 'form \<Rightarrow> ('form, 'var) out_port"
  where "hyp_port_h_for t is f = snd (snd (hyp_port_for' t is f))"

lemma hyp_port_prefix:
  assumes "f \<in> hyps_along t is"
  shows "prefix (hyp_port_path_for t is f@[hyp_port_i_for t is f]) is"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def by auto

lemma hyp_port_strict_prefix:
  assumes "f \<in> hyps_along t is"
  shows "strict_prefix (hyp_port_path_for t is f) is"
using hyp_port_prefix[OF assms] by (simp add: strict_prefixI' prefix_order.dual_order.strict_trans1)

lemma hyp_port_it_paths:
  assumes "is \<in> it_paths t"
  assumes "f \<in> hyps_along t is"
  shows "hyp_port_path_for t is f \<in> it_paths t"
using assms by (rule it_paths_strict_prefix[OF _ hyp_port_strict_prefix] )


lemma hyp_port_hyps:
  assumes "f \<in> hyps_along t is"
  shows "hyps (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f) = Some (inPorts' (iNodeOf (tree_at t (hyp_port_path_for t is f))) ! hyp_port_i_for t is f)"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto

lemma hyp_port_outPort:
  assumes "f \<in> hyps_along t is"
  shows "(hyp_port_h_for t is f) |\<in>| outPorts (iNodeOf (tree_at t (hyp_port_path_for t is f)))"
using hyps_correct[OF hyp_port_hyps[OF assms]]..

lemma hyp_port_eq:
  assumes "f \<in> hyps_along t is"
  shows "f = subst (iSubst (tree_at t (hyp_port_path_for t is f))) (freshen (iAnnot (tree_at t (hyp_port_path_for t is f))) (labelsOut (iNodeOf (tree_at t (hyp_port_path_for t is f))) (hyp_port_h_for t is f)))"
using hyp_port_for_spec'[OF assms] unfolding hyp_port_path_for_def hyp_port_i_for_def hyp_port_h_for_def by auto


definition isidx :: "nat list \<Rightarrow> nat" where "isidx xs = to_nat (Some xs)"
definition v_away :: "nat" where "v_away = to_nat (None :: nat list option)"
lemma isidx_inj[simp]: "isidx xs = isidx ys \<longleftrightarrow> xs = ys"
  unfolding isidx_def by simp
lemma isidx_v_away[simp]: "isidx xs \<noteq> v_away"
  unfolding isidx_def v_away_def by simp


definition mapWithIndex where "mapWithIndex f xs = map (\<lambda> (i,t) . f i t) (List.enumerate 0 xs)"
lemma mapWithIndex_cong [fundef_cong]:
  "xs = ys \<Longrightarrow> (\<And>x i. x \<in> set ys \<Longrightarrow> f i x = g i x) \<Longrightarrow> mapWithIndex f xs = mapWithIndex g ys"
unfolding mapWithIndex_def by (auto simp add: in_set_enumerate_eq)

lemma mapWithIndex_Nil[simp]: "mapWithIndex f [] = []"
  unfolding mapWithIndex_def by simp

lemma length_mapWithIndex[simp]: "length (mapWithIndex f xs) = length xs"
  unfolding mapWithIndex_def by simp

lemma nth_mapWithIndex[simp]: "i < length xs \<Longrightarrow> mapWithIndex f xs ! i = f i (xs ! i)"
  unfolding mapWithIndex_def by (auto simp add: nth_enumerate_eq)

lemma list_all2_mapWithIndex2E:
  assumes "list_all2 P as bs"
  assumes "\<And> i a b . i < length bs \<Longrightarrow> P a b \<Longrightarrow> Q a (f i b)"
  shows "list_all2 Q as (mapWithIndex f bs)"
using assms(1)
by (auto simp add: list_all2_conv_all_nth mapWithIndex_def nth_enumerate_eq intro: assms(2) split: prod.split)

text \<open>The globalize function, which renames all local constants so that they cannot clash with 
local constants occurring anywhere else in the tree.\<close>


fun globalize_node :: "nat list \<Rightarrow> ('var \<Rightarrow> 'var) \<Rightarrow> ('form,'rule,'subst,'var) itnode \<Rightarrow>  ('form,'rule,'subst,'var) itnode"  where
  "globalize_node is f (I n p i s) =  I n p (isidx is) (subst_renameLCs f s)"
  | "globalize_node is f (H i s) = H (isidx is) (subst_renameLCs f s)"

fun globalize :: "nat list \<Rightarrow> ('var \<Rightarrow> 'var) \<Rightarrow> ('form,'rule,'subst,'var) itree \<Rightarrow> ('form,'rule,'subst,'var) itree" where
  "globalize is f (RNode r ants) = RNode 
    (globalize_node is f r)
    (mapWithIndex (\<lambda> i' t.
      globalize (is@[i'])
                (rerename (a_fresh (inPorts' (iNodeOf (RNode r ants)) ! i'))
                          (iAnnot (RNode r ants)) (isidx is) f)
                t
      ) ants)"

lemma iAnnot'_globalize_node[simp]: "iAnnot' (globalize_node is f n) = isidx is"
  by (cases n) auto

lemma iAnnot_globalize:
  assumes "is' \<in> it_paths (globalize is f t)"
  shows  "iAnnot (tree_at (globalize is f t) is') = isidx (is@is')"
  using assms
  by (induction t arbitrary: f "is" is') (auto elim!: it_paths_RNodeE)

lemma all_local_consts_listed':
  assumes "n \<in> sset nodes"
  assumes "p |\<in>| inPorts n"
  shows "lconsts (a_conc p) \<union> (\<Union>(lconsts ` fset (a_hyps p))) \<subseteq> a_fresh p "
  using assms
  by (auto simp add: nodes_def stream.set_map lconsts_anyP closed_no_lconsts conclusions_closed fmember.rep_eq f_antecedent_def dest!: all_local_consts_listed)

lemma no_local_consts_in_consequences':
  "n \<in> sset nodes \<Longrightarrow> Reg p |\<in>| outPorts n \<Longrightarrow>  lconsts p = {}"
  using no_local_consts_in_consequences
  by (auto simp add: nodes_def lconsts_anyP closed_no_lconsts assumptions_closed stream.set_map f_consequent_def)

lemma iwf_globalize:
  assumes "local_iwf t (\<Gamma> \<turnstile> c)"
  shows "plain_iwf (globalize is f t) (renameLCs f |`| \<Gamma> \<turnstile> renameLCs f c)"
using assms
proof (induction t "\<Gamma> \<turnstile> c" arbitrary: "is" f \<Gamma> c rule: iwf.induct)
  case (iwf n p s i \<Gamma> ants c "is" f)

  note \<open>n \<in> sset nodes\<close>
  moreover
  note \<open>Reg p |\<in>| outPorts n\<close>
  moreover
  { fix i' 
    let ?V = "a_fresh (inPorts' n ! i')"
    let ?f' = "rerename ?V i (isidx is) f"
    let ?t = "globalize (is @ [i']) ?f' (ants ! i')"
    let ?ip = "inPorts' n ! i'"
    let ?\<Gamma>' = "(\<lambda>h. subst (subst_renameLCs f s) (freshen (isidx is) (labelsOut n h))) |`| hyps_for n ?ip"
    let ?c' = "subst (subst_renameLCs f s) (freshen (isidx is) (labelsIn n ?ip))"

    assume "i' < length (inPorts' n)"
    hence "(inPorts' n ! i') |\<in>| inPorts n" by (simp add: inPorts_fset_of)

    from \<open>i' < length (inPorts' n)\<close>
    have subset_V: "?V \<subseteq> all_local_vars n"
      unfolding all_local_vars_def
      by (auto simp add: inPorts_fset_of set_conv_nth)

    from \<open>local_fresh_check n i s (\<Gamma> \<turnstile> c)\<close> 
    have "freshenLC i ` all_local_vars n \<inter> subst_lconsts s = {}" 
      by (rule local_fresh_check.cases) simp
    hence "freshenLC i ` ?V \<inter> subst_lconsts s = {}" 
      using subset_V  by auto
    hence rerename_subst: "subst_renameLCs ?f' s = subst_renameLCs f s"
      by (rule rerename_subst_noop)

    from all_local_consts_listed'[OF \<open> n \<in> sset nodes\<close> \<open>(inPorts' n ! i') |\<in>| inPorts n\<close>]
    have subset_conc: "lconsts (a_conc (inPorts' n ! i')) \<subseteq> ?V"
      and subset_hyp': "\<And> hyp . hyp |\<in>| a_hyps (inPorts' n ! i') \<Longrightarrow> lconsts hyp \<subseteq> ?V"
      by (auto simp add: fmember.rep_eq)
      
    from List.list_all2_nthD[OF \<open>list_all2 _ _ _\<close> \<open>i' < length (inPorts' n)\<close>,simplified]
    have "plain_iwf ?t
           (renameLCs ?f' |`| ((\<lambda>h. subst s (freshen i (labelsOut n h))) |`| hyps_for n ?ip |\<union>|  \<Gamma>) \<turnstile>
            renameLCs ?f' (subst s (freshen i (a_conc ?ip))))"
         by simp
    also have "renameLCs ?f' |`| ((\<lambda>h. subst s (freshen i (labelsOut n h))) |`| hyps_for n ?ip |\<union>|  \<Gamma>)
      = (\<lambda>x. subst (subst_renameLCs ?f' s) (renameLCs ?f' (freshen i (labelsOut n x)))) |`|  hyps_for n ?ip |\<union>| renameLCs ?f' |`| \<Gamma>"
     by (simp add: fimage_fimage fimage_funion comp_def rename_subst)
    also have "renameLCs ?f' |`| \<Gamma> =  renameLCs f |`| \<Gamma>"
    proof(rule fimage_cong[OF refl])
      fix x
      assume "x |\<in>| \<Gamma>"
      with \<open>local_fresh_check n i s (\<Gamma> \<turnstile> c)\<close>
      have "freshenLC i ` all_local_vars n \<inter> lconsts x = {}" 
        by (elim local_fresh_check.cases) simp
      hence "freshenLC i ` ?V \<inter> lconsts x = {}" 
        using subset_V  by auto
      thus "renameLCs ?f' x = renameLCs f x"
        by (rule rerename_rename_noop)
    qed
    also have "(\<lambda>x. subst (subst_renameLCs ?f' s) (renameLCs ?f' (freshen i (labelsOut n x)))) |`|  hyps_for n ?ip = ?\<Gamma>'"
    proof(rule fimage_cong[OF refl])
      fix hyp
      assume "hyp |\<in>| hyps_for n (inPorts' n ! i')"
      hence "labelsOut n hyp |\<in>| a_hyps (inPorts' n ! i')"
        apply (cases hyp)
        apply (solves simp)
        apply (cases n)
        apply (auto split: if_splits)
        done
      from subset_hyp'[OF this]
      have subset_hyp: "lconsts (labelsOut n hyp) \<subseteq> ?V".
      
      show "subst (subst_renameLCs ?f' s) (renameLCs ?f' (freshen i (labelsOut n hyp))) =
            subst (subst_renameLCs f s)  (freshen (isidx is) (labelsOut n hyp))"
        apply (simp add: freshen_def rename_rename  rerename_subst)
        apply (rule arg_cong[OF renameLCs_cong])
        apply (auto dest: subsetD[OF subset_hyp])
        done
    qed
    also have "renameLCs ?f' (subst s (freshen i (a_conc ?ip))) = subst (subst_renameLCs ?f' s) (renameLCs ?f' (freshen i (a_conc ?ip)))" by (simp add: rename_subst)
    also have "... = ?c'"
        apply (simp add: freshen_def rename_rename  rerename_subst)
        apply (rule arg_cong[OF renameLCs_cong])
        apply (auto dest: subsetD[OF subset_conc])
        done
    finally
    have "plain_iwf ?t (?\<Gamma>' |\<union>| renameLCs f |`| \<Gamma> \<turnstile> ?c')".
  }
  with list_all2_lengthD[OF \<open>list_all2 _ _ _\<close>]
  have "list_all2
     (\<lambda>ip t. plain_iwf t ((\<lambda>h. subst (subst_renameLCs f s)
       (freshen (isidx is) (labelsOut n h))) |`| hyps_for n ip |\<union>|  renameLCs f |`| \<Gamma> \<turnstile> subst (subst_renameLCs f s) (freshen (isidx is) (labelsIn n ip))))
     (inPorts' n)
     (mapWithIndex (\<lambda> i' t. globalize (is@[i']) (rerename (a_fresh (inPorts' n ! i')) i (isidx is) f) t) ants)"
   by (auto simp add: list_all2_conv_all_nth)
  moreover
  have "no_fresh_check n (isidx is) (subst_renameLCs f s) (renameLCs f |`| \<Gamma> \<turnstile> renameLCs f c)"..
  moreover
  from \<open>n \<in> sset nodes\<close> \<open>Reg p |\<in>| outPorts n\<close>
  have "lconsts p = {}" by (rule no_local_consts_in_consequences')
  with \<open>c = subst s (freshen i p)\<close>
  have "renameLCs f c = subst (subst_renameLCs f s) (freshen (isidx is) p)"
    by (simp add: rename_subst rename_closed freshen_closed)
  ultimately
  show ?case
    unfolding globalize.simps globalize_node.simps iNodeOf.simps iAnnot.simps itnode.sel rose_tree.sel  Let_def 
    by (rule iwf.intros(1))
next
  case (iwfH c \<Gamma> s i "is" f)
  from \<open>c |\<notin>| ass_forms\<close>
  have "renameLCs f c |\<notin>| ass_forms"
    using assumptions_closed closed_no_lconsts lconsts_renameLCs rename_closed by fastforce
  moreover
  from \<open>c |\<in>| \<Gamma>\<close>
  have "renameLCs f c |\<in>| renameLCs f |`| \<Gamma>"  by auto
  moreover
  from \<open>c = subst s (freshen i anyP)\<close>
  have "renameLCs f c = subst (subst_renameLCs f s)  (freshen (isidx is) anyP)"
    by (metis freshen_closed lconsts_anyP rename_closed rename_subst)
  ultimately 
  show "plain_iwf (globalize is f (HNode i s [])) (renameLCs f |`| \<Gamma> \<turnstile> renameLCs f c)" 
    unfolding globalize.simps globalize_node.simps  mapWithIndex_Nil  Let_def 
    by (rule iwf.intros(2))
qed

definition fresh_at where
  "fresh_at t xs =
   (case rev xs of [] \<Rightarrow> {}
                 | (i#is') \<Rightarrow> freshenLC (iAnnot (tree_at t (rev is'))) ` (a_fresh (inPorts' (iNodeOf (tree_at t (rev is'))) ! i)))"

lemma fresh_at_Nil[simp]:
  "fresh_at t [] = {}"
  unfolding fresh_at_def by simp

lemma fresh_at_snoc[simp]:
  "fresh_at t (is@[i]) = freshenLC (iAnnot (tree_at t is)) ` (a_fresh (inPorts' (iNodeOf (tree_at t is)) ! i))"
  unfolding fresh_at_def by simp

lemma fresh_at_def':
  "fresh_at t is =
   (if is = [] then {}
    else freshenLC (iAnnot (tree_at t (butlast is))) ` (a_fresh (inPorts' (iNodeOf (tree_at t (butlast is))) ! last is)))"
  unfolding fresh_at_def by (auto split: list.split)

lemma fresh_at_Cons[simp]:
  "fresh_at t (i#is) = (if is = [] then freshenLC (iAnnot t) ` (a_fresh (inPorts' (iNodeOf t) ! i)) else (let t' = iAnts t ! i in fresh_at t' is))"
  unfolding fresh_at_def'
  by (auto simp add: Let_def)

definition fresh_at_path where
  "fresh_at_path t is = \<Union>(fresh_at t ` set (prefixes is))"

lemma fresh_at_path_Nil[simp]:
  "fresh_at_path t [] = {}"
  unfolding fresh_at_path_def by simp

lemma fresh_at_path_Cons[simp]:
  "fresh_at_path t (i#is) = fresh_at t [i] \<union> fresh_at_path (iAnts t ! i) is"
  unfolding fresh_at_path_def
  by (fastforce split: if_splits)
  
lemma globalize_local_consts:
  assumes "is' \<in> it_paths (globalize is f t)"
  shows "subst_lconsts (iSubst (tree_at (globalize is f t) is')) \<subseteq>
    fresh_at_path (globalize is f t) is' \<union> range f"
  using assms
  apply (induction "is" f t  arbitrary: is' rule:globalize.induct)
  apply (rename_tac "is" f r ants is')
  apply (case_tac r)
   apply (auto simp add: subst_lconsts_subst_renameLCs  elim!: it_paths_RNodeE)
   apply (solves \<open>force dest!: subsetD[OF range_rerename]\<close>)
  apply (solves \<open>force dest!: subsetD[OF range_rerename]\<close>)
  done
  
lemma iwf_globalize':
  assumes "local_iwf t ent"
  assumes "\<And> x. x |\<in>| fst ent \<Longrightarrow> closed x"
  assumes "closed (snd ent)"
  shows "plain_iwf (globalize is (freshenLC v_away) t) ent"
using assms
proof(induction ent rule: prod.induct)
  case (Pair \<Gamma> c)
  have "plain_iwf (globalize is (freshenLC v_away) t) (renameLCs (freshenLC v_away) |`| \<Gamma> \<turnstile> renameLCs (freshenLC v_away) c)"
    by (rule iwf_globalize[OF Pair(1)])
  also
  from Pair(3) have "closed c" by simp
  hence "renameLCs (freshenLC v_away) c = c" by (simp add: closed_no_lconsts rename_closed)
  also
  from Pair(2)
  have "renameLCs (freshenLC v_away) |`| \<Gamma> = \<Gamma>"
    by (auto simp add: closed_no_lconsts rename_closed fmember.rep_eq image_iff)
  finally show ?case.
qed
end   

end
