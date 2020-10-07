(*  Title:    Irreducible.thy
    Author:   Max Wagner
*)

section \<open>Minimality under Irreducible Control Flow\<close>

txt \<open>Braun~et~al.~\cite{braun13cc} provide an extension to the original construction algorithm to ensure
minimality according to Cytron's definition even in the case of irreducible control flow. This extension
establishes the property of being \emph{redundant-scc-free}, i.e.\ the resulting graph $G$ contains no
subsets inducing a strongly connected subgraph $G'$ via \pf s such that $G'$ has less than two
$\phi$ arguments in $G\setminus G'$. In this section we will show that a graph with this property is Cytron-minimal.

Our formalization follows the proof sketch given in \cite{braun13cc}.
We first provide a formal proof of Lemma 1 from \cite{braun13cc} which states that every redundant set of \pf s contains at least one redundant SCC.
A redundant set of \pf s is a set $P$ of \pf s with $P \cup \{v\} \supseteq A$, where $A$ is the union over all \pf s arguments contained in $P$.
I.e.\ $P$ references at most one SSA value ($v$) outside $P$.
A redundant SCC is a redundant set that is strongly connected according to the \emph{is-argument} relation.

Next, we show that a CFG in SSA form without redundant sets of \pf s is Cytron-minimal.

Finally putting those results together, we conclude that the extension to Braun~et~al.'s algorithm always produces minimal SSA form.
\<close>

theory Irreducible
  imports Formal_SSA.Minimality
begin

context CFG_SSA_Transformed
begin


subsection \<open>Proof of Lemma 1 from Braun~et~al.\<close>

txt \<open>To preserve readability, we won't distinguish between graph nodes and the \pf s contained inside such a node.\<close>

txt \<open>The graph induced by the $\phi$ network contained in the vertex set @{term P}. Note that the edges
of this graph are not necessarily a subset of the edges of the input graph.\<close>
definition "induced_phi_graph g P \<equiv> {(\<phi>,\<phi>'). phiArg g \<phi> \<phi>'} \<inter> P \<times> P"

txt \<open>For the purposes of this section, we define a "redundant set" as a nonempty set of \pf s with
at most one $\phi$ argument outside itself. A redundant SCC is defined analogously. Note that since
any uses of values in a redundant set can be replaced by uses of its singular argument (without
modifying program semantics), the name is adequate.\<close>
definition "redundant_set g P \<equiv> P \<noteq> {} \<and> P \<subseteq> dom (phi g) \<and> (\<exists>v' \<in> allVars g. \<forall>\<phi> \<in> P. \<forall>\<phi>'. phiArg g \<phi> \<phi>' \<longrightarrow> \<phi>' \<in> P \<union> {v'})"
definition "redundant_scc g P scc \<equiv> redundant_set g scc \<and> is_scc (induced_phi_graph g P) scc"

txt \<open>We prove an important lemma via condensation graphs of $\phi$ networks, so the relevant definitions are introduced here.\<close>
definition "condensation_nodes g P \<equiv> scc_of (induced_phi_graph g P) ` P"
definition "condensation_edges g P \<equiv> ((\<lambda>(x,y). (scc_of (induced_phi_graph g P) x, scc_of (induced_phi_graph g P) y)) ` (induced_phi_graph g P)) - Id"


txt \<open>For a finite @{term P}, the condensation graph induced by @{term P} is finite and acyclic.\<close>

lemma condensation_finite: "finite (condensation_edges g P)"
txt \<open>The set of edges of the condensation graph, spanning at most all $\phi$ nodes and their arguments (both of which are finite sets), is finite itself.\<close>
proof -
  let ?phiEdges="{(a,b). phiArg g a b}"
  have "finite ?phiEdges"
  proof -
    let ?phiDomRan="(dom (phi g) \<times> \<Union> (set ` (ran (phi g))))"
    from phi_finite
    have "finite ?phiDomRan" by (simp add: imageE phi_finite map_dom_ran_finite)
    have "?phiEdges \<subseteq> ?phiDomRan"
     apply (rule subst[of "\<forall>a \<in> ?phiEdges. a \<in> ?phiDomRan"])
      apply (simp_all add: subset_eq[symmetric] phiArg_def)
     by (auto simp: ran_def)
    with \<open>finite ?phiDomRan\<close>
    show "finite ?phiEdges" by (rule Finite_Set.rev_finite_subset)
  qed
  hence "\<And>f. finite (f ` (?phiEdges \<inter> (P \<times> P)))" by auto
  thus "finite (condensation_edges g P)" unfolding condensation_edges_def induced_phi_graph_def by auto
qed


txt \<open>auxiliary lemmas for acyclicity\<close>

lemma condensation_nodes_edges: "(condensation_edges g P) \<subseteq> (condensation_nodes g P \<times> condensation_nodes g P)"
unfolding condensation_edges_def condensation_nodes_def induced_phi_graph_def
by auto


lemma condensation_edge_impl_path:
assumes "(a, b) \<in> (condensation_edges g P)"
assumes "(\<phi>\<^sub>a \<in> a)"
assumes "(\<phi>\<^sub>b \<in> b)"
shows "(\<phi>\<^sub>a, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*"
unfolding condensation_edges_def
proof -
  from assms(1)
  obtain x y where x_y_props:
    "(x, y) \<in> (induced_phi_graph g P)"
    "a = scc_of (induced_phi_graph g P) x"
    "b = scc_of (induced_phi_graph g P) y"
   unfolding condensation_edges_def by auto
  hence "x \<in> a" "y \<in> b" by auto

  txt \<open>All that's left is to combine these paths.\<close>
  with assms(2) x_y_props(2)
  have "(\<phi>\<^sub>a, x) \<in> (induced_phi_graph g P)\<^sup>*" by (meson is_scc_connected scc_of_is_scc)
  moreover with assms(3) x_y_props(3) \<open>y \<in> b\<close>
  have "(y, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*" by (meson is_scc_connected scc_of_is_scc)
  ultimately
  show "(\<phi>\<^sub>a, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*" using x_y_props(1)  by auto
qed


lemma path_in_condensation_impl_path:
assumes "(a, b) \<in> (condensation_edges g P)\<^sup>+"
assumes "(\<phi>\<^sub>a \<in> a)"
assumes "(\<phi>\<^sub>b \<in> b)"
shows "(\<phi>\<^sub>a, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*"
using assms
proof (induction arbitrary: \<phi>\<^sub>b rule:trancl_induct)
  fix y z \<phi>\<^sub>b
  assume "(y, z) \<in> condensation_edges g P"

  hence "is_scc (induced_phi_graph g P) y" unfolding condensation_edges_def by auto
  hence "\<exists>\<phi>\<^sub>y. \<phi>\<^sub>y \<in> y" using scc_non_empty' by auto
  then obtain \<phi>\<^sub>y where \<phi>\<^sub>y_in_y: "\<phi>\<^sub>y \<in> y" by auto

  assume \<phi>\<^sub>b_elem: "\<phi>\<^sub>b \<in> z"
  assume "\<And>\<phi>\<^sub>b. \<phi>\<^sub>a \<in> a \<Longrightarrow> \<phi>\<^sub>b \<in> y \<Longrightarrow> (\<phi>\<^sub>a, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*"
  with assms(2) \<phi>\<^sub>y_in_y
  have \<phi>\<^sub>a_to_\<phi>\<^sub>y: "(\<phi>\<^sub>a, \<phi>\<^sub>y) \<in> (induced_phi_graph g P)\<^sup>*" using condensation_edge_impl_path by auto

  from \<phi>\<^sub>b_elem \<phi>\<^sub>y_in_y \<open>(y, z) \<in> condensation_edges g P\<close>
  have "(\<phi>\<^sub>y, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*" using condensation_edge_impl_path by auto
  with \<phi>\<^sub>a_to_\<phi>\<^sub>y
  show "(\<phi>\<^sub>a, \<phi>\<^sub>b) \<in> (induced_phi_graph g P)\<^sup>*"  by auto
qed (auto intro:condensation_edge_impl_path)


lemma condensation_acyclic: "acyclic (condensation_edges g P)"
proof (rule acyclicI, rule allI, rule ccontr, simp)
  fix x
  txt \<open>Assume there is a cycle in the condensation graph.\<close>
  assume cyclic: "(x, x) \<in> (condensation_edges g P)\<^sup>+"
  have nonrefl: "(x, x) \<notin> (condensation_edges g P)" unfolding condensation_edges_def by auto
  txt \<open>Then there must be a second SCC \<open>b\<close> on this path.\<close>
  from this cyclic
  obtain b where b_on_path: "(x, b) \<in> (condensation_edges g P)" "(b, x) \<in> (condensation_edges g P)\<^sup>+"
   by (meson converse_tranclE)

  hence "x \<in> (condensation_nodes g P)" "b \<in> (condensation_nodes g P)" using condensation_nodes_edges by auto
  hence nodes_are_scc: "is_scc (induced_phi_graph g P) x" "is_scc (induced_phi_graph g P) b"
    using scc_of_is_scc unfolding induced_phi_graph_def condensation_nodes_def by auto

  txt \<open>However, the existence of this path means all nodes in @{term b} and @{term x} are mutually reachable.\<close>
  have "\<exists>\<phi>\<^sub>x. \<phi>\<^sub>x \<in> x" "\<exists>\<phi>\<^sub>b. \<phi>\<^sub>b \<in> b" using nodes_are_scc scc_non_empty' ex_in_conv by auto
  then obtain \<phi>\<^sub>x \<phi>\<^sub>b where \<phi>xb_elem: "\<phi>\<^sub>x \<in> x" "\<phi>\<^sub>b \<in> b" by metis
  with nodes_are_scc(1) b_on_path path_in_condensation_impl_path condensation_edge_impl_path \<phi>xb_elem(2)
  have "\<phi>\<^sub>b \<in> x"
   by - (rule is_scc_closed)
  txt \<open>This however means @{term x} and @{term b} must be the same SCC, which is a contradiction to the nonreflexivity of @{theory_text condensation_edges}.\<close>
  with nodes_are_scc \<phi>xb_elem
  have "x = b" using is_scc_unique[of "induced_phi_graph g P"] by simp
  hence "(x, x) \<in> (condensation_edges g P)" using b_on_path by simp
  with nonrefl
  show "False" by simp
qed


txt \<open>Since the condensation graph of a set is acyclic and finite, it must have a leaf.\<close>
lemma Ex_condensation_leaf:
assumes "P \<noteq> {}"
shows "\<exists>leaf. leaf \<in> (condensation_nodes g P) \<and> (\<forall> scc.(leaf, scc) \<notin> condensation_edges g P)"
proof -
  from assms obtain x where "x \<in> condensation_nodes g P" unfolding condensation_nodes_def by auto
  show ?thesis
  proof (rule wfE_min)
    from condensation_finite condensation_acyclic
    show "wf ((condensation_edges g P)\<inverse>)" by (rule finite_acyclic_wf_converse)
  next
    fix leaf
    assume leaf_node: "leaf \<in> condensation_nodes g P"
    moreover
    assume leaf_is_leaf: "scc \<notin> condensation_nodes g P" if "(scc, leaf) \<in> (condensation_edges g P)\<inverse>" for scc
    ultimately
    have "leaf \<in> condensation_nodes g P \<and> (\<forall>scc. (leaf, scc) \<notin> condensation_edges g P)" using condensation_nodes_edges by blast
    thus "\<exists>leaf. leaf \<in> condensation_nodes g P \<and> (\<forall>scc. (leaf, scc) \<notin> condensation_edges g P)" by blast
  qed fact
qed


lemma scc_in_P:
assumes "scc \<in> condensation_nodes g P"
shows "scc \<subseteq> P"
proof -
  have "scc \<subseteq> P" if y_props: "scc = scc_of (induced_phi_graph g P) n" "n \<in> P" for n
  proof -
    from y_props
    show "scc \<subseteq> P"
    proof (clarsimp simp:y_props(1); case_tac "n = x")
      fix x
      assume different: "n \<noteq> x"
      assume "x \<in> scc_of (induced_phi_graph g P) n"
      hence "(n, x) \<in> (induced_phi_graph g P)\<^sup>*" by (metis is_scc_connected scc_of_is_scc node_in_scc_of_node)
      with different
      have "(n, x) \<in> (induced_phi_graph g P)\<^sup>+" by (metis rtranclD)
      then obtain z where step: "(z, x) \<in> (induced_phi_graph g P)" by (meson tranclE)
      from step
      show "x \<in> P" unfolding induced_phi_graph_def by auto
    qed simp
  qed
  from this assms(1) have "x \<in> P" if x_node: "x \<in> scc" for x
   apply -
   apply (rule imageE[of scc "scc_of (induced_phi_graph g P)"])
    using condensation_nodes_def x_node by blast+
  thus ?thesis by clarify
qed


lemma redundant_scc_phis:
assumes "redundant_set g P" "scc \<in> condensation_nodes g P" "x \<in> scc"
shows "phi g x \<noteq> None"
using assms by (meson domIff redundant_set_def scc_in_P subsetCE)


txt \<open>The following lemma will be important for the main proof of this section.
If @{term P} is redundant, a leaf in the condensation graph induced by P corresponds to a strongly connected set
with at most one argument, thus a redundant strongly connected set exists.\<close>

txt \<open>Lemma 1. Every redundant set contains a redundant SCC.\<close>

lemma 1:
assumes "redundant_set g P"
shows "\<exists>scc \<subseteq> P. redundant_scc g P scc"
proof -
  from assms Ex_condensation_leaf[of P g]
  obtain leaf where leaf_props: "leaf \<in> (condensation_nodes g P)" "\<forall>scc. (leaf, scc) \<notin> condensation_edges g P"
   unfolding redundant_set_def by auto
  hence "is_scc (induced_phi_graph g P) leaf" unfolding condensation_nodes_def by auto
  moreover
  hence "leaf \<noteq> {}" by (rule scc_non_empty')
  moreover
  have "leaf \<subseteq> dom (phi g)"
    apply (subst subset_eq, rule ballI)
    using redundant_scc_phis leaf_props(1) assms(1) by auto
  moreover
  from assms
  obtain pred where pred_props: "pred \<in> allVars g" "\<forall>\<phi>\<in>P. \<forall>\<phi>'. phiArg g \<phi> \<phi>' \<longrightarrow> \<phi>' \<in> P \<union> {pred}" unfolding redundant_set_def by auto
  {
    txt \<open>Any argument of a \pf\ in the leaf SCC which is \emph{not} in the leaf SCC itself must be the unique argument of P\<close>
    fix \<phi> \<phi>'

    consider (in_P) "\<phi>' \<notin> leaf \<and> \<phi>' \<in> P" | (neither) "\<phi>' \<notin> leaf \<and> \<phi>' \<notin> P \<union> {pred}" | "\<phi>' \<notin> leaf \<and> \<phi>' \<in> {pred}" | "\<phi>' \<in> leaf" by auto
    hence "\<phi>' \<in> leaf \<union> {pred}" if "\<phi> \<in> leaf" and "phiArg g \<phi> \<phi>'"
    proof cases
      case in_P \<comment> \<open>In this case @{term leaf} wasn't really a leaf, a contradiction\<close>
      moreover
      from in_P that leaf_props(1) scc_in_P[of leaf g P]
      have "(\<phi>, \<phi>') \<in> induced_phi_graph g P" unfolding induced_phi_graph_def by auto
      ultimately
      have "(leaf, scc_of (induced_phi_graph g P) \<phi>') \<in> condensation_edges g P" unfolding condensation_edges_def
       using leaf_props(1) that \<open>is_scc (induced_phi_graph g P) leaf\<close>
       apply -
       apply clarsimp
       apply (rule conjI)
        prefer 2
        apply auto[1]
       unfolding condensation_nodes_def
       by (metis (no_types, lifting) is_scc_unique node_in_scc_of_node pair_imageI scc_of_is_scc)
      with leaf_props(2)
      show ?thesis by auto
    next
      case neither \<comment> \<open>In which case @{term P} itself wasn't redundant, a contradiction\<close>
      with that leaf_props pred_props
      have "\<not>redundant_set g P" unfolding redundant_set_def
        by (meson rev_subsetD scc_in_P)
      with assms
      show ?thesis by auto
    qed auto \<comment> \<open>the other cases are trivial\<close>
  }
  with pred_props(1)
  have "\<exists>v'\<in>allVars g. \<forall>\<phi>\<in>leaf. \<forall>\<phi>'. phiArg g \<phi> \<phi>' \<longrightarrow> \<phi>' \<in> leaf \<union> {v'}"  by auto
  ultimately
  have "redundant_scc g P leaf" unfolding redundant_scc_def redundant_set_def by auto
  thus ?thesis using leaf_props(1) scc_in_P by meson
qed

subsection \<open>Proof of Minimality\<close>

txt \<open>We inductively define the reachable-set of a \pf\ as all \pf s reachable from a given node via an
unbroken chain of $\phi$ argument edges to unnecessary \pf s.\<close>

inductive_set reachable :: "'g \<Rightarrow> 'val \<Rightarrow> 'val set"
  for g :: "'g" and \<phi> :: "'val"
  where refl: "unnecessaryPhi g \<phi> \<Longrightarrow> \<phi> \<in> reachable g \<phi>"
  | step: "\<phi>' \<in> reachable g \<phi> \<Longrightarrow> phiArg g \<phi>' \<phi>'' \<Longrightarrow> unnecessaryPhi g \<phi>'' \<Longrightarrow> \<phi>'' \<in> reachable g \<phi>"


lemma reachable_props:
  assumes "\<phi>' \<in> reachable g \<phi>"
  shows "(phiArg g)\<^sup>*\<^sup>* \<phi> \<phi>'" and "unnecessaryPhi g \<phi>'"
  using assms
  by (induction \<phi>' rule: reachable.induct) auto


txt \<open>We call the transitive arguments of a \pf\ not in its reachable-set the "true arguments" of this \pf.\<close>
definition [simp]: "trueArgs g \<phi> \<equiv> {\<phi>'. \<phi>' \<notin> reachable g \<phi>} \<inter> {\<phi>'. \<exists>\<phi>'' \<in> reachable g \<phi>. phiArg g \<phi>'' \<phi>'}"


lemma preds_finite: "finite (trueArgs g \<phi>)"
proof (rule ccontr)
  assume "infinite (trueArgs g \<phi>)"
  hence a: "infinite {\<phi>'. \<exists>\<phi>'' \<in> reachable g \<phi>. phiArg g \<phi>'' \<phi>'}" by auto
  have phiarg_set: "{\<phi>'. \<exists>\<phi>. phiArg g \<phi> \<phi>'} = \<Union> (set `{b. \<exists>a. phi g a = Some b})" unfolding phiArg_def by auto
  txt \<open>If the true arguments of a \pf\ are infinite in number, there must be an infinite number of \pf s\ldots\<close>
  have "infinite {\<phi>'. \<exists>\<phi>. phiArg g \<phi> \<phi>'}"
    by (rule infinite_super[of "{\<phi>'. \<exists>\<phi>'' \<in> reachable g \<phi>. phiArg g \<phi>'' \<phi>'}"])  (auto simp: a)
  with phiarg_set
  have "infinite (ran (phi g))" unfolding ran_def phiArg_def by clarsimp
  txt \<open>Which cannot be.\<close>
  thus False by (simp add:phi_finite map_dom_ran_finite)
qed


txt \<open>Any unnecessary $\phi$ with less than 2 true arguments induces with @{term "reachable g \<phi>"} a redundant set itself.\<close>

lemma few_preds_redundant:
assumes "card (trueArgs g \<phi>) < 2" "unnecessaryPhi g \<phi>"
shows "redundant_set g (reachable g \<phi>)"
unfolding redundant_set_def
proof (intro conjI)
  from assms
  show "reachable g \<phi> \<noteq> {}"
    using empty_iff reachable.intros(1) by auto
next
  from assms(2)
  show "reachable g \<phi> \<subseteq> dom (phi g)"
    by (metis domIff reachable.cases subsetI unnecessaryPhi_def)
next
  from assms(1)
  consider (single) "card (trueArgs g \<phi>) = 1" | (empty) "card (trueArgs g \<phi>) = 0" by force
  thus "\<exists>pred\<in>allVars g. \<forall>\<phi>'\<in>reachable g \<phi>. \<forall>\<phi>''. phiArg g \<phi>' \<phi>'' \<longrightarrow> \<phi>'' \<in> reachable g \<phi> \<union> {pred}"
  proof cases
    case single
    then obtain pred where pred_prop: "trueArgs g \<phi> = {pred}" using card_eq_1_singleton by blast
    hence "pred \<in> allVars g" by (auto intro: Int_Collect phiArg_in_allVars)
    moreover
    from pred_prop
    have "\<forall>\<phi>'\<in>reachable g \<phi>. \<forall>\<phi>''. phiArg g \<phi>' \<phi>'' \<longrightarrow> \<phi>'' \<in> reachable g \<phi> \<union> {pred}" by auto
    ultimately
    show ?thesis by auto
  next
    case empty
    from allDefs_in_allVars[of _ g "defNode g \<phi>"] assms
    have phi_var: "\<phi> \<in> allVars g" unfolding unnecessaryPhi_def phiDefs_def allDefs_def defNode_def phi_def trueArgs_def
      by (clarsimp simp: domIff phis_in_\<alpha>n)
    from empty assms(1)
    have no_preds: "trueArgs g \<phi> = {}"  by (subst card_0_eq[OF preds_finite, symmetric]) auto
    show ?thesis
    proof (rule bexI, rule ballI, rule allI, rule impI)
      fix \<phi>' \<phi>''
      assume phis_props: "\<phi>' \<in> reachable g \<phi>" "phiArg g \<phi>' \<phi>''"
      with no_preds
      have "\<phi>'' \<in> reachable g \<phi>"
      unfolding trueArgs_def
      proof -
        from phis_props
        have "\<phi>'' \<in> {\<phi>'. \<exists>\<phi>''\<in>reachable g \<phi>. phiArg g \<phi>'' \<phi>'}" by auto
        with phis_props no_preds
        show "\<phi>'' \<in> reachable g \<phi>" unfolding trueArgs_def by auto
      qed
      thus "\<phi>'' \<in> reachable g \<phi> \<union> {\<phi>}" by simp
    qed (auto simp: phi_var)
  qed
qed


lemma phiArg_trancl_same_var:
assumes "(phiArg g)\<^sup>+\<^sup>+ \<phi> n"
shows "var g \<phi> = var g n"
using assms
apply (induction rule: tranclp_induct)
  apply (rule phiArg_same_var[symmetric])
  apply simp
 using phiArg_same_var by auto


txt \<open>The following path extension lemma will be used a number of times in the inner induction of the
main proof. Basically, the idea is to extend a path ending in a $\phi$ argument to the corresponding \pf\ 
while preserving disjointness to a second path.\<close>

lemma phiArg_disjoint_paths_extend:
assumes "var g r = V" and "var g s = V" and "r \<in> allVars g" and "s \<in> allVars g"
and "V \<in> oldDefs g n" and "V \<in> oldDefs g m"
and "g \<turnstile> n-ns\<rightarrow>defNode g r" and "g \<turnstile> m-ms\<rightarrow>defNode g s"
and "set ns \<inter> set ms = {}"
and "phiArg g \<phi>\<^sub>r r"
obtains ns'
where "g \<turnstile> n-ns@ns'\<rightarrow>defNode g \<phi>\<^sub>r"
and "set (butlast (ns@ns')) \<inter> set ms = {}"
proof (cases "r = \<phi>\<^sub>r")
  case (True)
  txt \<open>If the node to extend the path to is already the endpoint, the lemma is trivial.\<close>
  with assms(7,8,9) in_set_butlastD
  have "g \<turnstile> n-ns@[]\<rightarrow>defNode g \<phi>\<^sub>r" "set (butlast (ns@[])) \<inter> set ms = {}"
    by simp_all fastforce
  with that show ?thesis .
next
  case False
  txt \<open>It suffices to obtain any path from r to @{term \<phi>\<^sub>r}.
     However, since we'll need the corresponding predecessor of @{term \<phi>\<^sub>r} later, we must do this as follows:\<close>
  from assms(10)
  have "\<phi>\<^sub>r \<in> allVars g" unfolding phiArg_def
    by (metis allDefs_in_allVars phiDefs_in_allDefs phi_def phi_phiDefs phis_in_\<alpha>n)
  with assms(10)
  obtain rs' pred\<^sub>\<phi>\<^sub>r where rs'_props: "g \<turnstile> defNode g r-rs'\<rightarrow> pred\<^sub>\<phi>\<^sub>r" "old.EntryPath g rs'" "r \<in> phiUses g pred\<^sub>\<phi>\<^sub>r" "pred\<^sub>\<phi>\<^sub>r \<in> set (old.predecessors g (defNode g \<phi>\<^sub>r))"
   by (rule phiArg_path_ex')

  define rs where "rs = rs'@[defNode g \<phi>\<^sub>r]"
  from rs'_props(2,1) old.EntryPath_distinct old.path2_hd
  have rs'_loopfree: "defNode g r \<notin> set (tl rs')"  by (simp add: Misc.distinct_hd_tl)

  from False assms have "defNode g \<phi>\<^sub>r \<noteq> defNode g r"
   apply -
   apply (rule phiArg_distinct_nodes)
     apply (auto intro:phiArg_in_allVars)[2]
   unfolding phiArg_def by (metis allDefs_in_allVars phiDefs_in_allDefs phi_def phi_phiDefs phis_in_\<alpha>n)

  from rs'_props
  have rs_props: "g \<turnstile> defNode g r-rs\<rightarrow> defNode g \<phi>\<^sub>r" "length rs > 1" "defNode g r \<notin> set (tl rs)"
     apply (subgoal_tac "defNode g r = hd rs'")
      prefer 2 using rs'_props(1)
     apply (rule old.path2_hd)
     using old.path2_snoc old.path2_def rs'_props(1) rs_def rs'_loopfree \<open>defNode g \<phi>\<^sub>r \<noteq> defNode g r\<close> by auto

  show thesis
  proof (cases "set (butlast rs) \<inter> set ms = {}")
    case inter_empty: True
    txt \<open>If the intersection of these is empty, @{term "tl rs"} is already the extension we're looking for\<close>
    show thesis
    proof (rule that)
      show "set (butlast (ns @ tl rs)) \<inter> set ms = {}"
      proof (rule ccontr, simp only: ex_in_conv[symmetric])
        assume "\<exists>x. x \<in> set (butlast (ns @ tl rs)) \<inter> set ms"
        then obtain x where x_props: "x \<in> set (butlast (ns @ tl rs))" "x \<in> set ms" by auto
        with rs_props(2)
        consider (in_ns) "x \<in> set ns" | (in_rs) "x \<in> set (butlast (tl rs))" by (metis Un_iff butlast_append in_set_butlastD set_append)
        thus False
         apply (cases)
          using x_props(2) assms(9)
          apply (simp add: disjoint_elem)
         by (metis x_props(2) inter_empty in_set_tlD List.butlast_tl disjoint_iff_not_equal)
      qed
    qed (auto intro:assms(7) rs_props(1) old.path2_app)
  next
    case inter_ex: False
    txt \<open>If the intersection is nonempty, there must be a first point of intersection @{term i}.\<close>
    from inter_ex assms(7,8) rs_props
    obtain i ri where ri_props: "g \<turnstile> defNode g r-ri\<rightarrow>i" "i \<in> set ms" "\<forall>n \<in> set (butlast ri). n \<notin> set ms" "prefix ri rs"
     apply -
     apply (rule old.path2_split_first_prop[of g "defNode g r" rs "defNode g \<phi>\<^sub>r", where P="\<lambda>m. m \<in> set ms"])
       apply blast
      apply (metis disjoint_iff_not_equal in_set_butlastD)
     by blast
    with assms(8) old.path2_prefix_ex
    obtain ms' where ms'_props: "g \<turnstile> m -ms'\<rightarrow> i" "prefix ms' ms" "i \<notin> set (butlast ms')" by blast

    txt \<open>We proceed by case distinction:
      \<^item> if @{prop "i = defNode g \<phi>\<^sub>r"}, the path @{term ri} is already the path extension we're looking for
      \<^item> Otherwise, the fact that @{term i} is on the path from $\phi$ argument to the $\phi$ itself leads to a contradiction.
        However, we still need to distinguish the cases of whether @{prop "m = i"}\<close>
    consider (ri_is_valid) "i = defNode g \<phi>\<^sub>r" | (m_i_same) "i \<noteq> defNode g \<phi>\<^sub>r" "m = i" | (m_i_differ) "i \<noteq> defNode g \<phi>\<^sub>r" "m \<noteq> i" by auto

    thus thesis
    proof (cases)
      case ri_is_valid
      txt \<open>@{term ri} is a valid path extension.\<close>
      with assms(7) ri_props(1)
      have "g \<turnstile> n -ns@(tl ri)\<rightarrow> defNode g \<phi>\<^sub>r" by auto

      moreover
      have "set (butlast (ns@(tl ri))) \<inter> set ms = {}"
      proof (rule ccontr)
        assume contr: "set (butlast (ns @ tl ri)) \<inter> set ms \<noteq> {}"
        from this
        obtain x where x_props: "x \<in> set (butlast (ns @ tl ri))" "x \<in> set ms" by auto
        with assms(9) have "x \<notin> set ns" by auto
        with x_props \<open>g \<turnstile> n-ns @ tl ri\<rightarrow>defNode g \<phi>\<^sub>r\<close> \<open>defNode g \<phi>\<^sub>r \<noteq> defNode g r\<close> assms(7)
        have "x \<in> set (butlast (tl ri))"
         by (metis Un_iff append_Nil2 butlast_append old.path2_last set_append)
        with x_props(2) ri_props(3)
        show "False" by (metis FormalSSA_Misc.in_set_tlD List.butlast_tl)
      qed
      ultimately
      show thesis by (rule that)
    next
      case m_i_same
      txt \<open>If @{prop "m = i"}, we have, with @{term m}, a variable definition on the path from a \pf\ to its argument.
          This constitutes a contradiction to the conventional property.\<close>
      note rs'_props(1) rs'_loopfree
      moreover have "r \<in> allDefs g (defNode g r)" by (simp add: assms(3))
      moreover from rs'_props(3) have "r \<in> allUses g pred\<^sub>\<phi>\<^sub>r" unfolding allUses_def by simp

      moreover
      from rs_props(1) m_i_same rs_def ri_props(1,2,4) \<open>defNode g \<phi>\<^sub>r \<noteq> defNode g r\<close> assms(7,9)
      have "m \<in> set (tl rs')"
       by (metis disjoint_elem hd_append in_hd_or_tl_conv in_prefix list.sel(1) old.path2_hd old.path2_last old.path2_last_in_ns prefix_snoc)

      moreover
      from assms(6) obtain def\<^sub>m where "def\<^sub>m \<in> allDefs g m" "var g def\<^sub>m = V" unfolding oldDefs_def using defs_in_allDefs by blast

      ultimately
      have "var g def\<^sub>m \<noteq> var g r" by - (rule conventional, simp_all)
      with \<open>var g def\<^sub>m = V\<close> assms(1)
      have "False" by simp
      thus ?thesis by simp

    next
      case m_i_differ
      txt \<open>If @{prop "m \<noteq> i"}, @{term i} constitutes a proper path convergence point.\<close>
      have "old.pathsConverge g m ms' n (ns @ tl ri) i"
      proof (rule old.pathsConvergeI)
        show "1 < length ms'" using m_i_differ ms'_props old.path2_nontriv by blast
      next
        show "1 < length (ns @ tl ri)"
        using ri_props old.path2_nontriv assms(9) by (metis assms(7) disjoint_elem old.path2_app old.path2_hd_in_ns)
      next
        show "set (butlast ms') \<inter> set (butlast (ns @ tl ri)) = {}"
        proof (rule ccontr)
          assume "set (butlast ms') \<inter> set (butlast (ns @ tl ri)) \<noteq> {}"
          then obtain i' where i'_props: "i' \<in> set (butlast ms')" "i' \<in> set (butlast (ns @ tl ri))" by auto
          with ms'_props(2)
          have i'_not_in_ms: "i' \<in> set (butlast ms)" by (metis in_set_butlast_appendI prefixE)

          with assms(9)
          show False
          proof (cases "i' \<notin> set ns")
            case True
            with i'_props(2)
            have "i' \<in> set (butlast (tl ri))"
             by (metis Un_iff butlast_append in_set_butlastD set_append)
            hence "i' \<in> set (butlast ri)" by (simp add:in_set_tlD List.butlast_tl)
            with i'_not_in_ms ri_props(3)
            show False by (auto dest:in_set_butlastD)
          qed (meson disjoint_elem in_set_butlastD)
        qed
      qed (auto intro: assms(7) ri_props(1) old.path2_app ms'_props(1))

      txt \<open>At this intersection of paths we can find a \pf.\<close>
      from this assms(6,5)
      have "necessaryPhi g V i" by (rule necessaryPhiI)

      txt \<open>Before we can conclude that there is indeed a $\phi$ at @{term i}, we have to prove a couple of technicalities\ldots\<close>
      moreover
      from m_i_differ ri_props(1,4) rs_def old.path2_last prefix_snoc
      have ri_rs'_prefix: "prefix ri rs'" by fastforce
      then obtain rs'_rest where rs'_rest_prop: "rs' = ri@rs'_rest" using prefixE by auto
      from old.path2_last[OF ri_props(1)] last_snoc[of _ i] obtain tmp where "ri = tmp@[i]"
       apply (subgoal_tac "ri \<noteq> []")
        prefer 2
        using ri_props(1) apply (simp add: old.path2_not_Nil)
       apply (rule_tac that)
       using append_butlast_last_id[symmetric] by auto 
      with rs'_rest_prop have rs'_rest_def: "rs' = tmp@i#rs'_rest" by auto
      with rs'_props(1) have "g \<turnstile> i -i#rs'_rest\<rightarrow> pred\<^sub>\<phi>\<^sub>r"
       by (simp add:old.path2_split)
      moreover
      note \<open>var g r = V\<close> [simp]
      from rs'_props(3)
      have "r \<in> allUses g pred\<^sub>\<phi>\<^sub>r" unfolding allUses_def by simp

      moreover
      from \<open>defNode g r \<notin> set (tl rs')\<close> rs'_rest_def
      have "defNode g r \<notin> set rs'_rest" by auto
      with \<open>g \<turnstile> i -i#rs'_rest\<rightarrow> pred\<^sub>\<phi>\<^sub>r\<close>
      have "\<And>x. x \<in> set rs'_rest \<Longrightarrow> r \<notin> allDefs g x"
       by (metis defNode_eq list.distinct(1) list.sel(3) list.set_cases old.path2_cases old.path2_in_\<alpha>n)

      moreover
      from assms(7,9) \<open>g \<turnstile> i -i#rs'_rest\<rightarrow> pred\<^sub>\<phi>\<^sub>r\<close> ri_props(2)
      have "r \<notin> defs g i"
       by (metis defNode_eq defs_in_allDefs disjoint_elem old.path2_hd_in_\<alpha>n old.path2_last_in_ns)
      ultimately

      txt \<open>The convergence property gives us that there is a $\phi$ in the last node fulfilling @{theory_text necessaryPhi}
          on a path to a use of @{term r} without a definition of @{term r}.
          Thus @{term i} bears a \pf\ for the value of @{term r}.\<close>

      have "\<exists>y. phis g (i, r) = Some y"
       by (rule convergence_prop [where g=g and n=i and v=r and ns="i#rs'_rest", simplified])
      moreover

      from \<open>g \<turnstile> n-ns\<rightarrow>defNode g r\<close> have "defNode g r \<in> set ns" by auto
      with \<open>set ns \<inter> set ms = {}\<close> \<open>i \<in> set ms\<close> have "i \<noteq> defNode g r" by auto
      moreover

      from ms'_props(1) have "i \<in> set (\<alpha>n g)" by auto
      moreover

      have "defNode g r \<in> set (\<alpha>n g)" by (simp add: assms(3))

      txt \<open>However, we now have two definitions of @{term r}: one in @{term i}, and one in @{term "defNode g r"}, which we know to be distinct.
          This is a contradiction to the @{theory_text allDefs_disjoint}-property.\<close>
      ultimately have False
        using allDefs_disjoint [where g=g and n=i and m="defNode g r"]
        unfolding allDefs_def phiDefs_def
        apply clarsimp
        apply (erule_tac c=r in equalityCE)
        using phi_def phis_phi by auto
      thus ?thesis by simp
    qed
  qed
qed


lemma reachable_same_var:
assumes "\<phi>' \<in> reachable g \<phi>"
shows "var g \<phi> = var g \<phi>'"
using assms by (metis Nitpick.rtranclp_unfold phiArg_trancl_same_var reachable_props(1))


lemma \<phi>_node_no_defs:
assumes "unnecessaryPhi g \<phi>" "\<phi> \<in> allVars g" "var g \<phi> \<in> oldDefs g n"
shows "defNode g \<phi> \<noteq> n"
using assms simpleDefs_phiDefs_var_disjoint defNode(1) not_None_eq phi_phiDefs
  unfolding unnecessaryPhi_def by auto


lemma defNode_differ_aux:
assumes "\<phi>\<^sub>s \<in> reachable g \<phi>" "\<phi> \<in> allVars g" "s \<in> allVars g" "\<phi>\<^sub>s \<noteq> s" "var g \<phi> = var g s"
shows "defNode g \<phi>\<^sub>s \<noteq> defNode g s" unfolding reachable_def
proof (rule ccontr)
  assume "\<not> defNode g \<phi>\<^sub>s \<noteq> defNode g s"
  hence eq: "defNode g \<phi>\<^sub>s = defNode g s" by simp
  from assms(1)
  have vars_eq: "var g \<phi> = var g \<phi>\<^sub>s"
    apply -
    apply (cases "\<phi> = \<phi>\<^sub>s")
    apply simp
    apply (rule phiArg_trancl_same_var)
    apply (drule reachable_props)
    unfolding reachable_def by (meson IntD1 mem_Collect_eq rtranclpD)
  have \<phi>\<^sub>s_in_allVars: "\<phi>\<^sub>s \<in> allVars g" unfolding reachable_def
  proof (cases "\<phi> = \<phi>\<^sub>s")
    case False
    with assms(1)
    obtain \<phi>' where "phiArg g \<phi>' \<phi>\<^sub>s"  by (metis rtranclp.cases reachable_props(1))
    thus "\<phi>\<^sub>s \<in> allVars g" by (rule phiArg_in_allVars)
  next
    case eq: True
    with assms(2)
    show "\<phi>\<^sub>s \<in> allVars g" by (subst eq[symmetric])
  qed

  from eq \<phi>\<^sub>s_in_allVars assms(3,4)
  have "var g \<phi>\<^sub>s \<noteq> var g s" by - (rule defNode_var_disjoint)
  with vars_eq assms(5)
  show False by auto
qed


txt \<open>Theorem 1. A graph which does not contain any redundant set is minimal according to Cytron et al.'s definition of minimality.\<close>

theorem no_redundant_set_minimal:
assumes no_redundant_set: "\<not>(\<exists>P. redundant_set g P)"
shows "cytronMinimal g"
proof (rule ccontr)
  assume "\<not>cytronMinimal g"
  txt \<open>Assume the graph is not Cytron-minimal. Thus there is a \pf\ which does not sit at the
      convergence point of multiple liveness intervals.\<close>
  then obtain \<phi> where \<phi>_props: "unnecessaryPhi g \<phi>" "\<phi> \<in> allVars g" "\<phi> \<in> reachable g \<phi>"
  using cytronMinimal_def unnecessaryPhi_def reachable_def unnecessaryPhi_def reachable.intros by auto

  txt \<open>We consider the reachable-set of @{term \<phi>}. If @{term \<phi>} has less than two true arguments, we
     know it to be a redundant set, a contradiction. Otherwise, we know there to be at least two
     paths from different definitions leading into the reachable-set of @{term \<phi>}.\<close>

  consider (nontrivial) "card (trueArgs g \<phi>) \<ge> 2" | (trivial) "card (trueArgs g \<phi>) < 2" using linorder_not_le by auto
  thus False
  proof cases
    case trivial
    txt \<open>If there are less than 2 true arguments of this set, the set is trivially redundant (see @{theory_text few_preds_redundant}).\<close>
    from this \<phi>_props(1)
    have "redundant_set g (reachable g \<phi>)" by (rule few_preds_redundant)
    with no_redundant_set
    show False by simp
  next
    case nontrivial
    txt \<open>If there are two or more necessary arguments, there must be disjoint paths from Defs to two of these \pf s.\<close>
    then obtain r s \<phi>\<^sub>r \<phi>\<^sub>s where assign_nodes_props:
      "r \<noteq> s" "\<phi>\<^sub>r \<in> reachable g \<phi>" "\<phi>\<^sub>s \<in> reachable g \<phi>"
      "\<not> unnecessaryPhi g r" "\<not> unnecessaryPhi g s"
      "r \<in> {n. (phiArg g)\<^sup>*\<^sup>* \<phi> n}" "s \<in> {n. (phiArg g)\<^sup>*\<^sup>* \<phi> n}"
      "phiArg g \<phi>\<^sub>r r" "phiArg g \<phi>\<^sub>s s"
     apply simp
     apply (rule set_take_two[OF nontrivial])
     apply simp
     by (meson reachable.intros(2) reachable_props(1) rtranclp_tranclp_tranclp tranclp.r_into_trancl tranclp_into_rtranclp)
    moreover from assign_nodes_props
    have \<phi>_r_s_uneq: "\<phi> \<noteq> r" "\<phi> \<noteq> s" using \<phi>_props by auto
    moreover
    from assign_nodes_props this
    have r_s_in_tranclp: "(phiArg g)\<^sup>+\<^sup>+ \<phi> r" "(phiArg g)\<^sup>+\<^sup>+ \<phi> s"
      by (meson mem_Collect_eq rtranclpD) (meson assign_nodes_props(7) \<phi>_r_s_uneq(2) mem_Collect_eq rtranclpD)
    from this
    obtain V where V_props: "var g r = V" "var g s = V" "var g \<phi> = V" by (metis phiArg_trancl_same_var)
    moreover
    from r_s_in_tranclp
    have r_s_allVars: "r \<in> allVars g" "s \<in> allVars g" by (metis phiArg_in_allVars tranclp.cases)+
    moreover
    from V_props defNode_var_disjoint r_s_allVars assign_nodes_props(1)
    have r_s_defNode_distinct: "defNode g r \<noteq> defNode g s" by auto
    ultimately
    obtain n ns m ms where r_s_path_props: "V \<in> oldDefs g n" "g \<turnstile> n-ns\<rightarrow>defNode g r" "V \<in> oldDefs g m" "g \<turnstile> m-ms\<rightarrow>defNode g s"
      "set ns \<inter> set ms = {}" by (auto intro: ununnecessaryPhis_disjoint_paths[of g r s])

    have n_m_distinct: "n \<noteq> m"
    proof (rule ccontr)
      assume n_m: "\<not> n \<noteq> m"
      with r_s_path_props(2) old.path2_hd_in_ns
      have "n \<in> set ns" by blast
      moreover
      from n_m r_s_path_props(4) old.path2_hd_in_ns
      have "n \<in> set ms" by blast
      ultimately
      show False using r_s_path_props(5) by auto
    qed

    txt \<open>These paths can be extended into paths reaching \pf s in our set.\<close>

    from V_props r_s_allVars r_s_path_props assign_nodes_props
    obtain rs where rs_props: "g \<turnstile> n -ns@rs\<rightarrow> defNode g \<phi>\<^sub>r" "set (butlast (ns@rs)) \<inter> set ms = {}"
    using phiArg_disjoint_paths_extend by blast

    txt \<open>(In fact, we can prove that @{prop "set (ns@rs) \<inter> set ms = {}"}, which we need for the next path extension.)\<close>
    have "defNode g \<phi>\<^sub>r \<notin> set ms"
    proof (rule ccontr)
      assume \<phi>\<^sub>r_in_ms: "\<not> defNode g \<phi>\<^sub>r \<notin> set ms"
      from this r_s_path_props(4)
      obtain ms' where ms'_props: "g \<turnstile> m -ms'\<rightarrow> defNode g \<phi>\<^sub>r" "prefix ms' ms" by -(rule old.path2_prefix_ex[of g m ms "defNode g s" "defNode g \<phi>\<^sub>r"], auto)

      have "old.pathsConverge g n (ns@rs) m ms' (defNode g \<phi>\<^sub>r)"
      proof (rule old.pathsConvergeI)
        show "set (butlast (ns @ rs)) \<inter> set (butlast ms') = {}"
        proof (rule ccontr)
          assume "set (butlast (ns @ rs)) \<inter> set (butlast ms') \<noteq> {}"
          then obtain c where c_props: "c \<in> set (butlast (ns@rs))" "c \<in> set (butlast ms')" by auto
          from this(2) ms'_props(2)
          have "c \<in> set ms" by (simp add: in_prefix in_set_butlastD)
          with c_props(1) rs_props(2)
          show False by auto
        qed
      next
        have m_n_\<phi>\<^sub>r_differ: "n \<noteq> defNode g \<phi>\<^sub>r" "m \<noteq> defNode g \<phi>\<^sub>r"
          using assign_nodes_props(2,3,4,5) V_props r_s_path_props \<phi>\<^sub>r_in_ms
          apply fastforce
         using V_props(1) \<phi>\<^sub>r_in_ms assign_nodes_props(8) old.path2_in_\<alpha>n phiArg_def phiArg_same_var r_s_path_props(3,4) simpleDefs_phiDefs_var_disjoint
         by auto
        with ms'_props(1)
        show "1 < length ms'" using old.path2_nontriv by simp
        from m_n_\<phi>\<^sub>r_differ rs_props(1)
        show "1 < length (ns@rs)" using old.path2_nontriv by blast
      qed (auto intro: rs_props set_mono_prefix ms'_props)
      with V_props r_s_path_props
      have "necessaryPhi' g \<phi>\<^sub>r" unfolding necessaryPhi_def using assign_nodes_props(8) phiArg_same_var by auto
      with reachable_props(2)[OF assign_nodes_props(2)]
      show False unfolding unnecessaryPhi_def by simp
    qed

    with rs_props
    have aux: "set ms \<inter> set (ns @ rs) = {}"
      by (metis disjoint_iff_not_equal not_in_butlast old.path2_last)

    have \<phi>\<^sub>r_V: "var g \<phi>\<^sub>r = V"
      using V_props(1) assign_nodes_props(8) phiArg_same_var by auto

    have \<phi>\<^sub>r_allVars: "\<phi>\<^sub>r \<in> allVars g"
      by (meson phiArg_def assign_nodes_props(8) allDefs_in_allVars old.path2_tl_in_\<alpha>n phiDefs_in_allDefs phi_phiDefs rs_props)

    from V_props(2) \<phi>\<^sub>r_V r_s_allVars(2) \<phi>\<^sub>r_allVars r_s_path_props(3) r_s_path_props(1)
             r_s_path_props(4) rs_props(1) aux assign_nodes_props(9)
    obtain ss where ss_props: "g \<turnstile> m -ms@ss\<rightarrow> defNode g \<phi>\<^sub>s" "set (butlast (ms@ss)) \<inter> set (butlast (ns@rs)) = {}"
     by (rule phiArg_disjoint_paths_extend) (metis disjoint_iff_not_equal in_set_butlastD)

    define p\<^sub>m where "p\<^sub>m = ms@ss"
    define p\<^sub>n where "p\<^sub>n = ns@rs"

    have ind_props: "g \<turnstile> m -p\<^sub>m\<rightarrow> defNode g \<phi>\<^sub>s" "g \<turnstile> n -p\<^sub>n\<rightarrow> defNode g \<phi>\<^sub>r" "set (butlast p\<^sub>m) \<inter> set (butlast p\<^sub>n) = {}"
    using rs_props(1) ss_props p\<^sub>m_def p\<^sub>n_def by auto

    txt \<open>The following case will occur twice in the induction, with swapped identifiers, so we're proving it outside.
    Basically, if the paths @{term p\<^sub>m} and @{term p\<^sub>n} intersect, the first such intersection point must be a \pf\ in @{term "reachable g \<phi>"},
    yielding the path convergence we seek.\<close>

    have path_crossing_yields_convergence:
      "\<exists>\<phi>\<^sub>z \<in> reachable g \<phi>. \<exists>ns ms. old.pathsConverge g n ns m ms (defNode g \<phi>\<^sub>z)"
      if "\<phi>\<^sub>r \<in> reachable g \<phi>" and "\<phi>\<^sub>s \<in> reachable g \<phi>" and "g \<turnstile> n -p\<^sub>n\<rightarrow> defNode g \<phi>\<^sub>r"
        and "g \<turnstile> m -p\<^sub>m\<rightarrow> defNode g \<phi>\<^sub>s" and "set (butlast p\<^sub>m) \<inter> set (butlast p\<^sub>n) = {}"
        and "set p\<^sub>m \<inter> set p\<^sub>n \<noteq> {}"
      for \<phi>\<^sub>r \<phi>\<^sub>s p\<^sub>m p\<^sub>n
    proof -
      from that(6) split_list_first_propE
      obtain p\<^sub>m1 n\<^sub>z p\<^sub>m2 where n\<^sub>z_props: "n\<^sub>z \<in> set p\<^sub>n" "p\<^sub>m = p\<^sub>m1 @ n\<^sub>z # p\<^sub>m2" "\<forall>n \<in> set p\<^sub>m1. n \<notin> set p\<^sub>n"
         by (auto intro: split_list_first_propE)

      with that(3,4)
      obtain p\<^sub>n' where p\<^sub>n'_props: "g \<turnstile> n-p\<^sub>n'\<rightarrow>n\<^sub>z" "g \<turnstile> m-p\<^sub>m1@[n\<^sub>z]\<rightarrow>n\<^sub>z" "prefix p\<^sub>n' p\<^sub>n" "n\<^sub>z \<notin> set (butlast p\<^sub>n')"
          by (meson old.path2_prefix_ex old.path2_split(1))

      from V_props(3) reachable_same_var[OF that(1)] reachable_same_var[OF that(2)]
      have phis_V: "var g \<phi>\<^sub>r = V" "var g \<phi>\<^sub>s = V" by simp_all
      from reachable_props(1) that(1,2) \<phi>_props(2) phiArg_in_allVars
      have phis_allVars: "\<phi>\<^sub>r \<in> allVars g" "\<phi>\<^sub>s \<in> allVars g" by (metis rtranclp.cases)+

      txt \<open>Various inequalities for proving paths aren't trivial.\<close>
      have "n \<noteq> defNode g \<phi>\<^sub>r" "m \<noteq> defNode g \<phi>\<^sub>r"
       using \<phi>_node_no_defs phis_V(1) phis_allVars(1) r_s_path_props(1,3) reachable_props(2) that(1) by blast+

      from \<phi>_node_no_defs reachable_props(2) that(2) r_s_path_props(1,3) phis_V(2) that phis_allVars
      have "m \<noteq> defNode g \<phi>\<^sub>s" "n \<noteq> defNode g \<phi>\<^sub>s" by blast+

      txt \<open>With this scenario, since @{prop "set (butlast p\<^sub>n) \<inter> set (butlast p\<^sub>m) = {}"}, one of the paths @{term p\<^sub>n} and
      @{term p\<^sub>m} must end somewhere within the other, however this means the \pf\ in that node must either be @{term \<phi>} or @{term \<phi>\<^sub>r}\<close>

      from assms n\<^sub>z_props
      consider (p\<^sub>n_ends_in_p\<^sub>m) "n\<^sub>z = defNode g \<phi>\<^sub>s" | (p\<^sub>m_ends_in_p\<^sub>n) "n\<^sub>z = defNode g \<phi>\<^sub>r"
      proof (cases "n\<^sub>z = last p\<^sub>n")
        case True
        with \<open>g \<turnstile> n -p\<^sub>n\<rightarrow> defNode g \<phi>\<^sub>r\<close>
        have "n\<^sub>z = defNode g \<phi>\<^sub>r" using old.path2_last by auto
        with that(2) show ?thesis.
      next
        case False
        from n\<^sub>z_props(2)
        have "n\<^sub>z \<in> set p\<^sub>m" by simp
        with False n\<^sub>z_props(1) \<open>set (butlast p\<^sub>m) \<inter> set (butlast p\<^sub>n) = {}\<close> \<open>g \<turnstile> m -p\<^sub>m\<rightarrow> defNode g \<phi>\<^sub>s\<close>
        have "n\<^sub>z = defNode g \<phi>\<^sub>s" by (metis disjoint_elem not_in_butlast old.path2_last)
        with that(1) show ?thesis.
      qed

      thus "\<exists>\<phi>\<^sub>z \<in> reachable g \<phi>. \<exists>ns ms. old.pathsConverge g n ns m ms (defNode g \<phi>\<^sub>z)"
      proof (cases)
        case p\<^sub>n_ends_in_p\<^sub>m
        have "old.pathsConverge g n p\<^sub>n' m p\<^sub>m (defNode g \<phi>\<^sub>s)"
        proof (rule old.pathsConvergeI)
          from p\<^sub>n_ends_in_p\<^sub>m p\<^sub>n'_props(1) show "g \<turnstile> n-p\<^sub>n'\<rightarrow>defNode g \<phi>\<^sub>s" by simp
          from \<open>n \<noteq> defNode g \<phi>\<^sub>s\<close> p\<^sub>n_ends_in_p\<^sub>m p\<^sub>n'_props(1) old.path2_nontriv show "1 < length p\<^sub>n'" by auto
          from that(4) show "g \<turnstile> m -p\<^sub>m\<rightarrow> defNode g \<phi>\<^sub>s".
          with \<open>m \<noteq> defNode g \<phi>\<^sub>s\<close> old.path2_nontriv show "1 < length p\<^sub>m" by simp
          from that p\<^sub>n'_props(3) show "set (butlast p\<^sub>n') \<inter> set (butlast p\<^sub>m) = {}"
           by (meson butlast_prefix disjointI disjoint_elem in_prefix)
        qed
        with that(1,2,3) show ?thesis by (auto intro:reachable.intros(2))
      next
        case p\<^sub>m_ends_in_p\<^sub>n
        have "old.pathsConverge g n p\<^sub>n' m (p\<^sub>m1@[n\<^sub>z]) (defNode g \<phi>\<^sub>r)"
        proof (rule old.pathsConvergeI)
          from p\<^sub>m_ends_in_p\<^sub>n  p\<^sub>n'_props(1,2) show "g \<turnstile> n-p\<^sub>n'\<rightarrow>defNode g \<phi>\<^sub>r" "g \<turnstile> m-p\<^sub>m1 @ [n\<^sub>z]\<rightarrow>defNode g \<phi>\<^sub>r" by simp_all
          with \<open>n \<noteq> defNode g \<phi>\<^sub>r\<close> \<open>m \<noteq> defNode g \<phi>\<^sub>r\<close> show "1 < length p\<^sub>n'" "1 < length (p\<^sub>m1 @ [n\<^sub>z])"
           using old.path2_nontriv[of g m "p\<^sub>m1 @ [n\<^sub>z]"] old.path2_nontriv[of g n] by simp_all
          from n\<^sub>z_props p\<^sub>n'_props(3) show "set (butlast p\<^sub>n') \<inter> set (butlast (p\<^sub>m1 @ [n\<^sub>z])) = {}"
           using butlast_snoc disjointI in_prefix in_set_butlastD by fastforce
        qed
        with that(1) show ?thesis by (auto intro:reachable.intros)
      qed
    qed


    txt \<open>Since the reachable-set was built starting at a single $\phi$, these paths must at some
         point converge \emph{within} @{term "reachable g \<phi>"}.\<close>
    from assign_nodes_props(3,2) ind_props V_props(3) \<phi>\<^sub>r_V \<phi>\<^sub>r_allVars
    have "\<exists>\<phi>\<^sub>z \<in> reachable g \<phi>. \<exists>ns ms. old.pathsConverge g n ns m ms (defNode g \<phi>\<^sub>z)"
    proof (induction arbitrary: p\<^sub>m p\<^sub>n rule: reachable.induct)
      case refl
      txt \<open>In the induction basis, we know that @{prop "\<phi> = \<phi>\<^sub>s"}, and a path to @{term \<phi>\<^sub>r} must be obtained
          -- for this we need a second induction.\<close>
      from refl.prems refl.hyps show ?case
      proof (induction arbitrary: p\<^sub>m p\<^sub>n rule: reachable.induct)
        case refl
        txt \<open>The first case, in which \<open>\<phi>\<^sub>r = \<phi>\<^sub>s = \<phi>\<close>, is trivial -- \<open>\<phi>\<close> suffices.\<close>
        have "old.pathsConverge g n p\<^sub>n m p\<^sub>m (defNode g \<phi>)"
        proof (rule old.pathsConvergeI)
          show "1 < length p\<^sub>n" "1 < length p\<^sub>m"
            using refl V_props simpleDefs_phiDefs_var_disjoint unfolding unnecessaryPhi_def
            by (metis domD domIff old.path2_hd_in_\<alpha>n old.path2_nontriv phi_phiDefs r_s_path_props(1) r_s_path_props(3))+
          show "g \<turnstile> n-p\<^sub>n\<rightarrow>defNode g \<phi>" "g \<turnstile> m-p\<^sub>m\<rightarrow>defNode g \<phi>" "set (butlast p\<^sub>n) \<inter> set (butlast p\<^sub>m) = {}"
          using refl by auto
        qed
        with \<open>\<phi> \<in> reachable g \<phi>\<close> show ?case by auto
      next
        case (step \<phi>' \<phi>\<^sub>r)
        txt \<open>In this case we have that @{prop "\<phi> = \<phi>\<^sub>s"} and need to acquire a path going to @{term \<phi>\<^sub>r},
            however with the aux.\ lemma we have, we still need that @{term p\<^sub>n} and @{term p\<^sub>m} are disjoint.\<close>
        thus ?case
        proof (cases "set p\<^sub>n \<inter> set p\<^sub>m = {}")
          case paths_cross: False
          with step reachable.intros
          show ?thesis using path_crossing_yields_convergence[of \<phi>\<^sub>r \<phi> p\<^sub>n p\<^sub>m] by (metis disjointI disjoint_elem)
        next
          case True
          txt \<open>If the paths are intersection-free, we can apply our path extension lemma to obtain the path needed.\<close>
          from step(9,8,10) \<open>\<phi> \<in> allVars g\<close> r_s_path_props(1,3) step(6,5) True step(2)
          obtain ns where "g \<turnstile> n -p\<^sub>n@ns\<rightarrow> defNode g \<phi>'" "set (butlast (p\<^sub>n@ns)) \<inter> set p\<^sub>m = {}" by (rule phiArg_disjoint_paths_extend)

          from this(2) have "set (butlast p\<^sub>m) \<inter> set (butlast (p\<^sub>n @ ns)) = {}"
            using in_set_butlastD by fastforce
          moreover
          from phiArg_same_var step.hyps(2) step.prems(5) have "var g \<phi>' = V"
            by auto
          moreover
          have "\<phi>' \<in> allVars g"
            by (metis \<phi>_props(2) phiArg_in_allVars reachable.cases step.hyps(1))
          ultimately
          show "\<exists>\<phi>\<^sub>z\<in>reachable g \<phi>. \<exists>ns ms. old.pathsConverge g n ns m ms (defNode g \<phi>\<^sub>z)"
            using step.prems(1) \<phi>_props V_props \<open>g \<turnstile> n -p\<^sub>n@ns\<rightarrow> defNode g \<phi>'\<close>
            by -(rule step.IH; blast)
        qed
      qed
    next
      case (step \<phi>' \<phi>\<^sub>s)
      txt \<open>With the induction basis handled, we can finally move on to the induction proper.\<close>

      show ?thesis
      proof (cases "set p\<^sub>m \<inter> set p\<^sub>n = {}")
        case True
        have \<phi>\<^sub>s_V: "var g \<phi>\<^sub>s = V" using step(1,2,3,9) reachable_same_var by (simp add: phiArg_same_var)
        from step(2) have \<phi>\<^sub>s_allVars: "\<phi>\<^sub>s \<in> allVars g" by (rule phiArg_in_allVars)

        obtain p\<^sub>m' where tmp: "g \<turnstile> m -p\<^sub>m@p\<^sub>m'\<rightarrow> defNode g \<phi>'" "set (butlast (p\<^sub>m@p\<^sub>m')) \<inter> set (butlast p\<^sub>n) = {}"
         by (rule phiArg_disjoint_paths_extend[of g \<phi>\<^sub>s V  \<phi>\<^sub>r m n p\<^sub>m p\<^sub>n \<phi>'])
            (metis \<phi>\<^sub>s_V \<phi>\<^sub>s_allVars step r_s_path_props(1,3) True disjoint_iff_not_equal in_set_butlastD)+

        from step(5) this(1) step(7) this(2) step(9) step(10) step(11)
        show ?thesis by (rule step.IH[of "p\<^sub>m@p\<^sub>m'" p\<^sub>n])
      next
        case paths_cross: False
        with step reachable.intros
        show ?thesis using path_crossing_yields_convergence[of \<phi>\<^sub>r \<phi>\<^sub>s p\<^sub>n p\<^sub>m] by blast
      qed
    qed

    then obtain \<phi>\<^sub>z ns ms where "\<phi>\<^sub>z \<in> reachable g \<phi>" and "old.pathsConverge g n ns m ms (defNode g \<phi>\<^sub>z)"
      by blast
    moreover
    with reachable_props have "var g \<phi>\<^sub>z = V" by (metis V_props(3) phiArg_trancl_same_var rtranclpD)
    ultimately have "necessaryPhi' g \<phi>\<^sub>z " using r_s_path_props
      unfolding necessaryPhi_def by blast
    moreover with \<open>\<phi>\<^sub>z \<in> reachable g \<phi>\<close> have "unnecessaryPhi g \<phi>\<^sub>z" by -(rule reachable_props)
    ultimately show False unfolding unnecessaryPhi_def by blast
  qed
qed

txt \<open>Together with lemma 1, we thus have that a CFG without redundant SCCs is cytron-minimal, proving that the
     property established by Braun et al.'s algorithm suffices.\<close>
corollary no_redundant_SCC_minimal:
assumes "\<not>(\<exists>P scc. redundant_scc g P scc)"
shows "cytronMinimal g"
using assms 1 no_redundant_set_minimal by blast


txt \<open>Finally, to conclude, we'll show that the above theorem is indeed a stronger assertion about a graph
     than the lack of trivial \pf s. Intuitively, this is because a set containing only a
     trivial \pf\ is a redundant set.\<close>

corollary
assumes "\<not>(\<exists>P. redundant_set g P)"
shows "\<not>redundant g"
proof -
  have "redundant g \<Longrightarrow> \<exists>P. redundant_set g P"
  proof -
    assume "redundant g"
    then obtain \<phi> where "phi g \<phi> \<noteq> None" "trivial g \<phi>"
     unfolding redundant_def redundant_set_def dom_def phiArg_def trivial_def isTrivialPhi_def
     by (clarsimp split: option.splits) fastforce
    hence "redundant_set g {\<phi>}"
     unfolding redundant_set_def dom_def phiArg_def trivial_def isTrivialPhi_def
     by auto
    thus ?thesis by auto
  qed
  with assms show ?thesis by auto
qed


end

end
