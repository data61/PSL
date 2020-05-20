section "Vertex Cover"

theory Approx_VC_Hoare
imports "HOL-Hoare.Hoare_Logic"
begin

text \<open>The algorithm is classical, the proof is based on and augments the one
by Berghammer and M\"uller-Olm \cite{BerghammerM03}.\<close>

subsection "Graph"

text \<open>A graph is simply a set of edges, where an edge is a 2-element set.\<close>

definition vertex_cover :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
"vertex_cover E C = (\<forall>e \<in> E. e \<inter> C \<noteq> {})"

abbreviation matching :: "'a set set \<Rightarrow> bool" where
"matching M \<equiv> pairwise disjnt M"

lemma card_matching_vertex_cover:
  "\<lbrakk> finite C;  matching M;  M \<subseteq> E;  vertex_cover E C \<rbrakk> \<Longrightarrow> card M \<le> card C"
apply(erule card_le_if_inj_on_rel[where r = "\<lambda>e v. v \<in> e"])
 apply (meson disjnt_def disjnt_iff vertex_cover_def subsetCE)
by (meson disjnt_iff pairwise_def)


subsection "The Approximation Algorithm"

text \<open>Formulated using a simple(!) predefined Hoare-logic.
This leads to a streamlined proof based on standard invariant reasoning.

The nondeterministic selection of an element from a set \<open>F\<close> is simulated by @{term "SOME x. x \<in> F"}.
The \<open>SOME\<close> operator is built into HOL: @{term "SOME x. P x"} denotes some \<open>x\<close> that satisfies \<open>P\<close>
if such an \<open>x\<close> exists; otherwise it denotes an arbitrary element. Note that there is no
actual nondeterminism involved: @{term "SOME x. P x"} is some fixed element
but in general we don't know which one. Proofs about \<open>SOME\<close> are notoriously tedious.
Typically it involves showing first that @{prop "\<exists>x. P x"}. Then @{thm someI_ex} implies
@{prop"P (SOME x. P x)"}. There are a number of (more) useful related theorems:
just click on @{thm someI_ex} to be taken there.\<close>

text \<open>Convenient notation for choosing an arbitrary element from a set:\<close>
abbreviation "some A \<equiv> SOME x. x \<in> A"

locale Edges =
  fixes E :: "'a set set"
  assumes finE: "finite E"
  assumes edges2: "e \<in> E \<Longrightarrow> card e = 2"
begin

text \<open>The invariant:\<close>

definition "inv_matching C F M =
  (matching M \<and> M \<subseteq> E \<and> card C \<le> 2 * card M \<and> (\<forall>e \<in> M. \<forall>f \<in> F. e \<inter> f = {}))"

definition invar :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
"invar C F = (F \<subseteq> E \<and> vertex_cover (E-F) C \<and> finite C \<and> (\<exists>M. inv_matching C F M))"

text \<open>Preservation of the invariant by the loop body:\<close>

lemma invar_step:
  assumes "F \<noteq> {}" "invar C F"
  shows "invar (C \<union> some F) (F - {e' \<in> F. some F \<inter> e' \<noteq> {}})"
proof -
  from assms(2) obtain M where "F \<subseteq> E" and vc: "vertex_cover (E-F) C" and fC: "finite C"
    and m: "matching M" "M \<subseteq> E" and card: "card C \<le> 2 * card M"
    and disj: "\<forall>e \<in> M. \<forall>f \<in> F. e \<inter> f = {}"
  by (auto simp: invar_def inv_matching_def)
  let ?e = "SOME e. e \<in> F"
  have "?e \<in> F" using \<open>F \<noteq> {}\<close> by (simp add: some_in_eq)
  hence fe': "finite ?e" using \<open>F \<subseteq> E\<close> edges2 by(intro card_ge_0_finite) auto
  have "?e \<notin> M" using edges2 \<open>?e \<in> F\<close> disj \<open>F \<subseteq> E\<close> by fastforce
  have card': "card (C \<union> ?e) \<le> 2 * card (insert ?e M)"
    using \<open>?e \<in> F\<close> \<open>?e \<notin> M\<close> card_Un_le[of C ?e] \<open>F \<subseteq> E\<close> edges2 card finite_subset[OF m(2) finE]
    by fastforce
  let ?M = "M \<union> {?e}"
  have vc': "vertex_cover (E - (F - {e' \<in> F. ?e \<inter> e' \<noteq> {}})) (C \<union> ?e)"
    using vc by(auto simp: vertex_cover_def)
  have m': "inv_matching (C \<union> ?e) (F - {e' \<in> F. ?e \<inter> e' \<noteq> {}}) ?M"
    using m card' \<open>F \<subseteq> E\<close> \<open>?e \<in> F\<close> disj
    by(auto simp: inv_matching_def Int_commute disjnt_def pairwise_insert)
  show ?thesis using \<open>F \<subseteq> E\<close> vc' fC fe' m' by(auto simp add: invar_def Let_def)
qed


lemma approx_vertex_cover:
"VARS C F
  {True}
  C := {};
  F := E;
  WHILE F \<noteq> {}
  INV {invar C F}
  DO C := C \<union> some F;
     F := F - {e' \<in> F. some F \<inter> e' \<noteq> {}}
  OD
  {vertex_cover E C \<and> (\<forall>C'. finite C' \<and> vertex_cover E C' \<longrightarrow> card C \<le> 2 * card C')}"
proof (vcg, goal_cases)
  case (1 C F)
  have "inv_matching {} E {}" by (auto simp add: inv_matching_def)
  with 1 show ?case by (auto simp add: invar_def vertex_cover_def)
next
  case (2 C F)
  thus ?case using invar_step[of F C] by(auto simp: Let_def)
next
  case (3 C F)
  then obtain M :: "'a set set" where
    post: "vertex_cover E C" "matching M" "M \<subseteq> E" "card C \<le> 2 * card M"
    by(auto simp: invar_def inv_matching_def)

  have opt: "card C \<le> 2 * card C'" if C': "finite C'" "vertex_cover E C'" for C'
  proof -
    note post(4)
    also have "2 * card M \<le> 2 * card C'"
    using card_matching_vertex_cover[OF C'(1) post(2,3) C'(2)] by simp
    finally show "card C \<le> 2 * card C'" .
  qed

  show ?case using post(1) opt by auto
qed

end (* locale Graph *)

subsection "Version for Hypergraphs"

text \<open>Almost the same. We assume that the degree of every edge is bounded.\<close>

locale Bounded_Hypergraph =
  fixes E :: "'a set set"
  fixes k :: nat
  assumes finE: "finite E"
  assumes edge_bnd: "e \<in> E \<Longrightarrow> finite e \<and> card e \<le> k"
  assumes E1: "{} \<notin> E"
begin

definition "inv_matching C F M =
  (matching M \<and> M \<subseteq> E \<and> card C \<le> k * card M \<and> (\<forall>e \<in> M. \<forall>f \<in> F. e \<inter> f = {}))"

definition invar :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
"invar C F = (F \<subseteq> E \<and> vertex_cover (E-F) C \<and> finite C \<and> (\<exists>M. inv_matching C F M))"

lemma invar_step:
  assumes "F \<noteq> {}" "invar C F"
  shows "invar (C \<union> some F) (F - {e' \<in> F. some F \<inter> e' \<noteq> {}})"
proof -
  from assms(2) obtain M where "F \<subseteq> E" and vc: "vertex_cover (E-F) C" and fC: "finite C"
    and m: "matching M" "M \<subseteq> E" and card: "card C \<le> k * card M"
    and disj: "\<forall>e \<in> M. \<forall>f \<in> F. e \<inter> f = {}"
  by (auto simp: invar_def inv_matching_def)
  let ?e = "SOME e. e \<in> F"
  have "?e \<in> F" using \<open>F \<noteq> {}\<close> by (simp add: some_in_eq)
  hence fe': "finite ?e" using \<open>F \<subseteq> E\<close> assms(2) edge_bnd by blast
  have "?e \<notin> M" using E1 \<open>?e \<in> F\<close> disj \<open>F \<subseteq> E\<close> by fastforce
  have card': "card (C \<union> ?e) \<le> k * card (insert ?e M)"
    using \<open>?e \<in> F\<close> \<open>?e \<notin> M\<close> card_Un_le[of C ?e] \<open>F \<subseteq> E\<close> edge_bnd card finite_subset[OF m(2) finE]
    by fastforce
  let ?M = "M \<union> {?e}"
  have vc': "vertex_cover (E - (F - {e' \<in> F. ?e \<inter> e' \<noteq> {}})) (C \<union> ?e)"
    using vc by(auto simp: vertex_cover_def)
  have m': "inv_matching (C \<union> ?e) (F - {e' \<in> F. ?e \<inter> e' \<noteq> {}}) ?M"
    using m card' \<open>F \<subseteq> E\<close> \<open>?e \<in> F\<close> disj
    by(auto simp: inv_matching_def Int_commute disjnt_def pairwise_insert)
  show ?thesis using \<open>F \<subseteq> E\<close> vc' fC fe' m' by(auto simp add: invar_def Let_def)
qed


lemma approx_vertex_cover_bnd:
"VARS C F
  {True}
  C := {};
  F := E;
  WHILE F \<noteq> {}
  INV {invar C F}
  DO C := C \<union> some F;
     F := F - {e' \<in> F. some F \<inter> e' \<noteq> {}}
  OD
  {vertex_cover E C \<and> (\<forall>C'. finite C' \<and> vertex_cover E C' \<longrightarrow> card C \<le> k * card C')}"
proof (vcg, goal_cases)
  case (1 C F)
  have "inv_matching {} E {}" by (auto simp add: inv_matching_def)
  with 1 show ?case by (auto simp add: invar_def vertex_cover_def)
next
  case (2 C F)
  thus ?case using invar_step[of F C] by(auto simp: Let_def)
next
  case (3 C F)
  then obtain M :: "'a set set" where
    post: "vertex_cover E C" "matching M" "M \<subseteq> E" "card C \<le> k * card M"
    by(auto simp: invar_def inv_matching_def)

  have opt: "card C \<le> k * card C'" if C': "finite C'" "vertex_cover E C'" for C'
  proof -
    note post(4)
    also have "k * card M \<le> k * card C'"
    using card_matching_vertex_cover[OF C'(1) post(2,3) C'(2)] by simp
    finally show "card C \<le> k * card C'" .
  qed

  show ?case using post(1) opt by auto
qed

end (* locale Bounded_Hypergraph *)

end
