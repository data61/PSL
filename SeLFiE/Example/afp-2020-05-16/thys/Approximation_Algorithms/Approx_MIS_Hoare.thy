section "Independent Set"

theory Approx_MIS_Hoare
imports
  "HOL-Hoare.Hoare_Logic"
  "HOL-Library.Disjoint_Sets"
begin


text \<open>The algorithm is classical, the proofs are inspired by the ones
by Berghammer and M\"uller-Olm \cite{BerghammerM03}.
In particular the approximation ratio is improved from \<open>\<Delta>+1\<close> to \<open>\<Delta>\<close>.\<close>


subsection "Graph"

text \<open>A set set is simply a set of edges, where an edge is a 2-element set.\<close>

definition independent_vertices :: "'a set set \<Rightarrow> 'a set \<Rightarrow> bool" where
"independent_vertices E S \<longleftrightarrow> S \<subseteq> \<Union>E \<and> (\<forall>v1 v2. v1 \<in> S \<and> v2 \<in> S \<longrightarrow> {v1, v2} \<notin> E)"

locale Graph_E =
  fixes E :: "'a set set"
  assumes finite_E: "finite E"
  assumes edges2: "e \<in> E \<Longrightarrow> card e = 2"
begin

fun vertices :: "'a set set \<Rightarrow> 'a set" where
"vertices G = \<Union>G"

abbreviation V :: "'a set" where
"V \<equiv> vertices E"

definition approximation_miv :: "nat \<Rightarrow> 'a set \<Rightarrow> bool" where
"approximation_miv n S \<longleftrightarrow> independent_vertices E S \<and> (\<forall>S'. independent_vertices E S' \<longrightarrow> card S' \<le> card S * n)"

fun neighbors :: "'a \<Rightarrow> 'a set" where
"neighbors v = {u. {u,v} \<in> E}"

fun degree_vertex :: "'a \<Rightarrow> nat" where
"degree_vertex v = card (neighbors v)"

abbreviation \<Delta> :: nat where
"\<Delta> \<equiv> Max{degree_vertex u|u. u \<in> V}"

lemma finite_edges: "e \<in> E \<Longrightarrow> finite e"
  using card_ge_0_finite and edges2 by force

lemma finite_V: "finite V"
  using finite_edges and finite_E by auto

lemma finite_neighbors: "finite (neighbors u)"
  using finite_V and rev_finite_subset [of V "neighbors u"] by auto

lemma independent_vertices_finite: "independent_vertices E S \<Longrightarrow> finite S"
  by (metis rev_finite_subset independent_vertices_def vertices.simps finite_V)

lemma edge_ex_vertices: "e \<in> E \<Longrightarrow> \<exists>u v. u \<noteq> v \<and> e = {u, v}"
proof -
  assume "e \<in> E"
  then have "card e = Suc (Suc 0)" using edges2 by auto
  then show "\<exists>u v. u \<noteq> v \<and> e = {u, v}"
    by (metis card_eq_SucD insertI1)
qed

lemma \<Delta>_pos [simp]: "E = {} \<or> 0 < \<Delta>"
proof cases
  assume "E = {}"
  then show "E = {} \<or> 0 < \<Delta>" by auto
next
  assume 1: "E \<noteq> {}"
  then have "V \<noteq> {}" using edges2 by fastforce
  moreover have "finite {degree_vertex u |u. u \<in> V}"
    by (metis finite_V finite_imageI Setcompr_eq_image)
  ultimately have 2: "\<Delta> \<in> {degree_vertex u |u. u \<in> V}" using Max_in by auto
  have "\<Delta> \<noteq> 0"
  proof
    assume "\<Delta> = 0"
    with 2 obtain u where 3: "u \<in> V" and 4: "degree_vertex u = 0" by auto
    from 3 obtain e where 5: "e \<in> E" and "u \<in> e" by auto
    moreover with 4 have "\<forall>v. {u, v} \<noteq> e" using finite_neighbors insert_absorb by fastforce
    ultimately show False using edge_ex_vertices by auto
  qed
  then show "E = {} \<or> 0 < \<Delta>" by auto
qed

lemma \<Delta>_max_degree: "u \<in> V \<Longrightarrow> degree_vertex u \<le> \<Delta>"
proof -
  assume H: "u \<in> V"
  have "finite {degree_vertex u |u. u \<in> V}"
    by (metis finite_V finite_imageI Setcompr_eq_image)
  with H show "degree_vertex u \<le> \<Delta>" using Max_ge by auto
qed

subsection \<open>Wei's algorithm: \<open>(\<Delta>+1)\<close>-approximation\<close>

text \<open>The 'functional' part of the invariant, used to prove that the algorithm produces an independent set of vertices.\<close>

definition inv_iv :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
"inv_iv S X \<longleftrightarrow> independent_vertices E S
            \<and> X \<subseteq> V
            \<and> (\<forall>v1 \<in> (V - X). \<forall>v2 \<in> S. {v1, v2} \<notin> E)
            \<and> S \<subseteq> X"

text \<open>Strenghten the invariant with an approximation ratio \<open>r\<close>:\<close>

definition inv_approx :: "'a set \<Rightarrow> 'a set \<Rightarrow> nat \<Rightarrow> bool" where
"inv_approx S X r \<longleftrightarrow> inv_iv S X \<and> card X \<le> card S * r"

text \<open>Preservation of the functional invariant:\<close>

lemma inv_preserv:
  fixes S :: "'a set"
    and X :: "'a set"
    and x :: "'a"
  assumes inv: "inv_iv S X"
      and x_def: "x \<in> V - X"
    shows "inv_iv (insert x S) (X \<union> neighbors x \<union> {x})"
proof -
  have inv1: "independent_vertices E S"
   and inv2: "X \<subseteq> V"
   and inv3: "S \<subseteq> X"
   and inv4: "\<forall>v1 v2. v1 \<in> (V - X) \<and> v2 \<in> S \<longrightarrow> {v1, v2} \<notin> E"
    using inv unfolding inv_iv_def by auto
  have finite_S: "finite S" using inv1 and independent_vertices_finite by auto
  have S1: "\<forall>y \<in> S. {x, y} \<notin> E" using inv4 and x_def by blast
  have S2: "\<forall>x \<in> S. \<forall>y \<in> S. {x, y} \<notin> E" using inv1 unfolding independent_vertices_def by metis
  have S3: "v1 \<in> insert x S \<Longrightarrow> v2 \<in> insert x S \<Longrightarrow> {v1, v2} \<notin> E" for v1 v2
    proof -
      assume "v1 \<in> insert x S" and "v2 \<in> insert x S"
      then consider
          (a) "v1 = x" and "v2 = x"
        | (b) "v1 = x" and "v2 \<in> S"
        | (c) "v1 \<in> S" and "v2 = x"
        | (d) "v1 \<in> S" and "v2 \<in> S"
        by auto
      then show "{v1, v2} \<notin> E"
      proof cases
        case a then show ?thesis using edges2 by force
      next
        case b then show ?thesis using S1 by auto
      next
        case c then show ?thesis using S1 by (metis doubleton_eq_iff)
      next
        case d then show ?thesis using S2 by auto
      qed
    qed
  (* invariant conjunct 1 *)
  have "independent_vertices E (insert x S)"
    using S3 and inv1 and x_def unfolding independent_vertices_def by auto
  (* invariant conjunct 2 *)
  moreover have "X \<union> neighbors x \<union> {x} \<subseteq> V"
  proof
    fix xa
    assume "xa \<in> X \<union> neighbors x \<union> {x}"
    then consider (a) "xa \<in> X" | (b) "xa \<in> neighbors x" | (c) "xa = x" by auto
    then show "xa \<in> V"
    proof cases
      case a
      then show ?thesis using inv2 by blast
    next
      case b
      then show ?thesis by auto
    next
      case c
      then show ?thesis using x_def by blast
    qed
  qed
  (* invariant conjunct 3 *)
  moreover have "insert x S \<subseteq> X \<union> neighbors x \<union> {x}" using inv3 by auto
  (* invariant conjunct 4 *)
  moreover have "v1 \<in> V - (X \<union> neighbors x \<union> {x}) \<Longrightarrow> v2 \<in> insert x S \<Longrightarrow> {v1, v2} \<notin> E" for v1 v2
  proof -
    assume H: "v1 \<in> V - (X \<union> neighbors x \<union> {x})" and "v2 \<in> insert x S"
    then consider (a) "v2 = x" | (b) "v2 \<in> S" by auto
    then show "{v1, v2} \<notin> E"
    proof cases
      case a
      with H have "v1 \<notin> neighbors v2" by blast
      then show ?thesis by auto
    next
      case b
      from H have "v1 \<in> V - X" by blast
      with b and inv4 show ?thesis by blast
    qed
  qed
  (* conclusion *)
  ultimately show "inv_iv (insert x S) (X \<union> neighbors x \<union> {x})" unfolding inv_iv_def by blast
qed

lemma inv_approx_preserv:
  assumes inv: "inv_approx S X (\<Delta> + 1)"
      and x_def: "x \<in> V - X"
    shows "inv_approx (insert x S) (X \<union> neighbors x \<union> {x}) (\<Delta> + 1)"
proof -
  have finite_S: "finite S" using inv and independent_vertices_finite
    unfolding inv_approx_def inv_iv_def by auto
  have Sx: "x \<notin> S" using inv and x_def unfolding inv_approx_def inv_iv_def by blast
  (* main invariant is preserved *)
  from inv have "inv_iv S X" unfolding inv_approx_def by auto
  with x_def have "inv_iv (insert x S) (X \<union> neighbors x \<union> {x})"
  proof (intro inv_preserv, auto) qed
  (* the approximation ratio is preserved (at most \<Delta>+1 vertices are removed in any iteration) *)
  moreover have "card (X \<union> neighbors x \<union> {x}) \<le> card (insert x S) * (\<Delta> + 1)"
  proof -
    have "degree_vertex x \<le> \<Delta>" using \<Delta>_max_degree and x_def by auto
    then have "card (neighbors x \<union> {x}) \<le> \<Delta> + 1" using card_Un_le [of "neighbors x" "{x}"] by auto
    then have "card (X \<union> neighbors x \<union> {x}) \<le> card X + \<Delta> + 1" using card_Un_le [of X "neighbors x \<union> {x}"] by auto
    also have "... \<le> card S * (\<Delta> + 1) + \<Delta> + 1" using inv unfolding inv_approx_def by auto
    also have "... = card (insert x S) * (\<Delta> + 1)" using finite_S and Sx by auto
    finally show ?thesis .
  qed
  (* conclusion *)
  ultimately show "inv_approx (insert x S) (X \<union> neighbors x \<union> {x}) (\<Delta> + 1)"
    unfolding inv_approx_def by auto
qed

(* the antecedent combines inv_approx (for an arbitrary ratio r) and the negated post-condition *)
lemma inv_approx: "independent_vertices E S \<Longrightarrow> card V \<le> card S * r \<Longrightarrow> approximation_miv r S"
proof -
  assume 1: "independent_vertices E S" and 2: "card V \<le> card S * r"
  have "independent_vertices E S' \<Longrightarrow> card S' \<le> card S * r" for S'
  proof -
    assume  "independent_vertices E S'"
    then have "S' \<subseteq> V" unfolding independent_vertices_def by auto
    then have "card S' \<le> card V" using finite_V and card_mono by auto
    also have "... \<le> card S * r" using 2 by auto
    finally show "card S' \<le> card S * r" .
  qed
  with 1 show "approximation_miv r S" unfolding approximation_miv_def by auto
qed

theorem wei_approx_\<Delta>_plus_1:
"VARS (S :: 'a set) (X :: 'a set) (x :: 'a)
  { True }
  S := {};
  X := {};
  WHILE X \<noteq> V
  INV { inv_approx S X (\<Delta> + 1) }
  DO x := (SOME x. x \<in> V - X);
     S := insert x S;
     X := X \<union> neighbors x \<union> {x}
  OD
  { approximation_miv (\<Delta> + 1) S }"
proof (vcg, goal_cases)
  case (1 S X x) (* invariant initially true *)
  then show ?case unfolding inv_approx_def inv_iv_def independent_vertices_def by auto
next
  case (2 S X x) (* invariant preserved by loop *)
  (* definedness of assignment *)
  let ?x = "(SOME x. x \<in> V - X)"
  have "V - X \<noteq> {}" using 2 unfolding inv_approx_def inv_iv_def by blast
  then have "?x \<in> V - X" using some_in_eq by metis
  with 2 show ?case using inv_approx_preserv by auto
next
  case (3 S X x) (* invariant implies post-condition *)
  then show ?case using inv_approx unfolding inv_approx_def inv_iv_def by auto
qed


subsection \<open>Wei's algorithm: \<open>\<Delta>\<close>-approximation\<close>

text \<open>The previous approximation uses very little information about the optimal solution (it has at most as many vertices as the set itself). With some extra effort we can improve the ratio to \<open>\<Delta>\<close> instead of \<open>\<Delta>+1\<close>. In order to do that we must show that among the vertices removed in each iteration, at most \<open>\<Delta>\<close> could belong to an optimal solution. This requires carrying around a set \<open>P\<close> (via a ghost variable) which records the vertices deleted in each iteration.\<close>

definition inv_partition :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
"inv_partition S X P \<longleftrightarrow> inv_iv S X
                     \<and> \<Union>P = X
                     \<and> (\<forall>p \<in> P. \<exists>s \<in> V. p = {s} \<union> neighbors s)
                     \<and> card P = card S
                     \<and> finite P"

lemma inv_partition_preserv:
  assumes inv: "inv_partition S X P"
      and x_def: "x \<in> V - X"
    shows "inv_partition (insert x S) (X \<union> neighbors x \<union> {x}) (insert ({x} \<union> neighbors x) P)"
proof -
  have finite_S: "finite S" using inv and independent_vertices_finite
    unfolding inv_partition_def inv_iv_def by auto
  have Sx: "x \<notin> S" using inv and x_def unfolding inv_partition_def inv_iv_def by blast
  (* main invariant is preserved *)
  from inv have "inv_iv S X" unfolding inv_partition_def by auto
  with x_def have "inv_iv (insert x S) (X \<union> neighbors x \<union> {x})"
  proof (intro inv_preserv, auto) qed
  (* conjunct 1 *)
  moreover have "\<Union>(insert ({x} \<union> neighbors x) P) = X \<union> neighbors x \<union> {x}"
    using inv unfolding inv_partition_def by auto
  (* conjunct 2 *)
  moreover have "(\<forall>p\<in>insert ({x} \<union> neighbors x) P. \<exists>s \<in> V. p = {s} \<union> neighbors s)"
    using inv and x_def unfolding inv_partition_def by auto
  (* conjunct 3 *)
  moreover have "card (insert ({x} \<union> neighbors x) P) = card (insert x S)"
  proof -
    from x_def and inv have "x \<notin> \<Union>P" unfolding inv_partition_def by auto
    then have "{x} \<union> neighbors x \<notin> P" by auto
    then have "card (insert ({x} \<union> neighbors x) P) = card P + 1" using inv unfolding inv_partition_def by auto
    moreover have "card (insert x S) = card S + 1" using Sx and finite_S by auto
    ultimately show ?thesis using inv unfolding inv_partition_def by auto
  qed
  (* conjunct 4 *)
  moreover have "finite (insert ({x} \<union> neighbors x) P)"
    using inv unfolding inv_partition_def by auto
  (* conclusion *)
  ultimately show "inv_partition (insert x S) (X \<union> neighbors x \<union> {x}) (insert ({x} \<union> neighbors x) P)"
    unfolding inv_partition_def by auto
qed

lemma card_Union_le_sum_card:
  fixes U :: "'a set set"
  assumes "\<forall>u \<in> U. finite u"
  shows "card (\<Union>U) \<le> sum card U"
proof (cases "finite U")
  case False
  then show "card (\<Union>U) \<le> sum card U"
    using card_eq_0_iff finite_UnionD by auto
next
  case True
  then show "card (\<Union>U) \<le> sum card U"
  proof (induct U rule: finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert x F)
    then have "card(\<Union>(insert x F)) \<le> card(x) + card (\<Union>F)" using card_Un_le by auto
    also have "... \<le> card(x) + sum card F" using insert.hyps by auto
    also have "... = sum card (insert x F)" using sum.insert_if and insert.hyps by auto
    finally show ?case .
  qed
qed

(* this lemma could be more generally about U :: "nat set", but this makes its application more difficult later *)
lemma sum_card:
  fixes U :: "'a set set"
    and n :: nat
  assumes "\<forall>S \<in> U. card S \<le> n"
  shows "sum card U \<le> card U * n"
proof cases
  assume "infinite U \<or> U = {}"
  then have "sum card U = 0" using sum.infinite by auto
  then show "sum card U \<le> card U * n" by auto
next
  assume "\<not>(infinite U \<or> U = {})"
  with assms have "finite U" and "U \<noteq> {}"and "\<forall>S \<in> U. card S \<le> n" by auto
  then show "sum card U \<le> card U * n"
  proof (induct U rule: finite_ne_induct)
    case (singleton x)
    then show ?case by auto
  next
    case (insert x F)
    assume "\<forall>S\<in>insert x F. card S \<le> n"
    then have 1:"card x \<le> n" and 2:"sum card F \<le> card F * n" using insert.hyps by auto
    then have "sum card (insert x F) = card x + sum card F" using sum.insert_if and insert.hyps by auto
    also have "... \<le> n + card F * n" using 1 and 2 by auto
    also have "... = card (insert x F) * n" using card_insert_if and insert.hyps by auto
    finally show ?case .
  qed
qed

(* among the vertices deleted in each iteration, at most \<Delta> can belong to an independent set of
   vertices: the chosen vertex or (some of) its neighbors *)
lemma x_or_neighbors:
  fixes P :: "'a set set"
    and S :: "'a set"
  assumes inv: "\<forall>p\<in>P. \<exists>s \<in> V. p = {s} \<union> neighbors s"
      and ivS: "independent_vertices E S"
    shows "\<forall>p \<in> P. card (S \<inter> p) \<le> \<Delta>"
proof
  fix p
  assume "p \<in> P"
  then obtain s where 1: "s \<in> V \<and> p = {s} \<union> neighbors s" using inv by blast
  then show "card (S \<inter> p) \<le> \<Delta>"
  proof cases
    assume "s \<in> S"
    then have "S \<inter> neighbors s = {}" using ivS unfolding independent_vertices_def by auto
    then have "S \<inter> p \<subseteq> {s}" using 1 by auto
    then have 2: "card (S \<inter> p) \<le> 1" using subset_singletonD by fastforce
    consider (a) "E = {}" | (b) "0 < \<Delta>" using \<Delta>_pos by auto
    then show "card (S \<inter> p) \<le> \<Delta>"
    proof cases
      case a
      then have "S = {}" using ivS unfolding independent_vertices_def by auto
      then show ?thesis by auto
    next
      case b
      then show ?thesis using 2 by auto
    qed  
  next
    assume "s \<notin> S"
    with 1 have "S \<inter> p \<subseteq> neighbors s" by auto
    then have "card (S \<inter> p) \<le> degree_vertex s" using card_mono and finite_neighbors by auto
    then show "card (S \<inter> p) \<le> \<Delta>" using 1 and \<Delta>_max_degree [of s] by auto
  qed
qed

(* the premise combines the invariant and the negated post-condition *)
lemma inv_partition_approx: "inv_partition S V P \<Longrightarrow> approximation_miv \<Delta> S"
proof -
  assume H1: "inv_partition S V P"
  then have "independent_vertices E S" unfolding inv_partition_def inv_iv_def by auto
  moreover have "independent_vertices E S' \<Longrightarrow> card S' \<le> card S * \<Delta>" for S'
  proof -
    let ?I = "{S' \<inter> p | p. p \<in> P}"
    (* split the optimal solution among the sets of P, which cover V so no element is
       lost. We obtain a cover of S' and show the required bound on its cardinality *)
    assume H2: "independent_vertices E S'"
    then have "S' \<subseteq> V" unfolding independent_vertices_def using vertices.simps by blast
    with H1 have "S' = S' \<inter> \<Union>P" unfolding inv_partition_def by auto
    then have "S' = (\<Union>p \<in> P. S' \<inter> p)" using Int_Union by auto
    then have "S' = \<Union>?I" by blast
    moreover have "finite S'" using H2 and independent_vertices_finite by auto
    then have "p \<in> P \<Longrightarrow> finite (S' \<inter> p)" for p by auto
    ultimately have "card S' \<le> sum card ?I" using card_Union_le_sum_card [of ?I] by auto
    also have "... \<le> card ?I * \<Delta>"
      using x_or_neighbors [of P S']
        and sum_card [of ?I \<Delta>]
        and H1 and H2 unfolding inv_partition_def by auto
    also have "... \<le> card P * \<Delta>"
    proof -
      have "finite P" using H1 unfolding inv_partition_def by auto
      then have "card ?I \<le> card P"
        using Setcompr_eq_image [of "\<lambda>p. S' \<inter> p" P]
          and card_image_le unfolding inv_partition_def by auto
      then show ?thesis by auto
    qed
    also have "... = card S * \<Delta>" using H1 unfolding inv_partition_def by auto
    ultimately show "card S' \<le> card S * \<Delta>" by auto
  qed
  ultimately show "approximation_miv \<Delta> S" unfolding approximation_miv_def by auto
qed

theorem wei_approx_\<Delta>:
"VARS (S :: 'a set) (X :: 'a set) (x :: 'a)
  { True }
  S := {};
  X := {};
  WHILE X \<noteq> V
  INV { \<exists>P. inv_partition S X P }
  DO x := (SOME x. x \<in> V - X);
     S := insert x S;
     X := X \<union> neighbors x \<union> {x}
  OD
  { approximation_miv \<Delta> S }"
proof (vcg, goal_cases)
  case (1 S X x) (* invariant initially true *)
  (* the invariant is initially true with the ghost variable P := {} *)
  have "inv_partition {} {} {}" unfolding inv_partition_def inv_iv_def independent_vertices_def by auto
  then show ?case by auto
next
  case (2 S X x) (* invariant preserved by loop *)
  (* definedness of assignment *)
  let ?x = "(SOME x. x \<in> V - X)"
  from 2 obtain P where I: "inv_partition S X P" by auto 
  then have "V - X \<noteq> {}" using 2 unfolding inv_partition_def by auto
  then have "?x \<in> V - X" using some_in_eq by metis
  (* show that the invariant is true with the ghost variable P := insert ({?x} \<union> neighbors ?x) P *)
  with I have "inv_partition (insert ?x S) (X \<union> neighbors ?x \<union> {?x}) (insert ({?x} \<union> neighbors ?x) P)"
    using inv_partition_preserv by blast
  then show ?case by auto
next
  case (3 S X x) (* invariant implies post-condition *)
  then show ?case using inv_partition_approx unfolding inv_approx_def by auto
qed

subsection "Wei's algorithm with dynamically computed approximation ratio"

text \<open>In this subsection, we augment the algorithm with a variable used to compute the effective approximation ratio of the solution. In addition, the vertex of smallest degree is picked. With this heuristic, the algorithm achieves an approximation ratio of \<open>(\<Delta>+2)/3\<close>, but this is not proved here.\<close>

definition vertex_heuristic :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"vertex_heuristic X v = (\<forall>u \<in> V - X. card (neighbors v - X) \<le> card (neighbors u - X))"

(* this lemma is needed to show that there exist a vertex to be picked by the heuristic *)
lemma ex_min_finite_set:
  fixes S :: "'a set"
    and f :: "'a \<Rightarrow> nat"
    shows "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> S \<and> (\<forall>y \<in> S. f x \<le> f y)"
          (is "?P1 \<Longrightarrow> ?P2 \<Longrightarrow> \<exists>x. ?minf S x")
proof (induct S rule: finite_ne_induct)
  case (singleton x)
  have "?minf {x} x" by auto
  then show ?case by auto
next
  case (insert x F)
  from insert(4) obtain y where Py: "?minf F y" by auto
  show "\<exists>z. ?minf (insert x F) z"
  proof cases
    assume "f x < f y"
    then have "?minf (insert x F) x" using Py by auto
    then show ?case by auto
  next
    assume "\<not>f x < f y"
    then have "?minf (insert x F) y" using Py by auto
    then show ?case by auto
  qed
qed

lemma inv_approx_preserv2:
  fixes S :: "'a set"
    and X :: "'a set"
    and s :: nat
    and x :: "'a"
  assumes inv: "inv_approx S X s"
      and x_def: "x \<in> V - X"
    shows "inv_approx (insert x S) (X \<union> neighbors x \<union> {x}) (max (card (neighbors x \<union> {x} - X)) s)"
proof -
  have finite_S: "finite S" using inv and independent_vertices_finite unfolding inv_approx_def inv_iv_def by auto
  have Sx: "x \<notin> S" using inv and x_def unfolding inv_approx_def inv_iv_def by blast
  (* main invariant is preserved *)
  from inv have "inv_iv S X" unfolding inv_approx_def by auto
  with x_def have "inv_iv (insert x S) (X \<union> neighbors x \<union> {x})"
  proof (intro inv_preserv, auto) qed
  (* the approximation ratio is preserved *)
  moreover have "card (X \<union> neighbors x \<union> {x}) \<le> card (insert x S) * max (card (neighbors x \<union> {x} - X)) s"
  proof -
    let ?N = "neighbors x \<union> {x} - X"
    have "card (X \<union> ?N) \<le> card X + card ?N" using card_Un_le [of X ?N] by auto
    also have "... \<le> card S * s + card ?N" using inv unfolding inv_approx_def by auto
    also have "... \<le> card S * max (card ?N) s + card ?N" by auto
    also have "... \<le> card S * max (card ?N) s + max (card ?N) s" by auto
    also have "... = card (insert x S) * max (card ?N) s" using Sx and finite_S by auto
    finally show ?thesis by auto
  qed
  (* conclusion *)
  ultimately show "inv_approx (insert x S) (X \<union> neighbors x \<union> {x}) (max (card (neighbors x \<union> {x} - X)) s)"
    unfolding inv_approx_def by auto
qed

theorem wei_approx_min_degree_heuristic:
"VARS (S :: 'a set) (X :: 'a set) (x :: 'a) (r :: nat)
  { True }
  S := {};
  X := {};
  r := 0;
  WHILE X \<noteq> V
  INV { inv_approx S X r }
  DO x := (SOME x. x \<in> V - X \<and> vertex_heuristic X x);
     S := insert x S;
     r := max (card (neighbors x \<union> {x} - X)) r;
     X := X \<union> neighbors x \<union> {x}
  OD
  { approximation_miv r S }"
proof (vcg, goal_cases)
  case (1 S X x r) (* invariant initially true *)
  then show ?case unfolding inv_approx_def inv_iv_def independent_vertices_def by auto
next
  case (2 S X x r) (* invariant preserved by loop *)
  (* definedness of assignment *)
  let ?x = "(SOME x. x \<in> V - X \<and> vertex_heuristic X x)"
  have "V - X \<noteq> {}" using 2 unfolding inv_approx_def inv_iv_def by blast
  moreover have "finite (V - X)" using 2 and finite_V by auto
  ultimately have "\<exists>x. x \<in> V - X \<and> vertex_heuristic X x"
    using ex_min_finite_set [where ?f = "\<lambda>x. card (neighbors x - X)"]
    unfolding vertex_heuristic_def by auto
  then have x_def: "?x \<in> V - X \<and> vertex_heuristic X ?x"
    using someI_ex [where ?P = "\<lambda>x. x \<in> V - X \<and> vertex_heuristic X x"] by auto
  with 2 show ?case using inv_approx_preserv2 by auto
next
  case (3 S X x r)
  then show ?case using inv_approx unfolding inv_approx_def inv_iv_def by auto
qed

end
end