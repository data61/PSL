theory Matching
imports Main
begin

type_synonym label = nat

section \<open>Definitions\<close>

definition finite_graph :: "'v set => ('v * 'v) set \<Rightarrow> bool" where
  "finite_graph V E = (finite V \<and> finite E \<and> 
  (\<forall> e \<in> E. fst e \<in> V \<and> snd e \<in> V \<and> fst e ~= snd e))"

definition degree :: "('v * 'v) set \<Rightarrow> 'v \<Rightarrow> nat" where
  "degree E v = card {e \<in> E. fst e = v \<or> snd e = v}"

definition edge_as_set :: "('v * 'v) \<Rightarrow> 'v set" where
  "edge_as_set e = {fst e, snd e}"

definition N :: "'v set \<Rightarrow> ('v \<Rightarrow> label) \<Rightarrow> nat \<Rightarrow> nat" where
  "N V L i = card {v \<in> V. L v = i}"

definition weight:: "label set \<Rightarrow> (label \<Rightarrow> nat) \<Rightarrow> nat" where
  "weight LV f = f 1 + (\<Sum>i\<in>LV. (f i) div 2)"

definition OSC :: "('v \<Rightarrow> label) \<Rightarrow> ('v * 'v) set \<Rightarrow> bool" where
  "OSC L E = (\<forall>e \<in> E. L (fst e) = 1 \<or> L (snd e) = 1 \<or> 
                     L (fst e) = L (snd e) \<and> L (fst e) > 1)"

definition disjoint_edges :: "('v * 'v) \<Rightarrow> ('v * 'v) \<Rightarrow> bool" where
  "disjoint_edges e1 e2 = (fst e1 \<noteq> fst e2 \<and> fst e1 \<noteq> snd e2 \<and> 
                          snd e1 \<noteq> fst e2 \<and> snd e1 \<noteq> snd e2)"

definition matching :: "'v set \<Rightarrow> ('v * 'v) set \<Rightarrow> ('v * 'v) set \<Rightarrow> bool" where
  "matching V E M = (M \<subseteq> E \<and> finite_graph V E \<and> 
  (\<forall>e1 \<in> M. \<forall> e2 \<in> M. e1 \<noteq> e2 \<longrightarrow> disjoint_edges e1 e2))"

definition matching_i :: "nat \<Rightarrow> 'v set \<Rightarrow> ('v * 'v) set \<Rightarrow> ('v * 'v) set \<Rightarrow>
  ('v \<Rightarrow> label) \<Rightarrow> ('v * 'v) set" where
  "matching_i i V E M L = {e \<in> M. i=1 \<and> (L (fst e) = i \<or> L (snd e) = i) 
  \<or> i>1 \<and> L (fst e) = i \<and> L (snd e) = i}"

definition V_i:: "nat \<Rightarrow> 'v set \<Rightarrow> ('v * 'v) set \<Rightarrow> ('v * 'v) set \<Rightarrow> 
                  ('v \<Rightarrow> label) \<Rightarrow> 'v set" where
  "V_i i V E M L = \<Union> (edge_as_set ` matching_i i V E M L)"

definition endpoint_inV :: "'v set \<Rightarrow> ('v * 'v) \<Rightarrow> 'v" where 
  "endpoint_inV V e = (if fst e \<in> V then fst e else snd e)" 

definition relevant_endpoint :: "('v \<Rightarrow> label) \<Rightarrow> 'v set \<Rightarrow> 
                                 ('v * 'v) \<Rightarrow> 'v" where 
  "relevant_endpoint L V e = (if L (fst e) = 1 then fst e else snd e)"

section \<open>Lemmas\<close>

lemma definition_of_range:
  "endpoint_inV V1 ` matching_i 1 V E M L = 
  { v. \<exists> e \<in> matching_i 1 V E M L. endpoint_inV V1 e = v }" by auto

lemma matching_i_edges_as_sets:
  "edge_as_set ` matching_i i V E M L = 
  { e1. \<exists> (u, v) \<in> matching_i i V E M L. edge_as_set (u, v) = e1}" by auto

lemma matching_disjointness:
  assumes "matching V E M"
  assumes "e1 \<in> M"
  assumes "e2 \<in> M"
  assumes "e1 \<noteq> e2"
  shows  "edge_as_set e1 \<inter> edge_as_set e2 = {}"
  using assms 
  by (auto simp add: edge_as_set_def disjoint_edges_def matching_def)

lemma expand_set_containment:
  assumes "matching V E M"
  assumes "e \<in> M"
  shows "e \<in> E"
  using assms
  by (auto simp add:matching_def)

theorem injectivity:
  assumes is_osc: "OSC L E"
  assumes is_m: "matching V E M"
  assumes e1_in_M1: "e1 \<in> matching_i 1 V E M L"
      and e2_in_M1: "e2 \<in> matching_i 1 V E M L"
  assumes diff: "(e1 \<noteq> e2)"
  shows "endpoint_inV {v \<in> V. L v = 1} e1 \<noteq> endpoint_inV {v \<in> V. L v = 1} e2"
proof -
  from e1_in_M1 have "e1 \<in> M" by (auto simp add: matching_i_def)
  moreover
  from e2_in_M1 have "e2 \<in> M" by (auto simp add: matching_i_def)
  ultimately
  have disjoint_edge_sets: "edge_as_set e1 \<inter> edge_as_set e2 = {}" 
    using diff is_m matching_disjointness by fast
  then show ?thesis by (auto simp add: edge_as_set_def endpoint_inV_def)
qed

subsection \<open>\<open>|M1| \<le> n1\<close>\<close>

lemma card_M1_le_NVL1: 
  assumes "matching V E M"
  assumes "OSC L E"
  shows "card (matching_i 1 V E M L) \<le> ( N V L 1)"
proof -
  let ?f = "endpoint_inV {v \<in> V. L v = 1}"
  let ?A = "matching_i 1 V E M L"
  let ?B = "{v \<in> V. L v = 1}"
  have "inj_on ?f ?A" using assms injectivity
    unfolding inj_on_def by blast
  moreover have "?f ` ?A \<subseteq> ?B"
  proof -
    {
      fix e assume "e \<in> matching_i 1 V E M L"
      then have "endpoint_inV {v \<in> V. L v = 1} e \<in> {v \<in> V. L v = 1}"
        using assms
        by (auto simp add: endpoint_inV_def matching_def
          matching_i_def OSC_def finite_graph_def definition_of_range)
    }
    then show ?thesis using assms definition_of_range by blast
  qed
  moreover have "finite ?B" using assms
    by (simp add: matching_def finite_graph_def)
  ultimately show ?thesis unfolding N_def by (rule card_inj_on_le)
qed

lemma edge_as_set_inj_on_Mi: 
  assumes "matching V E M"
  shows "inj_on edge_as_set (matching_i i V E M L)"
  using assms
  unfolding inj_on_def edge_as_set_def matching_def
    disjoint_edges_def matching_i_def 
  by blast

lemma card_Mi_eq_card_edge_as_set_Mi:
  assumes "matching V E M"
  shows "card (matching_i i V E M L) = card (edge_as_set` matching_i i V E M L)"
  (is "card ?Mi = card (?f ` _)")
proof -
  from assms have "bij_betw ?f ?Mi (?f ` ?Mi)"
    by (simp add: bij_betw_def matching_i_edges_as_sets edge_as_set_inj_on_Mi)
  then show ?thesis by (rule bij_betw_same_card)
qed

lemma card_edge_as_set_Mi_twice_card_partitions:
  assumes "OSC L E \<and> matching V E M \<and> i > 1"
  shows "2 * card (edge_as_set`matching_i i V E M L) 
  = card (V_i i V E M L)" (is "2 * card ?C = card ?Vi")
proof -
  from assms have 1: "finite (\<Union> ?C)" 
    by (auto simp add: matching_def finite_graph_def 
      matching_i_def edge_as_set_def finite_subset)
  show ?thesis unfolding V_i_def
  proof (rule card_partition)
    show "finite ?C" using 1 by (rule finite_UnionD)
  next
    show "finite (\<Union> ?C)" using 1 .
  next
    fix c assume "c \<in> ?C" then show "card c = 2"
    proof (rule imageE)
      fix x 
      assume 2: "c = edge_as_set x" and 3: "x \<in> matching_i i V E M L"
      with assms have "x \<in> E" 
        unfolding matching_i_def matching_def by blast
      then have "fst x \<noteq> snd x" using assms 3 
        by (auto simp add: matching_def finite_graph_def)
      with 2 show ?thesis by (auto simp add: edge_as_set_def)
    qed
  next
    fix x1 x2
    assume 4: "x1 \<in> ?C" and 5: "x2 \<in> ?C" and 6: "x1 \<noteq> x2"
    {
      fix e1 e2
      assume 7: "x1 = edge_as_set e1" "e1 \<in> matching_i i V E M L"
        "x2 = edge_as_set e2" "e2 \<in> matching_i i V E M L"
      from assms have "matching V E M" by simp
      moreover
      from 7 assms have "e1 \<in> M" and "e2 \<in> M"
        by (simp_all add: matching_i_def)
      moreover from 6 7 have "e1 \<noteq> e2" by blast
      ultimately have "x1 \<inter> x2 = {}" unfolding 7 
        by (rule matching_disjointness)
    }
    with 4 5 show "x1 \<inter> x2 = {}" by clarsimp
  qed
qed

lemma card_Mi_twice_card_Vi:
  assumes "OSC L E \<and> matching V E M \<and> i > 1"
  shows "2 * card (matching_i i V E M L) = card (V_i i V E M L)"
proof -
  from assms have "finite (V_i i V E M L)"
    by (auto simp add: edge_as_set_def finite_subset
      matching_def finite_graph_def V_i_def matching_i_def )
  with assms show ?thesis 
    by (simp add: card_Mi_eq_card_edge_as_set_Mi 
      card_edge_as_set_Mi_twice_card_partitions V_i_def)
qed

lemma card_Mi_le_floor_div_2_Vi:
  assumes "OSC L E \<and> matching V E M \<and> i > 1"
  shows "card (matching_i i V E M L) \<le> (card (V_i i V E M L)) div 2"
  using card_Mi_twice_card_Vi[OF assms]
  by arith

lemma card_Vi_le_NVLi:
  assumes "i>1 \<and> matching V E M"
  shows "card (V_i i V E M L) \<le> N V L i"
  unfolding N_def
proof (rule card_mono)
  show "finite {v \<in> V. L v = i}" using assms 
    by (simp add: matching_def finite_graph_def)
next
  let ?A = "edge_as_set ` matching_i i V E M L"
  let ?C = "{v \<in> V. L v = i}" 
  show "V_i i V E M L \<subseteq> ?C" using assms unfolding V_i_def
  proof (intro Union_least)
    fix X assume "X \<in> ?A"
    with assms have "\<exists>x \<in> matching_i i V E M L. edge_as_set x = X"
      by (simp add: matching_i_edges_as_sets)
    with assms show "X \<subseteq> ?C" 
      unfolding finite_graph_def matching_def
        matching_i_def edge_as_set_def by blast
  qed
qed

subsection \<open>\<open>|Mi| \<le> \<lfloor>ni/2\<rfloor>\<close>\<close>

lemma card_Mi_le_floor_div_2_NVLi:
  assumes "OSC L E \<and> matching V E M \<and> i > 1"
  shows "card (matching_i i V E M L) \<le> (N V L i) div 2"
proof -  
  from assms have "card (V_i i V E M L) \<le> (N V L i)"
    by (simp add: card_Vi_le_NVLi) 
  then have "card (V_i i V E M L) div 2 \<le> (N V L i) div 2"
    by simp
  moreover from assms have 
    "card (matching_i i V E M L) \<le> card (V_i i V E M L) div 2"
    by (intro card_Mi_le_floor_div_2_Vi)
  ultimately show ?thesis by auto
qed
subsection \<open>\<open>|M| \<le> \<Sum>|Mi|\<close>\<close>
lemma card_M_le_sum_card_Mi: 
assumes "matching V E M" and "OSC L E"
shows "card M \<le> (\<Sum> i \<in> L`V. card (matching_i i V E M L))"
  (is "card _ \<le> ?CardMi")
proof -
  let ?UnMi = "\<Union>x \<in> L`V. matching_i x V E M L"
  from assms have 1: "finite ?UnMi"
    by (auto simp add: matching_def 
      finite_graph_def matching_i_def finite_subset)
  {
    fix e assume e_inM: "e \<in> M"
    let ?v = "relevant_endpoint L V e"
    have 1: "e \<in> matching_i (L ?v) V E M L" using assms e_inM
      proof cases
        assume "L (fst e) = 1"
        thus ?thesis using assms e_inM 
          by (simp add: relevant_endpoint_def matching_i_def)
      next
        assume a: "L (fst e) \<noteq> 1" 
        have "L (fst e) = 1 \<or> L (snd e) = 1 
          \<or>  (L (fst e) = L (snd e) \<and> L (fst e) >1)"
          using assms e_inM unfolding OSC_def 
          by (blast intro: expand_set_containment)
        thus ?thesis using assms e_inM a 
          by (auto simp add: relevant_endpoint_def matching_i_def)
      qed
      have 2: "?v \<in> V" using assms e_inM 
        by (auto simp add: matching_def 
          relevant_endpoint_def matching_i_def finite_graph_def)
      then have "\<exists> v \<in> V. e \<in> matching_i (L v) V E M L" using assms 1 2
        by (intro bexI) 
    }
    with assms have "M \<subseteq> ?UnMi" by (auto)
    with assms and 1 have "card M \<le> card ?UnMi" by (intro card_mono)
    moreover from assms have "card ?UnMi = ?CardMi"
    proof (intro card_UN_disjoint) 
      show "finite (L`V)" using assms 
        by (simp add: matching_def finite_graph_def)
    next 
      show "\<forall>i\<in>L`V. finite (matching_i i V E M L)" using assms
        unfolding matching_def finite_graph_def matching_i_def
        by (blast intro: finite_subset)
    next 
      show "\<forall>i \<in> L`V. \<forall>j \<in> L`V. i \<noteq> j \<longrightarrow> 
        matching_i i V E M L \<inter> matching_i j V E M L = {}" using assms
        by (auto simp add: matching_i_def)
    qed
  ultimately show ?thesis by simp
qed

theorem card_M_le_weight_NVLi:
  assumes "matching V E M" and "OSC L E"
  shows "card M \<le> weight {i \<in> L ` V. i > 1} (N V L)" (is "_ \<le> ?W")
proof -
  let ?M01 = "\<Sum>i| i \<in> L`V \<and> (i=1 \<or> i=0). card (matching_i i V E M L)"
  let ?Mgr1 = "\<Sum>i| i \<in> L`V \<and> 1 < i. card (matching_i i V E M L)"
  let ?Mi = "\<Sum> i\<in>L`V. card (matching_i i V E M L)"
  have "card M \<le> ?Mi" using assms by (rule card_M_le_sum_card_Mi) 
  moreover
  have "?Mi \<le> ?W"
  proof -
    let ?A = "{i \<in> L ` V. i = 1 \<or> i = 0}"
    let ?B = "{i \<in> L ` V. 1 < i}"
    let ?g = "\<lambda> i. card (matching_i i V E M L)"
    let ?set01 = "{ i. i : L ` V & (i = 1 | i = 0)}"
    have a: "L ` V = ?A \<union> ?B" using assms by auto
    have "finite V" using assms 
      by (simp add: matching_def finite_graph_def)
    have b: "sum ?g (?A \<union> ?B) = sum ?g ?A + sum ?g ?B"
      using assms \<open>finite V\<close> by (auto intro: sum.union_disjoint)    
    have 1: "?Mi = ?M01+ ?Mgr1" using assms a b 
      by (simp add: matching_def finite_graph_def)
    moreover
    have 0: "card (matching_i 0 V E M L) = 0" using assms
      by (simp add: matching_i_def)
      have 2: "?M01 \<le> N V L 1" 
      proof cases
        assume a: "1 \<in> L`V"
        have "?M01 = card (matching_i 1 V E M L)" 
        proof cases
          assume b: "0 \<in> L`V"
          with a assms have  "?set01 = {0, 1}" by blast
          thus ?thesis using assms 0 by simp
        next
          assume b: "0 \<notin> L`V"
          with a have "?set01 = {1}" by (auto simp del:One_nat_def)
          thus ?thesis by simp
        qed
        thus ?thesis using assms a 
          by (simp del: One_nat_def, intro card_M1_le_NVL1)
      next
        assume a: "1 \<notin> L`V"
        show ?thesis
        proof cases
          assume b: "0 \<in> L`V"
          with a assms have  "?set01 = {0}" by (auto simp del:One_nat_def)
          thus ?thesis using assms 0 by auto
        next
          assume b: "0 \<notin> L`V"
          with a have "?set01 = {}" by (auto simp del:One_nat_def)
            then have "?M01 = (\<Sum>i\<in>{}. card (matching_i i V E M L))" by auto
            thus ?thesis by simp
          qed
        qed
      moreover
      have 3: "?Mgr1 \<le> (\<Sum>i|i\<in>L`V \<and> 1 < i. N V L i div 2)" using assms 
        by (intro sum_mono card_Mi_le_floor_div_2_NVLi, simp)
    ultimately
    show ?thesis using 1 2 3 assms by (simp add: weight_def)
  qed
  ultimately show ?thesis by simp
qed

section \<open>Final Theorem\<close>
text\<open>The following theorem is due to Edmond~\cite{Edmonds:matching}:\<close>

theorem maximum_cardinality_matching:
  assumes "matching V E M" and "OSC L E"
  and "card M = weight {i \<in> L ` V. i > 1} (N V L)"
  and "matching V E M'"
  shows "card M' \<le> card M"
  using assms card_M_le_weight_NVLi
  by simp

text\<open>The widely used algorithmic library LEDA has a certifying algorithm for maximum cardinality matching.
This Isabelle proof is part of the work done to verify the checker of this certifying algorithm. For more information see \cite{VerificationofCertifyingComputations}.\<close>
end
