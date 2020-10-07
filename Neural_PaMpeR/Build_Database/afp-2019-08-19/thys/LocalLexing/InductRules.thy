theory InductRules
imports Main
begin

lemma disjCases2[consumes 1, case_names 1 2]:
  assumes AB: "A \<or> B"
  and AP: "A \<Longrightarrow> P"
  and BP: "B \<Longrightarrow> P"
  shows "P"
proof -
  from AB AP BP show ?thesis by blast
qed

lemma disjCases3[consumes 1, case_names 1 2 3]:
  assumes AB: "A \<or> B \<or> C"
  and AP: "A \<Longrightarrow> P"
  and BP: "B \<Longrightarrow> P"
  and CP: "C \<Longrightarrow> P"
  shows "P"
proof -
  from AB AP BP CP show ?thesis by blast
qed

lemma disjCases4[consumes 1, case_names 1 2 3 4]:
  assumes AB: "A \<or> B \<or> C \<or> D"
  and AP: "A \<Longrightarrow> P"
  and BP: "B \<Longrightarrow> P"
  and CP: "C \<Longrightarrow> P"
  and DP: "D \<Longrightarrow> P"
  shows "P"
proof -
  from AB AP BP CP DP show ?thesis by blast
qed

lemma disjCases5[consumes 1, case_names 1 2 3 4 5]:
  assumes AB: "A \<or> B \<or> C \<or> D \<or> E"
  and AP: "A \<Longrightarrow> P"
  and BP: "B \<Longrightarrow> P"
  and CP: "C \<Longrightarrow> P"
  and DP: "D \<Longrightarrow> P"
  and EP: "E \<Longrightarrow> P"
  shows "P"
proof -
  from AB AP BP CP DP EP show ?thesis by blast
qed

lemma minimal_witness_ex:
  assumes k: "P (k::nat)"
  shows "\<exists> k0. k0 \<le> k \<and> P k0 \<and> (\<forall> k. k < k0 \<longrightarrow> \<not> (P k))" 
proof -
  let ?K = "{ h. h \<le> k \<and> P h }" 
  have finite_K: "finite ?K" by auto
  have "k \<in> ?K" by (simp add: k)
  then have nonempty_K: "?K \<noteq> {}" by auto
  let ?k = "Min ?K"
  have witness: "?k \<le> k \<and> P ?k"
    by (metis (mono_tags, lifting) Min_in finite_K mem_Collect_eq nonempty_K)
  have minimal: "\<forall> h. h < ?k \<longrightarrow> \<not> (P h)" 
    by (metis Min_le witness dual_order.strict_implies_order 
        dual_order.trans finite_K leD mem_Collect_eq)
  from witness minimal show ?thesis by metis 
qed

lemma minimal_witness[consumes 1, case_names Minimal]:
  assumes "P (k::nat)"
  and "\<And> K. K \<le> k \<Longrightarrow> P K \<Longrightarrow> (\<And> k. k < K \<Longrightarrow> \<not> (P k)) \<Longrightarrow> Q"
  shows "Q"
proof -
  from assms minimal_witness_ex show ?thesis by metis
qed

lemma ex_minimal_witness[consumes 1, case_names Minimal]:
  assumes "\<exists> k. P (k::nat)"
  and "\<And> K. P K \<Longrightarrow> (\<And> k. k < K \<Longrightarrow> \<not> (P k)) \<Longrightarrow> Q"
  shows "Q"
proof -
  from assms minimal_witness_ex show ?thesis by metis
qed

end
