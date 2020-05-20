subsection \<open> ETP definitions \<close>

text \<open> We define Extended Trapdoor Permutations (ETPs) following \cite{DBLP:books/sp/17/Lindell17} and \cite{DBLP:books/cu/Goldreich2004}. 
In particular we consider the property of Hard Core Predicates (HCPs). \<close>

theory ETP imports
  CryptHOL.CryptHOL
begin

type_synonym ('index,'range) dist2 = "(bool \<times> 'index \<times> bool \<times> bool) \<Rightarrow> bool spmf"

type_synonym ('index,'range) advP2 = "'index \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('index,'range) dist2 \<Rightarrow> 'range \<Rightarrow> bool spmf"

locale etp =
  fixes I :: "('index \<times> 'trap) spmf" \<comment> \<open>samples index and trapdoor\<close>
    and domain :: "'index \<Rightarrow> 'range set" 
    and range :: "'index \<Rightarrow> 'range set"
    and F :: "'index \<Rightarrow> ('range \<Rightarrow> 'range)" \<comment> \<open>permutation\<close>
    and F\<^sub>i\<^sub>n\<^sub>v :: "'index \<Rightarrow> 'trap \<Rightarrow> 'range \<Rightarrow> 'range" \<comment> \<open>must be efficiently computable\<close>
    and B :: "'index \<Rightarrow> 'range \<Rightarrow> bool" \<comment> \<open>hard core predicate\<close>
  assumes dom_eq_ran: "y \<in> set_spmf I \<longrightarrow> domain (fst y) = range (fst y)"
    and finite_range: "y \<in> set_spmf I \<longrightarrow> finite (range (fst y))" 
    and non_empty_range: "y \<in> set_spmf I \<longrightarrow> range (fst y) \<noteq> {}" 
    and bij_betw: "y \<in> set_spmf I \<longrightarrow> bij_betw (F (fst y)) (domain (fst y)) (range (fst y))"
    and lossless_I: "lossless_spmf I"
    and F_f_inv: "y \<in> set_spmf I \<longrightarrow> x \<in> range (fst y) \<longrightarrow> F\<^sub>i\<^sub>n\<^sub>v (fst y) (snd y) (F (fst y) x) = x"
begin

definition S :: "'index \<Rightarrow> 'range spmf"
  where "S \<alpha> = spmf_of_set (range \<alpha>)"

lemma lossless_S: "y \<in> set_spmf I \<longrightarrow>  lossless_spmf (S (fst y))"
  by(simp add: lossless_spmf_def S_def finite_range non_empty_range)

lemma set_spmf_S [simp]: "y \<in> set_spmf I \<longrightarrow> set_spmf (S (fst y)) = range (fst y)" 
  by (simp add: S_def finite_range)

lemma f_inj_on: "y \<in> set_spmf I \<longrightarrow> inj_on (F (fst y)) (range (fst y))" 
  by(metis bij_betw_def bij_betw dom_eq_ran bij_betw_def bij_betw dom_eq_ran) 

lemma range_f: "y \<in> set_spmf I \<longrightarrow>  x \<in> range (fst y) \<longrightarrow> F (fst y) x \<in> range (fst y)" 
  by (metis bij_betw bij_betw dom_eq_ran bij_betwE)   

lemma f_inv_f [simp]: "y \<in> set_spmf I \<longrightarrow> x \<in> range (fst y) \<longrightarrow> F\<^sub>i\<^sub>n\<^sub>v (fst y) (snd y) (F (fst y) x) = x"
  by (metis bij_betw bij_betw_inv_into_left dom_eq_ran F_f_inv)

lemma f_inv_f' [simp]: "y \<in> set_spmf I \<longrightarrow> x \<in> range (fst y) \<longrightarrow> Hilbert_Choice.inv_into (range (fst y)) (F (fst y)) (F (fst y) x) = x" 
  by (metis bij_betw bij_betw_inv_into_left bij_betw dom_eq_ran)

lemma B_F_inv_rewrite: "(B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = (B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> y\<^sub>\<sigma>') = m1)) = m1" 
  by auto

lemma uni_set_samp: 
  assumes "y \<in> set_spmf I"
  shows "map_spmf (\<lambda> x. F (fst y) x) (S (fst y)) = (S (fst y))" 
(is "?lhs = ?rhs")
proof-
  have rhs: "?rhs = spmf_of_set (range (fst y))" 
    unfolding S_def by(simp)
  also have "map_spmf (\<lambda> x. F (fst y) x) (spmf_of_set (range (fst y))) = spmf_of_set ((\<lambda> x. F (fst y) x) ` (range (fst y)))"
    using f_inj_on assms 
    by (metis map_spmf_of_set_inj_on) 
  also have "(\<lambda> x. F (fst y) x) ` (range (fst y)) = range (fst y)"
    apply(rule endo_inj_surj) 
    using bij_betw
      by (auto simp add: bij_betw_def dom_eq_ran f_inj_on bij_betw finite_range assms)  
  finally show ?thesis by(simp add: rhs)
qed

text\<open>We define the security property of the hard core predicate (HCP) using a game.\<close>

definition HCP_game :: "('index,'range) advP2 \<Rightarrow>  bool \<Rightarrow> bool \<Rightarrow> ('index,'range) dist2 \<Rightarrow> bool spmf"
  where "HCP_game A = (\<lambda> \<sigma> b\<^sub>\<sigma> D. do {
    (\<alpha>, \<tau>) \<leftarrow> I;
    x \<leftarrow> S \<alpha>;
    b' \<leftarrow> A \<alpha> \<sigma> b\<^sub>\<sigma> D x;
    let b = B \<alpha> (F\<^sub>i\<^sub>n\<^sub>v \<alpha> \<tau> x);
    return_spmf (b = b')})"

definition "HCP_adv A \<sigma> b\<^sub>\<sigma> D = \<bar>((spmf (HCP_game A \<sigma> b\<^sub>\<sigma> D) True) - 1/2)\<bar>" 

end

end



