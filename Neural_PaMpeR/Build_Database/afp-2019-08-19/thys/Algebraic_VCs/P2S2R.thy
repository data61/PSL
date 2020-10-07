(* Title: Isomorphisms Betweeen Predicates, Sets and Relations *}
   Author: Victor Gomes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Isomorphisms Between Predicates, Sets and Relations\<close>

theory P2S2R
imports Main

begin    

notation relcomp (infixl ";" 70)
notation inf (infixl "\<sqinter>" 70)  
notation sup (infixl "\<squnion>" 65)
notation Id_on ("s2r")
notation Domain ("r2s")
notation Collect ("p2s")

definition rel_n :: "'a rel \<Rightarrow> 'a rel" where 
  "rel_n  \<equiv> (\<lambda>X. Id \<inter> - X)"  

lemma subid_meet: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> R \<inter> S = R ; S"
  by blast

subsection\<open>Isomorphism Between Sets and Relations\<close>

lemma srs: "r2s \<circ> s2r = id"
  by auto

lemma rsr: "R \<subseteq> Id \<Longrightarrow> s2r (r2s R) = R"
  by (auto simp: Id_def Id_on_def Domain_def) 

lemma s2r_inj: "inj s2r"
  by (metis Domain_Id_on injI)

lemma r2s_inj: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2s R = r2s S \<Longrightarrow> R = S"
  by (metis rsr)

lemma s2r_surj: "\<forall>R \<subseteq> Id. \<exists>A. R = s2r A"
  using rsr by auto
 
lemma r2s_surj: "\<forall>A. \<exists>R \<subseteq> Id. A = r2s R"
  by (metis Domain_Id_on Id_onE pair_in_Id_conv subsetI)

lemma s2r_union_hom: "s2r (A \<union> B) = s2r A \<union> s2r B"
  by (simp add: Id_on_def)

lemma s2r_inter_hom: "s2r (A \<inter> B) = s2r A \<inter> s2r B"
  by (auto simp: Id_on_def)  

lemma s2r_inter_hom_var: "s2r (A \<inter> B) = s2r A ; s2r B"
  by (auto simp: Id_on_def)

lemma s2r_compl_hom: "s2r (- A) = rel_n (s2r A)"
  by (auto simp add: rel_n_def)

lemma r2s_union_hom: "r2s (R \<union> S) = r2s R \<union> r2s S"
  by auto

lemma r2s_inter_hom: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2s (R \<inter> S) = r2s R \<inter> r2s S"
  by auto

lemma r2s_inter_hom_var: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2s (R ; S) = r2s R \<inter> r2s S"
  by (metis r2s_inter_hom subid_meet)

lemma r2s_ad_hom: "R \<subseteq> Id \<Longrightarrow> r2s (rel_n R) = - r2s R"
  by (metis r2s_surj rsr s2r_compl_hom)

subsection \<open>Isomorphism Between Predicates and Sets\<close>

type_synonym 'a pred = "'a \<Rightarrow> bool"

definition s2p :: "'a set \<Rightarrow> 'a pred" where
  "s2p S = (\<lambda>x. x \<in> S)"

lemma sps [simp]: "s2p \<circ> p2s = id" 
  by (intro ext, simp add: s2p_def)

lemma psp [simp]: "p2s \<circ> s2p = id"
  by (intro ext, simp add: s2p_def)

lemma s2p_bij: "bij s2p"
  using o_bij psp sps by blast

lemma p2s_bij: "bij p2s"
  using o_bij psp sps by blast

lemma s2p_compl_hom: "s2p (- A) = - (s2p A)"
  by (metis Collect_mem_eq comp_eq_dest_lhs id_apply sps uminus_set_def)
 
lemma s2p_inter_hom: "s2p (A \<inter> B) = (s2p A) \<sqinter> (s2p B)"
  by (metis Collect_mem_eq comp_eq_dest_lhs id_apply inf_set_def sps)

lemma s2p_union_hom: "s2p (A \<union> B) = (s2p A) \<squnion> (s2p B)"
  by (auto simp: s2p_def)

lemma p2s_neg_hom: "p2s (- P) = - (p2s P)"
  by fastforce

lemma p2s_conj_hom: "p2s (P \<sqinter> Q) = p2s P \<inter> p2s Q"
  by blast

lemma p2s_disj_hom: "p2s (P \<squnion> Q) = p2s P \<union> p2s Q"
  by blast

subsection \<open>Isomorphism Between Predicates and Relations\<close>

definition p2r :: "'a pred \<Rightarrow> 'a rel" where
  "p2r P = {(s,s) |s. P s}"

definition r2p :: "'a rel \<Rightarrow> 'a pred" where
  "r2p R = (\<lambda>x. x \<in> Domain R)"

lemma p2r_subid: "p2r P \<subseteq> Id"
  by (simp add: p2r_def subset_eq)

lemma p2s2r: "p2r = s2r \<circ> p2s"
proof (intro ext)
  fix P :: "'a pred"
  have "{(a, a) |a. P a} = {(b, a). b = a \<and> P b}"
    by blast
  thus "p2r P = (s2r \<circ> p2s) P"
    by (simp add: Id_on_def' p2r_def)
qed

lemma r2s2p: "r2p = s2p \<circ> r2s"
  by (intro ext, simp add: r2p_def s2p_def)

lemma prp [simp]: "r2p \<circ> p2r = id"
  by (intro ext, simp add: p2s2r r2p_def)

lemma rpr: "R \<subseteq> Id \<Longrightarrow> p2r (r2p R) = R"
  by (metis comp_apply id_apply p2s2r psp r2s2p rsr)

lemma p2r_inj: "inj p2r"
  by (metis comp_eq_dest_lhs id_apply injI prp)

lemma r2p_inj: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2p R = r2p S \<Longrightarrow> R = S"
  by (metis rpr)

lemma p2r_surj: "\<forall> R \<subseteq> Id. \<exists>P. R = p2r P"
  using rpr by auto

lemma r2p_surj: "\<forall>P. \<exists>R \<subseteq> Id. P = r2p R"
  by (metis comp_apply id_apply p2r_subid prp)

lemma p2r_neg_hom: "p2r (- P) = rel_n (p2r P)"
  by (simp add: p2s2r p2s_neg_hom s2r_compl_hom)

lemma p2r_conj_hom [simp]: "p2r P \<inter> p2r Q = p2r (P \<sqinter> Q)"
  by (simp add: p2s2r p2s_conj_hom s2r_inter_hom)

lemma p2r_conj_hom_var [simp]: "p2r P ; p2r Q = p2r (P \<sqinter> Q)"
  by (simp add: p2s2r p2s_conj_hom s2r_inter_hom_var)

lemma p2r_id_neg [simp]: "Id \<inter> - p2r p = p2r (-p)"
  by (auto simp: p2r_def)

lemma [simp]: "p2r bot = {}"
  by (auto simp: p2r_def)

lemma p2r_disj_hom [simp]: "p2r P \<union> p2r Q = p2r (P \<squnion> Q)"
  by (simp add: p2s2r p2s_disj_hom s2r_union_hom)

lemma r2p_ad_hom: "R \<subseteq> Id \<Longrightarrow> r2p (rel_n R) = - (r2p R)"
  by (simp add: r2s2p r2s_ad_hom s2p_compl_hom)

lemma r2p_inter_hom: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2p (R \<inter> S) = (r2p R) \<sqinter> (r2p S)"
  by (simp add: r2s2p r2s_inter_hom s2p_inter_hom)

lemma r2p_inter_hom_var: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2p (R ; S) = (r2p R) \<sqinter> (r2p S)"
  by (simp add: r2s2p r2s_inter_hom_var s2p_inter_hom)

lemma rel_to_pred_union_hom: "R \<subseteq> Id \<Longrightarrow> S \<subseteq> Id \<Longrightarrow> r2p (R \<union> S) = (r2p R) \<squnion> (r2p S)"
  by (simp add: Domain_Un_eq r2s2p s2p_union_hom)

end
