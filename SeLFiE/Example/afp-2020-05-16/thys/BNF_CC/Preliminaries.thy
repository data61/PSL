(* Author: Andreas Lochbihler, ETH Zurich
   Author: Joshua Schneider, ETH Zurich *)

section \<open>Preliminaries\<close>

theory Preliminaries imports
  Main
begin

alias Grp = BNF_Def.Grp
alias vimage2p = BNF_Def.vimage2p

lemma Domainp_conversep: "Domainp R\<inverse>\<inverse> = Rangep R"
  by auto

lemma Grp_apply: "Grp A f x y \<longleftrightarrow> y = f x \<and> x \<in> A"
  by (simp add: Grp_def)

lemma conversep_Grp_id: "(Grp A id)\<inverse>\<inverse> = Grp A id"
  by (auto simp add: fun_eq_iff Grp_apply)

lemma eq_onp_compp_Grp: "eq_onp P OO Grp A f = Grp (Collect P \<inter> A) f"
  by (auto simp add: fun_eq_iff eq_onp_def elim: GrpE intro: GrpI)


consts relcompp_witness :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> 'a \<times> 'c \<Rightarrow> 'b"

specification (relcompp_witness)
  relcompp_witness1: "(A OO B) (fst xy) (snd xy) \<Longrightarrow> A (fst xy) (relcompp_witness A B xy)"
  relcompp_witness2: "(A OO B) (fst xy) (snd xy) \<Longrightarrow> B (relcompp_witness A B xy) (snd xy)"
  apply(fold all_conj_distrib)
  apply(rule choice allI)+
  apply(auto)
  done

lemmas relcompp_witness[of _ _ "(x, y)" for x y, simplified] = relcompp_witness1 relcompp_witness2

hide_fact (open) relcompp_witness1 relcompp_witness2

lemma relcompp_witness_eq [simp]: "relcompp_witness (=) (=) (x, x) = x"
  using relcompp_witness(1)[of "(=)" "(=)" x x] by (simp add: eq_OO)


lemma Quotient_equiv_abs1: "\<lbrakk> Quotient R Abs Rep T; R x y \<rbrakk> \<Longrightarrow> T x (Abs y)"
  unfolding Quotient_alt_def2 by blast

lemma Quotient_equiv_abs2: "\<lbrakk> Quotient R Abs Rep T; R x y \<rbrakk> \<Longrightarrow> T y (Abs x)"
  unfolding Quotient_alt_def2 by blast

lemma Quotient_rep_equiv1: "\<lbrakk> Quotient R Abs Rep T; T a b \<rbrakk> \<Longrightarrow> R a (Rep b)"
  unfolding Quotient_alt_def3 by blast

lemma Quotient_rep_equiv2: "\<lbrakk> Quotient R Abs Rep T; T a b \<rbrakk> \<Longrightarrow> R (Rep b) a"
  unfolding Quotient_alt_def3 by blast

end
