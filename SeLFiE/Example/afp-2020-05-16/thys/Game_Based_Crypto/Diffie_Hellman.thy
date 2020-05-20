(* Title: Diffie_Hellman.thy
  Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Specifying security using games\<close>

theory Diffie_Hellman imports
  CryptHOL.Cyclic_Group_SPMF
  CryptHOL.Computational_Model
begin

subsection \<open>The DDH game\<close>

locale ddh =
  fixes \<G> :: "'grp cyclic_group" (structure)
begin

type_synonym 'grp' adversary = "'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' \<Rightarrow> bool spmf"

definition ddh_0 :: "'grp adversary \<Rightarrow> bool spmf"
where "ddh_0 \<A> = do {
     x \<leftarrow> sample_uniform (order \<G>);
     y \<leftarrow> sample_uniform (order \<G>);
     \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] (x * y))
  }"

definition ddh_1 :: "'grp adversary \<Rightarrow> bool spmf"
where "ddh_1 \<A> = do {
     x \<leftarrow> sample_uniform (order \<G>);
     y \<leftarrow> sample_uniform (order \<G>);
     z \<leftarrow> sample_uniform (order \<G>);
     \<A> (\<^bold>g [^] x) (\<^bold>g [^] y) (\<^bold>g [^] z)
  }"

definition advantage :: "'grp adversary \<Rightarrow> real"
where "advantage \<A> = \<bar>spmf (ddh_0 \<A>) True - spmf (ddh_1 \<A>) True\<bar>"

definition lossless :: "'grp adversary \<Rightarrow> bool"
where "lossless \<A> \<longleftrightarrow> (\<forall>\<alpha> \<beta> \<gamma>. lossless_spmf (\<A> \<alpha> \<beta> \<gamma>))"

lemma lossless_ddh_0:
  "\<lbrakk> lossless \<A>; 0 < order \<G> \<rbrakk>
  \<Longrightarrow> lossless_spmf (ddh_0 \<A>)"
by(auto simp add: lossless_def ddh_0_def split_def Let_def)

lemma lossless_ddh_1:
  "\<lbrakk> lossless \<A>; 0 < order \<G> \<rbrakk>
  \<Longrightarrow> lossless_spmf (ddh_1 \<A>)"
by(auto simp add: lossless_def ddh_1_def split_def Let_def)

end

subsection \<open>The LCDH game\<close>

locale lcdh =
  fixes \<G> :: "'grp cyclic_group" (structure)
begin

type_synonym 'grp' adversary = "'grp' \<Rightarrow> 'grp' \<Rightarrow> 'grp' set spmf"

definition lcdh :: "'grp adversary \<Rightarrow> bool spmf"
where "lcdh \<A> = do { 
     x \<leftarrow> sample_uniform (order \<G>);
     y \<leftarrow> sample_uniform (order \<G>);
     zs \<leftarrow> \<A> (\<^bold>g [^] x) (\<^bold>g [^] y);
     return_spmf (\<^bold>g [^] (x * y) \<in> zs)
  }"

definition advantage :: "'grp adversary \<Rightarrow> real"
where "advantage \<A> = spmf (lcdh \<A>) True"

definition lossless :: "'grp adversary \<Rightarrow> bool"
where "lossless \<A> \<longleftrightarrow> (\<forall>\<alpha> \<beta>. lossless_spmf (\<A> \<alpha> \<beta>))"

lemma lossless_lcdh:
  "\<lbrakk> lossless \<A>; 0 < order \<G> \<rbrakk>
  \<Longrightarrow> lossless_spmf (lcdh \<A>)"
by(auto simp add: lossless_def lcdh_def split_def Let_def)

end

end
