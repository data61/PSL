theory Partial_Equivalence_Relation
imports Main
begin

subsection \<open>Partial Equivalence Relations\<close>
text \<open>
  The abstract datatype for a union-find structure is a partial equivalence
  relation.
\<close>

definition "part_equiv R \<equiv> sym R \<and> trans R"

lemma part_equivI[intro?]: "\<lbrakk>sym R; trans R\<rbrakk> \<Longrightarrow> part_equiv R" 
  by (simp add: part_equiv_def)

lemma part_equiv_refl:
  "part_equiv R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (x,x)\<in>R"
  "part_equiv R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (y,y)\<in>R"
  by (metis part_equiv_def symD transD)+

lemma part_equiv_sym: "part_equiv R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (y,x)\<in>R"
  by (metis part_equiv_def symD)

lemma part_equiv_trans: "part_equiv R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (y,z)\<in>R \<Longrightarrow> (x,z)\<in>R"
  by (metis part_equiv_def transD)

lemma part_equiv_trans_sym: 
  "\<lbrakk> part_equiv R; (a,b)\<in>R; (c,b)\<in>R \<rbrakk> \<Longrightarrow> (a,c)\<in>R"
  "\<lbrakk> part_equiv R; (a,b)\<in>R; (a,c)\<in>R \<rbrakk> \<Longrightarrow> (b,c)\<in>R"
  apply (metis part_equiv_sym part_equiv_trans)+
  done

text \<open>We define a shortcut for symmetric closure.\<close>
definition "symcl R \<equiv> R \<union> R\<inverse>"

lemma sym_symcl[simp, intro!]: "sym (symcl R)"
  by (metis sym_Un_converse symcl_def)
lemma sym_trans_is_part_equiv[simp, intro!]: "part_equiv ((symcl R)\<^sup>*)"
  by (metis part_equiv_def sym_rtrancl sym_symcl trans_rtrancl)

text \<open>We also define a shortcut for melding the equivalence classes of
  two given elements\<close>
definition per_union where "per_union R a b \<equiv> R \<union> 
  { (x,y). (x,a)\<in>R \<and> (y,b)\<in>R } \<union> { (y,x). (x,a)\<in>R \<and> (y,b)\<in>R }"

lemma union_part_equivp: 
  "part_equiv R \<Longrightarrow> part_equiv (per_union R a b)"
  apply rule
  unfolding per_union_def
  apply (rule symI)
  apply (auto dest: part_equiv_sym) []

  apply (rule transI)
  apply (auto dest: part_equiv_trans part_equiv_trans_sym)
  done

lemma per_union_cmp: 
  "\<lbrakk> part_equiv R; (l,j)\<in>R \<rbrakk> \<Longrightarrow> per_union R l j = R"
  unfolding per_union_def by (auto dest: part_equiv_trans_sym)

lemma per_union_same[simp]: "part_equiv R \<Longrightarrow> per_union R l l = R"
  unfolding per_union_def by (auto dest: part_equiv_trans_sym)

lemma per_union_commute[simp]: "per_union R i j = per_union R j i"
  unfolding per_union_def by auto

lemma per_union_dom[simp]: "Domain (per_union R i j) = Domain R"
  unfolding per_union_def by auto

lemma per_classes_dj: 
  "\<lbrakk>part_equiv R; (i,j)\<notin>R\<rbrakk> \<Longrightarrow> R``{i} \<inter> R``{j} = {}"
  by (auto dest: part_equiv_trans_sym)

lemma per_class_in_dom: "\<lbrakk>part_equiv R\<rbrakk> \<Longrightarrow> R``{i} \<subseteq> Domain R"
  by (auto dest: part_equiv_trans_sym)

end
