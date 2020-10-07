(* Title:      Relation Algebra
   Author:     Alasdair Armstrong, Simon Foster, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Vectors\<close>

theory Relation_Algebra_Vectors
  imports Relation_Algebra
begin

text \<open>Vectors can be used for modelling sets of states. In this section we
follow Maddux's book to derive some of their most important properties.\<close>

context relation_algebra
begin

definition is_vector :: "'a \<Rightarrow> bool"
  where "is_vector x \<equiv> x = x ; 1"

lemma vector_compl: "is_vector x \<Longrightarrow> is_vector (-x)"
by (metis one_compl is_vector_def)

lemma vector_add: "\<lbrakk>is_vector x; is_vector y\<rbrakk> \<Longrightarrow> is_vector (x + y)"
by (metis comp_distr is_vector_def)

lemma vector_mult: "\<lbrakk>is_vector x; is_vector y\<rbrakk> \<Longrightarrow> is_vector (x \<cdot> y)"
by (metis ra_1 is_vector_def)

lemma vector_comp: "\<lbrakk>is_vector x; is_vector y\<rbrakk> \<Longrightarrow> is_vector (x ; y)"
by (metis comp_assoc is_vector_def)

lemma vector_1: "is_vector x \<Longrightarrow> (x \<cdot> y) ; z = x \<cdot> y ; z"
by (metis inf.commute ra_1 is_vector_def)

lemma vector_1_comm: "is_vector y \<Longrightarrow> (x \<cdot> y) ; z = x ; z \<cdot> y"
by (metis ra_1 is_vector_def)

lemma vector_2: "is_vector y \<Longrightarrow> (x \<cdot> y\<^sup>\<smile>) ; z = x ; (y \<cdot> z)"
by (metis inf.commute ra_2 is_vector_def)

lemma vector_2_var: "is_vector y \<Longrightarrow> (x \<cdot> y\<^sup>\<smile>) ; z = (x \<cdot> y\<^sup>\<smile>) ; (y \<cdot> z)"
by (metis inf.left_idem vector_2)

lemma vector_idem [simp]: "is_vector x \<Longrightarrow> x ; x = x"
by (metis inf_absorb2 inf_top_left maddux_21 vector_1_comm)

lemma vector_rectangle [simp]: "is_vector x \<Longrightarrow> x ; 1 ; x = x"
by (metis vector_idem is_vector_def)

lemma vector_3 [simp]: "is_vector x \<Longrightarrow> (x \<cdot> 1') ; y = x \<cdot> y"
by (metis inf.commute mult.left_neutral vector_1)

end (* relation_algebra *)

end

