theory FSet_More
imports  "HOL-Library.FSet"
begin

lemma Suc_pred_image[simp]: "0 \<notin> P \<Longrightarrow> (\<lambda>x. Suc (x - Suc 0)) ` P = P"
    unfolding image_def by safe (metis Suc_pred neq0_conv)+

context includes fset.lifting begin

lemmas Suc_pred_fimage[simp] = Suc_pred_image[Transfer.transferred]

end

lemma ffilter_eq_fempty_iff:
  "ffilter P X = {||} \<longleftrightarrow> (\<forall>x. x |\<in>| X \<longrightarrow> \<not> P x)"
  "{||} = ffilter P X \<longleftrightarrow> (\<forall>x. x |\<in>| X \<longrightarrow> \<not> P x)"
  by auto

lemma max_ffilter_below[simp]: "\<lbrakk>x |\<in>| P; x < n\<rbrakk> \<Longrightarrow>
  max n (Suc (fMax (ffilter (\<lambda>i. i < n) P))) = n"
  by (metis max.absorb1 Suc_leI fMax_in fempty_iff ffmember_filter)

lemma fMax_boundedD:
  "\<lbrakk>fMax P < n; x |\<in>| P\<rbrakk> \<Longrightarrow> x < n"
  "\<lbrakk>fMax P \<le> n; n |\<notin>| P; x |\<in>| P\<rbrakk> \<Longrightarrow> x < n"
  by (metis fMax_ge le_less_trans, metis fMax_ge leD neqE order.strict_trans2)

lemma fMax_ffilter_less: "x |\<in>| P \<Longrightarrow> x < n \<Longrightarrow> fMax (ffilter (\<lambda>i. i < n) P) < n"
  by (metis fMax_in ffilter_eq_fempty_iff(2) ffmember_filter)

end
