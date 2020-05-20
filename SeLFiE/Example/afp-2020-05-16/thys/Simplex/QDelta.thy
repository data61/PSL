(* Authors: F. Maric, M. Spasic, R. Thiemann *)
section \<open>Rational Numbers Extended with Infinitesimal Element\<close>
theory QDelta
  imports  
    Abstract_Linear_Poly
    Simplex_Algebra 
begin

datatype QDelta = QDelta rat rat

primrec qdfst :: "QDelta \<Rightarrow> rat"
  where
    "qdfst (QDelta a b) = a"

primrec qdsnd :: "QDelta \<Rightarrow> rat"
  where
    "qdsnd (QDelta a b) = b"

lemma [simp]: "QDelta (qdfst qd) (qdsnd qd) = qd"
  by (cases qd) auto

lemma [simp]: "\<lbrakk>QDelta.qdsnd x = QDelta.qdsnd y; QDelta.qdfst y = QDelta.qdfst x\<rbrakk> \<Longrightarrow> x = y"
  by (cases x) auto

instantiation QDelta :: rational_vector
begin

definition zero_QDelta :: "QDelta"
  where
    "0 = QDelta 0 0"

definition plus_QDelta :: "QDelta \<Rightarrow> QDelta \<Rightarrow> QDelta"
  where
    "qd1 + qd2 = QDelta (qdfst qd1 + qdfst qd2) (qdsnd qd1 + qdsnd qd2)"

definition minus_QDelta :: "QDelta \<Rightarrow> QDelta \<Rightarrow> QDelta"
  where
    "qd1 - qd2 = QDelta (qdfst qd1 - qdfst qd2) (qdsnd qd1 - qdsnd qd2)"

definition uminus_QDelta :: "QDelta \<Rightarrow> QDelta"
  where
    "- qd = QDelta (- (qdfst qd)) (- (qdsnd qd))"

definition scaleRat_QDelta :: "rat \<Rightarrow> QDelta \<Rightarrow> QDelta"
  where
    "r *R qd = QDelta (r*(qdfst qd)) (r*(qdsnd qd))"

instance 
proof 
qed (auto simp add: plus_QDelta_def zero_QDelta_def uminus_QDelta_def minus_QDelta_def scaleRat_QDelta_def field_simps)
end

instantiation QDelta :: linorder
begin
definition less_eq_QDelta :: "QDelta \<Rightarrow> QDelta \<Rightarrow> bool"
  where
    "qd1 \<le> qd2 \<longleftrightarrow> (qdfst qd1 < qdfst qd2) \<or> (qdfst qd1 = qdfst qd2 \<and> qdsnd qd1 \<le> qdsnd qd2)"

definition less_QDelta :: "QDelta \<Rightarrow> QDelta \<Rightarrow> bool"
  where
    "qd1 < qd2 \<longleftrightarrow> (qdfst qd1 < qdfst qd2) \<or> (qdfst qd1 = qdfst qd2 \<and> qdsnd qd1 < qdsnd qd2)"

instance proof qed (auto simp add: less_QDelta_def less_eq_QDelta_def)
end

instantiation QDelta:: linordered_rational_vector
begin
instance proof qed (auto simp add: plus_QDelta_def less_QDelta_def scaleRat_QDelta_def mult_strict_left_mono mult_strict_left_mono_neg)
end

instantiation QDelta :: lrv
begin
definition one_QDelta where
  "one_QDelta = QDelta 1 0"
instance proof qed (auto simp add: one_QDelta_def zero_QDelta_def)
end

definition \<delta>0 :: "QDelta \<Rightarrow> QDelta \<Rightarrow> rat"
  where
    "\<delta>0 qd1 qd2 ==
    let c1 = qdfst qd1; c2 = qdfst qd2; k1 = qdsnd qd1; k2 = qdsnd qd2 in
      (if (c1 < c2 \<and> k1 > k2) then 
              (c2 - c1) / (k1 - k2) 
       else
               1
       )
    "

definition val :: "QDelta \<Rightarrow> rat \<Rightarrow> rat"
  where "val qd \<delta> = (qdfst qd) + \<delta> * (qdsnd qd)"

lemma val_plus: 
  "val (qd1 + qd2) \<delta> = val qd1 \<delta> + val qd2 \<delta>"
  by (simp add: field_simps val_def plus_QDelta_def)

lemma val_scaleRat:
  "val (c *R qd) \<delta> = c * val qd \<delta>"
  by (simp add: field_simps val_def scaleRat_QDelta_def)

lemma qdfst_setsum:
  "finite A \<Longrightarrow> qdfst (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. qdfst (f x))"
  by (induct A rule: finite_induct) (auto simp add: zero_QDelta_def plus_QDelta_def)

lemma qdsnd_setsum:
  "finite A \<Longrightarrow> qdsnd (\<Sum>x\<in>A. f x) = (\<Sum>x\<in>A. qdsnd (f x))"
  by (induct A rule: finite_induct) (auto simp add: zero_QDelta_def plus_QDelta_def)

lemma valuate_valuate_rat:
  "lp \<lbrace>(\<lambda>v. (QDelta (vl v) 0))\<rbrace> = QDelta (lp\<lbrace>vl\<rbrace>) 0"
  using Rep_linear_poly
  by (simp add: valuate_def scaleRat_QDelta_def qdsnd_setsum qdfst_setsum)

lemma valuate_rat_valuate:
  "lp\<lbrace>(\<lambda>v. val (vl v) \<delta>)\<rbrace> = val (lp\<lbrace>vl\<rbrace>) \<delta>"
  unfolding valuate_def val_def
  using rational_vector.scale_sum_right[of \<delta> "\<lambda>x. Rep_linear_poly lp x * qdsnd (vl x)" "{v :: nat. Rep_linear_poly lp v \<noteq> (0 :: rat)}"]
  using Rep_linear_poly
  by (auto simp add: field_simps sum.distrib qdfst_setsum qdsnd_setsum) (auto simp add: scaleRat_QDelta_def)

lemma delta0:
  assumes "qd1 \<le> qd2"
  shows "\<forall> \<epsilon>. \<epsilon> > 0 \<and> \<epsilon> \<le> (\<delta>0 qd1 qd2) \<longrightarrow> val qd1 \<epsilon> \<le> val qd2 \<epsilon>"
proof-
  have "\<And> e c1 c2 k1 k2 :: rat. \<lbrakk>e \<ge> 0; c1 < c2; k1 \<le> k2\<rbrakk> \<Longrightarrow> c1 + e*k1 \<le> c2 + e*k2"
  proof-
    fix e c1 c2 k1 k2 :: rat
    show "\<lbrakk>e \<ge> 0; c1 < c2; k1 \<le> k2\<rbrakk> \<Longrightarrow> c1 + e*k1 \<le> c2 + e*k2"
      using mult_left_mono[of "k1" "k2" "e"]
      using add_less_le_mono[of "c1" "c2" "e*k1" "e*k2"]
      by simp
  qed
  then show ?thesis
    using assms
    by (auto simp add: \<delta>0_def val_def less_eq_QDelta_def Let_def field_simps mult_left_mono)
qed

primrec
  \<delta>_min ::"(QDelta \<times> QDelta) list \<Rightarrow> rat" where
  "\<delta>_min [] = 1" |
  "\<delta>_min (h # t) = min (\<delta>_min t) (\<delta>0 (fst h) (snd h))"

lemma delta_gt_zero:
  "\<delta>_min l > 0"
  by (induct l) (auto simp add: Let_def field_simps \<delta>0_def)

lemma delta_le_one: 
  "\<delta>_min l \<le> 1" 
  by (induct l, auto)

lemma delta_min_append:
  "\<delta>_min (as @ bs) = min (\<delta>_min as) (\<delta>_min bs)"
  by (induct as, insert delta_le_one[of bs], auto)

lemma delta_min_mono: "set as \<subseteq> set bs \<Longrightarrow> \<delta>_min bs \<le> \<delta>_min as" 
proof (induct as)
  case Nil
  then show ?case using delta_le_one by simp
next
  case (Cons a as)
  from Cons(2) have "a \<in> set bs" by auto
  from split_list[OF this]
  obtain bs1 bs2 where bs: "bs = bs1 @ [a] @ bs2" by auto
  have bs: "\<delta>_min bs = \<delta>_min ([a] @ bs)" unfolding bs delta_min_append by auto
  show ?case unfolding bs using Cons(1-2) by auto
qed


lemma delta_min:
  assumes "\<forall> qd1 qd2. (qd1, qd2) \<in> set qd \<longrightarrow> qd1 \<le> qd2"
  shows "\<forall> \<epsilon>. \<epsilon> > 0 \<and> \<epsilon> \<le> \<delta>_min qd \<longrightarrow> (\<forall> qd1 qd2. (qd1, qd2) \<in> set qd \<longrightarrow> val qd1 \<epsilon> \<le> val qd2 \<epsilon>)"
  using assms
  using delta0
  by (induct qd, auto)

lemma QDelta_0_0: "QDelta 0 0 = 0" by code_simp
lemma qdsnd_0: "qdsnd 0 = 0" by code_simp
lemma qdfst_0: "qdfst 0 = 0" by code_simp


end
