theory Arity
imports "Launchbury.HOLCF-Join-Classes"
begin

typedef Arity = "UNIV :: nat set"
  morphisms Rep_Arity to_Arity by auto

setup_lifting type_definition_Arity

(*
instantiation Arity :: order
begin
lift_definition less_eq_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . x \<le> y".
lift_definition less_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . x < y".
instance
  apply standard
  apply (transfer, fastforce)+
  done
end
*)

instantiation Arity :: po
begin
lift_definition below_Arity :: "Arity \<Rightarrow> Arity \<Rightarrow> bool" is "\<lambda> x y . y \<le> x".

instance
apply standard
apply ((transfer, auto)+)
done
end

instance Arity :: chfin
proof
  fix S  :: "nat \<Rightarrow> Arity"
  assume "chain S"
  have "(ARG_MIN Rep_Arity x. x \<in> range S) \<in> range S"
    by (rule arg_min_natI) auto
  then obtain n where n: "S n = (ARG_MIN Rep_Arity x. x \<in> range S)" by auto
  have "max_in_chain n S"
  proof(rule max_in_chainI)
    fix j
    assume "n \<le> j" hence "S n \<sqsubseteq> S j" using \<open>chain S\<close> by (metis chain_mono)
    also
    have "Rep_Arity (S n) \<le> Rep_Arity (S j)"
      unfolding n image_def
      by (metis (lifting, full_types) arg_min_nat_lemma UNIV_I mem_Collect_eq)
    hence "S j \<sqsubseteq> S n" by transfer
    finally  
    show "S n = S j".
  qed
  thus "\<exists>n. max_in_chain n S"..
qed

instance Arity :: cpo ..

lift_definition inc_Arity :: "Arity \<Rightarrow> Arity" is Suc.
lift_definition pred_Arity :: "Arity \<Rightarrow> Arity" is "(\<lambda> x . x - 1)".

lemma inc_Arity_cont[simp]: "cont inc_Arity"
  apply (rule chfindom_monofun2cont)
  apply (rule monofunI)
  apply (transfer, simp)
  done

lemma pred_Arity_cont[simp]: "cont pred_Arity"
  apply (rule chfindom_monofun2cont)
  apply (rule monofunI)
  apply (transfer, simp)
  done

definition inc :: "Arity \<rightarrow> Arity" where
  "inc = (\<Lambda> x. inc_Arity x)"

definition pred :: "Arity \<rightarrow> Arity" where
  "pred = (\<Lambda> x. pred_Arity x)"

lemma inc_inj[simp]: "inc\<cdot>n = inc\<cdot>n' \<longleftrightarrow> n = n'"
  by (simp add: inc_def pred_def, transfer, simp)

lemma pred_inc[simp]: "pred\<cdot>(inc\<cdot>n) = n" 
  by (simp add: inc_def pred_def, transfer, simp)

lemma inc_below_inc[simp]: "inc\<cdot>a \<sqsubseteq> inc\<cdot>b \<longleftrightarrow> a \<sqsubseteq> b"
  by (simp add: inc_def pred_def, transfer, simp)

lemma inc_below_below_pred[elim]:
  "inc\<cdot>a \<sqsubseteq> b \<Longrightarrow> a \<sqsubseteq> pred \<cdot> b"
  by (simp add: inc_def pred_def, transfer, simp)

lemma Rep_Arity_inc[simp]: "Rep_Arity (inc\<cdot>a') = Suc (Rep_Arity a')"
  by (simp add: inc_def pred_def, transfer, simp)

instantiation Arity :: zero
begin
lift_definition zero_Arity :: Arity is 0.
instance..
end

instantiation Arity :: one
begin
lift_definition one_Arity :: Arity is 1.
instance ..
end

lemma one_is_inc_zero: "1 = inc\<cdot>0"
  by (simp add: inc_def, transfer, simp)

lemma inc_not_0[simp]: "inc\<cdot>n = 0 \<longleftrightarrow> False"
  by (simp add: inc_def pred_def, transfer, simp)
 
lemma pred_0[simp]: "pred\<cdot>0 = 0"
  by (simp add: inc_def pred_def, transfer, simp)
  
lemma Arity_ind:  "P 0 \<Longrightarrow> (\<And> n. P n \<Longrightarrow> P (inc\<cdot>n)) \<Longrightarrow> P n"
  apply (simp add: inc_def)
  apply transfer
  by (rule nat.induct) 
 
lemma Arity_total:   
  fixes x y :: Arity
  shows "x \<sqsubseteq> y \<or> y \<sqsubseteq> x"
by transfer auto

instance Arity :: Finite_Join_cpo
proof
  fix x y :: Arity
  show "compatible x y" by (metis Arity_total compatibleI)
qed

lemma Arity_zero_top[simp]: "(x :: Arity) \<sqsubseteq> 0"
  by transfer simp

lemma Arity_above_top[simp]: "0 \<sqsubseteq> (a :: Arity) \<longleftrightarrow> a = 0"
  by transfer simp

lemma Arity_zero_join[simp]: "(x :: Arity) \<squnion> 0 = 0"
  by transfer simp
lemma Arity_zero_join2[simp]: "0 \<squnion> (x :: Arity) = 0"
  by transfer simp

lemma Arity_up_zero_join[simp]: "(x :: Arity\<^sub>\<bottom>) \<squnion> up\<cdot>0 = up\<cdot>0"
  by (cases x) auto
lemma Arity_up_zero_join2[simp]: "up\<cdot>0 \<squnion> (x :: Arity\<^sub>\<bottom>) = up\<cdot>0"
  by (cases x) auto
lemma up_zero_top[simp]: "x \<sqsubseteq> up\<cdot>(0::Arity)"
  by (cases x) auto
lemma Arity_above_up_top[simp]: "up\<cdot>0 \<sqsubseteq> (a :: Arity\<^sub>\<bottom>) \<longleftrightarrow> a = up\<cdot>0"
  by (metis Arity_up_zero_join2 join_self_below(4))


lemma Arity_exhaust: "(y = 0 \<Longrightarrow> P) \<Longrightarrow> (\<And>x. y = inc \<cdot> x \<Longrightarrow> P) \<Longrightarrow> P"
  by (metis Abs_cfun_inverse2 Arity.inc_def Rep_Arity_inverse inc_Arity.abs_eq inc_Arity_cont list_decode.cases zero_Arity_def)

end
