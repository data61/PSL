theory ValuesFSetProps
  imports ValuesFSet
begin

inductive_cases 
  vfun_le_inv[elim!]: "VFun t1 \<sqsubseteq> VFun t2" and
  le_fun_nat_inv[elim!]: "VFun t2 \<sqsubseteq> VNat x1" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_fun_any_inv[elim!]: "VFun t \<sqsubseteq> v" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun t" 

proposition val_le_refl[simp]: fixes v::val shows "v \<sqsubseteq> v" by (induction v) auto

proposition val_le_trans[trans]: fixes v2::val shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  by (induction v2 arbitrary: v1 v3) blast+

lemma fsubset[intro!]: "fset A \<subseteq> fset B \<Longrightarrow> A |\<subseteq>| B"
proof (rule fsubsetI)
  fix x assume ab: "fset A \<subseteq> fset B" and xa: "x |\<in>| A"
  from xa have "x \<in> fset A" using fmember.rep_eq[of x A] by simp
  from this ab have "x \<in> fset B" by blast
  from this show "x |\<in>| B" using fmember.rep_eq[of x B] by simp
qed
    
proposition val_le_antisymm: fixes v1::val shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v1 \<rbrakk> \<Longrightarrow> v1 = v2"
  by (induction v1 arbitrary: v2) auto

lemma le_nat_any[simp]: "VNat n \<sqsubseteq> v \<Longrightarrow> v = VNat n"
  by (cases v) auto

lemma le_any_nat[simp]: "v \<sqsubseteq> VNat n \<Longrightarrow> v = VNat n"
  by (cases v) auto

lemma le_nat_nat[simp]: "VNat n \<sqsubseteq> VNat n' \<Longrightarrow> n = n'"
  by auto

end
  
