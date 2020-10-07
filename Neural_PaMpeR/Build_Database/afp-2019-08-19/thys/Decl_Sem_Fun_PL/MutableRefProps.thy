theory MutableRefProps
  imports MutableRef
begin
  
inductive_cases 
  vfun_le_inv[elim!]: "VFun t1 \<sqsubseteq> VFun t2" and
  le_fun_nat_inv[elim!]: "VFun t2 \<sqsubseteq> VNat x1" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_fun_any_inv[elim!]: "VFun t \<sqsubseteq> v" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun t" and
  le_pair_any_inv[elim!]: "VPair v1 v2 \<sqsubseteq> v" and
  le_any_pair_inv[elim!]: "v \<sqsubseteq> VPair v1 v2" and
  le_addr_any_inv[elim!]: "VAddr a \<sqsubseteq> v" and
  le_any_addr_inv[elim!]: "v \<sqsubseteq> VAddr a" and
  le_wrong_any_inv[elim!]: "Wrong \<sqsubseteq> v" and
  le_any_wrong_inv[elim!]: "v \<sqsubseteq> Wrong"

proposition val_le_refl: "v \<sqsubseteq> v" by (induction v) auto

proposition val_le_trans: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  by (induction v2 arbitrary: v1 v3) blast+

proposition val_le_antisymm: "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v1 \<rbrakk> \<Longrightarrow> v1 = v2"
  by (induction v1 arbitrary: v2) blast+
    
end
  
