section "Declarative semantics with tables as lists"

text\<open>
  The semantics that represents function tables as lists is largely obsolete,
  being replaced by the finite set representation. However, the proof
  of equivalence to the intersection type system still uses the version
  based on lists.
\<close>
  
subsection "Definition of values for declarative semantics" 

theory Values
  imports Main Lambda
begin
  
datatype val = VNat nat | VFun "(val \<times> val) list"

type_synonym func = "(val \<times> val) list"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) 
  and fun_le :: "func \<Rightarrow> func \<Rightarrow> bool" (infix "\<lesssim>" 52) where
  vnat_le[intro!]: "(VNat n) \<sqsubseteq> (VNat n)" |
  vfun_le[intro!]: "t1 \<lesssim> t2 \<Longrightarrow> (VFun t1) \<sqsubseteq> (VFun t2)" |
  fun_le[intro!]: "(\<forall> v1 v2. (v1,v2) \<in> set t1 \<longrightarrow> 
                       (\<exists> v3 v4. (v3,v4) \<in> set t2 
                        \<and> v1 \<sqsubseteq> v3 \<and> v3 \<sqsubseteq> v1 \<and> v2 \<sqsubseteq> v4 \<and> v4 \<sqsubseteq> v2))
                   \<Longrightarrow> t1 \<lesssim> t2"

type_synonym env = "((name \<times> val) list)"

definition env_le :: "env \<Rightarrow> env \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "\<rho> \<sqsubseteq> \<rho>' \<equiv> \<forall> x v. lookup \<rho> x = Some v \<longrightarrow> (\<exists> v'. lookup \<rho>' x = Some v' \<and> v \<sqsubseteq> v')" 

definition env_eq :: "env \<Rightarrow> env \<Rightarrow> bool" (infix "\<approx>" 50) where
  "\<rho> \<approx> \<rho>' \<equiv> (\<forall> x. lookup \<rho> x = lookup \<rho>' x)"

end
  
