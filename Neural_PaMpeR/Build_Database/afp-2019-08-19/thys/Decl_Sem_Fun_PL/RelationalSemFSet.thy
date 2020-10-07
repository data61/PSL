section "Declarative semantics as a relational semantics"

theory RelationalSemFSet
  imports Lambda ValuesFSet
begin
  
inductive rel_sem :: "env \<Rightarrow> exp \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ \<Rightarrow> _" [52,52,52] 51) where
  rnat[intro!]: "\<rho> \<turnstile> ENat n \<Rightarrow> VNat n" |
  rprim[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Rightarrow> VNat n1; \<rho> \<turnstile> e2 \<Rightarrow> VNat n2 \<rbrakk> \<Longrightarrow> \<rho> \<turnstile> EPrim f e1 e2 \<Rightarrow> VNat (f n1 n2)" |
  rvar[intro!]: "\<lbrakk> lookup \<rho> x = Some v'; v \<sqsubseteq> v' \<rbrakk> \<Longrightarrow> \<rho> \<turnstile> EVar x \<Rightarrow> v" |
  rlam[intro!]: "\<lbrakk> \<forall> v v'. (v,v') \<in> fset t \<longrightarrow> (x,v)#\<rho> \<turnstile> e \<Rightarrow> v' \<rbrakk>
    \<Longrightarrow> \<rho> \<turnstile> ELam x e \<Rightarrow> VFun t" |
  rapp[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Rightarrow> VFun t; \<rho> \<turnstile> e2 \<Rightarrow> v2; (v3,v3') \<in> fset t; v3 \<sqsubseteq> v2; v \<sqsubseteq> v3'\<rbrakk>
    \<Longrightarrow> \<rho> \<turnstile> EApp e1 e2 \<Rightarrow> v" |
  rifnz[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Rightarrow> VNat n; n \<noteq> 0; \<rho> \<turnstile> e2 \<Rightarrow> v \<rbrakk> \<Longrightarrow> \<rho> \<turnstile> EIf e1 e2 e3 \<Rightarrow> v" |
  rifz[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Rightarrow> VNat n; n = 0; \<rho> \<turnstile> e3 \<Rightarrow> v \<rbrakk> \<Longrightarrow> \<rho> \<turnstile> EIf e1 e2 e3 \<Rightarrow> v"
  
end
  
