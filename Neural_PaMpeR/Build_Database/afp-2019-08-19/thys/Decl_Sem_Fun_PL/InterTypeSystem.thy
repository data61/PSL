section "Declarative semantics as a type system"

theory InterTypeSystem
  imports Lambda
begin

datatype ty = TNat nat | TFun funty
    and funty = TArrow ty ty (infix "\<rightarrow>" 55) | TInt funty funty (infix "\<sqinter>" 56) | TTop ("\<top>")

inductive subtype :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "<:" 52) 
  and fsubtype :: "funty \<Rightarrow> funty \<Rightarrow> bool" (infix "<::" 52) where
  sub_refl: "A <: A" |
  sub_funty[intro!]: "f1 <:: f2 \<Longrightarrow> TFun f1 <: TFun f2" | 
  sub_fun[intro!]: "\<lbrakk> T1 <: T1'; T1' <: T1; T2 <: T2'; T2' <: T2 \<rbrakk> \<Longrightarrow> (T1\<rightarrow>T2) <:: (T1'\<rightarrow>T2')" |
  sub_inter_l1[intro!]: "T1 \<sqinter> T2 <:: T1" |
  sub_inter_l2[intro!]: "T1 \<sqinter> T2 <:: T2" |
  sub_inter_r[intro!]: "\<lbrakk> T3 <:: T1; T3 <:: T2 \<rbrakk> \<Longrightarrow> T3 <:: T1 \<sqinter> T2" |
  sub_fun_top[intro!]: "T1 \<rightarrow> T2 <:: \<top>" |
  sub_top_top[intro!]: "\<top> <:: \<top>" |
  fsub_refl[intro!]: "T <:: T" |
  sub_trans[trans]: "\<lbrakk> T1 <:: T2; T2 <:: T3 \<rbrakk> \<Longrightarrow> T1 <:: T3"

definition ty_eq  :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "\<approx>" 50) where
  "A \<approx> B \<equiv> A <: B \<and> B <: A"
definition fty_eq :: "funty \<Rightarrow> funty \<Rightarrow> bool" (infix "\<simeq>" 50) where
  "F1 \<simeq> F2 \<equiv> F1 <:: F2 \<and> F2 <:: F1"
  
type_synonym tyenv = "(name \<times> ty) list"

inductive wt :: "tyenv \<Rightarrow> exp \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51,51,51] 51) where
  wt_var[intro!]: "lookup \<Gamma> x = Some T \<Longrightarrow> \<Gamma> \<turnstile> EVar x : T" |
  wt_nat[intro!]: "\<Gamma> \<turnstile> ENat n : TNat n" |
  wt_lam[intro!]: "\<lbrakk> (x,A)#\<Gamma> \<turnstile> e : B \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> ELam x e : TFun (A \<rightarrow> B)" |
  wt_app[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : TFun (A \<rightarrow> B); \<Gamma> \<turnstile> e2 : A \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> EApp e1 e2 : B" |
  wt_top[intro!]: "\<Gamma> \<turnstile> ELam x e : TFun \<top>" |
  wt_inter[intro!]: "\<lbrakk> \<Gamma> \<turnstile> ELam x e : TFun A; \<Gamma> \<turnstile> ELam x e : TFun B \<rbrakk> 
       \<Longrightarrow> \<Gamma> \<turnstile> ELam x e : TFun (A \<sqinter> B)" |
  wt_sub[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e : A; A <: B \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> e : B" |
  wt_prim[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : TNat n1; \<Gamma> \<turnstile> e2 : TNat n2 \<rbrakk>
       \<Longrightarrow> \<Gamma> \<turnstile> EPrim f e1 e2 : TNat (f n1 n2)" |
  wt_ifz[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : TNat 0; \<Gamma> \<turnstile> e3 : B \<rbrakk> 
       \<Longrightarrow> \<Gamma> \<turnstile> EIf e1 e2 e3 : B" |
  wt_ifnz[intro!]: "\<lbrakk> \<Gamma> \<turnstile> e1 : TNat n; n \<noteq> 0; \<Gamma> \<turnstile> e2 : B \<rbrakk>
     \<Longrightarrow> \<Gamma> \<turnstile> EIf e1 e2 e3 : B"

end
  
  
