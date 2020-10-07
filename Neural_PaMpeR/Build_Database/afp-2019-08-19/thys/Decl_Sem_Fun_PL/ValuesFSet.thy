theory ValuesFSet
  imports Main Lambda "HOL-Library.FSet" 
begin

datatype val = VNat nat | VFun "(val \<times> val) fset"

type_synonym func = "(val \<times> val) fset"

inductive val_le :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where
  vnat_le[intro!]: "(VNat n) \<sqsubseteq> (VNat n)" |
  vfun_le[intro!]: "fset t1 \<subseteq> fset t2 \<Longrightarrow> (VFun t1) \<sqsubseteq> (VFun t2)"

type_synonym env = "((name \<times> val) list)"

definition env_le :: "env \<Rightarrow> env \<Rightarrow> bool" (infix "\<sqsubseteq>" 52) where 
  "\<rho> \<sqsubseteq> \<rho>' \<equiv> \<forall> x v. lookup \<rho> x = Some v \<longrightarrow> (\<exists> v'. lookup \<rho>' x = Some v' \<and> v \<sqsubseteq> v')" 

definition env_eq :: "env \<Rightarrow> env \<Rightarrow> bool" (infix "\<approx>" 50) where
  "\<rho> \<approx> \<rho>' \<equiv> (\<forall> x. lookup \<rho> x = lookup \<rho>' x)"

fun vadd :: "(val \<times> nat) \<times> (val \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "vadd ((_,v),(_,u)) r = v + u + r"
  
primrec vsize :: "val \<Rightarrow> nat" where
"vsize (VNat n) = 1" |
"vsize (VFun t) = 1 + ffold vadd 0
                            (fimage (map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))) t)"

abbreviation vprod_size :: "val \<times> val \<Rightarrow> (val \<times> nat) \<times> (val \<times> nat)" where
  "vprod_size \<equiv> map_prod (\<lambda> v. (v,vsize v)) (\<lambda> v. (v,vsize v))"

abbreviation fsize :: "func \<Rightarrow> nat" where
  "fsize t \<equiv> 1 + ffold vadd 0 (fimage vprod_size t)"

interpretation vadd_vprod: comp_fun_commute "vadd \<circ> vprod_size"
  unfolding comp_fun_commute_def by auto  

lemma vprod_size_inj: "inj_on vprod_size (fset A)"
  unfolding inj_on_def by auto
  
lemma fsize_def2: "fsize t = 1 + ffold (vadd \<circ> vprod_size) 0 t"
  using vprod_size_inj[of t] ffold_fimage[of vprod_size t vadd 0] by simp

lemma fsize_finsert_in[simp]:
  assumes v12_t: "(v1,v2) |\<in>| t" shows "fsize (finsert (v1,v2) t) = fsize t"
proof -
  from v12_t have "finsert (v1,v2) t = t" by auto
  from this show ?thesis by simp
qed
 
lemma fsize_finsert_notin[simp]: 
  assumes v12_t: "(v1,v2) |\<notin>| t"
  shows "fsize (finsert (v1,v2) t) = vsize v1 + vsize v2 + fsize t"
proof -
  let ?f = "vadd \<circ> vprod_size"
  have "fsize (finsert (v1,v2) t) = 1 + ffold ?f 0 (finsert (v1,v2) t)"
    using fsize_def2[of "finsert (v1,v2) t"] by simp
  also from v12_t have "... = 1 + ?f (v1,v2) (ffold ?f 0 t)" by simp
  finally have "fsize (finsert (v1,v2) t) = 1 + ?f (v1,v2) (ffold ?f 0 t)" .
  from this show ?thesis using fsize_def2[of t] by simp
qed
    
end
  
