subsection "Subsumption and change of environment"

theory DenotLam5
  imports Main Lambda DeclSemAsDenot ValueProps
begin

lemma e_prim_intro[intro]: "\<lbrakk> VNat n1 \<in> E e1 \<rho>; VNat n2 \<in> E e2 \<rho>; v = VNat (f n1 n2) \<rbrakk>
    \<Longrightarrow> v \<in> E (EPrim f e1 e2) \<rho>" by auto

lemma e_prim_elim[elim]: "\<lbrakk> v \<in> E (EPrim f e1 e2) \<rho>;
   \<And> n1 n2. \<lbrakk> VNat n1 \<in> E e1 \<rho>; VNat n2 \<in> E e2 \<rho>; v = VNat (f n1 n2) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto 
 
lemma e_app_elim[elim]: "\<lbrakk> v3 \<in> E (EApp e1 e2) \<rho>;
  \<And> f v2 v2' v3'. \<lbrakk> VFun f \<in> E e1 \<rho>; v2 \<in> E e2 \<rho>; (v2',v3') \<in> set f; v2' \<sqsubseteq> v2; v3 \<sqsubseteq> v3' \<rbrakk> \<Longrightarrow> P
 \<rbrakk> \<Longrightarrow> P"
  by auto 

lemma e_app_intro[intro]: "\<lbrakk> VFun f \<in> E e1 \<rho>; v2 \<in> E e2 \<rho>; (v2',v3') \<in> set f; v2' \<sqsubseteq> v2; v3 \<sqsubseteq> v3'\<rbrakk>
     \<Longrightarrow> v3 \<in> E (EApp e1 e2) \<rho>" by auto 

lemma e_lam_intro[intro]: "\<lbrakk> v = VFun f;
      \<forall> v1 v2. (v1,v2) \<in> set f \<longrightarrow> v2 \<in> E e ((x,v1)#\<rho>) \<rbrakk>
    \<Longrightarrow> v \<in> E (ELam x e) \<rho>"
  by auto  

lemma e_lam_intro2[intro]: 
  "\<lbrakk> VFun f \<in> E (ELam x e) \<rho>; v2 \<in> E e ((x,v1)#\<rho>) \<rbrakk> 
  \<Longrightarrow> VFun ((v1,v2)#f) \<in> E (ELam x e) \<rho>"    
  by auto 

lemma e_lam_intro3[intro]: "VFun [] \<in> E (ELam x e) \<rho>"
  by auto 

lemma e_if_intro[intro]: "\<lbrakk> VNat n \<in> E e1 \<rho>; n = 0 \<longrightarrow> v \<in> E e3 \<rho>; n \<noteq> 0 \<longrightarrow> v \<in> E e2 \<rho> \<rbrakk>
    \<Longrightarrow> v \<in> E (EIf e1 e2 e3) \<rho>"
  by auto 

lemma e_var_intro[elim]: "\<lbrakk> lookup \<rho> x = Some v'; v \<sqsubseteq> v' \<rbrakk> \<Longrightarrow> v \<in> E (EVar x) \<rho>"
  by auto 

lemma e_var_elim[elim]: "\<lbrakk> v \<in> E (EVar x) \<rho>;
   \<And> v'. \<lbrakk> lookup \<rho> x = Some v'; v \<sqsubseteq> v' \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto 

lemma e_lam_elim[elim]: "\<lbrakk> v \<in> E (ELam x e) \<rho>;
   \<And> f. \<lbrakk> v = VFun f; \<forall> v1 v2. (v1,v2) \<in> set f \<longrightarrow> v2 \<in> E e ((x,v1)#\<rho>) \<rbrakk>
    \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto 

lemma e_lam_elim2[elim]: "\<lbrakk> VFun ((v1,v2)#f) \<in> E (ELam x e) \<rho>;
   \<lbrakk> v2 \<in> E e ((x,v1)#\<rho>) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by auto 

lemma e_if_elim[elim]: "\<lbrakk> v \<in> E (EIf e1 e2 e3) \<rho>;
   \<And> n. \<lbrakk> VNat n \<in> E e1 \<rho>; n = 0 \<longrightarrow> v \<in> E e3 \<rho>; n \<noteq> 0 \<longrightarrow> v \<in> E e2 \<rho> \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" 
  by auto 
    
definition xenv_le :: "name set \<Rightarrow> env \<Rightarrow> env \<Rightarrow> bool" ("_ \<turnstile> _ \<sqsubseteq> _" [51,51,51] 52) where 
  "X \<turnstile> \<rho> \<sqsubseteq> \<rho>' \<equiv> \<forall> x v. x \<in> X \<and> lookup \<rho> x = Some v \<longrightarrow> (\<exists> v'. lookup \<rho>' x = Some v' \<and> v \<sqsubseteq> v')" 
declare xenv_le_def[simp]
    
proposition change_env_le: fixes v::val and \<rho>::env
  assumes de: "v \<in> E e \<rho>" and vp_v: "v' \<sqsubseteq> v" and rr: "FV e \<turnstile> \<rho> \<sqsubseteq> \<rho>'"
  shows "v' \<in> E e \<rho>'"
  using de rr vp_v
proof (induction e arbitrary: v v' \<rho> \<rho>' rule: exp.induct)
  case (EVar x v v' \<rho> \<rho>')
  from EVar obtain v2 where lx: "lookup \<rho> x = Some v2" and v_v2: "v \<sqsubseteq> v2" by auto 
  from lx EVar obtain v3 where 
    lx2: "lookup \<rho>' x = Some v3" and v2_v3: "v2 \<sqsubseteq> v3" by force
  from v_v2 v2_v3 have v_v3: "v \<sqsubseteq> v3" by (rule val_le_trans)
  from EVar v_v3 have vp_v3: "v' \<sqsubseteq> v3" using val_le_trans by blast 
  from lx2 vp_v3 show ?case by (rule e_var_intro)
next
  case (ENat n) then show ?case by simp
next
  case (ELam x e)
  from ELam(2) obtain f where v: "v = VFun f" and 
    body: "\<forall> v1 v2. (v1,v2) \<in> set f \<longrightarrow> v2 \<in> E e ((x,v1)#\<rho>)" by auto
  from v ELam(4) obtain f' where vp: "v' = VFun f'" and fp_f: "f' \<lesssim> f" by (case_tac v') auto 
  from vp show ?case
  proof (simp, clarify)
    fix v1 v2 assume v12: "(v1,v2)\<in> set f'" 
    from v12 fp_f obtain v3 v4 where v34: "(v3,v4) \<in> set f" and 
      v31: "v3 \<sqsubseteq> v1" and v24: "v2 \<sqsubseteq> v4" by blast
    from v34 body have v4_E: "v4 \<in> E e ((x,v3)#\<rho>)" by blast
    from ELam(3) v31 have rr2: "FV e \<turnstile> ((x,v3)#\<rho>) \<sqsubseteq> ((x,v1)#\<rho>')" by auto
    from ELam(1) v24 v4_E rr2 show "v2 \<in> E e ((x,v1)#\<rho>')" by blast
  qed
next
  case (EApp e1 e2)
  from EApp(3) obtain f and v2::val and v2' v3' where f_e1: "VFun f \<in> E e1 \<rho>" and 
    v2_e2: "v2 \<in> E e2 \<rho>" and v23p_f: "(v2',v3') \<in> set f" and v2p_v2: "v2' \<sqsubseteq> v2" and
    v_v3: "v \<sqsubseteq> v3'" by blast
  from EApp(4) have 1: "FV e1 \<turnstile> \<rho> \<sqsubseteq> \<rho>'" by auto
  have f_f: "VFun f \<sqsubseteq> VFun f" by auto 
  from EApp(1) f_e1 1 f_f have f_e1b: "VFun f \<in> E e1 \<rho>'" by blast
  from EApp(4) have 2: "FV e2 \<turnstile> \<rho> \<sqsubseteq> \<rho>'" by auto
  from EApp(2) v2_e2 2 have v2_e2b: "v2 \<in> E e2 \<rho>'" by auto 
  from EApp(5) v_v3 have vp_v3p: "v' \<sqsubseteq> v3'" by (rule val_le_trans)
  from f_e1b v2_e2b v23p_f v2p_v2 vp_v3p
  show ?case by auto
next
  case (EPrim f e1 e2)
  from EPrim(3) obtain n1 n2 where n1_e1: "VNat n1 \<in> E e1 \<rho>" and n2_e2: "VNat n2 \<in> E e2 \<rho>" and
    v: "v = VNat (f n1 n2)" by blast
  from EPrim(4) have 1: "FV e1 \<turnstile> \<rho> \<sqsubseteq> \<rho>'" by auto
  from EPrim(1) n1_e1 1 have n1_e1b: "VNat n1 \<in> E e1 \<rho>'" by blast
  from EPrim(4) have 2: "FV e2 \<turnstile> \<rho> \<sqsubseteq> \<rho>'" by auto
  from EPrim(2) n2_e2 2 have n2_e2b: "VNat n2 \<in> E e2 \<rho>'" by blast
  from v EPrim(5) have vp: "v' = VNat (f n1 n2)" by auto
  from n1_e1b n2_e2b vp show ?case by auto 
next
  case (EIf e1 e2 e3)
  then show ?case
    apply simp apply clarify
    apply (rename_tac n) apply (rule_tac x=n in exI) apply (rule conjI)
     apply force
    apply force done
qed
  
\<comment> \<open>Subsumption is admissible\<close> 
proposition e_sub: "\<lbrakk> v \<in> E e \<rho>; v' \<sqsubseteq> v \<rbrakk> \<Longrightarrow> v' \<in> E e \<rho>"
  apply (subgoal_tac "FV e \<turnstile> \<rho> \<sqsubseteq> \<rho>") using change_env_le apply blast apply auto done

lemma env_le_ext: fixes \<rho>::env assumes rr: "\<rho> \<sqsubseteq> \<rho>'" shows "((x,v)#\<rho>) \<sqsubseteq> ((x,v)#\<rho>')"  
  using rr by (simp add: env_le_def)
 
lemma change_env: fixes \<rho>::env assumes de: "v \<in> E e \<rho>" and rr: "FV e \<turnstile> \<rho> \<sqsubseteq> \<rho>'" shows "v \<in> E e \<rho>'"
proof -
  have vv: "v \<sqsubseteq> v" by auto
  from de rr vv show ?thesis using change_env_le by blast
qed

lemma raise_env: fixes \<rho>::env assumes de: "v \<in> E e \<rho>" and rr: "\<rho> \<sqsubseteq> \<rho>'" shows "v \<in> E e \<rho>'"
  using de rr change_env env_le_def by auto 

lemma env_eq_refl[simp]: fixes \<rho>::env shows "\<rho> \<approx> \<rho>" by (simp add: env_eq_def) 

lemma env_eq_ext: fixes \<rho>::env assumes rr: "\<rho> \<approx> \<rho>'" shows "((x,v)#\<rho>) \<approx> ((x,v)#\<rho>')"  
  using rr by (simp add: env_eq_def) 

lemma eq_implies_le: fixes \<rho>::env shows "\<rho> \<approx> \<rho>' \<Longrightarrow> \<rho> \<sqsubseteq> \<rho>'" 
  by (simp add: env_le_def env_eq_def) 

lemma env_swap: fixes \<rho>::env assumes rr: "\<rho> \<approx> \<rho>'" and ve: "v \<in> E e \<rho>" shows "v \<in> E e \<rho>'"
  using rr ve apply (subgoal_tac "\<rho> \<sqsubseteq> \<rho>'") prefer 2 apply (rule eq_implies_le) apply blast
  apply (rule raise_env) apply auto done

lemma env_strengthen: "\<lbrakk> v \<in> E e \<rho>; \<forall> x. x \<in> FV e \<longrightarrow> lookup \<rho>' x = lookup \<rho> x \<rbrakk> \<Longrightarrow> v \<in> E e \<rho>'"
  using change_env by auto    

end
