subsection "Properties about values"

theory ValueProps
  imports Values
begin

inductive_cases fun_le_inv[elim]: "t1 \<lesssim> t2" and
  vfun_le_inv[elim!]: "VFun t1 \<sqsubseteq> VFun t2" and
  le_fun_nat_inv[elim!]: "VFun t2 \<sqsubseteq> VNat x1" and
  le_fun_cons_inv[elim!]: "(v1, v2) # t1 \<lesssim> t2" and
  le_any_nat_inv[elim!]: "v \<sqsubseteq> VNat n" and
  le_nat_any_inv[elim!]: "VNat n \<sqsubseteq> v" and
  le_fun_any_inv[elim!]: "VFun t \<sqsubseteq> v" and
  le_any_fun_inv[elim!]: "v \<sqsubseteq> VFun t"

lemma fun_le_cons: "(a # t1) \<lesssim> t2 \<Longrightarrow> t1 \<lesssim> t2" 
  by (case_tac a) auto

function val_size :: "val \<Rightarrow> nat" and fun_size :: "func \<Rightarrow> nat" where
  "val_size (VNat n) = 0" |
  "val_size (VFun t) = 1 + fun_size t" |
  "fun_size [] = 0" |
  "fun_size ((v1,v2)#t) = 1 + val_size v1 + val_size v2 + fun_size t" 
  by pat_completeness auto
termination val_size by size_change

lemma val_size_mem: "(a, b) \<in> set t \<Longrightarrow> val_size a + val_size b < fun_size t"
  by (induction t) auto
lemma val_size_mem_l: "(a, b) \<in> set t \<Longrightarrow> val_size a < fun_size t"
  by (induction t) auto
lemma val_size_mem_r: "(a, b) \<in> set t \<Longrightarrow> val_size b < fun_size t"
  by (induction t) auto
        
lemma val_fun_le_refl: "\<forall> v t. n = val_size v + fun_size t \<longrightarrow> v \<sqsubseteq> v \<and> t \<lesssim> t"
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case apply clarify apply (rule conjI)
  proof -
    fix v::val and t::func assume n: "n = val_size v + fun_size t"     
    show "v \<sqsubseteq> v"
    proof (cases v)
      case (VNat x1)
      then show ?thesis by auto
    next
      case (VFun t')
      let ?m = "val_size (VNat 0) + fun_size t'"
      from 1 n VFun have "t' \<lesssim> t'" 
        apply (erule_tac x="?m" in allE) apply (erule impE)
         apply force apply (erule_tac x="VNat 0" in allE) apply (erule_tac x="t'" in allE)
        apply simp done
      from this VFun show ?thesis by force
    qed 
  next
    fix v::val and t::func assume n: "n = val_size v + fun_size t"
    show "t \<lesssim> t"
      apply (rule fun_le) apply clarify
    proof -
      fix v1 v2 assume v12: "(v1,v2) \<in> set t"
      from 1 v12 have v11: "v1 \<sqsubseteq> v1"
        apply (erule_tac x="val_size v1 + fun_size []" in allE)
        apply (erule impE) using n apply simp apply (frule val_size_mem) apply force
        apply (erule_tac x=v1 in allE) apply (erule_tac x="[]" in allE) apply force done
      from 1 v12 have v22: "v2 \<sqsubseteq> v2" 
        apply (erule_tac x="val_size v2 + fun_size []" in allE)
        apply (erule impE) using n apply simp apply (frule val_size_mem) apply force
        apply (erule_tac x=v2 in allE) apply (erule_tac x="[]" in allE) apply force done
      from v12 v11 v22
      show "\<exists> v3 v4. (v3,v4) \<in> set t \<and> v1 \<sqsubseteq> v3 \<and> v3 \<sqsubseteq> v1 \<and> v2 \<sqsubseteq> v4 \<and> v4 \<sqsubseteq> v2" by blast 
      qed
  qed
qed

proposition val_le_refl[simp]: fixes v::val shows "v \<sqsubseteq> v" using val_fun_le_refl by auto
    
lemma fun_le_refl[simp]: fixes t::func shows "t \<lesssim> t" using val_fun_le_refl by auto
    
definition val_eq :: "val \<Rightarrow> val \<Rightarrow> bool" (infix "\<sim>" 52) where
  "val_eq v1 v2 \<equiv> (v1 \<sqsubseteq> v2 \<and> v2 \<sqsubseteq> v1)"
  
definition fun_eq :: "func \<Rightarrow> func \<Rightarrow> bool" (infix "\<sim>" 52) where
  "fun_eq t1 t2 \<equiv> (t1 \<lesssim> t2 \<and> t2 \<lesssim> t1)" 

lemma vfun_eq[intro!]: "t \<sim> t' \<Longrightarrow> VFun t \<sim> VFun t'"
  apply (simp add: val_eq_def fun_eq_def) 
  apply (rule conjI) apply (erule conjE) apply (rule vfun_le) apply assumption
  apply (erule conjE) apply (rule vfun_le) apply assumption
  done
 
lemma val_eq_refl[simp]: fixes v::val shows "v \<sim> v"
  by (simp add: val_eq_def) 

lemma val_eq_symm: fixes v1::val and v2::val shows "v1 \<sim> v2 \<Longrightarrow> v2 \<sim> v1"
  unfolding val_eq_def by blast 
    
lemma val_le_fun_le_trans: 
   "\<forall> v2 t2. n = val_size v2 + fun_size t2 \<longrightarrow> 
    (\<forall> v1 v3. v1 \<sqsubseteq> v2 \<longrightarrow> v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3) 
    \<and> (\<forall> t1 t3. t1 \<lesssim> t2 \<longrightarrow> t2 \<lesssim> t3 \<longrightarrow> t1 \<lesssim> t3)"
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case apply clarify
  proof
    fix v2 t2 assume n: "n = val_size v2 + fun_size t2"
    show "\<forall>v1 v3. v1 \<sqsubseteq> v2 \<longrightarrow> v2 \<sqsubseteq> v3 \<longrightarrow> v1 \<sqsubseteq> v3" apply clarify
    proof -
      fix v1 v3 assume v12: "v1 \<sqsubseteq> v2" and v23: "v2 \<sqsubseteq> v3"
      show "v1 \<sqsubseteq> v3"
      proof (cases v2)
        case (VNat n)
        from VNat v12 have v1: "v1 = VNat n" by auto 
        from VNat v23 have v3: "v3 = VNat n" by auto 
        from v1 v3 show ?thesis by auto 
      next
        case (VFun t2')
        from v12 VFun obtain t1 where t12: "t1 \<lesssim> t2'" and v1: "v1 = VFun t1" by auto
        from v23 VFun obtain t3 where t23: "t2' \<lesssim> t3" and v3: "v3 = VFun t3" by auto 
        let ?m = "val_size (VNat 0) + fun_size t2'"
        from 1 n VFun have IH: "\<forall>t1 t3. t1 \<lesssim> t2' \<longrightarrow> t2' \<lesssim> t3 \<longrightarrow> t1 \<lesssim> t3"
          apply simp apply (erule_tac x="?m" in allE) apply (erule impE) apply force
          apply (erule_tac x="VNat 0" in allE)apply (erule_tac x="t2'" in allE) 
          apply auto done 
        from t12 t23 IH have "t1 \<lesssim> t3" by auto 
        from this v1 v3 show ?thesis apply auto done
      qed
    qed
  next
    fix v5 t2 assume n: "n = val_size v5 + fun_size t2"
    show "\<forall>t1 t3. t1 \<lesssim> t2 \<longrightarrow> t2 \<lesssim> t3 \<longrightarrow> t1 \<lesssim> t3" apply clarify
    proof -
      fix t1 t3 v1 v2 assume t12: "t1 \<lesssim> t2" and t23: "t2 \<lesssim> t3" and v12: "(v1,v2) \<in> set t1"
      from v12 t12 obtain v1' v2' where v12p: "(v1',v2') \<in> set t2" and 
          v1_v1p: "v1 \<sqsubseteq> v1'" and v11p: "v1' \<sqsubseteq> v1" and v22p: "v2 \<sqsubseteq> v2'" and v2p_v2: "v2' \<sqsubseteq> v2" by blast 
      from v12p t23 obtain v1'' v2'' where v12pp: "(v1'',v2'') \<in> set t3" and
         v1p_v1pp: "v1' \<sqsubseteq> v1''" and v11pp: "v1'' \<sqsubseteq> v1'" and 
         v22pp: "v2' \<sqsubseteq> v2''" and v2pp_v2p: "v2'' \<sqsubseteq> v2'" by blast
          
      from v12p have sv1p: "val_size v1' < fun_size t2" using val_size_mem_l by blast 
      from v12 1 v11p v11pp n sv1p have v1pp_v1: "v1'' \<sqsubseteq> v1" 
        apply (erule_tac x="val_size v1' + fun_size []" in allE)
        apply (erule impE) apply force apply (erule_tac x=v1' in allE)
        apply (erule_tac x="[]" in allE) apply (erule impE) apply force
        apply (erule conjE) apply blast done
      
      from v12p have sv2p: "val_size v2' < fun_size t2" using val_size_mem_r by blast 
      from v12 1 v22p v22pp n sv2p have v2_v2pp: "v2 \<sqsubseteq> v2''" 
        apply (erule_tac x="val_size v2' + fun_size []" in allE)
        apply (erule impE) apply force apply (erule_tac x=v2' in allE)
        apply (erule_tac x="[]" in allE) apply (erule impE) apply force
        apply (erule conjE) apply blast done

      from v12 1 v1_v1p v1p_v1pp n sv1p have v1_v1pp: "v1 \<sqsubseteq> v1''" 
        apply (erule_tac x="val_size v1' + fun_size []" in allE)
        apply (erule impE) apply force apply (erule_tac x=v1' in allE)
        apply (erule_tac x="[]" in allE) apply (erule impE) apply force
        apply (erule conjE) apply blast done
      
      from v12 1 v2pp_v2p v2p_v2 n sv2p have v2pp_v2: "v2'' \<sqsubseteq> v2" 
        apply (erule_tac x="val_size v2' + fun_size []" in allE)
        apply (erule impE) apply force apply (erule_tac x=v2' in allE)
        apply (erule_tac x="[]" in allE) apply (erule impE) apply force
        apply (erule conjE) apply blast done
        
      from v12pp v1pp_v1 v2_v2pp v1_v1pp v2pp_v2
      show " \<exists>v3 v4. (v3, v4) \<in> set t3 \<and> v1 \<sqsubseteq> v3 \<and> v3 \<sqsubseteq> v1 \<and> v2 \<sqsubseteq> v4 \<and> v4 \<sqsubseteq> v2" by blast
    qed
  qed
qed

proposition val_le_trans: fixes v2::val shows "\<lbrakk> v1 \<sqsubseteq> v2; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v1 \<sqsubseteq> v3"
  using val_le_fun_le_trans by blast

lemma fun_le_trans: "\<lbrakk> t1 \<lesssim> t2; t2 \<lesssim> t3 \<rbrakk> \<Longrightarrow> t1 \<lesssim> t3"
  using val_le_fun_le_trans by blast
    
lemma val_eq_trans: fixes v1::val and v2::val and v3::val 
  assumes v12: "v1 \<sim> v2" and v23: "v2 \<sim> v3" shows "v1 \<sim> v3"
  using v12 v23 apply (simp only: val_eq_def) using val_le_trans apply blast done
    
lemma fun_eq_refl[simp]: fixes t::func shows "t \<sim> t"
  by (simp add: fun_eq_def) 

lemma fun_eq_trans: fixes t1::func and t2::func and t3::func
  assumes t12: "t1 \<sim> t2" and t23: "t2 \<sim> t3" shows "t1 \<sim> t3"
  using t12 t23 unfolding fun_eq_def apply clarify apply (rule conjI)
   apply (rule fun_le_trans) apply assumption apply assumption
  apply (rule fun_le_trans) apply assumption apply assumption
  done
    
lemma append_fun_le:
   "\<lbrakk> t1' \<lesssim> t1; t2' \<lesssim> t2 \<rbrakk> \<Longrightarrow> t1' @ t2' \<lesssim> t1 @ t2"
  apply (rule fun_le) apply clarify apply simp apply (erule fun_le_inv)+ apply blast done

lemma append_fun_equiv:
   "\<lbrakk> t1' \<sim> t1; t2' \<sim> t2 \<rbrakk> \<Longrightarrow> t1' @ t2' \<sim> t1 @ t2"
  apply (simp add: val_eq_def fun_eq_def) using append_fun_le apply blast done

lemma append_leq_symm: "t2 @ t1 \<lesssim> t1 @ t2"
  apply (rule fun_le) apply force done
    
lemma append_eq_symm: "t2 @ t1 \<sim> t1 @ t2"
  unfolding fun_eq_def val_eq_def apply (rule conjI)
  apply (rule append_leq_symm) apply (rule append_leq_symm) done

lemma le_nat_any[simp]: "VNat n \<sqsubseteq> v \<Longrightarrow> v = VNat n"
  by (cases v) auto 

lemma le_any_nat[simp]: "v \<sqsubseteq> VNat n \<Longrightarrow> v = VNat n"
  by (cases v) auto

lemma le_nat_nat[simp]: "VNat n \<sqsubseteq> VNat n' \<Longrightarrow> n = n'"
  by auto 
  
end
  
