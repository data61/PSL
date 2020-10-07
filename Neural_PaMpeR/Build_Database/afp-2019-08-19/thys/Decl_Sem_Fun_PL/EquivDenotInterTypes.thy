section "Equivalence of denotational and type system views"

theory EquivDenotInterTypes
  imports InterTypeSystem DeclSemAsDenot DenotLam5
begin
  
fun V :: "ty \<Rightarrow> val" and Vf :: "funty \<Rightarrow> (val \<times> val) list" where
  "V (TNat n) = VNat n" |
  "V (TFun f) = VFun (Vf f)" |
  "Vf (A \<rightarrow> B) = [(V A, V B)]" |
  "Vf (A \<sqinter> B) = Vf A @ Vf B" |
  "Vf \<top> = []"

fun Venv :: "tyenv \<Rightarrow> env" where
  "Venv [] = []" |
  "Venv ((x,A)#\<Gamma>) = (x,V A)#Venv \<Gamma>"

function T :: "val \<Rightarrow> ty" and Tf :: "(val \<times> val) list \<Rightarrow> funty" where
  "T (VNat n) = TNat n" |
  "T (VFun t) = TFun (Tf t)" |
  "Tf [] = \<top>" |
  "Tf ((v1,v2)#t) = (T v1 \<rightarrow> T v2) \<sqinter> Tf t"
  by pat_completeness auto
termination T by size_change

fun Tenv :: "env \<Rightarrow> tyenv" where
  "Tenv [] = []" |
  "Tenv ((x,v)#\<rho>) = (x,T v)#Tenv \<rho>" 
    
lemma sub_inter_left1: "A <:: C \<Longrightarrow> A \<sqinter> B <:: C"
  apply (subgoal_tac "A \<sqinter> B <:: A")
   apply (rule sub_trans) apply assumption apply assumption 
  apply blast
  done
    
lemma sub_inter_left2: "B <:: C \<Longrightarrow> A \<sqinter> B <:: C"
  apply (subgoal_tac "A \<sqinter> B <:: B")
   apply (rule sub_trans) apply assumption apply assumption 
  apply blast
  done

lemma vf_nil[simp]: "Vf (Tf []) = []" by simp
    
lemma vf_cons[simp]: "Vf (Tf ((v,v')#t)) = (V (T v), V (T v'))#(Vf (Tf t))" by simp
  
proposition vt_id: shows "V (T v) = v" and "Vf (Tf t) = t"
  by (induction rule: T_Tf.induct) force+ 

lemma lookup_tenv: 
  "lookup \<rho> x = Some v \<Longrightarrow> lookup (Tenv \<rho>) x = Some (T v)"
  by (induction \<rho> arbitrary: x v) force+

proposition table_mem_sub:
  "(v, v') \<in> set t \<Longrightarrow> Tf t <:: (T v) \<rightarrow> (T v')"
proof (induction t arbitrary: v v')
  case Nil
  then show ?case by auto
next
  case (Cons p t)
  show ?case
  proof (cases p)
    case (Pair v1 v2)
    with Cons show ?thesis 
      apply simp
      apply (erule disjE) 
       apply force 
      apply (subgoal_tac "Tf t <:: T v \<rightarrow> T v'") prefer 2 apply blast
      apply (rule sub_inter_left2) apply assumption done
  qed
qed

lemma Tf_top: "Tf t <:: \<top>"
proof (induction t)
  case Nil
  then show ?case by auto
next
  case (Cons p t)
  with sub_inter_left2 show ?case by (cases p) auto
qed
    
lemma le_sub_flip_aux:
  "\<forall> v v' t t'. n = val_size v + val_size v' + fun_size t + fun_size t' \<longrightarrow>
   (v \<sqsubseteq> v' \<longrightarrow> T v' <: T v) \<and> (t \<lesssim> t' \<longrightarrow> Tf t' <:: Tf t)"
proof (induction n rule: nat_less_induct)
  case (1 n)
  show ?case apply clarify apply (rule conjI) apply clarify prefer 2 apply clarify
     prefer 2
  proof -
    fix v::val and v' t t' assume n: "n = val_size v + val_size v' + fun_size t + fun_size t'"
      and v_vp: "v \<sqsubseteq> v'"
    show "T v' <: T v"
    proof (cases v)
      case (VNat n1)
      from VNat v_vp have vp: "v' = VNat n1" by auto 
      from VNat vp show ?thesis apply simp using sub_refl by blast 
    next
      case (VFun t1)
      from VFun v_vp obtain t2 where vp: "v' = VFun t2" and t1_t2: "t1 \<lesssim> t2" by auto
      let ?m = "val_size (VNat 0) + val_size (VNat 0) + fun_size t1 + fun_size t2"
      from 1 t1_t2 n VFun vp have t2_t1: "Tf t2 <:: Tf t1"
        apply simp
        apply (erule_tac x="?m" in allE)
        apply (erule impE) apply force apply simp apply (erule_tac x="VNat 0" in allE)
        apply (erule_tac x="VNat 0" in allE)
        apply (erule_tac x="t1" in allE)
        apply (erule_tac x="t2" in allE) apply auto done
      from t2_t1 VFun vp show ?thesis by auto 
    qed      
  next
    fix v v' t t' assume n: "n = val_size v + val_size v' + fun_size t + fun_size t'" 
      and t_tp: "t \<lesssim> t'"
    show "Tf t' <:: Tf t"
    proof (cases t)
      case Nil
      from Nil have "Tf t = \<top>" by simp
      then show ?thesis using Tf_top by auto
    next
      case (Cons a t1)
      show ?thesis
      proof (cases a)
        case (Pair v1 v2)
        from Cons Pair show ?thesis apply simp
        proof
          from Cons Pair have v12: "(v1,v2) \<in> set t" by auto
          from t_tp v12 obtain v3 v4 where v34: "(v3,v4) \<in> set t'" and
            v13: "v1 \<sqsubseteq> v3" and v31: "v3 \<sqsubseteq> v1" and v24: "v2 \<sqsubseteq> v4" and v42: "v4 \<sqsubseteq> v2" by blast
          have Tv3_Tv1: "T v3 \<approx> T v1"
          proof -
            let ?m = "val_size v1 + val_size v3"
            from v12 have sv1: "val_size v1 < fun_size t" using val_size_mem_l by auto 
            from v34 have sv3: "val_size v3 < fun_size t'" using val_size_mem_l by auto 
            from 1 v13 n sv1 sv3 have Tv31: "T v3 <: T v1" 
              apply (erule_tac x="?m" in allE) apply (erule impE) apply force 
              apply (erule_tac x=v1 in allE) apply (erule_tac x=v3 in allE)
              apply (erule_tac x="[]" in allE)apply (erule_tac x="[]" in allE)
              apply (erule impE) defer apply blast apply simp
              done
            from 1 v31 n sv1 sv3 have Tv13: "T v1 <: T v3" 
              apply (erule_tac x="?m" in allE) apply (erule impE) apply force 
              apply (erule_tac x=v3 in allE) apply (erule_tac x=v1 in allE)
              apply (erule_tac x="[]" in allE) apply (erule_tac x="[]" in allE) apply auto done
            from Tv13 Tv31 show ?thesis unfolding ty_eq_def by blast
          qed
          have Tv4_Tv2: "T v4 \<approx> T v2"
          proof -
            let ?m = "val_size v2 + val_size v4"
            from v12 have sv2: "val_size v2 < fun_size t" using val_size_mem_r by auto 
            from v34 have sv4: "val_size v4 < fun_size t'" using val_size_mem_r by auto 
            from 1 v42 n sv2 sv4 have Tv2_v4: "T v2 <: T v4" 
              apply (erule_tac x="?m" in allE) apply (erule impE) apply force 
              apply (erule_tac x=v4 in allE) apply (erule_tac x=v2 in allE)
              apply (erule_tac x="[]" in allE) apply (erule_tac x="[]" in allE)
              apply (erule impE) defer apply blast apply simp
              done
            from 1 v24 n sv2 sv4 have Tv4_v2: "T v4 <: T v2"
              apply (erule_tac x="?m" in allE) apply (erule impE) apply force 
              apply (erule_tac x=v2 in allE) apply (erule_tac x=v4 in allE)
              apply (erule_tac x="[]" in allE) apply (erule_tac x="[]" in allE)
              apply (erule impE) defer apply blast apply simp
              done
            from Tv2_v4 Tv4_v2 show ?thesis unfolding ty_eq_def by blast
          qed
          from Tv3_Tv1 Tv4_Tv2 have T34_T12: "T v3 \<rightarrow> T v4 <:: T v1 \<rightarrow> T v2" 
            unfolding ty_eq_def by blast
          from v34 have tp_T34: "Tf t' <:: T v3 \<rightarrow> T v4" using table_mem_sub by blast
          from tp_T34 T34_T12 show "Tf t' <:: T v1 \<rightarrow> T v2" by (rule sub_trans)
        next
          let ?m = "fun_size t' + fun_size t1"
          from Cons Pair t_tp have t1_tp: "t1 \<lesssim> t'" by auto 
          from 1 n t1_tp Cons Pair
          show "Tf t' <:: Tf t1"
            apply (erule_tac x="?m" in allE) apply (erule impE) apply force
            apply (erule_tac x="VNat 0" in allE) apply (erule_tac x="VNat 0" in allE)
            apply (erule_tac x="t1" in allE) apply (erule_tac x="t'" in allE)
            apply auto done
          qed
      qed
    qed
  qed
qed    

proposition le_sub_flip: "v \<sqsubseteq> v' \<Longrightarrow> T v' <: T v" using le_sub_flip_aux by blast 
   
lemma le_sub_fun_flip: "t \<lesssim> t' \<Longrightarrow> Tf t' <:: Tf t" using le_sub_flip_aux by blast

lemma Tf_append: "Tf (t1 @ t2) <:: Tf t1 \<sqinter> Tf t2"
proof (induction t1)
  case Nil
  then show ?case 
    apply simp apply (rule sub_inter_r) using Tf_top apply blast 
    apply (rule fsub_refl) done
next
  case (Cons a t1)
  then show ?case 
    apply (case_tac a) apply simp apply (rule sub_inter_r) apply (rule sub_inter_r)
      apply (rule sub_inter_left1) apply (rule fsub_refl) apply (rule sub_inter_left2)
     apply (subgoal_tac "Tf t1 \<sqinter> Tf t2 <:: Tf t1") prefer 2 apply (rule sub_inter_left1)
      apply (rule fsub_refl) apply (rule sub_trans) apply assumption apply assumption
    apply (rule sub_inter_left2) apply (subgoal_tac "Tf t1 \<sqinter> Tf t2 <:: Tf t2")
     prefer 2 apply (rule sub_inter_left2)
     apply (rule fsub_refl) apply (rule sub_trans) apply assumption apply assumption done
qed
  
lemma append_Tf: "Tf t1 \<sqinter> Tf t2 <:: Tf (t1 @ t2)"
proof (induction t1)
  case Nil
  then show ?case apply simp apply (rule sub_inter_left2) apply (rule fsub_refl) done
next
  case (Cons p t1)
  then show ?case
    apply (cases p) apply simp apply (rule sub_inter_r)
     apply (rule sub_inter_left1) apply (rule sub_inter_left1) apply (rule fsub_refl)
    apply (rename_tac v1 v2)
    apply (subgoal_tac "((T v1 \<rightarrow> T v2) \<sqinter> Tf t1) \<sqinter> Tf t2 <:: Tf t1 \<sqinter> Tf t2")
     prefer 2 apply (rule sub_inter_r) apply (rule sub_inter_left1)
      apply (rule sub_inter_left2) apply (rule fsub_refl)
     apply (rule sub_inter_left2) apply (rule fsub_refl)
    apply (rule sub_trans) apply assumption apply assumption done
qed
 
proposition tv_id: shows "T (V A) \<approx> A" and "Tf (Vf F) \<simeq> F"
proof (induction rule: V_Vf.induct)
  case (1 n)
  then show ?case apply (simp add: ty_eq_def) apply (rule sub_refl) done
next
  case (2 f)
  then show ?case 
    apply (simp add: ty_eq_def) apply (rule conjI) apply (rule sub_funty)
    using le_sub_flip fty_eq_def apply blast
    apply (rule sub_funty) using le_sub_flip fty_eq_def apply blast
    done
next
  case (3 A B)
  then show ?case 
    apply (simp add: fty_eq_def) apply(rule conjI) apply (rule sub_inter_left1)
    using ty_eq_def apply blast
    apply (rule sub_inter_r) using ty_eq_def apply blast 
    apply blast done
next
  case (4 A B)
  then show ?case 
    using fty_eq_def apply simp apply (rule conjI) apply (rule sub_inter_r)
      apply (subgoal_tac "Tf (Vf A @ Vf B) <:: Tf (Vf A) \<sqinter> Tf (Vf B)")
       prefer 2 using Tf_append apply simp 
      apply (subgoal_tac "Tf (Vf A) \<sqinter> Tf (Vf B) <:: A")
       apply (rule sub_trans) apply assumption apply assumption  
      apply (rule sub_inter_left1) apply blast 
     apply (subgoal_tac "Tf (Vf A @ Vf B) <:: Tf (Vf A) \<sqinter> Tf (Vf B)")
      prefer 2 using Tf_append apply simp 
     apply (subgoal_tac "Tf (Vf A) \<sqinter> Tf (Vf B) <:: B")
      apply (rule sub_trans) apply assumption apply assumption  
     apply (rule sub_inter_left2) apply blast 
    apply (subgoal_tac "Tf (Vf A) \<sqinter> Tf (Vf B) <:: Tf (Vf A @ Vf B)")
     prefer 2 apply (rule append_Tf)
    apply (subgoal_tac "A \<sqinter> B <:: Tf (Vf A) \<sqinter> Tf (Vf B)")
     apply (rule sub_trans) apply blast 
     apply blast apply (rule sub_inter_r) apply (rule sub_inter_left1) apply blast
    apply (rule sub_inter_left2) apply blast done
next
  case 5
  then show ?case  using fty_eq_def by auto 
qed

lemma denot_lam_implies_ts:
  assumes et: "\<forall> v \<rho>. v \<in> E e \<rho> \<longrightarrow> Tenv \<rho> \<turnstile> e : T v" and
       fe: "\<forall>v1 v2. (v1, v2) \<in> set f \<longrightarrow> v2 \<in> E e ((x, v1) # \<rho>)"
  shows "Tenv \<rho> \<turnstile> ELam x e : TFun (Tf f)"
  using et fe
proof (induction f)
  case Nil
  then show ?case by auto
next
  case (Cons a f)
  then show ?case
  proof (cases a)
    case (Pair v v')
    {
      assume 1: "Tenv \<rho> \<turnstile> ELam x e : TFun (Tf f)" and
        2: "\<forall>v \<rho>. v \<in> E e \<rho> \<longrightarrow> Tenv \<rho> \<turnstile> e : T v" and
        3: "\<forall>v1 v2.
          (v1 = v \<and> v2 = v' \<longrightarrow> v' \<in> E e ((x, v) # \<rho>)) \<and>
          ((v1, v2) \<in> set f \<longrightarrow> v2 \<in> E e ((x, v1) # \<rho>))"
      from 3 have 4: "v' \<in> E e ((x,v)#\<rho>)" by simp
      from 2 4 have 5: "Tenv ((x,v)#\<rho>) \<turnstile> e : T v'"
        apply (erule_tac x=v' in allE) apply (erule_tac x="(x,v)#\<rho>" in allE) apply simp done
      from 5 have "(x, T v) # Tenv \<rho> \<turnstile> e : T v'" by simp
    }
    from Cons Pair this show ?thesis
      apply simp apply (rule wt_inter) apply (rule wt_lam) apply blast apply blast done
  qed
qed

theorem denot_implies_ts: 
  assumes ve: "v \<in> E e \<rho>" shows "Tenv \<rho> \<turnstile> e : T v"
  using ve
proof (induction e arbitrary: v \<rho>)
  case (EVar x)
  then show ?case 
    apply simp apply (erule exE) apply (erule conjE)  
    apply (subgoal_tac "lookup (Tenv \<rho>) x = Some (T v')")
     prefer 2 apply (rule lookup_tenv) apply assumption 
    apply (rule wt_sub) apply blast 
    apply (rule le_sub_flip) apply assumption
    done
next
  case (ENat x)
  then show ?case by auto
next
  case (ELam x e)
  then show ?case 
    apply simp apply clarify apply simp
    apply (rule denot_lam_implies_ts)
     apply blast apply blast done
next
  case (EApp e1 e2)
  then show ?case 
    apply simp apply clarify 
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e1 : T (VFun f)") 
     prefer 2 apply assumption apply (subgoal_tac "Tf f <:: T v2' \<rightarrow> T v3'")
     prefer 2 apply (rule table_mem_sub) apply assumption  
    apply (subgoal_tac "Tenv \<rho> \<turnstile> EApp e1 e2 : T v3'") apply (rule wt_sub)
      apply assumption
     apply (rule le_sub_flip) apply assumption
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e1 : TFun (T v2' \<rightarrow> T v3')") prefer 2
     apply (rule wt_sub) apply assumption apply simp apply (rule sub_funty) apply assumption
    apply (rule wt_app) apply assumption   
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e2 : T v2") prefer 2 apply assumption
    apply (rule wt_sub) apply assumption apply (rule le_sub_flip) apply assumption  done
next
  case (EPrim f e1 e2)
  then show ?case 
    apply simp apply clarify
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e1 : T (VNat n1)") prefer 2 apply assumption
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e2 : T (VNat n2)") prefer 2 apply assumption
    apply force done
next
  case (EIf e1 e2 e3)
  then show ?case 
    apply simp apply clarify
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e1 : T (VNat n)") prefer 2 apply assumption
    apply (case_tac n) apply simp
     apply (subgoal_tac "Tenv \<rho> \<turnstile> e3 : T v") prefer 2 apply assumption
     apply blast
    apply simp 
    apply (subgoal_tac "Tenv \<rho> \<turnstile> e2 : T v") prefer 2 apply assumption
    apply (rule wt_ifnz) apply assumption apply simp apply assumption done
qed
    
lemma venv_lookup: assumes lx: "lookup \<Gamma> x = Some A" shows "lookup (Venv \<Gamma>) x = Some (V A)"
  using lx
proof (induction \<Gamma> arbitrary: A)
  case Nil
  then show ?case by auto
next
  case (Cons b \<Gamma>)
  obtain x' B where "b = (x',B)" by (cases b) auto
  with Cons show ?case by (cases "x = x'") auto
qed
  
lemma append_fun_equiv: "\<lbrakk> t1' \<sim> t1; t2' \<sim> t2 \<rbrakk> \<Longrightarrow> t1' @ t2' \<sim> t1 @ t2"
  apply (simp add: val_eq_def fun_eq_def)
  using append_fun_le apply blast 
  done
    
lemma append_eq_symm: "t2 @ t1 \<sim> t1 @ t2"
  unfolding fun_eq_def val_eq_def apply (rule conjI)
   apply (rule append_leq_symm) 
  apply (rule append_leq_symm) 
  done
    
lemma sub_le_flip: "(A <: B \<longrightarrow> V B \<sqsubseteq> V A) \<and> (f1 <:: f2 \<longrightarrow> (Vf f2) \<lesssim> (Vf f1))"
proof (induction rule: subtype_fsubtype.induct)
  case (sub_trans T1 T2 T3)
  then show ?case using fun_le_trans by blast
qed force+
    
theorem ts_implies_denot:
  assumes wte: "\<Gamma> \<turnstile> e : A" shows "V A \<in> E e (Venv \<Gamma>)"
  using wte
proof (induction \<Gamma> e A rule: wt.induct)
  case (wt_var \<Gamma> x T)
  then show ?case 
    apply simp 
    apply (subgoal_tac "lookup (Venv \<Gamma>) x = Some (V T)")
     prefer 2 apply (rule venv_lookup)
     apply assumption
    apply (rule_tac x="V T" in exI)
    apply force
    done
next
  case (wt_sub \<Gamma> e A B)
  then show ?case
    apply (subgoal_tac "V B \<sqsubseteq> V A")
     prefer 2 using sub_le_flip apply blast
    apply (rule e_sub)
     apply auto
    done
qed fastforce+
  
end
  
