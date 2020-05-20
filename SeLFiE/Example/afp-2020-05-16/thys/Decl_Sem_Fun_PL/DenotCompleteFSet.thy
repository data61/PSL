section "Completeness of the declarative semantics wrt. operational"

theory DenotCompleteFSet
  imports ChangeEnv SmallStepLam DenotSoundFSet
begin

subsection "Reverse substitution preserves denotation"
  
fun join :: "val \<Rightarrow> val \<Rightarrow> val option" (infix "\<squnion>" 60) where
  "(VNat n) \<squnion> (VNat n') = (if n = n' then Some (VNat n) else None)" |
  "(VFun f) \<squnion> (VFun f') = Some (VFun (f |\<union>| f'))" |
  "v \<squnion> v' = None"

lemma combine_values:
  assumes vv: "isval v" and v1v: "v1 \<in> E v \<rho>" and v2v: "v2 \<in> E v \<rho>"
  shows " \<exists> v3. v3 \<in> E v \<rho> \<and> (v1 \<squnion> v2 = Some v3)" 
  using vv v1v v2v by (induction v arbitrary: v1 v2 \<rho>) auto

lemma le_union1: fixes v1::val assumes v12: "v1 \<squnion> v2 = Some v12" shows "v1 \<sqsubseteq> v12"
proof (cases v1)
  case (VNat n1) hence v1: "v1=VNat n1" by simp
  show ?thesis 
  proof (cases v2)
    case (VNat n2) with v1 v12 show ?thesis by (cases "n1=n2") auto
  next
    case (VFun x2) with v1 v12 show ?thesis by auto
  qed
next
  case (VFun t2) from VFun have v1: "v1=VFun t2" by simp
  show ?thesis
  proof (cases v2)
    case (VNat n1) with v1 v12 show ?thesis by auto
  next
    case (VFun n2) with v1 v12 show ?thesis by auto
  qed
qed

lemma le_union2: "v1 \<squnion> v2 = Some v12 \<Longrightarrow> v2 \<sqsubseteq> v12"
  apply (cases v1)
   apply (cases v2)
    apply auto
   apply (rename_tac x1 x1')
   apply (case_tac "x1 = x1'")
    apply auto
  apply (cases v2)
   apply auto
  done

lemma le_union_left: "\<lbrakk> v1 \<squnion> v2 = Some v12; v1 \<sqsubseteq> v3; v2 \<sqsubseteq> v3 \<rbrakk> \<Longrightarrow> v12 \<sqsubseteq> v3"
  apply (cases v1) apply (cases v2) apply force+ done
    
lemma e_val: "isval v \<Longrightarrow> \<exists> v'. v' \<in> E v \<rho>"
  apply (case_tac v) apply auto apply (rule_tac x="{||}" in exI) apply force done

lemma reverse_subst_lam:
  assumes fl: "VFun f \<in> E (ELam x e) \<rho>"
    and vv: "is_val v" and ls: "ELam x e = ELam x (subst y v e')" and xy: "x \<noteq> y" 
    and IH: "\<forall> v1 v2. v2 \<in> E (subst y v e') ((x,v1)#\<rho>) 
        \<longrightarrow> (\<exists> \<rho>' v'. v' \<in> E v [] \<and> v2 \<in> E e' \<rho>' \<and> \<rho>' \<approx> (y,v')#(x,v1)#\<rho>)"
  shows "\<exists> \<rho>' v''. v'' \<in> E v [] \<and> VFun f \<in> E (ELam x e') \<rho>' \<and> \<rho>' \<approx> ((y,v'')#\<rho>)"
  using fl vv ls IH xy 
proof (induction f arbitrary: x e e' \<rho> v y)
  case empty
  from empty(2) is_val_def obtain v' where vp_v: "v' \<in> E v []" using e_val[of v "[]"] by blast
  let ?R = "(y,v')#\<rho>"
  have 1: "VFun {||} \<in> E (ELam x e') ?R" by simp
  have 2: "?R \<approx> (y, v') # \<rho>" by auto
  from vp_v 1 2 show ?case by blast
next
  case (insert a f x e e' \<rho> v y)
  from insert(3) have 1: "VFun f \<in> E (ELam x e) \<rho>" by auto
  obtain v1 v2 where a: "a = (v1,v2)" by (cases a) simp
  from insert 1 have "\<exists> \<rho>' v''. v'' \<in> E v [] \<and> VFun f \<in> E (ELam x e') \<rho>' \<and> \<rho>' \<approx> ((y,v'')#\<rho>)"
    by blast
  from this obtain \<rho>'' v'' where vpp_v: "v'' \<in> E v []" and f_l: "VFun f \<in> E (ELam x e') \<rho>''" 
    and rpp_r: "\<rho>'' \<approx> ((y,v'')#\<rho>)" by blast
  from insert(3) a have v2_e: "v2 \<in> E e ((x,v1)#\<rho>)" using e_lam_elim2 by blast
  from insert v2_e have "\<exists>\<rho>'' v'. v' \<in> E v [] \<and> v2 \<in> E e' \<rho>'' \<and> \<rho>'' \<approx> (y, v')#(x, v1)#\<rho>" by auto
  from this obtain \<rho>3 v' where vp_v: "v' \<in> E v []" and v2_ep: "v2 \<in> E e' \<rho>3" 
    and r3: "\<rho>3 \<approx> (y,v') # (x,v1) # \<rho>" by blast
  from insert(4) have "isval v" by auto
  from this vp_v vpp_v obtain v3 where v3_v: "v3 \<in> E v []" and vp_vpp: "v' \<squnion> v'' = Some v3"
    using combine_values by blast
  have 4: "VFun (finsert a f) \<in> E (ELam x e') ((y, v3) # \<rho>)" 
  proof -
    from vp_vpp have v3_vpp: "v'' \<sqsubseteq> v3" using le_union2 by simp
    from rpp_r v3_vpp have "\<rho>'' \<sqsubseteq> (y,v3)#\<rho>" by (simp add: env_eq_def env_le_def) 
    from f_l this have 2: "VFun f \<in> E (ELam x e') ((y, v3) # \<rho>)" by (rule raise_env) 
    from vp_vpp have vp_v3: "v' \<sqsubseteq> v3" using le_union1 by simp
    from vp_v3 r3 insert have "\<rho>3 \<sqsubseteq> (x,v1)#(y,v3)#\<rho>" by (simp add: env_eq_def env_le_def)
    from v2_ep this have 3: "v2 \<in> E e' ((x,v1)#(y,v3)#\<rho>)" by (rule raise_env)      
    from 2 3 a show "?thesis" using e_lam_intro2 by blast
  qed
  have 5: "(y, v3) # \<rho> \<approx> (y, v3) # \<rho>" by auto
  from v3_v 4 5 show ?case by blast
qed
  
lemma lookup_ext_none: "\<lbrakk> lookup \<rho> y = None; x \<noteq> y \<rbrakk> \<Longrightarrow> lookup ((x,v)#\<rho>) y = None"
  by auto

\<comment> \<open>For reverse subst lemma, the variable case shows up over and over, so we prove it as a lemma\<close>
lemma rev_subst_var:
  assumes ev: "e = EVar y \<and> v = e'" and vv: "is_val v" and vp_E: "v' \<in> E e' \<rho>"
  shows "\<exists> \<rho>' v''. v'' \<in> E v [] \<and> v' \<in> E e \<rho>' \<and> \<rho>' \<approx> ((y,v'')#\<rho>)"
proof -
  from vv have lx: "\<forall> x. x \<in> FV v \<longrightarrow> lookup [] x = lookup \<rho> x" by auto
  from ev vp_E lx env_strengthen[of v' v \<rho> "[]"] have n_Ev: "v' \<in> E v []" by blast 
  have ly: "lookup ((y,v')#\<rho>) y = Some v'" by simp
  from env_eq_def have rr: "((y,v')#\<rho>) \<approx> ((y,v')#\<rho>)" by simp
  from ev ly have n_Ee: "v' \<in> E e ((y,v')#\<rho>)" by simp 
  from n_Ev rr n_Ee show ?thesis by blast
qed
  
lemma reverse_subst_pres_denot:
  assumes vep: "v' \<in> E e' \<rho>" and vv: "is_val v" and ep: "e' = subst y v e"
  shows "\<exists> \<rho>' v''. v'' \<in> E v [] \<and> v' \<in> E e \<rho>' \<and> \<rho>' \<approx> ((y,v'')#\<rho>)"
  using vep vv ep 
proof  (induction arbitrary: v' y v e rule: E.induct)
  case (1 n \<rho>) \<comment> \<open>e' = ENat n\<close>
  from 1(1) have vp: "v' = VNat n" by auto 
  from 1(3) have "e = ENat n \<or> (e = EVar y \<and> v = ENat n)" by (cases e, auto)
  then show ?case
  proof
    assume e: "e = ENat n"
    from 1(2) e_val is_val_def obtain v'' where vpp_E: "v'' \<in> E v []" by force
    from env_eq_def have rr: "((y,v'')#\<rho>) \<approx> ((y,v'')#\<rho>)" by simp
    from vp e have vp_E: "v' \<in> E e ((y,v'')#\<rho>)" by simp
    from vpp_E vp_E rr show ?thesis by blast 
  next
    assume ev: "e = EVar y \<and> v = ENat n"
    from ev 1(2) 1(1) rev_subst_var show ?thesis by blast
  qed
next
  case (2 x \<rho>) \<comment> \<open>e' = EVar x\<close>
  from 2 have e: "e = EVar x" by (cases e, auto)
  from 2 e have xy: "x \<noteq> y" by force
  from 2(2) e_val is_val_def obtain v'' where vpp_E: "v'' \<in> E v []" by force
  from env_eq_def have rr: "((y,v'')#\<rho>) \<approx> ((y,v'')#\<rho>)" by simp
  from 2(1) obtain vx where lx: "lookup \<rho> x = Some vx" and vp_vx: "v' \<sqsubseteq> vx" by auto
  from e lx vp_vx xy have vp_E: "v' \<in> E e ((y,v'')#\<rho>)" by simp 
  from vpp_E rr vp_E show ?case by blast
next
  case (3 x eb \<rho>)
  { assume ev: "e = EVar y \<and> v = ELam x eb"
    from ev 3(3) 3(2) rev_subst_var have ?case by blast
  } also { assume ex: "e = ELam x eb \<and> x = y" 
    from 3(3) e_val is_val_def obtain v'' where vpp_E: "v'' \<in> E v []" by force
    from env_eq_def have rr: "((y,v'')#\<rho>) \<approx> ((y,v'')#\<rho>)" by simp
    from ex have lz: "\<forall> z. z \<in> FV (ELam x eb) \<longrightarrow> lookup ((y,v'')#\<rho>) z = lookup \<rho> z" by auto
    from ex 3(2) lz env_strengthen[of v' "ELam x eb" \<rho> "(y,v'')#\<rho>"]
    have vp_E: "v' \<in> E e ((y,v'')#\<rho>)" by blast
    from vpp_E vp_E rr have ?case by blast 
  } moreover { assume exb: "\<exists> e'. e = ELam x e' \<and> x \<noteq> y \<and> eb = subst y v e'" 
    from exb obtain e'' where e: "e = ELam x e''" and xy: "x \<noteq> y" 
      and eb: "eb = subst y v e''" by blast
    from 3(2) obtain f where vp: "v' = VFun f" by auto 
    from 3(2) vp have f_E: "VFun f \<in> E (ELam x eb) \<rho>" by simp
    from 3(4) e xy have ls: "ELam x eb = ELam x (subst y v e'')" by simp
    from 3(3) eb have IH: "\<forall> v1 v2. v2 \<in> E (subst y v e'') ((x,v1)#\<rho>) 
        \<longrightarrow> (\<exists> \<rho>' v'. v' \<in> E v [] \<and> v2 \<in> E e'' \<rho>' \<and> \<rho>' \<approx> (y,v')#(x,v1)#\<rho>)"
      apply clarify apply (subgoal_tac "(v1,v2) \<in> fset {|(v1,v2)|}") prefer 2 apply simp
      apply (rule 3(1)) apply assumption apply simp+ done
    from f_E 3(3) ls xy IH e vp have ?case apply clarify apply (rule reverse_subst_lam)
        apply blast+ done
  } moreover from 3(4) have "(e = EVar y \<and> v = ELam x eb)
      \<or> (e = ELam x eb \<and> x = y)
      \<or> (\<exists> e'. e = ELam x e' \<and> x \<noteq> y \<and> eb = subst y v e')" by (cases e) auto
  ultimately show ?case by blast 
next
  case (4 e1 e2 \<rho>) \<comment> \<open>e' = EApp e1 e2\<close>
  from 4(4) 4(5) obtain e1' e2' where 
    e: "e = EApp e1' e2'" and e1:"e1 = subst y v e1'" and e2: "e2 = subst y v e2'"
    apply (cases e) apply (rename_tac x) apply auto apply (case_tac "y = x") apply auto 
    apply (rename_tac x1 x2) apply (case_tac "y = x1") apply auto done
  from 4(3) obtain f v2 and v2'::val and v3' where
    f_E: "VFun f \<in> E e1 \<rho>" and v2_E: "v2 \<in> E e2 \<rho>" and v23: "(v2',v3') \<in> fset f" 
    and v2p_v2: "v2' \<sqsubseteq> v2" and vp_v3: "v' \<sqsubseteq> v3'" by blast
  from 4(1) f_E 4(4) e1 obtain \<rho>1 w1 where v1_Ev: "w1 \<in> E v []" and f_E1: "VFun f \<in> E e1' \<rho>1"
    and r1: "\<rho>1 \<approx> (y,w1)#\<rho>" by blast
  from 4(2) v2_E 4(4) e2 obtain \<rho>2 w2 where v2_Ev: "w2 \<in> E v []" and v2_E2: "v2 \<in> E e2' \<rho>2"
    and r2: "\<rho>2 \<approx> (y,w2)#\<rho>" by blast 
  from 4(4) v1_Ev v2_Ev combine_values obtain w3 where 
    w3_Ev: "w3 \<in> E v []" and w123: "w1 \<squnion> w2 = Some w3" by (simp only: is_val_def) blast 
  from w123 le_union1 have w13: "w1 \<sqsubseteq> w3" by blast
  from w123 le_union2 have w23: "w2 \<sqsubseteq> w3" by blast
  from w13 have r13: "((y,w1)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
  from w23 have r23: "((y,w2)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
  from r1 f_E1 have f_E1b: "VFun f \<in> E e1' ((y,w1)#\<rho>)" by (rule env_swap)
  from f_E1b r13 have f_E1c: "VFun f \<in> E e1' ((y,w3)#\<rho>)" by (rule raise_env)
  from r2 v2_E2 have v2_E2b: "v2 \<in> E e2' ((y,w2)#\<rho>)" by (rule env_swap)
  from v2_E2b r23 have v2_E2c: "v2 \<in> E e2' ((y,w3)#\<rho>)" by (rule raise_env)
  from f_E1c v2_E2c v23 v2p_v2 vp_v3 have vp_E2: "v' \<in> E (EApp e1' e2') ((y,w3)#\<rho>)" by blast
  have rr3: "((y,w3)#\<rho>) \<approx> ((y,w3)#\<rho>)" by (simp add: env_eq_def) 
  from w3_Ev vp_E2 rr3 e show ?case by blast
next
  case (5 f e1 e2 \<rho>) \<comment> \<open>e' = EPrim f e1 e2, very similar to case for EApp\<close>
  from 5(4) 5(5) obtain e1' e2' where 
    e: "e = EPrim f e1' e2'" and e1:"e1 = subst y v e1'" and e2: "e2 = subst y v e2'"
    apply (cases e) apply auto apply (rename_tac x) apply (case_tac "y = x") apply auto 
    apply (rename_tac x1 x2) apply (case_tac "y = x1") apply auto done
  from 5(3) obtain n1 n2 where
    n1_E: "VNat n1 \<in> E e1 \<rho>" and n2_E: "VNat n2 \<in> E e2 \<rho>" and vp: "v' = VNat (f n1 n2)" by blast
  from 5(1) n1_E 5(4) e1 obtain \<rho>1 w1 where v1_Ev: "w1 \<in> E v []" and n1_E1: "VNat n1 \<in> E e1' \<rho>1"
    and r1: "\<rho>1 \<approx> (y,w1)#\<rho>" by blast 
  from 5(2) n2_E 5(4) e2 obtain \<rho>2 w2 where v2_Ev: "w2 \<in> E v []" and n2_E2: "VNat n2 \<in> E e2' \<rho>2"
    and r2: "\<rho>2 \<approx> (y,w2)#\<rho>" by blast 
  from 5(4) v1_Ev v2_Ev combine_values obtain w3 where 
    w3_Ev: "w3 \<in> E v []" and w123: "w1 \<squnion> w2 = Some w3" by (simp only: is_val_def) blast 
  from w123 le_union1 have w13: "w1 \<sqsubseteq> w3" by blast
  from w123 le_union2 have w23: "w2 \<sqsubseteq> w3" by blast
  from w13 have r13: "((y,w1)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
  from w23 have r23: "((y,w2)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
  from r1 n1_E1 have n1_E1b: "VNat n1 \<in> E e1' ((y,w1)#\<rho>)" by (rule env_swap)
  from n1_E1b r13 have n1_E1c: "VNat n1 \<in> E e1' ((y,w3)#\<rho>)" by (rule raise_env)
  from r2 n2_E2 have n2_E2b: "VNat n2 \<in> E e2' ((y,w2)#\<rho>)" by (rule env_swap)
  from n2_E2b r23 have v2_E2c: "VNat n2 \<in> E e2' ((y,w3)#\<rho>)" by (rule raise_env)
  from n1_E1c v2_E2c vp have vp_E2: "v' \<in> E (EPrim f e1' e2') ((y,w3)#\<rho>)" by blast
  have rr3: "((y,w3)#\<rho>) \<approx> ((y,w3)#\<rho>)" by (simp add: env_eq_def) 
  from w3_Ev vp_E2 rr3 e show ?case by blast
next
  case (6 e1 e2 e3 \<rho>) \<comment> \<open>e' = EIf e1 e2 e3\<close>
  from 6(5) 6(6) obtain e1' e2' e3' where 
    e: "e = EIf e1' e2' e3'" and e1:"e1 = subst y v e1'" and e2: "e2 = subst y v e2'"
    and e3: "e3 = subst y v e3'" 
    apply (cases e) apply auto apply (case_tac "y=x1") apply auto apply (case_tac "y=x31") by auto
  from 6(4) e_if_elim obtain n where n_E: "VNat n \<in> E e1 \<rho>" and 
    els: "n = 0 \<longrightarrow> v' \<in> E e3 \<rho>" and thn: "n \<noteq> 0 \<longrightarrow> v' \<in> E e2 \<rho>" by blast
  from 6 n_E e1 obtain \<rho>1 w1 where w1_Ev: "w1 \<in> E v []" and n_E2: "VNat n \<in> E e1' \<rho>1"
    and r1: "\<rho>1 \<approx> (y,w1)#\<rho>" by blast
  show ?case
  proof (cases "n = 0")
    case True with els have vp_E2: "v' \<in> E e3 \<rho>" by simp
    from 6 vp_E2 e3 obtain \<rho>2 w2 where w2_Ev: "w2 \<in> E v []" and vp_E2: "v' \<in> E e3' \<rho>2"
    and r2: "\<rho>2 \<approx> (y,w2)#\<rho>" by blast
    from 6(5) w1_Ev w2_Ev combine_values obtain w3 where 
      w3_Ev: "w3 \<in> E v []" and w123: "w1 \<squnion> w2 = Some w3" by (simp only: is_val_def) blast 
    from w123 le_union1 have w13: "w1 \<sqsubseteq> w3" by blast
    from w123 le_union2 have w23: "w2 \<sqsubseteq> w3" by blast
    from w13 have r13: "((y,w1)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
    from w23 have r23: "((y,w2)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
    from r1 n_E2 have n_E1b: "VNat n \<in> E e1' ((y,w1)#\<rho>)" by (rule env_swap)
    from n_E1b r13 have n_E1c: "VNat n \<in> E e1' ((y,w3)#\<rho>)" by (rule raise_env)
    from r2 vp_E2 have vp_E2b: "v' \<in> E e3' ((y,w2)#\<rho>)" by (rule env_swap)
    from vp_E2b r23 have vp_E2c: "v' \<in> E e3' ((y,w3)#\<rho>)" by (rule raise_env)
    have rr3: "((y,w3)#\<rho>) \<approx> ((y,w3)#\<rho>)" by (simp add: env_eq_def) 
    from True n_E1c vp_E2c e have vp_E3: "v' \<in> E e ((y,w3)#\<rho>)" by auto 
    from w3_Ev rr3 vp_E3 show ?thesis by blast
  next
    case False with thn have vp_E2: "v' \<in> E e2 \<rho>" by simp
    from 6 vp_E2 e2 obtain \<rho>2 w2 where w2_Ev: "w2 \<in> E v []" and vp_E2: "v' \<in> E e2' \<rho>2"
    and r2: "\<rho>2 \<approx> (y,w2)#\<rho>" by blast
    from 6(5) w1_Ev w2_Ev combine_values obtain w3 where 
      w3_Ev: "w3 \<in> E v []" and w123: "w1 \<squnion> w2 = Some w3" by (simp only: is_val_def) blast 
    from w123 le_union1 have w13: "w1 \<sqsubseteq> w3" by blast
    from w123 le_union2 have w23: "w2 \<sqsubseteq> w3" by blast
    from w13 have r13: "((y,w1)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
    from w23 have r23: "((y,w2)#\<rho>) \<sqsubseteq> ((y,w3)#\<rho>)" by (simp add: env_le_def)
    from r1 n_E2 have n_E1b: "VNat n \<in> E e1' ((y,w1)#\<rho>)" by (rule env_swap)
    from n_E1b r13 have n_E1c: "VNat n \<in> E e1' ((y,w3)#\<rho>)" by (rule raise_env)
    from r2 vp_E2 have vp_E2b: "v' \<in> E e2' ((y,w2)#\<rho>)" by (rule env_swap)
    from vp_E2b r23 have vp_E2c: "v' \<in> E e2' ((y,w3)#\<rho>)" by (rule raise_env)
    have rr3: "((y,w3)#\<rho>) \<approx> ((y,w3)#\<rho>)" by (simp add: env_eq_def) 
    from False n_E1c vp_E2c e have vp_E3: "v' \<in> E e ((y,w3)#\<rho>)" by auto 
    from w3_Ev rr3 vp_E3 show ?thesis by blast
  qed
qed
  
subsection "Reverse reduction preserves denotation"

lemma reverse_step_pres_denot:
  fixes e::exp assumes e_ep: "e \<longrightarrow> e'" and v_ep: "v \<in> E e' \<rho>"
  shows "v \<in> E e \<rho>"
  using e_ep v_ep
proof (induction arbitrary: v \<rho> rule: reduce.induct)
  case (beta v x e v' \<rho>)
  from beta obtain \<rho>' v'' where 1: "v'' \<in> E v []" and 2: "v' \<in> E e \<rho>'" and 3: "\<rho>' \<approx> (x, v'') # \<rho>"
    using reverse_subst_pres_denot[of v' "subst x v e" \<rho> v x e] by blast
  from beta 1 2 3 show ?case
    apply simp apply (rule_tac x="{|(v'',v')|}" in exI) apply (rule conjI)
     apply clarify apply simp apply clarify apply (rule env_swap) apply blast apply blast 
    apply (rule_tac x=v'' in exI) apply (rule conjI) apply (rule env_strengthen)
      apply assumption apply force apply force done
qed auto
    
lemma reverse_multi_step_pres_denot:
  fixes e::exp assumes e_ep: "e \<longrightarrow>* e'" and v_ep: "v \<in> E e' \<rho>" shows "v \<in> E e \<rho>" 
  using e_ep v_ep reverse_step_pres_denot
  by (induction arbitrary: v \<rho> rule: multi_step.induct) auto 

subsection "Completeness"

theorem completeness:
  assumes ev: "e \<longrightarrow>* v"and vv: "is_val v"
  shows "\<exists> v'. v' \<in> E e \<rho> \<and> v' \<in> E v []"
proof -
  from vv have "\<exists> v'. v' \<in> E v []" using e_val by auto 
  from this obtain v' where vp_v: "v' \<in> E v []" by blast
  from vp_v vv have vp_v2: "v' \<in> E v \<rho>" using env_strengthen by force 
  from ev vp_v2 reverse_multi_step_pres_denot[of e v v' \<rho>]
  have "v' \<in> E e \<rho>" by simp 
  from this vp_v show ?thesis by blast 
qed

theorem reduce_pres_denot: fixes e::exp assumes r: "e \<longrightarrow> e'" shows "E e = E e'"
  apply (rule ext) apply (rule equalityI) apply (rule subsetI) 
   apply (rule subject_reduction) apply assumption using r apply assumption
  apply (rule subsetI) 
  using r apply (rule reverse_step_pres_denot) apply assumption
  done

theorem multi_reduce_pres_denot: fixes e::exp assumes r: "e \<longrightarrow>* e'" shows "E e = E e'"
  using r reduce_pres_denot by induction auto

theorem complete_wrt_op_sem:
  assumes e_n: "e \<Down> ONat n" shows "E e [] = E (ENat n) []"
proof -
  from e_n have 1: "e \<longrightarrow>* ENat n"
    unfolding run_def apply simp apply (erule exE)
    apply (rename_tac v) apply (case_tac v) apply auto done
  from 1 show ?thesis using multi_reduce_pres_denot by simp
qed

end
