section "Soundness of the declarative semantics wrt. operational"

theory DenotSoundFSet
  imports SmallStepLam BigStepLam ChangeEnv
begin

subsection "Substitution preserves denotation"
  
lemma subst_app: "subst x v (EApp e1 e2) = EApp (subst x v e1) (subst x v e2)"
  by auto 
    
lemma subst_prim: "subst x v (EPrim f e1 e2) = EPrim f (subst x v e1) (subst x v e2)"
  by auto 

lemma subst_lam_eq: "subst x v (ELam x e) = ELam x e" by auto 

lemma subst_lam_neq: "y \<noteq> x \<Longrightarrow> subst x v (ELam y e) = ELam y (subst x v e)" by simp 

lemma subst_if: "subst x v (EIf e1 e2 e3) = EIf (subst x v e1) (subst x v e2) (subst x v e3)"
  by auto 

lemma substitution:
  fixes \<Gamma>::env and A::val 
  assumes wte: "B \<in> E e \<Gamma>'" and wtv: "A \<in> E v []"
    and gp: "\<Gamma>' \<approx> (x,A)#\<Gamma>" and v: "is_val v"
  shows "B \<in> E (subst x v e) \<Gamma>"
  using wte wtv gp v
proof (induction arbitrary: v A B \<Gamma> x rule: E.induct)
  case (1 n \<rho>)
  then show ?case by auto
next
  case (2 x \<rho> v A B \<Gamma> x')
  then show ?case 
    apply (simp only: env_eq_def)
    apply (cases "x = x'")
     apply simp apply clarify
     apply (rule env_strengthen)
      apply (rule e_sub)
       apply auto
    done
next
  case (3 x e \<rho> v A B \<Gamma> x')
  then show ?case 
    apply (case_tac "x' = x") apply (simp only: subst_lam_eq)
     apply (rule env_strengthen) apply assumption apply (simp add: env_eq_def) 
    apply (simp only: subst_lam_neq) apply (erule e_lam_elim)
    apply (rule e_lam_intro)
     apply assumption apply clarify apply (erule_tac x=v1 in allE) apply (erule_tac x=v2 in allE)
    apply clarify 
    apply (subgoal_tac "(x,v1)#\<rho> \<approx> (x',A)#(x,v1)#\<Gamma>")
     prefer 2 apply (simp add: env_eq_def)
    apply blast 
    done
next
  case (4 e1 e2 \<rho>)
  then show ?case
    apply (simp only: subst_app)
    apply (erule e_app_elim) 
    apply (rule e_app_intro) 
        apply auto 
    done
next
  case (5 f e1 e2 \<rho>)
  then show ?case 
    apply (simp only: subst_prim) apply (erule e_prim_elim) apply simp 
    apply (rule_tac x=n1 in exI) apply (rule conjI)
     apply force
    apply (rule_tac x=n2 in exI) 
    apply auto
    done
next
  case (6 e1 e2 e3 \<rho>)
  then show ?case 
    apply (simp only: subst_if) apply (erule e_if_elim) apply (rename_tac n)
    apply simp
    apply (case_tac "n = 0") apply (rule_tac x=0 in exI)
     apply force
    apply (rule_tac x=n in exI) apply simp done
qed
 
subsection "Reduction preserves denotation"
  
lemma subject_reduction: fixes e::exp assumes v: "v \<in> E e \<rho>" and r: "e \<longrightarrow> e'" shows "v \<in> E e' \<rho>"
  using r v 
proof (induction arbitrary: v \<rho> rule: reduce.induct)
   case (beta v x e v' \<rho>)
   then show ?case apply (simp only: is_val_def)
     apply (erule e_app_elim) apply (erule e_lam_elim) apply clarify 
     apply (rename_tac f v2 v2' v3' f')
     apply (erule_tac x=v2' in allE) apply (erule_tac x=v3' in allE) apply clarify
     apply (subgoal_tac "v3' \<in> E (subst x v e) \<rho>") prefer 2 apply (rule substitution)
         apply (subgoal_tac "v3' \<in> E e ((x,v2)#\<rho>)") prefer 2 apply (rule raise_env)
           apply assumption apply (simp add: env_le_def) prefer 2 apply (rule env_strengthen)
          apply assumption apply force prefer 2 apply (subgoal_tac "(x,v2)#\<rho> \<approx> (x,v2)#\<rho>") prefer 2
         apply (simp add: env_eq_def) apply assumption apply assumption
      apply simp
     apply simp
     apply (rule e_sub)
      apply assumption
     apply (rule val_le_trans)
      apply blast
     apply force  
     done
qed force+

theorem preservation: assumes v: "v \<in> E e \<rho>" and rr: "e \<longrightarrow>* e'" shows "v \<in> E e' \<rho>"
  using rr v subject_reduction by (induction arbitrary: \<rho> v) auto 

lemma canonical_nat: assumes v: "VNat n \<in> E v \<rho>" and vv: "isval v" shows "v = ENat n"
  using v vv by (cases v) auto

lemma canonical_fun: assumes v: "VFun f \<in> E v \<rho>" and vv: "isval v" shows "\<exists> x e. v = ELam x e"
  using v vv by (cases v) auto

subsection "Progress"

theorem progress: assumes v: "v \<in> E e \<rho>" and r: "\<rho> = []" and fve: "FV e = {}"
  shows "is_val e \<or> (\<exists> e'. e \<longrightarrow> e')"
  using v r fve
proof (induction arbitrary: v rule: E.induct)
  case (4 e1 e2 \<rho>)
  show ?case 
    apply (rule e_app_elim) using 4(3) apply assumption
    apply (cases "is_val e1")
     apply (cases "is_val e2")
      apply (frule canonical_fun) apply force apply (erule exE)+ apply simp apply (rule disjI2) 
      apply (rename_tac x e)
      apply (rule_tac x="subst x e2 e" in exI)
      apply (rule beta) apply simp
    using 4 apply simp 
     apply blast
    using 4 apply simp 
    apply blast done
next
  case (5 f e1 e2 \<rho>)
   show ?case 
     apply (rule e_prim_elim) using 5(3) apply assumption
     using 5 apply (case_tac "isval e1")
      apply (case_tac "isval e2")
       apply (subgoal_tac "e1 = ENat n1") prefer 2 using canonical_nat apply blast 
       apply (subgoal_tac "e2 = ENat n2") prefer 2 using canonical_nat apply blast 
       apply force
      apply force
     apply force done
next
  case (6 e1 e2 e3 \<rho>)
  show ?case
    apply (rule e_if_elim) 
    using 6(4) apply assumption
    apply (cases "isval e1")
     apply (rename_tac n)
     apply (subgoal_tac "e1 = ENat n") prefer 2 apply (rule canonical_nat) apply blast apply blast
     apply (rule disjI2) apply (case_tac "n = 0") apply force apply force 
    apply (rule disjI2)
    using 6 apply (subgoal_tac "\<exists> e1'. e1 \<longrightarrow> e1'") prefer 2 apply force 
    apply clarify apply (rename_tac e1')
    apply (rule_tac x="EIf e1' e2 e3" in exI)
    apply (rule if_cond) apply assumption
    done
qed auto

    
subsection "Logical relation between values and big-step values"

fun good_entry :: "name \<Rightarrow> exp \<Rightarrow> benv \<Rightarrow> (val \<times> bval set) \<times> (val \<times> bval set) \<Rightarrow> bool \<Rightarrow> bool" where
  "good_entry x e \<rho> ((v1,g1),(v2,g2)) r = ((\<forall> v \<in> g1. \<exists> v'. (x,v)#\<rho> \<turnstile> e \<Down> v' \<and> v' \<in> g2) \<and> r)"
 
primrec good :: "val \<Rightarrow> bval set" where
  Gnat: "good (VNat n) = { BNat n }" |
  Gfun: "good (VFun f) = { vc. \<exists> x e \<rho>. vc = BClos x e \<rho> 
          \<and> (ffold (good_entry x e \<rho>) True (fimage (map_prod (\<lambda>v. (v,good v)) (\<lambda>v. (v,good v))) f)) }"

inductive good_env :: "benv \<Rightarrow> env \<Rightarrow> bool" where
  genv_nil[intro!]: "good_env [] []" |
  genv_cons[intro!]: "\<lbrakk> v \<in> good v'; good_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> good_env ((x,v)#\<rho>) ((x,v')#\<rho>')" 
  
inductive_cases 
  genv_any_nil_inv: "good_env \<rho> []" and
  genv_any_cons_inv: "good_env \<rho> (b#\<rho>')" 

lemma lookup_good:
  assumes l: "lookup \<rho>' x = Some A" and EE: "good_env \<rho> \<rho>'"
  shows "\<exists> v. lookup \<rho> x = Some v \<and> v \<in> good A"
  using l EE
proof (induction \<rho>' arbitrary: x A \<rho>)
  case Nil
  show ?case apply (rule genv_any_nil_inv) using Nil by auto
next
  case (Cons a \<rho>')
  show ?case
    apply (rule genv_any_cons_inv) 
     using Cons apply force
    apply (rename_tac x') apply clarify
    using Cons apply (case_tac "x = x'") 
     apply force
    apply force 
    done
qed

abbreviation good_prod :: "val \<times> val \<Rightarrow> (val \<times> bval set) \<times> (val \<times> bval set)" where
  "good_prod \<equiv> map_prod (\<lambda>v. (v,good v)) (\<lambda>v. (v,good v))"
    
lemma good_prod_inj: "inj_on good_prod (fset A)"
  unfolding inj_on_def apply auto done
  
definition good_fun :: "func \<Rightarrow> name \<Rightarrow> exp \<Rightarrow> benv \<Rightarrow> bool" where
  "good_fun f x e \<rho> \<equiv> (ffold (good_entry x e \<rho>) True (fimage good_prod f))"

lemma good_fun_def2:
  "good_fun f x e \<rho> = ffold (good_entry x e \<rho> \<circ> good_prod) True f"
proof -
  interpret ge: comp_fun_commute "(good_entry x e \<rho>) \<circ> good_prod"
    unfolding comp_fun_commute_def by auto  
  show "good_fun f x e \<rho>
         = ffold ((good_entry x e \<rho>) \<circ> good_prod) True f"
     using good_prod_inj[of "f"] good_fun_def
        ffold_fimage[of good_prod "f" "good_entry x e \<rho>" True] by auto
qed

lemma gfun_elim: "w \<in> good (VFun f) \<Longrightarrow> \<exists> x e \<rho>. w = BClos x e \<rho> \<and> good_fun f x e \<rho>"
  using good_fun_def by auto
  
lemma gfun_mem_iff: "good_fun f x e \<rho> = (\<forall> v1 v2. (v1,v2) \<in> fset f \<longrightarrow> 
    (\<forall> v \<in> good v1. \<exists> v'. (x,v)#\<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2))"
proof (induction f arbitrary: x e \<rho>)
  case empty
  interpret ge: comp_fun_commute "(good_entry x e \<rho>)"
    unfolding comp_fun_commute_def by auto
  from empty show ?case using good_fun_def2 by simp
next
  case (insert p f)
  interpret ge: comp_fun_commute "(good_entry x e \<rho>) \<circ> good_prod"
    unfolding comp_fun_commute_def by auto
  have "good_fun (finsert p f) x e \<rho>
         = ffold ((good_entry x e \<rho>) \<circ> good_prod) True (finsert p f)" by (simp add: good_fun_def2)
  also from insert(1) have "... = ((good_entry x e \<rho>) \<circ> good_prod) p 
                  (ffold ((good_entry x e \<rho>) \<circ> good_prod) True f)" by simp
  finally have 1: "good_fun (finsert p f) x e \<rho>
      = ((good_entry x e \<rho>) \<circ> good_prod) p (ffold ((good_entry x e \<rho>) \<circ> good_prod) True f)" .  
  show ?case
  proof
    assume 2: "good_fun (finsert p f) x e \<rho>"
    show "\<forall>v1 v2. (v1, v2) \<in> fset (finsert p f) \<longrightarrow>
       (\<forall>v\<in>good v1. \<exists>v'. (x, v) # \<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2)"
    proof clarify
      fix v1 v2 v assume 3: "(v1, v2) \<in> fset (finsert p f)" and 4: "v \<in> good v1"
      from 3 have "(v1,v2) = p \<or> (v1,v2) \<in> fset f" by auto
      from this show "\<exists>v'. (x, v) # \<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2"
      proof 
        assume v12_p: "(v1,v2) = p"
        from 1 v12_p[THEN sym] 2 4 show ?thesis by simp
      next
        assume v12_f: "(v1,v2) \<in> fset f"
        from 1 2 have 5: "good_fun f x e \<rho>" apply simp 
          apply (cases "(good_prod p)") by (auto simp: good_fun_def2)
        from v12_f 5 4 insert(2)[of x e \<rho>] show ?thesis by auto
      qed
    qed
  next
    assume 2: "\<forall>v1 v2. (v1, v2) \<in> fset (finsert p f) \<longrightarrow>
       (\<forall>v\<in>good v1. \<exists>v'. (x, v) # \<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2)"
    have 3: "good_entry x e \<rho> (good_prod p) True" 
      apply (cases p) apply simp apply clarify
    proof -
      fix v1 v2 v
      assume p: "p = (v1,v2)" and v_v1: "v \<in> good v1"
      from p have "(v1,v2) \<in> fset (finsert p f)" by simp
      from this 2 v_v1 show "\<exists>v'. (x, v) # \<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2" by blast
    qed        
    from insert(2) 2 have 4: "good_fun f x e \<rho>" by auto
    have "(good_entry x e \<rho> \<circ> good_prod) p
     (ffold (good_entry x e \<rho> \<circ> good_prod) True f)" 
      apply simp apply (cases "good_prod p")
      apply (rename_tac a b c)
      apply (case_tac a) apply simp
      apply (rule conjI) prefer 2 using 4 good_fun_def2 apply force
      using 3 apply force done
    from this 1 show "good_fun (finsert p f) x e \<rho>"
       unfolding good_fun_def by simp
  qed
qed
  
lemma gfun_mem: "\<lbrakk> (v1,v2) \<in> fset f; good_fun f x e \<rho> \<rbrakk> 
      \<Longrightarrow> \<forall> v \<in> good v1. \<exists> v'. (x,v)#\<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2"
  using gfun_mem_iff by blast 
  
lemma gfun_intro: "(\<forall> v1 v2.(v1,v2)\<in>fset f\<longrightarrow>(\<forall>v\<in>good v1.\<exists> v'.(x,v)#\<rho> \<turnstile> e \<Down> v'\<and>v'\<in>good v2))
  \<Longrightarrow> good_fun f x e \<rho>" using gfun_mem_iff[of f x e \<rho>] by simp
    
lemma sub_good: fixes v::val assumes wv: "w \<in> good v" and vp_v: "v' \<sqsubseteq> v" shows "w \<in> good v'"
proof (cases v)
  case (VNat n)
  from this wv vp_v show ?thesis by auto
next
  case (VFun t1)
  from vp_v VFun obtain t2 where b: "v' = VFun t2" and t2_t1: "fset t2 \<subseteq> fset t1" by auto
  from wv VFun obtain x e \<rho> where w: "w = BClos x e \<rho>" by auto
  from w wv VFun have gt1: "good_fun t1 x e \<rho>" by (simp add: good_fun_def)          
  have gt2: "good_fun t2 x e \<rho>" apply (rule gfun_intro) apply clarify
  proof -
    fix v1 v2 w1
    assume v12: "(v1,v2) \<in> fset t2" and w1_v1: "w1 \<in> good v1"
    from v12 t2_t1 have v12_t1: "(v1,v2) \<in> fset t1" by blast
    from gt1 v12_t1 w1_v1 show "\<exists>v'. (x, w1) # \<rho> \<turnstile> e \<Down> v' \<and> v' \<in> good v2" 
      by (simp add: gfun_mem)
  qed
  from gt2 b w show ?thesis by (simp add: good_fun_def)
qed

subsection "Denotational semantics sound wrt. big-step"
    
lemma denot_terminates: assumes vp_e: "v' \<in> E e \<rho>'" and ge: "good_env \<rho> \<rho>'" 
  shows "\<exists> v. \<rho> \<turnstile> e \<Down> v \<and> v \<in> good v'"
  using vp_e ge 
proof (induction arbitrary: v' \<rho> rule: E.induct)
  case (1 n \<rho>) \<comment> \<open>ENat\<close>
  then show ?case by auto
next \<comment> \<open>EVar\<close>
  case (2 x \<rho> v' \<rho>')
  from 2 obtain v1 where lx_vpp: "lookup \<rho> x = Some v1" and vp_v1: "v' \<sqsubseteq> v1" by auto
  from lx_vpp 2(2) obtain v2 where lx: "lookup \<rho>' x = Some v2" and v2_v1: "v2 \<in> good v1"
    using lookup_good[of \<rho> x v1 \<rho>'] by blast
  from lx have x_v2: "\<rho>' \<turnstile> EVar x \<Down> v2" by auto
  from v2_v1 vp_v1 have v2_vp: "v2 \<in> good v'" using sub_good by blast
  from x_v2 v2_vp show ?case by blast
next \<comment> \<open>ELam\<close>
  case (3 x e \<rho> v' \<rho>')
  have 1: "\<rho>' \<turnstile> ELam x e \<Down> BClos x e \<rho>'" by auto
  have 2: "BClos x e \<rho>' \<in> good v'"
  proof -
    from 3(2) obtain t where vp: "v' = VFun t" and 
      body: "\<forall>v1 v2. (v1, v2) \<in> fset t \<longrightarrow> v2 \<in> E e ((x, v1) # \<rho>)" by blast
    have gt: "good_fun t x e \<rho>'" apply (rule gfun_intro) apply clarify 
    proof -
      fix v1 v2 w1 assume v12_t: "(v1,v2) \<in> fset t" and w1_v1: "w1 \<in> good v1" 
      from v12_t body have v2_Ee: "v2 \<in> E e ((x, v1) # \<rho>)" by blast
      from 3(3) w1_v1 have ge: "good_env ((x,w1)#\<rho>') ((x,v1)#\<rho>)" by auto
      from v12_t v2_Ee ge 3(1)[of v1 v2 t v2]
      show "\<exists>v'. (x, w1) # \<rho>' \<turnstile> e \<Down> v' \<and> v' \<in> good v2" by blast
    qed
    from vp gt show ?thesis unfolding good_fun_def by simp         
  qed
  from 1 2 show ?case by blast
next \<comment> \<open>EApp\<close>
  case (4 e1 e2 \<rho> v' \<rho>')
  from 4(3) show ?case
  proof
    fix t v2 and v2'::val and v3' assume t_Ee1: "VFun t \<in> E e1 \<rho>" and v2_Ee2: "v2 \<in> E e2 \<rho>" and
      v23_t: "(v2',v3') \<in> fset t" and v2p_v2: "v2' \<sqsubseteq> v2" and vp_v3p: "v' \<sqsubseteq> v3'"
    from 4(1) t_Ee1 4(4) obtain w1 where e1_w1: "\<rho>' \<turnstile> e1 \<Down> w1" and
      w1_t: "w1 \<in> good (VFun t)" by blast
    from 4(2) v2_Ee2 4(4) obtain w2 where e2_w2: "\<rho>' \<turnstile> e2 \<Down> w2" and w2_v2: "w2 \<in> good v2" by blast
    from w1_t obtain x e \<rho>1 where w1: "w1 = BClos x e \<rho>1" and gt: "good_fun t x e \<rho>1"
      by (auto simp: good_fun_def)
    from w2_v2 v2p_v2 have w2_v2p: "w2 \<in> good v2'" by (rule sub_good)
    from v23_t gt w2_v2p obtain w3 where e_w3: "(x,w2)#\<rho>1 \<turnstile> e \<Down> w3" and w3_v3p: "w3 \<in> good v3'"
      using gfun_mem[of v2' v3' t x e \<rho>1] by blast
    from w3_v3p vp_v3p have w3_vp: "w3 \<in> good v'" by (rule sub_good)
    from e1_w1 e2_w2 w1 e_w3 w3_vp show "\<exists>v. \<rho>' \<turnstile> EApp e1 e2 \<Down> v \<and> v \<in> good v'" by blast
  qed
next \<comment> \<open>EPrim\<close>
  case (5 f e1 e2 \<rho> v' \<rho>')
  from 5(3) show ?case
  proof
    fix n1 n2 assume n1_e1: "VNat n1 \<in> E e1 \<rho>" and n2_e2: "VNat n2 \<in> E e2 \<rho>" and
      vp: "v' = VNat (f n1 n2)"
    from 5(1)[of "VNat n1" \<rho>'] n1_e1 5(4) have e1_w1: "\<rho>' \<turnstile> e1 \<Down> BNat n1" by auto
    from 5(2)[of "VNat n2" \<rho>'] n2_e2 5(4) have e2_w2: "\<rho>' \<turnstile> e2 \<Down> BNat n2" by auto
    from e1_w1 e2_w2 have 1: "\<rho>' \<turnstile> EPrim f e1 e2 \<Down> BNat (f n1 n2)" by blast
    from vp have 2: "BNat (f n1 n2) \<in> good v'" by auto
    from 1 2 show "\<exists>v. \<rho>' \<turnstile> EPrim f e1 e2 \<Down> v \<and> v \<in> good v'" by auto
  qed
next \<comment> \<open>EIf\<close>
  case (6 e1 e2 e3 \<rho> v' \<rho>')
  from 6(4) show ?case
  proof
    fix n assume n_e1: "VNat n \<in> E e1 \<rho>" and els: "n = 0 \<longrightarrow> v' \<in> E e3 \<rho>" and
      thn: "n \<noteq> 0 \<longrightarrow> v' \<in> E e2 \<rho>"
    from 6(1)[of "VNat n" \<rho>'] n_e1 6(5) have e1_w1: "\<rho>' \<turnstile> e1 \<Down> BNat n" by auto
    show "\<exists>v. \<rho>' \<turnstile> EIf e1 e2 e3 \<Down> v \<and> v \<in> good v'"
    proof (cases "n = 0")
      case True
      from 6(2)[of n v' \<rho>'] True els 6(5) obtain w3 where 
        e3_w3: "\<rho>' \<turnstile> e3 \<Down> w3" and w3_vp: "w3 \<in> good v'" by blast 
      from e1_w1 True e3_w3 w3_vp show ?thesis by blast
    next
      case False
      from 6(3)[of n v' \<rho>'] False thn 6(5) obtain w2 where 
        e2_w2: "\<rho>' \<turnstile> e2 \<Down> w2" and w2_vp: "w2 \<in> good v'" by blast 
      from e1_w1 False e2_w2 have "\<rho>' \<turnstile> EIf e1 e2 e3 \<Down> w2" 
        using eval_if1[of \<rho>' e1 n e2 w2 e3] by simp
      from this w2_vp show ?thesis by (rule_tac x=w2 in exI) simp
    qed
  qed
qed

theorem sound_wrt_op_sem:
  assumes E_e_n: "E e [] = E (ENat n) []" and fv_e: "FV e = {}" shows "e \<Down> ONat n"
proof -
  have "VNat n \<in> E (ENat n) []" by simp  
  with E_e_n have 1: "VNat n \<in> E e []" by simp
  have 2: "good_env [] []" by auto
  from 1 2 obtain v where e_v: "[] \<turnstile> e \<Down> v" and v_n: "v \<in> good (VNat n)" using denot_terminates by blast
  from v_n have v: "v = BNat n" by auto
  from e_v fv_e obtain v' ob where e_vp: "e \<longrightarrow>* v'" and 
    vp_ob: "observe v' ob" and v_ob: "bs_observe v ob" using sound_wrt_small_step by blast
  from e_vp vp_ob v_ob v show ?thesis unfolding run_def by (case_tac ob) auto
qed

end
