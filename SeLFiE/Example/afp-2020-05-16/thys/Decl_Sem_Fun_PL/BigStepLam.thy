section "Big-step semantics of CBV lambda calculus"

theory BigStepLam
  imports Lambda SmallStepLam
begin

datatype bval
  = BNat nat
  | BClos name exp "(name \<times> bval) list"

type_synonym benv = "(name \<times> bval) list"

inductive eval :: "benv \<Rightarrow> exp \<Rightarrow> bval \<Rightarrow> bool" ("_ \<turnstile> _ \<Down> _" [50,50,50] 51) where
  eval_nat[intro!]: "\<rho> \<turnstile> ENat n \<Down> BNat n" |
  eval_var[intro!]: "lookup \<rho> x = Some v \<Longrightarrow> \<rho> \<turnstile> EVar x \<Down> v" |
  eval_lam[intro!]: "\<rho> \<turnstile> ELam x e \<Down> BClos x e \<rho>" |
  eval_app[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Down> BClos x e \<rho>'; \<rho> \<turnstile> e2 \<Down> arg;
                       (x,arg)#\<rho>' \<turnstile> e \<Down> v \<rbrakk> \<Longrightarrow> 
                      \<rho> \<turnstile> EApp e1 e2 \<Down> v" |
  eval_prim[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Down> BNat n1; \<rho> \<turnstile> e2 \<Down> BNat n2 ; n3 = f n1 n2\<rbrakk> \<Longrightarrow>
                       \<rho> \<turnstile> EPrim f e1 e2 \<Down> BNat n3" |
  eval_if0[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Down> BNat 0; \<rho> \<turnstile> e3 \<Down> v3 \<rbrakk> \<Longrightarrow> 
                      \<rho> \<turnstile> EIf e1 e2 e3 \<Down> v3" |
  eval_if1[intro!]: "\<lbrakk> \<rho> \<turnstile> e1 \<Down> BNat n; n \<noteq> 0; \<rho> \<turnstile> e2 \<Down> v2 \<rbrakk> \<Longrightarrow>
                      \<rho> \<turnstile> EIf e1 e2 e3 \<Down> v2"

inductive_cases 
  eval_nat_inv[elim!]: "\<rho> \<turnstile> ENat n \<Down> v" and
  eval_var_inv[elim!]: "\<rho> \<turnstile> EVar x \<Down> v" and
  eval_lam_inv[elim!]: "\<rho> \<turnstile> ELam x e \<Down> v" and
  eval_app_inv[elim!]: "\<rho> \<turnstile> EApp e1 e2 \<Down> v" and
  eval_prim_inv[elim!]: "\<rho> \<turnstile> EPrim f e1 e2 \<Down> v" and
  eval_if_inv[elim!]: "\<rho> \<turnstile> EIf e1 e2 e3 \<Down> v" 

subsection "Big-step semantics is sound wrt. small-step semantics"
  
type_synonym env = "(name \<times> exp) list"   
  
fun psubst :: "env \<Rightarrow> exp \<Rightarrow> exp" where
  "psubst \<rho> (ENat n) = ENat n" |
  "psubst \<rho> (EVar x) = 
     (case lookup \<rho> x of
       None \<Rightarrow> EVar x
     | Some v \<Rightarrow> v)" |
  "psubst \<rho> (ELam x e) = ELam x (psubst ((x,EVar x)#\<rho>) e)" |
  "psubst \<rho> (EApp e1 e2) = EApp (psubst \<rho> e1) (psubst \<rho> e2)" |
  "psubst \<rho> (EPrim f e1 e2) = EPrim f (psubst \<rho> e1) (psubst \<rho> e2)" |
  "psubst \<rho> (EIf e1 e2 e3) = EIf (psubst \<rho> e1) (psubst \<rho> e2) (psubst \<rho> e3)" 


inductive bs_val :: "bval \<Rightarrow> exp \<Rightarrow> bool" and
  bs_env :: "benv \<Rightarrow> env \<Rightarrow> bool" where
  bs_nat[intro!]: "bs_val (BNat n) (ENat n)" |
  bs_clos[intro!]: "\<lbrakk> bs_env \<rho> \<rho>'; FV (ELam x (psubst ((x,EVar x)#\<rho>') e)) = {} \<rbrakk> \<Longrightarrow> 
                    bs_val (BClos x e \<rho>) (ELam x (psubst ((x,EVar x)#\<rho>') e))" |  
  bs_nil[intro!]: "bs_env [] []" |
  bs_cons[intro!]: "\<lbrakk> bs_val w v; bs_env \<rho> \<rho>' \<rbrakk> \<Longrightarrow> bs_env ((x,w)#\<rho>) ((x,v)#\<rho>')" 
  
inductive_cases bs_env_inv1[elim!]: "bs_env ((x, w) # \<rho>) \<rho>'" and
  bs_clos_inv[elim!]: "bs_val (BClos x e \<rho>'') v1" and
  bs_nat_inv[elim!]: "bs_val (BNat n) v"
  
lemma bs_val_is_val[intro!]: "bs_val w v \<Longrightarrow> is_val v"
  by (cases w) auto
  
lemma lookup_bs_env: "\<lbrakk> bs_env \<rho> \<rho>'; lookup \<rho> x = Some w \<rbrakk> \<Longrightarrow> 
  \<exists> v. lookup \<rho>' x = Some v \<and> bs_val w v"
  by (induction \<rho> arbitrary: \<rho>' x w) auto 

lemma app_red_cong1: "e1 \<longrightarrow>* e1' \<Longrightarrow> EApp e1 e2 \<longrightarrow>* EApp e1' e2" 
  by (induction rule: multi_step.induct) blast+  

lemma app_red_cong2: "e2 \<longrightarrow>* e2' \<Longrightarrow> EApp e1 e2 \<longrightarrow>* EApp e1 e2'" 
  by (induction rule: multi_step.induct) blast+ 
    
lemma prim_red_cong1: "e1 \<longrightarrow>* e1' \<Longrightarrow> EPrim f e1 e2 \<longrightarrow>* EPrim f e1' e2"
  by (induction rule: multi_step.induct) blast+
    
lemma prim_red_cong2: "e2 \<longrightarrow>* e2' \<Longrightarrow> EPrim f e1 e2 \<longrightarrow>* EPrim f e1 e2'" 
  by (induction rule: multi_step.induct) blast+ 

lemma if_red_cong1: "e1 \<longrightarrow>* e1' \<Longrightarrow> EIf e1 e2 e3 \<longrightarrow>* EIf e1' e2 e3" 
  by (induction rule: multi_step.induct) blast+

lemma multi_step_trans: "\<lbrakk> e1 \<longrightarrow>* e2; e2 \<longrightarrow>* e3 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"
proof (induction arbitrary: e3 rule: multi_step.induct)
  case (ms_cons e1 e2 e3 e3')
  then have "e2 \<longrightarrow>* e3'" by auto
  with ms_cons(1) show ?case by blast 
qed blast
    
lemma subst_id_fv: "x \<notin> FV e \<Longrightarrow> subst x v e = e"
  by (induction e arbitrary: x v) auto

definition sdom :: "env \<Rightarrow> name set" where
  "sdom \<rho> \<equiv> {x. \<exists> v. lookup \<rho> x = Some v \<and> v \<noteq> EVar x }"
  
definition closed_env :: "env \<Rightarrow> bool" where
  "closed_env \<rho> \<equiv> (\<forall> x v. x \<in> sdom \<rho> \<longrightarrow> lookup \<rho> x = Some v \<longrightarrow> FV v = {})"

definition equiv_env :: "env \<Rightarrow> env \<Rightarrow> bool" where
  "equiv_env \<rho> \<rho>' \<equiv> (sdom \<rho> = sdom \<rho>' \<and> (\<forall> x. x \<in> sdom \<rho> \<longrightarrow> lookup \<rho> x = lookup \<rho>' x))"

lemma sdom_cons_xx[simp]: "sdom ((x,EVar x)#\<rho>) = sdom \<rho> - {x}" 
  unfolding sdom_def by auto

lemma sdom_cons_v[simp]: "FV v = {} \<Longrightarrow> sdom ((x,v)#\<rho>) = insert x (sdom \<rho>)" 
  unfolding sdom_def by auto

lemma lookup_some_in_dom: "\<lbrakk> lookup \<rho> x = Some v; v \<noteq> EVar x \<rbrakk> \<Longrightarrow> x \<in> sdom \<rho>"
proof (induction \<rho>)
  case (Cons b \<rho>)
  show ?case
  proof (cases b)
    case (Pair y v')
    with Cons show ?thesis unfolding sdom_def by auto
  qed
qed auto

lemma lookup_none_notin_dom: "lookup \<rho> x = None \<Longrightarrow> x \<notin> sdom \<rho>"
proof (induction \<rho>)
  case (Cons b \<rho>)
  show ?case
  proof (cases b)
    case (Pair y v)
    with Cons show ?thesis unfolding sdom_def by auto
  qed
qed (auto simp: sdom_def)
  
lemma psubst_change: "equiv_env \<rho> \<rho>' \<Longrightarrow> psubst \<rho> e = psubst \<rho>' e"
proof (induction e arbitrary: \<rho> \<rho>')
  case (EVar x)
  show ?case
  proof (cases "lookup \<rho> x")
    case None from None have lx: "lookup \<rho> x = None" by simp
    show ?thesis
    proof (cases "lookup \<rho>' x")
      case None
      with EVar lx show ?thesis by auto
    next
      case (Some v)
      from EVar lx Some have "x \<notin> sdom \<rho>'" unfolding equiv_env_def by auto
      with lx Some show ?thesis unfolding sdom_def by simp 
    qed
  next
    case (Some v) from Some have lx: "lookup \<rho> x = Some v" by simp
    show ?thesis
    proof (cases "lookup \<rho>' x")
      case None
      from EVar lx None have "x \<notin> sdom \<rho>" unfolding equiv_env_def by auto
      with None Some show ?thesis unfolding sdom_def by simp
    next
      case (Some v')
      from EVar Some lx show ?thesis by (simp add: equiv_env_def sdom_def) force
    qed 
  qed
next
  case (ELam x' e)
  from ELam(2) have "equiv_env ((x',EVar x')#\<rho>) ((x',EVar x')#\<rho>')" by (simp add: equiv_env_def)
  with ELam show ?case by (simp add: equiv_env_def)
qed fastforce+

lemma subst_psubst: "\<lbrakk> closed_env \<rho>; FV v = {} \<rbrakk> \<Longrightarrow> 
    subst x v (psubst ((x, EVar x) # \<rho>) e) = psubst ((x, v) # \<rho>) e"
proof (induction e arbitrary: x v \<rho>)
  case (EVar x x' v \<rho>)
  show ?case
  proof (cases "x = x'")
    case True
    then show ?thesis by force 
  next
    case False from False have xxp: "x \<noteq> x'" by simp
    show ?thesis
    proof (cases "lookup \<rho> x")
      case None
      then show ?thesis by auto
    next
      case (Some v')
      show ?thesis
      proof (cases "v' = EVar x")
        case True
        with Some show ?thesis by auto
      next
        case False
        from False Some have xdom: "x \<in> sdom \<rho>" using lookup_some_in_dom by simp
        from this EVar Some have "FV v' = {}" using closed_env_def by blast
        from this Some show ?thesis using subst_id_fv by auto 
      qed
    qed
  qed
next
  case (ELam x' e)
  show ?case
  proof (cases "x = x'")
    case True
    then show ?thesis apply simp apply (rule psubst_change)
      using equiv_env_def sdom_def by auto
  next
    case False
    then show ?thesis apply simp
    proof -
      assume x_xp: "x \<noteq> x'"
      let ?r = "(x',EVar x') # \<rho>"
      from ELam have IHprem: "closed_env ((x', EVar x') # \<rho>)" using closed_env_def by auto          
      have "psubst ((x',EVar x')#(x, EVar x)#\<rho>) e = psubst ((x,EVar x)#(x',EVar x') # \<rho>) e"
        apply (rule psubst_change) using x_xp equiv_env_def by auto
      from this have "subst x v (psubst ((x', EVar x') # (x, EVar x) # \<rho>) e)
                       = subst x v (psubst ((x,EVar x)#(x',EVar x') # \<rho>) e)" by simp         
      also with ELam IHprem have "... = psubst ((x,v)#(x',EVar x')#\<rho>) e"
        using ELam(1)[of "(x',EVar x')#\<rho>" v x] by simp
      also have "... = psubst ((x',EVar x')#(x,v)#\<rho>) e"
        apply (rule psubst_change) using x_xp equiv_env_def sdom_def by auto
      finally show "subst x v (psubst ((x', EVar x') # (x, EVar x) # \<rho>) e)
                    = psubst ((x', EVar x') # (x,v) # \<rho>) e" .
    qed
  qed
qed fastforce+

inductive_cases bsenv_nil[elim!]: "bs_env [] \<rho>'" 
 
lemma bs_env_dom: "bs_env \<rho> \<rho>' \<Longrightarrow> set (map fst \<rho>) = sdom \<rho>'"
proof (induction \<rho> arbitrary: \<rho>')
  case Nil
  then show ?case by (force simp: sdom_def)
next
  case (Cons b \<rho>)
  then show ?case
  proof (cases b)
    case (Pair x v')
    with Cons show ?thesis by (cases v') force+
  qed
qed 
    
lemma closed_env_cons[intro!]: "FV v = {} \<Longrightarrow> closed_env \<rho>'' \<Longrightarrow> closed_env ((a, v) # \<rho>'')"
  by (simp add: closed_env_def sdom_def)   

lemma bs_env_closed: "bs_env \<rho> \<rho>' \<Longrightarrow> closed_env \<rho>'"
proof (induction \<rho> arbitrary: \<rho>')
  case Nil
  then show ?case by (force simp: closed_env_def)
next
  case (Cons b \<rho>)
  from Cons obtain x v v' \<rho>'' where b: "b = (x,v)" and rp: "\<rho>' = (x,v')#\<rho>''"
    and vvp: "bs_val v v'" and r_rpp: "bs_env \<rho> \<rho>''" by (cases b) blast
  from vvp have "is_val v'" by blast
  from this have fv_vp: "FV v' = {}" by auto
  from Cons r_rpp have "closed_env \<rho>''" by blast
  from this rp fv_vp show ?case by blast
qed
  
lemma psubst_fv: "closed_env \<rho> \<Longrightarrow> FV (psubst \<rho> e) = FV e - sdom \<rho>" 
proof (induction e arbitrary: \<rho>)
  case (EVar x)
  then show ?case
    apply (simp add: closed_env_def)
    apply (cases "x \<in> sdom \<rho>")  
     apply (erule_tac x=x in allE)
     apply (erule impE) apply blast apply (simp add: sdom_def) apply clarify  
     apply force
    apply (simp add: sdom_def)
    apply (cases "lookup \<rho> x")
     apply force
    apply force
    done
next
  case (ELam x e)
  from ELam have "closed_env ((x, EVar x) # \<rho>)" by (simp add: closed_env_def sdom_def)
  from this ELam show ?case by auto
qed fastforce+
    
lemma big_small_step:
  assumes ev: "\<rho> \<turnstile> e \<Down> w" and r_rp: "bs_env \<rho> \<rho>'" and fv_e: "FV e \<subseteq> set (map fst \<rho>)"
  shows "\<exists> v. psubst \<rho>' e \<longrightarrow>* v \<and> is_val v \<and> bs_val w v"
  using ev r_rp fv_e
proof (induction arbitrary: \<rho>' rule: eval.induct)
  case (eval_nat \<rho> n \<rho>')
  then show ?case by (rule_tac x="ENat n" in exI) auto 
next
  case (eval_var \<rho> x w \<rho>')
  from eval_var obtain v where lx: "lookup \<rho>' x = Some v" and 
    vv: "is_val v" and w_v: "bs_val w v" using lookup_bs_env by blast
  from lx vv w_v show ?case by (rule_tac x=v in exI) auto
next
  case (eval_lam \<rho> x e \<rho>')
  from eval_lam(1) have dom_eq: "set (map fst \<rho>) = sdom \<rho>'" using bs_env_dom by blast
  from eval_lam(1) have "closed_env ((x,EVar x)#\<rho>')" using bs_env_closed closed_env_def by auto
  from this psubst_fv have "FV (psubst ((x,EVar x)#\<rho>') e) = FV e - sdom ((x,EVar x)#\<rho>')" by blast
  from this eval_lam(2) dom_eq
  have fv_lam: "FV (ELam x (psubst ((x,EVar x)#\<rho>') e)) = {}" by auto
  from fv_lam eval_lam have 1: "bs_val (BClos x e \<rho>) (ELam x (psubst ((x, EVar x) # \<rho>') e))" by auto   
  from this eval_lam fv_lam show ?case
    by (rule_tac x="ELam x (psubst ((x,EVar x)#\<rho>') e)" in exI) auto
next
  case (eval_app \<rho> e1 x e \<rho>' e2 arg v  \<rho>'')
  from eval_app(8) have "FV e1 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_app(7) eval_app(4)[of \<rho>''] obtain v1 where e1_v1: "psubst \<rho>'' e1 \<longrightarrow>* v1" and 
    vv1: "is_val v1" and clos_v1: "bs_val (BClos x e \<rho>') v1" by (simp, blast)
  from eval_app(8) have "FV e2 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_app(5) eval_app(7) obtain v2 where e2_v2: "psubst \<rho>'' e2 \<longrightarrow>* v2" and
    vv2: "is_val v2" and arg_v2: "bs_val arg v2" by blast
  from vv2 have fv_v2: "FV v2 = {}" by auto 
  from clos_v1 obtain \<rho>2 where rpp_r2: "bs_env \<rho>' \<rho>2" and fv_v1: "FV v1 = {}" and
    v1_lam: "v1 = ELam x (psubst ((x,EVar x)#\<rho>2) e)" by auto
  let ?r = "((x,v2) # \<rho>2)"
  from rpp_r2 have cr2: "closed_env \<rho>2" using bs_env_closed by auto
  from this have "closed_env ((x,EVar x)#\<rho>2)"  using  closed_env_def sdom_def by auto
  from this have fve: "FV (psubst ((x,EVar x)#\<rho>2) e) = FV e - sdom ((x,EVar x)#\<rho>2)" 
    using psubst_fv[of "(x,EVar x)#\<rho>2"] by blast
  let ?r2 = "((x, arg) # \<rho>')"
  from rpp_r2 arg_v2 vv2 have rr: "bs_env ?r2 ?r" by auto
  from rr bs_env_dom have dr2_dr: "set (map fst ?r2) = sdom ?r" by blast 
  from fve dr2_dr fv_v1 v1_lam fv_v2 have "FV e \<subseteq> set (map fst ((x, arg) # \<rho>'))" by auto 
  from this rr eval_app(6) obtain v3 where e_v3: "psubst ?r e \<longrightarrow>* v3" and 
    vv3: "isval v3" and v_v3: "bs_val v v3" by (simp, blast)      
  from e1_v1 have 1: "EApp (psubst \<rho>'' e1) (psubst \<rho>'' e2) \<longrightarrow>* EApp v1 (psubst \<rho>'' e2)"
    by (rule app_red_cong1) 
  from e2_v2 have 2: "EApp v1 (psubst \<rho>'' e2) \<longrightarrow>* EApp v1 v2"
    by (rule app_red_cong2)
  from vv2 fv_v2 have vv2b: "is_val v2" by auto 
  let ?body = "psubst ((x,EVar x)#\<rho>2) e"
  from v1_lam vv2b have 3: "EApp (ELam x ?body) v2 \<longrightarrow>
      subst x v2 (psubst ((x,EVar x)#\<rho>2) e)" using beta[of v2 x "?body"] by simp
  have 4: "subst x v2 (psubst ((x,EVar x)#\<rho>2) e) = psubst ?r e"
    apply (rule subst_psubst) using fv_v2 cr2 by auto
  have 4: "subst x v2 (psubst ((x,EVar x)#\<rho>2) e) = psubst ?r e"
    apply (rule subst_psubst) using fv_v2 cr2 by auto
  from 1 2 have 5: "psubst \<rho>'' (EApp e1 e2) \<longrightarrow>* EApp v1 v2" apply simp 
    by (rule multi_step_trans) auto
  from 5 3 4 v1_lam have 6: "psubst \<rho>'' (EApp e1 e2) \<longrightarrow>* psubst ?r e"
    apply simp apply (rule multi_step_trans) apply assumption apply blast done
  from 6 e_v3 have 7: "psubst \<rho>'' (EApp e1 e2) \<longrightarrow>* v3" by (rule multi_step_trans) 
  from 7 vv3 v_v3 show ?case by blast
next
  case (eval_prim \<rho> e1 n1 e2 n2 n3 f \<rho>')
  from eval_prim(7) have "FV e1 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_prim obtain v1 where e1_v1: "psubst \<rho>' e1 \<longrightarrow>* v1" and
    n1_v1: "bs_val (BNat n1) v1" by blast
  from n1_v1 have v1: "v1 = ENat n1" by blast 

  from eval_prim(7) have "FV e2 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_prim obtain v2 where e2_v2: "psubst \<rho>' e2 \<longrightarrow>* v2" and
    n2_v2: "bs_val (BNat n2) v2" by blast
  from n2_v2 have v2: "v2 = ENat n2" by blast 
  
  from e1_v1 have 1: "EPrim f (psubst \<rho>' e1) (psubst \<rho>' e2) \<longrightarrow>* EPrim f v1 (psubst \<rho>' e2)"
    by (rule prim_red_cong1) 
  from e2_v2 have 2: "EPrim f v1 (psubst \<rho>' e2) \<longrightarrow>* EPrim f v1 v2"
    by (rule prim_red_cong2)
  from v1 v2 have 3: "EPrim f v1 v2 \<longrightarrow> ENat (f n1 n2)" by auto 
  from 1 2 have 5: "psubst \<rho>' (EPrim f e1 e2) \<longrightarrow>* EPrim f v1 v2" apply simp 
    apply (rule multi_step_trans) apply auto done
  from 5 3  have 6: "psubst \<rho>' (EPrim f e1 e2) \<longrightarrow>* ENat (f n1 n2)" apply simp
    apply (rule multi_step_trans) apply assumption apply blast done
  from this eval_prim(3) show ?case apply (rule_tac x="ENat (f n1 n2)" in exI) by auto
next
  case (eval_if0 \<rho> e1 e3 v3 e2 \<rho>')
  from eval_if0(6) have "FV e1 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_if0 obtain v1 where e1_v1: "psubst \<rho>' e1 \<longrightarrow>* v1" and
    n1_v1: "bs_val (BNat 0) v1" by blast
  from n1_v1 have v1: "v1 = ENat 0" by blast 
  from eval_if0(6) have "FV e3 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_if0 obtain v3' where e3_v3: "psubst \<rho>' e3 \<longrightarrow>* v3'" and
    v3_v3: "bs_val v3 v3'" by blast
      
  from e1_v1 have 1: "EIf (psubst \<rho>' e1) (psubst \<rho>' e2) (psubst \<rho>' e3) 
    \<longrightarrow>* EIf v1 (psubst \<rho>' e2) (psubst \<rho>' e3)" by (rule if_red_cong1) 
  from v1 have 3: "EIf v1 (psubst \<rho>' e2) (psubst \<rho>' e3) \<longrightarrow> (psubst \<rho>' e3)" by auto 
  from 1 3 have 5: "psubst \<rho>' (EIf e1 e2 e3) \<longrightarrow>* psubst \<rho>' e3" apply simp 
    apply (rule multi_step_trans) apply assumption apply blast done
  from 5 e3_v3 have 6: "psubst \<rho>' (EIf e1 e2 e3) \<longrightarrow>* v3'"
    apply (rule multi_step_trans) done
  from 6 v3_v3 show ?case by blast
next
  case (eval_if1 \<rho> e1 n e2 v2 e3 \<rho>')
  from eval_if1 have "FV e1 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_if1 obtain v1 where e1_v1: "psubst \<rho>' e1 \<longrightarrow>* v1" and
    n1_v1: "bs_val (BNat n) v1" and nz: "n \<noteq> 0" apply auto apply blast done
  from n1_v1 have v1: "v1 = ENat n" by blast 
  from eval_if1 have "FV e2 \<subseteq> set (map fst \<rho>)" by auto
  from this eval_if1 obtain v2' where e2_v2: "psubst \<rho>' e2 \<longrightarrow>* v2'" and
    v2_v2: "bs_val v2 v2'" by blast 
  from e1_v1 have 1: "EIf (psubst \<rho>' e1) (psubst \<rho>' e2) (psubst \<rho>' e3) 
    \<longrightarrow>* EIf v1 (psubst \<rho>' e2) (psubst \<rho>' e3)" by (rule if_red_cong1) 
  from v1 nz have 3: "EIf v1 (psubst \<rho>' e2) (psubst \<rho>' e3) \<longrightarrow> (psubst \<rho>' e2)" by auto 
  from 1 3 have 5: "psubst \<rho>' (EIf e1 e2 e3) \<longrightarrow>* psubst \<rho>' e2" apply simp 
    apply (rule multi_step_trans) apply assumption apply blast done
  from 5 e2_v2 have 6: "psubst \<rho>' (EIf e1 e2 e3) \<longrightarrow>* v2'"
    by (rule multi_step_trans)
  from 6 v2_v2 show ?case by blast
qed

lemma psubst_id: "FV e \<inter> sdom \<rho> = {} \<Longrightarrow> psubst \<rho> e = e"
proof (induction e arbitrary: \<rho>)
  case (EVar x)
  then show ?case by (cases "lookup \<rho> x") (auto simp: sdom_def)
next
  case (ENat x \<rho>)
  from ENat have "sdom ((x,EVar x)#\<rho>) = sdom \<rho> - {x}" by simp
  with ENat show ?case by auto
next
  case (ELam x e)
  from ELam have "FV e \<inter> sdom ((x,EVar x)#\<rho>) = {}" by auto
  with ELam show ?case by auto
qed fastforce+
 
    
fun bs_observe :: "bval \<Rightarrow> obs \<Rightarrow> bool" where
  "bs_observe (BNat n) (ONat n') = (n = n')" |
  "bs_observe (BClos x e \<rho>) OFun = True" |
  "bs_observe e ob = False" 

theorem sound_wrt_small_step:
  assumes e_v: "[] \<turnstile> e \<Down> v" and fv_e: "FV e = {}"
  shows "\<exists> v' ob. e \<longrightarrow>* v' \<and> isval v' \<and> observe v' ob
    \<and> bs_observe v ob"
proof -
  have 1: "bs_env [] []" by blast
  from fv_e have 2: "FV e \<subseteq> set (map fst [])" by simp
  from e_v 1 2 big_small_step obtain v' where 3: "psubst [] e \<longrightarrow>* v'" and 4: "is_val v'" and 
    5: "bs_val v v'" by blast
  have "psubst [] e = e" using psubst_id sdom_def apply auto done
  from this 3 4 5 show ?thesis apply (rule_tac x=v' in exI) apply simp
    apply (case_tac v)
     apply simp apply clarify apply simp
       apply (rename_tac n) apply (rule_tac x="ONat n" in exI) apply force
     apply (rule_tac x=OFun in exI) apply force done
qed
  
subsection "Big-step semantics is deterministic"

theorem big_step_fun:
  assumes ev: "\<rho> \<turnstile> e \<Down> v" and evp: "\<rho> \<turnstile> e \<Down> v'" shows "v = v'"
  using ev evp 
proof (induction arbitrary: v')
  case (eval_app \<rho> e1 x e \<rho>' e2 arg v)
  from eval_app(7) obtain x' e' \<rho>'' arg' where e1_cl: "\<rho> \<turnstile> e1 \<Down> BClos x' e' \<rho>''" and
    e2_argp: "\<rho> \<turnstile> e2 \<Down> arg'" and e_vp: "(x', arg') # \<rho>'' \<turnstile> e' \<Down> v'" by blast
  from eval_app(4) e1_cl have 1: "BClos x e \<rho>' = BClos x' e' \<rho>''" by simp
  from eval_app(5) e2_argp have 2: "arg = arg'" by simp
  from eval_app(6) e_vp 1 2 show ?case by simp
next
  case (eval_if0 \<rho> e1 e3 v3 e2)
  from eval_if0(5)
  show ?case
  proof (rule eval_if_inv)
    assume "\<rho> \<turnstile> e3 \<Down> v'" with eval_if0(4) show ?thesis by simp
  next
    fix n assume "\<rho> \<turnstile> e1 \<Down> BNat n" and nz: "n > 0"
    with eval_if0(3) have "False" by auto thus ?thesis ..
  qed
next
  case (eval_if1 \<rho> e1 n e2 v2 e3)
  then show ?case by blast
qed fastforce+

end
