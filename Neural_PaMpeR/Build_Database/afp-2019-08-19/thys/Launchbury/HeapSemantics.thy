theory HeapSemantics
  imports EvalHeap "AList-Utils-Nominal" HasESem Iterative "Env-Nominal"
begin

subsubsection \<open>A locale for heap semantics, abstract in the expression semantics\<close>

context has_ESem
begin

abbreviation EvalHeapSem_syn  ("\<^bold>\<lbrakk> _ \<^bold>\<rbrakk>\<^bsub>_\<^esub>"  [0,0] 110)
  where "EvalHeapSem_syn \<Gamma> \<rho> \<equiv> evalHeap \<Gamma> (\<lambda> e. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>\<^esub>)"

definition
  HSem :: "('var \<times> 'exp) list \<Rightarrow> ('var \<Rightarrow> 'value) \<rightarrow> ('var \<Rightarrow> 'value)"
  where "HSem \<Gamma> = (\<Lambda> \<rho> . (\<mu> \<rho>'. \<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>))"

abbreviation HSem_syn ("\<lbrace> _ \<rbrace>_"  [0,60] 60)
  where "\<lbrace>\<Gamma>\<rbrace>\<rho> \<equiv> HSem \<Gamma> \<cdot> \<rho>"

lemma HSem_def': "\<lbrace>\<Gamma>\<rbrace>\<rho> = (\<mu> \<rho>'. \<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  unfolding HSem_def by simp

subsubsection \<open>Induction and other lemmas about @{term HSem}\<close>

lemma HSem_ind:
  assumes "adm P"
  assumes "P \<bottom>"
  assumes step: "\<And> \<rho>'. P \<rho>' \<Longrightarrow>  P (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  shows "P (\<lbrace>\<Gamma>\<rbrace>\<rho>)"
  unfolding HSem_def'
  apply (rule fix_ind[OF assms(1), OF assms(2)])
  using step by simp

lemma HSem_below:
  assumes rho: "\<And>x. x \<notin> domA h \<Longrightarrow> \<rho> x \<sqsubseteq> r x"
  assumes h: "\<And>x. x \<in> domA h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r x"
  shows "\<lbrace>h\<rbrace>\<rho> \<sqsubseteq> r"
proof (rule HSem_ind, goal_cases)
  case 1 show ?case by (auto)
next
  case 2 show ?case by (rule minimal)
next
  case (3 \<rho>')
    show ?case
    by (rule override_on_belowI)
       (auto simp add: lookupEvalHeap  below_trans[OF monofun_cfun_arg[OF \<open>\<rho>' \<sqsubseteq> r\<close>] h] rho)
qed

lemma HSem_bot_below:
  assumes h: "\<And>x. x \<in> domA h \<Longrightarrow> \<lbrakk>the (map_of h x)\<rbrakk>\<^bsub>r\<^esub> \<sqsubseteq> r x"
  shows "\<lbrace>h\<rbrace>\<bottom> \<sqsubseteq> r"
  using assms 
by (metis HSem_below fun_belowD minimal)

lemma HSem_bot_ind:
  assumes "adm P"
  assumes "P \<bottom>"
  assumes step: "\<And> \<rho>'. P \<rho>' \<Longrightarrow> P (\<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>)"
  shows "P (\<lbrace>\<Gamma>\<rbrace>\<bottom>)"
  apply (rule HSem_ind[OF assms(1,2)])
  apply (drule assms(3))
  apply simp
  done
  
lemma parallel_HSem_ind:
  assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P \<bottom> \<bottom>"
  assumes step: "\<And>y z. P y z \<Longrightarrow>
    P (\<rho>\<^sub>1 ++\<^bsub>domA \<Gamma>\<^sub>1\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^sub>1\<^bold>\<rbrakk>\<^bsub>y\<^esub>) (\<rho>\<^sub>2 ++\<^bsub>domA \<Gamma>\<^sub>2\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^sub>2\<^bold>\<rbrakk>\<^bsub>z\<^esub>)"
  shows "P (\<lbrace>\<Gamma>\<^sub>1\<rbrace>\<rho>\<^sub>1) (\<lbrace>\<Gamma>\<^sub>2\<rbrace>\<rho>\<^sub>2)"
  unfolding HSem_def'
  apply (rule parallel_fix_ind[OF assms(1), OF assms(2)])
  using step by simp

lemma HSem_eq:
  shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<rho> ++\<^bsub>domA \<Gamma>\<^esub> \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>\<^esub>"
  unfolding HSem_def'
  by (subst fix_eq) simp

lemma HSem_bot_eq:
  shows "\<lbrace>\<Gamma>\<rbrace>\<bottom> = \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<bottom>\<^esub>"
  by (subst HSem_eq) simp

lemma lookup_HSem_other:
  assumes "y \<notin> domA h"
  shows "(\<lbrace>h\<rbrace>\<rho>) y = \<rho> y"
  apply (subst HSem_eq)
  using assms by simp

lemma lookup_HSem_heap:
  assumes "y \<in> domA h"
  shows "(\<lbrace>h\<rbrace>\<rho>) y = \<lbrakk> the (map_of h y) \<rbrakk>\<^bsub>\<lbrace>h\<rbrace>\<rho>\<^esub>"
  apply (subst HSem_eq)
  using assms by (simp add: lookupEvalHeap)

lemma HSem_edom_subset:  "edom (\<lbrace>\<Gamma>\<rbrace>\<rho>) \<subseteq> edom \<rho> \<union> domA \<Gamma>"
  apply rule
  unfolding edomIff
  apply (case_tac "x \<in> domA \<Gamma>")
  apply (auto simp add: lookup_HSem_other)
  done

lemma (in -) env_restr_override_onI:"-S2 \<subseteq> S \<Longrightarrow> env_restr S \<rho>1 ++\<^bsub>S2\<^esub> \<rho>2 = \<rho>1 ++\<^bsub>S2\<^esub> \<rho>2"
  by (rule ext) (auto simp add: lookup_override_on_eq )

lemma HSem_restr:
  "\<lbrace>h\<rbrace>(\<rho> f|` (- domA h)) = \<lbrace>h\<rbrace>\<rho>"
  apply (rule parallel_HSem_ind)
  apply simp
  apply auto[1]
  apply (subst env_restr_override_onI)
  apply simp_all
  done

lemma HSem_restr_cong:
  assumes "\<rho> f|` (- domA h) = \<rho>' f|` (- domA h)"
  shows "\<lbrace>h\<rbrace>\<rho> = \<lbrace>h\<rbrace>\<rho>'"
  apply (subst (1 2) HSem_restr[symmetric])
  by (simp add: assms)

lemma HSem_restr_cong_below:
  assumes "\<rho> f|` (- domA h) \<sqsubseteq> \<rho>' f|` (- domA h)"
  shows "\<lbrace>h\<rbrace>\<rho> \<sqsubseteq> \<lbrace>h\<rbrace>\<rho>'"
  by (subst (1 2) HSem_restr[symmetric]) (rule monofun_cfun_arg[OF assms])

lemma HSem_reorder:
  assumes "map_of \<Gamma> = map_of \<Delta>"
  shows "\<lbrace>\<Gamma>\<rbrace>\<rho> = \<lbrace>\<Delta>\<rbrace>\<rho>"
by (simp add: HSem_def' evalHeap_reorder[OF assms] assms dom_map_of_conv_domA[symmetric])

lemma HSem_reorder_head:
  assumes "x \<noteq> y"
  shows "\<lbrace>(x,e1)#(y,e2)#\<Gamma>\<rbrace>\<rho> = \<lbrace>(y,e2)#(x,e1)#\<Gamma>\<rbrace>\<rho>"
proof-
  have "set ((x,e1)#(y,e2)#\<Gamma>) = set ((y,e2)#(x,e1)#\<Gamma>)"
    by auto
  thus ?thesis      
    unfolding HSem_def evalHeap_reorder_head[OF assms]
    by (simp add: domA_def)
qed

lemma HSem_reorder_head_append:
  assumes "x \<notin> domA \<Gamma>"
  shows "\<lbrace>(x,e)#\<Gamma>@\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma> @ ((x,e)#\<Delta>)\<rbrace>\<rho>"
proof-
  have "set ((x,e)#\<Gamma>@\<Delta>) = set (\<Gamma> @ ((x,e)#\<Delta>))" by auto
  thus ?thesis
    unfolding HSem_def  evalHeap_reorder_head_append[OF assms]
    by simp
qed  

lemma env_restr_HSem:
  assumes "domA \<Gamma> \<inter> S = {}"
  shows "(\<lbrace> \<Gamma> \<rbrace>\<rho>) f|` S = \<rho> f|` S"
proof (rule env_restr_eqI)
  fix x
  assume "x \<in> S"
  hence "x \<notin> domA \<Gamma>" using assms by auto
  thus "(\<lbrace> \<Gamma> \<rbrace>\<rho>) x = \<rho> x"
    by (rule lookup_HSem_other)
qed

lemma env_restr_HSem_noop:
  assumes "domA \<Gamma> \<inter> edom \<rho> = {}"
  shows "(\<lbrace> \<Gamma> \<rbrace>\<rho>) f|` edom \<rho> = \<rho>"
  by (simp add: env_restr_HSem[OF assms] env_restr_useless)

lemma HSem_Nil[simp]: "\<lbrace>[]\<rbrace>\<rho> = \<rho>"
  by (subst HSem_eq, simp)

subsubsection \<open>Substitution\<close>

lemma HSem_subst_exp:
  assumes "\<And>\<rho>'. \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> e' \<rbrakk>\<^bsub>\<rho>'\<^esub>"
  shows "\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e') # \<Gamma>\<rbrace>\<rho>"
  by (rule parallel_HSem_ind) (auto simp add: assms evalHeap_subst_exp)

lemma HSem_subst_expr_below:
  assumes below: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
  shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
  by (rule HSem_below) (auto simp add: lookup_HSem_heap below lookup_HSem_other)

lemma HSem_subst_expr:
  assumes below1: "\<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>\<^esub>"
  assumes below2: "\<lbrakk> e2 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e1 \<rbrakk>\<^bsub>\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho>\<^esub>"
  shows "\<lbrace>(x, e1) # \<Gamma>\<rbrace>\<rho> = \<lbrace>(x, e2) # \<Gamma>\<rbrace>\<rho>"
  by (metis assms HSem_subst_expr_below below_antisym)

subsubsection \<open>Re-calculating the semantics of the heap is idempotent\<close> 

lemma HSem_redo:
  shows "\<lbrace>\<Gamma>\<rbrace>(\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) f|` (edom \<rho> \<union> domA \<Delta>) = \<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>" (is "?LHS = ?RHS")
proof (rule below_antisym)
  show "?LHS \<sqsubseteq> ?RHS"
  by (rule HSem_below)
     (auto simp add: lookup_HSem_heap fun_belowD[OF env_restr_below_itself])

  show "?RHS \<sqsubseteq> ?LHS"
  proof(rule HSem_below, goal_cases)
    case (1 x)
    thus ?case
      by (cases "x \<notin> edom \<rho>") (auto simp add: lookup_HSem_other dest:lookup_not_edom)
  next
    case prems: (2 x)
    thus ?case
    proof(cases "x \<in> domA \<Gamma>")
    case True
      thus ?thesis by (auto simp add: lookup_HSem_heap)
    next
    case False
      hence delta: "x \<in> domA \<Delta>" using prems by auto
      with False \<open>?LHS \<sqsubseteq> ?RHS\<close>
      show ?thesis by (auto simp add: lookup_HSem_other lookup_HSem_heap monofun_cfun_arg)
    qed
  qed
qed

subsubsection \<open>Iterative definition of the heap semantics\<close>

lemma iterative_HSem:
  assumes "x \<notin> domA \<Gamma>"
  shows "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
proof-
  from assms
  interpret iterative
    where e1 =  "\<Lambda> \<rho>'. \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>"
    and e2 = "\<Lambda> \<rho>'. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>"
    and S = "domA \<Gamma>"
    and x = x by unfold_locales

  have "\<lbrace>(x,e) # \<Gamma>\<rbrace>\<rho> = fix \<cdot> L"
    by (simp add: HSem_def' override_on_upd ne)
  also have "\<dots> = fix \<cdot> R"
    by (rule iterative_override_on)
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))"
    by (simp add: HSem_def')
  finally show ?thesis.
qed

lemma iterative_HSem':
  assumes "x \<notin> domA \<Gamma>"
  shows "(\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>))
       = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
proof-
  from assms
  interpret iterative
    where e1 =  "\<Lambda> \<rho>'. \<^bold>\<lbrakk>\<Gamma>\<^bold>\<rbrakk>\<^bsub>\<rho>'\<^esub>"
    and e2 = "\<Lambda> \<rho>'. \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>"
    and S = "domA \<Gamma>"
    and x = x by unfold_locales

  have "(\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<rho>'\<^esub>)) = fix \<cdot> R"
    by (simp add: HSem_def')
  also have "\<dots> = fix \<cdot> L"
    by (rule iterative_override_on[symmetric])
  also have "\<dots> = fix \<cdot> R'"
    by (rule iterative_override_on')
  also have "\<dots> = (\<mu> \<rho>'. (\<rho> ++\<^bsub>domA \<Gamma>\<^esub> (\<lbrace>\<Gamma>\<rbrace>\<rho>'))( x := \<lbrakk>e\<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<rho>'\<^esub>))"
    by (simp add: HSem_def')
  finally
  show ?thesis.
qed

subsubsection \<open>Fresh variables on the heap are irrelevant\<close>

lemma HSem_ignores_fresh_restr':
  assumes "fv \<Gamma> \<subseteq> S"
  assumes "\<And> x \<rho>. x \<in> domA \<Gamma> \<Longrightarrow> \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>\<rho> f|` (fv (the (map_of \<Gamma> x)))\<^esub>"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` S = \<lbrace>\<Gamma>\<rbrace>\<rho> f|` S"
proof(induction rule: parallel_HSem_ind[case_names adm base step])
  case adm thus ?case by simp
next
  case base
    show ?case by simp
next
  case (step y z)
  have "\<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>y\<^esub> = \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>z\<^esub>"
  proof(rule evalHeap_cong')
    fix x
    assume "x \<in> domA \<Gamma>"
    hence "fv (the (map_of \<Gamma> x)) \<subseteq> fv \<Gamma>" by (rule map_of_fv_subset)
    with assms(1)
    have "fv (the (map_of \<Gamma> x)) \<inter> S = fv (the (map_of \<Gamma> x))" by auto
    with step
    have "y f|` fv (the (map_of \<Gamma> x)) = z f|` fv (the (map_of \<Gamma> x))" by auto
    with \<open>x \<in> domA \<Gamma>\<close>
    show "\<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>y\<^esub> = \<lbrakk> the (map_of \<Gamma> x) \<rbrakk>\<^bsub>z\<^esub>"
      by (subst (1 2) assms(2)[OF \<open>x \<in> domA \<Gamma>\<close>]) simp
  qed
  moreover
  have "domA \<Gamma> \<subseteq> S" using domA_fv_subset assms(1) by auto
  ultimately
  show ?case by (simp add: env_restr_add env_restr_evalHeap_noop)
qed
end

subsubsection \<open>Freshness\<close>

context has_ignore_fresh_ESem begin
 
lemma ESem_fresh_cong:
  assumes "\<rho> f|` (fv e) = \<rho>' f|` (fv e)"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
by (metis assms ESem_considers_fv)

lemma ESem_fresh_cong_subset:
  assumes "fv e \<subseteq> S"
  assumes "\<rho> f|` S = \<rho>' f|` S"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
by (rule ESem_fresh_cong[OF  env_restr_eq_subset[OF assms]])

lemma ESem_fresh_cong_below:
  assumes "\<rho> f|` (fv e) \<sqsubseteq> \<rho>' f|` (fv e)"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
by (metis assms ESem_considers_fv monofun_cfun_arg)

lemma ESem_fresh_cong_below_subset:
  assumes "fv e \<subseteq> S"
  assumes "\<rho> f|` S \<sqsubseteq> \<rho>' f|` S"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> \<sqsubseteq> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub>"
by (rule ESem_fresh_cong_below[OF  env_restr_below_subset[OF assms]])

lemma ESem_ignores_fresh_restr:
  assumes "atom ` S \<sharp>* e"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (- S)\<^esub>"
proof-
  have "fv e \<inter> - S = fv e" using assms by (auto simp add: fresh_def fresh_star_def fv_supp)
  thus ?thesis by (subst (1 2) ESem_considers_fv) simp
qed

lemma ESem_ignores_fresh_restr':
  assumes "atom ` (edom \<rho> - S) \<sharp>* e"
  shows "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` S\<^esub>"
proof-
  have "\<lbrakk> e \<rbrakk>\<^bsub>\<rho>\<^esub> =  \<lbrakk> e \<rbrakk>\<^bsub>\<rho> f|` (- (edom \<rho> - S))\<^esub>"
    by (rule ESem_ignores_fresh_restr[OF assms])
  also have "\<rho> f|` (- (edom \<rho> - S)) = \<rho> f|` S" 
    by (rule ext) (auto simp add: lookup_env_restr_eq dest: lookup_not_edom)
  finally show ?thesis.
qed

lemma HSem_ignores_fresh_restr'':
  assumes "fv \<Gamma> \<subseteq> S"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` S = \<lbrace>\<Gamma>\<rbrace>\<rho> f|` S"
by (rule HSem_ignores_fresh_restr'[OF assms(1) ESem_considers_fv])

lemma HSem_ignores_fresh_restr:
  assumes "atom ` S \<sharp>* \<Gamma>"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (- S) = \<lbrace>\<Gamma>\<rbrace>\<rho> f|` (- S)"
proof-
  from assms have "fv \<Gamma> \<subseteq> - S" by (auto simp add: fv_def fresh_star_def fresh_def)
  thus ?thesis by (rule HSem_ignores_fresh_restr'')
qed

lemma HSem_fresh_cong_below:
  assumes "\<rho> f|` ((S \<union> fv \<Gamma>) - domA \<Gamma>) \<sqsubseteq> \<rho>' f|` ((S \<union> fv \<Gamma>) - domA \<Gamma>)"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` S \<sqsubseteq> (\<lbrace>\<Gamma>\<rbrace>\<rho>') f|` S"
proof-
  from assms
  have "\<lbrace>\<Gamma>\<rbrace>(\<rho> f|` (S \<union> fv \<Gamma>)) \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>(\<rho>' f|` (S \<union> fv \<Gamma>))"
    by (auto intro: HSem_restr_cong_below simp add: Diff_eq inf_commute)
  hence "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` (S \<union> fv \<Gamma>) \<sqsubseteq> (\<lbrace>\<Gamma>\<rbrace>\<rho>') f|` (S \<union> fv \<Gamma>)"
    by (subst (1 2) HSem_ignores_fresh_restr'') simp_all
  thus ?thesis
    by (rule env_restr_below_subset[OF Un_upper1])
qed

lemma HSem_fresh_cong:
  assumes "\<rho> f|` ((S \<union> fv \<Gamma>) - domA \<Gamma>) = \<rho>' f|` ((S \<union> fv \<Gamma>) - domA \<Gamma>)"
  shows "(\<lbrace>\<Gamma>\<rbrace>\<rho>) f|` S = (\<lbrace>\<Gamma>\<rbrace>\<rho>') f|` S"
apply (rule below_antisym)
apply (rule HSem_fresh_cong_below[OF eq_imp_below[OF assms]])
apply (rule HSem_fresh_cong_below[OF eq_imp_below[OF assms[symmetric]]])
done

subsubsection \<open>Adding a fresh variable to a heap does not affect its semantics\<close> 

lemma HSem_add_fresh':
  assumes fresh: "atom x \<sharp> \<Gamma>"
  assumes "x \<notin> edom \<rho>"
  assumes step: "\<And>e \<rho>'. e \<in> snd ` set \<Gamma> \<Longrightarrow> \<lbrakk> e \<rbrakk>\<^bsub>\<rho>'\<^esub> = \<lbrakk> e \<rbrakk>\<^bsub>env_delete x \<rho>'\<^esub>"
  shows  "env_delete x (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
proof (rule parallel_HSem_ind, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by auto
next
  case prems: (3 y z)
  have "env_delete x \<rho> = \<rho>" using \<open>x \<notin> edom \<rho>\<close> by (rule env_delete_noop)
  moreover
  from fresh have "x \<notin> domA \<Gamma>" by (metis domA_not_fresh)
  hence "env_delete x (\<^bold>\<lbrakk> (x, e) # \<Gamma> \<^bold>\<rbrakk>\<^bsub>y\<^esub>) = \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>y\<^esub>"
    by (auto intro: env_delete_noop dest:  subsetD[OF edom_evalHeap_subset])
  moreover
  have "\<dots> = \<^bold>\<lbrakk> \<Gamma> \<^bold>\<rbrakk>\<^bsub>z\<^esub>"
    apply (rule evalHeap_cong[OF refl])
    apply (subst (1) step, assumption)
    using prems(1) apply auto
    done
  ultimately
  show ?case using \<open>x \<notin> domA \<Gamma>\<close>
    by (simp add: env_delete_add)
qed

lemma HSem_add_fresh:
  assumes "atom x \<sharp> \<Gamma>"
  assumes "x \<notin> edom \<rho>"
  shows  "env_delete x (\<lbrace>(x, e) # \<Gamma>\<rbrace>\<rho>) = \<lbrace>\<Gamma>\<rbrace>\<rho>"
proof(rule HSem_add_fresh'[OF assms], goal_cases)
  case (1 e \<rho>')
  assume "e \<in> snd ` set \<Gamma>"
  hence "atom x \<sharp> e" by (metis assms(1) fresh_heap_expr')
  hence "x \<notin> fv e" by (simp add: fv_def fresh_def)
  thus ?case 
    by (rule ESem_fresh_cong[OF env_restr_env_delete_other[symmetric]])
qed

subsubsection \<open>Mutual recursion with fresh variables\<close>

lemma HSem_subset_below:
  assumes fresh: "atom ` domA \<Gamma> \<sharp>* \<Delta>" 
  shows "\<lbrace>\<Delta>\<rbrace>(\<rho> f|` (- domA \<Gamma>)) \<sqsubseteq> (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)  f|` (- domA \<Gamma>)"
proof(rule HSem_below)
  fix x
  assume [simp]: "x \<in> domA \<Delta>"
  with assms have *: "atom ` domA \<Gamma> \<sharp>* the (map_of \<Delta> x)" by (metis fresh_star_map_of)
  hence [simp]: "x \<notin> domA \<Gamma>" using fresh \<open>x \<in> domA \<Delta>\<close> by (metis fresh_star_def domA_not_fresh image_eqI)
  show "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>(\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>) f|` (- domA \<Gamma>)\<^esub> \<sqsubseteq> ((\<lbrace>\<Delta> @ \<Gamma>\<rbrace>\<rho>) f|` (- domA \<Gamma>)) x"
    by (simp add: lookup_HSem_heap ESem_ignores_fresh_restr[OF *, symmetric])
 qed (simp add: lookup_HSem_other lookup_env_restr_eq)

text \<open>In the following lemma we show that the semantics of fresh variables can be be calculated
together with the presently bound variables, or separately.\<close>

lemma HSem_merge:
  assumes fresh: "atom ` domA \<Gamma> \<sharp>* \<Delta>"
  shows "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> = \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
proof(rule below_antisym)
  have map_of_eq: "map_of (\<Delta> @ \<Gamma>) = map_of (\<Gamma> @ \<Delta>)"
  proof
    fix x
    show "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
    proof (cases "x \<in> domA \<Gamma>")
      case True
      hence "x \<notin> domA \<Delta>" by (metis fresh_distinct fresh IntI equals0D)
      thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
        by (simp add: map_add_dom_app_simps dom_map_of_conv_domA)
    next
      case False
      thus "map_of (\<Delta> @ \<Gamma>) x = map_of (\<Gamma> @ \<Delta>) x"
        by (simp add: map_add_dom_app_simps dom_map_of_conv_domA)
    qed
  qed

  show "\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho>"
  proof(rule HSem_below)
    fix x
    assume [simp]:"x \<notin> domA \<Gamma>"

    have "(\<lbrace>\<Delta>\<rbrace>\<rho>) x = ((\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- domA \<Gamma>)) x" by simp
    also have "\<dots> = (\<lbrace>\<Delta>\<rbrace>(\<rho> f|` (- domA \<Gamma>))) x"
      by (rule arg_cong[OF HSem_ignores_fresh_restr[OF fresh]])
    also have "\<dots> \<sqsubseteq> ((\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>)  f|` (- domA \<Gamma>)) x"
      by (rule fun_belowD[OF HSem_subset_below[OF fresh]] )
    also have "\<dots> = (\<lbrace>\<Delta>@\<Gamma>\<rbrace>\<rho>) x" by simp
    also have "\<dots> = (\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) x" by (rule arg_cong[OF HSem_reorder[OF map_of_eq]])
    finally
    show "(\<lbrace>\<Delta>\<rbrace>\<rho>) x \<sqsubseteq> (\<lbrace>\<Gamma> @ \<Delta>\<rbrace>\<rho>) x".
  qed (auto simp add: lookup_HSem_heap lookup_env_restr_eq)

   have *: "\<And> x. x \<in> domA \<Delta> \<Longrightarrow> x \<notin> domA \<Gamma>"
    using fresh by (auto simp add: fresh_Pair fresh_star_def domA_not_fresh)

  have foo: "edom \<rho> \<union> domA \<Delta> \<union> domA \<Gamma> - (edom \<rho> \<union> domA \<Delta> \<union> domA \<Gamma>) \<inter> - domA \<Gamma> = domA \<Gamma>" by auto
  have foo2:"(edom \<rho> \<union> domA \<Delta> - (edom \<rho> \<union> domA \<Delta>) \<inter> - domA \<Gamma>) \<subseteq> domA \<Gamma>" by auto

  { fix x
    assume "x \<in> domA \<Delta>"
    hence *: "atom ` domA \<Gamma> \<sharp>* the (map_of \<Delta> x)"
      by (rule  fresh_star_map_of[OF _ fresh])

    have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>(\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- domA \<Gamma>)\<^esub>"
      by (rule ESem_ignores_fresh_restr[OF *])
    also have "(\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- domA \<Gamma>) = (\<lbrace>\<Delta>\<rbrace>\<rho>) f|` (- domA \<Gamma>)"
      by (simp add: env_restr_HSem)
    also have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<dots>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>"
      by (rule ESem_ignores_fresh_restr[symmetric, OF *])
    finally
    have "\<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub> = \<lbrakk> the (map_of \<Delta> x) \<rbrakk>\<^bsub>\<lbrace>\<Delta>\<rbrace>\<rho>\<^esub>".
  }
  thus "\<lbrace>\<Gamma>@\<Delta>\<rbrace>\<rho> \<sqsubseteq> \<lbrace>\<Gamma>\<rbrace>\<lbrace>\<Delta>\<rbrace>\<rho>"
    by -(rule HSem_below, auto simp add: lookup_HSem_other lookup_HSem_heap *)
qed
end

subsubsection \<open>Parallel induction\<close>

lemma parallel_HSem_ind_different_ESem:
  assumes "adm (\<lambda>\<rho>'. P (fst \<rho>') (snd \<rho>'))"
  assumes "P \<bottom> \<bottom>"
  assumes "\<And>y z. P y z \<Longrightarrow> P (\<rho> ++\<^bsub>domA h\<^esub> evalHeap h (\<lambda>e. ESem1 e \<cdot> y)) (\<rho>2 ++\<^bsub>domA h2\<^esub> evalHeap h2 (\<lambda>e. ESem2 e \<cdot> z))"
  shows "P (has_ESem.HSem ESem1 h\<cdot>\<rho>) (has_ESem.HSem ESem2 h2\<cdot>\<rho>2)"
proof-
  interpret HSem1: has_ESem ESem1.
  interpret HSem2: has_ESem ESem2.

  show ?thesis
    unfolding HSem1.HSem_def' HSem2.HSem_def'
    apply (rule parallel_fix_ind[OF assms(1)])
    apply (rule assms(2))
    apply simp
    apply (erule assms(3))
    done
qed

subsubsection \<open>Congruence rule\<close>

lemma HSem_cong[fundef_cong]:
  "\<lbrakk> (\<And> e. e \<in> snd ` set heap2 \<Longrightarrow> ESem1 e = ESem2 e); heap1 = heap2  \<rbrakk>
      \<Longrightarrow> has_ESem.HSem ESem1 heap1 = has_ESem.HSem ESem2 heap2"
  unfolding has_ESem.HSem_def
  by (auto cong:evalHeap_cong)

subsubsection \<open>Equivariance of the heap semantics\<close>

lemma HSem_eqvt[eqvt]:
  "\<pi> \<bullet> has_ESem.HSem ESem \<Gamma> = has_ESem.HSem (\<pi> \<bullet> ESem) (\<pi> \<bullet> \<Gamma>)"
proof-
  show ?thesis
   unfolding has_ESem.HSem_def
   apply (subst permute_Lam, simp)
   apply (subst eqvt_lambda)
   apply (simp add: Cfun_app_eqvt permute_Lam)
   done
qed

end
