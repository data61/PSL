section \<open>Trace equivalence for resources\<close>

theory Random_System imports Converter_Rewrite begin

fun trace_callee :: "('a, 'b, 's) callee \<Rightarrow> 's spmf \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b spmf" where
  "trace_callee callee p [] x = bind_spmf p (\<lambda>s. map_spmf fst (callee s x))"
| "trace_callee callee p ((a, b) # xs) x = 
   trace_callee callee (cond_spmf_fst (bind_spmf p (\<lambda>s. callee s a)) b) xs x"

definition trace_callee_eq :: "('a, 'b, 's1) callee \<Rightarrow> ('a, 'b, 's2) callee \<Rightarrow> 'a set \<Rightarrow> 's1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> bool" where
  "trace_callee_eq callee1 callee2 A p q \<longleftrightarrow> 
  (\<forall>xs. set xs \<subseteq> A \<times> UNIV \<longrightarrow> (\<forall>x \<in> A. trace_callee callee1 p xs x = trace_callee callee2 q xs x))"

abbreviation trace_callee_eq' :: "'a set \<Rightarrow> ('a, 'b, 's1) callee \<Rightarrow> 's1 \<Rightarrow> ('a, 'b, 's2) callee \<Rightarrow> 's2 \<Rightarrow> bool"
  ("_ \<turnstile>\<^sub>C/ (_'((_)')) \<approx>/ (_'((_)'))" [90, 0, 0, 0, 0] 91)
  where "trace_callee_eq' A callee1 s1 callee2 s2 \<equiv> trace_callee_eq callee1 callee2 A (return_spmf s1) (return_spmf s2)"

lemma trace_callee_eqI:
  assumes "\<And>xs x. \<lbrakk> set xs \<subseteq> A \<times> UNIV; x \<in> A \<rbrakk>
    \<Longrightarrow> trace_callee callee1 p xs x = trace_callee callee2 q xs x"
  shows "trace_callee_eq callee1 callee2 A p q"
  using assms by(simp add: trace_callee_eq_def)

lemma trace_callee_eqD:
  assumes "trace_callee_eq callee1 callee2 A p q"
    and "set xs \<subseteq> A \<times> UNIV" "x \<in> A"
  shows "trace_callee callee1 p xs x = trace_callee callee2 q xs x"
  using assms by(simp add: trace_callee_eq_def)

lemma cond_spmf_fst_None [simp]: "cond_spmf_fst (return_pmf None) x = return_pmf None"
  by(simp)

lemma trace_callee_None [simp]:
  "trace_callee callee (return_pmf None) xs x = return_pmf None"
  by(induction xs)(auto)

proposition trace'_eqI_sim:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes start: "S p q"
    and step: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and sim: "\<And>p q a res b s'. \<lbrakk> S p q; a \<in> A; res \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 res a) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
  shows "trace_callee_eq callee1 callee2 A p q"
proof(rule trace_callee_eqI)
  fix xs :: "('a \<times> 'b) list" and z
  assume xs: "set xs \<subseteq> A \<times> UNIV" and z: "z \<in> A"

  from start show "trace_callee callee1 p xs z = trace_callee callee2 q xs z" using xs
  proof(induction xs arbitrary: p q)
    case Nil
    then show ?case using z by(simp add: step)
  next
    case (Cons xy xs)
    obtain x y where xy [simp]: "xy = (x, y)" by(cases xy)
    have "trace_callee callee1 p (xy # xs) z = 
      trace_callee callee1 (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s x)) y) xs z"
      by(simp add: bind_map_spmf split_def o_def)
    also have "\<dots> = trace_callee callee2 (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s x)) y) xs z"
    proof(cases "\<exists>s \<in> set_spmf q. \<exists>s'. (y, s') \<in> set_spmf (callee2 s x)")
      case True
      then obtain s s' where "s \<in> set_spmf q" "(y, s') \<in> set_spmf (callee2 s x)" by blast
      from sim[OF \<open>S p q\<close> _ this] show ?thesis using Cons.prems by (auto intro: Cons.IH)
    next
      case False
      then have "cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s x)) y = return_pmf None"
        by(auto simp add: bind_eq_return_pmf_None)
      moreover from step[OF \<open>S p q\<close>, of x, THEN arg_cong[where f=set_spmf], THEN eq_refl] Cons.prems False
      have "cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s x)) y = return_pmf None"
        by(clarsimp simp add: bind_eq_return_pmf_None)(rule ccontr; fastforce)
      ultimately show ?thesis by(simp del: cond_spmf_fst_eq_return_None)
    qed
    also have "\<dots> = trace_callee callee2 q (xy # xs) z"
      by(simp add: split_def o_def)
    finally show ?case .
  qed
qed

fun trace_callee_aux :: "('a, 'b, 's) callee \<Rightarrow> 's spmf \<Rightarrow> ('a \<times> 'b) list \<Rightarrow> 's spmf" where
  "trace_callee_aux callee p [] = p"
| "trace_callee_aux callee p ((x, y) # xs) = trace_callee_aux callee (cond_spmf_fst (bind_spmf p (\<lambda>res. callee res x)) y) xs"

lemma trace_callee_conv_trace_callee_aux:
  "trace_callee callee p xs a = bind_spmf (trace_callee_aux callee p xs) (\<lambda>s. map_spmf fst (callee s a))"
  by(induction xs arbitrary: p)(auto simp add: split_def)

lemma trace_callee_aux_append:
  "trace_callee_aux callee p (xs @ ys) = trace_callee_aux callee (trace_callee_aux callee p xs) ys"
  by(induction xs arbitrary: p)(auto simp add: split_def)

inductive trace_callee_closure :: "('a, 'b, 's1) callee \<Rightarrow> ('a, 'b, 's2) callee \<Rightarrow> 'a set \<Rightarrow> 's1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> 's1 spmf \<Rightarrow> 's2 spmf \<Rightarrow> bool"
  for callee1 callee2 A p q where
    "trace_callee_closure callee1 callee2 A p q (trace_callee_aux callee1 p xs) (trace_callee_aux callee2 q xs)" if "set xs \<subseteq> A \<times> UNIV"

lemma trace_callee_closure_start: "trace_callee_closure callee1 callee2 A p q p q"
  by(simp add: trace_callee_closure.simps exI[where x="[]"])

lemma trace_callee_closure_step:
  assumes "trace_callee_eq callee1 callee2 A p q"
    and "trace_callee_closure callee1 callee2 A p q p' q'"
    and "a \<in> A"
  shows "bind_spmf p' (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q' (\<lambda>s. map_spmf fst (callee2 s a))"
proof -
  from assms(2) obtain xs where xs: "set xs \<subseteq> A \<times> UNIV" 
    and p: "p' = trace_callee_aux callee1 p xs" and q: "q' = trace_callee_aux callee2 q xs" by(cases)
  from trace_callee_eqD[OF assms(1) xs assms(3)] p q show ?thesis 
    by(simp add: trace_callee_conv_trace_callee_aux)
qed

lemma trace_callee_closure_sim:
  assumes "trace_callee_closure callee1 callee2 A p q p' q'"
    and "a \<in> A"
  shows "trace_callee_closure callee1 callee2 A p q
     (cond_spmf_fst (bind_spmf p' (\<lambda>s. callee1 s a)) b)
     (cond_spmf_fst (bind_spmf q' (\<lambda>s. callee2 s a)) b)"
  using assms  proof (cases)
  case (1 xs)
  then show ?thesis by 
      (auto simp add:trace_callee_closure.simps assms trace_callee_aux_append split_def map_spmf_conv_bind_spmf intro!: exI[where x="xs @ [(a, b)]"])     
qed

proposition trace_callee_eq_complete:
  assumes "trace_callee_eq callee1 callee2 A p q"
  obtains S
  where "S p q"                          
    and "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and "\<And>p q a s b s'. \<lbrakk> S p q; a \<in> A; s \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 s a) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
  by(rule that[where S="trace_callee_closure callee1 callee2 A p q"])
    (auto intro: trace_callee_closure_start trace_callee_closure_step[OF assms] trace_callee_closure_sim)

lemma set_spmf_cond_spmf_fst: "set_spmf (cond_spmf_fst p a) = snd ` (set_spmf p \<inter> {a} \<times> UNIV)"
  by(simp add: cond_spmf_fst_def)

lemma trace_callee_eq_run_gpv:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes trace_eq: "trace_callee_eq callee1 callee2 A p q"
    and inv1: "callee_invariant_on callee1 I1 \<I>"
    and inv1: "callee_invariant_on callee2 I2 \<I>"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and out: "outs_gpv \<I> gpv \<subseteq> A"
    and pq: "lossless_spmf p" "lossless_spmf q"
    and I1: "\<forall>x\<in>set_spmf p. I1 x"
    and I2: "\<forall>y\<in>set_spmf q. I2 y"
  shows "bind_spmf p (run_gpv callee1 gpv) = bind_spmf q (run_gpv callee2 gpv)"
proof -
  from trace_eq obtain S where start: "S p q"
    and sim: "\<And>p q a. \<lbrakk> S p q; a \<in> A \<rbrakk> \<Longrightarrow>
      bind_spmf p (\<lambda>s. map_spmf fst (callee1 s a)) = bind_spmf q (\<lambda>s. map_spmf fst (callee2 s a))"
    and S: "\<And>p q a s b s'. \<lbrakk> S p q; a \<in> A; s \<in> set_spmf q; (b, s') \<in> set_spmf (callee2 s a) \<rbrakk>
      \<Longrightarrow> S (cond_spmf_fst (bind_spmf p (\<lambda>s. callee1 s a)) b)
            (cond_spmf_fst (bind_spmf q (\<lambda>s. callee2 s a)) b)"
    by(rule trace_callee_eq_complete) blast

  interpret I1: callee_invariant_on callee1 I1 \<I> by fact
  interpret I2: callee_invariant_on callee2 I2 \<I> by fact

  from \<open>S p q\<close> out pq WT I1 I2 show ?thesis
  proof(induction arbitrary: p q gpv rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono exec_gpv.mono exec_gpv_def exec_gpv_def, case_names adm bottom step])
    case (step exec_gpv' g)
    have[simp]: "generat \<in> set_spmf (the_gpv gpv) \<Longrightarrow>
         p \<bind> (\<lambda>xa. map_spmf fst (case generat of 
             Pure x \<Rightarrow> return_spmf (x, xa)
           | IO out c \<Rightarrow> callee1 xa out \<bind> (\<lambda>(x, y). exec_gpv' (c x) y))) =
         q \<bind> (\<lambda>xa. map_spmf fst (case generat of 
             Pure x \<Rightarrow> return_spmf (x, xa)
           | IO out c \<Rightarrow> callee2 xa out \<bind> (\<lambda>(x, y). g (c x) y)))" for generat
    proof (cases generat, goal_cases)
      case (2 out rpv)
      have [simp]: "IO out rpv \<in> set_spmf (the_gpv gpv) \<Longrightarrow> generat = IO out rpv \<Longrightarrow>
        map_spmf fst (p \<bind> (\<lambda>xa. callee1 xa out)) = map_spmf fst (q \<bind> (\<lambda>xa. callee2 xa out))"
        unfolding map_bind_spmf o_def
        by (rule sim) (use step.prems in \<open>auto intro: outs_gpv.IO\<close>)

      have[simp]: "\<lbrakk>IO out rpv \<in> set_spmf (the_gpv gpv); generat = IO out rpv; x \<in> set_spmf q; (a, b) \<in> set_spmf (callee2 x out)\<rbrakk> \<Longrightarrow>
       cond_spmf_fst (p \<bind> (\<lambda>xa. callee1 xa out)) a \<bind> (\<lambda>x. map_spmf fst (exec_gpv' (rpv a) x)) =
       cond_spmf_fst (q \<bind> (\<lambda>xa. callee2 xa out)) a \<bind> (\<lambda>x. map_spmf fst (g (rpv a) x))" for a b x
      proof (rule step.IH, goal_cases)
        case 1 then show ?case using step.prems by(auto intro!: S intro: outs_gpv.IO)
      next
        case 2
        then show ?case using step.prems by(force intro: outs_gpv.Cont dest: WT_calleeD[OF I2.WT_callee] WT_gpvD[OF step.prems(5)])
      next
        case 3
        then show ?case using sim[OF \<open>S p q\<close>, of out] step.prems(2)
          by(force simp add: bind_UNION image_Union intro: rev_image_eqI intro: outs_gpv.IO dest: arg_cong[where f="set_spmf"])
      next
        case 4
        then show ?case by(auto 4 3 simp add: bind_UNION image_Union intro: rev_image_eqI)
      next
        case 5
        then show ?case using step.prems by(auto 4 3 dest: WT_calleeD[OF I2.WT_callee] intro: WT_gpvD)
      next
        case 6
        then show ?case using step.prems by(auto simp add: bind_UNION image_Union set_spmf_cond_spmf_fst intro: I1.callee_invariant WT_gpvD)
      next
        case 7
        then show ?case using step.prems by(auto simp add: bind_UNION image_Union set_spmf_cond_spmf_fst intro: I2.callee_invariant WT_gpvD)
      qed 

      from 2 show ?case 
        by(simp add: map_bind_spmf o_def)
          (subst (1 2) bind_spmf_assoc[symmetric]
            , rewrite in "bind_spmf \<hole> _ = _" cond_spmf_fst_inverse[symmetric]
            , rewrite in "_ = bind_spmf \<hole> _" cond_spmf_fst_inverse[symmetric]
            , subst (1 2) bind_spmf_assoc
            , auto simp add: bind_map_spmf o_def intro!: bind_spmf_cong)
    qed (simp add: bind_spmf_const lossless_weight_spmfD step.prems)

    show ?case unfolding map_bind_spmf o_def by(subst (1 2) bind_commute_spmf) (auto intro: bind_spmf_cong[OF refl])
  qed simp_all
qed

lemma trace_callee_eq'_run_gpv:
  fixes callee1 :: "('a, 'b, 's1) callee" and callee2 :: "('a, 'b, 's2) callee"
  assumes trace_eq: "A \<turnstile>\<^sub>C callee1(s1) \<approx> callee2(s2)"
    and inv1: "callee_invariant_on callee1 I1 \<I>"
    and inv1: "callee_invariant_on callee2 I2 \<I>"
    and WT: "\<I> \<turnstile>g gpv \<surd>"
    and out: "outs_gpv \<I> gpv \<subseteq> A"
    and I1: "I1 s1"
    and I2: "I2 s2"
  shows "run_gpv callee1 gpv s1 = run_gpv callee2 gpv s2"
  using trace_callee_eq_run_gpv[OF assms(1-5)] assms(6-) by simp

abbreviation trace_eq :: "'a set \<Rightarrow> ('a, 'b) resource spmf \<Rightarrow> ('a, 'b) resource spmf \<Rightarrow> bool" where
  "trace_eq \<equiv> trace_callee_eq run_resource run_resource"

abbreviation trace_eq' :: "'a set \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool" ("(_) \<turnstile>\<^sub>R/ (_)/ \<approx> (_)" [90, 90, 90] 91) where
  "A \<turnstile>\<^sub>R res \<approx> res' \<equiv> trace_eq A (return_spmf res) (return_spmf res')"

lemma trace_callee_resource_of_oracle2:
  "trace_callee run_resource (map_spmf (resource_of_oracle callee) p) xs x =
   trace_callee callee p xs x"
proof(induction xs arbitrary: p)
  case (Cons xy xs)
  then show ?case by (cases xy) (simp add: bind_map_spmf o_def Cons.IH[symmetric] cond_spmf_fst_def map_bind_spmf[symmetric, unfolded o_def] spmf.map_comp map_prod_vimage)
qed (simp add: map_bind_spmf bind_map_spmf o_def spmf.map_comp)

lemma trace_callee_resource_of_oracle [simp]:
  "trace_callee run_resource (return_spmf (resource_of_oracle callee s)) xs x =
   trace_callee callee (return_spmf s) xs x"
  using trace_callee_resource_of_oracle2[of callee "return_spmf s" xs x] by simp

lemma trace_eq'_resource_of_oracle [simp]:
  "A \<turnstile>\<^sub>R resource_of_oracle callee1 s1 \<approx> resource_of_oracle callee2 s2 =
   A \<turnstile>\<^sub>C callee1(s1) \<approx> callee2(s2)"
  by(simp add: trace_callee_eq_def)

end
