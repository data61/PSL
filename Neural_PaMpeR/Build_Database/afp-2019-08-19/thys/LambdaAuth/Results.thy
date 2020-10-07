(* Author: Matthias Brun,   ETH Zürich, 2019 *)
(* Author: Dmitriy Traytel, ETH Zürich, 2019 *)

section \<open>Formalization of Miller et al.'s~\cite{adsg} Main Results\<close>

(*<*)
theory Results
  imports Agreement
begin
(*>*)

lemma judge_imp_agree:
  assumes "\<Gamma> \<turnstile> e : \<tau>"
  shows   "\<Gamma> \<turnstile> e, e, e : \<tau>"
  using assms by (induct \<Gamma> e \<tau>) (auto simp: fresh_Pair)

subsection \<open>Lemma 2.1\<close>

lemma lemma2_1:
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>"
  shows   "\<lparr>eP\<rparr> = eV"
  using assms by (induct \<Gamma> e eP eV \<tau>) (simp_all add: Abs1_eq)

subsection \<open>Counterexample to Lemma 2.2\<close>

lemma lemma2_2_false:
  fixes x :: var
  assumes "\<And>\<Gamma> e eP eV \<tau> eP' eV'. \<lbrakk> \<Gamma> \<turnstile> e, eP, eV : \<tau>; \<Gamma> \<turnstile> e, eP', eV' : \<tau> \<rbrakk> \<Longrightarrow> eP = eP' \<and> eV = eV'"
  shows False
proof -
  have a1: "{$$} \<turnstile> Prj1 (Pair Unit Unit), Prj1 (Pair Unit Unit), Prj1 (Pair Unit Unit) : One"
    by fastforce
  also have a2: "{$$} \<turnstile> Prj1 (Pair Unit Unit), Prj1 (Pair Unit (Hashed (hash Unit) Unit)), Prj1 (Pair Unit (Hash (hash Unit))) : One"
    by fastforce
  from a1 a2 have "Prj1 (Pair Unit Unit) = Prj1 (Pair Unit (Hash (hash Unit)))"
    by (auto dest: assms)
  then show False
    by simp
qed

lemma smallstep_ideal_deterministic:
  "\<lless>[], t\<ggreater> I\<rightarrow> \<lless>[], u\<ggreater> \<Longrightarrow> \<lless>[], t\<ggreater> I\<rightarrow> \<lless>[], u'\<ggreater> \<Longrightarrow> u = u'"
proof (nominal_induct "[]::proofstream" t I "[]::proofstream" u avoiding: u' rule: smallstep.strong_induct)
  case (s_App1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from s_App1(3) value_no_step[OF s_App1(1)] show ?case
    by (auto dest!: s_App1(2))
next
  case (s_App2 v\<^sub>1 e\<^sub>2 e\<^sub>2')
  from s_App2(4) value_no_step[OF s_App2(2)] value_no_step[OF _ s_App2(1)] show ?case
    by (force dest!: s_App2(3))
next
  case (s_AppLam v x e)
  from  s_AppLam(5,1,3) value_no_step[OF _ s_AppLam(2)] show ?case
  proof (cases rule: s_App_inv)
    case (AppLam y e')
    obtain z :: var where "atom z \<sharp> (x, e, y, e')"
      by (metis obtain_fresh)
    with AppLam s_AppLam(1,3) show ?thesis
      by (auto simp: fresh_Pair intro: box_equals[OF _ subst_term_perm[symmetric, of z] subst_term_perm[symmetric, of z]])
  qed (auto dest: value_no_step)
next
  case (s_AppRec v x e)
  from s_AppRec(5,1,3) value_no_step[OF _ s_AppRec(2)] show ?case
  proof (cases rule: s_App_inv)
    case (AppRec y e')
    obtain z :: var where "atom z \<sharp> (x, e, y, e')"
      by (metis obtain_fresh)
    with AppRec(1-4) AppRec(5)[simplified] s_AppRec(1,3) show ?thesis
      by (auto simp: fresh_Pair AppRec(5)
          intro: box_equals[OF _ subst_term_perm[symmetric, of z] subst_term_perm[symmetric, of z]])
  qed (auto dest: value_no_step)
next
  case (s_Let1 x e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from s_Let1(1,2,3,8) value_no_step[OF s_Let1(6)] show ?case
    by (auto dest: s_Let1(7))
next
  case (s_Let2 v x e)
  from s_Let2(1,3,5) value_no_step[OF _ s_Let2(2)] show ?case
    by force
next
  case (s_Inj1 e e')
  from s_Inj1(2,3) show ?case
    by auto
next
  case (s_Inj2 e e')
  from s_Inj2(2,3) show ?case
    by auto
next
  case (s_Case e e' e\<^sub>1 e\<^sub>2)
  from s_Case(2,3) value_no_step[OF s_Case(1)] show ?case
    by auto
next
  case (s_Pair1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from s_Pair1(2,3) value_no_step[OF s_Pair1(1)] show ?case
    by auto
next
  case (s_Pair2 v\<^sub>1 e\<^sub>2 e\<^sub>2')
  from s_Pair2(3,4) value_no_step[OF _ s_Pair2(1)] value_no_step[OF s_Pair2(2)] show ?case
    by force
next
  case (s_Prj1 e e')
  from s_Prj1(2,3) value_no_step[OF s_Prj1(1)] show ?case
    by auto
next
  case (s_Prj2 e e')
  from s_Prj2(2,3) value_no_step[OF s_Prj2(1)] show ?case
    by auto
next
  case (s_Unroll e e')
  from s_Unroll(2,3) value_no_step[OF s_Unroll(1)] show ?case
    by auto
next
  case (s_Roll e e')
  from s_Roll(2,3) show ?case
    by auto
next
  case (s_Auth e e')
  from s_Auth(2,3) value_no_step[OF s_Auth(1)] show ?case
    by auto
next
  case (s_Unauth e e')
  from s_Unauth(2,3) value_no_step[OF s_Unauth(1)] show ?case
    by auto
qed (auto 0 3 dest: value_no_step)

lemma smallsteps_ideal_deterministic:
  "\<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], u\<ggreater> \<Longrightarrow> \<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], u'\<ggreater> \<Longrightarrow> u = u'"
proof (induct "[]::proofstream" t I i "[]::proofstream" u arbitrary: u' rule: smallsteps.induct)
  case (s_Tr e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 e\<^sub>3)
  from s_Tr(4) show ?case
  proof (cases rule: smallsteps.cases)
    case _: (s_Tr i \<pi>\<^sub>4 e\<^sub>4)
    with s_Tr(1,3) s_Tr(2)[of e\<^sub>4] show ?thesis
      using smallstepsI_ps_emptyD(2)[of e\<^sub>1 i \<pi>\<^sub>4 e\<^sub>4] smallstepI_ps_eq[of \<pi>\<^sub>2 e\<^sub>2 "[]" e\<^sub>3]
      by (auto intro!: smallstep_ideal_deterministic elim!: smallstepI_ps_emptyD)
  qed simp
qed auto

subsection \<open>Lemma 2.3\<close>

lemma lemma2_3:
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>"
  shows   "erase_env \<Gamma> \<turnstile>\<^sub>W e : erase \<tau>"
  using assms unfolding erase_env_def
proof (nominal_induct \<Gamma> e eP eV \<tau> rule: agree.strong_induct)
  case (a_HashI v vP \<tau> h \<Gamma>)
  then show ?case
    by (induct \<Gamma>) (auto simp: judge_weak_weakening_2 fmmap_fmupd judge_weak_fresh_env_fresh_term fresh_tyenv_None)
qed (simp_all add: fresh_fmmap_erase_fresh fmmap_fmupd judge_weak_fresh_env_fresh_term)

subsection \<open>Lemma 2.4\<close>

lemma lemma2_4[dest]:
  assumes "\<Gamma> \<turnstile> e, eP, eV : \<tau>"
  shows   "value e \<and> value eP \<and> value eV \<or> \<not> value e \<and> \<not> value eP \<and> \<not> value eV"
  using assms by (nominal_induct \<Gamma> e eP eV \<tau> rule: agree.strong_induct) auto

subsection \<open>Lemma 3\<close>

lemma lemma3_general:
  fixes \<Gamma> :: tyenv and vs vPs vVs :: tenv
  assumes "\<Gamma> \<turnstile> e : \<tau>" "A |\<subseteq>| fmdom \<Gamma>"
  and     "fmdom vs = A" "fmdom vPs = A" "fmdom vVs = A"
  and     "\<forall>x. x |\<in>| A \<longrightarrow> (\<exists>\<tau>' v vP h.
    \<Gamma> $$ x = Some (AuthT \<tau>') \<and>
    vs $$ x = Some v \<and>
   vPs $$ x = Some (Hashed h vP) \<and>
   vVs $$ x = Some (Hash h) \<and>
   {$$} \<turnstile> v, Hashed h vP, Hash h : (AuthT \<tau>'))"
  shows  "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : \<tau>"
  using assms
proof (nominal_induct \<Gamma> e \<tau> avoiding: vs vPs vVs A rule: judge.strong_induct)
  case (j_Unit \<Gamma>)
  then show ?case
    by auto
next
  case (j_Var \<Gamma> x \<tau>)
  with j_Var show ?case
  proof (cases "x |\<in>| A")
    case True
    with j_Var show ?thesis
      by (fastforce dest!: spec[of _ x] intro: agree_weakening_env)
  next
    case False
    with j_Var show ?thesis
      by (auto simp add: a_Var dest!: fmdomI split: option.splits)
  qed
next
  case (j_Lam x \<Gamma> \<tau>\<^sub>1 e \<tau>\<^sub>2)
  from j_Lam(4) have [simp]: "A |-| {|x|} = A"
    by (simp add: fresh_fset_fminus)
  from j_Lam(5,8-) have "fmdrop_fset A \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : \<tau>\<^sub>2"
    by (intro j_Lam(7)[of A vs vPs vVs]) (auto simp: fresh_tyenv_None)
  with j_Lam(1-5) show ?case
    by (auto simp: fresh_fmdrop_fset)
next
  case (j_App \<Gamma> e \<tau>\<^sub>1 \<tau>\<^sub>2 e')
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
    and "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e' vs, psubst_term e' vPs, psubst_term e' vVs : \<tau>\<^sub>1"
    by simp_all
  then show ?case
    by auto
next
  case (j_Let x \<Gamma> e\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 \<tau>\<^sub>2)
  from j_Let(4) have [simp]: "A |-| {|x|} = A"
    by (simp add: fresh_fset_fminus)
  from j_Let(8,11-) have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e\<^sub>1 vs, psubst_term e\<^sub>1 vPs, psubst_term e\<^sub>1 vVs : \<tau>\<^sub>1"
    by simp
  moreover from j_Let(4,5,11-) have "fmdrop_fset A \<Gamma>(x $$:= \<tau>\<^sub>1) \<turnstile> psubst_term e\<^sub>2 vs, psubst_term e\<^sub>2 vPs, psubst_term e\<^sub>2 vVs : \<tau>\<^sub>2"
    by (intro j_Let(10)) (auto simp: fresh_tyenv_None)
  ultimately show ?case using j_Let(1-6)
    by (auto simp: fresh_fmdrop_fset fresh_Pair fresh_psubst)
next
  case (j_Rec x \<Gamma> y \<tau>\<^sub>1 \<tau>\<^sub>2 e')
  from j_Rec(4) have [simp]: "A |-| {|x|} = A"
    by (simp add: fresh_fset_fminus)
  from j_Rec(9,14-) have "fmdrop_fset A \<Gamma>(x $$:= Fun \<tau>\<^sub>1 \<tau>\<^sub>2) \<turnstile> psubst_term (Lam y e') vs, psubst_term (Lam y e') vPs, psubst_term (Lam y e') vVs : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
    by (intro j_Rec(13)) (auto simp: fresh_tyenv_None)
  with j_Rec(1-11) show ?case
    by (auto simp: fresh_fmdrop_fset)
next
  case (j_Case \<Gamma> e \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>1 \<tau> e\<^sub>2)
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e  vs, psubst_term e  vPs, psubst_term e  vVs : Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
    and "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e\<^sub>1 vs, psubst_term e\<^sub>1 vPs, psubst_term e\<^sub>1 vVs : Fun \<tau>\<^sub>1 \<tau>"
    and "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e\<^sub>2 vs, psubst_term e\<^sub>2 vPs, psubst_term e\<^sub>2 vVs : Fun \<tau>\<^sub>2 \<tau>"
    by simp_all
  then show ?case
    by auto
next
  case (j_Prj1 \<Gamma> e \<tau>\<^sub>1 \<tau>\<^sub>2)
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"
    by simp
  then show ?case
    by auto
next
  case (j_Prj2 \<Gamma> e \<tau>\<^sub>1 \<tau>\<^sub>2)
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : Prod \<tau>\<^sub>1 \<tau>\<^sub>2"
    by simp
  then show ?case
    by auto
next
  case (j_Roll \<alpha> \<Gamma> e \<tau>)
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
    by simp
  with j_Roll(4,5) show ?case
    by (auto simp: fresh_fmdrop_fset)
next
  case (j_Unroll \<alpha> \<Gamma> e \<tau>)
  then have "fmdrop_fset A \<Gamma> \<turnstile> psubst_term e vs, psubst_term e vPs, psubst_term e vVs : Mu \<alpha> \<tau>"
    by simp
  with j_Unroll(4,5) show ?case
    by (auto simp: fresh_fmdrop_fset)
qed auto

lemmas lemma3 = lemma3_general[where A = "fmdom \<Gamma>" and \<Gamma> = \<Gamma>, simplified] for \<Gamma>

subsection \<open>Lemma 4\<close>

lemma lemma4:
  assumes "\<Gamma>(x $$:= \<tau>') \<turnstile> e, eP, eV : \<tau>"
  and     "{$$} \<turnstile> v, vP, vV : \<tau>'"
  and     "value v" "value vP" "value vV"
  shows   "\<Gamma> \<turnstile> e[v / x], eP[vP / x], eV[vV / x] : \<tau>"
  using assms
proof (nominal_induct "\<Gamma>(x $$:= \<tau>')" e eP eV \<tau> avoiding: x \<Gamma> rule: agree.strong_induct)
  case a_Unit
  then show ?case by auto
next
  case (a_Var y \<tau>)
  then show ?case
  proof (induct \<Gamma>)
    case fmempty
    then show ?case by (metis agree.a_Var fmupd_lookup option.sel subst_term.simps(2))
  next
    case (fmupd x y \<Gamma>)
    then show ?case
      using agree_weakening_2 fresh_tyenv_None by auto
  qed
next
  case (a_Lam y \<tau>\<^sub>1 e eP eV \<tau>\<^sub>2)
  from a_Lam(1,2,5,6,7-) show ?case
    using agree_empty_fresh by (auto simp: fmap_reorder_neq_updates)
next
  case (a_App v\<^sub>1 v\<^sub>2 v\<^sub>1P v\<^sub>2P v\<^sub>1V v\<^sub>2V \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_App(5-) show ?case
    by (auto intro: a_App(2,4))
next
  case (a_Let y e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  then show ?case
    using agree_empty_fresh by (auto simp: fmap_reorder_neq_updates intro!: agree.a_Let[where x=y])
next
  case (a_Rec y z \<tau>\<^sub>1 \<tau>\<^sub>2 e eP eV)
  from a_Rec(10) have "\<forall>a::var. atom a \<sharp> v" "\<forall>a::var. atom a \<sharp> vP" "\<forall>a::var. atom a \<sharp> vV"
    by auto
  with a_Rec(1-8,10-) show ?case
    using a_Rec(9)[OF fmap_reorder_neq_updates]
    by (auto simp: fmap_reorder_neq_updates intro!: agree.a_Rec[where x=y])
next
  case (a_Case v v\<^sub>1 v\<^sub>2 vP v\<^sub>1P v\<^sub>2P vV v\<^sub>1V v\<^sub>2V \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)
  from a_Case(7-) show ?case
    by (auto intro: a_Case(2,4,6))
next
  case (a_HashI v vP \<tau> h)
  then have "atom x \<sharp> v" "atom x \<sharp> vP" by auto
  with a_HashI show ?case by auto
qed auto

subsection \<open>Lemma 5:  Single-Step Correctness\<close>

lemma lemma5:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater>"
  obtains eP' eV' \<pi>
  where   "{$$} \<turnstile> e', eP', eV' : \<tau>" "\<forall>\<pi>\<^sub>P. \<lless> \<pi>\<^sub>P, eP \<ggreater> P\<rightarrow> \<lless> \<pi>\<^sub>P @ \<pi>, eP' \<ggreater>" "\<forall>\<pi>'. \<lless> \<pi> @ \<pi>', eV \<ggreater> V\<rightarrow> \<lless> \<pi>', eV' \<ggreater>"
proof (atomize_elim, insert assms, nominal_induct "{$$}::tyenv" e eP eV \<tau> avoiding: e' rule: agree.strong_induct)
  case (a_App e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_App(5) show ?case
  proof (cases rule: s_App_inv)
    case (App1 e\<^sub>1')
    with a_App(2) obtain eP\<^sub>1' eV\<^sub>1' \<pi> where *: "{$$} \<turnstile> e\<^sub>1', eP\<^sub>1', eV\<^sub>1' : Fun \<tau>\<^sub>1 \<tau>\<^sub>2"
      "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<^sub>1\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP\<^sub>1'\<ggreater>" "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<^sub>1\<ggreater> V\<rightarrow> \<lless>\<pi>', eV\<^sub>1'\<ggreater>"
      by blast
    show ?thesis
    proof (intro exI conjI)
      from * App1 a_App(1,3,5-)
      show "{$$} \<turnstile> e', App eP\<^sub>1' eP\<^sub>2, App eV\<^sub>1' eV\<^sub>2 : \<tau>\<^sub>2"
        "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, App eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, App eP\<^sub>1' eP\<^sub>2\<ggreater>"
        "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', App eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', App eV\<^sub>1' eV\<^sub>2\<ggreater>"
        by auto
    qed
  next
    case (App2 e\<^sub>2')
    with a_App(4) obtain eP\<^sub>2' eV\<^sub>2' \<pi> where *: "{$$} \<turnstile> e\<^sub>2', eP\<^sub>2', eV\<^sub>2' : \<tau>\<^sub>1"
      "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP\<^sub>2'\<ggreater>" "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', eV\<^sub>2'\<ggreater>"
      by blast
    show ?thesis
    proof (intro exI conjI)
      from * App2 a_App(1,3,5-)
      show "{$$} \<turnstile> e', App eP\<^sub>1 eP\<^sub>2', App eV\<^sub>1 eV\<^sub>2' : \<tau>\<^sub>2"
        "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, App eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, App eP\<^sub>1 eP\<^sub>2'\<ggreater>"
        "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', App eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', App eV\<^sub>1 eV\<^sub>2'\<ggreater>"
        by auto
    qed
  next
    case (AppLam x e)
    from a_App(1)[unfolded \<open>e\<^sub>1 = Lam x e\<close>] show ?thesis
    proof (cases rule: a_Lam_inv_I[case_names _ Lam])
      case (Lam eP eV)
      show ?thesis
      proof (intro exI conjI)
        from Lam a_App(3,5) AppLam show "{$$} \<turnstile> e', eP[eP\<^sub>2 / x], eV[eV\<^sub>2 / x] : \<tau>\<^sub>2"
          by (auto intro: lemma4)
        from Lam a_App(3,5) AppLam show "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, App eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ [], eP[eP\<^sub>2 / x]\<ggreater>"
          by (intro allI iffD1[OF smallstepP_ps_prepend[where \<pi> = "[]", simplified]])
            (auto simp: fresh_Pair intro!: s_AppLam[where v=eP\<^sub>2])
        from Lam a_App(3,5) AppLam show "\<forall>\<pi>'. \<lless>[] @ \<pi>', App eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', eV[eV\<^sub>2 / x]\<ggreater>"
          by (intro allI iffD1[OF smallstepV_ps_append[where \<pi>' = "[]", simplified]])
            (auto simp: fresh_Pair intro!: s_AppLam[where v=eV\<^sub>2])
      qed
    qed simp
  next
    case (AppRec x e)
    from a_App(1)[unfolded \<open>e\<^sub>1 = Rec x e\<close>] show ?thesis
    proof (cases rule: a_Rec_inv_I[consumes 1, case_names _ Rec])
      case (Rec y e'' eP' eV')
      from Rec(5,4) show ?thesis
      proof (cases rule: a_Lam_inv_I[consumes 1, case_names _ Lam])
        case (Lam eP'' eV'')
        show ?thesis
        proof (intro conjI exI[of _ "[]"] exI)
          let ?eP = "App (Lam y eP''[Rec x (Lam y eP'') / x]) eP\<^sub>2"
          let ?eV = "App (Lam y eV''[Rec x (Lam y eV'') / x]) eV\<^sub>2"
          from a_App(3) AppRec have [simp]: "value eP\<^sub>2" "atom x \<sharp> eP\<^sub>2" "value eV\<^sub>2" "atom x \<sharp> eV\<^sub>2"
            by (auto simp: fresh_Pair)
          from Lam a_App(3,5-) AppRec Rec show "{$$} \<turnstile> e', ?eP, ?eV : \<tau>\<^sub>2"
            unfolding term.eq_iff Abs1_eq(3)
            by (auto simp: fmap_reorder_neq_updates
              intro!: agree.a_App[where \<Gamma>="{$$}"] a_Lam[where x=y] lemma4)
          from Lam a_App(3,5-) AppRec Rec show "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, App eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ [], ?eP\<ggreater>"
            unfolding term.eq_iff Abs1_eq(3)
            using s_AppRec[where v=eP\<^sub>2 and x=x and \<pi>="[]" and e="Lam y eP''" and uv=P]
            by (intro allI iffD1[OF smallstepP_ps_prepend[of "[]", simplified]])
              (auto simp: fresh_Pair simp del: s_AppRec)
          from Lam a_App(3,5-) AppRec Rec show "\<forall>\<pi>'. \<lless>[] @ \<pi>', App eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', ?eV\<ggreater>"
            unfolding term.eq_iff Abs1_eq(3)
            using s_AppRec[where v=eV\<^sub>2 and x=x and \<pi>="[]" and e="Lam y eV''" and uv=V]
            by (intro allI iffD1[OF smallstepV_ps_append[of _ _ "[]", simplified]])
              (auto simp: fresh_Pair simp del: s_AppRec)
        qed
      qed (simp add: fresh_fmap_update)
    qed simp
  qed
next
  case (a_Let x e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  then have "atom x \<sharp> (e\<^sub>1, [])" by auto
  with a_Let(10) show ?case
  proof (cases rule: s_Let_inv)
    case Let1
    show ?thesis
    proof (intro conjI exI[of _ "[]"] exI)
      from a_Let(6,8) Let1 show "{$$} \<turnstile> e', eP\<^sub>2[eP\<^sub>1 / x], eV\<^sub>2[eV\<^sub>1 / x] : \<tau>\<^sub>2"
        by (auto intro: lemma4)
      from a_Let(4,6) Let1 show "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Let eP\<^sub>1 x eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ [], eP\<^sub>2[eP\<^sub>1 / x]\<ggreater>"
        by (intro allI iffD1[OF smallstepP_ps_prepend[of "[]", simplified]] s_Let2) auto
      from a_Let(5,6) Let1 show "\<forall>\<pi>'. \<lless>[] @ \<pi>', Let eV\<^sub>1 x eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', eV\<^sub>2[eV\<^sub>1 / x]\<ggreater>"
        by (intro allI iffD1[OF smallstepV_ps_append[of _ _ "[]", simplified]] s_Let2) auto
    qed
  next
    case (Let2 e\<^sub>1')
    moreover
    from Let2 a_Let(7) obtain eP\<^sub>1' eV\<^sub>1' \<pi>
      where ih: "{$$} \<turnstile> e\<^sub>1', eP\<^sub>1', eV\<^sub>1' : \<tau>\<^sub>1"
        "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<^sub>1\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP\<^sub>1'\<ggreater>"
        "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<^sub>1\<ggreater> V\<rightarrow> \<lless>\<pi>', eV\<^sub>1'\<ggreater>"
      by (blast dest: spec[of _ "[]"])
    then have [simp]: "atom x \<sharp> ({$$}, e\<^sub>1', eP\<^sub>1', eV\<^sub>1')"
      using agree_empty_fresh by auto
    from ih a_Let(4) have [simp]: "atom x \<sharp> \<pi>"
      using fresh_Nil fresh_append fresh_ps_smallstep_P by blast
    from a_Let ih have agree: "{$$} \<turnstile> Let e\<^sub>1' x e\<^sub>2, Let eP\<^sub>1' x eP\<^sub>2, Let eV\<^sub>1' x eV\<^sub>2 : \<tau>\<^sub>2"
      by auto
    moreover from a_Let(4,5) ih(1) spec[OF ih(2), of "[]", simplified]
    have "\<lless>\<pi>', Let eP\<^sub>1 x eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>' @ \<pi>, Let eP\<^sub>1' x eP\<^sub>2\<ggreater>" for \<pi>'
      by (intro iffD1[OF smallstepP_ps_prepend[of "[]", simplified]] s_Let1) (auto simp: fresh_Pair)
    moreover from a_Let(4,5) ih(1) spec[OF ih(3), of "[]", simplified]
    have "\<lless>\<pi> @ \<pi>', Let eV\<^sub>1 x eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', Let eV\<^sub>1' x eV\<^sub>2\<ggreater>" for \<pi>'
      by (intro iffD1[OF smallstepV_ps_append[of \<pi> _ "[]", simplified]] s_Let1) (auto simp: fresh_Pair)
    ultimately show ?thesis
      by blast
  qed
next
  case (a_Case e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau> e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_Case(7) show ?case
  proof (cases rule: s_Case_inv)
    case (Case e'')
    with a_Case(2)[of e''] obtain eP'' eV'' \<pi> where ih: "{$$} \<turnstile> e'', eP'', eV'' : Syntax.Sum \<tau>\<^sub>1 \<tau>\<^sub>2"
      "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP''\<ggreater>" "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<ggreater> V\<rightarrow> \<lless>\<pi>', eV''\<ggreater>"
      by blast
    show ?thesis
    proof (intro conjI exI[of _ \<pi>] exI)
      from ih(1) a_Case(3,5) Case show "{$$} \<turnstile> e', Case eP'' eP\<^sub>1 eP\<^sub>2, Case eV'' eV\<^sub>1 eV\<^sub>2 : \<tau>"
        by auto
      from a_Case(5) spec[OF ih(2), of "[]", simplified]
      show "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Case eP eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, Case eP'' eP\<^sub>1 eP\<^sub>2\<ggreater>"
        by (intro allI iffD1[OF smallstepP_ps_prepend[of "[]", simplified]] s_Case) auto
      from a_Case(5) spec[OF ih(3), of "[]", simplified]
      show "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', Case eV eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>', Case eV'' eV\<^sub>1 eV\<^sub>2\<ggreater>"
        by (intro allI iffD1[OF smallstepV_ps_append[of _ _ "[]", simplified]] s_Case) auto
    qed
  next
    case (Inj1 v)
    from a_Case(1)[unfolded \<open>e = Inj1 v\<close>] show ?thesis
    proof (cases rule: a_Inj1_inv_I[consumes 1, case_names Case])
      case (Case vP vV)
      with a_Case(3,5) Inj1 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI)
        from Case a_Case(3,5) Inj1 show "{$$} \<turnstile> e', App eP\<^sub>1 vP, App eV\<^sub>1 vV : \<tau>"
          by auto
      qed auto
    qed
  next
    case (Inj2 v)
    from a_Case(1)[unfolded \<open>e = Inj2 v\<close>] show ?thesis
    proof (cases rule: a_Inj2_inv_I[consumes 1, case_names Case])
      case (Case vP vV)
      with a_Case(3,5) Inj2 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI)
        from Case a_Case(3,5) Inj2 show "{$$} \<turnstile> e', App eP\<^sub>2 vP, App eV\<^sub>2 vV : \<tau>"
          by auto
      qed auto
    qed
  qed
next
  case (a_Prj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Prj1(3) show ?case
  proof (cases rule: s_Prj1_inv)
    case (Prj1 e'')
    then show ?thesis
      by (blast dest!: a_Prj1(2))
  next
    case (PrjPair1 v\<^sub>2)
    from a_Prj1(1)[unfolded \<open>e = Syntax.Pair e' v\<^sub>2\<close>] show ?thesis
    proof (cases rule: a_Pair_inv_I[consumes 1, case_names Pair])
      case (Pair eP\<^sub>1 eV\<^sub>1 eP\<^sub>2 eV\<^sub>2)
      with PrjPair1 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI)
        show "{$$} \<turnstile> e', eP\<^sub>1, eV\<^sub>1 : \<tau>\<^sub>1"
          by (rule Pair)
      qed auto
    qed
  qed
next
  case (a_Prj2 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Prj2(3) show ?case
  proof (cases rule: s_Prj2_inv)
    case (Prj2 e'')
    then show ?thesis
      by (blast dest!: a_Prj2(2))
  next
    case (PrjPair2 v\<^sub>1)
    from a_Prj2(1)[unfolded \<open>e = Syntax.Pair v\<^sub>1 e'\<close>] show ?thesis
    proof (cases rule: a_Pair_inv_I[consumes 1, case_names Pair])
      case (Pair eP\<^sub>1 eV\<^sub>1 eP\<^sub>2 eV\<^sub>2)
      with PrjPair2 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI)
        show "{$$} \<turnstile> e', eP\<^sub>2, eV\<^sub>2 : \<tau>\<^sub>2"
          by (rule Pair)
      qed auto
    qed
  qed
next
  case (a_Roll \<alpha> e eP eV \<tau>)
  from a_Roll(5) show ?case
  proof (cases rule: s_Roll_inv)
    case (Roll e'')
    with a_Roll(4) obtain eP'' eV'' \<pi> where *: "{$$} \<turnstile> e'', eP'', eV'' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
      "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP''\<ggreater>" "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<ggreater> V\<rightarrow> \<lless>\<pi>', eV''\<ggreater>"
      by blast
    show ?thesis
    proof (intro exI conjI)
      from * Roll
      show "{$$} \<turnstile> e', Roll eP'', Roll eV'' : Mu \<alpha> \<tau>"
        "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Roll eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, Roll eP''\<ggreater>"
        "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', Roll eV\<ggreater> V\<rightarrow> \<lless>\<pi>', Roll eV''\<ggreater>"
        by auto
    qed
  qed
next
  case (a_Unroll \<alpha> e eP eV \<tau>)
  from a_Unroll(5) show ?case
  proof (cases rule: s_Unroll_inv)
    case (Unroll e'')
    with a_Unroll(4) obtain eP'' eV'' \<pi> where *: "{$$} \<turnstile> e'', eP'', eV'' : Mu \<alpha> \<tau>"
      "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP''\<ggreater>" "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', eV\<ggreater> V\<rightarrow> \<lless>\<pi>', eV''\<ggreater>"
      by blast
    show ?thesis
    proof (intro exI conjI)
      from * Unroll
      show "{$$} \<turnstile> e', Unroll eP'', Unroll eV'' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>"
        "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Unroll eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, Unroll eP''\<ggreater>"
        "\<forall>\<pi>'. \<lless>\<pi> @ \<pi>', Unroll eV\<ggreater> V\<rightarrow> \<lless>\<pi>', Unroll eV''\<ggreater>"
        by auto
    qed
  next
    case UnrollRoll
    with a_Unroll(3)[unfolded \<open>e = Roll e'\<close>] show ?thesis
    proof (cases rule: a_Roll_inv_I[case_names Roll])
      case (Roll eP' eV')
      with UnrollRoll show ?thesis
      proof (intro conjI exI[of _ "[]"] exI)
        show "{$$} \<turnstile> e', eP', eV' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha>" by fact
      qed auto
    qed
  qed
next
  case (a_Auth e eP eV \<tau>)
  from a_Auth(1) have [simp]: "atom x \<sharp> eP" for x :: var
    using agree_empty_fresh by simp
  from a_Auth(3) show ?case
  proof (cases rule: s_AuthI_inv)
    case (Auth e'')
    then show ?thesis
      by (blast dest!: a_Auth(2))
  next
    case AuthI
    with a_Auth(1) have "value eP" "value eV" by auto
    with a_Auth(1) AuthI(2) show ?thesis
    proof (intro conjI exI[of _ "[]"] exI)
      from a_Auth(1) AuthI(2) \<open>value eP\<close>
      show "{$$} \<turnstile> e', Hashed (hash \<lparr>eP\<rparr>) eP, Hash (hash \<lparr>eP\<rparr>) : AuthT \<tau>"
        by (auto dest: lemma2_1 simp: fresh_shallow)
    qed (auto dest: lemma2_1 simp: fresh_shallow)
  qed
next
  case (a_Unauth e eP eV \<tau>)
  from a_Unauth(1) have eP_closed: "closed eP"
    using agree_empty_fresh by simp
  from a_Unauth(3) show ?case
  proof (cases rule: s_UnauthI_inv)
    case (Unauth e')
    then show ?thesis
      by (blast dest!: a_Unauth(2))
  next
    case UnauthI
    with a_Unauth(1) have "value eP" "value eV" by auto
    from a_Unauth(1) show ?thesis
    proof (cases rule: a_AuthT_value_inv[case_names _ _ _ Unauth])
      case (Unauth vP')
      show ?thesis
      proof (intro conjI exI[of _ "[\<lparr>vP'\<rparr>]"] exI)
        from Unauth(1,2) UnauthI(2) a_Unauth(1)
        show "{$$} \<turnstile> e', vP', \<lparr>vP'\<rparr> : \<tau>"
          by (auto simp: fresh_shallow)
        then have "closed vP'"
          by auto
        with Unauth(1,2) a_Unauth(1) show
          "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Unauth eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ [\<lparr>vP'\<rparr>], vP'\<ggreater>"
          "\<forall>\<pi>'. \<lless>[\<lparr>vP'\<rparr>] @ \<pi>', Unauth eV\<ggreater> V\<rightarrow> \<lless>\<pi>', \<lparr>vP'\<rparr>\<ggreater>"
          by (auto simp: fresh_shallow)
      qed
    qed (auto simp: \<open>value e\<close> \<open>value eP\<close> \<open>value eV\<close>)
  qed
next
  case (a_Pair e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  from a_Pair(5) show ?case
  proof (cases rule: s_Pair_inv)
    case (Pair1 e\<^sub>1')
    with a_Pair(1,3) show ?thesis
      by (blast dest!: a_Pair(2))
  next
    case (Pair2 e\<^sub>2')
    with a_Pair(1,3) show ?thesis
      by (blast dest!: a_Pair(4))
  qed
next
  case (a_Inj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Inj1(3) show ?case
  proof (cases rule: s_Inj1_inv)
    case (Inj1 e')
    with a_Inj1(1) show ?thesis
      by (blast dest!: a_Inj1(2))
  qed
next
  case (a_Inj2 e eP eV \<tau>\<^sub>2 \<tau>\<^sub>1)
  from a_Inj2(3) show ?case
  proof (cases rule: s_Inj2_inv)
    case (Inj2 e'')
    with a_Inj2(1) show ?thesis
      by (blast dest!: a_Inj2(2))
  qed
qed (simp, meson value.intros value_no_step)+

subsection \<open>Lemma 6: Single-Step Security\<close>

lemma lemma6:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> \<pi>\<^sub>A, eV \<ggreater> V\<rightarrow> \<lless> \<pi>', eV' \<ggreater>"
  obtains e' eP' \<pi>
  where "\<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater>" "\<forall>\<pi>\<^sub>P. \<lless> \<pi>\<^sub>P, eP \<ggreater> P\<rightarrow> \<lless> \<pi>\<^sub>P @ \<pi>, eP' \<ggreater>"
  and   "{$$} \<turnstile> e', eP', eV' : \<tau> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
         (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
proof (atomize_elim, insert assms, nominal_induct "{$$}::tyenv" e eP eV \<tau> avoiding: \<pi>\<^sub>A \<pi>' eV' rule: agree.strong_induct)
  case (a_App e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_App(5) show ?case
  proof (cases rule: s_App_inv)
    case (App1 eV\<^sub>1')
    with a_App(1,3) show ?thesis
      by (blast dest!: a_App(2))
  next
    case (App2 e\<^sub>2')
    with a_App(1,3) show ?thesis
      by (blast dest!: a_App(4))
  next
    case (AppLam x eV'')
    from a_App(1)[unfolded \<open>eV\<^sub>1 = Lam x eV''\<close>] show ?thesis
    proof (cases rule: a_Lam_inv_V[case_names Lam])
      case (Lam e'' eP'')
      with a_App(3) AppLam show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        from Lam a_App(3) AppLam show "{$$} \<turnstile> e''[e\<^sub>2 / x], eP''[eP\<^sub>2 / x], eV' : \<tau>\<^sub>2"
          by (auto intro: lemma4)
      qed (auto 0 3 simp: fresh_Pair intro!: s_AppLam[where \<pi>="[]"]
          intro: iffD1[OF smallstepP_ps_prepend[of "[]" _ "[]", simplified]])
    qed
  next
    case (AppRec x eV'')
    from a_App(1)[unfolded \<open>eV\<^sub>1 = Rec x eV''\<close>] show ?thesis
    proof (cases rule: a_Rec_inv_V[case_names _ Rec])
      case (Rec y e'''  eP''' eV''')
      with a_App(1,3) AppRec show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        let ?e = "App (Lam y e'''[Rec x (Lam y e''') / x]) e\<^sub>2"
        let ?eP = "App (Lam y eP'''[Rec x (Lam y eP''') / x]) eP\<^sub>2"
        from Rec a_App(3) AppRec show "{$$} \<turnstile> ?e, ?eP, eV' : \<tau>\<^sub>2"
          by (auto simp del: subst_term.simps(3) intro!: agree.a_App[where \<Gamma>="{$$}"] lemma4)
      qed (auto 0 3 simp del: subst_term.simps(3) simp: fresh_Pair intro!: s_AppRec[where \<pi>="[]"]
          intro: iffD1[OF smallstepP_ps_prepend[of "[]" _ "[]", simplified]])
    qed simp
  qed
next
  case (a_Let x e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  then have "atom x \<sharp> (eV\<^sub>1, \<pi>\<^sub>A)" by auto
  with a_Let(12) show ?case
  proof (cases rule: s_Let_inv)
    case Let1
    with a_Let(5,6,8,10) show ?thesis
    proof (intro conjI exI[of _ "[]"] exI disjI1)
      from Let1 a_Let(5,6,8,10) show "{$$} \<turnstile> e\<^sub>2[e\<^sub>1 / x], eP\<^sub>2[eP\<^sub>1 / x], eV' : \<tau>\<^sub>2"
        by (auto intro: lemma4)
    qed (auto 0 3 intro: iffD1[OF smallstepP_ps_prepend[of "[]" _ "[]", simplified]])
  next
    case (Let2 eV\<^sub>1')
    with a_Let(9)[of \<pi>\<^sub>A \<pi>' eV\<^sub>1'] obtain e\<^sub>1' \<pi> eP\<^sub>1' s s' where
      ih: "\<lless>[], e\<^sub>1\<ggreater> I\<rightarrow> \<lless>[], e\<^sub>1'\<ggreater>" "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<^sub>1\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP\<^sub>1'\<ggreater>"
        "{$$} \<turnstile> e\<^sub>1', eP\<^sub>1', eV\<^sub>1' : \<tau>\<^sub>1 \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
         closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s'"
      by blast
    with a_Let(5,6) have fresh: "atom x \<sharp> e\<^sub>1'" "atom x \<sharp> eP\<^sub>1'"
      using fresh_smallstep_I fresh_smallstep_P by blast+
    from ih a_Let(2,6) have "atom x \<sharp> \<pi>"
      using fresh_append fresh_ps_smallstep_P by blast
    with Let2 a_Let(1-8,10,12-) fresh ih show ?thesis
    proof (intro conjI exI[of _ "\<pi>"] exI)
      from \<open>atom x \<sharp> \<pi>\<close> Let2 a_Let(1-8,10,12-) fresh ih
      show "{$$} \<turnstile> Let e\<^sub>1' x e\<^sub>2, Let eP\<^sub>1' x eP\<^sub>2, eV' : \<tau>\<^sub>2 \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
        (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
        by auto
    qed (auto dest: spec[of _ "[]"] intro!: iffD1[OF smallstepP_ps_prepend, of "[]", simplified])
  qed
next
  case (a_Case e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau> e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_Case(7) show ?case
  proof (cases rule: s_Case_inv)
    case (Case eV'')
    from a_Case(2)[OF Case(2)] show ?thesis
    proof (elim exE disjE conjE, goal_cases ok collision)
      case (ok e'' \<pi> eP'')
      with Case a_Case(3,5) show ?case by blast
    next
      case (collision e'' \<pi> eP'' s s')
      with Case a_Case(3,5) show ?case
      proof (intro exI[of _ "[s]"] exI conjI disjI2)
        from Case a_Case(3,5) collision show "\<lless>[], Case e e\<^sub>1 e\<^sub>2\<ggreater> I\<rightarrow> \<lless>[], Case e'' e\<^sub>1 e\<^sub>2\<ggreater>"
          "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, Case eP eP\<^sub>1 eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ [s], Case eP'' eP\<^sub>1 eP\<^sub>2\<ggreater>"
          by auto
        from collision show "closed s" "closed s'" "s \<noteq> s'" "hash s = hash s'" by auto
      qed simp
    qed
  next
    case (Inj1 vV)
    from a_Case(1)[unfolded \<open>eV = Inj1 vV\<close>] show ?thesis
    proof (cases rule: a_Inj1_inv_V[consumes 1, case_names Inj])
      case (Inj v' vP')
      with Inj1 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        from a_Case(3) Inj Inj1 show "{$$} \<turnstile> App e\<^sub>1 v', App eP\<^sub>1 vP', eV' : \<tau>"
          by auto
      qed auto
    qed
  next
    case (Inj2 vV)
    from a_Case(1)[unfolded \<open>eV = Inj2 vV\<close>] show ?thesis
    proof (cases rule: a_Inj2_inv_V[consumes 1, case_names Inj])
      case (Inj v' vP')
      with Inj2 show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        from a_Case(5) Inj Inj2 show "{$$} \<turnstile> App e\<^sub>2 v', App eP\<^sub>2 vP', eV' : \<tau>"
          by auto
      qed auto
    qed
  qed
next
  case (a_Prj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Prj1(3) show ?case
  proof (cases rule: s_Prj1_inv)
    case (Prj1 eV'')
    then show ?thesis
      by (blast dest!: a_Prj1(2))
  next
    case (PrjPair1 v\<^sub>2)
    with a_Prj1(1) show ?thesis
    proof (cases rule: a_Prod_inv[consumes 1, case_names _ _ _ _ Pair])
      case (Pair e\<^sub>1 eP\<^sub>1 eV\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
      with PrjPair1 a_Prj1(1) show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        from Pair PrjPair1 a_Prj1(1) show "{$$} \<turnstile> e\<^sub>1, eP\<^sub>1, eV' : \<tau>\<^sub>1"
          by auto
      qed auto
    qed simp_all
  qed
next
  case (a_Prj2 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Prj2(3) show ?case
  proof (cases rule: s_Prj2_inv)
    case (Prj2 eV'')
    then show ?thesis
      by (blast dest!: a_Prj2(2))
  next
    case (PrjPair2 v\<^sub>2)
    with a_Prj2(1) show ?thesis
    proof (cases rule: a_Prod_inv[consumes 1, case_names _ _ _ _ Pair])
      case (Pair e\<^sub>1 eP\<^sub>1 eV\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
      with PrjPair2 a_Prj2(1) show ?thesis
      proof (intro conjI exI[of _ "[]"] exI disjI1)
        from Pair PrjPair2 a_Prj2(1) show "{$$} \<turnstile> e\<^sub>2, eP\<^sub>2, eV' : \<tau>\<^sub>2"
          by auto
      qed auto
    qed simp_all
  qed
next
  case (a_Roll \<alpha> e eP eV \<tau>)
  from a_Roll(7) show ?case
  proof (cases rule: s_Roll_inv)
    case (Roll eV'')
    from a_Roll(6)[OF Roll(2)] obtain e'' \<pi> eP'' where ih:
      "\<lless>[], e\<ggreater> I\<rightarrow> \<lless>[], e''\<ggreater>" "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP''\<ggreater>"
      "{$$} \<turnstile> e'', eP'', eV'' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
      (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
      by blast
    with Roll show ?thesis
    proof (intro exI[of _ "\<pi>"] exI conjI)
      from ih Roll show "{$$} \<turnstile> Roll e'', Roll eP'', eV' : Mu \<alpha> \<tau> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
        (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
        by auto
    qed auto
  qed
next
  case (a_Unroll \<alpha> e eP eV \<tau>)
  from a_Unroll(7) show ?case
  proof (cases rule: s_Unroll_inv)
    case (Unroll eV'')
    from a_Unroll(6)[OF Unroll(2)] obtain e'' \<pi> eP'' where ih:
      "\<lless>[], e\<ggreater> I\<rightarrow> \<lless>[], e''\<ggreater>" "\<forall>\<pi>\<^sub>P. \<lless>\<pi>\<^sub>P, eP\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>, eP''\<ggreater>"
      "{$$} \<turnstile> e'', eP'', eV'' : Mu \<alpha> \<tau> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
      (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
      by blast
    with Unroll show ?thesis
    proof (intro exI[of _ "\<pi>"] exI conjI)
      from ih Unroll show "{$$} \<turnstile> Unroll e'', Unroll eP'', eV' : subst_type \<tau> (Mu \<alpha> \<tau>) \<alpha> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<or>
        (\<exists>s s'. closed s \<and> closed s' \<and> \<pi> = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
        by auto
    qed auto
  next
    case UnrollRoll
    with a_Unroll(5) show ?thesis
      by fastforce
  qed
next
  case (a_Auth e eP eV \<tau>)
  from a_Auth(1) have [simp]: "atom x \<sharp> eP" for x :: var
    using agree_empty_fresh by simp
  from a_Auth(3) show ?case
  proof (cases rule: s_AuthV_inv)
    case (Auth eV'')
    from a_Auth(2)[OF Auth(2)] show ?thesis
    proof (elim exE disjE conjE, goal_cases ok collision)
      case (ok e'' \<pi> eP'')
      with Auth show ?case
      proof (intro conjI exI[of _ "\<pi>"] exI disjI1)
        from ok Auth show "{$$} \<turnstile> Auth e'', Auth eP'', eV' : AuthT \<tau>"
          by auto
      qed auto
    next
      case (collision e'' \<pi> eP'' s s')
      then show ?case by blast
    qed
  next
    case AuthV
    with a_Auth(1) show ?thesis
    proof (intro exI[of _ "[]"] exI conjI disjI1)
      from a_Auth(1) AuthV show "{$$} \<turnstile> e, Hashed (hash \<lparr>eP\<rparr>) eP, eV' : AuthT \<tau>"
        by (auto dest: lemma2_1)
    qed (auto simp: fresh_shallow)
  qed
next
  case (a_Unauth e eP eV \<tau>)
  from a_Unauth(3) show ?case
  proof (cases rule: s_UnauthV_inv)
    case (Unauth e')
    then show ?thesis
      by (blast dest!: a_Unauth(2))
  next
    case UnauthV
    from a_Unauth(1)[unfolded \<open>eV = Hash (hash eV')\<close>] UnauthV a_Unauth(1) show ?thesis
    proof (cases rule: a_AuthT_value_inv[consumes 1, case_names _ _ _ Hashed])
      case (Hashed vP')
      with UnauthV a_Unauth(1) show ?thesis
      proof (intro exI[of _ "[\<lparr>vP'\<rparr>]"] exI conjI)
        from Hashed UnauthV a_Unauth(1) show "{$$} \<turnstile> e, vP', eV' : \<tau> \<and> \<pi>\<^sub>A = [\<lparr>vP'\<rparr>] @ \<pi>' \<or>
          (\<exists>s s'. closed s \<and> closed s' \<and> [\<lparr>vP'\<rparr>] = [s] \<and> \<pi>\<^sub>A = [s'] @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s')"
          by (fastforce elim: a_HashI_inv[where \<Gamma>="{$$}"])
      qed auto
    qed auto
  qed
next
  case (a_Pair e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  from a_Pair(5) show ?case
  proof (cases rule: s_Pair_inv)
    case (Pair1 eV\<^sub>1')
    with a_Pair(3) show ?thesis
      using a_Pair(2)[of \<pi>\<^sub>A \<pi>' eV\<^sub>1'] by blast
  next
    case (Pair2 eV\<^sub>2')
    with a_Pair(1) show ?thesis
      using a_Pair(4)[of \<pi>\<^sub>A \<pi>' eV\<^sub>2'] by blast
  qed
next
  case (a_Inj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Inj1(3) show ?case
  proof (cases rule: s_Inj1_inv)
    case (Inj1 eV'')
    then show ?thesis
      using a_Inj1(2)[of \<pi>\<^sub>A \<pi>' eV''] by blast
  qed
next
  case (a_Inj2 e eP eV \<tau>\<^sub>2 \<tau>\<^sub>1)
  from a_Inj2(3) show ?case
  proof (cases rule: s_Inj2_inv)
    case (Inj2 eV'')
    with a_Inj2(1) show ?thesis
      using a_Inj2(2)[of \<pi>\<^sub>A \<pi>' eV''] by blast
  qed
qed (simp, meson value.intros value_no_step)+

subsection \<open>Theorem 1: Correctness\<close>

lemma theorem1_correctness:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> [], e \<ggreater> I\<rightarrow>i \<lless> [], e' \<ggreater>"
  obtains eP' eV' \<pi>
  where "\<lless> [], eP \<ggreater> P\<rightarrow>i \<lless> \<pi>, eP' \<ggreater>"
    "\<lless> \<pi>, eV \<ggreater> V\<rightarrow>i \<lless> [], eV' \<ggreater>"
    "{$$} \<turnstile> e', eP', eV' : \<tau>"
  using assms(2,1)
proof (atomize_elim, induct "[]::proofstream" e I i "[]::proofstream" e' rule: smallsteps.induct)
  case (s_Id e)
  then show ?case by auto
next
  case (s_Tr e\<^sub>1 i \<pi>\<^sub>2 e\<^sub>2 e\<^sub>3)
  then have "\<pi>\<^sub>2 = []" by (auto dest: smallstepI_ps_eq)
  with s_Tr obtain eP\<^sub>2 \<pi> eV\<^sub>2 where ih:
    "\<lless>[], eP\<ggreater> P\<rightarrow>i \<lless>\<pi>, eP\<^sub>2\<ggreater>" "\<lless>\<pi>, eV\<ggreater> V\<rightarrow>i \<lless>[], eV\<^sub>2\<ggreater>" "{$$} \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau>"
    by (atomize_elim, intro s_Tr(2)) auto
  moreover obtain eP\<^sub>3 eV\<^sub>3 \<pi>' where agree: "{$$} \<turnstile> e\<^sub>3, eP\<^sub>3, eV\<^sub>3 : \<tau>"
    and "\<lless>\<pi>\<^sub>P, eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>', eP\<^sub>3\<ggreater>" "\<lless>\<pi>' @ \<pi>'', eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>\<pi>'', eV\<^sub>3\<ggreater>"
  for \<pi>\<^sub>P \<pi>'' using lemma5[OF ih(3) s_Tr(3)[unfolded \<open>\<pi>\<^sub>2 = []\<close>], of thesis] by blast
  ultimately have "\<lless>[], eP\<ggreater> P\<rightarrow>i + 1 \<lless>\<pi> @ \<pi>', eP\<^sub>3\<ggreater>" "\<lless>\<pi> @ \<pi>', eV\<ggreater> V\<rightarrow>i + 1 \<lless>[], eV\<^sub>3\<ggreater>"
    by (auto simp: smallstepsV_ps_append[of _ _ _ "[]", simplified, symmetric]
       intro!: smallsteps.s_Tr[of "\<pi> @ \<pi>'"])
  with agree show ?case by blast
qed

subsection \<open>Counterexamples to Theorem 1: Security\<close>

text \<open>Counterexample using administrative normal form.\<close>

lemma security_false:
  assumes agree: "\<And>e eP eV \<tau> \<pi>A i \<pi>' eV'. \<lbrakk> {$$} \<turnstile> e, eP, eV : \<tau>; \<lless> \<pi>A, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>', eV' \<ggreater> \<rbrakk> \<Longrightarrow>
      \<exists>e' eP' \<pi> j \<pi>0 s s'. (\<lless> [], e \<ggreater> I\<rightarrow>i \<lless> [], e' \<ggreater> \<and> \<lless> [], eP \<ggreater> P\<rightarrow>i \<lless> \<pi>, eP' \<ggreater> \<and> (\<pi>A = \<pi> @ \<pi>') \<and> {$$} \<turnstile> e', eP', eV' : \<tau>) \<or>
       (j \<le> i \<and> \<lless> [], eP \<ggreater> P\<rightarrow>j \<lless> \<pi>0 @ [s], eP' \<ggreater> \<and> (\<pi>A = \<pi>0 @ [s'] @ \<pi>') \<and> s \<noteq> s' \<and> hash s = hash s')"
  and     collision: "hash (Inj1 Unit) = hash (Inj2 Unit)"
  and     no_collision_with_Unit: "\<And>t. hash Unit = hash t \<Longrightarrow> t = Unit"
  shows   False
proof -
  define i where "i = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))"
  obtain x y z :: var where fresh: "atom y \<sharp> x" "atom z \<sharp> (x, y)"
    by (metis obtain_fresh)
  define t where "t = Let (Let (Auth (Inj1 Unit)) y (Unauth (Var y))) x (Let (Let (Auth Unit) z (Unauth (Var z))) y (Var x))"
  note fresh_Cons[simp]
  have prover: "\<lless> [], t \<ggreater> P\<rightarrow>i \<lless> [Inj1 Unit, Unit], Inj1 Unit \<ggreater>" \<comment> \<open>prover execution\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
           apply (rule s_Let1[rotated])
            apply (rule s_Let1[rotated])
             apply (rule s_AuthP[rotated])
              apply simp
             apply simp
            apply simp
           apply simp
          apply (rule s_Let1[rotated])
           apply (rule s_Let2)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rule s_Let1[rotated])
          apply (rule s_UnauthP)
          apply simp
         apply simp
        apply simp
        apply (rule s_Let2)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let1[rotated])
        apply (rule s_Let1[rotated])
         apply (rule s_AuthP[rotated])
          apply simp
         apply simp
        apply simp
       apply simp
      apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
     apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthP)
      apply simp
     apply simp
    apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  have verifier1: "\<lless> [Inj1 Unit, Unit], t \<ggreater> V\<rightarrow>i \<lless> [], Inj1 Unit \<ggreater>" \<comment> \<open>verifier execution\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
           apply (rule s_Let1[rotated])
            apply (rule s_Let1[rotated])
             apply (rule s_AuthV[rotated])
              apply simp
             apply simp
            apply simp
           apply simp
          apply (rule s_Let1[rotated])
           apply (rule s_Let2)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rule s_Let1[rotated])
          apply (rule s_UnauthV)
           apply simp
          apply simp
         apply simp
        apply (rule s_Let2)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let1[rotated])
        apply (rule s_Let1[rotated])
         apply (rule s_AuthV[rotated])
          apply simp
         apply simp
        apply simp
       apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
     apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthV)
       apply simp
      apply simp
     apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  have verifier2: "\<lless> [Inj2 Unit, Unit], t \<ggreater> V\<rightarrow>i \<lless> [], Inj2 Unit \<ggreater>" \<comment> \<open>verifier execution with proofstream containing collision\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
           apply (rule s_Let1[rotated])
            apply (rule s_Let1[rotated])
             apply (rule s_AuthV[rotated])
              apply simp
             apply simp
            apply simp
           apply simp
          apply (rule s_Let1[rotated])
           apply (rule s_Let2)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rule s_Let1[rotated])
          apply (rule s_UnauthV)
           apply simp
          apply (simp add: collision)
         apply simp
        apply (rule s_Let2)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let1[rotated])
        apply (rule s_Let1[rotated])
         apply (rule s_AuthV[rotated])
          apply simp
         apply simp
        apply simp
       apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
     apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthV)
       apply simp
      apply simp
     apply simp
    apply (rule s_Let2[of Unit y _ "Inj2 Unit", simplified])
    apply simp
    done
  have judge: "{$$} \<turnstile> t : Sum One One"
    unfolding t_def using fresh
    by (force simp: fresh_Pair fresh_fmap_update)
  have ideal_deterministic: "e = Inj1 Unit" if "\<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], e\<ggreater>" for e
    apply (rule smallsteps_ideal_deterministic[OF that])
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
           apply (rule s_Let1[rotated])
            apply (rule s_Let1[rotated])
             apply (rule s_AuthI[rotated])
             apply simp
            apply simp
           apply simp
          apply (rule s_Let1[rotated])
           apply (rule s_Let2)
            apply simp
           apply simp
          apply simp
         apply simp
         apply (rule s_Let1[rotated])
          apply (rule s_UnauthI)
          apply simp
         apply simp
        apply (rule s_Let2)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let1[rotated])
        apply (rule s_Let1[rotated])
         apply (rule s_AuthI[rotated])
         apply simp
        apply simp
       apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
     apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthI)
      apply simp
     apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  from agree[OF judge_imp_agree[OF judge] verifier2] collision prover verifier1 show False
  proof safe
    fix e' eP'
    assume agree: "{$$} \<turnstile> e', eP', Inj2 Unit : Sum One One"
    assume assm: "\<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], e'\<ggreater>"
    then have "e' = Inj1 Unit"
      by (simp add: ideal_deterministic)
    with agree show False
      by auto
  qed (auto dest!: no_collision_with_Unit[OF sym])
qed

text \<open>Alternative, shorter counterexample not in administrative normal form.\<close>

lemma security_false_alt:
  assumes agree: "\<And>e eP eV \<tau> \<pi>A i \<pi>' eV'. \<lbrakk> {$$} \<turnstile> e, eP, eV : \<tau>; \<lless> \<pi>A, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>', eV' \<ggreater> \<rbrakk> \<Longrightarrow>
      \<exists>e' eP' \<pi> j \<pi>0 s s'. (\<lless> [], e \<ggreater> I\<rightarrow>i \<lless> [], e' \<ggreater> \<and> \<lless> [], eP \<ggreater> P\<rightarrow>i \<lless> \<pi>, eP' \<ggreater> \<and> (\<pi>A = \<pi> @ \<pi>') \<and> {$$} \<turnstile> e', eP', eV' : \<tau>) \<or>
       (j \<le> i \<and> \<lless> [], eP \<ggreater> P\<rightarrow>j \<lless> \<pi>0 @ [s], eP' \<ggreater> \<and> (\<pi>A = \<pi>0 @ [s'] @ \<pi>') \<and> s \<noteq> s' \<and> hash s = hash s')"
  and     collision: "hash (Inj1 Unit) = hash (Inj2 Unit)"
  and     no_collision_with_Unit: "\<And>t. hash Unit = hash t \<Longrightarrow> t = Unit"
  shows   False
proof -
  define i where "i = Suc (Suc (Suc (Suc (Suc (Suc 0)))))"
  obtain x y z :: var where fresh: "atom y \<sharp> x" "atom z \<sharp> (x, y)"
    by (metis obtain_fresh)
  define t where "t = Let (Unauth (Auth (Inj1 Unit))) x (Let (Unauth (Auth Unit)) y (Var x))"
  note fresh_Cons[simp]
  have prover: "\<lless> [], t \<ggreater> P\<rightarrow>i \<lless> [Inj1 Unit, Unit], Inj1 Unit \<ggreater>" \<comment> \<open>prover execution\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
         apply (rule s_Let1[rotated])
          apply (rule s_Unauth)
          apply (rule s_AuthP[rotated])
           apply simp
          apply simp
         apply simp
        apply simp
        apply (rule s_Let1[rotated])
         apply (rule s_UnauthP)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Unauth)
       apply (rule s_AuthP[rotated])
        apply simp
       apply simp
      apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthP)
      apply simp
     apply simp
    apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  have verifier1: "\<lless> [Inj1 Unit, Unit], t \<ggreater> V\<rightarrow>i \<lless> [], Inj1 Unit \<ggreater>" \<comment> \<open>verifier execution\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
         apply (rule s_Let1[rotated])
          apply (rule s_Unauth)
          apply (rule s_AuthV[rotated])
           apply simp
          apply simp
         apply simp
        apply (rule s_Let1[rotated])
         apply (rule s_UnauthV)
         apply simp
        apply simp
       apply simp
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Unauth)
       apply (rule s_AuthV[rotated])
        apply simp
       apply simp
      apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthV)
      apply simp
     apply simp
    apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  have verifier2: "\<lless> [Inj2 Unit, Unit], t \<ggreater> V\<rightarrow>i \<lless> [], Inj2 Unit \<ggreater>" \<comment> \<open>verifier execution with proofstream containing collision\<close>
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
         apply (rule s_Let1[rotated])
          apply (rule s_Unauth)
          apply (rule s_AuthV[rotated])
           apply simp
          apply simp
         apply simp
        apply (rule s_Let1[rotated])
         apply (rule s_UnauthV)
          apply simp
         apply (simp add: collision)
        apply simp
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Unauth)
       apply (rule s_AuthV[rotated])
        apply simp
       apply simp
      apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthV)
      apply simp
     apply simp
    apply simp
    apply (rule s_Let2[of Unit y _ "Inj2 Unit", simplified])
    apply simp
    done
  have judge: "{$$} \<turnstile> t : Sum One One"
    unfolding t_def using fresh
    by (force simp: fresh_Pair fresh_fmap_update)
  have ideal_deterministic: "e = Inj1 Unit" if "\<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], e\<ggreater>" for e
    apply (rule smallsteps_ideal_deterministic[OF that])
    unfolding i_def t_def Suc_eq_plus1 using fresh
    apply -
    apply (rule smallsteps.intros)+
         apply (rule s_Let1[rotated])
          apply (rule s_Unauth)
          apply (rule s_AuthI[rotated])
          apply simp
         apply simp
        apply (rule s_Let1[rotated])
         apply (rule s_UnauthI)
         apply simp
        apply simp
       apply (rule s_Let2)
        apply simp
       apply simp
      apply simp
      apply (rule s_Let1[rotated])
       apply (rule s_Unauth)
       apply (rule s_AuthI[rotated])
       apply simp
      apply simp
     apply (rule s_Let1[rotated])
      apply (rule s_UnauthI)
      apply simp
     apply simp
    apply (rule s_Let2[of Unit y _ "Inj1 Unit", simplified])
    apply simp
    done
  from agree[OF judge_imp_agree[OF judge] verifier2] collision prover verifier1 show False
  proof safe
    fix e' eP'
    assume agree: "{$$} \<turnstile> e', eP', Inj2 Unit : Sum One One"
    assume assm: "\<lless>[], t\<ggreater> I\<rightarrow>i \<lless>[], e'\<ggreater>"
    then have "e' = Inj1 Unit"
      by (simp add: ideal_deterministic)
    with agree show False
      by auto
  qed (auto dest!: no_collision_with_Unit[OF sym])
qed

subsection \<open>Corrected Theorem 1: Security\<close>

lemma theorem1_security:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> \<pi>\<^sub>A, eV \<ggreater> V\<rightarrow>i \<lless> \<pi>', eV' \<ggreater>"
shows "(\<exists>e' eP' \<pi>. \<lless> [], e \<ggreater> I\<rightarrow>i \<lless> [], e' \<ggreater> \<and> \<lless> [], eP \<ggreater> P\<rightarrow>i \<lless> \<pi>, eP' \<ggreater> \<and> \<pi>\<^sub>A = \<pi> @ \<pi>' \<and> {$$} \<turnstile> e', eP', eV' : \<tau>) \<or>
       (\<exists>eP' j \<pi>\<^sub>0 \<pi>\<^sub>0' s s'. j \<le> i \<and> \<lless> [], eP \<ggreater> P\<rightarrow>j \<lless> \<pi>\<^sub>0 @ [s], eP' \<ggreater> \<and> \<pi>\<^sub>A = \<pi>\<^sub>0 @ [s'] @ \<pi>\<^sub>0' @ \<pi>' \<and> s \<noteq> s' \<and> hash s = hash s' \<and> closed s \<and> closed s')"
using assms(2,1) proof (induct \<pi>\<^sub>A eV V i \<pi>' eV' rule: smallsteps.induct)
  case (s_Id \<pi> e)
  then show ?case by blast
next
  case (s_Tr \<pi>\<^sub>1 eV\<^sub>1 i \<pi>\<^sub>2 eV\<^sub>2 \<pi>\<^sub>3 eV\<^sub>3)
  then obtain e\<^sub>2 \<pi> eP\<^sub>2 j \<pi>\<^sub>0 \<pi>\<^sub>0' s s'
    where "\<lless>[], e\<ggreater> I\<rightarrow>i \<lless>[], e\<^sub>2\<ggreater> \<and> \<lless>[], eP\<ggreater> P\<rightarrow>i \<lless>\<pi>, eP\<^sub>2\<ggreater> \<and> \<pi>\<^sub>1 = \<pi> @ \<pi>\<^sub>2 \<and> {$$} \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau> \<or>
            j \<le> i \<and> \<lless>[], eP\<ggreater> P\<rightarrow>j \<lless>\<pi>\<^sub>0 @ [s], eP\<^sub>2\<ggreater> \<and> closed s \<and> closed s' \<and> \<pi>\<^sub>1 = \<pi>\<^sub>0 @ [s'] @ \<pi>\<^sub>0' @ \<pi>\<^sub>2 \<and> s \<noteq> s' \<and> hash s = hash s'"
    by blast
  then show ?case
  proof (elim disjE conjE, goal_cases ok collision)
    case ok
    obtain e\<^sub>3 eP\<^sub>3 \<pi>' where
      "\<lless>[], e\<^sub>2\<ggreater> I\<rightarrow> \<lless>[], e\<^sub>3\<ggreater>" "\<lless>\<pi>\<^sub>P, eP\<^sub>2\<ggreater> P\<rightarrow> \<lless>\<pi>\<^sub>P @ \<pi>', eP\<^sub>3\<ggreater>"
      "{$$} \<turnstile> e\<^sub>3, eP\<^sub>3, eV\<^sub>3 : \<tau> \<and> \<pi>\<^sub>2 = \<pi>' @ \<pi>\<^sub>3 \<or>
      (\<exists>s s'. closed s \<and> closed s' \<and> \<pi>' = [s] \<and> \<pi>\<^sub>2 = [s'] @ \<pi>\<^sub>3 \<and> s \<noteq> s' \<and> hash s = hash s')"
    for \<pi>\<^sub>P using lemma6[OF ok(4) s_Tr(3), of thesis] by blast
    then show ?case
    proof (elim disjE conjE exE, goal_cases ok2 collision)
      case ok2
      with s_Tr(1,3-) ok show ?case
        by auto
    next
      case (collision s s')
      then show ?case
      proof (intro disjI2 exI conjI)
        from ok collision show "\<lless>[], eP\<ggreater> P\<rightarrow>i + 1 \<lless>\<pi> @ [s], eP\<^sub>3\<ggreater>"
          by (elim smallsteps.s_Tr) auto
        from ok collision show "\<pi>\<^sub>1 = \<pi> @ [s'] @ [] @ \<pi>\<^sub>3"
          by simp
      qed simp_all
    qed
  next
    case collision
    from s_Tr(3) collision show ?case
    proof (elim smallstepV_consumes_proofstream, intro disjI2 exI conjI)
      fix \<pi>\<^sub>0''
      assume *: "\<pi>\<^sub>2 = \<pi>\<^sub>0'' @ \<pi>\<^sub>3"
      from collision * show "\<pi>\<^sub>1 = \<pi>\<^sub>0 @ [s'] @ (\<pi>\<^sub>0' @ \<pi>\<^sub>0'') @ \<pi>\<^sub>3"
        by simp
    qed simp_all
  qed
qed

subsection \<open>Remark 1\<close>

lemma remark1_single:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> \<pi>P, eP \<ggreater> P\<rightarrow> \<lless> \<pi>P @ \<pi>, eP' \<ggreater>"
  obtains e' eV' where "{$$} \<turnstile> e', eP', eV' : \<tau> \<and> \<lless> [], e \<ggreater> I\<rightarrow> \<lless> [], e' \<ggreater> \<and> \<lless> \<pi>, eV \<ggreater> V\<rightarrow> \<lless> [], eV' \<ggreater>"
proof (atomize_elim, insert assms, nominal_induct "{$$}::tyenv" e eP eV \<tau> avoiding: \<pi>P \<pi> eP' rule: agree.strong_induct)
  case (a_App e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_App(5) show ?case
  proof (cases rule: s_App_inv)
    case (App1 eP\<^sub>1')
    with a_App(2,3) show ?thesis by blast
  next
    case (App2 eP\<^sub>2')
    with a_App(1,4) show ?thesis by blast
  next
    case (AppLam x eP)
    from a_App(1)[unfolded \<open>eP\<^sub>1 = Lam x eP\<close>] show ?thesis
    proof (cases rule: a_Lam_inv_P[case_names Lam])
      case (Lam v' vV')
      with a_App(3) AppLam show ?thesis
        by (auto 0 4 simp: fresh_Pair del: s_AppLam intro!: s_AppLam lemma4)
    qed
  next
    case (AppRec x e)
    from a_App(1)[unfolded \<open>eP\<^sub>1 = Rec x e\<close>] show ?thesis
    proof (cases rule: a_Rec_inv_P[case_names _ Rec])
      case (Rec y e'' eP'' eV'')
      show ?thesis
      proof (intro exI conjI)
        let ?e = "App (Lam y (e''[Rec x (Lam y e'') / x])) e\<^sub>2"
        let ?eV = "App (Lam y (eV''[Rec x (Lam y eV'') / x])) eV\<^sub>2"
        from a_App(3) Rec AppRec show "{$$} \<turnstile> ?e, eP', ?eV : \<tau>\<^sub>2"
          by (auto intro!: agree.a_App[where \<Gamma>="{$$}"] lemma4
            simp del: subst_term.simps(3) simp: subst_term.simps(3)[symmetric])
        from a_App(3) Rec AppRec show "\<lless>[], App e\<^sub>1 e\<^sub>2\<ggreater> I\<rightarrow> \<lless>[], ?e\<ggreater>"
          by (auto intro!: s_AppRec[where v=e\<^sub>2]
            simp del: subst_term.simps(3) simp: subst_term.simps(3)[symmetric] fresh_Pair)
        from a_App(3) Rec AppRec show "\<lless>\<pi>, App eV\<^sub>1 eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>[], ?eV\<ggreater>"
          by (auto intro!: s_AppRec[where v=eV\<^sub>2]
            simp del: subst_term.simps(3) simp: subst_term.simps(3)[symmetric] fresh_Pair)
      qed
    qed simp
  qed
next
  case (a_Let x e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  then have "atom x \<sharp> (eP\<^sub>1, \<pi>P)" by auto
  with a_Let(12) show ?case
  proof (cases rule: s_Let_inv)
    case Let1
    with a_Let show ?thesis
      by (intro exI[where P = "\<lambda>x. \<exists>y. (Q x y)" for Q, OF exI, of _ "e\<^sub>2[e\<^sub>1 / x]" "eV\<^sub>2[eV\<^sub>1 / x]"])
        (auto intro!: lemma4)
  next
    case (Let2 eP\<^sub>1')
    with a_Let(9) obtain e\<^sub>1' eV\<^sub>1'
      where ih: "{$$} \<turnstile> e\<^sub>1', eP\<^sub>1', eV\<^sub>1' : \<tau>\<^sub>1" "\<lless>[], e\<^sub>1\<ggreater> I\<rightarrow> \<lless>[], e\<^sub>1'\<ggreater>" "\<lless>\<pi>, eV\<^sub>1\<ggreater> V\<rightarrow> \<lless>[], eV\<^sub>1'\<ggreater>"
      by blast
    from a_Let Let2 have "\<not> value e\<^sub>1" "\<not> value eP\<^sub>1" "\<not> value eV\<^sub>1" by auto
    with Let2 a_Let(2,5,7,10) ih show ?thesis
      by (intro exI[where P = "\<lambda>x. \<exists>y. (Q x y)" for Q, OF exI, of _ "Let e\<^sub>1' x e\<^sub>2" "Let eV\<^sub>1' x eV\<^sub>2"])
       (fastforce simp: fresh_Pair del: agree.a_Let intro!: agree.a_Let)
  qed
next
  case (a_Case e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2 e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau> e\<^sub>2 eP\<^sub>2 eV\<^sub>2)
  from a_Case(7) show ?case
  proof (cases rule: s_Case_inv)
    case (Case eP'')
    with a_Case(2,3,5) show ?thesis by blast
  next
    case (Inj1 v)
    with a_Case(1,3,5) show ?thesis by blast
  next
    case (Inj2 v)
    with a_Case(1,3,5) show ?thesis by blast
  qed
next
  case (a_Prj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2 \<pi>P \<pi> eP')
  from a_Prj1(3) show ?case
  proof (cases rule: s_Prj1_inv)
    case (Prj1 eP'')
    with a_Prj1(2) show ?thesis by blast
  next
    case (PrjPair1 v\<^sub>2)
    with a_Prj1(1) show ?thesis by fastforce
  qed
next
  case (a_Prj2 v vP vV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Prj2(3) show ?case
  proof (cases rule: s_Prj2_inv)
    case (Prj2 eP'')
    with a_Prj2(2) show ?thesis by blast
  next
    case (PrjPair2 v\<^sub>2)
    with a_Prj2(1) show ?thesis by fastforce
  qed
next
  case (a_Roll \<alpha> e eP eV \<tau>)
  from a_Roll(7) show ?case
  proof (cases rule: s_Roll_inv)
    case (Roll eP'')
    with a_Roll(4,5,6) show ?thesis by blast
  qed
next
  case (a_Unroll \<alpha> e eP eV \<tau>)
  from a_Unroll(7) show ?case
  proof (cases rule: s_Unroll_inv)
    case (Unroll eP'')
    with a_Unroll(5,6) show ?thesis by fastforce
  next
    case UnrollRoll
    with a_Unroll(5) show ?thesis by blast
  qed
next
  case (a_Auth e eP eV \<tau>)
  from a_Auth(3) show ?case
  proof (cases rule: s_AuthP_inv)
    case (Auth eP'')
    with a_Auth(3) show ?thesis
      by (auto dest!: a_Auth(2)[of \<pi>P \<pi> eP''])
  next
    case AuthP
    with a_Auth(1) show ?thesis
      by (auto 0 4 simp: lemma2_1 intro: exI[of _ "Hash (hash \<lparr>eP\<rparr>)"] exI[of _ e])
  qed
next
  case (a_Unauth e eP eV \<tau>)
  from a_Unauth(1) have eP_closed: "closed eP"
    using agree_empty_fresh by simp
  from a_Unauth(3) show ?case
  proof (cases rule: s_UnauthP_inv)
    case (Unauth e')
    with a_Unauth(2) show ?thesis
      by blast
  next
    case (UnauthP h)
    with a_Unauth(1,3) eP_closed show ?thesis
      by (force intro: a_AuthT_value_inv[OF a_Unauth(1)] simp: fresh_shallow)
  qed
next
  case (a_Inj1 e eP eV \<tau>\<^sub>1 \<tau>\<^sub>2)
  from a_Inj1(3) show ?case
  proof (cases rule: s_Inj1_inv)
    case (Inj1 eP'')
    with a_Inj1(1,2) show ?thesis by blast
  qed
next
  case (a_Inj2 e eP eV \<tau>\<^sub>2 \<tau>\<^sub>1)
  from a_Inj2(3) show ?case
  proof (cases rule: s_Inj2_inv)
    case (Inj2 eP'')
    with a_Inj2(1,2) show ?thesis by blast
  qed
next
  case (a_Pair e\<^sub>1 eP\<^sub>1 eV\<^sub>1 \<tau>\<^sub>1 e\<^sub>2 eP\<^sub>2 eV\<^sub>2 \<tau>\<^sub>2)
  from a_Pair(5) show ?case
  proof (cases rule: s_Pair_inv)
    case (Pair1 eP\<^sub>1')
    with a_Pair(1,2,3) show ?thesis by blast
  next
    case (Pair2 eP\<^sub>2')
    with a_Pair(1,3,4) show ?thesis by blast
  qed
qed (auto dest: value_no_step)

lemma remark1:
  assumes "{$$} \<turnstile> e, eP, eV : \<tau>"
  and     "\<lless> \<pi>\<^sub>P, eP \<ggreater> P\<rightarrow>i \<lless> \<pi>\<^sub>P @ \<pi>, eP' \<ggreater>"
  obtains e' eV'
  where "{$$} \<turnstile> e', eP', eV' : \<tau>" "\<lless> [], e \<ggreater> I\<rightarrow>i \<lless> [], e' \<ggreater>" "\<lless> \<pi>, eV \<ggreater> V\<rightarrow>i \<lless> [], eV' \<ggreater>"
  using assms(2,1)
proof (atomize_elim, nominal_induct \<pi>\<^sub>P eP P i "\<pi>\<^sub>P @ \<pi>" eP' arbitrary: \<pi> rule: smallsteps.strong_induct)
  case (s_Id e \<pi>P)
  then show ?case
    using s_Id_inv by blast
next
  case (s_Tr \<pi>\<^sub>1 eP\<^sub>1 i \<pi>\<^sub>2 eP\<^sub>2 eP\<^sub>3)
  from s_Tr obtain \<pi>' \<pi>'' where ps: "\<pi>\<^sub>2 = \<pi>\<^sub>1 @ \<pi>'" "\<pi> = \<pi>' @ \<pi>''"
    by (force elim: smallstepP_generates_proofstream smallstepsP_generates_proofstream)
  with s_Tr obtain e\<^sub>2 eV\<^sub>2 where ih: "{$$} \<turnstile> e\<^sub>2, eP\<^sub>2, eV\<^sub>2 : \<tau>"
    "\<lless>[], e\<ggreater> I\<rightarrow>i \<lless>[], e\<^sub>2\<ggreater>" "\<lless>\<pi>', eV\<ggreater> V\<rightarrow>i \<lless>[], eV\<^sub>2\<ggreater>"
    by atomize_elim (auto elim: s_Tr(2)[of \<pi>'])
  moreover
  obtain e\<^sub>3 eV\<^sub>3 where agree: "{$$} \<turnstile> e\<^sub>3, eP\<^sub>3, eV\<^sub>3 : \<tau>" and
    "\<lless>[], e\<^sub>2\<ggreater> I\<rightarrow> \<lless>[], e\<^sub>3\<ggreater>" "\<lless>\<pi>'', eV\<^sub>2\<ggreater> V\<rightarrow> \<lless>[], eV\<^sub>3\<ggreater>"
    by (rule remark1_single[OF ih(1) iffD2[OF smallstepP_ps_prepend s_Tr(3)[unfolded ps]]]) blast
  ultimately have "\<lless>[], e\<ggreater> I\<rightarrow>i + 1 \<lless>[], e\<^sub>3\<ggreater>" "\<lless>\<pi>, eV\<ggreater> V\<rightarrow>i + 1 \<lless>[], eV\<^sub>3\<ggreater>"
    by (auto simp: smallstepsV_ps_append[of _ _ _ "[]", simplified, symmetric] ps
       intro!: smallsteps.s_Tr[where m=V and \<pi>\<^sub>1="\<pi>' @ \<pi>''" and \<pi>\<^sub>2=\<pi>''])
  with agree show ?case
    by blast
qed

(*<*)
end
(*>*)