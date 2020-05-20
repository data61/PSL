theory Converter_Rewrite imports
  Converter
begin

section \<open>Equivalence of converters restricted by interfaces\<close>

coinductive eq_resource_on :: "'a set \<Rightarrow> ('a, 'b) resource \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool" ("_ \<turnstile>\<^sub>R/ _ \<sim>/ _" [100, 99, 99] 99)
  for A where
    eq_resource_onI: "A \<turnstile>\<^sub>R res \<sim> res'" if
    "\<And>a. a \<in> A \<Longrightarrow> rel_spmf (rel_prod (=) (eq_resource_on A)) (run_resource res a) (run_resource res' a)"

lemma eq_resource_on_coinduct [consumes 1, case_names eq_resource_on, coinduct pred: eq_resource_on]:
  assumes "X res res'"
    and "\<And>res res' a. \<lbrakk> X res res'; a \<in> A \<rbrakk>
      \<Longrightarrow> rel_spmf (rel_prod (=) (\<lambda>res res'. X res res' \<or> A \<turnstile>\<^sub>R res \<sim> res')) (run_resource res a) (run_resource res' a)"
  shows "A \<turnstile>\<^sub>R res \<sim> res'"
  using assms(1) by(rule eq_resource_on.coinduct)(auto dest: assms(2))

lemma eq_resource_onD:
  assumes "A \<turnstile>\<^sub>R res \<sim> res'" "a \<in> A"
  shows "rel_spmf (rel_prod (=) (eq_resource_on A)) (run_resource res a) (run_resource res' a)"
  using assms by(auto elim: eq_resource_on.cases)

lemma eq_resource_on_refl [simp]: "A \<turnstile>\<^sub>R res \<sim> res"
  by(coinduction arbitrary: res)(auto intro: rel_spmf_reflI)

lemma eq_resource_on_reflI: "res = res' \<Longrightarrow> A \<turnstile>\<^sub>R res \<sim> res'"
  by(simp add: eq_resource_on_refl)

lemma eq_resource_on_sym: "A \<turnstile>\<^sub>R res \<sim> res'" if "A \<turnstile>\<^sub>R res' \<sim> res"
  using that
  by(coinduction arbitrary: res res')
    (drule (1) eq_resource_onD, rewrite in "\<hole>" conversep_iff[symmetric]
      , auto simp add: spmf_rel_conversep[symmetric] elim!: rel_spmf_mono)

lemma eq_resource_on_trans [trans]: "A \<turnstile>\<^sub>R res \<sim> res''" if "A \<turnstile>\<^sub>R res \<sim> res'" "A \<turnstile>\<^sub>R res' \<sim> res''"
  using that by(coinduction arbitrary: res res' res'')
    ((drule (1) eq_resource_onD)+, drule (1) rel_spmf_OO_trans, auto elim!:rel_spmf_mono) 

lemma eq_resource_on_UNIV_D [simp]: "res = res'" if "UNIV \<turnstile>\<^sub>R res \<sim> res'"
  using that by(coinduction arbitrary: res res')(auto dest: eq_resource_onD)

lemma eq_resource_on_UNIV_iff: "UNIV \<turnstile>\<^sub>R res \<sim> res' \<longleftrightarrow> res = res'"
  by(auto dest: eq_resource_on_UNIV_D)

lemma eq_resource_on_mono: "\<lbrakk> A' \<turnstile>\<^sub>R res \<sim> res'; A \<subseteq> A' \<rbrakk> \<Longrightarrow> A \<turnstile>\<^sub>R res \<sim> res'"
  by(coinduction arbitrary: res res')(auto dest: eq_resource_onD elim!: rel_spmf_mono)

lemma eq_resource_on_empty [simp]: "{} \<turnstile>\<^sub>R res \<sim> res'"
  by(rule eq_resource_onI; simp)

lemma eq_resource_on_resource_of_oracleI:
  includes lifting_syntax 
  fixes S
  assumes sim: "(S ===> eq_on A ===> rel_spmf (rel_prod (=) S)) r1 r2"
    and S: "S s1 s2"
  shows "A \<turnstile>\<^sub>R resource_of_oracle r1 s1 \<sim> resource_of_oracle r2 s2"
  using S  by(coinduction arbitrary: s1 s2)
    (drule sim[THEN rel_funD, THEN rel_funD], simp add: eq_on_def
      , fastforce simp add: eq_on_def spmf_rel_map elim: rel_spmf_mono)

lemma exec_gpv_eq_resource_on:
  assumes "outs_\<I> \<I> \<turnstile>\<^sub>R res \<sim> res'"
    and "\<I> \<turnstile>g gpv \<surd>"
    and "\<I> \<turnstile>res res \<surd>"
  shows "rel_spmf (rel_prod (=) (eq_resource_on (outs_\<I> \<I>))) (exec_gpv run_resource gpv res) (exec_gpv run_resource gpv res')"
  using assms
proof(induction arbitrary: res res' gpv rule: exec_gpv_fixp_induct)
  case (step exec_gpv')
  have[simp]: "\<lbrakk>(s, r1) \<in> set_spmf (run_resource res g1); (s, r2) \<in> set_spmf (run_resource res' g1);
    IO g1 g2 \<in> set_spmf (the_gpv gpv); outs_\<I> \<I> \<turnstile>\<^sub>R r1 \<sim> r2\<rbrakk> \<Longrightarrow> rel_spmf (rel_prod (=) (eq_resource_on (outs_\<I> \<I>))) 
        (exec_gpv' (g2 s) r1) (exec_gpv' (g2 s) r2)" for g1 g2 r1 s r2
    by(rule step.IH, simp, rule WT_gpv_ContD[OF step.prems(2)], assumption)
      (auto elim: outs_gpv.IO WT_calleeD[OF run_resource.WT_callee, OF step.prems(3)]
        dest!: WT_resourceD[OF step.prems(3), rotated 1] intro: WT_gpv_outs_gpv[THEN subsetD, OF step.prems(2)])

  show ?case
    by(clarsimp intro!: rel_spmf_bind_reflI step.prems split!: generat.split)
      (rule rel_spmf_bindI', rule eq_resource_onD[OF step.prems(1)]
        , auto elim: outs_gpv.IO intro:  eq_resource_onD[OF step.prems(1)] WT_gpv_outs_gpv[THEN subsetD, OF step.prems(2)])
qed simp_all

inductive eq_\<I>_generat :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'out, 'in \<Rightarrow> 'c) generat \<Rightarrow> ('b, 'out, 'in \<Rightarrow> 'd) generat \<Rightarrow> bool"
  for A \<I> D where
    Pure: "eq_\<I>_generat A \<I> D (Pure x) (Pure y)" if "A x y"
  | IO: "eq_\<I>_generat A \<I> D (IO out c) (IO out c')" if "out \<in> outs_\<I> \<I>" "\<And>input. input \<in> responses_\<I> \<I> out \<Longrightarrow> D (c input) (c' input)"

hide_fact (open) Pure IO

inductive_simps eq_\<I>_generat_simps [simp, code]:
  "eq_\<I>_generat A \<I> D (Pure x) (Pure y)"
  "eq_\<I>_generat A \<I> D (IO out c) (Pure y)"
  "eq_\<I>_generat A \<I> D (Pure x) (IO out' c')"
  "eq_\<I>_generat A \<I> D (IO out c) (IO out' c')"

inductive_simps eq_\<I>_generat_iff1:
  "eq_\<I>_generat A \<I> D (Pure x) g'"
  "eq_\<I>_generat A \<I> D (IO out c) g'"

inductive_simps eq_\<I>_generat_iff2:
  "eq_\<I>_generat A \<I> D g (Pure x)"
  "eq_\<I>_generat A \<I> D g (IO out c)"

lemma eq_\<I>_generat_mono':
  "\<lbrakk> eq_\<I>_generat A \<I> D x y; \<And>x y. A x y \<Longrightarrow> A' x y; \<And>x y. D x y \<Longrightarrow> D' x y; \<I> \<le> \<I>' \<rbrakk>
  \<Longrightarrow> eq_\<I>_generat A' \<I>' D' x y"
  by(auto 4 4 elim!: eq_\<I>_generat.cases simp add: le_\<I>_def)

lemma eq_\<I>_generat_mono: "eq_\<I>_generat A \<I> D \<le> eq_\<I>_generat A' \<I>' D'" if "A \<le> A'" "D \<le> D'" "\<I> \<le> \<I>'"
  using that by(auto elim!: eq_\<I>_generat_mono' dest: predicate2D)

lemma eq_\<I>_generat_mono'' [mono]:
  "\<lbrakk> \<And>x y. A x y \<longrightarrow> A' x y; \<And>x y. D x y \<longrightarrow> D' x y \<rbrakk>
  \<Longrightarrow> eq_\<I>_generat A \<I> D x y \<longrightarrow> eq_\<I>_generat A' \<I> D' x y"
  by(auto elim: eq_\<I>_generat_mono')

lemma eq_\<I>_generat_conversep: "eq_\<I>_generat A\<inverse>\<inverse> \<I> D\<inverse>\<inverse> = (eq_\<I>_generat A \<I> D)\<inverse>\<inverse>"
  by(fastforce elim: eq_\<I>_generat.cases)

lemma eq_\<I>_generat_reflI:
  assumes  "\<And>x. x \<in> generat_pures generat \<Longrightarrow> A x x"
    and "\<And>out c. generat = IO out c \<Longrightarrow> out \<in> outs_\<I> \<I> \<and> (\<forall>input\<in>responses_\<I> \<I> out. D (c input) (c input))"
  shows "eq_\<I>_generat A \<I> D generat generat"
  using assms by(cases generat) auto

lemma eq_\<I>_generat_relcompp:
  "eq_\<I>_generat A \<I> D OO eq_\<I>_generat A' \<I> D' = eq_\<I>_generat (A OO A') \<I> (D OO D')"
  by(auto 4 3 intro!: ext elim!: eq_\<I>_generat.cases simp add: eq_\<I>_generat_iff1 eq_\<I>_generat_iff2 relcompp.simps) metis

lemma eq_\<I>_generat_map1:
  "eq_\<I>_generat A \<I> D (map_generat f id ((\<circ>) g) generat) generat' \<longleftrightarrow>
   eq_\<I>_generat (\<lambda>x. A (f x)) \<I> (\<lambda>x. D (g x)) generat generat'"
  by(cases generat; cases generat') auto

lemma eq_\<I>_generat_map2:
  "eq_\<I>_generat A \<I> D generat (map_generat f id ((\<circ>) g) generat') \<longleftrightarrow>
   eq_\<I>_generat (\<lambda>x y. A x (f y)) \<I> (\<lambda>x y. D x (g y)) generat generat'"
  by(cases generat; cases generat') auto

lemmas eq_\<I>_generat_map [simp] = 
  eq_\<I>_generat_map1[abs_def] eq_\<I>_generat_map2
  eq_\<I>_generat_map1[where g=id, unfolded fun.map_id0, abs_def] eq_\<I>_generat_map2[where g=id, unfolded fun.map_id0]

lemma eq_\<I>_generat_into_rel_generat:
  "eq_\<I>_generat A \<I>_full D generat generat' \<Longrightarrow> rel_generat A (=) (rel_fun (=) D) generat generat'"
  by(erule eq_\<I>_generat.cases) auto

coinductive eq_\<I>_gpv :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('a, 'out, 'in) gpv \<Rightarrow> ('b, 'out, 'in) gpv \<Rightarrow> bool"
  for A \<I> where
    eq_\<I>_gpvI: "eq_\<I>_gpv A \<I> gpv gpv'" 
  if "rel_spmf (eq_\<I>_generat A \<I> (eq_\<I>_gpv A \<I>)) (the_gpv gpv) (the_gpv gpv')"

lemma eq_\<I>_gpv_coinduct [consumes 1, case_names eq_\<I>_gpv, coinduct pred: eq_\<I>_gpv]:
  assumes "X gpv gpv'"
    and "\<And>gpv gpv'. X gpv gpv'
      \<Longrightarrow> rel_spmf (eq_\<I>_generat A \<I> (\<lambda>gpv gpv'. X gpv gpv' \<or> eq_\<I>_gpv A \<I> gpv gpv')) (the_gpv gpv) (the_gpv gpv')"
  shows "eq_\<I>_gpv A \<I> gpv gpv'"
  using assms(1) by(rule eq_\<I>_gpv.coinduct)(blast dest: assms(2))

lemma eq_\<I>_gpvD:
  "eq_\<I>_gpv A \<I> gpv gpv' \<Longrightarrow> rel_spmf (eq_\<I>_generat A \<I> (eq_\<I>_gpv A \<I>)) (the_gpv gpv) (the_gpv gpv')"
  by(blast elim!: eq_\<I>_gpv.cases)

lemma eq_\<I>_gpv_Done [intro!]: "A x y \<Longrightarrow> eq_\<I>_gpv A \<I> (Done x) (Done y)"
  by(rule eq_\<I>_gpvI) simp

lemma eq_\<I>_gpv_Done_iff [simp]: "eq_\<I>_gpv A \<I> (Done x) (Done y) \<longleftrightarrow> A x y"
  by(auto dest: eq_\<I>_gpvD)

lemma eq_\<I>_gpv_Pause:
  "\<lbrakk> out \<in> outs_\<I> \<I>; \<And>input. input \<in> responses_\<I> \<I> out \<Longrightarrow> eq_\<I>_gpv A \<I> (rpv input) (rpv' input) \<rbrakk>
  \<Longrightarrow> eq_\<I>_gpv A \<I> (Pause out rpv) (Pause out rpv')"
  by(rule eq_\<I>_gpvI) simp

lemma eq_\<I>_gpv_mono: "eq_\<I>_gpv A \<I> \<le> eq_\<I>_gpv A' \<I>'" if A: "A \<le> A'" "\<I> \<le> \<I>'"
proof
  show "eq_\<I>_gpv A' \<I>' gpv gpv'" if "eq_\<I>_gpv A \<I> gpv gpv'" for gpv gpv' using that
    by(coinduction arbitrary: gpv gpv')
      (drule eq_\<I>_gpvD, auto dest: eq_\<I>_gpvD elim: rel_spmf_mono eq_\<I>_generat_mono[OF A(1) _ A(2), THEN predicate2D, rotated -1])
qed

lemma eq_\<I>_gpv_mono':
  "\<lbrakk> eq_\<I>_gpv A \<I> gpv gpv'; \<And>x y. A x y \<Longrightarrow> A' x y; \<I> \<le> \<I>' \<rbrakk> \<Longrightarrow> eq_\<I>_gpv A' \<I>' gpv gpv'"
  by(blast intro: eq_\<I>_gpv_mono[THEN predicate2D])

lemma eq_\<I>_gpv_mono'' [mono]:
  "eq_\<I>_gpv A \<I> gpv gpv' \<longrightarrow> eq_\<I>_gpv A' \<I> gpv gpv'" if "\<And>x y. A x y \<longrightarrow> A' x y"
  using that by(blast intro: eq_\<I>_gpv_mono')

lemma eq_\<I>_gpv_conversep: "eq_\<I>_gpv A\<inverse>\<inverse> \<I> = (eq_\<I>_gpv A \<I>)\<inverse>\<inverse>"
proof(intro ext iffI; simp)
  show "eq_\<I>_gpv A \<I> gpv gpv'" if "eq_\<I>_gpv A\<inverse>\<inverse> \<I> gpv' gpv" for A and gpv gpv' using that
    by(coinduction arbitrary: gpv gpv')
      (drule eq_\<I>_gpvD, rewrite in \<hole> conversep_iff[symmetric]
        , auto simp add: pmf.rel_conversep[symmetric] option.rel_conversep[symmetric] eq_\<I>_generat_conversep[symmetric] elim: eq_\<I>_generat_mono' rel_spmf_mono)

  from this[of "conversep A"] show "eq_\<I>_gpv A\<inverse>\<inverse> \<I> gpv' gpv" if "eq_\<I>_gpv A \<I> gpv gpv'" for gpv gpv'
    using that by simp
qed

lemma eq_\<I>_gpv_reflI:
  "\<lbrakk> \<And>x. x \<in> results_gpv \<I> gpv \<Longrightarrow> A x x; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> eq_\<I>_gpv A \<I> gpv gpv"
  by(coinduction arbitrary: gpv)(auto intro!: rel_spmf_reflI eq_\<I>_generat_reflI elim!: generat.set_cases intro: results_gpv.intros dest: WT_gpvD)

lemma eq_\<I>_gpv_into_rel_gpv: "eq_\<I>_gpv A \<I>_full gpv gpv' \<Longrightarrow> rel_gpv A (=) gpv gpv'"
  by(coinduction arbitrary: gpv gpv')
    (drule eq_\<I>_gpvD, auto elim: spmf_rel_mono_strong generat.rel_mono_strong dest: eq_\<I>_generat_into_rel_generat )

lemma eq_\<I>_gpv_relcompp: "eq_\<I>_gpv (A OO A') \<I> = eq_\<I>_gpv A \<I> OO eq_\<I>_gpv A' \<I>" (is "?lhs = ?rhs")
proof(intro ext iffI relcomppI; (elim relcomppE)?)
  fix gpv gpv''
  assume *: "?lhs gpv gpv''"
  define middle where "middle = corec_gpv (\<lambda>(gpv, gpv'').
    map_spmf (map_generat (relcompp_witness A A') (relcompp_witness (=) (=)) ((\<circ>) Inr \<circ> rel_witness_fun (=) (=)) \<circ> 
              rel_witness_generat)
    (rel_witness_spmf (eq_\<I>_generat (A OO A') \<I> (eq_\<I>_gpv (A OO A') \<I>)) (the_gpv gpv, the_gpv gpv'')))"
  have middle_sel [simp]: "the_gpv (middle (gpv, gpv'')) = 
     map_spmf (map_generat (relcompp_witness A A') (relcompp_witness (=) (=)) ((\<circ>) middle \<circ> rel_witness_fun (=) (=)) \<circ> 
              rel_witness_generat)
    (rel_witness_spmf (eq_\<I>_generat (A OO A') \<I> (eq_\<I>_gpv (A OO A') \<I>)) (the_gpv gpv, the_gpv gpv''))"
    for gpv gpv'' by(auto simp add: middle_def spmf.map_comp o_def generat.map_comp)
  show "eq_\<I>_gpv A \<I> gpv (middle (gpv, gpv''))" using *
    by(coinduction arbitrary: gpv gpv'')
      (drule eq_\<I>_gpvD, simp add: spmf_rel_map, erule rel_witness_spmf1[THEN rel_spmf_mono]
        , auto 4 3 del: relcomppE elim!: relcompp_witness eq_\<I>_generat.cases)

  show "eq_\<I>_gpv A' \<I> (middle (gpv, gpv'')) gpv''" using *
    by(coinduction arbitrary: gpv gpv'')
      (drule eq_\<I>_gpvD, simp add: spmf_rel_map, erule rel_witness_spmf2[THEN rel_spmf_mono]
        , auto 4 3 del: relcomppE elim: rel_witness_spmf2[THEN rel_spmf_mono] elim!: relcompp_witness eq_\<I>_generat.cases)
next
  show "?lhs gpv gpv''" if "eq_\<I>_gpv A \<I> gpv gpv'" and "eq_\<I>_gpv A' \<I> gpv' gpv''" for gpv gpv' gpv'' using that
    by(coinduction arbitrary: gpv gpv' gpv'')
      ((drule eq_\<I>_gpvD)+, simp, drule (1) rel_spmf_OO_trans, erule rel_spmf_mono
        , auto simp add: eq_\<I>_generat_relcompp elim: eq_\<I>_generat_mono')
qed

lemma eq_\<I>_gpv_map_gpv1: "eq_\<I>_gpv A \<I> (map_gpv f id gpv) gpv' \<longleftrightarrow> eq_\<I>_gpv (\<lambda>x. A (f x)) \<I> gpv gpv'" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  show ?rhs if ?lhs using that
    by(coinduction arbitrary: gpv gpv')
      (drule eq_\<I>_gpvD, auto simp add: gpv.map_sel spmf_rel_map elim!: rel_spmf_mono eq_\<I>_generat_mono')
  show ?lhs if ?rhs using that
    by(coinduction arbitrary: gpv gpv')
      (drule eq_\<I>_gpvD, auto simp add: gpv.map_sel spmf_rel_map elim!: rel_spmf_mono eq_\<I>_generat_mono')
qed

lemma eq_\<I>_gpv_map_gpv2: "eq_\<I>_gpv A \<I> gpv (map_gpv f id gpv') = eq_\<I>_gpv (\<lambda>x y. A x (f y)) \<I> gpv gpv'"
  using eq_\<I>_gpv_map_gpv1[of "conversep A" \<I> f gpv' gpv]
  by(rewrite in "_ = \<hole>" conversep_iff[symmetric] , simp add: eq_\<I>_gpv_conversep[symmetric])
    (subst (asm) eq_\<I>_gpv_conversep , simp add: conversep_iff[abs_def])

lemmas eq_\<I>_gpv_map_gpv [simp] = eq_\<I>_gpv_map_gpv1[abs_def] eq_\<I>_gpv_map_gpv2

lemma (in callee_invariant_on) eq_\<I>_exec_gpv:
  "\<lbrakk> eq_\<I>_gpv A \<I> gpv gpv'; I s \<rbrakk> \<Longrightarrow> rel_spmf (rel_prod A (eq_onp I)) (exec_gpv callee gpv s) (exec_gpv callee gpv' s)"
proof(induction arbitrary: s gpv gpv' rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf exec_gpv.mono exec_gpv.mono exec_gpv_def exec_gpv_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step exec_gpv' exec_gpv'')
  show ?case using step.prems
    by - (drule eq_\<I>_gpvD, erule rel_spmf_bindI
        , auto split!: generat.split simp add: eq_onp_same_args 
        intro: WT_callee[THEN WT_calleeD] callee_invariant step.IH intro!: rel_spmf_bind_reflI)
qed

lemma eq_\<I>_gpv_coinduct_bind [consumes 1, case_names eq_\<I>_gpv]:
  fixes gpv :: "('a, 'out, 'in) gpv" and gpv' :: "('a', 'out, 'in) gpv"
  assumes X: "X gpv gpv'"
    and step: "\<And>gpv gpv'. X gpv gpv'
      \<Longrightarrow> rel_spmf (eq_\<I>_generat A \<I> (\<lambda>gpv gpv'. X gpv gpv' \<or> eq_\<I>_gpv A \<I> gpv gpv' \<or> 
      (\<exists>gpv'' gpv''' (B :: 'b \<Rightarrow> 'b' \<Rightarrow> bool) f g. gpv = bind_gpv gpv'' f \<and> gpv' = bind_gpv gpv''' g \<and> eq_\<I>_gpv B \<I> gpv'' gpv''' \<and> (rel_fun B X) f g))) (the_gpv gpv) (the_gpv gpv')"
  shows "eq_\<I>_gpv A \<I> gpv gpv'"
proof -
  fix x y
  define gpv'' :: "('b, 'out, 'in) gpv" where "gpv'' \<equiv> Done x"
  define f :: "'b \<Rightarrow> ('a, 'out, 'in) gpv" where "f \<equiv> \<lambda>_. gpv"
  define gpv''' :: "('b', 'out, 'in) gpv" where "gpv''' \<equiv> Done y"
  define g :: "'b' \<Rightarrow> ('a', 'out, 'in) gpv" where "g \<equiv> \<lambda>_. gpv'"
  have "eq_\<I>_gpv (\<lambda>x y. X (f x) (g y)) \<I> gpv'' gpv'''" using X
    by(simp add: f_def g_def gpv''_def gpv'''_def)
  then have "eq_\<I>_gpv A \<I> (bind_gpv gpv'' f) (bind_gpv gpv''' g)"
    by(coinduction arbitrary: gpv'' f gpv''' g)
      (drule eq_\<I>_gpvD, (clarsimp simp add: bind_gpv.sel spmf_rel_map simp del: bind_gpv_sel' elim!: rel_spmf_bindI split!: generat.split dest!: step)
        , erule rel_spmf_mono, (erule eq_\<I>_generat.cases; clarsimp), (erule meta_allE, erule (1) meta_impE)
        , (fastforce | force intro: exI[where x="Done _"] elim!: eq_\<I>_gpv_mono' dest: rel_funD)+)

  then show ?thesis unfolding gpv''_def gpv'''_def f_def g_def by simp
qed

context
  fixes S :: "'s1 \<Rightarrow> 's2 \<Rightarrow> bool"
    and callee1 :: "'s1 \<Rightarrow> 'out \<Rightarrow> ('in \<times> 's1, 'out', 'in') gpv"
    and callee2 :: "'s2 \<Rightarrow> 'out \<Rightarrow> ('in \<times> 's2, 'out', 'in') gpv"
    and \<I> :: "('out, 'in) \<I>"
    and \<I>' :: "('out', 'in') \<I>"
  assumes callee: "\<And>s1 s2 q. \<lbrakk> S s1 s2; q \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> eq_\<I>_gpv (rel_prod (eq_onp (\<lambda>r. r \<in> responses_\<I> \<I> q)) S) \<I>' (callee1 s1 q) (callee2 s2 q)"
begin

lemma eq_\<I>_gpv_inline1:
  includes lifting_syntax
  assumes "S s1 s2" "eq_\<I>_gpv A \<I> gpv1 gpv2"
  shows "rel_spmf (rel_sum (rel_prod A S) 
      (\<lambda>(q, rpv1, rpv2) (q', rpv1', rpv2'). q = q' \<and> q' \<in> outs_\<I> \<I>' \<and> (\<exists>q'' \<in> outs_\<I> \<I>. 
          (\<forall>r \<in> responses_\<I> \<I>' q'. eq_\<I>_gpv (rel_prod (eq_onp (\<lambda>r'. r' \<in> responses_\<I> \<I> q'')) S) \<I>' (rpv1 r) (rpv1' r)) \<and> 
          (\<forall>r' \<in> responses_\<I> \<I> q''. eq_\<I>_gpv A \<I> (rpv2 r') (rpv2' r')))))
     (inline1 callee1 gpv1 s1) (inline1 callee2 gpv2 s2)"
  using assms
proof(induction arbitrary: gpv1 gpv2 s1 s2 rule: parallel_fixp_induct_2_2[OF partial_function_definitions_spmf partial_function_definitions_spmf inline1.mono inline1.mono inline1_def inline1_def, unfolded lub_spmf_empty, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step inline1' inline1'')
  from step.prems show ?case
    by - (erule eq_\<I>_gpvD[THEN rel_spmf_bindI]
        , clarsimp split!: generat.split
        , erule eq_\<I>_gpvD[OF callee(1), THEN rel_spmf_bindI]
        , auto simp add: eq_onp_def intro: step.IH[THEN rel_spmf_mono] elim: eq_\<I>_gpvD[OF callee(1), THEN rel_spmf_bindI] split!: generat.split)
qed

lemma eq_\<I>_gpv_inline:
  assumes S: "S s1 s2"
    and gpv: "eq_\<I>_gpv A \<I> gpv1 gpv2"
  shows "eq_\<I>_gpv (rel_prod A S) \<I>' (inline callee1 gpv1 s1) (inline callee2 gpv2 s2)"
  using S gpv
  by (coinduction arbitrary: gpv1 gpv2 s1 s2 rule: eq_\<I>_gpv_coinduct_bind)
    (clarsimp simp add: inline_sel spmf_rel_map, drule (1) eq_\<I>_gpv_inline1
      , fastforce split!: generat.split sum.split del: disjCI intro!: disjI2 rel_funI elim: rel_spmf_mono simp add: eq_onp_def)

end

lemma eq_\<I>_gpv_left_gpv_cong:
  "eq_\<I>_gpv A \<I> gpv gpv' \<Longrightarrow> eq_\<I>_gpv A (\<I> \<oplus>\<^sub>\<I> \<I>') (left_gpv gpv) (left_gpv gpv')"
  by(coinduction arbitrary: gpv gpv')
    (drule eq_\<I>_gpvD, auto 4 4 simp add: spmf_rel_map elim!: rel_spmf_mono eq_\<I>_generat.cases)

lemma eq_\<I>_gpv_right_gpv_cong:
  "eq_\<I>_gpv A \<I>' gpv gpv' \<Longrightarrow> eq_\<I>_gpv A (\<I> \<oplus>\<^sub>\<I> \<I>') (right_gpv gpv) (right_gpv gpv')"
  by(coinduction arbitrary: gpv gpv')
    (drule eq_\<I>_gpvD, auto 4 4 simp add: spmf_rel_map elim!: rel_spmf_mono eq_\<I>_generat.cases)

lemma eq_\<I>_gpvD_WT1: "\<lbrakk> eq_\<I>_gpv A \<I> gpv gpv'; \<I> \<turnstile>g gpv \<surd> \<rbrakk> \<Longrightarrow> \<I> \<turnstile>g gpv' \<surd>"
  by(coinduction arbitrary: gpv gpv')(fastforce simp add: eq_\<I>_generat_iff2 dest: WT_gpv_ContD eq_\<I>_gpvD dest!: rel_setD2 set_spmf_parametric[THEN rel_funD])

lemma eq_\<I>_gpvD_results_gpv2: 
  assumes "eq_\<I>_gpv A \<I> gpv gpv'" "y \<in> results_gpv \<I> gpv'"
  shows "\<exists>x \<in> results_gpv \<I> gpv. A x y"
  using assms(2,1)
  by(induction arbitrary: gpv)
    (fastforce dest!: set_spmf_parametric[THEN rel_funD] rel_setD2 dest: eq_\<I>_gpvD simp add: eq_\<I>_generat_iff2 intro: results_gpv.intros)+


coinductive eq_\<I>_converter :: "('a, 'b) \<I> \<Rightarrow> ('out, 'in) \<I> \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> bool"
  ("_,_ \<turnstile>\<^sub>C/ _ \<sim>/ _" [100, 0, 99, 99] 99)
  for \<I> \<I>' where
    eq_\<I>_converterI: "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'" if
    "\<And>q. q \<in> outs_\<I> \<I> \<Longrightarrow> eq_\<I>_gpv (rel_prod (eq_onp (\<lambda>r. r \<in> responses_\<I> \<I> q)) (eq_\<I>_converter \<I> \<I>')) \<I>' (run_converter conv q) (run_converter conv' q)"

lemma eq_\<I>_converter_coinduct [consumes 1, case_names eq_\<I>_converter, coinduct pred: eq_\<I>_converter]:
  assumes "X conv conv'"
    and "\<And>conv conv' q. \<lbrakk> X conv conv'; q \<in> outs_\<I> \<I> \<rbrakk>
     \<Longrightarrow> eq_\<I>_gpv (rel_prod (eq_onp (\<lambda>r. r \<in> responses_\<I> \<I> q)) (\<lambda>conv conv'. X conv conv' \<or> \<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv')) \<I>'
           (run_converter conv q) (run_converter conv' q)"
  shows "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'"
  using assms(1) by(rule eq_\<I>_converter.coinduct)(blast dest: assms(2))

lemma eq_\<I>_converterD: 
  "eq_\<I>_gpv (rel_prod (eq_onp (\<lambda>r. r \<in> responses_\<I> \<I> q)) (eq_\<I>_converter \<I> \<I>')) \<I>' (run_converter conv q) (run_converter conv' q)"
  if "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'" "q \<in> outs_\<I> \<I>"
  using that by(blast elim: eq_\<I>_converter.cases)

lemma eq_\<I>_converter_reflI: "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv" if "\<I>, \<I>' \<turnstile>\<^sub>C conv \<surd>"
  using that by(coinduction arbitrary: conv)(auto intro!: eq_\<I>_gpv_reflI dest: WT_converterD simp add: eq_onp_same_args)

lemma eq_\<I>_converter_sym [sym]: "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'" if "\<I>, \<I>' \<turnstile>\<^sub>C conv' \<sim> conv"
  using that
  by(coinduction arbitrary: conv conv')
    (drule (1) eq_\<I>_converterD, rewrite in \<hole> conversep_iff[symmetric]
      ,  auto simp add: eq_\<I>_gpv_conversep[symmetric] eq_onp_def elim: eq_\<I>_gpv_mono')

lemma eq_\<I>_converter_trans [trans]:
  "\<lbrakk> \<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'; \<I>, \<I>' \<turnstile>\<^sub>C conv' \<sim> conv'' \<rbrakk> \<Longrightarrow> \<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv''"
  by(coinduction arbitrary: conv conv' conv'')
    ((drule (1) eq_\<I>_converterD)+, drule (1) eq_\<I>_gpv_relcompp[THEN fun_cong, THEN fun_cong, THEN iffD2, OF relcomppI]
      , auto simp add: eq_OO prod.rel_compp[symmetric] eq_onp_def elim!: eq_\<I>_gpv_mono')

lemma eq_\<I>_converter_mono:
  assumes *: "\<I>1, \<I>2 \<turnstile>\<^sub>C conv \<sim> conv'"
    and le: "\<I>1' \<le> \<I>1" "\<I>2 \<le> \<I>2'"
  shows "\<I>1', \<I>2' \<turnstile>\<^sub>C conv \<sim> conv'"
  using *
  by(coinduction arbitrary: conv conv')
    (auto simp add: eq_onp_def dest!:eq_\<I>_converterD  intro: responses_\<I>_mono[THEN subsetD, OF le(1)] 
      elim!: eq_\<I>_gpv_mono'[OF _ _ le(2)] outs_\<I>_mono[THEN subsetD, OF le(1)])

lemma eq_\<I>_converter_eq: "conv1 = conv2" if "\<I>_full, \<I>_full \<turnstile>\<^sub>C conv1 \<sim> conv2"
  using that
  by(coinduction arbitrary: conv1 conv2)
    (auto simp add: eq_\<I>_gpv_into_rel_gpv eq_onp_def intro!: rel_funI elim!: gpv.rel_mono_strong eq_\<I>_gpv_into_rel_gpv dest:eq_\<I>_converterD)

lemma eq_\<I>_attach_on: (* TODO: generalise to eq_resource_on *)
  assumes "\<I>' \<turnstile>res res \<surd>" "\<I>_uniform A UNIV, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'"
  shows "A \<turnstile>\<^sub>R attach conv res \<sim> attach conv' res"
  using assms
  by(coinduction arbitrary: conv conv' res)
    (auto 4 4 simp add: eq_onp_def spmf_rel_map dest: eq_\<I>_converterD intro!: rel_funI run_resource.eq_\<I>_exec_gpv[THEN rel_spmf_mono])

lemma eq_\<I>_attach_on':
  assumes "\<I>' \<turnstile>res res \<surd>" "\<I>, \<I>' \<turnstile>\<^sub>C conv \<sim> conv'" "A \<subseteq> outs_\<I> \<I>"
  shows "A \<turnstile>\<^sub>R attach conv res \<sim> attach conv' res"
  using assms(1) assms(2)[THEN eq_\<I>_converter_mono]
  by(rule eq_\<I>_attach_on)(use assms(3) in \<open>auto simp add: le_\<I>_def\<close>)

lemma eq_\<I>_attach:
  "\<lbrakk> \<I>' \<turnstile>res res \<surd>; \<I>_full, \<I>' \<turnstile>\<^sub>C conv \<sim> conv' \<rbrakk> \<Longrightarrow> attach conv res = attach conv' res"
  by(rule eq_resource_on_UNIV_D)(simp add: eq_\<I>_attach_on)

lemma eq_\<I>_comp_cong:
  "\<lbrakk> \<I>1, \<I>2 \<turnstile>\<^sub>C conv1 \<sim> conv1'; \<I>2, \<I>3 \<turnstile>\<^sub>C conv2 \<sim> conv2' \<rbrakk>
  \<Longrightarrow> \<I>1, \<I>3 \<turnstile>\<^sub>C comp_converter conv1 conv2 \<sim> comp_converter conv1' conv2'"
  by(coinduction arbitrary: conv1 conv2 conv1' conv2')
    (clarsimp, rule eq_\<I>_gpv_mono'[OF eq_\<I>_gpv_inline[where S="eq_\<I>_converter \<I>2 \<I>3"]]
      , (fastforce elim!: eq_\<I>_converterD)+)

lemma comp_converter_cong: "comp_converter conv1 conv2 = comp_converter conv1' conv2'"
  if "\<I>_full, \<I> \<turnstile>\<^sub>C conv1 \<sim> conv1'" "\<I>, \<I>_full \<turnstile>\<^sub>C conv2 \<sim> conv2'"
  by(rule eq_\<I>_converter_eq)(rule eq_\<I>_comp_cong[OF that])

lemma parallel_converter2_id_id: 
  "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>\<^sub>C parallel_converter2 id_converter id_converter \<sim> id_converter"
  by(coinduction)(auto split: sum.split intro!: eq_\<I>_gpv_Pause simp add: eq_onp_same_args)

lemma parallel_converter2_eq_\<I>_cong:
  "\<lbrakk> \<I>1, \<I>1' \<turnstile>\<^sub>C conv1 \<sim> conv1'; \<I>2, \<I>2' \<turnstile>\<^sub>C conv2 \<sim> conv2' \<rbrakk>
  \<Longrightarrow> \<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<turnstile>\<^sub>C parallel_converter2 conv1 conv2 \<sim> parallel_converter2 conv1' conv2'"
  by(coinduction arbitrary: conv1 conv2 conv1' conv2')
    (fastforce intro!: eq_\<I>_gpv_left_gpv_cong eq_\<I>_gpv_right_gpv_cong dest: eq_\<I>_converterD elim!: eq_\<I>_gpv_mono' simp add: eq_onp_def)

lemma id_converter_eq_self: "\<I>,\<I>' \<turnstile>\<^sub>C id_converter \<sim> id_converter" if "\<I> \<le> \<I>'"
  by(rule eq_\<I>_converter_mono[OF _ order_refl that])(rule eq_\<I>_converter_reflI[OF WT_converter_id])

lemma eq_\<I>_converterD_WT1:
  assumes "\<I>,\<I>' \<turnstile>\<^sub>C conv1 \<sim> conv2" and "\<I>,\<I>' \<turnstile>\<^sub>C conv1 \<surd>"
  shows "\<I>,\<I>' \<turnstile>\<^sub>C conv2 \<surd>"
  using assms
  by(coinduction arbitrary: conv1 conv2)
    (drule (1) eq_\<I>_converterD, auto 4 3 dest: eq_\<I>_converterD eq_\<I>_gpvD_WT1 WT_converterD_WT WT_converterD_results eq_\<I>_gpvD_results_gpv2 simp add: eq_onp_def)

lemma eq_\<I>_converterD_WT:
  assumes "\<I>,\<I>' \<turnstile>\<^sub>C conv1 \<sim> conv2"
  shows "\<I>,\<I>' \<turnstile>\<^sub>C conv1 \<surd> \<longleftrightarrow> \<I>,\<I>' \<turnstile>\<^sub>C conv2 \<surd>"
proof(rule iffI, goal_cases)
  case 1 then show ?case using assms by (auto intro: eq_\<I>_converterD_WT1) 
next
  case 2 then show ?case using assms[symmetric] by (auto intro: eq_\<I>_converterD_WT1)
qed

lemma eq_\<I>_gpv_Fail [simp]: "eq_\<I>_gpv A \<I> Fail Fail"
  by(rule eq_\<I>_gpv.intros) simp

lemma eq_\<I>_restrict_gpv:
  assumes "eq_\<I>_gpv A \<I> gpv gpv'"
  shows "eq_\<I>_gpv A \<I> (restrict_gpv \<I> gpv) gpv'"
  using assms
  by(coinduction arbitrary: gpv gpv')
    (fastforce dest: eq_\<I>_gpvD simp add: spmf_rel_map pmf.rel_map option_rel_Some1 eq_\<I>_generat_iff1 elim!: pmf.rel_mono_strong eq_\<I>_generat_mono' split: option.split generat.split)

lemma eq_\<I>_restrict_converter:
  assumes "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<surd>"
    and "outs_\<I> \<I> \<subseteq> A"
  shows "\<I>,\<I>' \<turnstile>\<^sub>C restrict_converter A \<I>' cnv \<sim> cnv"
  using assms(1)
  by(coinduction arbitrary: cnv)
    (use assms(2) in \<open>auto intro!: eq_\<I>_gpv_reflI eq_\<I>_restrict_gpv simp add: eq_onp_def dest: WT_converterD\<close>)

lemma eq_\<I>_restrict_gpv_full:
  "eq_\<I>_gpv A \<I>_full (restrict_gpv \<I> gpv) (restrict_gpv \<I> gpv')"
  if "eq_\<I>_gpv A \<I> gpv gpv'"
  using that
  by(coinduction arbitrary: gpv gpv')
    (fastforce dest: eq_\<I>_gpvD simp add: pmf.rel_map in_set_spmf[symmetric] elim!: pmf.rel_mono_strong split!: option.split generat.split)

lemma eq_\<I>_restrict_converter_cong:
  assumes "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<sim> cnv'"
    and "A \<subseteq> outs_\<I> \<I>"
  shows "restrict_converter A \<I>' cnv = restrict_converter A \<I>' cnv'"
  using assms
  by(coinduction arbitrary: cnv cnv')
    (fastforce intro: eq_\<I>_gpv_into_rel_gpv eq_\<I>_restrict_gpv_full elim!: eq_\<I>_gpv_mono' simp add: eq_onp_def rel_fun_def gpv.rel_map dest: eq_\<I>_converterD)

end

