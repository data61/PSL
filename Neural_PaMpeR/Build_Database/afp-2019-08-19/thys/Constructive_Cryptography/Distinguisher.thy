section \<open>Distinguisher\<close>

theory Distinguisher imports Random_System begin

type_synonym ('a, 'b) distinguisher = "(bool, 'a, 'b) gpv"

translations
  (type) "('a, 'b) distinguisher" <= (type) "(bool, 'a, 'b) gpv"

definition connect :: "('a, 'b) distinguisher \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool spmf" where
  "connect d res = run_gpv run_resource d res"

definition absorb :: "('a, 'b) distinguisher \<Rightarrow> ('a, 'b, 'out, 'in) converter \<Rightarrow> ('out, 'in) distinguisher" where
  "absorb d conv = map_gpv fst id (inline run_converter d conv)"

lemma distinguish_attach: "connect d (attach conv res) = connect (absorb d conv) res"
proof -
  let ?R = "\<lambda>res (conv', res'). res = attach conv' res'"
  have*: "rel_spmf (rel_prod (=) ?R) (exec_gpv run_resource d (attach conv res))
     (exec_gpv (\<lambda>p y. map_spmf (\<lambda>p. (fst (fst p), snd (fst p), snd p))
       (exec_gpv run_resource (run_converter (fst p) y) (snd p))) d (conv, res))"
    by(rule exec_gpv_parametric[where S="\<lambda>res (conv', res'). res = attach conv' res'" and CALL="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD])
      (auto simp add: gpv.rel_eq spmf_rel_map split_def intro: rel_spmf_reflI intro!: rel_funI)

  show ?thesis
    by(simp add: connect_def absorb_def exec_gpv_map_gpv_id spmf.map_comp exec_gpv_inline  o_def split_def spmf_rel_eq[symmetric])
      (rule pmf.map_transfer[THEN rel_funD, THEN rel_funD]
        , rule option.map_transfer[where Rb="rel_prod (=) ?R", THEN rel_funD]
        , auto simp add: * intro: fst_transfer)
qed

lemma absorb_comp_converter: "absorb d (comp_converter conv conv') = absorb (absorb d conv) conv'"
proof -
  let ?R = "\<lambda>conv (conv', conv''). conv = comp_converter conv' conv''"
  have*: "rel_gpv (rel_prod (=) ?R) (=) (inline run_converter d (comp_converter conv conv'))
   (inline (\<lambda>p c2. map_gpv (\<lambda>p. (fst (fst p), snd (fst p), snd p)) id (inline run_converter (run_converter (fst p) c2) (snd p)))  d (conv, conv'))"
    by(rule inline_parametric[where C="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD])
      (auto simp add: gpv.rel_eq gpv.rel_map split_def intro: gpv.rel_refl_strong intro!: rel_funI)

  show ?thesis
    by(simp add: gpv.rel_eq[symmetric] absorb_def inline_map_gpv gpv.map_comp inline_assoc o_def split_def id_def[symmetric])
      (rule gpv.map_transfer[where R1b="rel_prod (=) ?R", THEN rel_funD, THEN rel_funD, THEN rel_funD]
        , auto simp add: * intro: fst_transfer id_transfer)
qed

lemma connect_cong_trace:
  fixes res1 res2 :: "('a, 'b) resource"
  assumes trace_eq: "A \<turnstile>\<^sub>R res1 \<approx> res2"
    and WT: "\<I> \<turnstile>g d \<surd>"
    and out: "outs_gpv \<I> d \<subseteq> A"
    and WT1: "\<I> \<turnstile>res res1 \<surd>"
    and WT2: "\<I> \<turnstile>res res2 \<surd>"
  shows "connect d res1 = connect d res2"
  unfolding connect_def using trace_eq callee_invariant_run_resource callee_invariant_run_resource WT out WT1 WT2
  by(rule trace_callee_eq'_run_gpv)

lemma distinguish_trace_eq:
  assumes distinguish: "\<And>distinguisher. \<I> \<turnstile>g distinguisher \<surd> \<Longrightarrow> connect distinguisher res = connect distinguisher res'"
    and WT1: "\<I> \<turnstile>res res1 \<surd>"
    and WT2: "\<I> \<turnstile>res res2 \<surd>"
  shows "outs_\<I> \<I> \<turnstile>\<^sub>R res \<approx> res'"
proof(rule ccontr)
  let ?P = "\<lambda>xs. \<exists>x. set xs \<subseteq> outs_\<I> \<I> \<times> UNIV \<and> x \<in> outs_\<I> \<I> \<and> trace_callee run_resource (return_spmf res) xs x \<noteq> trace_callee run_resource (return_spmf res') xs x"
  assume "\<not> ?thesis"
  then have "Ex ?P" unfolding trace_callee_eq_def by auto
  with wf_strict_prefix[unfolded wfP_eq_minimal, THEN spec, of "Collect ?P"]
  obtain xs x where xs: "set xs \<subseteq> outs_\<I> \<I> \<times> UNIV"
    and x: "x \<in> outs_\<I> \<I>"
    and neq: "trace_callee run_resource (return_spmf res) xs x \<noteq> trace_callee run_resource (return_spmf res') xs x"
    and shortest: "\<And>xs' x. \<lbrakk> strict_prefix xs' xs; set xs' \<subseteq>  outs_\<I> \<I> \<times> UNIV; x \<in> outs_\<I> \<I> \<rbrakk>
      \<Longrightarrow> trace_callee run_resource (return_spmf res) xs' x = trace_callee run_resource (return_spmf res') xs' x"
    by(auto)
  have shortest: "\<And>xs' x. \<lbrakk> strict_prefix xs' xs; x \<in> outs_\<I> \<I> \<rbrakk>
      \<Longrightarrow> trace_callee run_resource (return_spmf res) xs' x = trace_callee run_resource (return_spmf res') xs' x"
    by(rule shortest)(use xs in \<open>auto 4 3 dest: strict_prefix_setD\<close>)

  define p where "p \<equiv> return_spmf res"
  define q where "q \<equiv> return_spmf res'"
  have p: "lossless_spmf p" and q: "lossless_spmf q" by(simp_all add: p_def q_def)
  from neq obtain y where y: "spmf (trace_callee run_resource p xs x) y \<noteq> spmf (trace_callee run_resource q xs x) y"
    by(fastforce intro: spmf_eqI simp add: p_def q_def)
  have eq: "spmf (trace_callee run_resource p ys x) y = spmf (trace_callee run_resource q ys x) y"
    if "strict_prefix ys xs" "x \<in> outs_\<I> \<I>" for ys x y using shortest[OF that]
    by(auto intro: spmf_eqI simp add: p_def q_def)
  define d :: "('a \<times> 'b) list \<Rightarrow> _"
    where "d = rec_list (Pause x (\<lambda>y'. Done (y = y'))) (\<lambda>(x, y) xs rec. Pause x (\<lambda>input. if input = y then rec else Done False))"
  have d_simps [simp]:
    "d [] = Pause x (\<lambda>y'. Done (y = y'))"
    "d ((a, b) # xs) = Pause a (\<lambda>input. if input = b then d xs else Done False)" for a b xs
    by(simp_all add: d_def fun_eq_iff)
  have WT_d: "\<I> \<turnstile>g d xs \<surd>" using xs by(induction xs)(use x in auto)
  from distinguish[OF WT_d]
  have "spmf (bind_spmf p (connect (d xs))) True = spmf (bind_spmf q (connect (d xs))) True"
    by(simp add: p_def q_def)
  thus False using y eq xs
  proof(induction xs arbitrary: p q)
    case Nil
    then show ?case
      by(simp add: connect_def[abs_def] map_bind_spmf o_def split_def)
        (simp add: map_spmf_conv_bind_spmf[symmetric] map_bind_spmf[unfolded o_def, symmetric] spmf_map vimage_def eq_commute)
  next
    case (Cons xy xs p q)
    obtain x' y' where xy [simp]: "xy = (x', y')" by(cases xy)
    let ?p = "cond_spmf_fst (p \<bind> (\<lambda>s. run_resource s x')) y'"
      and ?q = "cond_spmf_fst (q \<bind> (\<lambda>s. run_resource s x')) y'"
    from Cons.prems(1)
    have "spmf ((map_spmf fst (p \<bind> (\<lambda>y. run_resource y x')) \<bind> (\<lambda>x. map_spmf (Pair x) (cond_spmf_fst (p \<bind> (\<lambda>y. run_resource y x')) x))) \<bind> (\<lambda>(a, b). if a = y' then connect (d xs) b else return_spmf False)) True =
      spmf ((map_spmf fst (q \<bind> (\<lambda>y. run_resource y x')) \<bind> (\<lambda>x. map_spmf (Pair x) (cond_spmf_fst (q \<bind> (\<lambda>y. run_resource y x')) x))) \<bind> (\<lambda>(a, b). if a = y' then connect (d xs) b else return_spmf False)) True"
      unfolding cond_spmf_fst_inverse
      by(clarsimp simp add: connect_def[abs_def] map_bind_spmf o_def split_def if_distrib[where f="\<lambda>x. run_gpv _ x _"] cong del: if_weak_cong)
    hence "spmf ((p \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) \<bind>
                (\<lambda>a. if a = y' then cond_spmf_fst (p \<bind> (\<lambda>y. run_resource y x')) a \<bind> connect (d xs)
                          else bind_spmf (cond_spmf_fst (p \<bind> (\<lambda>y. run_resource y x')) a) (\<lambda>_. return_spmf False))) True =
      spmf ((q \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) \<bind>
                (\<lambda>a. if a = y' then cond_spmf_fst (q \<bind> (\<lambda>y. run_resource y x')) a \<bind> connect (d xs)
                            else bind_spmf (cond_spmf_fst (q \<bind> (\<lambda>y. run_resource y x')) a) (\<lambda>_. return_spmf False))) True"
      by(rule box_equals; use nothing in \<open>rule arg_cong2[where f=spmf]\<close>)
        (auto simp add: map_bind_spmf bind_map_spmf o_def split_def intro!: bind_spmf_cong)
    hence "LINT a|measure_spmf (p \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))). (if a = y' then spmf (?p \<bind> connect (d xs)) True else 0) =
      LINT a|measure_spmf (q \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))). (if a = y' then spmf (?q \<bind> connect (d xs)) True else 0)"
      by(rule box_equals; use nothing in \<open>subst spmf_bind\<close>)
        (auto intro!: Bochner_Integration.integral_cong simp add: bind_spmf_const spmf_scale_spmf)
    hence "LINT a|measure_spmf (p \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))). indicator {y'} a * spmf (?p \<bind> connect (d xs)) True =
      LINT a|measure_spmf (q \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))). indicator {y'} a * spmf (?q \<bind> connect (d xs)) True"
      by(rule box_equals; use nothing in \<open>rule Bochner_Integration.integral_cong\<close>) auto
    hence "spmf (p \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) y' * spmf (?p \<bind> connect (d xs)) True =
      spmf (q \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) y' * spmf (?q \<bind> connect (d xs)) True"
      by(simp add: spmf_conv_measure_spmf)
    moreover from Cons.prems(3)[of "[]" x'] Cons.prems(4)
    have "spmf (p \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) y' = spmf (q \<bind> (\<lambda>s. map_spmf fst (run_resource s x'))) y'"
      by(simp)
    ultimately have "spmf (?p \<bind> connect (d xs)) True = spmf (?q \<bind> connect (d xs)) True"
      by(auto simp add: cond_spmf_fst_def)(auto 4 3 simp add: spmf_eq_0_set_spmf cond_spmf_def o_def bind_UNION intro: rev_image_eqI)
    moreover
    have "spmf (trace_callee run_resource ?p xs x) y \<noteq> spmf (trace_callee run_resource ?q xs x) y"
      using Cons.prems by simp
    moreover
    have "spmf (trace_callee run_resource ?p ys x) y = spmf (trace_callee run_resource ?q ys x) y"
      if ys: "strict_prefix ys xs" and x: "x \<in> outs_\<I> \<I>" for ys x y
      using Cons.prems(3)[of "xy # ys" x y] ys x by simp
    moreover have "set xs \<subseteq> outs_\<I> \<I> \<times> UNIV" using Cons.prems(4) by auto
    ultimately show ?case by(rule Cons.IH)
  qed
qed

lemma connect_eq_resource_cong:
  assumes "\<I> \<turnstile>g distinguisher \<surd>"
    and "outs_\<I> \<I> \<turnstile>\<^sub>R res \<sim> res'"
    and "\<I> \<turnstile>res res \<surd>"
  shows "connect distinguisher res = connect distinguisher res'"
  unfolding connect_def
  by(fold spmf_rel_eq, rule map_spmf_parametric[THEN rel_funD, THEN rel_funD, rotated])
    (auto simp add: rel_fun_def intro: assms exec_gpv_eq_resource_on )

lemma WT_gpv_absorb [WT_intro]:
  "\<lbrakk> \<I>' \<turnstile>g gpv \<surd>; \<I>', \<I> \<turnstile>\<^sub>C conv \<surd> \<rbrakk> \<Longrightarrow> \<I> \<turnstile>g absorb gpv conv \<surd>"
  by(simp add: absorb_def run_converter.WT_gpv_inline_invar)

lemma plossless_gpv_absorb [plossless_intro]:
  assumes gpv: "plossless_gpv \<I>' gpv"
    and conv: "plossless_converter \<I>' \<I> conv"
    and [WT_intro]: "\<I>' \<turnstile>g gpv \<surd>" "\<I>', \<I> \<turnstile>\<^sub>C conv \<surd>"
  shows "plossless_gpv \<I> (absorb gpv conv)"
  by(auto simp add: absorb_def intro: run_plossless_converter.plossless_inline_invariant[OF gpv] WT_intro conv dest: plossless_converterD)

lemma interaction_any_bounded_by_absorb [interaction_bound]:
  assumes gpv: "interaction_any_bounded_by gpv bound1"
    and conv: "interaction_any_bounded_converter conv bound2"
  shows "interaction_any_bounded_by (absorb gpv conv) (bound1 * bound2)"
  unfolding absorb_def
  by(rule interaction_bounded_by_map_gpv_id, rule interaction_bounded_by_inline_invariant[OF gpv, rotated 2])
    (rule conv, auto elim: interaction_any_bounded_converter.cases)

end