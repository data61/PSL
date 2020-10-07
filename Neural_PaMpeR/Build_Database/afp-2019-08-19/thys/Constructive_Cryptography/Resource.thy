theory Resource imports
  More_CryptHOL
begin

section \<open>Resources\<close>

subsection \<open>Type definition\<close>

codatatype ('a, 'b) resource
  = Resource (run_resource: "'a \<Rightarrow> ('b \<times> ('a, 'b) resource) spmf")
  for map: map_resource'
    rel: rel_resource'

lemma case_resource_conv_run_resource: "case_resource f res = f (run_resource res)"
  by(fact resource.case_eq_if)

subsection \<open>Functor\<close>

context 
  fixes a :: "'a \<Rightarrow> 'a'"
    and b :: "'b \<Rightarrow> 'b'"
begin

primcorec map_resource :: "('a', 'b) resource \<Rightarrow> ('a, 'b') resource" where
  "run_resource (map_resource res) = map_spmf (map_prod b map_resource) \<circ> (run_resource res) \<circ> a"

lemma map_resource_sel [simp]:
  "run_resource (map_resource res) a' = map_spmf (map_prod b map_resource) (run_resource res (a a'))"
  by simp

declare map_resource.sel [simp del]

lemma map_resource_ctr [simp, code]:
  "map_resource (Resource f) = Resource (map_spmf (map_prod b map_resource) \<circ> f \<circ> a)"
  by(rule resource.expand; simp add: fun_eq_iff)

end

lemma map_resource_id1: "map_resource id f res = map_resource' f res"
  by(coinduction arbitrary: res)(auto simp add: rel_fun_def spmf_rel_map resource.map_sel intro!: rel_spmf_reflI)

lemma map_resource_id [simp]: "map_resource id id res = res"
  by(simp add: map_resource_id1 resource.map_id)

lemma map_resource_compose [simp]:
  "map_resource a b (map_resource a' b' res) = map_resource (a' \<circ> a) (b \<circ> b') res"
  by(coinduction arbitrary: res)(auto 4 3 intro!: rel_funI rel_spmf_reflI simp add: spmf_rel_map)

functor resource: map_resource by(simp_all add: o_def fun_eq_iff)

subsection \<open>Relator\<close>

coinductive rel_resource :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('c \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'c) resource \<Rightarrow> ('b, 'd) resource \<Rightarrow> bool"
  for A B where
    rel_resourceI:
    "rel_fun A (rel_spmf (rel_prod B (rel_resource A B))) (run_resource res1) (run_resource res2) 
  \<Longrightarrow> rel_resource A B res1 res2"

lemma rel_resource_coinduct [consumes 1, case_names rel_resource, coinduct pred: rel_resource]:
  assumes "X res1 res2"
    and "\<And>res1 res2. X res1 res2 \<Longrightarrow>
         rel_fun A (rel_spmf (rel_prod B (\<lambda>res1 res2. X res1 res2 \<or> rel_resource A B res1 res2)))
            (run_resource res1) (run_resource res2)"
  shows "rel_resource A B res1 res2"
  using assms(1) by(rule rel_resource.coinduct)(simp add: assms(2))

lemma rel_resource_simps [simp, code]:
  "rel_resource A B (Resource f) (Resource g) \<longleftrightarrow> rel_fun A (rel_spmf (rel_prod B (rel_resource A B))) f g" 
  by(subst rel_resource.simps) simp

lemma rel_resourceD:
  "rel_resource A B res1 res2 \<Longrightarrow> rel_fun A (rel_spmf (rel_prod B (rel_resource A B))) (run_resource res1) (run_resource res2)"
  by(blast elim: rel_resource.cases)

lemma rel_resource_eq1: "rel_resource (=) = rel_resource'"
proof(intro ext iffI)
  show "rel_resource' B res1 res2" if "rel_resource (=) B res1 res2" for B res1 res2 using that
    by(coinduction arbitrary: res1 res2)(auto elim: rel_resource.cases)
  show "rel_resource (=) B res1 res2" if "rel_resource' B res1 res2" for B res1 res2 using that
    by(coinduction arbitrary: res1 res2)(auto 4 4 elim: resource.rel_cases intro: spmf_rel_mono_strong simp add: rel_fun_def)
qed

lemma rel_resource_eq: (* [relator_eq] *) "rel_resource (=) (=) = (=)"
  by(simp add: rel_resource_eq1 resource.rel_eq)

lemma rel_resource_mono:
  assumes "A' \<le> A" "B \<le> B'"
  shows "rel_resource A B \<le> rel_resource A' B'"
proof
  show "rel_resource A' B' res1 res2" if "rel_resource A B res1 res2" for res1 res2 using that
    by(coinduct)(auto dest: rel_resourceD elim!: rel_spmf_mono prod.rel_mono_strong rel_fun_mono intro: assms[THEN predicate2D])
qed

lemma rel_resource_conversep: "rel_resource A\<inverse>\<inverse> B\<inverse>\<inverse> = (rel_resource A B)\<inverse>\<inverse>"
proof(intro ext iffI; simp)
  show "rel_resource A B res1 res2" if "rel_resource A\<inverse>\<inverse> B\<inverse>\<inverse> res2 res1"
    for A :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool" and B :: "'c1 \<Rightarrow> 'c2 \<Rightarrow> bool" and res1 res2
    using that by(coinduct)
      (drule rel_resourceD, rewrite in \<hole> conversep_iff[symmetric] 
        , subst rel_fun_conversep[symmetric], subst spmf_rel_conversep[symmetric], erule rel_fun_mono
        , auto simp add: prod.rel_conversep[symmetric] rel_fun_def conversep_iff[abs_def]  elim:rel_spmf_mono prod.rel_mono_strong)

  from this[of "A\<inverse>\<inverse>" "B\<inverse>\<inverse>"]
  show "rel_resource A\<inverse>\<inverse> B\<inverse>\<inverse> res2 res1" if "rel_resource A B res1 res2" for res1 res2 using that by simp
qed

lemma rel_resource_map_resource'1:
  "rel_resource A B (map_resource' f res1) res2 = rel_resource A (\<lambda>x. B (f x)) res1 res2"
  (is "?lhs = ?rhs")
proof
  show ?rhs if ?lhs using that
    by(coinduction arbitrary: res1 res2)
      (drule rel_resourceD, auto simp add: map_resource.sel map_resource_id1[symmetric] rel_fun_comp spmf_rel_map prod.rel_map[abs_def]
        elim!: rel_fun_mono rel_spmf_mono prod.rel_mono[THEN predicate2D, rotated -1])

  show ?lhs if ?rhs using that
    by(coinduction arbitrary: res1 res2)
      (drule rel_resourceD, auto simp add: map_resource.sel map_resource_id1[symmetric] rel_fun_comp spmf_rel_map prod.rel_map[abs_def]
        elim!: rel_fun_mono rel_spmf_mono prod.rel_mono[THEN predicate2D, rotated -1])
qed

lemma rel_resource_map_resource'2:
  "rel_resource A B res1 (map_resource' f res2) = rel_resource A (\<lambda>x y. B x (f y)) res1 res2"
  using rel_resource_map_resource'1[of "conversep A" "conversep B" f res2 res1]
  by(rewrite in "\<hole> = _" conversep_iff[symmetric]
      , rewrite in "_ = \<hole>" conversep_iff[symmetric])
    (simp only: rel_resource_conversep[symmetric]
      , simp only: conversep_iff[abs_def])

lemmas resource_rel_map' = rel_resource_map_resource'1[abs_def] rel_resource_map_resource'2

lemma rel_resource_pos_distr:
  "rel_resource A B OO rel_resource A' B' \<le> rel_resource (A OO A') (B OO B')"
proof(rule predicate2I)
  show "rel_resource (A OO A') (B OO B') res1 res3"
    if "(rel_resource A B OO rel_resource A' B') res1 res3"
    for res1 res3 using that
    apply(coinduction arbitrary: res1 res3)
    apply(erule relcomppE)
    apply(drule rel_resourceD)+
    apply(rule rel_fun_mono)
      apply(rule pos_fun_distr[THEN predicate2D])
      apply(erule (1) relcomppI)
     apply simp
    apply(rule rel_spmf_mono)
     apply(erule rel_spmf_pos_distr[THEN predicate2D])
    apply(auto simp add: prod.rel_compp[symmetric] elim: prod.rel_mono[THEN predicate2D, rotated -1])
    done
qed

lemma left_unique_rel_resource:
  "\<lbrakk> left_total A; left_unique B \<rbrakk> \<Longrightarrow> left_unique (rel_resource A B)"
  unfolding left_unique_alt_def left_total_alt_def rel_resource_conversep[symmetric]
  apply(subst rel_resource_eq[symmetric])
  apply(rule order_trans[OF rel_resource_pos_distr])
  apply(erule (1) rel_resource_mono)
  done

lemma right_unique_rel_resource:
  "\<lbrakk> right_total A; right_unique B \<rbrakk> \<Longrightarrow> right_unique (rel_resource A B)"
  unfolding right_unique_alt_def right_total_alt_def rel_resource_conversep[symmetric]
  apply(subst rel_resource_eq[symmetric])
  apply(rule order_trans[OF rel_resource_pos_distr])
  apply(erule (1) rel_resource_mono)
  done

lemma bi_unique_rel_resource [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique B \<rbrakk> \<Longrightarrow> bi_unique (rel_resource A B)"
  unfolding bi_unique_alt_def bi_total_alt_def by(blast intro: left_unique_rel_resource right_unique_rel_resource)


definition rel_witness_resource :: "('a \<Rightarrow> 'e \<Rightarrow> bool) \<Rightarrow> ('e \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> 'd \<Rightarrow> bool) \<Rightarrow> ('a, 'b) resource \<times> ('c, 'd) resource \<Rightarrow> ('e, 'b \<times> 'd) resource" where
  "rel_witness_resource A A' B = corec_resource (\<lambda>(res1, res2).
   map_spmf (map_prod id Inr \<circ> rel_witness_prod) \<circ> 
   rel_witness_spmf (rel_prod B (rel_resource (A OO A') B)) \<circ> 
   rel_witness_fun A A' (run_resource res1, run_resource res2))"

lemma rel_witness_resource_sel [simp]:
  "run_resource (rel_witness_resource A A' B (res1, res2)) =
   map_spmf (map_prod id (rel_witness_resource A A' B) \<circ> rel_witness_prod) \<circ> 
   rel_witness_spmf (rel_prod B (rel_resource (A OO A') B)) \<circ> 
   rel_witness_fun A A' (run_resource res1, run_resource res2)"
  by(auto simp add: rel_witness_resource_def o_def fun_eq_iff spmf.map_comp intro!: map_spmf_cong)

lemma assumes "rel_resource (A OO A') B res res'"
  and A: "left_unique A" "right_total A"
  and A': "right_unique A'" "left_total A'"
shows rel_witness_resource1: "rel_resource A (\<lambda>b (b', c). b = b' \<and> B b' c) res (rel_witness_resource A A' B (res, res'))" (is "?thesis1")
  and rel_witness_resource2: "rel_resource A' (\<lambda>(b, c') c. c = c' \<and> B b c') (rel_witness_resource A A' B (res, res')) res'" (is "?thesis2")
proof -
  show ?thesis1 using assms(1)
  proof(coinduction arbitrary: res res')
    case rel_resource
    from this[THEN rel_resourceD] show ?case
      by(simp add: rel_fun_comp)
        (erule rel_fun_mono[OF rel_witness_fun1[OF _ A A']]
          , auto simp add: spmf_rel_map elim!: rel_spmf_mono[OF rel_witness_spmf1])
  qed
  show ?thesis2 using assms(1)
  proof(coinduction arbitrary: res res')
    case rel_resource
    from this[THEN rel_resourceD] show ?case
      by(simp add: rel_fun_comp)
        (erule rel_fun_mono[OF rel_witness_fun2[OF _ A A']]
          , auto simp add: spmf_rel_map elim!: rel_spmf_mono[OF rel_witness_spmf2])
  qed
qed

lemma rel_resource_neg_distr:
  assumes A: "left_unique A" "right_total A"
    and A': "right_unique A'" "left_total A'"
  shows "rel_resource (A OO A') (B OO B') \<le> rel_resource A B OO rel_resource A' B'"
proof(rule predicate2I relcomppI)+
  fix res res''
  assume *: "rel_resource (A OO A') (B OO B') res res''"
  let ?res' = "map_resource' (relcompp_witness B B') (rel_witness_resource A A' (B OO B') (res, res''))"
  show "rel_resource A B res ?res'" using rel_witness_resource1[OF * A A'] unfolding resource_rel_map'
    by(rule rel_resource_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
  show "rel_resource A' B' ?res' res''" using rel_witness_resource2[OF * A A'] unfolding resource_rel_map'
    by(rule rel_resource_mono[THEN predicate2D, rotated -1]; clarify del: relcomppE elim!: relcompp_witness)
qed

lemma left_total_rel_resource:
  "\<lbrakk> left_unique A; right_total A; left_total B \<rbrakk> \<Longrightarrow> left_total (rel_resource A B)"
  unfolding left_unique_alt_def left_total_alt_def rel_resource_conversep[symmetric]
  apply(subst rel_resource_eq[symmetric])
  apply(rule order_trans[rotated])
   apply(rule rel_resource_neg_distr; simp add: left_unique_alt_def)
  apply(rule rel_resource_mono; assumption)
  done

lemma right_total_rel_resource:
  "\<lbrakk> right_unique A; left_total A; right_total B \<rbrakk> \<Longrightarrow> right_total (rel_resource A B)"
  unfolding right_unique_alt_def right_total_alt_def rel_resource_conversep[symmetric]
  apply(subst rel_resource_eq[symmetric])
  apply(rule order_trans[rotated])
   apply(rule rel_resource_neg_distr; simp add: right_unique_alt_def)
  apply(rule rel_resource_mono; assumption)
  done

lemma bi_total_rel_resource [transfer_rule]:
  "\<lbrakk> bi_total A; bi_unique A; bi_total B \<rbrakk> \<Longrightarrow> bi_total (rel_resource A B)"
  unfolding bi_total_alt_def bi_unique_alt_def
  by(blast intro: left_total_rel_resource right_total_rel_resource)

context includes lifting_syntax begin

lemma Resource_parametric [transfer_rule]:
  "((A ===> rel_spmf (rel_prod B (rel_resource A B))) ===> rel_resource A B) Resource Resource"
  by(rule rel_funI)(simp)

lemma run_resource_parametric [transfer_rule]:
  "(rel_resource A B ===> A ===> rel_spmf (rel_prod B (rel_resource A B))) run_resource run_resource"
  by(rule rel_funI)(auto dest: rel_resourceD)

lemma corec_resource_parametric [transfer_rule]:
  "((S ===> A ===> rel_spmf (rel_prod B (rel_sum (rel_resource A B) S))) ===> S ===> rel_resource A B)
   corec_resource corec_resource"
proof((rule rel_funI)+, goal_cases)
  case (1 f g s1 s2)
  then show ?case using 1(2)
    by (coinduction arbitrary: s1 s2)
      (drule 1(1)[THEN rel_funD], auto 4 4 simp add: rel_fun_comp spmf_rel_map prod.rel_map[abs_def] split: sum.split elim!: rel_fun_mono rel_spmf_mono elim: prod.rel_mono[THEN predicate2D, rotated -1])
qed

lemma map_resource_parametric [transfer_rule]:
  "((A' ===> A) ===> (B ===> B') ===> rel_resource A B ===> rel_resource A' B') map_resource map_resource"
  unfolding map_resource_def by(transfer_prover)

lemma map_resource'_parametric [transfer_rule]:
  "((B ===> B') ===> rel_resource (=) B ===> rel_resource (=) B') map_resource' map_resource'"
  unfolding map_resource_id1[symmetric] by transfer_prover

lemma case_resource_parametric [transfer_rule]:
  "(((A ===> rel_spmf (rel_prod B (rel_resource A B))) ===> C) ===> rel_resource A B ===> C)
  case_resource case_resource"
  unfolding case_resource_conv_run_resource by transfer_prover

end

lemma rel_resource_Grp:
  "rel_resource (conversep (BNF_Def.Grp UNIV f)) (BNF_Def.Grp UNIV g) = BNF_Def.Grp UNIV (map_resource f g)"
proof((rule ext iffI)+, goal_cases)
  case (1 res res')
  have *: "rel_resource (\<lambda>a b. b = f a)\<inverse>\<inverse> (\<lambda>a b. b = g a) res res' \<Longrightarrow> res' = map_resource f g res"
    by(rule sym, subst (3) map_resource_id[symmetric], subst rel_resource_eq[symmetric])
      (erule map_resource_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1]
        , auto simp add: rel_fun_def)

  from 1 show ?case unfolding Grp_def using * by (clarsimp simp add: * simp del: conversep_iff)
next
  case (2 _ _)
  then show ?case 
    by(clarsimp simp add: Grp_iff, subst map_resource_id[symmetric])
      (rule map_resource_parametric[THEN rel_funD, THEN rel_funD, THEN rel_funD, rotated -1]
        , subst rel_resource_eq, auto simp add: Grp_iff rel_fun_def)
qed

subsection \<open>Losslessness\<close>

coinductive lossless_resource :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool"
  for \<I> where
    lossless_resourceI: "lossless_resource \<I> res" if
    "\<And>a. a \<in> outs_\<I> \<I> \<Longrightarrow> lossless_spmf (run_resource res a)"
    "\<And>a b res'. \<lbrakk> a \<in> outs_\<I> \<I>; (b, res') \<in> set_spmf (run_resource res a) \<rbrakk> \<Longrightarrow> lossless_resource \<I> res'"

lemma lossless_resource_coinduct [consumes 1, case_names lossless_resource, case_conclusion lossless_resource lossless step, coinduct pred: lossless_resource]:
  assumes "X res"
    and "\<And>res a. \<lbrakk> X res; a \<in> outs_\<I> \<I> \<rbrakk> \<Longrightarrow> lossless_spmf (run_resource res a) \<and>
          (\<forall>(b, res') \<in> set_spmf (run_resource res a). X res' \<or> lossless_resource \<I> res')"
  shows "lossless_resource \<I> res"
  using assms(1) by(rule lossless_resource.coinduct)(auto dest: assms(2))

lemma lossless_resourceD:
  "\<lbrakk> lossless_resource \<I> res; a \<in> outs_\<I> \<I> \<rbrakk>
  \<Longrightarrow> lossless_spmf (run_resource res a) \<and> (\<forall>(x, res')\<in>set_spmf (run_resource res a). lossless_resource \<I> res')"
  by(auto elim: lossless_resource.cases)

lemma lossless_resource_mono:
  assumes "lossless_resource \<I>' res"
    and le: "outs_\<I> \<I> \<subseteq> outs_\<I> \<I>'"
  shows "lossless_resource \<I> res"
  using assms(1)
  by(coinduction arbitrary: res)(auto dest: lossless_resourceD intro: subsetD[OF le])

lemma lossless_resource_mono': 
  "\<lbrakk> lossless_resource \<I>' res; \<I> \<le> \<I>' \<rbrakk> \<Longrightarrow> lossless_resource \<I> res"
  by(erule lossless_resource_mono)(simp add: le_\<I>_def)


subsection \<open>Operations\<close>

context fixes "oracle" :: "'s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's) spmf" begin

primcorec resource_of_oracle :: "'s \<Rightarrow> ('a, 'b) resource" where
  "run_resource (resource_of_oracle s) = (\<lambda>a. map_spmf (map_prod id resource_of_oracle) (oracle s a))"

end

lemma resource_of_oracle_parametric [transfer_rule]: includes lifting_syntax shows
  "((S ===> A ===> rel_spmf (rel_prod B S)) ===> S ===> rel_resource A B) resource_of_oracle resource_of_oracle"
  unfolding resource_of_oracle_def by transfer_prover

lemma map_resource_resource_of_oracle:
  "map_resource f g (resource_of_oracle oracle s) = resource_of_oracle (map_fun id (map_fun f (map_spmf (map_prod g id))) oracle) s"
  for s :: 's
  using resource_of_oracle_parametric[of "BNF_Def.Grp UNIV (id :: 's \<Rightarrow> _)" "conversep (BNF_Def.Grp UNIV f)" "BNF_Def.Grp UNIV g"]
  unfolding prod.rel_Grp option.rel_Grp pmf.rel_Grp rel_fun_Grp rel_resource_Grp
  by simp
    (subst (asm) (1 2) eq_alt[symmetric]
      , subst (asm) (1 2) conversep_eq[symmetric]
      , subst (asm) (1 2) eq_alt
      , unfold rel_fun_Grp, simp add: rel_fun_Grp rel_fun_def Grp_iff)

lemma (in callee_invariant_on) lossless_resource_of_oracle:
  assumes *: "\<And>s x. \<lbrakk> x \<in> outs_\<I> \<I>; I s \<rbrakk> \<Longrightarrow> lossless_spmf (callee s x)"
    and "I s" 
  shows "lossless_resource \<I> (resource_of_oracle callee s)"
  using \<open>I s\<close> by(coinduction arbitrary: s)(auto intro: * dest: callee_invariant)

context includes lifting_syntax begin

lemma resource_of_oracle_rprodl: includes lifting_syntax shows
  "resource_of_oracle ((rprodl ---> id ---> map_spmf (map_prod id lprodr)) oracle) ((s1, s2), s3) = 
    resource_of_oracle oracle (s1, s2, s3)"
  by(rule resource_of_oracle_parametric[of "BNF_Def.Grp UNIV rprodl" "(=)" "(=)", THEN rel_funD, THEN rel_funD, unfolded rel_resource_eq])
    (auto simp add: Grp_iff rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)

lemma resource_of_oracle_extend_state_oracle [simp]:
  "resource_of_oracle (extend_state_oracle oracle) (s', s) = resource_of_oracle oracle s"
  by(rule resource_of_oracle_parametric[of "conversep (BNF_Def.Grp UNIV (\<lambda>s. (s', s)))" "(=)" "(=)", THEN rel_funD, THEN rel_funD, unfolded rel_resource_eq])
    (auto simp add: Grp_iff rel_fun_def spmf_rel_map intro!: rel_spmf_reflI)

end

lemma exec_gpv_resource_of_oracle:
  "exec_gpv run_resource gpv (resource_of_oracle oracle s) = map_spmf (map_prod id (resource_of_oracle oracle)) (exec_gpv oracle gpv s)"
  by(subst spmf.map_id[symmetric], fold pmf.rel_eq)
    (rule pmf.map_transfer[THEN rel_funD, THEN rel_funD, rotated]
      , rule exec_gpv_parametric[where S="\<lambda>res s. res = resource_of_oracle oracle s" and CALL="(=)" and A="(=)", THEN rel_funD, THEN rel_funD, THEN rel_funD]
      , auto simp add: gpv.rel_eq rel_fun_def spmf_rel_map elim: option.rel_cases intro!: rel_spmf_reflI)

primcorec parallel_resource :: "('a, 'b) resource \<Rightarrow> ('c, 'd) resource \<Rightarrow> ('a + 'c, 'b + 'd) resource" where
  "run_resource (parallel_resource res1 res2) = 
   (\<lambda>ac. case ac of Inl a \<Rightarrow> map_spmf (map_prod Inl (\<lambda>res1'. parallel_resource res1' res2)) (run_resource res1 a)
         | Inr c \<Rightarrow> map_spmf (map_prod Inr (\<lambda>res2'. parallel_resource res1 res2')) (run_resource res2 c))"

lemma parallel_resource_parametric [transfer_rule]: includes lifting_syntax shows
  "(rel_resource A B ===> rel_resource C D ===> rel_resource (rel_sum A C) (rel_sum B D))
   parallel_resource parallel_resource"
  unfolding parallel_resource_def by transfer_prover

text \<open>
  We cannot define the analogue of @{term plus_oracle} because we no longer have access to the state,
  so state sharing is not possible!  So we can only compose resources, but we cannot build one
  resource with several interfaces this way!
\<close>

lemma resource_of_parallel_oracle:
  "resource_of_oracle (parallel_oracle oracle1 oracle2) (s1, s2) =
   parallel_resource (resource_of_oracle oracle1 s1) (resource_of_oracle oracle2 s2)"
  by(coinduction arbitrary: s1 s2)
    (auto 4 3 simp add: rel_fun_def spmf_rel_map split: sum.split intro!: rel_spmf_reflI)

lemma parallel_resource_assoc: \<comment> \<open>There's still an ugly map operation in there to rebalance the interface trees, but well...\<close>
  "parallel_resource (parallel_resource res1 res2) res3 = 
   map_resource rsuml lsumr (parallel_resource res1 (parallel_resource res2 res3))"
  by(coinduction arbitrary: res1 res2 res3)
    (auto 4 5 intro!: rel_funI rel_spmf_reflI simp add: spmf_rel_map split: sum.split)


lemma lossless_parallel_resource:
  assumes "lossless_resource \<I> res1" "lossless_resource \<I>' res2"
  shows "lossless_resource (\<I> \<oplus>\<^sub>\<I> \<I>') (parallel_resource res1 res2)"
  using assms
  by(coinduction arbitrary: res1 res2)(clarsimp; erule PlusE; simp; frule (1) lossless_resourceD; auto 4 3)

subsection \<open>Well-typing\<close>

coinductive WT_resource :: "('a, 'b) \<I> \<Rightarrow> ('a, 'b) resource \<Rightarrow> bool" ("_ /\<turnstile>res _ \<surd>" [100, 0] 99)
  for \<I> where
    WT_resourceI: "\<I> \<turnstile>res res \<surd>"
  if "\<And>q r res'. \<lbrakk> q \<in> outs_\<I> \<I>; (r, res') \<in> set_spmf (run_resource res q) \<rbrakk> \<Longrightarrow> r \<in> responses_\<I> \<I> q \<and> \<I> \<turnstile>res res' \<surd>" 

lemma WT_resource_coinduct [consumes 1, case_names WT_resource, case_conclusion WT_resource response WT_resource, coinduct pred: WT_resource]:
  assumes "X res"
    and "\<And>res q r res'. \<lbrakk> X res; q \<in> outs_\<I> \<I>; (r, res') \<in> set_spmf (run_resource res q) \<rbrakk>
       \<Longrightarrow> r \<in> responses_\<I> \<I> q \<and> (X res' \<or> \<I> \<turnstile>res res' \<surd>)"
  shows "\<I> \<turnstile>res res \<surd>"
  using assms(1) by(rule WT_resource.coinduct)(blast dest: assms(2))

lemma WT_resourceD:
  assumes "\<I> \<turnstile>res res \<surd>" "q \<in> outs_\<I> \<I>" "(r, res') \<in> set_spmf (run_resource res q)"
  shows "r \<in> responses_\<I> \<I> q \<and> \<I> \<turnstile>res res' \<surd>"
  using assms by(auto elim: WT_resource.cases)

lemma WT_resource_of_oracle [simp]:
  assumes "\<And>s. \<I> \<turnstile>c oracle s \<surd>"
  shows "\<I> \<turnstile>res resource_of_oracle oracle s \<surd>"
  by(coinduction arbitrary: s)(auto dest: WT_calleeD[OF assms])

lemma WT_resource_bot [simp]: "bot \<turnstile>res res \<surd>"
  by(rule WT_resource.intros)auto

lemma WT_resource_full: "\<I>_full \<turnstile>res res \<surd>"
  by(coinduction arbitrary: res)(auto)

lemma (in callee_invariant_on) WT_resource_of_oracle:
  "I s \<Longrightarrow> \<I> \<turnstile>res resource_of_oracle callee s \<surd>"
  by(coinduction arbitrary: s)(auto dest: callee_invariant')

named_theorems WT_intro "Interface typing introduction rules"

lemmas [WT_intro] = WT_gpv_map_gpv' WT_gpv_map_gpv

lemma WT_parallel_resource [WT_intro]:
  assumes "\<I>1 \<turnstile>res res1 \<surd>"
    and "\<I>2 \<turnstile>res res2 \<surd>"
  shows "\<I>1 \<oplus>\<^sub>\<I> \<I>2 \<turnstile>res parallel_resource res1 res2 \<surd>"
  using assms
  by(coinduction arbitrary: res1 res2)(auto 4 4 intro!: imageI dest: WT_resourceD)

lemma callee_invariant_run_resource: "callee_invariant_on run_resource (\<lambda>res.  \<I> \<turnstile>res res \<surd>) \<I>"
  by(unfold_locales)(auto dest: WT_resourceD intro: WT_calleeI)

lemma callee_invariant_run_lossless_resource:
  "callee_invariant_on run_resource (\<lambda>res. lossless_resource \<I> res \<and> \<I> \<turnstile>res res \<surd>) \<I>"
  by(unfold_locales)(auto dest: WT_resourceD lossless_resourceD intro: WT_calleeI)

interpretation run_lossless_resource:
  callee_invariant_on run_resource "\<lambda>res. lossless_resource \<I> res \<and> \<I> \<turnstile>res res \<surd>" \<I> for \<I>
  by(rule callee_invariant_run_lossless_resource)

end
