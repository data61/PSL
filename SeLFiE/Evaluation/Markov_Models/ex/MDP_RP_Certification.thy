section \<open>Certification of Reachability Problems on MDPs\<close>

theory MDP_RP_Certification
imports
  "../MDP_Reachability_Problem"
  "HOL-Library.IArray"
  "HOL-Library.Code_Target_Numeral"
begin

context Reachability_Problem
begin

lemma p_ub':
  fixes x
  assumes 1: "s \<in> S" "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> (\<Sum>t\<in>S. pmf D t * x t) \<le> x s"
  assumes 2: "\<And>s. s \<in> S1 \<Longrightarrow> x s \<noteq> 0 \<Longrightarrow> (\<exists>t\<in>S2. (s, t) \<in> (SIGMA s:S1. \<Union>D\<in>K s. set_pmf D)\<^sup>*)"
  assumes 3: "\<And>s. s \<in> S - S1 - S2 \<Longrightarrow> x s = 0"
  assumes 4: "\<And>s. s \<in> S2 \<Longrightarrow> x s = 1"
  shows "enn2real (p s) \<le> x s"
proof (rule p_ub[OF 1 _ 4])
  fix s assume "s \<in> S" "p s = 0" with 2[of s] p_pos[of s] p_S2[of s] 3[of s] show "x s = 0"
    by (cases "x s = 0") auto
qed

lemma n_lb':
  fixes x
  assumes "wf R"
  assumes 1: "s \<in> S" "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> x s \<le> (\<Sum>t\<in>S. pmf D t * x t)"
  assumes 2: "\<And>s D. s \<in> S1 \<Longrightarrow> D \<in> K s \<Longrightarrow> x s \<noteq> 0 \<Longrightarrow> \<exists>t\<in>D. ((t, s) \<in> R \<and> t \<in> S1 \<and> x t \<noteq> 0) \<or> t \<in> S2"
  assumes 3: "\<And>s. s \<in> S - S1 - S2 \<Longrightarrow> x s = 0"
  assumes 4: "\<And>s. s \<in> S2 \<Longrightarrow> x s = 1"
  shows "x s \<le> enn2real (n s)"
proof (rule n_lb[OF 1 _ 4])
  fix s assume *: "s \<in> S" "n s = 0"
  show "x s = 0"
  proof (rule ccontr)
    assume "x s \<noteq> 0"
    with * n_S2[of s] n_nS12[of s] 3[of s] have "s \<in> S1"
      by (metis DiffI zero_neq_one)
    have "0 < n s"
      by (intro n_pos[of "\<lambda>s. x s \<noteq> 0", OF \<open>x s \<noteq> 0\<close> \<open>s \<in> S1\<close> \<open>wf R\<close>])
         (metis zero_less_one n_S2 2)
    with \<open>n s = 0\<close> show False by auto
  qed
qed

end

no_notation Stream.snth (infixl "!!" 100) \<comment> \<open>we use @{text "!!"} for IArray\<close>

subsection \<open>Computable representation\<close>

record mdp_reachability_problem =
  state_count :: nat
  distrs :: "(nat \<times> rat) list list iarray"
  states1 :: "bool iarray"
  states2 :: "bool iarray"

record 'a RP_sub_cert =
  solution :: "rat iarray"
  witness :: "('a \<times> nat) iarray"

record RP_cert =
  pos_cert :: "(nat \<times> nat) RP_sub_cert"
  neg_cert :: "nat list RP_sub_cert"

definition "sparse_mult sx y = sum_list (map (\<lambda>(n, x). x * y !! n) sx)"

primrec lookup where
  "lookup d [] x = d"
| "lookup d (y#ys) x = (if fst y = x then snd y else lookup d ys x)"

lemma lookup_eq_map_of: "lookup d xs x = (case map_of xs x of Some x \<Rightarrow> x | None \<Rightarrow> d)"
  by (induct xs) simp_all

lemma lookup_in_set:
  "distinct (map fst xs) \<Longrightarrow> x \<in> set xs \<Longrightarrow> lookup d xs (fst x) = snd x"
  unfolding lookup_eq_map_of by (subst map_of_is_SomeI[where y="snd x"]) simp_all

lemma lookup_not_in_set:
  "x \<notin> fst ` set xs \<Longrightarrow> lookup d xs x = d"
  unfolding lookup_eq_map_of
  by (subst map_of_eq_None_iff[of xs x, THEN iffD2]) auto

lemma lookup_nonneg:
  "(\<And>x v. (x, v) \<in> set xs \<Longrightarrow> 0 \<le> v) \<Longrightarrow> (0::'a::ordered_comm_monoid_add) \<le> lookup 0 xs x"
  apply (induction xs)
  apply simp
  apply force
  done

lemma sparse_mult_eq_sum_lookup:
  fixes xs :: "(nat \<times> 'a::comm_semiring_1) list"
  assumes "list_all (\<lambda>(n, x). n < M) xs" "distinct (map fst xs)"
  shows "sparse_mult xs y = (\<Sum>i<M. lookup 0 xs i * y !! i)"
proof -
  from \<open>distinct (map fst xs)\<close> have "distinct xs" "inj_on fst (set xs)"
    by (simp_all add: distinct_map)
  then have "sparse_mult xs y = (\<Sum>x\<in>set xs. snd x * y !! fst x)"
    by (auto intro!: sum.cong simp add: sparse_mult_def sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>x\<in>set xs. lookup 0 xs (fst x) * y !! fst x)"
    by (intro sum.cong refl arg_cong2[where f="(*)"]) (simp add: lookup_in_set assms)
  also have "\<dots> = (\<Sum>x\<in>fst ` set xs. lookup 0 xs x * y !! x)"
    using \<open>inj_on fst (set xs)\<close> by (simp add: sum.reindex)
  also have "\<dots> = (\<Sum>x<M. lookup 0 xs x * y !! x)"
    using assms(1)
    by (intro sum.mono_neutral_cong_left)
       (auto simp: list_all_iff lookup_eq_map_of map_of_eq_None_iff[THEN iffD2])
  finally show ?thesis .
qed

lemma sum_list_eq_sum_lookup:
  fixes xs :: "(nat \<times> 'a::comm_semiring_1) list"
  assumes "list_all (\<lambda>(n, x). n < M) xs" "distinct (map fst xs)"
  shows "sum_list (map snd xs) = (\<Sum>i<M. lookup 0 xs i)"
proof -
  from \<open>distinct (map fst xs)\<close> have "distinct xs" "inj_on fst (set xs)"
    by (simp_all add: distinct_map)
  then have "sum_list (map snd xs) = (\<Sum>x\<in>set xs. snd x)"
    by (auto intro!: sum.cong simp add: sparse_mult_def sum_list_distinct_conv_sum_set)
  also have "\<dots> = (\<Sum>x\<in>set xs. lookup 0 xs (fst x))"
    by (intro sum.cong refl arg_cong2[where f="(*)"]) (simp add: lookup_in_set assms)
  also have "\<dots> = (\<Sum>x\<in>fst ` set xs. lookup 0 xs x)"
    using \<open>inj_on fst (set xs)\<close> by (simp add: sum.reindex)
  also have "\<dots> = (\<Sum>x<M. lookup 0 xs x)"
    using assms(1)
    by (intro sum.mono_neutral_cong_left)
       (auto simp: list_all_iff lookup_eq_map_of map_of_eq_None_iff[THEN iffD2])
  finally show ?thesis .
qed

definition
  "valid_mdp_rp mdp \<longleftrightarrow>
    0 < state_count mdp \<and>
    IArray.length (distrs mdp) = state_count mdp \<and>
    IArray.length (states1 mdp) = state_count mdp \<and>
    IArray.length (states2 mdp) = state_count mdp \<and>
    (\<forall>i<state_count mdp. \<not> (states1 mdp !! i \<and> states2 mdp !! i) \<and>
      list_all (\<lambda>ds. distinct (map fst ds) \<and> list_all (\<lambda>(n, x). 0 \<le> x \<and> n < state_count mdp) ds \<and>
                     sum_list (map snd ds) = 1) (distrs mdp !! i) \<and>
      \<not> List.null (distrs mdp !! i))"

definition
  "valid_sub_cert mdp c ord check \<longleftrightarrow>
    IArray.length (witness c) = state_count mdp \<and>
    IArray.length (solution c) = state_count mdp \<and>
    (\<forall>i<state_count mdp.
      if states2 mdp !! i then solution c !! i = 1
      else if states1 mdp !! i then 0 \<le> solution c !! i \<and>
        (list_all (\<lambda>ds. ord (sparse_mult ds (solution c)) (solution c !! i)) (distrs mdp !! i)) \<and>
        (0 < solution c !! i \<longrightarrow> check (distrs mdp !! i) (witness c !! i))
      else solution c !! i = 0)"

definition
  "valid_pos_cert mdp c \<longleftrightarrow>
    valid_sub_cert mdp c (\<le>)
      (\<lambda>D ((j, a), n). j < state_count mdp \<and> snd (witness c !! j) < n \<and> 0 < solution c !! j \<and>
        a < length D \<and> lookup 0 (D ! a) j \<noteq> 0)"

definition
  "valid_neg_cert mdp c \<longleftrightarrow>
    valid_sub_cert mdp c (\<ge>)
      (\<lambda>D (J, n). list_all2 (\<lambda>j d. j < state_count mdp \<and> snd (witness c !! j) < n \<and>
        lookup 0 d j \<noteq> 0 \<and> 0 < solution c !! j) J D)"

definition
  "valid_cert mdp c \<longleftrightarrow> valid_pos_cert mdp (pos_cert c) \<and> valid_neg_cert mdp (neg_cert c)"

lemma valid_mdp_rpD_length:
  assumes "valid_mdp_rp mdp"
  shows "0 < state_count mdp" "IArray.length (distrs mdp) = state_count mdp"
    "IArray.length (states1 mdp) = state_count mdp" "IArray.length (states2 mdp) = state_count mdp"
  using assms by (auto simp: valid_mdp_rp_def)

lemma valid_mdp_rpD:
  assumes "valid_mdp_rp mdp" "i < state_count mdp"
  shows "\<not> (states1 mdp !! i \<and> states2 mdp !! i)"
    and "\<And>ds n x. ds \<in> set (distrs mdp !! i) \<Longrightarrow> (n, x) \<in> set ds \<Longrightarrow> n < state_count mdp"
    and "\<And>ds n x. ds \<in> set (distrs mdp !! i) \<Longrightarrow> (n, x) \<in> set ds \<Longrightarrow> 0 \<le> x"
    and "\<And>ds. ds \<in> set (distrs mdp !! i) \<Longrightarrow> sum_list (map snd ds) = 1"
    and "\<And>ds. ds \<in> set (distrs mdp !! i) \<Longrightarrow> distinct (map fst ds)"
    and "distrs mdp !! i \<noteq> []"
  using assms by (auto simp: valid_mdp_rp_def list_all_iff List.null_def elim!: allE[of _ i])

lemma valid_mdp_rp_sparse_mult:
  assumes "valid_mdp_rp mdp" "i < state_count mdp" "ds \<in> set (distrs mdp !! i)"
  shows "sparse_mult ds y = (\<Sum>i<state_count mdp. lookup 0 ds i * y !! i)"
  using valid_mdp_rpD(2,5)[OF assms] by (intro sparse_mult_eq_sum_lookup) (auto simp: list_all_iff)

lemma valid_sub_certD:
  assumes "valid_mdp_rp mdp" "valid_sub_cert mdp c ord check" "i < state_count mdp"
  shows "\<not> states1 mdp !! i \<Longrightarrow> \<not> states2 mdp !! i \<Longrightarrow> solution c !! i = 0"
    and "states2 mdp !! i \<Longrightarrow> solution c !! i = 1"
    and "states1 mdp !! i \<Longrightarrow> 0 \<le> solution c !! i"
    and "\<And>ds. states1 mdp !! i \<Longrightarrow> ds \<in> set (distrs mdp !! i) \<Longrightarrow> ord (sparse_mult ds (solution c)) (solution c !! i)"
    and "\<And>ds. states1 mdp !! i \<Longrightarrow> 0 < solution c !! i \<longrightarrow> check (distrs mdp !! i) (witness c !! i)"
  using assms(2,3) valid_mdp_rpD(1)[OF assms(1,3)]
  by (auto simp add: valid_sub_cert_def list_all_iff)

lemma valid_pos_certD:
  assumes "valid_mdp_rp mdp" "valid_pos_cert mdp c" "i < state_count mdp" "states1 mdp !! i"
    "0 < solution c !! i" "witness c !! i = ((j, a), n)"
  shows "snd (witness c !! j) < n \<and> j < state_count mdp \<and> a < length (distrs mdp !! i) \<and>
          lookup 0 ((distrs mdp !! i) ! a) j \<noteq> 0 \<and> 0 < solution c !! j"
  using valid_sub_certD(5)[OF assms(1) assms(2)[unfolded valid_pos_cert_def] assms(3,4)] assms(5-) by auto

lemma valid_neg_certD:
  assumes "valid_mdp_rp mdp" "valid_neg_cert mdp c" "i < state_count mdp" "states1 mdp !! i"
    "0 < solution c !! i" "witness c !! i = (js, n)"
  shows "list_all2 (\<lambda>j ds. j < state_count mdp \<and> snd (witness c !! j) < n \<and> lookup 0 ds j \<noteq> 0 \<and> 0 < solution c !! j) js (distrs mdp !! i)"
  using valid_sub_certD(5)[OF assms(1) assms(2)[unfolded valid_neg_cert_def] assms(3)] assms(4-) by auto

context
  fixes mdp c
  assumes rp: "valid_mdp_rp mdp"
  assumes cert: "valid_cert mdp c"
begin

interpretation pmf_as_function .

abbreviation "S \<equiv> {..< state_count mdp}"
abbreviation "S1 \<equiv> {i. i < state_count mdp \<and> (states1 mdp) !! i}"
abbreviation "S2 \<equiv> {i. i < state_count mdp \<and> (states2 mdp) !! i}"

lift_definition K :: "nat \<Rightarrow> nat pmf set" is
  "\<lambda>i. if i < state_count mdp then
     { (\<lambda>j. of_rat (lookup 0 D j) :: real) | D. D \<in> set (distrs mdp !! i) }
     else { indicator {0} }"
proof (auto split: if_split_asm simp del: IArray.sub_def)
  fix n D assume n: "n < state_count mdp" and D: "D \<in> set (distrs mdp !! n)"
  from valid_mdp_rpD(3)[OF rp this] show nn: "\<And>i. 0 \<le> lookup 0 D i"
    by (auto simp add: lookup_eq_map_of split: option.split dest: map_of_SomeD)
  show "(\<integral>\<^sup>+ x. ennreal (real_of_rat (lookup 0 D x)) \<partial>count_space UNIV) = 1"
    using valid_mdp_rpD(2,3,4,5)[OF rp n D]
    apply (subst nn_integral_count_space'[of "{..< state_count mdp}"])
    apply (auto intro: nn lookup_not_in_set simp: of_rat_sum[symmetric] lookup_nonneg)
    apply (subst sum_list_eq_sum_lookup[symmetric])
    apply (auto simp: list_all_iff lookup_eq_map_of split: option.split)
    done
next
  show "(\<integral>\<^sup>+ x. ennreal (indicator {0} x) \<partial>count_space UNIV) = 1"
    by (subst nn_integral_count_space'[of "{0}"]) auto
qed

interpretation MDP: Reachability_Problem K S S1 S2
proof
  show "S1 \<inter> S2 = {}" "S1 \<subseteq> S" "S2 \<subseteq> S"
    using valid_mdp_rpD(1)[OF rp] by auto
  show "finite S" "S \<noteq> {}"
    using \<open>valid_mdp_rp mdp\<close> by (auto simp add: valid_mdp_rp_def)
  show "\<And>s. K s \<noteq> {}"
    using valid_mdp_rpD(6)[OF rp] by transfer simp
  show "\<And>s. finite (K s)"
    by transfer simp

  fix s assume "s \<in> S" then show "(\<Union>D\<in>K s. set_pmf D) \<subseteq> S"
    using valid_mdp_rpD(2)[OF rp]
    by transfer (auto simp: lookup_eq_map_of split: option.splits dest!: map_of_SomeD)
qed

definition "P_max s = enn2real (MDP.p s)"
definition "P_min s = enn2real (MDP.n s)"

lemma
  assumes "i < state_count mdp"
  shows P_max: "P_max i \<le> real_of_rat (solution (pos_cert c) !! i)" (is ?max)
    and P_min: "P_min i \<ge> real_of_rat (solution (neg_cert c) !! i)" (is ?min)
proof -
  have "valid_pos_cert mdp (pos_cert c)" "valid_neg_cert mdp (neg_cert c)"
    using \<open>valid_cert mdp c\<close> by (auto simp: valid_cert_def)
  note pos = this(1)[unfolded valid_pos_cert_def] and neg = this(2)[unfolded valid_neg_cert_def]

  let ?x = "\<lambda>s. real_of_rat (solution (pos_cert c) !! s)"
  have "enn2real (MDP.p i) \<le> ?x i"
  proof (rule MDP.p_ub')
    show "i \<in> S" using assms by simp
  next
    fix s D assume "s \<in> S1" "D \<in> K s"
    then obtain j where j: "j < length (distrs mdp !! s)"
      "\<And>i. i < state_count mdp \<Longrightarrow> pmf D i = real_of_rat (lookup 0 (distrs mdp !! s ! j) i)"
      by transfer (auto simp: in_set_conv_nth)
    with valid_sub_certD(4)[OF \<open>valid_mdp_rp mdp\<close> pos, of s "distrs mdp !! s ! j"] \<open>s \<in> S1\<close>
         valid_mdp_rp_sparse_mult[OF \<open>valid_mdp_rp mdp\<close>, of s "distrs mdp !! s ! j" "solution (pos_cert c)"]
    show "(\<Sum>t\<in>S. pmf D t * ?x t) \<le> ?x s"
      by (simp add: of_rat_mult[symmetric] of_rat_sum[symmetric] of_rat_less_eq j)
  next
    fix s a assume "s \<in> S2" then show "?x s = 1"
      using valid_sub_certD[OF \<open>valid_mdp_rp mdp\<close> pos] by simp
  next
    fix s define X where "X = (SIGMA s:S1. \<Union>D\<in>K s. set_pmf D)"
    assume "s \<in> S1" "?x s \<noteq> 0"
    with valid_sub_certD(3)[OF rp pos, of s]
    have "0 < ?x s"
      by simp
    with \<open>s\<in>S1\<close> show "\<exists>t\<in>S2. (s, t) \<in> X\<^sup>*"
    proof (induction n\<equiv>"snd (witness (pos_cert c) !! s)" arbitrary: s rule: less_induct)
      case (less s)
      obtain t a n where eq: "witness (pos_cert c) !! s = ((t, a), n)"
        by (metis prod.exhaust)
      from valid_pos_certD[OF rp \<open>valid_pos_cert mdp (pos_cert c)\<close> _ _ _ this] less.prems
      have ord: "snd (witness (pos_cert c) !! t) < snd (witness (pos_cert c) !! s)"
        and t: "lookup 0 (distrs mdp !! s ! a) t \<noteq> 0" "0 < ?x t" "t\<in>S" "a < length (distrs mdp !! s)"
        unfolding eq by auto
      with \<open>s\<in>S1\<close> have X: "(s, t) \<in> X"
        unfolding X_def
        by (transfer fixing: s t a c)
           (auto simp: X_def in_set_conv_nth
                 intro!: exI[of _ "\<lambda>j. real_of_rat (lookup 0 (distrs mdp !! s ! a) j)"]
                         exI[of _ "distrs mdp !! s ! a"] exI[of _ a])
      show ?case
      proof cases
        assume "t \<in> S1"
        with less.hyps[OF ord _ \<open>0 < ?x t\<close>] X show ?thesis
          by auto
      next
        assume "t \<notin> S1"
        with valid_sub_certD[OF \<open>valid_mdp_rp mdp\<close> pos, of t] \<open>0 < ?x t\<close> \<open>t\<in>S\<close>
        have "t \<in> S2"
          by auto
        with X show ?thesis
          by auto
      qed
    qed
  next
    fix s assume "s \<in> S - S1 - S2" then show "?x s = 0"
      using valid_sub_certD(1)[OF \<open>valid_mdp_rp mdp\<close> pos, of s] by simp
  qed
  then show ?max
    by (simp add: P_max_def)

  let ?x = "\<lambda>s. real_of_rat (solution (neg_cert c) !! s)"
  have "?x i \<le> enn2real (MDP.n i)"
  proof (rule MDP.n_lb')
    show "i \<in> S" using assms by simp
  next
    fix s D assume "s \<in> S1" "D \<in> K s"
    then obtain j where j: "j < length (distrs mdp !! s)"
      "\<And>i. i < state_count mdp \<Longrightarrow> pmf D i = real_of_rat (lookup 0 (distrs mdp !! s ! j) i)"
      by transfer (auto simp: in_set_conv_nth)
    with valid_sub_certD(4)[OF \<open>valid_mdp_rp mdp\<close> neg, of s "distrs mdp !! s ! j"] \<open>s \<in> S1\<close>
         valid_mdp_rp_sparse_mult[OF \<open>valid_mdp_rp mdp\<close>, of s "distrs mdp !! s ! j" "solution (neg_cert c)"]
    show "?x s \<le> (\<Sum>t\<in>S. pmf D t * ?x t)"
      by (simp add: of_rat_mult[symmetric] of_rat_sum[symmetric] of_rat_less_eq j)
  next
    fix s a assume "s \<in> S2" then show "?x s = 1"
      using valid_sub_certD[OF \<open>valid_mdp_rp mdp\<close> neg] by simp
  next
    show "wf ((S \<times> S \<inter> {(s, t). snd (witness (neg_cert c) !! t) < snd (witness (neg_cert c) !! s)})\<inverse>)" (is "wf ?F")
      using MDP.S_finite
      by (intro finite_acyclic_wf_converse acyclicI_order[where f="\<lambda>s. snd (witness (neg_cert c) !! s)"]) auto

    fix s D assume 2: "s \<in> S1" "D \<in> K s" and "?x s \<noteq> 0"
    then have "0 < ?x s"
      using valid_sub_certD(3)[OF \<open>valid_mdp_rp mdp\<close> neg, of s] by auto

    from 2 obtain a where a: "a < length (distrs mdp !! s)"
      "\<And>i. i < state_count mdp \<Longrightarrow> pmf D i = real_of_rat (lookup 0 (distrs mdp !! s ! a) i)"
      by transfer (auto simp: in_set_conv_nth)

    obtain js n where eq: "witness (neg_cert c) !! s = (js, n)"
      by (metis prod.exhaust)
    from valid_neg_certD[OF \<open>valid_mdp_rp mdp\<close> \<open>valid_neg_cert mdp (neg_cert c)\<close> _ _ _ eq] a \<open>s \<in> S1\<close> \<open>0 < ?x s\<close>
    have *: "length js = length (distrs mdp !! s)" "js ! a \<in> S"
      "snd (witness (neg_cert c) !! (js ! a)) < snd (witness (neg_cert c) !! s)"
      "lookup 0 (distrs mdp !! s ! a) (js ! a) \<noteq> 0"
      "0 < ?x (js ! a)"
      unfolding eq by (auto dest: list_all2_nthD2 list_all2_lengthD)
    with a \<open>s \<in> S1\<close> have js_a: "js ! a \<in> D" "(js ! a, s) \<in> ?F"
      by (auto simp: set_pmf_iff)

    show "\<exists>t\<in>D. (t, s) \<in> ?F \<and> t \<in> S1 \<and> ?x t \<noteq> 0 \<or> t \<in> S2"
    proof cases
      assume "js ! a \<in> S1" with js_a \<open>0 < ?x (js ! a)\<close> show ?thesis by auto
    next
      assume "js ! a \<notin> S1"
      with \<open>0 < ?x (js ! a)\<close> \<open>js!a \<in> S\<close> valid_sub_certD[OF rp neg, of "js ! a"]
      have "js ! a \<in> S2"
        by (auto simp:  less_le)
      with \<open>js ! a \<in> D\<close> show ?thesis
        by auto
    qed
  next
    fix s assume "s \<in> S - S1 - S2" then show "?x s = 0"
      using valid_sub_certD(1)[OF \<open>valid_mdp_rp mdp\<close> neg, of s] by simp
  qed
  then show ?min
    by (simp add: P_min_def)
qed

end

end
