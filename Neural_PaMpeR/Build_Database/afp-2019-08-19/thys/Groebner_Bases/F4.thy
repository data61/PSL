(* Author: Alexander Maletzky *)

section \<open>Faug\`ere's F4 Algorithm\<close>

theory F4
  imports Macaulay_Matrix Algorithm_Schema
begin

text \<open>This theory implements Faug\`ere's F4 algorithm based on @{const gd_term.gb_schema_direct}.\<close>

subsection \<open>Symbolic Preprocessing\<close>

context gd_term
begin

definition sym_preproc_aux_term1 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term1 d =
            {((gs1, ks1, ts1, fs1), (gs2::('t \<Rightarrow>\<^sub>0 'b) list, ks2, ts2, fs2)). \<exists>t2\<in>set ts2. \<forall>t1\<in>set ts1. t1 \<prec>\<^sub>t t2}"

definition sym_preproc_aux_term2 :: "('a \<Rightarrow> nat) \<Rightarrow> ((('t \<Rightarrow>\<^sub>0 'b::zero) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) \<times>
                                                (('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)) set"
  where "sym_preproc_aux_term2 d =
            {((gs1, ks1, ts1, fs1), (gs2::('t \<Rightarrow>\<^sub>0 'b) list, ks2, ts2, fs2)). gs1 = gs2 \<and>
                                              dgrad_set_le d (pp_of_term ` set ts1) (pp_of_term ` (Keys (set gs2) \<union> set ts2))}"

definition sym_preproc_aux_term
  where "sym_preproc_aux_term d = sym_preproc_aux_term1 d \<inter> sym_preproc_aux_term2 d"

lemma wfp_on_ord_term_strict:
  assumes "dickson_grading d"
  shows "wfp_on (\<prec>\<^sub>t) (pp_of_term -` dgrad_set d m)"
proof (rule wfp_onI_min)
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> pp_of_term -` dgrad_set d m"
  from wf_dickson_less_v[OF assms, of m] \<open>x \<in> Q\<close> obtain z
    where "z \<in> Q" and *: "\<And>y. dickson_less_v d m y z \<Longrightarrow> y \<notin> Q" by (rule wfE_min[to_pred], blast)
  from this(1) \<open>Q \<subseteq> pp_of_term -` dgrad_set d m\<close> have "z \<in> pp_of_term -` dgrad_set d m" ..
  show "\<exists>z\<in>Q. \<forall>y \<in> pp_of_term -` dgrad_set d m. y \<prec>\<^sub>t z \<longrightarrow> y \<notin> Q"
  proof (intro bexI ballI impI, rule *)
    fix y
    assume "y \<in> pp_of_term -` dgrad_set d m" and "y \<prec>\<^sub>t z"
    from this(1) \<open>z \<in> pp_of_term -` dgrad_set d m\<close> have "d (pp_of_term y) \<le> m" and "d (pp_of_term z) \<le> m"
      by (simp_all add: dgrad_set_def)
    thus "dickson_less_v d m y z" using \<open>y \<prec>\<^sub>t z\<close> by (rule dickson_less_vI)
  qed fact
qed

lemma sym_preproc_aux_term1_wf_on:
  assumes "dickson_grading d"
  shows "wfp_on (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d) {x. set (fst (snd (snd x))) \<subseteq> pp_of_term -` dgrad_set d m}"
proof (rule wfp_onI_min)
  let ?B = "pp_of_term -` dgrad_set d m"
  let ?A = "{x::(('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list). set (fst (snd (snd x))) \<subseteq> ?B}"
  have A_sub_Pow: "set ` fst ` snd ` snd ` ?A \<subseteq> Pow ?B" by auto
  fix x Q
  assume "x \<in> Q" and "Q \<subseteq> ?A"
  let ?Q = "{ord_term_lin.Max (set (fst (snd (snd q)))) | q. q \<in> Q \<and> fst (snd (snd q)) \<noteq> []}"
  show "\<exists>z\<in>Q. \<forall>y\<in>{x. set (fst (snd (snd x))) \<subseteq> ?B}. (y, z) \<in> sym_preproc_aux_term1 d \<longrightarrow> y \<notin> Q"
  proof (cases "\<exists>z\<in>Q. fst (snd (snd z)) = []")
    case True
    then obtain z where "z \<in> Q" and "fst (snd (snd z)) = []" ..
    show ?thesis
    proof (intro bexI ballI impI)
      fix y
      assume "(y, z) \<in> sym_preproc_aux_term1 d"
      then obtain t where "t \<in> set (fst (snd (snd z)))" unfolding sym_preproc_aux_term1_def by auto
      with \<open>fst (snd (snd z)) = []\<close> show "y \<notin> Q" by simp
    qed fact
  next
    case False
    hence *: "q \<in> Q \<Longrightarrow> fst (snd (snd q)) \<noteq> []" for q by blast
    with \<open>x \<in> Q\<close> have "fst (snd (snd x)) \<noteq> []" by simp
    from assms have "wfp_on (\<prec>\<^sub>t) ?B" by (rule wfp_on_ord_term_strict)
    moreover from \<open>x \<in> Q\<close> \<open>fst (snd (snd x)) \<noteq> []\<close>
    have "ord_term_lin.Max (set (fst (snd (snd x)))) \<in> ?Q" by blast
    moreover have "?Q \<subseteq> ?B"
    proof (rule, simp, elim exE conjE, simp)
      fix a b c d0
      assume "(a, b, c, d0) \<in> Q" and "c \<noteq> []"
      from this(1) \<open>Q \<subseteq> ?A\<close> have "(a, b, c, d0) \<in> ?A" ..
      hence "pp_of_term ` set c \<subseteq> dgrad_set d m" by auto
      moreover have "pp_of_term (ord_term_lin.Max (set c)) \<in> pp_of_term ` set c"
      proof
        from \<open>c \<noteq> []\<close> show "ord_term_lin.Max (set c) \<in> set c" by simp
      qed (fact refl)
      ultimately show "pp_of_term (ord_term_lin.Max (set c)) \<in> dgrad_set d m" ..
    qed
    ultimately obtain t where "t \<in> ?Q" and min: "\<And>s. s \<prec>\<^sub>t t \<Longrightarrow> s \<notin> ?Q" by (rule wfp_onE_min) blast
    from this(1) obtain z where "z \<in> Q" and "fst (snd (snd z)) \<noteq> []"
      and t: "t = ord_term_lin.Max (set (fst (snd (snd z))))" by blast
    show ?thesis
    proof (intro bexI ballI impI, rule)
      fix y
      assume "y \<in> ?A" and "(y, z) \<in> sym_preproc_aux_term1 d" and "y \<in> Q"
      from this(2) obtain t' where "t' \<in> set (fst (snd (snd z)))"
        and **: "\<And>s. s \<in> set (fst (snd (snd y))) \<Longrightarrow> s \<prec>\<^sub>t t'"
        unfolding sym_preproc_aux_term1_def by auto
      from \<open>y \<in> Q\<close> have "fst (snd (snd y)) \<noteq> []" by (rule *)
      with \<open>y \<in> Q\<close> have "ord_term_lin.Max (set (fst (snd (snd y)))) \<in> ?Q" (is "?s \<in> _")
        by blast
      from \<open>fst (snd (snd y)) \<noteq> []\<close> have "?s \<in> set (fst (snd (snd y)))" by simp
      hence "?s \<prec>\<^sub>t t'" by (rule **)
      also from \<open>t' \<in> set (fst (snd (snd z)))\<close> have "t' \<preceq>\<^sub>t t" unfolding t
        using \<open>fst (snd (snd z)) \<noteq> []\<close> by simp
      finally have "?s \<notin> ?Q" by (rule min)
      from this \<open>?s \<in> ?Q\<close> show False ..
    qed fact
  qed
qed

lemma sym_preproc_aux_term_wf:
  assumes "dickson_grading d"
  shows "wf (sym_preproc_aux_term d)"
proof (rule wfI_min)
  fix x::"(('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)" and Q
  assume "x \<in> Q"
  let ?A = "Keys (set (fst x)) \<union> set (fst (snd (snd x)))"
  have "finite ?A" by (simp add: finite_Keys)
  hence "finite (pp_of_term ` ?A)" by (rule finite_imageI)
  then obtain m where "pp_of_term ` ?A \<subseteq> dgrad_set d m" by (rule dgrad_set_exhaust)
  hence A: "?A \<subseteq> pp_of_term -` dgrad_set d m" by blast
  let ?B = "pp_of_term -` dgrad_set d m"
  let ?Q = "{q \<in> Q. Keys (set (fst q)) \<union> set (fst (snd (snd q))) \<subseteq> ?B}"
  from assms have "wfp_on (\<lambda>x y. (x, y) \<in> sym_preproc_aux_term1 d) {x. set (fst (snd (snd x))) \<subseteq> ?B}"
    by (rule sym_preproc_aux_term1_wf_on)
  moreover from \<open>x \<in> Q\<close> A have "x \<in> ?Q" by simp
  moreover have "?Q \<subseteq> {x. set (fst (snd (snd x))) \<subseteq> ?B}" by auto
  ultimately obtain z where "z \<in> ?Q"
    and *: "\<And>y. (y, z) \<in> sym_preproc_aux_term1 d \<Longrightarrow> y \<notin> ?Q" by (rule wfp_onE_min) blast
  from this(1) have "z \<in> Q" and "Keys (set (fst z)) \<union> set (fst (snd (snd z))) \<subseteq> ?B" by simp_all
  from this(2) have a: "pp_of_term ` (Keys (set (fst z)) \<union> set (fst (snd (snd z)))) \<subseteq> dgrad_set d m"
    by blast
  show "\<exists>z\<in>Q. \<forall>y. (y, z) \<in> sym_preproc_aux_term d \<longrightarrow> y \<notin> Q"
  proof (intro bexI allI impI)
    fix y
    assume "(y, z) \<in> sym_preproc_aux_term d"
    hence "(y, z) \<in> sym_preproc_aux_term1 d" and "(y, z) \<in> sym_preproc_aux_term2 d"
      by (simp_all add: sym_preproc_aux_term_def)
    from this(2) have "fst y = fst z"
      and "dgrad_set_le d (pp_of_term ` set (fst (snd (snd y)))) (pp_of_term ` (Keys (set (fst z)) \<union> set (fst (snd (snd z)))))"
      by (auto simp add: sym_preproc_aux_term2_def)
    from this(2) a have "pp_of_term ` (set (fst (snd (snd y)))) \<subseteq> dgrad_set d m"
      by (rule dgrad_set_le_dgrad_set)
    hence "Keys (set (fst y)) \<union> set (fst (snd (snd y))) \<subseteq> ?B"
      using a by (auto simp add: \<open>fst y = fst z\<close>)
    moreover from \<open>(y, z) \<in> sym_preproc_aux_term1 d\<close> have "y \<notin> ?Q" by (rule *)
    ultimately show "y \<notin> Q" by simp
  qed fact
qed

primrec sym_preproc_addnew :: "('t \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> 't list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> 't \<Rightarrow>
                              ('t list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)" where
  "sym_preproc_addnew [] vs fs _ = (vs, fs)"|
  "sym_preproc_addnew (g # gs) vs fs v =
    (if lt g adds\<^sub>t v then
      (let f = monom_mult 1 (pp_of_term v - lp g) g in
        sym_preproc_addnew gs (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f))) (insert_list f fs) v
      )
    else
      sym_preproc_addnew gs vs fs v
    )"

lemma fst_sym_preproc_addnew_less:
  assumes "\<And>u. u \<in> set vs \<Longrightarrow> u \<prec>\<^sub>t v"
    and "u \<in> set (fst (sym_preproc_addnew gs vs fs v))"
  shows "u \<prec>\<^sub>t v"
  using assms
proof (induct gs arbitrary: fs vs)
  case Nil
  from Nil(2) have "u \<in> set vs" by simp
  thus ?case by (rule Nil(1))
next
  case (Cons g gs)
  from Cons(3) show ?case
  proof (simp add: Let_def split: if_splits)
    let ?t = "pp_of_term v - lp g"
    assume "lt g adds\<^sub>t v"
    assume "u \<in> set (fst (sym_preproc_addnew gs
                                (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail (monom_mult 1 ?t g))))
                                (insert_list (monom_mult 1 ?t g) fs) v))"
    with _ show ?thesis
    proof (rule Cons(1))
      fix u
      assume "u \<in> set (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail (monom_mult 1 ?t g))))"
      hence "u \<in> set vs \<or> u \<in> keys (tail (monom_mult 1 ?t g))"
        by (simp add: set_merge_wrt keys_to_list_def set_pps_to_list)
      thus "u \<prec>\<^sub>t v"
      proof
        assume "u \<in> set vs"
        thus ?thesis by (rule Cons(2))
      next
        assume "u \<in> keys (tail (monom_mult 1 ?t g))"
        hence "u \<prec>\<^sub>t lt (monom_mult 1 ?t g)" by (rule keys_tail_less_lt)
        also have "... \<preceq>\<^sub>t ?t \<oplus> lt g" by (rule lt_monom_mult_le)
        also from \<open>lt g adds\<^sub>t v\<close> have "... = v"
          by (metis add_diff_cancel_right' adds_termE pp_of_term_splus)
        finally show ?thesis .
      qed
    qed
  next
    assume "u \<in> set (fst (sym_preproc_addnew gs vs fs v))"
    with Cons(2) show ?thesis by (rule Cons(1))
  qed
qed

lemma fst_sym_preproc_addnew_dgrad_set_le:
  assumes "dickson_grading d"
  shows "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs vs fs v))) (pp_of_term ` (Keys (set gs) \<union> insert v (set vs)))"
proof (induct gs arbitrary: fs vs)
  case Nil
  show ?case by (auto intro: dgrad_set_le_subset)
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    assume "lt g adds\<^sub>t v"
    let ?t = "pp_of_term v - lp g"
    let ?vs = "merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail (monom_mult 1 ?t g)))"
    let ?fs = "insert_list (monom_mult 1 ?t g) fs"
    from Cons have "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs ?vs ?fs v)))
                                    (pp_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs)))"
    proof (rule dgrad_set_le_trans)
      show "dgrad_set_le d (pp_of_term ` (Keys (set gs) \<union> insert v (set ?vs)))
                            (pp_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs)))"
        unfolding dgrad_set_le_def set_merge_wrt set_keys_to_list
      proof (intro ballI)
        fix s
        assume "s \<in> pp_of_term ` (Keys (set gs) \<union> insert v (set vs \<union> keys (tail (monom_mult 1 ?t g))))"
        hence "s \<in> pp_of_term ` (Keys (set gs) \<union> insert v (set vs)) \<union> pp_of_term ` keys (tail (monom_mult 1 ?t g))"
          by auto
        thus "\<exists>t \<in> pp_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs)). d s \<le> d t"
        proof
          assume "s \<in> pp_of_term ` (Keys (set gs) \<union> insert v (set vs))"
          thus ?thesis by (auto simp add: Keys_insert)
        next
          assume "s \<in> pp_of_term ` keys (tail (monom_mult 1 ?t g))"
          hence "s \<in> pp_of_term ` keys (monom_mult 1 ?t g)" by (auto simp add: keys_tail)
          from this keys_monom_mult_subset have "s \<in> pp_of_term ` (\<oplus>) ?t ` keys g" by blast
          then obtain u where "u \<in> keys g" and s: "s = pp_of_term (?t \<oplus> u)" by blast
          have "d s = d ?t \<or> d s = d (pp_of_term u)" unfolding s pp_of_term_splus
            using dickson_gradingD1[OF assms] by auto
          thus ?thesis
          proof
            from \<open>lt g adds\<^sub>t v\<close> have "lp g adds pp_of_term v" by (simp add: adds_term_def)
            assume "d s = d ?t"
            also from assms \<open>lp g adds pp_of_term v\<close> have "... \<le> d (pp_of_term v)"
              by (rule dickson_grading_minus)
            finally show ?thesis by blast
          next
            assume "d s = d (pp_of_term u)"
            moreover from \<open>u \<in> keys g\<close> have "u \<in> Keys (insert g (set gs))" by (simp add: Keys_insert)
            ultimately show ?thesis by auto
          qed
        qed
      qed
    qed
    thus "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs ?vs ?fs v)))
                        (insert (pp_of_term v) (pp_of_term ` (Keys (insert g (set gs)) \<union> set vs)))"
      by simp
  next
    from Cons show "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs vs fs v)))
                           (insert (pp_of_term v) (pp_of_term ` (Keys (insert g (set gs)) \<union> set vs)))"
    proof (rule dgrad_set_le_trans)
      show "dgrad_set_le d (pp_of_term ` (Keys (set gs) \<union> insert v (set vs)))
                          (insert (pp_of_term v) (pp_of_term ` (Keys (insert g (set gs)) \<union> set vs)))"
        by (rule dgrad_set_le_subset, auto simp add: Keys_def)
    qed
  qed
qed

lemma components_fst_sym_preproc_addnew_subset:
  "component_of_term ` set (fst (sym_preproc_addnew gs vs fs v)) \<subseteq> component_of_term ` (Keys (set gs) \<union> insert v (set vs))"
proof (induct gs arbitrary: fs vs)
  case Nil
  show ?case by (auto intro: dgrad_set_le_subset)
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    assume "lt g adds\<^sub>t v"
    let ?t = "pp_of_term v - lp g"
    let ?vs = "merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail (monom_mult 1 ?t g)))"
    let ?fs = "insert_list (monom_mult 1 ?t g) fs"
    from Cons have "component_of_term ` set (fst (sym_preproc_addnew gs ?vs ?fs v)) \<subseteq>
                     component_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs))"
    proof (rule subset_trans)
      show "component_of_term ` (Keys (set gs) \<union> insert v (set ?vs)) \<subseteq>
             component_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs))"
        unfolding set_merge_wrt set_keys_to_list
      proof
        fix k
        assume "k \<in> component_of_term ` (Keys (set gs) \<union> insert v (set vs \<union> keys (tail (monom_mult 1 ?t g))))"
        hence "k \<in> component_of_term ` (Keys (set gs) \<union> insert v (set vs)) \<union> component_of_term ` keys (tail (monom_mult 1 ?t g))"
          by auto
        thus "k \<in> component_of_term ` (Keys (insert g (set gs)) \<union> insert v (set vs))"
        proof
          assume "k \<in> component_of_term ` (Keys (set gs) \<union> insert v (set vs))"
          thus ?thesis by (auto simp add: Keys_insert)
        next
          assume "k \<in> component_of_term ` keys (tail (monom_mult 1 ?t g))"
          hence "k \<in> component_of_term ` keys (monom_mult 1 ?t g)" by (auto simp add: keys_tail)
          from this keys_monom_mult_subset have "k \<in> component_of_term ` (\<oplus>) ?t ` keys g" by blast
          also have "... \<subseteq> component_of_term ` keys g" using component_of_term_splus by fastforce
          finally show ?thesis by (simp add: image_Un Keys_insert)
        qed
      qed
    qed
    thus "component_of_term ` set (fst (sym_preproc_addnew gs ?vs ?fs v)) \<subseteq>
           insert (component_of_term v) (component_of_term ` (Keys (insert g (set gs)) \<union> set vs))"
      by simp
  next
    from Cons show "component_of_term ` set (fst (sym_preproc_addnew gs vs fs v)) \<subseteq>
                insert (component_of_term v) (component_of_term ` (Keys (insert g (set gs)) \<union> set vs))"
    proof (rule subset_trans)
      show "component_of_term ` (Keys (set gs) \<union> insert v (set vs)) \<subseteq>
             insert (component_of_term v) (component_of_term ` (Keys (insert g (set gs)) \<union> set vs))"
        by (auto simp add: Keys_def)
    qed
  qed
qed

lemma fst_sym_preproc_addnew_superset: "set vs \<subseteq> set (fst (sym_preproc_addnew gs vs fs v))"
proof (induct gs arbitrary: vs fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    let ?t = "pp_of_term v - lp g"
    define f where "f = monom_mult 1 ?t g"
    have "set vs \<subseteq> set (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f)))" by (auto simp add: set_merge_wrt)
    thus "set vs \<subseteq> set (fst (sym_preproc_addnew gs
                              (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f))) (insert_list f fs) v))"
      using Cons by (rule subset_trans)
  next
    show "set vs \<subseteq> set (fst (sym_preproc_addnew gs vs fs v))" by (fact Cons)
  qed
qed

lemma snd_sym_preproc_addnew_superset: "set fs \<subseteq> set (snd (sym_preproc_addnew gs vs fs v))"
proof (induct gs arbitrary: vs fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  show ?case
  proof (simp add: Let_def, intro conjI impI)
    let ?t = "pp_of_term v - lp g"
    define f where "f = monom_mult 1 ?t g"
    have "set fs \<subseteq> set (insert_list f fs)" by (auto simp add: set_insert_list)
    thus "set fs \<subseteq> set (snd (sym_preproc_addnew gs
                              (merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f))) (insert_list f fs) v))"
      using Cons by (rule subset_trans)
  next
    show "set fs \<subseteq> set (snd (sym_preproc_addnew gs vs fs v))" by (fact Cons)
  qed
qed

lemma in_snd_sym_preproc_addnewE:
  assumes "p \<in> set (snd (sym_preproc_addnew gs vs fs v))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g s. g \<in> set gs \<Longrightarrow> p = monom_mult 1 s g \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct gs arbitrary: vs fs thesis)
  case Nil
  from Nil(1) have "p \<in> set fs" by simp
  thus ?case by (rule Nil(2))
next
  case (Cons g gs)
  from Cons(2) show ?case
  proof (simp add: Let_def split: if_splits)
    define f where "f = monom_mult 1 (pp_of_term v - lp g) g"
    define ts' where "ts' = merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f))"
    define fs' where "fs' = insert_list f fs"
    assume "p \<in> set (snd (sym_preproc_addnew gs ts' fs' v))"
    thus ?thesis
    proof (rule Cons(1))
      assume "p \<in> set fs'"
      hence "p = f \<or> p \<in> set fs" by (simp add: fs'_def set_insert_list)
      thus ?thesis
      proof
        assume "p = f"
        have "g \<in> set (g # gs)" by simp
        from this \<open>p = f\<close> show ?thesis unfolding f_def by (rule Cons(4))
      next
        assume "p \<in> set fs"
        thus ?thesis by (rule Cons(3))
      qed
    next
      fix h s
      assume "h \<in> set gs"
      hence "h \<in> set (g # gs)" by simp
      moreover assume "p = monom_mult 1 s h"
      ultimately show thesis by (rule Cons(4))
    qed
  next
    assume "p \<in> set (snd (sym_preproc_addnew gs vs fs v))"
    moreover note Cons(3)
    moreover have "h \<in> set gs \<Longrightarrow> p = monom_mult 1 s h \<Longrightarrow> thesis" for h s
    proof -
      assume "h \<in> set gs"
      hence "h \<in> set (g # gs)" by simp
      moreover assume "p = monom_mult 1 s h"
      ultimately show thesis by (rule Cons(4))
    qed
    ultimately show ?thesis by (rule Cons(1))
  qed
qed

lemma sym_preproc_addnew_pmdl:
  "pmdl (set gs \<union> set (snd (sym_preproc_addnew gs vs fs v))) = pmdl (set gs \<union> set fs)"
    (is "pmdl (set gs \<union> ?l) = ?r")
proof
  have "set gs \<subseteq> set gs \<union> set fs" by simp
  also have "... \<subseteq> ?r" by (fact pmdl.span_superset)
  finally have "set gs \<subseteq> ?r" .
  moreover have "?l \<subseteq> ?r"
  proof
    fix p
    assume "p \<in> ?l"
    thus "p \<in> ?r"
    proof (rule in_snd_sym_preproc_addnewE)
      assume "p \<in> set fs"
      hence "p \<in> set gs \<union> set fs" by simp
      thus ?thesis by (rule pmdl.span_base)
    next
      fix g s
      assume "g \<in> set gs" and p: "p = monom_mult 1 s g"
      from this(1) \<open>set gs \<subseteq> ?r\<close> have "g \<in> ?r" ..
      thus ?thesis unfolding p by (rule pmdl_closed_monom_mult)
    qed
  qed
  ultimately have "set gs \<union> ?l \<subseteq> ?r" by blast
  thus "pmdl (set gs \<union> ?l) \<subseteq> ?r" by (rule pmdl.span_subset_spanI)
next
  from snd_sym_preproc_addnew_superset have "set gs \<union> set fs \<subseteq> set gs \<union> ?l" by blast
  thus "?r \<subseteq> pmdl (set gs \<union> ?l)" by (rule pmdl.span_mono)
qed

lemma Keys_snd_sym_preproc_addnew:
  "Keys (set (snd (sym_preproc_addnew gs vs fs v))) \<union> insert v (set vs) =
   Keys (set fs) \<union> insert v (set (fst (sym_preproc_addnew gs vs (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list) v)))"
proof (induct gs arbitrary: vs fs)
  case Nil
  show ?case by simp
next
  case (Cons g gs)
  from Cons have eq: "insert v (Keys (set (snd (sym_preproc_addnew gs ts' fs' v))) \<union> set ts') =
                      insert v (Keys (set fs') \<union> set (fst (sym_preproc_addnew gs ts' fs' v)))"
    for ts' fs' by simp
  show ?case
  proof (simp add: Let_def eq, rule)
    assume "lt g adds\<^sub>t v"
    let ?t = "pp_of_term v - lp g"
    define f where "f = monom_mult 1 ?t g"
    define ts' where "ts' = merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail f))"
    define fs' where "fs' = insert_list f fs"
    have "keys (tail f) = keys f - {v}"
    proof (cases "g = 0")
      case True
      hence "f = 0" by (simp add: f_def)
      thus ?thesis by simp
    next
      case False
      hence "lt f = ?t \<oplus> lt g" by (simp add: f_def lt_monom_mult)
      also from \<open>lt g adds\<^sub>t v\<close> have "... = v"
        by (metis add_diff_cancel_right' adds_termE pp_of_term_splus)
      finally show ?thesis by (simp add: keys_tail)
    qed
    hence ts': "set ts' = set vs \<union> (keys f - {v})"
      by (simp add: ts'_def set_merge_wrt set_keys_to_list)
    have fs': "set fs' = insert f (set fs)" by (simp add: fs'_def set_insert_list)
    hence "f \<in> set fs'" by simp
    from this snd_sym_preproc_addnew_superset have "f \<in> set (snd (sym_preproc_addnew gs ts' fs' v))" ..
    hence "keys f \<subseteq> Keys (set (snd (sym_preproc_addnew gs ts' fs' v)))" by (rule keys_subset_Keys)
    hence "insert v (Keys (set (snd (sym_preproc_addnew gs ts' fs' v))) \<union> set vs) =
          insert v (Keys (set (snd (sym_preproc_addnew gs ts' fs' v))) \<union> set ts')"
      by (auto simp add: ts')
    also have "... = insert v (Keys (set fs') \<union> set (fst (sym_preproc_addnew gs ts' fs' v)))"
      by (fact eq)
    also have "... = insert v (Keys (set fs) \<union> set (fst (sym_preproc_addnew gs ts' fs' v)))"
    proof -
      {
        fix u
        assume "u \<noteq> v" and "u \<in> keys f"
        hence "u \<in> set ts'" by (simp add: ts')
        from this fst_sym_preproc_addnew_superset have "u \<in> set (fst (sym_preproc_addnew gs ts' fs' v))" ..
      }
      thus ?thesis by (auto simp add: fs' Keys_insert)
    qed
    finally show "insert v (Keys (set (snd (sym_preproc_addnew gs ts' fs' v))) \<union> set vs) =
                  insert v (Keys (set fs) \<union> set (fst (sym_preproc_addnew gs ts' fs' v)))" .
  qed
qed

lemma sym_preproc_addnew_complete:
  assumes "g \<in> set gs" and "lt g adds\<^sub>t v"
  shows "monom_mult 1 (pp_of_term v - lp g) g \<in> set (snd (sym_preproc_addnew gs vs fs v))"
  using assms(1)
proof (induct gs arbitrary: vs fs)
  case Nil
  thus ?case by simp
next
  case (Cons h gs)
  let ?t = "pp_of_term v - lp g"
  show ?case
  proof (cases "h = g")
    case True
    show ?thesis
    proof (simp add: True assms(2) Let_def)
      define f where "f = monom_mult 1 ?t g"
      define ts' where "ts' = merge_wrt (\<succ>\<^sub>t) vs (keys_to_list (tail (monom_mult 1 ?t g)))"
      have "f \<in> set (insert_list f fs)" by (simp add: set_insert_list)
      with snd_sym_preproc_addnew_superset show "f \<in> set (snd (sym_preproc_addnew gs ts' (insert_list f fs) v))" ..
    qed
  next
    case False
    with Cons(2) have "g \<in> set gs" by simp
    hence *: "monom_mult 1 ?t g \<in> set (snd (sym_preproc_addnew gs ts' fs' v))" for ts' fs'
      by (rule Cons(1))
    show ?thesis by (simp add: Let_def *)
  qed
qed

function sym_preproc_aux :: "('t \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> 't list \<Rightarrow> ('t list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) \<Rightarrow>
                              ('t list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)" where
  "sym_preproc_aux gs ks (vs, fs) =
    (if vs = [] then
      (ks, fs)
    else
      let v = ord_term_lin.max_list vs; vs' = removeAll v vs in
        sym_preproc_aux gs (ks @ [v]) (sym_preproc_addnew gs vs' fs v)
    )"
  by pat_completeness auto
termination proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  let ?R = "(sym_preproc_aux_term d)::((('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) set"
  show ?thesis
  proof
    from dg show "wf ?R" by (rule sym_preproc_aux_term_wf)
  next
    fix gs::"('t \<Rightarrow>\<^sub>0 'b) list" and ks vs fs v vs'
    assume "vs \<noteq> []" and "v = ord_term_lin.max_list vs" and vs': "vs' = removeAll v vs"
    from this(1, 2) have v: "v = ord_term_lin.Max (set vs)"
      by (simp add: ord_term_lin.max_list_Max)
    obtain vs0 fs0 where eq: "sym_preproc_addnew gs vs' fs v = (vs0, fs0)" by fastforce
    show "((gs, ks @ [v], sym_preproc_addnew gs vs' fs v), (gs, ks, vs, fs)) \<in> ?R"
    proof (simp add: eq sym_preproc_aux_term_def sym_preproc_aux_term1_def sym_preproc_aux_term2_def,
           intro conjI bexI ballI)
      fix w
      assume "w \<in> set vs0"
      show "w \<prec>\<^sub>t v"
      proof (rule fst_sym_preproc_addnew_less)
        fix u
        assume "u \<in> set vs'"
        thus "u \<prec>\<^sub>t v" unfolding vs' v set_removeAll using ord_term_lin.antisym_conv1 by fastforce
      next
        from \<open>w \<in> set vs0\<close> show "w \<in> set (fst (sym_preproc_addnew gs vs' fs v))" by (simp add: eq)
      qed
    next
      from \<open>vs \<noteq> []\<close> show "v \<in> set vs" by (simp add: v)
    next
      from dg have "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs vs' fs v)))
                                    (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
        by (rule fst_sym_preproc_addnew_dgrad_set_le)
      moreover have "insert v (set vs') = set vs" by (auto simp add: vs' v \<open>vs \<noteq> []\<close>)
      ultimately show "dgrad_set_le d (pp_of_term ` set vs0) (pp_of_term ` (Keys (set gs) \<union> set vs))"
        by (simp add: eq)
    qed
  qed
qed

lemma sym_preproc_aux_Nil: "sym_preproc_aux gs ks ([], fs) = (ks, fs)"
  by simp

lemma sym_preproc_aux_sorted:
  assumes "sorted_wrt (\<succ>\<^sub>t) (v # vs)"
  shows "sym_preproc_aux gs ks (v # vs, fs) = sym_preproc_aux gs (ks @ [v]) (sym_preproc_addnew gs vs fs v)"
proof -
  from assms have *: "u \<in> set vs \<Longrightarrow> u \<prec>\<^sub>t v" for u by simp
  have "ord_term_lin.max_list (v # vs) = ord_term_lin.Max (set (v # vs))"
    by (simp add: ord_term_lin.max_list_Max del: ord_term_lin.max_list.simps)
  also have "... = v"
  proof (rule ord_term_lin.Max_eqI)
    fix s
    assume "s \<in> set (v # vs)"
    hence "s = v \<or> s \<in> set vs" by simp
    thus "s \<preceq>\<^sub>t v"
    proof
      assume "s = v"
      thus ?thesis by simp
    next
      assume "s \<in> set vs"
      hence "s \<prec>\<^sub>t v" by (rule *)
      thus ?thesis by simp
    qed
  next
    show "v \<in> set (v # vs)" by simp
  qed rule
  finally have eq1: "ord_term_lin.max_list (v # vs) = v" .
  have eq2: "removeAll v (v # vs) = vs"
  proof (simp, rule removeAll_id, rule)
    assume "v \<in> set vs"
    hence "v \<prec>\<^sub>t v" by (rule *)
    thus False ..
  qed
  show ?thesis by (simp only: sym_preproc_aux.simps eq1 eq2 Let_def, simp)
qed

lemma sym_preproc_aux_induct [consumes 0, case_names base rec]:
  assumes base: "\<And>ks fs. P ks [] fs (ks, fs)"
    and rec: "\<And>ks vs fs v vs'. vs \<noteq> [] \<Longrightarrow> v = ord_term_lin.Max (set vs) \<Longrightarrow> vs' = removeAll v vs \<Longrightarrow>
                P (ks @ [v]) (fst (sym_preproc_addnew gs vs' fs v)) (snd (sym_preproc_addnew gs vs' fs v))
                    (sym_preproc_aux gs (ks @ [v]) (sym_preproc_addnew gs vs' fs v)) \<Longrightarrow>
                P ks vs fs (sym_preproc_aux gs (ks @ [v]) (sym_preproc_addnew gs vs' fs v))"
  shows "P ks vs fs (sym_preproc_aux gs ks (vs, fs))"
proof -
  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  let ?R = "(sym_preproc_aux_term d)::((('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) \<times>
                                        ('t \<Rightarrow>\<^sub>0 'b) list \<times> 't list \<times> 't list \<times> ('t \<Rightarrow>\<^sub>0 'b) list) set"
  define args where "args = (gs, ks, vs, fs)"
  from dg have "wf ?R" by (rule sym_preproc_aux_term_wf)
  hence "fst args = gs \<Longrightarrow> P (fst (snd args)) (fst (snd (snd args))) (snd (snd (snd args)))
                              (sym_preproc_aux gs (fst (snd args)) (snd (snd args)))"
  proof induct
    fix x
    assume IH': "\<And>y. (y, x) \<in> sym_preproc_aux_term d \<Longrightarrow> fst y = gs \<Longrightarrow>
                    P (fst (snd y)) (fst (snd (snd y))) (snd (snd (snd y)))
                      (sym_preproc_aux gs (fst (snd y)) (snd (snd y)))"
    assume "fst x = gs"
    then obtain x0 where x: "x = (gs, x0)" by (meson eq_fst_iff)
    obtain ks x1 where x0: "x0 = (ks, x1)" by (meson case_prodE case_prodI2)
    obtain vs fs where x1: "x1 = (vs, fs)" by (meson case_prodE case_prodI2)
    from IH' have IH: "\<And>ks' n. ((gs, ks', n), (gs, ks, vs, fs)) \<in> sym_preproc_aux_term d \<Longrightarrow>
                            P ks' (fst n) (snd n) (sym_preproc_aux gs ks' n)"
      unfolding x x0 x1 by fastforce
    show "P (fst (snd x)) (fst (snd (snd x))) (snd (snd (snd x)))
            (sym_preproc_aux gs (fst (snd x)) (snd (snd x)))"
    proof (simp add: x x0 x1 Let_def, intro conjI impI)
      show "P ks [] fs (ks, fs)" by (fact base)
    next
      assume "vs \<noteq> []"
      define v where "v = ord_term_lin.max_list vs"
      from \<open>vs \<noteq> []\<close> have v_alt: "v = ord_term_lin.Max (set vs)" unfolding v_def
        by (rule ord_term_lin.max_list_Max)
      define vs' where "vs' = removeAll v vs"
      show "P ks vs fs (sym_preproc_aux gs (ks @ [v]) (sym_preproc_addnew gs vs' fs v))"
      proof (rule rec, fact \<open>vs \<noteq> []\<close>, fact v_alt, fact vs'_def)
        let ?n = "sym_preproc_addnew gs vs' fs v"
        obtain vs0 fs0 where eq: "?n = (vs0, fs0)" by fastforce
        show "P (ks @ [v]) (fst ?n) (snd ?n) (sym_preproc_aux gs (ks @ [v]) ?n)"
        proof (rule IH,
              simp add: eq sym_preproc_aux_term_def sym_preproc_aux_term1_def sym_preproc_aux_term2_def,
              intro conjI bexI ballI)
          fix s
          assume "s \<in> set vs0"
          show "s \<prec>\<^sub>t v"
          proof (rule fst_sym_preproc_addnew_less)
            fix u
            assume "u \<in> set vs'"
            thus "u \<prec>\<^sub>t v" unfolding vs'_def v_alt set_removeAll using ord_term_lin.antisym_conv1
              by fastforce
          next
            from \<open>s \<in> set vs0\<close> show "s \<in> set (fst (sym_preproc_addnew gs vs' fs v))" by (simp add: eq)
          qed
        next
          from \<open>vs \<noteq> []\<close> show "v \<in> set vs" by (simp add: v_alt)
        next
          from dg have "dgrad_set_le d (pp_of_term ` set (fst (sym_preproc_addnew gs vs' fs v)))
                                        (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
            by (rule fst_sym_preproc_addnew_dgrad_set_le)
          moreover have "insert v (set vs') = set vs" by (auto simp add: vs'_def v_alt \<open>vs \<noteq> []\<close>)
          ultimately show "dgrad_set_le d (pp_of_term ` set vs0) (pp_of_term ` (Keys (set gs) \<union> set vs))"
            by (simp add: eq)
        qed
      qed
    qed
  qed
  thus ?thesis by (simp add: args_def)
qed

lemma fst_sym_preproc_aux_sorted_wrt:
  assumes "sorted_wrt (\<succ>\<^sub>t) ks" and "\<And>k v. k \<in> set ks \<Longrightarrow> v \<in> set vs \<Longrightarrow> v \<prec>\<^sub>t k"
  shows "sorted_wrt (\<succ>\<^sub>t) (fst (sym_preproc_aux gs ks (vs, fs)))"
  using assms
proof (induct gs ks vs fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(1) show ?case by simp
next
  case (rec ks vs fs v vs')
  from rec(1) have "v \<in> set vs" by (simp add: rec(2))
  from rec(1) have *: "\<And>u. u \<in> set vs' \<Longrightarrow> u \<prec>\<^sub>t v" unfolding rec(2, 3) set_removeAll
    using ord_term_lin.antisym_conv3 by force
  show ?case
  proof (rule rec(4))
    show "sorted_wrt (\<succ>\<^sub>t) (ks @ [v])"
    proof (simp add: sorted_wrt_append rec(5), rule)
      fix k
      assume "k \<in> set ks"
      from this \<open>v \<in> set vs\<close> show "v \<prec>\<^sub>t k" by (rule rec(6))
    qed
  next
    fix k u
    assume "k \<in> set (ks @ [v])" and "u \<in> set (fst (sym_preproc_addnew gs vs' fs v))"
    from * this(2) have "u \<prec>\<^sub>t v" by (rule fst_sym_preproc_addnew_less)
    from \<open>k \<in> set (ks @ [v])\<close> have "k \<in> set ks \<or> k = v" by auto
    thus "u \<prec>\<^sub>t k"
    proof
      assume "k \<in> set ks"
      from this \<open>v \<in> set vs\<close> have "v \<prec>\<^sub>t k" by (rule rec(6))
      with \<open>u \<prec>\<^sub>t v\<close> show ?thesis by simp
    next
      assume "k = v"
      with \<open>u \<prec>\<^sub>t v\<close> show ?thesis by simp
    qed
  qed
qed

lemma fst_sym_preproc_aux_complete:
  assumes "Keys (set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)) = set ks \<union> set vs"
  shows "set (fst (sym_preproc_aux gs ks (vs, fs))) = Keys (set (snd (sym_preproc_aux gs ks (vs, fs))))"
  using assms
proof (induct gs ks vs fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  thus ?case by simp
next
  case (rec ks vs fs v vs')
  from rec(1) have "v \<in> set vs" by (simp add: rec(2))
  hence eq: "insert v (set vs') = set vs" by (auto simp add: rec(3))
  also from rec(5) have "... \<subseteq> Keys (set fs)" by simp
  also from snd_sym_preproc_addnew_superset have "... \<subseteq> Keys (set (snd (sym_preproc_addnew gs vs' fs v)))"
    by (rule Keys_mono)
  finally have "... = ... \<union> (insert v (set vs'))" by blast
  also have "... = Keys (set fs) \<union> insert v (set (fst (sym_preproc_addnew gs vs' fs v)))"
    by (fact Keys_snd_sym_preproc_addnew)
  also have "... = (set ks \<union> (insert v (set vs'))) \<union> (insert v (set (fst (sym_preproc_addnew gs vs' fs v))))"
    by (simp only: rec(5) eq)
  also have "... = set (ks @ [v]) \<union> (set vs' \<union> set (fst (sym_preproc_addnew gs vs' fs v)))" by auto
  also from fst_sym_preproc_addnew_superset have "... = set (ks @ [v]) \<union> set (fst (sym_preproc_addnew gs vs' fs v))"
    by blast
  finally show ?case by (rule rec(4))
qed

lemma snd_sym_preproc_aux_superset: "set fs \<subseteq> set (snd (sym_preproc_aux gs ks (vs, fs)))"
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by simp
next
  case (rec ks vs fs v vs')
  from snd_sym_preproc_addnew_superset rec(4) show ?case by (rule subset_trans)
qed

lemma in_snd_sym_preproc_auxE:
  assumes "p \<in> set (snd (sym_preproc_aux gs ks (vs, fs)))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms
proof (induct gs ks vs fs arbitrary: thesis rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(1) have "p \<in> set fs" by simp
  thus ?case by (rule base(2))
next
  case (rec ks vs fs v vs')
  from rec(5) show ?case
  proof (rule rec(4))
    assume "p \<in> set (snd (sym_preproc_addnew gs vs' fs v))"
    thus ?thesis
    proof (rule in_snd_sym_preproc_addnewE)
      assume "p \<in> set fs"
      thus ?thesis by (rule rec(6))
    next
      fix g s
      assume "g \<in> set gs" and "p = monom_mult 1 s g"
      thus ?thesis by (rule rec(7))
    qed
  next
    fix g t
    assume "g \<in> set gs" and "p = monom_mult 1 t g"
    thus ?thesis by (rule rec(7))
  qed
qed

lemma snd_sym_preproc_aux_pmdl:
  "pmdl (set gs \<union> set (snd (sym_preproc_aux gs ks (ts, fs)))) = pmdl (set gs \<union> set fs)"
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by simp
next
  case (rec ks vs fs v vs')
  from rec(4) sym_preproc_addnew_pmdl show ?case by (rule trans)
qed

lemma snd_sym_preproc_aux_dgrad_set_le:
  assumes "dickson_grading d" and "set vs \<subseteq> Keys (set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  shows "dgrad_set_le d (pp_of_term ` Keys (set (snd (sym_preproc_aux gs ks (vs, fs))))) (pp_of_term ` Keys (set gs \<union> set fs))"
  using assms(2)
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by (rule dgrad_set_le_subset, simp add: Keys_Un image_Un)
next
  case (rec ks vs fs v vs')
  let ?n = "sym_preproc_addnew gs vs' fs v"
  from rec(1) have "v \<in> set vs" by (simp add: rec(2))
  hence set_vs: "insert v (set vs') = set vs" by (auto simp add: rec(3))
  from rec(5) have eq: "Keys (set fs) \<union> (Keys (set gs) \<union> set vs) = Keys (set gs) \<union> Keys (set fs)"
    by blast
  have "dgrad_set_le d (pp_of_term ` Keys (set (snd (sym_preproc_aux gs (ks @ [v]) ?n))))
                        (pp_of_term ` Keys (set gs \<union> set (snd ?n)))"
  proof (rule rec(4))
    have "set (fst ?n) \<subseteq> Keys (set (snd ?n)) \<union> insert v (set vs')"
      by (simp only: Keys_snd_sym_preproc_addnew, blast)
    also have "... = Keys (set (snd ?n)) \<union> (set vs)" by (simp only: set_vs)
    also have "... \<subseteq> Keys (set (snd ?n))"
    proof -
      {
        fix u
        assume "u \<in> set vs"
        with rec(5) have "u \<in> Keys (set fs)" ..
        then obtain f where "f \<in> set fs" and "u \<in> keys f" by (rule in_KeysE)
        from this(1) snd_sym_preproc_addnew_superset have "f \<in> set (snd ?n)" ..
        with \<open>u \<in> keys f\<close> have "u \<in> Keys (set (snd ?n))" by (rule in_KeysI)
      }
      thus ?thesis by auto
    qed
    finally show "set (fst ?n) \<subseteq> Keys (set (snd ?n))" .
  qed
  also have "dgrad_set_le d ... (pp_of_term ` Keys (set gs \<union> set fs))"
  proof (simp only: image_Un Keys_Un dgrad_set_le_Un, rule)
    show "dgrad_set_le d (pp_of_term ` Keys (set gs)) (pp_of_term ` Keys (set gs) \<union> pp_of_term ` Keys (set fs))"
      by (rule dgrad_set_le_subset, simp)
  next
    have "dgrad_set_le d (pp_of_term ` Keys (set (snd ?n))) (pp_of_term ` (Keys (set fs) \<union> insert v (set (fst ?n))))"
      by (rule dgrad_set_le_subset, auto simp only: Keys_snd_sym_preproc_addnew[symmetric])
    also have "dgrad_set_le d ... (pp_of_term ` Keys (set fs) \<union> pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
    proof (simp only: dgrad_set_le_Un image_Un, rule)
      show "dgrad_set_le d (pp_of_term ` Keys (set fs))
            (pp_of_term ` Keys (set fs) \<union> (pp_of_term ` Keys (set gs) \<union> pp_of_term ` insert v (set vs')))"
        by (rule dgrad_set_le_subset, blast)
    next
      have "dgrad_set_le d (pp_of_term ` {v}) (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
        by (rule dgrad_set_le_subset, simp)
      moreover from assms(1) have "dgrad_set_le d (pp_of_term ` set (fst ?n)) (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
        by (rule fst_sym_preproc_addnew_dgrad_set_le)
      ultimately have "dgrad_set_le d (pp_of_term ` ({v} \<union> set (fst ?n))) (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))"
        by (simp only: dgrad_set_le_Un image_Un)
      also have "dgrad_set_le d (pp_of_term ` (Keys (set gs) \<union> insert v (set vs')))
                                (pp_of_term ` (Keys (set fs) \<union> (Keys (set gs) \<union> insert v (set vs'))))"
        by (rule dgrad_set_le_subset, blast)
      finally show "dgrad_set_le d (pp_of_term ` insert v (set (fst ?n)))
                                   (pp_of_term ` Keys (set fs) \<union> (pp_of_term ` Keys (set gs) \<union> pp_of_term ` insert v (set vs')))"
        by (simp add: image_Un)
    qed
    finally show "dgrad_set_le d (pp_of_term ` Keys (set (snd ?n))) (pp_of_term ` Keys (set gs) \<union> pp_of_term ` Keys (set fs))"
      by (simp only: set_vs eq, metis eq image_Un)
  qed
  finally show ?case .
qed

lemma components_snd_sym_preproc_aux_subset:
  assumes "set vs \<subseteq> Keys (set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  shows "component_of_term ` Keys (set (snd (sym_preproc_aux gs ks (vs, fs)))) \<subseteq>
          component_of_term ` Keys (set gs \<union> set fs)"
  using assms
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  show ?case by (simp add: Keys_Un image_Un)
next
  case (rec ks vs fs v vs')
  let ?n = "sym_preproc_addnew gs vs' fs v"
  from rec(1) have "v \<in> set vs" by (simp add: rec(2))
  hence set_vs: "insert v (set vs') = set vs" by (auto simp add: rec(3))
  from rec(5) have eq: "Keys (set fs) \<union> (Keys (set gs) \<union> set vs) = Keys (set gs) \<union> Keys (set fs)"
    by blast
  have "component_of_term ` Keys (set (snd (sym_preproc_aux gs (ks @ [v]) ?n))) \<subseteq>
                        component_of_term ` Keys (set gs \<union> set (snd ?n))"
  proof (rule rec(4))
    have "set (fst ?n) \<subseteq> Keys (set (snd ?n)) \<union> insert v (set vs')"
      by (simp only: Keys_snd_sym_preproc_addnew, blast)
    also have "... = Keys (set (snd ?n)) \<union> (set vs)" by (simp only: set_vs)
    also have "... \<subseteq> Keys (set (snd ?n))"
    proof -
      {
        fix u
        assume "u \<in> set vs"
        with rec(5) have "u \<in> Keys (set fs)" ..
        then obtain f where "f \<in> set fs" and "u \<in> keys f" by (rule in_KeysE)
        from this(1) snd_sym_preproc_addnew_superset have "f \<in> set (snd ?n)" ..
        with \<open>u \<in> keys f\<close> have "u \<in> Keys (set (snd ?n))" by (rule in_KeysI)
      }
      thus ?thesis by auto
    qed
    finally show "set (fst ?n) \<subseteq> Keys (set (snd ?n))" .
  qed
  also have "... \<subseteq> component_of_term ` Keys (set gs \<union> set fs)"
  proof (simp only: image_Un Keys_Un Un_subset_iff, rule, fact Un_upper1)
    have "component_of_term ` Keys (set (snd ?n)) \<subseteq> component_of_term ` (Keys (set fs) \<union> insert v (set (fst ?n)))"
      by (auto simp only: Keys_snd_sym_preproc_addnew[symmetric])
    also have "... \<subseteq> component_of_term ` Keys (set fs) \<union> component_of_term ` (Keys (set gs) \<union> insert v (set vs'))"
    proof (simp only: Un_subset_iff image_Un, rule, fact Un_upper1)
      have "component_of_term ` {v} \<subseteq> component_of_term ` (Keys (set gs) \<union> insert v (set vs'))"
        by simp
      moreover have "component_of_term ` set (fst ?n) \<subseteq> component_of_term ` (Keys (set gs) \<union> insert v (set vs'))"
        by (rule components_fst_sym_preproc_addnew_subset)
      ultimately have "component_of_term ` ({v} \<union> set (fst ?n)) \<subseteq> component_of_term ` (Keys (set gs) \<union> insert v (set vs'))"
        by (simp only: Un_subset_iff image_Un)
      also have "component_of_term ` (Keys (set gs) \<union> insert v (set vs')) \<subseteq>
                          component_of_term ` (Keys (set fs) \<union> (Keys (set gs) \<union> insert v (set vs')))"
        by blast
      finally show "component_of_term ` insert v (set (fst ?n)) \<subseteq>
                        component_of_term ` Keys (set fs) \<union>
                        (component_of_term ` Keys (set gs) \<union> component_of_term ` insert v (set vs'))"
        by (simp add: image_Un)
    qed
    finally show "component_of_term ` Keys (set (snd ?n)) \<subseteq>
                    component_of_term ` Keys (set gs) \<union> component_of_term ` Keys (set fs)"
      by (simp only: set_vs eq, metis eq image_Un)
  qed
  finally show ?case .
qed

lemma snd_sym_preproc_aux_complete:
  assumes "\<And>u' g'. u' \<in> Keys (set fs) \<Longrightarrow> u' \<notin> set vs \<Longrightarrow> g' \<in> set gs \<Longrightarrow> lt g' adds\<^sub>t u' \<Longrightarrow>
            monom_mult 1 (pp_of_term u' - lp g') g' \<in> set fs"
  assumes "u \<in> Keys (set (snd (sym_preproc_aux gs ks (vs, fs))))" and "g \<in> set gs" and "lt g adds\<^sub>t u"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (pp_of_term u - lp g) g \<in>
          set (snd (sym_preproc_aux gs ks (vs, fs)))"
  using assms
proof (induct fs rule: sym_preproc_aux_induct)
  case (base ks fs)
  from base(2) have "u \<in> Keys (set fs)" by simp
  from this _ base(3, 4) have "monom_mult 1 (pp_of_term u - lp g) g \<in> set fs"
  proof (rule base(1))
    show "u \<notin> set []" by simp
  qed
  thus ?case by simp
next
  case (rec ks vs fs v vs')
  from rec(1) have "v \<in> set vs" by (simp add: rec(2))
  hence set_ts: "set vs = insert v (set vs')" by (auto simp add: rec(3))

  let ?n = "sym_preproc_addnew gs vs' fs v"
  from _ rec(6, 7, 8) show ?case
  proof (rule rec(4))
    fix v' g'
    assume "v' \<in> Keys (set (snd ?n))" and "v' \<notin> set (fst ?n)" and "g' \<in> set gs" and "lt g' adds\<^sub>t v'"
    from this(1) Keys_snd_sym_preproc_addnew have "v' \<in> Keys (set fs) \<union> insert v (set (fst ?n))"
      by blast
    with \<open>v' \<notin> set (fst ?n)\<close> have disj: "v' \<in> Keys (set fs) \<or> v' = v" by blast
    show "monom_mult 1 (pp_of_term v' - lp g') g' \<in> set (snd ?n)"
    proof (cases "v' = v")
      case True
      from \<open>g' \<in> set gs\<close> \<open>lt g' adds\<^sub>t v'\<close> show ?thesis
        unfolding True by (rule sym_preproc_addnew_complete)
    next
      case False
      with disj have "v' \<in> Keys (set fs)" by simp
      moreover have "v' \<notin> set vs"
      proof
        assume "v' \<in> set vs"
        hence "v' \<in> set vs'" using False by (simp add: rec(3))
        with fst_sym_preproc_addnew_superset have "v' \<in> set (fst ?n)" ..
        with \<open>v' \<notin> set (fst ?n)\<close> show False ..
      qed
      ultimately have "monom_mult 1 (pp_of_term v' - lp g') g' \<in> set fs"
        using \<open>g' \<in> set gs\<close> \<open>lt g' adds\<^sub>t v'\<close> by (rule rec(5))
      with snd_sym_preproc_addnew_superset show ?thesis ..
    qed
  qed
qed

definition sym_preproc :: "('t \<Rightarrow>\<^sub>0 'b::semiring_1) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t list \<times> ('t \<Rightarrow>\<^sub>0 'b) list)"
  where "sym_preproc gs fs = sym_preproc_aux gs [] (Keys_to_list fs, fs)"

lemma sym_preproc_Nil [simp]: "sym_preproc gs [] = ([], [])"
  by (simp add: sym_preproc_def)

lemma fst_sym_preproc:
  "fst (sym_preproc gs fs) = Keys_to_list (snd (sym_preproc gs (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)))"
proof -
  let ?a = "fst (sym_preproc gs fs)"
  let ?b = "Keys_to_list (snd (sym_preproc gs fs))"
  have "antisymp (\<succ>\<^sub>t)" unfolding antisymp_def by fastforce
  have "irreflp (\<succ>\<^sub>t)" by (simp add: irreflp_def)
  moreover have "transp (\<succ>\<^sub>t)" unfolding transp_def by fastforce
  moreover have s1: "sorted_wrt (\<succ>\<^sub>t) ?a" unfolding sym_preproc_def
    by (rule fst_sym_preproc_aux_sorted_wrt, simp_all)
  ultimately have d1: "distinct ?a" by (rule distinct_sorted_wrt_irrefl)
  have s2: "sorted_wrt (\<succ>\<^sub>t) ?b" by (fact Keys_to_list_sorted_wrt)
  with \<open>irreflp (\<succ>\<^sub>t)\<close> \<open>transp (\<succ>\<^sub>t)\<close> have d2: "distinct ?b" by (rule distinct_sorted_wrt_irrefl)
  from \<open>antisymp (\<succ>\<^sub>t)\<close> s1 d1 s2 d2 show ?thesis
  proof (rule sorted_wrt_distinct_set_unique)
    show "set ?a = set ?b" unfolding set_Keys_to_list sym_preproc_def
      by (rule fst_sym_preproc_aux_complete, simp add: set_Keys_to_list)
  qed
qed

lemma snd_sym_preproc_superset: "set fs \<subseteq> set (snd (sym_preproc gs fs))"
  by (simp only: sym_preproc_def snd_conv, fact snd_sym_preproc_aux_superset)

lemma in_snd_sym_preprocE:
  assumes "p \<in> set (snd (sym_preproc gs fs))"
  assumes 1: "p \<in> set fs \<Longrightarrow> thesis"
  assumes 2: "\<And>g t. g \<in> set gs \<Longrightarrow> p = monom_mult 1 t g \<Longrightarrow> thesis"
  shows thesis
  using assms unfolding sym_preproc_def snd_conv by (rule in_snd_sym_preproc_auxE)

lemma snd_sym_preproc_pmdl: "pmdl (set gs \<union> set (snd (sym_preproc gs fs))) = pmdl (set gs \<union> set fs)"
  unfolding sym_preproc_def snd_conv by (fact snd_sym_preproc_aux_pmdl)

lemma snd_sym_preproc_dgrad_set_le:
  assumes "dickson_grading d"
  shows "dgrad_set_le d (pp_of_term ` Keys (set (snd (sym_preproc gs fs))))
                        (pp_of_term ` Keys (set gs \<union> set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list)))"
  unfolding sym_preproc_def snd_conv using assms
proof (rule snd_sym_preproc_aux_dgrad_set_le)
  show "set (Keys_to_list fs) \<subseteq> Keys (set fs)" by (simp add: set_Keys_to_list)
qed

corollary snd_sym_preproc_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (snd (sym_preproc gs fs))) (set gs \<union> set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  unfolding dgrad_p_set_le_def
proof -
  from assms show "dgrad_set_le d (pp_of_term ` Keys (set (snd (sym_preproc gs fs)))) (pp_of_term ` Keys (set gs \<union> set fs))"
    by (rule snd_sym_preproc_dgrad_set_le)
qed

lemma components_snd_sym_preproc_subset:
  "component_of_term ` Keys (set (snd (sym_preproc gs fs))) \<subseteq>
          component_of_term ` Keys (set gs \<union> set (fs::('t \<Rightarrow>\<^sub>0 'b::semiring_1_no_zero_divisors) list))"
  unfolding sym_preproc_def snd_conv
  by (rule components_snd_sym_preproc_aux_subset, simp add: set_Keys_to_list)

lemma snd_sym_preproc_complete:
  assumes "v \<in> Keys (set (snd (sym_preproc gs fs)))" and "g \<in> set gs" and "lt g adds\<^sub>t v"
  shows "monom_mult (1::'b::semiring_1_no_zero_divisors) (pp_of_term v - lp g) g \<in> set (snd (sym_preproc gs fs))"
  using _ assms unfolding sym_preproc_def snd_conv
proof (rule snd_sym_preproc_aux_complete)
  fix u' and g'::"'t \<Rightarrow>\<^sub>0 'b"
  assume "u' \<in> Keys (set fs)" and "u' \<notin> set (Keys_to_list fs)"
  thus "monom_mult 1 (pp_of_term u' - lp g') g' \<in> set fs" by (simp add: set_Keys_to_list)
qed

end (* gd_term *)

subsection \<open>\<open>lin_red\<close>\<close>

context ordered_term
begin

definition lin_red :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) \<Rightarrow> bool"
  where "lin_red F p q \<equiv> (\<exists>f\<in>F. red_single p q f 0)"

text \<open>@{const lin_red} is a restriction of @{const red}, where the reductor (\<open>f\<close>) may only be
  multiplied by a constant factor, i.\,e. where the power-product is \<open>0\<close>.\<close>

lemma lin_redI:
  assumes "f \<in> F" and "red_single p q f 0"
  shows "lin_red F p q"
  unfolding lin_red_def using assms ..

lemma lin_redE:
  assumes "lin_red F p q"
  obtains f::"'t \<Rightarrow>\<^sub>0 'b::field" where "f \<in> F" and "red_single p q f 0"
proof -
  from assms obtain f where "f \<in> F" and t: "red_single p q f 0" unfolding lin_red_def by blast
  thus "?thesis" ..
qed

lemma lin_red_imp_red:
  assumes "lin_red F p q"
  shows "red F p q"
proof -
  from assms obtain f where "f \<in> F" and "red_single p q f 0" by (rule lin_redE)
  thus ?thesis by (rule red_setI)
qed

lemma lin_red_Un: "lin_red (F \<union> G) p q = (lin_red F p q \<or> lin_red G p q)"
proof
  assume "lin_red (F \<union> G) p q"
  then obtain f where "f \<in> F \<union> G" and r: "red_single p q f 0" by (rule lin_redE)
  from this(1) show "lin_red F p q \<or> lin_red G p q"
  proof
    assume "f \<in> F"
    from this r have "lin_red F p q" by (rule lin_redI)
    thus ?thesis ..
  next
    assume "f \<in> G" 
    from this r have "lin_red G p q" by (rule lin_redI)
    thus ?thesis ..
  qed
next
  assume "lin_red F p q \<or> lin_red G p q"
  thus "lin_red (F \<union> G) p q"
  proof
    assume "lin_red F p q"
    then obtain f where "f \<in> F" and r: "red_single p q f 0" by (rule lin_redE)
    from this(1) have "f \<in> F \<union> G" by simp
    from this r show ?thesis by (rule lin_redI)
  next
    assume "lin_red G p q"
    then obtain g where "g \<in> G" and r: "red_single p q g 0" by (rule lin_redE)
    from this(1) have "g \<in> F \<union> G" by simp
    from this r show ?thesis by (rule lin_redI)
  qed
qed

lemma lin_red_imp_red_rtrancl:
  assumes "(lin_red F)\<^sup>*\<^sup>* p q"
  shows "(red F)\<^sup>*\<^sup>* p q"
  using assms
proof induct
  case base
  show ?case ..
next
  case (step y z)
  from step(2) have "red F y z" by (rule lin_red_imp_red)
  with step(3) show ?case ..
qed

lemma phull_closed_lin_red:
  assumes "phull B \<subseteq> phull A" and "p \<in> phull A" and "lin_red B p q"
  shows "q \<in> phull A"
proof -
  from assms(3) obtain f where "f \<in> B" and "red_single p q f 0" by (rule lin_redE)
  hence q: "q = p - (lookup p (lt f) / lc f) \<cdot> f"
    by (simp add: red_single_def term_simps map_scale_eq_monom_mult)
  have "q - p \<in> phull B"
    by (simp add: q, rule phull.span_neg, rule phull.span_scale, rule phull.span_base, fact \<open>f \<in> B\<close>)
  with assms(1) have "q - p \<in> phull A" ..
  from this assms(2) have "(q - p) + p \<in> phull A" by (rule phull.span_add)
  thus ?thesis by simp
qed

subsection \<open>Reduction\<close>

definition Macaulay_red :: "'t list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "Macaulay_red vs fs =
     (let lts = map lt (filter (\<lambda>p. p \<noteq> 0) fs) in
       filter (\<lambda>p. p \<noteq> 0 \<and> lt p \<notin> set lts) (mat_to_polys vs (row_echelon (polys_to_mat vs fs)))
     )"

text \<open>\<open>Macaulay_red vs fs\<close> auto-reduces (w.\,r.\,t. @{const lin_red}) the given list \<open>fs\<close> and returns
  those non-zero polynomials whose leading terms are not in \<open>lt_set (set fs)\<close>.
  Argument \<open>vs\<close> is expected to be \<open>Keys_to_list fs\<close>; this list is passed as an argument
  to @{const Macaulay_red}, because it can be efficiently computed by symbolic preprocessing.\<close>

lemma Macaulay_red_alt:
  "Macaulay_red (Keys_to_list fs) fs = filter (\<lambda>p. lt p \<notin> lt_set (set fs)) (Macaulay_list fs)"
proof -
  have "{x \<in> set fs. x \<noteq> 0} = set fs - {0}" by blast
  thus ?thesis by (simp add: Macaulay_red_def Macaulay_list_def Macaulay_mat_def lt_set_def Let_def)
qed

lemma set_Macaulay_red:
  "set (Macaulay_red (Keys_to_list fs) fs) = set (Macaulay_list fs) - {p. lt p \<in> lt_set (set fs)}"
  by (auto simp add: Macaulay_red_alt)

lemma Keys_Macaulay_red: "Keys (set (Macaulay_red (Keys_to_list fs) fs)) \<subseteq> Keys (set fs)"
proof -
  have "Keys (set (Macaulay_red (Keys_to_list fs) fs)) \<subseteq> Keys (set (Macaulay_list fs))"
    unfolding set_Macaulay_red by (fact Keys_minus)
  also have "... \<subseteq> Keys (set fs)" by (fact Keys_Macaulay_list)
  finally show ?thesis .
qed

end (* ordered_term *)

context gd_term
begin

lemma Macaulay_red_reducible:
  assumes "f \<in> phull (set fs)" and "F \<subseteq> set fs" and "lt_set F = lt_set (set fs)"
  shows "(lin_red (F \<union> set (Macaulay_red (Keys_to_list fs) fs)))\<^sup>*\<^sup>* f 0"
proof -
  define A where "A = F \<union> set (Macaulay_red (Keys_to_list fs) fs)"

  have phull_A: "phull A \<subseteq> phull (set fs)"
  proof (rule phull.span_subset_spanI, simp add: A_def, rule)
    have "F \<subseteq> phull F" by (rule phull.span_superset)
    also from assms(2) have "... \<subseteq> phull (set fs)" by (rule phull.span_mono)
    finally show "F \<subseteq> phull (set fs)" .
  next
    have "set (Macaulay_red (Keys_to_list fs) fs) \<subseteq> set (Macaulay_list fs)"
      by (auto simp add: set_Macaulay_red)
    also have "... \<subseteq> phull (set (Macaulay_list fs))" by (rule phull.span_superset)
    also have "... = phull (set fs)" by (rule phull_Macaulay_list)
    finally show "set (Macaulay_red (Keys_to_list fs) fs) \<subseteq> phull (set fs)" .
  qed

  have lt_A: "p \<in> phull (set fs) \<Longrightarrow> p \<noteq> 0 \<Longrightarrow> (\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lt g = lt p \<Longrightarrow> thesis) \<Longrightarrow> thesis"
    for p thesis
  proof -
    assume "p \<in> phull (set fs)" and "p \<noteq> 0"
    then obtain g where g_in: "g \<in> set (Macaulay_list fs)" and "g \<noteq> 0" and "lt p = lt g"
      by (rule Macaulay_list_lt)
    assume *: "\<And>g. g \<in> A \<Longrightarrow> g \<noteq> 0 \<Longrightarrow> lt g = lt p \<Longrightarrow> thesis"
    show ?thesis
    proof (cases "g \<in> set (Macaulay_red (Keys_to_list fs) fs)")
      case True
      hence "g \<in> A" by (simp add: A_def)
      from this \<open>g \<noteq> 0\<close> \<open>lt p = lt g\<close>[symmetric] show ?thesis by (rule *)
    next
      case False
      with g_in have "lt g \<in> lt_set (set fs)" by (simp add: set_Macaulay_red)
      also have "... = lt_set F" by (simp only: assms(3))
      finally obtain g' where "g' \<in> F" and "g' \<noteq> 0" and "lt g' = lt g" by (rule lt_setE)
      from this(1) have "g' \<in> A" by (simp add: A_def)
      moreover note \<open>g' \<noteq> 0\<close>
      moreover have "lt g' = lt p" by (simp only: \<open>lt p = lt g\<close> \<open>lt g' = lt g\<close>)
      ultimately show ?thesis by (rule *)
    qed
  qed

  from assms(2) finite_set have "finite F" by (rule finite_subset)
  from this finite_set have fin_A: "finite A" unfolding A_def by (rule finite_UnI)

  from ex_dgrad obtain d::"'a \<Rightarrow> nat" where dg: "dickson_grading d" ..
  from fin_A have "finite (insert f A)" ..
  then obtain m where "insert f A \<subseteq> dgrad_p_set d m" by (rule dgrad_p_set_exhaust)
  hence A_sub: "A \<subseteq> dgrad_p_set d m" and "f \<in> dgrad_p_set d m" by simp_all
  from dg have "wfP (dickson_less_p d m)" by (rule wf_dickson_less_p)
  from this assms(1) \<open>f \<in> dgrad_p_set d m\<close> show "(lin_red A)\<^sup>*\<^sup>* f 0"
  proof (induct f)
    fix p
    assume IH: "\<And>q. dickson_less_p d m q p \<Longrightarrow> q \<in> phull (set fs) \<Longrightarrow> q \<in> dgrad_p_set d m \<Longrightarrow>
                    (lin_red A)\<^sup>*\<^sup>* q 0"
      and "p \<in> phull (set fs)" and "p \<in> dgrad_p_set d m"
    show "(lin_red A)\<^sup>*\<^sup>* p 0"
    proof (cases "p = 0")
      case True
      thus ?thesis by simp
    next
      case False
      with \<open>p \<in> phull (set fs)\<close> obtain g where "g \<in> A" and "g \<noteq> 0" and "lt g = lt p" by (rule lt_A)
      define q where "q = p - monom_mult (lc p / lc g) 0 g"
      from \<open>g \<in> A\<close> have lr: "lin_red A p q"
      proof (rule lin_redI)
        show "red_single p q g 0"
          by (simp add: red_single_def \<open>lt g = lt p\<close> lc_def[symmetric] q_def \<open>g \<noteq> 0\<close> lc_not_0[OF False] term_simps)
      qed
      moreover have "(lin_red A)\<^sup>*\<^sup>* q 0"
      proof -
        from lr have red: "red A p q" by (rule lin_red_imp_red)
        with dg A_sub \<open>p \<in> dgrad_p_set d m\<close> have "q \<in> dgrad_p_set d m" by (rule dgrad_p_set_closed_red)
        moreover from red have "q \<prec>\<^sub>p p" by (rule red_ord)
        ultimately have "dickson_less_p d m q p" using \<open>p \<in> dgrad_p_set d m\<close>
          by (simp add: dickson_less_p_def)
        moreover from phull_A \<open>p \<in> phull (set fs)\<close> lr have "q \<in> phull (set fs)"
          by (rule phull_closed_lin_red)
        ultimately show ?thesis using \<open>q \<in> dgrad_p_set d m\<close> by (rule IH)
      qed
      ultimately show ?thesis by fastforce
    qed
  qed
qed

primrec pdata_pairs_to_list :: "('t, 'b::field, 'c) pdata_pair list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list" where
  "pdata_pairs_to_list [] = []"|
  "pdata_pairs_to_list (p # ps) =
    (let f = fst (fst p); g = fst (snd p); lf = lp f; lg = lp g; l = lcs lf lg in
      (monom_mult (1 / lc f) (l - lf) f) # (monom_mult (1 / lc g) (l - lg) g) #
      (pdata_pairs_to_list ps)
    )"

lemma in_pdata_pairs_to_listI1:
  assumes "(f, g) \<in> set ps"
  shows "monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f)))
              (fst f) \<in> set (pdata_pairs_to_list ps)" (is "?m \<in> _")
  using assms
proof (induct ps)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  from Cons(2) have "p = (f, g) \<or> (f, g) \<in> set ps" by auto
  thus ?case
  proof
    assume "p = (f, g)"
    show ?thesis by (simp add: \<open>p = (f, g)\<close> Let_def)
  next
    assume "(f, g) \<in> set ps"
    hence "?m \<in> set (pdata_pairs_to_list ps)" by (rule Cons(1))
    thus ?thesis by (simp add: Let_def)
  qed
qed

lemma in_pdata_pairs_to_listI2:
  assumes "(f, g) \<in> set ps"
  shows "monom_mult (1 / lc (fst g)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst g)))
              (fst g) \<in> set (pdata_pairs_to_list ps)" (is "?m \<in> _")
  using assms
proof (induct ps)
  case Nil
  thus ?case by simp
next
  case (Cons p ps)
  from Cons(2) have "p = (f, g) \<or> (f, g) \<in> set ps" by auto
  thus ?case
  proof
    assume "p = (f, g)"
    show ?thesis by (simp add: \<open>p = (f, g)\<close> Let_def)
  next
    assume "(f, g) \<in> set ps"
    hence "?m \<in> set (pdata_pairs_to_list ps)" by (rule Cons(1))
    thus ?thesis by (simp add: Let_def)
  qed
qed

lemma in_pdata_pairs_to_listE:
  assumes "h \<in> set (pdata_pairs_to_list ps)"
  obtains f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
    and "h = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
  using assms
proof (induct ps arbitrary: thesis)
  case Nil
  from Nil(2) show ?case by simp
next
  case (Cons p ps)
  let ?f = "fst (fst p)"
  let ?g = "fst (snd p)"
  let ?lf = "lp ?f"
  let ?lg = "lp ?g"
  let ?l = "lcs ?lf ?lg"
  from Cons(3) have "h = monom_mult (1 / lc ?f) (?l - ?lf) ?f \<or> h = monom_mult (1 / lc ?g) (?l - ?lg) ?g \<or>
                     h \<in> set (pdata_pairs_to_list ps)"
    by (simp add: Let_def)
  thus ?case
  proof (elim disjE)
    assume h: "h = monom_mult (1 / lc ?f) (?l - ?lf) ?f"
    have "(fst p, snd p) \<in> set (p # ps)" by simp
    hence "(fst p, snd p) \<in> set (p # ps) \<or> (snd p, fst p) \<in> set (p # ps)" ..
    from this h show ?thesis by (rule Cons(2))
  next
    assume h: "h = monom_mult (1 / lc ?g) (?l - ?lg) ?g"
    have "(fst p, snd p) \<in> set (p # ps)" by simp
    hence "(snd p, fst p) \<in> set (p # ps) \<or> (fst p, snd p) \<in> set (p # ps)" ..
    moreover from h have "h = monom_mult (1 / lc ?g) ((lcs ?lg ?lf) - ?lg) ?g"
      by (simp only: lcs_comm)
    ultimately show ?thesis by (rule Cons(2))
  next
    assume h_in: "h \<in> set (pdata_pairs_to_list ps)"
    obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
      and h: "h = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
      by (rule Cons(1), assumption, intro h_in)
    from this(1) have "(f, g) \<in> set (p # ps) \<or> (g, f) \<in> set (p # ps)" by auto
    from this h show ?thesis by (rule Cons(2))
  qed
qed

definition f4_red_aux :: "('t, 'b::field, 'c) pdata list \<Rightarrow> ('t, 'b, 'c) pdata_pair list \<Rightarrow>
                          ('t \<Rightarrow>\<^sub>0 'b) list"
  where "f4_red_aux bs ps =
            (let aux = sym_preproc (map fst bs) (pdata_pairs_to_list ps) in Macaulay_red (fst aux) (snd aux))"

text \<open>@{const f4_red_aux} only takes two arguments, since it does not distinguish between those
  elements of the current basis that are known to be a Gr\"obner basis (called \<open>gs\<close> in
  @{theory Groebner_Bases.Algorithm_Schema}) and the remaining ones.\<close>

lemma f4_red_aux_not_zero: "0 \<notin> set (f4_red_aux bs ps)"
  by (simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red set_Macaulay_list)

lemma f4_red_aux_irredudible:
  assumes "h \<in> set (f4_red_aux bs ps)" and "b \<in> set bs" and "fst b \<noteq> 0"
  shows "\<not> lt (fst b) adds\<^sub>t lt h"
proof
  from assms(1) f4_red_aux_not_zero have "h \<noteq> 0" by metis
  hence "lt h \<in> keys h" by (rule lt_in_keys)
  also from assms(1) have "... \<subseteq> Keys (set (f4_red_aux bs ps))" by (rule keys_subset_Keys)
  also have "... \<subseteq> Keys (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    (is "_ \<subseteq> Keys (set ?s)") by (simp only: f4_red_aux_def Let_def fst_sym_preproc Keys_Macaulay_red)
  finally have "lt h \<in> Keys (set ?s)" .
  moreover from assms(2) have "fst b \<in> set (map fst bs)" by auto
  moreover assume a: "lt (fst b) adds\<^sub>t lt h"
  ultimately have "monom_mult 1 (lp h - lp (fst b)) (fst b) \<in> set ?s" (is "?m \<in> _")
    by (rule snd_sym_preproc_complete)
  from assms(3) have "?m \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  with \<open>?m \<in> set ?s\<close> have "lt ?m \<in> lt_set (set ?s)" by (rule lt_setI)
  moreover from assms(3) a have "lt ?m = lt h"
    by (simp add: lt_monom_mult, metis add_diff_cancel_right' adds_termE pp_of_term_splus)
  ultimately have "lt h \<in> lt_set (set ?s)" by simp
  moreover from assms(1) have "lt h \<notin> lt_set (set ?s)"
    by (simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red)
  ultimately show False by simp
qed

lemma f4_red_aux_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (f4_red_aux bs ps)) (args_to_set ([], bs, ps))"
  unfolding dgrad_p_set_le_def dgrad_set_le_def
proof
  fix s
  assume "s \<in> pp_of_term ` Keys (set (f4_red_aux bs ps))"
  also have "... \<subseteq> pp_of_term ` Keys (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    (is "_ \<subseteq> pp_of_term ` Keys (set ?s)")
    by (rule image_mono, simp only: f4_red_aux_def Let_def fst_sym_preproc Keys_Macaulay_red)
  finally have "s \<in> pp_of_term ` Keys (set ?s)" .
  with snd_sym_preproc_dgrad_set_le[OF assms] obtain t
    where "t \<in> pp_of_term ` Keys (set (map fst bs) \<union> set (pdata_pairs_to_list ps))" and "d s \<le> d t"
    by (rule dgrad_set_leE)
  from this(1) have "t \<in> pp_of_term ` Keys (fst ` set bs) \<or> t \<in> pp_of_term ` Keys (set (pdata_pairs_to_list ps))"
    by (simp add: Keys_Un image_Un)
  thus "\<exists>t \<in> pp_of_term ` Keys (args_to_set ([], bs, ps)). d s \<le> d t"
  proof
    assume "t \<in> pp_of_term ` Keys (fst `  set bs)"
    also have "... \<subseteq> pp_of_term ` Keys (args_to_set ([], bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_alt)
    finally have "t \<in> pp_of_term ` Keys (args_to_set ([], bs, ps))" .
    with \<open>d s \<le> d t\<close> show ?thesis ..
  next
    assume "t \<in> pp_of_term ` Keys (set (pdata_pairs_to_list ps))"
    then obtain p where "p \<in> set (pdata_pairs_to_list ps)" and "t \<in> pp_of_term ` keys p"
      by (auto elim: in_KeysE)
    from this(1) obtain f g where disj: "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
      and p: "p = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
      by (rule in_pdata_pairs_to_listE)
    from disj have "fst f \<in> args_to_set ([], bs, ps) \<and> fst g \<in> args_to_set ([], bs, ps)"
    proof
      assume "(f, g) \<in> set ps"
      hence "f \<in> fst ` set ps" and "g \<in> snd ` set ps" by force+
      hence "fst f \<in> fst ` fst ` set ps" and "fst g \<in> fst ` snd ` set ps" by simp_all
      thus ?thesis by (simp add: args_to_set_def image_Un)
    next
      assume "(g, f) \<in> set ps"
      hence "f \<in> snd ` set ps" and "g \<in> fst ` set ps" by force+
      hence "fst f \<in> fst ` snd ` set ps" and "fst g \<in> fst ` fst ` set ps" by simp_all
      thus ?thesis by (simp add: args_to_set_def image_Un)
    qed
    hence "fst f \<in> args_to_set ([], bs, ps)" and "fst g \<in> args_to_set ([], bs, ps)" by simp_all
    hence keys_f: "keys (fst f) \<subseteq> Keys (args_to_set ([], bs, ps))"
      and keys_g: "keys (fst g) \<subseteq> Keys (args_to_set ([], bs, ps))"
      by (auto intro!: keys_subset_Keys)
    let ?lf = "lp (fst f)"
    let ?lg = "lp (fst g)"
    define l where "l = lcs ?lf ?lg"
    have "pp_of_term ` keys p \<subseteq> pp_of_term ` ((\<oplus>) (lcs ?lf ?lg - ?lf) ` keys (fst f))" unfolding p
      using keys_monom_mult_subset by (rule image_mono)
    with \<open>t \<in> pp_of_term ` keys p\<close> have "t \<in> pp_of_term ` ((\<oplus>) (l - ?lf) ` keys (fst f))" unfolding l_def ..
    then obtain t' where "t' \<in> pp_of_term ` keys (fst f)" and t: "t = (l - ?lf) + t'"
      using pp_of_term_splus by fastforce
    from this(1) have "fst f \<noteq> 0" by auto
    show ?thesis
    proof (cases "fst g = 0")
      case True
      hence "?lg = 0" by (simp add: lt_def min_term_def term_simps)
      hence "l = ?lf" by (simp add: l_def lcs_zero lcs_comm)
      hence "t = t'" by (simp add: t)
      with \<open>d s \<le> d t\<close> have "d s \<le> d t'" by simp
      moreover from \<open>t' \<in> pp_of_term ` keys (fst f)\<close> keys_f have "t' \<in> pp_of_term ` Keys (args_to_set ([], bs, ps))"
        by blast
      ultimately show ?thesis ..
    next
      case False
      have "d t = d (l - ?lf) \<or> d t = d t'"
        by (auto simp add: t dickson_gradingD1[OF assms])
      thus ?thesis
      proof
        assume "d t = d (l - ?lf)"
        also from assms have "... \<le> ord_class.max (d ?lf) (d ?lg)"
          unfolding l_def by (rule dickson_grading_lcs_minus)
        finally have "d s \<le> d ?lf \<or> d s \<le> d ?lg" using \<open>d s \<le> d t\<close> by auto
        thus ?thesis
        proof
          assume "d s \<le> d ?lf"
          moreover have "lt (fst f) \<in> Keys (args_to_set ([], bs, ps))"
            by (rule, rule lt_in_keys, fact+)
          ultimately show ?thesis by blast
        next
          assume "d s \<le> d ?lg"
          moreover have "lt (fst g) \<in> Keys (args_to_set ([], bs, ps))"
            by (rule, rule lt_in_keys, fact+)
          ultimately show ?thesis by blast
        qed
      next
        assume "d t = d t'"
        with \<open>d s \<le> d t\<close> have "d s \<le> d t'" by simp
        moreover from \<open>t' \<in> pp_of_term ` keys (fst f)\<close> keys_f have "t' \<in> pp_of_term ` Keys (args_to_set ([], bs, ps))"
          by blast
        ultimately show ?thesis ..
      qed
    qed
  qed
qed

lemma components_f4_red_aux_subset:
  "component_of_term ` Keys (set (f4_red_aux bs ps)) \<subseteq> component_of_term ` Keys (args_to_set ([], bs, ps))"
proof
  fix k
  assume "k \<in> component_of_term ` Keys (set (f4_red_aux bs ps))"
  also have "... \<subseteq> component_of_term ` Keys (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (rule image_mono, simp only: f4_red_aux_def Let_def fst_sym_preproc Keys_Macaulay_red)
  also have "... \<subseteq> component_of_term ` Keys (set (map fst bs) \<union> set (pdata_pairs_to_list ps))"
    by (fact components_snd_sym_preproc_subset)
  finally have "k \<in> component_of_term ` Keys (fst ` set bs) \<union> component_of_term ` Keys (set (pdata_pairs_to_list ps))"
    by (simp add: image_Un Keys_Un)
  thus "k \<in> component_of_term ` Keys (args_to_set ([], bs, ps))"
  proof
    assume "k \<in> component_of_term ` Keys (fst `  set bs)"
    also have "... \<subseteq> component_of_term ` Keys (args_to_set ([], bs, ps))"
      by (rule image_mono, rule Keys_mono, auto simp add: args_to_set_alt)
    finally show "k \<in> component_of_term ` Keys (args_to_set ([], bs, ps))" .
  next
    assume "k \<in> component_of_term ` Keys (set (pdata_pairs_to_list ps))"
    then obtain p where "p \<in> set (pdata_pairs_to_list ps)" and "k \<in> component_of_term ` keys p"
      by (auto elim: in_KeysE)
    from this(1) obtain f g where disj: "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
      and p: "p = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
      by (rule in_pdata_pairs_to_listE)
    from disj have "fst f \<in> args_to_set ([], bs, ps)"
      by (simp add: args_to_set_alt, metis fst_conv image_eqI snd_conv)
    hence "fst f \<in> args_to_set ([], bs, ps)" by simp
    hence keys_f: "keys (fst f) \<subseteq> Keys (args_to_set ([], bs, ps))"
      by (auto intro!: keys_subset_Keys)
    let ?lf = "lp (fst f)"
    let ?lg = "lp (fst g)"
    define l where "l = lcs ?lf ?lg"
    have "component_of_term ` keys p \<subseteq> component_of_term ` ((\<oplus>) (lcs ?lf ?lg - ?lf) ` keys (fst f))"
      unfolding p using keys_monom_mult_subset by (rule image_mono)
    with \<open>k \<in> component_of_term ` keys p\<close> have "k \<in> component_of_term ` ((\<oplus>) (l - ?lf) ` keys (fst f))"
      unfolding l_def ..
    hence "k \<in> component_of_term ` keys (fst f)" using component_of_term_splus by fastforce
    with keys_f show "k \<in> component_of_term ` Keys (args_to_set ([], bs, ps))" by blast
  qed
qed

lemma pmdl_f4_red_aux: "set (f4_red_aux bs ps) \<subseteq> pmdl (args_to_set ([], bs, ps))"
proof -
  have "set (f4_red_aux bs ps) \<subseteq>
          set (Macaulay_list (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (auto simp add: f4_red_aux_def Let_def fst_sym_preproc set_Macaulay_red)
  also have "... \<subseteq> pmdl (set (Macaulay_list (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps)))))"
    by (fact pmdl.span_superset)
  also have "... = pmdl (set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (fact pmdl_Macaulay_list)
  also have "... \<subseteq> pmdl (set (map fst bs) \<union>
                        set (snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))))"
    by (rule pmdl.span_mono, blast)
  also have "... = pmdl (set (map fst bs) \<union> set (pdata_pairs_to_list ps))"
    by (fact snd_sym_preproc_pmdl)
  also have "... \<subseteq> pmdl (args_to_set ([], bs, ps))"
  proof (rule pmdl.span_subset_spanI, simp only: Un_subset_iff, rule conjI)
    have "set (map fst bs) \<subseteq> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_def)
    also have "... \<subseteq> pmdl (args_to_set ([], bs, ps))" by (rule pmdl.span_superset)
    finally show "set (map fst bs) \<subseteq> pmdl (args_to_set ([], bs, ps))" .
  next
    show "set (pdata_pairs_to_list ps) \<subseteq> pmdl (args_to_set ([], bs, ps))"
    proof
      fix p
      assume "p \<in> set (pdata_pairs_to_list ps)"
      then obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
        and p: "p = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
        by (rule in_pdata_pairs_to_listE)
      from this(1) have "f \<in> fst ` set ps \<union> snd ` set ps" by force
      hence "fst f \<in> args_to_set ([], bs, ps)" by (auto simp add: args_to_set_alt)
      hence "fst f \<in> pmdl (args_to_set ([], bs, ps))" by (rule pmdl.span_base)
      thus "p \<in> pmdl (args_to_set ([], bs, ps))" unfolding p by (rule pmdl_closed_monom_mult)
    qed
  qed
  finally show ?thesis .
qed

lemma f4_red_aux_phull_reducible:
  assumes "set ps \<subseteq> set bs \<times> set bs"
    and "f \<in> phull (set (pdata_pairs_to_list ps))"
  shows "(red (fst ` set bs \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* f 0"
proof -
  define fs where "fs = snd (sym_preproc (map fst bs) (pdata_pairs_to_list ps))"
  have "set (pdata_pairs_to_list ps) \<subseteq> set fs" unfolding fs_def by (fact snd_sym_preproc_superset)
  hence "phull (set (pdata_pairs_to_list ps)) \<subseteq> phull (set fs)" by (rule phull.span_mono)
  with assms(2) have f_in: "f \<in> phull (set fs)" ..
  have eq: "(set fs) \<union> set (f4_red_aux bs ps) = (set fs) \<union> set (Macaulay_red (Keys_to_list fs) fs)"
    by (simp add: f4_red_aux_def fs_def Let_def fst_sym_preproc)

  have "(lin_red ((set fs) \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* f 0"
    by (simp only: eq, rule Macaulay_red_reducible, fact f_in, fact subset_refl, fact refl)
  thus ?thesis
  proof induct
    case base
    show ?case ..
  next
    case (step y z)
    from step(2) have "red (fst ` set bs \<union> set (f4_red_aux bs ps)) y z" unfolding lin_red_Un
    proof
      assume "lin_red (set fs) y z"
      then obtain a where "a \<in> set fs" and r: "red_single y z a 0" by (rule lin_redE)
      from this(1) obtain b c t where "b \<in> fst ` set bs" and a: "a = monom_mult c t b" unfolding fs_def
      proof (rule in_snd_sym_preprocE)
        assume *: "\<And>b c t. b \<in> fst ` set bs \<Longrightarrow> a = monom_mult c t b \<Longrightarrow> thesis"
        assume "a \<in> set (pdata_pairs_to_list ps)"
        then obtain f g where "(f, g) \<in> set ps \<or> (g, f) \<in> set ps"
          and a: "a = monom_mult (1 / lc (fst f)) ((lcs (lp (fst f)) (lp (fst g))) - (lp (fst f))) (fst f)"
          by (rule in_pdata_pairs_to_listE)
        from this(1) have "f \<in> fst ` set ps \<union> snd ` set ps" by force
        with assms(1) have "f \<in> set bs" by fastforce
        hence "fst f \<in> fst ` set bs" by simp
        from this a show ?thesis by (rule *)
      next
        fix g s
        assume *: "\<And>b c t. b \<in> fst ` set bs \<Longrightarrow> a = monom_mult c t b \<Longrightarrow> thesis"
        assume "g \<in> set (map fst bs)"
        hence "g \<in> fst ` set bs" by simp
        moreover assume "a = monom_mult 1 s g"
        ultimately show ?thesis by (rule *)
      qed
      from r have "c \<noteq> 0" and "b \<noteq> 0" by (simp_all add: a red_single_def monom_mult_eq_zero_iff)
      from r have "red_single y z b t"
        by (simp add: a red_single_def monom_mult_eq_zero_iff lt_monom_mult[OF \<open>c \<noteq> 0\<close> \<open>b \<noteq> 0\<close>]
                      monom_mult_assoc term_simps)
      with \<open>b \<in> fst ` set bs\<close> have "red (fst ` set bs) y z" by (rule red_setI)
      thus ?thesis by (rule red_unionI1)
    next
      assume "lin_red (set (f4_red_aux bs ps)) y z"
      hence "red (set (f4_red_aux bs ps)) y z" by (rule lin_red_imp_red)
      thus ?thesis by (rule red_unionI2)
    qed
    with step(3) show ?case ..
  qed
qed

corollary f4_red_aux_spoly_reducible:
  assumes "set ps \<subseteq> set bs \<times> set bs" and "(p, q) \<in> set ps"
  shows "(red (fst ` set bs \<union> set (f4_red_aux bs ps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
  using assms(1)
proof (rule f4_red_aux_phull_reducible)
  let ?lt = "lp (fst p)"
  let ?lq = "lp (fst q)"
  let ?l = "lcs ?lt ?lq"
  let ?p = "monom_mult (1 / lc (fst p)) (?l - ?lt) (fst p)"
  let ?q = "monom_mult (1 / lc (fst q)) (?l - ?lq) (fst q)"
  from assms(2) have "?p \<in> set (pdata_pairs_to_list ps)" and "?q \<in> set (pdata_pairs_to_list ps)"
    by (rule in_pdata_pairs_to_listI1, rule in_pdata_pairs_to_listI2)
  hence "?p \<in> phull (set (pdata_pairs_to_list ps))" and "?q \<in> phull (set (pdata_pairs_to_list ps))"
    by (auto intro: phull.span_base)
  hence "?p - ?q \<in> phull (set (pdata_pairs_to_list ps))" by (rule phull.span_diff)
  thus "spoly (fst p) (fst q) \<in> phull (set (pdata_pairs_to_list ps))"
    by (simp add: spoly_def Let_def phull.span_zero lc_def split: if_split)
qed

definition f4_red :: "('t, 'b::field, 'c::default, 'd) complT"
  where "f4_red gs bs ps sps data = (map (\<lambda>h. (h, default)) (f4_red_aux (gs @ bs) sps), snd data)"

lemma fst_set_fst_f4_red: "fst ` set (fst (f4_red gs bs ps sps data)) = set (f4_red_aux (gs @ bs) sps)"
  by (simp add: f4_red_def, force)

lemma rcp_spec_f4_red: "rcp_spec f4_red"
proof (rule rcp_specI)
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  show "0 \<notin> fst ` set (fst (f4_red gs bs ps sps data))"
    by (simp add: fst_set_fst_f4_red f4_red_aux_not_zero)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps h b and data::"nat \<times> 'd"
  assume "h \<in> set (fst (f4_red gs bs ps sps data))" and "b \<in> set gs \<union> set bs"
  from this(1) have "fst h \<in> fst ` set (fst (f4_red gs bs ps sps data))" by simp
  hence "fst h \<in> set (f4_red_aux (gs @ bs) sps)" by (simp only: fst_set_fst_f4_red)
  moreover from \<open>b \<in> set gs \<union> set bs\<close> have "b \<in> set (gs @ bs)" by simp
  moreover assume "fst b \<noteq> 0"
  ultimately show "\<not> lt (fst b) adds\<^sub>t lt (fst h)" by (rule f4_red_aux_irredudible)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and d::"'a \<Rightarrow> nat" and data::"nat \<times> 'd"
  assume "dickson_grading d"
  hence "dgrad_p_set_le d (set (f4_red_aux (gs @ bs) sps)) (args_to_set ([], gs @ bs, sps))"
    by (fact f4_red_aux_dgrad_p_set_le)
  also have "... = args_to_set (gs, bs, sps)" by (simp add: args_to_set_alt image_Un)
  finally show "dgrad_p_set_le d (fst ` set (fst (f4_red gs bs ps sps data))) (args_to_set (gs, bs, sps))"
    by (simp only: fst_set_fst_f4_red)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  have "component_of_term ` Keys (set (f4_red_aux (gs @ bs) sps)) \<subseteq>
        component_of_term ` Keys (args_to_set ([], gs @ bs, sps))"
    by (fact components_f4_red_aux_subset)
  also have "... = component_of_term ` Keys (args_to_set (gs, bs, sps))"
    by (simp add: args_to_set_alt image_Un)
  finally show "component_of_term ` Keys (fst ` set (fst (f4_red gs bs ps sps data))) \<subseteq>
        component_of_term ` Keys (args_to_set (gs, bs, sps))"
    by (simp only: fst_set_fst_f4_red)
next
  fix gs bs::"('t, 'b, 'c) pdata list" and ps sps and data::"nat \<times> 'd"
  have "set (f4_red_aux (gs @ bs) sps) \<subseteq> pmdl (args_to_set ([], gs @ bs, sps))"
    by (fact pmdl_f4_red_aux)
  also have "... = pmdl (args_to_set (gs, bs, sps))" by (simp add: args_to_set_alt image_Un)
  finally have "fst ` set (fst (f4_red gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps))"
    by (simp only: fst_set_fst_f4_red)
  moreover {
    fix p q :: "('t, 'b, 'c) pdata"
    assume "set sps \<subseteq> set bs \<times> (set gs \<union> set bs)"
    hence "set sps \<subseteq> set (gs @ bs) \<times> set (gs @ bs)" by fastforce
    moreover assume "(p, q) \<in> set sps"
    ultimately have "(red (fst ` set (gs @ bs) \<union> set (f4_red_aux (gs @ bs) sps)))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0"
      by (rule f4_red_aux_spoly_reducible)
  }
  ultimately show
    "fst ` set (fst (f4_red gs bs ps sps data)) \<subseteq> pmdl (args_to_set (gs, bs, sps)) \<and>
     (\<forall>(p, q)\<in>set sps.
         set sps \<subseteq> set bs \<times> (set gs \<union> set bs) \<longrightarrow>
         (red (fst ` (set gs \<union> set bs) \<union> fst ` set (fst (f4_red gs bs ps sps data))))\<^sup>*\<^sup>* (spoly (fst p) (fst q)) 0)"
    by (auto simp add: image_Un fst_set_fst_f4_red)
qed

lemmas compl_struct_f4_red = compl_struct_rcp[OF rcp_spec_f4_red]
lemmas compl_pmdl_f4_red = compl_pmdl_rcp[OF rcp_spec_f4_red]
lemmas compl_conn_f4_red = compl_conn_rcp[OF rcp_spec_f4_red]

subsection \<open>Pair Selection\<close>

primrec f4_sel_aux :: "'a \<Rightarrow> ('t, 'b::zero, 'c) pdata_pair list \<Rightarrow> ('t, 'b, 'c) pdata_pair list" where
  "f4_sel_aux _ [] = []"|
  "f4_sel_aux t (p # ps) =
    (if (lcs (lp (fst (fst p))) (lp (fst (snd p)))) = t then
      p # (f4_sel_aux t ps)
    else
      []
    )"

lemma f4_sel_aux_subset: "set (f4_sel_aux t ps) \<subseteq> set ps"
  by (induct ps, auto)

primrec f4_sel :: "('t, 'b::zero, 'c, 'd) selT" where
  "f4_sel gs bs [] data = []"|
  "f4_sel gs bs (p # ps) data = p # (f4_sel_aux (lcs (lp (fst (fst p))) (lp (fst (snd p)))) ps)"

lemma sel_spec_f4_sel: "sel_spec f4_sel"
proof (rule sel_specI)
  fix gs bs :: "('t, 'b, 'c) pdata list" and ps::"('t, 'b, 'c) pdata_pair list" and data::"nat \<times> 'd"
  assume "ps \<noteq> []"
  then obtain p ps' where ps: "ps = p # ps'" by (meson list.exhaust)
  show "f4_sel gs bs ps data \<noteq> [] \<and> set (f4_sel gs bs ps data) \<subseteq> set ps"
  proof
    show "f4_sel gs bs ps data \<noteq> []" by (simp add: ps)
  next
    from f4_sel_aux_subset show "set (f4_sel gs bs ps data) \<subseteq> set ps" by (auto simp add: ps)
  qed
qed

subsection \<open>The F4 Algorithm\<close>

text \<open>The F4 algorithm is just @{const gb_schema_direct} with parameters instantiated by suitable
  functions.\<close>

lemma struct_spec_f4: "struct_spec f4_sel add_pairs_canon add_basis_canon f4_red"
  using sel_spec_f4_sel ap_spec_add_pairs_canon ab_spec_add_basis_sorted compl_struct_f4_red
  by (rule struct_specI)

definition f4_aux :: "('t, 'b, 'c) pdata list \<Rightarrow> nat \<times> nat \<times> 'd \<Rightarrow> ('t, 'b, 'c) pdata list \<Rightarrow>
                   ('t, 'b, 'c) pdata_pair list \<Rightarrow> ('t, 'b::field, 'c::default) pdata list"
  where "f4_aux = gb_schema_aux f4_sel add_pairs_canon add_basis_canon f4_red"

lemmas f4_aux_simps [code] = gb_schema_aux_simps[OF struct_spec_f4, folded f4_aux_def]

definition f4 :: "('t, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('t, 'b::field, 'c::default) pdata' list"
  where "f4 = gb_schema_direct f4_sel add_pairs_canon add_basis_canon f4_red"

lemmas f4_simps [code] = gb_schema_direct_def[of f4_sel add_pairs_canon add_basis_canon f4_red, folded f4_def f4_aux_def]

lemmas f4_isGB = gb_schema_direct_isGB[OF struct_spec_f4 compl_conn_f4_red, folded f4_def]

lemmas f4_pmdl = gb_schema_direct_pmdl[OF struct_spec_f4 compl_pmdl_f4_red, folded f4_def]

subsubsection \<open>Special Case: \<open>punit\<close>\<close>

lemma (in gd_term) struct_spec_f4_punit: "punit.struct_spec punit.f4_sel add_pairs_punit_canon punit.add_basis_canon punit.f4_red"
  using punit.sel_spec_f4_sel ap_spec_add_pairs_punit_canon ab_spec_add_basis_sorted punit.compl_struct_f4_red
  by (rule punit.struct_specI)

definition f4_aux_punit :: "('a, 'b, 'c) pdata list \<Rightarrow> nat \<times> nat \<times> 'd \<Rightarrow> ('a, 'b, 'c) pdata list \<Rightarrow>
                   ('a, 'b, 'c) pdata_pair list \<Rightarrow> ('a, 'b::field, 'c::default) pdata list"
  where "f4_aux_punit = punit.gb_schema_aux punit.f4_sel add_pairs_punit_canon punit.add_basis_canon punit.f4_red"

lemmas f4_aux_punit_simps [code] = punit.gb_schema_aux_simps[OF struct_spec_f4_punit, folded f4_aux_punit_def]

definition f4_punit :: "('a, 'b, 'c) pdata' list \<Rightarrow> 'd \<Rightarrow> ('a, 'b::field, 'c::default) pdata' list"
  where "f4_punit = punit.gb_schema_direct punit.f4_sel add_pairs_punit_canon punit.add_basis_canon punit.f4_red"

lemmas f4_punit_simps [code] = punit.gb_schema_direct_def[of "punit.f4_sel" add_pairs_punit_canon
                                "punit.add_basis_canon" "punit.f4_red", folded f4_punit_def f4_aux_punit_def]

lemmas f4_punit_isGB = punit.gb_schema_direct_isGB[OF struct_spec_f4_punit punit.compl_conn_f4_red, folded f4_punit_def]

lemmas f4_punit_pmdl = punit.gb_schema_direct_pmdl[OF struct_spec_f4_punit punit.compl_pmdl_f4_red, folded f4_punit_def]

end (* gd_term *)

end (* theory *)
