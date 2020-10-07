(*  Title:       Projective geometry
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

section "Projective geometry"

theory Projective
  imports Linear_Algebra2
  Euclid_Tarski
  Action
begin

subsection "Proportionality on non-zero vectors"

context vector_space
begin

  definition proportionality :: "('b \<times> 'b) set" where
    "proportionality \<equiv> {(x, y). x \<noteq> 0 \<and> y \<noteq> 0 \<and> (\<exists>k. x = scale k y)}"

  definition non_zero_vectors :: "'b set" where
    "non_zero_vectors \<equiv> {x. x \<noteq> 0}"

  lemma proportionality_refl_on: "refl_on local.non_zero_vectors local.proportionality"
  proof -
    have "local.proportionality \<subseteq> local.non_zero_vectors \<times> local.non_zero_vectors"
      unfolding proportionality_def non_zero_vectors_def
      by auto
    moreover have "\<forall>x\<in>local.non_zero_vectors. (x, x) \<in> local.proportionality"
    proof
      fix x
      assume "x \<in> local.non_zero_vectors"
      hence "x \<noteq> 0" unfolding non_zero_vectors_def ..
      moreover have "x = scale 1 x" by simp
      ultimately show "(x, x) \<in> local.proportionality"
        unfolding proportionality_def
        by blast
    qed
    ultimately show "refl_on local.non_zero_vectors local.proportionality"
      unfolding refl_on_def ..
  qed

  lemma proportionality_sym: "sym local.proportionality"
  proof -
    { fix x y
      assume "(x, y) \<in> local.proportionality"
      hence "x \<noteq> 0" and "y \<noteq> 0" and "\<exists>k. x = scale k y"
        unfolding proportionality_def
        by simp+
      from \<open>\<exists>k. x = scale k y\<close> obtain k where "x = scale k y" by auto
      with \<open>x \<noteq> 0\<close> have "k \<noteq> 0" by simp
      with \<open>x = scale k y\<close> have "y = scale (1/k) x" by simp
      with \<open>x \<noteq> 0\<close> and \<open>y \<noteq> 0\<close> have "(y, x) \<in> local.proportionality"
        unfolding proportionality_def
        by auto
    }
    thus "sym local.proportionality"
      unfolding sym_def
      by blast
  qed

  lemma proportionality_trans: "trans local.proportionality"
  proof -
    { fix x y z
      assume "(x, y) \<in> local.proportionality" and "(y, z) \<in> local.proportionality"
      hence "x \<noteq> 0" and "z \<noteq> 0" and "\<exists>j. x = scale j y" and "\<exists>k. y = scale k z"
        unfolding proportionality_def
        by simp+
      from \<open>\<exists>j. x = scale j y\<close> and \<open>\<exists>k. y = scale k z\<close>
      obtain j and k where "x = scale j y" and "y = scale k z" by auto+
      hence "x = scale (j * k) z" by simp
      with \<open>x \<noteq> 0\<close> and \<open>z \<noteq> 0\<close> have "(x, z) \<in> local.proportionality"
        unfolding proportionality_def
        by auto
    }
    thus "trans local.proportionality"
      unfolding trans_def
      by blast
  qed

  theorem proportionality_equiv: "equiv local.non_zero_vectors local.proportionality"
    unfolding equiv_def
    by (simp add:
      proportionality_refl_on
      proportionality_sym
      proportionality_trans)

end

definition invertible_proportionality ::
  "((real^('n::finite)^'n) \<times> (real^'n^'n)) set" where
  "invertible_proportionality \<equiv>
  real_vector.proportionality \<inter> (Collect invertible \<times> Collect invertible)"

lemma invertible_proportionality_equiv:
  "equiv (Collect invertible :: (real^('n::finite)^'n) set)
  invertible_proportionality"
  (is "equiv ?invs _")
proof -
  from zero_not_invertible
  have "real_vector.non_zero_vectors \<inter> ?invs = ?invs"
    unfolding real_vector.non_zero_vectors_def
    by auto
  from equiv_restrict and real_vector.proportionality_equiv
  have "equiv (real_vector.non_zero_vectors \<inter> ?invs) invertible_proportionality"
    unfolding invertible_proportionality_def
    by auto
  with \<open>real_vector.non_zero_vectors \<inter> ?invs = ?invs\<close>
  show "equiv ?invs invertible_proportionality"
    by simp
qed

subsection "Points of the real projective plane"

typedef proj2 = "(real_vector.non_zero_vectors :: (real^3) set)//real_vector.proportionality"
proof
  have "(axis 1 1 :: real^3) \<in> real_vector.non_zero_vectors"
    unfolding real_vector.non_zero_vectors_def 
    by (simp add: axis_def vec_eq_iff[where 'a="real"])
  thus "real_vector.proportionality `` {axis 1 1} \<in> (real_vector.non_zero_vectors :: (real^3) set)//real_vector.proportionality"
    unfolding quotient_def 
    by auto
qed

definition proj2_rep :: "proj2 \<Rightarrow> real^3" where
  "proj2_rep x \<equiv> \<some> v. v \<in> Rep_proj2 x"

definition proj2_abs :: "real^3 \<Rightarrow> proj2" where
  "proj2_abs v \<equiv> Abs_proj2 (real_vector.proportionality `` {v})"

lemma proj2_rep_in: "proj2_rep x \<in> Rep_proj2 x"
proof -
  let ?v = "proj2_rep x"
  from quotient_element_nonempty and
    real_vector.proportionality_equiv and
    Rep_proj2 [of x]
  have "\<exists> w. w \<in> Rep_proj2 x"
    by auto
  with someI_ex [of "\<lambda> z. z \<in> Rep_proj2 x"]
  show "?v \<in> Rep_proj2 x"
    unfolding proj2_rep_def
    by simp
qed

lemma proj2_rep_non_zero: "proj2_rep x \<noteq> 0"
proof -
  from
    Union_quotient [of real_vector.non_zero_vectors real_vector.proportionality]
    and real_vector.proportionality_equiv
    and Rep_proj2 [of x] and proj2_rep_in [of x]
  have "proj2_rep x \<in> real_vector.non_zero_vectors"
    unfolding quotient_def
    by auto
  thus "proj2_rep x \<noteq> 0"
    unfolding real_vector.non_zero_vectors_def
    by simp
qed

lemma proj2_rep_abs:
  fixes v :: "real^3"
  assumes "v \<in> real_vector.non_zero_vectors"
  shows "(v, proj2_rep (proj2_abs v)) \<in> real_vector.proportionality"
proof -
  from \<open>v \<in> real_vector.non_zero_vectors\<close>
  have "real_vector.proportionality `` {v} \<in> (real_vector.non_zero_vectors :: (real^3) set)//real_vector.proportionality"
    unfolding quotient_def
    by auto 
  with Abs_proj2_inverse
  have "Rep_proj2 (proj2_abs v) = real_vector.proportionality `` {v}"
    unfolding proj2_abs_def
    by simp
  with proj2_rep_in
  have "proj2_rep (proj2_abs v) \<in> real_vector.proportionality `` {v}" by auto
  thus "(v, proj2_rep (proj2_abs v)) \<in> real_vector.proportionality" by simp
qed

lemma proj2_abs_rep: "proj2_abs (proj2_rep x) = x"
proof -
  from partition_Image_element
  [of real_vector.non_zero_vectors
    real_vector.proportionality
    "Rep_proj2 x"
    "proj2_rep x"]
    and real_vector.proportionality_equiv
    and Rep_proj2 [of x] and proj2_rep_in [of x]
  have "real_vector.proportionality `` {proj2_rep x} = Rep_proj2 x"
    by simp
  with Rep_proj2_inverse show "proj2_abs (proj2_rep x) = x"
    unfolding proj2_abs_def
    by simp
qed

lemma proj2_abs_mult:
  assumes "c \<noteq> 0"
  shows "proj2_abs (c *\<^sub>R v) = proj2_abs v"
proof cases
  assume "v = 0"
  thus "proj2_abs (c *\<^sub>R v) = proj2_abs v" by simp
next
  assume "v \<noteq> 0"
  with \<open>c \<noteq> 0\<close>
  have "(c *\<^sub>R v, v) \<in> real_vector.proportionality"
    and "c *\<^sub>R v \<in> real_vector.non_zero_vectors"
    and "v \<in> real_vector.non_zero_vectors"
    unfolding real_vector.proportionality_def
      and real_vector.non_zero_vectors_def
    by simp_all
  with eq_equiv_class_iff
  [of real_vector.non_zero_vectors
    real_vector.proportionality
    "c *\<^sub>R v"
    v]
    and real_vector.proportionality_equiv
  have "real_vector.proportionality `` {c *\<^sub>R v} =
    real_vector.proportionality `` {v}"
    by simp
  thus "proj2_abs (c *\<^sub>R v) = proj2_abs v"
    unfolding proj2_abs_def
    by simp
qed

lemma proj2_abs_mult_rep:
  assumes "c \<noteq> 0"
  shows "proj2_abs (c *\<^sub>R proj2_rep x) = x"
  using proj2_abs_mult and proj2_abs_rep and assms
  by simp

lemma proj2_rep_inj: "inj proj2_rep"
  by (simp add: inj_on_inverseI [of UNIV proj2_abs proj2_rep] proj2_abs_rep)

lemma proj2_rep_abs2:
  assumes "v \<noteq> 0"
  shows "\<exists> k. k \<noteq> 0 \<and> proj2_rep (proj2_abs v) = k *\<^sub>R v"
proof -
  from proj2_rep_abs [of v] and \<open>v \<noteq> 0\<close>
  have "(v, proj2_rep (proj2_abs v)) \<in> real_vector.proportionality"
    unfolding real_vector.non_zero_vectors_def
    by simp
  then obtain c where "v = c *\<^sub>R proj2_rep (proj2_abs v)"
    unfolding real_vector.proportionality_def
    by auto
  with \<open>v \<noteq> 0\<close> have "c \<noteq> 0" by auto
  hence "1/c \<noteq> 0" by simp

  from \<open>v = c *\<^sub>R proj2_rep (proj2_abs v)\<close>
  have "(1/c) *\<^sub>R v = (1/c) *\<^sub>R c *\<^sub>R proj2_rep (proj2_abs v)"
    by simp
  with \<open>c \<noteq> 0\<close> have "proj2_rep (proj2_abs v) = (1/c) *\<^sub>R v" by simp

  with \<open>1/c \<noteq> 0\<close> show "\<exists> k. k \<noteq> 0 \<and> proj2_rep (proj2_abs v) = k *\<^sub>R v"
    by blast
qed

lemma proj2_abs_abs_mult:
  assumes "proj2_abs v = proj2_abs w" and "w \<noteq> 0"
  shows "\<exists> c. v = c *\<^sub>R w"
proof cases
  assume "v = 0"
  hence "v = 0 *\<^sub>R w" by simp
  thus "\<exists> c. v = c *\<^sub>R w" ..
next
  assume "v \<noteq> 0"
  from \<open>proj2_abs v = proj2_abs w\<close>
  have "proj2_rep (proj2_abs v) = proj2_rep (proj2_abs w)" by simp
  with proj2_rep_abs2 and \<open>w \<noteq> 0\<close>
  obtain k where "proj2_rep (proj2_abs v) = k *\<^sub>R w" by auto
  with proj2_rep_abs2 [of v] and \<open>v \<noteq> 0\<close>
  obtain j where "j \<noteq> 0" and "j *\<^sub>R v = k *\<^sub>R w" by auto
  hence "(1/j) *\<^sub>R j *\<^sub>R v = (1/j) *\<^sub>R k *\<^sub>R w" by simp
  with \<open>j \<noteq> 0\<close> have "v = (k/j) *\<^sub>R w" by simp
  thus "\<exists> c. v = c *\<^sub>R w" ..
qed

lemma dependent_proj2_abs:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "i \<noteq> 0 \<or> j \<noteq> 0" and "i *\<^sub>R p + j *\<^sub>R q = 0"
  shows "proj2_abs p = proj2_abs q"
proof -
  have "i \<noteq> 0"
  proof
    assume "i = 0"
    with \<open>i \<noteq> 0 \<or> j \<noteq> 0\<close> have "j \<noteq> 0" by simp
    with \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> and \<open>q \<noteq> 0\<close> have "i *\<^sub>R p \<noteq> 0" by auto
    with \<open>i = 0\<close> show False by simp
  qed
  with \<open>p \<noteq> 0\<close> and \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> have "j \<noteq> 0" by auto

  from \<open>i \<noteq> 0\<close>
  have "proj2_abs p = proj2_abs (i *\<^sub>R p)" by (rule proj2_abs_mult [symmetric])
  also from \<open>i *\<^sub>R p + j *\<^sub>R q = 0\<close> and proj2_abs_mult [of "-1" "j *\<^sub>R q"]
  have "\<dots> = proj2_abs (j *\<^sub>R q)" by (simp add: algebra_simps [symmetric])
  also from \<open>j \<noteq> 0\<close> have "\<dots> = proj2_abs q" by (rule proj2_abs_mult)
  finally show "proj2_abs p = proj2_abs q" .
qed

lemma proj2_rep_dependent:
  assumes "i *\<^sub>R proj2_rep v + j *\<^sub>R proj2_rep w = 0"
  (is "i *\<^sub>R ?p + j *\<^sub>R ?q = 0")
  and "i \<noteq> 0 \<or> j \<noteq> 0"
  shows "v = w"
proof -
  have "?p \<noteq> 0" and "?q \<noteq> 0" by (rule proj2_rep_non_zero)+
  with \<open>i \<noteq> 0 \<or> j \<noteq> 0\<close> and \<open>i *\<^sub>R ?p + j *\<^sub>R ?q = 0\<close>
  have "proj2_abs ?p = proj2_abs ?q" by (simp add: dependent_proj2_abs)
  thus "v = w" by (simp add: proj2_abs_rep)
qed

lemma proj2_rep_independent:
  assumes "p \<noteq> q"
  shows "independent {proj2_rep p, proj2_rep q}"
proof
  let ?p' = "proj2_rep p"
  let ?q' = "proj2_rep q"
  let ?S = "{?p', ?q'}"
  assume "dependent ?S"
  from proj2_rep_inj and \<open>p \<noteq> q\<close> have "?p' \<noteq> ?q'"
    unfolding inj_on_def
    by auto
  with dependent_explicit_2 [of ?p' ?q'] and \<open>dependent ?S\<close>
  obtain i and j where "i *\<^sub>R ?p' + j *\<^sub>R ?q' = 0" and "i \<noteq> 0 \<or> j \<noteq> 0"
    by (simp add: scalar_equiv) auto
  with proj2_rep_dependent have "p = q" by simp
  with \<open>p \<noteq> q\<close> show False ..
qed

subsection "Lines of the real projective plane"

definition proj2_Col :: "[proj2, proj2, proj2] \<Rightarrow> bool" where
  "proj2_Col p q r \<equiv>
  (\<exists> i j k. i *\<^sub>R proj2_rep p + j *\<^sub>R proj2_rep q + k *\<^sub>R proj2_rep r = 0
  \<and> (i\<noteq>0 \<or> j\<noteq>0 \<or> k\<noteq>0))"

lemma proj2_Col_abs:
  assumes "p \<noteq> 0" and "q \<noteq> 0" and "r \<noteq> 0" and "i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0"
  and "i *\<^sub>R p + j *\<^sub>R q + k *\<^sub>R r = 0"
  shows "proj2_Col (proj2_abs p) (proj2_abs q) (proj2_abs r)"
  (is "proj2_Col ?pp ?pq ?pr")
proof -
  from \<open>p \<noteq> 0\<close> and proj2_rep_abs2
  obtain i' where "i' \<noteq> 0" and "proj2_rep ?pp = i' *\<^sub>R p" (is "?rp = _") by auto
  from \<open>q \<noteq> 0\<close> and proj2_rep_abs2
  obtain j' where "j' \<noteq> 0" and "proj2_rep ?pq = j' *\<^sub>R q" (is "?rq = _") by auto
  from \<open>r \<noteq> 0\<close> and proj2_rep_abs2
  obtain k' where "k' \<noteq> 0" and "proj2_rep ?pr = k' *\<^sub>R r" (is "?rr = _") by auto
  with \<open>i *\<^sub>R p + j *\<^sub>R q + k *\<^sub>R r = 0\<close>
    and \<open>i' \<noteq> 0\<close> and \<open>proj2_rep ?pp = i' *\<^sub>R p\<close>
    and \<open>j' \<noteq> 0\<close> and \<open>proj2_rep ?pq = j' *\<^sub>R q\<close>
  have "(i/i') *\<^sub>R ?rp + (j/j') *\<^sub>R ?rq + (k/k') *\<^sub>R ?rr = 0" by simp

  from \<open>i' \<noteq> 0\<close> and \<open>j' \<noteq> 0\<close> and \<open>k' \<noteq> 0\<close> and \<open>i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0\<close>
  have "i/i' \<noteq> 0 \<or> j/j' \<noteq> 0 \<or> k/k' \<noteq> 0" by simp
  with \<open>(i/i') *\<^sub>R ?rp + (j/j') *\<^sub>R ?rq + (k/k') *\<^sub>R ?rr = 0\<close>
  show "proj2_Col ?pp ?pq ?pr" by (unfold proj2_Col_def, best)
qed

lemma proj2_Col_permute:
  assumes "proj2_Col a b c"
  shows "proj2_Col a c b"
  and "proj2_Col b a c"
proof -
  let ?a' = "proj2_rep a"
  let ?b' = "proj2_rep b"
  let ?c' = "proj2_rep c"
  from \<open>proj2_Col a b c\<close>
  obtain i and j and k where
    "i *\<^sub>R ?a' + j *\<^sub>R ?b' + k *\<^sub>R ?c' = 0"
    and "i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0"
    unfolding proj2_Col_def
    by auto

  from \<open>i *\<^sub>R ?a' + j *\<^sub>R ?b' + k *\<^sub>R ?c' = 0\<close>
  have "i *\<^sub>R ?a' + k *\<^sub>R ?c' + j *\<^sub>R ?b' = 0"
    and "j *\<^sub>R ?b' + i *\<^sub>R ?a' + k *\<^sub>R ?c' = 0"
    by (simp_all add: ac_simps)
  moreover from \<open>i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0\<close>
  have "i \<noteq> 0 \<or> k \<noteq> 0 \<or> j \<noteq> 0" and "j \<noteq> 0 \<or> i \<noteq> 0 \<or> k \<noteq> 0" by auto
  ultimately show "proj2_Col a c b" and "proj2_Col b a c"
    unfolding proj2_Col_def
    by auto
qed

lemma proj2_Col_coincide: "proj2_Col a a c"
proof -
  have "1 *\<^sub>R proj2_rep a + (-1) *\<^sub>R proj2_rep a + 0 *\<^sub>R proj2_rep c = 0"
    by simp
  moreover have "(1::real) \<noteq> 0" by simp
  ultimately show "proj2_Col a a c"
    unfolding proj2_Col_def
    by blast
qed

lemma proj2_Col_iff:
  assumes "a \<noteq> r"
  shows "proj2_Col a r t \<longleftrightarrow>
  t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R (proj2_rep a) + (proj2_rep r)))"
proof
  let ?a' = "proj2_rep a"
  let ?r' = "proj2_rep r"
  let ?t' = "proj2_rep t"

  { assume "proj2_Col a r t"
    then obtain h and j and k where
      "h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' = 0"
      and "h \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0"
      unfolding proj2_Col_def
      by auto
    
    show "t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r'))"
    proof cases
      assume "j = 0"
      with \<open>h \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0\<close> have "h \<noteq> 0 \<or> k \<noteq> 0" by simp
      with proj2_rep_dependent
        and \<open>h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' = 0\<close>
        and \<open>j = 0\<close>
      have "t = a" by auto
      thus "t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r'))" ..
    next
      assume "j \<noteq> 0"
      have "k \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> k \<noteq> 0"
        with proj2_rep_dependent
          and \<open>h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' = 0\<close>
          and \<open>j \<noteq> 0\<close>
        have "a = r" by simp
        with \<open>a \<noteq> r\<close> show False ..
      qed
      
      from \<open>h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' = 0\<close>
      have "h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' - k *\<^sub>R ?t' = -k *\<^sub>R ?t'" by simp
      hence "h *\<^sub>R ?a' + j *\<^sub>R ?r' = -k *\<^sub>R ?t'" by simp
      with proj2_abs_mult_rep [of "-k"] and \<open>k \<noteq> 0\<close>
      have "proj2_abs (h *\<^sub>R ?a' + j *\<^sub>R ?r') = t" by simp
      with proj2_abs_mult [of "1/j" "h *\<^sub>R ?a' + j *\<^sub>R ?r'"] and \<open>j \<noteq> 0\<close>
      have "proj2_abs ((h/j) *\<^sub>R ?a' + ?r') = t"
        by (simp add: scaleR_right_distrib)
      hence "\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r')" by auto
      thus "t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r'))" ..
    qed
  }

  { assume "t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r'))"
    show "proj2_Col a r t"
    proof cases
      assume "t = a"
      with proj2_Col_coincide and proj2_Col_permute
      show "proj2_Col a r t" by blast
    next
      assume "t \<noteq> a"
      with \<open>t = a \<or> (\<exists> i. t = proj2_abs (i *\<^sub>R ?a' + ?r'))\<close>
      obtain i where "t = proj2_abs (i *\<^sub>R ?a' + ?r')" by auto
      from proj2_rep_dependent [of i a 1 r] and \<open>a \<noteq> r\<close>
      have "i *\<^sub>R ?a' + ?r' \<noteq> 0" by auto
      with proj2_rep_abs2 and \<open>t = proj2_abs (i *\<^sub>R ?a' + ?r')\<close>
      obtain j where "?t' = j *\<^sub>R (i *\<^sub>R ?a' + ?r')" by auto
      hence "?t' - ?t' = (j * i) *\<^sub>R ?a' + j *\<^sub>R ?r' + (-1) *\<^sub>R ?t'"
        by (simp add: scaleR_right_distrib)
      hence "(j * i) *\<^sub>R ?a' + j *\<^sub>R ?r' + (-1) *\<^sub>R ?t' = 0" by simp
      have "\<exists> h j k. h *\<^sub>R ?a' + j *\<^sub>R ?r' + k *\<^sub>R ?t' = 0
        \<and> (h \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0)"
      proof standard+
        from \<open>(j * i) *\<^sub>R ?a' + j *\<^sub>R ?r' + (-1) *\<^sub>R ?t' = 0\<close>
        show "(j * i) *\<^sub>R ?a' + j *\<^sub>R ?r' + (-1) *\<^sub>R ?t' = 0" .
        show "j * i \<noteq> 0 \<or> j \<noteq> 0 \<or> (-1::real) \<noteq> 0" by simp
      qed
      thus "proj2_Col a r t"
        unfolding proj2_Col_def .
    qed
  }
qed

definition proj2_Col_coeff :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> real" where
  "proj2_Col_coeff a r t \<equiv> \<some> i. t = proj2_abs (i *\<^sub>R proj2_rep a + proj2_rep r)"

lemma proj2_Col_coeff:
  assumes "proj2_Col a r t" and "a \<noteq> r" and "t \<noteq> a"
  shows "t = proj2_abs ((proj2_Col_coeff a r t) *\<^sub>R proj2_rep a + proj2_rep r)"
proof -
  from \<open>a \<noteq> r\<close> and \<open>proj2_Col a r t\<close> and \<open>t \<noteq> a\<close> and proj2_Col_iff
  have "\<exists> i. t = proj2_abs (i *\<^sub>R proj2_rep a + proj2_rep r)" by simp
  thus "t = proj2_abs ((proj2_Col_coeff a r t) *\<^sub>R proj2_rep a + proj2_rep r)"
    by (unfold proj2_Col_coeff_def) (rule someI_ex)
qed

lemma proj2_Col_coeff_unique':
  assumes "a \<noteq> 0" and "r \<noteq> 0" and "proj2_abs a \<noteq> proj2_abs r"
  and "proj2_abs (i *\<^sub>R a + r) = proj2_abs (j *\<^sub>R a + r)"
  shows "i = j"
proof -
  from \<open>a \<noteq> 0\<close> and \<open>r \<noteq> 0\<close> and \<open>proj2_abs a \<noteq> proj2_abs r\<close>
    and dependent_proj2_abs [of a r _ 1]
  have "i *\<^sub>R a + r \<noteq> 0" and "j *\<^sub>R a + r \<noteq> 0" by auto
  with proj2_rep_abs2 [of "i *\<^sub>R a + r"]
    and proj2_rep_abs2 [of "j *\<^sub>R a + r"]
  obtain k and l where "k \<noteq> 0"
    and "proj2_rep (proj2_abs (i *\<^sub>R a + r)) = k *\<^sub>R (i *\<^sub>R a + r)"
    and "proj2_rep (proj2_abs (j *\<^sub>R a + r)) = l *\<^sub>R (j *\<^sub>R a + r)"
    by auto
  with \<open>proj2_abs (i *\<^sub>R a + r) = proj2_abs (j *\<^sub>R a + r)\<close>
  have "(k * i) *\<^sub>R a + k *\<^sub>R r = (l * j) *\<^sub>R a + l *\<^sub>R r"
    by (simp add: scaleR_right_distrib)
  hence "(k * i - l * j) *\<^sub>R a + (k - l) *\<^sub>R r = 0"
    by (simp add: algebra_simps vec_eq_iff)
  with \<open>a \<noteq> 0\<close> and \<open>r \<noteq> 0\<close> and \<open>proj2_abs a \<noteq> proj2_abs r\<close>
    and dependent_proj2_abs [of a r "k * i - l * j" "k - l"]
  have "k * i - l * j = 0" and "k - l = 0" by auto
  from \<open>k - l = 0\<close> have "k = l" by simp
  with \<open>k * i - l * j = 0\<close> have "k * i = k * j" by simp
  with \<open>k \<noteq> 0\<close> show "i = j" by simp
qed

lemma proj2_Col_coeff_unique:
  assumes "a \<noteq> r"
  and "proj2_abs (i *\<^sub>R proj2_rep a + proj2_rep r)
  = proj2_abs (j *\<^sub>R proj2_rep a + proj2_rep r)"
  shows "i = j"
proof -
  let ?a' = "proj2_rep a"
  let ?r' = "proj2_rep r"
  have "?a' \<noteq> 0" and "?r' \<noteq> 0" by (rule proj2_rep_non_zero)+

  from \<open>a \<noteq> r\<close> have "proj2_abs ?a' \<noteq> proj2_abs ?r'" by (simp add: proj2_abs_rep)
  with \<open>?a' \<noteq> 0\<close> and \<open>?r' \<noteq> 0\<close>
    and \<open>proj2_abs (i *\<^sub>R ?a' + ?r') = proj2_abs (j *\<^sub>R ?a' + ?r')\<close>
    and proj2_Col_coeff_unique'
  show "i = j" by simp
qed

datatype proj2_line = P2L proj2

definition L2P :: "proj2_line \<Rightarrow> proj2" where
  "L2P l \<equiv> case l of P2L p \<Rightarrow> p"

lemma L2P_P2L [simp]: "L2P (P2L p) = p"
  unfolding L2P_def
  by simp

lemma P2L_L2P [simp]: "P2L (L2P l) = l"
  by (induct l) simp

lemma L2P_inj [simp]:
  assumes "L2P l = L2P m"
  shows "l = m"
  using P2L_L2P [of l] and assms
  by simp

lemma P2L_to_L2P: "P2L p = l \<longleftrightarrow> p = L2P l"
proof
  assume "P2L p = l"
  hence "L2P (P2L p) = L2P l" by simp
  thus "p = L2P l" by simp
next
  assume "p = L2P l"
  thus "P2L p = l" by simp
qed

definition proj2_line_abs :: "real^3 \<Rightarrow> proj2_line" where
  "proj2_line_abs v \<equiv> P2L (proj2_abs v)"

definition proj2_line_rep :: "proj2_line \<Rightarrow> real^3" where
  "proj2_line_rep l \<equiv> proj2_rep (L2P l)"

lemma proj2_line_rep_abs:
  assumes "v \<noteq> 0"
  shows "\<exists> k. k \<noteq> 0 \<and> proj2_line_rep (proj2_line_abs v) = k *\<^sub>R v"
  unfolding proj2_line_rep_def and proj2_line_abs_def
  using proj2_rep_abs2 and \<open>v \<noteq> 0\<close>
  by simp

lemma proj2_line_abs_rep [simp]: "proj2_line_abs (proj2_line_rep l) = l"
  unfolding proj2_line_abs_def and proj2_line_rep_def
  by (simp add: proj2_abs_rep)

lemma proj2_line_rep_non_zero: "proj2_line_rep l \<noteq> 0"
  unfolding proj2_line_rep_def
  using proj2_rep_non_zero
  by simp

lemma proj2_line_rep_dependent:
  assumes "i *\<^sub>R proj2_line_rep l + j *\<^sub>R proj2_line_rep m = 0"
  and "i \<noteq> 0 \<or> j \<noteq> 0"
  shows "l = m"
  using proj2_rep_dependent [of i "L2P l" j "L2P m"] and assms
  unfolding proj2_line_rep_def
  by simp

lemma proj2_line_abs_mult:
  assumes "k \<noteq> 0"
  shows "proj2_line_abs (k *\<^sub>R v) = proj2_line_abs v"
  unfolding proj2_line_abs_def
  using \<open>k \<noteq> 0\<close>
  by (subst proj2_abs_mult) simp_all

lemma proj2_line_abs_abs_mult:
  assumes "proj2_line_abs v = proj2_line_abs w" and "w \<noteq> 0"
  shows "\<exists> k. v = k *\<^sub>R w"
  using assms
  by (unfold proj2_line_abs_def) (simp add: proj2_abs_abs_mult)

definition proj2_incident :: "proj2 \<Rightarrow> proj2_line \<Rightarrow> bool" where
  "proj2_incident p l \<equiv> (proj2_rep p) \<bullet> (proj2_line_rep l) = 0"

lemma proj2_points_define_line:
  shows "\<exists> l. proj2_incident p l \<and> proj2_incident q l"
proof -
  let ?p' = "proj2_rep p"
  let ?q' = "proj2_rep q"
  let ?B = "{?p', ?q'}"
  from card_suc_ge_insert [of ?p' "{?q'}"] have "card ?B \<le> 2" by simp
  with dim_le_card' [of ?B] have "dim ?B < 3" by simp
  with lowdim_subset_hyperplane [of ?B]
  obtain l' where "l' \<noteq> 0" and "span ?B \<subseteq> {x. l' \<bullet> x = 0}" by auto
  let ?l = "proj2_line_abs l'"
  let ?l'' = "proj2_line_rep ?l"
  from proj2_line_rep_abs and \<open>l' \<noteq> 0\<close>
  obtain k where "?l'' = k *\<^sub>R l'" by auto

  have "?p' \<in> ?B" and "?q' \<in> ?B" by simp_all
  with span_superset [of ?B] and \<open>span ?B \<subseteq> {x. l' \<bullet> x = 0}\<close>
  have "l' \<bullet> ?p' = 0" and "l' \<bullet> ?q' = 0" by auto
  hence "?p' \<bullet> l' = 0" and "?q' \<bullet> l' = 0" by (simp_all add: inner_commute)
  with dot_scaleR_mult(2) [of _ k l'] and \<open>?l'' = k *\<^sub>R l'\<close>
  have "proj2_incident p ?l \<and> proj2_incident q ?l"
    unfolding proj2_incident_def
    by simp
  thus "\<exists> l. proj2_incident p l \<and> proj2_incident q l" by auto
qed

definition proj2_line_through :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2_line" where
  "proj2_line_through p q \<equiv> \<some> l. proj2_incident p l \<and> proj2_incident q l"

lemma proj2_line_through_incident:
  shows "proj2_incident p (proj2_line_through p q)"
  and "proj2_incident q (proj2_line_through p q)"
  unfolding proj2_line_through_def
  using proj2_points_define_line
    and someI_ex [of "\<lambda> l. proj2_incident p l \<and> proj2_incident q l"]
  by simp_all

lemma proj2_line_through_unique:
  assumes "p \<noteq> q" and "proj2_incident p l" and "proj2_incident q l"
  shows "l = proj2_line_through p q"
proof -
  let ?l' = "proj2_line_rep l"
  let ?m = "proj2_line_through p q"
  let ?m' = "proj2_line_rep ?m"
  let ?p' = "proj2_rep p"
  let ?q' = "proj2_rep q"
  let ?A = "{?p', ?q'}"
  let ?B = "insert ?m' ?A"
  from proj2_line_through_incident
  have "proj2_incident p ?m" and "proj2_incident q ?m" by simp_all
  with \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
  have ortho: "\<And>w. w\<in>?A \<Longrightarrow> orthogonal ?m' w" "\<And>w. w\<in>?A \<Longrightarrow> orthogonal ?l' w"
    unfolding proj2_incident_def and orthogonal_def
    by (metis empty_iff inner_commute insert_iff)+
  from proj2_rep_independent and \<open>p \<noteq> q\<close> have "independent ?A" by simp
  from proj2_line_rep_non_zero have "?m' \<noteq> 0" by simp
  with orthogonal_independent \<open>independent ?A\<close> ortho
  have "independent ?B" by auto

  from proj2_rep_inj and \<open>p \<noteq> q\<close> have "?p' \<noteq> ?q'"
    unfolding inj_on_def
    by auto
  hence "card ?A = 2" by simp
  moreover have "?m' \<notin> ?A"
    using ortho(1) orthogonal_self proj2_line_rep_non_zero by auto
  ultimately have "card ?B = 3" by simp
  with independent_is_basis [of ?B] and \<open>independent ?B\<close>
  have "is_basis ?B" by simp
  with basis_expand obtain c where "?l' = (\<Sum> v\<in>?B. c v *\<^sub>R v)" by auto
  let ?l'' = "?l' - c ?m' *\<^sub>R ?m'"
  from \<open>?l' = (\<Sum> v\<in>?B. c v *\<^sub>R v)\<close> and \<open>?m' \<notin> ?A\<close>
  have "?l'' = (\<Sum> v\<in>?A. c v *\<^sub>R v)" by simp
  with orthogonal_sum [of ?A] ortho
  have "orthogonal ?l' ?l''" and "orthogonal ?m' ?l''"
    by (simp_all add: scalar_equiv)
  from \<open>orthogonal ?m' ?l''\<close>
  have "orthogonal (c ?m' *\<^sub>R ?m') ?l''" by (simp add: orthogonal_clauses)
  with \<open>orthogonal ?l' ?l''\<close>
  have "orthogonal ?l'' ?l''" by (simp add: orthogonal_clauses)
  with orthogonal_self_eq_0 [of ?l''] have "?l'' = 0" by simp
  with proj2_line_rep_dependent [of 1 l "- c ?m'" ?m] show "l = ?m" by simp
qed

lemma proj2_incident_unique:
  assumes "proj2_incident p l"
  and "proj2_incident q l"
  and "proj2_incident p m"
  and "proj2_incident q m"
  shows "p = q \<or> l = m"
proof cases
  assume "p = q"
  thus "p = q \<or> l = m" ..
next
  assume "p \<noteq> q"
  with \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
    and proj2_line_through_unique
  have "l = proj2_line_through p q" by simp
  moreover from \<open>p \<noteq> q\<close> and \<open>proj2_incident p m\<close> and \<open>proj2_incident q m\<close>
  have "m = proj2_line_through p q" by (rule proj2_line_through_unique)
  ultimately show "p = q \<or> l = m" by simp
qed

lemma proj2_lines_define_point: "\<exists> p. proj2_incident p l \<and> proj2_incident p m"
proof -
  let ?l' = "L2P l"
  let ?m' = "L2P m"
  from proj2_points_define_line [of ?l' ?m']
  obtain p' where "proj2_incident ?l' p' \<and> proj2_incident ?m' p'" by auto
  hence "proj2_incident (L2P p') l \<and> proj2_incident (L2P p') m"
    unfolding proj2_incident_def and proj2_line_rep_def
    by (simp add: inner_commute)
  thus "\<exists> p. proj2_incident p l \<and> proj2_incident p m" by auto
qed

definition proj2_intersection :: "proj2_line \<Rightarrow> proj2_line \<Rightarrow> proj2" where
  "proj2_intersection l m \<equiv> L2P (proj2_line_through (L2P l) (L2P m))"

lemma proj2_incident_switch:
  assumes "proj2_incident p l"
  shows "proj2_incident (L2P l) (P2L p)"
  using assms
  unfolding proj2_incident_def and proj2_line_rep_def
  by (simp add: inner_commute)

lemma proj2_intersection_incident:
  shows "proj2_incident (proj2_intersection l m) l"
  and "proj2_incident (proj2_intersection l m) m"
  using proj2_line_through_incident(1) [of "L2P l" "L2P m"]
    and proj2_line_through_incident(2) [of "L2P m" "L2P l"]
    and proj2_incident_switch [of "L2P l"]
    and proj2_incident_switch [of "L2P m"]
  unfolding proj2_intersection_def
  by simp_all

lemma proj2_intersection_unique:
  assumes "l \<noteq> m" and "proj2_incident p l" and "proj2_incident p m"
  shows "p = proj2_intersection l m"
proof -
  from \<open>l \<noteq> m\<close> have "L2P l \<noteq> L2P m" by auto
  from \<open>proj2_incident p l\<close> and \<open>proj2_incident p m\<close>
    and proj2_incident_switch
  have "proj2_incident (L2P l) (P2L p)" and "proj2_incident (L2P m) (P2L p)"
    by simp_all
  with \<open>L2P l \<noteq> L2P m\<close> and proj2_line_through_unique
  have "P2L p = proj2_line_through (L2P l) (L2P m)" by simp
  thus "p = proj2_intersection l m"
    unfolding proj2_intersection_def
    by (simp add: P2L_to_L2P)
qed

lemma proj2_not_self_incident:
  "\<not> (proj2_incident p (P2L p))"
  unfolding proj2_incident_def and proj2_line_rep_def
  using proj2_rep_non_zero and inner_eq_zero_iff [of "proj2_rep p"]
  by simp

lemma proj2_another_point_on_line:
  "\<exists> q. q \<noteq> p \<and> proj2_incident q l"
proof -
  let ?m = "P2L p"
  let ?q = "proj2_intersection l ?m"
  from proj2_intersection_incident
  have "proj2_incident ?q l" and "proj2_incident ?q ?m" by simp_all
  from \<open>proj2_incident ?q ?m\<close> and proj2_not_self_incident have "?q \<noteq> p" by auto
  with \<open>proj2_incident ?q l\<close> show "\<exists> q. q \<noteq> p \<and> proj2_incident q l" by auto
qed

lemma proj2_another_line_through_point:
  "\<exists> m. m \<noteq> l \<and> proj2_incident p m"
proof -
  from proj2_another_point_on_line
  obtain q where "q \<noteq> L2P l \<and> proj2_incident q (P2L p)" by auto
  with proj2_incident_switch [of q "P2L p"]
  have "P2L q \<noteq> l \<and> proj2_incident p (P2L q)" by auto
  thus "\<exists> m. m \<noteq> l \<and> proj2_incident p m" ..
qed

lemma proj2_incident_abs:
  assumes "v \<noteq> 0" and "w \<noteq> 0"
  shows "proj2_incident (proj2_abs v) (proj2_line_abs w) \<longleftrightarrow> v \<bullet> w = 0"
proof -
  from \<open>v \<noteq> 0\<close> and proj2_rep_abs2
  obtain j where "j \<noteq> 0" and "proj2_rep (proj2_abs v) = j *\<^sub>R v" by auto

  from \<open>w \<noteq> 0\<close> and proj2_line_rep_abs
  obtain k where "k \<noteq> 0"
    and "proj2_line_rep (proj2_line_abs w) = k *\<^sub>R w"
    by auto
  with \<open>j \<noteq> 0\<close> and \<open>proj2_rep (proj2_abs v) = j *\<^sub>R v\<close>
  show "proj2_incident (proj2_abs v) (proj2_line_abs w) \<longleftrightarrow> v \<bullet> w = 0"
    unfolding proj2_incident_def
    by (simp add: dot_scaleR_mult)
qed

lemma proj2_incident_left_abs:
  assumes "v \<noteq> 0"
  shows "proj2_incident (proj2_abs v) l \<longleftrightarrow> v \<bullet> (proj2_line_rep l) = 0"
proof -
  have "proj2_line_rep l \<noteq> 0" by (rule proj2_line_rep_non_zero)
  with \<open>v \<noteq> 0\<close> and proj2_incident_abs [of v "proj2_line_rep l"]
  show "proj2_incident (proj2_abs v) l \<longleftrightarrow> v \<bullet> (proj2_line_rep l) = 0" by simp
qed

lemma proj2_incident_right_abs:
  assumes "v \<noteq> 0"
  shows "proj2_incident p (proj2_line_abs v) \<longleftrightarrow> (proj2_rep p) \<bullet> v = 0"
proof -
  have "proj2_rep p \<noteq> 0" by (rule proj2_rep_non_zero)
  with \<open>v \<noteq> 0\<close> and proj2_incident_abs [of "proj2_rep p" v]
  show "proj2_incident p (proj2_line_abs v) \<longleftrightarrow> (proj2_rep p) \<bullet> v = 0"
    by (simp add: proj2_abs_rep)
qed

definition proj2_set_Col :: "proj2 set \<Rightarrow> bool" where
  "proj2_set_Col S \<equiv> \<exists> l. \<forall> p\<in>S. proj2_incident p l"

lemma proj2_subset_Col:
  assumes "T \<subseteq> S" and "proj2_set_Col S"
  shows "proj2_set_Col T"
  using \<open>T \<subseteq> S\<close> and \<open>proj2_set_Col S\<close>
  by (unfold proj2_set_Col_def) auto

definition proj2_no_3_Col :: "proj2 set \<Rightarrow> bool" where
  "proj2_no_3_Col S \<equiv> card S = 4 \<and> (\<forall> p\<in>S. \<not> proj2_set_Col (S - {p}))"

lemma proj2_Col_iff_not_invertible:
  "proj2_Col p q r
  \<longleftrightarrow> \<not> invertible (vector [proj2_rep p, proj2_rep q, proj2_rep r] :: real^3^3)"
  (is "_ \<longleftrightarrow> \<not> invertible (vector [?u, ?v, ?w])")
proof -
  let ?M = "vector [?u,?v,?w] :: real^3^3"
  have "proj2_Col p q r \<longleftrightarrow> (\<exists> x. x \<noteq> 0 \<and> x v* ?M = 0)"
  proof
    assume "proj2_Col p q r"
    then obtain i and j and k
      where "i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0" and "i *\<^sub>R ?u + j *\<^sub>R ?v + k *\<^sub>R ?w = 0"
      unfolding proj2_Col_def
      by auto
    let ?x = "vector [i,j,k] :: real^3"
    from \<open>i \<noteq> 0 \<or> j \<noteq> 0 \<or> k \<noteq> 0\<close>
    have "?x \<noteq> 0"
      unfolding vector_def
      by (simp add: vec_eq_iff forall_3)
    moreover {
      from \<open>i *\<^sub>R ?u + j *\<^sub>R ?v + k *\<^sub>R ?w = 0\<close>
      have "?x v* ?M = 0"
        unfolding vector_def and vector_matrix_mult_def
        by (simp add: sum_3 vec_eq_iff algebra_simps) }
    ultimately show "\<exists> x. x \<noteq> 0 \<and> x v* ?M = 0" by auto
  next
    assume "\<exists> x. x \<noteq> 0 \<and> x v* ?M = 0"
    then obtain x where "x \<noteq> 0" and "x v* ?M = 0" by auto
    let ?i = "x$1"
    let ?j = "x$2"
    let ?k = "x$3"
    from \<open>x \<noteq> 0\<close> have "?i \<noteq> 0 \<or> ?j \<noteq> 0 \<or> ?k \<noteq> 0" by (simp add: vec_eq_iff forall_3)
    moreover {
      from \<open>x v* ?M = 0\<close>
      have "?i *\<^sub>R ?u + ?j *\<^sub>R ?v + ?k *\<^sub>R ?w = 0"
        unfolding vector_matrix_mult_def and sum_3 and vector_def
        by (simp add: vec_eq_iff algebra_simps) }
    ultimately show "proj2_Col p q r"
      unfolding proj2_Col_def
      by auto
  qed
  also from matrix_right_invertible_ker [of ?M]
  have "\<dots> \<longleftrightarrow> \<not> (\<exists> M'. ?M ** M' = mat 1)" by auto
  also from matrix_left_right_inverse
  have "\<dots> \<longleftrightarrow> \<not> invertible ?M"
    unfolding invertible_def
    by auto
  finally show "proj2_Col p q r \<longleftrightarrow> \<not> invertible ?M" .
qed

lemma not_invertible_iff_proj2_set_Col:
  "\<not> invertible (vector [proj2_rep p, proj2_rep q, proj2_rep r] :: real^3^3)
  \<longleftrightarrow> proj2_set_Col {p,q,r}"
  (is "\<not> invertible ?M \<longleftrightarrow> _")
proof -
  from left_invertible_iff_invertible
  have "\<not> invertible ?M  \<longleftrightarrow> \<not> (\<exists> M'. M' ** ?M = mat 1)" by auto
  also from matrix_left_invertible_ker [of ?M]
  have "\<dots> \<longleftrightarrow> (\<exists> y. y \<noteq> 0 \<and> ?M *v y = 0)" by auto
  also have "\<dots> \<longleftrightarrow> (\<exists> l. \<forall> s\<in>{p,q,r}. proj2_incident s l)"
  proof
    assume "\<exists> y. y \<noteq> 0 \<and> ?M *v y = 0"
    then obtain y where "y \<noteq> 0" and "?M *v y = 0" by auto
    let ?l = "proj2_line_abs y"
    from \<open>?M *v y = 0\<close>
    have "\<forall> s\<in>{p,q,r}. proj2_rep s \<bullet> y = 0"
      unfolding vector_def
        and matrix_vector_mult_def
        and inner_vec_def
        and sum_3
      by (simp add: vec_eq_iff forall_3)
    with \<open>y \<noteq> 0\<close> and proj2_incident_right_abs
    have "\<forall> s\<in>{p,q,r}. proj2_incident s ?l" by simp
    thus "\<exists> l. \<forall> s\<in>{p,q,r}. proj2_incident s l" ..
  next
    assume "\<exists> l. \<forall> s\<in>{p,q,r}. proj2_incident s l"
    then obtain l where "\<forall> s\<in>{p,q,r}. proj2_incident s l" ..
    let ?y = "proj2_line_rep l"
    have "?y \<noteq> 0" by (rule proj2_line_rep_non_zero)
    moreover {
      from \<open>\<forall> s\<in>{p,q,r}. proj2_incident s l\<close>
      have "?M *v ?y = 0"
        unfolding vector_def
          and matrix_vector_mult_def
          and inner_vec_def
          and sum_3
          and proj2_incident_def
        by (simp add: vec_eq_iff) }
    ultimately show "\<exists> y. y \<noteq> 0 \<and> ?M *v y = 0" by auto
  qed
  finally show "\<not> invertible ?M \<longleftrightarrow> proj2_set_Col {p,q,r}"
    unfolding proj2_set_Col_def .
qed

lemma proj2_Col_iff_set_Col:
  "proj2_Col p q r \<longleftrightarrow> proj2_set_Col {p,q,r}"
  by (simp add: proj2_Col_iff_not_invertible
    not_invertible_iff_proj2_set_Col)

lemma proj2_incident_Col:
  assumes "proj2_incident p l" and "proj2_incident q l" and "proj2_incident r l"
  shows "proj2_Col p q r"
proof -
  from \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close> and \<open>proj2_incident r l\<close>
  have "proj2_set_Col {p,q,r}" by (unfold proj2_set_Col_def) auto
  thus "proj2_Col p q r" by (subst proj2_Col_iff_set_Col)
qed

lemma proj2_incident_iff_Col:
  assumes "p \<noteq> q" and "proj2_incident p l" and "proj2_incident q l"
  shows "proj2_incident r l \<longleftrightarrow> proj2_Col p q r"
proof
  assume "proj2_incident r l"
  with \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
  show "proj2_Col p q r" by (rule proj2_incident_Col)
next
  assume "proj2_Col p q r"
  hence "proj2_set_Col {p,q,r}" by (simp add: proj2_Col_iff_set_Col)
  then obtain m where "\<forall> s\<in>{p,q,r}. proj2_incident s m"
    unfolding proj2_set_Col_def ..
  hence "proj2_incident p m" and "proj2_incident q m" and "proj2_incident r m"
    by simp_all
  from \<open>p \<noteq> q\<close> and \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
    and \<open>proj2_incident p m\<close> and \<open>proj2_incident q m\<close>
    and proj2_incident_unique
  have "m = l" by auto
  with \<open>proj2_incident r m\<close> show "proj2_incident r l" by simp
qed

lemma proj2_incident_iff:
  assumes "p \<noteq> q" and "proj2_incident p l" and "proj2_incident q l"
  shows "proj2_incident r l
  \<longleftrightarrow> r = p \<or> (\<exists> k. r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q))"
proof -
  from \<open>p \<noteq> q\<close> and \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
  have "proj2_incident r l \<longleftrightarrow> proj2_Col p q r" by (rule proj2_incident_iff_Col)
  with \<open>p \<noteq> q\<close> and proj2_Col_iff
  show "proj2_incident r l
    \<longleftrightarrow> r = p \<or> (\<exists> k. r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q))"
    by simp
qed

lemma not_proj2_set_Col_iff_span:
  assumes "card S = 3"
  shows "\<not> proj2_set_Col S \<longleftrightarrow> span (proj2_rep ` S) = UNIV"
proof -
  from \<open>card S = 3\<close> and choose_3 [of S]
  obtain p and q and r where "S = {p,q,r}" by auto
  let ?u = "proj2_rep p"
  let ?v = "proj2_rep q"
  let ?w = "proj2_rep r"
  let ?M = "vector [?u, ?v, ?w] :: real^3^3"
  from \<open>S = {p,q,r}\<close> and not_invertible_iff_proj2_set_Col [of p q r]
  have "\<not> proj2_set_Col S \<longleftrightarrow> invertible ?M" by auto
  also from left_invertible_iff_invertible
  have "\<dots> \<longleftrightarrow> (\<exists> N. N ** ?M = mat 1)" ..
  also from matrix_left_invertible_span_rows
  have "\<dots> \<longleftrightarrow> span (rows ?M) = UNIV" by auto
  finally have "\<not> proj2_set_Col S \<longleftrightarrow> span (rows ?M) = UNIV" .

  have "rows ?M = {?u, ?v, ?w}"
  proof
    { fix x
      assume "x \<in> rows ?M"
      then obtain i :: 3  where "x = ?M $ i"
        unfolding rows_def and row_def
        by (auto simp add: vec_lambda_beta vec_lambda_eta)
      with exhaust_3 have "x = ?u \<or> x = ?v \<or> x = ?w"
        unfolding vector_def
        by auto
      hence "x \<in> {?u, ?v, ?w}" by simp }
    thus "rows ?M \<subseteq> {?u, ?v, ?w}" ..
    { fix x
      assume "x \<in> {?u, ?v, ?w}"
      hence "x = ?u \<or> x = ?v \<or> x = ?w" by simp
      hence "x = ?M $ 1 \<or> x = ?M $ 2 \<or> x = ?M $ 3"
        unfolding vector_def
        by simp
      hence "x \<in> rows ?M"
        unfolding rows_def row_def vec_lambda_eta
        by blast }
    thus "{?u, ?v, ?w} \<subseteq> rows ?M" ..
  qed
  with \<open>S = {p,q,r}\<close>
  have "rows ?M = proj2_rep ` S"
    unfolding image_def
    by auto
  with \<open>\<not> proj2_set_Col S \<longleftrightarrow> span (rows ?M) = UNIV\<close>
  show "\<not> proj2_set_Col S \<longleftrightarrow> span (proj2_rep ` S) = UNIV" by simp
qed

lemma proj2_no_3_Col_span:
  assumes "proj2_no_3_Col S" and "p \<in> S"
  shows "span (proj2_rep ` (S - {p})) = UNIV"
proof -
  from \<open>proj2_no_3_Col S\<close> have "card S = 4" unfolding proj2_no_3_Col_def ..
  with \<open>p \<in> S\<close> and \<open>card S = 4\<close> and card_gt_0_diff_singleton [of S p]
  have "card (S - {p}) = 3" by simp

  from \<open>proj2_no_3_Col S\<close> and \<open>p \<in> S\<close>
  have "\<not> proj2_set_Col (S - {p})"
    unfolding proj2_no_3_Col_def
    by simp
  with \<open>card (S - {p}) = 3\<close> and not_proj2_set_Col_iff_span
  show "span (proj2_rep ` (S - {p})) = UNIV" by simp
qed

lemma fourth_proj2_no_3_Col:
  assumes "\<not> proj2_Col p q r"
  shows "\<exists> s. proj2_no_3_Col {s,r,p,q}"
proof -
  from \<open>\<not> proj2_Col p q r\<close> and proj2_Col_coincide have "p \<noteq> q" by auto
  hence "card {p,q} = 2" by simp

  from \<open>\<not> proj2_Col p q r\<close> and proj2_Col_coincide and proj2_Col_permute
  have "r \<notin> {p,q}" by fast
  with \<open>card {p,q} = 2\<close> have "card {r,p,q} = 3" by simp

  have "finite {r,p,q}" by simp

  let ?s = "proj2_abs (\<Sum> t\<in>{r,p,q}. proj2_rep t)"
  have "\<exists> j. (\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s"
  proof cases
    assume "(\<Sum> t\<in>{r,p,q}. proj2_rep t) = 0"
    hence "(\<Sum> t\<in>{r,p,q}. proj2_rep t) = 0 *\<^sub>R proj2_rep ?s" by simp
    thus "\<exists> j. (\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s" ..
  next
    assume "(\<Sum> t\<in>{r,p,q}. proj2_rep t) \<noteq> 0"
    with proj2_rep_abs2
    obtain k where "k \<noteq> 0"
      and "proj2_rep ?s = k *\<^sub>R (\<Sum> t\<in>{r,p,q}. proj2_rep t)"
      by auto
    hence "(1/k) *\<^sub>R proj2_rep ?s = (\<Sum> t\<in>{r,p,q}. proj2_rep t)" by simp
    from this [symmetric]
    show "\<exists> j. (\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s" ..
  qed
  then obtain j where "(\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s" ..
  let ?c = "\<lambda> t. if t = ?s then 1 - j else 1"
  from \<open>p \<noteq> q\<close> have "?c p \<noteq> 0 \<or> ?c q \<noteq> 0" by simp

  let ?d = "\<lambda> t. if t = ?s then j else -1"

  let ?S = "{?s,r,p,q}"

  have "?s \<notin> {r,p,q}"
  proof
    assume "?s \<in> {r,p,q}"

    from \<open>r \<notin> {p,q}\<close> and \<open>p \<noteq> q\<close>
    have "?c r *\<^sub>R proj2_rep r + ?c p *\<^sub>R proj2_rep p + ?c q *\<^sub>R proj2_rep q
      = (\<Sum> t\<in>{r,p,q}. ?c t *\<^sub>R proj2_rep t)"
      by (simp add: sum.insert [of _ _ "\<lambda> t. ?c t *\<^sub>R proj2_rep t"])
    also from \<open>finite {r,p,q}\<close> and \<open>?s \<in> {r,p,q}\<close>
    have "\<dots> = ?c ?s *\<^sub>R proj2_rep ?s + (\<Sum> t\<in>{r,p,q}-{?s}. ?c t *\<^sub>R proj2_rep t)"
      by (simp only:
        sum.remove [of "{r,p,q}" ?s "\<lambda> t. ?c t *\<^sub>R proj2_rep t"])
    also have "\<dots>
      = -j *\<^sub>R proj2_rep ?s + (proj2_rep ?s + (\<Sum> t\<in>{r,p,q}-{?s}. proj2_rep t))"
      by (simp add: algebra_simps)
    also from \<open>finite {r,p,q}\<close> and \<open>?s \<in> {r,p,q}\<close>
    have "\<dots> = -j *\<^sub>R proj2_rep ?s + (\<Sum> t\<in>{r,p,q}. proj2_rep t)"
      by (simp only:
        sum.remove [of "{r,p,q}" ?s "\<lambda> t. proj2_rep t",symmetric])
    also from \<open>(\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s\<close>
    have "\<dots> = 0" by simp
    finally
    have "?c r *\<^sub>R proj2_rep r + ?c p *\<^sub>R proj2_rep p + ?c q *\<^sub>R proj2_rep q = 0"
      .
    with \<open>?c p \<noteq> 0 \<or> ?c q \<noteq> 0\<close>
    have "proj2_Col p q r"
      by (unfold proj2_Col_def) (auto simp add: algebra_simps)
    with \<open>\<not> proj2_Col p q r\<close> show False ..
  qed
  with \<open>card {r,p,q} = 3\<close> have "card ?S = 4" by simp

  from \<open>\<not> proj2_Col p q r\<close> and proj2_Col_permute
  have "\<not> proj2_Col r p q" by fast
  hence "\<not> proj2_set_Col {r,p,q}" by (subst proj2_Col_iff_set_Col [symmetric])

  have "\<forall> u\<in>?S. \<not> proj2_set_Col (?S - {u})"
  proof
    fix u
    assume "u \<in> ?S"
    with \<open>card ?S = 4\<close> have "card (?S - {u}) = 3" by simp
    show "\<not> proj2_set_Col (?S - {u})"
    proof cases
      assume "u = ?s"
      with \<open>?s \<notin> {r,p,q}\<close> have "?S - {u} = {r,p,q}" by simp
      with \<open>\<not> proj2_set_Col {r,p,q}\<close> show "\<not> proj2_set_Col (?S - {u})" by simp
    next
      assume "u \<noteq> ?s"
      hence "insert ?s ({r,p,q} - {u}) = ?S - {u}" by auto

      from \<open>finite {r,p,q}\<close> have "finite ({r,p,q} - {u})" by simp

      from \<open>?s \<notin> {r,p,q}\<close> have "?s \<notin> {r,p,q} - {u}" by simp
      hence "\<forall> t\<in>{r,p,q}-{u}. ?d t = -1" by auto

      from \<open>u \<noteq> ?s\<close> and  \<open>u \<in> ?S\<close> have "u \<in> {r,p,q}" by simp
      hence "(\<Sum> t\<in>{r,p,q}. proj2_rep t)
        = proj2_rep u + (\<Sum> t\<in>{r,p,q}-{u}. proj2_rep t)"
        by (simp add: sum.remove)
      with \<open>(\<Sum> t\<in>{r,p,q}. proj2_rep t) = j *\<^sub>R proj2_rep ?s\<close>
      have "proj2_rep u
        = j *\<^sub>R proj2_rep ?s - (\<Sum> t\<in>{r,p,q}-{u}. proj2_rep t)"
        by simp
      also from \<open>\<forall> t\<in>{r,p,q}-{u}. ?d t = -1\<close>
      have "\<dots> = j *\<^sub>R proj2_rep ?s + (\<Sum> t\<in>{r,p,q}-{u}. ?d t *\<^sub>R proj2_rep t)"
        by (simp add: sum_negf)
      also from \<open>finite ({r,p,q} - {u})\<close>  and \<open>?s \<notin> {r,p,q} - {u}\<close>
      have "\<dots> = (\<Sum> t\<in>insert ?s ({r,p,q}-{u}). ?d t *\<^sub>R proj2_rep t)"
        by (simp add: sum.insert)
      also from \<open>insert ?s ({r,p,q} - {u}) = ?S - {u}\<close>
      have "\<dots> = (\<Sum> t\<in>?S-{u}. ?d t *\<^sub>R proj2_rep t)" by simp
      finally have "proj2_rep u = (\<Sum> t\<in>?S-{u}. ?d t *\<^sub>R proj2_rep t)" .
      moreover
      have "\<forall> t\<in>?S-{u}. ?d t *\<^sub>R proj2_rep t \<in> span (proj2_rep ` (?S - {u}))"
        by (simp add: span_clauses)
      ultimately have "proj2_rep u \<in> span (proj2_rep ` (?S - {u}))"
        by (metis (no_types, lifting) span_sum)

      have "\<forall> t\<in>{r,p,q}. proj2_rep t \<in> span (proj2_rep ` (?S - {u}))"
      proof
        fix t
        assume "t \<in> {r,p,q}"
        show "proj2_rep t \<in> span (proj2_rep ` (?S - {u}))"
        proof cases
          assume "t = u"
          from \<open>proj2_rep u \<in> span (image proj2_rep (?S - {u}))\<close>
          show "proj2_rep t \<in> span (proj2_rep ` (?S - {u}))"
            by (subst \<open>t = u\<close>)
        next
          assume "t \<noteq> u"
          with \<open>t \<in> {r,p,q}\<close>
          have "proj2_rep t \<in> proj2_rep ` (?S - {u})" by simp
          with span_superset [of "proj2_rep ` (?S - {u})"]
          show "proj2_rep t \<in> span (proj2_rep ` (?S - {u}))" by fast
        qed
      qed
      hence "proj2_rep ` {r,p,q} \<subseteq> span (proj2_rep ` (?S - {u}))"
        by (simp only: image_subset_iff)
      hence
        "span (proj2_rep ` {r,p,q}) \<subseteq> span (span (proj2_rep ` (?S - {u})))"
        by (simp only: span_mono)
      hence "span (proj2_rep ` {r,p,q}) \<subseteq> span (proj2_rep ` (?S - {u}))"
        by (simp only: span_span)
      moreover
      from \<open>\<not> proj2_set_Col {r,p,q}\<close>
        and \<open>card {r,p,q} = 3\<close>
        and not_proj2_set_Col_iff_span
      have "span (proj2_rep ` {r,p,q}) = UNIV" by simp
      ultimately have "span (proj2_rep ` (?S - {u})) = UNIV" by auto
      with \<open>card (?S - {u}) = 3\<close> and not_proj2_set_Col_iff_span
      show "\<not> proj2_set_Col (?S - {u})" by simp
    qed
  qed
  with \<open>card ?S = 4\<close>
  have "proj2_no_3_Col ?S" by (unfold proj2_no_3_Col_def) fast
  thus "\<exists> s. proj2_no_3_Col {s,r,p,q}" ..
qed

lemma proj2_set_Col_expand:
  assumes "proj2_set_Col S" and "{p,q,r} \<subseteq> S" and "p \<noteq> q" and "r \<noteq> p"
  shows "\<exists> k. r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)"
proof -
  from \<open>proj2_set_Col S\<close>
  obtain l where "\<forall> t\<in>S. proj2_incident t l" unfolding proj2_set_Col_def ..
  with \<open>{p,q,r} \<subseteq> S\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and proj2_incident_iff [of p q l r]
  show "\<exists> k. r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)" by simp
qed

subsection "Collineations of the real projective plane"

typedef cltn2 =
  "(Collect invertible :: (real^3^3) set)//invertible_proportionality"
proof
  from matrix_id_invertible have "(mat 1 :: real^3^3) \<in> Collect invertible"
    by simp
  thus "invertible_proportionality `` {mat 1} \<in>
    (Collect invertible :: (real^3^3) set)//invertible_proportionality"
    unfolding quotient_def
    by auto
qed

definition cltn2_rep :: "cltn2 \<Rightarrow> real^3^3" where
  "cltn2_rep A \<equiv> \<some> B. B \<in> Rep_cltn2 A"

definition cltn2_abs :: "real^3^3 \<Rightarrow> cltn2" where
  "cltn2_abs B \<equiv> Abs_cltn2 (invertible_proportionality `` {B})"

definition cltn2_independent :: "cltn2 set \<Rightarrow> bool" where
  "cltn2_independent X \<equiv> independent {cltn2_rep A | A. A \<in> X}"

definition apply_cltn2 :: "proj2 \<Rightarrow> cltn2 \<Rightarrow> proj2" where
  "apply_cltn2 x A \<equiv> proj2_abs (proj2_rep x v* cltn2_rep A)"

lemma cltn2_rep_in: "cltn2_rep B \<in> Rep_cltn2 B"
proof -
  let ?A = "cltn2_rep B"
  from quotient_element_nonempty and
    invertible_proportionality_equiv and
    Rep_cltn2 [of B]
  have "\<exists> C. C \<in> Rep_cltn2 B"
    by auto
  with someI_ex [of "\<lambda> C. C \<in> Rep_cltn2 B"]
  show "?A \<in> Rep_cltn2 B"
    unfolding cltn2_rep_def
    by simp
qed

lemma cltn2_rep_invertible: "invertible (cltn2_rep A)"
proof -
  from
    Union_quotient [of "Collect invertible" invertible_proportionality]
    and invertible_proportionality_equiv
    and Rep_cltn2 [of A] and cltn2_rep_in [of A]
  have "cltn2_rep A \<in> Collect invertible"
    unfolding quotient_def
    by auto
  thus "invertible (cltn2_rep A)"
    unfolding invertible_proportionality_def
    by simp
qed

lemma cltn2_rep_abs:
  fixes A :: "real^3^3"
  assumes "invertible A"
  shows "(A, cltn2_rep (cltn2_abs A)) \<in> invertible_proportionality"
proof -
  from \<open>invertible A\<close>
  have "invertible_proportionality `` {A} \<in> (Collect invertible :: (real^3^3) set)//invertible_proportionality"
    unfolding quotient_def
    by auto 
  with Abs_cltn2_inverse
  have "Rep_cltn2 (cltn2_abs A) = invertible_proportionality `` {A}"
    unfolding cltn2_abs_def
    by simp
  with cltn2_rep_in
  have "cltn2_rep (cltn2_abs A) \<in> invertible_proportionality `` {A}" by auto
  thus "(A, cltn2_rep (cltn2_abs A)) \<in> invertible_proportionality" by simp
qed

lemma cltn2_rep_abs2:
  assumes "invertible A"
  shows "\<exists> k. k \<noteq> 0 \<and> cltn2_rep (cltn2_abs A) = k *\<^sub>R A"
proof -
  from \<open>invertible A\<close> and cltn2_rep_abs
  have "(A, cltn2_rep (cltn2_abs A)) \<in> invertible_proportionality" by simp
  then obtain c where "A = c *\<^sub>R cltn2_rep (cltn2_abs A)"
    unfolding invertible_proportionality_def and real_vector.proportionality_def
    by auto
  with \<open>invertible A\<close> and zero_not_invertible have "c \<noteq> 0" by auto
  hence "1/c \<noteq> 0" by simp

  let ?k = "1/c"
  from \<open>A = c *\<^sub>R cltn2_rep (cltn2_abs A)\<close>
  have "?k *\<^sub>R A = ?k *\<^sub>R c *\<^sub>R cltn2_rep (cltn2_abs A)" by simp
  with \<open>c \<noteq> 0\<close> have "cltn2_rep (cltn2_abs A) = ?k *\<^sub>R A" by simp
  with \<open>?k \<noteq> 0\<close>
  show "\<exists> k. k \<noteq> 0 \<and> cltn2_rep (cltn2_abs A) = k *\<^sub>R A" by blast
qed

lemma cltn2_abs_rep: "cltn2_abs (cltn2_rep A) = A"
proof -
  from partition_Image_element
  [of "Collect invertible"
    invertible_proportionality
    "Rep_cltn2 A"
    "cltn2_rep A"]
    and invertible_proportionality_equiv
    and Rep_cltn2 [of A] and cltn2_rep_in [of A]
  have "invertible_proportionality `` {cltn2_rep A} = Rep_cltn2 A"
    by simp
  with Rep_cltn2_inverse
  show "cltn2_abs (cltn2_rep A) = A"
    unfolding cltn2_abs_def
    by simp
qed

lemma cltn2_abs_mult:
  assumes "k \<noteq> 0" and "invertible A"
  shows "cltn2_abs (k *\<^sub>R A) = cltn2_abs A"
proof -
  from \<open>k \<noteq> 0\<close> and \<open>invertible A\<close> and scalar_invertible
  have "invertible (k *\<^sub>R A)" by auto
  with \<open>invertible A\<close>
  have "(k *\<^sub>R A, A) \<in> invertible_proportionality"
    unfolding invertible_proportionality_def
      and real_vector.proportionality_def
    by (auto simp add: zero_not_invertible)
  with eq_equiv_class_iff
  [of "Collect invertible" invertible_proportionality "k *\<^sub>R A" A]
    and invertible_proportionality_equiv
    and \<open>invertible A\<close> and \<open>invertible (k *\<^sub>R A)\<close>
  have "invertible_proportionality `` {k *\<^sub>R A}
    = invertible_proportionality `` {A}"
    by simp
  thus "cltn2_abs (k *\<^sub>R A) = cltn2_abs A"
    unfolding cltn2_abs_def
    by simp
qed

lemma cltn2_abs_mult_rep:
  assumes "k \<noteq> 0"
  shows "cltn2_abs (k *\<^sub>R cltn2_rep A) = A"
  using cltn2_rep_invertible and cltn2_abs_mult and cltn2_abs_rep and assms
  by simp

lemma apply_cltn2_abs:
  assumes "x \<noteq> 0" and "invertible A"
  shows "apply_cltn2 (proj2_abs x) (cltn2_abs A) = proj2_abs (x v* A)"
proof -
  from proj2_rep_abs2 and \<open>x \<noteq> 0\<close>
  obtain k where "k \<noteq> 0" and "proj2_rep (proj2_abs x) = k *\<^sub>R x" by auto

  from cltn2_rep_abs2 and \<open>invertible A\<close>
  obtain c where "c \<noteq> 0" and "cltn2_rep (cltn2_abs A) = c *\<^sub>R A" by auto

  from \<open>k \<noteq> 0\<close> and \<open>c \<noteq> 0\<close> have "k * c \<noteq> 0" by simp

  from \<open>proj2_rep (proj2_abs x) = k *\<^sub>R x\<close> and \<open>cltn2_rep (cltn2_abs A) = c *\<^sub>R A\<close>
  have "proj2_rep (proj2_abs x) v* cltn2_rep (cltn2_abs A) = (k*c) *\<^sub>R (x v* A)"
    by (simp add: scaleR_vector_matrix_assoc vector_scaleR_matrix_ac)
  with \<open>k * c \<noteq> 0\<close> 
  show "apply_cltn2 (proj2_abs x) (cltn2_abs A) = proj2_abs (x v* A)"
    unfolding apply_cltn2_def
    by (simp add: proj2_abs_mult)
qed

lemma apply_cltn2_left_abs:
  assumes "v \<noteq> 0"
  shows "apply_cltn2 (proj2_abs v) C = proj2_abs (v v* cltn2_rep C)"
proof -
  have "cltn2_abs (cltn2_rep C) = C" by (rule cltn2_abs_rep)
  with \<open>v \<noteq> 0\<close> and cltn2_rep_invertible and apply_cltn2_abs [of v "cltn2_rep C"]
  show "apply_cltn2 (proj2_abs v) C = proj2_abs (v v* cltn2_rep C)"
    by simp
qed

lemma apply_cltn2_right_abs:
  assumes "invertible M"
  shows "apply_cltn2 p (cltn2_abs M) = proj2_abs (proj2_rep p v* M)"
proof -
  from proj2_rep_non_zero and \<open>invertible M\<close> and apply_cltn2_abs
  have "apply_cltn2 (proj2_abs (proj2_rep p)) (cltn2_abs M)
    = proj2_abs (proj2_rep p v* M)"
    by simp
  thus "apply_cltn2 p (cltn2_abs M) = proj2_abs (proj2_rep p v* M)"
    by (simp add: proj2_abs_rep)
qed

lemma non_zero_mult_rep_non_zero:
  assumes "v \<noteq> 0"
  shows "v v* cltn2_rep C \<noteq> 0"
  using \<open>v \<noteq> 0\<close> and cltn2_rep_invertible and times_invertible_eq_zero
  by auto

lemma rep_mult_rep_non_zero: "proj2_rep p v* cltn2_rep A \<noteq> 0"
  using proj2_rep_non_zero
  by (rule non_zero_mult_rep_non_zero)

definition cltn2_image :: "proj2 set \<Rightarrow> cltn2 \<Rightarrow> proj2 set" where
  "cltn2_image P A \<equiv> {apply_cltn2 p A | p. p \<in> P}"

subsubsection "As a group"

definition cltn2_id :: cltn2 where
  "cltn2_id \<equiv> cltn2_abs (mat 1)"

definition cltn2_compose :: "cltn2 \<Rightarrow> cltn2 \<Rightarrow> cltn2" where
  "cltn2_compose A B \<equiv> cltn2_abs (cltn2_rep A ** cltn2_rep B)"

definition cltn2_inverse :: "cltn2 \<Rightarrow> cltn2" where
  "cltn2_inverse A \<equiv> cltn2_abs (matrix_inv (cltn2_rep A))"

lemma cltn2_compose_abs:
  assumes "invertible M" and "invertible N"
  shows "cltn2_compose (cltn2_abs M) (cltn2_abs N) = cltn2_abs (M ** N)"
proof -
  from \<open>invertible M\<close> and \<open>invertible N\<close> and invertible_mult
  have "invertible (M ** N)" by auto

  from \<open>invertible M\<close> and \<open>invertible N\<close> and cltn2_rep_abs2
  obtain j and k where "j \<noteq> 0" and "k \<noteq> 0"
    and "cltn2_rep (cltn2_abs M) = j *\<^sub>R M"
    and "cltn2_rep (cltn2_abs N) = k *\<^sub>R N"
    by blast

  from \<open>j \<noteq> 0\<close> and \<open>k \<noteq> 0\<close> have "j * k \<noteq> 0" by simp

  from \<open>cltn2_rep (cltn2_abs M) = j *\<^sub>R M\<close> and \<open>cltn2_rep (cltn2_abs N) = k *\<^sub>R N\<close>
  have "cltn2_rep (cltn2_abs M) ** cltn2_rep (cltn2_abs N)
    = (j * k) *\<^sub>R (M ** N)"
    by (simp add: matrix_scalar_ac scalar_matrix_assoc [symmetric])
  with \<open>j * k \<noteq> 0\<close> and \<open>invertible (M ** N)\<close>
  show "cltn2_compose (cltn2_abs M) (cltn2_abs N) = cltn2_abs (M ** N)"
    unfolding cltn2_compose_def
    by (simp add: cltn2_abs_mult)
qed

lemma cltn2_compose_left_abs:
  assumes "invertible M"
  shows "cltn2_compose (cltn2_abs M) A = cltn2_abs (M ** cltn2_rep A)"
proof -
  from \<open>invertible M\<close> and cltn2_rep_invertible and cltn2_compose_abs
  have "cltn2_compose (cltn2_abs M) (cltn2_abs (cltn2_rep A))
    = cltn2_abs (M ** cltn2_rep A)"
    by simp
  thus "cltn2_compose (cltn2_abs M) A = cltn2_abs (M ** cltn2_rep A)"
    by (simp add: cltn2_abs_rep)
qed

lemma cltn2_compose_right_abs:
  assumes "invertible M"
  shows "cltn2_compose A (cltn2_abs M) = cltn2_abs (cltn2_rep A ** M)"
proof -
  from \<open>invertible M\<close> and cltn2_rep_invertible and cltn2_compose_abs
  have "cltn2_compose (cltn2_abs (cltn2_rep A)) (cltn2_abs M)
    = cltn2_abs (cltn2_rep A ** M)"
    by simp
  thus "cltn2_compose A (cltn2_abs M) = cltn2_abs (cltn2_rep A ** M)"
    by (simp add: cltn2_abs_rep)
qed

lemma cltn2_abs_rep_abs_mult:
  assumes "invertible M" and "invertible N"
  shows "cltn2_abs (cltn2_rep (cltn2_abs M) ** N) = cltn2_abs (M ** N)"
proof -
  from \<open>invertible M\<close> and \<open>invertible N\<close>
  have "invertible (M ** N)" by (simp add: invertible_mult)

  from \<open>invertible M\<close> and cltn2_rep_abs2
  obtain k where "k \<noteq> 0" and "cltn2_rep (cltn2_abs M) = k *\<^sub>R M" by auto
  from \<open>cltn2_rep (cltn2_abs M) = k *\<^sub>R M\<close>
  have "cltn2_rep (cltn2_abs M) ** N = k *\<^sub>R M ** N" by simp
  with \<open>k \<noteq> 0\<close> and \<open>invertible (M ** N)\<close> and cltn2_abs_mult
  show "cltn2_abs (cltn2_rep (cltn2_abs M) ** N) = cltn2_abs (M ** N)"
    by (simp add: scalar_matrix_assoc [symmetric])
qed

lemma cltn2_assoc:
  "cltn2_compose (cltn2_compose A B) C = cltn2_compose A (cltn2_compose B C)"
proof -
  let ?A' = "cltn2_rep A"
  let ?B' = "cltn2_rep B"
  let ?C' = "cltn2_rep C"
  from cltn2_rep_invertible
  have "invertible ?A'" and "invertible ?B'" and "invertible ?C'" by simp_all
  with invertible_mult
  have "invertible (?A' ** ?B')" and "invertible (?B' ** ?C')"
    and "invertible (?A' ** ?B' ** ?C')"
    by auto
  from \<open>invertible (?A' ** ?B')\<close> and \<open>invertible ?C'\<close> and cltn2_abs_rep_abs_mult
  have "cltn2_abs (cltn2_rep (cltn2_abs (?A' ** ?B')) ** ?C')
    = cltn2_abs (?A' ** ?B' ** ?C')"
    by simp

  from \<open>invertible (?B' ** ?C')\<close> and cltn2_rep_abs2 [of "?B' ** ?C'"]
  obtain k where "k \<noteq> 0"
    and "cltn2_rep (cltn2_abs (?B' ** ?C')) = k *\<^sub>R (?B' ** ?C')"
    by auto
  from \<open>cltn2_rep (cltn2_abs (?B' ** ?C')) = k *\<^sub>R (?B' ** ?C')\<close>
  have "?A' ** cltn2_rep (cltn2_abs (?B' ** ?C')) = k *\<^sub>R (?A' ** ?B' ** ?C')"
    by (simp add: matrix_scalar_ac matrix_mul_assoc scalar_matrix_assoc)
  with \<open>k \<noteq> 0\<close> and \<open>invertible (?A' ** ?B' ** ?C')\<close>
    and cltn2_abs_mult [of k "?A' ** ?B' ** ?C'"]
  have "cltn2_abs (?A' ** cltn2_rep (cltn2_abs (?B' ** ?C')))
    = cltn2_abs (?A' ** ?B' ** ?C')"
    by simp
  with \<open>cltn2_abs (cltn2_rep (cltn2_abs (?A' ** ?B')) ** ?C')
    = cltn2_abs (?A' ** ?B' ** ?C')\<close>
  show
    "cltn2_compose (cltn2_compose A B) C = cltn2_compose A (cltn2_compose B C)"
    unfolding cltn2_compose_def
    by simp
qed

lemma cltn2_left_id: "cltn2_compose cltn2_id A = A"
proof -
  let ?A' = "cltn2_rep A"
  from cltn2_rep_invertible have "invertible ?A'" by simp
  with matrix_id_invertible and cltn2_abs_rep_abs_mult [of "mat 1" ?A']
  have "cltn2_compose cltn2_id A = cltn2_abs (cltn2_rep A)"
    unfolding cltn2_compose_def and cltn2_id_def
    by (auto simp add: matrix_mul_lid)
  with cltn2_abs_rep show "cltn2_compose cltn2_id A = A" by simp
qed

lemma cltn2_left_inverse: "cltn2_compose (cltn2_inverse A) A = cltn2_id"
proof -
  let ?M = "cltn2_rep A"
  let ?M' = "matrix_inv ?M"
  from cltn2_rep_invertible have "invertible ?M" by simp
  with matrix_inv_invertible have "invertible ?M'" by auto
  with \<open>invertible ?M\<close> and cltn2_abs_rep_abs_mult
  have "cltn2_compose (cltn2_inverse A) A = cltn2_abs (?M' ** ?M)"
    unfolding cltn2_compose_def and cltn2_inverse_def
    by simp
  with \<open>invertible ?M\<close>
  show "cltn2_compose (cltn2_inverse A) A = cltn2_id"
    unfolding cltn2_id_def
    by (simp add: matrix_inv)
qed

lemma cltn2_left_inverse_ex:
  "\<exists> B. cltn2_compose B A = cltn2_id"
  using cltn2_left_inverse ..

interpretation cltn2:
  group "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"
  using cltn2_assoc and cltn2_left_id and cltn2_left_inverse_ex
    and groupI [of "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"]
  by simp_all

lemma cltn2_inverse_inv [simp]:
  "inv\<^bsub>(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)\<^esub> A
  = cltn2_inverse A"
  using cltn2_left_inverse [of A] and cltn2.inv_equality
  by simp

lemmas cltn2_inverse_id [simp] = cltn2.inv_one [simplified]
  and cltn2_inverse_compose = cltn2.inv_mult_group [simplified]

subsubsection "As a group action"

lemma apply_cltn2_id [simp]: "apply_cltn2 p cltn2_id = p"
proof -
  from matrix_id_invertible and apply_cltn2_right_abs
  have "apply_cltn2 p cltn2_id = proj2_abs (proj2_rep p v* mat 1)"
    unfolding cltn2_id_def by blast
  thus "apply_cltn2 p cltn2_id = p"
    by (simp add: proj2_abs_rep)
qed

lemma apply_cltn2_compose:
  "apply_cltn2 (apply_cltn2 p A) B = apply_cltn2 p (cltn2_compose A B)"
proof -
  from rep_mult_rep_non_zero and cltn2_rep_invertible and apply_cltn2_abs
  have "apply_cltn2 (apply_cltn2 p A) (cltn2_abs (cltn2_rep B))
    = proj2_abs ((proj2_rep p v* cltn2_rep A) v* cltn2_rep B)"
    unfolding apply_cltn2_def [of p A]
    by simp
  hence "apply_cltn2 (apply_cltn2 p A) B
    = proj2_abs (proj2_rep p v* (cltn2_rep A ** cltn2_rep B))"
    by (simp add: cltn2_abs_rep vector_matrix_mul_assoc)

  from cltn2_rep_invertible and invertible_mult
  have "invertible (cltn2_rep A ** cltn2_rep B)" by auto
  with apply_cltn2_right_abs
  have "apply_cltn2 p (cltn2_compose A B)
    = proj2_abs (proj2_rep p v* (cltn2_rep A ** cltn2_rep B))"
    unfolding cltn2_compose_def
    by simp
  with \<open>apply_cltn2 (apply_cltn2 p A) B
    = proj2_abs (proj2_rep p v* (cltn2_rep A ** cltn2_rep B))\<close>
  show "apply_cltn2 (apply_cltn2 p A) B = apply_cltn2 p (cltn2_compose A B)"
    by simp
qed

interpretation cltn2:
  action "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)" apply_cltn2
proof
  let ?G = "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"
  fix p
  show "apply_cltn2 p \<one>\<^bsub>?G\<^esub> = p" by simp
  fix A B
  have "apply_cltn2 (apply_cltn2 p A) B = apply_cltn2 p (A \<otimes>\<^bsub>?G\<^esub> B)"
    by simp (rule apply_cltn2_compose)
  thus "A \<in> carrier ?G \<and> B \<in> carrier ?G
    \<longrightarrow> apply_cltn2 (apply_cltn2 p A) B = apply_cltn2 p (A \<otimes>\<^bsub>?G\<^esub> B)"
    ..
qed

definition cltn2_transpose :: "cltn2 \<Rightarrow> cltn2" where
  "cltn2_transpose A \<equiv> cltn2_abs (transpose (cltn2_rep A))"

definition apply_cltn2_line :: "proj2_line \<Rightarrow> cltn2 \<Rightarrow> proj2_line" where
  "apply_cltn2_line l A
  \<equiv> P2L (apply_cltn2 (L2P l) (cltn2_transpose (cltn2_inverse A)))"

lemma cltn2_transpose_abs:
  assumes "invertible M"
  shows "cltn2_transpose (cltn2_abs M) = cltn2_abs (transpose M)"
proof -
  from \<open>invertible M\<close> and transpose_invertible have "invertible (transpose M)" by auto

  from \<open>invertible M\<close> and cltn2_rep_abs2
  obtain k where "k \<noteq> 0" and "cltn2_rep (cltn2_abs M) = k *\<^sub>R M" by auto

  from \<open>cltn2_rep (cltn2_abs M) = k *\<^sub>R M\<close>
  have "transpose (cltn2_rep (cltn2_abs M)) = k *\<^sub>R transpose M"
    by (simp add: transpose_scalar)
  with \<open>k \<noteq> 0\<close> and \<open>invertible (transpose M)\<close>
  show "cltn2_transpose (cltn2_abs M) = cltn2_abs (transpose M)"
    unfolding cltn2_transpose_def
    by (simp add: cltn2_abs_mult)
qed

lemma cltn2_transpose_compose:
  "cltn2_transpose (cltn2_compose A B)
  = cltn2_compose (cltn2_transpose B) (cltn2_transpose A)"
proof -
  from cltn2_rep_invertible
  have "invertible (cltn2_rep A)" and "invertible (cltn2_rep B)"
    by simp_all
  with transpose_invertible
  have "invertible (transpose (cltn2_rep A))"
    and "invertible (transpose (cltn2_rep B))"
    by auto

  from \<open>invertible (cltn2_rep A)\<close> and \<open>invertible (cltn2_rep B)\<close>
    and invertible_mult
  have "invertible (cltn2_rep A ** cltn2_rep B)" by auto
  with \<open>invertible (cltn2_rep A ** cltn2_rep B)\<close> and cltn2_transpose_abs
  have "cltn2_transpose (cltn2_compose A B)
    = cltn2_abs (transpose (cltn2_rep A ** cltn2_rep B))"
    unfolding cltn2_compose_def
    by simp
  also have "\<dots> = cltn2_abs (transpose (cltn2_rep B) ** transpose (cltn2_rep A))"
    by (simp add: matrix_transpose_mul)
  also from \<open>invertible (transpose (cltn2_rep B))\<close>
    and \<open>invertible (transpose (cltn2_rep A))\<close>
    and cltn2_compose_abs
  have "\<dots> = cltn2_compose (cltn2_transpose B) (cltn2_transpose A)"
    unfolding cltn2_transpose_def
    by simp
  finally show "cltn2_transpose (cltn2_compose A B)
    = cltn2_compose (cltn2_transpose B) (cltn2_transpose A)" .
qed

lemma cltn2_transpose_transpose: "cltn2_transpose (cltn2_transpose A) = A"
proof -
  from cltn2_rep_invertible have "invertible (cltn2_rep A)" by simp
  with transpose_invertible have "invertible (transpose (cltn2_rep A))" by auto
  with cltn2_transpose_abs [of "transpose (cltn2_rep A)"]
  have
    "cltn2_transpose (cltn2_transpose A) = cltn2_abs (transpose (transpose (cltn2_rep A)))"
    unfolding cltn2_transpose_def [of A]
    by simp
  with cltn2_abs_rep and transpose_transpose [of "cltn2_rep A"]
  show "cltn2_transpose (cltn2_transpose A) = A" by simp
qed

lemma cltn2_transpose_id [simp]: "cltn2_transpose cltn2_id = cltn2_id"
  using cltn2_transpose_abs
  unfolding cltn2_id_def
  by (simp add: transpose_mat matrix_id_invertible)

lemma apply_cltn2_line_id [simp]: "apply_cltn2_line l cltn2_id = l"
  unfolding apply_cltn2_line_def
  by simp

lemma apply_cltn2_line_compose:
  "apply_cltn2_line (apply_cltn2_line l A) B
  = apply_cltn2_line l (cltn2_compose A B)"
proof -
  have "cltn2_compose
    (cltn2_transpose (cltn2_inverse A)) (cltn2_transpose (cltn2_inverse B))
    = cltn2_transpose (cltn2_inverse (cltn2_compose A B))"
    by (simp add: cltn2_transpose_compose cltn2_inverse_compose)
  thus "apply_cltn2_line (apply_cltn2_line l A) B
    = apply_cltn2_line l (cltn2_compose A B)"
    unfolding apply_cltn2_line_def
    by (simp add: apply_cltn2_compose)
qed

interpretation cltn2_line:
  action
  "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"
  apply_cltn2_line
proof
  let ?G = "(|carrier = UNIV, mult = cltn2_compose, one = cltn2_id|)"
  fix l
  show "apply_cltn2_line l \<one>\<^bsub>?G\<^esub> = l" by simp
  fix A B
  have "apply_cltn2_line (apply_cltn2_line l A) B
    = apply_cltn2_line l (A \<otimes>\<^bsub>?G\<^esub> B)"
    by simp (rule apply_cltn2_line_compose)
  thus "A \<in> carrier ?G \<and> B \<in> carrier ?G
    \<longrightarrow> apply_cltn2_line (apply_cltn2_line l A) B
    = apply_cltn2_line l (A \<otimes>\<^bsub>?G\<^esub> B)"
    ..
qed

lemmas apply_cltn2_inv [simp] = cltn2.act_act_inv [simplified]
lemmas apply_cltn2_line_inv [simp] = cltn2_line.act_act_inv [simplified]

lemma apply_cltn2_line_alt_def:
  "apply_cltn2_line l A
  = proj2_line_abs (cltn2_rep (cltn2_inverse A) *v proj2_line_rep l)"
proof -
  have "invertible (cltn2_rep (cltn2_inverse A))" by (rule cltn2_rep_invertible)
  hence "invertible (transpose (cltn2_rep (cltn2_inverse A)))"
    by (rule transpose_invertible)
  hence
    "apply_cltn2 (L2P l) (cltn2_transpose (cltn2_inverse A))
    = proj2_abs (proj2_rep (L2P l) v* transpose (cltn2_rep (cltn2_inverse A)))"
    unfolding cltn2_transpose_def
    by (rule apply_cltn2_right_abs)
  hence "apply_cltn2 (L2P l) (cltn2_transpose (cltn2_inverse A))
    = proj2_abs (cltn2_rep (cltn2_inverse A) *v proj2_line_rep l)"
    unfolding proj2_line_rep_def
    by simp
  thus "apply_cltn2_line l A
    = proj2_line_abs (cltn2_rep (cltn2_inverse A) *v proj2_line_rep l)"
    unfolding apply_cltn2_line_def and proj2_line_abs_def ..
qed

lemma rep_mult_line_rep_non_zero: "cltn2_rep A *v proj2_line_rep l \<noteq> 0"
  using proj2_line_rep_non_zero and cltn2_rep_invertible
    and invertible_times_eq_zero
  by auto

lemma apply_cltn2_incident:
  "proj2_incident p (apply_cltn2_line l A)
  \<longleftrightarrow> proj2_incident (apply_cltn2 p (cltn2_inverse A)) l"
proof -
  have "proj2_rep p v* cltn2_rep (cltn2_inverse A) \<noteq> 0"
    by (rule rep_mult_rep_non_zero)
  with proj2_rep_abs2
  obtain j where "j \<noteq> 0"
    and "proj2_rep (proj2_abs (proj2_rep p v* cltn2_rep (cltn2_inverse A)))
    = j *\<^sub>R (proj2_rep p v* cltn2_rep (cltn2_inverse A))"
    by auto

  let ?v = "cltn2_rep (cltn2_inverse A) *v proj2_line_rep l"
  have "?v \<noteq> 0" by (rule rep_mult_line_rep_non_zero)
  with proj2_line_rep_abs [of ?v]
  obtain k where "k \<noteq> 0"
    and "proj2_line_rep (proj2_line_abs ?v) = k *\<^sub>R ?v"
    by auto
  hence "proj2_incident p (apply_cltn2_line l A)
    \<longleftrightarrow> proj2_rep p \<bullet> (cltn2_rep (cltn2_inverse A) *v proj2_line_rep l) = 0"
    unfolding proj2_incident_def and apply_cltn2_line_alt_def
    by (simp add: dot_scaleR_mult)
  also from dot_lmul_matrix [of "proj2_rep p" "cltn2_rep (cltn2_inverse A)"]
  have
    "\<dots> \<longleftrightarrow> (proj2_rep p v* cltn2_rep (cltn2_inverse A)) \<bullet> proj2_line_rep l = 0"
    by simp
  also from \<open>j \<noteq> 0\<close>
    and \<open>proj2_rep (proj2_abs (proj2_rep p v* cltn2_rep (cltn2_inverse A)))
    = j *\<^sub>R (proj2_rep p v* cltn2_rep (cltn2_inverse A))\<close>
  have "\<dots> \<longleftrightarrow> proj2_incident (apply_cltn2 p (cltn2_inverse A)) l"
    unfolding proj2_incident_def and apply_cltn2_def
    by (simp add: dot_scaleR_mult)
  finally show ?thesis .
qed

lemma apply_cltn2_preserve_incident [iff]:
  "proj2_incident (apply_cltn2 p A) (apply_cltn2_line l A)
  \<longleftrightarrow> proj2_incident p l"
  by (simp add: apply_cltn2_incident)

lemma apply_cltn2_preserve_set_Col:
  assumes "proj2_set_Col S"
  shows "proj2_set_Col {apply_cltn2 p C | p. p \<in> S}"
proof -
  from \<open>proj2_set_Col S\<close>
  obtain l where "\<forall> p\<in>S. proj2_incident p l" unfolding proj2_set_Col_def ..
  hence "\<forall> q \<in> {apply_cltn2 p C | p. p \<in> S}.
    proj2_incident q (apply_cltn2_line l C)"
    by auto
  thus "proj2_set_Col {apply_cltn2 p C | p. p \<in> S}"
    unfolding proj2_set_Col_def ..
qed

lemma apply_cltn2_injective:
  assumes "apply_cltn2 p C = apply_cltn2 q C"
  shows "p = q"
proof -
  from \<open>apply_cltn2 p C = apply_cltn2 q C\<close>
  have "apply_cltn2 (apply_cltn2 p C) (cltn2_inverse C)
    = apply_cltn2 (apply_cltn2 q C) (cltn2_inverse C)"
    by simp
  thus "p = q" by simp
qed

lemma apply_cltn2_line_injective:
  assumes "apply_cltn2_line l C = apply_cltn2_line m C"
  shows "l = m"
proof -
  from \<open>apply_cltn2_line l C = apply_cltn2_line m C\<close>
  have "apply_cltn2_line (apply_cltn2_line l C) (cltn2_inverse C)
    = apply_cltn2_line (apply_cltn2_line m C) (cltn2_inverse C)"
    by simp
  thus "l = m" by simp
qed

lemma apply_cltn2_line_unique:
  assumes "p \<noteq> q" and "proj2_incident p l" and "proj2_incident q l"
  and "proj2_incident (apply_cltn2 p C) m"
  and "proj2_incident (apply_cltn2 q C) m"
  shows "apply_cltn2_line l C = m"
proof -
  from \<open>proj2_incident p l\<close>
  have "proj2_incident (apply_cltn2 p C) (apply_cltn2_line l C)" by simp

  from \<open>proj2_incident q l\<close>
  have "proj2_incident (apply_cltn2 q C) (apply_cltn2_line l C)" by simp

  from \<open>p \<noteq> q\<close> and apply_cltn2_injective [of p C q]
  have "apply_cltn2 p C \<noteq> apply_cltn2 q C" by auto
  with \<open>proj2_incident (apply_cltn2 p C) (apply_cltn2_line l C)\<close>
    and \<open>proj2_incident (apply_cltn2 q C) (apply_cltn2_line l C)\<close>
    and \<open>proj2_incident (apply_cltn2 p C) m\<close>
    and \<open>proj2_incident (apply_cltn2 q C) m\<close>
    and proj2_incident_unique
  show "apply_cltn2_line l C = m" by fast
qed

lemma apply_cltn2_unique:
  assumes "l \<noteq> m" and "proj2_incident p l" and "proj2_incident p m"
  and "proj2_incident q (apply_cltn2_line l C)"
  and "proj2_incident q (apply_cltn2_line m C)"
  shows "apply_cltn2 p C = q"
proof -
  from \<open>proj2_incident p l\<close>
  have "proj2_incident (apply_cltn2 p C) (apply_cltn2_line l C)" by simp

  from \<open>proj2_incident p m\<close>
  have "proj2_incident (apply_cltn2 p C) (apply_cltn2_line m C)" by simp

  from \<open>l \<noteq> m\<close> and apply_cltn2_line_injective [of l C m]
  have "apply_cltn2_line l C \<noteq> apply_cltn2_line m C" by auto
  with \<open>proj2_incident (apply_cltn2 p C) (apply_cltn2_line l C)\<close>
    and \<open>proj2_incident (apply_cltn2 p C) (apply_cltn2_line m C)\<close>
    and \<open>proj2_incident q (apply_cltn2_line l C)\<close>
    and \<open>proj2_incident q (apply_cltn2_line m C)\<close>
    and proj2_incident_unique
  show "apply_cltn2 p C = q" by fast
qed

subsubsection \<open>Parts of some Statements from \cite{borsuk}\<close>
text \<open>All theorems with names beginning with \emph{statement} are based
  on corresponding theorems in \cite{borsuk}.\<close>

lemma statement52_existence:
  fixes a :: "proj2^3" and a3 :: "proj2"
  assumes "proj2_no_3_Col (insert a3 (range (($) a)))"
  shows "\<exists> A. apply_cltn2 (proj2_abs (vector [1,1,1])) A = a3 \<and>
  (\<forall> j. apply_cltn2 (proj2_abs (axis j 1)) A = a$j)"
proof -
  let ?v = "proj2_rep a3"
  let ?B = "proj2_rep ` range (($) a)"

  from \<open>proj2_no_3_Col (insert a3 (range (($) a)))\<close>
  have "card (insert a3 (range (($) a))) = 4" unfolding proj2_no_3_Col_def ..

  from card_image_le [of UNIV "($) a"]
  have "card (range (($) a)) \<le> 3" by simp
  with card_insert_if [of "range (($) a)" a3]
    and \<open>card (insert a3 (range (($) a))) = 4\<close>
  have "a3 \<notin> range (($) a)" by auto
  hence "(insert a3 (range (($) a))) - {a3} = range (($) a)" by simp
  with \<open>proj2_no_3_Col (insert a3 (range (($) a)))\<close>
    and proj2_no_3_Col_span [of "insert a3 (range (($) a))" a3]
  have "span ?B = UNIV" by simp

  from card_suc_ge_insert [of a3 "range (($) a)"]
    and \<open>card (insert a3 (range (($) a))) = 4\<close>
    and \<open>card (range (($) a)) \<le> 3\<close>
  have "card (range (($) a)) = 3" by simp
  with card_image [of proj2_rep "range (($) a)"]
    and proj2_rep_inj
    and subset_inj_on
  have "card ?B = 3" by auto
  hence "finite ?B" by simp
  with \<open>span ?B = UNIV\<close> and span_finite [of ?B]
  obtain c where "(\<Sum> w \<in> ?B. (c w) *\<^sub>R w) = ?v"
    by (auto simp add: scalar_equiv) (metis (no_types, lifting) UNIV_I rangeE)
  let ?C = "\<chi> i. c (proj2_rep (a$i)) *\<^sub>R (proj2_rep (a$i))"
  let ?A = "cltn2_abs ?C"

  from proj2_rep_inj and \<open>a3 \<notin> range (($) a)\<close> have "?v \<notin> ?B"
    unfolding inj_on_def
    by auto

  have "\<forall> i. c (proj2_rep (a$i)) \<noteq> 0"
  proof
    fix i
    let ?Bi = "proj2_rep ` (range (($) a) - {a$i})"

    have "a$i \<in> insert a3 (range (($) a))" by simp

    have "proj2_rep (a$i) \<in> ?B" by auto

    from image_set_diff [of proj2_rep] and proj2_rep_inj
    have "?Bi = ?B - {proj2_rep (a$i)}" by simp
    with sum_diff1 [of ?B "\<lambda> w. (c w) *\<^sub>R w"]
      and \<open>finite ?B\<close>
      and \<open>proj2_rep (a$i) \<in> ?B\<close>
    have "(\<Sum> w \<in> ?Bi. (c w) *\<^sub>R w) =
      (\<Sum> w \<in> ?B. (c w) *\<^sub>R w) - c (proj2_rep (a$i)) *\<^sub>R proj2_rep (a$i)"
      by simp

    from \<open>a3 \<notin> range (($) a)\<close> have "a3 \<noteq> a$i" by auto
    hence "insert a3 (range (($) a)) - {a$i} =
      insert a3 (range (($) a) - {a$i})" by auto
    hence "proj2_rep ` (insert a3 (range (($) a)) - {a$i}) = insert ?v ?Bi"
      by simp
    moreover from \<open>proj2_no_3_Col (insert a3 (range (($) a)))\<close>
      and \<open>a$i \<in> insert a3 (range (($) a))\<close>
    have "span (proj2_rep ` (insert a3 (range (($) a)) - {a$i})) = UNIV"
      by (rule proj2_no_3_Col_span)
    ultimately have "span (insert ?v ?Bi) = UNIV" by simp

    from \<open>?Bi = ?B - {proj2_rep (a$i)}\<close>
      and \<open>proj2_rep (a$i) \<in> ?B\<close>
      and \<open>card ?B = 3\<close>
    have "card ?Bi = 2" by (simp add: card_gt_0_diff_singleton)
    hence "finite ?Bi" by simp
    with \<open>card ?Bi = 2\<close> and dim_le_card' [of ?Bi] have "dim ?Bi \<le> 2" by simp
    hence "dim (span ?Bi) \<le> 2" by (subst dim_span)
    then have "span ?Bi \<noteq> UNIV"
      by clarify (auto simp: dim_UNIV)
    with \<open>span (insert ?v ?Bi) = UNIV\<close> and span_redundant
    have "?v \<notin> span ?Bi" by auto

    { assume "c (proj2_rep (a$i)) = 0"
      with \<open>(\<Sum> w \<in> ?Bi. (c w) *\<^sub>R w) =
        (\<Sum> w \<in> ?B. (c w) *\<^sub>R w) - c (proj2_rep (a$i)) *\<^sub>R proj2_rep (a$i)\<close>
        and \<open>(\<Sum> w \<in> ?B. (c w) *\<^sub>R w) = ?v\<close>
      have "?v = (\<Sum> w \<in> ?Bi. (c w) *\<^sub>R w)"
        by simp
      with span_finite [of ?Bi] and \<open>finite ?Bi\<close>
      have "?v \<in> span ?Bi" by (simp add: scalar_equiv)
      with \<open>?v \<notin> span ?Bi\<close> have False .. }
    thus "c (proj2_rep (a$i)) \<noteq> 0" ..
  qed
  hence "\<forall> w\<in>?B. c w \<noteq> 0"
    unfolding image_def
    by auto

  have "rows ?C = (\<lambda> w. (c w) *\<^sub>R w) ` ?B"
    unfolding rows_def
      and row_def
      and image_def
    by (auto simp: vec_lambda_eta)

  have "\<forall> x. x \<in> span (rows ?C)"
  proof
    fix x :: "real^3"
    from \<open>finite ?B\<close> and span_finite [of ?B] and \<open>span ?B = UNIV\<close>
    obtain ub where "(\<Sum> w\<in>?B. (ub w) *\<^sub>R w) = x"
      by (auto simp add: scalar_equiv) (metis (no_types, lifting) UNIV_I rangeE)
    have "\<forall> w\<in>?B. (ub w) *\<^sub>R w \<in> span (rows ?C)"
    proof
      fix w
      assume "w \<in> ?B"
      with span_superset [of "rows ?C"] and \<open>rows ?C = image (\<lambda> w. (c w) *\<^sub>R w) ?B\<close>
      have "(c w) *\<^sub>R w \<in> span (rows ?C)" by auto
      with span_mul [of "(c w) *\<^sub>R w" "rows ?C" "(ub w)/(c w)"]
      have "((ub w)/(c w)) *\<^sub>R ((c w) *\<^sub>R w) \<in> span (rows ?C)"
        by (simp add: scalar_equiv)
      with \<open>\<forall> w\<in>?B. c w \<noteq> 0\<close> and \<open>w \<in> ?B\<close>
      show "(ub w) *\<^sub>R w \<in> span (rows ?C)" by auto
    qed
    with span_sum [of ?B "\<lambda> w. (ub w) *\<^sub>R w"] and \<open>finite ?B\<close>
    have "(\<Sum> w\<in>?B. (ub w) *\<^sub>R w) \<in> span (rows ?C)" by blast
    with \<open>(\<Sum> w\<in>?B. (ub w) *\<^sub>R w) = x\<close> show "x \<in> span (rows ?C)" by simp
  qed
  hence "span (rows ?C) = UNIV" by auto
  with matrix_left_invertible_span_rows [of ?C]
  have "\<exists> C'. C' ** ?C = mat 1" ..
  with left_invertible_iff_invertible
  have "invertible ?C" ..

  have "(vector [1,1,1] :: real^3) \<noteq> 0"
    unfolding vector_def
    by (simp add: vec_eq_iff forall_3)
  with apply_cltn2_abs and \<open>invertible ?C\<close>
  have "apply_cltn2 (proj2_abs (vector [1,1,1])) ?A =
    proj2_abs (vector [1,1,1] v* ?C)"
    by simp
  from inj_on_iff_eq_card [of UNIV "($) a"] and \<open>card (range (($) a)) = 3\<close>
  have "inj (($) a)" by simp
  from exhaust_3 have "\<forall> i::3. (vector [1::real,1,1])$i = 1"
    unfolding vector_def
    by auto
  with vector_matrix_row [of "vector [1,1,1]" ?C]
  have "(vector [1,1,1]) v* ?C =
    (\<Sum> i\<in>UNIV. (c (proj2_rep (a$i))) *\<^sub>R (proj2_rep (a$i)))"
    by simp
  also from sum.reindex
  [of "($) a" UNIV "\<lambda> x. (c (proj2_rep x)) *\<^sub>R (proj2_rep x)"]
    and \<open>inj (($) a)\<close>
  have "\<dots> = (\<Sum> x\<in>(range (($) a)). (c (proj2_rep x)) *\<^sub>R (proj2_rep x))"
    by simp
  also from sum.reindex
  [of proj2_rep "range (($) a)" "\<lambda> w. (c w) *\<^sub>R w"]
    and proj2_rep_inj and subset_inj_on [of proj2_rep UNIV "range (($) a)"]
  have "\<dots> = (\<Sum> w\<in>?B. (c w) *\<^sub>R w)" by simp
  also from \<open>(\<Sum> w \<in> ?B. (c w) *\<^sub>R w) = ?v\<close> have "\<dots> = ?v" by simp
  finally have "(vector [1,1,1]) v* ?C = ?v" .
  with \<open>apply_cltn2 (proj2_abs (vector [1,1,1])) ?A =
    proj2_abs (vector [1,1,1] v* ?C)\<close>
  have "apply_cltn2 (proj2_abs (vector [1,1,1])) ?A = proj2_abs ?v" by simp
  with proj2_abs_rep have "apply_cltn2 (proj2_abs (vector [1,1,1])) ?A = a3"
    by simp
  have "\<forall> j. apply_cltn2 (proj2_abs (axis j 1)) ?A = a$j"
  proof
    fix j :: "3"
    have "((axis j 1)::real^3) \<noteq> 0" by (simp add: vec_eq_iff axis_def)
    with apply_cltn2_abs and \<open>invertible ?C\<close>
    have "apply_cltn2 (proj2_abs (axis j 1)) ?A = proj2_abs (axis j 1 v* ?C)"
      by simp

    have "\<forall> i\<in>(UNIV-{j}).
      ((axis j 1)$i * c (proj2_rep (a$i))) *\<^sub>R (proj2_rep (a$i)) = 0"
      by (simp add: axis_def)
    with sum.mono_neutral_left [of UNIV "{j}"
      "\<lambda> i. ((axis j 1)$i * c (proj2_rep (a$i))) *\<^sub>R (proj2_rep (a$i))"]
      and vector_matrix_row [of "axis j 1" ?C]
    have "(axis j 1) v* ?C = ?C$j" by (simp add: scalar_equiv)
    hence "(axis j 1) v* ?C = c (proj2_rep (a$j)) *\<^sub>R (proj2_rep (a$j))" by simp
    with proj2_abs_mult_rep and \<open>\<forall> i. c (proj2_rep (a$i)) \<noteq> 0\<close>
      and \<open>apply_cltn2 (proj2_abs (axis j 1)) ?A = proj2_abs (axis j 1 v* ?C)\<close>
    show "apply_cltn2 (proj2_abs (axis j 1)) ?A = a$j"
      by simp
  qed
  with \<open>apply_cltn2 (proj2_abs (vector [1,1,1])) ?A = a3\<close>
  show "\<exists> A. apply_cltn2 (proj2_abs (vector [1,1,1])) A = a3 \<and>
    (\<forall> j. apply_cltn2 (proj2_abs (axis j 1)) A = a$j)"
    by auto
qed

lemma statement53_existence:
  fixes p :: "proj2^4^2"
  assumes "\<forall> i. proj2_no_3_Col (range (($) (p$i)))"
  shows "\<exists> C. \<forall> j. apply_cltn2 (p$0$j) C = p$1$j"
proof -
  let ?q = "\<chi> i. \<chi> j::3. p$i $ (of_int (Rep_bit1 j))"
  let ?D = "\<chi> i. \<some> D. apply_cltn2 (proj2_abs (vector [1,1,1])) D = p$i$3
    \<and> (\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) D = ?q$i$j')"
  have "\<forall> i. apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$i) = p$i$3
    \<and> (\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$i) = ?q$i$j')"
  proof
    fix i
    have "range (($) (p$i)) = insert (p$i$3) (range (($) (?q$i)))"
    proof
      show "range (($) (p$i)) \<supseteq> insert (p$i$3) (range (($) (?q$i)))" by auto
      show "range (($) (p$i)) \<subseteq> insert (p$i$3) (range (($) (?q$i)))"
      proof
        fix r
        assume "r \<in> range (($) (p$i))"
        then obtain j where "r = p$i$j" by auto
        with eq_3_or_of_3 [of j]
        show "r \<in> insert (p$i$3) (range (($) (?q$i)))" by auto
      qed
    qed
    moreover from \<open>\<forall> i. proj2_no_3_Col (range (($) (p$i)))\<close>
    have "proj2_no_3_Col (range (($) (p$i)))" ..
    ultimately have "proj2_no_3_Col (insert (p$i$3) (range (($) (?q$i))))"
      by simp
    hence "\<exists> D. apply_cltn2 (proj2_abs (vector [1,1,1])) D = p$i$3
      \<and> (\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) D = ?q$i$j')"
      by (rule statement52_existence)
    with someI_ex [of "\<lambda> D. apply_cltn2 (proj2_abs (vector [1,1,1])) D = p$i$3
      \<and> (\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) D = ?q$i$j')"]
    show "apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$i) = p$i$3
      \<and> (\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$i) = ?q$i$j')"
      by simp
  qed
  hence "apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$0) = p$0$3"
    and "apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$1) = p$1$3"
    and "\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$0) = ?q$0$j'"
    and "\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$1) = ?q$1$j'"
    by simp_all

  let ?C = "cltn2_compose (cltn2_inverse (?D$0)) (?D$1)"
  have "\<forall> j. apply_cltn2 (p$0$j) ?C = p$1$j"
  proof
    fix j
    show "apply_cltn2 (p$0$j) ?C = p$1$j"
    proof cases
      assume "j = 3"
      with \<open>apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$0) = p$0$3\<close>
        and  cltn2.act_inv_iff
      have
        "apply_cltn2 (p$0$j) (cltn2_inverse (?D$0)) = proj2_abs (vector [1,1,1])"
        by simp
      with \<open>apply_cltn2 (proj2_abs (vector [1,1,1])) (?D$1) = p$1$3\<close>
        and \<open>j = 3\<close>
        and cltn2.act_act [of "cltn2_inverse (?D$0)" "?D$1" "p$0$j"]
      show "apply_cltn2 (p$0$j) ?C = p$1$j" by simp
    next
      assume "j \<noteq> 3"
      with eq_3_or_of_3 obtain j' :: 3 where "j = of_int (Rep_bit1 j')"
        by metis
      with \<open>\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$0) = ?q$0$j'\<close>
        and \<open>\<forall> j'. apply_cltn2 (proj2_abs (axis j' 1)) (?D$1) = ?q$1$j'\<close>
      have "p$0$j = apply_cltn2 (proj2_abs (axis j' 1)) (?D$0)"
        and "p$1$j = apply_cltn2 (proj2_abs (axis j' 1)) (?D$1)"
        by simp_all
      from \<open>p$0$j = apply_cltn2 (proj2_abs (axis j' 1)) (?D$0)\<close>
        and cltn2.act_inv_iff
      have "apply_cltn2 (p$0$j) (cltn2_inverse (?D$0)) = proj2_abs (axis j' 1)"
        by simp
      with \<open>p$1$j = apply_cltn2 (proj2_abs (axis j' 1)) (?D$1)\<close>
        and cltn2.act_act [of "cltn2_inverse (?D$0)" "?D$1" "p$0$j"]
      show "apply_cltn2 (p$0$j) ?C = p$1$j" by simp
    qed
  qed
  thus "\<exists> C. \<forall> j. apply_cltn2 (p$0$j) C = p$1$j" by (rule exI [of _ ?C])
qed

lemma apply_cltn2_linear:
  assumes "j *\<^sub>R v + k *\<^sub>R w \<noteq> 0"
  shows "j *\<^sub>R (v v* cltn2_rep C) + k *\<^sub>R (w v* cltn2_rep C) \<noteq> 0"
  (is "?u \<noteq> 0")
  and "apply_cltn2 (proj2_abs (j *\<^sub>R v + k *\<^sub>R w)) C
  = proj2_abs (j *\<^sub>R (v v* cltn2_rep C) + k *\<^sub>R (w v* cltn2_rep C))"
proof -
  have "?u = (j *\<^sub>R v + k *\<^sub>R w) v* cltn2_rep C"
    by (simp only: vector_matrix_left_distrib scaleR_vector_matrix_assoc)
  with \<open>j *\<^sub>R v + k *\<^sub>R w \<noteq> 0\<close> and non_zero_mult_rep_non_zero
  show "?u \<noteq> 0" by simp

  from \<open>?u = (j *\<^sub>R v + k *\<^sub>R w) v* cltn2_rep C\<close>
    and \<open>j *\<^sub>R v + k *\<^sub>R w \<noteq> 0\<close>
    and apply_cltn2_left_abs
  show "apply_cltn2 (proj2_abs (j *\<^sub>R v + k *\<^sub>R w)) C = proj2_abs ?u"
    by simp
qed

lemma apply_cltn2_imp_mult:
  assumes "apply_cltn2 p C = q"
  shows "\<exists> k. k \<noteq> 0 \<and> proj2_rep p v* cltn2_rep C = k *\<^sub>R proj2_rep q"
proof -
  have "proj2_rep p v* cltn2_rep C \<noteq> 0" by (rule rep_mult_rep_non_zero)

  from \<open>apply_cltn2 p C = q\<close>
  have "proj2_abs (proj2_rep p v* cltn2_rep C) = q" by (unfold apply_cltn2_def)
  hence "proj2_rep (proj2_abs (proj2_rep p v* cltn2_rep C)) = proj2_rep q"
    by simp
  with \<open>proj2_rep p v* cltn2_rep C \<noteq> 0\<close> and proj2_rep_abs2 [of "proj2_rep p v* cltn2_rep C"]
  have "\<exists> j. j \<noteq> 0 \<and> proj2_rep q = j *\<^sub>R (proj2_rep p v* cltn2_rep C)" by simp
  then obtain j where "j \<noteq> 0"
    and "proj2_rep q = j *\<^sub>R (proj2_rep p v* cltn2_rep C)" by auto
  hence "proj2_rep p v* cltn2_rep C = (1/j) *\<^sub>R proj2_rep q"
    by (simp add: field_simps)
  with \<open>j \<noteq> 0\<close>
  show "\<exists> k. k \<noteq> 0 \<and> proj2_rep p v* cltn2_rep C = k *\<^sub>R proj2_rep q"
    by (simp add: exI [of _ "1/j"])
qed

lemma statement55:
  assumes "p \<noteq> q"
  and "apply_cltn2 p C = q"
  and "apply_cltn2 q C = p"
  and "proj2_incident p l"
  and "proj2_incident q l"
  and "proj2_incident r l"
  shows "apply_cltn2 (apply_cltn2 r C) C = r"
proof cases
  assume "r = p"
  with \<open>apply_cltn2 p C = q\<close> and \<open>apply_cltn2 q C = p\<close>
  show "apply_cltn2 (apply_cltn2 r C) C = r" by simp
next
  assume "r \<noteq> p"

  from \<open>apply_cltn2 p C = q\<close> and apply_cltn2_imp_mult [of p C q]
  obtain i where "i \<noteq> 0" and "proj2_rep p v* cltn2_rep C = i *\<^sub>R proj2_rep q"
    by auto

  from \<open>apply_cltn2 q C = p\<close> and apply_cltn2_imp_mult [of q C p]
  obtain j where "j \<noteq> 0" and "proj2_rep q v* cltn2_rep C = j *\<^sub>R proj2_rep p"
    by auto

  from \<open>p \<noteq> q\<close>
    and \<open>proj2_incident p l\<close>
    and \<open>proj2_incident q l\<close>
    and \<open>proj2_incident r l\<close>
    and proj2_incident_iff
  have "r = p \<or> (\<exists> k. r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q))"
    by fast
  with \<open>r \<noteq> p\<close>
  obtain k where "r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)" by auto

  from \<open>p \<noteq> q\<close> and proj2_rep_dependent [of k p 1 q]
  have "k *\<^sub>R proj2_rep p + proj2_rep q \<noteq> 0" by auto
  with \<open>r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)\<close>
    and apply_cltn2_linear [of k "proj2_rep p" 1 "proj2_rep q"]
  have "k *\<^sub>R (proj2_rep p v* cltn2_rep C) + proj2_rep q v* cltn2_rep C \<noteq> 0"
    and "apply_cltn2 r C
    = proj2_abs
    (k *\<^sub>R (proj2_rep p v* cltn2_rep C) + proj2_rep q v* cltn2_rep C)"
    by simp_all
  with \<open>proj2_rep p v* cltn2_rep C = i *\<^sub>R proj2_rep q\<close>
    and \<open>proj2_rep q v* cltn2_rep C = j *\<^sub>R proj2_rep p\<close>
  have "(k * i) *\<^sub>R proj2_rep q + j *\<^sub>R proj2_rep p \<noteq> 0"
    and "apply_cltn2 r C
    = proj2_abs ((k * i) *\<^sub>R proj2_rep q + j *\<^sub>R proj2_rep p)"
    by simp_all
  with apply_cltn2_linear
  have "apply_cltn2 (apply_cltn2 r C) C
    = proj2_abs
    ((k * i) *\<^sub>R (proj2_rep q v* cltn2_rep C)
    + j *\<^sub>R (proj2_rep p v* cltn2_rep C))"
    by simp
  with \<open>proj2_rep p v* cltn2_rep C = i *\<^sub>R proj2_rep q\<close>
    and \<open>proj2_rep q v* cltn2_rep C = j *\<^sub>R proj2_rep p\<close>
  have "apply_cltn2 (apply_cltn2 r C) C
    = proj2_abs ((k * i * j) *\<^sub>R proj2_rep p + (j * i) *\<^sub>R proj2_rep q)"
    by simp
  also have "\<dots> = proj2_abs ((i * j) *\<^sub>R (k *\<^sub>R proj2_rep p + proj2_rep q))"
    by (simp add: algebra_simps)
  also from \<open>i \<noteq> 0\<close> and \<open>j \<noteq> 0\<close> and proj2_abs_mult
  have "\<dots> = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)" by simp
  also from \<open>r = proj2_abs (k *\<^sub>R proj2_rep p + proj2_rep q)\<close>
  have "\<dots> = r" by simp
  finally show "apply_cltn2 (apply_cltn2 r C) C = r" .
qed

subsection "Cross ratios"

definition cross_ratio :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> real" where
  "cross_ratio p q r s \<equiv> proj2_Col_coeff p q s / proj2_Col_coeff p q r"

definition cross_ratio_correct :: "proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> proj2 \<Rightarrow> bool" where
  "cross_ratio_correct p q r s \<equiv>
  proj2_set_Col {p,q,r,s} \<and> p \<noteq> q \<and> r \<noteq> p \<and> s \<noteq> p \<and> r \<noteq> q"

lemma proj2_Col_coeff_abs:
  assumes "p \<noteq> q" and "j \<noteq> 0"
  shows "proj2_Col_coeff p q (proj2_abs (i *\<^sub>R proj2_rep p + j *\<^sub>R proj2_rep q))
  = i/j"
  (is "proj2_Col_coeff p q ?r = i/j")
proof -
  from \<open>j \<noteq> 0\<close>
    and proj2_abs_mult [of "1/j" "i *\<^sub>R proj2_rep p + j *\<^sub>R proj2_rep q"]
  have "?r = proj2_abs ((i/j) *\<^sub>R proj2_rep p + proj2_rep q)"
    by (simp add: scaleR_right_distrib)

  from \<open>p \<noteq> q\<close> and proj2_rep_dependent [of _ p 1 q]
  have "(i/j) *\<^sub>R proj2_rep p + proj2_rep q \<noteq> 0" by auto
  with \<open>?r = proj2_abs ((i/j) *\<^sub>R proj2_rep p + proj2_rep q)\<close>
    and proj2_rep_abs2
  obtain k where "k \<noteq> 0"
    and "proj2_rep ?r = k *\<^sub>R ((i/j) *\<^sub>R proj2_rep p + proj2_rep q)"
    by auto
  hence "(k*i/j) *\<^sub>R proj2_rep p + k *\<^sub>R proj2_rep q - proj2_rep ?r = 0"
    by (simp add: scaleR_right_distrib)
  hence "\<exists> l. (k*i/j) *\<^sub>R proj2_rep p + k *\<^sub>R proj2_rep q + l *\<^sub>R proj2_rep ?r = 0
    \<and> (k*i/j \<noteq> 0 \<or> k \<noteq> 0 \<or> l \<noteq> 0)"
    by (simp add: exI [of _ "-1"])
  hence "proj2_Col p q ?r" by (unfold proj2_Col_def) auto

  have "?r \<noteq> p"
  proof
    assume "?r = p"
    with \<open>(k*i/j) *\<^sub>R proj2_rep p + k *\<^sub>R proj2_rep q - proj2_rep ?r = 0\<close>
    have "(k*i/j - 1) *\<^sub>R proj2_rep p + k *\<^sub>R proj2_rep q = 0"
      by (simp add: algebra_simps)
    with \<open>k \<noteq> 0\<close> and proj2_rep_dependent have "p = q" by simp
    with \<open>p \<noteq> q\<close> show False ..
  qed
  with \<open>proj2_Col p q ?r\<close> and \<open>p \<noteq> q\<close>
  have "?r = proj2_abs (proj2_Col_coeff p q ?r *\<^sub>R proj2_rep p + proj2_rep q)"
    by (rule proj2_Col_coeff)
  with \<open>p \<noteq> q\<close> and \<open>?r = proj2_abs ((i/j) *\<^sub>R proj2_rep p + proj2_rep q)\<close>
    and proj2_Col_coeff_unique
  show "proj2_Col_coeff p q ?r = i/j" by simp
qed

lemma proj2_set_Col_coeff:
  assumes "proj2_set_Col S" and "{p,q,r} \<subseteq> S" and "p \<noteq> q" and "r \<noteq> p"
  shows "r = proj2_abs (proj2_Col_coeff p q r *\<^sub>R proj2_rep p + proj2_rep q)"
  (is "r = proj2_abs (?i *\<^sub>R ?u + ?v)")
proof -
  from \<open>{p,q,r} \<subseteq> S\<close> and \<open>proj2_set_Col S\<close>
  have "proj2_set_Col {p,q,r}" by (rule proj2_subset_Col)
  hence "proj2_Col p q r" by (subst proj2_Col_iff_set_Col)
  with \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and proj2_Col_coeff
  show "r = proj2_abs (?i *\<^sub>R ?u + ?v)" by simp
qed

lemma cross_ratio_abs:
  fixes u v :: "real^3" and i j k l :: real
  assumes "u \<noteq> 0" and "v \<noteq> 0" and "proj2_abs u \<noteq> proj2_abs v"
  and "j \<noteq> 0" and "l \<noteq> 0"
  shows "cross_ratio (proj2_abs u) (proj2_abs v)
  (proj2_abs (i *\<^sub>R u + j *\<^sub>R v))
  (proj2_abs (k *\<^sub>R u + l *\<^sub>R v))
  = j * k / (i * l)"
  (is "cross_ratio ?p ?q ?r ?s = _")
proof -
  from \<open>u \<noteq> 0\<close> and proj2_rep_abs2
  obtain g where "g \<noteq> 0" and "proj2_rep ?p = g *\<^sub>R u" by auto

  from \<open>v \<noteq> 0\<close> and proj2_rep_abs2
  obtain h where "h \<noteq> 0" and "proj2_rep ?q = h *\<^sub>R v" by auto
  with \<open>g \<noteq> 0\<close> and \<open>proj2_rep ?p = g *\<^sub>R u\<close>
  have "?r = proj2_abs ((i/g) *\<^sub>R proj2_rep ?p + (j/h) *\<^sub>R proj2_rep ?q)"
    and "?s = proj2_abs ((k/g) *\<^sub>R proj2_rep ?p + (l/h) *\<^sub>R proj2_rep ?q)"
    by (simp_all add: field_simps)
  with \<open>?p \<noteq> ?q\<close> and \<open>h \<noteq> 0\<close> and \<open>j \<noteq> 0\<close> and \<open>l \<noteq> 0\<close> and proj2_Col_coeff_abs
  have "proj2_Col_coeff ?p ?q ?r = h*i/(g*j)"
    and "proj2_Col_coeff ?p ?q ?s = h*k/(g*l)"
    by simp_all
  with \<open>g \<noteq> 0\<close> and \<open>h \<noteq> 0\<close>
  show "cross_ratio ?p ?q ?r ?s = j*k/(i*l)"
    by (unfold cross_ratio_def) (simp add: field_simps)
qed

lemma cross_ratio_abs2:
  assumes "p \<noteq> q"
  shows "cross_ratio p q
  (proj2_abs (i *\<^sub>R proj2_rep p + proj2_rep q))
  (proj2_abs (j *\<^sub>R proj2_rep p + proj2_rep q))
  = j/i"
  (is "cross_ratio p q ?r ?s = _")
proof -
  let ?u = "proj2_rep p"
  let ?v = "proj2_rep q"
  have "?u \<noteq> 0" and "?v \<noteq> 0" by (rule proj2_rep_non_zero)+

  have "proj2_abs ?u = p" and "proj2_abs ?v = q" by (rule proj2_abs_rep)+
  with \<open>?u \<noteq> 0\<close> and \<open>?v \<noteq> 0\<close> and \<open>p \<noteq> q\<close> and cross_ratio_abs [of ?u ?v 1 1 i j]
  show "cross_ratio p q ?r ?s = j/i" by simp
qed

lemma cross_ratio_correct_cltn2:
  assumes "cross_ratio_correct p q r s"
  shows "cross_ratio_correct (apply_cltn2 p C) (apply_cltn2 q C)
  (apply_cltn2 r C) (apply_cltn2 s C)"
  (is "cross_ratio_correct ?pC ?qC ?rC ?sC")
proof -
  from \<open>cross_ratio_correct p q r s\<close>
  have "proj2_set_Col {p,q,r,s}"
    and "p \<noteq> q" and "r \<noteq> p" and "s \<noteq> p" and "r \<noteq> q"
    by (unfold cross_ratio_correct_def) simp_all

  have "{apply_cltn2 t C | t. t \<in> {p,q,r,s}} = {?pC,?qC,?rC,?sC}" by auto
  with \<open>proj2_set_Col {p,q,r,s}\<close>
    and apply_cltn2_preserve_set_Col [of "{p,q,r,s}" C]
  have "proj2_set_Col {?pC,?qC,?rC,?sC}" by simp

  from \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close> and \<open>r \<noteq> q\<close> and apply_cltn2_injective
  have "?pC \<noteq> ?qC" and "?rC \<noteq> ?pC" and "?sC \<noteq> ?pC" and "?rC \<noteq> ?qC" by fast+
  with \<open>proj2_set_Col {?pC,?qC,?rC,?sC}\<close>
  show "cross_ratio_correct ?pC ?qC ?rC ?sC"
    by (unfold cross_ratio_correct_def) simp
qed

lemma cross_ratio_cltn2:
  assumes "proj2_set_Col {p,q,r,s}" and "p \<noteq> q" and "r \<noteq> p" and "s \<noteq> p"
  shows "cross_ratio (apply_cltn2 p C) (apply_cltn2 q C)
  (apply_cltn2 r C) (apply_cltn2 s C)
  = cross_ratio p q r s"
  (is "cross_ratio ?pC ?qC ?rC ?sC = _")
proof -
  let ?u = "proj2_rep p"
  let ?v = "proj2_rep q"
  let ?i = "proj2_Col_coeff p q r"
  let ?j = "proj2_Col_coeff p q s"
  from \<open>proj2_set_Col {p,q,r,s}\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close>
    and proj2_set_Col_coeff
  have "r = proj2_abs (?i *\<^sub>R ?u + ?v)" and "s = proj2_abs (?j *\<^sub>R ?u + ?v)"
    by simp_all

  let ?uC = "?u v* cltn2_rep C"
  let ?vC = "?v v* cltn2_rep C"
  have "?uC \<noteq> 0" and "?vC \<noteq> 0" by (rule rep_mult_rep_non_zero)+

  have "proj2_abs ?uC = ?pC" and "proj2_abs ?vC = ?qC"
    by (unfold apply_cltn2_def) simp_all

  from \<open>p \<noteq> q\<close> and apply_cltn2_injective have "?pC \<noteq> ?qC" by fast

  from \<open>p \<noteq> q\<close> and proj2_rep_dependent [of _ p 1 q]
  have "?i *\<^sub>R ?u + ?v \<noteq> 0" and "?j *\<^sub>R ?u + ?v \<noteq> 0" by auto
  with \<open>r = proj2_abs (?i *\<^sub>R ?u + ?v)\<close> and \<open>s = proj2_abs (?j *\<^sub>R ?u + ?v)\<close>
    and apply_cltn2_linear [of ?i ?u 1 ?v]
    and apply_cltn2_linear [of ?j ?u 1 ?v]
  have "?rC = proj2_abs (?i *\<^sub>R ?uC + ?vC)"
    and "?sC = proj2_abs (?j *\<^sub>R ?uC + ?vC)"
    by simp_all
  with \<open>?uC \<noteq> 0\<close> and \<open>?vC \<noteq> 0\<close> and \<open>proj2_abs ?uC = ?pC\<close>
    and \<open>proj2_abs ?vC = ?qC\<close> and \<open>?pC \<noteq> ?qC\<close>
    and cross_ratio_abs [of ?uC ?vC 1 1 ?i ?j]
  have "cross_ratio ?pC ?qC ?rC ?sC = ?j/?i" by simp
  thus "cross_ratio ?pC ?qC ?rC ?sC = cross_ratio p q r s"
    unfolding cross_ratio_def [of p q r s] .
qed

lemma cross_ratio_unique:
  assumes "cross_ratio_correct p q r s" and "cross_ratio_correct p q r t"
  and "cross_ratio p q r s = cross_ratio p q r t"
  shows "s = t"
proof -
  from \<open>cross_ratio_correct p q r s\<close> and \<open>cross_ratio_correct p q r t\<close>
  have "proj2_set_Col {p,q,r,s}" and "proj2_set_Col {p,q,r,t}"
    and "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q" and "s \<noteq> p" and "t \<noteq> p"
    by (unfold cross_ratio_correct_def) simp_all

  let ?u = "proj2_rep p"
  let ?v = "proj2_rep q"
  let ?i = "proj2_Col_coeff p q r"
  let ?j = "proj2_Col_coeff p q s"
  let ?k = "proj2_Col_coeff p q t"
  from \<open>proj2_set_Col {p,q,r,s}\<close> and \<open>proj2_set_Col {p,q,r,t}\<close>
    and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close> and \<open>t \<noteq> p\<close> and proj2_set_Col_coeff
  have "r = proj2_abs (?i *\<^sub>R ?u + ?v)"
    and "s = proj2_abs (?j *\<^sub>R ?u + ?v)"
    and "t = proj2_abs (?k *\<^sub>R ?u + ?v)"
    by simp_all

  from \<open>r \<noteq> q\<close> and \<open>r = proj2_abs (?i *\<^sub>R ?u + ?v)\<close>
  have "?i \<noteq> 0" by (auto simp add: proj2_abs_rep)
  with \<open>cross_ratio p q r s = cross_ratio p q r t\<close>
  have "?j = ?k" by (unfold cross_ratio_def) simp
  with \<open>s = proj2_abs (?j *\<^sub>R ?u + ?v)\<close> and \<open>t = proj2_abs (?k *\<^sub>R ?u + ?v)\<close>
  show "s = t" by simp
qed

lemma cltn2_three_point_line:
  assumes "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q"
  and "proj2_incident p l" and "proj2_incident q l" and "proj2_incident r l"
  and "apply_cltn2 p C = p" and "apply_cltn2 q C = q" and "apply_cltn2 r C = r"
  and "proj2_incident s l"
  shows "apply_cltn2 s C = s" (is "?sC = s")
proof cases
  assume "s = p"
  with \<open>apply_cltn2 p C = p\<close> show "?sC = s" by simp
next
  assume "s \<noteq> p"

  let ?pC = "apply_cltn2 p C"
  let ?qC = "apply_cltn2 q C"
  let ?rC = "apply_cltn2 r C"

  from \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close> and \<open>proj2_incident r l\<close>
    and \<open>proj2_incident s l\<close>
  have "proj2_set_Col {p,q,r,s}" by (unfold proj2_set_Col_def) auto
  with \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close> and \<open>r \<noteq> q\<close>
  have "cross_ratio_correct p q r s" by (unfold cross_ratio_correct_def) simp
  hence "cross_ratio_correct ?pC ?qC ?rC ?sC"
    by (rule cross_ratio_correct_cltn2)
  with \<open>?pC = p\<close> and \<open>?qC = q\<close> and \<open>?rC = r\<close>
  have "cross_ratio_correct p q r ?sC" by simp

  from \<open>proj2_set_Col {p,q,r,s}\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close>
  have "cross_ratio ?pC ?qC ?rC ?sC = cross_ratio p q r s"
    by (rule cross_ratio_cltn2)
  with \<open>?pC = p\<close> and \<open>?qC = q\<close> and \<open>?rC = r\<close>
  have "cross_ratio p q r ?sC = cross_ratio p q r s" by simp
  with \<open>cross_ratio_correct p q r ?sC\<close> and \<open>cross_ratio_correct p q r s\<close>
  show "?sC = s" by (rule cross_ratio_unique)
qed

lemma cross_ratio_equal_cltn2:
  assumes "cross_ratio_correct p q r s"
  and "cross_ratio_correct (apply_cltn2 p C) (apply_cltn2 q C)
  (apply_cltn2 r C) t"
  (is "cross_ratio_correct ?pC ?qC ?rC t")
  and "cross_ratio (apply_cltn2 p C) (apply_cltn2 q C) (apply_cltn2 r C) t
    = cross_ratio p q r s"
  shows "t = apply_cltn2 s C" (is "t = ?sC")
proof -
  from \<open>cross_ratio_correct p q r s\<close>
  have "cross_ratio_correct ?pC ?qC ?rC ?sC" by (rule cross_ratio_correct_cltn2)

  from \<open>cross_ratio_correct p q r s\<close>
  have "proj2_set_Col {p,q,r,s}" and "p \<noteq> q" and "r \<noteq> p" and "s \<noteq> p"
    by (unfold cross_ratio_correct_def) simp_all
  hence "cross_ratio ?pC ?qC ?rC ?sC = cross_ratio p q r s"
    by (rule cross_ratio_cltn2)
  with \<open>cross_ratio ?pC ?qC ?rC t = cross_ratio p q r s\<close>
  have "cross_ratio ?pC ?qC ?rC t = cross_ratio ?pC ?qC ?rC ?sC" by simp
  with \<open>cross_ratio_correct ?pC ?qC ?rC t\<close>
    and \<open>cross_ratio_correct ?pC ?qC ?rC ?sC\<close>
  show "t = ?sC" by (rule cross_ratio_unique)
qed

lemma proj2_Col_distinct_coeff_non_zero:
  assumes "proj2_Col p q r" and "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q"
  shows "proj2_Col_coeff p q r \<noteq> 0"
proof
  assume "proj2_Col_coeff p q r = 0"

  from \<open>proj2_Col p q r\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close>
  have "r = proj2_abs ((proj2_Col_coeff p q r) *\<^sub>R proj2_rep p + proj2_rep q)"
    by (rule proj2_Col_coeff)
  with \<open>proj2_Col_coeff p q r = 0\<close> have "r = q" by (simp add: proj2_abs_rep)
  with \<open>r \<noteq> q\<close> show False ..
qed

lemma cross_ratio_product:
  assumes "proj2_Col p q s" and "p \<noteq> q" and "s \<noteq> p" and "s \<noteq> q"
  shows "cross_ratio p q r s * cross_ratio p q s t = cross_ratio p q r t"
proof -
  from \<open>proj2_Col p q s\<close> and \<open>p \<noteq> q\<close> and \<open>s \<noteq> p\<close> and \<open>s \<noteq> q\<close>
  have "proj2_Col_coeff p q s \<noteq> 0" by (rule proj2_Col_distinct_coeff_non_zero)
  thus "cross_ratio p q r s * cross_ratio p q s t = cross_ratio p q r t"
    by (unfold cross_ratio_def) simp
qed

lemma cross_ratio_equal_1:
  assumes "proj2_Col p q r" and "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q"
  shows "cross_ratio p q r r = 1"
proof -
  from \<open>proj2_Col p q r\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>r \<noteq> q\<close>
  have "proj2_Col_coeff p q r \<noteq> 0" by (rule proj2_Col_distinct_coeff_non_zero)
  thus "cross_ratio p q r r = 1" by (unfold cross_ratio_def) simp
qed

lemma cross_ratio_1_equal:
  assumes "cross_ratio_correct p q r s" and "cross_ratio p q r s = 1"
  shows "r = s"
proof -
  from \<open>cross_ratio_correct p q r s\<close>
  have "proj2_set_Col {p,q,r,s}" and "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q"
    by (unfold cross_ratio_correct_def) simp_all

  from \<open>proj2_set_Col {p,q,r,s}\<close>
  have "proj2_set_Col {p,q,r}"
    by (simp add: proj2_subset_Col [of "{p,q,r}" "{p,q,r,s}"])
  with \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>r \<noteq> q\<close>
  have "cross_ratio_correct p q r r" by (unfold cross_ratio_correct_def) simp

  from \<open>proj2_set_Col {p,q,r}\<close>
  have "proj2_Col p q r" by (subst proj2_Col_iff_set_Col)
  with \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>r \<noteq> q\<close>
  have "cross_ratio p q r r = 1" by (simp add: cross_ratio_equal_1)
  with \<open>cross_ratio p q r s = 1\<close>
  have "cross_ratio p q r r = cross_ratio p q r s" by simp
  with \<open>cross_ratio_correct p q r r\<close> and \<open>cross_ratio_correct p q r s\<close>
  show "r = s" by (rule cross_ratio_unique)
qed

lemma cross_ratio_swap_34:
  shows "cross_ratio p q s r = 1 / (cross_ratio p q r s)"
  by (unfold cross_ratio_def) simp

lemma cross_ratio_swap_13_24:
  assumes "cross_ratio_correct p q r s" and "r \<noteq> s"
  shows "cross_ratio r s p q = cross_ratio p q r s"
proof -
  from \<open>cross_ratio_correct p q r s\<close>
  have "proj2_set_Col {p,q,r,s}" and "p \<noteq> q" and "r \<noteq> p" and "s \<noteq> p" and "r \<noteq> q"
    by (unfold cross_ratio_correct_def, simp_all)

  have "proj2_rep p \<noteq> 0" (is "?u \<noteq> 0") and "proj2_rep q \<noteq> 0" (is "?v \<noteq> 0")
    by (rule proj2_rep_non_zero)+

  have "p = proj2_abs ?u" and "q = proj2_abs ?v"
    by (simp_all add: proj2_abs_rep)
  with \<open>p \<noteq> q\<close> have "proj2_abs ?u \<noteq> proj2_abs ?v" by simp

  let ?i = "proj2_Col_coeff p q r"
  let ?j = "proj2_Col_coeff p q s"
  from \<open>proj2_set_Col {p,q,r,s}\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>s \<noteq> p\<close>
  have "r = proj2_abs (?i *\<^sub>R ?u + ?v)" (is "r = proj2_abs ?w")
    and "s = proj2_abs (?j *\<^sub>R ?u + ?v)" (is "s = proj2_abs ?x")
    by (simp_all add: proj2_set_Col_coeff)
  with \<open>r \<noteq> s\<close> have "?i \<noteq> ?j" by auto

  from \<open>?u \<noteq> 0\<close> and \<open>?v \<noteq> 0\<close> and \<open>proj2_abs ?u \<noteq> proj2_abs ?v\<close>
    and dependent_proj2_abs [of ?u ?v _ 1]
  have "?w \<noteq> 0" and "?x \<noteq> 0" by auto

  from \<open>r = proj2_abs (?i *\<^sub>R ?u + ?v)\<close> and \<open>r \<noteq> q\<close>
  have "?i \<noteq> 0" by (auto simp add: proj2_abs_rep)

  have "?w - ?x = (?i - ?j) *\<^sub>R ?u" by (simp add: algebra_simps)
  with \<open>?i \<noteq> ?j\<close>
  have "p = proj2_abs (?w - ?x)" by (simp add: proj2_abs_mult_rep)

  have "?j *\<^sub>R ?w - ?i *\<^sub>R ?x = (?j - ?i) *\<^sub>R ?v" by (simp add: algebra_simps)
  with \<open>?i \<noteq> ?j\<close>
  have "q = proj2_abs (?j *\<^sub>R ?w - ?i *\<^sub>R ?x)" by (simp add: proj2_abs_mult_rep)
  with \<open>?w \<noteq> 0\<close> and \<open>?x \<noteq> 0\<close> and \<open>r \<noteq> s\<close> and \<open>?i \<noteq> 0\<close> and \<open>r = proj2_abs ?w\<close>
    and \<open>s = proj2_abs ?x\<close> and \<open>p = proj2_abs (?w - ?x)\<close>
    and cross_ratio_abs [of ?w ?x "-1" "-?i" 1 ?j]
  have "cross_ratio r s p q = ?j / ?i" by (simp add: algebra_simps)
  thus "cross_ratio r s p q = cross_ratio p q r s"
    by (unfold cross_ratio_def [of p q r s], simp)
qed

lemma cross_ratio_swap_12:
  assumes "cross_ratio_correct p q r s" and "cross_ratio_correct q p r s"
  shows "cross_ratio q p r s = 1 / (cross_ratio p q r s)"
proof cases
  assume "r = s"

  from \<open>cross_ratio_correct p q r s\<close>
  have "proj2_set_Col {p,q,r,s}" and "p \<noteq> q" and "r \<noteq> p" and "r \<noteq> q"
    by (unfold cross_ratio_correct_def) simp_all

  from \<open>proj2_set_Col {p,q,r,s}\<close> and \<open>r = s\<close>
  have "proj2_Col p q r" by (simp_all add: proj2_Col_iff_set_Col)
  hence "proj2_Col q p r" by (rule proj2_Col_permute)
  with \<open>proj2_Col p q r\<close> and \<open>p \<noteq> q\<close> and \<open>r \<noteq> p\<close> and \<open>r \<noteq> q\<close> and \<open>r = s\<close>
  have "cross_ratio p q r s = 1" and "cross_ratio q p r s = 1"
    by (simp_all add: cross_ratio_equal_1)
  thus "cross_ratio q p r s = 1 / (cross_ratio p q r s)" by simp
next
  assume "r \<noteq> s"
  with \<open>cross_ratio_correct q p r s\<close>
  have "cross_ratio q p r s = cross_ratio r s q p"
    by (simp add: cross_ratio_swap_13_24)
  also have "\<dots> = 1 / (cross_ratio r s p q)" by (rule cross_ratio_swap_34)
  also from \<open>cross_ratio_correct p q r s\<close> and \<open>r \<noteq> s\<close>
  have "\<dots> = 1 / (cross_ratio p q r s)" by (simp add: cross_ratio_swap_13_24)
  finally show "cross_ratio q p r s = 1 / (cross_ratio p q r s)" .
qed

subsection "Cartesian subspace of the real projective plane"

definition vector2_append1 :: "real^2 \<Rightarrow> real^3" where
  "vector2_append1 v = vector [v$1, v$2, 1]"

lemma vector2_append1_non_zero: "vector2_append1 v \<noteq> 0"
proof -
  have "(vector2_append1 v)$3 \<noteq> 0$3"
    unfolding vector2_append1_def and vector_def
    by simp
  thus "vector2_append1 v \<noteq> 0" by auto
qed

definition proj2_pt :: "real^2 \<Rightarrow> proj2" where
  "proj2_pt v \<equiv> proj2_abs (vector2_append1 v)"

lemma proj2_pt_scalar:
  "\<exists> c. c \<noteq> 0 \<and> proj2_rep (proj2_pt v) = c *\<^sub>R vector2_append1 v"
  unfolding proj2_pt_def
  by (simp add: proj2_rep_abs2 vector2_append1_non_zero)

abbreviation z_non_zero :: "proj2 \<Rightarrow> bool" where
  "z_non_zero p \<equiv> (proj2_rep p)$3 \<noteq> 0"

definition cart2_pt :: "proj2 \<Rightarrow> real^2" where
  "cart2_pt p \<equiv>
  vector [(proj2_rep p)$1 / (proj2_rep p)$3, (proj2_rep p)$2 / (proj2_rep p)$3]"

definition cart2_append1 :: "proj2 \<Rightarrow> real^3" where
  "cart2_append1 p \<equiv>  (1 / ((proj2_rep p)$3)) *\<^sub>R proj2_rep p"

lemma cart2_append1_z:
  assumes "z_non_zero p"
  shows "(cart2_append1 p)$3 = 1"
  using \<open>z_non_zero p\<close>
  by (unfold cart2_append1_def) simp

lemma cart2_append1_non_zero:
  assumes "z_non_zero p"
  shows "cart2_append1 p \<noteq> 0"
proof -
  from \<open>z_non_zero p\<close> have "(cart2_append1 p)$3 = 1" by (rule cart2_append1_z)
  thus "cart2_append1 p \<noteq> 0" by (simp add: vec_eq_iff exI [of _ 3])
qed

lemma proj2_rep_cart2_append1:
  assumes "z_non_zero p"
  shows "proj2_rep p = ((proj2_rep p)$3) *\<^sub>R cart2_append1 p"
  using \<open>z_non_zero p\<close>
  by (unfold cart2_append1_def) simp

lemma proj2_abs_cart2_append1:
  assumes "z_non_zero p"
  shows "proj2_abs (cart2_append1 p) = p"
proof -
  from \<open>z_non_zero p\<close>
  have "proj2_abs (cart2_append1 p) = proj2_abs (proj2_rep p)"
    by (unfold cart2_append1_def) (simp add: proj2_abs_mult)
  thus "proj2_abs (cart2_append1 p) = p" by (simp add: proj2_abs_rep)
qed

lemma cart2_append1_inj:
  assumes "z_non_zero p" and "cart2_append1 p = cart2_append1 q"
  shows "p = q"
proof -
  from \<open>z_non_zero p\<close> have "(cart2_append1 p)$3 = 1" by (rule cart2_append1_z)
  with \<open>cart2_append1 p = cart2_append1 q\<close>
  have "(cart2_append1 q)$3 = 1" by simp
  hence "z_non_zero q" by (unfold cart2_append1_def) auto

  from \<open>cart2_append1 p = cart2_append1 q\<close>
  have "proj2_abs (cart2_append1 p) = proj2_abs (cart2_append1 q)" by simp
  with \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close>
  show "p = q" by (simp add: proj2_abs_cart2_append1)
qed

lemma cart2_append1:
  assumes "z_non_zero p"
  shows "vector2_append1 (cart2_pt p) = cart2_append1 p"
  using \<open>z_non_zero p\<close>
  unfolding vector2_append1_def
    and cart2_append1_def
    and cart2_pt_def
    and vector_def
  by (simp add: vec_eq_iff forall_3)

lemma cart2_proj2: "cart2_pt (proj2_pt v) = v"
proof -
  let ?v' = "vector2_append1 v"
  let ?p = "proj2_pt v"
  from proj2_pt_scalar
  obtain c where "c \<noteq> 0" and "proj2_rep ?p = c *\<^sub>R ?v'" by auto
  hence "(cart2_pt ?p)$1 = v$1" and "(cart2_pt ?p)$2 = v$2"
    unfolding cart2_pt_def and vector2_append1_def and vector_def
    by simp+
  thus "cart2_pt ?p = v" by (simp add: vec_eq_iff forall_2)
qed

lemma z_non_zero_proj2_pt: "z_non_zero (proj2_pt v)"
proof -
  from proj2_pt_scalar
  obtain c where "c \<noteq> 0" and "proj2_rep (proj2_pt v) = c *\<^sub>R (vector2_append1 v)"
    by auto
  from \<open>proj2_rep (proj2_pt v) = c *\<^sub>R (vector2_append1 v)\<close>
  have "(proj2_rep (proj2_pt v))$3 = c"
    unfolding vector2_append1_def and vector_def
    by simp
  with \<open>c \<noteq> 0\<close> show "z_non_zero (proj2_pt v)" by simp
qed

lemma cart2_append1_proj2: "cart2_append1 (proj2_pt v) = vector2_append1 v"
proof -
  from z_non_zero_proj2_pt
  have "cart2_append1 (proj2_pt v) = vector2_append1 (cart2_pt (proj2_pt v))"
    by (simp add: cart2_append1)
  thus "cart2_append1 (proj2_pt v) = vector2_append1 v"
    by (simp add: cart2_proj2)
qed

lemma proj2_pt_inj: "inj proj2_pt"
  by (simp add: inj_on_inverseI [of UNIV cart2_pt proj2_pt] cart2_proj2)

lemma proj2_cart2:
  assumes "z_non_zero p"
  shows "proj2_pt (cart2_pt p) = p"
proof -
  from \<open>z_non_zero p\<close>
  have "(proj2_rep p)$3 *\<^sub>R vector2_append1 (cart2_pt p) = proj2_rep p"
    unfolding vector2_append1_def and cart2_pt_def and vector_def
    by (simp add: vec_eq_iff forall_3)
  with \<open>z_non_zero p\<close>
    and proj2_abs_mult [of "(proj2_rep p)$3" "vector2_append1 (cart2_pt p)"]
  have "proj2_abs (vector2_append1 (cart2_pt p)) = proj2_abs (proj2_rep p)"
    by simp
  thus "proj2_pt (cart2_pt p) = p"
    by (unfold proj2_pt_def) (simp add: proj2_abs_rep)
qed

lemma cart2_injective:
  assumes "z_non_zero p" and "z_non_zero q" and "cart2_pt p = cart2_pt q"
  shows "p = q"
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close>
  have "proj2_pt (cart2_pt p) = p" and "proj2_pt (cart2_pt q) = q"
    by (simp_all add: proj2_cart2)

  from \<open>proj2_pt (cart2_pt p) = p\<close> and \<open>cart2_pt p = cart2_pt q\<close>
  have "proj2_pt (cart2_pt q) = p" by simp
  with \<open>proj2_pt (cart2_pt q) = q\<close> show "p = q" by simp
qed

lemma proj2_Col_iff_euclid:
  "proj2_Col (proj2_pt a) (proj2_pt b) (proj2_pt c) \<longleftrightarrow> real_euclid.Col a b c"
  (is "proj2_Col ?p ?q ?r \<longleftrightarrow> _")
proof
  let ?a' = "vector2_append1 a"
  let ?b' = "vector2_append1 b"
  let ?c' = "vector2_append1 c"
  let ?a'' = "proj2_rep ?p"
  let ?b'' = "proj2_rep ?q"
  let ?c'' = "proj2_rep ?r"
  from proj2_pt_scalar obtain i and j and k where
    "i \<noteq> 0" and "?a'' = i *\<^sub>R ?a'"
    and "j \<noteq> 0" and "?b'' = j *\<^sub>R ?b'"
    and "k \<noteq> 0" and "?c'' = k *\<^sub>R ?c'"
    by metis
  hence "?a' = (1/i) *\<^sub>R ?a''"
    and "?b' = (1/j) *\<^sub>R ?b''"
    and "?c' = (1/k) *\<^sub>R ?c''"
    by simp_all

  { assume "proj2_Col ?p ?q ?r"
    then obtain i' and j' and k' where
      "i' *\<^sub>R ?a'' + j' *\<^sub>R ?b'' + k' *\<^sub>R ?c'' = 0" and "i'\<noteq>0 \<or> j'\<noteq>0 \<or> k'\<noteq>0"
      unfolding proj2_Col_def
      by auto

    let ?i'' = "i * i'"
    let ?j'' = "j * j'"
    let ?k'' = "k * k'"
    from \<open>i\<noteq>0\<close> and \<open>j\<noteq>0\<close> and \<open>k\<noteq>0\<close> and \<open>i'\<noteq>0 \<or> j'\<noteq>0 \<or> k'\<noteq>0\<close>
    have "?i''\<noteq>0 \<or> ?j''\<noteq>0 \<or> ?k''\<noteq>0" by simp

    from \<open>i' *\<^sub>R ?a'' + j' *\<^sub>R ?b'' + k' *\<^sub>R ?c'' = 0\<close>
      and \<open>?a'' = i *\<^sub>R ?a'\<close>
      and \<open>?b'' = j *\<^sub>R ?b'\<close>
      and \<open>?c'' = k *\<^sub>R ?c'\<close>
    have "?i'' *\<^sub>R ?a' + ?j'' *\<^sub>R ?b' + ?k'' *\<^sub>R ?c' = 0"
      by (simp add: ac_simps)
    hence "(?i'' *\<^sub>R ?a' + ?j'' *\<^sub>R ?b' + ?k'' *\<^sub>R ?c')$3 = 0"
      by simp
    hence "?i'' + ?j'' + ?k'' = 0"
      unfolding vector2_append1_def and vector_def
      by simp

    have "(?i'' *\<^sub>R ?a' + ?j'' *\<^sub>R ?b' + ?k'' *\<^sub>R ?c')$1 =
      (?i'' *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c)$1"
      and "(?i'' *\<^sub>R ?a' + ?j'' *\<^sub>R ?b' + ?k'' *\<^sub>R ?c')$2 =
      (?i'' *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c)$2"
      unfolding vector2_append1_def and vector_def
      by simp+
    with \<open>?i'' *\<^sub>R ?a' + ?j'' *\<^sub>R ?b' + ?k'' *\<^sub>R ?c' = 0\<close>
    have "?i'' *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c = 0"
      by (simp add: vec_eq_iff forall_2)

    have "dep2 (b - a) (c - a)"
    proof cases
      assume "?k'' = 0"
      with \<open>?i'' + ?j'' + ?k'' = 0\<close> have "?j'' = -?i''" by simp
      with \<open>?i''\<noteq>0 \<or> ?j''\<noteq>0 \<or> ?k''\<noteq>0\<close> and \<open>?k'' = 0\<close> have "?i'' \<noteq> 0" by simp
      
      from \<open>?i'' *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c = 0\<close>
        and \<open>?k'' = 0\<close> and \<open>?j'' = -?i''\<close>
      have "?i'' *\<^sub>R a + (-?i'' *\<^sub>R b) = 0" by simp
      with \<open>?i'' \<noteq> 0\<close> have "a = b" by (simp add: algebra_simps)
      hence "b - a = 0 *\<^sub>R (c - a)" by simp
      moreover have "c - a = 1 *\<^sub>R (c - a)" by simp
      ultimately have "\<exists> x t s. b - a = t *\<^sub>R x \<and> c - a = s *\<^sub>R x"
        by blast
      thus "dep2 (b - a) (c - a)" unfolding dep2_def .
    next
      assume "?k'' \<noteq> 0"
      from \<open>?i'' + ?j'' + ?k'' = 0\<close> have "?i'' = -(?j'' + ?k'')" by simp
      with \<open>?i'' *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c = 0\<close>
      have "-(?j'' + ?k'') *\<^sub>R a + ?j'' *\<^sub>R b + ?k'' *\<^sub>R c = 0" by simp
      hence "?k'' *\<^sub>R (c - a) = - ?j'' *\<^sub>R (b - a)"
        by (simp add: scaleR_left_distrib
          scaleR_right_diff_distrib
          scaleR_left_diff_distrib
          algebra_simps)
      hence "(1/?k'') *\<^sub>R ?k'' *\<^sub>R (c - a) = (-?j'' / ?k'') *\<^sub>R (b - a)"
        by simp
      with \<open>?k'' \<noteq> 0\<close> have "c - a = (-?j'' / ?k'') *\<^sub>R (b - a)" by simp
      moreover have "b - a = 1 *\<^sub>R (b - a)" by simp
      ultimately have "\<exists> x t s. b - a = t *\<^sub>R x \<and> c - a = s *\<^sub>R x" by blast
      thus "dep2 (b - a) (c - a)" unfolding dep2_def .
    qed
    with Col_dep2 show "real_euclid.Col a b c" by auto
  }

  { assume "real_euclid.Col a b c"
    with Col_dep2 have "dep2 (b - a) (c - a)" by auto
    then obtain x and t and s where "b - a = t *\<^sub>R x" and "c - a = s *\<^sub>R x"
      unfolding dep2_def
      by auto

    show "proj2_Col ?p ?q ?r"
    proof cases
      assume "t = 0"
      with \<open>b - a = t *\<^sub>R x\<close> have "a = b" by simp
      with proj2_Col_coincide show "proj2_Col ?p ?q ?r" by simp
    next
      assume "t \<noteq> 0"

      from \<open>b - a = t *\<^sub>R x\<close> and \<open>c - a = s *\<^sub>R x\<close>
      have "s *\<^sub>R (b - a) = t *\<^sub>R (c - a)" by simp
      hence "(s - t) *\<^sub>R a + (-s) *\<^sub>R b + t *\<^sub>R c = 0"
        by (simp add: scaleR_right_diff_distrib
          scaleR_left_diff_distrib
          algebra_simps)
      hence "((s - t) *\<^sub>R ?a' + (-s) *\<^sub>R ?b' + t *\<^sub>R ?c')$1 = 0"
        and "((s - t) *\<^sub>R ?a' + (-s) *\<^sub>R ?b' + t *\<^sub>R ?c')$2 = 0"
        unfolding vector2_append1_def and vector_def
        by (simp_all add: vec_eq_iff)
      moreover have "((s - t) *\<^sub>R ?a' + (-s) *\<^sub>R ?b' + t *\<^sub>R ?c')$3 = 0"
        unfolding vector2_append1_def and vector_def
        by simp
      ultimately have "(s - t) *\<^sub>R ?a' + (-s) *\<^sub>R ?b' + t *\<^sub>R ?c' = 0"
        by (simp add: vec_eq_iff forall_3)
      with \<open>?a' = (1/i) *\<^sub>R ?a''\<close>
        and \<open>?b' = (1/j) *\<^sub>R ?b''\<close>
        and \<open>?c' = (1/k) *\<^sub>R ?c''\<close>
      have "((s - t)/i) *\<^sub>R ?a'' + (-s/j) *\<^sub>R ?b'' + (t/k) *\<^sub>R ?c'' = 0"
        by simp
      moreover from \<open>t \<noteq> 0\<close> and \<open>k \<noteq> 0\<close> have "t/k \<noteq> 0" by simp
      ultimately show "proj2_Col ?p ?q ?r"
        unfolding proj2_Col_def
        by blast
    qed
  }
qed

lemma proj2_Col_iff_euclid_cart2:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
  shows
  "proj2_Col p q r \<longleftrightarrow> real_euclid.Col (cart2_pt p) (cart2_pt q) (cart2_pt r)"
  (is "_ \<longleftrightarrow> real_euclid.Col ?a ?b ?c")
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
  have "proj2_pt ?a = p" and "proj2_pt ?b = q" and "proj2_pt ?c = r"
    by (simp_all add: proj2_cart2)
  with proj2_Col_iff_euclid [of ?a ?b ?c]
  show "proj2_Col p q r \<longleftrightarrow> real_euclid.Col ?a ?b ?c" by simp
qed

lemma euclid_Col_cart2_incident:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r" and "p \<noteq> q"
  and "proj2_incident p l" and "proj2_incident q l"
  and "real_euclid.Col (cart2_pt p) (cart2_pt q) (cart2_pt r)"
  (is "real_euclid.Col ?cp ?cq ?cr")
  shows "proj2_incident r l"
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
    and \<open>real_euclid.Col ?cp ?cq ?cr\<close>
  have "proj2_Col p q r" by (subst proj2_Col_iff_euclid_cart2, simp_all)
  hence "proj2_set_Col {p,q,r}" by (simp add: proj2_Col_iff_set_Col)
  then obtain m where
    "proj2_incident p m" and "proj2_incident q m" and "proj2_incident r m"
    by (unfold proj2_set_Col_def, auto)

  from \<open>p \<noteq> q\<close> and \<open>proj2_incident p l\<close> and \<open>proj2_incident q l\<close>
    and \<open>proj2_incident p m\<close> and \<open>proj2_incident q m\<close> and proj2_incident_unique
  have "l = m" by auto
  with \<open>proj2_incident r m\<close> show "proj2_incident r l" by simp
qed

lemma euclid_B_cart2_common_line:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
  and "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)"
  (is "B\<^sub>\<real> ?cp ?cq ?cr")
  shows "\<exists> l. proj2_incident p l \<and> proj2_incident q l \<and> proj2_incident r l"
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
    and \<open>B\<^sub>\<real> ?cp ?cq ?cr\<close> and proj2_Col_iff_euclid_cart2
  have "proj2_Col p q r" by (unfold real_euclid.Col_def) simp
  hence "proj2_set_Col {p,q,r}" by (simp add: proj2_Col_iff_set_Col)
  thus "\<exists> l. proj2_incident p l \<and> proj2_incident q l \<and> proj2_incident r l"
    by (unfold proj2_set_Col_def) simp
qed

lemma cart2_append1_between:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
  shows "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)
  \<longleftrightarrow> (\<exists> k\<ge>0. k \<le> 1
  \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p)"
proof -
  let ?cp = "cart2_pt p"
  let ?cq = "cart2_pt q"
  let ?cr = "cart2_pt r"
  let ?cp1 = "vector2_append1 ?cp"
  let ?cq1 = "vector2_append1 ?cq"
  let ?cr1 = "vector2_append1 ?cr"
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
  have "?cp1 = cart2_append1 p"
    and "?cq1 = cart2_append1 q"
    and "?cr1 = cart2_append1 r"
    by (simp_all add: cart2_append1)

  have "\<forall> k. ?cq - ?cp = k *\<^sub>R (?cr - ?cp) \<longleftrightarrow> ?cq = k *\<^sub>R ?cr + (1 - k) *\<^sub>R ?cp"
    by (simp add: algebra_simps)
  hence "\<forall> k. ?cq - ?cp = k *\<^sub>R (?cr - ?cp)
    \<longleftrightarrow> ?cq1 = k *\<^sub>R ?cr1 + (1 - k) *\<^sub>R ?cp1"
    unfolding vector2_append1_def and vector_def
    by (simp add: vec_eq_iff forall_2 forall_3)
  with \<open>?cp1 = cart2_append1 p\<close>
    and \<open>?cq1 = cart2_append1 q\<close>
    and \<open>?cr1 = cart2_append1 r\<close>
  have "\<forall> k. ?cq - ?cp = k *\<^sub>R (?cr - ?cp)
    \<longleftrightarrow> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
    by simp
  thus "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)
    \<longleftrightarrow> (\<exists> k\<ge>0. k \<le> 1
    \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p)"
    by (unfold real_euclid_B_def) simp
qed

lemma cart2_append1_between_right_strict:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
  and "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)" and "q \<noteq> r"
  shows "\<exists> k\<ge>0. k < 1
  \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
    and \<open>B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)\<close> and cart2_append1_between
  obtain k where "k \<ge> 0" and "k \<le> 1"
    and "cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
    by auto

  have "k \<noteq> 1"
  proof
    assume "k = 1"
    with \<open>cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p\<close>
    have "cart2_append1 q = cart2_append1 r" by simp
    with \<open>z_non_zero q\<close> have "q = r" by (rule cart2_append1_inj)
    with \<open>q \<noteq> r\<close> show False ..
  qed
  with \<open>k \<le> 1\<close> have "k < 1" by simp
  with \<open>k \<ge> 0\<close>
    and \<open>cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p\<close>
  show "\<exists> k\<ge>0. k < 1
    \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
    by (simp add: exI [of _ k])
qed

lemma cart2_append1_between_strict:
  assumes "z_non_zero p" and "z_non_zero q" and "z_non_zero r"
  and "B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)" and "q \<noteq> p" and "q \<noteq> r"
  shows "\<exists> k>0. k < 1
  \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
proof -
  from \<open>z_non_zero p\<close> and \<open>z_non_zero q\<close> and \<open>z_non_zero r\<close>
    and \<open>B\<^sub>\<real> (cart2_pt p) (cart2_pt q) (cart2_pt r)\<close> and \<open>q \<noteq> r\<close>
    and cart2_append1_between_right_strict [of p q r]
  obtain k where "k \<ge> 0" and "k < 1"
    and "cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
    by auto

  have "k \<noteq> 0"
  proof
    assume "k = 0"
    with \<open>cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p\<close>
    have "cart2_append1 q = cart2_append1 p" by simp
    with \<open>z_non_zero q\<close> have "q = p" by (rule cart2_append1_inj)
    with \<open>q \<noteq> p\<close> show False ..
  qed
  with \<open>k \<ge> 0\<close> have "k > 0" by simp
  with \<open>k < 1\<close>
    and \<open>cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p\<close>
  show "\<exists> k>0. k < 1
    \<and> cart2_append1 q = k *\<^sub>R cart2_append1 r + (1 - k) *\<^sub>R cart2_append1 p"
    by (simp add: exI [of _ k])
qed

end
