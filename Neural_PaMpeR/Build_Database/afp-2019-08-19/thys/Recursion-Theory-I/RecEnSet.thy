(*  Title:       Computably enumerable sets of natural numbers
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Computably enumerable sets of natural numbers\<close>

theory RecEnSet
imports PRecList PRecFun2 PRecFinSet PRecUnGr
begin

subsection \<open>Basic definitions\<close>

definition
  fn_to_set :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "fn_to_set f = { x. \<exists> y. f x y = 0 }"

definition
  ce_sets :: "(nat set) set" where
  "ce_sets = { (fn_to_set p) | p. p \<in> PrimRec2 }"

subsection \<open>Basic properties of computably enumerable sets\<close>

lemma ce_set_lm_1: "p \<in> PrimRec2 \<Longrightarrow> fn_to_set p \<in> ce_sets" by (auto simp add: ce_sets_def)

lemma ce_set_lm_2: "\<lbrakk> p \<in> PrimRec2; \<forall> x. (x \<in> A) = (\<exists> y. p x y = 0)\<rbrakk> \<Longrightarrow> A \<in> ce_sets"
proof -
  assume p_is_pr: "p \<in> PrimRec2"
  assume "\<forall> x. (x \<in> A) = (\<exists> y. p x y = 0)"
  then have "A = fn_to_set p" by (unfold fn_to_set_def, auto)
  with p_is_pr show "A \<in> ce_sets" by (simp add: ce_set_lm_1)
qed

lemma ce_set_lm_3: "A \<in> ce_sets \<Longrightarrow> \<exists> p \<in> PrimRec2. A = fn_to_set p"
proof -
  assume "A \<in> ce_sets"
  then have "A \<in> { (fn_to_set p) | p. p \<in> PrimRec2 }" by (simp add: ce_sets_def)
  thus ?thesis by auto
qed

lemma ce_set_lm_4: "A \<in> ce_sets \<Longrightarrow> \<exists> p \<in> PrimRec2. \<forall> x. (x \<in> A) = (\<exists> y. p x y = 0)"
proof -
  assume "A \<in> ce_sets"
  then have "\<exists> p \<in> PrimRec2. A = fn_to_set p" by (rule ce_set_lm_3)
  then obtain p where p_is_pr: "p \<in> PrimRec2" and L1: "A = fn_to_set p" ..
  from p_is_pr L1 show ?thesis by (unfold fn_to_set_def, auto)
qed

lemma ce_set_lm_5: "\<lbrakk> A \<in> ce_sets; p \<in> PrimRec1 \<rbrakk> \<Longrightarrow> { x . p x \<in> A } \<in> ce_sets"
proof -
  assume A1: "A \<in> ce_sets"
  assume A2: "p \<in> PrimRec1"
  from A1 have "\<exists> pA \<in> PrimRec2. A = fn_to_set pA" by (rule ce_set_lm_3)
  then obtain pA where pA_is_pr: "pA \<in> PrimRec2" and S1: "A = fn_to_set pA" ..
  from S1 have S2: "A = { x . \<exists> y. pA x y = 0 }" by (simp add: fn_to_set_def)
  define q where "q x y = pA (p x) y" for x y
  from pA_is_pr A2 have q_is_pr: "q \<in> PrimRec2" unfolding q_def by prec
  have "\<And> x. (p x \<in> A) = (\<exists> y. q x y = 0)"
  proof -
    fix x show "(p x \<in> A) = (\<exists> y. q x y = 0)"
    proof
      assume A: "p x \<in> A"
      with S2 obtain y where L1: "pA (p x) y = 0" by auto
      then have "q x y = 0" by (simp add: q_def)
      thus "\<exists> y. q x y = 0" ..
    next
      assume A: "\<exists>y. q x y = 0"
      then obtain y where L1: "q x y = 0" ..
      then have "pA (p x) y = 0" by (simp add: q_def)
      with S2 show "p x \<in> A" by auto
    qed
  qed
  then have "{ x . p x \<in> A } = { x. \<exists> y. q x y = 0 }" by auto
  then have "{ x . p x \<in> A } = fn_to_set q" by (simp add: fn_to_set_def)
  moreover from q_is_pr have "fn_to_set q \<in> ce_sets" by (rule ce_set_lm_1)
  ultimately show ?thesis by auto
qed

lemma ce_set_lm_6: "\<lbrakk> A \<in> ce_sets; A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists> q \<in> PrimRec1. A = { q x | x. x \<in> UNIV }"
proof -
  assume A1: "A \<in> ce_sets"
  assume A2: "A \<noteq> {}"
  from A1 have "\<exists> pA \<in> PrimRec2. A = fn_to_set pA" by (rule ce_set_lm_3)
  then obtain pA where pA_is_pr: "pA \<in> PrimRec2" and S1: "A = fn_to_set pA" ..
  from S1 have S2: "A = { x. \<exists> y. pA x y = 0 }" by (simp add: fn_to_set_def)
  from A2 obtain a where a_in: "a \<in> A" by auto
  define q where "q z = (if pA (c_fst z) (c_snd z) = 0 then c_fst z else a)" for z
  from pA_is_pr have q_is_pr: "q \<in> PrimRec1" unfolding q_def by prec
  have S3: "\<forall> z. q z \<in> A"
  proof
    fix z show "q z \<in> A"
    proof cases
      assume A: "pA (c_fst z) (c_snd z) = 0"
      with S2 have "c_fst z \<in> A" by auto
      moreover from A q_def have "q z = c_fst z" by simp
      ultimately show "q z \<in> A" by auto
    next
      assume A: "pA (c_fst z) (c_snd z) \<noteq> 0"
      with q_def have "q z = a" by simp
      with a_in show "q z \<in> A" by auto
    qed
  qed
  then have S4: "{ q x | x. x \<in> UNIV } \<subseteq> A" by auto
  have S5: "A \<subseteq> { q x | x. x \<in> UNIV }"
  proof
    fix x assume A: "x \<in> A" show "x \<in> {q x |x. x \<in> UNIV}"
    proof
      from A S2 obtain y where L1: "pA x y = 0" by auto
      let ?z = "c_pair x y"
      from L1 have "q ?z = x" by (simp add: q_def)
      then have "\<exists> u. q u = x" by blast
      then show "\<exists>u. x = q u \<and> u \<in> UNIV" by auto
    qed
  qed
  from S4 S5 have S6: "A = { q x | x. x \<in> UNIV }" by auto
  with q_is_pr show ?thesis by blast
qed

lemma ce_set_lm_7: "\<lbrakk> A \<in> ce_sets; p \<in> PrimRec1\<rbrakk> \<Longrightarrow> { p x | x. x \<in> A } \<in> ce_sets"
proof -
  assume A1: "A \<in> ce_sets"
  assume A2: "p \<in> PrimRec1"
  let ?B = "{ p x | x. x \<in> A }"
  fix y have S1: "(y \<in> ?B) = (\<exists> x. x \<in> A \<and> (y = p x))" by auto
  from A1 have "\<exists> pA \<in> PrimRec2. A = fn_to_set pA" by (rule ce_set_lm_3)
  then obtain pA where pA_is_pr: "pA \<in> PrimRec2" and S2: "A = fn_to_set pA" ..
  from S2 have S3: "A = { x. \<exists> y. pA x y = 0 }" by (simp add: fn_to_set_def)
  define q where "q y t = (if y = p (c_snd t) then pA (c_snd t) (c_fst t) else 1)" for y t
  from pA_is_pr A2 have q_is_pr: "q \<in> PrimRec2" unfolding q_def by prec
  have L1: "\<And> y. (y \<in> ?B) = (\<exists> z. q y z = 0)"
  proof - fix y show "(y \<in> ?B) = (\<exists> z. q y z = 0)"
  proof
    assume AA1: "y \<in> ?B"
    then obtain x0 where LL_2: "x0 \<in> A" and LL_3: "y = p x0" by auto
    from S3 have LL_4: "(x0 \<in> A) = (\<exists> z. pA x0 z = 0)" by auto
    from LL_2 LL_4 obtain z0 where LL_5: "pA x0 z0 = 0" by auto
    define t where "t = c_pair z0 x0"
    from t_def q_def LL_3 LL_5 have "q y t = 0" by simp
    then show "\<exists> z. q y z = 0" by auto
  next
    assume A1: "\<exists> z. q y z = 0"
    then obtain z0 where LL_1: "q y z0 = 0" ..
    have LL2: "y = p (c_snd z0)"
    proof (rule ccontr)
      assume "y \<noteq> p (c_snd z0)"
      with q_def LL_1 have "q y z0 = 1" by auto
      with LL_1 show False by auto
    qed
    from LL2 LL_1 q_def have LL3: "pA (c_snd z0) (c_fst z0) = 0" by auto
    with S3 have LL4: "c_snd z0 \<in> A" by auto
    with LL2 show "y \<in> {p x | x. x \<in> A}" by auto
  qed
  qed
  then have L2: "?B = { y | y. \<exists> z. q y z = 0}" by auto
  with fn_to_set_def have "?B = fn_to_set q" by auto
  with q_is_pr ce_set_lm_1 show ?thesis by auto
qed

theorem ce_empty: "{} \<in> ce_sets"
proof -
  let ?f = "(\<lambda> x a. (1::nat))"
  have S1: "?f \<in> PrimRec2" by (rule const_is_pr_2)
  then have "\<forall> x a. ?f x a \<noteq> 0" by simp
  then have "{x. \<exists> a. ?f x a = 0 }={}" by auto
  also have "fn_to_set ?f = \<dots>" by (simp add: fn_to_set_def)
  with S1 show ?thesis by (auto simp add: ce_sets_def)
qed

theorem ce_univ: "UNIV \<in> ce_sets"
proof -
  let ?f = "(\<lambda> x a. (0::nat))"
  have S1: "?f \<in> PrimRec2" by (rule const_is_pr_2)
  then have "\<forall> x a. ?f x a = 0" by simp
  then have "{x. \<exists> a. ?f x a = 0 }=UNIV" by auto
  also have "fn_to_set ?f = \<dots>" by (simp add: fn_to_set_def)
  with S1 show ?thesis by (auto simp add: ce_sets_def)
qed

theorem ce_singleton: "{a} \<in> ce_sets"
proof -
  let ?f = "\<lambda> x y. (abs_of_diff x a) + y"
  have S1: "?f \<in> PrimRec2" using const_is_pr_2 [where ?n="a"] by prec
  then have "\<forall> x y. (?f x y = 0) = (x=a \<and> y=0)" by (simp add: abs_of_diff_eq)
  then have S2: "{x. \<exists> y. ?f x y = 0 }={a}" by auto
  have "fn_to_set ?f = {x. \<exists> y. ?f x y = 0 }" by (simp add: fn_to_set_def)
  with S2 have "fn_to_set ?f = {a}" by simp
  with S1 show ?thesis by (auto simp add: ce_sets_def)
qed

theorem ce_union: "\<lbrakk> A \<in> ce_sets; B \<in> ce_sets \<rbrakk> \<Longrightarrow> A \<union> B \<in> ce_sets"
proof -
  assume A1: "A \<in> ce_sets"
  then obtain p_a where S2: "p_a \<in> PrimRec2" and S3: "A = fn_to_set p_a"
    by (auto simp add: ce_sets_def)
  assume A2: "B \<in> ce_sets"
  then obtain p_b where S5: "p_b \<in> PrimRec2" and S6: "B = fn_to_set p_b"
    by (auto simp add: ce_sets_def)
  let ?p = "(\<lambda> x y. (p_a x y) * (p_b x y))"
  from S2 S5 have S7: "?p \<in> PrimRec2" by prec
  have S8: "\<forall> x y. (?p x y = 0) = ((p_a x y = 0) \<or> (p_b x y = 0))" by simp
  let ?C = "fn_to_set ?p"
  have S9: "?C = {x. \<exists> y. ?p x y = 0}" by (simp add: fn_to_set_def)
  from S3 have S10: "A = {x. \<exists> y. p_a x y = 0}" by (simp add: fn_to_set_def)
  from S6 have S11: "B = {x. \<exists> y. p_b x y = 0}" by (simp add: fn_to_set_def)
  from S10 S11 S9 S8 have S12: "?C = A \<union> B" by auto
  from S7 have "?C \<in> ce_sets" by (auto simp add: ce_sets_def)
  with S12 show ?thesis by simp
qed

theorem ce_intersect: "\<lbrakk> A \<in> ce_sets; B \<in> ce_sets \<rbrakk> \<Longrightarrow> A \<inter> B \<in> ce_sets"
proof -
  assume A1: "A \<in> ce_sets"
  then obtain p_a where S2: "p_a \<in> PrimRec2" and S3: "A = fn_to_set p_a"
    by (auto simp add: ce_sets_def)
  assume A2: "B \<in> ce_sets"
  then obtain p_b where S5: "p_b \<in> PrimRec2" and S6: "B = fn_to_set p_b"
    by (auto simp add: ce_sets_def)
  let ?p = "(\<lambda> x y. (p_a x (c_fst y)) + (p_b x (c_snd y)))"
  from S2 S5 have S7: "?p \<in> PrimRec2" by prec
  have S8: "\<forall> x. (\<exists> y. ?p x y = 0) = ((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0))"
  proof
    fix x show "(\<exists> y. ?p x y = 0) = ((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0))"
    proof -
    have 1: "(\<exists> y. ?p x y = 0) \<Longrightarrow> ((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0))"
    by blast
    have 2: "((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0)) \<Longrightarrow> (\<exists> y. ?p x y = 0)"
    proof -
      assume "((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0))"
      then obtain z1 z2 where s_23: "p_a x z1 = 0" and s_24: "p_b x z2 = 0" by auto
      let ?y1 = "c_pair z1 z2"
      from s_23 have s_25: "p_a x (c_fst ?y1) = 0" by simp
      from s_24 have s_26: "p_b x (c_snd ?y1) = 0" by simp
      from s_25 s_26 have s_27: "p_a x (c_fst ?y1) + p_b x (c_snd ?y1) = 0" by simp
      then show ?thesis ..
    qed
    from 1 2 have "(\<exists> y. ?p x y = 0) = ((\<exists> z. p_a x z = 0) \<and> (\<exists> z. p_b x z = 0))" by (rule iffI)
    then show ?thesis by auto
    qed
  qed
  let ?C = "fn_to_set ?p"
  have S9: "?C = {x. \<exists> y. ?p x y = 0}" by (simp add: fn_to_set_def)
  from S3 have S10: "A = {x. \<exists> y. p_a x y = 0}" by (simp add: fn_to_set_def)
  from S6 have S11: "B = {x. \<exists> y. p_b x y = 0}" by (simp add: fn_to_set_def)
  from S10 S11 S9 S8 have S12: "?C = A \<inter> B" by auto
  from S7 have "?C \<in> ce_sets" by (auto simp add: ce_sets_def)
  with S12 show ?thesis by simp
qed

subsection \<open>Enumeration of computably enumerable sets\<close>

definition
  nat_to_ce_set :: "nat \<Rightarrow> (nat set)" where
  "nat_to_ce_set = (\<lambda> n. fn_to_set (pr_conv_1_to_2 (nat_to_pr n)))"

lemma nat_to_ce_set_lm_1: "nat_to_ce_set n = { x . \<exists> y. (nat_to_pr n) (c_pair x y) = 0 }"
proof -
  have S1: "nat_to_ce_set n = fn_to_set (pr_conv_1_to_2 (nat_to_pr n))" by (simp add: nat_to_ce_set_def)
  then have S2: "nat_to_ce_set n = { x . \<exists> y. (pr_conv_1_to_2 (nat_to_pr n)) x y = 0}" by (simp add: fn_to_set_def)
  have S3: "\<And> x y. (pr_conv_1_to_2 (nat_to_pr n)) x y = (nat_to_pr n) (c_pair x y)" by (simp add: pr_conv_1_to_2_def)
  from S2 S3 show ?thesis by auto
qed

lemma nat_to_ce_set_into_ce: "nat_to_ce_set n \<in> ce_sets"
proof -
  have S1: "nat_to_ce_set n = fn_to_set (pr_conv_1_to_2 (nat_to_pr n))" by (simp add: nat_to_ce_set_def)
  have "(nat_to_pr n) \<in> PrimRec1" by (rule nat_to_pr_into_pr)
  then have S2: "(pr_conv_1_to_2 (nat_to_pr n)) \<in> PrimRec2" by (rule pr_conv_1_to_2_lm)
  from S2 S1 show ?thesis by (simp add: ce_set_lm_1)
qed

lemma nat_to_ce_set_srj: "A \<in> ce_sets \<Longrightarrow> \<exists> n. A = nat_to_ce_set n"
proof -
  assume A: "A \<in> ce_sets"
  then have "\<exists> p \<in> PrimRec2. A = fn_to_set p" by (rule ce_set_lm_3)
  then obtain p where p_is_pr: "p \<in> PrimRec2" and S1: "A = fn_to_set p" ..
  define q where "q = pr_conv_2_to_1 p"
  from p_is_pr have q_is_pr: "q \<in> PrimRec1" by (unfold q_def, rule pr_conv_2_to_1_lm)
  from q_def have S2: "pr_conv_1_to_2 q = p" by simp
  let ?n = "index_of_pr q"
  from q_is_pr have "nat_to_pr ?n = q" by (rule index_of_pr_is_real)
  with S2 S1 have "A = fn_to_set (pr_conv_1_to_2 (nat_to_pr ?n))" by auto
  then have "A = nat_to_ce_set ?n" by (simp add: nat_to_ce_set_def)
  thus ?thesis ..
qed


subsection \<open>Characteristic functions\<close>

definition
  chf :: "nat set \<Rightarrow> (nat \<Rightarrow> nat)" \<comment> \<open>Characteristic function\<close> where
  "chf = (\<lambda> A x. if x \<in> A then 0 else 1 )"

definition
  zero_set :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "zero_set = (\<lambda> f. { x. f x = 0})"

lemma chf_lm_1 [simp]: "zero_set (chf A) = A" by (unfold chf_def, unfold zero_set_def, simp)

lemma chf_lm_2: "(x \<in> A) = (chf A x = 0)" by (unfold chf_def, simp)

lemma chf_lm_3: "(x \<notin> A) = (chf A x = 1)" by (unfold chf_def, simp)

lemma chf_lm_4: "chf A \<in> PrimRec1 \<Longrightarrow> A \<in> ce_sets"
proof -
  assume A: "chf A \<in> PrimRec1"
  define p where "p = chf A"
  from A p_def have p_is_pr: "p \<in> PrimRec1" by auto
  define q where "q x y = p x" for x y :: nat
  from p_is_pr have q_is_pr: "q \<in> PrimRec2" unfolding q_def by prec
  have S1: "A = {x. p(x) = 0}"
  proof -
    have "zero_set p = A" by (unfold p_def, simp)
    thus ?thesis by (simp add: zero_set_def)
  qed
  have S2: "fn_to_set q = {x. \<exists> y. q x y = 0}" by (simp add: fn_to_set_def)
  have S3: "\<And> x. (p x = 0) = (\<exists> y. q x y = 0)" by (unfold q_def, auto)
  then have S4: "{x. p x = 0} = {x. \<exists> y. q x y = 0}" by auto
  with S1 S2 have S5: "fn_to_set q = A" by auto
  from q_is_pr have "fn_to_set q \<in> ce_sets" by (rule ce_set_lm_1)
  with S5 show ?thesis by auto
qed

lemma chf_lm_5: "finite A \<Longrightarrow> chf A \<in> PrimRec1"
proof -
  assume A: "finite A"
  define u where "u = set_to_nat A"
  from A have S1: "nat_to_set u = A" by (unfold u_def, rule nat_to_set_srj)
  have "chf A = (\<lambda> x. sgn2 (c_in x u))"
  proof
    fix x show "chf A x = sgn2 (c_in x u)"
    proof cases
      assume A: "x \<in> A"
      then have S1_1: "chf A x = 0" by (simp add: chf_lm_2)
      from A S1 have "x \<in> nat_to_set u" by auto
      then have "c_in x u = 1" by (simp add: x_in_u_eq)
      with S1_1 show ?thesis by simp
    next
      assume A: "x \<notin> A"
      then have S1_1: "chf A x = 1" by (simp add: chf_def)
      from A S1 have "x \<notin> nat_to_set u" by auto
      then have "c_in x u = 0" by (simp add: x_in_u_eq c_in_def)
      with S1_1 show ?thesis by simp
    qed
  qed
  moreover from c_in_is_pr have "(\<lambda> x. sgn2 (c_in x u)) \<in> PrimRec1" by prec
  ultimately show ?thesis by auto
qed

theorem ce_finite: "finite A \<Longrightarrow> A \<in> ce_sets"
proof -
  assume A: "finite A"
  then have "chf A \<in> PrimRec1" by (rule chf_lm_5)
  then show ?thesis by (rule chf_lm_4)
qed

subsection \<open>Computably enumerable relations\<close>

definition
  ce_set_to_rel :: "nat set \<Rightarrow> (nat * nat) set" where
  "ce_set_to_rel = (\<lambda> A. { (c_fst x, c_snd x) | x. x \<in> A})"

definition
  ce_rel_to_set :: "(nat * nat) set \<Rightarrow> nat set" where
  "ce_rel_to_set = (\<lambda> R. { c_pair x y | x y. (x,y) \<in> R})"

definition
  ce_rels :: "((nat * nat) set) set" where
  "ce_rels = { R | R. ce_rel_to_set R \<in> ce_sets }"

lemma ce_rel_lm_1 [simp]: "ce_set_to_rel (ce_rel_to_set r) = r"
proof
  show " ce_set_to_rel (ce_rel_to_set r) \<subseteq> r"
  proof fix z
    assume A: "z \<in> ce_set_to_rel (ce_rel_to_set r)"
    then obtain u where L1: "u \<in> (ce_rel_to_set r)" and L2: "z = (c_fst u, c_snd u)"
      unfolding ce_set_to_rel_def by auto
    from L1 obtain x y where L3: "(x,y) \<in> r" and L4: "u = c_pair x y"
      unfolding ce_rel_to_set_def by auto
    from L4 have L5: "c_fst u = x" by simp
    from L4 have L6: "c_snd u = y" by simp
    from L5 L6 L2 have "z = (x,y)" by simp
    with L3 show "z \<in> r" by auto
  qed
next
  show "r \<subseteq> ce_set_to_rel (ce_rel_to_set r)"
  proof fix z show "z \<in> r \<Longrightarrow> z \<in> ce_set_to_rel (ce_rel_to_set r)"
    proof -
      assume A: "z \<in> r"
      define x where "x = fst z"
      define y where "y = snd z"
      from x_def y_def have L1: "z = (x,y)" by simp
      define u where "u = c_pair x y"
      from A L1 u_def have L2: "u \<in> ce_rel_to_set r" by (unfold ce_rel_to_set_def, auto)
      from L1 u_def have L3: "z = (c_fst u, c_snd u)" by simp
      from L2 L3 show "z \<in> ce_set_to_rel (ce_rel_to_set r)" by (unfold ce_set_to_rel_def, auto)
    qed
  qed
qed

lemma ce_rel_lm_2 [simp]: "ce_rel_to_set (ce_set_to_rel A) = A"
proof
  show "ce_rel_to_set (ce_set_to_rel A) \<subseteq> A"
  proof fix z show "z \<in> ce_rel_to_set (ce_set_to_rel A) \<Longrightarrow> z \<in> A"
    proof -
      assume A: "z \<in> ce_rel_to_set (ce_set_to_rel A)"
      then obtain x y where L1: "z = c_pair x y" and L2: "(x,y) \<in> ce_set_to_rel A"
        unfolding ce_rel_to_set_def by auto
      from L2 obtain u where L3: "(x,y) = (c_fst u, c_snd u)" and L4: "u \<in> A"
        unfolding ce_set_to_rel_def by auto
      from L3 L1 have L5: "z = u" by simp
      with L4 show "z \<in> A" by auto
    qed
  qed
next
  show "A \<subseteq> ce_rel_to_set (ce_set_to_rel A)"
  proof fix z show "z \<in> A \<Longrightarrow> z \<in> ce_rel_to_set (ce_set_to_rel A)"
    proof -
      assume A: "z \<in> A"
      then have L1: "(c_fst z, c_snd z) \<in> ce_set_to_rel A" by (unfold ce_set_to_rel_def, auto)
      define x where "x = c_fst z"
      define y where "y = c_snd z"
      from L1 x_def y_def have L2: "(x,y) \<in> ce_set_to_rel A" by simp
      then have L3: "c_pair x y \<in> ce_rel_to_set (ce_set_to_rel A)" by (unfold ce_rel_to_set_def, auto)
      with x_def y_def show "z \<in> ce_rel_to_set (ce_set_to_rel A)" by simp
    qed
  qed
qed

lemma ce_rels_def1: "ce_rels = { ce_set_to_rel A | A. A \<in> ce_sets}"
proof
  show "ce_rels \<subseteq> {ce_set_to_rel A |A. A \<in> ce_sets}"
  proof fix r show " r \<in> ce_rels \<Longrightarrow> r \<in> {ce_set_to_rel A |A. A \<in> ce_sets}"
    proof -
      assume A: "r \<in> ce_rels"
      then have L1: "ce_rel_to_set r \<in> ce_sets" by (unfold ce_rels_def, auto)
      define A where "A = ce_rel_to_set r"
      from A_def L1 have L2: "A \<in> ce_sets" by auto
      from A_def have L3: "ce_set_to_rel A = r" by simp
      with L2 show "r \<in> {ce_set_to_rel A |A. A \<in> ce_sets}" by auto
    qed
  qed
next
  show "{ce_set_to_rel A |A. A \<in> ce_sets} \<subseteq> ce_rels"
  proof fix r show "r \<in> {ce_set_to_rel A |A. A \<in> ce_sets} \<Longrightarrow> r \<in> ce_rels"
    proof -
      assume A: "r \<in> {ce_set_to_rel A |A. A \<in> ce_sets}"
      then obtain A where L1: "r = ce_set_to_rel A" and L2: "A \<in> ce_sets" by auto
      from L1 have "ce_rel_to_set r = A" by simp
      with L2 show "r \<in> ce_rels" unfolding ce_rels_def by auto
    qed
  qed
qed

lemma ce_rel_to_set_inj: "inj ce_rel_to_set"
proof (rule inj_on_inverseI)
  fix x assume A: "(x::(nat\<times>nat) set) \<in> UNIV" show "ce_set_to_rel (ce_rel_to_set x) = x" by (rule ce_rel_lm_1)
qed

lemma ce_rel_to_set_srj: "surj ce_rel_to_set"
proof (rule surjI [where ?f=ce_set_to_rel])
  fix x show "ce_rel_to_set (ce_set_to_rel x) = x" by (rule ce_rel_lm_2)
qed

lemma ce_rel_to_set_bij: "bij ce_rel_to_set"
proof (rule bijI)
  show "inj ce_rel_to_set" by (rule ce_rel_to_set_inj)
next
  show "surj ce_rel_to_set" by (rule ce_rel_to_set_srj)
qed

lemma ce_set_to_rel_inj: "inj ce_set_to_rel"
proof (rule inj_on_inverseI)
  fix x assume A: "(x::nat set) \<in> UNIV" show "ce_rel_to_set (ce_set_to_rel x) = x" by (rule ce_rel_lm_2)
qed

lemma ce_set_to_rel_srj: "surj ce_set_to_rel"
proof (rule surjI [where ?f=ce_rel_to_set])
  fix x show "ce_set_to_rel (ce_rel_to_set x) = x" by (rule ce_rel_lm_1)
qed

lemma ce_set_to_rel_bij: "bij ce_set_to_rel"
proof (rule bijI)
  show "inj ce_set_to_rel" by (rule ce_set_to_rel_inj)
next
  show "surj ce_set_to_rel" by (rule ce_set_to_rel_srj)
qed

lemma ce_rel_lm_3: "A \<in> ce_sets \<Longrightarrow> ce_set_to_rel A \<in> ce_rels"
proof -
  assume A: "A \<in> ce_sets"
  from A ce_rels_def1 show ?thesis by auto
qed

lemma ce_rel_lm_4: "ce_set_to_rel A \<in> ce_rels \<Longrightarrow> A \<in> ce_sets"
proof -
  assume A: "ce_set_to_rel A \<in> ce_rels"
  from A show ?thesis by (unfold ce_rels_def, auto)
qed

lemma ce_rel_lm_5: "(A \<in> ce_sets) = (ce_set_to_rel A \<in> ce_rels)"
proof
  assume "A \<in> ce_sets" then show "ce_set_to_rel A \<in> ce_rels" by (rule ce_rel_lm_3)
next
  assume "ce_set_to_rel A \<in> ce_rels" then show "A \<in> ce_sets" by (rule ce_rel_lm_4)
qed

lemma ce_rel_lm_6: "r \<in> ce_rels \<Longrightarrow> ce_rel_to_set r \<in> ce_sets"
proof -
  assume A: "r \<in> ce_rels"
  then show ?thesis by (unfold ce_rels_def, auto)
qed

lemma ce_rel_lm_7: "ce_rel_to_set r \<in> ce_sets \<Longrightarrow> r \<in> ce_rels"
proof -
  assume "ce_rel_to_set r \<in> ce_sets"
  then show ?thesis by (unfold ce_rels_def, auto)
qed

lemma ce_rel_lm_8: "(r \<in> ce_rels) = (ce_rel_to_set r \<in> ce_sets)" by (unfold ce_rels_def, auto)

lemma ce_rel_lm_9: "(x,y) \<in> r \<Longrightarrow> c_pair x y \<in> ce_rel_to_set r" by (unfold ce_rel_to_set_def, auto)

lemma ce_rel_lm_10: "x \<in> A \<Longrightarrow> (c_fst x, c_snd x) \<in> ce_set_to_rel A" by (unfold ce_set_to_rel_def, auto)

lemma ce_rel_lm_11: "c_pair x y \<in> ce_rel_to_set r \<Longrightarrow> (x,y) \<in> r"
proof -
  assume A: "c_pair x y \<in> ce_rel_to_set r"
  let ?z = "c_pair x y"
  from A have "(c_fst ?z, c_snd ?z) \<in> ce_set_to_rel (ce_rel_to_set r)" by (rule ce_rel_lm_10)
  then show "(x,y) \<in> r" by simp
qed

lemma ce_rel_lm_12: "(c_pair x y \<in> ce_rel_to_set r) = ((x,y) \<in> r)"
proof
  assume "c_pair x y \<in> ce_rel_to_set r" then show "(x, y) \<in> r" by (rule ce_rel_lm_11)
next
  assume "(x, y) \<in> r" then show "c_pair x y \<in> ce_rel_to_set r" by (rule ce_rel_lm_9)
qed

lemma ce_rel_lm_13: "(x,y) \<in> ce_set_to_rel A \<Longrightarrow> c_pair x y \<in> A"
proof -
  assume "(x,y) \<in> ce_set_to_rel A"
  then have "c_pair x y \<in> ce_rel_to_set (ce_set_to_rel A)" by (rule ce_rel_lm_9)
  then show ?thesis by simp
qed

lemma ce_rel_lm_14: "c_pair x y \<in> A \<Longrightarrow> (x,y) \<in> ce_set_to_rel A"
proof -
  assume "c_pair x y \<in> A"
  then have "c_pair x y \<in> ce_rel_to_set (ce_set_to_rel A)" by simp
  then show ?thesis by (rule ce_rel_lm_11)
qed

lemma ce_rel_lm_15: "((x,y) \<in> ce_set_to_rel A) = (c_pair x y \<in> A)"
proof
  assume "(x, y) \<in> ce_set_to_rel A" then show "c_pair x y \<in> A" by (rule ce_rel_lm_13)
next
  assume "c_pair x y \<in> A" then show "(x, y) \<in> ce_set_to_rel A" by (rule ce_rel_lm_14)
qed

lemma ce_rel_lm_16: "x \<in> ce_rel_to_set r \<Longrightarrow> (c_fst x, c_snd x) \<in> r"
proof -
  assume "x \<in> ce_rel_to_set r"
  then have "(c_fst x, c_snd x) \<in> ce_set_to_rel (ce_rel_to_set r)" by (rule ce_rel_lm_10)
  then show ?thesis by simp
qed

lemma ce_rel_lm_17: "(c_fst x, c_snd x) \<in> ce_set_to_rel A \<Longrightarrow> x \<in> A"
proof -
  assume "(c_fst x, c_snd x) \<in> ce_set_to_rel A"
  then have "c_pair (c_fst x) (c_snd x) \<in> A" by (rule ce_rel_lm_13)
  then show ?thesis by simp
qed

lemma ce_rel_lm_18: "((c_fst x, c_snd x) \<in> ce_set_to_rel A) = (x \<in> A)"
proof
  assume "(c_fst x, c_snd x) \<in> ce_set_to_rel A" then show "x \<in> A" by (rule ce_rel_lm_17)
next
  assume "x \<in> A" then show "(c_fst x, c_snd x) \<in> ce_set_to_rel A" by (rule ce_rel_lm_10)
qed

lemma ce_rel_lm_19: "(c_fst x, c_snd x) \<in> r \<Longrightarrow> x \<in> ce_rel_to_set r"
proof -
  assume "(c_fst x, c_snd x) \<in> r"
  then have "(c_fst x, c_snd x) \<in> ce_set_to_rel (ce_rel_to_set r)" by simp
  then show ?thesis by (rule ce_rel_lm_17)
qed

lemma ce_rel_lm_20: "((c_fst x, c_snd x) \<in> r) = (x \<in> ce_rel_to_set r)"
proof
  assume "(c_fst x, c_snd x) \<in> r" then show "x \<in> ce_rel_to_set r" by (rule ce_rel_lm_19)
next
  assume "x \<in> ce_rel_to_set r" then show "(c_fst x, c_snd x) \<in> r" by (rule ce_rel_lm_16)
qed

lemma ce_rel_lm_21: "r \<in> ce_rels \<Longrightarrow> \<exists> p \<in> PrimRec3. \<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)"
proof -
  assume r_ce: "r \<in> ce_rels"
  define A where "A = ce_rel_to_set r"
  from r_ce have A_ce: "A \<in> ce_sets" by (unfold A_def, rule ce_rel_lm_6)
  then have "\<exists> p \<in> PrimRec2. A = fn_to_set p" by (rule ce_set_lm_3)
  then obtain q where q_is_pr: "q \<in> PrimRec2" and A_def1: "A = fn_to_set q" ..
  from A_def1 have A_def2: "A = { x. \<exists> y. q x y = 0}" by (unfold fn_to_set_def)
  define p where "p x y u = q (c_pair x y) u" for x y u
  from q_is_pr have p_is_pr: "p \<in> PrimRec3" unfolding p_def by prec
  have "\<And> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)"
  proof - fix x y show "((x,y) \<in> r) = (\<exists> u. p x y u = 0)"
    proof
      assume A: "(x,y) \<in> r"
      define z where "z = c_pair x y"
      with A_def A have z_in_A: "z \<in> A" by (unfold ce_rel_to_set_def, auto)
      with A_def2 have "z \<in> { x. \<exists> y. q x y = 0}" by auto
      then obtain u where "q z u = 0" by auto
      with z_def have "p x y u = 0" by (simp add: z_def p_def)
      then show "\<exists> u. p x y u = 0" by auto
    next
      assume A: "\<exists> u. p x y u = 0"
      define z where "z = c_pair x y"
      from A obtain u where "p x y u = 0" by auto
      then have q_z: "q z u = 0" by (simp add: z_def p_def)
      with A_def2 have z_in_A: "z \<in> A" by auto
      then have "c_pair x y \<in> A" by (unfold z_def)
      then have "c_pair x y \<in> ce_rel_to_set r" by (unfold A_def)
      then show "(x,y) \<in> r" by (rule ce_rel_lm_11)
    qed
  qed
  with p_is_pr show ?thesis by auto
qed

lemma ce_rel_lm_22: "r \<in> ce_rels \<Longrightarrow> \<exists> p \<in> PrimRec3. r = { (x,y). \<exists> u. p x y u = 0 }"
proof -
  assume r_ce: "r \<in> ce_rels"
  then have "\<exists> p \<in> PrimRec3. \<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)" by (rule ce_rel_lm_21)
  then obtain p where p_is_pr: "p \<in> PrimRec3" and L1: "\<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)" by auto
  from p_is_pr L1 show ?thesis by blast
qed

lemma ce_rel_lm_23: "\<lbrakk> p \<in> PrimRec3; \<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0) \<rbrakk> \<Longrightarrow> r \<in> ce_rels"
proof -
  assume p_is_pr: "p \<in> PrimRec3"
  assume A: "\<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)"
  define q where "q z u = p (c_fst z) (c_snd z) u" for z u
  from p_is_pr have q_is_pr: "q \<in> PrimRec2" unfolding q_def by prec
  define A where "A = { x. \<exists> y. q x y = 0}"
  then have A_def1: "A = fn_to_set q" by (unfold fn_to_set_def, auto)
  from q_is_pr A_def1 have A_ce: "A \<in> ce_sets" by (simp add: ce_set_lm_1)
  have main: "A = ce_rel_to_set r"
  proof
    show "A \<subseteq> ce_rel_to_set r"
    proof
      fix z assume z_in_A: "z \<in> A"
      show "z \<in> ce_rel_to_set r"
      proof -
        define x where "x = c_fst z"
        define y where "y = c_snd z"
        from z_in_A A_def obtain u where L2: "q z u = 0" by auto
        with x_def y_def q_def have L3: "p x y u = 0" by simp
        then have "\<exists>u. p x y u = 0" by auto
        with A have "(x,y) \<in> r" by auto
        then have "c_pair x y \<in> ce_rel_to_set r" by (rule ce_rel_lm_9)
        with x_def y_def show ?thesis by simp
      qed
    qed
  next
    show "ce_rel_to_set r \<subseteq> A"
    proof
      fix z assume z_in_r: "z \<in> ce_rel_to_set r"
      show "z \<in> A"
      proof -
        define x where "x = c_fst z"
        define y where "y = c_snd z"
        from z_in_r have "(c_fst z, c_snd z) \<in> r" by (rule ce_rel_lm_16)
        with x_def y_def have "(x,y) \<in> r" by simp
        with A obtain u where L1: "p x y u = 0" by auto
        with x_def y_def q_def have "q z u = 0" by simp
        with A_def show "z \<in> A" by auto
      qed
    qed
  qed
  with A_ce have "ce_rel_to_set r \<in> ce_sets" by auto
  then show "r \<in> ce_rels" by (rule ce_rel_lm_7)
qed

lemma ce_rel_lm_24: "\<lbrakk> r \<in> ce_rels; s \<in> ce_rels \<rbrakk> \<Longrightarrow> s O r \<in> ce_rels"
proof -
  assume r_ce: "r \<in> ce_rels"
  assume s_ce: "s \<in> ce_rels"
  from r_ce have "\<exists> p \<in> PrimRec3. \<forall> x y. ((x,y) \<in> r)=(\<exists> u. p x y u = 0)" by (rule ce_rel_lm_21)
  then obtain p_r where p_r_is_pr: "p_r \<in> PrimRec3" and R1: "\<forall> x y. ((x,y) \<in> r)=(\<exists> u. p_r x y u = 0)"
    by auto
  from s_ce have "\<exists> p \<in> PrimRec3. \<forall> x y. ((x,y) \<in> s)=(\<exists> u. p x y u = 0)" by (rule ce_rel_lm_21)
  then obtain p_s where p_s_is_pr: "p_s \<in> PrimRec3" and S1: "\<forall> x y. ((x,y) \<in> s)=(\<exists> u. p_s x y u = 0)"
    by auto
  define p where "p x z u = (p_s x (c_fst u) (c_fst (c_snd u))) + (p_r (c_fst u) z (c_snd (c_snd u)))"
    for x z u
  from p_r_is_pr p_s_is_pr have p_is_pr: "p \<in> PrimRec3" unfolding p_def by prec
  define sr where "sr = s O r"
  have main: "\<forall> x z. ((x,z) \<in> sr) = (\<exists> u. p x z u = 0)"
  proof (rule allI, rule allI)
    fix x z
    show "((x, z) \<in> sr) = (\<exists>u. p x z u = 0)"
    proof
      assume A: "(x, z) \<in> sr"
      show "\<exists>u. p x z u = 0"
      proof -
        from A sr_def obtain y where L1: "(x,y) \<in> s" and L2: "(y,z) \<in> r" by auto
        from L1 S1 obtain u_s where L3: "p_s x y u_s = 0" by auto
        from L2 R1 obtain u_r where L4: "p_r y z u_r = 0" by auto
        define u where "u = c_pair y (c_pair u_s u_r)"
        from L3 L4 have "p x z u = 0" by (unfold p_def, unfold u_def, simp)
        then show ?thesis by auto
      qed
    next
      assume A: "\<exists>u. p x z u = 0"
      show "(x, z) \<in> sr"
      proof -
        from A obtain u where L1: "p x z u = 0" by auto
        then have L2: "(p_s x (c_fst u) (c_fst (c_snd u))) + (p_r (c_fst u) z (c_snd (c_snd u))) = 0" by (unfold p_def)
        from L2 have L3: "p_s x (c_fst u) (c_fst (c_snd u)) = 0" by auto
        from L2 have L4: "p_r (c_fst u) z (c_snd (c_snd u)) = 0" by auto
        from L3 S1 have L5: "(x,(c_fst u)) \<in> s" by auto
        from L4 R1 have L6: "((c_fst u),z) \<in> r" by auto
        from L5 L6 have "(x,z) \<in> s O r" by auto
        with sr_def show ?thesis by auto
      qed
    qed
  qed
  from p_is_pr main have "sr \<in> ce_rels" by (rule ce_rel_lm_23)
  then show ?thesis by (unfold sr_def)
qed

lemma ce_rel_lm_25: "r \<in> ce_rels \<Longrightarrow> r^-1 \<in> ce_rels"
proof -
  assume r_ce: "r \<in> ce_rels"
  have "r^-1 = {(y,x). (x,y) \<in> r}" by auto
  then have L1: "\<forall> x y. ((x,y) \<in> r) = ((y,x) \<in> r^-1)" by auto
  from r_ce have "\<exists> p \<in> PrimRec3. \<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)" by (rule ce_rel_lm_21)
  then obtain p where p_is_pr: "p \<in> PrimRec3" and R1: "\<forall> x y. ((x,y) \<in> r) = (\<exists> u. p x y u = 0)" by auto
  define q where "q x y u = p y x u" for x y u
  from p_is_pr have q_is_pr: "q \<in> PrimRec3" unfolding q_def by prec
  from L1 R1 have L2: "\<forall> x y. ((x,y) \<in> r^-1) = (\<exists> u. p y x u = 0)" by auto
  with q_def have L3: "\<forall> x y. ((x,y) \<in> r^-1) = (\<exists> u. q x y u = 0)" by auto
  with q_is_pr show ?thesis by (rule ce_rel_lm_23)
qed

lemma ce_rel_lm_26: "r \<in> ce_rels \<Longrightarrow> Domain r \<in> ce_sets"
proof -
  assume r_ce: "r \<in> ce_rels"
  have L1: "\<forall> x. (x \<in> Domain r) = (\<exists> y. (x,y) \<in> r)" by auto
  define A where "A = ce_rel_to_set r"
  from r_ce have "ce_rel_to_set r \<in> ce_sets" by (rule ce_rel_lm_6)
  then have A_ce: "A \<in> ce_sets" by (unfold A_def)
  have "\<forall> x y. ((x,y) \<in> r) = (c_pair x y \<in> ce_rel_to_set r)" by (simp add: ce_rel_lm_12)
  then have L2: "\<forall> x y. ((x,y) \<in> r) = (c_pair x y \<in> A)" by (unfold A_def)
  from A_ce c_fst_is_pr have L3: "{ c_fst z |z.  z \<in> A } \<in> ce_sets" by (rule ce_set_lm_7)
  have L4: "\<forall> x. (x \<in> { c_fst z |z.  z \<in> A }) =(\<exists> y. c_pair x y \<in> A)"
  proof fix x show "(x \<in> { c_fst z |z.  z \<in> A }) =(\<exists> y. c_pair x y \<in> A)"
    proof
      assume A: "x \<in> {c_fst z |z. z \<in> A}"
      then obtain z where z_in_A: "z \<in> A" and x_z: "x = c_fst z" by auto
      from x_z have "z = c_pair x (c_snd z)" by simp
      with z_in_A have "c_pair x (c_snd z) \<in> A" by auto
      then show "\<exists>y. c_pair x y \<in> A" by auto
    next
      assume A: "\<exists>y. c_pair x y \<in> A"
      then obtain y where y_1: "c_pair x y \<in> A" by auto
      define z where "z = c_pair x y"
      from y_1 have z_in_A: "z \<in> A" by (unfold z_def)
      from z_def have x_z: "x = c_fst z" by (unfold z_def, simp)
      from z_in_A x_z show "x \<in> {c_fst z |z. z \<in> A}" by auto
    qed
  qed
  from L1 L2 have L5: "\<forall> x. (x \<in> Domain r) = (\<exists> y. c_pair x y \<in> A)" by auto
  from L4 L5 have L6: "\<forall> x. (x \<in> Domain r) = (x \<in> { c_fst z |z.  z \<in> A })" by auto
  then have "Domain r = { c_fst z |z.  z \<in> A }" by auto  
  with L3 show "Domain r \<in> ce_sets" by auto
qed

lemma ce_rel_lm_27: "r \<in> ce_rels \<Longrightarrow> Range r \<in> ce_sets"
proof -
  assume r_ce: "r \<in> ce_rels"
  then have "r^-1 \<in> ce_rels" by (rule ce_rel_lm_25)
  then have "Domain (r^-1) \<in> ce_sets" by (rule ce_rel_lm_26)
  then show ?thesis by (unfold Domain_converse [symmetric])
qed

lemma ce_rel_lm_28: "r \<in> ce_rels \<Longrightarrow> Field r \<in> ce_sets"
proof -
  assume r_ce: "r \<in> ce_rels"
  from r_ce have L1: "Domain r \<in> ce_sets" by (rule ce_rel_lm_26)
  from r_ce have L2: "Range r \<in> ce_sets" by (rule ce_rel_lm_27)
  from L1 L2 have L3: "Domain r \<union> Range r \<in> ce_sets" by (rule ce_union)
  then show ?thesis by (unfold Field_def)
qed

lemma ce_rel_lm_29: "\<lbrakk> A \<in> ce_sets; B \<in> ce_sets \<rbrakk> \<Longrightarrow> A \<times> B \<in> ce_rels"
proof -
  assume A_ce: "A \<in> ce_sets"
  assume B_ce: "B \<in> ce_sets"
  define r_a where "r_a = {(x,(0::nat)) | x. x \<in> A}"
  define r_b where "r_b = {((0::nat),z) | z. z \<in> B}"
  have L1: "r_a O r_b = A \<times> B" by (unfold r_a_def, unfold r_b_def, auto)
  have r_a_ce: "r_a \<in> ce_rels"
  proof -
    have loc1: "ce_rel_to_set r_a = { c_pair x 0 | x. x \<in> A}" by (unfold r_a_def, unfold ce_rel_to_set_def, auto)
    define p where "p x = c_pair x 0" for x
    have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
    from A_ce p_is_pr have "{ c_pair x 0 | x. x \<in> A} \<in> ce_sets"
      unfolding p_def by (simp add: ce_set_lm_7)
    with loc1 have "ce_rel_to_set r_a \<in> ce_sets" by auto
    then show ?thesis by (rule ce_rel_lm_7)
  qed
  have r_b_ce: "r_b \<in> ce_rels"
  proof -
    have loc1: "ce_rel_to_set r_b = { c_pair 0 z | z. z \<in> B}"
      by (unfold r_b_def, unfold ce_rel_to_set_def, auto)
    define p where "p z = c_pair 0 z" for z
    have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
    from B_ce p_is_pr have "{ c_pair 0 z | z. z \<in> B} \<in> ce_sets"
      unfolding p_def by (simp add: ce_set_lm_7)
    with loc1 have "ce_rel_to_set r_b \<in> ce_sets" by auto
    then show ?thesis by (rule ce_rel_lm_7)
  qed
  from r_b_ce r_a_ce have "r_a O r_b \<in> ce_rels" by (rule ce_rel_lm_24)
  with L1 show ?thesis by auto
qed

lemma ce_rel_lm_30: "{} \<in> ce_rels"
proof -
  have "ce_rel_to_set {} = {}" by (unfold ce_rel_to_set_def, auto)
  with ce_empty have "ce_rel_to_set {} \<in> ce_sets" by auto
  then show ?thesis by (rule ce_rel_lm_7)
qed

lemma ce_rel_lm_31: "UNIV \<in> ce_rels"
proof -
  from ce_univ ce_univ have "UNIV \<times> UNIV \<in> ce_rels" by (rule ce_rel_lm_29)
  then show ?thesis by auto
qed

lemma ce_rel_lm_32: "ce_rel_to_set (r \<union> s) = (ce_rel_to_set r) \<union> (ce_rel_to_set s)" by (unfold ce_rel_to_set_def, auto)

lemma ce_rel_lm_33: "\<lbrakk> r \<in> ce_rels; s \<in> ce_rels \<rbrakk> \<Longrightarrow> r \<union> s \<in> ce_rels"
proof -
  assume "r \<in> ce_rels"
  then have r_ce: "ce_rel_to_set r \<in> ce_sets" by (rule ce_rel_lm_6)
  assume "s \<in> ce_rels"
  then have s_ce: "ce_rel_to_set s \<in> ce_sets" by (rule ce_rel_lm_6)  
  have "ce_rel_to_set (r \<union> s) = (ce_rel_to_set r) \<union> (ce_rel_to_set s)" by (unfold ce_rel_to_set_def, auto)
  moreover from r_ce s_ce have "(ce_rel_to_set r) \<union> (ce_rel_to_set s) \<in> ce_sets" by (rule ce_union)
  ultimately have "ce_rel_to_set (r \<union> s) \<in> ce_sets" by auto
  then show ?thesis by (rule ce_rel_lm_7)
qed

lemma ce_rel_lm_34: "ce_rel_to_set (r \<inter> s) = (ce_rel_to_set r) \<inter> (ce_rel_to_set s)"
proof
  show "ce_rel_to_set (r \<inter> s) \<subseteq> ce_rel_to_set r \<inter> ce_rel_to_set s" by (unfold ce_rel_to_set_def, auto)
next
  show "ce_rel_to_set r \<inter> ce_rel_to_set s \<subseteq> ce_rel_to_set (r \<inter> s)"
  proof fix x assume A: "x \<in> ce_rel_to_set r \<inter> ce_rel_to_set s"
    from A have L1: "x \<in> ce_rel_to_set r" by auto
    from A have L2: "x \<in> ce_rel_to_set s" by auto
    from L1 obtain u v where L3: "(u,v) \<in> r" and L4: "x = c_pair u v" 
      unfolding ce_rel_to_set_def by auto
    from L2 obtain u1 v1 where L5: "(u1,v1) \<in> s" and L6: "x = c_pair u1 v1" 
      unfolding ce_rel_to_set_def by auto
    from L4 L6 have L7: "c_pair u1 v1 = c_pair u v" by auto
    then have "u1=u" by (rule c_pair_inj1)
    moreover from L7 have "v1=v" by (rule c_pair_inj2)
    ultimately have "(u,v)=(u1,v1)" by auto
    with L3 L5 have "(u,v) \<in> r \<inter> s" by auto
    with L4 show "x \<in> ce_rel_to_set (r \<inter> s)" by (unfold ce_rel_to_set_def, auto)
  qed
qed

lemma ce_rel_lm_35: "\<lbrakk> r \<in> ce_rels; s \<in> ce_rels \<rbrakk> \<Longrightarrow> r \<inter> s \<in> ce_rels"
proof -
  assume "r \<in> ce_rels"
  then have r_ce: "ce_rel_to_set r \<in> ce_sets" by (rule ce_rel_lm_6)
  assume "s \<in> ce_rels"
  then have s_ce: "ce_rel_to_set s \<in> ce_sets" by (rule ce_rel_lm_6)  
  have "ce_rel_to_set (r \<inter> s) = (ce_rel_to_set r) \<inter> (ce_rel_to_set s)" by (rule ce_rel_lm_34)
  moreover from r_ce s_ce have "(ce_rel_to_set r) \<inter> (ce_rel_to_set s) \<in> ce_sets" by (rule ce_intersect)
  ultimately have "ce_rel_to_set (r \<inter> s) \<in> ce_sets" by auto
  then show ?thesis by (rule ce_rel_lm_7)
qed

lemma ce_rel_lm_36: "ce_set_to_rel (A \<union> B) = (ce_set_to_rel A) \<union> (ce_set_to_rel B)"
  by (unfold ce_set_to_rel_def, auto)

lemma ce_rel_lm_37: "ce_set_to_rel (A \<inter> B) = (ce_set_to_rel A) \<inter> (ce_set_to_rel B)"
proof -
  define f where "f x = (c_fst x, c_snd x)" for x
  have f_inj: "inj f"
  proof (unfold f_def, rule inj_on_inverseI [where ?g="\<lambda> (u,v). c_pair u v"])
    fix x :: nat
    assume "x \<in> UNIV"
    show "case_prod c_pair (c_fst x, c_snd x) = x" by simp
  qed
  from f_inj have "f ` (A \<inter> B) = f ` A \<inter> f ` B" by (rule image_Int)
  then show ?thesis by (unfold f_def, unfold ce_set_to_rel_def, auto)
qed

lemma ce_rel_lm_38: "\<lbrakk> r \<in> ce_rels; A \<in> ce_sets \<rbrakk> \<Longrightarrow> r``A \<in> ce_sets"
proof -
  assume r_ce: "r \<in> ce_rels"
  assume A_ce: "A \<in> ce_sets"
  have L1: "r``A = Range (r \<inter> A \<times> UNIV)" by blast
  have L2: "Range (r \<inter> A \<times> UNIV) \<in> ce_sets"
  proof (rule ce_rel_lm_27)
    show "r \<inter> A \<times> UNIV \<in> ce_rels"
    proof (rule ce_rel_lm_35)
      show "r \<in> ce_rels" by (rule r_ce)
    next
      show "A \<times> UNIV \<in> ce_rels"
      proof (rule ce_rel_lm_29)
        show "A \<in> ce_sets" by (rule A_ce)
      next
        show "UNIV \<in> ce_sets" by (rule ce_univ)
      qed
    qed
  qed
  from L1 L2 show ?thesis by auto
qed


subsection \<open>Total computable functions\<close>

definition
  graph :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<times> nat) set" where
  "graph = (\<lambda> f. { (x, f x) | x. x \<in> UNIV})"

lemma graph_lm_1: "(x,y) \<in> graph f \<Longrightarrow> y = f x" by (unfold graph_def, auto)

lemma graph_lm_2: "y = f x \<Longrightarrow> (x,y) \<in> graph f" by (unfold graph_def, auto)

lemma graph_lm_3: "((x,y) \<in> graph f) = (y = f x)" by (unfold graph_def, auto)

lemma graph_lm_4: "graph (f o g) = (graph g) O (graph f)" by (unfold graph_def, auto)

definition
  c_graph :: "(nat \<Rightarrow> nat) \<Rightarrow> nat set" where
  "c_graph = (\<lambda> f. { c_pair x (f x) | x. x \<in> UNIV})"

lemma c_graph_lm_1: "c_pair x y \<in> c_graph f \<Longrightarrow> y = f x"
proof -
  assume A: "c_pair x y \<in> c_graph f"
  have S1: "c_graph f = {c_pair x (f x) | x. x \<in> UNIV}" by (simp add: c_graph_def)
  from A S1 obtain z where S2: "c_pair x y = c_pair z (f z)" by auto
  then have "x = z" by (rule c_pair_inj1)
  moreover from S2 have "y = f z" by (rule c_pair_inj2)
  ultimately show ?thesis by auto
qed

lemma c_graph_lm_2: "y = f x \<Longrightarrow> c_pair x y \<in> c_graph f" by (unfold c_graph_def, auto)

lemma c_graph_lm_3: "(c_pair x y \<in> c_graph f) = (y = f x)"
proof
  assume "c_pair x y \<in> c_graph f" then show "y = f x" by (rule c_graph_lm_1)
next
  assume "y = f x" then show "c_pair x y \<in> c_graph f" by (rule c_graph_lm_2)
qed

lemma c_graph_lm_4: "c_graph f = ce_rel_to_set (graph f)" by (unfold c_graph_def ce_rel_to_set_def graph_def, auto)

lemma c_graph_lm_5: "graph f = ce_set_to_rel (c_graph f)" by (simp add: c_graph_lm_4)

definition
  total_recursive :: "(nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "total_recursive = (\<lambda> f. graph f \<in> ce_rels)"

lemma total_recursive_def1: "total_recursive = (\<lambda> f. c_graph f \<in> ce_sets)"
proof (rule ext) fix f show " total_recursive f = (c_graph f \<in> ce_sets)"
  proof
    assume A: "total_recursive f"
    then have "graph f \<in> ce_rels" by (unfold total_recursive_def)
    then have "ce_rel_to_set (graph f) \<in> ce_sets" by (rule ce_rel_lm_6)
    then show "c_graph f \<in> ce_sets" by (simp add: c_graph_lm_4)
  next
    assume "c_graph f \<in> ce_sets"
    then have "ce_rel_to_set (graph f) \<in> ce_sets" by (simp add: c_graph_lm_4)
    then have "graph f \<in> ce_rels" by (rule ce_rel_lm_7)
    then show "total_recursive f" by (unfold total_recursive_def)
  qed
qed

theorem pr_is_total_rec: "f \<in> PrimRec1 \<Longrightarrow> total_recursive f"
proof -
  assume A: "f \<in> PrimRec1"
  define p where "p x = c_pair x (f x)" for x
  from A have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
  let ?U = "{ p x | x. x \<in> UNIV }"
  from ce_univ p_is_pr have U_ce: "?U \<in> ce_sets" by (rule ce_set_lm_7)
  have U_1: "?U = { c_pair x (f x) | x. x \<in> UNIV}" by (simp add: p_def)
  with U_ce have S1: "{ c_pair x (f x) | x. x \<in> UNIV} \<in> ce_sets" by simp
  with c_graph_def have c_graph_f_is_ce: "c_graph f \<in> ce_sets" by (unfold c_graph_def, auto)
  then show ?thesis by (unfold total_recursive_def1, auto)
qed

theorem comp_tot_rec: "\<lbrakk> total_recursive f; total_recursive g \<rbrakk> \<Longrightarrow> total_recursive (f o g)"
proof -
  assume "total_recursive f"
  then have f_ce: "graph f \<in> ce_rels" by (unfold total_recursive_def)
  assume "total_recursive g"
  then have g_ce: "graph g \<in> ce_rels" by (unfold total_recursive_def)
  from f_ce g_ce have "graph g O graph f \<in> ce_rels" by (rule ce_rel_lm_24)
  then have "graph (f o g) \<in> ce_rels" by (simp add: graph_lm_4)
  then show ?thesis by (unfold total_recursive_def)
qed

lemma univ_for_pr_tot_rec_lm: "c_graph univ_for_pr \<in> ce_sets"
proof -
  define A where "A = c_graph univ_for_pr"
  from A_def have S1: "A = { c_pair x (univ_for_pr x) | x. x \<in> UNIV }"
    by (simp add: c_graph_def)
  from S1 have S2: "A = { z . \<exists> x. z = c_pair x (univ_for_pr x) }" by auto
  have S3: "\<And> z. (\<exists> x. (z = c_pair x (univ_for_pr x))) = (univ_for_pr (c_fst z) = c_snd z)"
  proof -
    fix z show "(\<exists> x. (z = c_pair x (univ_for_pr x))) = (univ_for_pr (c_fst z) = c_snd z)"
    proof
      assume A: "\<exists>x. z = c_pair x (univ_for_pr x)"
      then obtain x where S3_1: "z = c_pair x (univ_for_pr x)" ..
      then show "univ_for_pr (c_fst z) = c_snd z" by simp
    next
      assume A: "univ_for_pr (c_fst z) = c_snd z"
      from A have "z = c_pair (c_fst z) (univ_for_pr (c_fst z))" by simp
      thus "\<exists>x. z = c_pair x (univ_for_pr x)" ..
    qed
  qed
  with S2 have S4: "A = { z . univ_for_pr (c_fst z) = c_snd z }" by auto
  define p where "p x y =
    (if c_assoc_have_key (pr_gr y) (c_fst x) = 0 then
      (if c_assoc_value (pr_gr y) (c_fst x) = c_snd x then (0::nat) else 1)
    else 1)" for x y
  from c_assoc_have_key_is_pr c_assoc_value_is_pr pr_gr_is_pr have p_is_pr: "p \<in> PrimRec2"
    unfolding p_def by prec
  have S5: "\<And> z. (univ_for_pr (c_fst z) = c_snd z) = (\<exists> y. p z y = 0)"
  proof -
    fix z show "(univ_for_pr (c_fst z) = c_snd z) = (\<exists> y. p z y = 0)"
    proof
      assume A: "univ_for_pr (c_fst z) = c_snd z"
      let ?n = "c_fst (c_fst z)"
      let ?x = "c_snd (c_fst z)"
      let ?y = "loc_upb ?n ?x"
      have S5_1: "c_assoc_have_key (pr_gr ?y) (c_pair ?n ?x) = 0" by (rule loc_upb_main)
      have S5_2: "c_assoc_value (pr_gr ?y) (c_pair ?n ?x) = univ_for_pr (c_pair ?n ?x)" by (rule pr_gr_value)
      from S5_1 have S5_3: "c_assoc_have_key (pr_gr ?y) (c_fst z) = 0" by simp
      from S5_2 A have S5_4: "c_assoc_value (pr_gr ?y) (c_fst z) = c_snd z" by simp
      from S5_3 S5_4 have "p z ?y = 0" by (simp add: p_def)
      thus "\<exists> y. p z y = 0" ..
    next
      assume A: "\<exists>y. p z y = 0"
      then obtain y where S5_1: "p z y = 0" ..
      have S5_2: "c_assoc_have_key (pr_gr y) (c_fst z) = 0"
      proof (rule ccontr)
        assume A_1: "c_assoc_have_key (pr_gr y) (c_fst z) \<noteq> 0"
        then have "p z y = 1" by (simp add: p_def)
        with S5_1 show False by auto
      qed
      then have S5_3: "p z y = (if c_assoc_value (pr_gr y) (c_fst z) = c_snd z then (0::nat) else 1)" by (simp add: p_def)
      have S5_4: "c_assoc_value (pr_gr y) (c_fst z) = c_snd z"
      proof (rule ccontr)
        assume A_2: "c_assoc_value (pr_gr y) (c_fst z) \<noteq> c_snd z"
        then have "p z y = 1" by (simp add: p_def)
        with S5_1 show False by auto
      qed
      have S5_5: "c_is_sub_fun (pr_gr y) univ_for_pr" by (rule pr_gr_1)
      from S5_5 S5_2 have S5_6: "c_assoc_value (pr_gr y) (c_fst z) = univ_for_pr (c_fst z)" by (rule c_is_sub_fun_lm_1)
      with S5_4 show "univ_for_pr (c_fst z) = c_snd z" by auto
    qed
  qed
  from S5 S4 have "A = {z. \<exists> y. p z y = 0}" by auto
  then have "A = fn_to_set p" by (simp add: fn_to_set_def)
  moreover from p_is_pr have "fn_to_set p \<in> ce_sets" by (rule ce_set_lm_1)
  ultimately have "A \<in> ce_sets" by auto
  with A_def show ?thesis by auto
qed

theorem univ_for_pr_tot_rec: "total_recursive univ_for_pr"
proof -
  have "c_graph univ_for_pr \<in> ce_sets" by (rule univ_for_pr_tot_rec_lm)
  then show ?thesis by (unfold total_recursive_def1, auto)
qed

subsection \<open>Computable sets, Post's theorem\<close>

definition
  computable :: "nat set \<Rightarrow> bool" where
  "computable = (\<lambda> A. A \<in> ce_sets \<and> -A \<in> ce_sets)"

lemma computable_complement_1: "computable A \<Longrightarrow> computable (- A)"
proof -
  assume "computable A"
  then show ?thesis by (unfold computable_def, auto)
qed

lemma computable_complement_2: "computable (- A) \<Longrightarrow> computable A"
proof -
  assume "computable (- A)"
  then show ?thesis by (unfold computable_def, auto)
qed

lemma computable_complement_3: "(computable A) = (computable (- A))" by (unfold computable_def, auto)

theorem comp_impl_tot_rec: "computable A \<Longrightarrow> total_recursive (chf A)"
proof -
  assume A: "computable A"
  from A have A1: "A \<in> ce_sets" by (unfold computable_def, simp)
  from A have A2: "-A \<in> ce_sets" by (unfold computable_def, simp)
  define p where "p x = c_pair x 0" for x
  define q where "q x = c_pair x 1" for x
  from p_def have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
  from q_def have q_is_pr: "q \<in> PrimRec1" unfolding q_def by prec
  define U0 where "U0 = {p x | x. x \<in> A}"
  define U1 where "U1 = {q x | x. x \<in> - A}"
  from A1 p_is_pr have U0_ce: "U0 \<in> ce_sets" by(unfold U0_def, rule ce_set_lm_7)
  from A2 q_is_pr have U1_ce: "U1 \<in> ce_sets" by(unfold U1_def, rule ce_set_lm_7)
  define U where "U = U0 \<union> U1"
  from U0_ce U1_ce have U_ce: "U \<in> ce_sets" by (unfold U_def, rule ce_union)
  define V where "V = c_graph (chf A)"
  have V_1: "V = { c_pair x (chf A x) | x. x \<in> UNIV}" by (simp add: V_def c_graph_def)
  from U0_def p_def have U0_1: "U0 = { c_pair x y | x y. x \<in> A \<and> y=0}" by auto
  from U1_def q_def have U1_1: "U1 = { c_pair x y | x y. x \<notin> A \<and> y=1}" by auto
  from U0_1 U1_1 U_def have U_1: "U = { c_pair x y | x y. (x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)}" by auto
  from V_1 have V_2: "V = { c_pair x y | x y. y = chf A x}" by auto
  have L1: "\<And> x y. ((x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)) = (y = chf A x)"
  proof -
    fix x y
    show "((x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)) = (y = chf A x)" by(unfold chf_def, auto)
  qed
  from V_2 U_1 L1 have "U=V" by simp
  with U_ce have V_ce: "V \<in> ce_sets" by auto
  with V_def have "c_graph (chf A) \<in> ce_sets" by auto
  then show ?thesis by (unfold total_recursive_def1)
qed

theorem tot_rec_impl_comp: "total_recursive (chf A) \<Longrightarrow> computable A"
proof -
  assume A: "total_recursive (chf A)"
  then have A1: "c_graph (chf A) \<in> ce_sets" by (unfold total_recursive_def1)
  let ?U = "c_graph (chf A)"
  have L1: "?U = { c_pair x (chf A x) | x. x \<in> UNIV}" by (simp add: c_graph_def)
  have L2: "\<And> x y. ((x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)) = (y = chf A x)"
  proof - fix x y show "((x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)) = (y = chf A x)" by(unfold chf_def, auto)
  qed
  from L1 L2 have L3: "?U = { c_pair x y | x y. (x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)}" by auto
  define p where "p x = c_pair x 0" for x
  define q where "q x = c_pair x 1" for x
  have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
  have q_is_pr: "q \<in> PrimRec1" unfolding q_def by prec
  define V where "V = { c_pair x y | x y. (x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)}"
  from V_def L3 A1 have V_ce: "V \<in> ce_sets" by auto
  from V_def have L4: "\<forall> z. (z \<in> V) = (\<exists> x y. z = c_pair x y \<and>  ((x \<in> A \<and> y=0) \<or> (x \<notin> A \<and> y=1)))" by blast
  have L5: "\<And> x. (p x \<in> V) = (x \<in> A)"
  proof - fix x show "(p x \<in> V) = (x \<in> A)"
    proof
      assume A: "p x \<in> V"
      then have "c_pair x 0 \<in> V" by (unfold p_def)
      with V_def obtain x1 y1 where L5_2: "c_pair x 0 = c_pair x1 y1"
        and L5_3: "((x1 \<in> A \<and> y1=0) \<or> (x1 \<notin> A \<and> y1=1))" by auto
      from L5_2 have X_eq_X1: "x=x1" by (rule c_pair_inj1)
      from L5_2 have Y1_eq_0: "0=y1" by (rule c_pair_inj2)
      from L5_3 X_eq_X1 Y1_eq_0 show "x \<in> A" by auto
    next
      assume A: "x \<in> A"
      let ?z = "c_pair x 0"
      from A have L5_1: "\<exists> x1 y1. c_pair x 0 = c_pair x1 y1 \<and>  ((x1 \<in> A \<and> y1=0) \<or> (x1 \<notin> A \<and> y1=1))" by auto
      with V_def have "c_pair x 0 \<in> V" by auto
      with p_def show "p x \<in> V" by simp
    qed
  qed
  then have A_eq: "A = { x. p x \<in> V}" by auto
  from V_ce p_is_pr have "{ x. p x \<in> V} \<in> ce_sets" by (rule ce_set_lm_5)
  with A_eq have A_ce: "A \<in> ce_sets" by simp
  have CA_eq: "- A = {x. q x \<in> V}"
  proof -
    have "\<And> x. (q x \<in> V) = (x \<notin> A)"
    proof - fix x show "(q x \<in> V) = (x \<notin> A)"
      proof
        assume A: "q x \<in> V"
        then have "c_pair x 1 \<in> V" by (unfold q_def)
        with V_def obtain x1 y1 where L5_2: "c_pair x 1 = c_pair x1 y1"
          and L5_3: "((x1 \<in> A \<and> y1=0) \<or> (x1 \<notin> A \<and> y1=1))" by auto
        from L5_2 have X_eq_X1: "x=x1" by (rule c_pair_inj1)
        from L5_2 have Y1_eq_1: "1=y1" by (rule c_pair_inj2)
        from L5_3 X_eq_X1 Y1_eq_1 show "x \<notin> A" by auto
      next
        assume A: "x \<notin> A"
        from A have L5_1: "\<exists> x1 y1. c_pair x 1 = c_pair x1 y1 \<and>  ((x1 \<in> A \<and> y1=0) \<or> (x1 \<notin> A \<and> y1=1))" by auto
        with V_def have "c_pair x 1 \<in> V" by auto
        with q_def show "q x \<in> V" by simp
      qed
    qed
    then show ?thesis by auto
  qed
  from V_ce q_is_pr have "{ x. q x \<in> V} \<in> ce_sets" by (rule ce_set_lm_5)
  with CA_eq have CA_ce: "- A \<in> ce_sets" by simp
  from A_ce CA_ce show ?thesis by (simp add: computable_def)
qed

theorem post_th_0: "(computable A) = (total_recursive (chf A))"
proof
  assume "computable A" then show "total_recursive (chf A)" by (rule comp_impl_tot_rec)
next
  assume "total_recursive (chf A)" then show "computable A" by (rule tot_rec_impl_comp)
qed

subsection \<open>Universal computably enumerable set\<close>

definition
  univ_ce :: "nat set" where
  "univ_ce = { c_pair n x | n x. x \<in> nat_to_ce_set n }"

lemma univ_for_pr_lm: "univ_for_pr (c_pair n x) = (nat_to_pr n) x"
  by (simp add: univ_for_pr_def pr_conv_2_to_1_def)

theorem univ_is_ce: "univ_ce \<in> ce_sets"
proof -
  define A where "A = c_graph univ_for_pr"
  then have "A \<in> ce_sets" by (simp add: univ_for_pr_tot_rec_lm)
  then have "\<exists> pA \<in> PrimRec2. A = fn_to_set pA" by (rule ce_set_lm_3)
  then obtain pA where pA_is_pr: "pA \<in> PrimRec2" and S1: "A = fn_to_set pA" by auto
  from S1 have S2: "A = { x. \<exists> y. pA x y = 0 }" by (simp add: fn_to_set_def)
  define p where "p z y = pA (c_pair (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y))) 0) (c_snd y)"
    for z y
  from pA_is_pr have p_is_pr: "p \<in> PrimRec2" unfolding p_def by prec
  have "\<And> z. (\<exists> n x. z = c_pair n x \<and> x \<in> nat_to_ce_set n) = (c_snd z \<in> nat_to_ce_set (c_fst z))"
  proof -
    fix z show "(\<exists> n x. z = c_pair n x \<and> x \<in> nat_to_ce_set n) = (c_snd z \<in> nat_to_ce_set (c_fst z))"
    proof
      assume A: "\<exists>n x. z = c_pair n x \<and> x \<in> nat_to_ce_set n"
      then obtain n x where L1: "z = c_pair n x \<and> x \<in> nat_to_ce_set n" by auto
      from L1 have L2: "z = c_pair n x" by auto
      from L1 have L3: "x \<in> nat_to_ce_set n" by auto
      from L1 have L4: "c_fst z = n" by simp
      from L1 have L5: "c_snd z = x" by simp
      from L3 L4 L5 show "c_snd z \<in> nat_to_ce_set (c_fst z)" by auto
    next
      assume A: "c_snd z \<in> nat_to_ce_set (c_fst z)"
      let ?n = "c_fst z"
      let ?x = "c_snd z"
      have L1: "z = c_pair ?n ?x" by simp
      from L1 A have "z = c_pair ?n ?x \<and> ?x \<in> nat_to_ce_set ?n" by auto
      thus "\<exists>n x. z = c_pair n x \<and> x \<in> nat_to_ce_set n" by blast
    qed
  qed
  then have "{ c_pair n x | n x. x \<in> nat_to_ce_set n } = { z. c_snd z \<in> nat_to_ce_set (c_fst z)}" by auto
  then have S3: "univ_ce  = { z. c_snd z \<in> nat_to_ce_set (c_fst z)}" by (simp add: univ_ce_def)
  have S4: "\<And> z. (c_snd z \<in> nat_to_ce_set (c_fst z)) = (\<exists> y. p z y = 0)"
  proof -
    fix z show "(c_snd z \<in> nat_to_ce_set (c_fst z)) = (\<exists> y. p z y = 0)"
    proof
      assume A: "c_snd z \<in> nat_to_ce_set (c_fst z)"
      have "nat_to_ce_set (c_fst z) = { x . \<exists> y. (nat_to_pr (c_fst z)) (c_pair x y) = 0 }" by (simp add: nat_to_ce_set_lm_1)
      with A obtain u where S4_1: "(nat_to_pr (c_fst z)) (c_pair (c_snd z) u) = 0"  by auto
      then have S4_2: "univ_for_pr (c_pair (c_fst z) (c_pair (c_snd z) u)) = 0" by (simp add: univ_for_pr_lm)
      from A_def have S4_3: "A = { c_pair x (univ_for_pr x) | x. x \<in> UNIV }" by (simp add: c_graph_def)
      then have S4_4: "\<And> x. c_pair x (univ_for_pr x) \<in> A" by auto
      then have "c_pair (c_pair (c_fst z) (c_pair (c_snd z) u)) (univ_for_pr (c_pair (c_fst z) (c_pair (c_snd z) u))) \<in> A" by auto
      with S4_2 have S4_5: "c_pair (c_pair (c_fst z) (c_pair (c_snd z) u)) 0 \<in> A" by auto
      with S2 obtain v where S4_6: "pA (c_pair (c_pair (c_fst z) (c_pair (c_snd z) u)) 0) v = 0" 
        by auto
      define y where "y = c_pair u v"
      from y_def have S4_7: "u = c_fst y" by simp
      from y_def have S4_8: "v = c_snd y" by simp
      from S4_6 S4_7 S4_8 p_def have "p z y = 0" by simp
      thus "\<exists> y. p z y = 0" ..
    next
      assume A: "\<exists>y. p z y = 0"
      then obtain y where S4_1: "p z y = 0" ..
      from S4_1 p_def have S4_2: "pA (c_pair (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y))) 0) (c_snd y) = 0" by simp
      with S2 have S4_3: "c_pair (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y))) 0 \<in> A" by auto
      with A_def have "c_pair (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y))) 0 \<in> c_graph univ_for_pr" by simp
      then have S4_4: "0 = univ_for_pr (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y)))" by (rule c_graph_lm_1)
      then have S4_5: "univ_for_pr (c_pair (c_fst z) (c_pair (c_snd z) (c_fst y))) = 0" by auto
      then have S4_6: "(nat_to_pr (c_fst z)) (c_pair (c_snd z) (c_fst y)) = 0" by (simp add: univ_for_pr_lm)
      then have S4_7: "\<exists> y. (nat_to_pr (c_fst z)) (c_pair (c_snd z) y) = 0" ..
      have S4_8: "nat_to_ce_set (c_fst z) = { x . \<exists> y. (nat_to_pr (c_fst z)) (c_pair x y) = 0 }" by (simp add: nat_to_ce_set_lm_1)
      from S4_7 have S4_9: "c_snd z \<in> { x . \<exists> y. (nat_to_pr (c_fst z)) (c_pair x y) = 0 }" by auto
      with S4_8 show "c_snd z \<in> nat_to_ce_set (c_fst z)" by auto
    qed
  qed
  with S3 have "univ_ce = {z. \<exists> y. p z y = 0}" by auto
  then have "univ_ce = fn_to_set p" by (simp add: fn_to_set_def)
  moreover from p_is_pr have "fn_to_set p \<in> ce_sets" by (rule ce_set_lm_1)
  ultimately show "univ_ce \<in> ce_sets" by auto
qed

lemma univ_ce_lm_1: "(c_pair n x \<in> univ_ce) = (x \<in> nat_to_ce_set n)"
proof -
  from univ_ce_def have S1: "univ_ce = {z . \<exists> n x. z = c_pair n x \<and> x \<in> nat_to_ce_set n}" by auto
  have S2: "(\<exists> n1 x1. c_pair n x = c_pair n1 x1 \<and> x1 \<in> nat_to_ce_set n1) = (x \<in> nat_to_ce_set n)"
  proof
    assume "\<exists>n1 x1. c_pair n x = c_pair n1 x1 \<and> x1 \<in> nat_to_ce_set n1"
    then obtain n1 x1 where L1: "c_pair n x = c_pair n1 x1" and L2: "x1 \<in> nat_to_ce_set n1" by auto
    from L1 have L3: "n = n1" by (rule c_pair_inj1)
    from L1 have L4: "x = x1" by (rule c_pair_inj2)
    from L2 L3 L4 show "x \<in> nat_to_ce_set n" by auto
  next
    assume A: "x \<in> nat_to_ce_set n"
    then have "c_pair n x = c_pair n x \<and> x \<in> nat_to_ce_set n" by auto
    thus "\<exists> n1 x1. c_pair n x = c_pair n1 x1 \<and> x1 \<in> nat_to_ce_set n1" by blast
  qed
  with S1 show ?thesis by auto
qed

theorem univ_ce_is_not_comp1: "- univ_ce \<notin> ce_sets"
proof (rule ccontr)
  assume "\<not> - univ_ce \<notin> ce_sets"
  then have A: "- univ_ce \<in> ce_sets" by auto
  define p where "p x = c_pair x x" for x
  have p_is_pr: "p \<in> PrimRec1" unfolding p_def by prec
  define A where "A = { x. p x \<in> - univ_ce }"
  from A p_is_pr have "{ x. p x \<in> - univ_ce } \<in> ce_sets" by (rule ce_set_lm_5)
  with A_def have S1: "A \<in> ce_sets" by auto
  then have "\<exists> n. A = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
  then obtain n where S2: "A = nat_to_ce_set n" ..
  from A_def have "(n \<in> A) = (p n \<in> - univ_ce)" by auto
  with p_def have "(n \<in> A) = (c_pair n n \<notin> univ_ce)" by auto
  with univ_ce_def univ_ce_lm_1 have "(n \<in> A) = (n \<notin> nat_to_ce_set n)" by auto
  with S2 have "(n \<in> A) = (n \<notin> A)" by auto
  thus False by auto
qed

theorem univ_ce_is_not_comp2: "\<not> total_recursive (chf univ_ce)"
proof
  assume "total_recursive (chf univ_ce)"
  then have "computable univ_ce" by (rule tot_rec_impl_comp)
  then have "- univ_ce \<in> ce_sets" by (unfold computable_def, auto)
  with univ_ce_is_not_comp1 show False by auto
qed

theorem univ_ce_is_not_comp3: "\<not> computable univ_ce"
proof (rule ccontr)
  assume "\<not> \<not> computable univ_ce"
  then have "computable univ_ce" by auto
  then have "total_recursive (chf univ_ce)" by (rule comp_impl_tot_rec)
  with univ_ce_is_not_comp2 show False by auto
qed

subsection \<open>s-1-1 theorem, one-one and many-one reducibilities\<close>

definition
  index_of_r_to_l :: nat where
  "index_of_r_to_l =
  pair_by_index
    (pair_by_index index_of_c_fst (comp_by_index index_of_c_fst index_of_c_snd))
    (comp_by_index index_of_c_snd index_of_c_snd)"

lemma index_of_r_to_l_lm: "nat_to_pr index_of_r_to_l (c_pair x (c_pair y z)) = c_pair (c_pair x y) z"
  apply(unfold index_of_r_to_l_def)
  apply(simp add: pair_by_index_main)
  apply(unfold c_f_pair_def)
  apply(simp add: index_of_c_fst_main)
  apply(simp add: comp_by_index_main)
  apply(simp add: index_of_c_fst_main)
  apply(simp add: index_of_c_snd_main)
done

definition
  s_ce :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "s_ce == (\<lambda> e x. s1_1 (comp_by_index e index_of_r_to_l) x)"

lemma s_ce_is_pr: "s_ce \<in> PrimRec2"
  unfolding s_ce_def using comp_by_index_is_pr s1_1_is_pr by prec

lemma s_ce_inj: "s_ce e1 x1 = s_ce e2 x2 \<Longrightarrow> e1=e2 \<and> x1=x2"
proof -
  let ?n1 = "index_of_r_to_l"
  assume "s_ce e1 x1 = s_ce e2 x2"
  then have "s1_1 (comp_by_index e1 ?n1) x1 = s1_1 (comp_by_index e2 ?n1) x2" by (unfold s_ce_def)
  then have L1: "comp_by_index e1 ?n1 = comp_by_index e2 ?n1 \<and> x1=x2" by (rule s1_1_inj)
  from L1 have "comp_by_index e1 ?n1 = comp_by_index e2 ?n1" ..
  then have "e1=e2" by (rule comp_by_index_inj1)
  moreover from L1 have "x1=x2" by auto
  ultimately show ?thesis by auto
qed

lemma s_ce_inj1: "s_ce e1 x = s_ce e2 x \<Longrightarrow> e1=e2"
proof -
  assume "s_ce e1 x = s_ce e2 x"
  then have "e1=e2 \<and> x=x" by (rule s_ce_inj)
  then show "e1=e2" by auto
qed

lemma s_ce_inj2: "s_ce e x1 = s_ce e x2 \<Longrightarrow> x1=x2"
proof -
  assume "s_ce e x1 = s_ce e x2"
  then have "e=e \<and> x1=x2" by (rule s_ce_inj)
  then show "x1=x2" by auto
qed

theorem s1_1_th1: "\<forall> n x y. ((nat_to_pr n) (c_pair x y)) = (nat_to_pr (s1_1 n x)) y"
proof (rule allI, rule allI, rule allI)
  fix n x y show "nat_to_pr n (c_pair x y) = nat_to_pr (s1_1 n x) y"
  proof -
    have "(\<lambda> y. (nat_to_pr n) (c_pair x y)) = nat_to_pr (s1_1 n x)" by (rule s1_1_th)
    then show ?thesis by (simp add: fun_eq_iff)
  qed
qed

lemma s_lm: "(nat_to_pr (s_ce e x)) (c_pair y z) = (nat_to_pr e) (c_pair (c_pair x y) z)"
proof -
  let ?n1 = "index_of_r_to_l"
  have "(nat_to_pr (s_ce e x)) (c_pair y z) = nat_to_pr (s1_1 (comp_by_index e ?n1) x) (c_pair y z)" by (unfold s_ce_def, simp)
  also have "\<dots> = (nat_to_pr (comp_by_index e ?n1)) (c_pair x (c_pair y z))" by (simp add: s1_1_th1)
  also have "\<dots> = (nat_to_pr e) ((nat_to_pr ?n1) (c_pair x (c_pair y z)))" by (simp add: comp_by_index_main)
  finally show ?thesis by (simp add: index_of_r_to_l_lm)
qed

theorem s_ce_1_1_th: "(c_pair x y \<in> nat_to_ce_set e) = (y \<in> nat_to_ce_set (s_ce e x))"
proof
  assume A: "c_pair x y \<in> nat_to_ce_set e"
  then obtain z where L1: "(nat_to_pr e) (c_pair (c_pair x y) z) = 0" 
    by (auto simp add: nat_to_ce_set_lm_1)
  have "(nat_to_pr (s_ce e x)) (c_pair y z) = 0" by (simp add: s_lm L1)
  with nat_to_ce_set_lm_1 show "y \<in> nat_to_ce_set (s_ce e x)" by auto
next
  assume A: "y \<in> nat_to_ce_set (s_ce e x)"
  then obtain z where L1: "(nat_to_pr (s_ce e x)) (c_pair y z) = 0" 
    by (auto simp add: nat_to_ce_set_lm_1)
  then have "(nat_to_pr e) (c_pair (c_pair x y) z) = 0" by (simp add: s_lm)
  with nat_to_ce_set_lm_1 show "c_pair x y \<in> nat_to_ce_set e" by auto
qed

definition
  one_reducible_to_via :: "(nat set) \<Rightarrow> (nat set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "one_reducible_to_via = (\<lambda> A B f. total_recursive f \<and> inj f \<and> (\<forall> x. (x \<in> A) = (f x \<in> B)))"

definition
  one_reducible_to :: "(nat set) \<Rightarrow> (nat set) \<Rightarrow> bool" where
  "one_reducible_to = (\<lambda> A B. \<exists> f. one_reducible_to_via A B f)"

definition
  many_reducible_to_via :: "(nat set) \<Rightarrow> (nat set) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "many_reducible_to_via = (\<lambda> A B f. total_recursive f \<and> (\<forall> x. (x \<in> A) = (f x \<in> B)))"

definition
  many_reducible_to :: "(nat set) \<Rightarrow> (nat set) \<Rightarrow> bool" where
  "many_reducible_to = (\<lambda> A B. \<exists> f. many_reducible_to_via A B f)"

lemma one_reducible_to_via_trans: "\<lbrakk> one_reducible_to_via A B f; one_reducible_to_via B C g \<rbrakk> \<Longrightarrow> one_reducible_to_via A C (g o f)"
proof -
  assume A1: "one_reducible_to_via A B f"
  assume A2: "one_reducible_to_via B C g"
  from A1 have f_tr: "total_recursive f" by (unfold one_reducible_to_via_def, auto)
  from A1 have f_inj: "inj f" by (unfold one_reducible_to_via_def, auto)
  from A1 have L1: "\<forall> x. (x \<in> A) = (f x \<in> B)" by (unfold one_reducible_to_via_def, auto)
  from A2 have g_tr: "total_recursive g" by (unfold one_reducible_to_via_def, auto)
  from A2 have g_inj: "inj g" by (unfold one_reducible_to_via_def, auto)
  from A2 have L2: "\<forall> x. (x \<in> B) = (g x \<in> C)" by (unfold one_reducible_to_via_def, auto)
  from g_tr f_tr have fg_tr: "total_recursive (g o f)" by (rule comp_tot_rec)
  from g_inj f_inj have fg_inj: "inj (g o f)" by (rule inj_compose)
  from L1 L2 have L3: "(\<forall> x. (x \<in> A) = ((g o f) x \<in> C))" by auto
  with fg_tr fg_inj show ?thesis by (unfold one_reducible_to_via_def, auto)
qed

lemma one_reducible_to_trans: "\<lbrakk> one_reducible_to A B; one_reducible_to B C \<rbrakk> \<Longrightarrow> one_reducible_to A C"
proof -
  assume "one_reducible_to A B"
  then obtain f where A1: "one_reducible_to_via A B f" unfolding one_reducible_to_def by auto
  assume "one_reducible_to B C"
  then obtain g where A2: "one_reducible_to_via B C g" unfolding one_reducible_to_def by auto
  from A1 A2 have "one_reducible_to_via A C (g o f)" by (rule one_reducible_to_via_trans)
  then show ?thesis unfolding one_reducible_to_def by auto
qed

lemma one_reducible_to_via_refl: "one_reducible_to_via A A (\<lambda> x. x)"
proof -
  have is_pr: "(\<lambda> x. x) \<in> PrimRec1" by (rule pr_id1_1)
  then have is_tr: "total_recursive (\<lambda> x. x)" by (rule pr_is_total_rec)
  have is_inj: "inj (\<lambda> x. x)" by simp
  have L1: "\<forall> x. (x \<in> A) = (((\<lambda> x. x) x) \<in> A)" by simp
  with is_tr is_inj show ?thesis by (unfold one_reducible_to_via_def, auto)
qed

lemma one_reducible_to_refl: "one_reducible_to A A"
proof -
  have "one_reducible_to_via A A (\<lambda> x. x)" by (rule one_reducible_to_via_refl)
  then show ?thesis by (unfold one_reducible_to_def, auto)
qed

lemma many_reducible_to_via_trans: "\<lbrakk> many_reducible_to_via A B f; many_reducible_to_via B C g \<rbrakk> \<Longrightarrow> many_reducible_to_via A C (g o f)"
proof -
  assume A1: "many_reducible_to_via A B f"
  assume A2: "many_reducible_to_via B C g"
  from A1 have f_tr: "total_recursive f" by (unfold many_reducible_to_via_def, auto)
  from A1 have L1: "\<forall> x. (x \<in> A) = (f x \<in> B)" by (unfold many_reducible_to_via_def, auto)
  from A2 have g_tr: "total_recursive g" by (unfold many_reducible_to_via_def, auto)
  from A2 have L2: "\<forall> x. (x \<in> B) = (g x \<in> C)" by (unfold many_reducible_to_via_def, auto)
  from g_tr f_tr have fg_tr: "total_recursive (g o f)" by (rule comp_tot_rec)
  from L1 L2 have L3: "(\<forall> x. (x \<in> A) = ((g o f) x \<in> C))" by auto
  with fg_tr show ?thesis by (unfold many_reducible_to_via_def, auto)
qed

lemma many_reducible_to_trans: "\<lbrakk> many_reducible_to A B; many_reducible_to B C \<rbrakk> \<Longrightarrow> many_reducible_to A C"
proof -
  assume "many_reducible_to A B"
  then obtain f where A1: "many_reducible_to_via A B f"
    unfolding many_reducible_to_def by auto
  assume "many_reducible_to B C"
  then obtain g where A2: "many_reducible_to_via B C g"
    unfolding many_reducible_to_def by auto
  from A1 A2 have "many_reducible_to_via A C (g o f)" by (rule many_reducible_to_via_trans)
  then show ?thesis unfolding many_reducible_to_def by auto
qed

lemma one_reducibility_via_is_many: "one_reducible_to_via A B f \<Longrightarrow> many_reducible_to_via A B f"
proof -
  assume A: "one_reducible_to_via A B f"
  from A have f_tr: "total_recursive f" by (unfold one_reducible_to_via_def, auto)
  from A have "\<forall> x. (x \<in> A) = (f x \<in> B)" by (unfold one_reducible_to_via_def, auto)
  with f_tr show ?thesis by (unfold many_reducible_to_via_def, auto)
qed

lemma one_reducibility_is_many: "one_reducible_to A B \<Longrightarrow> many_reducible_to A B"
proof -
  assume "one_reducible_to A B"
  then obtain f where A: "one_reducible_to_via A B f" 
    unfolding one_reducible_to_def by auto
  then have "many_reducible_to_via A B f" by (rule one_reducibility_via_is_many)
  then show ?thesis unfolding many_reducible_to_def by auto
qed

lemma many_reducible_to_via_refl: "many_reducible_to_via A A (\<lambda> x. x)"
proof -
  have "one_reducible_to_via A A (\<lambda> x. x)" by (rule one_reducible_to_via_refl)
  then show ?thesis by (rule one_reducibility_via_is_many)
qed

lemma many_reducible_to_refl: "many_reducible_to A A"
proof -
  have "one_reducible_to A A" by (rule one_reducible_to_refl)
  then show ?thesis by (rule one_reducibility_is_many)
qed

theorem m_red_to_comp: "\<lbrakk> many_reducible_to A B; computable B \<rbrakk> \<Longrightarrow> computable A"
proof -
  assume "many_reducible_to A B"
  then obtain f where A1: "many_reducible_to_via A B f" 
    unfolding many_reducible_to_def by auto
  from A1 have f_tr: "total_recursive f" by (unfold many_reducible_to_via_def, auto)
  from A1 have L1: "\<forall> x. (x \<in> A) = (f x \<in> B)" by (unfold many_reducible_to_via_def, auto)
  assume "computable B"
  then have L2: "total_recursive (chf B)" by (rule comp_impl_tot_rec)
  have L3: "chf A = (chf B) o f"
  proof fix x
    have "chf A x = (chf B) (f x)"
    proof cases
      assume A: "x \<in> A"
      then have L3_1: "chf A x = 0" by (simp add: chf_lm_2)
      from A L1 have "f x \<in> B" by auto
      then have L3_2: "(chf B) (f x) = 0" by (simp add: chf_lm_2)
      from L3_1 L3_2 show "chf A x = (chf B) (f x)" by auto
    next
      assume A: "x \<notin> A"
      then have L3_1: "chf A x = 1" by (simp add: chf_lm_3)
      from A L1 have "f x \<notin> B" by auto
      then have L3_2: "(chf B) (f x) = 1" by (simp add: chf_lm_3)
      from L3_1 L3_2 show "chf A x = (chf B) (f x)" by auto
    qed
    then show "chf A x = (chf B \<circ> f) x" by auto
  qed
  from L2 f_tr have "total_recursive (chf B \<circ> f)" by (rule comp_tot_rec)
  with L3 have "total_recursive (chf A)" by auto
  then show ?thesis by (rule tot_rec_impl_comp)
qed

lemma many_reducible_lm_1: "many_reducible_to univ_ce A \<Longrightarrow> \<not> computable A"
proof (rule ccontr)
  assume A1: "many_reducible_to univ_ce A"
  assume "\<not> \<not> computable A"
  then have A2: "computable A" by auto
  from A1 A2 have "computable univ_ce" by (rule m_red_to_comp)
  with univ_ce_is_not_comp3 show False by auto
qed

lemma one_reducible_lm_1: "one_reducible_to univ_ce A \<Longrightarrow> \<not> computable A"
proof -
  assume "one_reducible_to univ_ce A"
  then have "many_reducible_to univ_ce A" by (rule one_reducibility_is_many)
  then show ?thesis by (rule many_reducible_lm_1)
qed

lemma one_reducible_lm_2: "one_reducible_to_via (nat_to_ce_set n) univ_ce (\<lambda> x. c_pair n x)"
proof -
  define f where "f x = c_pair n x" for x
  have f_is_pr: "f \<in> PrimRec1" unfolding f_def by prec
  then have f_tr: "total_recursive f" by (rule pr_is_total_rec)
  have f_inj: "inj f"
  proof (rule injI)
    fix x y assume A: "f x = f y"
    then have "c_pair n x = c_pair n y" by (unfold f_def)
    then show "x = y" by (rule c_pair_inj2)
  qed
  have "\<forall> x. (x \<in> (nat_to_ce_set n)) = (f x \<in> univ_ce)"
  proof fix x show "(x \<in> nat_to_ce_set n) = (f x \<in> univ_ce)" by (unfold f_def, simp add: univ_ce_lm_1)
  qed
  with f_tr f_inj show ?thesis by (unfold f_def, unfold one_reducible_to_via_def, auto)
qed

lemma one_reducible_lm_3: "one_reducible_to (nat_to_ce_set n) univ_ce"
proof -
  have "one_reducible_to_via (nat_to_ce_set n) univ_ce (\<lambda> x. c_pair n x)" by (rule one_reducible_lm_2)
  then show ?thesis by (unfold one_reducible_to_def, auto)
qed

lemma one_reducible_lm_4: "A \<in> ce_sets \<Longrightarrow> one_reducible_to A univ_ce"
proof -
  assume "A \<in> ce_sets"
  then have "\<exists> n. A = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
  then obtain n where "A = nat_to_ce_set n" by auto
  with one_reducible_lm_3 show ?thesis by auto
qed

subsection \<open>One-complete sets\<close>

definition
  one_complete :: "nat set \<Rightarrow> bool" where
  "one_complete = (\<lambda> A. A \<in> ce_sets \<and> (\<forall> B. B \<in> ce_sets \<longrightarrow> one_reducible_to B A))"

theorem univ_is_complete: "one_complete univ_ce"
proof (unfold one_complete_def)
  show "univ_ce \<in> ce_sets \<and> (\<forall>B. B \<in> ce_sets \<longrightarrow> one_reducible_to B univ_ce)"
  proof
    show "univ_ce \<in> ce_sets" by (rule univ_is_ce)
  next
    show "\<forall>B. B \<in> ce_sets \<longrightarrow> one_reducible_to B univ_ce"
    proof (rule allI, rule impI)
      fix B assume "B \<in> ce_sets" then show "one_reducible_to B univ_ce" by (rule one_reducible_lm_4)
    qed
  qed
qed

subsection \<open>Index sets, Rice's theorem\<close>

definition
  index_set :: "nat set \<Rightarrow> bool" where
  "index_set = (\<lambda> A. \<forall> n m. n \<in> A \<and> (nat_to_ce_set n = nat_to_ce_set m) \<longrightarrow> m \<in> A)"

lemma index_set_lm_1: "\<lbrakk> index_set A; n\<in> A; nat_to_ce_set n = nat_to_ce_set m \<rbrakk> \<Longrightarrow> m \<in> A"
proof -
  assume A1: "index_set A"
  assume A2: "n \<in> A"
  assume A3: "nat_to_ce_set n = nat_to_ce_set m"
  from A2 A3 have L1: "n \<in> A \<and> (nat_to_ce_set n = nat_to_ce_set m)" by auto
  from A1 have L2: "\<forall> n m. n \<in> A \<and> (nat_to_ce_set n = nat_to_ce_set m) \<longrightarrow> m \<in> A" by (unfold index_set_def)
  from L1 L2 show ?thesis by auto
qed

lemma index_set_lm_2: "index_set A \<Longrightarrow> index_set (-A)"
proof -
  assume A: "index_set A"
  show "index_set (-A)"
  proof (unfold index_set_def)
    show "\<forall>n m. n \<in> - A \<and> nat_to_ce_set n = nat_to_ce_set m \<longrightarrow> m \<in> - A"
    proof (rule allI, rule allI, rule impI)
      fix n m assume A1: "n \<in> - A \<and> nat_to_ce_set n = nat_to_ce_set m"
      from A1 have A2: "n \<in> -A" by auto
      from A1 have A3: "nat_to_ce_set m = nat_to_ce_set n" by auto
      show "m \<in> - A"
      proof
        assume "m \<in> A"
        from A this A3 have "n \<in> A" by (rule index_set_lm_1)
        with A2 show False by auto
      qed
    qed
  qed
qed

lemma Rice_lm_1: "\<lbrakk> index_set A; A \<noteq> {}; A \<noteq> UNIV; \<exists> n \<in> A. nat_to_ce_set n = {} \<rbrakk> \<Longrightarrow> one_reducible_to univ_ce (- A)"
proof -
  assume A1: "index_set A"
  assume A2: "A \<noteq> {}"
  assume A3: "A \<noteq> UNIV"
  assume "\<exists> n \<in> A. nat_to_ce_set n = {}"
  then obtain e_0 where e_0_in_A: "e_0 \<in> A" and e_0_empty: "nat_to_ce_set e_0 = {}" by auto
  from e_0_in_A A3 obtain e_1 where e_1_not_in_A: "e_1 \<in> (- A)" by auto
  with e_0_in_A have e_0_neq_e_1: "e_0 \<noteq> e_1" by auto
  have "nat_to_ce_set e_0 \<noteq> nat_to_ce_set e_1"
  proof
    assume "nat_to_ce_set e_0 = nat_to_ce_set e_1"
    with A1 e_0_in_A have "e_1 \<in> A" by (rule index_set_lm_1)
    with e_1_not_in_A show False by auto
  qed
  with e_0_empty have e1_not_empty: "nat_to_ce_set e_1 \<noteq> {}" by auto
  define we_1 where "we_1 = nat_to_ce_set e_1"
  from e1_not_empty have we_1_not_empty: "we_1 \<noteq> {}" by (unfold we_1_def)
  define r where "r = univ_ce \<times> we_1"
  have loc_lm_1: "\<And> x. x \<in> univ_ce \<Longrightarrow> \<forall> y. (y \<in> we_1) = ((x,y) \<in> r)" by (unfold r_def, auto)
  have loc_lm_2: "\<And> x. x \<notin> univ_ce \<Longrightarrow> \<forall> y. (y \<in> {}) = ((x,y) \<in> r)" by (unfold r_def, auto)
  have r_ce: "r \<in> ce_rels"
  proof (unfold r_def, rule ce_rel_lm_29)
    show "univ_ce \<in> ce_sets" by (rule univ_is_ce)
    show "we_1 \<in> ce_sets" by (unfold we_1_def, rule nat_to_ce_set_into_ce)
  qed
  define we_n where "we_n = ce_rel_to_set r"
  from r_ce have we_n_ce: "we_n \<in> ce_sets" by (unfold we_n_def, rule ce_rel_lm_6)
  then have "\<exists> n. we_n = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
  then obtain n where we_n_df1: "we_n = nat_to_ce_set n" by auto
  define f where "f x = s_ce n x" for x
  from s_ce_is_pr have f_is_pr: "f \<in> PrimRec1" unfolding f_def by prec
  then have f_tr: "total_recursive f" by (rule pr_is_total_rec)
  have f_inj: "inj f"
  proof (rule injI)
    fix x y
    assume "f x = f y"
    then have "s_ce n x = s_ce n y" by (unfold f_def)
    then show "x = y" by (rule s_ce_inj2)
  qed
  have loc_lm_3: "\<forall> x y. (c_pair x y \<in> we_n) = (y \<in> nat_to_ce_set (f x))"
  proof (rule allI, rule allI)
    fix x y show "(c_pair x y \<in> we_n) = (y \<in> nat_to_ce_set (f x))" by (unfold f_def, unfold we_n_df1, simp add: s_ce_1_1_th)
  qed
  from A1 have loc_lm_4: "index_set (- A)" by (rule index_set_lm_2)
  have loc_lm_5: "\<forall> x. (x \<in> univ_ce) = (f x \<in> -A)"
  proof fix x show "(x \<in> univ_ce) = (f x \<in> -A)"
    proof
      assume A: "x \<in> univ_ce"
      then have S1: "\<forall> y. (y \<in> we_1) = ((x,y) \<in> r)" by (rule loc_lm_1)
      from ce_rel_lm_12 have "\<forall> y. (c_pair x y \<in> ce_rel_to_set r) = ((x,y) \<in> r)" by auto
      then have "\<forall> y. ((x,y) \<in> r) = (c_pair x y \<in> we_n)" by (unfold we_n_def, auto)
      with S1 have "\<forall> y. (y \<in> we_1) = (c_pair x y \<in> we_n)" by auto
      with loc_lm_3 have "\<forall> y. (y \<in> we_1) = (y \<in> nat_to_ce_set (f x))" by auto
      then have S2: "we_1 = nat_to_ce_set (f x)" by auto
      then have "nat_to_ce_set e_1 = nat_to_ce_set (f x)" by (unfold we_1_def)
      with loc_lm_4 e_1_not_in_A show "f x \<in> -A" by (rule index_set_lm_1)
    next
      show " f x \<in> - A \<Longrightarrow> x \<in> univ_ce"
      proof (rule ccontr)
        assume fx_in_A: "f x \<in> - A"
        assume x_not_in_univ: "x \<notin> univ_ce"
        then have S1: "\<forall> y. (y \<in> {}) = ((x,y) \<in> r)" by (rule loc_lm_2)
        from ce_rel_lm_12 have "\<forall> y. (c_pair x y \<in> ce_rel_to_set r) = ((x,y) \<in> r)" by auto
        then have "\<forall> y. ((x,y) \<in> r) = (c_pair x y \<in> we_n)" by (unfold we_n_def, auto)
        with S1 have "\<forall> y. (y \<in> {}) = (c_pair x y \<in> we_n)" by auto
        with loc_lm_3 have "\<forall> y. (y \<in> {}) = (y \<in> nat_to_ce_set (f x))" by auto
        then have S2: "{} = nat_to_ce_set (f x)" by auto
        then have "nat_to_ce_set e_0 = nat_to_ce_set (f x)" by (unfold e_0_empty)
        with A1 e_0_in_A have "f x \<in> A" by (rule index_set_lm_1)
        with fx_in_A show False by auto
      qed
    qed
  qed
  with f_tr f_inj have "one_reducible_to_via univ_ce (-A) f" by (unfold one_reducible_to_via_def, auto)
  then show ?thesis by (unfold one_reducible_to_def, auto)
qed

lemma Rice_lm_2: "\<lbrakk> index_set A; A \<noteq> {}; A \<noteq> UNIV; n \<in> A;  nat_to_ce_set n = {} \<rbrakk> \<Longrightarrow> one_reducible_to univ_ce (- A)"
proof -
  assume A1: "index_set A"
  assume A2: "A \<noteq> {}"
  assume A3: "A \<noteq> UNIV"
  assume A4: "n \<in> A"
  assume A5: "nat_to_ce_set n = {}"
  from A4 A5 have S1: "\<exists> n \<in> A. nat_to_ce_set n = {}" by auto
  from A1 A2 A3 S1 show ?thesis by (rule Rice_lm_1)
qed

theorem Rice_1: "\<lbrakk> index_set A; A \<noteq> {}; A \<noteq> UNIV \<rbrakk> \<Longrightarrow> one_reducible_to univ_ce A \<or> one_reducible_to univ_ce (- A)"
proof -
  assume A1: "index_set A"
  assume A2: "A \<noteq> {}"
  assume A3: "A \<noteq> UNIV"
  from ce_empty have "\<exists> n. {} = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
  then obtain n where n_empty: "nat_to_ce_set n = {}" by auto
  show ?thesis
  proof cases
    assume A: "n \<in> A"
    from A1 A2 A3 A n_empty have "one_reducible_to univ_ce (- A)" by (rule Rice_lm_2)
    then show ?thesis by auto
  next
    assume "n \<notin> A" then have A: "n \<in> - A" by auto
    from A1 have S1: "index_set (- A)" by (rule index_set_lm_2)
    from A3 have S2: "- A \<noteq> {}" by auto
    from A2 have S3: "- A \<noteq> UNIV" by auto
    from S1 S2 S3 A n_empty have "one_reducible_to univ_ce (- (- A))" by (rule Rice_lm_2)
    then have "one_reducible_to univ_ce A" by simp
    then show ?thesis by auto
  qed
qed

theorem Rice_2: "\<lbrakk> index_set A; A \<noteq> {}; A \<noteq> UNIV \<rbrakk> \<Longrightarrow> \<not> computable A"
proof -
  assume A1: "index_set A"
  assume A2: "A \<noteq> {}"
  assume A3: "A \<noteq> UNIV"
  from A1 A2 A3 have "one_reducible_to univ_ce A \<or> one_reducible_to univ_ce (- A)" by (rule Rice_1)
  then have S1: "\<not> one_reducible_to univ_ce A \<longrightarrow> one_reducible_to univ_ce (- A)" by auto
  show ?thesis
  proof cases
    assume "one_reducible_to univ_ce A"
    then show "\<not> computable A" by (rule one_reducible_lm_1)
  next
    assume "\<not> one_reducible_to univ_ce A"
    with S1 have "one_reducible_to univ_ce (- A)" by auto
    then have "\<not> computable (- A)" by (rule one_reducible_lm_1)
    with computable_complement_3 show "\<not> computable A" by auto
  qed
qed

theorem Rice_3: "\<lbrakk> C \<subseteq> ce_sets; computable { n. nat_to_ce_set n \<in> C} \<rbrakk> \<Longrightarrow> C = {} \<or> C = ce_sets"
proof (rule ccontr)
  assume A1: "C \<subseteq> ce_sets"
  assume A2: "computable { n. nat_to_ce_set n \<in> C}"
  assume A3: "\<not> (C = {} \<or> C = ce_sets)"
  from A3 have A4: "C \<noteq> {}" by auto
  from A3 have A5: "C \<noteq> ce_sets" by auto
  define A where "A = { n. nat_to_ce_set n \<in> C}"
  have S1: "index_set A"
  proof (unfold index_set_def)
    show "\<forall>n m. n \<in> A \<and> nat_to_ce_set n = nat_to_ce_set m \<longrightarrow> m \<in> A"
    proof (rule allI, rule allI, rule impI)
      fix n m assume A1_1: "n \<in> A \<and> nat_to_ce_set n = nat_to_ce_set m"
      from A1_1 have "n \<in> A" by auto
      then have S1_1: "nat_to_ce_set n \<in> C" by (unfold A_def, auto)
      from A1_1 have "nat_to_ce_set n = nat_to_ce_set m" by auto
      with S1_1 have "nat_to_ce_set m \<in> C" by auto
      then show "m \<in> A" by (unfold A_def, auto)
    qed
  qed
  have S2: "A \<noteq> {}"
  proof -
    from A4 obtain B where S2_1: "B \<in> C" by auto
    with A1 have "B \<in> ce_sets" by auto
    then have "\<exists> n. B = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
    then obtain n where "B = nat_to_ce_set n" ..
    with S2_1 have "nat_to_ce_set n \<in> C" by auto
    then show ?thesis by (unfold A_def, auto)
  qed
  have S3: "A \<noteq> UNIV"
  proof -
    from A1 A5 obtain B where S2_1: "B \<notin> C" and S2_2: "B \<in> ce_sets" by auto
    from S2_2 have "\<exists> n. B = nat_to_ce_set n" by (rule nat_to_ce_set_srj)
    then obtain n where "B = nat_to_ce_set n" ..
    with S2_1 have "nat_to_ce_set n \<notin> C" by auto
    then show ?thesis by (unfold A_def, auto)
  qed
  from S1 S2 S3 have "\<not> computable A" by (rule Rice_2)
  with A2 show False unfolding A_def by auto
qed

end
