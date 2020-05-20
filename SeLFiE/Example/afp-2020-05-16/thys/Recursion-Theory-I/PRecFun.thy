(*  Title:       Primitive recursive function
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Primitive recursive functions\<close>

theory PRecFun imports CPair
begin

text \<open>
  This theory contains definition of the primitive recursive functions.
\<close>


subsection \<open>Basic definitions\<close>

primrec
  PrimRecOp :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat)"
where
  "PrimRecOp g h 0 x  = g x"
| "PrimRecOp g h (Suc y) x = h y (PrimRecOp g h y x) x"

primrec
  PrimRecOp_last :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat)"
where
  "PrimRecOp_last g h x 0  = g x"
| "PrimRecOp_last g h x (Suc y)= h x (PrimRecOp_last g h x y) y"

primrec
  PrimRecOp1 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)"
where
  "PrimRecOp1 a h 0 = a"
| "PrimRecOp1 a h (Suc y) = h y (PrimRecOp1 a h y)"

inductive_set 
  PrimRec1 :: "(nat \<Rightarrow> nat) set" and
  PrimRec2 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) set" and
  PrimRec3 :: "(nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat) set"
where
  zero: "(\<lambda> x. 0) \<in> PrimRec1"
  | suc:   "Suc \<in> PrimRec1"
  | id1_1: "(\<lambda> x. x) \<in> PrimRec1"
  | id2_1: "(\<lambda> x y. x) \<in> PrimRec2"
  | id2_2: "(\<lambda> x y. y) \<in> PrimRec2"
  | id3_1: "(\<lambda> x y z. x) \<in> PrimRec3"
  | id3_2: "(\<lambda> x y z. y) \<in> PrimRec3"
  | id3_3: "(\<lambda> x y z. z) \<in> PrimRec3"
  | comp1_1: "\<lbrakk> f \<in> PrimRec1; g \<in> PrimRec1\<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x)) \<in> PrimRec1"
  | comp1_2: "\<lbrakk> f \<in> PrimRec1; g \<in> PrimRec2\<rbrakk> \<Longrightarrow> (\<lambda> x y. f (g x y)) \<in> PrimRec2"
  | comp1_3: "\<lbrakk> f \<in> PrimRec1; g \<in> PrimRec3\<rbrakk> \<Longrightarrow> (\<lambda> x y z. f (g x y z)) \<in> PrimRec3"
  | comp2_1: "\<lbrakk> f \<in> PrimRec2; g \<in> PrimRec1; h \<in> PrimRec1\<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x) (h x)) \<in> PrimRec1"
  | comp3_1: "\<lbrakk> f \<in> PrimRec3; g \<in> PrimRec1; h \<in> PrimRec1; k \<in> PrimRec1\<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x) (h x) (k x)) \<in> PrimRec1"
  | comp2_2: "\<lbrakk> f \<in> PrimRec2; g \<in> PrimRec2; h \<in> PrimRec2\<rbrakk> \<Longrightarrow> (\<lambda> x y. f (g x y) (h x y)) \<in> PrimRec2"
  | comp2_3: "\<lbrakk> f \<in> PrimRec2; g \<in> PrimRec3; h \<in> PrimRec3\<rbrakk> \<Longrightarrow> (\<lambda> x y z. f (g x y z) (h x y z)) \<in> PrimRec3"
  | comp3_2: "\<lbrakk> f \<in> PrimRec3; g \<in> PrimRec2; h \<in> PrimRec2; k \<in> PrimRec2\<rbrakk> \<Longrightarrow> (\<lambda> x y. f (g x y) (h x y) (k x y)) \<in> PrimRec2"
  | comp3_3: "\<lbrakk> f \<in> PrimRec3; g \<in> PrimRec3; h \<in> PrimRec3; k \<in> PrimRec3\<rbrakk> \<Longrightarrow> (\<lambda> x y z. f (g x y z) (h x y z) (k x y z)) \<in> PrimRec3"
  | prim_rec: "\<lbrakk> g \<in> PrimRec1; h \<in> PrimRec3\<rbrakk> \<Longrightarrow> PrimRecOp g h \<in> PrimRec2"

lemmas pr_zero = PrimRec1_PrimRec2_PrimRec3.zero
lemmas pr_suc = PrimRec1_PrimRec2_PrimRec3.suc
lemmas pr_id1_1 = PrimRec1_PrimRec2_PrimRec3.id1_1
lemmas pr_id2_1 = PrimRec1_PrimRec2_PrimRec3.id2_1
lemmas pr_id2_2 = PrimRec1_PrimRec2_PrimRec3.id2_2
lemmas pr_id3_1 = PrimRec1_PrimRec2_PrimRec3.id3_1
lemmas pr_id3_2 = PrimRec1_PrimRec2_PrimRec3.id3_2
lemmas pr_id3_3 = PrimRec1_PrimRec2_PrimRec3.id3_3
lemmas pr_comp1_1 = PrimRec1_PrimRec2_PrimRec3.comp1_1
lemmas pr_comp1_2 = PrimRec1_PrimRec2_PrimRec3.comp1_2
lemmas pr_comp1_3 = PrimRec1_PrimRec2_PrimRec3.comp1_3
lemmas pr_comp2_1 = PrimRec1_PrimRec2_PrimRec3.comp2_1
lemmas pr_comp2_2 = PrimRec1_PrimRec2_PrimRec3.comp2_2
lemmas pr_comp2_3 = PrimRec1_PrimRec2_PrimRec3.comp2_3
lemmas pr_comp3_1 = PrimRec1_PrimRec2_PrimRec3.comp3_1
lemmas pr_comp3_2 = PrimRec1_PrimRec2_PrimRec3.comp3_2
lemmas pr_comp3_3 = PrimRec1_PrimRec2_PrimRec3.comp3_3
lemmas pr_rec = PrimRec1_PrimRec2_PrimRec3.prim_rec

ML_file \<open>Utils.ML\<close>

named_theorems prec

method_setup prec0 = \<open>
  Attrib.thms >> (fn ths => fn ctxt => Method.METHOD (fn facts =>
    HEADGOAL (prec0_tac ctxt (facts @ Named_Theorems.get ctxt @{named_theorems prec}))))
\<close> "apply primitive recursive functions"


lemmas [prec] = pr_zero pr_suc pr_id1_1 pr_id2_1 pr_id2_2 pr_id3_1 pr_id3_2 pr_id3_3

lemma pr_swap: "f \<in> PrimRec2 \<Longrightarrow> (\<lambda> x y. f y x) \<in> PrimRec2" by prec0

theorem pr_rec_scheme: "\<lbrakk> g \<in> PrimRec1; h \<in> PrimRec3; \<forall> x. f 0 x = g x; \<forall> x y. f (Suc y) x = h y (f y x) x \<rbrakk> \<Longrightarrow> f \<in> PrimRec2"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  assume h_is_pr: "h \<in> PrimRec3"
  assume f_at_0: "\<forall> x. f 0 x = g x"
  assume f_at_Suc: "\<forall> x y. f (Suc y) x = h y (f y x) x"
  from f_at_0 f_at_Suc have "\<And> x y. f y x  = PrimRecOp g h y x" by (induct_tac y, simp_all)
  then have "f = PrimRecOp g h" by (simp add: ext)
  with g_is_pr h_is_pr show ?thesis by (simp add: pr_rec)
qed

lemma op_plus_is_pr [prec]: "(\<lambda> x y. x + y) \<in> PrimRec2"
proof (rule pr_swap)
 show "(\<lambda> x y. y+x) \<in> PrimRec2"
  proof -
    have S1: "PrimRecOp (\<lambda> x. x) (\<lambda> x y z. Suc y) \<in> PrimRec2"
    proof (rule pr_rec)
      show "(\<lambda> x. x) \<in> PrimRec1" by (rule pr_id1_1)
    next
      show "(\<lambda> x y z. Suc y) \<in> PrimRec3" by prec0
    qed
    have "(\<lambda> x y. y+x) = PrimRecOp (\<lambda> x. x) (\<lambda> x y z. Suc y)" (is "_ = ?f")
    proof -
      have "\<And> x y. (?f y x = y + x)" by (induct_tac y, auto)
      thus ?thesis by (simp add: ext)
    qed
    with S1 show ?thesis by simp
  qed
qed

lemma op_mult_is_pr [prec]: "(\<lambda> x y. x*y) \<in> PrimRec2"
proof (rule pr_swap)
 show "(\<lambda> x y. y*x) \<in> PrimRec2"
  proof -
    have S1: "PrimRecOp (\<lambda> x. 0) (\<lambda> x y z. y+z) \<in> PrimRec2"
    proof (rule pr_rec)
      show "(\<lambda> x. 0) \<in> PrimRec1" by (rule pr_zero)
    next
      show "(\<lambda> x y z. y+z) \<in> PrimRec3" by prec0
    qed
    have "(\<lambda> x y. y*x) = PrimRecOp (\<lambda> x. 0) (\<lambda> x y z. y+z)" (is "_ = ?f")
    proof -
      have "\<And> x y. (?f y x = y * x)" by (induct_tac y, auto)
      thus ?thesis by (simp add: ext)
    qed
    with S1 show ?thesis by simp
  qed
qed

lemma const_is_pr: "(\<lambda> x. (n::nat)) \<in> PrimRec1"
proof (induct n)
  show "(\<lambda> x. 0) \<in> PrimRec1" by (rule pr_zero)
next
  fix n assume "(\<lambda> x. n) \<in> PrimRec1"
  then show "(\<lambda> x. Suc n) \<in> PrimRec1" by prec0
qed

lemma const_is_pr_2: "(\<lambda> x y. (n::nat)) \<in> PrimRec2"
proof (rule pr_comp1_2 [where ?f="%x.(n::nat)" and ?g="%x y. x"])
  show "(\<lambda> x. n) \<in> PrimRec1" by (rule const_is_pr)
next
  show "(\<lambda> x y. x) \<in> PrimRec2" by (rule pr_id2_1)
qed

lemma const_is_pr_3: "(\<lambda> x y z. (n::nat)) \<in> PrimRec3"
proof (rule pr_comp1_3 [where ?f="%x.(n::nat)" and ?g="%x y z. x"])
  show "(\<lambda> x. n) \<in> PrimRec1" by (rule const_is_pr)
next
  show "(\<lambda> x y z. x) \<in> PrimRec3" by (rule pr_id3_1)
qed

theorem pr_rec_last: "\<lbrakk>g \<in> PrimRec1; h \<in> PrimRec3\<rbrakk> \<Longrightarrow> PrimRecOp_last g h \<in> PrimRec2"
proof -
  assume A1: "g \<in> PrimRec1"
  assume A2: "h \<in> PrimRec3"
  let ?h1 = "\<lambda> x y z. h z y x"
  from A2 pr_id3_3 pr_id3_2 pr_id3_1 have h1_is_pr: "?h1 \<in> PrimRec3" by (rule pr_comp3_3)
  let ?f1 = "PrimRecOp g ?h1"
  from A1 h1_is_pr have f1_is_pr: "?f1 \<in> PrimRec2" by (rule pr_rec)
  let ?f = "\<lambda> x y. ?f1 y x"
  from f1_is_pr have f_is_pr: "?f \<in> PrimRec2" by (rule pr_swap)
  have "\<And> x y. ?f x y = PrimRecOp_last g h x y" by (induct_tac y, simp_all)
  then have "?f = PrimRecOp_last g h" by (simp add: ext)
  with f_is_pr show ?thesis by simp
qed

theorem pr_rec1: "h \<in> PrimRec2 \<Longrightarrow> PrimRecOp1 (a::nat) h \<in> PrimRec1"
proof -
  assume A1: "h \<in> PrimRec2"
  let ?g = "(\<lambda> x. a)"
  have g_is_pr: "?g \<in> PrimRec1" by (rule const_is_pr)
  let ?h1 = "(\<lambda> x y z. h x y)"
  from A1 have h1_is_pr: "?h1 \<in> PrimRec3" by prec0
  let ?f1 = "PrimRecOp ?g ?h1"  
  from g_is_pr h1_is_pr have f1_is_pr: "?f1 \<in> PrimRec2" by (rule pr_rec)
  let ?f = "(\<lambda> x. ?f1 x 0)"
  from f1_is_pr pr_id1_1 pr_zero have f_is_pr: "?f \<in> PrimRec1" by (rule pr_comp2_1)
  have "\<And> y. ?f y = PrimRecOp1 a h y" by (induct_tac y, auto)
  then have "?f = PrimRecOp1 a h" by (simp add: ext)
  with f_is_pr show ?thesis by (auto)
qed

theorem pr_rec1_scheme: "\<lbrakk> h \<in> PrimRec2; f 0 = a; \<forall> y. f (Suc y) = h y (f y) \<rbrakk> \<Longrightarrow> f \<in> PrimRec1"
proof -
  assume h_is_pr: "h \<in> PrimRec2"
  assume f_at_0: "f 0 = a"
  assume f_at_Suc: "\<forall> y. f (Suc y) = h y (f y)"
  from f_at_0 f_at_Suc have "\<And> y. f y  = PrimRecOp1 a h y" by (induct_tac y, simp_all)
  then have "f = PrimRecOp1 a h" by (simp add: ext)
  with h_is_pr show ?thesis by (simp add: pr_rec1)
qed

lemma pred_is_pr: "(\<lambda> x. x - (1::nat)) \<in> PrimRec1"
proof -
  have S1: "PrimRecOp1 0 (\<lambda> x y. x) \<in> PrimRec1"
  proof (rule pr_rec1)
    show "(\<lambda> x y. x) \<in> PrimRec2" by (rule pr_id2_1)
  qed
  have "(\<lambda> x. x-(1::nat)) = PrimRecOp1 0 (\<lambda> x y. x)" (is "_ = ?f")
  proof -
    have "\<And> x. (?f x = x-(1::nat))" by (induct_tac x, auto)
    thus ?thesis by (simp add: ext)
  qed
  with S1 show ?thesis by simp
qed

lemma op_sub_is_pr [prec]: "(\<lambda> x y. x-y) \<in> PrimRec2"
proof (rule pr_swap)
 show "(\<lambda> x y. y - x) \<in> PrimRec2"
  proof -
    have S1: "PrimRecOp (\<lambda> x. x) (\<lambda> x y z.  y-(1::nat)) \<in> PrimRec2"
    proof (rule pr_rec)
      show "(\<lambda> x. x) \<in> PrimRec1" by (rule pr_id1_1)
    next
      from pred_is_pr pr_id3_2 show "(\<lambda> x y z. y-(1::nat)) \<in> PrimRec3" by (rule pr_comp1_3)
    qed
    have "(\<lambda> x y. y - x) = PrimRecOp (\<lambda> x. x) (\<lambda> x y z.  y-(1::nat))" (is "_ = ?f")
    proof -
      have "\<And> x y. (?f y x = x - y)" by (induct_tac y, auto)
      thus ?thesis by (simp add: ext)
    qed
    with S1 show ?thesis by simp
  qed
qed

lemmas [prec] =
  const_is_pr [of 0] const_is_pr_2 [of 0] const_is_pr_3 [of 0]
  const_is_pr [of 1] const_is_pr_2 [of 1] const_is_pr_3 [of 1]
  const_is_pr [of 2] const_is_pr_2 [of 2] const_is_pr_3 [of 2]

definition
  sgn1 :: "nat \<Rightarrow> nat" where
  "sgn1 x = (case x of 0 \<Rightarrow> 0 | Suc y \<Rightarrow> 1)"

definition
  sgn2 :: "nat \<Rightarrow> nat" where
  "sgn2 x \<equiv> (case x of 0 \<Rightarrow> 1 | Suc y \<Rightarrow> 0)"

definition
  abs_of_diff :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "abs_of_diff = (\<lambda> x y. (x - y) + (y - x))"

lemma [simp]: "sgn1 0 = 0" by (simp add: sgn1_def)
lemma [simp]: "sgn1 (Suc y) = 1" by (simp add: sgn1_def)
lemma [simp]: "sgn2 0 = 1" by (simp add: sgn2_def)
lemma [simp]: "sgn2 (Suc y) = 0" by (simp add: sgn2_def)
lemma [simp]: "x \<noteq> 0 \<Longrightarrow> sgn1 x = 1" by (simp add: sgn1_def, cases x, auto)
lemma [simp]: "x \<noteq> 0 \<Longrightarrow> sgn2 x = 0" by (simp add: sgn2_def, cases x, auto)

lemma sgn1_nz_impl_arg_pos: "sgn1 x \<noteq> 0 \<Longrightarrow> x > 0" by (cases x) auto
lemma sgn1_zero_impl_arg_zero: "sgn1 x = 0 \<Longrightarrow> x = 0" by (cases x) auto
lemma sgn2_nz_impl_arg_zero: "sgn2 x \<noteq> 0 \<Longrightarrow> x = 0" by (cases x) auto
lemma sgn2_zero_impl_arg_pos: "sgn2 x = 0 \<Longrightarrow> x > 0" by (cases x) auto

lemma sgn1_nz_eq_arg_pos: "(sgn1 x \<noteq> 0) = (x > 0)" by (cases x) auto
lemma sgn1_zero_eq_arg_zero: "(sgn1 x = 0) = (x = 0)" by (cases x) auto
lemma sgn2_nz_eq_arg_pos: "(sgn2 x \<noteq> 0) = (x = 0)" by (cases x) auto
lemma sgn2_zero_eq_arg_zero: "(sgn2 x = 0) = (x > 0)" by (cases x) auto

lemma sgn1_pos_eq_one: "sgn1 x > 0 \<Longrightarrow> sgn1 x = 1" by (cases x) auto
lemma sgn2_pos_eq_one: "sgn2 x > 0 \<Longrightarrow> sgn2 x = 1" by (cases x) auto

lemma sgn2_eq_1_sub_arg: "sgn2 = (\<lambda> x. 1 - x)"
proof (rule ext)
  fix x show "sgn2 x = 1 - x" by (cases x) auto
qed

lemma sgn1_eq_1_sub_sgn2: "sgn1  = (\<lambda> x. 1 - (sgn2 x))"
proof
  fix x show "sgn1 x = 1 - sgn2 x"
  proof -
    have "1- sgn2 x = 1 - (1 - x)" by (simp add: sgn2_eq_1_sub_arg)
    then show ?thesis by (simp add: sgn1_def, cases x, auto)
  qed
qed

lemma sgn2_is_pr [prec]: "sgn2 \<in> PrimRec1"
proof -
  have "(\<lambda> x. 1 - x) \<in> PrimRec1" by prec0
  thus ?thesis by (simp add: sgn2_eq_1_sub_arg)
qed

lemma sgn1_is_pr [prec]: "sgn1 \<in> PrimRec1"
proof -
  from sgn2_is_pr have "(\<lambda> x. 1 - (sgn2 x)) \<in> PrimRec1" by prec0
  thus ?thesis by (simp add: sgn1_eq_1_sub_sgn2)
qed

lemma abs_of_diff_is_pr [prec]: "abs_of_diff \<in> PrimRec2" unfolding abs_of_diff_def by prec0

lemma abs_of_diff_eq: "(abs_of_diff x y = 0) = (x = y)" by (simp add: abs_of_diff_def, arith)

lemma sf_is_pr [prec]: "sf \<in> PrimRec1"
proof -
  have S1: "PrimRecOp1 0 (\<lambda> x y. y + x + 1) \<in> PrimRec1"
  proof (rule pr_rec1)
    show "(\<lambda> x y. y + x + 1) \<in> PrimRec2" by prec0
  qed
  have "(\<lambda> x. sf x) = PrimRecOp1 0 (\<lambda> x y. y + x + 1)" (is "_ = ?f")
  proof -
    have "\<And> x. (?f x = sf x)"
    proof (induct_tac x)
      show "?f 0 = sf 0" by (simp add: sf_at_0)
    next
      fix x assume "?f x = sf x"
      with sf_at_Suc show "?f (Suc x) = sf (Suc x)"  by auto
    qed
    thus ?thesis by (simp add: ext)
  qed
  with S1 show ?thesis by simp
qed

lemma c_pair_is_pr [prec]: "c_pair \<in> PrimRec2"
proof -
  have "c_pair = (\<lambda> x y. sf (x+y) + x)" by (simp add: c_pair_def ext)
  moreover from sf_is_pr have "(\<lambda> x y. sf (x+y) + x) \<in> PrimRec2" by prec0
  ultimately show ?thesis by (simp)
qed

lemma if_is_pr: "\<lbrakk> p \<in> PrimRec1; q1 \<in> PrimRec1; q2 \<in> PrimRec1\<rbrakk> \<Longrightarrow> (\<lambda> x. if (p x = 0) then (q1 x) else (q2 x)) \<in> PrimRec1"
proof -
  have if_as_pr: "(\<lambda> x. if (p x = 0) then (q1 x) else (q2 x)) = (\<lambda> x. (sgn2 (p x)) * (q1 x) + (sgn1 (p x)) * (q2 x))"
  proof (rule ext)
    fix x show "(if (p x = 0) then (q1 x) else (q2 x)) = (sgn2 (p x)) * (q1 x) + (sgn1 (p x)) * (q2 x)" (is "?left = ?right")
    proof cases
      assume A1: "p x = 0"
      then have S1: "?left = q1 x" by simp
      from A1 have S2: "?right = q1 x" by simp
      from S1 S2 show ?thesis by simp
    next
      assume A2: "p x \<noteq> 0"
      then have S3: "p x > 0" by simp
      then show ?thesis by simp
    qed
  qed
  assume "p \<in> PrimRec1" and "q1 \<in> PrimRec1" and "q2 \<in> PrimRec1"
  then have "(\<lambda> x. (sgn2 (p x)) * (q1 x) + (sgn1 (p x)) * (q2 x)) \<in> PrimRec1" by prec0
  with if_as_pr show ?thesis by simp
qed

lemma if_eq_is_pr [prec]: "\<lbrakk> p1 \<in> PrimRec1; p2 \<in> PrimRec1; q1 \<in> PrimRec1; q2 \<in> PrimRec1\<rbrakk> \<Longrightarrow> (\<lambda> x. if (p1 x = p2 x) then (q1 x) else (q2 x)) \<in> PrimRec1"
proof -
  have S1: "(\<lambda> x. if (p1 x = p2 x) then (q1 x) else (q2 x)) = (\<lambda> x. if (abs_of_diff (p1 x) (p2 x) = 0) then (q1 x) else (q2 x))" (is "?L = ?R") by (simp add: abs_of_diff_eq)
  assume A1: "p1 \<in> PrimRec1" and A2: "p2 \<in> PrimRec1"
  with abs_of_diff_is_pr have S2: "(\<lambda> x. abs_of_diff (p1 x) (p2 x)) \<in> PrimRec1" by prec0
  assume "q1 \<in> PrimRec1" and "q2 \<in> PrimRec1"
  with S2 have "?R \<in> PrimRec1" by (rule if_is_pr)
  with S1 show ?thesis by simp
qed

lemma if_is_pr2 [prec]: "\<lbrakk> p \<in> PrimRec2; q1 \<in> PrimRec2; q2 \<in> PrimRec2\<rbrakk> \<Longrightarrow> (\<lambda> x y. if (p x y = 0) then (q1 x y) else (q2 x y)) \<in> PrimRec2"
proof -
  have if_as_pr: "(\<lambda> x y. if (p x y = 0) then (q1 x y) else (q2 x y)) = (\<lambda> x y. (sgn2 (p x y)) * (q1 x y) + (sgn1 (p x y)) * (q2 x y))"
  proof (rule ext, rule ext)
    fix x fix y show "(if (p x y = 0) then (q1 x y) else (q2 x y)) = (sgn2 (p x y)) * (q1 x y) + (sgn1 (p x y)) * (q2 x y)" (is "?left = ?right")
    proof cases
      assume A1: "p x y = 0"
      then have S1: "?left = q1 x y" by simp
      from A1 have S2: "?right = q1 x y" by simp
      from S1 S2 show ?thesis by simp
    next
      assume A2: "p x y \<noteq> 0"
      then have S3: "p x y > 0" by simp
      then show ?thesis by simp
    qed
  qed
  assume "p \<in> PrimRec2" and "q1 \<in> PrimRec2" and "q2 \<in> PrimRec2"
  then have "(\<lambda> x y. (sgn2 (p x y)) * (q1 x y) + (sgn1 (p x y)) * (q2 x y)) \<in> PrimRec2" by prec0
  with if_as_pr show ?thesis by simp
qed

lemma if_eq_is_pr2: "\<lbrakk> p1 \<in> PrimRec2; p2 \<in> PrimRec2; q1 \<in> PrimRec2; q2 \<in> PrimRec2\<rbrakk> \<Longrightarrow> (\<lambda> x y. if (p1 x y = p2 x y) then (q1 x y) else (q2 x y)) \<in> PrimRec2"
proof -
  have S1: "(\<lambda> x y. if (p1 x y = p2 x y) then (q1 x y) else (q2 x y)) = (\<lambda> x y. if (abs_of_diff (p1 x y) (p2 x y) = 0) then (q1 x y) else (q2 x y))" (is "?L = ?R") by (simp add: abs_of_diff_eq)
  assume A1: "p1 \<in> PrimRec2" and A2: "p2 \<in> PrimRec2"
  with abs_of_diff_is_pr have S2: "(\<lambda> x y. abs_of_diff (p1 x y) (p2 x y)) \<in> PrimRec2" by prec0
  assume "q1 \<in> PrimRec2" and "q2 \<in> PrimRec2"
  with S2 have "?R \<in> PrimRec2" by (rule if_is_pr2)
  with S1 show ?thesis by simp
qed

lemma if_is_pr3 [prec]: "\<lbrakk> p \<in> PrimRec3; q1 \<in> PrimRec3; q2 \<in> PrimRec3\<rbrakk> \<Longrightarrow> (\<lambda> x y z. if (p x y z = 0) then (q1 x y z) else (q2 x y z)) \<in> PrimRec3"
proof -
  have if_as_pr: "(\<lambda> x y z. if (p x y z = 0) then (q1 x y z) else (q2 x y z)) = (\<lambda> x y z. (sgn2 (p x y z)) * (q1 x y z) + (sgn1 (p x y z)) * (q2 x y z))"
  proof (rule ext, rule ext, rule ext)
    fix x fix y fix z show "(if (p x y z = 0) then (q1 x y z) else (q2 x y z)) = (sgn2 (p x y z)) * (q1 x y z) + (sgn1 (p x y z)) * (q2 x y z)" (is "?left = ?right")
    proof cases
      assume A1: "p x y z = 0"
      then have S1: "?left = q1 x y z" by simp
      from A1 have S2: "?right = q1 x y z" by simp
      from S1 S2 show ?thesis by simp
    next
      assume A2: "p x y z \<noteq> 0"
      then have S3: "p x y z > 0" by simp
      then show ?thesis by simp
    qed
  qed
  assume "p \<in> PrimRec3" and "q1 \<in> PrimRec3" and "q2 \<in> PrimRec3"
  then have "(\<lambda> x y z. (sgn2 (p x y z)) * (q1 x y z) + (sgn1 (p x y z)) * (q2 x y z)) \<in> PrimRec3"
    by prec0
  with if_as_pr show ?thesis by simp
qed

lemma if_eq_is_pr3: "\<lbrakk> p1 \<in> PrimRec3; p2 \<in> PrimRec3; q1 \<in> PrimRec3; q2 \<in> PrimRec3\<rbrakk> \<Longrightarrow> (\<lambda> x y z. if (p1 x y z = p2 x y z) then (q1 x y z) else (q2 x y z)) \<in> PrimRec3"
proof -
  have S1: "(\<lambda> x y z. if (p1 x y z = p2 x y z) then (q1 x y z) else (q2 x y z)) = (\<lambda> x y z. if (abs_of_diff (p1 x y z) (p2 x y z) = 0) then (q1 x y z) else (q2 x y z))" (is "?L = ?R") by (simp add: abs_of_diff_eq)
  assume A1: "p1 \<in> PrimRec3" and A2: "p2 \<in> PrimRec3"
  with abs_of_diff_is_pr have S2: "(\<lambda> x y z. abs_of_diff (p1 x y z) (p2 x y z)) \<in> PrimRec3"
    by prec0
  assume "q1 \<in> PrimRec3" and "q2 \<in> PrimRec3"
  with S2 have "?R \<in> PrimRec3" by (rule if_is_pr3)
  with S1 show ?thesis by simp
qed

ML \<open>
fun get_if_by_index 1 = @{thm if_eq_is_pr}
  | get_if_by_index 2 = @{thm if_eq_is_pr2}
  | get_if_by_index 3 = @{thm if_eq_is_pr3}
  | get_if_by_index _ = raise BadArgument

fun if_comp_tac ctxt = SUBGOAL (fn (t, i) =>
  let
    val t = extract_trueprop_arg (Logic.strip_imp_concl t)
    val (t1, t2) = extract_set_args t
    val n2 =
      let
        val Const(s, _) = t2
      in
        get_num_by_set s
      end
    val (name, _, n1) = extract_free_arg t1
  in
    if name = @{const_name If} then
      resolve_tac ctxt [get_if_by_index n2] i
    else
      let
        val comp = get_comp_by_indexes (n1, n2)
      in
        Rule_Insts.res_inst_tac ctxt
          [((("f", 0), Position.none), Variable.revert_fixed ctxt name)] [] comp i
      end
  end
  handle BadArgument => no_tac)

fun prec_tac ctxt facts i =
  Method.insert_tac ctxt facts i THEN
  REPEAT (resolve_tac ctxt [@{thm const_is_pr}, @{thm const_is_pr_2}, @{thm const_is_pr_3}] i ORELSE
    assume_tac ctxt i ORELSE if_comp_tac ctxt i)
\<close>

method_setup prec = \<open>
  Attrib.thms >> (fn ths => fn ctxt => Method.METHOD (fn facts =>
    HEADGOAL (prec_tac ctxt (facts @ Named_Theorems.get ctxt @{named_theorems prec}))))
\<close> "apply primitive recursive functions"


subsection \<open>Bounded least operator\<close>

definition
  b_least :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "b_least f x \<equiv> (Least (%y. y = x \<or> (y < x \<and> (f x y) \<noteq> 0)))"

definition
  b_least2 :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> nat)" where
  "b_least2 f x y \<equiv> (Least (%z. z = y \<or> (z < y \<and> (f x z) \<noteq> 0)))"

lemma b_least_aux1: "b_least f x = x \<or> (b_least f x < x \<and> (f x (b_least f x)) \<noteq> 0)"
proof -
  let ?P = "%y. y = x \<or> (y < x \<and> (f x y) \<noteq> 0)"
  have "?P x" by simp
  then have "?P (Least ?P)" by (rule LeastI)
  thus ?thesis by (simp add: b_least_def)
qed

lemma b_least_le_arg: "b_least f x \<le> x"
proof -
  have "b_least f x = x \<or> (b_least f x < x \<and> (f x (b_least f x)) \<noteq> 0)" by (rule b_least_aux1)
  from this show ?thesis by (arith)
qed

lemma less_b_least_impl_zero: "y < b_least f x \<Longrightarrow> f x y = 0"
proof -
  assume A1: "y < b_least f x" (is "_ < ?b")
  have "b_least f x \<le> x" by (rule b_least_le_arg)
  with A1 have S1: "y < x" by simp
  with A1 have " y < (Least (%y. y = x \<or> (y < x \<and> (f x y) \<noteq> 0)))" by (simp add: b_least_def)
  then have "\<not> (y = x \<or> (y < x \<and> (f x y) \<noteq> 0))" by (rule not_less_Least)
  with S1 show ?thesis by simp
qed

lemma nz_impl_b_least_le: "(f x y) \<noteq> 0 \<Longrightarrow> (b_least f x) \<le> y"
proof (rule ccontr)
  assume A1: "f x y \<noteq> 0"
  assume "\<not> b_least f x \<le> y"
  then have "y < b_least f x" by simp
  with A1 show False by (simp add: less_b_least_impl_zero)
qed

lemma b_least_less_impl_nz: "b_least f x < x \<Longrightarrow> f x (b_least f x) \<noteq> 0"
proof -
  assume A1: "b_least f x < x"
  have "b_least f x = x \<or> (b_least f x < x \<and> (f x (b_least f x)) \<noteq> 0)" by (rule b_least_aux1)
  from A1 this show ?thesis by simp
qed

lemma b_least_less_impl_eq: "b_least f x < x \<Longrightarrow> (b_least f x) = (Least (%y. (f x y) \<noteq> 0))"
proof -
  assume A1: "b_least f x < x" (is "?b < _")
  let ?B = "(Least (%y. (f x y) \<noteq> 0))"
  from A1 have S1: "f x ?b \<noteq> 0" by (rule b_least_less_impl_nz)
  from S1 have S2: "?B  \<le> ?b" by (rule Least_le)
  from S1 have S3: "f x ?B \<noteq> 0" by (rule LeastI)
  from S3 have S4: "?b \<le> ?B" by (rule nz_impl_b_least_le)
  from S2 S4 show ?thesis by simp
qed

lemma less_b_least_impl_zero2: "\<lbrakk>y < x; b_least f x = x\<rbrakk> \<Longrightarrow> f x y = 0" by (simp add: less_b_least_impl_zero)

lemma nz_impl_b_least_less: "\<lbrakk>y<x; (f x y) \<noteq> 0\<rbrakk> \<Longrightarrow> (b_least f x) < x"
proof -
  assume A1: "y < x"
  assume "f x y \<noteq> 0"
  then have "b_least f x \<le> y" by (rule nz_impl_b_least_le)
  with A1 show ?thesis by simp
qed

lemma b_least_aux2: "\<lbrakk>y<x; (f x y) \<noteq> 0\<rbrakk> \<Longrightarrow> (b_least f x) = (Least (%y. (f x y) \<noteq> 0))"
proof -
  assume A1: "y < x" and A2: "f x y \<noteq> 0"
  from A1 A2 have S1: "b_least f x < x" by (rule nz_impl_b_least_less)
  thus ?thesis by (rule b_least_less_impl_eq)
qed

lemma b_least2_aux1: "b_least2 f x y = y \<or> (b_least2 f x y < y \<and> (f x (b_least2 f x y)) \<noteq> 0)"
proof -
  let ?P = "%z. z = y \<or> (z < y \<and> (f x z) \<noteq> 0)"
  have "?P y" by simp
  then have "?P (Least ?P)" by (rule LeastI)
  thus ?thesis by (simp add: b_least2_def)
qed

lemma b_least2_le_arg: "b_least2 f x y \<le> y"
proof -
  let ?B = "b_least2 f x y"
  have "?B = y \<or> (?B < y \<and> (f x ?B) \<noteq> 0)" by (rule b_least2_aux1)
  from this show ?thesis by (arith)
qed

lemma less_b_least2_impl_zero: "z < b_least2 f x y \<Longrightarrow> f x z = 0"
proof -
  assume A1: "z < b_least2 f x y" (is "_ < ?b")
  have "b_least2 f x y \<le> y" by (rule b_least2_le_arg)
  with A1 have S1: "z < y" by simp
  with A1 have " z < (Least (%z. z = y \<or> (z < y \<and> (f x z) \<noteq> 0)))" by (simp add: b_least2_def)
  then have "\<not> (z = y \<or> (z < y \<and> (f x z) \<noteq> 0))" by (rule not_less_Least)
  with S1 show ?thesis by simp
qed

lemma nz_impl_b_least2_le: "(f x z) \<noteq> 0 \<Longrightarrow> (b_least2 f x y) \<le> z"
proof -
  assume A1: "f x z \<noteq> 0"
  have S1: "z < b_least2 f x y \<Longrightarrow> f x z = 0" by (rule less_b_least2_impl_zero)
  from A1 S1 show ?thesis by arith
qed

lemma b_least2_less_impl_nz: "b_least2 f x y < y \<Longrightarrow> f x (b_least2 f x y) \<noteq> 0"
proof -
  assume A1: "b_least2 f x y < y"
  have "b_least2 f x y = y \<or> (b_least2 f x y < y \<and> (f x (b_least2 f x y)) \<noteq> 0)" by (rule b_least2_aux1)
  with A1 show ?thesis by simp
qed

lemma b_least2_less_impl_eq: "b_least2 f x y < y \<Longrightarrow> (b_least2 f x y) = (Least (%z. (f x z) \<noteq> 0))"
proof -
  assume A1: "b_least2 f x y < y" (is "?b < _")
  let ?B = "(Least (%z. (f x z) \<noteq> 0))"
  from A1 have S1: "f x ?b \<noteq> 0" by (rule b_least2_less_impl_nz)
  from S1 have S2: "?B  \<le> ?b" by (rule Least_le)
  from S1 have S3: "f x ?B \<noteq> 0" by (rule LeastI)
  from S3 have S4: "?b \<le> ?B" by (rule nz_impl_b_least2_le)
  from S2 S4 show ?thesis by simp
qed

lemma less_b_least2_impl_zero2: "\<lbrakk>z<y; b_least2 f x y = y\<rbrakk> \<Longrightarrow> f x z = 0"
proof -
  assume  "z < y" and "b_least2 f x y = y"
  hence "z < b_least2 f x y" by simp
  thus ?thesis by (rule less_b_least2_impl_zero)
qed

lemma nz_b_least2_impl_less: "\<lbrakk>z<y; (f x z) \<noteq> 0\<rbrakk> \<Longrightarrow> (b_least2 f x y) < y"
proof (rule ccontr)
  assume A1: "z < y"
  assume A2: "f x z \<noteq> 0"
  assume "\<not> (b_least2 f x y) < y" then have A3: "y \<le> (b_least2 f x y)" by simp
  have "b_least2 f x y \<le> y" by (rule b_least2_le_arg)
  with A3 have "b_least2 f x y = y" by simp
  with A1 have "f x z = 0" by (rule less_b_least2_impl_zero2)
  with A2 show False by simp
qed

lemma b_least2_less_impl_eq2: "\<lbrakk>z < y; (f x z) \<noteq> 0\<rbrakk> \<Longrightarrow> (b_least2 f x y) = (Least (%z. (f x z) \<noteq> 0))"
proof -
  assume A1: "z < y" and A2: "f x z \<noteq> 0"
  from A1 A2 have S1: "b_least2 f x y < y" by (rule nz_b_least2_impl_less)
  thus ?thesis by (rule b_least2_less_impl_eq)
qed

lemma b_least2_aux2: "b_least2 f x y < y \<Longrightarrow> b_least2 f x (Suc y) = b_least2 f x y"
proof -
  let ?B = "b_least2 f x y"
  assume A1: "?B < y"
  from A1 have S1: "f x ?B \<noteq> 0" by (rule b_least2_less_impl_nz)
  from S1 have S2: "b_least2 f x (Suc y) \<le> ?B" by (simp add: nz_impl_b_least2_le)
  from A1 S2 have S3: "b_least2 f x (Suc y) < Suc y" by (simp)
  from S3 have S4: "f x (b_least2 f x (Suc y)) \<noteq> 0" by (rule b_least2_less_impl_nz)
  from S4 have S5: "?B \<le> b_least2 f x (Suc y)" by (rule nz_impl_b_least2_le)
  from S2 S5 show ?thesis by simp
qed

lemma b_least2_aux3: "\<lbrakk> b_least2 f x y = y; f x y \<noteq> 0\<rbrakk> \<Longrightarrow> b_least2 f x (Suc y) = y"
proof -
  assume A1: "b_least2 f x y =y"
  assume A2: "f x y \<noteq> 0"
  from A2 have S1: "b_least2 f x (Suc y) \<le> y" by (rule nz_impl_b_least2_le)
  have S2: "b_least2 f x (Suc y) < y \<Longrightarrow> False"
  proof -
    assume A2_1: "b_least2 f x (Suc y) < y" (is "?z < _")
    from A2_1 have S2_1: "?z < Suc y" by simp
    from S2_1 have S2_2: "f x ?z \<noteq> 0" by (rule b_least2_less_impl_nz)
    from A2_1 S2_2 have S2_3: "b_least2 f x y < y" by (rule nz_b_least2_impl_less)
    from S2_3 A1 show ?thesis by simp
  qed
  from S2 have S3: "\<not> (b_least2 f x (Suc y) < y)" by auto
  from S1 S3 show ?thesis by simp
qed

lemma b_least2_mono: "y1 \<le> y2 \<Longrightarrow> b_least2 f x y1 \<le> b_least2 f x y2"
proof (rule ccontr)
  assume A1: "y1 \<le> y2"
  let ?b1 = "b_least2 f x y1" and ?b2 = "b_least2 f x y2"
  assume "\<not> ?b1 \<le> ?b2" then have A2: "?b2 < ?b1" by simp
  have S1: "?b1 \<le> y1" by (rule b_least2_le_arg)
  have S2: "?b2 \<le> y2" by (rule b_least2_le_arg)
  from A1 A2 S1 S2 have S3: "?b2 < y2" by simp
  then have S4: "f x ?b2 \<noteq> 0" by (rule b_least2_less_impl_nz)
  from A2 have S5: "f x ?b2 = 0" by (rule less_b_least2_impl_zero)
  from S4 S5 show False by simp
qed

lemma b_least2_aux4: "\<lbrakk> b_least2 f x y = y; f x y = 0\<rbrakk> \<Longrightarrow> b_least2 f x (Suc y) = Suc y"
proof -
  assume A1: "b_least2 f x y = y"
  assume A2: "f x y = 0"
  have S1: "b_least2 f x (Suc y) \<le> Suc y" by (rule b_least2_le_arg)
  have S2: "y \<le> b_least2 f x (Suc y)"
  proof -
    have "y \<le> Suc y" by simp
    then have "b_least2 f x y \<le> b_least2 f x (Suc y)" by (rule b_least2_mono)
    with A1 show ?thesis by simp
  qed
  from S1 S2  have "b_least2 f x (Suc y) =y \<or> b_least2 f x (Suc y) = Suc y" by arith
  moreover
  {
    assume A3: "b_least2 f x (Suc y) = y"
    have "f x y \<noteq> 0"
    proof -
      have "y < Suc y" by simp
      with A3 have "b_least2 f x (Suc y) < Suc y" by simp
      from this have "f x (b_least2 f x (Suc y)) \<noteq> 0" by (simp add: b_least2_less_impl_nz)
      with A3 show "f x y \<noteq> 0" by simp      
    qed
    with A2 have ?thesis by simp
  }
  moreover
  {
    assume "b_least2 f x (Suc y) = Suc y"
    then have ?thesis by simp
  }
  ultimately show ?thesis by blast
qed

lemma b_least2_at_zero: "b_least2 f x 0 = 0"
proof -
  have S1: "b_least2 f x 0 \<le> 0" by (rule b_least2_le_arg)
  from S1 show ?thesis by auto
qed

theorem pr_b_least2: "f \<in> PrimRec2 \<Longrightarrow> b_least2 f \<in> PrimRec2"
proof -
  define loc_Op1 where "loc_Op1 = (\<lambda> (f::nat \<Rightarrow> nat \<Rightarrow> nat) x y z. (sgn1 (z - y)) * y + (sgn2 (z - y))*((sgn1 (f x z))*z + (sgn2 (f x z))*(Suc z)))"
  define loc_Op2 where "loc_Op2 = (\<lambda> f. PrimRecOp_last (\<lambda> x. 0) (loc_Op1 f))"
  have loc_op2_lm_1: "\<And> f x y. loc_Op2 f x y < y \<Longrightarrow> loc_Op2 f x (Suc y) = loc_Op2 f x y"
  proof -
    fix f x y
    let ?b = "loc_Op2 f x y"
    have S1: "loc_Op2 f x (Suc y) = (loc_Op1 f) x ?b y" by (simp add: loc_Op2_def)
    assume "?b < y"
    then have "y - ?b > 0" by simp
    then have "loc_Op1 f x ?b y = ?b" by (simp add: loc_Op1_def)
    with S1 show "loc_Op2 f x y < y \<Longrightarrow> loc_Op2 f x (Suc y) = loc_Op2 f x y" by simp
  qed
  have loc_op2_lm_2: "\<And> f x y. \<lbrakk>\<not>(loc_Op2 f x y < y); f x y \<noteq> 0\<rbrakk> \<Longrightarrow> loc_Op2 f x (Suc y) = y"
  proof -
    fix f x y
    let ?b = "loc_Op2 f x y" and ?h = "loc_Op1 f"
    have S1: "loc_Op2 f x (Suc y) = ?h x ?b y" by (simp add: loc_Op2_def)
    assume "\<not>(?b < y)"
    then have S2: "y - ?b = 0" by simp
    assume "f x y \<noteq> 0"
    with S2 have "?h x ?b y = y" by (simp add: loc_Op1_def)
    with S1 show "loc_Op2 f x (Suc y) = y" by simp
  qed
  have loc_op2_lm_3: "\<And> f x y. \<lbrakk>\<not>(loc_Op2 f x y < y); f x y = 0\<rbrakk> \<Longrightarrow> loc_Op2 f x (Suc y) = Suc y"
  proof -
    fix f x y
    let ?b = "loc_Op2 f x y" and ?h = "loc_Op1 f"
    have S1: "loc_Op2 f x (Suc y) = ?h x ?b y" by (simp add: loc_Op2_def)
    assume "\<not>(?b < y)"
    then have S2: "y - ?b = 0" by simp
    assume "f x y = 0"
    with S2 have "?h x ?b y = Suc y" by (simp add: loc_Op1_def)
    with S1 show "loc_Op2 f x (Suc y) = Suc y" by simp
  qed
  have Op2_eq_b_least2_at_point: "\<And> f x y. loc_Op2 f x y = b_least2 f x y"
  proof - fix f x show "\<And> y. loc_Op2 f x y = b_least2 f x y"
  proof (induct_tac y)
    show "loc_Op2 f x 0 = b_least2 f x 0" by (simp add: loc_Op2_def b_least2_at_zero)
  next
    fix y
    assume A1: "loc_Op2 f x y = b_least2 f x y"
    then show "loc_Op2 f x (Suc y) = b_least2 f x (Suc y)"
    proof cases
      assume A2: "loc_Op2 f x y < y"
      then have S1: "loc_Op2 f x (Suc y) = loc_Op2 f x y" by (rule loc_op2_lm_1)
      from A1 A2 have "b_least2 f x y < y" by simp
      then have S2: "b_least2 f x (Suc y) = b_least2 f x y" by (rule b_least2_aux2)
      from A1 S1 S2 show ?thesis by simp
    next
      assume A3: "\<not> loc_Op2 f x y < y"
      have A3': "b_least2 f x y = y"
      proof -
        have "b_least2 f x y \<le> y" by (rule b_least2_le_arg)
        from A1 A3 this show ?thesis by simp
      qed
      then show ?thesis
      proof cases
        assume A4: "f x y \<noteq> 0"
        with A3 have S3: "loc_Op2 f x (Suc y) = y" by (rule loc_op2_lm_2)
        from A3' A4 have S4: "b_least2 f x (Suc y) = y" by (rule b_least2_aux3)
        from S3 S4 show ?thesis by simp
      next
        assume "\<not> f x y \<noteq>  0"
        then have A5: "f x y = 0" by simp
        with A3 have S5: "loc_Op2 f x (Suc y) = Suc y" by (rule loc_op2_lm_3)
        from A3' A5 have S6: "b_least2 f x (Suc y) = Suc y" by (rule b_least2_aux4)
        from S5 S6 show ?thesis by simp
      qed
    qed
  qed
  qed
  have Op2_eq_b_least2: "loc_Op2 = b_least2" by (simp add: Op2_eq_b_least2_at_point ext)
  assume A1: "f \<in> PrimRec2"
  have pr_loc_Op2: "loc_Op2 f \<in> PrimRec2"
  proof -
    from A1 have S1: "loc_Op1 f \<in> PrimRec3" by (simp add: loc_Op1_def, prec)
    from pr_zero S1 have S2: "PrimRecOp_last (\<lambda> x. 0) (loc_Op1 f) \<in> PrimRec2" by (rule pr_rec_last)
    from this show ?thesis by (simp add: loc_Op2_def)
  qed
  from Op2_eq_b_least2 this show "b_least2 f \<in> PrimRec2" by simp
qed

lemma b_least_def1: "b_least f = (\<lambda> x. b_least2 f x x)" by (simp add: b_least2_def b_least_def ext)

theorem pr_b_least: "f \<in> PrimRec2 \<Longrightarrow> b_least f \<in> PrimRec1"
proof -
  assume "f \<in> PrimRec2"
  then have "b_least2 f \<in> PrimRec2" by (rule pr_b_least2)
  from this pr_id1_1 pr_id1_1 have "(\<lambda> x. b_least2 f x x) \<in> PrimRec1" by (rule pr_comp2_1)
  then show ?thesis by (simp add: b_least_def1)
qed

subsection \<open>Examples\<close>

theorem c_sum_as_b_least: "c_sum = (\<lambda> u. b_least2 (\<lambda> u z. (sgn1 (sf(z+1) - u))) u (Suc u))"
proof (rule ext)
  fix u show "c_sum u = b_least2 (\<lambda> u z. (sgn1 (sf(z+1) - u))) u (Suc u)"
  proof -
    have lm_1: "(\<lambda> x y. (sgn1 (sf(y+1) - x) \<noteq> 0)) = (\<lambda> x y. (x < sf(y+1)))"
    proof (rule ext, rule ext)
      fix x y show "(sgn1 (sf(y+1) - x) \<noteq> 0) = (x < sf(y+1))"
      proof -
        have "(sgn1 (sf(y+1) - x) \<noteq> 0) = (sf(y+1) - x > 0)" by (rule sgn1_nz_eq_arg_pos)
        thus "(sgn1 (sf(y+1) - x) \<noteq> 0) = (x < sf(y+1))" by auto
      qed
    qed (* lm_1 *)
    let ?f = "\<lambda> u z. (sgn1 (sf(z+1) - u))"
    have S1: "?f u u \<noteq> 0"
    proof -
      have S1_1: "u+1 \<le> sf(u+1)" by (rule arg_le_sf)
      have S1_2: "u < u+1" by simp
      from S1_1 S1_2 have S1_3: "u < sf(u+1)" by simp
      from S1_3 have S1_4: "sf(u+1) - u > 0" by simp
      from S1_4 have S1_5: "sgn1 (sf(u+1)-u) = 1" by simp
      from S1_5 show ?thesis by simp
    qed
    have S3: "u < Suc u" by simp
    from S3 S1 have S4: "b_least2 ?f u (Suc u) = (Least (%z. (?f u z) \<noteq> 0))" by (rule b_least2_less_impl_eq2)
    let ?P = "\<lambda> u z. ?f u z \<noteq> 0"
    let ?Q = "\<lambda> u z. u < sf(z+1)"
    from lm_1 have S6: "?P = ?Q" by simp
    from S6 have S7: "(%z. ?P u z) = (%z. ?Q u z)" by (rule fun_cong)
    from S7 have S8: "(Least (%z. ?P u z)) = (Least (%z. ?Q u z))" by auto
    from S4 S8 have S9: "b_least2 ?f u (Suc u) = (Least (%z. u < sf(z+1)))" by (rule trans)
    thus ?thesis by (simp add: c_sum_def)
  qed
qed

theorem c_sum_is_pr: "c_sum \<in> PrimRec1"
proof -
  let ?f = "\<lambda> u z. (sgn1 (sf(z+1) - u))"
  have S1: "(\<lambda> u z. sgn1 ((sf(z+1) - u))) \<in> PrimRec2" by prec
  define g where "g = b_least2 ?f"
  from g_def S1 have "g \<in> PrimRec2" by (simp add: pr_b_least2)
  then have S2: "(\<lambda> u. g u (Suc u)) \<in> PrimRec1" by prec
  from g_def have "c_sum = (\<lambda> u. g u (Suc u))" by (simp add: c_sum_as_b_least ext)
  with S2 show ?thesis by simp
qed

theorem c_fst_is_pr [prec]: "c_fst \<in> PrimRec1"
proof -
  have S1: "(\<lambda> u. c_fst u) = (\<lambda> u. (u - sf (c_sum u)))" by (simp add: c_fst_def ext)
  from c_sum_is_pr have "(\<lambda> u. (u - sf (c_sum u))) \<in> PrimRec1" by prec
  with S1 show ?thesis by simp
qed

theorem c_snd_is_pr [prec]: "c_snd \<in> PrimRec1"
proof -
  have S1: "c_snd = (\<lambda> u. (c_sum u) - (c_fst u))" by (simp add: c_snd_def ext)
  from c_sum_is_pr c_fst_is_pr have S2: "(\<lambda> u. (c_sum u) - (c_fst u)) \<in> PrimRec1" by prec
  from S1 this show ?thesis by simp
qed

theorem pr_1_to_2: "f \<in> PrimRec1 \<Longrightarrow> (\<lambda> x y. f (c_pair x y)) \<in> PrimRec2" by prec

theorem pr_2_to_1: "f \<in> PrimRec2 \<Longrightarrow> (\<lambda> z. f (c_fst z) (c_snd z)) \<in> PrimRec1" by prec

definition "pr_conv_1_to_2 = (\<lambda> f x y. f (c_pair x y))"
definition "pr_conv_1_to_3 = (\<lambda> f x y z. f (c_pair (c_pair x y) z))"
definition "pr_conv_2_to_1 = (\<lambda> f x. f (c_fst x) (c_snd x))"
definition "pr_conv_3_to_1 = (\<lambda> f x. f (c_fst (c_fst x)) (c_snd (c_fst x)) (c_snd x))"
definition "pr_conv_3_to_2 = (\<lambda> f. pr_conv_1_to_2 (pr_conv_3_to_1 f))"
definition "pr_conv_2_to_3 = (\<lambda> f. pr_conv_1_to_3 (pr_conv_2_to_1 f))"

lemma [simp]: "pr_conv_1_to_2 (pr_conv_2_to_1 f) = f" by(simp add: pr_conv_1_to_2_def pr_conv_2_to_1_def)
lemma [simp]: "pr_conv_2_to_1 (pr_conv_1_to_2 f) = f" by(simp add: pr_conv_1_to_2_def pr_conv_2_to_1_def)
lemma [simp]: "pr_conv_1_to_3 (pr_conv_3_to_1 f) = f" by(simp add: pr_conv_1_to_3_def pr_conv_3_to_1_def)
lemma [simp]: "pr_conv_3_to_1 (pr_conv_1_to_3 f) = f" by(simp add: pr_conv_1_to_3_def pr_conv_3_to_1_def)
lemma [simp]: "pr_conv_3_to_2 (pr_conv_2_to_3 f) = f" by(simp add: pr_conv_3_to_2_def pr_conv_2_to_3_def)
lemma [simp]: "pr_conv_2_to_3 (pr_conv_3_to_2 f) = f" by(simp add: pr_conv_3_to_2_def pr_conv_2_to_3_def)

lemma pr_conv_1_to_2_lm: "f \<in> PrimRec1 \<Longrightarrow> pr_conv_1_to_2 f \<in> PrimRec2" by (simp add: pr_conv_1_to_2_def, prec)
lemma pr_conv_1_to_3_lm: "f \<in> PrimRec1 \<Longrightarrow> pr_conv_1_to_3 f \<in> PrimRec3" by (simp add: pr_conv_1_to_3_def, prec)
lemma pr_conv_2_to_1_lm: "f \<in> PrimRec2 \<Longrightarrow> pr_conv_2_to_1 f \<in> PrimRec1" by (simp add: pr_conv_2_to_1_def, prec)
lemma pr_conv_3_to_1_lm: "f \<in> PrimRec3 \<Longrightarrow> pr_conv_3_to_1 f \<in> PrimRec1" by (simp add: pr_conv_3_to_1_def, prec)
lemma pr_conv_3_to_2_lm: "f \<in> PrimRec3 \<Longrightarrow> pr_conv_3_to_2 f \<in> PrimRec2"
proof -
  assume "f \<in> PrimRec3"
  then have "pr_conv_3_to_1 f \<in> PrimRec1" by (rule pr_conv_3_to_1_lm)
  thus ?thesis by (simp add: pr_conv_3_to_2_def pr_conv_1_to_2_lm)
qed
lemma pr_conv_2_to_3_lm: "f \<in> PrimRec2 \<Longrightarrow> pr_conv_2_to_3 f \<in> PrimRec3"
proof -
  assume "f \<in> PrimRec2"
  then have "pr_conv_2_to_1 f \<in> PrimRec1" by (rule pr_conv_2_to_1_lm)
  thus ?thesis by (simp add: pr_conv_2_to_3_def pr_conv_1_to_3_lm)
qed

theorem b_least2_scheme: "\<lbrakk> f \<in> PrimRec2; g \<in> PrimRec1; \<forall> x. h x < g x; \<forall> x. f x (h x) \<noteq> 0; \<forall> z x. z < h x \<longrightarrow> f x z = 0 \<rbrakk> \<Longrightarrow>
                            h \<in> PrimRec1"
proof -
  assume f_is_pr: "f \<in> PrimRec2"
  assume g_is_pr: "g \<in> PrimRec1"
  assume h_lt_g: "\<forall> x. h x < g x"
  assume f_at_h_nz: "\<forall> x. f x (h x) \<noteq> 0"
  assume h_is_min: "\<forall> z x. z < h x \<longrightarrow> f x z = 0"
  have h_def: "h = (\<lambda> x. b_least2 f x (g x))"
  proof
    fix x show "h x = b_least2 f x (g x)"
    proof -
      from f_at_h_nz have S1: "b_least2 f x (g x) \<le> h x" by (simp add: nz_impl_b_least2_le)
      from h_lt_g have "h x < g x" by auto
      with S1 have "b_least2 f x (g x) < g x" by simp
      then have S2: "f x (b_least2 f x (g x)) \<noteq> 0" by (rule b_least2_less_impl_nz)
      have S3: "h x \<le> b_least2 f x (g x)"
      proof (rule ccontr)
        assume "\<not> h x \<le> b_least2 f x (g x)" then have "b_least2 f x (g x) < h x" by auto
        with h_is_min have "f x (b_least2 f x (g x)) = 0" by simp
        with S2 show False by auto
      qed
      from S1 S3 show ?thesis by auto
    qed
  qed
  define f1 where "f1 = b_least2 f"
  from f_is_pr f1_def have f1_is_pr: "f1 \<in> PrimRec2" by (simp add: pr_b_least2)
  with g_is_pr have "(\<lambda> x. f1 x (g x)) \<in> PrimRec1" by prec
  with h_def f1_def show "h \<in> PrimRec1" by auto
qed

theorem b_least2_scheme2: "\<lbrakk> f \<in> PrimRec3; g \<in> PrimRec2; \<forall> x y. h x y < g x y; \<forall> x y. f x y (h x y) \<noteq> 0;
                             \<forall> z x y. z < h x y \<longrightarrow> f x y z = 0 \<rbrakk> \<Longrightarrow>
                             h \<in> PrimRec2"
proof -
  assume f_is_pr: "f \<in> PrimRec3"
  assume g_is_pr: "g \<in> PrimRec2"
  assume h_lt_g: "\<forall> x y. h x y < g x y"
  assume f_at_h_nz: "\<forall> x y. f x y (h x y) \<noteq> 0"
  assume h_is_min: "\<forall> z x y. z < h x y \<longrightarrow> f x y z = 0"
  define f1 where "f1 = pr_conv_3_to_2 f"
  define g1 where "g1 = pr_conv_2_to_1 g"
  define h1 where "h1 = pr_conv_2_to_1 h"
  from f_is_pr f1_def have f1_is_pr: "f1 \<in> PrimRec2" by (simp add: pr_conv_3_to_2_lm)
  from g_is_pr g1_def have g1_is_pr: "g1 \<in> PrimRec1" by (simp add: pr_conv_2_to_1_lm)
  from h_lt_g h1_def g1_def have h1_lt_g1: "\<forall> x. h1 x < g1 x" by (simp add: pr_conv_2_to_1_def)
  from f_at_h_nz f1_def h1_def have f1_at_h1_nz: "\<forall> x. f1 x (h1 x) \<noteq> 0" by (simp add: pr_conv_2_to_1_def pr_conv_3_to_2_def pr_conv_3_to_1_def pr_conv_1_to_2_def)
  from h_is_min f1_def h1_def have h1_is_min: "\<forall> z x. z < h1 x \<longrightarrow> f1 x z = 0" by (simp add: pr_conv_2_to_1_def pr_conv_3_to_2_def pr_conv_3_to_1_def pr_conv_1_to_2_def)
  from f1_is_pr g1_is_pr h1_lt_g1 f1_at_h1_nz h1_is_min have h1_is_pr: "h1 \<in> PrimRec1" by (rule b_least2_scheme)
  from h1_def have "h = pr_conv_1_to_2 h1" by simp
  with h1_is_pr show "h \<in> PrimRec2" by (simp add: pr_conv_1_to_2_lm)
qed

theorem div_is_pr: "(\<lambda> a b. a div b) \<in> PrimRec2"
proof -
  define f where "f a b z = (sgn1 b) * (sgn1 (b*(z+1)-a)) + (sgn2 b)*(sgn2 z)" for a b z
  have f_is_pr: "f \<in> PrimRec3" unfolding f_def by prec
  define h where "h a b = a div b" for a b :: nat
  define g where "g a b = a + 1" for a b :: nat
  have g_is_pr: "g \<in> PrimRec2" unfolding g_def by prec
  have h_lt_g: "\<forall> a b. h a b < g a b"
  proof (rule allI, rule allI)
    fix a b
    from h_def have "h a b \<le> a" by simp
    also from g_def have "a < g a b" by simp
    ultimately show "h a b < g a b" by simp
  qed
  have f_at_h_nz: "\<forall> a b. f a b (h a b) \<noteq> 0"
  proof (rule allI, rule allI)
    fix a b show "f a b (h a b) \<noteq> 0"
    proof cases
      assume A: "b = 0"
      with h_def have "h a b = 0" by simp
      with f_def A show ?thesis by simp
    next
      assume A: "b \<noteq> 0"
      then have S1: "b > 0" by auto
      from A f_def have S2: "f a b (h a b) = sgn1 (b * (h a b + 1) - a)" by simp
      then have "?thesis = (sgn1(b * (h a b + 1) - a) \<noteq> 0)" by auto
      also have "\<dots> = (b * (h a b + 1) - a > 0)" by (rule sgn1_nz_eq_arg_pos)
      also have "\<dots> = (a < b * (h a b + 1))" by auto
      also have "\<dots> = (a < b * (h a b) + b)" by auto
      also from h_def have "\<dots> = (a < b * (a div b) + b)" by simp
      finally have S3: "?thesis = (a < b * (a div b) + b)" by auto
      have S4: "a < b * (a div b) + b"
      proof -
        from S1 have S4_1: "a mod b < b" by (rule mod_less_divisor)
        also have S4_2: "b * (a div b) + a mod b = a" by (rule mult_div_mod_eq)
        from S4_1 have S4_3: "b * (a div b) + a mod b < b * (a div b) + b" by arith
        from S4_2 S4_3 show ?thesis by auto
      qed
      from S3 S4 show ?thesis by auto
    qed
  qed
  have h_is_min: "\<forall> z a b. z < h a b \<longrightarrow> f a b z = 0"
  proof (rule allI, rule allI, rule allI, rule impI)
    fix a b z assume A: "z < h a b" show "f a b z = 0"
    proof -
      from A h_def have S1: "z < a div b" by simp
      then have S2: "a div b > 0" by simp
      have S3: "b \<noteq> 0"
      proof (rule ccontr)
        assume "\<not> b \<noteq> 0" then have "b = 0" by auto
        then have "a div b = 0" by auto
        with S2 show False by auto
      qed
      from S3 have b_pos: "0 < b" by auto
      from S1 have S4: "z+1 \<le> a div b" by auto
      from b_pos have "(b * (z+1) \<le> b * (a div b)) = (z+1 \<le> a div b)" by (rule nat_mult_le_cancel1)
      with S4 have S5: "b*(z+1) \<le> b*(a div b)" by simp
      moreover have "b*(a div b) \<le> a"
      proof -
        have "b*(a div b) + (a mod b) = a" by (rule mult_div_mod_eq)
        moreover have "0 \<le> a mod b" by auto
        ultimately show ?thesis by arith
      qed
      ultimately have S6: "b*(z+1) \<le> a"
        by (simp add: minus_mod_eq_mult_div [symmetric])
      then have "b*(z+1) - a = 0" by auto
      with S3 f_def show ?thesis by simp
    qed
  qed
  from f_is_pr g_is_pr h_lt_g f_at_h_nz h_is_min have h_is_pr: "h \<in> PrimRec2" by (rule b_least2_scheme2)
  with h_def [abs_def] show ?thesis by simp
qed

theorem mod_is_pr: "(\<lambda> a b. a mod b) \<in> PrimRec2"
proof -
  have "(\<lambda> (a::nat) (b::nat). a mod b) = (\<lambda> a b. a - (a div b) * b)"
  proof (rule ext, rule ext)
    fix a b show "(a::nat) mod b = a - (a div b) * b" by (rule minus_div_mult_eq_mod [symmetric])
  qed
  also from div_is_pr have "(\<lambda> a b. a - (a div b) * b) \<in> PrimRec2" by prec
  ultimately show ?thesis by auto
qed

theorem pr_rec_last_scheme: "\<lbrakk> g \<in> PrimRec1; h \<in> PrimRec3; \<forall> x. f x 0 = g x; \<forall> x y. f x (Suc y) = h x (f x y) y \<rbrakk> \<Longrightarrow> f \<in> PrimRec2"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  assume h_is_pr: "h \<in> PrimRec3"
  assume f_at_0: "\<forall> x. f x 0 = g x"
  assume f_at_Suc: "\<forall> x y. f x (Suc y) = h x (f x y) y"
  from f_at_0 f_at_Suc have "\<And> x y. f x y = PrimRecOp_last g h x y" by (induct_tac y, simp_all)
  then have "f = PrimRecOp_last g h" by (simp add: ext)
  with g_is_pr h_is_pr show ?thesis by (simp add: pr_rec_last)
qed

theorem power_is_pr: "(\<lambda> (x::nat) (n::nat). x ^ n) \<in> PrimRec2"
proof -
  define g :: "nat \<Rightarrow> nat" where "g x = 1" for x
  define h where "h a b c = a * b" for a b c :: nat
  have g_is_pr: "g \<in> PrimRec1" unfolding g_def by prec
  have h_is_pr: "h \<in> PrimRec3" unfolding h_def by prec
  let ?f = "\<lambda> (x::nat) (n::nat). x ^ n"
  have f_at_0: "\<forall> x. ?f x 0 = g x"
  proof
    fix x show "x ^ 0 = g x" by (simp add: g_def)
  qed
  have f_at_Suc: "\<forall> x y. ?f x (Suc y) = h x (?f x y) y"
  proof (rule allI, rule allI)
    fix x y show "?f x (Suc y) = h x (?f x y) y" by (simp add: h_def)
  qed
  from g_is_pr h_is_pr f_at_0 f_at_Suc show ?thesis by (rule pr_rec_last_scheme)
qed

end
