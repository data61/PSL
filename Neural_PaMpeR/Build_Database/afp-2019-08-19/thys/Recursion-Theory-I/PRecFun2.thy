(*  Title:       Primitive recursive functions of one variable
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Primitive recursive functions of one variable\<close>

theory PRecFun2
imports PRecFun
begin

subsection \<open>Alternative definition of primitive recursive functions of one variable\<close>

definition
  UnaryRecOp :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "UnaryRecOp = (\<lambda> g h. pr_conv_2_to_1 (PrimRecOp g (pr_conv_1_to_3 h)))"

lemma unary_rec_into_pr: "\<lbrakk> g \<in> PrimRec1; h \<in> PrimRec1 \<rbrakk> \<Longrightarrow> UnaryRecOp g h \<in> PrimRec1" by (simp add: UnaryRecOp_def pr_conv_1_to_3_lm pr_conv_2_to_1_lm pr_rec)

definition
  c_f_pair :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat)" where
  "c_f_pair = (\<lambda> f g x. c_pair (f x) (g x))"

lemma c_f_pair_to_pr: "\<lbrakk> f \<in> PrimRec1; g \<in> PrimRec1 \<rbrakk> \<Longrightarrow> c_f_pair f g \<in> PrimRec1"
  unfolding c_f_pair_def by prec

inductive_set PrimRec1' :: "(nat \<Rightarrow> nat) set"
where
  zero: "(\<lambda> x. 0) \<in> PrimRec1'"
  | suc:  "Suc \<in> PrimRec1'"
  | fst:  "c_fst \<in> PrimRec1'"
  | snd:  "c_snd \<in> PrimRec1'"
  | comp: "\<lbrakk> f \<in> PrimRec1'; g \<in> PrimRec1' \<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x)) \<in> PrimRec1'"
  | pair: "\<lbrakk> f \<in> PrimRec1'; g \<in> PrimRec1' \<rbrakk> \<Longrightarrow> c_f_pair f g \<in> PrimRec1'"
  | un_rec: "\<lbrakk> f \<in> PrimRec1'; g \<in> PrimRec1' \<rbrakk> \<Longrightarrow> UnaryRecOp f g \<in> PrimRec1'"

lemma primrec'_into_primrec: "f \<in> PrimRec1' \<Longrightarrow> f \<in> PrimRec1"
proof (induct f rule: PrimRec1'.induct)
  case zero show ?case by (rule pr_zero)
next
  case suc show ?case by (rule pr_suc)
next
  case fst show ?case by (rule c_fst_is_pr)
next
  case snd show ?case by (rule c_snd_is_pr)
next
  case comp from comp show ?case by (simp add: pr_comp1_1)
next
  case pair from pair show ?case by (simp add: c_f_pair_to_pr)
next
  case un_rec from un_rec show ?case by (simp add: unary_rec_into_pr)
qed

lemma pr_id1_1': "(\<lambda> x. x) \<in> PrimRec1'"
proof -
  have "c_f_pair c_fst c_snd \<in> PrimRec1'" by (simp add: PrimRec1'.fst PrimRec1'.snd PrimRec1'.pair)
  moreover have "c_f_pair c_fst c_snd = (\<lambda> x. x)" by (simp add: c_f_pair_def)
  ultimately show ?thesis by simp
qed

lemma pr_id2_1': "pr_conv_2_to_1 (\<lambda> x y. x) \<in> PrimRec1'" by (simp add: pr_conv_2_to_1_def PrimRec1'.fst)

lemma pr_id2_2': "pr_conv_2_to_1 (\<lambda> x y. y) \<in> PrimRec1'" by (simp add: pr_conv_2_to_1_def PrimRec1'.snd)

lemma pr_id3_1': "pr_conv_3_to_1 (\<lambda> x y z. x) \<in> PrimRec1'"
proof -
  have "pr_conv_3_to_1 (\<lambda> x y z. x) = (\<lambda>x. c_fst (c_fst x))" by (simp add: pr_conv_3_to_1_def)
  moreover from PrimRec1'.fst PrimRec1'.fst have "(\<lambda>x. c_fst (c_fst x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  ultimately show ?thesis by simp
qed

lemma pr_id3_2': "pr_conv_3_to_1 (\<lambda> x y z. y) \<in> PrimRec1'"
proof -
  have "pr_conv_3_to_1 (\<lambda> x y z. y) = (\<lambda>x. c_snd (c_fst x))" by (simp add: pr_conv_3_to_1_def)
  moreover from PrimRec1'.snd PrimRec1'.fst have "(\<lambda>x. c_snd (c_fst x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  ultimately show ?thesis by simp
qed

lemma pr_id3_3': "pr_conv_3_to_1 (\<lambda> x y z. z) \<in> PrimRec1'"
proof -
  have "pr_conv_3_to_1 (\<lambda> x y z. z) = (\<lambda>x. c_snd x)" by (simp add: pr_conv_3_to_1_def)
  thus ?thesis by (simp add: PrimRec1'.snd)
qed

lemma pr_comp2_1': "\<lbrakk> pr_conv_2_to_1 f \<in> PrimRec1'; g \<in> PrimRec1'; h \<in> PrimRec1' \<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x) (h x)) \<in> PrimRec1'"
proof -
  assume A1: "pr_conv_2_to_1 f \<in> PrimRec1'"
  assume A2: "g \<in> PrimRec1'"
  assume A3: "h \<in> PrimRec1'"
  let ?f1 = "pr_conv_2_to_1 f"
  have S1: "(%x. ?f1 ((c_f_pair g h) x)) = (\<lambda> x. f (g x) (h x))" by (simp add: c_f_pair_def pr_conv_2_to_1_def)
  from A2 A3 have S2: "c_f_pair g h \<in> PrimRec1'" by (rule PrimRec1'.pair)
  from A1 S2 have S3: "(%x. ?f1 ((c_f_pair g h) x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  with S1 show ?thesis by simp
qed

lemma pr_comp3_1': "\<lbrakk> pr_conv_3_to_1 f \<in> PrimRec1'; g \<in> PrimRec1'; h \<in> PrimRec1'; k \<in> PrimRec1' \<rbrakk> \<Longrightarrow> (\<lambda> x. f (g x) (h x) (k x)) \<in> PrimRec1'"
proof -
  assume A1: "pr_conv_3_to_1 f \<in> PrimRec1'"
  assume A2: "g \<in> PrimRec1'"
  assume A3: "h \<in> PrimRec1'"
  assume A4: "k \<in> PrimRec1'"
  from A2 A3 have "c_f_pair g h \<in> PrimRec1'" by (rule PrimRec1'.pair)
  from this A4 have "c_f_pair (c_f_pair g h) k \<in> PrimRec1'" by (rule PrimRec1'.pair)
  from A1 this have "(%x. (pr_conv_3_to_1 f) ((c_f_pair (c_f_pair g h) k) x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  then show ?thesis by (simp add: c_f_pair_def pr_conv_3_to_1_def)
qed

lemma pr_comp1_2': "\<lbrakk> f \<in> PrimRec1'; pr_conv_2_to_1 g \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_2_to_1 (\<lambda> x y. f (g x y)) \<in> PrimRec1'"
proof -
  assume "f \<in> PrimRec1'"
  and "pr_conv_2_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  then show ?thesis by (simp add: pr_conv_2_to_1_def)
qed

lemma pr_comp1_3': "\<lbrakk> f \<in> PrimRec1'; pr_conv_3_to_1 g \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_3_to_1 (\<lambda> x y z. f (g x y z)) \<in> PrimRec1'"
proof -
  assume "f \<in> PrimRec1'"
  and "pr_conv_3_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x)) \<in> PrimRec1'" by (rule PrimRec1'.comp)
  then show ?thesis by (simp add: pr_conv_3_to_1_def)
qed

lemma pr_comp2_2': "\<lbrakk> pr_conv_2_to_1 f \<in> PrimRec1'; pr_conv_2_to_1 g \<in> PrimRec1'; pr_conv_2_to_1 h \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_2_to_1 (\<lambda> x y. f (g x y) (h x y)) \<in> PrimRec1'"
proof -
  assume "pr_conv_2_to_1 f \<in> PrimRec1'"
  and "pr_conv_2_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  and "pr_conv_2_to_1 h \<in> PrimRec1'" (is "?h1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x) (?h1 x)) \<in> PrimRec1'" by (rule pr_comp2_1')
  then show ?thesis by (simp add: pr_conv_2_to_1_def)
qed

lemma pr_comp2_3': "\<lbrakk> pr_conv_2_to_1 f \<in> PrimRec1'; pr_conv_3_to_1 g \<in> PrimRec1'; pr_conv_3_to_1 h \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_3_to_1 (\<lambda> x y z. f (g x y z) (h x y z)) \<in> PrimRec1'"
proof -
  assume "pr_conv_2_to_1 f \<in> PrimRec1'"
  and "pr_conv_3_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  and "pr_conv_3_to_1 h \<in> PrimRec1'" (is "?h1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x) (?h1 x)) \<in> PrimRec1'" by (rule pr_comp2_1')
  then show ?thesis by (simp add: pr_conv_3_to_1_def)
qed

lemma pr_comp3_2': "\<lbrakk> pr_conv_3_to_1 f \<in> PrimRec1'; pr_conv_2_to_1 g \<in> PrimRec1'; pr_conv_2_to_1 h \<in> PrimRec1'; pr_conv_2_to_1 k \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_2_to_1 (\<lambda> x y. f (g x y) (h x y) (k x y)) \<in> PrimRec1'"
proof -
  assume "pr_conv_3_to_1 f \<in> PrimRec1'"
  and "pr_conv_2_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  and "pr_conv_2_to_1 h \<in> PrimRec1'" (is "?h1 \<in> PrimRec1'")
  and "pr_conv_2_to_1 k \<in> PrimRec1'" (is "?k1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x) (?h1 x) (?k1 x)) \<in> PrimRec1'" by (rule pr_comp3_1')
  then show ?thesis by (simp add: pr_conv_2_to_1_def)
qed

lemma pr_comp3_3': "\<lbrakk> pr_conv_3_to_1 f \<in> PrimRec1'; pr_conv_3_to_1 g \<in> PrimRec1'; pr_conv_3_to_1 h \<in> PrimRec1'; pr_conv_3_to_1 k \<in> PrimRec1' \<rbrakk> \<Longrightarrow> pr_conv_3_to_1 (\<lambda> x y z. f (g x y z) (h x y z) (k x y z)) \<in> PrimRec1'"
proof -
  assume "pr_conv_3_to_1 f \<in> PrimRec1'"
  and "pr_conv_3_to_1 g \<in> PrimRec1'" (is "?g1 \<in> PrimRec1'")
  and "pr_conv_3_to_1 h \<in> PrimRec1'" (is "?h1 \<in> PrimRec1'")
  and "pr_conv_3_to_1 k \<in> PrimRec1'" (is "?k1 \<in> PrimRec1'")
  then have "(\<lambda> x. f (?g1 x) (?h1 x) (?k1 x)) \<in> PrimRec1'" by (rule pr_comp3_1')
  then show ?thesis by (simp add: pr_conv_3_to_1_def)
qed

lemma lm': "(f1 \<in> PrimRec1 \<longrightarrow> f1 \<in> PrimRec1') \<and> (g1 \<in> PrimRec2 \<longrightarrow> pr_conv_2_to_1 g1 \<in> PrimRec1') \<and> (h1 \<in> PrimRec3 \<longrightarrow> pr_conv_3_to_1 h1 \<in> PrimRec1')"
proof (induct rule: PrimRec1_PrimRec2_PrimRec3.induct)
     case zero show ?case by (rule PrimRec1'.zero)
next case suc show ?case by (rule PrimRec1'.suc)
next case id1_1 show ?case by (rule pr_id1_1')
next case id2_1 show ?case by (rule pr_id2_1')
next case id2_2 show ?case by (rule pr_id2_2')
next case id3_1 show ?case by (rule pr_id3_1')
next case id3_2 show ?case by (rule pr_id3_2')
next case id3_3 show ?case by (rule pr_id3_3')
next case comp1_1 from comp1_1 show ?case by (simp add: PrimRec1'.comp)
next case comp1_2 from comp1_2 show ?case by (simp add: pr_comp1_2')
next case comp1_3 from comp1_3 show ?case by (simp add: pr_comp1_3')
next case comp2_1 from comp2_1 show ?case by (simp add: pr_comp2_1')
next case comp2_2 from comp2_2 show ?case by (simp add: pr_comp2_2')
next case comp2_3 from comp2_3 show ?case by (simp add: pr_comp2_3')
next case comp3_1 from comp3_1 show ?case by (simp add: pr_comp3_1')
next case comp3_2 from comp3_2 show ?case by (simp add: pr_comp3_2')
next case comp3_3 from comp3_3 show ?case by (simp add: pr_comp3_3')
next case prim_rec
  fix g h assume A1: "g \<in> PrimRec1'" and "pr_conv_3_to_1 h \<in> PrimRec1'"
  then have "UnaryRecOp g (pr_conv_3_to_1 h) \<in> PrimRec1'" by (rule PrimRec1'.un_rec)
  moreover have "UnaryRecOp g (pr_conv_3_to_1 h) = pr_conv_2_to_1 (PrimRecOp g h)" by (simp add: UnaryRecOp_def)
  ultimately show "pr_conv_2_to_1 (PrimRecOp g h) \<in> PrimRec1'" by simp
qed

theorem pr_1_eq_1': "PrimRec1 = PrimRec1'"
proof -
  have S1: "\<And> f. f \<in> PrimRec1 \<longrightarrow> f \<in> PrimRec1'" by (simp add: lm')
  have S2: "\<And> f. f \<in> PrimRec1' \<longrightarrow> f \<in> PrimRec1" by (simp add: primrec'_into_primrec)
  from S1 S2 show ?thesis by blast
qed

subsection \<open>The scheme datatype\<close>

datatype PrimScheme = Base_zero | Base_suc | Base_fst | Base_snd
                      | Comp_op PrimScheme PrimScheme
                      | Pair_op PrimScheme PrimScheme
                      | Rec_op PrimScheme PrimScheme

primrec
  sch_to_pr :: "PrimScheme \<Rightarrow> (nat \<Rightarrow> nat)"
where
  "sch_to_pr Base_zero = (\<lambda> x. 0)"
| "sch_to_pr Base_suc = Suc"
| "sch_to_pr Base_fst = c_fst"
| "sch_to_pr Base_snd = c_snd"
| "sch_to_pr (Comp_op t1 t2)  = (\<lambda> x. (sch_to_pr t1) ((sch_to_pr t2) x))"
| "sch_to_pr (Pair_op t1 t2)  = c_f_pair (sch_to_pr t1) (sch_to_pr t2)"
| "sch_to_pr (Rec_op t1 t2)  = UnaryRecOp (sch_to_pr t1) (sch_to_pr t2)"

lemma sch_to_pr_into_pr: "sch_to_pr sch \<in> PrimRec1" by (simp add: pr_1_eq_1', induct sch, simp_all add: PrimRec1'.intros)

lemma sch_to_pr_srj: "f \<in> PrimRec1 \<Longrightarrow> (\<exists> sch. f = sch_to_pr sch)"
proof -
  assume "f \<in> PrimRec1" then have A1: "f \<in> PrimRec1'" by (simp add: pr_1_eq_1')
  from A1 show ?thesis
  proof (induct f rule: PrimRec1'.induct)
    have "(\<lambda> x. 0) = sch_to_pr Base_zero" by simp
    then show "\<exists>sch. (\<lambda>u. 0) = sch_to_pr sch" by (rule exI)
  next
    have "Suc = sch_to_pr Base_suc" by simp
    then show "\<exists>sch. Suc = sch_to_pr sch" by (rule exI)
  next
    have "c_fst = sch_to_pr Base_fst" by simp
    then show "\<exists>sch. c_fst = sch_to_pr sch" by (rule exI)
  next
    have "c_snd = sch_to_pr Base_snd" by simp
    then show "\<exists>sch. c_snd = sch_to_pr sch" by (rule exI)
  next
    fix f1 f2 assume B1: "\<exists>sch. f1 = sch_to_pr sch" and B2: "\<exists>sch. f2 = sch_to_pr sch"
    from B1 obtain sch1 where S1: "f1 = sch_to_pr sch1" ..
    from B2 obtain sch2 where S2: "f2 = sch_to_pr sch2" ..
    from S1 S2 have "(\<lambda> x. f1 (f2 x)) = sch_to_pr (Comp_op sch1 sch2)" by simp
    then show "\<exists>sch. (\<lambda>x. f1 (f2 x)) = sch_to_pr sch" by (rule exI)
  next
    fix f1 f2 assume B1: "\<exists>sch. f1 = sch_to_pr sch" and B2: "\<exists>sch. f2 = sch_to_pr sch"
    from B1 obtain sch1 where S1: "f1 = sch_to_pr sch1" ..
    from B2 obtain sch2 where S2: "f2 = sch_to_pr sch2" ..
    from S1 S2 have "c_f_pair f1 f2 = sch_to_pr (Pair_op sch1 sch2)" by simp
    then show "\<exists>sch. c_f_pair f1 f2 = sch_to_pr sch" by (rule exI)
  next
    fix f1 f2 assume B1: "\<exists>sch. f1 = sch_to_pr sch" and B2: "\<exists>sch. f2 = sch_to_pr sch"
    from B1 obtain sch1 where S1: "f1 = sch_to_pr sch1" ..
    from B2 obtain sch2 where S2: "f2 = sch_to_pr sch2" ..
    from S1 S2 have "UnaryRecOp f1 f2 = sch_to_pr (Rec_op sch1 sch2)" by simp
    then show "\<exists>sch. UnaryRecOp f1 f2 = sch_to_pr sch" by (rule exI)
  qed
qed

definition
  loc_f :: "nat \<Rightarrow> PrimScheme \<Rightarrow> PrimScheme \<Rightarrow> PrimScheme" where
  "loc_f n sch1 sch2 =
    (if n=0 then Base_zero else
     if n=1 then Base_suc else
     if n=2 then Base_fst else
     if n=3 then Base_snd else
     if n=4 then (Comp_op sch1 sch2) else
     if n=5 then (Pair_op sch1 sch2) else
     if n=6 then (Rec_op sch1 sch2) else
     Base_zero)"

definition
  mod7 :: "nat \<Rightarrow> nat" where
  "mod7 = (\<lambda> x. x mod 7)"

lemma c_snd_snd_lt [termination_simp]: "c_snd (c_snd (Suc (Suc x))) < Suc (Suc x)"
proof -
  let ?y = "Suc (Suc x)"
  have "?y > 1" by simp
  then have "c_snd ?y < ?y" by (rule c_snd_less_arg)
  moreover have "c_snd (c_snd ?y) \<le> c_snd ?y" by (rule c_snd_le_arg)
  ultimately show ?thesis by simp
qed

lemma c_fst_snd_lt [termination_simp]: "c_fst (c_snd (Suc (Suc x))) < Suc (Suc x)"
proof -
  let ?y = "Suc (Suc x)"
  have "?y > 1" by simp
  then have "c_snd ?y < ?y" by (rule c_snd_less_arg)
  moreover have "c_fst (c_snd ?y) \<le> c_snd ?y" by (rule c_fst_le_arg)
  ultimately show ?thesis by simp
qed

fun nat_to_sch :: "nat \<Rightarrow> PrimScheme" where
  "nat_to_sch 0 = Base_zero"
| "nat_to_sch (Suc 0) = Base_zero"
| "nat_to_sch x = (let u=mod7 (c_fst x); v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)"

primrec sch_to_nat :: "PrimScheme \<Rightarrow> nat" where
  "sch_to_nat Base_zero = 0"
| "sch_to_nat Base_suc = c_pair 1 0"
| "sch_to_nat Base_fst = c_pair 2 0"
| "sch_to_nat Base_snd = c_pair 3 0"
| "sch_to_nat (Comp_op t1 t2) = c_pair 4 (c_pair (sch_to_nat t1) (sch_to_nat t2))"
| "sch_to_nat (Pair_op t1 t2) = c_pair 5 (c_pair (sch_to_nat t1) (sch_to_nat t2))"
| "sch_to_nat (Rec_op t1 t2)  = c_pair 6 (c_pair (sch_to_nat t1) (sch_to_nat t2))"

lemma loc_srj_lm_1: "nat_to_sch (Suc (Suc x)) = (let u=mod7 (c_fst (Suc (Suc x))); v=c_snd (Suc (Suc x)); v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by simp

lemma loc_srj_lm_2: "x > 1 \<Longrightarrow> nat_to_sch x = (let u=mod7 (c_fst x); v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)"
proof -
  assume A1: "x > 1"
  let ?y = "x-(2::nat)"
  from A1 have S1: "x = Suc (Suc ?y)" by arith
  have S2: "nat_to_sch (Suc (Suc ?y)) = (let u=mod7 (c_fst (Suc (Suc ?y))); v=c_snd (Suc (Suc ?y)); v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (rule loc_srj_lm_1)
  from S1 S2 show ?thesis by simp
qed

lemma loc_srj_0: "nat_to_sch (c_pair 1 0) = Base_suc"
proof -
  let ?x = "c_pair 1 0"
  have S1: "?x = 2" by (simp add: c_pair_def sf_def)
  then have S2: "?x = Suc (Suc 0)" by simp
  let ?y = "Suc (Suc 0)"
  have S3: "nat_to_sch ?y = (let u=mod7 (c_fst ?y); v=c_snd ?y; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_1)
  have S4: "c_fst ?y = 1"
  proof -
    from S2 have "c_fst ?y = c_fst ?x" by simp
    then show ?thesis by simp
  qed
  have S5: "c_snd ?y = 0"
  proof -
    from S2 have "c_snd ?y = c_snd ?x" by simp
    then show ?thesis by simp
  qed
  from S4 have S6: "mod7 (c_fst ?y) = 1" by (simp add: mod7_def)
  from S3 S5 S6 have S9: "?R = loc_f 1 Base_zero Base_zero" by (simp add: Let_def c_fst_at_0 c_snd_at_0)
  then have S10: "?R = Base_suc" by (simp add: loc_f_def)
  with S3 have S11: "nat_to_sch ?y = Base_suc" by simp
  from S2 this show ?thesis by simp
qed

lemma nat_to_sch_at_2: "nat_to_sch 2 = Base_suc"
proof -
  have S1: "c_pair 1 0 = 2" by (simp add: c_pair_def sf_def)
  have S2: "nat_to_sch (c_pair 1 0) = Base_suc" by (rule loc_srj_0)
  from S1 S2 show ?thesis by simp
qed

lemma loc_srj_1: "nat_to_sch (c_pair 2 0) = Base_fst"
proof -
  let ?x = "c_pair 2 0"
  have S1: "?x = 5" by (simp add: c_pair_def sf_def)
  then have S2: "?x = Suc (Suc 3)" by simp
  let ?y = "Suc (Suc 3)"
  have S3: "nat_to_sch ?y = (let u=mod7 (c_fst ?y); v=c_snd ?y; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_1)
  have S4: "c_fst ?y = 2"
  proof -
    from S2 have "c_fst ?y = c_fst ?x" by simp
    then show ?thesis by simp
  qed
  have S5: "c_snd ?y = 0"
  proof -
    from S2 have "c_snd ?y = c_snd ?x" by simp
    then show ?thesis by simp
  qed
  from S4 have S6: "mod7 (c_fst ?y) = 2" by (simp add: mod7_def)
  from S3 S5 S6 have S9: "?R = loc_f 2 Base_zero Base_zero" by (simp add: Let_def c_fst_at_0 c_snd_at_0)
  then have S10: "?R = Base_fst" by (simp add: loc_f_def)
  with S3 have S11: "nat_to_sch ?y = Base_fst" by simp
  from S2 this show ?thesis by simp
qed

lemma loc_srj_2: "nat_to_sch (c_pair 3 0) = Base_snd"
proof -
  let ?x = "c_pair 3 0"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 3" by simp
  have S4: "c_snd ?x = 0" by simp
  from S3 have S6: "mod7 (c_fst ?x) = 3" by (simp add: mod7_def)
  from S3 S4 S6 have S7: "?R = loc_f 3 Base_zero Base_zero" by (simp add: Let_def c_fst_at_0 c_snd_at_0)
  then have S8: "?R = Base_snd" by (simp add: loc_f_def)
  with S2 have S10: "nat_to_sch ?x = Base_snd" by simp
  from S2 this show ?thesis by simp
qed

lemma loc_srj_3: "\<lbrakk>nat_to_sch (sch_to_nat sch1) = sch1; nat_to_sch (sch_to_nat sch2) = sch2\<rbrakk>
       \<Longrightarrow> nat_to_sch (c_pair 4 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))) = Comp_op sch1 sch2"
proof -
  assume A1: "nat_to_sch (sch_to_nat sch1) = sch1"
  assume A2: "nat_to_sch (sch_to_nat sch2) = sch2"
  let ?x = "c_pair 4 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 4" by simp
  have S4: "c_snd ?x = c_pair (sch_to_nat sch1) (sch_to_nat sch2)" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 4" by (simp add: mod7_def)
  from A1 A2 S4 S5 have "?R = Comp_op sch1 sch2" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

lemma loc_srj_3_1: "nat_to_sch (c_pair 4 (c_pair n1 n2)) = Comp_op (nat_to_sch n1) (nat_to_sch n2)"
proof -
  let ?x = "c_pair 4 (c_pair n1 n2)"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 4" by simp
  have S4: "c_snd ?x = c_pair n1 n2" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 4" by (simp add: mod7_def)
  from S4 S5 have "?R = Comp_op (nat_to_sch n1) (nat_to_sch n2)" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

lemma loc_srj_4: "\<lbrakk>nat_to_sch (sch_to_nat sch1) = sch1; nat_to_sch (sch_to_nat sch2) = sch2\<rbrakk>
       \<Longrightarrow> nat_to_sch (c_pair 5 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))) = Pair_op sch1 sch2"
proof -
  assume A1: "nat_to_sch (sch_to_nat sch1) = sch1"
  assume A2: "nat_to_sch (sch_to_nat sch2) = sch2"
  let ?x = "c_pair 5 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 5" by simp
  have S4: "c_snd ?x = c_pair (sch_to_nat sch1) (sch_to_nat sch2)" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 5" by (simp add: mod7_def)
  from A1 A2 S4 S5 have "?R = Pair_op sch1 sch2" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

lemma loc_srj_4_1: "nat_to_sch (c_pair 5 (c_pair n1 n2)) = Pair_op (nat_to_sch n1) (nat_to_sch n2)"
proof -
  let ?x = "c_pair 5 (c_pair n1 n2)"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 5" by simp
  have S4: "c_snd ?x = c_pair n1 n2" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 5" by (simp add: mod7_def)
  from S4 S5 have "?R = Pair_op (nat_to_sch n1) (nat_to_sch n2)" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

lemma loc_srj_5: "\<lbrakk>nat_to_sch (sch_to_nat sch1) = sch1; nat_to_sch (sch_to_nat sch2) = sch2\<rbrakk>
       \<Longrightarrow> nat_to_sch (c_pair 6 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))) = Rec_op sch1 sch2"
proof -
  assume A1: "nat_to_sch (sch_to_nat sch1) = sch1"
  assume A2: "nat_to_sch (sch_to_nat sch2) = sch2"
  let ?x = "c_pair 6 (c_pair (sch_to_nat sch1) (sch_to_nat sch2))"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 6" by simp
  have S4: "c_snd ?x = c_pair (sch_to_nat sch1) (sch_to_nat sch2)" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 6" by (simp add: mod7_def)
  from A1 A2 S4 S5 have "?R = Rec_op sch1 sch2" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

lemma loc_srj_5_1: "nat_to_sch (c_pair 6 (c_pair n1 n2)) = Rec_op (nat_to_sch n1) (nat_to_sch n2)"
proof -
  let ?x = "c_pair 6 (c_pair n1 n2)"
  have S1: "?x > 1" by (simp add: c_pair_def sf_def)
  from S1 have S2: "nat_to_sch ?x = (let u=mod7 (c_fst ?x); v=c_snd ?x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" (is "_ = ?R") by (rule loc_srj_lm_2)
  have S3: "c_fst ?x = 6" by simp
  have S4: "c_snd ?x = c_pair n1 n2" by simp
  from S3 have S5: "mod7 (c_fst ?x) = 6" by (simp add: mod7_def)
  from S4 S5 have "?R = Rec_op (nat_to_sch n1) (nat_to_sch n2)" by (simp add: Let_def c_fst_at_0 c_snd_at_0 loc_f_def)
  with S2 show ?thesis by simp
qed

theorem nat_to_sch_srj: "nat_to_sch (sch_to_nat sch) = sch"
apply(induct sch, auto simp add: loc_srj_0 loc_srj_1 loc_srj_2 loc_srj_3 loc_srj_4 loc_srj_5)
apply(insert loc_srj_0)
apply(simp)
done

subsection \<open>Indexes of primitive recursive functions of one variables\<close>

definition
  nat_to_pr :: "nat \<Rightarrow> (nat \<Rightarrow> nat)" where
  "nat_to_pr = (\<lambda> x. sch_to_pr (nat_to_sch x))"

theorem nat_to_pr_into_pr: "nat_to_pr n \<in> PrimRec1" by (simp add: nat_to_pr_def sch_to_pr_into_pr)

lemma nat_to_pr_srj: "f \<in> PrimRec1 \<Longrightarrow> (\<exists> n. f = nat_to_pr n)"
proof -
  assume "f \<in> PrimRec1"
  then have S1: "(\<exists> t. f = sch_to_pr t)" by (rule sch_to_pr_srj)
  from S1 obtain t where S2: "f = sch_to_pr t" ..
  let ?n = "sch_to_nat t"
  have S3: "nat_to_pr ?n = sch_to_pr (nat_to_sch ?n)" by (simp add: nat_to_pr_def)
  have S4: "nat_to_sch ?n = t" by (rule nat_to_sch_srj)
  from S3 S4 have S5: "nat_to_pr ?n = sch_to_pr t" by simp
  from S2 S5 have "nat_to_pr ?n = f" by simp
  then have "f = nat_to_pr ?n" by simp
  then show ?thesis ..
qed

lemma nat_to_pr_at_0: "nat_to_pr 0 = (\<lambda> x. 0)" by (simp add: nat_to_pr_def)

definition
  index_of_pr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat" where
  "index_of_pr f = (SOME n. f = nat_to_pr n)"

theorem index_of_pr_is_real: "f \<in> PrimRec1 \<Longrightarrow> nat_to_pr (index_of_pr f) = f"
proof -
  assume "f \<in> PrimRec1"
  hence "\<exists> n. f = nat_to_pr n" by (rule nat_to_pr_srj)
  hence "f = nat_to_pr (SOME n. f = nat_to_pr n)" by (rule someI_ex)
  thus ?thesis by (simp add: index_of_pr_def)
qed

definition
  comp_by_index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "comp_by_index = (\<lambda> n1 n2. c_pair 4 (c_pair n1 n2))"

definition
  pair_by_index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "pair_by_index = (\<lambda> n1 n2. c_pair 5 (c_pair n1 n2))"

definition
  rec_by_index :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "rec_by_index = (\<lambda> n1 n2. c_pair 6 (c_pair n1 n2))"

lemma comp_by_index_is_pr: "comp_by_index \<in> PrimRec2"
  unfolding comp_by_index_def
  using const_is_pr_2 [of 4] by prec

lemma comp_by_index_inj: "comp_by_index x1 y1 = comp_by_index x2 y2 \<Longrightarrow> x1=x2 \<and> y1=y2"
proof -
  assume "comp_by_index x1 y1 = comp_by_index x2 y2"
  hence "c_pair 4 (c_pair x1 y1) = c_pair 4 (c_pair x2 y2)" by (unfold comp_by_index_def)
  hence "c_pair x1 y1 = c_pair x2 y2" by (rule c_pair_inj2)
  thus ?thesis by (rule c_pair_inj)
qed

lemma comp_by_index_inj1: "comp_by_index x1 y1 = comp_by_index x2 y2 \<Longrightarrow> x1 = x2" by (frule comp_by_index_inj, drule conjunct1)

lemma comp_by_index_inj2: "comp_by_index x1 y1 = comp_by_index x2 y2 \<Longrightarrow> y1 = y2" by (frule comp_by_index_inj, drule conjunct2)

lemma comp_by_index_main: "nat_to_pr (comp_by_index n1 n2) = (\<lambda> x. (nat_to_pr n1) ((nat_to_pr n2) x))" by (unfold comp_by_index_def, unfold nat_to_pr_def, simp add: loc_srj_3_1)

lemma pair_by_index_is_pr: "pair_by_index \<in> PrimRec2" by (unfold pair_by_index_def, insert const_is_pr_2 [where ?n="(5::nat)"], prec)

lemma pair_by_index_inj: "pair_by_index x1 y1 = pair_by_index x2 y2 \<Longrightarrow> x1=x2 \<and> y1=y2"
proof -
  assume "pair_by_index x1 y1 = pair_by_index x2 y2"
  hence "c_pair 5 (c_pair x1 y1) = c_pair 5 (c_pair x2 y2)" by (unfold pair_by_index_def)
  hence "c_pair x1 y1 = c_pair x2 y2" by (rule c_pair_inj2)
  thus ?thesis by (rule c_pair_inj)
qed

lemma pair_by_index_inj1: "pair_by_index x1 y1 = pair_by_index x2 y2 \<Longrightarrow> x1 = x2" by (frule pair_by_index_inj, drule conjunct1)

lemma pair_by_index_inj2: "pair_by_index x1 y1 = pair_by_index x2 y2 \<Longrightarrow> y1 = y2" by (frule pair_by_index_inj, drule conjunct2)

lemma pair_by_index_main: "nat_to_pr (pair_by_index n1 n2) = c_f_pair (nat_to_pr n1) (nat_to_pr n2)" by (unfold pair_by_index_def, unfold nat_to_pr_def, simp add: loc_srj_4_1)

lemma nat_to_sch_of_pair_by_index [simp]: "nat_to_sch (pair_by_index n1 n2) = Pair_op (nat_to_sch n1) (nat_to_sch n2)"
  by (simp add: pair_by_index_def loc_srj_4_1)

lemma rec_by_index_is_pr: "rec_by_index \<in> PrimRec2" by (unfold rec_by_index_def, insert const_is_pr_2 [where ?n="(6::nat)"], prec)

lemma rec_by_index_inj: "rec_by_index x1 y1 = rec_by_index x2 y2 \<Longrightarrow> x1=x2 \<and> y1=y2"
proof -
  assume "rec_by_index x1 y1 = rec_by_index x2 y2"
  hence "c_pair 6 (c_pair x1 y1) = c_pair 6 (c_pair x2 y2)" by (unfold rec_by_index_def)
  hence "c_pair x1 y1 = c_pair x2 y2" by (rule c_pair_inj2)
  thus ?thesis by (rule c_pair_inj)
qed

lemma rec_by_index_inj1: "rec_by_index x1 y1 = rec_by_index x2 y2 \<Longrightarrow> x1 = x2" by (frule rec_by_index_inj, drule conjunct1)

lemma rec_by_index_inj2: "rec_by_index x1 y1 = rec_by_index x2 y2 \<Longrightarrow> y1 = y2" by (frule rec_by_index_inj, drule conjunct2)

lemma rec_by_index_main: "nat_to_pr (rec_by_index n1 n2) = UnaryRecOp (nat_to_pr n1) (nat_to_pr n2)" by (unfold rec_by_index_def, unfold nat_to_pr_def, simp add: loc_srj_5_1)

subsection \<open>s-1-1 theorem for primitive recursive functions of one variable\<close>

definition
  index_of_const :: "nat \<Rightarrow> nat" where
  "index_of_const = PrimRecOp1 0 (\<lambda> x y. c_pair 4 (c_pair 2 y))"

lemma index_of_const_is_pr: "index_of_const \<in> PrimRec1"
proof -
  have "(\<lambda> x y. c_pair (4::nat) (c_pair (2::nat) y)) \<in> PrimRec2" by (insert const_is_pr_2 [where ?n="(4::nat)"], prec)
  then show ?thesis by (simp add: index_of_const_def pr_rec1)
qed

lemma index_of_const_at_0: "index_of_const 0 = 0" by (simp add: index_of_const_def)

lemma index_of_const_at_suc: "index_of_const (Suc u) = c_pair 4 (c_pair 2 (index_of_const u))" by (unfold index_of_const_def, induct u, auto)

lemma index_of_const_main: "nat_to_pr (index_of_const n) = (\<lambda> x. n)" (is "?P n")
proof (induct n)
  show "?P 0" by (simp add: index_of_const_at_0 nat_to_pr_at_0)
next
  fix n assume "?P n"
  then show "?P (Suc n)" by ((simp add: index_of_const_at_suc nat_to_sch_at_2 nat_to_pr_def loc_srj_3_1))
qed

lemma index_of_const_lm_1: "(nat_to_pr (index_of_const n)) 0 = n" by (simp add: index_of_const_main)

lemma index_of_const_inj: "index_of_const n1 = index_of_const n2 \<Longrightarrow> n1 = n2"
proof -
  assume "index_of_const n1 = index_of_const n2"
  then have "(nat_to_pr (index_of_const n1)) 0  = (nat_to_pr (index_of_const n2)) 0" by simp
  thus ?thesis by (simp add: index_of_const_lm_1)
qed

definition "index_of_zero = sch_to_nat Base_zero"
definition "index_of_suc = sch_to_nat Base_suc"
definition "index_of_c_fst = sch_to_nat Base_fst"
definition "index_of_c_snd = sch_to_nat Base_snd"
definition "index_of_id = pair_by_index index_of_c_fst index_of_c_snd"

lemma index_of_zero_main: "nat_to_pr index_of_zero = (\<lambda> x. 0)" by (simp add: index_of_zero_def nat_to_pr_def)

lemma index_of_suc_main: "nat_to_pr index_of_suc = Suc"
apply(simp add: index_of_suc_def nat_to_pr_def)
apply(insert loc_srj_0)
apply(simp)
done

lemma index_of_c_fst_main: "nat_to_pr index_of_c_fst = c_fst" by (simp add: index_of_c_fst_def nat_to_pr_def loc_srj_1)

lemma [simp]: "nat_to_sch index_of_c_fst = Base_fst" by (unfold index_of_c_fst_def, rule nat_to_sch_srj)

lemma index_of_c_snd_main: "nat_to_pr index_of_c_snd = c_snd" by (simp add: index_of_c_snd_def nat_to_pr_def loc_srj_2)

lemma [simp]: "nat_to_sch index_of_c_snd = Base_snd" by (unfold index_of_c_snd_def, rule nat_to_sch_srj)

lemma index_of_id_main: "nat_to_pr index_of_id = (\<lambda> x. x)" by (simp add: index_of_id_def nat_to_pr_def c_f_pair_def)

definition
  index_of_c_pair_n :: "nat \<Rightarrow> nat" where
  "index_of_c_pair_n = (\<lambda> n. pair_by_index (index_of_const n) index_of_id)"

lemma index_of_c_pair_n_is_pr: "index_of_c_pair_n \<in> PrimRec1"
proof -
  have "(\<lambda> x. index_of_id) \<in> PrimRec1" by (rule const_is_pr)
  with pair_by_index_is_pr index_of_const_is_pr have "(\<lambda> n. pair_by_index (index_of_const n) index_of_id) \<in> PrimRec1" by prec
  then show ?thesis by (fold index_of_c_pair_n_def)
qed

lemma index_of_c_pair_n_main: "nat_to_pr (index_of_c_pair_n n) = (\<lambda> x. c_pair n x)"
proof -
  have "nat_to_pr (index_of_c_pair_n n) = nat_to_pr (pair_by_index (index_of_const n) index_of_id)" by (simp add: index_of_c_pair_n_def)
  also have "\<dots> = c_f_pair (nat_to_pr (index_of_const n)) (nat_to_pr index_of_id)" by (simp add: pair_by_index_main)
  also have "\<dots> = c_f_pair (\<lambda> x. n) (\<lambda> x. x)" by (simp add: index_of_const_main index_of_id_main)
  finally show ?thesis by (simp add: c_f_pair_def)
qed

lemma index_of_c_pair_n_inj: "index_of_c_pair_n x1 = index_of_c_pair_n x2 \<Longrightarrow> x1=x2"
proof -
  assume "index_of_c_pair_n x1 = index_of_c_pair_n x2"
  hence "pair_by_index (index_of_const x1) index_of_id = pair_by_index (index_of_const x2) index_of_id" by (unfold index_of_c_pair_n_def)
  hence "index_of_const x1 = index_of_const x2" by (rule pair_by_index_inj1)
  thus ?thesis by (rule index_of_const_inj)
qed

definition
  s1_1 :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "s1_1 = (\<lambda> n x. comp_by_index n (index_of_c_pair_n x))"

lemma s1_1_is_pr: "s1_1 \<in> PrimRec2" by (unfold s1_1_def, insert comp_by_index_is_pr index_of_c_pair_n_is_pr, prec)

theorem s1_1_th: "(\<lambda> y. (nat_to_pr n) (c_pair x y)) = nat_to_pr (s1_1 n x)"
proof -
  have "nat_to_pr (s1_1 n x) = nat_to_pr (comp_by_index n (index_of_c_pair_n x))" by (simp add: s1_1_def)
  also have "\<dots> = (\<lambda> z. (nat_to_pr n) ((nat_to_pr (index_of_c_pair_n x)) z))" by (simp add: comp_by_index_main)
  also have "\<dots> = (\<lambda> z. (nat_to_pr n) ((\<lambda> u. c_pair x u) z))" by (simp add: index_of_c_pair_n_main)
  finally show ?thesis by simp
qed

lemma s1_1_inj: "s1_1 x1 y1 = s1_1 x2 y2 \<Longrightarrow> x1=x2 \<and> y1=y2"
proof -
  assume "s1_1 x1 y1 = s1_1 x2 y2"
  then have "comp_by_index x1 (index_of_c_pair_n y1) = comp_by_index x2 (index_of_c_pair_n y2)" by (unfold s1_1_def)
  then have S1: "x1=x2 \<and> index_of_c_pair_n y1 = index_of_c_pair_n y2" by (rule comp_by_index_inj)
  then have S2: "x1=x2" ..
  from S1 have "index_of_c_pair_n y1 = index_of_c_pair_n y2" ..
  then have "y1 = y2" by (rule index_of_c_pair_n_inj)
  with S2 show ?thesis ..
qed

lemma s1_1_inj1: "s1_1 x1 y1 = s1_1 x2 y2 \<Longrightarrow> x1=x2" by (frule s1_1_inj, drule conjunct1)

lemma s1_1_inj2: "s1_1 x1 y1 = s1_1 x2 y2 \<Longrightarrow> y1=y2" by (frule s1_1_inj, drule conjunct2)

primrec
  pr_index_enumerator :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "pr_index_enumerator n 0 = n"
| "pr_index_enumerator n (Suc m) = comp_by_index index_of_id (pr_index_enumerator n m)"

theorem pr_index_enumerator_is_pr: "pr_index_enumerator \<in> PrimRec2"
proof -
  define g where "g x = x" for x :: nat
  have g_is_pr: "g \<in> PrimRec1" by (unfold g_def, rule pr_id1_1)
  define h where "h a b c = comp_by_index index_of_id b" for a b c :: nat
  from comp_by_index_is_pr have h_is_pr: "h \<in> PrimRec3" unfolding h_def by prec
  let ?f = "pr_index_enumerator"
  from g_def have f_at_0: "\<forall> x. ?f x 0 = g x" by auto
  from h_def have f_at_Suc: "\<forall> x y. ?f x (Suc y) = h x (?f x y) y" by auto
  from g_is_pr h_is_pr f_at_0 f_at_Suc show ?thesis by (rule pr_rec_last_scheme)
qed

lemma pr_index_enumerator_increase1: "pr_index_enumerator n m < pr_index_enumerator (n+1) m"
proof (induct m)
  show "pr_index_enumerator n 0 < pr_index_enumerator (n + 1) 0" by simp
  next fix na assume A: "pr_index_enumerator n na < pr_index_enumerator (n + 1) na"
  show "pr_index_enumerator n (Suc na) < pr_index_enumerator (n + 1) (Suc na)"
  proof -
    let ?a = "pr_index_enumerator n na"
    let ?b = "pr_index_enumerator (n+1) na"
    have S1: "pr_index_enumerator n (Suc na) = comp_by_index index_of_id ?a" by simp
    have L1: "pr_index_enumerator (n+1) (Suc na) = comp_by_index index_of_id ?b" by simp
    from A have "c_pair index_of_id ?a < c_pair index_of_id ?b" by (rule c_pair_strict_mono2)
    then have "c_pair 4 (c_pair index_of_id ?a) < c_pair 4 (c_pair index_of_id ?b)" by (rule c_pair_strict_mono2)
    then have "comp_by_index index_of_id ?a < c_pair 4 (c_pair index_of_id ?b)" by (simp add: comp_by_index_def)
    then have "comp_by_index index_of_id ?a < comp_by_index index_of_id ?b" by (simp add: comp_by_index_def)
    with S1 L1 show ?thesis by auto
  qed
qed

lemma pr_index_enumerator_increase2: "pr_index_enumerator n m < pr_index_enumerator n (m + 1)"
proof -
  let ?a = "pr_index_enumerator n m"
  have S1: "pr_index_enumerator n (m + 1) = comp_by_index index_of_id ?a" by simp
  have S2: "comp_by_index index_of_id ?a = c_pair 4 (c_pair index_of_id ?a)" by (simp add: comp_by_index_def)
  have S3: "4 + c_pair index_of_id ?a \<le> c_pair 4 (c_pair index_of_id ?a)" by (rule sum_le_c_pair)
  then have S4: "c_pair index_of_id ?a < c_pair 4 (c_pair index_of_id ?a)" by auto
  have S5: "?a \<le> c_pair index_of_id ?a" by (rule arg2_le_c_pair)
  from S4 S5 have S6: "?a < c_pair 4 (c_pair index_of_id ?a)" by auto
  with S1 S2 show ?thesis by auto
qed

lemma f_inc_mono: "(\<forall> (x::nat). (f::nat\<Rightarrow>nat) x < f (x+1)) \<Longrightarrow> \<forall> (x::nat) (y::nat). (x < y \<longrightarrow> f x < f y)"
proof (rule allI, rule allI)
  fix x y assume A: "\<forall> (x::nat). f x < f (x+1)" show " x < y \<longrightarrow> f x < f y"
  proof
    assume A1: "x < y"
    have L1: "\<And> u v. f u < f (u + (v+1))"
    proof -
      fix u v show "f u < f (u + (v+1))"
      proof (induct v)
        from A show "f u < f (u + (0 + 1))" by auto
      next
        fix v n
        assume A2: "f u < f (u + (n + 1))"
        from A have S1: "f (u + (n + 1)) < f (u + (Suc n + 1))" by auto
        from A2 S1 show " f u < f (u + (Suc n + 1))" by (rule less_trans)
      qed
    qed
  let ?v = "(y - x) - 1"
  from A1 have S2: "y = x + (?v + 1)" by auto
  have "f x < f (x + (?v + 1))" by (rule L1)
  with S2 show "f x < f y" by auto
  qed
qed

lemma pr_index_enumerator_mono1: "n1 < n2 \<Longrightarrow> pr_index_enumerator n1 m < pr_index_enumerator n2 m"
proof -
  assume A: "n1 < n2"
  define f where "f x = pr_index_enumerator x m" for x
  have f_inc: "\<forall> x. f x < f (x+1)"
  proof
    fix x show "f x < f (x+1)" by (unfold f_def, rule pr_index_enumerator_increase1)
  qed
  from f_inc have "\<forall> x y. (x < y \<longrightarrow> f x < f y)" by (rule f_inc_mono)
  with A f_def show ?thesis by auto
qed

lemma pr_index_enumerator_mono2: "m1 < m2 \<Longrightarrow> pr_index_enumerator n m1 < pr_index_enumerator n m2"
proof -
  assume A: "m1 < m2"
  define f where "f x = pr_index_enumerator n x" for x
  have f_inc: "\<forall> x. f x < f (x+1)"
  proof
    fix x show "f x < f (x+1)" by (unfold f_def, rule pr_index_enumerator_increase2)
  qed
  from f_inc have "\<forall> x y. (x < y \<longrightarrow> f x < f y)" by (rule f_inc_mono)
  with A f_def show ?thesis by auto
qed

lemma f_mono_inj: "\<forall> (x::nat) (y::nat). (x < y \<longrightarrow> (f::nat\<Rightarrow>nat) x < f y) \<Longrightarrow> \<forall> (x::nat) (y::nat). (f x = f y \<longrightarrow> x = y)"
proof (rule allI, rule allI)
  fix x y assume A: "\<forall>x y. x < y \<longrightarrow> f x < f y" show "f x = f y \<longrightarrow> x = y"
  proof
    assume A1: "f x = f y" show "x = y"
    proof (rule ccontr)
      assume A2: "x \<noteq> y" show False
      proof cases
        assume A3: "x < y"
        from A A3 have "f x < f y" by auto
        with A1 show False by auto
      next
        assume "\<not> x < y" with A2 have A4: "y < x" by auto
        from A A4 have "f y < f x" by auto
        with A1 show False by auto
      qed
    qed
  qed
qed

theorem pr_index_enumerator_inj1: "pr_index_enumerator n1 m = pr_index_enumerator n2 m \<Longrightarrow> n1 = n2"
proof -
  assume A: "pr_index_enumerator n1 m = pr_index_enumerator n2 m"
  define f where "f x = pr_index_enumerator x m" for x
  have f_mono: "\<forall> x y. (x < y \<longrightarrow> f x < f y)"
  proof (rule allI, rule allI)
    fix x y show "x < y \<longrightarrow> f x < f y" by (unfold f_def, simp add: pr_index_enumerator_mono1)
  qed
  from f_mono have "\<forall> x y. (f x = f y \<longrightarrow> x = y)" by (rule f_mono_inj)
  with A f_def show ?thesis by auto
qed

theorem pr_index_enumerator_inj2: "pr_index_enumerator n m1 = pr_index_enumerator n m2 \<Longrightarrow> m1 = m2"
proof -
  assume A: "pr_index_enumerator n m1 = pr_index_enumerator n m2"
  define f where "f x = pr_index_enumerator n x" for x
  have f_mono: "\<forall> x y. (x < y \<longrightarrow> f x < f y)"
  proof (rule allI, rule allI)
    fix x y show "x < y \<longrightarrow> f x < f y" by (unfold f_def, simp add: pr_index_enumerator_mono2)
  qed
  from f_mono have "\<forall> x y. (f x = f y \<longrightarrow> x = y)" by (rule f_mono_inj)
  with A f_def show ?thesis by auto
qed

theorem pr_index_enumerator_main: "nat_to_pr n = nat_to_pr (pr_index_enumerator n m)"
proof (induct m)
  show "nat_to_pr n = nat_to_pr (pr_index_enumerator n 0)" by simp
next
  fix na assume A: "nat_to_pr n = nat_to_pr (pr_index_enumerator n na)"
  show "nat_to_pr n = nat_to_pr (pr_index_enumerator n (Suc na))"
  proof -
    let ?a = "pr_index_enumerator n na"
    have S1: "pr_index_enumerator n (Suc na) = comp_by_index index_of_id ?a" by simp
    have "nat_to_pr (comp_by_index index_of_id ?a) = (\<lambda> x. (nat_to_pr index_of_id) (nat_to_pr ?a x))" by (rule comp_by_index_main)
    with index_of_id_main have "nat_to_pr (comp_by_index index_of_id ?a) = nat_to_pr ?a" by simp
    with A S1 show ?thesis by simp
  qed
qed

end
