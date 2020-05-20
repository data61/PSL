(*  Title:       The function which is universal for primitive recursive functions of one variable
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>The function which is universal for primitive recursive functions of one variable\<close>

theory PRecUnGr
imports PRecFun2 PRecList
begin

text \<open>
  We introduce a particular function which is universal for primitive
  recursive functions of one variable.
\<close>

definition
  g_comp :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g_comp c_ls key = (
    let n = c_fst key; x = c_snd key; m = c_snd n;
    m1 = c_fst m; m2 = c_snd m in
    \<comment> \<open>We have \<open>key = <n, x>; n = <?, m>; m = <m1, m2>\<close>.\<close>
    if c_assoc_have_key c_ls (c_pair m2 x) = 0 then
      (let y = c_assoc_value c_ls (c_pair m2 x) in
       if c_assoc_have_key c_ls (c_pair m1 y) = 0 then
         (let z = c_assoc_value c_ls (c_pair m1 y) in
         c_cons (c_pair key z) c_ls)
       else c_ls
      )
    else c_ls
  )"

definition
  g_pair :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g_pair c_ls key = (
    let n = c_fst key; x = c_snd key; m = c_snd n;
    m1 = c_fst m; m2 = c_snd m in
    \<comment> \<open>We have \<open>key = <n, x>; n = <?, m>; m = <m1, m2>\<close>.\<close>
    if c_assoc_have_key c_ls (c_pair m1 x) = 0 then
      (let y1 = c_assoc_value c_ls (c_pair m1 x) in
       if c_assoc_have_key c_ls (c_pair m2 x) = 0 then
         (let y2 = c_assoc_value c_ls (c_pair m2 x) in
         c_cons (c_pair key (c_pair y1 y2)) c_ls)
       else c_ls
      )
    else c_ls
  )"

definition
  g_rec :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g_rec c_ls key = (
    let n = c_fst key; x = c_snd key; m = c_snd n;
    m1 = c_fst m; m2 = c_snd m; y1 = c_fst x; x1 = c_snd x in
    \<comment> \<open>We have \<open>key = <n, x>; n = <?, m>; m = <m1, m2>; x = <y1, x1>\<close>.\<close>
    if y1 = 0 then
    (
      if c_assoc_have_key c_ls (c_pair m1 x1) = 0 then
        c_cons (c_pair key (c_assoc_value c_ls (c_pair m1 x1))) c_ls
      else c_ls
    )
    else
    (
     let y2 = y1-(1::nat) in
      if c_assoc_have_key c_ls (c_pair n (c_pair y2 x1)) = 0 then
      (   
        let t1 = c_assoc_value c_ls (c_pair n (c_pair y2 x1)); t2 = c_pair (c_pair y2 t1) x1 in
        if c_assoc_have_key c_ls (c_pair m2 t2) = 0 then
          c_cons (c_pair key (c_assoc_value c_ls (c_pair m2 t2))) c_ls
        else c_ls 
      )
      else c_ls
    )
  )"

definition
  g_step :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "g_step c_ls key = (
    let n = c_fst key; x = c_snd key; n1 = (c_fst n) mod 7 in
    if n1 = 0 then c_cons (c_pair key 0) c_ls else
    if n1 = 1 then c_cons (c_pair key (Suc x)) c_ls else
    if n1 = 2 then c_cons (c_pair key (c_fst x)) c_ls else
    if n1 = 3 then c_cons (c_pair key (c_snd x)) c_ls else
    if n1 = 4 then g_comp c_ls key else
    if n1 = 5 then g_pair c_ls key else
    if n1 = 6 then g_rec c_ls key else
    c_ls
  )"

definition
  pr_gr :: "nat \<Rightarrow> nat" where
  pr_gr_def: "pr_gr = PrimRecOp1 0 (\<lambda> a b. g_step b (c_fst a))"

lemma pr_gr_at_0: "pr_gr 0 = 0" by (simp add: pr_gr_def)

lemma pr_gr_at_Suc: "pr_gr (Suc x) = g_step (pr_gr x) (c_fst x)" by (simp add: pr_gr_def)

definition
  univ_for_pr :: "nat \<Rightarrow> nat" where
  "univ_for_pr = pr_conv_2_to_1 nat_to_pr"

theorem univ_is_not_pr: "univ_for_pr \<notin> PrimRec1"
proof (rule ccontr)
  assume "\<not> univ_for_pr \<notin> PrimRec1" then have A1: "univ_for_pr \<in> PrimRec1" by simp
  let ?f = "\<lambda> n. univ_for_pr (c_pair n n) + 1"
  let ?n0 = "index_of_pr ?f"
  from A1 have S1: "?f \<in> PrimRec1" by prec
  then have S2: "nat_to_pr ?n0 = ?f" by (rule index_of_pr_is_real)
  then have S3: "nat_to_pr ?n0 ?n0 = ?f ?n0" by simp
  have S4: "?f ?n0 = univ_for_pr (c_pair ?n0 ?n0) + 1" by simp
  from S3 S4 show False by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
qed

definition
  c_is_sub_fun :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool" where
  "c_is_sub_fun ls f \<longleftrightarrow> (\<forall> x. c_assoc_have_key ls x = 0 \<longrightarrow> c_assoc_value ls x = f x)"

lemma c_is_sub_fun_lm_1: "\<lbrakk> c_is_sub_fun ls f; c_assoc_have_key ls x = 0 \<rbrakk>  \<Longrightarrow> c_assoc_value ls x = f x"
apply(unfold c_is_sub_fun_def)
apply(auto)
done

lemma c_is_sub_fun_lm_2: "c_is_sub_fun ls f \<Longrightarrow> c_is_sub_fun (c_cons (c_pair x (f x)) ls) f"
proof -
  assume A1: "c_is_sub_fun ls f"
  show ?thesis
  proof (unfold c_is_sub_fun_def, rule allI, rule impI)
    fix xa assume A2: "c_assoc_have_key (c_cons (c_pair x (f x)) ls) xa = 0" show "c_assoc_value (c_cons (c_pair x (f x)) ls) xa = f xa"
    proof cases
      assume C1: "xa = x"
      then show "c_assoc_value (c_cons (c_pair x (f x)) ls) xa = f xa" by (simp add: PRecList.c_assoc_lm_2)
    next
      assume C2: "\<not> xa = x"
      then have S1: "c_assoc_have_key (c_cons (c_pair x (f x)) ls) xa = c_assoc_have_key ls xa" by (rule c_assoc_lm_3)
      from C2 have S2: "c_assoc_value (c_cons (c_pair x (f x)) ls) xa = c_assoc_value ls xa" by (rule c_assoc_lm_4)
      from A2 S1 have S3: "c_assoc_have_key ls xa = 0" by simp
      from A1 S3 have "c_assoc_value ls xa = f xa" by (rule c_is_sub_fun_lm_1)
      with S2 show ?thesis by simp
    qed
  qed
qed

lemma mod7_lm: "(n::nat) mod 7 = 0 \<or>
                (n::nat) mod 7 = 1 \<or>
                (n::nat) mod 7 = 2 \<or>
                (n::nat) mod 7 = 3 \<or>
                (n::nat) mod 7 = 4 \<or>
                (n::nat) mod 7 = 5 \<or>
                (n::nat) mod 7 = 6" by arith

lemma nat_to_sch_at_pos: "x > 0 \<Longrightarrow> nat_to_sch x = (let u=(c_fst x) mod 7; v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)"
proof -
  assume A: "x > 0"
  show ?thesis
  proof cases
    assume A1: "x = 1"
    then have S1: "c_fst x = 0"
    proof -
      have "1 = c_pair 0 1" by (simp add: c_pair_def sf_def)
      then have "c_fst 1 = c_fst (c_pair 0 1)" by simp
      then have "c_fst 1 = 0" by simp
      with A1 show ?thesis by simp
    qed
    from A1 have S2: "nat_to_sch x = Base_zero" by simp
    from S1 S2 show "nat_to_sch x = (let u=(c_fst x) mod 7; v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)"
    apply(insert S1 S2)
    apply(simp add: Let_def loc_f_def)
    done
  next
    assume "\<not> x = 1"
    from A this have A2: "x > 1" by simp
    from this have "nat_to_sch x = (let u=mod7 (c_fst x); v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (rule loc_srj_lm_2)
    from this show "nat_to_sch x = (let u=(c_fst x) mod 7; v=c_snd x; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: mod7_def)
  qed
qed

lemma nat_to_sch_0: "c_fst n mod 7 = 0 \<Longrightarrow> nat_to_sch n = Base_zero"
proof -
  assume A: "c_fst n mod 7 = 0"
  show ?thesis
  proof cases
    assume "n=0"
    then show "nat_to_sch n = Base_zero" by simp
  next
    assume "\<not> n = 0" then have "n > 0" by simp
    then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (rule nat_to_sch_at_pos)
    with A show "nat_to_sch n = Base_zero" by (simp add: Let_def loc_f_def)
  qed
qed

lemma loc_lm_1: "c_fst n mod 7 \<noteq> 0 \<Longrightarrow> n > 0"
proof -
  assume A: "c_fst n mod 7 \<noteq> 0"
  have "n = 0 \<Longrightarrow> False"
  proof -
    assume "n = 0"
    then have "c_fst n mod 7 = 0" by (simp add: c_fst_at_0)
    with A show ?thesis by simp
  qed
  then have "\<not> n = 0" by auto
  then show ?thesis by simp
qed

lemma loc_lm_2: "c_fst n mod 7 \<noteq> 0 \<Longrightarrow> nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)"
proof -
  assume "c_fst n mod 7 \<noteq> 0"
  then have "n > 0" by (rule loc_lm_1)
  then show ?thesis by (rule nat_to_sch_at_pos)
qed

lemma nat_to_sch_1: "c_fst n mod 7 = 1 \<Longrightarrow> nat_to_sch n = Base_suc"
proof -
  assume A1: "c_fst n mod 7 = 1"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Base_suc" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_sch_2: "c_fst n mod 7 = 2 \<Longrightarrow> nat_to_sch n = Base_fst"
proof -
  assume A1: "c_fst n mod 7 = 2"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Base_fst" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_sch_3: "c_fst n mod 7 = 3 \<Longrightarrow> nat_to_sch n = Base_snd"
proof -
  assume A1: "c_fst n mod 7 = 3"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Base_snd" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_sch_4: "c_fst n mod 7 = 4 \<Longrightarrow> nat_to_sch n = Comp_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))"
proof -
  assume A1: "c_fst n mod 7 = 4"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Comp_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_sch_5: "c_fst n mod 7 = 5 \<Longrightarrow> nat_to_sch n = Pair_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))"
proof -
  assume A1: "c_fst n mod 7 = 5"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Pair_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_sch_6: "c_fst n mod 7 = 6 \<Longrightarrow> nat_to_sch n = Rec_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))"
proof -
  assume A1: "c_fst n mod 7 = 6"
  then have "nat_to_sch n = (let u=(c_fst n) mod 7; v=c_snd n; v1=c_fst v; v2 = c_snd v; sch1=nat_to_sch v1; sch2=nat_to_sch v2 in loc_f u sch1 sch2)" by (simp add: loc_lm_2)
  with A1 show "nat_to_sch n = Rec_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (simp add: Let_def loc_f_def)
qed

lemma nat_to_pr_lm_0: "c_fst n mod 7 = 0 \<Longrightarrow> nat_to_pr n x = 0"
proof -
  assume A: "c_fst n mod 7 = 0"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Base_zero" by (rule nat_to_sch_0)
  from S1 S2 show ?thesis by simp
qed

lemma nat_to_pr_lm_1: "c_fst n mod 7 = 1 \<Longrightarrow> nat_to_pr n x = Suc x"
proof -
  assume A: "c_fst n mod 7 = 1"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Base_suc" by (rule nat_to_sch_1)
  from S1 S2 show ?thesis by simp
qed

lemma nat_to_pr_lm_2: "c_fst n mod 7 = 2 \<Longrightarrow> nat_to_pr n x = c_fst x"
proof -
  assume A: "c_fst n mod 7 = 2"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Base_fst" by (rule nat_to_sch_2)
  from S1 S2 show ?thesis by simp
qed

lemma nat_to_pr_lm_3: "c_fst n mod 7 = 3 \<Longrightarrow> nat_to_pr n x = c_snd x"
proof -
  assume A: "c_fst n mod 7 = 3"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Base_snd" by (rule nat_to_sch_3)
  from S1 S2 show ?thesis by simp
qed

lemma nat_to_pr_lm_4: "c_fst n mod 7 = 4 \<Longrightarrow> nat_to_pr n x = (nat_to_pr (c_fst (c_snd n)) (nat_to_pr (c_snd (c_snd n)) x))"
proof -
  assume A: "c_fst n mod 7 = 4"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Comp_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (rule nat_to_sch_4)
  from S1 S2 have S3: "nat_to_pr n x = sch_to_pr (Comp_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))) x" by simp
  from S3 have S4: "nat_to_pr n x = (sch_to_pr (nat_to_sch (c_fst (c_snd n)))) ((sch_to_pr (nat_to_sch (c_snd (c_snd n)))) x)" by simp
  from S4 show ?thesis by (simp add: nat_to_pr_def)
qed

lemma nat_to_pr_lm_5: "c_fst n mod 7 = 5 \<Longrightarrow> nat_to_pr n x = (c_f_pair (nat_to_pr (c_fst (c_snd n))) (nat_to_pr (c_snd (c_snd n)))) x"
proof -
  assume A: "c_fst n mod 7 = 5"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Pair_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (rule nat_to_sch_5)
  from S1 S2 have S3: "nat_to_pr n x = sch_to_pr (Pair_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))) x" by simp
  from S3 show ?thesis by (simp add: nat_to_pr_def)
qed

lemma nat_to_pr_lm_6: "c_fst n mod 7 = 6 \<Longrightarrow> nat_to_pr n x = (UnaryRecOp (nat_to_pr (c_fst (c_snd n))) (nat_to_pr (c_snd (c_snd n)))) x"
proof -
  assume A: "c_fst n mod 7 = 6"
  have S1: "nat_to_pr n x = sch_to_pr (nat_to_sch n) x" by (simp add: nat_to_pr_def)
  from A have S2: "nat_to_sch n = Rec_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))" by (rule nat_to_sch_6)
  from S1 S2 have S3: "nat_to_pr n x = sch_to_pr (Rec_op (nat_to_sch (c_fst (c_snd n))) (nat_to_sch (c_snd (c_snd n)))) x" by simp
  from S3 show ?thesis by (simp add: nat_to_pr_def)
qed

lemma univ_for_pr_lm_0: "c_fst (c_fst key) mod 7 = 0 \<Longrightarrow> univ_for_pr key = 0"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 0"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_0)
qed

lemma univ_for_pr_lm_1: "c_fst (c_fst key) mod 7 = 1 \<Longrightarrow> univ_for_pr key = Suc (c_snd key)"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 1"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_1)
qed

lemma univ_for_pr_lm_2: "c_fst (c_fst key) mod 7 = 2 \<Longrightarrow> univ_for_pr key = c_fst (c_snd key)"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 2"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_2)
qed

lemma univ_for_pr_lm_3: "c_fst (c_fst key) mod 7 = 3 \<Longrightarrow> univ_for_pr key = c_snd (c_snd key)"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 3"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_3)
qed

lemma univ_for_pr_lm_4: "c_fst (c_fst key) mod 7 = 4 \<Longrightarrow> univ_for_pr key = (nat_to_pr (c_fst (c_snd (c_fst key))) (nat_to_pr (c_snd (c_snd (c_fst key))) (c_snd key)))"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 4"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_4)
  (* nat_to_pr n x = (nat_to_pr (c_fst (c_snd (c_fst key))) (nat_to_pr (c_snd (c_snd (c_fst key))) (c_snd key))) *)
qed

lemma univ_for_pr_lm_4_1: "c_fst (c_fst key) mod 7 = 4 \<Longrightarrow> univ_for_pr key = univ_for_pr (c_pair (c_fst (c_snd (c_fst key))) (univ_for_pr (c_pair (c_snd (c_snd (c_fst key))) (c_snd key))))"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 4"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_4 univ_for_pr_def pr_conv_2_to_1_def)
qed

lemma univ_for_pr_lm_5: "c_fst (c_fst key) mod 7 = 5 \<Longrightarrow> univ_for_pr key = c_pair (univ_for_pr (c_pair (c_fst (c_snd (c_fst key))) (c_snd key))) (univ_for_pr (c_pair (c_snd (c_snd (c_fst key))) (c_snd key)))"
proof -
  assume A: "c_fst (c_fst key) mod 7 = 5"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A show ?thesis by (simp add: nat_to_pr_lm_5 c_f_pair_def univ_for_pr_def pr_conv_2_to_1_def)
qed

lemma univ_for_pr_lm_6_1: "\<lbrakk>c_fst (c_fst key) mod 7 = 6; c_fst (c_snd key) = 0\<rbrakk> \<Longrightarrow> univ_for_pr key = univ_for_pr (c_pair (c_fst (c_snd (c_fst key))) (c_snd (c_snd key)))"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 6"
  assume A2: "c_fst (c_snd key) = 0"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A1 A2 show ?thesis by (simp add: nat_to_pr_lm_6 UnaryRecOp_def univ_for_pr_def pr_conv_2_to_1_def)
qed

lemma univ_for_pr_lm_6_2: "\<lbrakk>c_fst (c_fst key) mod 7 = 6; c_fst (c_snd key) = Suc u\<rbrakk> \<Longrightarrow> univ_for_pr key = univ_for_pr
            (c_pair (c_snd (c_snd (c_fst key)))
              (c_pair (c_pair u (univ_for_pr (c_pair (c_fst key) (c_pair u (c_snd (c_snd key)))))) (c_snd (c_snd key))))"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 6"
  assume A2: "c_fst (c_snd key) = Suc u"
  have S1: "univ_for_pr key = nat_to_pr (c_fst key) (c_snd key)" by (simp add: univ_for_pr_def pr_conv_2_to_1_def)
  with A1 A2 show ?thesis 
  apply(simp add: nat_to_pr_lm_6 UnaryRecOp_def univ_for_pr_def pr_conv_2_to_1_def)
  apply(simp add: pr_conv_1_to_3_def)
  done
qed

lemma univ_for_pr_lm_6_3: "\<lbrakk>c_fst (c_fst key) mod 7 = 6; c_fst (c_snd key) \<noteq> 0\<rbrakk> \<Longrightarrow> univ_for_pr key = univ_for_pr
            (c_pair (c_snd (c_snd (c_fst key)))
              (c_pair (c_pair (c_fst (c_snd key) - 1) (univ_for_pr (c_pair (c_fst key) (c_pair (c_fst (c_snd key) - 1) (c_snd (c_snd key)))))) (c_snd (c_snd key))))"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 6"
  assume A2: "c_fst (c_snd key) \<noteq> 0" then have 
  A3: "c_fst (c_snd key) > 0" by simp
  let ?u = "c_fst (c_snd key) - (1::nat)"
  from A3 have S1: "c_fst (c_snd key) = Suc ?u" by simp
  from A1 S1 have S2: "univ_for_pr key = univ_for_pr
            (c_pair (c_snd (c_snd (c_fst key)))
              (c_pair (c_pair ?u (univ_for_pr (c_pair (c_fst key) (c_pair ?u (c_snd (c_snd key)))))) (c_snd (c_snd key))))" by (rule univ_for_pr_lm_6_2)
  thus ?thesis by simp
qed

lemma g_comp_lm_0: "\<lbrakk> c_fst (c_fst key) mod 7 = 4; c_is_sub_fun ls univ_for_pr; g_comp ls key \<noteq> ls\<rbrakk> \<Longrightarrow> g_comp ls key = c_cons (c_pair key (univ_for_pr key)) ls"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 4"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  assume A3: "g_comp ls key \<noteq> ls"
  let ?n = "c_fst key"
  let ?x = "c_snd key"
  let ?m = "c_snd ?n"
  let ?m1 = "c_fst ?m"
  let ?m2 = "c_snd ?m"
  let ?k1 = "c_pair ?m2 ?x"
  have S1: "c_assoc_have_key ls ?k1 = 0"
  proof (rule ccontr)
    assume A1_1: "c_assoc_have_key ls ?k1 \<noteq> 0"
    then have "g_comp ls key = ls" by(simp add: g_comp_def)
    with A3 show False by simp
  qed
  let ?y = "c_assoc_value ls ?k1"
  from A2 S1 have S2: "?y = univ_for_pr ?k1" by (rule c_is_sub_fun_lm_1)
  let ?k2 = "c_pair ?m1 ?y"
  have S3: "c_assoc_have_key ls ?k2 = 0"
  proof (rule ccontr)
    assume A3_1: "c_assoc_have_key ls ?k2 \<noteq> 0"
    then have "g_comp ls key = ls" by (simp add: g_comp_def Let_def)
    with A3 show False by simp
  qed
  let ?z = "c_assoc_value ls ?k2"
  from A2 S3 have S4: "?z = univ_for_pr ?k2" by (rule c_is_sub_fun_lm_1)
  from S2 have S5: "?k2 = c_pair ?m1 (univ_for_pr ?k1)" by simp
  from S4 S5 have S6: "?z = univ_for_pr (c_pair ?m1 (univ_for_pr ?k1))" by simp
  from A1 S6 have S7: "?z = univ_for_pr key" by (simp add: univ_for_pr_lm_4_1)
  from S1 S3 S7 show ?thesis by (simp add: g_comp_def Let_def)
qed

lemma g_comp_lm_1: "\<lbrakk> c_fst (c_fst key) mod 7 = 4; c_is_sub_fun ls univ_for_pr\<rbrakk> \<Longrightarrow> c_is_sub_fun (g_comp ls key) univ_for_pr"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 4"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  show ?thesis
  proof cases
    assume "g_comp ls key = ls"
    with A2 show "c_is_sub_fun (g_comp ls key) univ_for_pr" by simp
  next  
    assume "g_comp ls key \<noteq> ls"
    from A1 A2 this have S1: "g_comp ls key = c_cons (c_pair key (univ_for_pr key)) ls" by (rule g_comp_lm_0)
    with A2 show "c_is_sub_fun (g_comp ls key) univ_for_pr" by (simp add: c_is_sub_fun_lm_2)
  qed
qed

lemma g_pair_lm_0: "\<lbrakk> c_fst (c_fst key) mod 7 = 5; c_is_sub_fun ls univ_for_pr; g_pair ls key \<noteq> ls\<rbrakk> \<Longrightarrow> g_pair ls key = c_cons (c_pair key (univ_for_pr key)) ls"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 5"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  assume A3: "g_pair ls key \<noteq> ls"
  let ?n = "c_fst key"
  let ?x = "c_snd key"
  let ?m = "c_snd ?n"
  let ?m1 = "c_fst ?m"
  let ?m2 = "c_snd ?m"
  let ?k1 = "c_pair ?m1 ?x"
  have S1: "c_assoc_have_key ls ?k1 = 0"
  proof (rule ccontr)
    assume A1_1: "c_assoc_have_key ls ?k1 \<noteq> 0"
    then have "g_pair ls key = ls" by(simp add: g_pair_def)
    with A3 show False by simp
  qed
  let ?y1 = "c_assoc_value ls ?k1"
  from A2 S1 have S2: "?y1 = univ_for_pr ?k1" by (rule c_is_sub_fun_lm_1)
  let ?k2 = "c_pair ?m2 ?x"
  have S3: "c_assoc_have_key ls ?k2 = 0"
  proof (rule ccontr)
    assume A3_1: "c_assoc_have_key ls ?k2 \<noteq> 0"
    then have "g_pair ls key = ls" by (simp add: g_pair_def Let_def)
    with A3 show False by simp
  qed
  let ?y2 = "c_assoc_value ls ?k2"
  from A2 S3 have S4: "?y2 = univ_for_pr ?k2" by (rule c_is_sub_fun_lm_1)
  let ?z = "c_pair ?y1 ?y2"
  from S2 S4 have S5: "?z = c_pair (univ_for_pr ?k1) (univ_for_pr ?k2)" by simp
  from A1 S5 have S6: "?z = univ_for_pr key" by (simp add: univ_for_pr_lm_5)
  from S1 S3 S6 show ?thesis by (simp add: g_pair_def Let_def)
qed

lemma g_pair_lm_1: "\<lbrakk> c_fst (c_fst key) mod 7 = 5; c_is_sub_fun ls univ_for_pr\<rbrakk> \<Longrightarrow> c_is_sub_fun (g_pair ls key) univ_for_pr"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 5"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  show ?thesis
  proof cases
    assume "g_pair ls key = ls"
    with A2 show "c_is_sub_fun (g_pair ls key) univ_for_pr" by simp
  next  
    assume "g_pair ls key \<noteq> ls"
    from A1 A2 this have S1: "g_pair ls key = c_cons (c_pair key (univ_for_pr key)) ls" by (rule g_pair_lm_0)
    with A2 show "c_is_sub_fun (g_pair ls key) univ_for_pr" by (simp add: c_is_sub_fun_lm_2)
  qed
qed

lemma g_rec_lm_0: "\<lbrakk> c_fst (c_fst key) mod 7 = 6; c_is_sub_fun ls univ_for_pr; g_rec ls key \<noteq> ls\<rbrakk> \<Longrightarrow> g_rec ls key = c_cons (c_pair key (univ_for_pr key)) ls"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 6"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  assume A3: "g_rec ls key \<noteq> ls"
  let ?n = "c_fst key"
  let ?x = "c_snd key"
  let ?m = "c_snd ?n"
  let ?m1 = "c_fst ?m"
  let ?m2 = "c_snd ?m"
  let ?y1 = "c_fst ?x"
  let ?x1 = "c_snd ?x"
  show ?thesis
  proof cases
    assume A1_1: "?y1 = 0"
    let ?k1 = "c_pair ?m1 ?x1"
    have S1_1: "c_assoc_have_key ls ?k1 = 0"
    proof (rule ccontr)
      assume "c_assoc_have_key ls ?k1 \<noteq> 0"
      with A1_1 have "g_rec ls key = ls" by(simp add: g_rec_def)
      with A3 show False by simp
    qed
    let ?v = "c_assoc_value ls ?k1"
    from A2 S1_1 have S1_2: "?v = univ_for_pr ?k1" by (rule c_is_sub_fun_lm_1)
    from A1 A1_1 S1_2 have S1_3: "?v = univ_for_pr key" by (simp add: univ_for_pr_lm_6_1)
    from A1_1 S1_1 S1_3 show ?thesis by (simp add: g_rec_def Let_def)
  next
    assume A2_1: "?y1 \<noteq> 0" then have A2_2: "?y1 > 0" by simp
    let ?y2 = "?y1 - (1::nat)"
    let ?k2 = "c_pair ?n (c_pair ?y2 ?x1)"
    have S2_1: "c_assoc_have_key ls ?k2 = 0"
    proof (rule ccontr)
      assume "c_assoc_have_key ls ?k2 \<noteq> 0"
      with A2_1 have "g_rec ls key = ls" by (simp add: g_rec_def Let_def)
      with A3 show False by simp
    qed
    let ?t1 = "c_assoc_value ls ?k2"
    from A2 S2_1 have S2_2: "?t1 = univ_for_pr ?k2" by (rule c_is_sub_fun_lm_1)
    let ?t2 = "c_pair (c_pair ?y2 ?t1) ?x1"
    let ?k3 = "c_pair ?m2 ?t2"
    have S2_3: "c_assoc_have_key ls ?k3 = 0"
    proof (rule ccontr)
      assume "c_assoc_have_key ls ?k3 \<noteq> 0"
      with A2_1 have "g_rec ls key = ls" by (simp add: g_rec_def Let_def)
      with A3 show False by simp
    qed
    let ?u = "c_assoc_value ls ?k3"
    from A2 S2_3 have S2_4: "?u = univ_for_pr ?k3" by (rule c_is_sub_fun_lm_1)
    from S2_4 S2_2 have S2_5: "?u = univ_for_pr (c_pair ?m2 (c_pair (c_pair ?y2 (univ_for_pr ?k2)) ?x1))" by simp
    from A1 A2_1 S2_5 have S2_6: "?u = univ_for_pr key" by (simp add: univ_for_pr_lm_6_3)
    from A2_1 S2_1 S2_3 S2_6 show ?thesis by (simp add: g_rec_def Let_def)
  qed
qed

lemma g_rec_lm_1: "\<lbrakk> c_fst (c_fst key) mod 7 = 6; c_is_sub_fun ls univ_for_pr\<rbrakk> \<Longrightarrow> c_is_sub_fun (g_rec ls key) univ_for_pr"
proof -
  assume A1: "c_fst (c_fst key) mod 7 = 6"
  assume A2: "c_is_sub_fun ls univ_for_pr"
  show ?thesis
  proof cases
    assume "g_rec ls key = ls"
    with A2 show "c_is_sub_fun (g_rec ls key) univ_for_pr" by simp
  next  
    assume "g_rec ls key \<noteq> ls"
    from A1 A2 this have S1: "g_rec ls key = c_cons (c_pair key (univ_for_pr key)) ls" by (rule g_rec_lm_0)
    with A2 show "c_is_sub_fun (g_rec ls key) univ_for_pr" by (simp add: c_is_sub_fun_lm_2)
  qed
qed

lemma g_step_lm_0: "c_fst (c_fst key) mod 7 = 0 \<Longrightarrow> g_step ls key = c_cons (c_pair key 0) ls" by (simp add: g_step_def)

lemma g_step_lm_1: "c_fst (c_fst key) mod 7 = 1 \<Longrightarrow> g_step ls key = c_cons (c_pair key (Suc (c_snd key))) ls" by (simp add: g_step_def Let_def)

lemma g_step_lm_2: "c_fst (c_fst key) mod 7 = 2 \<Longrightarrow> g_step ls key = c_cons (c_pair key (c_fst (c_snd key))) ls" by (simp add: g_step_def Let_def)

lemma g_step_lm_3: "c_fst (c_fst key) mod 7 = 3 \<Longrightarrow> g_step ls key = c_cons (c_pair key (c_snd (c_snd key))) ls" by (simp add: g_step_def Let_def)

lemma g_step_lm_4: "c_fst (c_fst key) mod 7 = 4 \<Longrightarrow> g_step ls key = g_comp ls key" by (simp add: g_step_def)

lemma g_step_lm_5: "c_fst (c_fst key) mod 7 = 5 \<Longrightarrow> g_step ls key = g_pair ls key" by (simp add: g_step_def)

lemma g_step_lm_6: "c_fst (c_fst key) mod 7 = 6 \<Longrightarrow> g_step ls key = g_rec ls key" by (simp add: g_step_def)

lemma g_step_lm_7: "c_is_sub_fun ls univ_for_pr \<Longrightarrow> c_is_sub_fun (g_step ls key) univ_for_pr"
proof -
  assume A1: "c_is_sub_fun ls univ_for_pr"
  let ?n = "c_fst key"
  let ?x = "c_snd key"
  let ?n1 = "(c_fst ?n) mod 7"
  have S1: "?n1 = 0 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 0"
    then have S1_1: "g_step ls key = c_cons (c_pair key 0) ls" by (rule g_step_lm_0)
    from A have S1_2: "univ_for_pr key = 0" by (rule univ_for_pr_lm_0)
    from A1 have S1_3: "c_is_sub_fun (c_cons (c_pair key (univ_for_pr key)) ls) univ_for_pr" by (rule c_is_sub_fun_lm_2)
    from S1_3 S1_1 S1_2 show ?thesis by simp
  qed
  have S2: "?n1 = 1 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 1"
    then have S2_1: "g_step ls key = c_cons (c_pair key (Suc (c_snd key))) ls" by (rule g_step_lm_1)
    from A have S2_2: "univ_for_pr key = Suc (c_snd key)" by (rule univ_for_pr_lm_1)
    from A1 have S2_3: "c_is_sub_fun (c_cons (c_pair key (univ_for_pr key)) ls) univ_for_pr" by (rule c_is_sub_fun_lm_2)
    from S2_3 S2_1 S2_2 show ?thesis by simp
  qed
  have S3: "?n1 = 2 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 2"
    then have S2_1: "g_step ls key = c_cons (c_pair key (c_fst (c_snd key))) ls" by (rule g_step_lm_2)
    from A have S2_2: "univ_for_pr key = c_fst (c_snd key)" by (rule univ_for_pr_lm_2)
    from A1 have S2_3: "c_is_sub_fun (c_cons (c_pair key (univ_for_pr key)) ls) univ_for_pr" by (rule c_is_sub_fun_lm_2)
    from S2_3 S2_1 S2_2 show ?thesis by simp
  qed
  have S4: "?n1 = 3 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 3"
    then have S2_1: "g_step ls key = c_cons (c_pair key (c_snd (c_snd key))) ls" by (rule g_step_lm_3)
    from A have S2_2: "univ_for_pr key = c_snd (c_snd key)" by (rule univ_for_pr_lm_3)
    from A1 have S2_3: "c_is_sub_fun (c_cons (c_pair key (univ_for_pr key)) ls) univ_for_pr" by (rule c_is_sub_fun_lm_2)
    from S2_3 S2_1 S2_2 show ?thesis by simp
  qed
  have S5: "?n1 = 4 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 4"
    then have S2_1: "g_step ls key = g_comp ls key" by (rule g_step_lm_4)
    from A A1 S2_1 show ?thesis by (simp add: g_comp_lm_1)
  qed
  have S6: "?n1 = 5 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 5"
    then have S2_1: "g_step ls key = g_pair ls key" by (rule g_step_lm_5)
    from A A1 S2_1 show ?thesis by (simp add: g_pair_lm_1)
  qed
  have S7: "?n1 = 6 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 6"
    then have S2_1: "g_step ls key = g_rec ls key" by (rule g_step_lm_6)
    from A A1 S2_1 show ?thesis by (simp add: g_rec_lm_1)
  qed
  have S8: "?n1=0 \<or> ?n1=1 \<or> ?n1=2 \<or> ?n1=3 \<or> ?n1=4 \<or> ?n1=5 \<or> ?n1=6" by (rule mod7_lm)
  with S1 S2 S3 S4 S5 S6 S7 show ?thesis by fast
qed

theorem pr_gr_1: "c_is_sub_fun (pr_gr x) univ_for_pr"
apply(induct x)
apply(simp add: pr_gr_at_0 c_is_sub_fun_def c_assoc_have_key_df)
apply(simp add: pr_gr_at_Suc)
apply(simp add: g_step_lm_7)
done

lemma comp_next: "g_comp ls key = ls \<or> c_tl (g_comp ls key) = ls" by(simp add: g_comp_def Let_def)
lemma pair_next: "g_pair ls key = ls \<or> c_tl (g_pair ls key) = ls" by(simp add: g_pair_def Let_def)
lemma rec_next: "g_rec ls key = ls \<or> c_tl (g_rec ls key) = ls" by(simp add: g_rec_def Let_def)

lemma step_next: "g_step ls key = ls \<or> c_tl (g_step ls key) = ls"
apply(simp add: g_step_def comp_next pair_next rec_next Let_def)
(* (* apply(simp add: g_step_def g_comp_def g_pair_def g_rec_def Let_def) *)*)
done

lemma lm1: "pr_gr (Suc x) = pr_gr x \<or> c_tl (pr_gr (Suc x)) = pr_gr x" by(simp add: pr_gr_at_Suc step_next)

lemma c_assoc_have_key_pos: "c_assoc_have_key ls x = 0 \<Longrightarrow> ls > 0"
proof -
  assume A1: "c_assoc_have_key ls x = 0"
  thus ?thesis
  proof (cases)
    assume A2: "ls = 0"
    then have S1: "c_assoc_have_key ls x = 1" by (simp add: c_assoc_have_key_df)
    with A1 have S2: False by auto
    then show "ls > 0" by auto
  next
    assume A3: "\<not> ls = 0"
    then show "ls > 0" by auto
  qed
qed

lemma lm2: "c_assoc_have_key (c_tl ls) key = 0 \<Longrightarrow> c_assoc_have_key ls key = 0"
proof -
  assume A1: "c_assoc_have_key (c_tl ls) key = 0"
  from A1 have S1: "c_tl ls > 0" by (rule c_assoc_have_key_pos)
  have S2: "c_tl ls \<le> ls" by (rule c_tl_le)
  from S1 S2 have S3: "ls \<noteq> 0" by auto
  from A1 S3 show ?thesis by (auto simp add: c_assoc_have_key_lm_1)
qed

lemma lm3: "c_assoc_have_key (pr_gr x) key = 0 \<Longrightarrow> c_assoc_have_key (pr_gr (Suc x)) key = 0"
proof -
  assume A1: "c_assoc_have_key (pr_gr x) key = 0"
  have S1: "pr_gr (Suc x) = pr_gr x \<or> c_tl (pr_gr (Suc x)) = pr_gr x" by (rule lm1)
  from A1 have S2: "pr_gr (Suc x) = pr_gr x \<Longrightarrow> ?thesis" by auto
  have S3: "c_tl (pr_gr (Suc x)) = pr_gr x \<Longrightarrow> ?thesis"
  proof -
    assume "c_tl (pr_gr (Suc x)) = pr_gr x" (is "c_tl ?ls = _")
    with A1 have "c_assoc_have_key (c_tl ?ls) key = 0" by auto
    then show "c_assoc_have_key ?ls key = 0" by (rule lm2)
  qed
  from S1 S2 S3 show ?thesis by auto
qed

lemma lm4: "\<lbrakk> c_assoc_have_key (pr_gr x) key = 0; 0 \<le> y\<rbrakk> \<Longrightarrow> c_assoc_have_key (pr_gr (x+y)) key = 0"
apply(induct_tac y)
apply(auto)
apply(simp add: lm3)
done

lemma lm5: "\<lbrakk> c_assoc_have_key (pr_gr x) key = 0; x \<le> y \<rbrakk> \<Longrightarrow> c_assoc_have_key (pr_gr y) key = 0"
proof -
  assume A1: "c_assoc_have_key (pr_gr x) key = 0"
  assume A2: "x \<le> y"
  let ?z = "y-x"
  from A2 have S1: "0 \<le> ?z" by auto
  from A2 have S2: "y = x + ?z" by auto
  from A1 S1 have S3: "c_assoc_have_key (pr_gr (x+?z)) key = 0" by (rule lm4)
  from S2 S3 show ?thesis by auto
qed

lemma loc_upb_lm_1: "n = 0 \<Longrightarrow> (c_fst n) mod 7 = 0"
apply(simp add: c_fst_at_0)
done

lemma loc_upb_lm_2: "(c_fst n) mod 7 > 1 \<Longrightarrow> c_snd n < n"
proof -
  assume A1: "c_fst n mod 7 > 1"
  from A1 have S1: "1 < c_fst n" by simp
  have S2: "c_fst n \<le> n" by (rule c_fst_le_arg)
  from S1 S2 have S3: "1 < n" by simp
  from S3 have S4: "n>1" by simp
  from S4 show ?thesis by (rule c_snd_less_arg)
qed

lemma loc_upb_lm_2_0: "(c_fst n) mod 7 = 4 \<longrightarrow> c_fst (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 4"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_fst (c_snd n) \<le>  c_snd n" by (rule c_fst_le_arg)
  from S1 S2 show "c_fst (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_2: "(c_fst n) mod 7 = 4 \<longrightarrow> c_snd (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 4"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_snd (c_snd n) \<le>  c_snd n" by (rule c_snd_le_arg)
  from S1 S2 show "c_snd (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_3: "(c_fst n) mod 7 = 5 \<longrightarrow> c_fst (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 5"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_fst (c_snd n) \<le>  c_snd n" by (rule c_fst_le_arg)
  from S1 S2 show "c_fst (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_4: "(c_fst n) mod 7 = 5 \<longrightarrow> c_snd (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 5"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_snd (c_snd n) \<le>  c_snd n" by (rule c_snd_le_arg)
  from S1 S2 show "c_snd (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_5: "(c_fst n) mod 7 = 6 \<longrightarrow> c_fst (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 6"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_fst (c_snd n) \<le>  c_snd n" by (rule c_fst_le_arg)
  from S1 S2 show "c_fst (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_6: "(c_fst n) mod 7 = 6 \<longrightarrow> c_snd (c_snd n) < n"
proof
  assume A1: "c_fst n mod 7 = 6"
  then have S0: "c_fst n mod 7 > 1" by auto
  then have S1: "c_snd n < n" by (rule loc_upb_lm_2)
  have S2: "c_snd (c_snd n) \<le>  c_snd n" by (rule c_snd_le_arg)
  from S1 S2 show "c_snd (c_snd n) < n" by auto
qed

lemma loc_upb_lm_2_7: "\<lbrakk>y2 = y1 - (1::nat); 0 < y1; x1 = c_snd x; y1 = c_fst x\<rbrakk> \<Longrightarrow> c_pair y2 x1 < x"
proof -
  assume A1: "y2 = y1 - (1::nat)" and A2: "0 < y1" and A3: "x1 = c_snd x" and A4: "y1 = c_fst x"
  from A1 A2 have S1: "y2 < y1" by auto
  from S1 have S2: "c_pair y2 x1 < c_pair y1 x1" by (rule c_pair_strict_mono1)
  from A3 A4 have S3: "c_pair y1 x1 = x" by auto
  from S2 S3 show "c_pair y2 x1 < x" by auto
qed

function loc_upb :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  aa: "loc_upb n x = (
     let n1 = (c_fst n) mod 7 in
       if n1 = 0 then (c_pair (c_pair n x) 0) + 1 else
       if n1 = 1 then (c_pair (c_pair n x) 0) + 1 else
       if n1 = 2 then (c_pair (c_pair n x) 0) + 1 else
       if n1 = 3 then (c_pair (c_pair n x) 0) + 1 else
       if n1 = 4 then (
       let m = c_snd n; m1 = c_fst m; m2 = c_snd m;
       y = c_assoc_value (pr_gr (loc_upb m2 x)) (c_pair m2 x) in
         (c_pair (c_pair n x) (loc_upb m2 x + loc_upb m1 y)) + 1
       ) else
       if n1 = 5 then (
       let m = c_snd n; m1 = c_fst m; m2 = c_snd m in
         (c_pair (c_pair n x) (loc_upb m1 x + loc_upb m2 x)) + 1
       ) else
       if n1 = 6 then (
       let m = c_snd n; m1 = c_fst m; m2 = c_snd m; y1 = c_fst x; x1 = c_snd x in
         if y1 = 0 then (
           (c_pair (c_pair n x) (loc_upb m1 x1)) + 1
         ) else (
           let y2 = y1-(1::nat);
             t1 = c_assoc_value (pr_gr (loc_upb n (c_pair y2 x1))) (c_pair n (c_pair y2 x1)); t2 = c_pair (c_pair y2 t1) x1 in
             (c_pair (c_pair n x) (loc_upb n (c_pair y2 x1) + loc_upb m2 t2)) + 1
         )
       )
       else 0
 )"
by auto

termination
apply (relation "measure (\<lambda> m. m) <*lex*> measure (\<lambda> n. n)")
apply (simp_all add: loc_upb_lm_2_0 loc_upb_lm_2_2 loc_upb_lm_2_3 loc_upb_lm_2_4 loc_upb_lm_2_5 loc_upb_lm_2_6 loc_upb_lm_2_7)
apply auto
done

definition
  lex_p :: "((nat \<times> nat) \<times> nat \<times> nat) set" where
  "lex_p = ((measure (\<lambda> m. m)) <*lex*> (measure (\<lambda> n. n)))"

lemma wf_lex_p: "wf(lex_p)"
apply(simp add: lex_p_def)
apply(auto)
done

lemma lex_p_eq: "((n',x'), (n,x)) \<in> lex_p = (n'<n \<or> n'=n \<and> x'<x) "
apply(simp add: lex_p_def)
done

lemma loc_upb_lex_0: "c_fst n mod 7 = 0 \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "c_fst n mod 7 = 0"
  let ?key = "c_pair n x"
  let ?s = "c_pair ?key 0"
  let ?ls = "pr_gr ?s"
  from A1 have "loc_upb n x = ?s + 1" by simp
  then have S1: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
  from A1 have S2: "g_step ?ls ?key = c_cons (c_pair ?key 0) ?ls" by (simp add: g_step_def)
  from S1 S2 have "pr_gr (loc_upb n x) = c_cons (c_pair ?key 0) ?ls" by auto
  thus ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_lex_1: "c_fst n mod 7 = 1 \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "c_fst n mod 7 = 1"
  let ?key = "c_pair n x"
  let ?s = "c_pair ?key 0"
  let ?ls = "pr_gr ?s"
  from A1 have "loc_upb n x = ?s + 1" by simp
  then have S1: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
  from A1 have S2: "g_step ?ls ?key = c_cons (c_pair ?key (Suc x)) ?ls" by (simp add: g_step_def)
  from S1 S2 have "pr_gr (loc_upb n x) = c_cons (c_pair ?key (Suc x)) ?ls" by auto
  thus ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_lex_2: "c_fst n mod 7 = 2 \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "c_fst n mod 7 = 2"
  let ?key = "c_pair n x"
  let ?s = "c_pair ?key 0"
  let ?ls = "pr_gr ?s"
  from A1 have "loc_upb n x = ?s + 1" by simp
  then have S1: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
  from A1 have S2: "g_step ?ls ?key = c_cons (c_pair ?key (c_fst x)) ?ls" by (simp add: g_step_def)
  from S1 S2 have "pr_gr (loc_upb n x) = c_cons (c_pair ?key (c_fst x)) ?ls" by auto
  thus ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_lex_3: "c_fst n mod 7 = 3 \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "c_fst n mod 7 = 3"
  let ?key = "c_pair n x"
  let ?s = "c_pair ?key 0"
  let ?ls = "pr_gr ?s"
  from A1 have "loc_upb n x = ?s + 1" by simp
  then have S1: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
  from A1 have S2: "g_step ?ls ?key = c_cons (c_pair ?key (c_snd x)) ?ls" by (simp add: g_step_def)
  from S1 S2 have "pr_gr (loc_upb n x) = c_cons (c_pair ?key (c_snd x)) ?ls" by auto
  thus ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_lex_4: "\<lbrakk>\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0;
                       c_fst n mod 7 = 4\<rbrakk> \<Longrightarrow>
                       c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0"
  assume A2: "c_fst n mod 7 = 4"
  let ?key = "c_pair n x"
  let ?m1 = "c_fst (c_snd n)"
  let ?m2 = "c_snd (c_snd n)"
  define upb1 where "upb1 = loc_upb ?m2 x"
  from A2 have m2_lt_n: "?m2 < n" by (simp add: loc_upb_lm_2_2)
  then have M2: "((?m2, x), (n,x)) \<in> lex_p" by (simp add: lex_p_eq)
  with A1 upb1_def have S1: "c_assoc_have_key (pr_gr upb1) (c_pair ?m2 x) = 0" by auto
  from M2 have M2': "((?m2, x), n, x) \<in> measure (\<lambda>m. m) <*lex*> measure (\<lambda>n. n)" by (simp add: lex_p_def)
  have T1: "c_is_sub_fun (pr_gr upb1) univ_for_pr" by (rule pr_gr_1)
  from T1 S1 have T2: "c_assoc_value (pr_gr upb1) (c_pair ?m2 x) = univ_for_pr (c_pair ?m2 x)" by (rule c_is_sub_fun_lm_1)
  define y where "y = c_assoc_value (pr_gr upb1) (c_pair ?m2 x)"
  from T2 y_def have T3: "y = univ_for_pr (c_pair ?m2 x)" by auto

  define upb2 where "upb2 = loc_upb ?m1 y"
  from A2 have "?m1 < n" by (simp add: loc_upb_lm_2_0)
  then have M1: "((?m1, y), (n,x)) \<in> lex_p" by (simp add: lex_p_eq)
  with A1 have S2: "c_assoc_have_key (pr_gr (loc_upb ?m1 y)) (c_pair ?m1 y) = 0" by auto
  from M1 have M1': "((?m1, y), n, x) \<in> measure (\<lambda>m. m) <*lex*> measure (\<lambda>n. n)" by (simp add: lex_p_def)
  from S1 upb1_def have S3: "c_assoc_have_key (pr_gr upb1) (c_pair ?m2 x) = 0" by auto
  from S2 upb2_def have S4: "c_assoc_have_key (pr_gr upb2) (c_pair ?m1 y) = 0" by auto

  let ?s = "c_pair ?key (upb1 + upb2)"
  let ?ls = "pr_gr ?s"
  let ?sum_upb = "upb1 +upb2"
  from A2 have "?m1 < n" by (simp add: loc_upb_lm_2_0)
  then have "((?m1, x), (n,x)) \<in> lex_p" by (simp add: lex_p_eq)
  then have M1'': "((?m1, x), n, x) \<in> measure (\<lambda>m. m) <*lex*> measure (\<lambda>n. n)" by (simp add: lex_p_def)
  from A2 M2' M1'' have S11: "loc_upb n x = (let y = c_assoc_value (pr_gr (loc_upb ?m2 x)) (c_pair ?m2 x)
                               in (c_pair (c_pair n x)
                                   (loc_upb ?m2 x + loc_upb ?m1 y)) + 1)"
    by(simp add: Let_def)
  define upb where "upb = loc_upb n x"
  from S11 y_def upb1_def upb2_def have "loc_upb n x = ?s + 1" by (simp add: Let_def)
  with upb_def have S11: "upb = ?s + 1" by auto

  have S7: "?sum_upb \<le> ?s" by (rule arg2_le_c_pair)
  have upb1_le_s: "upb1 \<le> ?s"
  proof -
    have S1: "upb1 \<le> ?sum_upb" by (rule Nat.le_add1)
    from S1 S7 show ?thesis by auto
  qed
  have upb2_le_s: "upb2 \<le> ?s"
  proof -
    have S1: "upb2 \<le> ?sum_upb" by (rule Nat.le_add2)
    from S1 S7 show ?thesis by auto
  qed

  have S18: "pr_gr upb = g_comp ?ls ?key"
  proof -
    from S11 have S1: "pr_gr upb = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
    from A2 have S2: "g_step ?ls ?key = g_comp ?ls ?key" by (simp add: g_step_def)
    from S1 S2 show ?thesis by auto
  qed

  from S3 upb1_le_s have S19: "c_assoc_have_key ?ls (c_pair ?m2 x) = 0" by (rule lm5)
  from S4 upb2_le_s have S20: "c_assoc_have_key ?ls (c_pair ?m1 y) = 0" by (rule lm5)
  have T_ls: "c_is_sub_fun ?ls univ_for_pr" by (rule pr_gr_1)
  from T_ls S19 have T_ls2: "c_assoc_value ?ls (c_pair ?m2 x) = univ_for_pr (c_pair ?m2 x)" by (rule c_is_sub_fun_lm_1)
  from T3 T_ls2 have T_y: "c_assoc_value ?ls (c_pair ?m2 x) = y" by auto
  from T_y  S19 S20 have S21: "g_comp ?ls ?key = c_cons (c_pair ?key (c_assoc_value ?ls (c_pair ?m1 y))) ?ls"
    by(unfold g_comp_def)(simp del: loc_upb.simps add: Let_def)
  from S18 S21 have "pr_gr upb = c_cons (c_pair ?key (c_assoc_value ?ls (c_pair ?m1 y))) ?ls" by auto
  with upb_def have "pr_gr (loc_upb n x) = c_cons (c_pair ?key (c_assoc_value ?ls (c_pair ?m1 y))) ?ls" by auto
  thus ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_lex_5: "\<lbrakk>\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0;
                       c_fst n mod 7 = 5\<rbrakk> \<Longrightarrow>
                       c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0"
  assume A2: "c_fst n mod 7 = 5"
  let ?key = "c_pair n x"
  let ?m1 = "c_fst (c_snd n)"
  let ?m2 = "c_snd (c_snd n)"
  from A2 have "?m1 < n" by (simp add: loc_upb_lm_2_3)
  then have "((?m1, x), (n,x)) \<in> lex_p" by (simp add: lex_p_eq)
  with A1 have S1: "c_assoc_have_key (pr_gr (loc_upb ?m1 x)) (c_pair ?m1 x) = 0" by auto
  from A2 have "?m2 < n" by (simp add: loc_upb_lm_2_4)
  then have "((?m2, x), (n,x)) \<in> lex_p" by (simp add: lex_p_eq)
  with A1 have S2: "c_assoc_have_key (pr_gr (loc_upb ?m2 x)) (c_pair ?m2 x) = 0" by auto
  define upb1 where "upb1 = loc_upb ?m1 x"
  define upb2 where "upb2 = loc_upb ?m2 x"
  from upb1_def S1 have S3: "c_assoc_have_key (pr_gr upb1) (c_pair ?m1 x) = 0" by auto
  from upb2_def S2 have S4: "c_assoc_have_key (pr_gr upb2) (c_pair ?m2 x) = 0" by auto
  let ?sum_upb = "upb1 +upb2"
  have S5: "upb1 \<le> ?sum_upb" by (rule Nat.le_add1)
  have S6: "upb2 \<le> ?sum_upb" by (rule Nat.le_add2)
  let ?s = "(c_pair ?key ?sum_upb)"
  have S7: "?sum_upb \<le> ?s" by (rule arg2_le_c_pair)
  from S5 S7 have S8: "upb1 \<le> ?s" by auto
  from S6 S7 have S9: "upb2 \<le> ?s" by auto
  let ?ls = "pr_gr ?s"
  from A2 upb1_def upb2_def have S10: "loc_upb n x = ?s + 1" by (simp add: Let_def)
  define upb where "upb = loc_upb n x"
  from upb_def S10 have S11: "upb = ?s + 1" by auto
  from S11 have S12: "pr_gr upb = g_step (pr_gr ?s) (c_fst ?s)" by (simp add: pr_gr_at_Suc)
  from S8 S10 upb_def have S13: "upb1 \<le> upb" by (simp only:)
  from S9 S10 upb_def have S14: "upb2 \<le> upb" by (simp only:)
  from S3 S13 have S15: "c_assoc_have_key (pr_gr upb) (c_pair ?m1 x) = 0" by (rule lm5)
  from S4 S14 have S16: "c_assoc_have_key (pr_gr upb) (c_pair ?m2 x) = 0" by (rule lm5)
  from A2 have S17: "g_step ?ls ?key = g_pair ?ls ?key" by (simp add: g_step_def)
  from S12 S17 have S18: "pr_gr upb = g_pair ?ls ?key" by auto
  from S3 S8 have S19: "c_assoc_have_key ?ls (c_pair ?m1 x) = 0" by (rule lm5)
  from S4 S9 have S20: "c_assoc_have_key ?ls (c_pair ?m2 x) = 0" by (rule lm5)
  let ?y1 = "c_assoc_value ?ls (c_pair ?m1 x)"
  let ?y2 = "c_assoc_value ?ls (c_pair ?m2 x)"
  let ?y = "c_pair ?y1 ?y2"
  from S19 S20 have S21: "g_pair ?ls ?key = c_cons (c_pair ?key ?y) ?ls" by (unfold g_pair_def, simp add: Let_def)
  from S18 S21 have S22: "pr_gr upb = c_cons (c_pair ?key ?y) ?ls" by auto
  from upb_def S22 have S23: "pr_gr (loc_upb n x) = c_cons (c_pair ?key ?y) ?ls" by auto
  from S23 show ?thesis by (simp add: c_assoc_lm_1)
qed

lemma loc_upb_6_z: "\<lbrakk>c_fst n mod 7 =6; c_fst x = 0\<rbrakk> \<Longrightarrow>
  loc_upb n x = c_pair (c_pair n x) (loc_upb (c_fst (c_snd n)) (c_snd x)) + 1" by (simp add: Let_def)

lemma loc_upb_6: "\<lbrakk>c_fst n mod 7 =6; c_fst x \<noteq> 0\<rbrakk> \<Longrightarrow> loc_upb n x = (
                              let m = c_snd n; m1 = c_fst m; m2 = c_snd m; y1 = c_fst x; x1 = c_snd x;
                              y2 = y1 - 1;
                              t1 = c_assoc_value (pr_gr (loc_upb n (c_pair y2 x1))) (c_pair n (c_pair y2 x1));
                              t2 = c_pair (c_pair y2 t1) x1 in
                                c_pair (c_pair n x) (loc_upb n (c_pair y2 x1) + (loc_upb m2 t2)) + 1)"
  by (simp add: Let_def)

lemma loc_upb_lex_6: "\<lbrakk>\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0;
                       c_fst n mod 7 = 6\<rbrakk> \<Longrightarrow>
                       c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0"
  assume A2: "c_fst n mod 7 = 6"
  let ?key = "c_pair n x"
  let ?m1 = "c_fst (c_snd n)"
  let ?m2 = "c_snd (c_snd n)"
  let ?y1 = "c_fst x"
  let ?x1 = "c_snd x"
  define upb where "upb = loc_upb n x"
  show ?thesis
  proof (cases)
    assume A: "?y1 = 0"
    from A2 A have S1: "loc_upb n x = c_pair ?key (loc_upb ?m1 (c_snd x)) + 1" by (rule loc_upb_6_z)
    define upb1 where "upb1 = loc_upb ?m1 (c_snd x)"
    from upb1_def S1 have S2: "loc_upb n x = c_pair ?key upb1 + 1" by auto
    let ?s = "c_pair ?key upb1"
    from S2 have S3: "pr_gr (loc_upb n x) = pr_gr (Suc ?s)" by simp
    have "pr_gr (Suc ?s) = g_step (pr_gr ?s) (c_fst ?s)" by (rule pr_gr_at_Suc)
    with S3 have S4: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) ?key" by auto
    let ?ls = "pr_gr ?s"
    from A2 have "g_step ?ls ?key = g_rec ?ls ?key" by (simp add: g_step_def)
    with S4 have S5: "pr_gr (loc_upb n x) = g_rec ?ls ?key" by auto
    have S6: "c_assoc_have_key ?ls (c_pair ?m1 ?x1) = 0"
    proof -
      from A2 have "?m1 < n" by (simp add: loc_upb_lm_2_5)
      then have "((?m1,?x1), n, x) \<in> lex_p" by (simp add: lex_p_eq)
      with A1 upb1_def have "c_assoc_have_key (pr_gr upb1) (c_pair ?m1 ?x1) = 0" by auto
      also have "upb1 \<le> ?s" by (rule arg2_le_c_pair)
      ultimately show ?thesis by (rule lm5)
    qed
    from A S6 have "g_rec ?ls ?key = c_cons (c_pair ?key (c_assoc_value ?ls (c_pair ?m1 ?x1))) ?ls" by (simp add: g_rec_def Let_def)
    with S5 show ?thesis by (simp add: c_assoc_lm_1)
  next
    assume A: "c_fst x \<noteq> 0" then have y1_pos: "c_fst x > 0" by auto
    let ?y2 = "?y1 - 1"
    from A2 A have "loc_upb n x = (
                              let m = c_snd n; m1 = c_fst m; m2 = c_snd m; y1 = c_fst x; x1 = c_snd x;
                              y2 = y1 - 1;
                              t1 = c_assoc_value (pr_gr (loc_upb n (c_pair y2 x1))) (c_pair n (c_pair y2 x1));
                              t2 = c_pair (c_pair y2 t1) x1 in
                                c_pair (c_pair n x) (loc_upb n (c_pair y2 x1) + (loc_upb m2 t2)) + 1)" by (rule loc_upb_6)
   then have S1: "loc_upb n x = (
                              let
                              t1 = c_assoc_value (pr_gr (loc_upb n (c_pair ?y2 ?x1))) (c_pair n (c_pair ?y2 ?x1));
                              t2 = c_pair (c_pair ?y2 t1) ?x1 in
                                c_pair (c_pair n x) (loc_upb n (c_pair ?y2 ?x1) + (loc_upb ?m2 t2)) + 1)" by (simp del: loc_upb.simps add: Let_def)
   let ?t1 = "univ_for_pr (c_pair n (c_pair ?y2 ?x1))"
   let ?t2 = "c_pair (c_pair ?y2 ?t1) ?x1"
   have S1_1: "c_assoc_have_key (pr_gr (loc_upb n (c_pair ?y2 ?x1))) (c_pair n (c_pair ?y2 ?x1)) = 0"
   proof -
     from A have "?y2 < ?y1" by auto
     then have "c_pair ?y2 ?x1 < c_pair ?y1 ?x1" by (rule c_pair_strict_mono1)
     then have "((n, c_pair ?y2 ?x1),n,x) \<in> lex_p" by (simp add: lex_p_eq)
     with A1 show ?thesis by auto
   qed
   have S2: "c_assoc_value (pr_gr (loc_upb n (c_pair ?y2 ?x1))) (c_pair n (c_pair ?y2 ?x1)) = univ_for_pr (c_pair n (c_pair ?y2 ?x1))"
   proof -
     have "c_is_sub_fun (pr_gr (loc_upb n (c_pair ?y2 ?x1))) univ_for_pr" by (rule pr_gr_1)
     with S1_1 show ?thesis by (simp add: c_is_sub_fun_lm_1)
   qed
   from S1 S2 have S3: "loc_upb n x = c_pair (c_pair n x) (loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2) + 1" by (simp del: loc_upb.simps add: Let_def)
   let ?s = "c_pair (c_pair n x) (loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2)"
   from S3 have S4: "pr_gr (loc_upb n x) = pr_gr (Suc ?s)" by (simp del: loc_upb.simps)
   have "pr_gr (Suc ?s) = g_step (pr_gr ?s) (c_fst ?s)" by (rule pr_gr_at_Suc)
   with S4 have S5: "pr_gr (loc_upb n x) = g_step (pr_gr ?s) ?key" by (simp del: loc_upb.simps)
   let ?ls = "pr_gr ?s"
   from A2 have "g_step ?ls ?key = g_rec ?ls ?key" by (simp add: g_step_def)
   with S5 have S6: "pr_gr (loc_upb n x) = g_rec ?ls ?key" by (simp del: loc_upb.simps)
   have S7: "c_assoc_have_key ?ls (c_pair n (c_pair ?y2 ?x1)) = 0"
   proof -
     have "loc_upb n (c_pair ?y2 ?x1) \<le> loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2" by (auto simp del: loc_upb.simps)
     also have "loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2 \<le> ?s" by (rule arg2_le_c_pair)
     ultimately have S7_1: "loc_upb n (c_pair ?y2 ?x1) \<le> ?s" by (auto simp del: loc_upb.simps)
     from S1_1 S7_1 show ?thesis by (rule lm5)
   qed
   have S8: "c_assoc_value ?ls (c_pair n (c_pair ?y2 ?x1)) = ?t1"
   proof -
     have "c_is_sub_fun ?ls univ_for_pr" by (rule pr_gr_1)
     with S7 show ?thesis by (simp add: c_is_sub_fun_lm_1)
   qed
   have S9: "c_assoc_have_key ?ls (c_pair ?m2 ?t2) = 0"
   proof -
     from A2 have "?m2 < n" by (simp add: loc_upb_lm_2_6)
     then have "((?m2,?t2), n, x) \<in> lex_p" by (simp add: lex_p_eq)
     with A1 have "c_assoc_have_key (pr_gr (loc_upb ?m2 ?t2)) (c_pair ?m2 ?t2) = 0" by auto
     also have "loc_upb ?m2 ?t2 \<le> ?s"
     proof -
       have "loc_upb ?m2 ?t2 \<le> loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2" by (auto simp del: loc_upb.simps)
       also have "loc_upb n (c_pair ?y2 ?x1) + loc_upb ?m2 ?t2 \<le> ?s" by (rule arg2_le_c_pair)
       ultimately show ?thesis by (auto simp del: loc_upb.simps)
     qed
     ultimately show ?thesis by (rule lm5)
   qed
    from A S7 S8 S9 have "g_rec ?ls ?key = c_cons (c_pair ?key (c_assoc_value ?ls (c_pair ?m2 ?t2))) ?ls" by (simp del: loc_upb.simps add: g_rec_def Let_def)
    with S6 show ?thesis by (simp add: c_assoc_lm_1)
  qed
qed

lemma wf_upb_step_0: 
  "\<lbrakk>\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0\<rbrakk> \<Longrightarrow>
      c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  assume A1: "\<And> n' x'. ((n',x'), (n,x)) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0"
  let ?n1 = "(c_fst n) mod 7"
  have S1: "?n1 = 0 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 0"
    thus ?thesis by (rule loc_upb_lex_0)
  qed
  have S2: "?n1 = 1 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 1"
    thus ?thesis by (rule loc_upb_lex_1)
  qed
  have S3: "?n1 = 2 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 2"
    thus ?thesis by (rule loc_upb_lex_2)
  qed
  have S4: "?n1 = 3 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 3"
    thus ?thesis by (rule loc_upb_lex_3)
  qed
  have S5: "?n1 = 4 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 4"
    from A1 A show ?thesis by (rule loc_upb_lex_4)
  qed
  have S6: "?n1 = 5 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 5"
    from A1 A show ?thesis by (rule loc_upb_lex_5)
  qed
  have S7: "?n1 = 6 \<Longrightarrow> ?thesis"
  proof -
    assume A: "?n1 = 6"
    from A1 A show ?thesis by (rule loc_upb_lex_6)
  qed
  have S8: "?n1=0 \<or> ?n1=1 \<or> ?n1=2 \<or> ?n1=3 \<or> ?n1=4 \<or> ?n1=5 \<or> ?n1=6" by (rule mod7_lm)
  from S1 S2 S3 S4 S5 S6 S7 S8 show ?thesis by fast
qed

lemma wf_upb_step: 
  assumes A1: "\<And> p2. (p2, p1) \<in> lex_p \<Longrightarrow>
    c_assoc_have_key (pr_gr (loc_upb (fst p2) (snd p2))) (c_pair (fst p2) (snd p2)) = 0"
  shows "c_assoc_have_key (pr_gr (loc_upb (fst p1) (snd p1))) (c_pair (fst p1) (snd p1)) = 0"
proof -
  let ?n = "fst p1"
  let ?x = "snd p1"
  from A1 have S1: "\<And> p2. (p2, (?n, ?x)) \<in> lex_p \<Longrightarrow>
    c_assoc_have_key (pr_gr (loc_upb (fst p2) (snd p2))) (c_pair (fst p2) (snd p2)) = 0"
    by auto
  have S2: "(\<And> n' x'. ((n',x'), (fst p1, snd p1)) \<in> lex_p
    \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0) \<Longrightarrow>
      c_assoc_have_key (pr_gr (loc_upb (fst p1) (snd p1))) (c_pair (fst p1) (snd p1)) = 0"
    by (rule wf_upb_step_0)
  then have S3: "(\<And> n' x'. ((n',x'), p1) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0)
    \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb (fst p1) (snd p1))) (c_pair (fst p1) (snd p1)) = 0" by auto
  have S4: "\<And>n' x'. ((n', x'), p1) \<in> lex_p \<Longrightarrow> c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0"
  proof -
    fix n' x'
    assume A4_1: "((n', x'), p1) \<in> lex_p"
    let ?p2 = "(n', x')"
    from A4_1 have S4_1: "(?p2, p1) \<in> lex_p" by auto
    from S4_1 have "c_assoc_have_key (pr_gr (loc_upb (fst ?p2) (snd ?p2))) (c_pair (fst ?p2) (snd ?p2)) = 0"
      by (rule A1)
    then show "c_assoc_have_key (pr_gr (loc_upb n' x')) (c_pair n' x') = 0" by auto
  qed
  from S4 S3 show ?thesis by auto
qed

theorem loc_upb_main: "c_assoc_have_key (pr_gr (loc_upb n x)) (c_pair n x) = 0"
proof -
  have loc_upb_lm: "\<And> p. c_assoc_have_key (pr_gr (loc_upb (fst p) (snd p))) (c_pair (fst p) (snd p)) = 0"
  proof - fix p show "c_assoc_have_key (pr_gr (loc_upb (fst p) (snd p))) (c_pair (fst p) (snd p)) = 0"
    proof -
      have S1: "wf lex_p" by (auto simp add: lex_p_def)
      from S1 wf_upb_step show ?thesis by (rule wf_induct_rule)
    qed
  qed
  let ?p = "(n,x)"
  have "c_assoc_have_key (pr_gr (loc_upb (fst ?p) (snd ?p))) (c_pair (fst ?p) (snd ?p)) = 0" by (rule loc_upb_lm)
  thus ?thesis by simp
qed

theorem pr_gr_value: "c_assoc_value (pr_gr (loc_upb n x)) (c_pair n x) = univ_for_pr (c_pair n x)"
  by (simp del: loc_upb.simps add: loc_upb_main pr_gr_1 c_is_sub_fun_lm_1)

theorem g_comp_is_pr: "g_comp \<in> PrimRec2"
proof -
  from c_assoc_have_key_is_pr c_assoc_value_is_pr c_cons_is_pr have "(\<lambda> x y. g_comp x y) \<in> PrimRec2"
    unfolding g_comp_def Let_def by prec
  thus ?thesis by auto
qed

theorem g_pair_is_pr: "g_pair \<in> PrimRec2"
proof -
  from c_assoc_have_key_is_pr c_assoc_value_is_pr c_cons_is_pr have "(\<lambda> x y. g_pair x y) \<in> PrimRec2"
    unfolding g_pair_def Let_def by prec
  thus ?thesis by auto
qed

theorem g_rec_is_pr: "g_rec \<in> PrimRec2"
proof -
  from c_assoc_have_key_is_pr c_assoc_value_is_pr c_cons_is_pr have "(\<lambda> x y. g_rec x y) \<in> PrimRec2"
    unfolding g_rec_def Let_def by prec
  thus ?thesis by auto
qed

theorem g_step_is_pr: "g_step \<in> PrimRec2"
proof -
  from g_comp_is_pr g_pair_is_pr g_rec_is_pr mod_is_pr c_assoc_have_key_is_pr c_assoc_value_is_pr c_cons_is_pr have
    "(\<lambda> ls key. g_step ls key) \<in> PrimRec2" unfolding g_step_def Let_def by prec
  thus ?thesis by auto
qed

theorem pr_gr_is_pr: "pr_gr \<in> PrimRec1"
proof -
  have S1: "(\<lambda> x. pr_gr x) = PrimRecOp1 0 (\<lambda> x y. g_step y (c_fst x))" (is "_ = ?f")
  proof
    fix x
    show "pr_gr x = ?f x" by (induct x) (simp add: pr_gr_at_0, simp add: pr_gr_at_Suc)
  qed
  have S2: "PrimRecOp1 0 (\<lambda> x y. g_step y (c_fst x)) \<in> PrimRec1"
  proof (rule pr_rec1)
    from g_step_is_pr show "(\<lambda>x y. g_step y (c_fst x)) \<in> PrimRec2" by prec
  qed
  from S1 S2 show ?thesis by auto
qed

end
