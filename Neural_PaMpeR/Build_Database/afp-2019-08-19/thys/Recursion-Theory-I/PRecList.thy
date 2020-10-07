(*  Title:       Primitive recursive coding of lists of natural numbers
    Author:      Michael Nedzelsky <MichaelNedzelsky at yandex.ru>, 2008
    Maintainer:  Michael Nedzelsky <MichaelNedzelsky at yandex.ru>
*)

section \<open>Primitive recursive coding of lists of natural numbers\<close>

theory PRecList
imports PRecFun
begin

text \<open>
  We introduce a particular coding \<open>list_to_nat\<close> from lists of
  natural numbers to natural numbers.
\<close>

definition
  c_len :: "nat \<Rightarrow> nat" where
  "c_len = (\<lambda> (u::nat). (sgn1 u) * (c_fst(u-(1::nat))+1))"

lemma c_len_1: "c_len u = (case u of 0 \<Rightarrow> 0 | Suc v \<Rightarrow> c_fst(v)+1)" by (unfold c_len_def, cases u, auto)

lemma c_len_is_pr: "c_len \<in> PrimRec1" unfolding c_len_def by prec

lemma [simp]: "c_len 0 = 0" by (simp add: c_len_def)

lemma c_len_2: "u \<noteq> 0 \<Longrightarrow> c_len u = c_fst(u-(1::nat))+1" by (simp add: c_len_def)

lemma c_len_3: "u>0 \<Longrightarrow> c_len u > 0" by (simp add: c_len_2)

lemma c_len_4: "c_len u = 0 \<Longrightarrow> u = 0"
proof cases
  assume A1: "u = 0"
  thus ?thesis by simp
next
  assume A1: "c_len u = 0" and A2: "u \<noteq> 0"
  from A2 have "c_len u > 0" by (simp add: c_len_3)
  from A1 this show "u=0" by simp
qed

lemma c_len_5: "c_len u > 0 \<Longrightarrow> u > 0"
proof cases
  assume A1: "c_len u > 0" and A2: "u=0"
  from A2 have "c_len u = 0" by simp
  from A1 this show ?thesis by simp
next
  assume A1: "u \<noteq> 0"
  from A1 show "u>0" by simp
qed

fun c_fold :: "nat list \<Rightarrow> nat" where
    "c_fold [] = 0"
  | "c_fold [x] = x"
  | "c_fold (x#ls) = c_pair x (c_fold ls)"

lemma c_fold_0: "ls \<noteq> [] \<Longrightarrow> c_fold (x#ls) = c_pair x (c_fold ls)"
proof -
  assume A1: "ls \<noteq> []"
  then have S1: "ls = (hd ls)#(tl ls)" by simp
  then have S2: "x#ls = x#(hd ls)#(tl ls)" by simp
  have S3: "c_fold (x#(hd ls)#(tl ls)) = c_pair x (c_fold ((hd ls)#(tl ls)))" by simp
  from S1 S2 S3 show ?thesis by simp
qed

primrec
  c_unfold :: "nat \<Rightarrow> nat \<Rightarrow> nat list"
where
  "c_unfold 0 u = []"
| "c_unfold (Suc k) u = (if k = 0 then [u] else ((c_fst u) # (c_unfold k (c_snd u))))"

lemma c_fold_1: "c_unfold 1 (c_fold [x]) = [x]" by simp

lemma c_fold_2: "c_fold (c_unfold 1 u) = u" by simp

lemma c_unfold_1: "c_unfold 1 u = [u]" by simp

lemma c_unfold_2: "c_unfold (Suc 1) u = (c_fst u) # (c_unfold 1 (c_snd u))" by simp

lemma c_unfold_3: "c_unfold (Suc 1) u = [c_fst u, c_snd u]" by simp

lemma c_unfold_4: "k > 0 \<Longrightarrow> c_unfold (Suc k) u = (c_fst u) # (c_unfold k (c_snd u))" by simp

lemma c_unfold_4_1: "k > 0 \<Longrightarrow> c_unfold (Suc k) u \<noteq> []" by (simp add: c_unfold_4)

lemma two: "(2::nat) = Suc 1" by simp

lemma c_unfold_5: "c_unfold 2 u = [c_fst u, c_snd u]" by (simp add: two)

lemma c_unfold_6: "k>0 \<Longrightarrow> c_unfold k u \<noteq> []"
proof -
  assume A1: "k>0"
  let ?k1 = "k-(1::nat)"
  from A1 have S1: "k = Suc ?k1" by simp
  have S2: "?k1 = 0 \<Longrightarrow> ?thesis"
  proof -
    assume A2_1: "?k1=0"
    from A1 A2_1 have S2_1: "k=1" by simp
    from S2_1 show ?thesis by (simp add: c_unfold_1)
  qed
  have S3: "?k1 > 0 \<Longrightarrow> ?thesis"
  proof -
    assume A3_1: "?k1 > 0"
    from A3_1 have S3_1: "c_unfold (Suc ?k1) u \<noteq> []" by (rule c_unfold_4_1)
    from S1 S3_1 show ?thesis by simp
  qed
  from S2 S3 show ?thesis by arith
qed

lemma th_lm_1: "k=1 \<Longrightarrow> (\<forall> u. c_fold (c_unfold k u) = u)" by (simp add: c_fold_2)

lemma th_lm_2: "\<lbrakk>k>0; (\<forall> u. c_fold (c_unfold k u) = u)\<rbrakk> \<Longrightarrow> (\<forall> u. c_fold (c_unfold (Suc k) u) = u)"
proof
  assume A1: "k>0"
  assume A2: "\<forall> u. c_fold (c_unfold k u) = u"
  fix u
  from A1 have S1: "c_unfold (Suc k) u = (c_fst u) # (c_unfold k (c_snd u))" by (rule c_unfold_4)
  let ?ls = "c_unfold k (c_snd u)"
  from A1 have S2: "?ls \<noteq> []" by (rule c_unfold_6)
  from S2 have S3: "c_fold ( (c_fst u) # ?ls) = c_pair (c_fst u) (c_fold ?ls)" by (rule c_fold_0)
  from A2 have S4: "c_fold ?ls = c_snd u" by simp
  from S3 S4 have S5: "c_fold ( (c_fst u) # ?ls) = c_pair (c_fst u) (c_snd u)" by simp
  from S5 have S6: "c_fold ( (c_fst u) # ?ls) = u" by simp
  from S1 S6 have S7: "c_fold (c_unfold (Suc k) u) = u" by simp
  thus "c_fold (c_unfold (Suc k) u) = u" .
qed

lemma th_lm_3: "(\<forall> u. c_fold (c_unfold (Suc k) u) = u)\<Longrightarrow> (\<forall> u. c_fold (c_unfold (Suc (Suc k)) u) = u)"
proof -
  assume A1: "\<forall> u. c_fold (c_unfold (Suc k) u) = u"
  let ?k1 = "Suc k"
  have S1: "?k1 > 0" by simp
  from S1 A1 have S2: "\<forall> u. c_fold (c_unfold (Suc ?k1) u) = u" by (rule th_lm_2)
  thus ?thesis by simp
qed

theorem th_1: "\<forall> u. c_fold (c_unfold (Suc k) u) = u"
apply(induct k)
apply(simp add: c_fold_2)
apply(rule th_lm_3)
apply(assumption)
done

theorem th_2: "k > 0 \<Longrightarrow> (\<forall> u. c_fold (c_unfold k u) = u)"
proof -
  assume A1: "k>0"
  let ?k1 = "k-(1::nat)"
  from A1 have S1: "Suc ?k1 = k" by simp
  have S2: "\<forall> u. c_fold (c_unfold (Suc ?k1) u) = u" by (rule th_1)
  from S1 S2 show ?thesis by simp
qed

lemma c_fold_3: "c_unfold 2 (c_fold [x, y]) = [x, y]" by (simp add: two)

theorem c_unfold_len: "ALL u. length (c_unfold k u) = k"
apply(induct k)
apply(simp)
apply(subgoal_tac "n=(0::nat) \<or> n>0")
apply(drule disjE)
prefer 3
apply(simp_all)
apply(auto)
done

lemma th_3_lm_0: "\<lbrakk>c_unfold (length ls) (c_fold ls) = ls; ls = a # ls1; ls1 = aa # list\<rbrakk> \<Longrightarrow> c_unfold (length (x # ls)) (c_fold (x # ls)) = x # ls"
proof -
  assume A1: "c_unfold (length ls) (c_fold ls) = ls"
  assume A2: "ls = a # ls1"
  assume A3: "ls1 = aa # list"
  from A2 have S1: "ls \<noteq> []" by simp
  from S1 have S2: "c_fold (x#ls) = c_pair x (c_fold ls)" by (rule c_fold_0)
  have S3: "length (x#ls) = Suc (length ls)" by simp
  from S3 have S4: "c_unfold (length (x # ls)) (c_fold (x # ls)) = c_unfold (Suc (length ls)) (c_fold (x # ls))" by simp
  from A2 have S5: "length ls > 0" by simp
  from S5 have S6: "c_unfold (Suc (length ls)) (c_fold (x # ls)) = c_fst (c_fold (x # ls))#(c_unfold (length ls) (c_snd (c_fold (x#ls))))" by (rule c_unfold_4)
  from S2 have S7: "c_fst (c_fold (x#ls)) = x" by simp
  from S2 have S8: "c_snd (c_fold (x#ls)) = c_fold ls" by simp
  from S6 S7 S8 have S9: "c_unfold (Suc (length ls)) (c_fold (x # ls)) = x # (c_unfold (length ls) (c_fold ls))" by simp
  from A1 have S10: "x # (c_unfold (length ls) (c_fold ls)) = x # ls" by simp
  from S9 S10 have S11: "c_unfold (Suc (length ls)) (c_fold (x # ls)) = (x # ls)" by simp
  thus ?thesis by simp
qed

lemma th_3_lm_1: "\<lbrakk>c_unfold (length ls) (c_fold ls) = ls; ls = a # ls1\<rbrakk> \<Longrightarrow> c_unfold (length (x # ls)) (c_fold (x # ls)) = x # ls"
apply(cases ls1)
apply(simp add: c_fold_1)
apply(simp)
done

lemma th_3_lm_2: "c_unfold (length ls) (c_fold ls) = ls \<Longrightarrow> c_unfold (length (x # ls)) (c_fold (x # ls)) = x # ls"
apply(cases ls)
apply(simp add: c_fold_1)
apply(rule th_3_lm_1)
apply(assumption+)
done

theorem th_3: "c_unfold (length ls) (c_fold ls) = ls"
apply(induct ls)
apply(simp)
apply(rule th_3_lm_2)
apply(assumption)
done

definition
  list_to_nat :: "nat list \<Rightarrow> nat" where
  "list_to_nat = (\<lambda> ls. if ls=[] then 0 else (c_pair ((length ls) - 1) (c_fold ls))+1)"

definition
  nat_to_list :: "nat \<Rightarrow> nat list" where
  "nat_to_list = (\<lambda> u. if u=0 then [] else (c_unfold (c_len u) (c_snd (u-(1::nat)))))"

lemma nat_to_list_of_pos: "u>0 \<Longrightarrow> nat_to_list u = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (simp add: nat_to_list_def)

theorem list_to_nat_th [simp]: "list_to_nat (nat_to_list u) = u"
proof -
  have S1: "u=0 \<Longrightarrow> ?thesis" by (simp add: list_to_nat_def nat_to_list_def)
  have S2: "u>0 \<Longrightarrow> ?thesis"
  proof -
    assume A1: "u>0"
    define ls where "ls = nat_to_list u"
    from ls_def A1 have S2_1: "ls = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (simp add: nat_to_list_def)
    let ?k = "c_len u"
    from A1 have S2_2: "?k > 0" by (rule c_len_3)
    from S2_1 have S2_3: "length ls = ?k" by (simp add: c_unfold_len)
    from S2_2 S2_3 have S2_4: "length ls > 0" by simp
    from S2_4 have S2_5: "ls \<noteq> []" by simp
    from S2_5 have S2_6: "list_to_nat ls = c_pair ((length ls)-(1::nat)) (c_fold ls)+1" by (simp add: list_to_nat_def)
    have S2_7: "c_fold ls = c_snd(u-(1::nat))"
    proof -
      from S2_1 have S2_7_1: "c_fold ls = c_fold (c_unfold (c_len u) (c_snd (u-(1::nat))))" by simp
      from S2_2 S2_7_1 show ?thesis by (simp add: th_2)
    qed
    have S2_8: "(length ls)-(1::nat) = c_fst (u-(1::nat))"
    proof -
      from S2_3 have S2_8_1: "length ls = c_len u" by simp
      from A1 S2_8_1 have S2_8_2: "length ls = c_fst(u-(1::nat)) + 1" by (simp add: c_len_2)
      from S2_8_2 show ?thesis by simp
    qed
    from S2_7 S2_8 have S2_9: "c_pair ((length ls)-(1::nat)) (c_fold ls) = c_pair (c_fst (u-(1::nat))) (c_snd (u-(1::nat)))" by simp 
    from S2_9 have S2_10: "c_pair ((length ls)-(1::nat)) (c_fold ls) = u - (1::nat)" by simp
    from S2_6 S2_10 have S2_11: "list_to_nat ls = (u - (1::nat))+1" by simp
    from A1 have S2_12: "(u - (1::nat))+1 = u" by simp
    from ls_def S2_11 S2_12 show ?thesis by simp
  qed
  from S1 S2 show ?thesis by arith
qed

theorem nat_to_list_th [simp]: "nat_to_list (list_to_nat ls) = ls"
proof -
  have S1: "ls=[] \<Longrightarrow> ?thesis" by (simp add: nat_to_list_def list_to_nat_def)
  have S2: "ls \<noteq> [] \<Longrightarrow> ?thesis"
  proof -
    assume A1: "ls \<noteq> []"
    define u where "u = list_to_nat ls"
    from u_def A1 have S2_1: "u = (c_pair ((length ls)-(1::nat)) (c_fold ls))+1" by (simp add: list_to_nat_def)
    let ?k = "length ls"
    from A1 have S2_2: "?k > 0" by simp
    from S2_1 have S2_3: "u>0" by simp
    from S2_3 have S2_4: "nat_to_list u = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (simp add: nat_to_list_def)
    have S2_5: "c_len u = length ls"
    proof -
      from S2_1 have S2_5_1: "u-(1::nat) = c_pair ((length ls)-(1::nat)) (c_fold ls)" by simp
      from S2_5_1 have S2_5_2: "c_fst (u-(1::nat)) = (length ls)-(1::nat)" by simp
      from S2_2 S2_5_2 have "c_fst (u-(1::nat))+1 = length ls" by simp
      from S2_3 this show ?thesis by (simp add: c_len_2)
    qed
    have S2_6: "c_snd (u-(1::nat)) = c_fold ls"
    proof -
      from S2_1 have S2_6_1: "u-(1::nat) = c_pair ((length ls)-(1::nat)) (c_fold ls)" by simp
      from S2_6_1 show ?thesis by simp
    qed
    from S2_4 S2_5 S2_6 have S2_7:"nat_to_list u = c_unfold (length ls) (c_fold ls)" by simp
    from S2_7 have "nat_to_list u = ls" by (simp add: th_3)
    from u_def this show ?thesis by simp
  qed
  have S3: "ls = [] \<or> ls \<noteq> []" by simp
  from S1 S2 S3 show ?thesis by auto
qed

lemma [simp]: "list_to_nat [] = 0" by (simp add: list_to_nat_def)

lemma [simp]: "nat_to_list 0 = []" by (simp add: nat_to_list_def)

theorem c_len_th_1: "c_len (list_to_nat ls) = length ls"
proof (cases)
  assume "ls=[]"
  from this show ?thesis by simp
next
  assume S1: "ls \<noteq> []"
  then have S2: "list_to_nat ls = c_pair ((length ls)-(1::nat)) (c_fold ls)+1" by (simp add: list_to_nat_def)
  let ?u = "list_to_nat ls"
  from S2 have u_not_zero: "?u > 0" by simp
  from S2 have S3: "?u-(1::nat) = c_pair ((length ls)-(1::nat)) (c_fold ls)" by simp
  then have S4: "c_fst(?u-(1::nat)) = (length ls)-(1::nat)" by simp
  from S1 this have S5: "c_fst(?u-(1::nat))+1=length ls" by simp
  from u_not_zero S5 have S6: "c_len (?u) = length ls" by (simp add: c_len_2)
  from S1 S6 show ?thesis by simp
qed

theorem "length (nat_to_list u) = c_len u"
proof -
  let ?ls = "nat_to_list u"
  have S1: "u = list_to_nat ?ls" by (rule list_to_nat_th [THEN sym])
  from c_len_th_1 have S2: "length ?ls = c_len (list_to_nat ?ls)" by (rule sym)
  from S1 S2 show ?thesis by (rule ssubst)
qed

definition
  c_hd :: "nat \<Rightarrow> nat" where
  "c_hd = (\<lambda> u. if u=0 then 0 else hd (nat_to_list u))"

definition
  c_tl :: "nat \<Rightarrow> nat" where
  "c_tl = (\<lambda> u. list_to_nat (tl (nat_to_list u)))"

definition
  c_cons :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_cons = (\<lambda> x u. list_to_nat (x # (nat_to_list u)))"


lemma [simp]: "c_hd 0 = 0" by (simp add: c_hd_def)

lemma c_hd_aux0: "c_len u = 1 \<Longrightarrow> nat_to_list u = [c_snd (u-(1::nat))]" by (simp add: nat_to_list_def c_len_5)

lemma c_hd_aux1: "c_len u = 1 \<Longrightarrow> c_hd u = c_snd (u-(1::nat))"
proof -
  assume A1: "c_len u = 1"
  then have S1: "nat_to_list u = [c_snd (u-(1::nat))]" by (simp add: nat_to_list_def c_len_5)
  from A1 have "u > 0" by (simp add: c_len_5)
  with S1 show ?thesis by (simp add: c_hd_def)
qed

lemma c_hd_aux2: "c_len u > 1 \<Longrightarrow> c_hd u = c_fst (c_snd (u-(1::nat)))"
proof -
  assume A1: "c_len u > 1"
  let ?k = "(c_len u) - 1"
  from A1 have S1: "c_len u = Suc ?k" by simp
  from A1 have S2: "c_len u > 0" by simp
  from S2 have S3: "u > 0" by (rule c_len_5)
  from S3 have S4: "c_hd u = hd (nat_to_list u)" by (simp add: c_hd_def)
  from S3 have S5: "nat_to_list u = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (rule nat_to_list_of_pos)
  from S1 S5 have S6: "nat_to_list u = c_unfold (Suc ?k) (c_snd (u-(1::nat)))" by simp
  from A1 have S7: "?k > 0" by simp
  from S7 have S8: "c_unfold (Suc ?k) (c_snd (u-(1::nat))) = (c_fst (c_snd (u-(1::nat)))) # (c_unfold ?k (c_snd (c_snd (u-(1::nat)))))" by (rule c_unfold_4)
  from S6 S8 have S9: "nat_to_list u = (c_fst (c_snd (u-(1::nat)))) # (c_unfold ?k (c_snd (c_snd (u-(1::nat)))))" by simp
  from S9 have S10: "hd (nat_to_list u) = c_fst (c_snd (u-(1::nat)))" by simp
  from S4 S10 show ?thesis by simp
qed

lemma c_hd_aux3: "u > 0 \<Longrightarrow> c_hd u = (if (c_len u) = 1 then c_snd (u-(1::nat)) else c_fst (c_snd (u-(1::nat))))"
proof -
  assume A1: "u > 0"
  from A1 have "c_len u > 0" by (rule c_len_3)
  then have S1: "c_len u = 1 \<or> c_len u > 1" by arith
  let ?tmp = "if (c_len u) = 1 then c_snd (u-(1::nat)) else c_fst (c_snd (u-(1::nat)))"
  have S2: "c_len u = 1 \<Longrightarrow> ?thesis"
  proof -
    assume A2_1: "c_len u = 1"
    then have S2_1: "c_hd u = c_snd (u-(1::nat))" by (rule c_hd_aux1)
    from A2_1 have S2_2: "?tmp = c_snd(u-(1::nat))" by simp
    from S2_1 this show ?thesis by simp
  qed
  have S3: "c_len u > 1 \<Longrightarrow> ?thesis"
  proof -
    assume A3_1: "c_len u > 1"
    from A3_1 have S3_1: "c_hd u = c_fst (c_snd (u-(1::nat)))" by (rule c_hd_aux2)
    from A3_1 have S3_2: "?tmp = c_fst (c_snd (u-(1::nat)))" by simp
    from S3_1 this show ?thesis by simp
  qed
  from S1 S2 S3 show ?thesis by auto
qed

lemma c_hd_aux4: "c_hd u = (if u=0 then 0 else (if (c_len u) = 1 then c_snd (u-(1::nat)) else c_fst (c_snd (u-(1::nat)))))"
proof cases
  assume "u=0" then show ?thesis by simp
next
  assume "u \<noteq> 0" then have A1: "u > 0" by simp
  then show ?thesis by (simp add: c_hd_aux3)
qed

lemma c_hd_is_pr: "c_hd \<in> PrimRec1"
proof -
  have "c_hd = (%u. (if u=0 then 0 else (if (c_len u) = 1 then c_snd (u-(1::nat)) else c_fst (c_snd (u-(1::nat))))))" (is "_ = ?R")  by (simp add: c_hd_aux4 ext)
  moreover have "?R \<in> PrimRec1"
  proof (rule if_is_pr)
    show "(\<lambda> x. x) \<in> PrimRec1" by (rule pr_id1_1)
    next show "(\<lambda> x. 0) \<in> PrimRec1" by (rule pr_zero)
    next show "(\<lambda>x. if c_len x = 1 then c_snd (x - 1) else c_fst (c_snd (x - 1))) \<in> PrimRec1"
    proof (rule if_eq_is_pr)
      show "c_len \<in> PrimRec1" by (rule c_len_is_pr)
      next show "(\<lambda> x. 1) \<in> PrimRec1" by (rule const_is_pr)
      next show "(\<lambda>x. c_snd (x - 1)) \<in> PrimRec1" by prec
      next show "(\<lambda>x. c_fst (c_snd (x - 1))) \<in> PrimRec1" by prec
    qed
  qed
  ultimately show ?thesis by simp
qed

lemma [simp]: "c_tl 0 = 0" by (simp add: c_tl_def)

lemma c_tl_eq_tl: "c_tl (list_to_nat ls) = list_to_nat (tl ls)" by (simp add: c_tl_def)

lemma tl_eq_c_tl: "tl (nat_to_list x) = nat_to_list (c_tl x)" by (simp add: c_tl_def)

lemma c_tl_aux1: "c_len u = 1 \<Longrightarrow> c_tl u = 0" by (unfold c_tl_def, simp add: c_hd_aux0)

lemma c_tl_aux2: "c_len u > 1 \<Longrightarrow> c_tl u = (c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1"
proof -
  assume A1: "c_len u > 1"
  let ?k = "(c_len u) - 1"
  from A1 have S1: "c_len u = Suc ?k" by simp
  from A1 have S2: "c_len u > 0" by simp
  from S2 have S3: "u > 0" by (rule c_len_5)
  from S3 have S4: "nat_to_list u = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (rule nat_to_list_of_pos)
  from A1 have S5: "?k > 0" by simp
  from S5 have S6: "c_unfold (Suc ?k) (c_snd (u-(1::nat))) = (c_fst (c_snd (u-(1::nat)))) # (c_unfold ?k (c_snd (c_snd (u-(1::nat)))))" by (rule c_unfold_4)
  from S6 have S7: "tl (c_unfold (Suc ?k) (c_snd (u-(1::nat)))) = c_unfold ?k (c_snd (c_snd (u-(1::nat))))" by simp
  from S2 S4 S7 have S8: "tl (nat_to_list u) = c_unfold ?k (c_snd (c_snd (u-(1::nat))))" by simp
  define ls where "ls = tl (nat_to_list u)"
  from ls_def S8 have S9: "length ls = ?k" by (simp add: c_unfold_len)
  from ls_def have S10: "c_tl u = list_to_nat ls" by (simp add: c_tl_def)
  from S5 S9 have S11: "length ls > 0" by simp
  from S11 have S12: "ls \<noteq> []" by simp
  from S12 have S13: "list_to_nat ls = (c_pair ((length ls) - 1) (c_fold ls))+1" by (simp add: list_to_nat_def)
  from S10 S13 have S14: "c_tl u = (c_pair ((length ls) - 1) (c_fold ls))+1" by simp
  from S9 have S15: "(length ls)-(1::nat) = ?k-(1::nat)" by simp
  from A1 have S16: "?k-(1::nat) = c_len u - (2::nat)" by arith
  from S15 S16 have S17: "(length ls)-(1::nat) = c_len u - (2::nat)" by simp
  from ls_def S8 have S18: "ls = c_unfold ?k (c_snd (c_snd (u-(1::nat))))" by simp
  from S5 have S19: "c_fold (c_unfold ?k (c_snd (c_snd (u-(1::nat))))) = c_snd (c_snd (u-(1::nat)))" by (simp add: th_2)
  from S18 S19 have S20: "c_fold ls = c_snd (c_snd (u-(1::nat)))" by simp
  from S14 S17 S20 show ?thesis by simp
qed

lemma c_tl_aux3: "c_tl u = (sgn1 ((c_len u) - 1))*((c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1)" (is "_ = ?R")
proof -
  have S1: "u=0 \<Longrightarrow> ?thesis" by simp
  have S2: "u>0 \<Longrightarrow> ?thesis"
  proof -
    assume A1: "u>0"
    have S2_1: "c_len u = 1 \<Longrightarrow> ?thesis" by (simp add: c_tl_aux1)
    have S2_2: "c_len u \<noteq> 1 \<Longrightarrow> ?thesis"
    proof -
      assume A2_2_1: "c_len u \<noteq> 1"
      from A1 have S2_2_1: "c_len u > 0" by (rule c_len_3)
      from A2_2_1 S2_2_1 have S2_2_2: "c_len u > 1" by arith
      from this have S2_2_3: "c_len u - 1 > 0" by simp
      from this have S2_2_4: "sgn1 (c_len u - 1)=1" by simp
      from S2_2_4 have S2_2_5: "?R = (c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1" by simp
      from S2_2_2 have S2_2_6: "c_tl u = (c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1" by (rule c_tl_aux2)
      from S2_2_5 S2_2_6 show ?thesis by simp
    qed
  from S2_1 S2_2 show ?thesis by blast
  qed
  from S1 S2 show ?thesis by arith
qed

lemma c_tl_less: "u > 0 \<Longrightarrow> c_tl u < u"
proof -
  assume A1: "u > 0"
  then have S1: "c_len u > 0" by (rule c_len_3)
  then show ?thesis
  proof cases
    assume "c_len u = 1"
    from this A1 show ?thesis by (simp add: c_tl_aux1)
  next
    assume "\<not> c_len u = 1" with S1 have A2: "c_len u > 1" by simp
    then have S2: "c_tl u = (c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1" by (rule c_tl_aux2)
    from A1 have S3: "c_len u = c_fst(u-(1::nat))+1" by (simp add: c_len_def)
    from A2 S3 have S4: "c_len u - (2::nat) < c_fst(u-(1::nat))" by simp
    then have S5: "(c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) < (c_pair (c_fst(u-(1::nat))) (c_snd (c_snd (u-(1::nat)))))" by (rule c_pair_strict_mono1)
    have S6: "c_snd (c_snd (u-(1::nat))) \<le> c_snd (u-(1::nat))" by (rule c_snd_le_arg)
    then have S7: "(c_pair (c_fst(u-(1::nat))) (c_snd (c_snd (u-(1::nat))))) \<le> (c_pair (c_fst(u-(1::nat))) (c_snd (u-(1::nat))))" by (rule c_pair_mono2)
    then have S8: "(c_pair (c_fst(u-(1::nat))) (c_snd (c_snd (u-(1::nat))))) \<le> u-(1::nat)" by simp
    with S5 have "(c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) < u - (1::nat)" by simp
    with S2 have "c_tl u < (u-(1::nat))+1" by simp
    with A1 show ?thesis by simp
  qed
qed

lemma c_tl_le: "c_tl u \<le> u"
proof (cases u)
  assume "u=0"
  then show ?thesis by simp
next
  fix v assume A1: "u = Suc v"
  then have S1: "u > 0" by simp
  then have S2: "c_tl u < u" by (rule c_tl_less)
  with A1 show "c_tl u \<le> u" by simp
qed

theorem c_tl_is_pr: "c_tl \<in> PrimRec1"
proof -
  have "c_tl = (\<lambda> u. (sgn1 ((c_len u) - 1))*((c_pair (c_len u - (2::nat)) (c_snd (c_snd (u-(1::nat))))) + 1))" (is "_ = ?R") by (simp add: c_tl_aux3 ext)
  moreover from c_len_is_pr c_pair_is_pr have "?R \<in> PrimRec1" by prec
  ultimately show ?thesis by simp
qed

lemma c_cons_aux1: "c_cons x 0 = (c_pair 0 x) + 1"
apply(unfold c_cons_def)
apply(simp)
apply(unfold list_to_nat_def)
apply(simp)
done

lemma c_cons_aux2: "u > 0 \<Longrightarrow> c_cons x u = (c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1"
proof -
  assume A1: "u > 0"
  from A1 have S1: "c_len u > 0" by (rule c_len_3)
  from A1 have S2: "nat_to_list u = c_unfold (c_len u) (c_snd (u-(1::nat)))" by (rule nat_to_list_of_pos)
  define ls where "ls = nat_to_list u"
  from ls_def S2 have S3: "ls = c_unfold (c_len u) (c_snd (u-(1::nat)))" by simp
  from S3 have S4: "length ls = c_len u" by (simp add: c_unfold_len)
  from S4 S1 have S5: "length ls > 0" by simp
  from S5 have S6: "ls \<noteq> []" by simp
  from ls_def have S7: "c_cons x u = list_to_nat (x # ls)" by (simp add: c_cons_def)
  have S8: "list_to_nat (x # ls) = (c_pair ((length (x#ls))-(1::nat)) (c_fold (x#ls)))+1" by (simp add: list_to_nat_def)
  have S9: "(length (x#ls))-(1::nat) = length ls" by simp
  from S9 S4 S8 have S10: "list_to_nat (x # ls) = (c_pair (c_len u) (c_fold (x#ls)))+1" by simp
  have S11: "c_fold (x#ls) = c_pair x (c_snd (u-(1::nat)))"
  proof -
    from S6 have S11_1: "c_fold (x#ls) = c_pair x (c_fold ls)" by (rule c_fold_0)
    from S3 have S11_2: "c_fold ls = c_fold (c_unfold (c_len u) (c_snd (u-(1::nat))))" by simp
    from S1 S11_2 have S11_3: "c_fold ls = c_snd (u-(1::nat))" by (simp add: th_2)
    from S11_1 S11_3 show ?thesis by simp
  qed
  from S7 S10 S11 show ?thesis by simp
qed

lemma c_cons_aux3: "c_cons = (\<lambda> x u. (sgn2 u)*((c_pair 0 x)+1) + (sgn1 u)*((c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1))"
proof (rule ext, rule ext)
  fix x u show "c_cons x u = (sgn2 u)*((c_pair 0 x)+1) + (sgn1 u)*((c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1)" (is "_ = ?R")
  proof cases
    assume A1: "u=0"
    then have "?R = (c_pair 0 x)+1" by simp
    moreover from A1 have "c_cons x u = (c_pair 0 x)+1" by (simp add: c_cons_aux1)
    ultimately show ?thesis by simp
  next
    assume A1: "u\<noteq>0"
    then have S1: "?R = (c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1" by simp
    from A1 have S2: "c_cons x u = (c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1" by (simp add: c_cons_aux2)
    from S1 S2 have "c_cons x u = ?R" by simp
    then show ?thesis .
  qed
qed

lemma c_cons_pos: "c_cons x u > 0"
proof cases
  assume "u=0"
  then show "c_cons x u > 0" by (simp add: c_cons_aux1)
next
  assume "\<not> u=0" then have "u>0" by simp
  then show "c_cons x u > 0" by (simp add: c_cons_aux2)
qed

theorem c_cons_is_pr: "c_cons \<in> PrimRec2"
proof -
  have "c_cons = (\<lambda> x u. (sgn2 u)*((c_pair 0 x)+1) + (sgn1 u)*((c_pair (c_len u) (c_pair x (c_snd (u-(1::nat))))) + 1))" (is "_ = ?R") by (simp add: c_cons_aux3)
  moreover from c_pair_is_pr c_len_is_pr have "?R \<in> PrimRec2" by prec
  ultimately show ?thesis by simp
qed

definition
  c_drop :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_drop = PrimRecOp (\<lambda> x. x) (\<lambda> x y z. c_tl y)"

lemma c_drop_at_0 [simp]: "c_drop 0 x = x" by (simp add: c_drop_def)

lemma c_drop_at_Suc: "c_drop (Suc y) x = c_tl (c_drop y x)" by (simp add: c_drop_def)

theorem c_drop_is_pr: "c_drop \<in> PrimRec2"
proof -
  have "(\<lambda> x. x) \<in> PrimRec1" by (rule pr_id1_1)
  moreover from c_tl_is_pr have "(\<lambda> x y z. c_tl y) \<in> PrimRec3" by prec
  ultimately show ?thesis by (simp add: c_drop_def pr_rec)
qed

lemma c_tl_c_drop: "c_tl (c_drop y x) = c_drop y (c_tl x)"
apply(induct y)
apply(simp)
apply(simp add: c_drop_at_Suc)
done

lemma c_drop_at_Suc1: "c_drop (Suc y) x = c_drop y (c_tl x)"
apply(simp add: c_drop_at_Suc c_tl_c_drop)
done

lemma c_drop_df: "\<forall> ls. drop n ls = nat_to_list (c_drop n (list_to_nat ls))"
proof (induct n)
  show "\<forall> ls. drop 0 ls = nat_to_list (c_drop 0 (list_to_nat ls))" by (simp add: c_drop_def)
next
  fix n assume A1: "\<forall> ls. drop n ls = nat_to_list (c_drop n (list_to_nat ls))"
  then show "\<forall> ls. drop (Suc n) ls = nat_to_list (c_drop (Suc n) (list_to_nat ls))"
  proof -
    {
    fix ls::"nat list"
    have S1: "drop (Suc n) ls = drop n (tl ls)" by (rule drop_Suc)
    from A1 have S2: "drop n (tl ls) = nat_to_list (c_drop n (list_to_nat (tl ls)))" by simp
    also have "\<dots> = nat_to_list (c_drop n (c_tl (list_to_nat ls)))" by  (simp add: c_tl_eq_tl)
    also have "\<dots> = nat_to_list (c_drop (Suc n) (list_to_nat ls))" by  (simp add: c_drop_at_Suc1)
    finally have "drop n (tl ls) = nat_to_list (c_drop (Suc n) (list_to_nat ls))" by simp
    with S1 have "drop (Suc n) ls = nat_to_list (c_drop (Suc n) (list_to_nat ls))" by simp    
    }
    then show ?thesis by blast
  qed
qed

definition
  c_nth :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_nth = (\<lambda> x n. c_hd (c_drop n x))"

lemma c_nth_is_pr: "c_nth \<in> PrimRec2"
proof (unfold c_nth_def)
  from c_hd_is_pr c_drop_is_pr show "(\<lambda>x n. c_hd (c_drop n x)) \<in> PrimRec2" by prec
qed

lemma c_nth_at_0: "c_nth x 0 = c_hd x" by (simp add: c_nth_def)

lemma c_hd_c_cons [simp]: "c_hd (c_cons x y) = x"
proof -
  have "c_cons x y > 0" by (rule c_cons_pos)
  then show ?thesis by (simp add: c_hd_def c_cons_def)
qed

lemma c_tl_c_cons [simp]: "c_tl (c_cons x y) = y" by (simp add: c_tl_def c_cons_def)

definition
  c_f_list :: "(nat \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "c_f_list = (\<lambda> f.
    let g = (%x. c_cons (f 0 x) 0); h = (%a b c. c_cons (f (Suc a) c) b) in PrimRecOp g h)"

lemma c_f_list_at_0: "c_f_list f 0 x = c_cons (f 0 x) 0" by (simp add: c_f_list_def Let_def)

lemma c_f_list_at_Suc: "c_f_list f (Suc y) x = c_cons (f (Suc y) x) (c_f_list f y x)" by ((simp add: c_f_list_def Let_def))

lemma c_f_list_is_pr: "f \<in> PrimRec2 \<Longrightarrow> c_f_list f \<in> PrimRec2"
proof -
  assume A1: "f \<in> PrimRec2"
  let ?g = "(%x. c_cons (f 0 x) 0)"
  from A1 c_cons_is_pr have S1: "?g \<in> PrimRec1" by prec
  let ?h = "(%a b c. c_cons (f (Suc a) c) b)"
  from A1 c_cons_is_pr have S2: "?h \<in> PrimRec3" by prec
  from S1 S2 show ?thesis by (simp add: pr_rec c_f_list_def Let_def)
qed

lemma c_f_list_to_f_0: "f y x = c_hd (c_f_list f y x)"
apply(induct y)
apply(simp add: c_f_list_at_0)
apply(simp add: c_f_list_at_Suc)
done

lemma c_f_list_to_f: "f = (\<lambda> y x. c_hd (c_f_list f y x))"
apply(rule ext, rule ext)
apply(rule c_f_list_to_f_0)
done

lemma c_f_list_f_is_pr: "c_f_list f \<in> PrimRec2 \<Longrightarrow> f \<in> PrimRec2"
proof -
  assume A1: "c_f_list f \<in> PrimRec2"
  have S1: "f = (\<lambda> y x. c_hd (c_f_list f y x))" by (rule c_f_list_to_f)
  from A1 c_hd_is_pr have S2: "(\<lambda> y x. c_hd (c_f_list f y x)) \<in> PrimRec2" by prec
  with S1 show ?thesis by simp
qed

lemma c_f_list_lm_1: "c_nth (c_cons x y) (Suc z) = c_nth y z" by (simp add: c_nth_def c_drop_at_Suc1)

lemma c_f_list_lm_2: " z < Suc n \<Longrightarrow> c_nth (c_f_list f (Suc n) x) (Suc n - z) = c_nth (c_f_list f n x) (n - z)"
proof -
  assume "z < Suc n"
  then have "Suc n - z = Suc (n-z)" by arith
  then have "c_nth (c_f_list f (Suc n) x) (Suc n - z) = c_nth (c_f_list f (Suc n) x) (Suc (n - z))" by simp
  also have "\<dots> = c_nth (c_cons (f (Suc n) x) (c_f_list f n x)) (Suc (n - z))" by (simp add: c_f_list_at_Suc)
  also have "\<dots> = c_nth (c_f_list f n x) (n - z)" by (simp add: c_f_list_lm_1)
  finally show ?thesis by simp
qed

lemma c_f_list_nth: "z \<le> y \<longrightarrow> c_nth (c_f_list f y x) (y-z) = f z x"
proof (induct y)
  show "z \<le> 0 \<longrightarrow> c_nth (c_f_list f 0 x) (0 - z) = f z x"
  proof
    assume "z \<le> 0" then have A1: "z=0" by simp
    then have "c_nth (c_f_list f 0 x) (0 - z) = c_nth (c_f_list f 0 x) 0" by simp
    also have "\<dots> = c_hd (c_f_list f 0 x)" by (simp add: c_nth_at_0)
    also have "\<dots> = c_hd (c_cons (f 0 x) 0)" by (simp add: c_f_list_at_0)
    also have "\<dots> = f 0 x" by simp
    finally show "c_nth (c_f_list f 0 x) (0 - z) = f z x" by (simp add: A1)
  qed
next
  fix n assume A2: " z \<le> n \<longrightarrow> c_nth (c_f_list f n x) (n - z) = f z x" show "z \<le> Suc n \<longrightarrow> c_nth (c_f_list f (Suc n) x) (Suc n - z) = f z x"
  proof
    assume A3: "z \<le> Suc n"
    show " z \<le> Suc n \<Longrightarrow> c_nth (c_f_list f (Suc n) x) (Suc n - z) = f z x"
    proof cases
      assume AA1: "z \<le> n"
      then have AA2: "z < Suc n" by simp
      from A2 this have S1: "c_nth (c_f_list f n x) (n - z) = f z x" by auto
      from AA2 have "c_nth (c_f_list f (Suc n) x) (Suc n - z) = c_nth (c_f_list f n x) (n - z)" by (rule c_f_list_lm_2)
      with S1 show "c_nth (c_f_list f (Suc n) x) (Suc n - z) = f z x" by simp
    next
      assume "\<not> z \<le> n"
      from A3 this have S1: "z = Suc n" by simp
      then have S2: "Suc n - z = 0" by simp
      then have "c_nth (c_f_list f (Suc n) x) (Suc n - z) = c_nth (c_f_list f (Suc n) x) 0" by simp
      also have "\<dots> = c_hd (c_f_list f (Suc n) x)" by (simp add: c_nth_at_0)
      also have "\<dots> = c_hd (c_cons (f (Suc n) x) (c_f_list f n x))" by (simp add: c_f_list_at_Suc)
      also have "\<dots> = f (Suc n) x" by simp
      finally show "c_nth (c_f_list f (Suc n) x) (Suc n - z) = f z x" by (simp add: S1)
    qed
  qed
qed

theorem th_pr_rec: "\<lbrakk> g \<in> PrimRec1; h \<in> PrimRec3; (\<forall> x. (f 0 x) = (g x)); (\<forall> x y. (f (Suc y) x) = h y (f y x) x) \<rbrakk> \<Longrightarrow> f \<in> PrimRec2"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  assume h_is_pr: "h \<in> PrimRec3"
  assume f_0: "\<forall> x. f 0 x = g x"
  assume f_1: "\<forall> x y. (f (Suc y) x) = h y (f y x) x"
  let ?f = "PrimRecOp g h"
  from g_is_pr h_is_pr have S1: "?f \<in> PrimRec2" by (rule pr_rec)
  have f_2:"\<forall> x. ?f 0 x = g x" by simp
  have f_3: "\<forall> x y. (?f (Suc y) x) = h y (?f y x) x" by simp
  have S2: "f = ?f"
  proof -
    have "\<And> x y. f y x = ?f y x"
    apply(induct_tac y)
    apply(insert f_0 f_1)
    apply(auto)
    done
    then show "f = ?f" by (simp add: ext)
  qed
  from S1 S2 show ?thesis by simp
qed

theorem th_rec: "\<lbrakk> g \<in> PrimRec1; \<alpha> \<in> PrimRec2; h \<in> PrimRec3; (\<forall> x y. \<alpha> y x \<le> y); (\<forall> x. (f 0 x) = (g x)); (\<forall> x y. (f (Suc y) x) = h y (f (\<alpha> y x) x) x) \<rbrakk> \<Longrightarrow> f \<in> PrimRec2"
proof -
  assume g_is_pr: "g \<in> PrimRec1"
  assume a_is_pr: "\<alpha> \<in> PrimRec2"
  assume h_is_pr: "h \<in> PrimRec3"
  assume a_le: "(\<forall> x y. \<alpha> y x \<le> y)"
  assume f_0: "\<forall> x. f 0 x = g x"
  assume f_1: "\<forall> x y. (f (Suc y) x) = h y (f (\<alpha> y x) x) x"
  let ?g' = "\<lambda> x. c_cons (g x) 0"
  let ?h' = "\<lambda> a b c. c_cons (h a (c_nth b (a - (\<alpha> a c))) c) b"
  let ?r = "c_f_list f"
  from g_is_pr c_cons_is_pr have g'_is_pr: "?g' \<in> PrimRec1" by prec
  from h_is_pr c_cons_is_pr c_nth_is_pr a_is_pr have h'_is_pr: "?h' \<in> PrimRec3" by prec
  have S1: "\<forall> x. ?r 0 x = ?g' x"
  proof
    fix x have "?r 0 x = c_cons (f 0 x) 0" by (rule c_f_list_at_0)
    with f_0 have "?r 0 x = c_cons (g x) 0" by simp
    then show "?r 0 x = ?g' x" by simp
  qed
  have S2: "\<forall> x y. ?r (Suc y) x = ?h' y (?r y x) x"
  proof (rule allI, rule allI)
    fix x y show "?r (Suc y) x = ?h' y (?r y x) x"
    proof -
      have S2_1: "?r (Suc y) x = c_cons (f (Suc y) x) (?r y x)" by (rule c_f_list_at_Suc)
      with f_1 have S2_2: "f (Suc y) x = h y (f (\<alpha> y x) x) x" by simp
      from a_le have S2_3: "\<alpha> y x \<le> y" by simp
      then have S2_4: "f (\<alpha> y x) x = c_nth (?r y x) (y-(\<alpha> y x))" by (simp add: c_f_list_nth)
      from S2_1 S2_2 S2_4 show ?thesis by simp
    qed
  qed
  from g'_is_pr h'_is_pr S1 S2 have S3: "?r \<in> PrimRec2" by (rule th_pr_rec)
  then show "f \<in> PrimRec2" by (rule c_f_list_f_is_pr)
qed

declare c_tl_less [termination_simp]

fun c_assoc_have_key :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  c_assoc_have_key_df [simp del]: "c_assoc_have_key y x = (if y = 0 then 1 else
    (if c_fst (c_hd y) = x then 0 else c_assoc_have_key (c_tl y) x))"

lemma c_assoc_have_key_lm_1: "y \<noteq> 0 \<Longrightarrow> c_assoc_have_key y x = (if c_fst (c_hd y) = x then 0 else c_assoc_have_key (c_tl y) x)" by (simp add: c_assoc_have_key_df)

theorem c_assoc_have_key_is_pr: "c_assoc_have_key \<in> PrimRec2"
proof -
  let ?h = "\<lambda> a b c. if c_fst (c_hd (Suc a)) = c then 0 else b"
  let ?a = "\<lambda> y x. c_tl (Suc y)"
  let ?g = "\<lambda> x. (1::nat)"
  have g_is_pr: "?g \<in> PrimRec1" by (rule const_is_pr)
  from c_tl_is_pr have a_is_pr: "?a \<in> PrimRec2" by prec
  have h_is_pr: "?h \<in> PrimRec3"
  proof (rule if_eq_is_pr3)
    from c_fst_is_pr c_hd_is_pr show "(\<lambda>x y z. c_fst (c_hd (Suc x))) \<in> PrimRec3" by prec
  next
    show "(\<lambda>x y z. z) \<in> PrimRec3" by (rule pr_id3_3)
  next
    show "(\<lambda>x y z. 0) \<in> PrimRec3" by prec
  next
    show "(\<lambda>x y z. y) \<in> PrimRec3" by (rule pr_id3_2)
  qed
  have a_le: "\<forall> x y. ?a y x \<le> y"
  proof (rule allI, rule allI)
    fix x y show "?a y x \<le> y"
    proof -
      have "Suc y > 0" by simp
      then have "?a y x < Suc y" by (rule c_tl_less)
      then show ?thesis by simp
    qed
  qed
  have f_0: "\<forall> x. c_assoc_have_key 0 x = ?g x" by (simp add: c_assoc_have_key_df)
  have f_1: "\<forall> x y. c_assoc_have_key (Suc y) x = ?h y (c_assoc_have_key (?a y x) x) x" by (simp add: c_assoc_have_key_df)
  from g_is_pr a_is_pr h_is_pr a_le f_0 f_1 show ?thesis by (rule th_rec)
qed

fun c_assoc_value :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  c_assoc_value_df [simp del]: "c_assoc_value y x = (if y = 0 then 0 else
    (if c_fst (c_hd y) = x then c_snd (c_hd y) else c_assoc_value (c_tl y) x))"

lemma c_assoc_value_lm_1: "y \<noteq> 0 \<Longrightarrow> c_assoc_value y x = (if c_fst (c_hd y) = x then c_snd (c_hd y) else c_assoc_value (c_tl y) x)" by (simp add: c_assoc_value_df)

theorem c_assoc_value_is_pr: "c_assoc_value \<in> PrimRec2"
proof -
  let ?h = "\<lambda> a b c. if c_fst (c_hd (Suc a)) = c then c_snd (c_hd (Suc a)) else b"
  let ?a = "\<lambda> y x. c_tl (Suc y)"
  let ?g = "\<lambda> x. (0::nat)"
  have g_is_pr: "?g \<in> PrimRec1" by (rule const_is_pr)
  from c_tl_is_pr have a_is_pr: "?a \<in> PrimRec2" by prec
  have h_is_pr: "?h \<in> PrimRec3"
  proof (rule if_eq_is_pr3)
    from c_fst_is_pr c_hd_is_pr show "(\<lambda>x y z. c_fst (c_hd (Suc x))) \<in> PrimRec3" by prec
  next
    show "(\<lambda>x y z. z) \<in> PrimRec3" by (rule pr_id3_3)
  next
    from c_snd_is_pr c_hd_is_pr show "(\<lambda>x y z. c_snd (c_hd (Suc x))) \<in> PrimRec3" by prec
  next
    show "(\<lambda>x y z. y) \<in> PrimRec3" by (rule pr_id3_2)
  qed
  have a_le: "\<forall> x y. ?a y x \<le> y"
  proof (rule allI, rule allI)
    fix x y show "?a y x \<le> y"
    proof -
      have "Suc y > 0" by simp
      then have "?a y x < Suc y" by (rule c_tl_less)
      then show ?thesis by simp
    qed
  qed
  have f_0: "\<forall> x. c_assoc_value 0 x = ?g x" by (simp add: c_assoc_value_df)
  have f_1: "\<forall> x y. c_assoc_value (Suc y) x = ?h y (c_assoc_value (?a y x) x) x" by (simp add: c_assoc_value_df)
  from g_is_pr a_is_pr h_is_pr a_le f_0 f_1 show ?thesis by (rule th_rec)
qed

lemma c_assoc_lm_1: "c_assoc_have_key (c_cons (c_pair x y) z) x = 0"
apply(simp add: c_assoc_have_key_df)
apply(simp add: c_cons_pos)
done

lemma c_assoc_lm_2: "c_assoc_value (c_cons (c_pair x y) z) x = y"
apply(simp add: c_assoc_value_df)
apply(rule impI)
apply(insert c_cons_pos [where x="(c_pair x y)" and u="z"])
apply(auto)
done

lemma c_assoc_lm_3: "x1 \<noteq> x \<Longrightarrow> c_assoc_have_key (c_cons (c_pair x y) z) x1 = c_assoc_have_key z x1"
proof -
  assume A1: "x1 \<noteq> x"
  let ?ls = "(c_cons (c_pair x y) z)"
  have S1: "?ls \<noteq> 0" by (simp add: c_cons_pos)
  then have S2: "c_assoc_have_key ?ls x1 = (if c_fst (c_hd ?ls) = x1 then 0 else c_assoc_have_key (c_tl ?ls) x1)" (is "_ = ?R")  by (rule c_assoc_have_key_lm_1)
  have S3: "c_fst (c_hd ?ls) = x" by simp
  with A1 have S4: "\<not> (c_fst (c_hd ?ls) = x1)" by simp
  from S4 have S5: "?R = c_assoc_have_key (c_tl ?ls) x1" by (rule if_not_P)
  from S2 S5 show ?thesis by simp
qed

lemma c_assoc_lm_4: "x1 \<noteq> x \<Longrightarrow> c_assoc_value (c_cons (c_pair x y) z) x1 = c_assoc_value z x1"
proof -
  assume A1: "x1 \<noteq> x"
  let ?ls = "(c_cons (c_pair x y) z)"
  have S1: "?ls \<noteq> 0" by (simp add: c_cons_pos)
  then have S2: "c_assoc_value ?ls x1 = (if c_fst (c_hd ?ls) = x1 then c_snd (c_hd ?ls) else c_assoc_value (c_tl ?ls) x1)" (is "_ = ?R")  by (rule c_assoc_value_lm_1)
  have S3: "c_fst (c_hd ?ls) = x" by simp
  with A1 have S4: "\<not> (c_fst (c_hd ?ls) = x1)" by simp
  from S4 have S5: "?R = c_assoc_value (c_tl ?ls) x1" by (rule if_not_P)
  from S2 S5 show ?thesis by simp
qed

end
