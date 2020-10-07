(*  Author:     Sebastian Skalberg, TU Muenchen
*)

section \<open>Binary Words\<close>

theory Word
imports Main
begin

subsection \<open>Auxilary Lemmas\<close>

lemma max_le [intro!]: "[| x \<le> z; y \<le> z |] ==> max x y \<le> z"
  by (simp add: max_def)

lemma max_mono:
  fixes x :: "'a::linorder"
  assumes mf: "mono f"
  shows       "max (f x) (f y) \<le> f (max x y)"
proof -
  from mf and max.cobounded1 [of x y]
  have fx: "f x \<le> f (max x y)" by (rule monoD)
  from mf and max.cobounded2 [of y x]
  have fy: "f y \<le> f (max x y)" by (rule monoD)
  from fx and fy
  show "max (f x) (f y) \<le> f (max x y)" by auto
qed

declare zero_le_power [intro]
  and zero_less_power [intro]

lemma int_nat_two_exp: "2 ^ k = int (2 ^ k)"
  by simp


subsection \<open>Bits\<close>

datatype bit =
    Zero ("\<zero>")
  | One ("\<one>")

primrec bitval :: "bit => nat" where
    "bitval \<zero> = 0"
  | "bitval \<one> = 1"

primrec bitnot :: "bit => bit"  ("\<not>\<^sub>b _" [40] 40) where
    bitnot_zero: "(\<not>\<^sub>b \<zero>) = \<one>"
  | bitnot_one : "(\<not>\<^sub>b \<one>) = \<zero>"

primrec bitand :: "bit => bit => bit"  (infixr "\<and>\<^sub>b" 35) where
    bitand_zero: "(\<zero> \<and>\<^sub>b y) = \<zero>"
  | bitand_one:  "(\<one> \<and>\<^sub>b y) = y"

primrec bitor :: "bit => bit => bit"  (infixr "\<or>\<^sub>b" 30) where
    bitor_zero: "(\<zero> \<or>\<^sub>b y) = y"
  | bitor_one:  "(\<one> \<or>\<^sub>b y) = \<one>"

primrec bitxor :: "bit => bit => bit"  (infixr "\<oplus>\<^sub>b" 30) where
    bitxor_zero: "(\<zero> \<oplus>\<^sub>b y) = y"
  | bitxor_one:  "(\<one> \<oplus>\<^sub>b y) = (bitnot y)"

lemma bitnot_bitnot [simp]: "(bitnot (bitnot b)) = b"
  by (cases b) simp_all

lemma bitand_cancel [simp]: "(b \<and>\<^sub>b b) = b"
  by (cases b) simp_all

lemma bitor_cancel [simp]: "(b \<or>\<^sub>b b) = b"
  by (cases b) simp_all

lemma bitxor_cancel [simp]: "(b \<oplus>\<^sub>b b) = \<zero>"
  by (cases b) simp_all


subsection \<open>Bit Vectors\<close>

text \<open>First, a couple of theorems expressing case analysis and
induction principles for bit vectors.\<close>

lemma bit_list_cases:
  assumes empty: "w = [] ==> P w"
  and     zero:  "!!bs. w = \<zero> # bs ==> P w"
  and     one:   "!!bs. w = \<one> # bs ==> P w"
  shows   "P w"
proof (cases w)
  assume "w = []"
  thus ?thesis by (rule empty)
next
  fix b bs
  assume [simp]: "w = b # bs"
  show "P w"
  proof (cases b)
    assume "b = \<zero>"
    hence "w = \<zero> # bs" by simp
    thus ?thesis by (rule zero)
  next
    assume "b = \<one>"
    hence "w = \<one> # bs" by simp
    thus ?thesis by (rule one)
  qed
qed

lemma bit_list_induct:
  assumes empty: "P []"
  and     zero:  "!!bs. P bs ==> P (\<zero>#bs)"
  and     one:   "!!bs. P bs ==> P (\<one>#bs)"
  shows   "P w"
proof (induct w, simp_all add: empty)
  fix b bs
  assume "P bs"
  then show "P (b#bs)"
    by (cases b) (auto intro!: zero one)
qed

definition
  bv_msb :: "bit list => bit" where
  "bv_msb w = (if w = [] then \<zero> else hd w)"

definition
  bv_extend :: "[nat,bit,bit list]=>bit list" where
  "bv_extend i b w = (replicate (i - length w) b) @ w"

definition
  bv_not :: "bit list => bit list" where
  "bv_not w = map bitnot w"

lemma bv_length_extend [simp]: "length w \<le> i ==> length (bv_extend i b w) = i"
  by (simp add: bv_extend_def)

lemma bv_not_Nil [simp]: "bv_not [] = []"
  by (simp add: bv_not_def)

lemma bv_not_Cons [simp]: "bv_not (b#bs) = (bitnot b) # bv_not bs"
  by (simp add: bv_not_def)

lemma bv_not_bv_not [simp]: "bv_not (bv_not w) = w"
  by (rule bit_list_induct [of _ w]) simp_all

lemma bv_msb_Nil [simp]: "bv_msb [] = \<zero>"
  by (simp add: bv_msb_def)

lemma bv_msb_Cons [simp]: "bv_msb (b#bs) = b"
  by (simp add: bv_msb_def)

lemma bv_msb_bv_not [simp]: "0 < length w ==> bv_msb (bv_not w) = (bitnot (bv_msb w))"
  by (cases w) simp_all

lemma bv_msb_one_length [simp,intro]: "bv_msb w = \<one> ==> 0 < length w"
  by (cases w) simp_all

lemma length_bv_not [simp]: "length (bv_not w) = length w"
  by (induct w) simp_all

definition
  bv_to_nat :: "bit list => nat" where
  "bv_to_nat = foldl (%bn b. 2 * bn + bitval b) 0"

lemma bv_to_nat_Nil [simp]: "bv_to_nat [] = 0"
  by (simp add: bv_to_nat_def)

lemma bv_to_nat_helper [simp]: "bv_to_nat (b # bs) = bitval b * 2 ^ length bs + bv_to_nat bs"
proof -
  let ?bv_to_nat' = "foldl (\<lambda>bn b. 2 * bn + bitval b)"
  have helper: "\<And>base. ?bv_to_nat' base bs = base * 2 ^ length bs + ?bv_to_nat' 0 bs"
  proof (induct bs)
    case Nil
    show ?case by simp
  next
    case (Cons x xs base)
    show ?case
      apply (simp only: foldl_Cons)
      apply (subst Cons [of "2 * base + bitval x"])
      apply simp
      apply (subst Cons [of "bitval x"])
      apply (simp add: add_mult_distrib)
      done
  qed
  show ?thesis by (simp add: bv_to_nat_def) (rule helper)
qed

lemma bv_to_nat0 [simp]: "bv_to_nat (\<zero>#bs) = bv_to_nat bs"
  by simp

lemma bv_to_nat1 [simp]: "bv_to_nat (\<one>#bs) = 2 ^ length bs + bv_to_nat bs"
  by simp

lemma bv_to_nat_upper_range: "bv_to_nat w < 2 ^ length w"
proof (induct w, simp_all)
  fix b bs
  assume "bv_to_nat bs < 2 ^ length bs"
  show "bitval b * 2 ^ length bs + bv_to_nat bs < 2 * 2 ^ length bs"
  proof (cases b, simp_all)
    have "bv_to_nat bs < 2 ^ length bs" by fact
    also have "... < 2 * 2 ^ length bs" by auto
    finally show "bv_to_nat bs < 2 * 2 ^ length bs" by simp
  next
    have "bv_to_nat bs < 2 ^ length bs" by fact
    hence "2 ^ length bs + bv_to_nat bs < 2 ^ length bs + 2 ^ length bs" by arith
    also have "... = 2 * (2 ^ length bs)" by simp
    finally show "bv_to_nat bs < 2 ^ length bs" by simp
  qed
qed

lemma bv_extend_longer [simp]:
  assumes wn: "n \<le> length w"
  shows       "bv_extend n b w = w"
  by (simp add: bv_extend_def wn)

lemma bv_extend_shorter [simp]:
  assumes wn: "length w < n"
  shows       "bv_extend n b w = bv_extend n b (b#w)"
proof -
  from wn
  have s: "n - Suc (length w) + 1 = n - length w"
    by arith
  have "bv_extend n b w = replicate (n - length w) b @ w"
    by (simp add: bv_extend_def)
  also have "... = replicate (n - Suc (length w) + 1) b @ w"
    by (subst s) rule
  also have "... = (replicate (n - Suc (length w)) b @ replicate 1 b) @ w"
    by (subst replicate_add) rule
  also have "... = replicate (n - Suc (length w)) b @ b # w"
    by simp
  also have "... = bv_extend n b (b#w)"
    by (simp add: bv_extend_def)
  finally show "bv_extend n b w = bv_extend n b (b#w)" .
qed

primrec rem_initial :: "bit => bit list => bit list" where
    "rem_initial b [] = []"
  | "rem_initial b (x#xs) = (if b = x then rem_initial b xs else x#xs)"

lemma rem_initial_length: "length (rem_initial b w) \<le> length w"
  by (rule bit_list_induct [of _ w],simp_all (no_asm),safe,simp_all)

lemma rem_initial_equal:
  assumes p: "length (rem_initial b w) = length w"
  shows      "rem_initial b w = w"
proof -
  have "length (rem_initial b w) = length w --> rem_initial b w = w"
  proof (induct w, simp_all, clarify)
    fix xs
    assume "length (rem_initial b xs) = length xs --> rem_initial b xs = xs"
    assume f: "length (rem_initial b xs) = Suc (length xs)"
    with rem_initial_length [of b xs]
    show "rem_initial b xs = b#xs"
      by auto
  qed
  from this and p show ?thesis ..
qed

lemma bv_extend_rem_initial: "bv_extend (length w) b (rem_initial b w) = w"
proof (induct w, simp_all, safe)
  fix xs
  assume ind: "bv_extend (length xs) b (rem_initial b xs) = xs"
  from rem_initial_length [of b xs]
  have [simp]: "Suc (length xs) - length (rem_initial b xs) =
      1 + (length xs - length (rem_initial b xs))"
    by arith
  have "bv_extend (Suc (length xs)) b (rem_initial b xs) =
      replicate (Suc (length xs) - length (rem_initial b xs)) b @ (rem_initial b xs)"
    by (simp add: bv_extend_def)
  also have "... =
      replicate (1 + (length xs - length (rem_initial b xs))) b @ rem_initial b xs"
    by simp
  also have "... =
      (replicate 1 b @ replicate (length xs - length (rem_initial b xs)) b) @ rem_initial b xs"
    by (subst replicate_add) (rule refl)
  also have "... = b # bv_extend (length xs) b (rem_initial b xs)"
    by (auto simp add: bv_extend_def [symmetric])
  also have "... = b # xs"
    by (simp add: ind)
  finally show "bv_extend (Suc (length xs)) b (rem_initial b xs) = b # xs" .
qed

lemma rem_initial_append1:
  assumes "rem_initial b xs ~= []"
  shows   "rem_initial b (xs @ ys) = rem_initial b xs @ ys"
  using assms by (induct xs) auto

lemma rem_initial_append2:
  assumes "rem_initial b xs = []"
  shows   "rem_initial b (xs @ ys) = rem_initial b ys"
  using assms by (induct xs) auto

definition
  norm_unsigned :: "bit list => bit list" where
  "norm_unsigned = rem_initial \<zero>"

lemma norm_unsigned_Nil [simp]: "norm_unsigned [] = []"
  by (simp add: norm_unsigned_def)

lemma norm_unsigned_Cons0 [simp]: "norm_unsigned (\<zero>#bs) = norm_unsigned bs"
  by (simp add: norm_unsigned_def)

lemma norm_unsigned_Cons1 [simp]: "norm_unsigned (\<one>#bs) = \<one>#bs"
  by (simp add: norm_unsigned_def)

lemma norm_unsigned_idem [simp]: "norm_unsigned (norm_unsigned w) = norm_unsigned w"
  by (rule bit_list_induct [of _ w],simp_all)

fun
  nat_to_bv_helper :: "nat => bit list => bit list"
where
  "nat_to_bv_helper n bs = (if n = 0 then bs
                               else nat_to_bv_helper (n div 2) ((if n mod 2 = 0 then \<zero> else \<one>)#bs))"

definition
  nat_to_bv :: "nat => bit list" where
  "nat_to_bv n = nat_to_bv_helper n []"

lemma nat_to_bv0 [simp]: "nat_to_bv 0 = []"
  by (simp add: nat_to_bv_def)

lemmas [simp del] = nat_to_bv_helper.simps

lemma n_div_2_cases:
  assumes zero: "(n::nat) = 0 ==> R"
  and     div : "[| n div 2 < n ; 0 < n |] ==> R"
  shows         "R"
proof (cases "n = 0")
  assume "n = 0"
  thus R by (rule zero)
next
  assume "n ~= 0"
  hence "0 < n" by simp
  hence "n div 2 < n" by arith
  from this and \<open>0 < n\<close> show R by (rule div)
qed

lemma int_wf_ge_induct:
  assumes ind :  "!!i::int. (!!j. [| k \<le> j ; j < i |] ==> P j) ==> P i"
  shows          "P i"
proof (rule wf_induct_rule [OF wf_int_ge_less_than])
  fix x
  assume ih: "(\<And>y::int. (y, x) \<in> int_ge_less_than k \<Longrightarrow> P y)"
  thus "P x"
    by (rule ind) (simp add: int_ge_less_than_def)
qed

lemma unfold_nat_to_bv_helper:
  "nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
proof -
  have "\<forall>l. nat_to_bv_helper b l = nat_to_bv_helper b [] @ l"
  proof (induct b rule: less_induct)
    fix n
    assume ind: "!!j. j < n \<Longrightarrow> \<forall> l. nat_to_bv_helper j l = nat_to_bv_helper j [] @ l"
    show "\<forall>l. nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
    proof
      fix l
      show "nat_to_bv_helper n l = nat_to_bv_helper n [] @ l"
      proof (cases "n < 0")
        assume "n < 0"
        thus ?thesis
          by (simp add: nat_to_bv_helper.simps)
      next
        assume "~n < 0"
        show ?thesis
        proof (rule n_div_2_cases [of n])
          assume [simp]: "n = 0"
          show ?thesis
            apply (simp only: nat_to_bv_helper.simps [of n])
            apply simp
            done
        next
          assume n2n: "n div 2 < n"
          assume [simp]: "0 < n"
          hence n20: "0 \<le> n div 2"
            by arith
          from ind [of "n div 2"] and n2n n20
          have ind': "\<forall>l. nat_to_bv_helper (n div 2) l = nat_to_bv_helper (n div 2) [] @ l"
            by blast
          show ?thesis
            apply (simp only: nat_to_bv_helper.simps [of n])
            apply (cases "n=0")
            apply simp
            apply (simp only: if_False)
            apply simp
            apply (subst spec [OF ind',of "\<zero>#l"])
            apply (subst spec [OF ind',of "\<one>#l"])
            apply (subst spec [OF ind',of "[\<one>]"])
            apply (subst spec [OF ind',of "[\<zero>]"])
            apply simp
            done
        qed
      qed
    qed
  qed
  thus ?thesis ..
qed

lemma nat_to_bv_non0 [simp]: "n\<noteq>0 ==> nat_to_bv n = nat_to_bv (n div 2) @ [if n mod 2 = 0 then \<zero> else \<one>]"
proof -
  assume n: "n\<noteq>0"
  show ?thesis
    apply (subst nat_to_bv_def [of n])
    apply (simp only: nat_to_bv_helper.simps [of n])
    apply (subst unfold_nat_to_bv_helper)
    apply (simp add: n)
    apply (subst nat_to_bv_def [of "n div 2"])
    apply auto
    done
qed

lemma bv_to_nat_dist_append:
  "bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
proof -
  have "\<forall>l2. bv_to_nat (l1 @ l2) = bv_to_nat l1 * 2 ^ length l2 + bv_to_nat l2"
  proof (induct l1, simp_all)
    fix x xs
    assume ind: "\<forall>l2. bv_to_nat (xs @ l2) = bv_to_nat xs * 2 ^ length l2 + bv_to_nat l2"
    show "\<forall>l2::bit list. bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
    proof
      fix l2
      show "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
      proof -
        have "(2::nat) ^ (length xs + length l2) = 2 ^ length xs * 2 ^ length l2"
          by (induct ("length xs")) simp_all
        hence "bitval x * 2 ^ (length xs + length l2) + bv_to_nat xs * 2 ^ length l2 =
          bitval x * 2 ^ length xs * 2 ^ length l2 + bv_to_nat xs * 2 ^ length l2"
          by simp
        also have "... = (bitval x * 2 ^ length xs + bv_to_nat xs) * 2 ^ length l2"
          by (simp add: ring_distribs)
        finally show ?thesis by simp
      qed
    qed
  qed
  thus ?thesis ..
qed

lemma bv_nat_bv [simp]: "bv_to_nat (nat_to_bv n) = n"
proof (induct n rule: less_induct)
  fix n
  assume ind: "!!j. j < n \<Longrightarrow> bv_to_nat (nat_to_bv j) = j"
  show "bv_to_nat (nat_to_bv n) = n"
  proof (rule n_div_2_cases [of n])
    assume "n = 0" then show ?thesis by simp
  next
    assume nn: "n div 2 < n"
    assume n0: "0 < n"
    from ind and nn
    have ind': "bv_to_nat (nat_to_bv (n div 2)) = n div 2" by blast
    from n0 have n0': "n \<noteq> 0" by simp
    show ?thesis
      apply (subst nat_to_bv_def)
      apply (simp only: nat_to_bv_helper.simps [of n])
      apply (simp only: n0' if_False)
      apply (subst unfold_nat_to_bv_helper)
      apply (subst bv_to_nat_dist_append)
      apply (fold nat_to_bv_def)
      apply (simp add: ind' split del: if_split)
      apply (cases "n mod 2 = 0")
      proof (simp_all)
        assume "n mod 2 = 0"
        with div_mult_mod_eq [of n 2]
        show "n div 2 * 2 = n" by simp
      next
        assume "n mod 2 = Suc 0"
        with div_mult_mod_eq [of n 2]
        show "Suc (n div 2 * 2) = n" by arith
      qed
  qed
qed

lemma bv_to_nat_type [simp]: "bv_to_nat (norm_unsigned w) = bv_to_nat w"
  by (rule bit_list_induct) simp_all

lemma length_norm_unsigned_le [simp]: "length (norm_unsigned w) \<le> length w"
  by (rule bit_list_induct) simp_all

lemma bv_to_nat_rew_msb: "bv_msb w = \<one> ==> bv_to_nat w = 2 ^ (length w - 1) + bv_to_nat (tl w)"
  by (rule bit_list_cases [of w]) simp_all

lemma norm_unsigned_result: "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = \<one>"
proof (rule length_induct [of _ xs])
  fix xs :: "bit list"
  assume ind: "\<forall>ys. length ys < length xs --> norm_unsigned ys = [] \<or> bv_msb (norm_unsigned ys) = \<one>"
  show "norm_unsigned xs = [] \<or> bv_msb (norm_unsigned xs) = \<one>"
  proof (rule bit_list_cases [of xs],simp_all)
    fix bs
    assume [simp]: "xs = \<zero>#bs"
    from ind
    have "length bs < length xs --> norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = \<one>" ..
    thus "norm_unsigned bs = [] \<or> bv_msb (norm_unsigned bs) = \<one>" by simp
  qed
qed

lemma norm_empty_bv_to_nat_zero:
  assumes nw: "norm_unsigned w = []"
  shows       "bv_to_nat w = 0"
proof -
  have "bv_to_nat w = bv_to_nat (norm_unsigned w)" by simp
  also have "... = bv_to_nat []" by (subst nw) (rule refl)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma bv_to_nat_lower_limit:
  assumes w0: "0 < bv_to_nat w"
  shows "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat w"
proof -
  from w0 and norm_unsigned_result [of w]
  have msbw: "bv_msb (norm_unsigned w) = \<one>"
    by (auto simp add: norm_empty_bv_to_nat_zero)
  have "2 ^ (length (norm_unsigned w) - 1) \<le> bv_to_nat (norm_unsigned w)"
    by (subst bv_to_nat_rew_msb [OF msbw],simp)
  thus ?thesis by simp
qed

lemmas [simp del] = nat_to_bv_non0

lemma norm_unsigned_length [intro!]: "length (norm_unsigned w) \<le> length w"
by (subst norm_unsigned_def,rule rem_initial_length)

lemma norm_unsigned_equal:
  "length (norm_unsigned w) = length w ==> norm_unsigned w = w"
by (simp add: norm_unsigned_def,rule rem_initial_equal)

lemma bv_extend_norm_unsigned: "bv_extend (length w) \<zero> (norm_unsigned w) = w"
by (simp add: norm_unsigned_def,rule bv_extend_rem_initial)

lemma norm_unsigned_append1 [simp]:
  "norm_unsigned xs \<noteq> [] ==> norm_unsigned (xs @ ys) = norm_unsigned xs @ ys"
by (simp add: norm_unsigned_def,rule rem_initial_append1)

lemma norm_unsigned_append2 [simp]:
  "norm_unsigned xs = [] ==> norm_unsigned (xs @ ys) = norm_unsigned ys"
by (simp add: norm_unsigned_def,rule rem_initial_append2)

lemma bv_to_nat_zero_imp_empty:
  "bv_to_nat w = 0 \<Longrightarrow> norm_unsigned w = []"
by (atomize (full), induct w rule: bit_list_induct) simp_all

lemma bv_to_nat_nzero_imp_nempty:
  "bv_to_nat w \<noteq> 0 \<Longrightarrow> norm_unsigned w \<noteq> []"
by (induct w rule: bit_list_induct) simp_all

lemma nat_helper1:
  assumes ass: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
  shows        "nat_to_bv (2 * bv_to_nat w + bitval x) = norm_unsigned (w @ [x])"
proof (cases x)
  assume [simp]: "x = \<one>"
  have "nat_to_bv (Suc (2 * bv_to_nat w) div 2) @ [\<one>] =
      nat_to_bv ((1 + 2 * bv_to_nat w) div 2) @ [\<one>]"
    by (simp add: add.commute)
  also have "... = nat_to_bv (bv_to_nat w) @ [\<one>]"
    by (subst div_add1_eq) simp
  also have "... = norm_unsigned w @ [\<one>]"
    by (subst ass) (rule refl)
  also have "... = norm_unsigned (w @ [\<one>])"
    by (cases "norm_unsigned w") simp_all
  finally have "nat_to_bv (Suc (2 * bv_to_nat w) div 2) @ [\<one>] = norm_unsigned (w @ [\<one>])" .
  then show ?thesis by (simp add: nat_to_bv_non0)
next
  assume [simp]: "x = \<zero>"
  show ?thesis
  proof (cases "bv_to_nat w = 0")
    assume "bv_to_nat w = 0"
    thus ?thesis
      by (simp add: bv_to_nat_zero_imp_empty)
  next
    assume "bv_to_nat w \<noteq> 0"
    thus ?thesis
      apply simp
      apply (subst nat_to_bv_non0)
      apply simp
      apply auto
      apply (subst ass)
      apply (cases "norm_unsigned w")
      apply (simp_all add: norm_empty_bv_to_nat_zero)
      done
  qed
qed

lemma nat_helper2: "nat_to_bv (2 ^ length xs + bv_to_nat xs) = \<one> # xs"
proof -
  have "\<forall>xs. nat_to_bv (2 ^ length (rev xs) + bv_to_nat (rev xs)) = \<one> # (rev xs)" (is "\<forall>xs. ?P xs")
  proof
    fix xs
    show "?P xs"
    proof (rule length_induct [of _ xs])
      fix xs :: "bit list"
      assume ind: "\<forall>ys. length ys < length xs --> ?P ys"
      show "?P xs"
      proof (cases xs)
        assume "xs = []"
        then show ?thesis by (simp add: nat_to_bv_non0)
      next
        fix y ys
        assume [simp]: "xs = y # ys"
        show ?thesis
          apply simp
          apply (subst bv_to_nat_dist_append)
          apply simp
        proof -
          have "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) =
            nat_to_bv (2 * (2 ^ length ys + bv_to_nat (rev ys)) + bitval y)"
            by (simp add: ac_simps ac_simps)
          also have "... = nat_to_bv (2 * (bv_to_nat (\<one>#rev ys)) + bitval y)"
            by simp
          also have "... = norm_unsigned (\<one>#rev ys) @ [y]"
          proof -
            from ind
            have "nat_to_bv (2 ^ length (rev ys) + bv_to_nat (rev ys)) = \<one> # rev ys"
              by auto
            hence [simp]: "nat_to_bv (2 ^ length ys + bv_to_nat (rev ys)) = \<one> # rev ys"
              by simp
            show ?thesis
              apply (subst nat_helper1)
              apply simp_all
              done
          qed
          also have "... = (\<one>#rev ys) @ [y]"
            by simp
          also have "... = \<one> # rev ys @ [y]"
            by simp
          finally show "nat_to_bv (2 * 2 ^ length ys + (bv_to_nat (rev ys) * 2 + bitval y)) =
              \<one> # rev ys @ [y]" .
        qed
      qed
    qed
  qed
  hence "nat_to_bv (2 ^ length (rev (rev xs)) + bv_to_nat (rev (rev xs))) =
      \<one> # rev (rev xs)" ..
  thus ?thesis by simp
qed

lemma nat_bv_nat [simp]: "nat_to_bv (bv_to_nat w) = norm_unsigned w"
proof (rule bit_list_induct [of _ w],simp_all)
  fix xs
  assume "nat_to_bv (bv_to_nat xs) = norm_unsigned xs"
  have "bv_to_nat xs = bv_to_nat (norm_unsigned xs)" by simp
  have "bv_to_nat xs < 2 ^ length xs"
    by (rule bv_to_nat_upper_range)
  show "nat_to_bv (2 ^ length xs + bv_to_nat xs) = \<one> # xs"
    by (rule nat_helper2)
qed

lemma bv_to_nat_qinj:
  assumes one: "bv_to_nat xs = bv_to_nat ys"
  and     len: "length xs = length ys"
  shows        "xs = ys"
proof -
  from one
  have "nat_to_bv (bv_to_nat xs) = nat_to_bv (bv_to_nat ys)"
    by simp
  hence xsys: "norm_unsigned xs = norm_unsigned ys"
    by simp
  have "xs = bv_extend (length xs) \<zero> (norm_unsigned xs)"
    by (simp add: bv_extend_norm_unsigned)
  also have "... = bv_extend (length ys) \<zero> (norm_unsigned ys)"
    by (simp add: xsys len)
  also have "... = ys"
    by (simp add: bv_extend_norm_unsigned)
  finally show ?thesis .
qed

lemma norm_unsigned_nat_to_bv [simp]:
  "norm_unsigned (nat_to_bv n) = nat_to_bv n"
proof -
  have "norm_unsigned (nat_to_bv n) = nat_to_bv (bv_to_nat (norm_unsigned (nat_to_bv n)))"
    by (subst nat_bv_nat) simp
  also have "... = nat_to_bv n" by simp
  finally show ?thesis .
qed

lemma length_nat_to_bv_upper_limit:
  assumes nk: "n \<le> 2 ^ k - 1"
  shows       "length (nat_to_bv n) \<le> k"
proof (cases "n = 0")
  case True
  thus ?thesis
    by (simp add: nat_to_bv_def nat_to_bv_helper.simps)
next
  case False
  hence n0: "0 < n" by simp
  show ?thesis
  proof (rule ccontr)
    assume "~ length (nat_to_bv n) \<le> k"
    hence "k < length (nat_to_bv n)" by simp
    hence "k \<le> length (nat_to_bv n) - 1" by arith
    hence "(2::nat) ^ k \<le> 2 ^ (length (nat_to_bv n) - 1)" by simp
    also have "... = 2 ^ (length (norm_unsigned (nat_to_bv n)) - 1)" by simp
    also have "... \<le> bv_to_nat (nat_to_bv n)"
      by (rule bv_to_nat_lower_limit) (simp add: n0)
    also have "... = n" by simp
    finally have "2 ^ k \<le> n" .
    with n0 have "2 ^ k - 1 < n" by arith
    with nk show False by simp
  qed
qed

lemma length_nat_to_bv_lower_limit:
  assumes nk: "2 ^ k \<le> n"
  shows       "k < length (nat_to_bv n)"
proof (rule ccontr)
  assume "~ k < length (nat_to_bv n)"
  hence lnk: "length (nat_to_bv n) \<le> k" by simp
  have "n = bv_to_nat (nat_to_bv n)" by simp
  also have "... < 2 ^ length (nat_to_bv n)"
    by (rule bv_to_nat_upper_range)
  also from lnk have "... \<le> 2 ^ k" by simp
  finally have "n < 2 ^ k" .
  with nk show False by simp
qed


subsection \<open>Unsigned Arithmetic Operations\<close>

definition
  bv_add :: "[bit list, bit list ] => bit list" where
  "bv_add w1 w2 = nat_to_bv (bv_to_nat w1 + bv_to_nat w2)"

lemma bv_add_type1 [simp]: "bv_add (norm_unsigned w1) w2 = bv_add w1 w2"
  by (simp add: bv_add_def)

lemma bv_add_type2 [simp]: "bv_add w1 (norm_unsigned w2) = bv_add w1 w2"
  by (simp add: bv_add_def)

lemma bv_add_returntype [simp]: "norm_unsigned (bv_add w1 w2) = bv_add w1 w2"
  by (simp add: bv_add_def)

lemma bv_add_length: "length (bv_add w1 w2) \<le> Suc (max (length w1) (length w2))"
proof (unfold bv_add_def,rule length_nat_to_bv_upper_limit)
  from bv_to_nat_upper_range [of w1] and bv_to_nat_upper_range [of w2]
  have "bv_to_nat w1 + bv_to_nat w2 \<le> (2 ^ length w1 - 1) + (2 ^ length w2 - 1)"
    by arith
  also have "... \<le>
      max (2 ^ length w1 - 1) (2 ^ length w2 - 1) + max (2 ^ length w1 - 1) (2 ^ length w2 - 1)"
    by (rule add_mono,safe intro!: max.cobounded1 max.cobounded2)
  also have "... = 2 * max (2 ^ length w1 - 1) (2 ^ length w2 - 1)" by simp
  also have "... \<le> 2 ^ Suc (max (length w1) (length w2)) - 2"
  proof (cases "length w1 \<le> length w2")
    assume w1w2: "length w1 \<le> length w2"
    hence "(2::nat) ^ length w1 \<le> 2 ^ length w2" by simp
    hence "(2::nat) ^ length w1 - 1 \<le> 2 ^ length w2 - 1" by arith
    with w1w2 show ?thesis
      by (simp add: diff_mult_distrib2 split: split_max)
  next
    assume [simp]: "~ (length w1 \<le> length w2)"
    have "~ ((2::nat) ^ length w1 - 1 \<le> 2 ^ length w2 - 1)"
    proof
      assume "(2::nat) ^ length w1 - 1 \<le> 2 ^ length w2 - 1"
      hence "((2::nat) ^ length w1 - 1) + 1 \<le> (2 ^ length w2 - 1) + 1"
        by (rule add_right_mono)
      hence "(2::nat) ^ length w1 \<le> 2 ^ length w2" by simp
      hence "length w1 \<le> length w2" by simp
      thus False by simp
    qed
    thus ?thesis
      by (simp add: diff_mult_distrib2 split: split_max)
  qed
  finally show "bv_to_nat w1 + bv_to_nat w2 \<le> 2 ^ Suc (max (length w1) (length w2)) - 1"
    by arith
qed

definition
  bv_mult :: "[bit list, bit list ] => bit list" where
  "bv_mult w1 w2 = nat_to_bv (bv_to_nat w1 * bv_to_nat w2)"

lemma bv_mult_type1 [simp]: "bv_mult (norm_unsigned w1) w2 = bv_mult w1 w2"
  by (simp add: bv_mult_def)

lemma bv_mult_type2 [simp]: "bv_mult w1 (norm_unsigned w2) = bv_mult w1 w2"
  by (simp add: bv_mult_def)

lemma bv_mult_returntype [simp]: "norm_unsigned (bv_mult w1 w2) = bv_mult w1 w2"
  by (simp add: bv_mult_def)

lemma bv_mult_length: "length (bv_mult w1 w2) \<le> length w1 + length w2"
proof (unfold bv_mult_def,rule length_nat_to_bv_upper_limit)
  from bv_to_nat_upper_range [of w1] and bv_to_nat_upper_range [of w2]
  have h: "bv_to_nat w1 \<le> 2 ^ length w1 - 1 \<and> bv_to_nat w2 \<le> 2 ^ length w2 - 1"
    by arith
  have "bv_to_nat w1 * bv_to_nat w2 \<le> (2 ^ length w1 - 1) * (2 ^ length w2 - 1)"
    apply (cut_tac h)
    apply (rule mult_mono)
    apply auto
    done
  also have "... < 2 ^ length w1 * 2 ^ length w2"
    by (rule mult_strict_mono,auto)
  also have "... = 2 ^ (length w1 + length w2)"
    by (simp add: power_add)
  finally show "bv_to_nat w1 * bv_to_nat w2 \<le> 2 ^ (length w1 + length w2) - 1"
    by arith
qed

subsection \<open>Signed Vectors\<close>

primrec norm_signed :: "bit list => bit list" where
    norm_signed_Nil: "norm_signed [] = []"
  | norm_signed_Cons: "norm_signed (b#bs) =
      (case b of
        \<zero> => if norm_unsigned bs = [] then [] else b#norm_unsigned bs
      | \<one> => b#rem_initial b bs)"

lemma norm_signed0 [simp]: "norm_signed [\<zero>] = []"
  by simp

lemma norm_signed1 [simp]: "norm_signed [\<one>] = [\<one>]"
  by simp

lemma norm_signed01 [simp]: "norm_signed (\<zero>#\<one>#xs) = \<zero>#\<one>#xs"
  by simp

lemma norm_signed00 [simp]: "norm_signed (\<zero>#\<zero>#xs) = norm_signed (\<zero>#xs)"
  by simp

lemma norm_signed10 [simp]: "norm_signed (\<one>#\<zero>#xs) = \<one>#\<zero>#xs"
  by simp

lemma norm_signed11 [simp]: "norm_signed (\<one>#\<one>#xs) = norm_signed (\<one>#xs)"
  by simp

lemmas [simp del] = norm_signed_Cons

definition
  int_to_bv :: "int => bit list" where
  "int_to_bv n = (if 0 \<le> n
                 then norm_signed (\<zero>#nat_to_bv (nat n))
                 else norm_signed (bv_not (\<zero>#nat_to_bv (nat (-n- 1)))))"

lemma int_to_bv_ge0 [simp]: "0 \<le> n ==> int_to_bv n = norm_signed (\<zero> # nat_to_bv (nat n))"
  by (simp add: int_to_bv_def)

lemma int_to_bv_lt0 [simp]:
    "n < 0 ==> int_to_bv n = norm_signed (bv_not (\<zero>#nat_to_bv (nat (-n- 1))))"
  by (simp add: int_to_bv_def)

lemma norm_signed_idem [simp]: "norm_signed (norm_signed w) = norm_signed w"
proof (rule bit_list_induct [of _ w], simp_all)
  fix xs
  assume eq: "norm_signed (norm_signed xs) = norm_signed xs"
  show "norm_signed (norm_signed (\<zero>#xs)) = norm_signed (\<zero>#xs)"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume "xs = \<zero>#ys"
    from this [symmetric] and eq
    show "norm_signed (norm_signed (\<zero>#ys)) = norm_signed (\<zero>#ys)"
      by simp
  qed
next
  fix xs
  assume eq: "norm_signed (norm_signed xs) = norm_signed xs"
  show "norm_signed (norm_signed (\<one>#xs)) = norm_signed (\<one>#xs)"
  proof (rule bit_list_cases [of xs],simp_all)
    fix ys
    assume "xs = \<one>#ys"
    from this [symmetric] and eq
    show "norm_signed (norm_signed (\<one>#ys)) = norm_signed (\<one>#ys)"
      by simp
  qed
qed

definition
  bv_to_int :: "bit list => int" where
  "bv_to_int w =
    (case bv_msb w of \<zero> => int (bv_to_nat w)
    | \<one> => - int (bv_to_nat (bv_not w) + 1))"

lemma bv_to_int_Nil [simp]: "bv_to_int [] = 0"
  by (simp add: bv_to_int_def)

lemma bv_to_int_Cons0 [simp]: "bv_to_int (\<zero>#bs) = int (bv_to_nat bs)"
  by (simp add: bv_to_int_def)

lemma bv_to_int_Cons1 [simp]: "bv_to_int (\<one>#bs) = - int (bv_to_nat (bv_not bs) + 1)"
  by (simp add: bv_to_int_def)

lemma bv_to_int_type [simp]: "bv_to_int (norm_signed w) = bv_to_int w"
proof (rule bit_list_induct [of _ w], simp_all)
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show "bv_to_int (norm_signed (\<zero>#xs)) = int (bv_to_nat xs)"
  proof (rule bit_list_cases [of xs], simp_all)
    fix ys
    assume [simp]: "xs = \<zero>#ys"
    from ind
    show "bv_to_int (norm_signed (\<zero>#ys)) = int (bv_to_nat ys)"
      by simp
  qed
next
  fix xs
  assume ind: "bv_to_int (norm_signed xs) = bv_to_int xs"
  show "bv_to_int (norm_signed (\<one>#xs)) = -1 - int (bv_to_nat (bv_not xs))"
  proof (rule bit_list_cases [of xs], simp_all)
    fix ys
    assume [simp]: "xs = \<one>#ys"
    from ind
    show "bv_to_int (norm_signed (\<one>#ys)) = -1 - int (bv_to_nat (bv_not ys))"
      by simp
  qed
qed

lemma bv_to_int_upper_range: "bv_to_int w < 2 ^ (length w - 1)"
proof (rule bit_list_cases [of w],simp_all add: bv_to_nat_upper_range)
  fix bs
  have "-1 - int (bv_to_nat (bv_not bs)) \<le> 0" by simp
  also have "... < 2 ^ length bs" by (induct bs) simp_all
  finally show "-1 - int (bv_to_nat (bv_not bs)) < 2 ^ length bs" .
qed

lemma bv_to_int_lower_range: "- (2 ^ (length w - 1)) \<le> bv_to_int w"
proof (rule bit_list_cases [of w],simp_all)
  fix bs :: "bit list"
  have "- (2 ^ length bs) \<le> (0::int)" by (induct bs) simp_all
  also have "... \<le> int (bv_to_nat bs)" by simp
  finally show "- (2 ^ length bs) \<le> int (bv_to_nat bs)" .
next
  fix bs
  from bv_to_nat_upper_range [of "bv_not bs"]
  show "- (2 ^ length bs) \<le> -1 - int (bv_to_nat (bv_not bs))"
    apply (simp add: algebra_simps) 
    by (metis of_nat_power add.commute not_less of_nat_numeral zle_add1_eq_le of_nat_le_iff)
qed

lemma int_bv_int [simp]: "int_to_bv (bv_to_int w) = norm_signed w"
proof (rule bit_list_cases [of w],simp)
  fix xs
  assume [simp]: "w = \<zero>#xs"
  show ?thesis
    apply simp
    apply (subst norm_signed_Cons [of "\<zero>" "xs"])
    apply simp
    using norm_unsigned_result [of xs]
    apply safe
    apply (rule bit_list_cases [of "norm_unsigned xs"])
    apply simp_all
    done
next
  fix xs
  assume [simp]: "w = \<one>#xs"
  show ?thesis
    apply (simp del: int_to_bv_lt0)
    apply (rule bit_list_induct [of _ xs], simp)
     apply (subst int_to_bv_lt0)
      apply linarith
     apply simp
     apply (metis add.commute bitnot_zero bv_not_Cons bv_not_bv_not int_nat_two_exp length_bv_not nat_helper2 nat_int norm_signed10 of_nat_add)
    apply simp
    done
qed

lemma bv_int_bv [simp]: "bv_to_int (int_to_bv i) = i"
  by (cases "0 \<le> i") simp_all

lemma bv_msb_norm [simp]: "bv_msb (norm_signed w) = bv_msb w"
  by (rule bit_list_cases [of w]) (simp_all add: norm_signed_Cons)

lemma norm_signed_length: "length (norm_signed w) \<le> length w"
  apply (cases w, simp_all)
  apply (subst norm_signed_Cons)
  apply (case_tac a, simp_all)
  apply (rule rem_initial_length)
  done

lemma norm_signed_equal: "length (norm_signed w) = length w ==> norm_signed w = w"
proof (rule bit_list_cases [of w], simp_all)
  fix xs
  assume "length (norm_signed (\<zero>#xs)) = Suc (length xs)"
  thus "norm_signed (\<zero>#xs) = \<zero>#xs"
    by (simp add: norm_signed_Cons norm_unsigned_equal [THEN eqTrueI]
             split: if_split_asm)
next
  fix xs
  assume "length (norm_signed (\<one>#xs)) = Suc (length xs)"
  thus "norm_signed (\<one>#xs) = \<one>#xs"
    apply (simp add: norm_signed_Cons)
    apply (rule rem_initial_equal)
    apply assumption
    done
qed

lemma bv_extend_norm_signed: "bv_msb w = b ==> bv_extend (length w) b (norm_signed w) = w"
proof (rule bit_list_cases [of w],simp_all)
  fix xs
  show "bv_extend (Suc (length xs)) \<zero> (norm_signed (\<zero>#xs)) = \<zero>#xs"
  proof (simp add: norm_signed_def,auto)
    assume "norm_unsigned xs = []"
    hence xx: "rem_initial \<zero> xs = []"
      by (simp add: norm_unsigned_def)
    have "bv_extend (Suc (length xs)) \<zero> (\<zero>#rem_initial \<zero> xs) = \<zero>#xs"
      apply (simp add: bv_extend_def replicate_app_Cons_same)
      apply (fold bv_extend_def)
      apply (rule bv_extend_rem_initial)
      done
    thus "bv_extend (Suc (length xs)) \<zero> [\<zero>] = \<zero>#xs"
      by (simp add: xx)
  next
    show "bv_extend (Suc (length xs)) \<zero> (\<zero>#norm_unsigned xs) = \<zero>#xs"
      apply (simp add: norm_unsigned_def)
      apply (simp add: bv_extend_def replicate_app_Cons_same)
      apply (fold bv_extend_def)
      apply (rule bv_extend_rem_initial)
      done
  qed
next
  fix xs
  show "bv_extend (Suc (length xs)) \<one> (norm_signed (\<one>#xs)) = \<one>#xs"
    apply (simp add: norm_signed_Cons)
    apply (simp add: bv_extend_def replicate_app_Cons_same)
    apply (fold bv_extend_def)
    apply (rule bv_extend_rem_initial)
    done
qed

lemma bv_to_int_qinj:
  assumes one: "bv_to_int xs = bv_to_int ys"
  and     len: "length xs = length ys"
  shows        "xs = ys"
proof -
  from one
  have "int_to_bv (bv_to_int xs) = int_to_bv (bv_to_int ys)" by simp
  hence xsys: "norm_signed xs = norm_signed ys" by simp
  hence xsys': "bv_msb xs = bv_msb ys"
  proof -
    have "bv_msb xs = bv_msb (norm_signed xs)" by simp
    also have "... = bv_msb (norm_signed ys)" by (simp add: xsys)
    also have "... = bv_msb ys" by simp
    finally show ?thesis .
  qed
  have "xs = bv_extend (length xs) (bv_msb xs) (norm_signed xs)"
    by (simp add: bv_extend_norm_signed)
  also have "... = bv_extend (length ys) (bv_msb ys) (norm_signed ys)"
    by (simp add: xsys xsys' len)
  also have "... = ys"
    by (simp add: bv_extend_norm_signed)
  finally show ?thesis .
qed

lemma int_to_bv_returntype [simp]: "norm_signed (int_to_bv w) = int_to_bv w"
  by (simp add: int_to_bv_def)

lemma bv_to_int_msb0: "0 \<le> bv_to_int w1 ==> bv_msb w1 = \<zero>"
  by (rule bit_list_cases,simp_all)

lemma bv_to_int_msb1: "bv_to_int w1 < 0 ==> bv_msb w1 = \<one>"
  by (rule bit_list_cases,simp_all)

lemma bv_to_int_lower_limit_gt0:
  assumes w0: "0 < bv_to_int w"
  shows       "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int w"
proof -
  from w0
  have "0 \<le> bv_to_int w" by simp
  hence [simp]: "bv_msb w = \<zero>" by (rule bv_to_int_msb0)
  have "2 ^ (length (norm_signed w) - 2) \<le> bv_to_int (norm_signed w)"
  proof (rule bit_list_cases [of w])
    assume "w = []"
    with w0 show ?thesis by simp
  next
    fix w'
    assume weq: "w = \<zero> # w'"
    thus ?thesis
    proof (simp add: norm_signed_Cons,safe)
      assume "norm_unsigned w' = []"
      with weq and w0 show False
        by (simp add: norm_empty_bv_to_nat_zero)
    next
      assume w'0: "norm_unsigned w' \<noteq> []"
      have "0 < bv_to_nat w'"
      proof (rule ccontr)
        assume "~ (0 < bv_to_nat w')"
        hence "bv_to_nat w' = 0"
          by arith
        hence "norm_unsigned w' = []"
          by (simp add: bv_to_nat_zero_imp_empty)
        with w'0
        show False by simp
      qed
      with bv_to_nat_lower_limit [of w']
      show "2 ^ (length (norm_unsigned w') - Suc 0) \<le> bv_to_nat w'"
        using One_nat_def int_nat_two_exp by presburger
    qed
  next
    fix w'
    assume weq: "w = \<one> # w'"
    from w0 have "bv_msb w = \<zero>" by simp
    with weq show ?thesis by simp
  qed
  also have "...  = bv_to_int w" by simp
  finally show ?thesis .
qed

lemma norm_signed_result: "norm_signed w = [] \<or> norm_signed w = [\<one>] \<or> bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
  apply (rule bit_list_cases [of w],simp_all)
  apply (case_tac "bs",simp_all)
  apply (case_tac "a",simp_all)
  apply (simp add: norm_signed_Cons)
  apply safe
  apply simp
proof -
  fix l
  assume msb: "\<zero> = bv_msb (norm_unsigned l)"
  assume "norm_unsigned l \<noteq> []"
  with norm_unsigned_result [of l]
  have "bv_msb (norm_unsigned l) = \<one>" by simp
  with msb show False by simp
next
  fix xs
  assume p: "\<one> = bv_msb (tl (norm_signed (\<one> # xs)))"
  have "\<one> \<noteq> bv_msb (tl (norm_signed (\<one> # xs)))"
    by (rule bit_list_induct [of _ xs],simp_all)
  with p show False by simp
qed

lemma bv_to_int_upper_limit_lem1:
  assumes w0: "bv_to_int w < -1"
  shows       "bv_to_int w < - (2 ^ (length (norm_signed w) - 2))"
proof -
  from w0
  have "bv_to_int w < 0" by simp
  hence msbw [simp]: "bv_msb w = \<one>"
    by (rule bv_to_int_msb1)
  have "bv_to_int w = bv_to_int (norm_signed w)" by simp
  also from norm_signed_result [of w]
  have "... < - (2 ^ (length (norm_signed w) - 2))"
  proof safe
    assume "norm_signed w = []"
    hence "bv_to_int (norm_signed w) = 0" by simp
    with w0 show ?thesis by simp
  next
    assume "norm_signed w = [\<one>]"
    hence "bv_to_int (norm_signed w) = -1" by simp
    with w0 show ?thesis by simp
  next
    assume "bv_msb (norm_signed w) \<noteq> bv_msb (tl (norm_signed w))"
    hence msb_tl: "\<one> \<noteq> bv_msb (tl (norm_signed w))" by simp
    show "bv_to_int (norm_signed w) < - (2 ^ (length (norm_signed w) - 2))"
    proof (rule bit_list_cases [of "norm_signed w"])
      assume "norm_signed w = []"
      hence "bv_to_int (norm_signed w) = 0" by simp
      with w0 show ?thesis by simp
    next
      fix w'
      assume nw: "norm_signed w = \<zero> # w'"
      from msbw have "bv_msb (norm_signed w) = \<one>" by simp
      with nw show ?thesis by simp
    next
      fix w'
      assume weq: "norm_signed w = \<one> # w'"
      show ?thesis
      proof (rule bit_list_cases [of w'])
        assume w'eq: "w' = []"
        from w0 have "bv_to_int (norm_signed w) < -1" by simp
        with w'eq and weq show ?thesis by simp
      next
        fix w''
        assume w'eq: "w' = \<zero> # w''"
        show ?thesis
          by (simp add: weq w'eq)
      next
        fix w''
        assume w'eq: "w' = \<one> # w''"
        with weq and msb_tl show ?thesis by simp
      qed
    qed
  qed
  finally show ?thesis .
qed

lemma length_int_to_bv_upper_limit_gt0:
  assumes w0: "0 < i"
  and     wk: "i \<le> 2 ^ (k - 1) - 1"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w0 wk
  have k1: "1 < k"
    by (cases "k - 1",simp_all)
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)" by simp
  hence "k \<le> length (int_to_bv i) - 1" by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2" by arith
  hence "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)" by simp
  also have "... \<le> i"
  proof -
    have "2 ^ (length (norm_signed (int_to_bv i)) - 2) \<le> bv_to_int (int_to_bv i)"
    proof (rule bv_to_int_lower_limit_gt0)
      from w0 show "0 < bv_to_int (int_to_bv i)" by simp
    qed
    thus ?thesis by simp
  qed
  finally have "2 ^ (k - 1) \<le> i" .
  with wk show False by simp
qed

lemma pos_length_pos:
  assumes i0: "0 < bv_to_int w"
  shows       "0 < length w"
proof -
  from norm_signed_result [of w]
  have "0 < length (norm_signed w)"
  proof (auto)
    assume ii: "norm_signed w = []"
    have "bv_to_int (norm_signed w) = 0" by (subst ii) simp
    hence "bv_to_int w = 0" by simp
    with i0 show False by simp
  next
    assume ii: "norm_signed w = []"
    assume jj: "bv_msb w \<noteq> \<zero>"
    have "\<zero> = bv_msb (norm_signed w)"
      by (subst ii) simp
    also have "... \<noteq> \<zero>"
      by (simp add: jj)
    finally show False by simp
  qed
  also have "... \<le> length w"
    by (rule norm_signed_length)
  finally show ?thesis .
qed

lemma neg_length_pos:
  assumes i0: "bv_to_int w < -1"
  shows       "0 < length w"
proof -
  from norm_signed_result [of w]
  have "0 < length (norm_signed w)"
  proof (auto)
    assume ii: "norm_signed w = []"
    have "bv_to_int (norm_signed w) = 0"
      by (subst ii) simp
    hence "bv_to_int w = 0" by simp
    with i0 show False by simp
  next
    assume ii: "norm_signed w = []"
    assume jj: "bv_msb w \<noteq> \<zero>"
    have "\<zero> = bv_msb (norm_signed w)" by (subst ii) simp
    also have "... \<noteq> \<zero>" by (simp add: jj)
    finally show False by simp
  qed
  also have "... \<le> length w"
    by (rule norm_signed_length)
  finally show ?thesis .
qed

lemma length_int_to_bv_lower_limit_gt0:
  assumes wk: "2 ^ (k - 1) \<le> i"
  shows       "k < length (int_to_bv i)"
proof (rule ccontr)
  have "0 < (2::int) ^ (k - 1)"
    by (rule zero_less_power) simp
  also have "... \<le> i" by (rule wk)
  finally have i0: "0 < i" .
  have lii0: "0 < length (int_to_bv i)"
    apply (rule pos_length_pos)
    apply (simp,rule i0)
    done
  assume "~ k < length (int_to_bv i)"
  hence "length (int_to_bv i) \<le> k" by simp
  with lii0
  have a: "length (int_to_bv i) - 1 \<le> k - 1"
    by arith
  have "i < 2 ^ (length (int_to_bv i) - 1)"
  proof -
    have "i = bv_to_int (int_to_bv i)"
      by simp
    also have "... < 2 ^ (length (int_to_bv i) - 1)"
      by (rule bv_to_int_upper_range)
    finally show ?thesis .
  qed
  also have "(2::int) ^ (length (int_to_bv i) - 1) \<le> 2 ^ (k - 1)" using a
    by simp
  finally have "i < 2 ^ (k - 1)" .
  with wk show False by simp
qed

lemma length_int_to_bv_upper_limit_lem1:
  assumes w1: "i < -1"
  and     wk: "- (2 ^ (k - 1)) \<le> i"
  shows       "length (int_to_bv i) \<le> k"
proof (rule ccontr)
  from w1 wk
  have k1: "1 < k" by (cases "k - 1") simp_all
  assume "~ length (int_to_bv i) \<le> k"
  hence "k < length (int_to_bv i)" by simp
  hence "k \<le> length (int_to_bv i) - 1" by arith
  hence a: "k - 1 \<le> length (int_to_bv i) - 2" by arith
  have "i < - (2 ^ (length (int_to_bv i) - 2))"
  proof -
    have "i = bv_to_int (int_to_bv i)"
      by simp
    also have "... < - (2 ^ (length (norm_signed (int_to_bv i)) - 2))"
      by (rule bv_to_int_upper_limit_lem1,simp,rule w1)
    finally show ?thesis by simp
  qed
  also have "... \<le> -(2 ^ (k - 1))"
  proof -
    have "(2::int) ^ (k - 1) \<le> 2 ^ (length (int_to_bv i) - 2)" using a by simp
    thus ?thesis by simp
  qed
  finally have "i < -(2 ^ (k - 1))" .
  with wk show False by simp
qed

lemma length_int_to_bv_lower_limit_lem1:
  assumes wk: "i < -(2 ^ (k - 1))"
  shows       "k < length (int_to_bv i)"
proof (rule ccontr)
  from wk have "i \<le> -(2 ^ (k - 1)) - 1" by simp
  also have "... < -1"
  proof -
    have "0 < (2::int) ^ (k - 1)"
      by (rule zero_less_power) simp
    hence "-((2::int) ^ (k - 1)) < 0" by simp
    thus ?thesis by simp
  qed
  finally have i1: "i < -1" .
  have lii0: "0 < length (int_to_bv i)"
    apply (rule neg_length_pos)
    apply (simp, rule i1)
    done
  assume "~ k < length (int_to_bv i)"
  hence "length (int_to_bv i) \<le> k"
    by simp
  with lii0 have a: "length (int_to_bv i) - 1 \<le> k - 1" by arith
  hence "(2::int) ^ (length (int_to_bv i) - 1) \<le> 2 ^ (k - 1)" by simp
  hence "-((2::int) ^ (k - 1)) \<le> - (2 ^ (length (int_to_bv i) - 1))" by simp
  also have "... \<le> i"
  proof -
    have "- (2 ^ (length (int_to_bv i) - 1)) \<le> bv_to_int (int_to_bv i)"
      by (rule bv_to_int_lower_range)
    also have "... = i"
      by simp
    finally show ?thesis .
  qed
  finally have "-(2 ^ (k - 1)) \<le> i" .
  with wk show False by simp
qed


subsection \<open>Signed Arithmetic Operations\<close>

subsubsection \<open>Conversion from unsigned to signed\<close>

definition
  utos :: "bit list => bit list" where
  "utos w = norm_signed (\<zero> # w)"

lemma utos_type [simp]: "utos (norm_unsigned w) = utos w"
  by (simp add: utos_def norm_signed_Cons)

lemma utos_returntype [simp]: "norm_signed (utos w) = utos w"
  by (simp add: utos_def)

lemma utos_length: "length (utos w) \<le> Suc (length w)"
  by (simp add: utos_def norm_signed_Cons)

lemma bv_to_int_utos: "bv_to_int (utos w) = int (bv_to_nat w)"
proof (simp add: utos_def norm_signed_Cons, safe)
  assume "norm_unsigned w = []"
  hence "bv_to_nat (norm_unsigned w) = 0" by simp
  thus "bv_to_nat w = 0" by simp
qed


subsubsection \<open>Unary minus\<close>

definition
  bv_uminus :: "bit list => bit list" where
  "bv_uminus w = int_to_bv (- bv_to_int w)"

lemma bv_uminus_type [simp]: "bv_uminus (norm_signed w) = bv_uminus w"
  by (simp add: bv_uminus_def)

lemma bv_uminus_returntype [simp]: "norm_signed (bv_uminus w) = bv_uminus w"
  by (simp add: bv_uminus_def)

lemma bv_uminus_length: "length (bv_uminus w) \<le> Suc (length w)"
proof -
  have "1 < -bv_to_int w \<or> -bv_to_int w = 1 \<or> -bv_to_int w = 0 \<or> -bv_to_int w = -1 \<or> -bv_to_int w < -1"
    by arith
  thus ?thesis
  proof safe
    assume p: "1 < - bv_to_int w"
    have lw: "0 < length w"
      apply (rule neg_length_pos)
      using p
      apply simp
      done
    show ?thesis
    proof (simp add: bv_uminus_def,rule length_int_to_bv_upper_limit_gt0,simp_all)
      from p show "bv_to_int w < 0" by simp
    next
      have "-(2^(length w - 1)) \<le> bv_to_int w"
        by (rule bv_to_int_lower_range)
      hence "- bv_to_int w \<le> 2^(length w - 1)" by simp
      also from lw have "... < 2 ^ length w" by simp
      finally show "- bv_to_int w < 2 ^ length w" by simp
    qed
  next
    assume p: "- bv_to_int w = 1"
    hence lw: "0 < length w" by (cases w) simp_all
    from p
    show ?thesis
      apply (simp add: bv_uminus_def)
      using lw
      apply (simp (no_asm) add: nat_to_bv_non0)
      done
  next
    assume "- bv_to_int w = 0"
    thus ?thesis by (simp add: bv_uminus_def)
  next
    assume p: "- bv_to_int w = -1"
    thus ?thesis by (simp add: bv_uminus_def)
  next
    assume p: "- bv_to_int w < -1"
    show ?thesis
      apply (simp add: bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
      apply simp
    proof -
      have "bv_to_int w < 2 ^ (length w - 1)"
        by (rule bv_to_int_upper_range)
      also have "... \<le> 2 ^ length w" by simp
      finally show "bv_to_int w \<le> 2 ^ length w" by simp
    qed
  qed
qed

lemma bv_uminus_length_utos: "length (bv_uminus (utos w)) \<le> Suc (length w)"
proof -
  have "-bv_to_int (utos w) = 0 \<or> -bv_to_int (utos w) = -1 \<or> -bv_to_int (utos w) < -1"
    by (simp add: bv_to_int_utos, arith)
  thus ?thesis
  proof safe
    assume "-bv_to_int (utos w) = 0"
    thus ?thesis by (simp add: bv_uminus_def)
  next
    assume "-bv_to_int (utos w) = -1"
    thus ?thesis by (simp add: bv_uminus_def)
  next
    assume p: "-bv_to_int (utos w) < -1"
    show ?thesis
      apply (simp add: bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
      apply (simp add: bv_to_int_utos)
      using bv_to_nat_upper_range [of w] int_nat_two_exp apply presburger
      done
  qed
qed

definition
  bv_sadd :: "[bit list, bit list ] => bit list" where
  "bv_sadd w1 w2 = int_to_bv (bv_to_int w1 + bv_to_int w2)"

lemma bv_sadd_type1 [simp]: "bv_sadd (norm_signed w1) w2 = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma bv_sadd_type2 [simp]: "bv_sadd w1 (norm_signed w2) = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma bv_sadd_returntype [simp]: "norm_signed (bv_sadd w1 w2) = bv_sadd w1 w2"
  by (simp add: bv_sadd_def)

lemma adder_helper:
  assumes lw: "0 < max (length w1) (length w2)"
  shows   "((2::int) ^ (length w1 - 1)) + (2 ^ (length w2 - 1)) \<le> 2 ^ max (length w1) (length w2)"
proof -
  have "((2::int) ^ (length w1 - 1)) + (2 ^ (length w2 - 1)) \<le>
      2 ^ (max (length w1) (length w2) - 1) + 2 ^ (max (length w1) (length w2) - 1)"
    by (auto simp:max_def)
  also have "... = 2 ^ max (length w1) (length w2)"
  proof -
    from lw
    show ?thesis
      apply simp
      apply (subst power_Suc [symmetric])
      apply simp
      done
  qed
  finally show ?thesis .
qed

lemma bv_sadd_length: "length (bv_sadd w1 w2) \<le> Suc (max (length w1) (length w2))"
proof -
  let ?Q = "bv_to_int w1 + bv_to_int w2"

  have helper: "?Q \<noteq> 0 ==> 0 < max (length w1) (length w2)"
  proof -
    assume p: "?Q \<noteq> 0"
    show "0 < max (length w1) (length w2)"
    proof (simp add: less_max_iff_disj,rule)
      assume [simp]: "w1 = []"
      show "w2 \<noteq> []"
      proof (rule ccontr,simp)
        assume [simp]: "w2 = []"
        from p show False by simp
      qed
    qed
  qed

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1" by arith
  thus ?thesis
  proof safe
    assume "?Q = 0"
    thus ?thesis
      by (simp add: bv_sadd_def)
  next
    assume "?Q = -1"
    thus ?thesis
      by (simp add: bv_sadd_def)
  next
    assume p: "0 < ?Q"
    show ?thesis
      apply (simp add: bv_sadd_def)
      apply (rule length_int_to_bv_upper_limit_gt0)
      apply (rule p)
    proof simp
      from bv_to_int_upper_range [of w2]
      have "bv_to_int w2 \<le> 2 ^ (length w2 - 1)"
        by simp
      with bv_to_int_upper_range [of w1]
      have "bv_to_int w1 + bv_to_int w2 < (2 ^ (length w1 - 1)) + (2 ^ (length w2 - 1))"
        by (rule add_less_le_mono)
      also have "... \<le> 2 ^ max (length w1) (length w2)"
        apply (rule adder_helper)
        apply (rule helper)
        using p
        apply simp
        done
      finally show "?Q < 2 ^ max (length w1) (length w2)" .
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (simp add: bv_sadd_def)
      apply (rule length_int_to_bv_upper_limit_lem1,simp_all)
      apply (rule p)
    proof -
      have "(2 ^ (length w1 - 1)) + 2 ^ (length w2 - 1) \<le> (2::int) ^ max (length w1) (length w2)"
        apply (rule adder_helper)
        apply (rule helper)
        using p
        apply simp
        done
      hence "-((2::int) ^ max (length w1) (length w2)) \<le> - (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1))"
        by simp
      also have "- (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1)) \<le> ?Q"
        apply (rule add_mono)
        apply (rule bv_to_int_lower_range [of w1])
        apply (rule bv_to_int_lower_range [of w2])
        done
      finally show "- (2^max (length w1) (length w2)) \<le> ?Q" .
    qed
  qed
qed

definition
  bv_sub :: "[bit list, bit list] => bit list" where
  "bv_sub w1 w2 = bv_sadd w1 (bv_uminus w2)"

lemma bv_sub_type1 [simp]: "bv_sub (norm_signed w1) w2 = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma bv_sub_type2 [simp]: "bv_sub w1 (norm_signed w2) = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma bv_sub_returntype [simp]: "norm_signed (bv_sub w1 w2) = bv_sub w1 w2"
  by (simp add: bv_sub_def)

lemma bv_sub_length: "length (bv_sub w1 w2) \<le> Suc (max (length w1) (length w2))"
proof (cases "bv_to_int w2 = 0")
  assume p: "bv_to_int w2 = 0"
  show ?thesis
  proof (simp add: bv_sub_def bv_sadd_def bv_uminus_def p)
    have "length (norm_signed w1) \<le> length w1"
      by (rule norm_signed_length)
    also have "... \<le> max (length w1) (length w2)"
      by (rule max.cobounded1)
    also have "... \<le> Suc (max (length w1) (length w2))"
      by arith
    finally show "length (norm_signed w1) \<le> Suc (max (length w1) (length w2))" .
  qed
next
  assume "bv_to_int w2 \<noteq> 0"
  hence "0 < length w2" by (cases w2,simp_all)
  hence lmw: "0 < max (length w1) (length w2)" by arith

  let ?Q = "bv_to_int w1 - bv_to_int w2"

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1" by arith
  thus ?thesis
  proof safe
    assume "?Q = 0"
    thus ?thesis
      by (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
  next
    assume "?Q = -1"
    thus ?thesis
      by (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
  next
    assume p: "0 < ?Q"
    show ?thesis
      apply (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_gt0)
      apply (rule p)
    proof simp
      from bv_to_int_lower_range [of w2]
      have v2: "- bv_to_int w2 \<le> 2 ^ (length w2 - 1)" by simp
      have "bv_to_int w1 + - bv_to_int w2 < (2 ^ (length w1 - 1)) + (2 ^ (length w2 - 1))"
        apply (rule add_less_le_mono)
        apply (rule bv_to_int_upper_range [of w1])
        apply (rule v2)
        done
      also have "... \<le> 2 ^ max (length w1) (length w2)"
        apply (rule adder_helper)
        apply (rule lmw)
        done
      finally show "?Q < 2 ^ max (length w1) (length w2)" by simp
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (simp add: bv_sub_def bv_sadd_def bv_uminus_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2 ^ (length w1 - 1)) + 2 ^ (length w2 - 1) \<le> (2::int) ^ max (length w1) (length w2)"
        apply (rule adder_helper)
        apply (rule lmw)
        done
      hence "-((2::int) ^ max (length w1) (length w2)) \<le> - (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1))"
        by simp
      also have "- (2 ^ (length w1 - 1)) + -(2 ^ (length w2 - 1)) \<le> bv_to_int w1 + -bv_to_int w2"
        apply (rule add_mono)
        apply (rule bv_to_int_lower_range [of w1])
        using bv_to_int_upper_range [of w2]
        apply simp
        done
      finally show "- (2^max (length w1) (length w2)) \<le> ?Q" by simp
    qed
  qed
qed

definition
  bv_smult :: "[bit list, bit list] => bit list" where
  "bv_smult w1 w2 = int_to_bv (bv_to_int w1 * bv_to_int w2)"

lemma bv_smult_type1 [simp]: "bv_smult (norm_signed w1) w2 = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma bv_smult_type2 [simp]: "bv_smult w1 (norm_signed w2) = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma bv_smult_returntype [simp]: "norm_signed (bv_smult w1 w2) = bv_smult w1 w2"
  by (simp add: bv_smult_def)

lemma bv_smult_length: "length (bv_smult w1 w2) \<le> length w1 + length w2"
proof -
  let ?Q = "bv_to_int w1 * bv_to_int w2"

  have lmw: "?Q \<noteq> 0 ==> 0 < length w1 \<and> 0 < length w2" by auto

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1" by arith
  thus ?thesis
  proof (safe dest!: iffD1 [OF mult_eq_0_iff])
    assume "bv_to_int w1 = 0"
    thus ?thesis by (simp add: bv_smult_def)
  next
    assume "bv_to_int w2 = 0"
    thus ?thesis by (simp add: bv_smult_def)
  next
    assume p: "?Q = -1"
    show ?thesis
      apply (simp add: bv_smult_def p)
      apply (cut_tac lmw)
      apply arith
      using p
      apply simp
      done
  next
    assume p: "0 < ?Q"
    thus ?thesis
    proof (simp add: zero_less_mult_iff,safe)
      assume bi1: "0 < bv_to_int w1"
      assume bi2: "0 < bv_to_int w2"
      show ?thesis
        apply (simp add: bv_smult_def)
        apply (rule length_int_to_bv_upper_limit_gt0)
        apply (rule p)
      proof simp
        have "?Q < 2 ^ (length w1 - 1) * 2 ^ (length w2 - 1)"
          apply (rule mult_strict_mono)
          apply (rule bv_to_int_upper_range)
          apply (rule bv_to_int_upper_range)
          apply (rule zero_less_power)
          apply simp
          using bi2
          apply simp
          done
        also have "... \<le> 2 ^ (length w1 + length w2 - Suc 0)"
          apply simp
          apply (subst power_add [symmetric])
          apply simp
          done
        finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)" .
      qed
    next
      assume bi1: "bv_to_int w1 < 0"
      assume bi2: "bv_to_int w2 < 0"
      show ?thesis
        apply (simp add: bv_smult_def)
        apply (rule length_int_to_bv_upper_limit_gt0)
        apply (rule p)
      proof simp
        have "-bv_to_int w1 * -bv_to_int w2 \<le> 2 ^ (length w1 - 1) * 2 ^(length w2 - 1)"
          apply (rule mult_mono)
          using bv_to_int_lower_range [of w1]
          apply simp
          using bv_to_int_lower_range [of w2]
          apply simp
          apply (rule zero_le_power,simp)
          using bi2
          apply simp
          done
        hence "?Q \<le> 2 ^ (length w1 - 1) * 2 ^(length w2 - 1)"
          by simp
        also have "... < 2 ^ (length w1 + length w2 - Suc 0)"
          apply simp
          apply (subst power_add [symmetric])
          apply simp
          apply (cut_tac lmw)
          apply arith
          apply (cut_tac p)
          apply arith
          done
        finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)" .
      qed
    qed
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (subst bv_smult_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2::int) ^ (length w1 - 1) * 2 ^(length w2 - 1) \<le> 2 ^ (length w1 + length w2 - Suc 0)"
        apply simp
        apply (subst power_add [symmetric])
        apply simp
        done
      hence "-((2::int) ^ (length w1 + length w2 - Suc 0)) \<le> -(2^(length w1 - 1) * 2 ^ (length w2 - 1))"
        by simp
      also have "... \<le> ?Q"
      proof -
        from p
        have q: "bv_to_int w1 * bv_to_int w2 < 0"
          by simp
        thus ?thesis
        proof (simp add: mult_less_0_iff,safe)
          assume bi1: "0 < bv_to_int w1"
          assume bi2: "bv_to_int w2 < 0"
          have "-bv_to_int w2 * bv_to_int w1 \<le> ((2::int)^(length w2 - 1)) * (2 ^ (length w1 - 1))"
            apply (rule mult_mono)
            using bv_to_int_lower_range [of w2]
            apply simp
            using bv_to_int_upper_range [of w1]
            apply simp
            apply (rule zero_le_power,simp)
            using bi1
            apply simp
            done
          hence "-?Q \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
            by (simp add: ac_simps)
          thus "-(((2::int)^(length w1 - Suc 0)) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
            by simp
        next
          assume bi1: "bv_to_int w1 < 0"
          assume bi2: "0 < bv_to_int w2"
          have "-bv_to_int w1 * bv_to_int w2 \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
            apply (rule mult_mono)
            using bv_to_int_lower_range [of w1]
            apply simp
            using bv_to_int_upper_range [of w2]
            apply simp
            apply (rule zero_le_power,simp)
            using bi2
            apply simp
            done
          hence "-?Q \<le> ((2::int)^(length w1 - 1)) * (2 ^ (length w2 - 1))"
            by (simp add: ac_simps)
          thus "-(((2::int)^(length w1 - Suc 0)) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
            by simp
        qed
      qed
      finally show "-(2 ^ (length w1 + length w2 - Suc 0)) \<le> ?Q" .
    qed
  qed
qed

lemma bv_msb_one: "bv_msb w = \<one> ==> bv_to_nat w \<noteq> 0"
by (cases w) simp_all

lemma bv_smult_length_utos: "length (bv_smult (utos w1) w2) \<le> length w1 + length w2"
proof -
  let ?Q = "bv_to_int (utos w1) * bv_to_int w2"

  have lmw: "?Q \<noteq> 0 ==> 0 < length (utos w1) \<and> 0 < length w2" by auto

  have "0 < ?Q \<or> ?Q = 0 \<or> ?Q = -1 \<or> ?Q < -1" by arith
  thus ?thesis
  proof (safe dest!: iffD1 [OF mult_eq_0_iff])
    assume "bv_to_int (utos w1) = 0"
    thus ?thesis by (simp add: bv_smult_def)
  next
    assume "bv_to_int w2 = 0"
    thus ?thesis by (simp add: bv_smult_def)
  next
    assume p: "0 < ?Q"
    thus ?thesis
    proof (simp add: zero_less_mult_iff,safe)
      assume biw2: "0 < bv_to_int w2"
      show ?thesis
        apply (simp add: bv_smult_def)
        apply (rule length_int_to_bv_upper_limit_gt0)
        apply (rule p)
      proof simp
        have "?Q < 2 ^ length w1 * 2 ^ (length w2 - 1)"
          apply (rule mult_strict_mono) 
          apply (simp add: bv_to_int_utos bv_to_nat_upper_range int_nat_two_exp del: of_nat_power)
          apply (rule bv_to_int_upper_range)
          apply (rule zero_less_power,simp)
          using biw2
          apply simp
          done
        also have "... \<le> 2 ^ (length w1 + length w2 - Suc 0)"
          apply simp
          apply (subst power_add [symmetric])
          apply simp
          apply (cut_tac lmw)
          apply arith
          using p
          apply auto
          done
        finally show "?Q < 2 ^ (length w1 + length w2 - Suc 0)" .
      qed
    next
      assume "bv_to_int (utos w1) < 0"
      thus ?thesis by (simp add: bv_to_int_utos)
    qed
  next
    assume p: "?Q = -1"
    thus ?thesis
      apply (simp add: bv_smult_def)
      apply (cut_tac lmw)
      apply arith
      apply simp
      done
  next
    assume p: "?Q < -1"
    show ?thesis
      apply (subst bv_smult_def)
      apply (rule length_int_to_bv_upper_limit_lem1)
      apply (rule p)
    proof simp
      have "(2::int) ^ length w1 * 2 ^(length w2 - 1) \<le> 2 ^ (length w1 + length w2 - Suc 0)"
        apply simp
        apply (subst power_add [symmetric])
        apply simp
        apply (cut_tac lmw)
        apply arith
        apply (cut_tac p)
        apply arith
        done
      hence "-((2::int) ^ (length w1 + length w2 - Suc 0)) \<le> -(2^ length w1 * 2 ^ (length w2 - 1))"
        by simp
      also have "... \<le> ?Q"
      proof -
        from p
        have q: "bv_to_int (utos w1) * bv_to_int w2 < 0"
          by simp
        thus ?thesis
        proof (simp add: mult_less_0_iff,safe)
          assume bi1: "0 < bv_to_int (utos w1)"
          assume bi2: "bv_to_int w2 < 0"
          have "-bv_to_int w2 * bv_to_int (utos w1) \<le> ((2::int)^(length w2 - 1)) * (2 ^ length w1)"
            apply (rule mult_mono)
            using bv_to_int_lower_range [of w2]
            apply simp
            apply (simp add: bv_to_int_utos)
            using bv_to_nat_upper_range [of w1]
            apply (simp add: int_nat_two_exp del: of_nat_power)
            apply (rule zero_le_power,simp)
            using bi1
            apply simp
            done
          hence "-?Q \<le> ((2::int)^length w1) * (2 ^ (length w2 - 1))"
            by (simp add: ac_simps)
          thus "-(((2::int)^length w1) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
            by simp
        next
          assume bi1: "bv_to_int (utos w1) < 0"
          thus "-(((2::int)^length w1) * (2 ^ (length w2 - Suc 0))) \<le> ?Q"
            by (simp add: bv_to_int_utos)
        qed
      qed
      finally show "-(2 ^ (length w1 + length w2 - Suc 0)) \<le> ?Q" .
    qed
  qed
qed

lemma bv_smult_sym: "bv_smult w1 w2 = bv_smult w2 w1"
  by (simp add: bv_smult_def ac_simps)

subsection \<open>Structural operations\<close>

definition
  bv_select :: "[bit list,nat] => bit" where
  "bv_select w i = w ! (length w - 1 - i)"

definition
  bv_chop :: "[bit list,nat] => bit list * bit list" where
  "bv_chop w i = (let len = length w in (take (len - i) w,drop (len - i) w))"

definition
  bv_slice :: "[bit list,nat*nat] => bit list" where
  "bv_slice w = (\<lambda>(b,e). fst (bv_chop (snd (bv_chop w (b+1))) e))"

lemma bv_select_rev:
  assumes notnull: "n < length w"
  shows            "bv_select w n = rev w ! n"
proof -
  have "\<forall>n. n < length w --> bv_select w n = rev w ! n"
  proof (rule length_induct [of _ w],auto simp add: bv_select_def)
    fix xs :: "bit list"
    fix n
    assume ind: "\<forall>ys::bit list. length ys < length xs --> (\<forall>n. n < length ys --> ys ! (length ys - Suc n) = rev ys ! n)"
    assume notx: "n < length xs"
    show "xs ! (length xs - Suc n) = rev xs ! n"
    proof (cases xs)
      assume "xs = []"
      with notx show ?thesis by simp
    next
      fix y ys
      assume [simp]: "xs = y # ys"
      show ?thesis
      proof (auto simp add: nth_append)
        assume noty: "n < length ys"
        from spec [OF ind,of ys]
        have "\<forall>n. n < length ys --> ys ! (length ys - Suc n) = rev ys ! n"
          by simp
        hence "n < length ys --> ys ! (length ys - Suc n) = rev ys ! n" ..
        from this and noty
        show "ys ! (length ys - Suc n) = rev ys ! n" ..
      next
        assume "~ n < length ys"
        hence x: "length ys \<le> n" by simp
        from notx have "n < Suc (length ys)" by simp
        hence "n \<le> length ys" by simp
        with x have "length ys = n" by simp
        thus "y = [y] ! (n - length ys)" by simp
      qed
    qed
  qed
  then have "n < length w --> bv_select w n = rev w ! n" ..
  from this and notnull show ?thesis ..
qed

lemma bv_chop_append: "bv_chop (w1 @ w2) (length w2) = (w1,w2)"
  by (simp add: bv_chop_def Let_def)

lemma append_bv_chop_id: "fst (bv_chop w l) @ snd (bv_chop w l) = w"
  by (simp add: bv_chop_def Let_def)

lemma bv_chop_length_fst [simp]: "length (fst (bv_chop w i)) = length w - i"
  by (simp add: bv_chop_def Let_def)

lemma bv_chop_length_snd [simp]: "length (snd (bv_chop w i)) = min i (length w)"
  by (simp add: bv_chop_def Let_def)

lemma bv_slice_length [simp]: "[| j \<le> i; i < length w |] ==> length (bv_slice w (i,j)) = i - j + 1"
  by (auto simp add: bv_slice_def)

definition
  length_nat :: "nat => nat" where
  [code del]: "length_nat x = (LEAST n. x < 2 ^ n)"

lemma length_nat: "length (nat_to_bv n) = length_nat n"
  apply (simp add: length_nat_def)
  apply (rule Least_equality [symmetric])
  prefer 2
  apply (rule length_nat_to_bv_upper_limit)
  apply arith
  apply (rule ccontr)
proof -
  assume "~ n < 2 ^ length (nat_to_bv n)"
  hence "2 ^ length (nat_to_bv n) \<le> n" by simp
  hence "length (nat_to_bv n) < length (nat_to_bv n)"
    by (rule length_nat_to_bv_lower_limit)
  thus False by simp
qed

lemma length_nat_0 [simp]: "length_nat 0 = 0"
  by (simp add: length_nat_def Least_equality)

lemma length_nat_non0:
  assumes n0: "n \<noteq> 0"
  shows       "length_nat n = Suc (length_nat (n div 2))"
  apply (simp add: length_nat [symmetric])
  apply (subst nat_to_bv_non0 [of n])
  apply (simp_all add: n0)
  done

definition
  length_int :: "int => nat" where
  "length_int x =
    (if 0 < x then Suc (length_nat (nat x))
    else if x = 0 then 0
    else Suc (length_nat (nat (-x - 1))))"

lemma length_int: "length (int_to_bv i) = length_int i"
proof (cases "0 < i")
  assume i0: "0 < i"
  hence "length (int_to_bv i) =
      length (norm_signed (\<zero> # norm_unsigned (nat_to_bv (nat i))))" by simp
  also from norm_unsigned_result [of "nat_to_bv (nat i)"]
  have "... = Suc (length_nat (nat i))"
    apply safe
    apply (simp del: norm_unsigned_nat_to_bv)
    apply (drule norm_empty_bv_to_nat_zero)
    using i0 apply simp
    apply (cases "norm_unsigned (nat_to_bv (nat i))")
    apply (drule norm_empty_bv_to_nat_zero [of "nat_to_bv (nat i)"])
    using i0 apply simp
    apply (simp add: i0)
    using i0 apply (simp add: length_nat [symmetric])
    done
  finally show ?thesis
    using i0
    by (simp add: length_int_def)
next
  assume "~ 0 < i"
  hence i0: "i \<le> 0" by simp
  show ?thesis
  proof (cases "i = 0")
    assume "i = 0"
    thus ?thesis by (simp add: length_int_def)
  next
    assume "i \<noteq> 0"
    with i0 have i0: "i < 0" by simp
    hence "length (int_to_bv i) =
        length (norm_signed (\<one> # bv_not (norm_unsigned (nat_to_bv (nat (- i) - 1)))))"
      by (simp add: int_to_bv_def nat_diff_distrib)
    also from norm_unsigned_result [of "nat_to_bv (nat (- i) - 1)"]
    have "... = Suc (length_nat (nat (- i) - 1))"
      apply safe
      apply (simp del: norm_unsigned_nat_to_bv)
      apply (drule norm_empty_bv_to_nat_zero [of "nat_to_bv (nat (-i) - Suc 0)"])
      using i0 apply simp
      apply (cases "- i - 1 = 0")
      apply simp
      apply (simp add: length_nat [symmetric])
      apply (cases "norm_unsigned (nat_to_bv (nat (- i) - 1))")
      apply simp
      apply simp
      done
    finally
    show ?thesis
      using i0 by (simp add: length_int_def nat_diff_distrib del: int_to_bv_lt0)
  qed
qed

lemma length_int_0 [simp]: "length_int 0 = 0"
  by (simp add: length_int_def)

lemma length_int_gt0: "0 < i ==> length_int i = Suc (length_nat (nat i))"
  by (simp add: length_int_def)

lemma length_int_lt0: "i < 0 ==> length_int i = Suc (length_nat (nat (- i) - 1))"
  by (simp add: length_int_def nat_diff_distrib)

lemma bv_chopI: "[| w = w1 @ w2 ; i = length w2 |] ==> bv_chop w i = (w1,w2)"
  by (simp add: bv_chop_def Let_def)

lemma bv_sliceI: "[| j \<le> i ; i < length w ; w = w1 @ w2 @ w3 ; Suc i = length w2 + j ; j = length w3  |] ==> bv_slice w (i,j) = w2"
  apply (simp add: bv_slice_def)
  apply (subst bv_chopI [of "w1 @ w2 @ w3" w1 "w2 @ w3"])
  apply simp
  apply simp
  apply simp
  apply (subst bv_chopI [of "w2 @ w3" w2 w3],simp_all)
  done

lemma bv_slice_bv_slice:
  assumes ki: "k \<le> i"
  and     ij: "i \<le> j"
  and     jl: "j \<le> l"
  and     lw: "l < length w"
  shows       "bv_slice w (j,i) = bv_slice (bv_slice w (l,k)) (j-k,i-k)"
proof -
  define w1 w2 w3 w4 w5
    where w_defs:
      "w1 = fst (bv_chop w (Suc l))"
      "w2 = fst (bv_chop (snd (bv_chop w (Suc l))) (Suc j))"
      "w3 = fst (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)"
      "w4 = fst (bv_chop (snd (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)) k)"
      "w5 = snd (bv_chop (snd (bv_chop (snd (bv_chop (snd (bv_chop w (Suc l))) (Suc j))) i)) k)"

  have w_def: "w = w1 @ w2 @ w3 @ w4 @ w5"
    by (simp add: w_defs append_bv_chop_id)

  from ki ij jl lw
  show ?thesis
    apply (subst bv_sliceI [where ?j = i and ?i = j and ?w = w and ?w1.0 = "w1 @ w2" and ?w2.0 = w3 and ?w3.0 = "w4 @ w5"])
    apply simp_all
    apply (rule w_def)
    apply (simp add: w_defs)
    apply (simp add: w_defs)
    apply (subst bv_sliceI [where ?j = k and ?i = l and ?w = w and ?w1.0 = w1 and ?w2.0 = "w2 @ w3 @ w4" and ?w3.0 = w5])
    apply simp_all
    apply (rule w_def)
    apply (simp add: w_defs)
    apply (simp add: w_defs)
    apply (subst bv_sliceI [where ?j = "i-k" and ?i = "j-k" and ?w = "w2 @ w3 @ w4" and ?w1.0 = w2 and ?w2.0 = w3 and ?w3.0 = w4])
    apply simp_all
    apply (simp_all add: w_defs)
    done
qed

lemma bv_to_nat_extend [simp]: "bv_to_nat (bv_extend n \<zero> w) = bv_to_nat w"
  apply (simp add: bv_extend_def)
  apply (subst bv_to_nat_dist_append)
  apply simp
  apply (induct ("n - length w"))
   apply simp_all
  done

lemma bv_msb_extend_same [simp]: "bv_msb w = b ==> bv_msb (bv_extend n b w) = b"
  apply (simp add: bv_extend_def)
  apply (cases "n - length w")
   apply simp_all
  done

lemma bv_to_int_extend [simp]:
  assumes a: "bv_msb w = b"
  shows      "bv_to_int (bv_extend n b w) = bv_to_int w"
proof (cases "bv_msb w")
  assume [simp]: "bv_msb w = \<zero>"
  with a have [simp]: "b = \<zero>" by simp
  show ?thesis by (simp add: bv_to_int_def)
next
  assume [simp]: "bv_msb w = \<one>"
  with a have [simp]: "b = \<one>" by simp
  show ?thesis
    apply (simp add: bv_to_int_def)
    apply (simp add: bv_extend_def)
    apply (induct ("n - length w"), simp_all)
    done
qed

lemma length_nat_mono [simp]: "x \<le> y ==> length_nat x \<le> length_nat y"
proof (rule ccontr)
  assume xy: "x \<le> y"
  assume "~ length_nat x \<le> length_nat y"
  hence lxly: "length_nat y < length_nat x"
    by simp
  hence "length_nat y < (LEAST n. x < 2 ^ n)"
    by (simp add: length_nat_def)
  hence "~ x < 2 ^ length_nat y"
    by (rule not_less_Least)
  hence xx: "2 ^ length_nat y \<le> x"
    by simp
  have yy: "y < 2 ^ length_nat y"
    apply (simp add: length_nat_def)
    apply (rule LeastI)
    apply (subgoal_tac "y < 2 ^ y",assumption)
    apply (cases "0 \<le> y")
    apply (induct y,simp_all)
    done
  with xx have "y < x" by simp
  with xy show False by simp
qed

lemma length_nat_mono_int: "x \<le> y ==> length_nat x \<le> length_nat y"
  by (rule length_nat_mono) arith

lemma length_nat_pos [simp,intro!]: "0 < x ==> 0 < length_nat x"
  by (simp add: length_nat_non0)

lemma length_int_mono_gt0: "[| 0 \<le> x ; x \<le> y |] ==> length_int x \<le> length_int y"
  by (cases "x = 0") (simp_all add: length_int_gt0 nat_le_eq_zle)

lemma length_int_mono_lt0: "[| x \<le> y ; y \<le> 0 |] ==> length_int y \<le> length_int x"
  by (cases "y = 0") (simp_all add: length_int_lt0)

lemmas [simp] = length_nat_non0

primrec fast_bv_to_nat_helper :: "[bit list, num] => num" where
    fast_bv_to_nat_Nil: "fast_bv_to_nat_helper [] k = k"
  | fast_bv_to_nat_Cons: "fast_bv_to_nat_helper (b#bs) k =
      fast_bv_to_nat_helper bs ((case_bit Num.Bit0 Num.Bit1 b) k)"

declare fast_bv_to_nat_helper.simps [code del]

lemma fast_bv_to_nat_Cons0: "fast_bv_to_nat_helper (\<zero>#bs) bin =
    fast_bv_to_nat_helper bs (Num.Bit0 bin)"
  by simp

lemma fast_bv_to_nat_Cons1: "fast_bv_to_nat_helper (\<one>#bs) bin =
    fast_bv_to_nat_helper bs (Num.Bit1 bin)"
  by simp

lemma mult_Bit0_left: "Num.Bit0 m * n = Num.Bit0 (m * n)"
  by (simp add: num_eq_iff nat_of_num_mult distrib_right)

lemma fast_bv_to_nat_def:
  "bv_to_nat (\<one> # bs) == numeral (fast_bv_to_nat_helper bs Num.One)"
proof -
  have "\<And>k. foldl (\<lambda>bn b. 2 * bn + bitval b) (numeral k) bs = numeral (fast_bv_to_nat_helper bs k)"
    apply (induct bs, simp)
    apply (case_tac a, simp_all add: mult_Bit0_left)
    done
  thus "PROP ?thesis"
    by (simp add: bv_to_nat_def add: numeral_One [symmetric]
      del: numeral_One One_nat_def)
qed

declare fast_bv_to_nat_Cons [simp del]
declare fast_bv_to_nat_Cons0 [simp]
declare fast_bv_to_nat_Cons1 [simp]

simproc_setup bv_to_nat ("bv_to_nat (x # xs)") = \<open>
  fn _ => fn ctxt => fn ct =>
    let
      fun is_const_bool (Const(@{const_name True},_)) = true
        | is_const_bool (Const(@{const_name False},_)) = true
        | is_const_bool _ = false
      fun is_const_bit (Const(@{const_name Zero},_)) = true
        | is_const_bit (Const(@{const_name One},_)) = true
        | is_const_bit _ = false
      fun vec_is_usable (Const(@{const_name Nil},_)) = true
        | vec_is_usable (Const(@{const_name Cons},_) $ b $ bs) =
            vec_is_usable bs andalso is_const_bit b
        | vec_is_usable _ = false
      fun proc (Const(@{const_name bv_to_nat},_) $
        (Const(@{const_name Cons},_) $ Const(@{const_name One},_) $ t)) =
            if vec_is_usable t then
              SOME
                (infer_instantiate ctxt
                  [(("bs", 0), Thm.cterm_of ctxt t)] @{thm fast_bv_to_nat_def})
            else NONE
        | proc _ = NONE
    in proc (Thm.term_of ct) end
\<close>

declare bv_to_nat1 [simp del]
declare bv_to_nat_helper [simp del]

definition
  bv_mapzip :: "[bit => bit => bit,bit list, bit list] => bit list" where
  "bv_mapzip f w1 w2 =
    (let g = bv_extend (max (length w1) (length w2)) \<zero>
     in map (case_prod f) (zip (g w1) (g w2)))"

lemma bv_length_bv_mapzip [simp]:
    "length (bv_mapzip f w1 w2) = max (length w1) (length w2)"
  by (simp add: bv_mapzip_def Let_def split: split_max)

lemma bv_mapzip_Nil [simp]: "bv_mapzip f [] [] = []"
  by (simp add: bv_mapzip_def Let_def)

lemma bv_mapzip_Cons [simp]: "length w1 = length w2 ==>
    bv_mapzip f (x#w1) (y#w2) = f x y # bv_mapzip f w1 w2"
  by (simp add: bv_mapzip_def Let_def)

end
