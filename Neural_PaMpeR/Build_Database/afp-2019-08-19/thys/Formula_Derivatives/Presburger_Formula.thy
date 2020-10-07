section \<open>Concrete Atomic Presburger Formulas\<close>

(*<*)
theory Presburger_Formula
imports
  Abstract_Formula
  "HOL-Library.Code_Target_Int"
  "List-Index.List_Index"
begin
(*>*)

declare [[coercion "of_bool :: bool \<Rightarrow> nat"]]
declare [[coercion int]]
declare [[coercion_map map]]
declare [[coercion_enabled]]

fun len :: "nat \<Rightarrow> nat" where \<comment> \<open>FIXME yet another logarithm\<close>
  "len 0 = 0"
| "len (Suc 0) = 1"
| "len n = Suc (len (n div 2))"

lemma len_eq0_iff: "len n = 0 \<longleftrightarrow> n = 0"
  by (induct n rule: len.induct) auto

lemma len_mult2[simp]: "len (2 * x) = (if x = 0 then 0 else Suc (len x))"
proof (induct x rule: len.induct)
  show "len (2 * Suc 0) = (if Suc 0 = 0 then 0 else Suc (len (Suc 0)))" by (simp add: numeral_eq_Suc)
qed auto

lemma len_mult2'[simp]: "len (x * 2) = (if x = 0 then 0 else Suc (len x))"
  using len_mult2 [of x] by (simp add: ac_simps)

lemma len_Suc_mult2[simp]: "len (Suc (2 * x)) = Suc (len x)"
proof (induct x rule: len.induct)
  show "len (Suc (2 * Suc 0)) = Suc (len (Suc 0))"
    by (metis div_less One_nat_def div2_Suc_Suc len.simps(3) lessI mult.right_neutral numeral_2_eq_2)
qed auto

lemma len_le_iff: "len x \<le> l \<longleftrightarrow> x < 2 ^ l"
proof (induct x arbitrary: l rule: len.induct)
  fix l show "(len (Suc 0) \<le> l) = (Suc 0 < 2 ^ l)"
  proof (cases l)
    case Suc then show ?thesis using le_less by fastforce
  qed simp
next
  fix v l assume "\<And>l. (len (Suc (Suc v) div 2) \<le> l) = (Suc (Suc v) div 2 < 2 ^ l)"
  then show "(len (Suc (Suc v)) \<le> l) = (Suc (Suc v) < 2 ^ l)"
    by (cases l) (simp_all, linarith)
qed simp

lemma len_pow2[simp]: "len (2 ^ x) = Suc x"
  by (induct x) auto

lemma len_div2[simp]: "len (x div 2) = len x - 1"
  by (induct x rule: len.induct) auto

lemma less_pow2_len[simp]: "x < 2 ^ len x"
  by (induct x rule: len.induct) auto

lemma len_alt: "len x = (LEAST i. x < 2 ^ i)"
proof (rule antisym)
  show "len x \<le> (LEAST i. x < 2 ^ i)"
    unfolding len_le_iff by (rule LeastI) (rule less_pow2_len)
qed (auto intro: Least_le)

lemma len_mono[simp]: "x \<le> y \<Longrightarrow> len x \<le> len y"
  unfolding len_le_iff using less_pow2_len[of y] by linarith

lemma len_div_pow2[simp]: "len (x div 2 ^ m) = len x - m"
  by (induct m arbitrary: x) (auto simp: div_mult2_eq)

lemma len_mult_pow2[simp]: "len (x * 2 ^ m) = (if x = 0 then 0 else len x + m)"
  by (induct m arbitrary: x) (auto simp: div_mult2_eq mult.assoc[symmetric] mult.commute[of _ 2])

lemma map_index'_Suc[simp]: "map_index' (Suc i) f xs = map_index' i (\<lambda>i. f (Suc i)) xs"
  by (induct xs arbitrary: i) auto


abbreviation (input) "zero n \<equiv> replicate n False"
abbreviation (input) "SUC \<equiv> \<lambda>_::unit. Suc"
definition "test_bit m n \<equiv> (m :: nat) div 2 ^ n mod 2 = 1"
definition "downshift m \<equiv> (m :: nat) div 2"
definition "upshift m \<equiv> (m :: nat) * 2"
definition "set_bit n m \<equiv> m + (if \<not> test_bit m n then 2 ^ n else (0 :: nat))"
definition "cut_bits n m \<equiv> (m :: nat) mod 2 ^ n"

typedef interp = "{(n :: nat, xs :: nat list). \<forall>x \<in> set xs. len x \<le> n}"
  by (force intro: exI[of _ "[]"])

setup_lifting type_definition_interp
type_synonym atom = "bool list"
type_synonym "value" = "nat"
datatype presb = Eq (tm: "int list") (const: int) (offset: "int")
derive linorder list
derive linorder presb
type_synonym formula = "(presb, unit) aformula"

lift_definition assigns :: "nat \<Rightarrow> interp \<Rightarrow> unit \<Rightarrow> value" ("_\<^bsup>_\<^esup>_" [900, 999, 999] 999) is
  "\<lambda>n (_, I) _. if n < length I then I ! n else 0" .

lift_definition nvars :: "interp \<Rightarrow> nat" ("#\<^sub>V _" [1000] 900) is
  "\<lambda>(_, I). length I" .

lift_definition Length :: "interp \<Rightarrow> nat" is "\<lambda>(n, _). n" .

lift_definition Extend :: "unit \<Rightarrow> nat \<Rightarrow> interp \<Rightarrow> value \<Rightarrow> interp" is
  "\<lambda>_ i (n, I) m. (max n (len m), insert_nth i m I)"
  by (force simp: max_def dest: in_set_takeD in_set_dropD)

lift_definition CONS :: "atom \<Rightarrow> interp \<Rightarrow> interp" is
  "\<lambda>bs (n, I). (Suc n, map_index (\<lambda>i n. 2 * n + (if bs ! i then 1 else 0)) I)"
  by (auto simp: set_zip)

lift_definition SNOC :: "atom \<Rightarrow> interp \<Rightarrow> interp" is
  "\<lambda>bs (n, I). (Suc n, map_index (\<lambda>i m. m + (if bs ! i then 2 ^ n else 0)) I)"
  by (auto simp: all_set_conv_all_nth len_le_iff)

definition extend :: "unit \<Rightarrow> bool \<Rightarrow> atom \<Rightarrow> atom" where
  "extend _ b bs \<equiv> b # bs"

abbreviation (input) size_atom :: "atom \<Rightarrow> nat" where
  "size_atom \<equiv> length"

definition FV0 :: "unit \<Rightarrow> presb \<Rightarrow> nat set" where
  "FV0 _ fm = (case fm of Eq is _ _ \<Rightarrow> {n. n < length is \<and> is!n \<noteq> 0})"

lemma FV0_code[code]:
  "FV0 x (Eq is i off) = Option.these (set (map_index (\<lambda>i x. if x = 0 then None else Some i) is))"
  unfolding FV0_def by (force simp: Option.these_def image_iff)

primrec wf0 :: "nat \<Rightarrow> presb \<Rightarrow> bool" where
  "wf0 idx (Eq is _ _) = (length is = idx)"

fun find0 where
  "find0 (_::unit) n (Eq is _ _) = (is ! n \<noteq> 0)"

primrec decr0 where
  "decr0 (_::unit) k (Eq is i d) = Eq (take k is @ drop (Suc k) is) i d"

definition scalar_product :: "nat list \<Rightarrow> int list \<Rightarrow> int" where
  "scalar_product ns is =
     sum_list (map_index (\<lambda>i b. (if i < length ns then ns ! i else 0) * b) is)"

lift_definition eval_tm :: "interp \<Rightarrow> int list \<Rightarrow> int" is
  "\<lambda>(_, I). scalar_product I" .

primrec satisfies0 where
  "satisfies0 I (Eq is i d) = (eval_tm I is = i - (2 ^ Length I) * d)"

inductive lformula0 where
  "lformula0 (Eq is i 0)"

code_pred lformula0 .

fun lderiv0 :: "bool list \<Rightarrow> presb \<Rightarrow> formula" where
  "lderiv0 bs (Eq is i d) = (if d \<noteq> 0 then undefined else
  (let v = i - scalar_product bs is
   in if v mod 2 = 0 then FBase (Eq is (v div 2) 0) else FBool False))"

fun rderiv0 :: "bool list \<Rightarrow> presb \<Rightarrow> formula" where
  "rderiv0 bs (Eq is i d) =
  (let
     l = - sum_list [i. i \<leftarrow> is, i < 0];
     h = - sum_list [i. i \<leftarrow> is, i > 0];
     d' = scalar_product bs is + 2 * d
   in if d' \<in> {min h i .. max l i} then FBase (Eq is i d') else FBool False)"

primrec nullable0 where
  "nullable0 (Eq is i off) = (i = off)"

definition \<sigma> :: "nat \<Rightarrow> atom list" where
  "\<sigma> n = List.n_lists n [True, False]"

named_theorems Presb_simps

lemma nvars_Extend[Presb_simps]: "#\<^sub>V (Extend () i \<AA> P) = Suc (#\<^sub>V \<AA>)"
  by (transfer, auto)

lemma Length_Extend[Presb_simps]: "Length (Extend () i \<AA> P) = max (Length \<AA>) (len P)"
  by (transfer, auto)

lemma Length0_inj[Presb_simps]: "Length \<AA> = 0 \<Longrightarrow> Length \<BB> = 0 \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow> \<AA> = \<BB>"
  by transfer (auto intro: nth_equalityI simp: all_set_conv_all_nth len_eq0_iff)

lemma ex_Length0[Presb_simps]: "\<exists>\<AA>. Length \<AA> = 0 \<and> #\<^sub>V \<AA> = idx"
  by (transfer fixing: idx) (auto intro: exI[of _ "replicate idx 0"])

lemma Extend_commute_safe[Presb_simps]: "\<lbrakk>j \<le> i; i < Suc (#\<^sub>V \<AA>)\<rbrakk> \<Longrightarrow>
  Extend k j (Extend k i \<AA> P) Q = Extend k (Suc i) (Extend k j \<AA> Q) P"
  by transfer (auto simp add: min_def take_Cons take_drop le_imp_diff_is_add split: nat.splits)

lemma Extend_commute_unsafe[Presb_simps]:
  "k \<noteq> k' \<Longrightarrow> Extend k j (Extend k' i \<AA> P) Q = Extend k' i (Extend k j \<AA> Q) P"
  by transfer auto

lemma assigns_Extend[Presb_simps]: "i < Suc (#\<^sub>V \<AA>) \<Longrightarrow>
  m\<^bsup>Extend k i \<AA> P\<^esup>k' = (if k = k' then if m = i then P else dec i m\<^bsup>\<AA>\<^esup>k else m\<^bsup>\<AA>\<^esup>k')"
  by transfer (auto simp: nth_append dec_def min_def)

lemma assigns_SNOC_zero[Presb_simps]: "m < #\<^sub>V \<AA> \<Longrightarrow> m\<^bsup>SNOC (zero (#\<^sub>V \<AA>)) \<AA>\<^esup>k = m\<^bsup>\<AA>\<^esup>k"
  by transfer auto

lemma Length_CONS[Presb_simps]: "Length (CONS x \<AA>) = Suc (Length \<AA>)"
  by transfer auto

lemma Length_SNOC[Presb_simps]: "Length (SNOC x \<AA>) = Suc (Length \<AA>)"
  by transfer auto

lemma nvars_CONS[Presb_simps]: "#\<^sub>V (CONS x \<AA>) = #\<^sub>V \<AA>"
  by transfer auto

lemma nvars_SNOC[Presb_simps]: "#\<^sub>V (SNOC x \<AA>) = #\<^sub>V \<AA>"
  by transfer auto

lemma Extend_CONS[Presb_simps]: "#\<^sub>V \<AA> = length x \<Longrightarrow>
  Extend k 0 (CONS x \<AA>) P = CONS (extend k (test_bit P 0) x) (Extend k 0 \<AA> (downshift P))"
  by transfer (auto simp: extend_def downshift_def test_bit_def, presburger+)

lemma Extend_SNOC[Presb_simps]: "\<lbrakk>#\<^sub>V \<AA> = length x; len P \<le> Length (SNOC x \<AA>)\<rbrakk> \<Longrightarrow>
  Extend k 0 (SNOC x \<AA>) P =
    SNOC (extend k (test_bit P (Length \<AA>)) x) (Extend k 0 \<AA> (cut_bits (Length \<AA>) P))"
  apply transfer
  apply (auto simp: cut_bits_def extend_def test_bit_def nth_Cons' max_absorb1 len_le_iff
    split: if_splits cong del: if_weak_cong)
   apply (metis add.commute mod_less mod_mult2_eq mult_numeral_1_right numeral_1_eq_Suc_0 power_commuting_commutes)
  apply (metis Euclidean_Division.div_eq_0_iff div_0 less_mult_imp_div_less mod_less nat_dvd_not_less semiring_normalization_rules(7))
  done

lemma odd_neq_even:
  "Suc (2 * x) = 2 * y \<longleftrightarrow> False"
  "2 * y = Suc (2 * x) \<longleftrightarrow> False"
  by presburger+

lemma CONS_inj[Presb_simps]: "size x = #\<^sub>V \<AA> \<Longrightarrow> size y = #\<^sub>V \<AA> \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow>
  CONS x \<AA> = CONS y \<BB> \<longleftrightarrow> (x = y \<and> \<AA> = \<BB>)"
  by transfer (auto simp: list_eq_iff_nth_eq odd_neq_even split: if_splits)

lemma mod_2_Suc_iff:
  "x mod 2 = Suc 0 \<longleftrightarrow> x = Suc (2 * (x div 2))"
  by presburger+

lemma CONS_surj[Presb_simps]: "Length \<AA> \<noteq> 0 \<Longrightarrow>
  \<exists>x \<BB>. \<AA> = CONS x \<BB> \<and> #\<^sub>V \<BB> = #\<^sub>V \<AA> \<and> size x = #\<^sub>V \<AA>"
  by transfer
    (auto simp: gr0_conv_Suc list_eq_iff_nth_eq len_le_iff split: if_splits
    intro!: exI[of _ "map (\<lambda>n. n mod 2 \<noteq> 0) _"] exI[of _ "map (\<lambda>n. n div 2) _"];
    auto simp: mod_2_Suc_iff)

lemma [Presb_simps]: 
  "length (extend k b x) = Suc (length x)"
  "downshift (upshift P) = P"
  "downshift (set_bit 0 P) = downshift P"
  "test_bit (set_bit n P) n"
  "\<not> test_bit (upshift P) 0"
  "len P \<le> p \<Longrightarrow> \<not> test_bit P p"
  "len (cut_bits n P) \<le> n"
  "len P \<le> n \<Longrightarrow> cut_bits n P = P"
  "len (upshift P) = (case len P of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> Suc (Suc n))"
  "len (downshift P) = (case len P of 0 \<Rightarrow> 0 | Suc n \<Rightarrow> n)"
  by (auto simp: extend_def set_bit_def cut_bits_def upshift_def downshift_def test_bit_def
    len_le_iff len_eq0_iff div_add_self2 split: nat.split)

lemma Suc0_div_pow2_eq: "Suc 0 div 2 ^ i = (if i = 0 then 1 else 0)"
  by (induct i) (auto simp: div_mult2_eq)

lemma set_unset_bit_preserves_len:
  assumes "x div 2 ^ m = 2 * q" "m < len x"
  shows "x + 2 ^ m < 2 ^ len x"
using assms proof (induct m arbitrary: x)
  case 0 then show ?case
    by (auto simp: div_mult2_eq len_Suc_mult2[symmetric]
      simp del: len_Suc_mult2 power_Suc split: if_splits)
next
  case (Suc m)
  with Suc(1)[of "x div 2"] show ?case by (cases "len x") (auto simp: div_mult2_eq)
qed

lemma len_set_bit[Presb_simps]: "len (set_bit m P) = max (Suc m) (len P)"
proof (rule antisym)
  show "len (set_bit m P) \<le> max (Suc m) (len P)"
    by (auto simp: set_bit_def test_bit_def max_def Suc_le_eq not_less len_le_iff
      set_unset_bit_preserves_len simp del: One_nat_def)
next
  have "P < 2 ^ len (P + 2 ^ m)" by (rule order.strict_trans2[OF less_pow2_len]) auto
  moreover have "m < len (P + 2 ^ m)" by (rule order.strict_trans2[OF _ len_mono[of "2 ^ m"]]) auto
  ultimately show "max (Suc m) (len P) \<le> len (set_bit m P)"
    by (auto simp: set_bit_def test_bit_def max_def Suc_le_eq not_less len_le_iff)
qed

lemma mod_pow2_div_pow2:
  fixes p m n :: nat
  shows "m < n \<Longrightarrow> p mod 2 ^ n div 2 ^ m = p div 2 ^ m mod 2 ^ (n - m)"
  by (induct m arbitrary: p n) (auto simp: div_mult2_eq mod_mult2_eq Suc_less_eq2)

lemma irrelevant_set_bit[simp]:
  fixes p m n :: nat
  assumes "n \<le> m"
  shows "(p + 2 ^ m) mod 2 ^ n = p mod 2 ^ n"
proof -
  from assms obtain q :: nat where "2 ^ m = q * 2 ^ n"
    by (metis le_add_diff_inverse mult.commute power_add)
  then show ?thesis by simp
qed

lemma mod_lemma: "\<lbrakk> (0::nat) < c; r < b \<rbrakk> \<Longrightarrow> b * (q mod c) + r < b * c"
  by (metis add_gr_0 div_le_mono div_mult_self1_is_m less_imp_add_positive mod_less_divisor not_less split_div)

lemma relevant_set_bit[simp]:
  fixes p m n :: nat
  assumes "m < n" "p div 2 ^ m = 2 * q"
  shows "(p + 2 ^ m) mod 2 ^ n = p mod 2 ^ n + 2 ^ m"
proof -
  have "p mod 2 ^ n + 2 ^ m < 2 ^ n"
  using assms proof (induct m arbitrary: p n)
    case 0 then show ?case
      by (auto simp: gr0_conv_Suc)
         (metis One_nat_def Suc_eq_plus1 lessI mod_lemma numeral_2_eq_2 zero_less_numeral zero_less_power)
  next
    case (Suc m)
    from Suc(1)[of "n - 1" "p div 2"] Suc(2,3) show ?case
      by (auto simp: div_mult2_eq mod_mult2_eq Suc_less_eq2)
  qed
  with \<open>m < n\<close> show ?thesis by (subst mod_add_eq [symmetric]) auto
qed

lemma cut_bits_set_bit[Presb_simps]: "cut_bits n (set_bit m p) =
  (if n \<le> m then cut_bits n p else set_bit m (cut_bits n p))"
  unfolding cut_bits_def set_bit_def test_bit_def
  by (auto simp: not_le mod_pow2_div_pow2 mod_mod_cancel simp del: One_nat_def)

lemma wf0_decr0[Presb_simps]:
  "wf0 (Suc idx) a \<Longrightarrow> l < Suc idx \<Longrightarrow> \<not> find0 k l a \<Longrightarrow> wf0 idx (decr0 k l a)"
  by (induct a) auto

lemma lformula0_decr0[Presb_simps]: "lformula0 a \<Longrightarrow> lformula0 (decr0 k l a)"
  by (induct a) (auto elim: lformula0.cases intro: lformula0.intros)

abbreviation sat0_syn (infix "\<Turnstile>0" 65) where
 "sat0_syn \<equiv> satisfies0"
abbreviation sat_syn (infix "\<Turnstile>" 65) where
 "sat_syn \<equiv> Formula_Operations.satisfies Extend Length satisfies0"
abbreviation sat_bounded_syn (infix "\<Turnstile>\<^sub>b" 65) where
 "sat_bounded_syn \<equiv> Formula_Operations.satisfies_bounded Extend Length len satisfies0"

lemma scalar_product_Nil[simp]: "scalar_product [] xs = 0"
  by (induct xs) (auto simp: scalar_product_def)

lemma scalar_product_Nil2[simp]: "scalar_product xs [] = 0"
  by (induct xs) (auto simp: scalar_product_def)

lemma scalar_product_Cons[simp]:
  "scalar_product xs (y # ys) = (case xs of x # xs \<Rightarrow> x * y + scalar_product xs ys | [] \<Rightarrow> 0)"
  by (cases xs) (simp, auto simp: scalar_product_def cong del: if_weak_cong)

lemma scalar_product_append[simp]: "scalar_product ns (xs @ ys) =
  scalar_product (take (length xs) ns) xs + scalar_product (drop (length xs) ns) ys"
  by (induct xs arbitrary: ns) (auto split: list.splits)

lemma scalar_product_trim: "scalar_product ns xs = scalar_product (take (length xs) ns) xs"
  by (induct xs arbitrary: ns) (auto split: list.splits)

lemma Extend_satisfies0_decr0[Presb_simps]:
  assumes "\<not> find0 k i a" "i < Suc (#\<^sub>V \<AA>)" "lformula0 a \<or> len P \<le> Length \<AA>"
  shows "Extend k i \<AA> P \<Turnstile>0 a = \<AA> \<Turnstile>0 decr0 k i a"
proof -
   { fix "is" :: "int list"
     assume "is ! i = 0"
     with assms(1,2) have "eval_tm (Extend k i \<AA> P) is = eval_tm \<AA> (take i is @ drop (Suc i) is)"
       by (cases a, transfer)
         (force intro: trans[OF scalar_product_trim] simp: min_def
         arg_cong2[OF refl id_take_nth_drop, of i _ scalar_product "take i xs @ _" for i x xs])
  } note * = this
  from assms show ?thesis
    by (cases a) (auto dest!: * simp: Length_Extend max_def elim: lformula0.cases)
qed

lemma scalar_product_eq0: "\<forall>c\<in>set ns. c = 0 \<Longrightarrow> scalar_product ns is = 0"
proof (induct "is" arbitrary: "ns")
  case Cons
  then show ?case by (cases ns) (auto simp: scalar_product_def cong del: if_weak_cong)
qed (simp add: scalar_product_def)

lemma nullable0_satisfies0[Presb_simps]: "Length \<AA> = 0 \<Longrightarrow> nullable0 a = \<AA> \<Turnstile>0 a"
proof (induct a)
  case Eq then show ?case unfolding nullable0.simps satisfies0.simps
    by transfer (auto simp: len_eq0_iff scalar_product_eq0)
qed

lemma satisfies0_cong: "wf0 (#\<^sub>V \<BB>) a \<Longrightarrow> #\<^sub>V \<AA> = #\<^sub>V \<BB> \<Longrightarrow> lformula0 a \<Longrightarrow>
  (\<And>m k. m < #\<^sub>V \<BB> \<Longrightarrow> m\<^bsup>\<AA>\<^esup>k = m\<^bsup>\<BB>\<^esup>k) \<Longrightarrow> \<AA> \<Turnstile>0 a = \<BB> \<Turnstile>0 a"
proof (induct a)
  case Eq then show ?case unfolding satisfies0.simps
    by transfer (auto simp: scalar_product_def
      intro!: arg_cong[of _ _ sum_list] map_index_cong elim!: lformula0.cases)
qed

lemma wf_lderiv0[Presb_simps]:
  "wf0 idx a \<Longrightarrow> lformula0 a \<Longrightarrow> Formula_Operations.wf (\<lambda>_. Suc) wf0 idx (lderiv0 x a)"
  by (induct a) (auto elim: lformula0.cases simp: Formula_Operations.wf.simps Let_def)

lemma lformula_lderiv0[Presb_simps]:
  "lformula0 a \<Longrightarrow> Formula_Operations.lformula lformula0 (lderiv0 x a)"
  by (induct a)
    (auto elim: lformula0.cases intro: lformula0.intros simp: Let_def Formula_Operations.lformula.simps)

lemma wf_rderiv0[Presb_simps]:
  "wf0 idx a \<Longrightarrow> Formula_Operations.wf (\<lambda>_. Suc) wf0 idx (rderiv0 x a)"
  by (induct a) (auto elim: lformula0.cases simp: Formula_Operations.wf.simps Let_def)

lemma find0_FV0[Presb_simps]: "\<lbrakk>wf0 idx a; l < idx\<rbrakk> \<Longrightarrow> find0 k l a = (l \<in> FV0 k a)"
  by (induct a) (auto simp: FV0_def)

lemma FV0_less[Presb_simps]: "wf0 idx a \<Longrightarrow> v \<in> FV0 k a \<Longrightarrow> v < idx"
  by (induct a) (auto simp: FV0_def)

lemma finite_FV0[Presb_simps]: "finite (FV0 k a)"
  by (induct a) (auto simp: FV0_def)

lemma finite_lderiv0[Presb_simps]:
  assumes "lformula0 a"
  shows "finite {\<phi>. \<exists>xs. \<phi> = fold (Formula_Operations.deriv extend lderiv0) xs (FBase a)}"
proof -
  define d where "d = Formula_Operations.deriv extend lderiv0"
  define l where "l is = sum_list [i. i \<leftarrow> is, i < 0]" for "is" :: "int list"
  define h where "h is = sum_list [i. i \<leftarrow> is, i > 0]" for "is" :: "int list"
  define \<Phi> where "\<Phi> a = (case a of
    Eq is n z \<Rightarrow> {FBase (Eq is i 0) | i . i \<in> {min (- h is) n .. max (- l is) n}} \<union>
      {FBool False :: formula})" for a
  { fix xs
    note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
    from \<open>lformula0 a\<close> have "FBase a \<in> \<Phi> a" by (auto simp: elim!: lformula0.cases)
    moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
    proof (induct a, unfold \<Phi>_def presb.case, elim UnE CollectE insertE emptyE exE conjE)
      fix "is" :: "int list" and bs :: "bool list" and i n :: int and \<phi> :: formula
      assume "i \<in> {min (- h is) n..max (- l is) n}" "\<phi> = FBase (presb.Eq is i 0)"
      moreover have "scalar_product bs is \<le> h is"
      proof (induct "is" arbitrary: bs)
        case (Cons x xs)
        from Cons[of "tl bs"] show ?case by (cases bs) (auto simp: h_def)
      qed (auto simp: h_def scalar_product_def)
      moreover have "l is \<le> scalar_product bs is"
      proof (induct "is" arbitrary: bs)
        case (Cons x xs)
        from Cons[of "tl bs"] show ?case by (cases bs) (auto simp: l_def)
      qed (auto simp: l_def scalar_product_def)
      ultimately show "d bs \<phi> \<in>
        {FBase (presb.Eq is i 0) |i. i \<in> {min (- h is) n..max (- l is) n}} \<union> {FBool False}"
        by (auto simp: d_def Let_def)
    qed (auto simp: d_def)
    then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a" by (induct xs) auto
    ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def by (auto split: presb.splits)
   ultimately show "?thesis" unfolding d_def by (blast intro: finite_subset)
qed

lemma finite_rderiv0[Presb_simps]:
  "finite {\<phi>. \<exists>xs. \<phi> = fold (Formula_Operations.deriv extend rderiv0) xs (FBase a)}"
proof -
  define d where "d = Formula_Operations.deriv extend rderiv0"
  define l where "l is = sum_list [i. i \<leftarrow> is, i < 0]"for "is" :: "int list"
  define h where "h is = sum_list [i. i \<leftarrow> is, i > 0]"for "is" :: "int list"
  define \<Phi> where "\<Phi> a = (case a of
    Eq is n z \<Rightarrow> {FBase (Eq is n i) | i . i \<in> {min (- h is) (min n z) .. max (- l is) (max n z)}} \<union>
      {FBool False :: formula})" for a
  { fix xs
    note Formula_Operations.fold_deriv_FBool[simp] Formula_Operations.deriv.simps[simp] \<Phi>_def[simp]
    have "FBase a \<in> \<Phi> a" by (auto split: presb.splits)
    moreover have "\<And>x \<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> d x \<phi> \<in> \<Phi> a"
    proof (induct a, unfold \<Phi>_def presb.case, elim UnE CollectE insertE emptyE exE conjE)
      fix "is" :: "int list" and bs :: "bool list" and i n m :: int and \<phi> :: formula
      assume "i \<in> {min (- h is) (min n m)..max (- l is) (max n m)}" "\<phi> = FBase (presb.Eq is n i)"
      moreover have "scalar_product bs is \<le> h is"
      proof (induct "is" arbitrary: bs)
        case (Cons x xs)
        from Cons[of "tl bs"] show ?case by (cases bs) (auto simp: h_def)
      qed (auto simp: h_def scalar_product_def)
      moreover have "l is \<le> scalar_product bs is"
      proof (induct "is" arbitrary: bs)
        case (Cons x xs)
        from Cons[of "tl bs"] show ?case by (cases bs) (auto simp: l_def)
      qed (auto simp: l_def scalar_product_def)
      ultimately show "d bs \<phi> \<in>
        {FBase (presb.Eq is n i) |i. i \<in> {min (- h is) (min n m)..max (- l is) (max n m)}} \<union> {FBool False}"
        by (auto 0 1 simp: d_def Let_def h_def l_def)
    qed (auto simp: d_def)
    then have "\<And>\<phi>. \<phi> \<in> \<Phi> a \<Longrightarrow> fold d xs \<phi> \<in> \<Phi> a" by (induct xs) auto
    ultimately have "fold d xs (FBase a) \<in> \<Phi> a" by blast
   }
   moreover have "finite (\<Phi> a)" unfolding \<Phi>_def by (auto split: presb.splits)
   ultimately show "?thesis" unfolding d_def by (blast intro: finite_subset)
qed

lemma scalar_product_CONS: "length xs = length (bs :: bool list) \<Longrightarrow>
  scalar_product (map_index (\<lambda>i n. 2 * n + bs ! i) xs) is =
  scalar_product bs is + 2 * scalar_product xs is"
  by (induct "is" arbitrary: bs xs) (auto split: list.splits simp: algebra_simps)

lemma eval_tm_CONS[simp]:
  "\<lbrakk>length is \<le> #\<^sub>V \<AA>; #\<^sub>V \<AA> = length x\<rbrakk> \<Longrightarrow>
   eval_tm (CONS x \<AA>) is = scalar_product x is + 2 * eval_tm \<AA> is"
  by transfer (auto simp: scalar_product_CONS[symmetric]
    intro!: arg_cong2[of _ _ _ _ scalar_product] nth_equalityI)

lemma satisfies_lderiv0[Presb_simps]:
  "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = length x; lformula0 a\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile> lderiv0 x a \<longleftrightarrow> CONS x \<AA> \<Turnstile>0 a"
  by (auto simp: Let_def Formula_Operations.satisfies_gen.simps
    split: if_splits elim!: lformula0.cases)

lemma satisfies_bounded_lderiv0[Presb_simps]:
  "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = length x; lformula0 a\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b lderiv0 x a \<longleftrightarrow> CONS x \<AA> \<Turnstile>0 a"
  by (auto simp: Let_def Formula_Operations.satisfies_gen.simps
    split: if_splits elim!: lformula0.cases)

lemma scalar_product_SNOC: "length xs = length (bs :: bool list)  \<Longrightarrow>
  scalar_product (map_index (\<lambda>i m. m + 2 ^ a * bs ! i) xs) is =
  scalar_product xs is + 2 ^ a * scalar_product bs is"
  by (induct "is" arbitrary: bs xs) (auto split: list.splits simp: algebra_simps)

lemma eval_tm_SNOC[simp]:
  "\<lbrakk>length is \<le> #\<^sub>V \<AA>; #\<^sub>V \<AA> = length x\<rbrakk> \<Longrightarrow>
   eval_tm (SNOC x \<AA>) is = eval_tm \<AA> is + 2 ^ Length \<AA> * scalar_product x is"
  by transfer (auto simp: scalar_product_SNOC[symmetric]
    intro!: arg_cong2[of _ _ _ _ scalar_product] nth_equalityI)

lemma Length_eq0_eval_tm_eq0[simp]: "Length \<AA> = 0 \<Longrightarrow> eval_tm \<AA> is = 0"
  by transfer (auto simp: len_eq0_iff scalar_product_eq0)

lemma less_pow2: "x < 2 ^ a \<Longrightarrow> int x < 2 ^ a"
  by (metis of_nat_less_iff of_nat_numeral of_nat_power [symmetric])

lemma scalar_product_upper_bound: "\<forall>x\<in>set b. len x \<le> a \<Longrightarrow>
  scalar_product b is \<le> (2 ^ a - 1) * sum_list [i. i \<leftarrow> is, i > 0]"
proof (induct "is" arbitrary: b)
  case (Cons i "is")
  then have "scalar_product (tl b) is \<le> (2 ^ a - 1) * sum_list [i. i \<leftarrow> is, i > 0]"
    by (auto simp: in_set_tlD)
  with Cons(2) show ?case
    by (auto 0 3 split: list.splits simp: len_le_iff mult_le_0_iff
      distrib_left add.commute[of _ "(2 ^ a - 1) * i"] less_pow2
      intro: add_mono elim: order_trans[OF add_mono[OF order_refl]])
qed simp

lemma scalar_product_lower_bound: "\<forall>x\<in>set b. len x \<le> a \<Longrightarrow>
  scalar_product b is \<ge> (2 ^ a - 1) * sum_list [i. i \<leftarrow> is, i < 0]"
proof (induct "is" arbitrary: b)
  case (Cons i "is")
  then have "scalar_product (tl b) is \<ge> (2 ^ a - 1) * sum_list [i. i \<leftarrow> is, i < 0]"
    by (auto simp: in_set_tlD)
  with Cons(2) show ?case
    by (auto 0 3 split: list.splits simp: len_le_iff mult_le_0_iff
      distrib_left add.commute[of _ "(2 ^ a - 1) * i"] less_pow2
      intro: add_mono elim: order_trans[OF add_mono[OF order_refl]] order_trans)
qed simp

lemma eval_tm_upper_bound: "eval_tm \<AA> is \<le> (2 ^ Length \<AA> - 1) * sum_list [i. i \<leftarrow> is, i > 0]"
  by transfer (auto simp: scalar_product_upper_bound)

lemma eval_tm_lower_bound: "eval_tm \<AA> is \<ge> (2 ^ Length \<AA> - 1) * sum_list [i. i \<leftarrow> is, i < 0]"
  by transfer (auto simp: scalar_product_lower_bound)

lemma satisfies_bounded_rderiv0[Presb_simps]:
  "\<lbrakk>wf0 (#\<^sub>V \<AA>) a; #\<^sub>V \<AA> = length x\<rbrakk> \<Longrightarrow> \<AA> \<Turnstile>\<^sub>b rderiv0 x a \<longleftrightarrow> SNOC x \<AA> \<Turnstile>0 a"
proof (induct a)
  case (Eq "is" n d)
  let ?l = "Length \<AA>"
  define d' where "d' = scalar_product x is + 2 * d"
  define l where "l = sum_list  [i. i \<leftarrow> is, i < 0]"
  define h where "h = sum_list  [i. i \<leftarrow> is, i > 0]"
  from Eq show ?case
  unfolding wf0.simps satisfies0.simps rderiv0.simps Let_def
  proof (split if_splits, simp only: Formula_Operations.satisfies_gen.simps satisfies0.simps
    Length_SNOC eval_tm_SNOC simp_thms(13) de_Morgan_conj not_le
    min_less_iff_conj max_less_iff_conj d'_def[symmetric] h_def[symmetric] l_def[symmetric], safe)
    assume "eval_tm \<AA> is + 2 ^ ?l * scalar_product x is = n - 2 ^ Suc ?l * d"
    with eval_tm_upper_bound[of \<AA> "is"] eval_tm_lower_bound[of \<AA> "is"] have
      *: "n + h \<le> 2 ^ ?l * (h + d')" "2 ^ ?l * (l + d') \<le> n + l"
      by (auto simp: algebra_simps h_def l_def d'_def)
    assume **: "d' \<notin> {min (- h) n..max (- l) n}"
    { assume "0 \<le> n + h"
      from order_trans[OF this *(1)] have "0 \<le> h + d'"
        unfolding zero_le_mult_iff using zero_less_power[of 2] by presburger
    }
    moreover
    { assume "n + h < 0"
      with *(1) have "n \<le> d'" by (auto dest: order_trans[OF _ mult_right_mono_neg[of 1]])
    }
    moreover
    { assume "n + l < 0"
      from le_less_trans[OF *(2) this] have "l + d' < 0" unfolding mult_less_0_iff by auto
    }
    moreover
    { assume "0 \<le> n + l"
      then have "0 \<le> l + d'" using ** calculation(1-2) by force
      with *(2) have "d' \<le> n" by (force dest: order_trans[OF mult_right_mono[of 1], rotated])
    }
    ultimately have "min (- h) n \<le> d'" "d' \<le> max (- l) n" by (auto simp: min_def max_def)
    with ** show False by auto
  qed (auto simp: algebra_simps d'_def)
qed

declare [[goals_limit = 100]]

global_interpretation Presb: Formula
  where SUC = SUC and LESS = "\<lambda>_. (<)" and Length = Length
  and assigns = assigns and nvars = nvars and Extend = Extend and CONS = CONS and SNOC = SNOC
  and extend = extend and size = size_atom and zero = zero and alphabet = \<sigma> and eval = test_bit
  and downshift = downshift and upshift = upshift and add = set_bit and cut = cut_bits and len = len
  and restrict = "\<lambda>_ _. True" and Restrict = "\<lambda>_ _. FBool True" and lformula0 = lformula0
  and FV0 = FV0 and find0 = find0 and wf0 = wf0 and decr0 = decr0 and satisfies0 = satisfies0
  and nullable0 = nullable0 and lderiv0 = lderiv0 and rderiv0 = rderiv0
  and TYPEVARS = undefined
  defines norm = "Formula_Operations.norm find0 decr0"
  and nFOr = "Formula_Operations.nFOr :: formula \<Rightarrow> _"
  and nFAnd = "Formula_Operations.nFAnd :: formula \<Rightarrow> _"
  and nFNot = "Formula_Operations.nFNot find0 decr0 :: formula \<Rightarrow> _"
  and nFEx = "Formula_Operations.nFEx find0 decr0"
  and nFAll = "Formula_Operations.nFAll find0 decr0"
  and decr = "Formula_Operations.decr decr0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and find = "Formula_Operations.find find0 :: _ \<Rightarrow> _ \<Rightarrow> formula \<Rightarrow> _"
  and FV = "Formula_Operations.FV FV0"
  and RESTR = "Formula_Operations.RESTR (\<lambda>_ _. FBool True) :: _ \<Rightarrow> formula"
  and RESTRICT = "Formula_Operations.RESTRICT (\<lambda>_ _. FBool True) FV0"
  and deriv = "\<lambda>d0 (a :: atom) (\<phi> :: formula). Formula_Operations.deriv extend d0 a \<phi>"
  and nullable = "\<lambda>\<phi> :: formula. Formula_Operations.nullable nullable0 \<phi>"
  and fut_default = "Formula.fut_default extend zero rderiv0"
  and fut = "Formula.fut extend zero find0 decr0 rderiv0"
  and finalize = "Formula.finalize SUC extend zero find0 decr0 rderiv0"
  and final = "Formula.final SUC extend zero find0 decr0
     nullable0 rderiv0 :: nat \<Rightarrow> formula \<Rightarrow> _"
  and presb_wf = "Formula_Operations.wf SUC (wf0 :: nat \<Rightarrow> presb \<Rightarrow> _)"
  and presb_lformula = "Formula_Operations.lformula (lformula0 :: presb \<Rightarrow> _) :: formula \<Rightarrow> _"
  and check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: formula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. presb_wf idx \<phi> \<and> presb_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: formula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    (final idx) (\<lambda>\<phi> :: formula. presb_wf idx \<phi> \<and> presb_lformula \<phi>)
    (=)"
  and bounded_check_eqv = "\<lambda>idx. DAs.check_eqv
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: formula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. presb_wf idx \<phi> \<and> presb_lformula \<phi>)
    (\<sigma> idx) (\<lambda>\<phi>. norm (RESTRICT \<phi>) :: formula)
    (\<lambda>a \<phi>. norm (deriv (lderiv0 :: _ \<Rightarrow> _ \<Rightarrow> formula) (a :: atom) \<phi>))
    nullable (\<lambda>\<phi> :: formula. presb_wf idx \<phi> \<and> presb_lformula \<phi>)
    (=)"
  and automaton = "DA.automaton
    (\<lambda>a \<phi>. norm (deriv lderiv0 (a :: atom) \<phi> :: formula))"
  by standard (auto simp: Presb_simps \<sigma>_def set_n_lists distinct_n_lists
    Formula_Operations.lformula.simps Formula_Operations.satisfies_gen.simps Formula_Operations.wf.simps
    dest: satisfies0_cong split: presb.splits if_splits)

(*Workaround for code generation*)
lemma check_eqv_code[code]: "check_eqv idx r s =
  ((presb_wf idx r \<and> presb_lformula r) \<and> (presb_wf idx s \<and> presb_lformula s) \<and>
  (case rtrancl_while (\<lambda>(p, q). final idx p = final idx q)
    (\<lambda>(p, q). map (\<lambda>a. (norm (deriv lderiv0 a p), norm (deriv lderiv0 a q))) (\<sigma> idx))
    (norm (RESTRICT r), norm (RESTRICT s)) of
    None \<Rightarrow> False
  | Some ([], x) \<Rightarrow> True
  | Some (a # list, x) \<Rightarrow> False))"
  unfolding check_eqv_def Presb.check_eqv_def Presb.step_alt ..

definition while where [code del, code_abbrev]: "while idx \<phi> = while_default (fut_default idx \<phi>)"
declare while_default_code[of "fut_default idx \<phi>" for idx \<phi>, folded while_def, code]

lemma check_eqv_sound: 
  "\<lbrakk>#\<^sub>V \<AA> = idx; check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (Presb.sat \<AA> \<phi> \<longleftrightarrow> Presb.sat \<AA> \<psi>)"
  unfolding check_eqv_def by (rule Presb.check_eqv_soundness)

lemma bounded_check_eqv_sound:
  "\<lbrakk>#\<^sub>V \<AA> = idx; bounded_check_eqv idx \<phi> \<psi>\<rbrakk> \<Longrightarrow> (Presb.sat\<^sub>b \<AA> \<phi> \<longleftrightarrow> Presb.sat\<^sub>b \<AA> \<psi>)"
  unfolding bounded_check_eqv_def by (rule Presb.bounded_check_eqv_soundness)

method_setup check_equiv = \<open>
  let
    fun tac ctxt =
      let
        val conv = @{computation_check terms: Trueprop
          "0 :: nat" "1 :: nat" "2 :: nat" "3 :: nat" Suc
          "plus :: nat \<Rightarrow> _" "minus :: nat \<Rightarrow> _"
          "times :: nat \<Rightarrow> _" "divide :: nat \<Rightarrow> _" "modulo :: nat \<Rightarrow> _"
          "0 :: int" "1 :: int" "2 :: int" "3 :: int" "-1 :: int"
          check_eqv datatypes: formula "int list" integer bool} ctxt
      in
        CONVERSION (Conv.params_conv ~1 (K (Conv.concl_conv ~1 conv)) ctxt) THEN'
        resolve_tac ctxt [TrueI]
      end
  in
    Scan.succeed (SIMPLE_METHOD' o tac)
  end
\<close>

end
