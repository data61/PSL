section \<open>Simple While Language with probabilistic choice and parallel execution\<close>

theory Language_Semantics
imports Interface
begin


subsection \<open>Preliminaries\<close>

text\<open>Trivia\<close>

declare zero_le_mult_iff[simp]
declare split_mult_pos_le[simp]
declare zero_le_divide_iff[simp]

lemma in_minus_Un[simp]:
assumes "i \<in> I"
shows "I - {i} Un {i} = I" and "{i} Un (I - {i}) = I"
apply(metis Un_commute assms insert_Diff_single insert_absorb insert_is_Un)
by (metis assms insert_Diff_single insert_absorb insert_is_Un)

lemma less_plus_cases[case_names Left Right]:
assumes
*: "(i::nat) < n1 \<Longrightarrow> phi" and
**: "\<And> i2. i = n1 + i2 \<Longrightarrow> phi"
shows phi
proof(cases "i < n1")
  case True
  thus ?thesis using * by simp
next
  case False hence "n1 \<le> i" by simp
  then obtain i2 where "i = n1 + i2" by (metis le_iff_add)
  thus ?thesis using ** by blast
qed

lemma less_plus_elim[elim!, consumes 1, case_names Left Right]:
assumes i: "(i:: nat) < n1 + n2" and
*: "i < n1 \<Longrightarrow> phi" and
**: "\<And> i2. \<lbrakk>i2 < n2; i = n1 + i2\<rbrakk> \<Longrightarrow> phi"
shows phi
apply(rule less_plus_cases[of i n1])
using assms by auto

lemma nth_append_singl[simp]:
"i < length al \<Longrightarrow> (al @ [a]) ! i = al ! i"
by (auto simp add: nth_append)

lemma take_append_singl[simp]:
assumes "n < length al" shows "take n (al @ [a]) = take n al"
using assms by (induct al rule: rev_induct) auto

lemma length_unique_prefix:
  "al1 \<le> al \<Longrightarrow> al2 \<le> al \<Longrightarrow> length al1 = length al2 \<Longrightarrow> al1 = al2"
  by (metis not_equal_is_parallel parallelE prefix_same_cases less_eq_list_def)

text\<open>take:\<close>

lemma take_length[simp]:
"take (length al) al = al"
using take_all by auto

lemma take_le:
assumes "n < length al"
shows "take n al @ [al ! n] \<le> al"
by (metis assms take_Suc_conv_app_nth take_is_prefix less_eq_list_def)

lemma list_less_iff_prefix: "a < b \<longleftrightarrow> strict_prefix a b"
  by (metis le_less less_eq_list_def less_irrefl prefix_order.le_less prefix_order.less_irrefl)

lemma take_lt:
  "n < length al \<Longrightarrow> take n al < al"
  unfolding list_less_iff_prefix
  using prefix_order.le_less[of "take n al" al]
  by (simp add: take_is_prefix) (metis length_take min_absorb2 nat_le_linear not_less)

lemma le_take:
assumes "n1 \<le> n2"
shows "take n1 al \<le> take n2 al"
using assms proof(induct al arbitrary: n1 n2)
  case (Cons a al)
  thus ?case
  by (cases n1 n2 rule: nat.exhaust[case_product nat.exhaust]) auto
qed auto

lemma inj_take:
assumes "n1 \<le> length al" and "n2 \<le> length al"
shows "take n1 al = take n2 al \<longleftrightarrow> n1 = n2"
proof-
  {assume "take n1 al = take n2 al"
   hence "n1 = n2"
   using assms proof(induct al arbitrary: n1 n2)
     case (Cons a al)
     thus ?case
     by (cases n1 n2 rule: nat.exhaust[case_product nat.exhaust]) auto
   qed auto
  }
  thus ?thesis by auto
qed

lemma lt_take: "n1 < n2 \<Longrightarrow> n2 \<le> length al \<Longrightarrow> take n1 al < take n2 al"
  by (metis inj_take le_less_trans le_take not_less_iff_gr_or_eq order.not_eq_order_implies_strict order.strict_implies_order)

text\<open>lsum:\<close>

definition lsum :: "('a \<Rightarrow> nat) \<Rightarrow> 'a list \<Rightarrow> nat" where
"lsum f al \<equiv> sum_list (map f al)"

lemma lsum_simps[simp]:
 "lsum f [] = 0"
 "lsum f (al @ [a]) = lsum f al + f a"
unfolding lsum_def by auto

lemma lsum_append:
"lsum f (al @ bl) = lsum f al + lsum f bl"
unfolding lsum_def by auto

lemma lsum_cong[fundef_cong]:
assumes "\<And> a. a \<in> set al \<Longrightarrow> f a = g a"
shows "lsum f al = lsum g al"
using assms unfolding lsum_def by (metis map_eq_conv)

lemma lsum_gt_0[simp]:
assumes "al \<noteq> []" and "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
shows "0 < lsum f al"
using assms by (induct rule: rev_induct) auto

lemma lsum_mono[simp]:
assumes "al \<le> bl"
shows "lsum f al \<le> lsum f bl"
proof-
  obtain cl where bl: "bl = al @ cl" using assms unfolding prefix_def less_eq_list_def by blast
  thus ?thesis unfolding bl lsum_append by simp
qed

lemma lsum_mono2[simp]:
assumes f: "\<And> b. b \<in> set bl \<Longrightarrow> f b > 0" and le: "al < bl"
shows "lsum f al < lsum f bl"
proof-
  obtain cl where bl: "bl = al @ cl" and cl: "cl \<noteq> []"
    using assms unfolding list_less_iff_prefix prefix_def strict_prefix_def by blast
  have "lsum f al < lsum f al + lsum f cl"
  using f cl unfolding bl by simp
  also have "... = lsum f bl" unfolding bl lsum_append by simp
  finally show ?thesis .
qed

lemma lsum_take[simp]:
"lsum f (take n al) \<le> lsum f al"
by (metis lsum_mono take_is_prefix less_eq_list_def)

lemma less_lsum_nchotomy:
assumes f: "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
and i: "(i::nat) < lsum f al"
shows "\<exists> n j. n < length al \<and> j < f (al ! n) \<and> i = lsum f (take n al) + j"
using assms proof(induct rule: rev_induct)
  case (snoc a al)
  hence i: "i < lsum f al + f a" and
  pos: "0 < f a"  "\<And>a'. a' \<in> set al \<Longrightarrow> 0 < f a'" by auto
  from i show ?case
  proof(cases rule: less_plus_elim)
    case Left
    then obtain n j where "n < length al \<and> j < f (al ! n) \<and> i = lsum f (take n al) + j"
    using pos snoc by auto
    thus ?thesis
    apply - apply(rule exI[of _ n]) apply(rule exI[of _ j]) by auto
  next
    case (Right j)
    thus ?thesis
    apply - apply(rule exI[of _ "length al"]) apply(rule exI[of _ j]) by simp
  qed
qed auto

lemma less_lsum_unique:
assumes "\<And> a. a \<in> set al \<Longrightarrow> (0::nat) < f a"
and "n1 < length al \<and> j1 < f (al ! n1)"
and "n2 < length al \<and> j2 < f (al ! n2)"
and "lsum f (take n1 al) + j1 = lsum f (take n2 al) + j2"
shows "n1 = n2 \<and> j1 = j2"
using assms proof(induct al arbitrary: n1 n2 j1 j2 rule: rev_induct)
  case (snoc a al)
  hence pos: "0 < f a"   "\<And> a'. a' \<in> set al \<Longrightarrow> 0 < f a'"
  and n1: "n1 < length al + 1" and n2: "n2 < length al + 1" by auto
  from n1 show ?case
  proof(cases rule: less_plus_elim)
    case Left note n1 = Left
    hence j1: "j1 < f (al ! n1)" using snoc by auto
    obtain al' where al: "al = (take n1 al) @ ((al ! n1) # al')"
    using n1 by (metis append_take_drop_id Cons_nth_drop_Suc)
    have "j1 < lsum f ((al ! n1) # al')" using pos j1 unfolding lsum_def by simp
    hence "lsum f (take n1 al) + j1 < lsum f (take n1 al) + lsum f ((al ! n1) # al')" by simp
    also have "... = lsum f al" unfolding lsum_append[THEN sym] using al by simp
    finally have lsum1: "lsum f (take n1 al) + j1 < lsum f al" .
    from n2 show ?thesis
    proof(cases rule: less_plus_elim)
      case Left note n2 = Left
      hence j2: "j2 < f (al ! n2)" using snoc by auto
      show ?thesis apply(rule snoc(1)) using snoc using pos n1 j1 n2 j2 by auto
    next
      case Right
      hence n2: "n2 = length al" by simp
      hence j2: "j2 < f a" using snoc by simp
      have "lsum f (take n1 al) + j1 = lsum f al + j2" using n1 n2 snoc by simp
      hence False using lsum1 by auto
      thus ?thesis by simp
    qed
  next
    case Right
    hence n1: "n1 = length al" by simp
    hence j1: "j1 < f a" using snoc by simp
    from n2 show ?thesis
    proof(cases rule: less_plus_elim)
      case Left note n2 = Left
      hence j2: "j2 < f (al ! n2)" using snoc by auto
      obtain al' where al: "al = (take n2 al) @ ((al ! n2) # al')"
      using n2 by (metis append_take_drop_id Cons_nth_drop_Suc)
      have "j2 < lsum f ((al ! n2) # al')" using pos j2 unfolding lsum_def by simp
      hence "lsum f (take n2 al) + j2 < lsum f (take n2 al) + lsum f ((al ! n2) # al')" by simp
      also have "... = lsum f al" unfolding lsum_append[THEN sym] using al by simp
      finally have lsum2: "lsum f (take n2 al) + j2 < lsum f al" .
      have "lsum f al + j1 = lsum f (take n2 al) + j2" using n1 n2 snoc by simp
      hence False using lsum2 by auto
      thus ?thesis by simp
    next
      case Right
      hence n2: "n2 = length al" by simp
      have "j1 = j2" using n1 n2 snoc by simp
      thus ?thesis using n1 n2 by simp
    qed
  qed
qed auto

definition locate_pred where
"locate_pred f al (i::nat) n_j \<equiv>
 fst n_j < length al \<and>
 snd n_j < f (al ! (fst n_j)) \<and>
 i = lsum f (take (fst n_j) al) + (snd n_j)"

definition locate where
"locate f al i \<equiv> SOME n_j. locate_pred f al i n_j"

definition locate1 where "locate1 f al i \<equiv> fst (locate f al i)"
definition locate2 where "locate2 f al i \<equiv> snd (locate f al i)"

lemma locate_pred_ex:
assumes "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
and "i < lsum f al"
shows "\<exists> n_j. locate_pred f al i n_j"
using assms less_lsum_nchotomy unfolding locate_pred_def by force

lemma locate_pred_unique:
assumes "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
and "locate_pred f al i n1_j1" "locate_pred f al i n2_j2"
shows "n1_j1 = n2_j2"
using assms less_lsum_unique unfolding locate_pred_def
apply(cases n1_j1, cases n2_j2) apply simp by blast

lemma locate_locate_pred:
assumes "\<And> a. a \<in> set al \<Longrightarrow> (0::nat) < f a"
and "i < lsum f al"
shows "locate_pred f al i (locate f al i)"
proof-
  obtain n_j where "locate_pred f al i n_j"
  using assms locate_pred_ex[of al f i] by auto
  thus ?thesis unfolding locate_def apply(intro someI[of "locate_pred f al i"]) by blast
qed

lemma locate_locate_pred_unique:
assumes "\<And> a. a \<in> set al \<Longrightarrow> (0::nat) < f a"
and "locate_pred f al i n_j"
shows "n_j = locate f al i"
unfolding locate_def apply(rule sym, rule some_equality)
using assms locate_locate_pred apply force
using assms locate_pred_unique by blast

lemma locate:
assumes "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
and "i < lsum f al"
shows "locate1 f al i < length al \<and>
 locate2 f al i < f (al ! (locate1 f al i)) \<and>
 i = lsum f (take (locate1 f al i) al) + (locate2 f al i)"
using assms locate_locate_pred
unfolding locate1_def locate2_def locate_pred_def by auto

lemma locate_unique:
assumes "\<And> a. a \<in> set al \<Longrightarrow> 0 < f a"
and "n < length al" and "j < f (al ! n)" and "i = lsum f (take n al) + j"
shows "n = locate1 f al i \<and> j = locate2 f al i"
proof-
  define n_j where "n_j = (n,j)"
  have "locate_pred f al i n_j" using assms unfolding n_j_def locate_pred_def by auto
  hence "n_j = locate f al i" using assms locate_locate_pred_unique by blast
  thus ?thesis unfolding n_j_def locate1_def locate2_def by (metis fst_conv n_j_def snd_conv)
qed

text\<open>sum:\<close>

lemma sum_2[simp]:
"sum f {..< 2} = f 0 + f (Suc 0)"
proof-
  have "{..< 2} = {0, Suc 0}" by auto
  thus ?thesis by force
qed

lemma inj_Plus[simp]:
"inj ((+) (a::nat))"
unfolding inj_on_def by auto

lemma inj_on_Plus[simp]:
"inj_on ((+) (a::nat)) A"
unfolding inj_on_def by auto

lemma Plus_int[simp]:
fixes a :: nat
shows "(+) b ` {..< a} = {b ..< b + a}"
proof safe
  fix x::nat assume "x \<in> {b..< b + a}"
  hence "b \<le> x" and x: "x < a + b" by auto
  then obtain y where xb: "x = b + y" by (metis le_iff_add)
  hence "y < a" using x by simp
  thus "x \<in> (+) b ` {..<a}" using xb by auto
qed auto

lemma sum_minus[simp]:
fixes a :: nat
shows "sum f {a ..< a + b} = sum (%x. f (a + x)) {..< b}"
using sum.reindex[of "(+) a" "{..< b}" f] by auto

lemma sum_Un_introL:
assumes "A1 = B1 Un C1" and "x = x1 + x2"
"finite A1" and
"B1 Int C1 = {}" and
"sum f1 B1 = x1" and "sum f1 C1 = x2"
shows "sum f1 A1 = x"
by (metis assms finite_Un sum.union_disjoint)

lemma sum_Un_intro:
assumes "A1 = B1 Un C1" and "A2 = B2 Un C2" and
"finite A1" and "finite A2" and
"B1 Int C1 = {}" and "B2 Int C2 = {}" and
"sum f1 B1 = sum f2 B2" and "sum f1 C1 = sum f2 C2"
shows "sum f1 A1 = sum f2 A2"
by (metis assms finite_Un sum.union_disjoint)

lemma sum_UN_introL:
assumes A1: "A1 = (UN n : N. B1 n)" and a2: "a2 = sum b2 N" and
fin: "finite N" "\<And> n. n \<in> N \<Longrightarrow> finite (B1 n)" and
int: "\<And> m n. {m, n} \<subseteq> N \<and> m \<noteq> n \<Longrightarrow> B1 m \<inter> B1 n = {}" and
ss: "\<And> n. n \<in> N \<Longrightarrow> sum f1 (B1 n) = b2 n"
shows "sum f1 A1 = a2" (is "?L = a2")
proof-
  have "?L = sum (%n. sum f1 (B1 n)) N"
  unfolding A1 using sum.UNION_disjoint[of N B1 f1] fin int by simp
  also have "... = sum b2 N" using ss fin by auto
  also have "... = a2" using a2 by simp
  finally show ?thesis .
qed

lemma sum_UN_intro:
assumes A1: "A1 = (UN n : N. B1 n)" and A2: "A2 = (UN n : N. B2 n)" and
fin: "finite N" "\<And> n. n \<in> N \<Longrightarrow> finite (B1 n) \<and> finite (B2 n)" and
int: "\<And> m n. {m, n} \<subseteq> N \<and> m \<noteq> n \<Longrightarrow> B1 m \<inter> B1 n = {}" "\<And> m n. {m, n} \<subseteq> N \<Longrightarrow> B2 m \<inter> B2 n = {}" and
ss: "\<And> n. n \<in> N \<Longrightarrow> sum f1 (B1 n) = sum f2 (B2 n)"
shows "sum f1 A1 = sum f2 A2" (is "?L = ?R")
proof-
  have "?L = sum (%n. sum f1 (B1 n)) N"
  unfolding A1 using sum.UNION_disjoint[of N B1 f1] fin int by simp
  also have "... = sum (%n. sum f2 (B2 n)) N" using ss fin sum.mono_neutral_left by auto
  also have "... = ?R"
  unfolding A2 using sum.UNION_disjoint[of N B2 f2] fin int by simp
  finally show ?thesis .
qed

lemma sum_Minus_intro:
fixes f1 :: "'a1 \<Rightarrow> real" and f2 :: "'a2 \<Rightarrow> real"
assumes "B1 = A1 - {a1}" and "B2 = A2 - {a2}" and
"a1 : A1" and "a2 : A2" and "finite A1" and "finite A2"
"sum f1 A1 = sum f2 A2" and "f1 a1 = f2 a2"
shows "sum f1 B1 = sum f2 B2"
proof-
  have 1: "A1 = B1 Un {a1}" and 2: "A2 = B2 Un {a2}"
    using assms by blast+
  from assms have "a1 \<notin> B1" by simp
  with 1 \<open>finite A1\<close> have "sum f1 A1 = sum f1 B1 + f1 a1"
    by simp
  hence 3: "sum f1 B1 = sum f1 A1 - f1 a1" by simp
  from assms have "a2 \<notin> B2" by simp
  with 2 \<open>finite A2 \<close>have "sum f2 A2 = sum f2 B2 + f2 a2"
    by simp
  hence "sum f2 B2 = sum f2 A2 - f2 a2" by simp
  thus ?thesis using 3 assms by simp
qed

lemma sum_singl_intro:
assumes "b = f a"
and "finite A" and "a \<in> A"
and "\<And> a'. \<lbrakk>a' \<in> A; a' \<noteq> a\<rbrakk> \<Longrightarrow> f a' = 0"
shows "sum f A = b"
proof-
  define B where "B = A - {a}"
  have "A = B Un {a}" unfolding B_def using assms by blast
  moreover have "B Int {a} = {}" unfolding B_def by blast
  ultimately have "sum f A = sum f B + sum f {a}"
  using assms sum.union_disjoint by blast
  moreover have "\<forall> b \<in> B. f b = 0" using assms unfolding B_def by auto
  ultimately show ?thesis using assms by auto
qed

lemma sum_all0_intro:
assumes "b = 0"
and "\<And> a. a \<in> A \<Longrightarrow> f a = 0"
shows "sum f A = b"
apply(cases "finite A")
by(metis assms sum.neutral sum.infinite)+

lemma sum_1:
assumes I: "finite I" and ss: "sum f I = 1" and i: "i \<in> I - I1" and I1: "I1 \<subseteq> I"
and f: "\<And>i. i \<in> I \<Longrightarrow> (0::real) \<le> f i"
shows "f i \<le> 1 - sum f I1"
proof-
  have "sum f I = sum f ({i} Un (I - {i}))" using i
  by (metis DiffE insert_Diff_single insert_absorb insert_is_Un)
  also have "... = sum f {i} + sum f (I - {i})"
  apply(rule sum.union_disjoint) using I by auto
  finally have "1 = f i + sum f (I - {i})" unfolding ss[THEN sym] by simp
  moreover have "sum f (I - {i}) \<ge> sum f I1"
  apply(rule sum_mono2) using assms by auto
  ultimately have "1 \<ge> f i + sum f I1" by auto
  thus ?thesis by auto
qed

subsection \<open>Syntax\<close>

datatype ('test, 'atom, 'choice) cmd =
  Done
| Atm "'atom"
| Seq "('test, 'atom, 'choice) cmd" "('test, 'atom, 'choice) cmd" ("_ ;; _"  [60, 61] 60)
| While "'test" "('test, 'atom, 'choice) cmd"
| Ch 'choice "('test, 'atom, 'choice) cmd" "('test, 'atom, 'choice) cmd"
| Par "('test, 'atom, 'choice) cmd list"
| ParT "('test, 'atom, 'choice) cmd list"

(* Commands containing no while loops: *)
fun noWhile where
  "noWhile Done \<longleftrightarrow> True"
| "noWhile (Atm atm) \<longleftrightarrow> True"
| "noWhile (c1 ;; c2) \<longleftrightarrow> noWhile c1 \<and> noWhile c2"
| "noWhile (While tst c) \<longleftrightarrow> False"
| "noWhile (Ch ch c1 c2) \<longleftrightarrow> noWhile c1 \<and> noWhile c2"
| "noWhile (Par cl) \<longleftrightarrow> (\<forall> c \<in> set cl. noWhile c)"
| "noWhile (ParT cl) \<longleftrightarrow> (\<forall> c \<in> set cl. noWhile c)"

(* ``Finished" commands: *)
fun finished where
  "finished Done \<longleftrightarrow> True"
| "finished (Atm atm) \<longleftrightarrow> False"
| "finished (c1 ;; c2) \<longleftrightarrow> False"
| "finished (While tst c) \<longleftrightarrow> False"
| "finished (Ch ch c1 c2) \<longleftrightarrow> False"
| "finished (Par cl) \<longleftrightarrow> (\<forall> c \<in> set cl. finished c)"
| "finished (ParT cl) \<longleftrightarrow> (\<forall> c \<in> set cl. finished c)"

definition noWhileL where
"noWhileL cl \<equiv> \<forall> c \<in> set cl. noWhile c"

lemma fin_Par_noWhileL[simp]:
"noWhile (Par cl) \<longleftrightarrow> noWhileL cl"
unfolding noWhileL_def by simp

lemma fin_ParT_noWhileL[simp]:
"noWhile (ParT cl) \<longleftrightarrow> noWhileL cl"
unfolding noWhileL_def by simp

declare noWhile.simps(6) [simp del]
declare noWhile.simps(7) [simp del]

lemma noWhileL_intro[intro]:
assumes "\<And> c. c \<in> set cl \<Longrightarrow> noWhile c"
shows "noWhileL cl"
using assms unfolding noWhileL_def by auto

lemma noWhileL_fin[simp]:
assumes "noWhileL cl" and "c \<in> set cl"
shows "noWhile c"
using assms unfolding noWhileL_def by simp

lemma noWhileL_update[simp]:
assumes cl: "noWhileL cl" and c': "noWhile c'"
shows "noWhileL (cl[n := c'])"
proof(cases "n < length cl")
  case True
  show ?thesis
  unfolding noWhileL_def proof safe
    fix c assume "c \<in> set (cl[n := c'])"
    hence "c \<in> insert c' (set cl)" using set_update_subset_insert by fastforce
    thus "noWhile c" using assms by (cases "c = c'") auto
  qed
qed (insert cl, auto)

definition finishedL where
"finishedL cl \<equiv> \<forall> c \<in> set cl. finished c"

lemma finished_Par_finishedL[simp]:
"finished (Par cl) \<longleftrightarrow> finishedL cl"
unfolding finishedL_def by simp

lemma finished_ParT_finishedL[simp]:
"finished (ParT cl) \<longleftrightarrow> finishedL cl"
unfolding finishedL_def by simp

declare finished.simps(6) [simp del]
declare finished.simps(7) [simp del]

lemma finishedL_intro[intro]:
assumes "\<And> c. c \<in> set cl \<Longrightarrow> finished c"
shows "finishedL cl"
using assms unfolding finishedL_def by auto

lemma finishedL_finished[simp]:
assumes "finishedL cl" and "c \<in> set cl"
shows "finished c"
using assms unfolding finishedL_def by simp

lemma finishedL_update[simp]:
assumes cl: "finishedL cl" and c': "finished c'"
shows "finishedL (cl[n := c'])"
proof(cases "n < length cl")
  case True
  show ?thesis
  unfolding finishedL_def proof safe
    fix c assume "c \<in> set (cl[n := c'])"
    hence "c \<in> insert c' (set cl)" using set_update_subset_insert by fastforce
    thus "finished c" using assms by (cases "c = c'") auto
  qed
qed (insert cl, auto)

lemma finished_fin[simp]:
"finished c \<Longrightarrow> noWhile c"
by(induct c) auto

lemma finishedL_noWhileL[simp]:
"finishedL cl \<Longrightarrow> noWhileL cl"
unfolding finishedL_def noWhileL_def by auto

locale PL =
  fixes
    aval :: "'atom \<Rightarrow> 'state \<Rightarrow> 'state" and
    tval :: "'test \<Rightarrow> 'state \<Rightarrow> bool" and
    cval :: "'choice \<Rightarrow> 'state \<Rightarrow> real"
  assumes
    properCh: "\<And> ch s. 0 \<le> cval ch s \<and> cval ch s \<le> 1"
begin

lemma [simp]: "(n::nat) < N \<Longrightarrow> 0 \<le> 1 / N" by auto

lemma [simp]: "(n::nat) < N \<Longrightarrow> 1 / N \<le> 1" by auto

lemma [simp]: "(n::nat) < N \<Longrightarrow> 0 \<le> 1 - 1 / N" by (simp add: divide_simps)

lemma sum_equal: "0 < (N::nat) \<Longrightarrow> sum (\<lambda> n. 1/N) {..< N} = 1"
unfolding sum_constant by auto

fun proper where
  "proper Done \<longleftrightarrow> True"
| "proper (Atm x) \<longleftrightarrow> True"
| "proper (Seq c1 c2) \<longleftrightarrow> proper c1 \<and> proper c2"
| "proper (While tst c) \<longleftrightarrow> proper c"
| "proper (Ch ch c1 c2) \<longleftrightarrow> proper c1 \<and> proper c2"
| "proper (Par cl) \<longleftrightarrow> cl \<noteq> [] \<and> (\<forall> c \<in> set cl. proper c)"
| "proper (ParT cl) \<longleftrightarrow> cl \<noteq> [] \<and> (\<forall> c \<in> set cl. proper c)"

definition properL where
"properL cl \<equiv> cl \<noteq> [] \<and> (\<forall> c \<in> set cl. proper c)"

lemma proper_Par_properL[simp]:
"proper (Par cl) \<longleftrightarrow> properL cl"
unfolding properL_def by simp

lemma proper_ParT_properL[simp]:
"proper (ParT cl) \<longleftrightarrow> properL cl"
unfolding properL_def by simp

declare proper.simps(6) [simp del]
declare proper.simps(7) [simp del]

lemma properL_intro[intro]:
"\<lbrakk>cl \<noteq> []; \<And> c. c \<in> set cl \<Longrightarrow> proper c\<rbrakk> \<Longrightarrow> properL cl"
unfolding properL_def by auto

lemma properL_notEmp[simp]: "properL cl \<Longrightarrow> cl \<noteq> []"
unfolding properL_def by simp

lemma properL_proper[simp]:
"\<lbrakk>properL cl; c \<in> set cl\<rbrakk> \<Longrightarrow> proper c"
unfolding properL_def by simp

lemma properL_update[simp]:
assumes cl: "properL cl" and c': "proper c'"
shows "properL (cl[n := c'])"
proof(cases "n < length cl")
  case True
  show ?thesis
  unfolding properL_def proof safe
    fix c assume "c \<in> set (cl[n := c'])"
    hence "c \<in> insert c' (set cl)" using set_update_subset_insert by fastforce
    thus "proper c" using assms by (cases "c = c'") auto
  qed (insert cl, auto)
qed (insert cl, auto)

lemma proper_induct[consumes 1, case_names Done Atm Seq While Ch Par ParT]:
assumes *: "proper c"
and Done: "phi Done"
and Atm: "\<And> atm. phi (Atm atm)"
and Seq: "\<And> c1 c2. \<lbrakk>phi c1; phi c2\<rbrakk> \<Longrightarrow> phi (c1 ;; c2)"
and While: "\<And> tst c. phi c \<Longrightarrow> phi (While tst c)"
and Ch: "\<And> ch c1 c2. \<lbrakk>phi c1; phi c2\<rbrakk> \<Longrightarrow> phi (Ch ch c1 c2)"
and Par: "\<And> cl. \<lbrakk>properL cl; \<And> c. c \<in> set cl \<Longrightarrow> phi c\<rbrakk> \<Longrightarrow> phi (Par cl)"
and ParT: "\<And> cl. \<lbrakk>properL cl; \<And> c. c \<in> set cl \<Longrightarrow> phi c\<rbrakk> \<Longrightarrow> phi (ParT cl)"
shows "phi c"
using * apply(induct c)
using assms unfolding properL_def by auto


subsubsection \<open>Operational Small-Step Semantics\<close>

(* "The Finished Threads": The sublist of finished threads from a list of threads  *)
definition "theFT cl \<equiv> {n. n < length cl \<and> finished (cl!n)}"

(* "The NopnFinished Threads": *)
definition "theNFT cl \<equiv> {n. n < length cl \<and> \<not> finished (cl!n)}"

lemma finite_theFT[simp]: "finite (theFT cl)"
unfolding theFT_def by simp

lemma theFT_length[simp]: "n \<in> theFT cl \<Longrightarrow> n < length cl"
unfolding theFT_def by simp

lemma theFT_finished[simp]: "n \<in> theFT cl \<Longrightarrow> finished (cl!n)"
unfolding theFT_def by simp

lemma finite_theNFT[simp]: "finite (theNFT cl)"
unfolding theNFT_def by simp

lemma theNFT_length[simp]: "n \<in> theNFT cl \<Longrightarrow> n < length cl"
unfolding theNFT_def by simp

lemma theNFT_notFinished[simp]: "n \<in> theNFT cl \<Longrightarrow> \<not> finished (cl!n)"
unfolding theNFT_def by simp

lemma theFT_Int_theNFT[simp]:
"theFT cl Int theNFT cl = {}" and "theNFT cl Int theFT cl = {}"
unfolding theFT_def theNFT_def by auto

lemma theFT_Un_theNFT[simp]:
"theFT cl Un theNFT cl = {..< length cl}" and
"theNFT cl Un theFT cl = {..< length cl}"
unfolding theFT_def theNFT_def by auto

lemma in_theFT_theNFT[simp]:
assumes "n1 \<in> theFT cl" and "n2 \<in> theNFT cl"
shows "n1 \<noteq> n2" and "n2 \<noteq> n1"
using assms theFT_Int_theNFT by blast+

(* The cumulated weight of the finished threads: *)
definition "WtFT cl \<equiv> sum (\<lambda> (n::nat). 1/(length cl)) (theFT cl)"

(* The cumulated weight of the non-finished threads: *)
definition "WtNFT cl \<equiv> sum (\<lambda> (n::nat). 1/(length cl)) (theNFT cl)"

lemma WtFT_WtNFT[simp]:
assumes "0 < length cl"
shows "WtFT cl + WtNFT cl = 1" (is "?A = 1")
proof-
  let ?w = "\<lambda> n. 1 / length cl" let ?L = "theFT cl" let ?Lnot = "theNFT cl"
  have 1: "{..< length cl} = ?L Un ?Lnot" by auto
  have "?A = sum ?w ?L + sum ?w ?Lnot" unfolding WtFT_def WtNFT_def by simp
  also have "... = sum ?w {..< length cl}" unfolding 1
  apply(rule sum.union_disjoint[THEN sym]) by auto
  also have "... = 1" unfolding sum_equal[OF assms] by auto
  finally show ?thesis .
qed

lemma WtNFT_1_WtFT: "0 < length cl \<Longrightarrow> WtNFT cl = 1 - WtFT cl"
  by (simp add: algebra_simps)

lemma WtNFT_WtFT_1[simp]:
assumes "0 < length cl" and "WtFT cl \<noteq> 1"
shows "WtNFT cl / (1 - WtFT cl) = 1" (is "?A / ?B = 1")
proof-
  have A: "?A = ?B" using assms WtNFT_1_WtFT by auto
  show ?thesis unfolding A using assms by auto
qed

lemma WtFT_ge_0[simp]: "WtFT cl \<ge> 0"
unfolding WtFT_def by (rule sum_nonneg) simp

lemma WtFT_le_1[simp]: "WtFT cl \<le> 1" (is "?L \<le> 1")
proof-
  let ?N = "length cl"
  have "?L \<le> sum (\<lambda> n::nat. 1/?N) {..< ?N}"
  unfolding WtFT_def apply(rule sum_mono2) by auto
  also have "... \<le> 1"
  by (metis div_by_0 le_cases neq0_conv not_one_le_zero of_nat_0 sum_not_0 sum_equal)
  finally show ?thesis .
qed

lemma le_1_WtFT[simp]: "0 \<le> 1 - WtFT cl" (is "0 \<le> ?R")
proof-
  have a: "-1 \<le> - WtFT cl" by simp
  have "(0 :: real) = 1 + (-1)" by simp
  also have "1 + (-1) \<le> 1 + (- WtFT cl)" using a by arith
  also have "... = ?R" by simp
  finally show ?thesis .
qed

lemma WtFT_lt_1[simp]: "WtFT cl \<noteq> 1 \<Longrightarrow> WtFT cl < 1"
using WtFT_le_1 by (auto simp add: le_less)

lemma lt_1_WtFT[simp]: "WtFT cl \<noteq> 1 \<Longrightarrow> 0 < 1 - WtFT cl"
using le_1_WtFT by (metis le_1_WtFT eq_iff_diff_eq_0 less_eq_real_def)

lemma notFinished_WtFT[simp]:
assumes "n < length cl" and "\<not> finished (cl ! n)"
shows "1 / length cl \<le> 1 - WtFT cl"
proof-
  have "0 < length cl" using assms by auto
  thus ?thesis unfolding WtFT_def apply(intro sum_1[of "{..< length cl}"])
  using assms by auto
qed

(* The branching of a command: *)
fun brn :: "('test, 'atom, 'choice) cmd \<Rightarrow> nat" where
  "brn Done = 1"
| "brn (Atm atm) = 1"
| "brn (c1 ;; c2) = brn c1"
| "brn (While tst c) = 1"
| "brn (Ch ch c1 c2) = 2"
| "brn (Par cl) = lsum brn cl"
| "brn (ParT cl) = lsum brn cl"

lemma brn_gt_0: "proper c \<Longrightarrow> 0 < brn c"
by (induct rule: proper_induct) auto

lemma brn_gt_0_L: "\<lbrakk>properL cl; c \<in> set cl\<rbrakk> \<Longrightarrow> 0 < brn c"
by (metis brn_gt_0 properL_def)

(* The locate-thread and locate-index operators.
   Given a thread list cl with n = length cl and i < (\<Sum> l < length cl . brn cl),
   (locateT cl i, locateI cl i) are (k, j) from the paper's Figure 1.
*)
definition "locateT \<equiv> locate1 brn"   definition "locateI \<equiv> locate2 brn"

definition "brnL cl n \<equiv> lsum brn (take n cl)"

lemma brnL_lsum: "brnL cl (length cl) = lsum brn cl"
unfolding brnL_def by simp

lemma brnL_unique:
assumes "properL cl" and "n1 < length cl \<and> j1 < brn (cl ! n1)"
and "n2 < length cl \<and> j2 < brn (cl ! n2)" and "brnL cl n1 + j1 = brnL cl n2 + j2"
shows "n1 = n2 \<and> j1 = j2"
apply (rule less_lsum_unique) using assms brn_gt_0 unfolding brnL_def properL_def by auto

lemma brn_Par_simp[simp]: "brn (Par cl) = brnL cl (length cl)"
unfolding brnL_lsum by simp

lemma brn_ParT_simp[simp]: "brn (ParT cl) = brnL cl (length cl)"
unfolding brnL_lsum by simp

declare brn.simps(6)[simp del]   declare brn.simps(7)[simp del]

lemma brnL_0[simp]: "brnL cl 0 = 0"
unfolding brnL_def by auto

lemma brnL_Suc[simp]: "n < length cl \<Longrightarrow> brnL cl (Suc n) = brnL cl n + brn (cl ! n)"
unfolding brnL_def using take_Suc_conv_app_nth[of n cl] by simp

lemma brnL_mono[simp]: "n1 \<le> n2 \<Longrightarrow> brnL cl n1 \<le> brnL cl n2"
using le_take[of n1 n2 cl] unfolding brnL_def by simp

lemma brnL_mono2[simp]:
assumes p: "properL cl" and n: "n1 < n2" and l: "n2 \<le> length cl"
shows "brnL cl n1 < brnL cl n2" (is "?L < ?R")
proof-
  have 1: "\<And>c. c \<in> set (take n2 cl) \<Longrightarrow> 0 < brn c"
  using p by (metis brn_gt_0 in_set_takeD properL_proper)
  have "take n1 cl < take n2 cl" using n l lt_take by auto
  hence "lsum brn (take n1 cl) < lsum brn (take n2 cl)"
  using lsum_mono2[of "take n2 cl" "%c. brn c" "take n1 cl"] 1 by simp
  thus ?thesis unfolding brnL_def .
qed

lemma brn_index[simp]:
assumes n: "n < length cl" and i: "i < brn (cl ! n)"
shows "brnL cl n + i < brnL cl (length cl)" (is "?L < ?R")
proof-
  have "?L < brnL cl (Suc n)" using assms by simp
  also have "... \<le> ?R"
  using n brnL_mono[of "Suc n" "length cl" cl] by simp
  finally show ?thesis .
qed

lemma brnL_gt_0[simp]: "\<lbrakk>properL cl; 0 < n\<rbrakk> \<Longrightarrow> 0 < brnL cl n"
by (metis properL_def brnL_mono brnL_mono2 le_0_eq length_greater_0_conv nat_le_linear neq0_conv)

lemma locateTI:
assumes "properL cl" and "ii < brn (Par cl)"
shows
"locateT cl ii < length cl \<and>
 locateI cl ii < brn (cl ! (locateT cl ii)) \<and>
 ii = brnL cl (locateT cl ii) + locateI cl ii"
using assms locate[of cl brn] brn_gt_0
unfolding locateT_def locateI_def brnL_def
unfolding brnL_lsum[THEN sym] by auto

lemma locateTI_unique:
assumes "properL cl" and "n < length cl"
and "i < brn (cl ! n)" and "ii = brnL cl n + i"
shows "n = locateT cl ii \<and> i = locateI cl ii"
using assms locate_unique[of cl brn] brn_gt_0
unfolding locateT_def locateI_def brnL_def
unfolding brnL_lsum[THEN sym] by auto

(*  pickFT picks a finished thread (if there is any).
    It will be used to perform a dummy transition in case the cumulated weight of the
    finished threads is 0; specifically, one will assign probability 1 to that picked fresh.
    (Obviously, the particular choice does not matter.)   *)
definition pickFT_pred where "pickFT_pred cl n \<equiv> n < length cl \<and> finished (cl!n)"
definition pickFT where "pickFT cl \<equiv> SOME n. pickFT_pred cl n"

lemma pickFT_pred:
assumes "WtFT cl = 1"  shows "\<exists> n. pickFT_pred cl n"
proof(rule ccontr, unfold not_ex)
  assume "\<forall>n. \<not> pickFT_pred cl n"
  hence "\<And> n. n < length cl \<Longrightarrow> \<not> finished (cl!n)"
  unfolding pickFT_pred_def by auto
  hence "theFT cl = {}" unfolding theFT_def by auto
  hence "WtFT cl = 0" unfolding WtFT_def by simp
  thus False using assms by simp
qed

lemma pickFT_pred_pickFT: "WtFT cl = 1 \<Longrightarrow> pickFT_pred cl (pickFT cl)"
unfolding pickFT_def by(auto intro: someI_ex pickFT_pred)

lemma pickFT_length[simp]: "WtFT cl = 1 \<Longrightarrow> pickFT cl < length cl"
using pickFT_pred_pickFT unfolding pickFT_pred_def by auto

lemma pickFT_finished[simp]: "WtFT cl = 1 \<Longrightarrow> finished (cl ! (pickFT cl))"
using pickFT_pred_pickFT unfolding pickFT_pred_def by auto

lemma pickFT_theFT[simp]: "WtFT cl = 1 \<Longrightarrow> pickFT cl \<in> theFT cl"
unfolding theFT_def by auto

(* The weight, continuation and effect defined as a single operator: *)
fun wt_cont_eff where
"wt_cont_eff Done s i = (1, Done, s)"
|
"wt_cont_eff (Atm atm) s i = (1, Done, aval atm s)"
|
"wt_cont_eff (c1 ;; c2) s i =
 (case wt_cont_eff c1 s i of
    (x, c1', s') \<Rightarrow>
      if finished c1' then (x, c2, s') else (x, c1' ;; c2, s'))"
|
"wt_cont_eff (While tst c) s i =
(if tval tst s
   then (1, c ;; (While tst c), s)
   else (1, Done, s))"
|
"wt_cont_eff (Ch ch c1 c2) s i =
 (if i = 0 then cval ch s else 1 - cval ch s,
  if i = 0 then c1 else c2,
  s)"
|
"wt_cont_eff (Par cl) s ii =
 (if cl ! (locateT cl ii) \<in> set cl then
 (case wt_cont_eff
         (cl ! (locateT cl ii))
         s
         (locateI cl ii) of
    (w, c', s') \<Rightarrow>
      ((1 / (length cl)) * w,
       Par (cl [(locateT cl ii) := c']),
       s'))
  else undefined)"
|
"wt_cont_eff (ParT cl) s ii =
 (if cl ! (locateT cl ii) \<in> set cl
   then
     (case wt_cont_eff
             (cl ! (locateT cl ii))
             s
             (locateI cl ii) of
        (w, c', s') \<Rightarrow>
           (if WtFT cl = 1
            then (if locateT cl ii = pickFT cl \<and> locateI cl ii = 0
                    then 1
                    else 0)
            else if finished (cl ! (locateT cl ii))
              then 0
              else (1 / (length cl))
                   / (1 - WtFT cl)
                   * w,
            ParT (cl [(locateT cl ii) := c']),
            s'))
   else undefined)"

(* weight, cont (transition) and effect: *)
definition wt where "wt c s i = fst (wt_cont_eff c s i)"
definition cont where "cont c s i = fst (snd (wt_cont_eff c s i))"
definition eff where "eff c s i = snd (snd (wt_cont_eff c s i))"

(* Their individual equations (corresponding to the paper's Figure 1):  *)
lemma wt_Done[simp]: "wt Done s i = 1"
unfolding wt_def by simp

lemma wt_Atm[simp]: "wt (Atm atm) s i = 1"
unfolding wt_def by simp

lemma wt_Seq[simp]:
"wt (c1 ;; c2) s = wt c1 s"
proof-
  {fix i have "wt (c1 ;; c2) s i = wt c1 s i"
   proof(cases "wt_cont_eff c1 s i")
     case (fields _ c1' _)
     thus ?thesis unfolding wt_def by(cases c1', auto)
   qed
  }
  thus ?thesis by auto
qed

lemma wt_While[simp]: "wt (While tst c) s i = 1"
unfolding wt_def by simp

lemma wt_Ch_L[simp]: "wt (Ch ch c1 c2) s 0 = cval ch s"
unfolding wt_def by simp

lemma wt_Ch_R[simp]: "wt (Ch ch c1 c2) s (Suc n) = 1 - cval ch s"
unfolding wt_def by simp

(*  *)
lemma cont_Done[simp]: "cont Done s i = Done"
unfolding cont_def by simp

lemma cont_Atm[simp]: "cont (Atm atm) s i = Done"
unfolding cont_def by simp

lemma cont_Seq_finished[simp]: "finished (cont c1 s i) \<Longrightarrow> cont (c1 ;; c2) s i = c2"
unfolding cont_def by(cases "wt_cont_eff c1 s i") auto

lemma cont_Seq_notFinished[simp]:
assumes "\<not> finished (cont c1 s i)"
shows "cont (c1 ;; c2) s i = (cont c1 s i) ;; c2"
proof(cases "wt_cont_eff c1 s i")
  case (fields _ c1' _)
  thus ?thesis using assms unfolding cont_def by(cases c1')  auto
qed

lemma cont_Seq_not_eq_finished[simp]: "\<not> finished c2 \<Longrightarrow> \<not> finished (cont (Seq c1 c2) s i)"
by (cases "finished (cont c1 s i)") auto

lemma cont_While_False[simp]: "tval tst s = False \<Longrightarrow> cont (While tst c) s i = Done"
unfolding cont_def by simp

lemma cont_While_True[simp]: "tval tst s = True \<Longrightarrow> cont (While tst c) s i = c ;; (While tst c)"
unfolding cont_def by simp

lemma cont_Ch_L[simp]: "cont (Ch ch c1 c2) s 0 = c1"
unfolding cont_def by simp

lemma cont_Ch_R[simp]: "cont (Ch ch c1 c2) s (Suc n) = c2"
unfolding cont_def by simp

(*  *)

lemma eff_Done[simp]: "eff Done s i = s"
unfolding eff_def by simp

lemma eff_Atm[simp]: "eff (Atm atm) s i = aval atm s"
unfolding eff_def by simp

lemma eff_Seq[simp]: "eff (c1 ;; c2) s = eff c1 s"
proof-
  {fix i have "eff (c1 ;; c2) s i = eff c1 s i"
   proof(cases "wt_cont_eff c1 s i")
     case (fields _ c1' _)
     thus ?thesis
     unfolding eff_def by(cases c1') auto
   qed
  }
  thus ?thesis by auto
qed

lemma eff_While[simp]: "eff (While tst c) s i = s"
unfolding eff_def by simp

lemma eff_Ch[simp]: "eff (Ch ch c1 c2) s i = s"
unfolding eff_def by simp

(* wt-cont-eff simps for parallel composition *)
lemma brnL_nchotomy:
assumes "properL cl" and "ii < brnL cl (length cl)"
shows "\<exists> n i. n < length cl \<and> i < brn (cl ! n) \<and> ii = brnL cl n + i"
unfolding brnL_def apply(rule less_lsum_nchotomy) using assms brn_gt_0
unfolding brnL_lsum[THEN sym] by auto

corollary brnL_cases[consumes 2, case_names Local, elim]:
assumes "properL cl" and "ii < brnL cl (length cl)" and
"\<And> n i. \<lbrakk>n < length cl; i < brn (cl ! n); ii = brnL cl n + i\<rbrakk> \<Longrightarrow> phi"
shows phi
using assms brnL_nchotomy by blast

lemma wt_cont_eff_Par[simp]:
assumes p: "properL cl"
and n: "n < length cl" and i: "i < brn (cl ! n)"
shows
"wt (Par cl) s (brnL cl n + i) =
 1 / (length cl) * wt (cl ! n) s i"
(is "?wL = ?wR")
(*  *)
"cont (Par cl) s (brnL cl n + i) =
 Par (cl [n := cont (cl ! n) s i])"
(is "?mL = ?mR")
(*  *)
"eff (Par cl) s (brnL cl n + i) =
 eff (cl ! n) s i"
(is "?eL = ?eR")
proof-
  define ii where "ii = brnL cl n + i"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have n_i: "n = n1" "i = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique n i by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using n i by simp
  hence "n1 < length cl"
  unfolding n1_def using i p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have "?wL = 1 / (length cl)* wt (cl ! n1) s i1"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using set unfolding n1_def i1_def unfolding wt_def by simp
  also have "... = ?wR" unfolding n_i by simp
  finally show "?wL = ?wR" .
  (*  *)
  have "?mL = Par (cl [n1 := cont (cl ! n1) s i1])"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using set unfolding n1_def i1_def unfolding cont_def by simp
  also have "... = ?mR" unfolding n_i by simp
  finally show "?mL = ?mR" .
  (*  *)
  have "?eL = eff (cl ! n1) s i1"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using set unfolding n1_def i1_def unfolding eff_def by simp
  also have "eff (cl ! n1) s i1 = ?eR" unfolding n_i by simp
  finally show "?eL = ?eR" .
qed

lemma cont_eff_ParT[simp]:
assumes p: "properL cl"
and n: "n < length cl" and i: "i < brn (cl ! n)"
shows
"cont (ParT cl) s (brnL cl n + i) =
 ParT (cl [n := cont (cl ! n) s i])"
(is "?mL = ?mR")
(*  *)
"eff (ParT cl) s (brnL cl n + i) =
 eff (cl ! n) s i"
(is "?eL = ?eR")
proof-
  define ii where "ii = brnL cl n + i"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have n_i: "n = n1" "i = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique n i by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using n i by simp
  hence "n1 < length cl"
  unfolding n1_def using i p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have "?mL = ParT (cl [n1 := cont (cl ! n1) s i1])"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using set unfolding n1_def i1_def unfolding cont_def by simp
  also have "... = ?mR" unfolding n_i by simp
  finally show "?mL = ?mR" .
  (*  *)
  have "?eL = eff (cl ! n1) s i1"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using set unfolding n1_def i1_def unfolding eff_def by simp
  also have "eff (cl ! n1) s i1 = ?eR" unfolding n_i by simp
  finally show "?eL = ?eR" .
qed

lemma wt_ParT_WtFT_pickFT_0[simp]:
assumes p: "properL cl" and WtFT: "WtFT cl = 1"
shows "wt (ParT cl) s (brnL cl (pickFT cl)) = 1"
(is "?wL = 1")
proof-
  define ii where "ii = brnL cl (pickFT cl)"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have ni: "pickFT cl < length cl" "0 < brn (cl! (pickFT cl))"
  using WtFT p brn_gt_0 by auto
  hence n_i: "pickFT cl = n1" "0 = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique[of cl "pickFT cl" 0 ii] by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using ni
  by (metis add.comm_neutral brn_index)
  hence "n1 < length cl"
  unfolding n1_def using ni p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have n1i1: "n1 = pickFT cl \<and> i1 = 0" using WtFT ni unfolding n_i by auto
  show "?wL = 1"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using WtFT n1i1 set unfolding n1_def i1_def unfolding wt_def by simp
qed

lemma wt_ParT_WtFT_notPickFT_0[simp]:
assumes p: "properL cl" and n: "n < length cl" and i: "i < brn (cl ! n)"
and WtFT: "WtFT cl = 1" and ni: "n = pickFT cl \<longrightarrow> i \<noteq> 0"
shows "wt (ParT cl) s (brnL cl n + i) = 0" (is "?wL = 0")
proof-
  define ii where "ii = brnL cl n + i"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have n_i: "n = n1" "i = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique n i by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using n i by simp
  hence "n1 < length cl"
  unfolding n1_def using i p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have n1i1: "n1 \<noteq> pickFT cl \<or> i1 \<noteq> 0" using WtFT ni unfolding n_i by auto
  show "?wL = 0"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using WtFT n1i1 set unfolding n1_def i1_def unfolding wt_def by force
qed

lemma wt_ParT_notWtFT_finished[simp]:
assumes p: "properL cl" and n: "n < length cl" and i: "i < brn (cl ! n)"
and WtFT: "WtFT cl \<noteq> 1" and f: "finished (cl ! n)"
shows "wt (ParT cl) s (brnL cl n + i) = 0" (is "?wL = 0")
proof-
  define ii where "ii = brnL cl n + i"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have n_i: "n = n1" "i = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique n i by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using n i by simp
  hence "n1 < length cl"
  unfolding n1_def using i p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have f: "finished (cl ! n1)" using f unfolding n_i by auto
  show "?wL = 0"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using WtFT f set unfolding n1_def i1_def unfolding wt_def by simp
qed

lemma wt_cont_eff_ParT_notWtFT_notFinished[simp]:
assumes p: "properL cl" and n: "n < length cl" and i: "i < brn (cl ! n)"
and WtFT: "WtFT cl \<noteq> 1" and nf: "\<not> finished (cl ! n)"
shows "wt (ParT cl) s (brnL cl n + i) =
       (1 / (length cl)) / (1 - WtFT cl) * wt (cl ! n) s i" (is "?wL = ?wR")
proof-
  define ii where "ii = brnL cl n + i"
  define n1 where "n1 = locateT cl ii"
  define i1 where "i1 = locateI cl ii"
  have n_i: "n = n1" "i = i1" using p unfolding n1_def i1_def
  using ii_def locateTI_unique n i by auto
  have lsum1: "ii < brnL cl (length cl)" unfolding ii_def using n i by simp
  hence "n1 < length cl" unfolding n1_def using i p locateTI[of cl ii] by simp
  hence set: "cl ! n1 \<in> set cl" by simp
  (*  *)
  have nf: "\<not> finished (cl ! n1)" using nf unfolding n_i by auto
  have "?wL = (1 / (length cl)) / (1 - WtFT cl) * wt (cl ! n1) s i1"
  unfolding ii_def[THEN sym]
  apply (cases "wt_cont_eff (cl ! n1) s i1")
  using WtFT nf set unfolding n1_def i1_def unfolding wt_def by simp
  also have "... = ?wR" unfolding n_i by simp
  finally show "?wL = ?wR" .
qed

(*  *)
lemma wt_ge_0[simp]:
assumes "proper c" and "i < brn c"
shows "0 \<le> wt c s i"
using assms proof (induct c arbitrary: i s rule: proper_induct)
  case (Ch ch c1 c2)
  thus ?case
  using properCh  by (cases i) (auto simp: algebra_simps)
next
  case (Par cl ii)
  have "properL cl" and "ii < brnL cl (length cl)" using Par by auto
  thus ?case
  apply (cases rule: brnL_cases)
  using Par by simp
next
  case (ParT cl ii)
  have "properL cl" and "ii < brnL cl (length cl)" using ParT by auto
  thus ?case
  proof(cases rule: brnL_cases)
    case (Local n i)
    show ?thesis
    proof (cases "WtFT cl = 1")
      case True
      thus ?thesis using Local ParT by (cases "n = pickFT cl \<and> i = 0") auto
    next
      case False
      thus ?thesis using Local ParT by (cases "finished (cl ! n)") auto
    qed
  qed
qed auto

lemma wt_le_1[simp]:
assumes "proper c" and "i < brn c"
shows "wt c s i \<le> 1"
using assms proof (induct c arbitrary: i s rule: proper_induct)
  case (Ch ch c1 c2)
  thus ?case
  using properCh by (cases i) auto
next
  case (Par cl ii)
  hence "properL cl" and "ii < brnL cl (length cl)" by auto
  thus ?case
  apply (cases rule: brnL_cases) apply simp
  using Par apply auto
  by (metis add_increasing2 diff_is_0_eq gr0_conv_Suc less_imp_diff_less less_or_eq_imp_le nth_mem of_nat_0_le_iff of_nat_Suc)
next
  case (ParT cl ii)
  have "properL cl" and "ii < brnL cl (length cl)" using ParT by auto
  thus ?case
  proof(cases rule: brnL_cases)
    case (Local n i)
    show ?thesis
    proof (cases "WtFT cl = 1")
      case True
      thus ?thesis using Local ParT by (cases "n = pickFT cl \<and> i = 0", auto)
    next
      case False note sch = False
      thus ?thesis using Local ParT proof (cases "finished (cl ! n)")
        case False note cln = False
        let ?L1 = "1 / (length cl)" let ?L2 = "wt (cl ! n) s i"
        let ?R = "WtFT cl"
        have "0 \<le> ?L1" and "0 \<le> ?L2" using ParT Local by auto
        moreover have "?L2 \<le> 1" using ParT Local by auto
        ultimately have "?L1 * ?L2 \<le> ?L1" by (metis mult_right_le_one_le)
        also have "?L1 \<le> 1 - ?R" using ParT Local cln by auto
        finally have "?L1 * ?L2 \<le> 1 - ?R" .
        thus ?thesis using Local ParT cln sch
          by (auto simp: pos_divide_le_eq mult.commute)
      qed (insert sch ParT Local, auto)
    qed
  qed
qed auto

abbreviation fromPlus ("(1{_..<+_})") where
"{a ..<+ b} \<equiv> {a ..< a + b}"

lemma brnL_UN:
assumes "properL cl"
shows "{..< brnL cl (length cl)} = (\<Union> n < length cl. {brnL cl n ..<+ brn (cl!n)})"
(is "?L = (\<Union> n < length cl. ?R n)")
proof safe
  fix ii assume ii: "ii < brnL cl (length cl)"
  from assms ii show "ii \<in> (\<Union> n < length cl. ?R n)"
  proof(cases rule: brnL_cases)
    case (Local n i)
    hence "ii \<in> ?R n" by simp
    thus ?thesis using Local by force
  qed
qed auto

lemma brnL_Int_lt:
assumes n12: "n1 < n2" and n2: "n2 < length cl"
shows
"{brnL cl n1 ..<+ brn (cl!n1)} \<inter> {brnL cl n2 ..<+ brn (cl!n2)} = {}"
proof-
  have "Suc n1 \<le> n2" using assms by simp
  hence "brnL cl (Suc n1) \<le> brnL cl n2" by simp
  thus ?thesis using assms by simp
qed

lemma brnL_Int:
assumes "n1 \<noteq> n2" and "n1 < length cl" and "n2 < length cl"
shows "{brnL cl n1 ..<+ brn (cl!n1)} \<inter> {brnL cl n2 ..<+ brn (cl!n2)} = {}"
proof(cases "n1 < n2")
  case True thus ?thesis using assms brnL_Int_lt by auto
next
  case False
  hence "n2 < n1" using assms by simp
  thus ?thesis using brnL_Int_lt assms by fastforce
qed

lemma sum_wt_Par_sub[simp]:
assumes cl: "properL cl" and n: "n < length cl" and I: "I \<subseteq> {..< brn (cl ! n)}"
shows "sum (wt (Par cl) s) ((+) (brnL cl n) ` I) =
       1 /(length cl) * sum (wt (cl ! n) s) I" (is "?L = ?wSch * ?R")
proof-
  have "?L = sum (%i. ?wSch * wt (cl ! n) s i) I"
  apply(rule sum.reindex_cong[of "(+) (brnL cl n)"]) using assms by auto
  also have "... = ?wSch * ?R"
  unfolding sum_distrib_left by simp
  finally show ?thesis .
qed

lemma sum_wt_Par[simp]:
assumes cl: "properL cl" and n: "n < length cl"
shows "sum (wt (Par cl) s) {brnL cl n ..<+ brn (cl!n)} =
       1 /(length cl) * sum (wt (cl ! n) s) {..< brn (cl ! n)}" (is "?L = ?W * ?R")
using assms by (simp add: sum_distrib_left)

lemma sum_wt_ParT_sub_WtFT_pickFT_0[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1"
and I: "I \<subseteq> {..< brn (cl ! (pickFT cl))}" "0 \<in> I"
shows "sum (wt (ParT cl) s) ((+) (brnL cl (pickFT cl)) ` I) = 1" (is "?L = 1")
proof-
  let ?n = "pickFT cl"
  let ?w = "%i. if i = 0 then (1::real) else 0"
  have n: "?n < length cl" using nf by simp
  have 0: "I = {0} Un (I - {0})" using I by auto
  have finI: "finite I" using I by (metis finite_nat_iff_bounded)
  have "?L = sum ?w I"
  proof (rule sum.reindex_cong [of "plus (brnL cl ?n)"])
    fix i assume i: "i \<in> I"
    have "i < brn (cl ! ?n)" using i I by auto
    note i = this i
    show "wt (ParT cl) s (brnL cl ?n + i) = ?w i"
    using nf n i cl by (cases "i = 0") auto
  qed (insert assms, auto)
  also have "... = sum ?w ({0} Un (I - {0}))" using 0 by auto
  also have "... = sum ?w {0::real} + sum ?w (I - {0})"
  using sum.union_disjoint[of "{0}" "I - {0}" ?w] finI by auto
  also have "... = 1" by simp
  finally show ?thesis .
qed

lemma sum_wt_ParT_sub_WtFT_pickFT_0_2[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1"
and II: "II \<subseteq> {..< brnL cl (length cl)}" "brnL cl (pickFT cl) \<in> II"
shows "sum (wt (ParT cl) s) II = 1" (is "?L = 1")
proof-
  let ?n = "pickFT cl"
  let ?w = "%ii. if ii = brnL cl (pickFT cl) then (1::real) else 0"
  have n: "?n < length cl" using nf by simp
  have 0: "II = {brnL cl ?n} Un (II - {brnL cl ?n})" using II by auto
  have finI: "finite II" using II by (metis finite_nat_iff_bounded)
  have "?L = sum ?w II"
  proof(rule sum.cong)
    fix ii assume ii: "ii \<in> II"
    hence ii: "ii < brnL cl (length cl)" using II by auto
    from cl ii show "wt (ParT cl) s ii = ?w ii"
    proof(cases rule: brnL_cases)
      case (Local n i)
      show ?thesis
      proof(cases "ii = brnL cl (pickFT cl)")
        case True
        have "n = pickFT cl \<and> i = 0"
        apply(intro brnL_unique[of cl]) using Local cl nf brn_gt_0 unfolding True by auto
        thus ?thesis using cl nf True by simp
      next
        case False
        hence "n = pickFT cl \<longrightarrow> i \<noteq> 0" unfolding Local by auto
        thus ?thesis using Local ii nf cl False by auto
      qed
    qed
  qed simp
  also have "... = sum ?w ({brnL cl ?n} Un (II - {brnL cl ?n}))" using 0 by simp
  also have "... = sum ?w {brnL cl ?n} + sum ?w (II - {brnL cl ?n})"
  apply(rule sum.union_disjoint) using finI by auto
  also have "... = 1" by simp
  finally show ?thesis .
qed

lemma sum_wt_ParT_sub_WtFT_notPickFT_0[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1" and n: "n < length cl"
and I: "I \<subseteq> {..< brn (cl ! n)}" and nI: "n = pickFT cl \<longrightarrow> 0 \<notin> I"
shows "sum (wt (ParT cl) s) ((+) (brnL cl n) ` I) = 0" (is "?L = 0")
proof-
  have "?L = sum (%i. 0) I"
  proof (rule sum.reindex_cong [of "plus (brnL cl n)"])
    fix i assume i: "i \<in> I"
    hence "n = pickFT cl \<longrightarrow> i \<noteq> 0" using nI by metis
    moreover have "i < brn (cl ! n)" using i I by auto
    ultimately show "wt (ParT cl) s (brnL cl n + i) = 0"
    using nf n cl by simp
  qed (insert assms, auto)
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma sum_wt_ParT_sub_notWtFT_finished[simp]:
assumes cl: "properL cl" and nf: "WtFT cl \<noteq> 1"
and n: "n < length cl" and cln: "finished (cl!n)" and I: "I \<subseteq> {..< brn (cl ! n)}"
shows "sum (wt (ParT cl) s) ((+) (brnL cl n) ` I) = 0" (is "?L = 0")
proof-
  have "?L = sum (%i. 0) I"
  apply(rule sum.reindex_cong[of "(+) (brnL cl n)"]) using assms by auto
  also have "... = 0" by simp
  finally show ?thesis .
qed

lemma sum_wt_ParT_sub_notWtFT_notFinished[simp]:
assumes cl: "properL cl" and nf: "WtFT cl \<noteq> 1" and n: "n < length cl"
and cln: "\<not> finished (cl!n)" and I: "I \<subseteq> {..< brn (cl ! n)}"
shows
"sum (wt (ParT cl) s) ((+) (brnL cl n) ` I) =
 (1 / (length cl)) / (1 - WtFT cl) * sum (wt (cl ! n) s) I"
(is "?L = ?w / (1 - ?wF) * ?R")
proof-
  have "?L = sum (%i. ?w / (1 - ?wF) * wt (cl ! n) s i) I"
  apply(rule sum.reindex_cong[of "(+) (brnL cl n)"])
  using assms by auto
  also have "... = ?w / (1 - ?wF) * ?R"
  unfolding sum_distrib_left by simp
  finally show ?thesis .
qed

lemma sum_wt_ParT_WtFT_pickFT_0[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1"
shows "sum (wt (ParT cl) s) {brnL cl (pickFT cl) ..<+ brn (cl ! (pickFT cl))} = 1"
proof-
  let ?n = "pickFT cl"
  have 1: "{brnL cl ?n ..<+ brn (cl ! ?n)} =
  (+) (brnL cl ?n) ` {..< brn (cl ! ?n)}" by simp
  show ?thesis unfolding 1
  apply(rule sum_wt_ParT_sub_WtFT_pickFT_0)
  using assms apply simp_all
  by (metis brn_gt_0_L nth_mem pickFT_length)
qed

lemma sum_wt_ParT_WtFT_notPickFT_0[simp]:
assumes cl: "properL cl" and nf: "WtFT cl = 1" and n: "n < length cl" "n \<noteq> pickFT cl"
shows "sum (wt (ParT cl) s) {brnL cl n ..<+ brn (cl!n)} = 0"
proof-
  have 1: "{brnL cl n ..<+ brn (cl!n)} = (+) (brnL cl n) ` {..< brn (cl!n)}" by simp
  show ?thesis unfolding 1 apply(rule sum_wt_ParT_sub_WtFT_notPickFT_0) using assms by auto
qed

lemma sum_wt_ParT_notWtFT_finished[simp]:
assumes cl: "properL cl" and "WtFT cl \<noteq> 1"
and n: "n < length cl" and cln: "finished (cl!n)"
shows "sum (wt (ParT cl) s) {brnL cl n ..<+ brn (cl!n)} = 0"
proof-
  have 1: "{brnL cl n ..<+ brn (cl!n)} = (+) (brnL cl n) ` {..< brn (cl!n)}" by simp
  show ?thesis unfolding 1
  apply(rule sum_wt_ParT_sub_notWtFT_finished) using assms by auto
qed

lemma sum_wt_ParT_notWtFT_notFinished[simp]:
assumes cl: "properL cl" and nf: "WtFT cl \<noteq> 1"
and n: "n < length cl" and cln: "\<not> finished (cl!n)"
shows
"sum (wt (ParT cl) s) {brnL cl n ..<+ brn (cl!n)} =
 (1 / (length cl)) / (1 - WtFT cl) *
 sum (wt (cl ! n) s) {..< brn (cl ! n)}"
proof-
  have 1: "{brnL cl n ..<+ brn (cl!n)} = (+) (brnL cl n) ` {..< brn (cl!n)}" by simp
  show ?thesis unfolding 1 apply(rule sum_wt_ParT_sub_notWtFT_notFinished) using assms by auto
qed

lemma sum_wt[simp]:
assumes "proper c"
shows "sum (wt c s) {..< brn c} = 1"
using assms proof (induct c arbitrary: s rule: proper_induct)
  case (Par cl)
  let ?w = "\<lambda> n. 1 / (length cl) * sum (wt (cl ! n) s) {..< brn (cl ! n)}"
  show ?case
  proof (rule sum_UN_introL [of _ "%n. {brnL cl n ..<+ brn (cl!n)}" "{..< length cl}" _ ?w])
    have "1 = sum (\<lambda> n. 1 / (length cl)) {..< length cl}"
    using Par by simp
    also have "... = sum ?w {..< length cl}" using Par by simp
    finally show "1 = sum ?w {..< length cl}" .
  next
    fix m n assume "{m, n} \<subseteq> {..<length cl} \<and> m \<noteq> n"
    thus
    "{brnL cl m ..<+ brn (cl!m)} \<inter> {brnL cl n ..<+ brn (cl!n)} = {}"
    using brnL_Int by auto
  qed(insert Par brnL_UN sum_wt_Par, auto)
next
  case (ParT cl)
  let ?v = "1/(length cl)" let ?wtF = "WtFT cl" let ?wtNF = "WtNFT cl"
  let ?w = "\<lambda>n.
  if ?wtF = 1
    then
      (if n = pickFT cl then 1 else 0)
    else
      (if finished (cl!n)
         then 0
         else ?v / (1 - ?wtF) *
              sum (wt (cl ! n) s) {..< brn (cl ! n)})"
  define w where "w = ?w"
  have w: "\<And> n. ?wtF \<noteq> 1 \<and> n < length cl \<and> \<not> finished (cl!n)
  \<Longrightarrow> w n = ?v / (1 - ?wtF)"
  unfolding w_def using ParT by simp
  show ?case
  proof(cases "WtFT cl = 1")
    case True
    with ParT show ?thesis by simp
  next
    case False note nf = False
    show ?thesis
    proof (rule sum_UN_introL [of _ "%n. {brnL cl n ..<+ brn (cl!n)}" "{..< length cl}" _ w])
      show "1 = sum w {..< length cl}"
      proof(cases "?wtF = 1")
        case True note sch = True
        let ?n = "pickFT cl"
        let ?L = "{?n}" let ?Lnot = "{..<length cl} - {?n}"
        have "?n < length cl" using ParT True by auto
        hence "{..< length cl} = ?L Un ?Lnot" by auto
        hence "sum w {..< length cl} = sum w (?L Un ?Lnot)" by simp
        also have "... = sum w ?L + sum w ?Lnot"
        apply(rule sum.union_disjoint) by auto
        also have "... = 1" unfolding w_def using sch by simp
        finally show ?thesis by simp
      next
        case False note sch = False
        let ?L = "theFT cl" let ?Lnot = "theNFT cl"
        have 1: "{..< length cl} = ?L Un ?Lnot" by auto
        have "sum w {..< length cl} = sum w ?L + sum w ?Lnot"
        unfolding 1 apply(rule sum.union_disjoint) by auto
        also have "... = sum w ?Lnot" unfolding w_def using sch by simp
        also have "... = sum (%n. ?v / (1 - ?wtF)) ?Lnot"
        apply(rule sum.cong) using w sch by auto
        also have "... = sum (%n. ?v) ?Lnot / (1 - ?wtF)"
        unfolding sum_divide_distrib by simp
        also have "... = ?wtNF / (1 - ?wtF)" unfolding WtNFT_def by simp
        also have "... = 1" using nf ParT by simp
        finally show ?thesis by simp
      qed
    next
      fix n assume n: "n \<in> {..<length cl}"
      show "sum (wt (ParT cl) s) {brnL cl n..<+brn (cl ! n)} = w n"
      proof-
        have "(\<Sum>i<brn (cl ! n). ?v * wt (cl ! n) s i / (1 - ?wtF)) =
        ?v * (\<Sum>i<brn (cl ! n). wt (cl ! n) s i) / (1 - ?wtF)"
        unfolding sum_distrib_left sum_divide_distrib by simp
        also have "... = ?v / (1 - ?wtF)" using ParT n by simp
        finally have "(\<Sum>i<brn (cl ! n). ?v * wt (cl ! n) s i / (1 - ?wtF)) =
        ?v / (1 - ?wtF)" .
        thus ?thesis unfolding w_def using n nf ParT by simp
      qed
    qed(insert ParT brnL_UN brnL_Int sum_wt_Par, auto)
  qed
qed auto

lemma proper_cont[simp]:
assumes "proper c" and "i < brn c"
shows "proper (cont c s i)"
using assms proof(induct c arbitrary: i s rule: cmd.induct)
  case (Ch ch c1 c2)
  thus ?case by (cases i) auto
next
  case (Seq c1 c2) thus ?case
  by (cases "finished (cont c1 s i)") auto
next
  case (While tst c) thus ?case
  by (cases "tval tst s") auto
next
  case (Par cl ii)
  hence "properL cl" and "ii < brnL cl (length cl)" by auto
  thus ?case
  using Par by (cases rule: brnL_cases) auto
next
  case (ParT cl ii)
  have "properL cl" and "ii < brnL cl (length cl)" using ParT by auto
  thus ?case apply (cases rule: brnL_cases) using ParT by auto
qed auto

lemma sum_subset_le_1[simp]:
assumes *: "proper c" and **: "I \<subseteq> {..< brn c}"
shows "sum (wt c s) I \<le> 1"
proof-
  define J where "J = {..< brn c}"
  have "I \<subseteq> J" and "finite J" using ** unfolding J_def by auto
  moreover have "\<forall> j \<in> J. wt c s j \<ge> 0" unfolding J_def using * by simp
  ultimately have "sum (wt c s) I \<le> sum (wt c s) J"
  using sum_mono2[of J I "wt c s"] by auto
  also have "... = 1" using * unfolding J_def by simp
  finally show "sum (wt c s) I \<le> 1" unfolding J_def by simp
qed

lemma sum_le_1[simp]:
assumes *: "proper c" and **: "i < brn c"
shows "sum (wt c s) {..i} \<le> 1"
proof-
  have "{..i} \<subseteq> {..< brn c}" using ** by auto
  thus ?thesis using assms sum_subset_le_1[of c "{..i}" s] by blast
qed


subsubsection \<open>Operations on configurations\<close>

definition "cont_eff cf b = snd (wt_cont_eff (fst cf) (snd cf) b)"

lemma cont_eff: "cont_eff cf b = (cont (fst cf) (snd cf) b, eff (fst cf) (snd cf) b)"
unfolding cont_eff_def cont_def eff_def by simp

end (* context PL *)


end
