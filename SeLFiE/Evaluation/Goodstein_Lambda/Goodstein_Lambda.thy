section \<open>Specification\<close>

theory Goodstein_Lambda
  imports Main
begin

subsection \<open>Hereditary base representation\<close>

text \<open>We define a data type of trees and an evaluation function that sums siblings and
  exponentiates with respect to the given base on nesting.\<close>

datatype C = C (unC: "C list")

fun evalC where
  "evalC b (C []) = 0"
| "evalC b (C (x # xs)) = b^evalC b x + evalC b (C xs)"

value "evalC 2 (C [])" \<comment> \<open>$0$\<close>
value "evalC 2 (C [C []])" \<comment> \<open>$2^0 = 1$\<close>
value "evalC 2 (C [C [C []]])" \<comment> \<open>$2^1 = 2$\<close>
value "evalC 2 (C [C [], C []])" \<comment> \<open>$2^0 + 2^0 = 2^0 \cdot 2 = 2$; not in hereditary base $2$\<close>

text \<open>The hereditary base representation is characterized as trees (i.e., nested lists) whose
  lists have monotonically increasing evaluations, with fewer than @{term "b"} repetitions for
  each value. We will show later that this representation is unique.\<close>

inductive_set hbase for b where
  "C [] \<in> hbase b"
| "i \<noteq> 0 \<Longrightarrow> i < b \<Longrightarrow> n \<in> hbase b \<Longrightarrow>
   C ms \<in> hbase b \<Longrightarrow> (\<And>m'. m' \<in> set ms \<Longrightarrow> evalC b n < evalC b m') \<Longrightarrow>
   C (replicate i n @ ms) \<in> hbase b"

text \<open>We can convert to and from natural numbers as follows.\<close>

definition H2N where
  "H2N b n = evalC b n"

text \<open>As we will show later, @{term "H2N b"} restricted to @{term "hbase n"} is bijective
  if @{prop "b \<ge> (2 :: nat)"}, so we can convert from natural numbers by taking the inverse.\<close>

definition N2H where
  "N2H b n = inv_into (hbase b) (H2N b) n"

subsection \<open>The Goodstein function\<close>

text \<open>We define a function that computes the length of the Goodstein sequence whose $c$-th element
  is $g_c = n$. Termination will be shown later, thereby establishing Goodstein's theorem.\<close>

function (sequential) goodstein :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "goodstein 0 n = 0"
  \<comment> \<open>we start counting at 1; also note that the initial base is @{term "c+1 :: nat"} and\<close>
  \<comment> \<open>hereditary base 1 makes no sense, so we have to avoid this case\<close>
| "goodstein c 0 = c"
| "goodstein c n = goodstein (c+1) (H2N (c+2) (N2H (c+1) n) - 1)"
  by pat_completeness auto

abbreviation \<G> where
  "\<G> n \<equiv> goodstein (Suc 0) n"

section \<open>Ordinals\<close>

text \<open>The following type contains countable ordinals, by the usual case distinction into 0,
  successor ordinal, or limit ordinal; limit ordinals are given by their fundamental sequence.
  Hereditary base @{term "b"} representations carry over to such ordinals by replacing each
  occurrence of the base by @{term "\<omega>"}.\<close>

datatype Ord = Z | S Ord | L "nat \<Rightarrow> Ord"

text \<open>Note that the following arithmetic operations are not correct for all ordinals. However, they
  will only be used in cases where they actually correspond to the ordinal arithmetic operations.\<close>

primrec addO where
  "addO n Z = n"
| "addO n (S m) = S (addO n m)"
| "addO n (L f) = L (\<lambda>i. addO n (f i))"

primrec mulO where
  "mulO n Z = Z"
| "mulO n (S m) = addO (mulO n m) n"
| "mulO n (L f) = L (\<lambda>i. mulO n (f i))"

definition \<omega> where
  "\<omega> = L (\<lambda>n. (S ^^ n) Z)"

primrec exp\<omega> where
  "exp\<omega> Z = S Z"
| "exp\<omega> (S n) = mulO (exp\<omega> n) \<omega>"
| "exp\<omega> (L f) = L (\<lambda>i. exp\<omega> (f i))"

subsection \<open>Evaluation\<close>

text \<open>Evaluating an ordinal number at base $b$ is accomplished by taking the $b$-th element of
  all fundamental sequences and interpreting zero and successor over the natural numbers.\<close>

primrec evalO where
  "evalO b Z = 0"
| "evalO b (S n) = Suc (evalO b n)"
| "evalO b (L f) = evalO b (f b)"

subsection \<open>Goodstein function and sequence\<close>

text \<open>We can define the Goodstein function very easily, but proving correctness will take a while.\<close>

primrec goodsteinO where
  "goodsteinO c Z = c"
| "goodsteinO c (S n) = goodsteinO (c+1) n"
| "goodsteinO c (L f) = goodsteinO c (f (c+2))"

primrec stepO where
  "stepO c Z = Z"
| "stepO c (S n) = n"
| "stepO c (L f) = stepO c (f (c+2))"

text \<open>We can compute a few values of the Goodstein sequence starting at $4$.\<close>

definition g4O where
  "g4O n = fold stepO [1..<Suc n] ((exp\<omega> ^^ 3) Z)"

value "map (\<lambda>n. evalO (n+2) (g4O n)) [0..<10]"
\<comment> \<open>@{value "[4, 26, 41, 60, 83, 109, 139, 173, 211, 253] :: nat list"}\<close>

subsection \<open>Properties of evaluation\<close>

lemma evalO_addO [simp]:
  "evalO b (addO n m) = evalO b n + evalO b m"
  by (induct m) auto

lemma evalO_mulO [simp]:
  "evalO b (mulO n m) = evalO b n * evalO b m"
  by (induct m) auto

lemma evalO_n [simp]:
  "evalO b ((S ^^ n) Z) = n"
  by (induct n) auto

lemma evalO_\<omega> [simp]:
  "evalO b \<omega> = b"
  by (auto simp: \<omega>_def)

lemma evalO_exp\<omega> [simp]:
  "evalO b (exp\<omega> n) = b^(evalO b n)"
  by (induct n) auto

text \<open>Note that evaluation is useful for proving that @{type "Ord"} values are distinct:\<close>
notepad begin
  have "addO n (exp\<omega> m) \<noteq> n" for n m by (auto dest: arg_cong[of _ _ "evalO 1"])
end

subsection \<open>Arithmetic properties\<close>

lemma addO_Z [simp]:
  "addO Z n = n"
  by (induct n) auto

lemma addO_assoc [simp]:
  "addO n (addO m p) = addO (addO n m) p"
  by (induct p) auto

lemma mul0_distrib [simp]:
  "mulO n (addO p q) = addO (mulO n p) (mulO n q)"
  by (induct q) auto

lemma mulO_assoc [simp]:
  "mulO n (mulO m p) = mulO (mulO n m) p"
  by (induct p) auto

lemma exp\<omega>_addO [simp]:
  "exp\<omega> (addO n m) = mulO (exp\<omega> n) (exp\<omega> m)"
  by (induct m) auto


section \<open>Cantor normal form\<close>

text \<open>The previously introduced tree type @{type C} can be used to represent Cantor normal forms;
  they are trees (evaluated at base @{term \<omega>}) such that siblings are in non-decreasing order.
  One can think of this as hereditary base @{term \<omega>}. The plan is to mirror selected operations on
  ordinals in Cantor normal forms.\<close>

subsection \<open>Conversion to and from the ordinal type @{type Ord}\<close>

fun C2O where
  "C2O (C []) = Z"
| "C2O (C (n # ns)) = addO (C2O (C ns)) (exp\<omega> (C2O n))"

definition O2C where
  "O2C = inv C2O"

text \<open>We show that @{term C2O} is injective, meaning the inverse is unique.\<close>

lemma addO_exp\<omega>_inj:
  assumes "addO n (exp\<omega> m) = addO n' (exp\<omega> m')"
  shows "n = n'" and "m = m'"
proof -
  have "addO n (exp\<omega> m) = addO n' (exp\<omega> m') \<Longrightarrow> n = n'"
    by (induct m arbitrary: m'; case_tac m';
      force simp: \<omega>_def dest!: fun_cong[of _ _ 1])
  moreover have "addO n (exp\<omega> m) = addO n (exp\<omega> m') \<Longrightarrow> m = m'"
    apply (induct m arbitrary: n m'; case_tac m')
    apply (auto 0 3 simp: \<omega>_def intro: rangeI
      dest: arg_cong[of _ _ "evalO 1"] fun_cong[of _ _ 0] fun_cong[of _ _ 1])[8] (* 1 left *)
    by simp (meson ext rangeI)
  ultimately show "n = n'" and "m = m'" using assms by simp_all
qed

lemma C2O_inj:
  "C2O n = C2O m \<Longrightarrow> n = m"
  by (induct n arbitrary: m rule: C2O.induct; case_tac m rule: C2O.cases)
    (auto dest: addO_exp\<omega>_inj arg_cong[of _ _ "evalO 1"])

lemma O2C_C2O [simp]:
  "O2C (C2O n) = n"
  by (auto intro!: inv_f_f simp: O2C_def inj_def C2O_inj)

lemma O2C_Z [simp]:
  "O2C Z = C []"
  using O2C_C2O[of "C []", unfolded C2O.simps] .

lemma C2O_replicate:
  "C2O (C (replicate i n)) = mulO (exp\<omega> (C2O n)) ((S ^^ i) Z)"
  by (induct i) auto

lemma C2O_app:
  "C2O (C (xs @ ys)) = addO (C2O (C ys)) (C2O (C xs))"
  by (induct xs arbitrary: ys) auto

subsection \<open>Evaluation\<close>

lemma evalC_def':
  "evalC b n = evalO b (C2O n)"
  by (induct n rule: C2O.induct) auto

lemma evalC_app [simp]:
  "evalC b (C (ns @ ms)) = evalC b (C ns) + evalC b (C ms)"
  by (induct ns) auto

lemma evalC_replicate [simp]:
  "evalC b (C (replicate c n)) = c * evalC b (C [n])"
  by (induct c) auto

subsection \<open>Transfer of the @{type Ord} induction principle to @{type C}\<close>

fun funC where \<comment> \<open>@{term funC} computes the fundamental sequence on @{type C}\<close>
  "funC (C []) = (\<lambda>i. [C []])"
| "funC (C (C [] # ns)) = (\<lambda>i. replicate i (C ns))"
| "funC (C (n # ns)) = (\<lambda>i. [C (funC n i @ ns)])"

lemma C2O_cons:
  "C2O (C (n # ns)) =
    (if n = C [] then S (C2O (C ns)) else L (\<lambda>i. C2O (C (funC n i @ ns))))"
  by (induct n arbitrary: ns rule: funC.induct)
    (simp_all add: \<omega>_def C2O_replicate C2O_app flip: exp\<omega>_addO)

lemma C_Ord_induct:
  assumes "P (C [])"
  and "\<And>ns. P (C ns) \<Longrightarrow> P (C (C [] # ns))"
  and "\<And>n ns ms. (\<And>i. P (C (funC (C (n # ns)) i @ ms))) \<Longrightarrow>
    P (C (C (n # ns) # ms))"
  shows "P n"
proof -
  have "\<forall>n. C2O n = m \<longrightarrow> P n" for m
    by (induct m; intro allI; case_tac n rule: funC.cases)
      (auto simp: C2O_cons simp del: C2O.simps(2) intro: assms)
  then show ?thesis by simp
qed

subsection \<open>Goodstein function and sequence on @{type C}\<close>

function (domintros) goodsteinC where
  "goodsteinC c (C []) = c"
| "goodsteinC c (C (C [] # ns)) = goodsteinC (c+1) (C ns)"
| "goodsteinC c (C (C (n # ns) # ms)) =
    goodsteinC c (C (funC (C (n # ns)) (c+2) @ ms))"
  by pat_completeness auto

termination
proof -
  have "goodsteinC_dom (c, n)" for c n
    by (induct n arbitrary: c rule: C_Ord_induct) (auto intro: goodsteinC.domintros)
  then show ?thesis by simp
qed

lemma goodsteinC_def':
  "goodsteinC c n = goodsteinO c (C2O n)"
  by (induct c n rule: goodsteinC.induct) (simp_all add: C2O_cons del: C2O.simps(2))

function (domintros) stepC where
  "stepC c (C []) = C []"
| "stepC c (C (C [] # ns)) = C ns"
| "stepC c (C (C (n # ns) # ms)) =
    stepC c (C (funC (C (n # ns)) (Suc (Suc c)) @ ms))"
  by pat_completeness auto

termination
proof -
  have "stepC_dom (c, n)" for c n
    by (induct n arbitrary: c rule: C_Ord_induct) (auto intro: stepC.domintros)
  then show ?thesis by simp
qed

definition g4C where
  "g4C n = fold stepC [1..<Suc n] (C [C [C [C []]]])"

value "map (\<lambda>n. evalC (n+2) (g4C n)) [0..<10]"
\<comment> \<open>@{value "[4, 26, 41, 60, 83, 109, 139, 173, 211, 253] :: nat list"}\<close>

subsection \<open>Properties\<close>

lemma stepC_def':
  "stepC c n = O2C (stepO c (C2O n))"
  by (induct c n rule: stepC.induct) (simp_all add: C2O_cons del: C2O.simps(2))

lemma funC_ne [simp]:
  "funC m (Suc n) \<noteq> []"
  by (cases m rule: funC.cases) simp_all

lemma evalC_funC [simp]:
  "evalC b (C (funC n b)) = evalC b (C [n])"
  by (induct n rule: funC.induct) simp_all

lemma stepC_app [simp]:
  "n \<noteq> C [] \<Longrightarrow> stepC c (C (unC n @ ns)) = C (unC (stepC c n) @ ns)"
  by (induct n arbitrary: ns rule: stepC.induct) simp_all

lemma stepC_cons [simp]:
  "ns \<noteq> [] \<Longrightarrow> stepC c (C (n # ns)) = C (unC (stepC c (C [n])) @ ns)"
  using stepC_app[of "C[n]" c ns] by simp

lemma stepC_dec:
  "n \<noteq> C [] \<Longrightarrow> Suc (evalC (Suc (Suc c)) (stepC c n)) = evalC (Suc (Suc c)) n"
  by (induct c n rule: stepC.induct) simp_all

lemma stepC_dec':
  "n \<noteq> C [] \<Longrightarrow> evalC (c+3) (stepC c n) < evalC (c+3) n"
proof (induct c n rule: stepC.induct)
  case (3 c n ns ms)
  have "evalC (c+3) (C (funC (C (n # ns)) (Suc (Suc c)))) \<le>
      (c+3) ^ ((c+3) ^ evalC (c+3) n + evalC (c+3) (C ns))"
    by (induct n rule: funC.induct) (simp_all add: distrib_right)
  then show ?case using 3 by simp
qed simp_all


section \<open>Hereditary base @{term b} representation\<close>

text \<open>We now turn to properties of the @{term "hbase b"} subset of trees.\<close>

subsection \<open>Uniqueness\<close>

text \<open>We show uniqueness of the hereditary base representation by showing that @{term "evalC b"}
  restricted to @{term "hbase b"} is injective.\<close>

lemma hbaseI2:
  "i < b \<Longrightarrow> n \<in> hbase b \<Longrightarrow> C m \<in> hbase b \<Longrightarrow>
    (\<And>m'. m' \<in> set m \<Longrightarrow> evalC b n < evalC b m') \<Longrightarrow>
    C (replicate i n @ m) \<in> hbase b"
  by (cases i) (auto intro: hbase.intros simp del: replicate.simps(2))

lemmas hbase_singletonI =
  hbase.intros(2)[of 1 "Suc (Suc b)" for b, OF _ _ _ hbase.intros(1), simplified]

lemma hbase_hd:
  "C ns \<in> hbase b \<Longrightarrow> ns \<noteq> [] \<Longrightarrow> hd ns \<in> hbase b"
  by (cases rule: hbase.cases) auto

lemmas hbase_hd' [dest] = hbase_hd[of "n # ns" for n ns, simplified]

lemma hbase_tl:
  "C ns \<in> hbase b \<Longrightarrow> ns \<noteq> [] \<Longrightarrow> C (tl ns) \<in> hbase b"
  by (cases "C ns" b rule: hbase.cases) (auto intro: hbaseI2)

lemmas hbase_tl' [dest] = hbase_tl[of "n # ns" for n ns, simplified]

lemma hbase_elt [dest]:
  "C ns \<in> hbase b \<Longrightarrow> n \<in> set ns \<Longrightarrow> n \<in> hbase b"
  by (induct ns) auto

lemma evalC_sum_list:
  "evalC b (C ns) = sum_list (map (\<lambda>n. b^evalC b n) ns)"
  by (induct ns) auto

lemma sum_list_replicate:
  "sum_list (replicate n x) = n * x"
  by (induct n) auto

lemma base_red:
  fixes b :: nat
  assumes n: "\<And>n'. n' \<in> set ns \<Longrightarrow> n < n'" "i < b" "i \<noteq> 0"
  and m: "\<And>m'. m' \<in> set ms \<Longrightarrow> m < m'" "j < b" "j \<noteq> 0"
  and s: "i * b^n + sum_list (map (\<lambda>n. b^n) ns) = j * b^m + sum_list (map (\<lambda>n. b^n) ms)"
  shows "i = j \<and> n = m"
  using n(1) m(1) s
proof (induct n arbitrary: m ns ms)
  { fix ns ms :: "nat list" and i j m :: nat
    assume n': "\<And>n'. n' \<in> set ns \<Longrightarrow> 0 < n'" "i < b" "i \<noteq> 0"
    assume m': "\<And>m'. m' \<in> set ms \<Longrightarrow> m < m'" "j < b" "j \<noteq> 0"
    assume s': "i * b^0 + sum_list (map (\<lambda>n. b^n) ns) = j * b^m + sum_list (map (\<lambda>n. b^n) ms)"
    obtain x where [simp]: "sum_list (map ((^) b) ns) = x*b"
      using n'(1)
      by (intro that[of "sum_list (map (\<lambda>n. b^(n-1)) ns)"])
        (simp add: ac_simps flip: sum_list_const_mult power_Suc cong: map_cong)
    obtain y where [simp]: "sum_list (map ((^) b) ms) = y*b"
      using order.strict_trans1[OF le0 m'(1)]
      by (intro that[of "sum_list (map (\<lambda>n. b^(n-1)) ms)"])
        (simp add: ac_simps flip: sum_list_const_mult power_Suc cong: map_cong)
    have [simp]: "m = 0"
      using s' n'(2,3)
      by (cases m, simp_all)
        (metis Groups.mult_ac(2) Groups.mult_ac(3) Suc_pred div_less mod_div_mult_eq
          mod_mult_self2 mod_mult_self2_is_0 mult_zero_right nat.simps(3))
    have "i = j \<and> 0 = m" using s' n'(2,3) m'(2,3)
      by simp (metis div_less mod_div_mult_eq mod_mult_self1)
  } note BASE = this
  {
    case 0 show ?case by (rule BASE; fact)
  next
    case (Suc n m')
    have "j = i \<and> 0 = Suc n" if "m' = 0" using Suc(2-4)
      by (intro BASE[of ms j ns "Suc n" i]) (simp_all add: ac_simps that n(2,3) m(2,3))
    then obtain m where m' [simp]: "m' = Suc m"
      by (cases m') auto
    obtain ns' where [simp]: "ns = map Suc ns'" "\<And>n'. n' \<in> set ns' \<Longrightarrow> n < n'"
      using Suc(2) less_trans[OF zero_less_Suc Suc(2)]
      by (intro that[of "map (\<lambda>n. n-1) ns"]; force cong: map_cong)
    obtain ms' where [simp]: "ms = map Suc ms'" "\<And>m'. m' \<in> set ms' \<Longrightarrow> m < m'"
      using Suc(3)[unfolded m'] less_trans[OF zero_less_Suc Suc(3)[unfolded m']]
      by (intro that[of "map (\<lambda>n. n-1) ms"]; force cong: map_cong)
    have *: "b * x = b * y \<Longrightarrow> x = y" for x y using n(2) by simp
    have "i = j \<and> n = m"
    proof (rule Suc(1)[of "map (\<lambda>n. n-1) ns" "map (\<lambda>n. n-1) ms" m, OF _ _ *], goal_cases)
      case 3 show ?case using Suc(4) unfolding add_mult_distrib2
        by (simp add: comp_def ac_simps flip: sum_list_const_mult)
    qed simp_all
    then show ?case by simp
  }
qed

lemma evalC_inj_on_hbase:
  "n \<in> hbase b \<Longrightarrow> m \<in> hbase b \<Longrightarrow> evalC b n = evalC b m \<Longrightarrow> n = m"
proof (induct n arbitrary: m rule: hbase.induct)
  case 1
  then show ?case by (cases m rule: hbase.cases) simp_all
next
  case (2 i n ns m')
  obtain j m ms where [simp]: "m' = C (replicate j m @ ms)" and
    m: "j \<noteq> 0" "j < b" "m \<in> hbase b" "C ms \<in> hbase b" "\<And>m'. m' \<in> set ms \<Longrightarrow> evalC b m < evalC b m'"
    using 2(8,1,2,9) by (cases m' rule: hbase.cases) simp_all
  have "i = j \<and> evalC b n = evalC b m" using 2(1,2,7,9) m(1,2,5)
    by (intro base_red[of "map (evalC b) ns" _ _ b "map (evalC b) ms"])
      (auto simp: comp_def evalC_sum_list sum_list_replicate)
  then show ?case
    using 2(4)[OF m(3)] 2(6)[OF m(4)] 2(9) by simp
qed

subsection \<open>Correctness of @{const stepC}\<close>

text \<open>We show that @{term "stepC c"} preserves hereditary base @{term "c + 2 :: nat"}
  representations. In order to cover intermediate results produced by @{const stepC}, we extend
  the hereditary base representation to allow the least significant digit to be equal to @{term b},
  which essentially means that we may have an extra sibling in front on every level.\<close>

inductive_set hbase_ext for b where
  "n \<in> hbase b \<Longrightarrow> n \<in> hbase_ext b"
| "n \<in> hbase_ext b \<Longrightarrow>
   C m \<in> hbase b \<Longrightarrow> (\<And>m'. m' \<in> set m \<Longrightarrow> evalC b n \<le> evalC b m') \<Longrightarrow>
   C (n # m) \<in> hbase_ext b"

lemma hbase_ext_hd' [dest]:
  "C (n # ns) \<in> hbase_ext b \<Longrightarrow> n \<in> hbase_ext b"
  by (cases rule: hbase_ext.cases) (auto intro: hbase_ext.intros(1))

lemma hbase_ext_tl:
  "C ns \<in> hbase_ext b \<Longrightarrow> ns \<noteq> [] \<Longrightarrow> C (tl ns) \<in> hbase b"
  by (cases "C ns" b rule: hbase_ext.cases; cases ns) (simp_all add: hbase_tl')

lemmas hbase_ext_tl' [dest] = hbase_ext_tl[of "n # ns" for n ns, simplified]

lemma hbase_funC:
  "c \<noteq> 0 \<Longrightarrow> C (n # ns) \<in> hbase_ext (Suc c) \<Longrightarrow>
    C (funC n (Suc c) @ ns) \<in> hbase_ext (Suc c)"
proof (induct n arbitrary: ns rule: funC.induct)
  case (2 ms)
  have [simp]: "evalC (Suc c) (C ms) < evalC (Suc c) m'" if "m' \<in> set ns" for m'
    using 2(2)
  proof (cases rule: hbase_ext.cases)
    case 1 then show ?thesis using that
      by (cases rule: hbase.cases, case_tac i) (auto intro: Suc_lessD)
  qed (auto simp: Suc_le_eq that)
  show ?case using 2
    by (auto 0 4 intro: hbase_ext.intros hbase.intros(2) order.strict_implies_order)
next
  case (3 m ms ms')
  show ?case
    unfolding funC.simps append_Cons append_Nil
  proof (rule hbase_ext.intros(2), goal_cases 31 32 33)
    case (33 m')
    show ?case using 3(3)
    proof (cases rule: hbase_ext.cases)
      case 1 show ?thesis using 1 3(1,2) 33
        by (cases rule: hbase.cases, case_tac i) (auto intro: less_or_eq_imp_le)
    qed (insert 33, simp)
  qed (insert 3, blast+)
qed auto

lemma stepC_sound:
  "n \<in> hbase_ext (Suc (Suc c)) \<Longrightarrow> stepC c n \<in> hbase (Suc (Suc c))"
proof (induct c n rule: stepC.induct)
  case (3 c n ns ms)
  show ?case using 3(2,1)
    by (cases rule: hbase_ext.cases; unfold stepC.simps) (auto intro: hbase_funC)
qed (auto intro: hbase.intros)

subsection \<open>Surjectivity of @{const evalC}\<close>

text \<open>Note that the base must be at least @{term "2 :: nat"}.\<close>

lemma evalC_surjective:
  "\<exists>n' \<in> hbase (Suc (Suc b)). evalC (Suc (Suc b)) n' = n"
proof (induct n)
  case 0 then show ?case by (auto intro: bexI[of _ "C []"] hbase.intros)
next
  have [simp]: "Suc x \<le> Suc (Suc b)^x" for x by (induct x) auto
  case (Suc n)
  then guess n' by (rule bexE)
  then obtain n' j where n': "Suc n \<le> j" "j = evalC (Suc (Suc b)) n'" "n' \<in> hbase (Suc (Suc b))"
    by (intro that[of _ "C [n']"])
      (auto intro!: intro: hbase.intros(1) dest!: hbaseI2[of 1 "b+2" n' "[]", simplified])
  then show ?case
  proof (induct rule: inc_induct)
    case (step m)
    guess n' using step(3)[OF step(4,5)] by (rule bexE)
    then show ?case using stepC_dec[of n' "b"]
      by (cases n' rule: C2O.cases) (auto intro: stepC_sound hbase_ext.intros(1))
  qed blast
qed

subsection \<open>Monotonicity of @{const hbase}\<close>

text \<open>Here we show that every hereditary base @{term "b :: nat"} number is also a valid hereditary
  base @{term "b+1 :: nat"} number. This is not immediate because we have to show that monotonicity
  of siblings is preserved.\<close>

lemma hbase_evalC_mono:
  assumes "n \<in> hbase b" "m \<in> hbase b" "evalC b n < evalC b m"
  shows "evalC (Suc b) n < evalC (Suc b) m"
proof (cases "b < 2")
  case True show ?thesis using assms(2,3) True by (cases rule: hbase.cases) simp_all
next
  case False
  then obtain b' where [simp]: "b = Suc (Suc b')"
    by (auto simp: numeral_2_eq_2 not_less_eq dest: less_imp_Suc_add)
  show ?thesis using assms(3,1,2)
  proof (induct "evalC b n" "evalC b m" arbitrary: n m rule: less_Suc_induct)
    case 1 then show ?case using stepC_sound[of m b', OF hbase_ext.intros(1)]
      stepC_dec[of m b'] stepC_dec'[of m b'] evalC_inj_on_hbase
      by (cases m rule: C2O.cases) (fastforce simp: eval_nat_numeral)+
  next
    case (2 j) then show ?case
      using evalC_surjective[of b' j] less_trans by fastforce
  qed
qed

lemma hbase_mono:
  "n \<in> hbase b \<Longrightarrow> n \<in> hbase (Suc b)"
  by (induct n rule: hbase.induct) (auto 0 3 intro: hbase.intros hbase_evalC_mono)

subsection \<open>Conversion to and from @{type nat}\<close>

text \<open>We have previously defined @{term "H2N b = evalC b"} and @{term "N2H b"} as its inverse.
  So we can use the injectivity and surjectivity of @{term "evalC b"} for simplification.\<close>

lemma N2H_inv:
  "n \<in> hbase b \<Longrightarrow> N2H b (H2N b n) = n"
  using evalC_inj_on_hbase
  by (auto simp: N2H_def H2N_def[abs_def] inj_on_def intro!: inv_into_f_f)

lemma H2N_inv:
  "H2N (Suc (Suc b)) (N2H (Suc (Suc b)) n) = n"
  using evalC_surjective[of "b" n]
  by (auto simp: N2H_def H2N_def[abs_def] intro: f_inv_into_f)

lemma N2H_eqI:
  "n \<in> hbase (Suc (Suc b)) \<Longrightarrow>
   H2N (Suc (Suc b)) n = m \<Longrightarrow> N2H (Suc (Suc b)) m = n"
  using N2H_inv by blast

lemma N2H_neI:
  "n \<in> hbase (Suc (Suc b)) \<Longrightarrow>
   H2N (Suc (Suc b)) n \<noteq> m \<Longrightarrow> N2H (Suc (Suc b)) m \<noteq> n"
  using H2N_inv by blast

lemma N2H_0 [simp]:
  "N2H (Suc (Suc c)) 0 = C []"
  using H2N_def N2H_inv hbase.intros(1) by fastforce

lemma N2H_nz [simp]:
  "0 < n \<Longrightarrow> N2H (Suc (Suc c)) n \<noteq> C []"
  by (metis N2H_0 H2N_inv neq0_conv)


section \<open>The Goodstein function revisited\<close>

text \<open>We are now ready to prove termination of the Goodstein function @{const goodstein} as well
  as its relation to @{const goodsteinC} and @{const goodsteinO}.\<close>

lemma goodstein_aux:
  "goodsteinC (Suc c) (N2H (Suc (Suc c)) (Suc n)) =
    goodsteinC (c+2) (N2H (c+3) (H2N (c+3) (N2H (c+2) (n+1)) - 1))"
proof -
  have [simp]: "n \<noteq> C [] \<Longrightarrow> goodsteinC c n = goodsteinC (c+1) (stepC c n)" for c n
    by (induct c n rule: stepC.induct) simp_all
  have [simp]: "stepC (Suc c) (N2H (Suc (Suc c)) (Suc n)) \<in> hbase (Suc (Suc (Suc c)))"
    by (metis H2N_def N2H_inv evalC_surjective hbase_ext.intros(1) hbase_mono stepC_sound)
  show ?thesis
    using arg_cong[OF stepC_dec[of "N2H (c+2) (n+1)" "c+1", folded H2N_def], of "\<lambda>n. N2H (c+3) (n-1)"]
    by (simp add: eval_nat_numeral N2H_inv)
qed

termination goodstein
proof (relation "measure (\<lambda>(c, n). goodsteinC c (N2H (c+1) n) - c)", goal_cases _ 1)
  case (1 c n)
  have *: "goodsteinC c n \<ge> c" for c n
    by (induct c n rule: goodsteinC.induct) simp_all
  show ?case by (simp add: goodstein_aux eval_nat_numeral) (meson Suc_le_eq diff_less_mono2 lessI *)
qed simp

lemma goodstein_def':
  "c \<noteq> 0 \<Longrightarrow> goodstein c n = goodsteinC c (N2H (c+1) n)"
  by (induct c n rule: goodstein.induct) (simp_all add: goodstein_aux eval_nat_numeral)

lemma goodstein_impl:
  "c \<noteq> 0 \<Longrightarrow> goodstein c n = goodsteinO c (C2O (N2H (c+1) n))"
  \<comment> \<open>but note that @{term N2H} is not executable as currently defined\<close>
  using goodstein_def'[unfolded goodsteinC_def'] .

lemma goodstein_16:
  "\<G> 16 = goodsteinO 1 (exp\<omega> (exp\<omega> (exp\<omega> (exp\<omega> Z))))"
proof -
  have "N2H (Suc (Suc 0)) 16 = C [C [C [C [C []]]]]"
    by (auto simp: H2N_def intro!: N2H_eqI hbase_singletonI hbase.intros(1))
  then show ?thesis by (simp add: goodstein_impl)
qed


section \<open>Translation to $\lambda$-calculus\<close>

text \<open>We define Church encodings for @{type nat} and @{type Ord}. Note that we are basically in a
  Hindley-Milner type system, so we cannot use a proper polymorphic type. We can still express
  Church encodings as folds over values of the original type.\<close>

abbreviation Z\<^sub>N where "Z\<^sub>N \<equiv> (\<lambda>s z. z)"
abbreviation S\<^sub>N where "S\<^sub>N \<equiv> (\<lambda>n s z. s (n s z))"

primrec fold_nat ("\<langle>_\<rangle>\<^sub>N") where
  "\<langle>0\<rangle>\<^sub>N = Z\<^sub>N"
| "\<langle>Suc n\<rangle>\<^sub>N = S\<^sub>N \<langle>n\<rangle>\<^sub>N"

lemma one\<^sub>N:
  "\<langle>1\<rangle>\<^sub>N = (\<lambda>x. x)"
  by simp

abbreviation Z\<^sub>O where "Z\<^sub>O \<equiv> (\<lambda>z s l. z)"
abbreviation S\<^sub>O where "S\<^sub>O \<equiv> (\<lambda>n z s l. s (n z s l))"
abbreviation L\<^sub>O where "L\<^sub>O \<equiv> (\<lambda>f z s l. l (\<lambda>i. f i z s l))"

primrec fold_Ord ("\<langle>_\<rangle>\<^sub>O") where
  "\<langle>Z\<rangle>\<^sub>O = Z\<^sub>O"
| "\<langle>S n\<rangle>\<^sub>O = S\<^sub>O \<langle>n\<rangle>\<^sub>O"
| "\<langle>L f\<rangle>\<^sub>O = L\<^sub>O (\<lambda>i. \<langle>f i\<rangle>\<^sub>O)"

text \<open>The following abbreviations and lemmas show how to implement the arithmetic functions and
  the Goodstein function on a Church-encoded @{type Ord} in lambda calculus.\<close>

abbreviation (input) add\<^sub>O where
  "add\<^sub>O n m \<equiv> (\<lambda>z s l. m (n z s l) s l)"

lemma add\<^sub>O:
  "\<langle>addO n m\<rangle>\<^sub>O = add\<^sub>O \<langle>n\<rangle>\<^sub>O \<langle>m\<rangle>\<^sub>O"
  by (induct m) simp_all

abbreviation (input) mul\<^sub>O where
  "mul\<^sub>O n m \<equiv> (\<lambda>z s l. m z (\<lambda>m. n m s l) l)"

lemma mul\<^sub>O:
  "\<langle>mulO n m\<rangle>\<^sub>O = mul\<^sub>O \<langle>n\<rangle>\<^sub>O \<langle>m\<rangle>\<^sub>O"
  by (induct m) (simp_all add: add\<^sub>O)

abbreviation (input) \<omega>\<^sub>O where
  "\<omega>\<^sub>O \<equiv> (\<lambda>z s l. l (\<lambda>n. \<langle>n\<rangle>\<^sub>N s z))"

lemma \<omega>\<^sub>O:
  "\<langle>\<omega>\<rangle>\<^sub>O = \<omega>\<^sub>O"
proof -
  have [simp]: "\<langle>(S ^^ i) Z\<rangle>\<^sub>O z s l = \<langle>i\<rangle>\<^sub>N s z" for i z s l by (induct i) simp_all
  show ?thesis by (simp add: \<omega>_def)
qed

abbreviation (input) exp\<omega>\<^sub>O where
  "exp\<omega>\<^sub>O n \<equiv> (\<lambda>z s l. n s (\<lambda>x z. l (\<lambda>n. \<langle>n\<rangle>\<^sub>N x z)) (\<lambda>f z. l (\<lambda>n. f n z)) z)"

lemma exp\<omega>\<^sub>O:
  "\<langle>exp\<omega> n\<rangle>\<^sub>O = exp\<omega>\<^sub>O \<langle>n\<rangle>\<^sub>O"
  by (induct n) (simp_all add: mul\<^sub>O \<omega>\<^sub>O)

abbreviation (input) goodstein\<^sub>O where
  "goodstein\<^sub>O \<equiv> (\<lambda>c n. n (\<lambda>x. x) (\<lambda>n m. n (m + 1)) (\<lambda>f m. f (m + 2) m) c)"

lemma goodstein\<^sub>O:
  "goodsteinO c n = goodstein\<^sub>O c \<langle>n\<rangle>\<^sub>O"
  by (induct n arbitrary: c) simp_all

text \<open>Note that modeling Church encodings with folds is still limited. For example, the meaningful
  expression @{text "\<langle>n\<rangle>\<^sub>N exp\<omega>\<^sub>O Z\<^sub>O"} cannot be typed in Isabelle/HOL, as that would require rank-2
  polymorphism.\<close>

subsection \<open>Alternative: free theorems\<close>

text \<open>The following is essentially the free theorem for Church-encoded @{type Ord} values.\<close>

lemma freeOrd:
  assumes "\<And>n. h (s n) = s' (h n)" and "\<And>f. h (l f) = l' (\<lambda>i. h (f i))"
  shows "h (\<langle>n\<rangle>\<^sub>O z s l) = \<langle>n\<rangle>\<^sub>O (h z) s' l'"
  by (induct n) (simp_all add: assms)

text \<open>Each of the following proofs first states a naive definition of the corresponding function
  (which is proved correct by induction), from which we then derive the optimized version using
  the free theorem, by (conditional) rewriting (without induction).\<close>

lemma add\<^sub>O':
  "\<langle>addO n m\<rangle>\<^sub>O = add\<^sub>O \<langle>n\<rangle>\<^sub>O \<langle>m\<rangle>\<^sub>O"
proof -
  have [simp]: "\<langle>addO n m\<rangle>\<^sub>O = \<langle>m\<rangle>\<^sub>O \<langle>n\<rangle>\<^sub>O S\<^sub>O L\<^sub>O"
    by (induct m) simp_all
  show ?thesis
    by (intro ext) (simp add: freeOrd[where h = "\<lambda>n. n _ _ _"])
qed

lemma mul\<^sub>O':
  "\<langle>mulO n m\<rangle>\<^sub>O = mul\<^sub>O \<langle>n\<rangle>\<^sub>O \<langle>m\<rangle>\<^sub>O"
proof -
  have [simp]: "\<langle>mulO n m\<rangle>\<^sub>O = \<langle>m\<rangle>\<^sub>O Z\<^sub>O (\<lambda>m. add\<^sub>O m \<langle>n\<rangle>\<^sub>O) L\<^sub>O"
    by (induct m) (simp_all add: add\<^sub>O)
  show ?thesis
    by (intro ext) (simp add: freeOrd[where h = "\<lambda>n. n _ _ _"])
qed

lemma exp\<omega>\<^sub>O':
  "\<langle>exp\<omega> n\<rangle>\<^sub>O = exp\<omega>\<^sub>O \<langle>n\<rangle>\<^sub>O"
proof -
  have [simp]: "\<langle>exp\<omega> n\<rangle>\<^sub>O = \<langle>n\<rangle>\<^sub>O (S\<^sub>O Z\<^sub>O) (\<lambda>m. mul\<^sub>O m \<omega>\<^sub>O) L\<^sub>O"
    by (induct n) (simp_all add: mul\<^sub>O \<omega>\<^sub>O)
  show ?thesis
    by (intro ext) (simp add: fun_cong[OF freeOrd[where h = "\<lambda>n z. n z _ _"]])
qed

end