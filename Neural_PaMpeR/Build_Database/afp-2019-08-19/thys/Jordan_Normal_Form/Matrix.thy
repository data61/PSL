(*
    Author:      René Thiemann
                 Akihisa Yamada
    License:     BSD
*)
(* with contributions from Alexander Bentkamp, Universität des Saarlandes *)

section\<open>Vectors and Matrices\<close>

text \<open>We define vectors as pairs of dimension and a characteristic function from natural numbers
to elements.
Similarly, matrices are defined as triples of two dimensions and one
characteristic function from pairs of natural numbers to elements.
Via a subtype we ensure that the characteristic function always behaves the same
on indices outside the intended one. Hence, every matrix has a unique representation.

In this part we define basic operations like matrix-addition, -multiplication, scalar-product,
etc. We connect these operations to HOL-Algebra with its explicit carrier sets.\<close>

theory Matrix
imports
  Missing_Ring
  "HOL-Algebra.Module"
  Polynomial_Interpolation.Ring_Hom
  Conjugate
begin

subsection\<open>Vectors\<close>

text \<open>Here we specify which value should be returned in case
  an index is out of bounds. The current solution has the advantage
  that in the implementation later on, no index comparison has to be performed.\<close>

definition undef_vec :: "nat \<Rightarrow> 'a" where
  "undef_vec i \<equiv> [] ! i"

definition mk_vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "mk_vec n f \<equiv> \<lambda> i. if i < n then f i else undef_vec (i - n)"

typedef 'a vec = "{(n, mk_vec n f) | n f :: nat \<Rightarrow> 'a. True}"
  by auto

setup_lifting type_definition_vec

lift_definition dim_vec :: "'a vec \<Rightarrow> nat" is fst .
lift_definition vec_index :: "'a vec \<Rightarrow> (nat \<Rightarrow> 'a)" (infixl "$" 100) is snd .
lift_definition vec :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a vec"
  is "\<lambda> n f. (n, mk_vec n f)" by auto

lift_definition vec_of_list :: "'a list \<Rightarrow> 'a vec" is
  "\<lambda> v. (length v, mk_vec (length v) (nth v))" by auto

lift_definition list_of_vec :: "'a vec \<Rightarrow> 'a list" is
  "\<lambda> (n,v). map v [0 ..< n]" .

definition carrier_vec :: "nat \<Rightarrow> 'a vec set" where
  "carrier_vec n = { v . dim_vec v = n}"

lemma carrier_vec_dim_vec[simp]: "v \<in> carrier_vec (dim_vec v)" unfolding carrier_vec_def by auto

lemma dim_vec[simp]: "dim_vec (vec n f) = n" by transfer simp
lemma vec_carrier[simp]: "vec n f \<in> carrier_vec n" unfolding carrier_vec_def by auto
lemma index_vec[simp]: "i < n \<Longrightarrow> vec n f $ i = f i" by transfer (simp add: mk_vec_def)
lemma eq_vecI[intro]: "(\<And> i. i < dim_vec w \<Longrightarrow> v $ i = w $ i) \<Longrightarrow> dim_vec v = dim_vec w
  \<Longrightarrow> v = w"
  by (transfer, auto simp: mk_vec_def)

lemma carrier_dim_vec: "v \<in> carrier_vec n \<longleftrightarrow> dim_vec v = n"
  unfolding carrier_vec_def by auto

lemma carrier_vecD[simp]: "v \<in> carrier_vec n \<Longrightarrow> dim_vec v = n" using carrier_dim_vec by auto

lemma carrier_vecI: "dim_vec v = n \<Longrightarrow> v \<in> carrier_vec n" using carrier_dim_vec by auto

instantiation vec :: (plus) plus
begin
definition plus_vec :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: plus vec" where
  "v\<^sub>1 + v\<^sub>2 \<equiv> vec (dim_vec v\<^sub>2) (\<lambda> i. v\<^sub>1 $ i + v\<^sub>2 $ i)"
instance ..
end

instantiation vec :: (minus) minus
begin
definition minus_vec :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: minus vec" where
  "v\<^sub>1 - v\<^sub>2 \<equiv> vec (dim_vec v\<^sub>2) (\<lambda> i. v\<^sub>1 $ i - v\<^sub>2 $ i)"
instance ..
end

definition
  zero_vec :: "nat \<Rightarrow> 'a :: zero vec" ("0\<^sub>v")
  where "0\<^sub>v n \<equiv> vec n (\<lambda> i. 0)"

lemma zero_carrier_vec[simp]: "0\<^sub>v n \<in> carrier_vec n"
  unfolding zero_vec_def carrier_vec_def by auto

lemma index_zero_vec[simp]: "i < n \<Longrightarrow> 0\<^sub>v n $ i = 0" "dim_vec (0\<^sub>v n) = n"
  unfolding zero_vec_def by auto

lemma vec_of_dim_0[simp]: "dim_vec v = 0 \<longleftrightarrow> v = 0\<^sub>v 0" by auto

definition
  unit_vec :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: zero_neq_one) vec"
  where "unit_vec n i = vec n (\<lambda> j. if j = i then 1 else 0)"

lemma index_unit_vec[simp]:
  "i < n \<Longrightarrow> j < n \<Longrightarrow> unit_vec n i $ j = (if j = i then 1 else 0)"
  "i < n \<Longrightarrow> unit_vec n i $ i = 1"
  "dim_vec (unit_vec n i) = n"
  unfolding unit_vec_def by auto

lemma unit_vec_eq[simp]:
  assumes i: "i < n"
  shows "(unit_vec n i = unit_vec n j) = (i = j)"
proof -
  have "i \<noteq> j \<Longrightarrow> unit_vec n i $ i \<noteq> unit_vec n j $ i"
    unfolding unit_vec_def using i by simp
  then show ?thesis by metis
qed

lemma unit_vec_nonzero[simp]:
  assumes i_n: "i < n" shows "unit_vec n i \<noteq> zero_vec n" (is "?l \<noteq> ?r")
proof -
  have "?l $ i = 1" "?r $ i = 0" using i_n by auto
  thus "?l \<noteq> ?r" by auto
qed

lemma unit_vec_carrier[simp]: "unit_vec n i \<in> carrier_vec n"
  unfolding unit_vec_def carrier_vec_def by auto

definition unit_vecs:: "nat \<Rightarrow> 'a :: zero_neq_one vec list"
  where "unit_vecs n = map (unit_vec n) [0..<n]"

text "List of first i units"

fun unit_vecs_first:: "nat \<Rightarrow> nat \<Rightarrow> 'a::zero_neq_one vec list"
  where "unit_vecs_first n 0 = []"
    |   "unit_vecs_first n (Suc i) = unit_vecs_first n i @ [unit_vec n i]"

lemma unit_vecs_first: "unit_vecs n = unit_vecs_first n n"
  unfolding unit_vecs_def set_map set_upt
proof -
  {fix m
    have "m \<le> n \<Longrightarrow> map (unit_vec n) [0..<m] = unit_vecs_first n m"
    proof (induct m)
      case (Suc m) then have mn:"m\<le>n" by auto
        show ?case unfolding upt_Suc using Suc(1)[OF mn] by auto
    qed auto
  }
  thus "map (unit_vec n) [0..<n] = unit_vecs_first n n" by auto
qed

text "list of last i units"

fun unit_vecs_last:: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero_neq_one vec list"
  where "unit_vecs_last n 0 = []"
    |   "unit_vecs_last n (Suc i) = unit_vec n (n - Suc i) # unit_vecs_last n i"

lemma unit_vecs_last_carrier: "set (unit_vecs_last n i) \<subseteq> carrier_vec n"
  by (induct i;auto)

lemma unit_vecs_last[code]: "unit_vecs n = unit_vecs_last n n"
proof -
  { fix m assume "m = n"
    have "m \<le> n \<Longrightarrow> map (unit_vec n) [n-m..<n] = unit_vecs_last n m"
      proof (induction m)
      case (Suc m)
        then have nm:"n - Suc m < n" by auto
        have ins: "[n - Suc m ..< n] = (n - Suc m) # [n - m ..< n]"
          unfolding upt_conv_Cons[OF nm]
          by (auto simp: Suc.prems Suc_diff_Suc Suc_le_lessD)
        show ?case
          unfolding ins
          unfolding unit_vecs_last.simps
          unfolding list.map
          using Suc
          unfolding Suc by auto
      qed simp
  }
  thus "unit_vecs n = unit_vecs_last n n"
    unfolding unit_vecs_def by auto
qed

lemma unit_vecs_carrier: "set (unit_vecs n) \<subseteq> carrier_vec n"
proof
  fix u :: "'a vec"  assume u: "u \<in> set (unit_vecs n)"
  then obtain i where "u = unit_vec n i" unfolding unit_vecs_def by auto
  then show "u \<in> carrier_vec n"
    using unit_vec_carrier by auto
qed

lemma unit_vecs_last_distinct:
  "j \<le> n \<Longrightarrow> i < n - j \<Longrightarrow> unit_vec n i \<notin> set (unit_vecs_last n j)"
  by (induction j arbitrary:i, auto)

lemma unit_vecs_first_distinct:
  "i \<le> j \<Longrightarrow> j < n \<Longrightarrow> unit_vec n j \<notin> set (unit_vecs_first n i)"
  by (induction i arbitrary:j, auto)

definition map_vec where "map_vec f v \<equiv> vec (dim_vec v) (\<lambda>i. f (v $ i))"

instantiation vec :: (uminus) uminus
begin
definition uminus_vec :: "'a :: uminus vec \<Rightarrow> 'a vec" where
  "- v \<equiv> vec (dim_vec v) (\<lambda> i. - (v $ i))"
instance ..
end

definition smult_vec :: "'a :: times \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl "\<cdot>\<^sub>v" 70)
  where "a \<cdot>\<^sub>v v \<equiv> vec (dim_vec v) (\<lambda> i. a * v $ i)"

definition scalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: semiring_0" (infix "\<bullet>" 70)
  where "v \<bullet> w \<equiv> \<Sum> i \<in> {0 ..< dim_vec w}. v $ i * w $ i"

definition monoid_vec :: "'a itself \<Rightarrow> nat \<Rightarrow> ('a :: monoid_add vec) monoid" where
  "monoid_vec ty n \<equiv> \<lparr>
    carrier = carrier_vec n,
    mult = (+),
    one = 0\<^sub>v n\<rparr>"

definition module_vec ::
  "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> ('a,'a vec) module" where
  "module_vec ty n \<equiv> \<lparr>
    carrier = carrier_vec n,
    mult = undefined,
    one = undefined,
    zero = 0\<^sub>v n,
    add = (+),
    smult = (\<cdot>\<^sub>v)\<rparr>"

lemma monoid_vec_simps:
  "mult (monoid_vec ty n) = (+)"
  "carrier (monoid_vec ty n) = carrier_vec n"
  "one (monoid_vec ty n) = 0\<^sub>v n"
  unfolding monoid_vec_def by auto

lemma module_vec_simps:
  "add (module_vec ty n) = (+)"
  "zero (module_vec ty n) = 0\<^sub>v n"
  "carrier (module_vec ty n) = carrier_vec n"
  "smult (module_vec ty n) = (\<cdot>\<^sub>v)"
  unfolding module_vec_def by auto

definition finsum_vec :: "'a :: monoid_add itself \<Rightarrow> nat \<Rightarrow> ('c \<Rightarrow> 'a vec) \<Rightarrow> 'c set \<Rightarrow> 'a vec" where
  "finsum_vec ty n = finprod (monoid_vec ty n)"

lemma index_add_vec[simp]:
  "i < dim_vec v\<^sub>2 \<Longrightarrow> (v\<^sub>1 + v\<^sub>2) $ i = v\<^sub>1 $ i + v\<^sub>2 $ i" "dim_vec (v\<^sub>1 + v\<^sub>2) = dim_vec v\<^sub>2"
  unfolding plus_vec_def by auto

lemma index_minus_vec[simp]:
  "i < dim_vec v\<^sub>2 \<Longrightarrow> (v\<^sub>1 - v\<^sub>2) $ i = v\<^sub>1 $ i - v\<^sub>2 $ i" "dim_vec (v\<^sub>1 - v\<^sub>2) = dim_vec v\<^sub>2"
  unfolding minus_vec_def by auto

lemma index_map_vec[simp]:
  "i < dim_vec v \<Longrightarrow> map_vec f v $ i = f (v $ i)"
  "dim_vec (map_vec f v) = dim_vec v"
  unfolding map_vec_def by auto

lemma map_carrier_vec[simp]: "map_vec h v \<in> carrier_vec n = (v \<in> carrier_vec n)"
  unfolding map_vec_def carrier_vec_def by auto

lemma index_uminus_vec[simp]:
  "i < dim_vec v \<Longrightarrow> (- v) $ i = - (v $ i)"
  "dim_vec (- v) = dim_vec v"
  unfolding uminus_vec_def by auto

lemma index_smult_vec[simp]:
  "i < dim_vec v \<Longrightarrow> (a \<cdot>\<^sub>v v) $ i = a * v $ i" "dim_vec (a \<cdot>\<^sub>v v) = dim_vec v"
  unfolding smult_vec_def by auto

lemma add_carrier_vec[simp]:
  "v\<^sub>1 \<in> carrier_vec n \<Longrightarrow> v\<^sub>2 \<in> carrier_vec n \<Longrightarrow> v\<^sub>1 + v\<^sub>2 \<in> carrier_vec n"
  unfolding carrier_vec_def by auto

lemma minus_carrier_vec[simp]:
  "v\<^sub>1 \<in> carrier_vec n \<Longrightarrow> v\<^sub>2 \<in> carrier_vec n \<Longrightarrow> v\<^sub>1 - v\<^sub>2 \<in> carrier_vec n"
  unfolding carrier_vec_def by auto

lemma comm_add_vec[ac_simps]:
  "(v\<^sub>1 :: 'a :: ab_semigroup_add vec) \<in> carrier_vec n \<Longrightarrow> v\<^sub>2 \<in> carrier_vec n \<Longrightarrow> v\<^sub>1 + v\<^sub>2 = v\<^sub>2 + v\<^sub>1"
  by (intro eq_vecI, auto simp: ac_simps)

lemma assoc_add_vec[simp]:
  "(v\<^sub>1 :: 'a :: semigroup_add vec) \<in> carrier_vec n \<Longrightarrow> v\<^sub>2 \<in> carrier_vec n \<Longrightarrow> v\<^sub>3 \<in> carrier_vec n
  \<Longrightarrow> (v\<^sub>1 + v\<^sub>2) + v\<^sub>3 = v\<^sub>1 + (v\<^sub>2 + v\<^sub>3)"
  by (intro eq_vecI, auto simp: ac_simps)

lemma zero_minus_vec[simp]: "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> 0\<^sub>v n - v = - v"
  by (intro eq_vecI, auto)

lemma minus_zero_vec[simp]: "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> v - 0\<^sub>v n = v"
  by (intro eq_vecI, auto)

lemma minus_cancel_vec[simp]: "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> v - v = 0\<^sub>v n"
  by (intro eq_vecI, auto)

lemma minus_add_uminus_vec: "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow>
  w \<in> carrier_vec n \<Longrightarrow> v - w = v + (- w)"
  by (intro eq_vecI, auto)

lemma comm_monoid_vec: "comm_monoid (monoid_vec TYPE ('a :: comm_monoid_add) n)"
  by (unfold_locales, auto simp: monoid_vec_def ac_simps)

lemma left_zero_vec[simp]: "(v :: 'a :: monoid_add vec) \<in> carrier_vec n  \<Longrightarrow> 0\<^sub>v n + v = v" by auto

lemma right_zero_vec[simp]: "(v :: 'a :: monoid_add vec) \<in> carrier_vec n  \<Longrightarrow> v + 0\<^sub>v n = v" by auto


lemma uminus_carrier_vec[simp]:
  "(- v \<in> carrier_vec n) = (v \<in> carrier_vec n)"
  unfolding carrier_vec_def by auto

lemma uminus_r_inv_vec[simp]:
  "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> (v + - v) = 0\<^sub>v n"
  by (intro eq_vecI, auto)

lemma uminus_l_inv_vec[simp]:
  "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> (- v + v) = 0\<^sub>v n"
  by (intro eq_vecI, auto)

lemma add_inv_exists_vec:
  "(v :: 'a :: group_add vec) \<in> carrier_vec n \<Longrightarrow> \<exists> w \<in> carrier_vec n. w + v = 0\<^sub>v n \<and> v + w = 0\<^sub>v n"
  by (intro bexI[of _ "- v"], auto)

lemma comm_group_vec: "comm_group (monoid_vec TYPE ('a :: ab_group_add) n)"
  by (unfold_locales, insert add_inv_exists_vec, auto simp: monoid_vec_def ac_simps Units_def)

lemmas finsum_vec_insert =
  comm_monoid.finprod_insert[OF comm_monoid_vec, folded finsum_vec_def, unfolded monoid_vec_simps]

lemmas finsum_vec_closed =
  comm_monoid.finprod_closed[OF comm_monoid_vec, folded finsum_vec_def, unfolded monoid_vec_simps]

lemmas finsum_vec_empty =
  comm_monoid.finprod_empty[OF comm_monoid_vec, folded finsum_vec_def, unfolded monoid_vec_simps]

lemma smult_carrier_vec[simp]: "(a \<cdot>\<^sub>v v \<in> carrier_vec n) = (v \<in> carrier_vec n)"
  unfolding carrier_vec_def by auto

lemma scalar_prod_left_zero[simp]: "v \<in> carrier_vec n \<Longrightarrow> 0\<^sub>v n \<bullet> v = 0"
  unfolding scalar_prod_def
  by (rule sum.neutral, auto)

lemma scalar_prod_right_zero[simp]: "v \<in> carrier_vec n \<Longrightarrow> v \<bullet> 0\<^sub>v n = 0"
  unfolding scalar_prod_def
  by (rule sum.neutral, auto)

lemma scalar_prod_left_unit[simp]: assumes v: "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n" and i: "i < n"
  shows "unit_vec n i \<bullet> v = v $ i"
proof -
  let ?f = "\<lambda> k. unit_vec n i $ k * v $ k"
  have id: "(\<Sum>k\<in>{0..<n}. ?f k) = unit_vec n i $ i * v $ i + (\<Sum>k\<in>{0..<n} - {i}. ?f k)"
    by (rule sum.remove, insert i, auto)
  also have "(\<Sum> k\<in>{0..<n} - {i}. ?f k) = 0"
    by (rule sum.neutral, insert i, auto)
  finally
  show ?thesis unfolding scalar_prod_def using i v by simp
qed

lemma scalar_prod_right_unit[simp]: assumes i: "i < n"
  shows "(v :: 'a :: semiring_1 vec) \<bullet> unit_vec n i = v $ i"
proof -
  let ?f = "\<lambda> k. v $ k * unit_vec n i $ k"
  have id: "(\<Sum>k\<in>{0..<n}. ?f k) = v $ i * unit_vec n i $ i + (\<Sum>k\<in>{0..<n} - {i}. ?f k)"
    by (rule sum.remove, insert i, auto)
  also have "(\<Sum>k\<in>{0..<n} - {i}. ?f k) = 0"
    by (rule sum.neutral, insert i, auto)
  finally
  show ?thesis unfolding scalar_prod_def using i by simp
qed

lemma add_scalar_prod_distrib: assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n" "v\<^sub>3 \<in> carrier_vec n"
  shows "(v\<^sub>1 + v\<^sub>2) \<bullet> v\<^sub>3 = v\<^sub>1 \<bullet> v\<^sub>3 + v\<^sub>2 \<bullet> v\<^sub>3"
proof -
  have "(\<Sum>i\<in>{0..<dim_vec v\<^sub>3}. (v\<^sub>1 + v\<^sub>2) $ i * v\<^sub>3 $ i) = (\<Sum>i\<in>{0..<dim_vec v\<^sub>3}. v\<^sub>1 $ i * v\<^sub>3 $ i + v\<^sub>2 $ i * v\<^sub>3 $ i)"
    by (rule sum.cong, insert v, auto simp: algebra_simps)
  thus ?thesis unfolding scalar_prod_def using v by (auto simp: sum.distrib)
qed

lemma scalar_prod_add_distrib: assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n" "v\<^sub>3 \<in> carrier_vec n"
  shows "v\<^sub>1 \<bullet> (v\<^sub>2 + v\<^sub>3) = v\<^sub>1 \<bullet> v\<^sub>2 + v\<^sub>1 \<bullet> v\<^sub>3"
proof -
  have "(\<Sum>i\<in>{0..<dim_vec v\<^sub>3}. v\<^sub>1 $ i * (v\<^sub>2 + v\<^sub>3) $ i) = (\<Sum>i\<in>{0..<dim_vec v\<^sub>3}. v\<^sub>1 $ i * v\<^sub>2 $ i + v\<^sub>1 $ i * v\<^sub>3 $ i)"
    by (rule sum.cong, insert v, auto simp: algebra_simps)
  thus ?thesis unfolding scalar_prod_def using v by (auto intro: sum.distrib)
qed

lemma smult_scalar_prod_distrib[simp]: assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n"
  shows "(a \<cdot>\<^sub>v v\<^sub>1) \<bullet> v\<^sub>2 = a * (v\<^sub>1 \<bullet> v\<^sub>2)"
  unfolding scalar_prod_def sum_distrib_left
  by (rule sum.cong, insert v, auto simp: ac_simps)

lemma scalar_prod_smult_distrib[simp]: assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n"
  shows "v\<^sub>1 \<bullet> (a \<cdot>\<^sub>v v\<^sub>2) = (a :: 'a :: comm_ring) * (v\<^sub>1 \<bullet> v\<^sub>2)"
  unfolding scalar_prod_def sum_distrib_left
  by (rule sum.cong, insert v, auto simp: ac_simps)

lemma comm_scalar_prod: assumes "(v\<^sub>1 :: 'a :: comm_semiring_0 vec) \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n"
  shows "v\<^sub>1 \<bullet> v\<^sub>2 = v\<^sub>2 \<bullet> v\<^sub>1"
  unfolding scalar_prod_def
  by (rule sum.cong, insert assms, auto simp: ac_simps)

lemma add_smult_distrib_vec:
  "((a::'a::ring) + b) \<cdot>\<^sub>v v = a \<cdot>\<^sub>v v + b \<cdot>\<^sub>v v"
  unfolding smult_vec_def plus_vec_def
  by (rule eq_vecI, auto simp: distrib_right)

lemma smult_add_distrib_vec:
  assumes "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "(a::'a::ring) \<cdot>\<^sub>v (v + w) = a \<cdot>\<^sub>v v + a \<cdot>\<^sub>v w"
  apply (rule eq_vecI)
  unfolding smult_vec_def plus_vec_def
  using assms distrib_left by auto

lemma smult_smult_assoc:
  "a \<cdot>\<^sub>v (b \<cdot>\<^sub>v v) = (a * b::'a::ring) \<cdot>\<^sub>v v"
  apply (rule sym, rule eq_vecI)
  unfolding smult_vec_def plus_vec_def using mult.assoc by auto

lemma one_smult_vec [simp]:
  "(1::'a::ring_1) \<cdot>\<^sub>v v = v" unfolding smult_vec_def
  by (rule eq_vecI,auto)

lemma uminus_zero_vec[simp]: "- (0\<^sub>v n) = (0\<^sub>v n :: 'a :: group_add vec)" 
  by (intro eq_vecI, auto)

lemma index_finsum_vec: assumes "finite F" and i: "i < n"
  and vs: "vs \<in> F \<rightarrow> carrier_vec n"
  shows "finsum_vec TYPE('a :: comm_monoid_add) n vs F $ i = sum (\<lambda> f. vs f $ i) F"
  using \<open>finite F\<close> vs
proof (induct F)
  case (insert f F)
  hence IH: "finsum_vec TYPE('a) n vs F $ i = (\<Sum>f\<in>F. vs f $ i)"
    and vs: "vs \<in> F \<rightarrow> carrier_vec n" "vs f \<in> carrier_vec n" by auto
  show ?case unfolding finsum_vec_insert[OF insert(1-2) vs]
    unfolding sum.insert[OF insert(1-2)]
    unfolding IH[symmetric]
    by (rule index_add_vec, insert i, insert finsum_vec_closed[OF vs(1)], auto)
qed (insert i, auto simp: finsum_vec_empty)

text \<open>Definition of pointwise ordering on vectors for non-strict part, and
  strict version is defined in a way such that the @{class order} constraints are satisfied.\<close>

instantiation vec :: (ord) ord
begin

definition less_eq_vec :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> bool" where
  "less_eq_vec v w = (dim_vec v = dim_vec w \<and> (\<forall> i < dim_vec w. v $ i \<le> w $ i))" 

definition less_vec :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> bool" where
  "less_vec v w = (v \<le> w \<and> \<not> (w \<le> v))"
instance ..
end

instantiation vec :: (preorder) preorder
begin
instance
  by (standard, auto simp: less_vec_def less_eq_vec_def order_trans)
end

instantiation vec :: (order) order
begin
instance
  by (standard, intro eq_vecI, auto simp: less_eq_vec_def order.antisym)
end


subsection\<open>Matrices\<close>

text \<open>Similarly as for vectors, we specify which value should be returned in case
  an index is out of bounds. It is defined in a way that only few
  index comparisons have to be performed in the implementation.\<close>

definition undef_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> nat \<times> nat \<Rightarrow> 'a" where
  "undef_mat nr nc f \<equiv> \<lambda> (i,j). [[f (i,j). j <- [0 ..< nc]] . i <- [0 ..< nr]] ! i ! j"

lemma undef_cong_mat: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "undef_mat nr nc f x = undef_mat nr nc f' x"
proof (cases x)
  case (Pair i j)
  have nth_map_ge: "\<And> i xs. \<not> i < length xs \<Longrightarrow> xs ! i = [] ! (i - length xs)"
    by (metis append_Nil2 nth_append)
  note [simp] = Pair undef_mat_def nth_map_ge[of i] nth_map_ge[of j]
  show ?thesis
    by (cases "i < nr", simp, cases "j < nc", insert assms, auto)
qed

definition mk_mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" where
  "mk_mat nr nc f \<equiv> \<lambda> (i,j). if i < nr \<and> j < nc then f (i,j) else undef_mat nr nc f (i,j)"

lemma cong_mk_mat: assumes "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow> f (i,j) = f' (i,j)"
  shows "mk_mat nr nc f = mk_mat nr nc f'"
  using undef_cong_mat[of nr nc f f', OF assms]
  using assms unfolding mk_mat_def
  by auto

typedef 'a mat = "{(nr, nc, mk_mat nr nc f) | nr nc f :: nat \<times> nat \<Rightarrow> 'a. True}"
  by auto

setup_lifting type_definition_mat

lift_definition dim_row :: "'a mat \<Rightarrow> nat" is fst .
lift_definition dim_col :: "'a mat \<Rightarrow> nat" is "fst o snd" .
lift_definition index_mat :: "'a mat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a)" (infixl "$$" 100) is "snd o snd" .
lift_definition mat :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<Rightarrow> 'a) \<Rightarrow> 'a mat"
  is "\<lambda> nr nc f. (nr, nc, mk_mat nr nc f)" by auto
lift_definition mat_of_row_fun :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a vec) \<Rightarrow> 'a mat" ("mat\<^sub>r")
  is "\<lambda> nr nc f. (nr, nc, mk_mat nr nc (\<lambda> (i,j). f i $ j))" by auto

definition mat_to_list :: "'a mat \<Rightarrow> 'a list list" where
  "mat_to_list A = [ [A $$ (i,j) . j <- [0 ..< dim_col A]] . i <- [0 ..< dim_row A]]"

fun square_mat :: "'a mat \<Rightarrow> bool" where "square_mat A = (dim_col A = dim_row A)"

definition upper_triangular :: "'a::zero mat \<Rightarrow> bool"
  where "upper_triangular A \<equiv>
    \<forall>i < dim_row A. \<forall> j < i. A $$ (i,j) = 0"

lemma upper_triangularD[elim] :
  "upper_triangular A \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0"
unfolding upper_triangular_def by auto

lemma upper_triangularI[intro] :
  "(\<And>i j. j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0) \<Longrightarrow> upper_triangular A"
unfolding upper_triangular_def by auto

lemma dim_row_mat[simp]: "dim_row (mat nr nc f) = nr" "dim_row (mat\<^sub>r nr nc g) = nr"
  by (transfer, simp)+

lemma dim_col_mat[simp]: "dim_col (mat nr nc f) = nc" "dim_col (mat\<^sub>r nr nc g) = nc"
  by (transfer, simp)+

definition carrier_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a mat set"
  where "carrier_mat nr nc = { m . dim_row m = nr \<and> dim_col m = nc}"

lemma carrier_mat_triv[simp]: "m \<in> carrier_mat (dim_row m) (dim_col m)"
  unfolding carrier_mat_def by auto

lemma mat_carrier[simp]: "mat nr nc f \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by auto

definition elements_mat :: "'a mat \<Rightarrow> 'a set"
  where "elements_mat A = set [A $$ (i,j). i <- [0 ..< dim_row A], j <- [0 ..< dim_col A]]"

lemma elements_matD [dest]:
  "a \<in> elements_mat A \<Longrightarrow> \<exists>i j. i < dim_row A \<and> j < dim_col A \<and> a = A $$ (i,j)"
  unfolding elements_mat_def by force

lemma elements_matI [intro]:
  "A \<in> carrier_mat nr nc \<Longrightarrow> i < nr \<Longrightarrow> j < nc \<Longrightarrow> a = A $$ (i,j) \<Longrightarrow> a \<in> elements_mat A"
  unfolding elements_mat_def carrier_mat_def by force

lemma index_mat[simp]:  "i < nr \<Longrightarrow> j < nc \<Longrightarrow> mat nr nc f $$ (i,j) = f (i,j)"
  "i < nr \<Longrightarrow> j < nc \<Longrightarrow> mat\<^sub>r nr nc g $$ (i,j) = g i $ j"
  by (transfer', simp add: mk_mat_def)+

lemma eq_matI[intro]: "(\<And> i j . i < dim_row B \<Longrightarrow> j < dim_col B \<Longrightarrow> A $$ (i,j) = B $$ (i,j))
  \<Longrightarrow> dim_row A = dim_row B
  \<Longrightarrow> dim_col A = dim_col B
  \<Longrightarrow> A = B"
  by (transfer, auto intro!: cong_mk_mat, auto simp: mk_mat_def)

lemma carrier_matI[intro]:
  assumes "dim_row A = nr" "dim_col A = nc" shows  "A \<in> carrier_mat nr nc"
  using assms unfolding carrier_mat_def by auto

lemma carrier_matD[dest,simp]: assumes "A \<in> carrier_mat nr nc"
  shows "dim_row A = nr" "dim_col A = nc" using assms
  unfolding carrier_mat_def by auto

lemma cong_mat: assumes "nr = nr'" "nc = nc'" "\<And> i j. i < nr \<Longrightarrow> j < nc \<Longrightarrow>
  f (i,j) = f' (i,j)" shows "mat nr nc f = mat nr' nc' f'"
  by (rule eq_matI, insert assms, auto)

definition row :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec" where
  "row A i = vec (dim_col A) (\<lambda> j. A $$ (i,j))"

definition rows :: "'a mat \<Rightarrow> 'a vec list" where
  "rows A = map (row A) [0..<dim_row A]"

lemma row_carrier[simp]: "row A i \<in> carrier_vec (dim_col A)" unfolding row_def by auto

lemma rows_carrier[simp]: "set (rows A) \<subseteq> carrier_vec (dim_col A)" unfolding rows_def by auto

lemma length_rows[simp]: "length (rows A) = dim_row A" unfolding rows_def by auto

lemma nth_rows[simp]: "i < dim_row A \<Longrightarrow> rows A ! i = row A i"
  unfolding rows_def by auto

lemma row_mat_of_row_fun[simp]: "i < nr \<Longrightarrow> dim_vec (f i) = nc \<Longrightarrow> row (mat\<^sub>r nr nc f) i = f i"
  by (rule eq_vecI, auto simp: row_def)

lemma set_rows_carrier:
  assumes "A \<in> carrier_mat m n" and "v \<in> set (rows A)" shows "v \<in> carrier_vec n"
  using assms by (auto simp: rows_def row_def)

definition mat_of_rows :: "nat \<Rightarrow> 'a vec list \<Rightarrow> 'a mat"
  where "mat_of_rows n rs = mat (length rs) n (\<lambda>(i,j). rs ! i $ j)"

definition mat_of_rows_list :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat" where
  "mat_of_rows_list nc rs = mat (length rs) nc (\<lambda> (i,j). rs ! i ! j)"

lemma mat_of_rows_carrier[simp]:
  "mat_of_rows n vs \<in> carrier_mat (length vs) n"
  "dim_row (mat_of_rows n vs) = length vs"
  "dim_col (mat_of_rows n vs) = n"
  unfolding mat_of_rows_def by auto

lemma mat_of_rows_row[simp]:
  assumes i:"i < length vs" and n: "vs ! i \<in> carrier_vec n"
  shows "row (mat_of_rows n vs) i = vs ! i"
  unfolding mat_of_rows_def row_def using n i by auto

lemma rows_mat_of_rows[simp]:
  assumes "set vs \<subseteq> carrier_vec n" shows "rows (mat_of_rows n vs) = vs"
  unfolding rows_def apply (rule nth_equalityI)
  using assms unfolding subset_code(1) by auto

lemma mat_of_rows_rows[simp]:
  "mat_of_rows (dim_col A) (rows A) = A"
  unfolding mat_of_rows_def by (rule, auto simp: row_def)


definition col :: "'a mat \<Rightarrow> nat \<Rightarrow> 'a vec" where
  "col A j = vec (dim_row A) (\<lambda> i. A $$ (i,j))"

definition cols :: "'a mat \<Rightarrow> 'a vec list" where
  "cols A = map (col A) [0..<dim_col A]"

definition mat_of_cols :: "nat \<Rightarrow> 'a vec list \<Rightarrow> 'a mat"
  where "mat_of_cols n cs = mat n (length cs) (\<lambda>(i,j). cs ! j $ i)"

definition mat_of_cols_list :: "nat \<Rightarrow> 'a list list \<Rightarrow> 'a mat" where
  "mat_of_cols_list nr cs = mat nr (length cs) (\<lambda> (i,j). cs ! j ! i)"

lemma col_dim[simp]: "col A i \<in> carrier_vec (dim_row A)" unfolding col_def by auto

lemma dim_col[simp]: "dim_vec (col A i) = dim_row A" by auto

lemma cols_dim[simp]: "set (cols A) \<subseteq> carrier_vec (dim_row A)" unfolding cols_def by auto

lemma cols_length[simp]: "length (cols A) = dim_col A" unfolding cols_def by auto

lemma cols_nth[simp]: "i < dim_col A \<Longrightarrow> cols A ! i = col A i"
  unfolding cols_def by auto

lemma mat_of_cols_carrier[simp]:
  "mat_of_cols n vs \<in> carrier_mat n (length vs)"
  "dim_row (mat_of_cols n vs) = n"
  "dim_col (mat_of_cols n vs) = length vs"
  unfolding mat_of_cols_def by auto

lemma col_mat_of_cols[simp]:
  assumes j:"j < length vs" and n: "vs ! j \<in> carrier_vec n"
  shows "col (mat_of_cols n vs) j = vs ! j"
  unfolding mat_of_cols_def col_def using j n by auto

lemma cols_mat_of_cols[simp]:
  assumes "set vs \<subseteq> carrier_vec n" shows "cols (mat_of_cols n vs) = vs"
  unfolding cols_def apply(rule nth_equalityI)
  using assms unfolding subset_code(1) by auto

lemma mat_of_cols_cols[simp]:
  "mat_of_cols (dim_row A) (cols A) = A"
  unfolding mat_of_cols_def by (rule, auto simp: col_def)


instantiation mat :: (ord) ord
begin

definition less_eq_mat :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "less_eq_mat A B = (dim_row A = dim_row B \<and> dim_col A = dim_col B \<and> 
      (\<forall> i < dim_row B. \<forall> j < dim_col B. A $$ (i,j) \<le> B $$ (i,j)))" 

definition less_mat :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "less_mat A B = (A \<le> B \<and> \<not> (B \<le> A))"
instance ..
end

instantiation mat :: (preorder) preorder
begin
instance
proof (standard, auto simp: less_mat_def less_eq_mat_def, goal_cases)
  case (1 A B C i j)
  thus ?case using order_trans[of "A $$ (i,j)" "B $$ (i,j)" "C $$ (i,j)"] by auto
qed
end

instantiation mat :: (order) order
begin
instance
  by (standard, intro eq_matI, auto simp: less_eq_mat_def order.antisym)
end

instantiation mat :: (plus) plus
begin
definition plus_mat :: "('a :: plus) mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "A + B \<equiv> mat (dim_row B) (dim_col B) (\<lambda> ij. A $$ ij + B $$ ij)"
instance ..
end

definition map_mat :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a mat \<Rightarrow> 'b mat" where
  "map_mat f A \<equiv> mat (dim_row A) (dim_col A) (\<lambda> ij. f (A $$ ij))"

definition smult_mat :: "'a :: times \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixl "\<cdot>\<^sub>m" 70)
  where "a \<cdot>\<^sub>m A \<equiv> map_mat (\<lambda> b. a * b) A"

definition zero_mat :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero mat" ("0\<^sub>m") where
  "0\<^sub>m nr nc \<equiv> mat nr nc (\<lambda> ij. 0)"

lemma elements_0_mat [simp]: "elements_mat (0\<^sub>m nr nc) \<subseteq> {0}"
  unfolding elements_mat_def zero_mat_def by auto

definition transpose_mat :: "'a mat \<Rightarrow> 'a mat" where
  "transpose_mat A \<equiv> mat (dim_col A) (dim_row A) (\<lambda> (i,j). A $$ (j,i))"

definition one_mat :: "nat \<Rightarrow> 'a :: {zero,one} mat" ("1\<^sub>m") where
  "1\<^sub>m n \<equiv> mat n n (\<lambda> (i,j). if i = j then 1 else 0)"

instantiation mat :: (uminus) uminus
begin
definition uminus_mat :: "'a :: uminus mat \<Rightarrow> 'a mat" where
  "- A \<equiv> mat (dim_row A) (dim_col A) (\<lambda> ij. - (A $$ ij))"
instance ..
end

instantiation mat :: (minus) minus
begin
definition minus_mat :: "('a :: minus) mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "A - B \<equiv> mat (dim_row B) (dim_col B) (\<lambda> ij. A $$ ij - B $$ ij)"
instance ..
end

instantiation mat :: (semiring_0) times
begin
definition times_mat :: "'a :: semiring_0 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat"
  where "A * B \<equiv> mat (dim_row A) (dim_col B) (\<lambda> (i,j). row A i \<bullet> col B j)"
instance ..
end

definition mult_mat_vec :: "'a :: semiring_0 mat \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixl "*\<^sub>v" 70)
  where "A *\<^sub>v v \<equiv> vec (dim_row A) (\<lambda> i. row A i \<bullet> v)"

definition inverts_mat :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "inverts_mat A B \<equiv> A * B = 1\<^sub>m (dim_row A)"

definition invertible_mat :: "'a :: semiring_1 mat \<Rightarrow> bool"
  where "invertible_mat A \<equiv> square_mat A \<and> (\<exists>B. inverts_mat A B \<and> inverts_mat B A)"

definition monoid_mat :: "'a :: monoid_add itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a mat monoid" where
  "monoid_mat ty nr nc \<equiv> \<lparr>
    carrier = carrier_mat nr nc,
    mult = (+),
    one = 0\<^sub>m nr nc\<rparr>"

definition ring_mat :: "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> 'b \<Rightarrow> ('a mat,'b) ring_scheme" where
  "ring_mat ty n b \<equiv> \<lparr>
    carrier = carrier_mat n n,
    mult = (*),
    one = 1\<^sub>m n,
    zero = 0\<^sub>m n n,
    add = (+),
    \<dots> = b\<rparr>"

definition module_mat :: "'a :: semiring_1 itself \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a,'a mat)module" where
  "module_mat ty nr nc \<equiv> \<lparr>
    carrier = carrier_mat nr nc,
    mult = (*),
    one = 1\<^sub>m nr,
    zero = 0\<^sub>m nr nc,
    add = (+),
    smult = (\<cdot>\<^sub>m)\<rparr>"

lemma ring_mat_simps:
  "mult (ring_mat ty n b) = (*)"
  "add (ring_mat ty n b) = (+)"
  "one (ring_mat ty n b) = 1\<^sub>m n"
  "zero (ring_mat ty n b) = 0\<^sub>m n n"
  "carrier (ring_mat ty n b) = carrier_mat n n"
  unfolding ring_mat_def by auto

lemma module_mat_simps:
  "mult (module_mat ty nr nc) = (*)"
  "add (module_mat ty nr nc) = (+)"
  "one (module_mat ty nr nc) = 1\<^sub>m nr"
  "zero (module_mat ty nr nc) = 0\<^sub>m nr nc"
  "carrier (module_mat ty nr nc) = carrier_mat nr nc"
  "smult (module_mat ty nr nc) = (\<cdot>\<^sub>m)"
  unfolding module_mat_def by auto

lemma index_zero_mat[simp]: "i < nr \<Longrightarrow> j < nc \<Longrightarrow> 0\<^sub>m nr nc $$ (i,j) = 0"
  "dim_row (0\<^sub>m nr nc) = nr" "dim_col (0\<^sub>m nr nc) = nc"
  unfolding zero_mat_def by auto

lemma index_one_mat[simp]: "i < n \<Longrightarrow> j < n \<Longrightarrow> 1\<^sub>m n $$ (i,j) = (if i = j then 1 else 0)"
  "dim_row (1\<^sub>m n) = n" "dim_col (1\<^sub>m n) = n"
  unfolding one_mat_def by auto

lemma index_add_mat[simp]:
  "i < dim_row B \<Longrightarrow> j < dim_col B \<Longrightarrow> (A + B) $$ (i,j) = A $$ (i,j) + B $$ (i,j)"
  "dim_row (A + B) = dim_row B" "dim_col (A + B) = dim_col B"
  unfolding plus_mat_def by auto

lemma index_minus_mat[simp]:
  "i < dim_row B \<Longrightarrow> j < dim_col B \<Longrightarrow> (A - B) $$ (i,j) = A $$ (i,j) - B $$ (i,j)"
  "dim_row (A - B) = dim_row B" "dim_col (A - B) = dim_col B"
  unfolding minus_mat_def by auto

lemma index_map_mat[simp]:
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> map_mat f A $$ (i,j) = f (A $$ (i,j))"
  "dim_row (map_mat f A) = dim_row A" "dim_col (map_mat f A) = dim_col A"
  unfolding map_mat_def by auto

lemma index_smult_mat[simp]:
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> (a \<cdot>\<^sub>m A) $$ (i,j) = a * A $$ (i,j)"
  "dim_row (a \<cdot>\<^sub>m A) = dim_row A" "dim_col (a \<cdot>\<^sub>m A) = dim_col A"
  unfolding smult_mat_def by auto

lemma index_uminus_mat[simp]:
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> (- A) $$ (i,j) = - (A $$ (i,j))"
  "dim_row (- A) = dim_row A" "dim_col (- A) = dim_col A"
  unfolding uminus_mat_def by auto

lemma index_transpose_mat[simp]:
  "i < dim_col A \<Longrightarrow> j < dim_row A \<Longrightarrow> transpose_mat A $$ (i,j) = A $$ (j,i)"
  "dim_row (transpose_mat A) = dim_col A" "dim_col (transpose_mat A) = dim_row A"
  unfolding transpose_mat_def by auto

lemma index_mult_mat[simp]:
  "i < dim_row A \<Longrightarrow> j < dim_col B \<Longrightarrow> (A * B) $$ (i,j) = row A i \<bullet> col B j"
  "dim_row (A * B) = dim_row A" "dim_col (A * B) = dim_col B"
  by (auto simp: times_mat_def)

lemma dim_mult_mat_vec[simp]: "dim_vec (A *\<^sub>v v) = dim_row A"
  by (auto simp: mult_mat_vec_def)

lemma index_mult_mat_vec[simp]: "i < dim_row A \<Longrightarrow> (A *\<^sub>v v) $ i = row A i \<bullet> v"
  by (auto simp: mult_mat_vec_def)

lemma index_row[simp]:
  "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> row A i $ j = A $$ (i,j)"
  "dim_vec (row A i) = dim_col A"
  by (auto simp: row_def)

lemma index_col[simp]: "i < dim_row A \<Longrightarrow> j < dim_col A \<Longrightarrow> col A j $ i = A $$ (i,j)"
  by (auto simp: col_def)

lemma upper_triangular_one[simp]: "upper_triangular (1\<^sub>m n)"
  by (rule, auto)

lemma upper_triangular_zero[simp]: "upper_triangular (0\<^sub>m n n)"
  by (rule, auto)

lemma mat_row_carrierI[intro,simp]: "mat\<^sub>r nr nc r \<in> carrier_mat nr nc"
  by (unfold carrier_mat_def carrier_vec_def, auto)

lemma eq_rowI: assumes rows: "\<And> i. i < dim_row B \<Longrightarrow> row A i = row B i"
  and dims: "dim_row A = dim_row B" "dim_col A = dim_col B"
  shows "A = B"
proof (rule eq_matI[OF _ dims])
  fix i j
  assume i: "i < dim_row B" and j: "j < dim_col B"
  from rows[OF i] have id: "row A i $ j = row B i $ j" by simp
  show "A $$ (i, j) = B $$ (i, j)"
    using index_row(1)[OF i j, folded id] index_row(1)[of i A j] i j dims
    by auto
qed

lemma row_mat[simp]: "i < nr \<Longrightarrow> row (mat nr nc f) i = vec nc (\<lambda> j. f (i,j))"
  by auto

lemma col_mat[simp]: "j < nc \<Longrightarrow> col (mat nr nc f) j = vec nr (\<lambda> i. f (i,j))"
  by auto

lemma zero_carrier_mat[simp]: "0\<^sub>m nr nc \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by auto

lemma smult_carrier_mat[simp]:
  "A \<in> carrier_mat nr nc \<Longrightarrow> k \<cdot>\<^sub>m A \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by auto

lemma add_carrier_mat[simp]:
  "B \<in> carrier_mat nr nc \<Longrightarrow> A + B \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by force

lemma one_carrier_mat[simp]: "1\<^sub>m n \<in> carrier_mat n n"
  unfolding carrier_mat_def by auto

lemma uminus_carrier_mat:
  "A \<in> carrier_mat nr nc \<Longrightarrow> (- A \<in> carrier_mat nr nc)"
  unfolding carrier_mat_def by auto

lemma uminus_carrier_iff_mat[simp]:
  "(- A \<in> carrier_mat nr nc) = (A \<in> carrier_mat nr nc)"
  unfolding carrier_mat_def by auto

lemma minus_carrier_mat:
  "B \<in> carrier_mat nr nc \<Longrightarrow> (A - B \<in> carrier_mat nr nc)"
  unfolding carrier_mat_def by auto

lemma transpose_carrier_mat[simp]: "(transpose_mat A \<in> carrier_mat nc nr) = (A \<in> carrier_mat nr nc)"
  unfolding carrier_mat_def by auto

lemma row_carrier_vec[simp]: "i < nr \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> row A i \<in> carrier_vec nc"
  unfolding carrier_vec_def by auto

lemma col_carrier_vec[simp]: "j < nc \<Longrightarrow> A \<in> carrier_mat nr nc \<Longrightarrow> col A j \<in> carrier_vec nr"
  unfolding carrier_vec_def by auto

lemma mult_carrier_mat[simp]:
  "A \<in> carrier_mat nr n \<Longrightarrow> B \<in> carrier_mat n nc \<Longrightarrow> A * B \<in> carrier_mat nr nc"
  unfolding carrier_mat_def by auto

lemma mult_mat_vec_carrier[simp]:
  "A \<in> carrier_mat nr n \<Longrightarrow> v \<in> carrier_vec n \<Longrightarrow> A *\<^sub>v v \<in> carrier_vec nr"
  unfolding carrier_mat_def carrier_vec_def by auto


lemma comm_add_mat[ac_simps]:
  "(A :: 'a :: comm_monoid_add mat) \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> A + B = B + A"
  by (intro eq_matI, auto simp: ac_simps)


lemma minus_r_inv_mat[simp]:
  "(A :: 'a :: group_add mat) \<in> carrier_mat nr nc \<Longrightarrow> (A - A) = 0\<^sub>m nr nc"
  by (intro eq_matI, auto)

lemma uminus_l_inv_mat[simp]:
  "(A :: 'a :: group_add mat) \<in> carrier_mat nr nc \<Longrightarrow> (- A + A) = 0\<^sub>m nr nc"
  by (intro eq_matI, auto)

lemma add_inv_exists_mat:
  "(A :: 'a :: group_add mat) \<in> carrier_mat nr nc \<Longrightarrow> \<exists> B \<in> carrier_mat nr nc. B + A = 0\<^sub>m nr nc \<and> A + B = 0\<^sub>m nr nc"
  by (intro bexI[of _ "- A"], auto)

lemma assoc_add_mat[simp]:
  "(A :: 'a :: monoid_add mat) \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> C \<in> carrier_mat nr nc
  \<Longrightarrow> (A + B) + C = A + (B + C)"
  by (intro eq_matI, auto simp: ac_simps)

lemma uminus_add_mat: fixes A :: "'a :: group_add mat"
  assumes "A \<in> carrier_mat nr nc"
  and "B \<in> carrier_mat nr nc"
  shows "- (A + B) = - B + - A"
  by (intro eq_matI, insert assms, auto simp: minus_add)

lemma transpose_transpose[simp]:
  "transpose_mat (transpose_mat A) = A"
  by (intro eq_matI, auto)

lemma transpose_one[simp]: "transpose_mat (1\<^sub>m n) = (1\<^sub>m n)"
  by auto

lemma row_transpose[simp]:
  "j < dim_col A \<Longrightarrow> row (transpose_mat A) j = col A j"
  unfolding row_def col_def
  by (intro eq_vecI, auto)

lemma col_transpose[simp]:
  "i < dim_row A \<Longrightarrow> col (transpose_mat A) i = row A i"
  unfolding row_def col_def
  by (intro eq_vecI, auto)

lemma row_zero[simp]:
  "i < nr \<Longrightarrow> row (0\<^sub>m nr nc) i = 0\<^sub>v nc"
   by (intro eq_vecI, auto)

lemma col_zero[simp]:
  "j < nc \<Longrightarrow> col (0\<^sub>m nr nc) j = 0\<^sub>v nr"
   by (intro eq_vecI, auto)

lemma row_one[simp]:
  "i < n \<Longrightarrow> row (1\<^sub>m n) i = unit_vec n i"
  by (intro eq_vecI, auto)

lemma col_one[simp]:
  "j < n \<Longrightarrow> col (1\<^sub>m n) j = unit_vec n j"
  by (intro eq_vecI, auto)

lemma transpose_add: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc
  \<Longrightarrow> transpose_mat (A + B) = transpose_mat A + transpose_mat B"
  by (intro eq_matI, auto)

lemma transpose_minus: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc
  \<Longrightarrow> transpose_mat (A - B) = transpose_mat A - transpose_mat B"
  by (intro eq_matI, auto)

lemma transpose_uminus: "A \<in> carrier_mat nr nc \<Longrightarrow> transpose_mat (- A) = - (transpose_mat A)"
  by (intro eq_matI, auto)

lemma row_add[simp]:
  "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> i < nr
  \<Longrightarrow> row (A + B) i = row A i + row B i"
  "i < dim_row A \<Longrightarrow> dim_row B = dim_row A \<Longrightarrow> dim_col B = dim_col A \<Longrightarrow> row (A + B) i = row A i + row B i"
  by (rule eq_vecI, auto)

lemma col_add[simp]:
  "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> j < nc
  \<Longrightarrow> col (A + B) j = col A j + col B j"
  by (rule eq_vecI, auto)

lemma row_mult[simp]: assumes m: "A \<in> carrier_mat nr n" "B \<in> carrier_mat n nc"
  and i: "i < nr"
  shows "row (A * B) i = vec nc (\<lambda> j. row A i \<bullet> col B j)"
  by (rule eq_vecI, insert m i, auto)

lemma col_mult[simp]: assumes m: "A \<in> carrier_mat nr n" "B \<in> carrier_mat n nc"
  and j: "j < nc"
  shows "col (A * B) j = vec nr (\<lambda> i. row A i \<bullet> col B j)"
  by (rule eq_vecI, insert m j, auto)

lemma transpose_mult:
  "(A :: 'a :: comm_semiring_0 mat) \<in> carrier_mat nr n \<Longrightarrow> B \<in> carrier_mat n nc
  \<Longrightarrow> transpose_mat (A * B) = transpose_mat B * transpose_mat A"
  by (intro eq_matI, auto simp: comm_scalar_prod[of _ n])

lemma left_add_zero_mat[simp]:
  "(A :: 'a :: monoid_add mat) \<in> carrier_mat nr nc  \<Longrightarrow> 0\<^sub>m nr nc + A = A"
  by (intro eq_matI, auto)

lemma add_uminus_minus_mat: "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow> 
  A + (- B) = A - (B :: 'a :: group_add mat)" 
  by (intro eq_matI, auto)

lemma right_add_zero_mat[simp]: "A \<in> carrier_mat nr nc \<Longrightarrow> 
  A + 0\<^sub>m nr nc = (A :: 'a :: monoid_add mat)" 
  by (intro eq_matI, auto)

lemma left_mult_zero_mat:
  "A \<in> carrier_mat n nc \<Longrightarrow> 0\<^sub>m nr n * A = 0\<^sub>m nr nc"
  by (intro eq_matI, auto)

lemma left_mult_zero_mat'[simp]: "dim_row A = n \<Longrightarrow> 0\<^sub>m nr n * A = 0\<^sub>m nr (dim_col A)"
  by (rule left_mult_zero_mat, unfold carrier_mat_def, simp)

lemma right_mult_zero_mat:
  "A \<in> carrier_mat nr n \<Longrightarrow> A * 0\<^sub>m n nc = 0\<^sub>m nr nc"
  by (intro eq_matI, auto)

lemma right_mult_zero_mat'[simp]: "dim_col A = n \<Longrightarrow> A * 0\<^sub>m n nc = 0\<^sub>m (dim_row A) nc"
  by (rule right_mult_zero_mat, unfold carrier_mat_def, simp)

lemma left_mult_one_mat:
  "(A :: 'a :: semiring_1 mat) \<in> carrier_mat nr nc \<Longrightarrow> 1\<^sub>m nr * A = A"
  by (intro eq_matI, auto)

lemma left_mult_one_mat'[simp]: "dim_row (A :: 'a :: semiring_1 mat) = n \<Longrightarrow> 1\<^sub>m n * A = A"
  by (rule left_mult_one_mat, unfold carrier_mat_def, simp)

lemma right_mult_one_mat:
  "(A :: 'a :: semiring_1 mat) \<in> carrier_mat nr nc \<Longrightarrow> A * 1\<^sub>m nc = A"
  by (intro eq_matI, auto)

lemma right_mult_one_mat'[simp]: "dim_col (A :: 'a :: semiring_1 mat) = n \<Longrightarrow> A * 1\<^sub>m n = A"
  by (rule right_mult_one_mat, unfold carrier_mat_def, simp)

lemma one_mult_mat_vec[simp]:
  "(v :: 'a :: semiring_1 vec) \<in> carrier_vec n \<Longrightarrow> 1\<^sub>m n *\<^sub>v v = v"
  by (intro eq_vecI, auto)

lemma minus_add_uminus_mat: fixes A :: "'a :: group_add mat"
  shows "A \<in> carrier_mat nr nc \<Longrightarrow> B \<in> carrier_mat nr nc \<Longrightarrow>
  A - B = A + (- B)"
  by (intro eq_matI, auto)

lemma add_mult_distrib_mat[algebra_simps]: assumes m: "A \<in> carrier_mat nr n"
  "B \<in> carrier_mat nr n" "C \<in> carrier_mat n nc"
  shows "(A + B) * C = A * C + B * C"
  using m by (intro eq_matI, auto simp: add_scalar_prod_distrib[of _ n])

lemma mult_add_distrib_mat[algebra_simps]: assumes m: "A \<in> carrier_mat nr n"
  "B \<in> carrier_mat n nc" "C \<in> carrier_mat n nc"
  shows "A * (B + C) = A * B + A * C"
  using m by (intro eq_matI, auto simp: scalar_prod_add_distrib[of _ n])

lemma add_mult_distrib_mat_vec[algebra_simps]: assumes m: "A \<in> carrier_mat nr nc"
  "B \<in> carrier_mat nr nc" "v \<in> carrier_vec nc"
  shows "(A + B) *\<^sub>v v = A *\<^sub>v v + B *\<^sub>v v"
  using m by (intro eq_vecI, auto intro!: add_scalar_prod_distrib)

lemma mult_add_distrib_mat_vec[algebra_simps]: assumes m: "A \<in> carrier_mat nr nc"
  "v\<^sub>1 \<in> carrier_vec nc" "v\<^sub>2 \<in> carrier_vec nc"
  shows "A *\<^sub>v (v\<^sub>1 + v\<^sub>2) = A *\<^sub>v v\<^sub>1 + A *\<^sub>v v\<^sub>2"
  using m by (intro eq_vecI, auto simp: scalar_prod_add_distrib[of _ nc])

lemma mult_mat_vec:
  assumes m: "(A::'a::field mat) \<in> carrier_mat nr nc" and v: "v \<in> carrier_vec nc"
  shows "A *\<^sub>v (k \<cdot>\<^sub>v v) = k \<cdot>\<^sub>v (A *\<^sub>v v)" (is "?l = ?r")
proof
  have nr: "dim_vec ?l = nr" using m v by auto
  also have "... = dim_vec ?r" using m v by auto
  finally show "dim_vec ?l = dim_vec ?r".

  show "\<And>i. i < dim_vec ?r \<Longrightarrow> ?l $ i = ?r $ i"
  proof -
    fix i assume "i < dim_vec ?r"
    hence i: "i < dim_row A" using nr m by auto
    hence i2: "i < dim_vec (A *\<^sub>v v)" using m by auto
    show "?l $ i = ?r $ i"
    apply (subst (1) mult_mat_vec_def)
    apply (subst (2) smult_vec_def)
    unfolding index_vec[OF i] index_vec[OF i2]
    unfolding mult_mat_vec_def smult_vec_def
    unfolding scalar_prod_def index_vec[OF i]
    by (simp add: mult.left_commute sum_distrib_left)
  qed
qed

lemma assoc_scalar_prod: assumes *: "v\<^sub>1 \<in> carrier_vec nr" "A \<in> carrier_mat nr nc" "v\<^sub>2 \<in> carrier_vec nc"
  shows "vec nc (\<lambda>j. v\<^sub>1 \<bullet> col A j) \<bullet> v\<^sub>2 = v\<^sub>1 \<bullet> vec nr (\<lambda>i. row A i \<bullet> v\<^sub>2)"
proof -
  have "vec nc (\<lambda>j. v\<^sub>1 \<bullet> col A j) \<bullet> v\<^sub>2 = (\<Sum>i\<in>{0..<nc}. vec nc (\<lambda>j. \<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A j $ k) $ i * v\<^sub>2 $ i)"
    unfolding scalar_prod_def using * by auto
  also have "\<dots> = (\<Sum>i\<in>{0..<nc}. (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A i $ k) * v\<^sub>2 $ i)"
    by (rule sum.cong, auto)
  also have "\<dots> = (\<Sum>i\<in>{0..<nc}. (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * col A i $ k * v\<^sub>2 $ i))"
    unfolding sum_distrib_right ..
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. (\<Sum>i\<in>{0..<nc}. v\<^sub>1 $ k * col A i $ k * v\<^sub>2 $ i))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. (\<Sum>i\<in>{0..<nc}. v\<^sub>1 $ k * (col A i $ k * v\<^sub>2 $ i)))"
    by (simp add: ac_simps)
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * (\<Sum>i\<in>{0..<nc}. col A i $ k * v\<^sub>2 $ i))"
    unfolding sum_distrib_left ..
  also have "\<dots> = (\<Sum>k\<in>{0..<nr}. v\<^sub>1 $ k * vec nr (\<lambda>k. \<Sum>i\<in>{0..<nc}. row A k $ i * v\<^sub>2 $ i) $ k)"
    using * by auto
  also have "\<dots> = v\<^sub>1 \<bullet> vec nr (\<lambda>i. row A i \<bullet> v\<^sub>2)" unfolding scalar_prod_def using * by simp
  finally show ?thesis .
qed

lemma assoc_mult_mat[simp]:
  "A \<in> carrier_mat n\<^sub>1 n\<^sub>2 \<Longrightarrow> B \<in> carrier_mat n\<^sub>2 n\<^sub>3 \<Longrightarrow> C \<in> carrier_mat n\<^sub>3 n\<^sub>4
  \<Longrightarrow> (A * B) * C = A * (B * C)"
  by (intro eq_matI, auto simp: assoc_scalar_prod)

lemma assoc_mult_mat_vec[simp]:
  "A \<in> carrier_mat n\<^sub>1 n\<^sub>2 \<Longrightarrow> B \<in> carrier_mat n\<^sub>2 n\<^sub>3 \<Longrightarrow> v \<in> carrier_vec n\<^sub>3
  \<Longrightarrow> (A * B) *\<^sub>v v = A *\<^sub>v (B *\<^sub>v v)"
  by (intro eq_vecI, auto simp add: mult_mat_vec_def assoc_scalar_prod)

lemma comm_monoid_mat: "comm_monoid (monoid_mat TYPE('a :: comm_monoid_add) nr nc)"
  by (unfold_locales, auto simp: monoid_mat_def ac_simps)

lemma comm_group_mat: "comm_group (monoid_mat TYPE('a :: ab_group_add) nr nc)"
  by (unfold_locales, insert add_inv_exists_mat, auto simp: monoid_mat_def ac_simps Units_def)

lemma semiring_mat: "semiring (ring_mat TYPE('a :: semiring_1) n b)"
  by (unfold_locales, auto simp: ring_mat_def algebra_simps)

lemma ring_mat: "ring (ring_mat TYPE('a :: comm_ring_1) n b)"
  by (unfold_locales, insert add_inv_exists_mat, auto simp: ring_mat_def algebra_simps Units_def)

lemma abelian_group_mat: "abelian_group (module_mat TYPE('a :: comm_ring_1) nr nc)"
  by (unfold_locales, insert add_inv_exists_mat, auto simp: module_mat_def Units_def)

lemma row_smult[simp]: assumes i: "i < dim_row A"
  shows "row (k \<cdot>\<^sub>m A) i = k \<cdot>\<^sub>v (row A i)"
  by (rule eq_vecI, insert i, auto)

lemma col_smult[simp]: assumes i: "i < dim_col A"
  shows "col (k \<cdot>\<^sub>m A) i = k \<cdot>\<^sub>v (col A i)"
  by (rule eq_vecI, insert i, auto)

lemma row_uminus[simp]: assumes i: "i < dim_row A"
  shows "row (- A) i = - (row A i)"
  by (rule eq_vecI, insert i, auto)

lemma scalar_prod_uminus_left[simp]: assumes dim: "dim_vec v = dim_vec (w :: 'a :: ring vec)"
  shows "- v \<bullet> w = - (v \<bullet> w)"
  unfolding scalar_prod_def dim[symmetric]
  by (subst sum_negf[symmetric], rule sum.cong, auto)

lemma col_uminus[simp]: assumes i: "i < dim_col A"
  shows "col (- A) i = - (col A i)"
  by (rule eq_vecI, insert i, auto)

lemma scalar_prod_uminus_right[simp]: assumes dim: "dim_vec v = dim_vec (w :: 'a :: ring vec)"
  shows "v \<bullet> - w = - (v \<bullet> w)"
  unfolding scalar_prod_def dim
  by (subst sum_negf[symmetric], rule sum.cong, auto)

context fixes A B :: "'a :: ring mat"
  assumes dim: "dim_col A = dim_row B"
begin
lemma uminus_mult_left_mat[simp]: "(- A * B) = - (A * B)"
  by (intro eq_matI, insert dim, auto)

lemma uminus_mult_right_mat[simp]: "(A * - B) = - (A * B)"
  by (intro eq_matI, insert dim, auto)
end

lemma minus_mult_distrib_mat[algebra_simps]: fixes A :: "'a :: ring mat"
  assumes m: "A \<in> carrier_mat nr n" "B \<in> carrier_mat nr n" "C \<in> carrier_mat n nc"
  shows "(A - B) * C = A * C - B * C"
  unfolding minus_add_uminus_mat[OF m(1,2)]
    add_mult_distrib_mat[OF m(1) uminus_carrier_mat[OF m(2)] m(3)]
  by (subst uminus_mult_left_mat, insert m, auto)

lemma minus_mult_distrib_mat_vec[algebra_simps]: assumes A: "(A :: 'a :: ring mat) \<in> carrier_mat nr nc"
  and B: "B \<in> carrier_mat nr nc"
  and v: "v \<in> carrier_vec nc"
shows "(A - B) *\<^sub>v v = A *\<^sub>v v - B *\<^sub>v v"
  unfolding minus_add_uminus_mat[OF A B]
  by (subst add_mult_distrib_mat_vec[OF A _ v], insert A B v, auto)

lemma mult_minus_distrib_mat_vec[algebra_simps]: assumes A: "(A :: 'a :: ring mat) \<in> carrier_mat nr nc"
  and v: "v \<in> carrier_vec nc"
  and w: "w \<in> carrier_vec nc"
shows "A *\<^sub>v (v - w) = A *\<^sub>v v - A *\<^sub>v w"
  unfolding minus_add_uminus_vec[OF v w]
  by (subst mult_add_distrib_mat_vec[OF A], insert A v w, auto)

lemma mult_minus_distrib_mat[algebra_simps]: fixes A :: "'a :: ring mat"
  assumes m: "A \<in> carrier_mat nr n" "B \<in> carrier_mat n nc" "C \<in> carrier_mat n nc"
  shows "A * (B - C) = A * B - A * C"
  unfolding minus_add_uminus_mat[OF m(2,3)]
    mult_add_distrib_mat[OF m(1) m(2) uminus_carrier_mat[OF m(3)]]
  by (subst uminus_mult_right_mat, insert m, auto)

lemma uminus_mult_mat_vec[simp]: assumes v: "dim_vec v = dim_col (A :: 'a :: ring mat)"
  shows "- A *\<^sub>v v = - (A *\<^sub>v v)"
  using v by (intro eq_vecI, auto)

lemma uminus_zero_vec_eq: assumes v: "(v :: 'a :: group_add vec) \<in> carrier_vec n"
  shows "(- v = 0\<^sub>v n) = (v = 0\<^sub>v n)"
proof
  assume z: "- v = 0\<^sub>v n"
  {
    fix i
    assume i: "i < n"
    have "v $ i = - (- (v $ i))" by simp
    also have "- (v $ i) = 0" using arg_cong[OF z, of "\<lambda> v. v $ i"] i v by auto
    also have "- 0 = (0 :: 'a)" by simp
    finally have "v $ i = 0" .
  }
  thus "v = 0\<^sub>v n" using v
    by (intro eq_vecI, auto)
qed auto

lemma map_carrier_mat[simp]:
  "(map_mat f A \<in> carrier_mat nr nc) = (A \<in> carrier_mat nr nc)"
  unfolding carrier_mat_def by auto

lemma col_map_mat[simp]:
  assumes "j < dim_col A" shows "col (map_mat f A) j = map_vec f (col A j)"
  unfolding map_mat_def map_vec_def using assms by auto

lemma scalar_vec_one[simp]: "1 \<cdot>\<^sub>v (v :: 'a :: semiring_1 vec) = v"
  by (rule eq_vecI, auto)

lemma scalar_prod_smult_right[simp]:
  "dim_vec w = dim_vec v \<Longrightarrow> w \<bullet> (k \<cdot>\<^sub>v v) = (k :: 'a :: comm_semiring_0) * (w \<bullet> v)"
  unfolding scalar_prod_def sum_distrib_left
  by (auto intro: sum.cong simp: ac_simps)

lemma scalar_prod_smult_left[simp]:
  "dim_vec w = dim_vec v \<Longrightarrow> (k \<cdot>\<^sub>v w) \<bullet> v = (k :: 'a :: comm_semiring_0) * (w \<bullet> v)"
  unfolding scalar_prod_def sum_distrib_left
  by (auto intro: sum.cong simp: ac_simps)

lemma mult_smult_distrib: assumes A: "A \<in> carrier_mat nr n" and B: "B \<in> carrier_mat n nc"
  shows "A * (k \<cdot>\<^sub>m B) = (k :: 'a :: comm_semiring_0) \<cdot>\<^sub>m (A * B)"
  by (rule eq_matI, insert A B, auto)

lemma add_smult_distrib_left_mat: assumes "A \<in> carrier_mat nr nc" "B \<in> carrier_mat nr nc"
  shows "k \<cdot>\<^sub>m (A + B) = (k :: 'a :: semiring) \<cdot>\<^sub>m A + k \<cdot>\<^sub>m B"
  by (rule eq_matI, insert assms, auto simp: field_simps)

lemma add_smult_distrib_right_mat: assumes "A \<in> carrier_mat nr nc"
  shows "(k + l) \<cdot>\<^sub>m A = (k :: 'a :: semiring) \<cdot>\<^sub>m A + l \<cdot>\<^sub>m A"
  by (rule eq_matI, insert assms, auto simp: field_simps)

lemma mult_smult_assoc_mat: assumes A: "A \<in> carrier_mat nr n" and B: "B \<in> carrier_mat n nc"
  shows "(k \<cdot>\<^sub>m A) * B = (k :: 'a :: comm_semiring_0) \<cdot>\<^sub>m (A * B)"
  by (rule eq_matI, insert A B, auto)

definition similar_mat_wit :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "similar_mat_wit A B P Q = (let n = dim_row A in {A,B,P,Q} \<subseteq> carrier_mat n n \<and> P * Q = 1\<^sub>m n \<and> Q * P = 1\<^sub>m n \<and>
    A = P * B * Q)"

definition similar_mat :: "'a :: semiring_1 mat \<Rightarrow> 'a mat \<Rightarrow> bool" where
  "similar_mat A B = (\<exists> P Q. similar_mat_wit A B P Q)"

lemma similar_matD: assumes "similar_mat A B"
  shows "\<exists> n P Q. {A,B,P,Q} \<subseteq> carrier_mat n n \<and> P * Q = 1\<^sub>m n \<and> Q * P = 1\<^sub>m n \<and> A = P * B * Q"
  using assms unfolding similar_mat_def similar_mat_wit_def[abs_def] Let_def by blast

lemma similar_matI: assumes "{A,B,P,Q} \<subseteq> carrier_mat n n" "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" "A = P * B * Q"
  shows "similar_mat A B" unfolding similar_mat_def
  by (rule exI[of _ P], rule exI[of _ Q], unfold similar_mat_wit_def Let_def, insert assms, auto)

fun pow_mat :: "'a :: semiring_1 mat \<Rightarrow> nat \<Rightarrow> 'a mat" (infixr "^\<^sub>m" 75) where
  "A ^\<^sub>m 0 = 1\<^sub>m (dim_row A)"
| "A ^\<^sub>m (Suc k) = A ^\<^sub>m k * A"

lemma pow_mat_dim[simp]:
  "dim_row (A ^\<^sub>m k) = dim_row A"
  "dim_col (A ^\<^sub>m k) = (if k = 0 then dim_row A else dim_col A)"
  by (induct k, auto)

lemma pow_mat_dim_square[simp]:
  "A \<in> carrier_mat n n \<Longrightarrow> dim_row (A ^\<^sub>m k) = n"
  "A \<in> carrier_mat n n \<Longrightarrow> dim_col (A ^\<^sub>m k) = n"
  by auto

lemma pow_carrier_mat[simp]: "A \<in> carrier_mat n n \<Longrightarrow> A ^\<^sub>m k \<in> carrier_mat n n"
  unfolding carrier_mat_def by auto

definition diag_mat :: "'a mat \<Rightarrow> 'a list" where
  "diag_mat A = map (\<lambda> i. A $$ (i,i)) [0 ..< dim_row A]"

lemma prod_list_diag_prod: "prod_list (diag_mat A) = (\<Prod> i = 0 ..< dim_row A. A $$ (i,i))"
  unfolding diag_mat_def
  by (subst prod.distinct_set_conv_list[symmetric], auto)

lemma diag_mat_transpose[simp]: "dim_row A = dim_col A \<Longrightarrow>
  diag_mat (transpose_mat A) = diag_mat A" unfolding diag_mat_def by auto

lemma diag_mat_zero[simp]: "diag_mat (0\<^sub>m n n) = replicate n 0"
  unfolding diag_mat_def
  by (rule nth_equalityI, auto)

lemma diag_mat_one[simp]: "diag_mat (1\<^sub>m n) = replicate n 1"
  unfolding diag_mat_def
  by (rule nth_equalityI, auto)

lemma pow_mat_ring_pow: assumes A: "(A :: ('a :: semiring_1)mat) \<in> carrier_mat n n"
  shows "A ^\<^sub>m k = A [^]\<^bsub>ring_mat TYPE('a) n b\<^esub> k"
  (is "_ = A [^]\<^bsub>?C\<^esub> k")
proof -
  interpret semiring ?C by (rule semiring_mat)
  show ?thesis
    by (induct k, insert A, auto simp: ring_mat_def nat_pow_def)
qed

definition diagonal_mat :: "'a::zero mat \<Rightarrow> bool" where
  "diagonal_mat A \<equiv> \<forall>i<dim_row A. \<forall>j<dim_col A. i \<noteq> j \<longrightarrow> A $$ (i,j) = 0"

definition (in comm_monoid_add) sum_mat :: "'a mat \<Rightarrow> 'a" where
  "sum_mat A = sum (\<lambda> ij. A $$ ij) ({0 ..< dim_row A} \<times> {0 ..< dim_col A})"

lemma sum_mat_0[simp]: "sum_mat (0\<^sub>m nr nc) = (0 :: 'a :: comm_monoid_add)"
  unfolding sum_mat_def
  by (rule sum.neutral, auto)

lemma sum_mat_add: assumes A: "(A :: 'a :: comm_monoid_add mat) \<in> carrier_mat nr nc" and B: "B \<in> carrier_mat nr nc"
  shows "sum_mat (A + B) = sum_mat A + sum_mat B"
proof -
  from A B have id: "dim_row A = nr" "dim_row B = nr" "dim_col A = nc" "dim_col B = nc"
    by auto
  show ?thesis unfolding sum_mat_def id
    by (subst sum.distrib[symmetric], rule sum.cong, insert A B, auto)
qed

subsection \<open>Update Operators\<close>

definition update_vec :: "'a vec \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a vec" ("_ |\<^sub>v _ \<mapsto> _" [60,61,62] 60)
  where "v |\<^sub>v i \<mapsto> a = vec (dim_vec v) (\<lambda>i'. if i' = i then a else v $ i')"

definition update_mat :: "'a mat \<Rightarrow> nat \<times> nat \<Rightarrow> 'a \<Rightarrow> 'a mat" ("_ |\<^sub>m _ \<mapsto> _" [60,61,62] 60)
  where "A |\<^sub>m ij \<mapsto> a = mat (dim_row A) (dim_col A) (\<lambda>ij'. if ij' = ij then a else A $$ ij')"

lemma dim_update_vec[simp]:
  "dim_vec (v |\<^sub>v i \<mapsto> a) = dim_vec v" unfolding update_vec_def by simp

lemma index_update_vec1[simp]:
  assumes "i < dim_vec v" shows "(v |\<^sub>v i \<mapsto> a) $ i = a"
  unfolding update_vec_def using assms by simp

lemma index_update_vec2[simp]:
  assumes "i' \<noteq> i" shows "(v |\<^sub>v i \<mapsto> a) $ i' = v $ i'"
  unfolding update_vec_def
  using assms apply transfer unfolding mk_vec_def by auto

lemma dim_update_mat[simp]:
  "dim_row (A |\<^sub>m ij \<mapsto> a) = dim_row A"
  "dim_col (A |\<^sub>m ij \<mapsto> a) = dim_col A" unfolding update_mat_def by simp+

lemma index_update_mat1[simp]:
  assumes "i < dim_row A" "j < dim_col A" shows "(A |\<^sub>m (i,j) \<mapsto> a) $$ (i,j) = a"
  unfolding update_mat_def using assms by simp

lemma index_update_mat2[simp]:
  assumes i': "i' < dim_row A" and j': "j' < dim_col A" and neq: "(i',j') \<noteq> ij"
  shows "(A |\<^sub>m ij \<mapsto> a) $$ (i',j') = A $$ (i',j')"
  unfolding update_mat_def using assms by auto

subsection \<open>Block Vectors and Matrices\<close>

definition append_vec :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a vec" (infixr "@\<^sub>v" 65) where
  "v @\<^sub>v w \<equiv> let n = dim_vec v; m = dim_vec w in
    vec (n + m) (\<lambda> i. if i < n then v $ i else w $ (i - n))"

lemma index_append_vec[simp]: "i < dim_vec v + dim_vec w
  \<Longrightarrow> (v @\<^sub>v w) $ i = (if i < dim_vec v then v $ i else w $ (i - dim_vec v))"
  "dim_vec (v @\<^sub>v w) = dim_vec v + dim_vec w"
  unfolding append_vec_def Let_def by auto

lemma append_carrier_vec[simp,intro]:
  "v \<in> carrier_vec n1 \<Longrightarrow> w \<in> carrier_vec n2 \<Longrightarrow> v @\<^sub>v w \<in> carrier_vec (n1 + n2)"
  unfolding carrier_vec_def by auto

lemma scalar_prod_append: assumes "v1 \<in> carrier_vec n1" "v2 \<in> carrier_vec n2"
  "w1 \<in> carrier_vec n1" "w2 \<in> carrier_vec n2"
  shows "(v1 @\<^sub>v v2) \<bullet> (w1 @\<^sub>v w2) = v1 \<bullet> w1 + v2 \<bullet> w2"
proof -
  from assms have dim: "dim_vec v1 = n1" "dim_vec v2 = n2" "dim_vec w1 = n1" "dim_vec w2 = n2" by auto
  have id: "{0 ..< n1 + n2} = {0 ..< n1} \<union> {n1 ..< n1 + n2}" by auto
  have id2: "{n1 ..< n1 + n2} = (plus n1) ` {0 ..< n2}"
    by (simp add: ac_simps)
  have "(v1 @\<^sub>v v2) \<bullet> (w1 @\<^sub>v w2) = (\<Sum>i = 0..<n1. v1 $ i * w1 $ i) +
    (\<Sum>i = n1..<n1 + n2. v2 $ (i - n1) * w2 $ (i - n1))"
  unfolding scalar_prod_def
    by (auto simp: dim id, subst sum.union_disjoint, insert assms, force+)
  also have "(\<Sum>i = n1..<n1 + n2. v2 $ (i - n1) * w2 $ (i - n1))
    = (\<Sum>i = 0..< n2. v2 $ i * w2 $ i)"
    by (rule sum.reindex_cong [OF _ id2]) simp_all
  finally show ?thesis by (simp, insert assms, auto simp: scalar_prod_def)
qed

definition "vec_first v n \<equiv> vec n (\<lambda>i. v $ i)"
definition "vec_last v n \<equiv> vec n (\<lambda>i. v $ (dim_vec v - n + i))"

lemma dim_vec_first[simp]: "dim_vec (vec_first v n) = n" unfolding vec_first_def by auto
lemma dim_vec_last[simp]: "dim_vec (vec_last v n) = n" unfolding vec_last_def by auto

lemma vec_first_carrier[simp]: "vec_first v n \<in> carrier_vec n" by (rule carrier_vecI, auto)
lemma vec_last_carrier[simp]: "vec_last v n \<in> carrier_vec n" by (rule carrier_vecI, auto)

lemma vec_first_last_append[simp]:
  assumes "v \<in> carrier_vec (n+m)" shows "vec_first v n @\<^sub>v vec_last v m = v"
  apply(rule) unfolding vec_first_def vec_last_def using assms by auto

lemma append_vec_le: assumes "v \<in> carrier_vec n" and w: "w \<in> carrier_vec n" 
  shows "v @\<^sub>v v' \<le> w @\<^sub>v w' \<longleftrightarrow> v \<le> w \<and> v' \<le> w'" 
proof -
  {
    fix i
    assume *: "\<forall>i. (\<not> i < n \<longrightarrow> i < n + dim_vec w' \<longrightarrow> v' $ (i - n) \<le> w' $ (i - n))"
      and i: "i < dim_vec w'" 
    have "v' $ i \<le> w' $ i" using *[rule_format, of "n + i"] i by auto
  }
  thus ?thesis using assms unfolding less_eq_vec_def by auto
qed

lemma all_vec_append: "(\<forall> x \<in> carrier_vec (n + m). P x) \<longleftrightarrow> (\<forall> x1 \<in> carrier_vec n. \<forall> x2 \<in> carrier_vec m. P (x1 @\<^sub>v x2))" 
proof (standard, force, intro ballI, goal_cases)
  case (1 x)
  have "x = vec n (\<lambda> i. x $ i) @\<^sub>v vec m (\<lambda> i. x $ (n + i))" 
    by (rule eq_vecI, insert 1(2), auto)
  hence "P x = P (vec n (\<lambda> i. x $ i) @\<^sub>v vec m (\<lambda> i. x $ (n + i)))" by simp
  also have "\<dots>" using 1 by auto
  finally show ?case .
qed


(* A B
   C D *)
definition four_block_mat :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" where
  "four_block_mat A B C D =
    (let nra = dim_row A; nrd = dim_row D;
         nca = dim_col A; ncd = dim_col D
       in
    mat (nra + nrd) (nca + ncd) (\<lambda> (i,j). if i < nra then
      if j < nca then A $$ (i,j) else B $$ (i,j - nca)
      else if j < nca then C $$ (i - nra, j) else D $$ (i - nra, j - nca)))"

lemma index_mat_four_block[simp]:
  "i < dim_row A + dim_row D \<Longrightarrow> j < dim_col A + dim_col D \<Longrightarrow> four_block_mat A B C D $$ (i,j)
  = (if i < dim_row A then
      if j < dim_col A then A $$ (i,j) else B $$ (i,j - dim_col A)
      else if j < dim_col A then C $$ (i - dim_row A, j) else D $$ (i - dim_row A, j - dim_col A))"
  "dim_row (four_block_mat A B C D) = dim_row A + dim_row D"
  "dim_col (four_block_mat A B C D) = dim_col A + dim_col D"
  unfolding four_block_mat_def Let_def by auto

lemma four_block_carrier_mat[simp]:
  "A \<in> carrier_mat nr1 nc1 \<Longrightarrow> D \<in> carrier_mat nr2 nc2 \<Longrightarrow>
  four_block_mat A B C D \<in> carrier_mat (nr1 + nr2) (nc1 + nc2)"
  unfolding carrier_mat_def by auto

lemma cong_four_block_mat: "A1 = B1 \<Longrightarrow> A2 = B2 \<Longrightarrow> A3 = B3 \<Longrightarrow> A4 = B4 \<Longrightarrow>
  four_block_mat A1 A2 A3 A4 = four_block_mat B1 B2 B3 B4" by auto

lemma four_block_one_mat[simp]:
  "four_block_mat (1\<^sub>m n1) (0\<^sub>m n1 n2) (0\<^sub>m n2 n1) (1\<^sub>m n2) = 1\<^sub>m (n1 + n2)"
  by (rule eq_matI, auto)

lemma four_block_zero_mat[simp]:
  "four_block_mat (0\<^sub>m nr1 nc1) (0\<^sub>m nr1 nc2) (0\<^sub>m nr2 nc1) (0\<^sub>m nr2 nc2) = 0\<^sub>m (nr1 + nr2) (nc1 + nc2)"
  by (rule eq_matI, auto)

lemma row_four_block_mat:
  assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows
  "i < nr1 \<Longrightarrow> row (four_block_mat A B C D) i = row A i @\<^sub>v row B i" (is "_ \<Longrightarrow> ?AB")
  "\<not> i < nr1 \<Longrightarrow> i < nr1 + nr2 \<Longrightarrow> row (four_block_mat A B C D) i = row C (i - nr1) @\<^sub>v row D (i - nr1)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?CD")
proof -
  assume i: "i < nr1"
  show ?AB by (rule eq_vecI, insert i c, auto)
next
  assume i: "\<not> i < nr1" "i < nr1 + nr2"
  show ?CD by (rule eq_vecI, insert i c, auto)
qed

lemma col_four_block_mat:
  assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows
  "j < nc1 \<Longrightarrow> col (four_block_mat A B C D) j = col A j @\<^sub>v col C j" (is "_ \<Longrightarrow> ?AC")
  "\<not> j < nc1 \<Longrightarrow> j < nc1 + nc2 \<Longrightarrow> col (four_block_mat A B C D) j = col B (j - nc1) @\<^sub>v col D (j - nc1)"
  (is "_ \<Longrightarrow> _ \<Longrightarrow> ?BD")
proof -
  assume j: "j < nc1"
  show ?AC by (rule eq_vecI, insert j c, auto)
next
  assume j: "\<not> j < nc1" "j < nc1 + nc2"
  show ?BD by (rule eq_vecI, insert j c, auto)
qed

lemma mult_four_block_mat: assumes
  c1: "A1 \<in> carrier_mat nr1 n1" "B1 \<in> carrier_mat nr1 n2" "C1 \<in> carrier_mat nr2 n1" "D1 \<in> carrier_mat nr2 n2" and
  c2: "A2 \<in> carrier_mat n1 nc1" "B2 \<in> carrier_mat n1 nc2" "C2 \<in> carrier_mat n2 nc1" "D2 \<in> carrier_mat n2 nc2"
  shows "four_block_mat A1 B1 C1 D1 * four_block_mat A2 B2 C2 D2
  = four_block_mat (A1 * A2 + B1 * C2) (A1 * B2 + B1 * D2)
    (C1 * A2 + D1 * C2) (C1 * B2 + D1 * D2)" (is "?M1 * ?M2 = _")
proof -
  note row = row_four_block_mat[OF c1]
  note col = col_four_block_mat[OF c2]
  {
    fix i j
    assume i: "i < nr1" and j: "j < nc1"
    have "row ?M1 i \<bullet> col ?M2 j = row A1 i \<bullet> col A2 j + row B1 i \<bullet> col C2 j"
      unfolding row(1)[OF i] col(1)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i j, auto)
  }
  moreover
  {
    fix i j
    assume i: "\<not> i < nr1" "i < nr1 + nr2" and j: "j < nc1"
    hence i': "i - nr1 < nr2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row C1 (i - nr1) \<bullet> col A2 j + row D1 (i - nr1) \<bullet> col C2 j"
      unfolding row(2)[OF i] col(1)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i i' j, auto)
  }
  moreover
  {
    fix i j
    assume i: "i < nr1" and j: "\<not> j < nc1" "j < nc1 + nc2"
    hence j': "j - nc1 < nc2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row A1 i \<bullet> col B2 (j - nc1) + row B1 i \<bullet> col D2 (j - nc1)"
      unfolding row(1)[OF i] col(2)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i j' j, auto)
  }
  moreover
  {
    fix i j
    assume i: "\<not> i < nr1" "i < nr1 + nr2" and j: "\<not> j < nc1" "j < nc1 + nc2"
    hence i': "i - nr1 < nr2" and j': "j - nc1 < nc2" by auto
    have "row ?M1 i \<bullet> col ?M2 j = row C1 (i - nr1) \<bullet> col B2 (j - nc1) + row D1 (i - nr1) \<bullet> col D2 (j - nc1)"
      unfolding row(2)[OF i] col(2)[OF j]
      by (rule scalar_prod_append[of _ n1 _ n2], insert c1 c2 i i' j' j, auto)
  }
  ultimately show ?thesis
    by (intro eq_matI, insert c1 c2, auto)
qed

definition append_rows :: "'a :: zero mat \<Rightarrow> 'a mat \<Rightarrow> 'a mat" (infixr "@\<^sub>r" 65)where
  "A @\<^sub>r B = four_block_mat A (0\<^sub>m (dim_row A) 0) B (0\<^sub>m (dim_row B) 0)" 

lemma carrier_append_rows[simp,intro]: "A \<in> carrier_mat nr1 nc \<Longrightarrow> B \<in> carrier_mat nr2 nc \<Longrightarrow>
  A @\<^sub>r B \<in> carrier_mat (nr1 + nr2) nc" 
  unfolding append_rows_def by auto

lemma col_mult2[simp]:
  assumes A: "A : carrier_mat nr n"
      and B: "B : carrier_mat n nc"
      and j: "j < nc"
  shows "col (A * B) j = A *\<^sub>v col B j"
proof
  have AB: "A * B : carrier_mat nr nc" using A B by auto
  fix i assume i: "i < dim_vec (A *\<^sub>v col B j)"
  show "col (A * B) j $ i = (A *\<^sub>v col B j) $ i"
    using A B AB j i by simp
qed auto

lemma mat_vec_as_mat_mat_mult: assumes A: "A \<in> carrier_mat nr nc" 
  and v: "v \<in> carrier_vec nc" 
shows "A *\<^sub>v v = col (A * mat_of_cols nc [v]) 0"  
  by (subst col_mult2[OF A], insert v, auto)

lemma mat_mult_append: assumes A: "A \<in> carrier_mat nr1 nc" 
  and B: "B \<in> carrier_mat nr2 nc" 
  and v: "v \<in> carrier_vec nc" 
shows "(A @\<^sub>r B) *\<^sub>v v = (A *\<^sub>v v) @\<^sub>v (B *\<^sub>v v)" 
proof -
  let ?Fb1 = "four_block_mat A (0\<^sub>m nr1 0) B (0\<^sub>m nr2 0)" 
  let ?Fb2 = "four_block_mat (mat_of_cols nc [v]) (0\<^sub>m nc 0) (0\<^sub>m 0 1) (0\<^sub>m 0 0)" 
  have id: "?Fb2 = mat_of_cols nc [v]" 
    using v by auto
  have "(A @\<^sub>r B) *\<^sub>v v = col (?Fb1 * ?Fb2) 0" unfolding id
    by (subst mat_vec_as_mat_mat_mult[OF _ v], insert A B, auto simp: append_rows_def)
  also have "?Fb1 * ?Fb2 = four_block_mat (A * mat_of_cols nc [v] + 0\<^sub>m nr1 0 * 0\<^sub>m 0 1) (A * 0\<^sub>m nc 0 + 0\<^sub>m nr1 0 * 0\<^sub>m 0 0)
     (B * mat_of_cols nc [v] + 0\<^sub>m nr2 0 * 0\<^sub>m 0 1) (B * 0\<^sub>m nc 0 + 0\<^sub>m nr2 0 * 0\<^sub>m 0 0)" 
    by (rule mult_four_block_mat[OF A _ B], auto)
  also have "(A * mat_of_cols nc [v] + 0\<^sub>m nr1 0 * 0\<^sub>m 0 1) = A * mat_of_cols nc [v]" 
    using A v by auto
  also have "(B * mat_of_cols nc [v] + 0\<^sub>m nr2 0 * 0\<^sub>m 0 1) = B * mat_of_cols nc [v]" 
    using B v by auto
  also have "(A * 0\<^sub>m nc 0 + 0\<^sub>m nr1 0 * 0\<^sub>m 0 0) = 0\<^sub>m nr1 0" using A by auto 
  also have "(B * 0\<^sub>m nc 0 + 0\<^sub>m nr2 0 * 0\<^sub>m 0 0) = 0\<^sub>m nr2 0" using B by auto
  finally have "(A @\<^sub>r B) *\<^sub>v v = col (four_block_mat (A * mat_of_cols nc [v]) (0\<^sub>m nr1 0) (B * mat_of_cols nc [v]) (0\<^sub>m nr2 0)) 0" .
  also have "\<dots> = col (A * mat_of_cols nc [v]) 0 @\<^sub>v col (B * mat_of_cols nc [v]) 0" 
    by (rule col_four_block_mat, insert A B v, auto)
  also have "col (A * mat_of_cols nc [v]) 0 = A *\<^sub>v v" 
    by (rule mat_vec_as_mat_mat_mult[symmetric, OF A v])
  also have "col (B * mat_of_cols nc [v]) 0 = B *\<^sub>v v" 
    by (rule mat_vec_as_mat_mat_mult[symmetric, OF B v])
  finally show ?thesis .
qed
 
lemma append_rows_le: assumes A: "A \<in> carrier_mat nr1 nc" 
  and B: "B \<in> carrier_mat nr2 nc" 
  and a: "a \<in> carrier_vec nr1" 
  and v: "v \<in> carrier_vec nc"
shows "(A @\<^sub>r B) *\<^sub>v v \<le> (a @\<^sub>v b) \<longleftrightarrow> A *\<^sub>v v \<le> a \<and> B *\<^sub>v v \<le> b" 
  unfolding mat_mult_append[OF A B v]
  by (rule append_vec_le[OF _ a], insert A v, auto)


lemma elements_four_block_mat:
  assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows
  "elements_mat (four_block_mat A B C D) \<subseteq>
   elements_mat A \<union> elements_mat B \<union> elements_mat C \<union> elements_mat D"
   (is "elements_mat ?four \<subseteq> _")
proof rule
  fix a assume "a \<in> elements_mat ?four"
  then obtain i j
    where i4: "i < dim_row ?four" and j4: "j < dim_col ?four" and a: "a = ?four $$ (i, j)"
    by auto
  show "a \<in> elements_mat A \<union> elements_mat B \<union> elements_mat C \<union> elements_mat D"
  proof (cases "i < nr1")
    case True note i1 = this
    show ?thesis
    proof (cases "j < nc1")
      case True
      then have "a = A $$ (i,j)" using c i1 a by simp
      thus ?thesis using c i1 True by auto next
      case False
      then have "a = B $$ (i,j-nc1)" using c i1 a j4 by simp
      moreover have "j - nc1 < nc2" using c j4 False by auto
      ultimately show ?thesis using c i1 by auto
    qed next
    case False note i1 = this
    have i2: "i - nr1 < nr2" using c i1 i4 by auto
    show ?thesis
    proof (cases "j < nc1")
      case True
      then have "a = C $$ (i-nr1,j)" using c i2 a i1 by simp
      thus ?thesis using c i2 True by auto next
      case False
      then have "a = D $$ (i-nr1,j-nc1)" using c i2 a i1 j4 by simp
      moreover have "j - nc1 < nc2" using c j4 False by auto
      ultimately show ?thesis using c i2 by auto
    qed
  qed
qed

lemma assoc_four_block_mat: fixes FB :: "'a mat \<Rightarrow> 'a mat \<Rightarrow> 'a :: zero mat"
  defines FB: "FB \<equiv> \<lambda> Bb Cc. four_block_mat Bb (0\<^sub>m (dim_row Bb) (dim_col Cc)) (0\<^sub>m (dim_row Cc) (dim_col Bb)) Cc"
  shows "FB A (FB B C) = FB (FB A B) C" (is "?L = ?R")
proof -
  let ?ar = "dim_row A" let ?ac = "dim_col A"
  let ?br = "dim_row B" let ?bc = "dim_col B"
  let ?cr = "dim_row C" let ?cc = "dim_col C"
  let ?r = "?ar + ?br + ?cr" let ?c = "?ac + ?bc + ?cc"
  let ?BC = "FB B C" let ?AB = "FB A B"
  have dL: "dim_row ?L = ?r" "dim_col ?L = ?c" unfolding FB by auto
  have dR: "dim_row ?R = ?ar + ?br + ?cr" "dim_col ?R = ?ac + ?bc + ?cc" unfolding FB by auto
  have dBC: "dim_row ?BC = ?br + ?cr" "dim_col ?BC = ?bc + ?cc" unfolding FB by auto
  have dAB: "dim_row ?AB = ?ar + ?br" "dim_col ?AB = ?ac + ?bc" unfolding FB by auto
  show ?thesis
  proof (intro eq_matI[of ?R ?L, unfolded dL dR, OF _ refl refl])
    fix i j
    assume i: "i < ?r" and j: "j < ?c"
    show "?L $$ (i,j) = ?R $$ (i,j)"
    proof (cases "i < ?ar")
      case True note i = this
      thus ?thesis using j
        by (cases "j < ?ac", auto simp: FB)
    next
      case False note ii = this
      show ?thesis
      proof (cases "j < ?ac")
        case True
        with i ii show ?thesis unfolding FB by auto
      next
        case False note jj = this
        from j jj i ii have L: "?L $$ (i,j) = ?BC $$ (i - ?ar, j - ?ac)" unfolding FB by auto
        have R: "?R $$ (i,j) = ?BC $$ (i - ?ar, j - ?ac)" using ii jj i j
          by (cases "i < ?ar + ?br"; cases "j < ?ac + ?bc", auto simp: FB)
        show ?thesis unfolding L R ..
      qed
    qed
  qed
qed

definition split_block :: "'a mat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('a mat \<times> 'a mat \<times> 'a mat \<times> 'a mat)"
  where "split_block A sr sc = (let
    nr = dim_row A; nc = dim_col A;
    nr2 = nr - sr; nc2 = nc - sc;
    A1 = mat sr sc (\<lambda> ij. A $$ ij);
    A2 = mat sr nc2 (\<lambda> (i,j). A $$ (i,j+sc));
    A3 = mat nr2 sc (\<lambda> (i,j). A $$ (i+sr,j));
    A4 = mat nr2 nc2 (\<lambda> (i,j). A $$ (i+sr,j+sc))
  in (A1,A2,A3,A4))"

lemma split_block: assumes res: "split_block A sr1 sc1 = (A1,A2,A3,A4)"
  and dims: "dim_row A = sr1 + sr2" "dim_col A = sc1 + sc2"
  shows "A1 \<in> carrier_mat sr1 sc1" "A2 \<in> carrier_mat sr1 sc2"
    "A3 \<in> carrier_mat sr2 sc1" "A4 \<in> carrier_mat sr2 sc2"
    "A = four_block_mat A1 A2 A3 A4"
  using res unfolding split_block_def Let_def
  by (auto simp: dims)

text \<open>Using @{const four_block_mat} we define block-diagonal matrices.\<close>

fun diag_block_mat :: "'a :: zero mat list \<Rightarrow> 'a mat" where
  "diag_block_mat [] = 0\<^sub>m 0 0"
| "diag_block_mat (A # As) = (let
     B = diag_block_mat As
     in four_block_mat A (0\<^sub>m (dim_row A) (dim_col B)) (0\<^sub>m (dim_row B) (dim_col A)) B)"

lemma dim_diag_block_mat:
  "dim_row (diag_block_mat As) = sum_list (map dim_row As)" (is "?row")
  "dim_col (diag_block_mat As) = sum_list (map dim_col As)" (is "?col")
proof -
  have "?row \<and> ?col"
    by (induct As, auto simp: Let_def)
  thus ?row and ?col by auto
qed

lemma diag_block_mat_singleton[simp]: "diag_block_mat [A] = A"
  by auto

lemma diag_block_mat_append: "diag_block_mat (As @ Bs) =
  (let A = diag_block_mat As; B = diag_block_mat Bs
  in four_block_mat A (0\<^sub>m (dim_row A) (dim_col B)) (0\<^sub>m (dim_row B) (dim_col A)) B)"
  unfolding Let_def
proof (induct As)
  case (Cons A As)
  show ?case
    unfolding append.simps
    unfolding diag_block_mat.simps Let_def
    unfolding Cons
    by (rule assoc_four_block_mat)
qed auto

lemma diag_block_mat_last: "diag_block_mat (As @ [B]) =
  (let A = diag_block_mat As
  in four_block_mat A (0\<^sub>m (dim_row A) (dim_col B)) (0\<^sub>m (dim_row B) (dim_col A)) B)"
  unfolding diag_block_mat_append diag_block_mat_singleton by auto


lemma diag_block_mat_square:
  "Ball (set As) square_mat \<Longrightarrow> square_mat (diag_block_mat As)"
by (induct As, auto simp:Let_def)

lemma diag_block_one_mat[simp]:
  "diag_block_mat (map (\<lambda>A. 1\<^sub>m (dim_row A)) As) = (1\<^sub>m (sum_list (map dim_row As)))"
  by (induct As, auto simp: Let_def)

lemma elements_diag_block_mat:
  "elements_mat (diag_block_mat As) \<subseteq> {0} \<union> \<Union> (set (map elements_mat As))"
proof (induct As)
  case Nil then show ?case using dim_diag_block_mat[of Nil] by auto next
  case (Cons A As)
    let ?D = "diag_block_mat As"
    let ?B = "0\<^sub>m (dim_row A) (dim_col ?D)"
    let ?C = "0\<^sub>m (dim_row ?D) (dim_col A)"
    have A: "A \<in> carrier_mat (dim_row A) (dim_col A)" by auto
    have B: "?B \<in> carrier_mat (dim_row A) (dim_col ?D)" by auto
    have C: "?C \<in> carrier_mat (dim_row ?D) (dim_col A)" by auto
    have D: "?D \<in> carrier_mat (dim_row ?D) (dim_col ?D)" by auto
    have
      "elements_mat (diag_block_mat (A#As)) \<subseteq>
       elements_mat A \<union> elements_mat ?B \<union> elements_mat ?C \<union> elements_mat ?D"
      unfolding diag_block_mat.simps Let_def
      using elements_four_block_mat[OF A B C D] elements_0_mat
      by auto
    also have "... \<subseteq> {0} \<union> elements_mat A \<union> elements_mat ?D"
      using elements_0_mat by auto
    finally show ?case using Cons by auto
qed

lemma diag_block_pow_mat: assumes sq: "Ball (set As) square_mat"
  shows "diag_block_mat As ^\<^sub>m n = diag_block_mat (map (\<lambda> A. A ^\<^sub>m n) As)" (is "?As ^\<^sub>m _ = _")
proof (induct n)
  case 0
  have "?As ^\<^sub>m 0 = 1\<^sub>m (dim_row ?As)" by simp
  also have "dim_row ?As = sum_list (map dim_row As)"
    using diag_block_mat_square[OF sq] unfolding dim_diag_block_mat by auto
  also have "1\<^sub>m \<dots> = diag_block_mat (map (\<lambda>A. 1\<^sub>m (dim_row A)) As)" by simp
  also have "\<dots> = diag_block_mat (map (\<lambda> A. A ^\<^sub>m 0) As)" by simp
  finally show ?case .
next
  case (Suc n)
  let ?An = "\<lambda> As. diag_block_mat (map (\<lambda>A. A ^\<^sub>m n) As)"
  let ?Asn = "\<lambda> As. diag_block_mat (map (\<lambda>A. A ^\<^sub>m n * A) As)"
  from Suc have "?case = (?An As * diag_block_mat As = ?Asn As)" by simp
  also have "\<dots>" using sq
  proof (induct As)
    case (Cons A As)
    hence IH: "?An As * diag_block_mat As = ?Asn As"
      and sq: "Ball (set As) square_mat" and A: "dim_col A = dim_row A" by auto
    have sq2: "Ball (set (List.map (\<lambda>A. A ^\<^sub>m n) As)) square_mat"
      and sq3: "Ball (set (List.map (\<lambda>A. A ^\<^sub>m n * A) As)) square_mat"
      using sq by auto
    define n1 where "n1 = dim_row A"
    define n2 where "n2 = sum_list (map dim_row As)"
    from A have A: "A \<in> carrier_mat n1 n1" unfolding n1_def carrier_mat_def by simp
    have [simp]: "dim_col (?An As) = n2" "dim_row (?An As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq2,unfolded square_mat.simps]
      unfolding dim_diag_block_mat map_map by (auto simp:o_def)
    have [simp]: "dim_col (?Asn As) = n2" "dim_row (?Asn As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq3,unfolded square_mat.simps]
      unfolding dim_diag_block_mat map_map by (auto simp:o_def)
    have [simp]:
      "dim_row (diag_block_mat As) = n2"
      "dim_col (diag_block_mat As) = n2"
      unfolding n2_def
      using diag_block_mat_square[OF sq,unfolded square_mat.simps]
      unfolding dim_diag_block_mat by auto

    have [simp]: "diag_block_mat As \<in> carrier_mat n2 n2" unfolding carrier_mat_def by simp
    have [simp]: "?An As \<in> carrier_mat n2 n2" unfolding carrier_mat_def by simp
    show ?case unfolding diag_block_mat.simps Let_def list.simps
      by (subst mult_four_block_mat[of _ n1 n1 _ n2 _ n2 _ _ n1 _ n2],
      insert A, auto simp: IH)
  qed auto
  finally show ?case by simp
qed

lemma diag_block_upper_triangular: assumes
    "\<And> A i j. A \<in> set As \<Longrightarrow> j < i \<Longrightarrow> i < dim_row A \<Longrightarrow> A $$ (i,j) = 0"
  and "Ball (set As) square_mat"
  and "j < i" "i < dim_row (diag_block_mat As)"
  shows "diag_block_mat As $$ (i,j) = 0"
  using assms
proof (induct As arbitrary: i j)
  case (Cons A As i j)
  let ?n1 = "dim_row A"
  let ?n2 = "sum_list (map dim_row As)"
  from Cons have [simp]: "dim_col A = ?n1" by simp
  from Cons have "Ball (set As) square_mat" by auto
  note [simp] = diag_block_mat_square[OF this,unfolded square_mat.simps]
  note [simp] = dim_diag_block_mat(1)
  from Cons(5) have i: "i < ?n1 + ?n2" by simp
  show ?case
  proof (cases "i < ?n1")
    case True
    with Cons(4) have j: "j < ?n1" by auto
    with True Cons(2)[of A, OF _ Cons(4)] show ?thesis
      by (simp add: Let_def)
  next
    case False note iAs = this
    show ?thesis
    proof (cases "j < ?n1")
      case True
      with i iAs show ?thesis by (simp add: Let_def)
    next
      case False note jAs = this
      from Cons(4) i have j: "j < ?n1 + ?n2" by auto
      show ?thesis using iAs jAs i j
        by (simp add: Let_def, subst Cons(1), insert Cons(2-4), auto)
    qed
  qed
qed simp

lemma smult_four_block_mat: assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows "a \<cdot>\<^sub>m four_block_mat A B C D = four_block_mat (a \<cdot>\<^sub>m A) (a \<cdot>\<^sub>m B) (a \<cdot>\<^sub>m C) (a \<cdot>\<^sub>m D)"
  by (rule eq_matI, insert c, auto)

lemma map_four_block_mat: assumes c: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows "map_mat f (four_block_mat A B C D) = four_block_mat (map_mat f A) (map_mat f B) (map_mat f C) (map_mat f D)"
  by (rule eq_matI, insert c, auto)

lemma add_four_block_mat: assumes
  c1: "A1 \<in> carrier_mat nr1 nc1" "B1 \<in> carrier_mat nr1 nc2" "C1 \<in> carrier_mat nr2 nc1" "D1 \<in> carrier_mat nr2 nc2" and
  c2: "A2 \<in> carrier_mat nr1 nc1" "B2 \<in> carrier_mat nr1 nc2" "C2 \<in> carrier_mat nr2 nc1" "D2 \<in> carrier_mat nr2 nc2"
  shows "four_block_mat A1 B1 C1 D1 + four_block_mat A2 B2 C2 D2
  = four_block_mat (A1 + A2) (B1 + B2) (C1 + C2) (D1 + D2)"
  by (rule eq_matI, insert assms, auto)


lemma diag_four_block_mat: assumes c: "A \<in> carrier_mat n1 n1"
   "D \<in> carrier_mat n2 n2"
  shows "diag_mat (four_block_mat A B C D) = diag_mat A @ diag_mat D"
  by (rule nth_equalityI, insert c, auto simp: diag_mat_def nth_append)

definition mk_diagonal :: "'a::zero list \<Rightarrow> 'a mat"
  where "mk_diagonal as = diag_block_mat (map (\<lambda>a. mat (Suc 0) (Suc 0) (\<lambda>_. a)) as)"

lemma mk_diagonal_dim:
  "dim_row (mk_diagonal as) = length as" "dim_col (mk_diagonal as) = length as"
  unfolding mk_diagonal_def by(induct as, auto simp: Let_def)

lemma mk_diagonal_diagonal: "diagonal_mat (mk_diagonal as)"
  unfolding mk_diagonal_def
proof (induct as)
  case Nil show ?case unfolding mk_diagonal_def diagonal_mat_def by simp next
  case (Cons a as)
    let ?n = "length (a#as)"
    let ?A = "mat (Suc 0) (Suc 0) (\<lambda>_. a)"
    let ?f = "map (\<lambda>a. mat (Suc 0) (Suc 0) (\<lambda>_. a))"
    let ?AS = "diag_block_mat (?f as)"
    let ?AAS = "diag_block_mat (?f (a#as))"
    show ?case
      unfolding diagonal_mat_def
    proof(intro allI impI)
      fix i j assume ir: "i < dim_row ?AAS" and jc: "j < dim_col ?AAS" and ij: "i \<noteq> j"
      hence ir2: "i < 1 + dim_row ?AS" and jc2: "j < 1 + dim_col ?AS"
        unfolding dim_row_mat list.map diag_block_mat.simps Let_def
        by auto
      show "?AAS $$ (i,j) = 0"
      proof (cases "i = 0")
        case True
          then show ?thesis using jc ij by (auto simp: Let_def) next
        case False note i0 = this
          show ?thesis
          proof (cases "j = 0")
            case True
              then show ?thesis using ir ij by (auto simp: Let_def) next
            case False
              have ir3: "i-1 < dim_row ?AS" and jc3: "j-1 < dim_col ?AS"
                using ir2 jc2 i0 False by auto
              have IH: "\<And>i j. i < dim_row ?AS \<Longrightarrow> j < dim_col ?AS \<Longrightarrow> i \<noteq> j \<Longrightarrow>
                ?AS $$ (i,j) = 0"
                using Cons unfolding diagonal_mat_def by auto
              have "?AS $$ (i-1,j-1) = 0"
                using IH[OF ir3 jc3] i0 False ij by auto
              thus ?thesis using ir jc ij by (simp add: Let_def)
          qed
      qed
    qed
qed

definition orthogonal_mat :: "'a::semiring_0 mat \<Rightarrow> bool"
  where "orthogonal_mat A \<equiv>
    let B = transpose_mat A * A in
    diagonal_mat B \<and> (\<forall>i<dim_col A. B $$ (i,i) \<noteq> 0)"

lemma orthogonal_matD[elim]:
  "orthogonal_mat A \<Longrightarrow>
   i < dim_col A \<Longrightarrow> j < dim_col A \<Longrightarrow> (col A i \<bullet> col A j = 0) = (i \<noteq> j)"
  unfolding orthogonal_mat_def diagonal_mat_def by auto

lemma orthogonal_matI[intro]:
  "(\<And>i j. i < dim_col A \<Longrightarrow> j < dim_col A \<Longrightarrow> (col A i \<bullet> col A j = 0) = (i \<noteq> j)) \<Longrightarrow>
   orthogonal_mat A"
  unfolding orthogonal_mat_def diagonal_mat_def by auto

definition orthogonal :: "'a::semiring_0 vec list \<Rightarrow> bool"
  where "orthogonal vs \<equiv>
    \<forall>i j. i < length vs \<longrightarrow> j < length vs \<longrightarrow>
      (vs ! i \<bullet> vs ! j = 0) = (i \<noteq> j)"

lemma orthogonalD[elim]:
  "orthogonal vs \<Longrightarrow> i < length vs \<Longrightarrow> j < length vs \<Longrightarrow>
  (nth vs i \<bullet> nth vs j = 0) = (i \<noteq> j)"
  unfolding orthogonal_def by auto

lemma orthogonalI[intro]:
  "(\<And>i j. i < length vs \<Longrightarrow> j < length vs \<Longrightarrow> (nth vs i \<bullet> nth vs j = 0) = (i \<noteq> j)) \<Longrightarrow>
   orthogonal vs"
  unfolding orthogonal_def by auto


lemma transpose_four_block_mat: assumes *: "A \<in> carrier_mat nr1 nc1" "B \<in> carrier_mat nr1 nc2"
  "C \<in> carrier_mat nr2 nc1" "D \<in> carrier_mat nr2 nc2"
  shows "transpose_mat (four_block_mat A B C D) =
    four_block_mat (transpose_mat A) (transpose_mat C) (transpose_mat B) (transpose_mat D)"
  by (rule eq_matI, insert *, auto)

lemma zero_transpose_mat[simp]: "transpose_mat (0\<^sub>m n m) = (0\<^sub>m m n)"
  by (rule eq_matI, auto)

lemma upper_triangular_four_block: assumes AD: "A \<in> carrier_mat n n" "D \<in> carrier_mat m m"
  and ut: "upper_triangular A" "upper_triangular D"
  shows "upper_triangular (four_block_mat A B (0\<^sub>m m n) D)"
proof -
  let ?C = "four_block_mat A B (0\<^sub>m m n) D"
  from AD have dim: "dim_row ?C = n + m" "dim_col ?C = n + m" "dim_row A = n" by auto
  show ?thesis
  proof (rule upper_triangularI, unfold dim)
    fix i j
    assume *: "j < i" "i < n + m"
    show "?C $$ (i,j) = 0"
    proof (cases "i < n")
      case True
      with upper_triangularD[OF ut(1) *(1)] * AD show ?thesis by auto
    next
      case False note i = this
      show ?thesis by (cases "j < n", insert upper_triangularD[OF ut(2)] * i AD, auto)
    qed
  qed
qed

lemma pow_four_block_mat: assumes A: "A \<in> carrier_mat n n"
  and B: "B \<in> carrier_mat m m"
  shows "(four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) B) ^\<^sub>m k =
    four_block_mat (A ^\<^sub>m k) (0\<^sub>m n m) (0\<^sub>m m n) (B ^\<^sub>m k)"
proof (induct k)
  case (Suc k)
  let ?FB = "\<lambda> A B. four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) B"
  let ?A = "?FB A B"
  let ?B = "?FB (A ^\<^sub>m k) (B ^\<^sub>m k)"
  from A B have Ak: "A ^\<^sub>m k \<in> carrier_mat n n" and Bk: "B ^\<^sub>m k \<in> carrier_mat m m" by auto
  have "?A ^\<^sub>m Suc k = ?A ^\<^sub>m k * ?A" by simp
  also have "?A ^\<^sub>m k = ?B " by (rule Suc)
  also have "?B * ?A = ?FB (A ^\<^sub>m Suc k) (B ^\<^sub>m Suc k)"
    by (subst mult_four_block_mat[OF Ak _ _ Bk A _ _ B], insert A B, auto)
  finally show ?case .
qed (insert A B, auto)

lemma uminus_scalar_prod:
  assumes [simp]: "v : carrier_vec n" "w : carrier_vec n"
  shows "- ((v::'a::field vec) \<bullet> w) = (- v) \<bullet> w"
  unfolding scalar_prod_def uminus_vec_def
  apply (subst sum_negf[symmetric])
proof (rule sum.cong[OF refl])
  fix i assume i: "i : {0 ..<dim_vec w}"
  have [simp]: "dim_vec v = n" "dim_vec w = n" by auto
  show "- (v $ i * w $ i) = vec (dim_vec v) (\<lambda>i. - v $ i) $ i * w $ i"
    unfolding minus_mult_left using i by auto
qed


lemma append_vec_eq:
  assumes [simp]: "v : carrier_vec n" "v' : carrier_vec n"
  shows [simp]: "v @\<^sub>v w = v' @\<^sub>v w' \<longleftrightarrow> v = v' \<and> w = w'" (is "?L \<longleftrightarrow> ?R")
proof
  have [simp]: "dim_vec v = n" "dim_vec v' = n" by auto
  { assume L: ?L
    have vv': "v = v'"
    proof
      fix i assume i: "i < dim_vec v'"
      have "(v @\<^sub>v w) $ i = (v' @\<^sub>v w') $ i" using L by auto
      thus "v $ i = v' $ i" using i by auto
    qed auto
    moreover have "w = w'"
    proof
      show "dim_vec w = dim_vec w'" using vv' L
        by (metis add_diff_cancel_left' index_append_vec(2))
      moreover fix i assume i: "i < dim_vec w'"
      have "(v @\<^sub>v w) $ (n + i) = (v' @\<^sub>v w') $ (n + i)" using L by auto
      ultimately show "w $ i = w' $ i" using i by simp
    qed
    ultimately show ?R by simp
  }
qed auto

lemma append_vec_add:
  assumes [simp]: "v : carrier_vec n" "v' : carrier_vec n"
      and [simp]: "w : carrier_vec m" "w' : carrier_vec m"
  shows "(v @\<^sub>v w) + (v' @\<^sub>v w') = (v + v') @\<^sub>v (w + w')" (is "?L = ?R")
proof
  have [simp]: "dim_vec v = n" "dim_vec v' = n" by auto
  have [simp]: "dim_vec w = m" "dim_vec w' = m" by auto
  fix i assume i: "i < dim_vec ?R"
  thus "?L $ i = ?R $ i" by (cases "i < n",auto)
qed auto


lemma mult_mat_vec_split:
  assumes A: "A : carrier_mat n n"
      and D: "D : carrier_mat m m"
      and a: "a : carrier_vec n"
      and d: "d : carrier_vec m"
  shows "four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) D *\<^sub>v (a @\<^sub>v d) = A *\<^sub>v a @\<^sub>v D *\<^sub>v d"
    (is "?A00D *\<^sub>v _ = ?r")
proof
  have A00D: "?A00D : carrier_mat (n+m) (n+m)" using four_block_carrier_mat[OF A D].
  fix i assume i: "i < dim_vec ?r"
  show "(?A00D *\<^sub>v (a @\<^sub>v d)) $ i = ?r $ i" (is "?li = _")
  proof (cases "i < n")
    case True
      have "?li = (row A i @\<^sub>v 0\<^sub>v m) \<bullet> (a @\<^sub>v d)"
        using A row_four_block_mat[OF A _ _ D] True by simp
      also have "... = row A i \<bullet> a + 0\<^sub>v m \<bullet> d"
        apply (rule scalar_prod_append) using A D a d True by auto
      also have "... = row A i \<bullet> a" using d by simp
      finally show ?thesis using A True by auto
    next case False
      let ?i = "i - n"
      have "?li = (0\<^sub>v n @\<^sub>v row D ?i) \<bullet> (a @\<^sub>v d)"
        using i row_four_block_mat[OF A _ _ D] False A D by simp
      also have "... = 0\<^sub>v n \<bullet> a + row D ?i \<bullet> d"
        apply (rule scalar_prod_append) using A D a d False by auto
      also have "... = row D ?i \<bullet> d" using a by simp
      finally show ?thesis using A D False i by auto
  qed
qed auto

lemma similar_mat_witI: assumes "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" "A = P * B * Q"
  "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "P \<in> carrier_mat n n" "Q \<in> carrier_mat n n"
  shows "similar_mat_wit A B P Q" using assms unfolding similar_mat_wit_def Let_def by auto

lemma similar_mat_witD: assumes "n = dim_row A" "similar_mat_wit A B P Q"
  shows "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" "A = P * B * Q"
  "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "P \<in> carrier_mat n n" "Q \<in> carrier_mat n n"
  using assms(2) unfolding similar_mat_wit_def Let_def assms(1)[symmetric] by auto

lemma similar_mat_witD2: assumes "A \<in> carrier_mat n m" "similar_mat_wit A B P Q"
  shows "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" "A = P * B * Q"
  "A \<in> carrier_mat n n" "B \<in> carrier_mat n n" "P \<in> carrier_mat n n" "Q \<in> carrier_mat n n"
  using similar_mat_witD[OF _ assms(2), of n] assms(1)[unfolded carrier_mat_def] by auto

lemma similar_mat_wit_sym: assumes sim: "similar_mat_wit A B P Q"
  shows "similar_mat_wit B A Q P"
proof -
  from similar_mat_witD[OF refl sim] obtain n where
    AB: "{A, B, P, Q} \<subseteq> carrier_mat n n" "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" and A: "A = P * B * Q" by blast
  hence *: "{B, A, Q, P} \<subseteq> carrier_mat n n" "Q * P = 1\<^sub>m n" "P * Q = 1\<^sub>m n" by auto
  let ?c = "\<lambda> A. A \<in> carrier_mat n n"
  from * have Carr: "?c B" "?c P" "?c Q" by auto
  note [simp] = assoc_mult_mat[of _ n n _ n _ n]
  show ?thesis
  proof (rule similar_mat_witI[of _ _ n])
    have "Q * A * P = (Q * P) * B * (Q * P)"
      using Carr unfolding A by simp
    also have "\<dots> = B" using Carr unfolding AB by simp
    finally show "B = Q * A * P" by simp
  qed (insert * AB, auto)
qed

lemma similar_mat_wit_refl: assumes A: "A \<in> carrier_mat n n"
  shows "similar_mat_wit A A (1\<^sub>m n) (1\<^sub>m n)"
  by (rule similar_mat_witI[OF _ _ _ A], insert A, auto)

lemma similar_mat_wit_trans: assumes AB: "similar_mat_wit A B P Q"
  and BC: "similar_mat_wit B C P' Q'"
  shows "similar_mat_wit A C (P * P') (Q' * Q)"
proof -
  from similar_mat_witD[OF refl AB] obtain n where
    AB: "{A, B, P, Q} \<subseteq> carrier_mat n n" "P * Q = 1\<^sub>m n" "Q * P = 1\<^sub>m n" "A = P * B * Q" by blast
  hence B: "B \<in> carrier_mat n n" by auto
  from similar_mat_witD2[OF B BC] have
    BC: "{C, P', Q'} \<subseteq> carrier_mat n n" "P' * Q' = 1\<^sub>m n" "Q' * P' = 1\<^sub>m n" "B = P' * C * Q'" by auto
  let ?c = "\<lambda> A. A \<in> carrier_mat n n"
  let ?P = "P * P'"
  let ?Q = "Q' * Q"
  from AB BC have carr: "?c A" "?c B" "?c C" "?c P" "?c P'" "?c Q" "?c Q'"
    and Carr: "{A, C, ?P, ?Q} \<subseteq> carrier_mat n n" by auto
  note [simp] = assoc_mult_mat[of _ n n _ n _ n]
  have id: "A = ?P * C * ?Q" unfolding AB(4)[unfolded BC(4)] using carr
    by simp
  have "?P * ?Q = P * (P' * Q') * Q" using carr by simp
  also have "\<dots> = 1\<^sub>m n" unfolding BC using carr AB by simp
  finally have PQ: "?P * ?Q = 1\<^sub>m n" .
  have "?Q * ?P = Q' * (Q * P) * P'" using carr by simp
  also have "\<dots> = 1\<^sub>m n" unfolding AB using carr BC by simp
  finally have QP: "?Q * ?P = 1\<^sub>m n" .
  show ?thesis
    by (rule similar_mat_witI[OF PQ QP id], insert Carr, auto)
qed

lemma similar_mat_refl: "A \<in> carrier_mat n n \<Longrightarrow> similar_mat A A"
  using similar_mat_wit_refl unfolding similar_mat_def by blast

lemma similar_mat_trans: "similar_mat A B \<Longrightarrow> similar_mat B C \<Longrightarrow> similar_mat A C"
  using similar_mat_wit_trans unfolding similar_mat_def by blast

lemma similar_mat_sym: "similar_mat A B \<Longrightarrow> similar_mat B A"
  using similar_mat_wit_sym unfolding similar_mat_def by blast

lemma similar_mat_wit_four_block: assumes
      1: "similar_mat_wit A1 B1 P1 Q1"
  and 2: "similar_mat_wit A2 B2 P2 Q2"
  and URA: "URA = (P1 * UR * Q2)"
  and LLA: "LLA = (P2 * LL * Q1)"
  and A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat m m"
  and LL: "LL \<in> carrier_mat m n"
  and UR: "UR \<in> carrier_mat n m"
  shows "similar_mat_wit (four_block_mat A1 URA LLA A2) (four_block_mat B1 UR LL B2)
    (four_block_mat P1 (0\<^sub>m n m) (0\<^sub>m m n) P2) (four_block_mat Q1 (0\<^sub>m n m) (0\<^sub>m m n) Q2)"
  (is "similar_mat_wit ?A ?B ?P ?Q")
proof -
  let ?n = "n + m"
  let ?O1 = "1\<^sub>m n"   let ?O2 = "1\<^sub>m m"   let ?O = "1\<^sub>m ?n"
  from similar_mat_witD2[OF A1 1] have 11: "P1 * Q1 = ?O1" "Q1 * P1 = ?O1"
    and P1: "P1 \<in> carrier_mat n n" and Q1: "Q1 \<in> carrier_mat n n"
    and B1: "B1 \<in> carrier_mat n n" and 1: "A1 = P1 * B1 * Q1" by auto
  from similar_mat_witD2[OF A2 2] have 21: "P2 * Q2 = ?O2" "Q2 * P2 = ?O2"
    and P2: "P2 \<in> carrier_mat m m" and Q2: "Q2 \<in> carrier_mat m m"
    and B2: "B2 \<in> carrier_mat m m" and 2: "A2 = P2 * B2 * Q2" by auto
  have PQ1: "?P * ?Q = ?O"
    by (subst mult_four_block_mat[OF P1 _ _ P2 Q1 _ _ Q2], unfold 11 21, insert P1 P2 Q1 Q2,
      auto intro!: eq_matI)
  have QP1: "?Q * ?P = ?O"
    by (subst mult_four_block_mat[OF Q1 _ _ Q2 P1 _ _ P2], unfold 11 21, insert P1 P2 Q1 Q2,
      auto intro!: eq_matI)
  let ?PB = "?P * ?B"
  have P: "?P \<in> carrier_mat ?n ?n" using P1 P2 by auto
  have Q: "?Q \<in> carrier_mat ?n ?n" using Q1 Q2 by auto
  have B: "?B \<in> carrier_mat ?n ?n" using B1 UR LL B2 by auto
  have PB: "?PB \<in> carrier_mat ?n ?n" using P B by auto
  have PB1: "P1 * B1 \<in> carrier_mat n n" using P1 B1 by auto
  have PB2: "P2 * B2 \<in> carrier_mat m m" using P2 B2 by auto
  have P1UR: "P1 * UR \<in> carrier_mat n m" using P1 UR by auto
  have P2LL: "P2 * LL \<in> carrier_mat m n" using P2 LL by auto
  have id: "?PB = four_block_mat (P1 * B1) (P1 * UR) (P2 * LL) (P2 * B2)"
    by (subst mult_four_block_mat[OF P1 _ _ P2 B1 UR LL B2], insert P1 P2 B1 B2 LL UR, auto)
  have id: "?PB * ?Q = four_block_mat (P1 * B1 * Q1) (P1 * UR * Q2)
    (P2 * LL * Q1) (P2 * B2 * Q2)" unfolding id
    by (subst mult_four_block_mat[OF PB1 P1UR P2LL PB2 Q1 _ _ Q2],
    insert P1 P2 B1 B2 Q1 Q2 UR LL, auto)
  have id: "?A = ?P * ?B * ?Q" unfolding id 1 2 URA LLA ..
  show ?thesis
    by (rule similar_mat_witI[OF PQ1 QP1 id], insert A1 A2 B1 B2 Q1 Q2 P1 P2, auto)
qed


lemma similar_mat_four_block_0_ex: assumes
      1: "similar_mat A1 B1"
  and 2: "similar_mat A2 B2"
  and A0: "A0 \<in> carrier_mat n m"
  and A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat m m"
  shows "\<exists> B0. B0 \<in> carrier_mat n m \<and> similar_mat (four_block_mat A1 A0 (0\<^sub>m m n) A2)
    (four_block_mat B1 B0 (0\<^sub>m m n) B2)"
proof -
  from 1[unfolded similar_mat_def] obtain P1 Q1 where 1: "similar_mat_wit A1 B1 P1 Q1" by auto
  note w1 = similar_mat_witD2[OF A1 1]
  from 2[unfolded similar_mat_def] obtain P2 Q2 where 2: "similar_mat_wit A2 B2 P2 Q2" by auto
  note w2 = similar_mat_witD2[OF A2 2]
  from w1 w2 have C: "B1 \<in> carrier_mat n n" "B2 \<in> carrier_mat m m" by auto
  from w1 w2 have id: "0\<^sub>m m n = Q2 * 0\<^sub>m m n * P1" by simp
  let ?wit = "Q1 * A0 * P2"
  from w1 w2 A0 have wit: "?wit \<in> carrier_mat n m" by auto
  from similar_mat_wit_sym[OF similar_mat_wit_four_block[OF similar_mat_wit_sym[OF 1] similar_mat_wit_sym[OF 2]
    refl id C zero_carrier_mat A0]]
  have "similar_mat (four_block_mat A1 A0 (0\<^sub>m m n) A2) (four_block_mat B1 (Q1 * A0 * P2) (0\<^sub>m m n) B2)"
    unfolding similar_mat_def by auto
  thus ?thesis using wit by auto
qed

lemma similar_mat_four_block_0_0: assumes
      1: "similar_mat A1 B1"
  and 2: "similar_mat A2 B2"
  and A1: "A1 \<in> carrier_mat n n"
  and A2: "A2 \<in> carrier_mat m m"
  shows "similar_mat (four_block_mat A1 (0\<^sub>m n m) (0\<^sub>m m n) A2)
    (four_block_mat B1 (0\<^sub>m n m) (0\<^sub>m m n) B2)"
proof -
  from 1[unfolded similar_mat_def] obtain P1 Q1 where 1: "similar_mat_wit A1 B1 P1 Q1" by auto
  note w1 = similar_mat_witD2[OF A1 1]
  from 2[unfolded similar_mat_def] obtain P2 Q2 where 2: "similar_mat_wit A2 B2 P2 Q2" by auto
  note w2 = similar_mat_witD2[OF A2 2]
  from w1 w2 have C: "B1 \<in> carrier_mat n n" "B2 \<in> carrier_mat m m" by auto
  from w1 w2 have id: "0\<^sub>m m n = Q2 * 0\<^sub>m m n * P1" by simp
  from w1 w2 have id2: "0\<^sub>m n m = Q1 * 0\<^sub>m n m * P2" by simp
  from similar_mat_wit_sym[OF similar_mat_wit_four_block[OF similar_mat_wit_sym[OF 1] similar_mat_wit_sym[OF 2]
    id2 id C zero_carrier_mat zero_carrier_mat]]
  show ?thesis unfolding similar_mat_def by blast
qed

lemma similar_diag_mat_block_mat: assumes "\<And> A B. (A,B) \<in> set Ms \<Longrightarrow> similar_mat A B"
  shows "similar_mat (diag_block_mat (map fst Ms)) (diag_block_mat (map snd Ms))"
  using assms
proof (induct Ms)
  case Nil
  show ?case by (auto intro!: similar_mat_refl[of _ 0])
next
  case (Cons AB Ms)
  obtain A B where AB: "AB = (A,B)" by force
  from Cons(2)[of A B] have simAB: "similar_mat A B" unfolding AB by auto
  from similar_matD[OF this] obtain n where A: "A \<in> carrier_mat n n" and B: "B \<in> carrier_mat n n" by auto
  hence [simp]: "dim_row A = n" "dim_col A = n" "dim_row B = n" "dim_col B = n" by auto
  let ?C = "diag_block_mat (map fst Ms)" let ?D = "diag_block_mat (map snd Ms)"
  from Cons(1)[OF Cons(2)] have simRec: "similar_mat ?C ?D" by auto
  from similar_matD[OF this] obtain m where C: "?C \<in> carrier_mat m m" and D: "?D \<in> carrier_mat m m" by auto
  hence [simp]: "dim_row ?C = m" "dim_col ?C = m" "dim_row ?D = m" "dim_col ?D = m" by auto
  have "similar_mat (diag_block_mat (map fst (AB # Ms))) (diag_block_mat (map snd (AB # Ms)))
    = similar_mat (four_block_mat A (0\<^sub>m n m) (0\<^sub>m m n) ?C) (four_block_mat B (0\<^sub>m n m) (0\<^sub>m m n) ?D)"
    unfolding AB by (simp add: Let_def)
  also have "\<dots>"
    by (rule similar_mat_four_block_0_0[OF simAB simRec A C])
  finally show ?case .
qed

lemma similar_mat_wit_pow: assumes wit: "similar_mat_wit A B P Q"
  shows "similar_mat_wit (A ^\<^sub>m k) (B ^\<^sub>m k) P Q"
proof -
  define n where "n = dim_row A"
  let ?C = "carrier_mat n n"
  from similar_mat_witD[OF refl wit, folded n_def] have
    A: "A \<in> ?C" and B: "B \<in> ?C" and P: "P \<in> ?C" and Q: "Q \<in> ?C"
    and PQ: "P * Q = 1\<^sub>m n" and QP: "Q * P = 1\<^sub>m n"
    and AB: "A = P * B * Q"
    by auto
  from A B have *: "(A ^\<^sub>m k) \<in> carrier_mat n n" "B ^\<^sub>m k \<in> carrier_mat n n" by auto
  note carr = A B P Q
  have id: "A ^\<^sub>m k = P * B ^\<^sub>m k * Q" unfolding AB
  proof (induct k)
    case 0
    thus ?case using carr by (simp add: PQ)
  next
    case (Suc k)
    define Bk where "Bk = B ^\<^sub>m k"
    have Bk: "Bk \<in> carrier_mat n n" unfolding Bk_def using carr by simp
    have "(P * B * Q) ^\<^sub>m Suc k = (P * Bk * Q) * (P * B * Q)" by (simp add: Suc Bk_def)
    also have "\<dots> = P * (Bk * (Q * P) * B) * Q"
      using carr Bk by (simp add: assoc_mult_mat[of _ n n _ n _ n])
    also have "Bk * (Q * P) = Bk" unfolding QP using Bk by simp
    finally show ?case unfolding Bk_def by simp
  qed
  show ?thesis
    by (rule similar_mat_witI[OF PQ QP id * P Q])
qed

lemma similar_mat_wit_pow_id: "similar_mat_wit A B P Q \<Longrightarrow> A ^\<^sub>m k = P * B ^\<^sub>m k * Q"
  using similar_mat_wit_pow[of A B P Q k] unfolding similar_mat_wit_def Let_def by blast

subsection\<open>Homomorphism properties\<close>

context semiring_hom
begin
abbreviation mat_hom :: "'a mat \<Rightarrow> 'b mat" ("mat\<^sub>h")
  where "mat\<^sub>h \<equiv> map_mat hom"

abbreviation vec_hom :: "'a vec \<Rightarrow> 'b vec" ("vec\<^sub>h")
  where "vec\<^sub>h \<equiv> map_vec hom"

lemma vec_hom_zero: "vec\<^sub>h (0\<^sub>v n) = 0\<^sub>v n"
  by (rule eq_vecI, auto)

lemma mat_hom_one: "mat\<^sub>h (1\<^sub>m n) = 1\<^sub>m n"
  by (rule eq_matI, auto)

lemma mat_hom_mult: assumes A: "A \<in> carrier_mat nr n" and B: "B \<in> carrier_mat n nc"
  shows "mat\<^sub>h (A * B) = mat\<^sub>h A * mat\<^sub>h B"
proof -
  let ?L = "mat\<^sub>h (A * B)"
  let ?R = "mat\<^sub>h A * mat\<^sub>h B"
  let ?A = "mat\<^sub>h A"
  let ?B = "mat\<^sub>h B"
  from A B have id:
    "dim_row ?L = nr" "dim_row ?R = nr"
    "dim_col ?L = nc" "dim_col ?R = nc"  by auto
  show ?thesis
  proof (rule eq_matI, unfold id)
    fix i j
    assume *: "i < nr" "j < nc"
    define I where "I = {0 ..< n}"
    have id: "{0 ..< dim_vec (col ?B j)} = I" "{0 ..< dim_vec (col B j)} = I"
      unfolding I_def using * B by auto
    have finite: "finite I" unfolding I_def by auto
    have I: "I \<subseteq> {0 ..< n}" unfolding I_def by auto
    have "?L $$ (i,j) = hom (row A i \<bullet> col B j)" using A B * by auto
    also have "\<dots> = row ?A i \<bullet> col ?B j" unfolding scalar_prod_def id using finite I
    proof (induct I)
      case (insert k I)
      show ?case unfolding sum.insert[OF insert(1-2)] hom_add hom_mult
        using insert(3-) * A B by auto
    qed simp
    also have "\<dots> = ?R $$ (i,j)" using A B * by auto
    finally
    show "?L $$ (i, j) = ?R $$ (i, j)" .
  qed auto
qed

lemma mult_mat_vec_hom: assumes A: "A \<in> carrier_mat nr n" and v: "v \<in> carrier_vec n"
  shows "vec\<^sub>h (A *\<^sub>v v) = mat\<^sub>h A *\<^sub>v vec\<^sub>h v"
proof -
  let ?L = "vec\<^sub>h (A *\<^sub>v v)"
  let ?R = "mat\<^sub>h A *\<^sub>v vec\<^sub>h v"
  let ?A = "mat\<^sub>h A"
  let ?v = "vec\<^sub>h v"
  from A v have id:
    "dim_vec ?L = nr" "dim_vec ?R = nr"
    by auto
  show ?thesis
  proof (rule eq_vecI, unfold id)
    fix i
    assume *: "i < nr"
    define I where "I = {0 ..< n}"
    have id: "{0 ..< dim_vec v} = I" "{0 ..< dim_vec (vec\<^sub>h v)} = I"
      unfolding I_def using * v  by auto
    have finite: "finite I" unfolding I_def by auto
    have I: "I \<subseteq> {0 ..< n}" unfolding I_def by auto
    have "?L $ i = hom (row A i \<bullet> v)" using A v * by auto
    also have "\<dots> = row ?A i \<bullet> ?v" unfolding scalar_prod_def id using finite I
    proof (induct I)
      case (insert k I)
      show ?case unfolding sum.insert[OF insert(1-2)] hom_add hom_mult
        using insert(3-) * A v by auto
    qed simp
    also have "\<dots> = ?R $ i" using A v * by auto
    finally
    show "?L $ i = ?R $ i" .
  qed auto
qed
end

lemma vec_eq_iff: "(x = y) = (dim_vec x = dim_vec y \<and> (\<forall> i < dim_vec y. x $ i = y $ i))" (is "?l = ?r")
proof
  assume ?r
  show ?l
    by (rule eq_vecI, insert \<open>?r\<close>, auto)
qed simp

lemma mat_eq_iff: "(x = y) = (dim_row x = dim_row y \<and> dim_col x = dim_col y \<and>
  (\<forall> i j. i < dim_row y \<longrightarrow> j < dim_col y \<longrightarrow> x $$ (i,j) = y $$ (i,j)))" (is "?l = ?r")
proof
  assume ?r
  show ?l
    by (rule eq_matI, insert \<open>?r\<close>, auto)
qed simp

lemma (in inj_semiring_hom) vec_hom_zero_iff[simp]: "(vec\<^sub>h x = 0\<^sub>v n) = (x = 0\<^sub>v n)"
proof -
  {
    fix i
    assume i: "i < n" "dim_vec x = n"
    hence "vec\<^sub>h x $ i = 0 \<longleftrightarrow> x $ i = 0"
      using index_map_vec(1)[of i x] by simp
  } note main = this
  show ?thesis unfolding vec_eq_iff by (simp, insert main, auto)
qed

lemma (in inj_semiring_hom) mat_hom_inj: "mat\<^sub>h A = mat\<^sub>h B \<Longrightarrow> A = B"
  unfolding mat_eq_iff by auto

lemma (in inj_semiring_hom) vec_hom_inj: "vec\<^sub>h v = vec\<^sub>h w \<Longrightarrow> v = w"
  unfolding vec_eq_iff by auto

lemma (in semiring_hom) mat_hom_pow: assumes A: "A \<in> carrier_mat n n"
  shows "mat\<^sub>h (A ^\<^sub>m k) = (mat\<^sub>h A) ^\<^sub>m k"
proof (induct k)
  case (Suc k)
  thus ?case using mat_hom_mult[OF pow_carrier_mat[OF A, of k] A] by simp
qed (simp add: mat_hom_one)

lemma (in semiring_hom) hom_sum_mat: "hom (sum_mat A) = sum_mat (mat\<^sub>h A)"
proof -
  obtain B where id: "?thesis = (hom (sum (($$) A) B) = sum (($$) (mat\<^sub>h A)) B)"
    and B: "B \<subseteq> {0..<dim_row A} \<times> {0..<dim_col A}"
  unfolding sum_mat_def by auto
  from B have "finite B"
    using finite_subset by blast
  thus ?thesis unfolding id using B
  proof (induct B)
    case (insert x F)
    show ?case unfolding sum.insert[OF insert(1-2)] hom_add
      using insert(3-) by auto
  qed simp
qed

lemma (in semiring_hom) vec_hom_smult: "vec\<^sub>h (ev \<cdot>\<^sub>v v) = hom ev \<cdot>\<^sub>v vec\<^sub>h v"
  by (rule eq_vecI, auto simp: hom_distribs)

lemma minus_scalar_prod_distrib: fixes v\<^sub>1 :: "'a :: ring vec"
  assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n" "v\<^sub>3 \<in> carrier_vec n"
  shows "(v\<^sub>1 - v\<^sub>2) \<bullet> v\<^sub>3 = v\<^sub>1 \<bullet> v\<^sub>3 - v\<^sub>2 \<bullet> v\<^sub>3"
  unfolding minus_add_uminus_vec[OF v(1-2)]
  by (subst add_scalar_prod_distrib[OF v(1)], insert v, auto)

lemma scalar_prod_minus_distrib: fixes v\<^sub>1 :: "'a :: ring vec"
  assumes v: "v\<^sub>1 \<in> carrier_vec n" "v\<^sub>2 \<in> carrier_vec n" "v\<^sub>3 \<in> carrier_vec n"
  shows "v\<^sub>1 \<bullet> (v\<^sub>2 - v\<^sub>3) = v\<^sub>1 \<bullet> v\<^sub>2 - v\<^sub>1 \<bullet> v\<^sub>3"
  unfolding minus_add_uminus_vec[OF v(2-3)]
  by (subst scalar_prod_add_distrib[OF v(1)], insert v, auto)

lemma uminus_add_minus_vec:
  assumes "l \<in> carrier_vec n" "r \<in> carrier_vec n"
  shows "- ((l::'a :: ab_group_add vec) + r) = (- l - r)"
  using assms by auto

lemma minus_add_minus_vec: fixes u :: "'a :: ab_group_add vec"
  assumes "u \<in> carrier_vec n" "v \<in> carrier_vec n" "w \<in> carrier_vec n"
  shows "u - (v + w) = u - v - w"
  using assms by auto

lemma uminus_add_minus_mat:
  assumes "l \<in> carrier_mat nr nc" "r \<in> carrier_mat nr nc"
  shows "- ((l::'a :: ab_group_add mat) + r) = (- l - r)"
  using assms by auto

lemma minus_add_minus_mat: fixes u :: "'a :: ab_group_add mat"
  assumes "u \<in> carrier_mat nr nc" "v \<in> carrier_mat nr nc" "w \<in> carrier_mat nr nc"
  shows "u - (v + w) = u - v - w"
  using assms by auto

lemma uminus_uminus_vec[simp]: "- (- (v::'a:: group_add vec)) = v"
  by auto

lemma uminus_eq_vec[simp]: "- (v::'a:: group_add vec) = - w \<longleftrightarrow> v = w"
  by (metis uminus_uminus_vec)

lemma uminus_uminus_mat[simp]: "- (- (A::'a:: group_add mat)) = A"
  by auto

lemma uminus_eq_mat[simp]: "- (A::'a:: group_add mat) = - B \<longleftrightarrow> A = B"
  by (metis uminus_uminus_mat)

lemma smult_zero_mat[simp]: "(k :: 'a :: mult_zero) \<cdot>\<^sub>m 0\<^sub>m nr nc = 0\<^sub>m nr nc"
  by (intro eq_matI, auto)

lemma similar_mat_wit_smult: fixes A :: "'a :: comm_ring_1 mat"
  assumes "similar_mat_wit A B P Q"
  shows "similar_mat_wit (k \<cdot>\<^sub>m A) (k \<cdot>\<^sub>m B) P Q"
proof -
  define n where "n = dim_row A"
  note main = similar_mat_witD[OF n_def assms]
  show ?thesis
    by (rule similar_mat_witI[OF main(1-2) _ _ _ main(6-7)], insert main(3-), auto
      simp: mult_smult_distrib mult_smult_assoc_mat[of _ n n _ n])
qed

lemma similar_mat_smult: fixes A :: "'a :: comm_ring_1 mat"
  assumes "similar_mat A B"
  shows "similar_mat (k \<cdot>\<^sub>m A) (k \<cdot>\<^sub>m B)"
  using similar_mat_wit_smult assms unfolding similar_mat_def by blast

definition mat_diag :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: zero) \<Rightarrow> 'a mat" where
  "mat_diag n f = Matrix.mat n n (\<lambda> (i,j). if i = j then f j else 0)"

lemma mat_diag_dim[simp]: "mat_diag n f \<in> carrier_mat n n"
  unfolding mat_diag_def by auto

lemma mat_diag_mult_left: assumes A: "A \<in> carrier_mat n nr"
  shows "mat_diag n f * A = Matrix.mat n nr (\<lambda> (i,j). f i * A $$ (i,j))"
proof (rule eq_matI, insert A, auto simp: mat_diag_def scalar_prod_def, goal_cases)
  case (1 i j)
  thus ?case by (subst sum.remove[of _ i], auto)
qed

lemma mat_diag_mult_right: assumes A: "A \<in> carrier_mat nr n"
  shows "A * mat_diag n f = Matrix.mat nr n (\<lambda> (i,j). A $$ (i,j) * f j)"
proof (rule eq_matI, insert A, auto simp: mat_diag_def scalar_prod_def, goal_cases)
  case (1 i j)
  thus ?case by (subst sum.remove[of _ j], auto)
qed

lemma mat_diag_diag[simp]: "mat_diag n f * mat_diag n g = mat_diag n (\<lambda> i. f i * g i)"
  by (subst mat_diag_mult_left[of _ n n], auto simp: mat_diag_def)

lemma mat_diag_one[simp]: "mat_diag n (\<lambda> x. 1) = 1\<^sub>m n" unfolding mat_diag_def by auto

text \<open>Interpret vector as row-matrix\<close>

definition "mat_of_row y = mat 1 (dim_vec y) (\<lambda> ij. y $ (snd ij))" 

lemma mat_of_row_carrier[simp,intro]: 
  "y \<in> carrier_vec n \<Longrightarrow> mat_of_row y \<in> carrier_mat 1 n"
  "y \<in> carrier_vec n \<Longrightarrow> mat_of_row y \<in> carrier_mat (Suc 0) n"
  unfolding mat_of_row_def by auto

lemma mat_of_row_dim[simp]: "dim_row (mat_of_row y) = 1" 
  "dim_col (mat_of_row y) = dim_vec y" 
  unfolding mat_of_row_def by auto

lemma mat_of_row_index[simp]: "x < dim_vec y \<Longrightarrow> mat_of_row y $$ (0,x) = y $ x" 
  unfolding mat_of_row_def by auto

lemma row_mat_of_row[simp]: "row (mat_of_row y) 0 = y" 
  by auto

lemma mat_of_row_mult_append_rows: assumes y1: "y1 \<in> carrier_vec nr1" 
  and y2: "y2 \<in> carrier_vec nr2" 
  and A1: "A1 \<in> carrier_mat nr1 nc" 
  and A2: "A2 \<in> carrier_mat nr2 nc" 
shows "mat_of_row (y1 @\<^sub>v y2) * (A1 @\<^sub>r A2) = 
  mat_of_row y1 * A1 + mat_of_row y2 * A2" 
proof -
  from A1 A2 have dim: "dim_row A1 = nr1" "dim_row A2 = nr2" by auto
  let ?M1 = "mat_of_row y1" 
  have M1: "?M1 \<in> carrier_mat 1 nr1" using y1 by auto
  let ?M2 = "mat_of_row y2" 
  have M2: "?M2 \<in> carrier_mat 1 nr2" using y2 by auto
  let ?M3 = "0\<^sub>m 0 nr1" 
  let ?M4 = "0\<^sub>m 0 nr2" 
  note z = zero_carrier_mat
  have id: "mat_of_row (y1 @\<^sub>v y2) = four_block_mat 
    ?M1 ?M2 ?M3 ?M4" using y1 y2 
    by (intro eq_matI, auto simp: mat_of_rows_def)
  show ?thesis
    unfolding id append_rows_def dim
    by (subst mult_four_block_mat[OF M1 M2 z z A1 z A2 z], insert A1 A2, auto)
qed


text \<open>Allowing to construct and deconstruct vectors like lists\<close>
abbreviation vNil where "vNil \<equiv> vec 0 ((!) [])"
definition vCons where "vCons a v \<equiv> vec (Suc (dim_vec v)) (\<lambda>i. case i of 0 \<Rightarrow> a | Suc i \<Rightarrow> v $ i)"

lemma vec_index_vCons_0 [simp]: "vCons a v $ 0 = a"
  by (simp add: vCons_def)

lemma vec_index_vCons_Suc [simp]:
  fixes v :: "'a vec"
  shows "vCons a v $ Suc n = v $ n"
proof-
  have 1: "vec (Suc d) f $ Suc n = vec d (f \<circ> Suc) $ n" for d and f :: "nat \<Rightarrow> 'a"
    by (transfer, auto simp: mk_vec_def)
  show ?thesis
    apply (auto simp: 1 vCons_def o_def) apply transfer apply (auto simp: mk_vec_def)
    done
qed

lemma vec_index_vCons: "vCons a v $ n = (if n = 0 then a else v $ (n - 1))"
  by (cases n, auto)

lemma dim_vec_vCons [simp]: "dim_vec (vCons a v) = Suc (dim_vec v)"
  by (simp add: vCons_def)

lemma vCons_carrier_vec[simp]: "vCons a v \<in> carrier_vec (Suc n) \<longleftrightarrow> v \<in> carrier_vec n"
  by (auto dest!: carrier_vecD intro: carrier_vecI)

lemma vec_Suc: "vec (Suc n) f = vCons (f 0) (vec n (f \<circ> Suc))" (is "?l = ?r")
proof (unfold vec_eq_iff, intro conjI allI impI)
  fix i assume "i < dim_vec ?r"
  then show "?l $ i = ?r $ i" by (cases i, auto)
qed simp

declare Abs_vec_cases[cases del]

lemma vec_cases [case_names vNil vCons, cases type: vec]:
  assumes "v = vNil \<Longrightarrow> thesis" and "\<And>a w. v = vCons a w \<Longrightarrow> thesis"
  shows "thesis"
proof (cases "dim_vec v")
  case 0 then show thesis by (intro assms(1), auto)
next
  case (Suc n)
  show thesis
  proof (rule assms(2))
    show v: "v = vCons (v $ 0) (vec n (\<lambda>i. v $ Suc i))" (is "v = ?r")
    proof (rule eq_vecI, unfold dim_vec_vCons dim_vec Suc)
      fix i
      assume "i < Suc n"
      then show "v $ i = ?r $ i" by (cases i, auto simp: vCons_def)
    qed simp
  qed
qed

lemma vec_induct [case_names vNil vCons, induct type: vec]:
  assumes "P vNil" and "\<And>a v. P v \<Longrightarrow> P (vCons a v)"
  shows "P v"
proof (induct "dim_vec v" arbitrary:v)
  case 0 then show ?case by (cases v, auto intro: assms(1))
next
  case (Suc n) then show ?case by (cases v, auto intro: assms(2))
qed

lemma carrier_vec_induct [consumes 1, case_names 0 Suc, induct set:carrier_vec]:
  assumes v: "v \<in> carrier_vec n"
    and 1: "P 0 vNil" and 2: "\<And>n a v. v \<in> carrier_vec n \<Longrightarrow> P n v \<Longrightarrow> P (Suc n) (vCons a v)"
  shows "P n v"
proof (insert v, induct n arbitrary: v)
  case 0 then have "v = vec 0 ((!) [])" by auto
  with 1 show ?case by auto
next
  case (Suc n) then show ?case by (cases v, auto dest!: carrier_vecD intro:2)
qed

lemma vec_of_list_Cons[simp]: "vec_of_list (a#as) = vCons a (vec_of_list as)"
  by (unfold vCons_def, transfer, auto simp:mk_vec_def split:nat.split)

lemma vec_of_list_Nil[simp]: "vec_of_list [] = vNil"
  by (transfer', auto)

lemma scalar_prod_vCons[simp]:
  "vCons a v \<bullet> vCons b w = a * b + v \<bullet> w"
  apply (unfold scalar_prod_def atLeast0_lessThan_Suc_eq_insert_0 dim_vec_vCons)
  apply (subst sum.insert) apply (simp,simp)
  apply (subst sum.reindex) apply force
  apply simp
  done

lemma zero_vec_Suc: "0\<^sub>v (Suc n) = vCons 0 (0\<^sub>v n)"
  by (auto simp: zero_vec_def vec_Suc o_def)

lemma zero_vec_zero[simp]: "0\<^sub>v 0 = vNil" by auto

lemma vCons_eq_vCons[simp]: "vCons a v = vCons b w \<longleftrightarrow> a = b \<and> v = w" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  note arg_cong[OF this]
  from this[of dim_vec] this[of "\<lambda>x. x$0"] this[of "\<lambda>x. x$Suc _"]
  show ?r by (auto simp: vec_eq_iff)
qed simp

lemma vec_carrier_vec[simp]: "vec n f \<in> carrier_vec m \<longleftrightarrow> n = m"
  unfolding carrier_vec_def by auto

notation transpose_mat ("(_\<^sup>T)" [1000])

lemma map_mat_transpose: "(map_mat f A)\<^sup>T = map_mat f A\<^sup>T" by auto

lemma cols_transpose[simp]: "cols A\<^sup>T = rows A" unfolding cols_def rows_def by auto
lemma rows_transpose[simp]: "rows A\<^sup>T = cols A" unfolding cols_def rows_def by auto
lemma list_of_vec_vec [simp]: "list_of_vec (vec n f) = map f [0..<n]"
  by (transfer, auto simp: mk_vec_def)

lemma list_of_vec_0 [simp]: "list_of_vec (0\<^sub>v n) = replicate n 0"
  by (simp add: zero_vec_def map_replicate_trivial)

lemma diag_mat_map:
  assumes M_carrier: "M \<in> carrier_mat n n"
  shows "diag_mat (map_mat f M) = map f (diag_mat M)"
proof -
  have dim_eq: "dim_row M = dim_col M" using M_carrier by auto
  have m: "map_mat f M $$ (i, i) = f (M $$ (i, i))" if i: "i < dim_row M" for i
    using dim_eq i by auto
  show ?thesis
    by (rule nth_equalityI, insert m, auto simp add: diag_mat_def M_carrier)
qed

lemma mat_of_rows_map [simp]:
  assumes x: "set vs \<subseteq> carrier_vec n"
  shows "mat_of_rows n (map (map_vec f) vs) = map_mat f (mat_of_rows n vs)"
proof-
  have "\<forall>x\<in>set vs. dim_vec x = n" using x by auto
  then show ?thesis by (auto simp add: mat_eq_iff map_vec_def mat_of_rows_def)
qed

lemma mat_of_cols_map [simp]:
  assumes x: "set vs \<subseteq> carrier_vec n"
  shows "mat_of_cols n (map (map_vec f) vs) = map_mat f (mat_of_cols n vs)"
proof-
  have "\<forall>x\<in>set vs. dim_vec x = n" using x by auto
  then show ?thesis by (auto simp add: mat_eq_iff map_vec_def mat_of_cols_def)
qed

lemma vec_of_list_map [simp]: "vec_of_list (map f xs) = map_vec f (vec_of_list xs)"
  unfolding map_vec_def by (transfer, auto simp add: mk_vec_def)

lemma map_vec: "map_vec f (vec n g) = vec n (f o g)" by auto

lemma mat_of_cols_Cons_index_0: "i < n \<Longrightarrow> mat_of_cols n (w # ws) $$ (i, 0) = w $ i"
  by (unfold mat_of_cols_def, transfer', auto simp: mk_mat_def)

lemma nth_map_out_of_bound: "i \<ge> length xs \<Longrightarrow> map f xs ! i = [] ! (i - length xs)"
  by (induct xs arbitrary:i, auto)

lemma mat_of_cols_Cons_index_Suc:
  "i < n \<Longrightarrow> mat_of_cols n (w # ws) $$ (i, Suc j) = mat_of_cols n ws $$ (i,j)"
  by (unfold mat_of_cols_def, transfer, auto simp: mk_mat_def undef_mat_def nth_append nth_map_out_of_bound)

lemma mat_of_cols_index: "i < n \<Longrightarrow> j < length ws \<Longrightarrow> mat_of_cols n ws $$ (i,j) = ws ! j $ i"
  by (unfold mat_of_cols_def, auto)

lemma mat_of_rows_index: "i < length rs \<Longrightarrow> j < n \<Longrightarrow> mat_of_rows n rs $$ (i,j) = rs ! i $ j"
  by (unfold mat_of_rows_def, auto)

lemma transpose_mat_of_rows: "(mat_of_rows n vs)\<^sup>T = mat_of_cols n vs"
  by (auto intro!: eq_matI simp: mat_of_rows_index mat_of_cols_index)

lemma transpose_mat_of_cols: "(mat_of_cols n vs)\<^sup>T = mat_of_rows n vs"
  by (auto intro!: eq_matI simp: mat_of_rows_index mat_of_cols_index)

lemma nth_list_of_vec [simp]:
  assumes "i < dim_vec v" shows "list_of_vec v ! i = v $ i"
  using assms by (transfer, auto)

lemma length_list_of_vec [simp]:
  "length (list_of_vec v) = dim_vec v" by (transfer, auto)

lemma vec_eq_0_iff:
  "v = 0\<^sub>v n \<longleftrightarrow> n = dim_vec v \<and> (n = 0 \<or> set (list_of_vec v) = {0})" (is "?l \<longleftrightarrow> ?r")
proof
  show "?l \<Longrightarrow> ?r" by auto
  show "?r \<Longrightarrow> ?l" by (intro iffI eq_vecI, force simp: set_conv_nth, force)
qed

lemma list_of_vec_vCons[simp]: "list_of_vec (vCons a v) = a # list_of_vec v" (is "?l = ?r")
proof (intro nth_equalityI)
  fix i
  assume "i < length ?l"
  then show "?l ! i = ?r ! i" by (cases i, auto)
qed simp

lemma append_vec_vCons[simp]: "vCons a v @\<^sub>v w = vCons a (v @\<^sub>v w)" (is "?l = ?r")
proof (unfold vec_eq_iff, intro conjI allI impI)
  fix i assume "i < dim_vec ?r"
  then show "?l $ i = ?r $ i" by (cases i; subst index_append_vec, auto)
qed simp

lemma append_vec_vNil[simp]: "vNil @\<^sub>v v = v"
  by (unfold vec_eq_iff, auto)

lemma list_of_vec_append[simp]: "list_of_vec (v @\<^sub>v w) = list_of_vec v @ list_of_vec w"
  by (induct v, auto)

lemma transpose_mat_eq[simp]: "A\<^sup>T = B\<^sup>T \<longleftrightarrow> A = B"
  using transpose_transpose by metis

lemma mat_col_eqI: assumes cols: "\<And> i. i < dim_col B \<Longrightarrow> col A i = col B i"
  and dims: "dim_row A = dim_row B" "dim_col A = dim_col B"
shows "A = B"
  by(subst transpose_mat_eq[symmetric], rule eq_rowI,insert assms,auto)

lemma upper_triangular_imp_distinct:
  assumes A: "A \<in> carrier_mat n n"
    and tri: "upper_triangular A"
    and diag: "0 \<notin> set (diag_mat A)"
  shows "distinct (rows A)"
proof-
  { fix i and j
    assume eq: "rows A ! i = rows A ! j" and ij: "i < j" and jn: "j < n"
    from tri A ij jn have "rows A ! j $ i = 0" by (auto dest!:upper_triangularD)
    with eq have "rows A ! i $ i = 0" by auto
    with diag ij jn A have False by (auto simp: diag_mat_def)
  }
  with A show ?thesis by (force simp: distinct_conv_nth nat_neq_iff)
qed

lemma dim_vec_of_list[simp] :"dim_vec (vec_of_list as) = length as" by transfer auto

lemma list_vec: "list_of_vec (vec_of_list xs) = xs"
by (transfer, metis (mono_tags, lifting) atLeastLessThan_iff map_eq_conv map_nth mk_vec_def old.prod.case set_upt)

lemma vec_list: "vec_of_list (list_of_vec v) = v"
apply transfer unfolding mk_vec_def by auto

lemma index_vec_of_list: "i<length xs \<Longrightarrow> (vec_of_list xs) $ i = xs ! i"
by (metis vec.abs_eq index_vec vec_of_list.abs_eq)

lemma vec_of_list_index: "vec_of_list xs $ j = xs ! j"
  apply transfer unfolding mk_vec_def unfolding undef_vec_def
  by (simp, metis append_Nil2 nth_append)

lemma list_of_vec_index: "list_of_vec v ! j = v $ j"
  by (metis vec_list vec_of_list_index)

lemma list_of_vec_map: "list_of_vec xs = map (($) xs) [0..<dim_vec xs]" by transfer auto

definition "component_mult v w = vec (min (dim_vec v) (dim_vec w)) (\<lambda>i. v $ i * w $ i)"
definition vec_set::"'a vec \<Rightarrow> 'a set" ("set\<^sub>v")
  where "vec_set v = vec_index v ` {..<dim_vec v}"

lemma index_component_mult:
assumes "i < dim_vec v" "i < dim_vec w"
shows "component_mult v w $ i = v $ i * w $ i"
  unfolding component_mult_def using assms index_vec by auto

lemma dim_component_mult:
"dim_vec (component_mult v w) = min (dim_vec v) (dim_vec w)"
  unfolding component_mult_def using index_vec by auto

lemma vec_setE:
assumes "a \<in> set\<^sub>v v"
obtains i where "v$i = a" "i<dim_vec v" using assms unfolding vec_set_def by blast

lemma vec_setI:
assumes "v$i = a" "i<dim_vec v"
shows "a \<in> set\<^sub>v v" using assms unfolding vec_set_def using image_eqI lessThan_iff by blast

lemma set_list_of_vec: "set (list_of_vec v) = set\<^sub>v v" unfolding vec_set_def by transfer auto


instantiation vec :: (conjugate) conjugate
begin

definition conjugate_vec :: "'a :: conjugate vec \<Rightarrow> 'a vec"
  where "conjugate v = vec (dim_vec v) (\<lambda>i. conjugate (v $ i))"

lemma conjugate_vCons [simp]:
  "conjugate (vCons a v) = vCons (conjugate a) (conjugate v)"
  by (auto simp: vec_Suc conjugate_vec_def)

lemma dim_vec_conjugate[simp]: "dim_vec (conjugate v) = dim_vec v"
  unfolding conjugate_vec_def by auto

lemma carrier_vec_conjugate[simp]: "v \<in> carrier_vec n \<Longrightarrow> conjugate v \<in> carrier_vec n"
  by (auto intro!: carrier_vecI)

lemma vec_index_conjugate[simp]:
  shows "i < dim_vec v \<Longrightarrow> conjugate v $ i = conjugate (v $ i)"
  unfolding conjugate_vec_def by auto

instance
proof
  fix v w :: "'a vec"
  show "conjugate (conjugate v) = v" by (induct v, auto simp: conjugate_vec_def)
  let ?v = "conjugate v"
  let ?w = "conjugate w"
  show "conjugate v = conjugate w \<longleftrightarrow> v = w"
  proof(rule iffI)
    assume cvw: "?v = ?w" show "v = w"
    proof(rule)
      have "dim_vec ?v = dim_vec ?w" using cvw by auto
      then show dim: "dim_vec v = dim_vec w" by simp
      fix i assume i: "i < dim_vec w"
      then have "conjugate v $ i = conjugate w $ i" using cvw by auto
      then have "conjugate (v$i) = conjugate (w $ i)" using i dim by auto
      then show "v $ i = w $ i" by auto
    qed
  qed auto
qed

end

lemma conjugate_add_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  assumes dim: "v : carrier_vec n" "w : carrier_vec n"
  shows "conjugate (v + w) = conjugate v + conjugate w"
  by (rule, insert dim, auto simp: conjugate_dist_add)

lemma uminus_conjugate_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  shows "- (conjugate v) = conjugate (- v)"
  by (rule, auto simp:conjugate_neg)

lemma conjugate_zero_vec[simp]:
  "conjugate (0\<^sub>v n :: 'a :: conjugatable_ring vec) = 0\<^sub>v n" by auto

lemma conjugate_vec_0[simp]:
  "conjugate (vec 0 f) = vec 0 f" by auto

lemma sprod_vec_0[simp]: "v \<bullet> vec 0 f = 0"
  by(auto simp: scalar_prod_def)

lemma conjugate_zero_iff_vec[simp]:
  fixes v :: "'a :: conjugatable_ring vec"
  shows "conjugate v = 0\<^sub>v n \<longleftrightarrow> v = 0\<^sub>v n"
  using conjugate_cancel_iff[of _ "0\<^sub>v n :: 'a vec"] by auto

lemma conjugate_smult_vec:
  fixes k :: "'a :: conjugatable_ring"
  shows "conjugate (k \<cdot>\<^sub>v v) = conjugate k \<cdot>\<^sub>v conjugate v"
  using conjugate_dist_mul by (intro eq_vecI, auto)

lemma conjugate_sprod_vec:
  fixes v w :: "'a :: conjugatable_ring vec"
  assumes v: "v : carrier_vec n" and w: "w : carrier_vec n"
  shows "conjugate (v \<bullet> w) = conjugate v \<bullet> conjugate w"
proof (insert w v, induct w arbitrary: v rule:carrier_vec_induct)
  case 0 then show ?case by (cases v, auto)
next
  case (Suc n b w) then show ?case
    by (cases v, auto dest: carrier_vecD simp:conjugate_dist_add conjugate_dist_mul)
qed 

abbreviation cscalar_prod :: "'a vec \<Rightarrow> 'a vec \<Rightarrow> 'a :: conjugatable_ring" (infix "\<bullet>c" 70)
  where "(\<bullet>c) \<equiv> \<lambda>v w. v \<bullet> conjugate w"

lemma conjugate_conjugate_sprod[simp]:
  assumes v[simp]: "v : carrier_vec n" and w[simp]: "w : carrier_vec n"
  shows "conjugate (conjugate v \<bullet> w) = v \<bullet>c w"
  apply (subst conjugate_sprod_vec[of _ n]) by auto

lemma conjugate_vec_sprod_comm:
  fixes v w :: "'a :: {conjugatable_ring, comm_ring} vec"
  assumes "v : carrier_vec n" and "w : carrier_vec n"
  shows "v \<bullet>c w = (conjugate w \<bullet> v)"
  unfolding scalar_prod_def using assms by(subst sum.ivl_cong, auto simp: ac_simps)

lemma conjugate_square_ge_0_vec[intro!]:
  fixes v :: "'a :: conjugatable_ordered_ring vec"
  shows "v \<bullet>c v \<ge> 0"
proof (induct v)
  case vNil
  then show ?case by auto
next
  case (vCons a v)
  then show ?case using conjugate_square_positive[of a] by auto
qed

lemma conjugate_square_eq_0_vec[simp]:
  fixes v :: "'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors} vec"
  assumes "v \<in> carrier_vec n"
  shows "v \<bullet>c v = 0 \<longleftrightarrow> v = 0\<^sub>v n"
proof (insert assms, induct rule: carrier_vec_induct)
  case 0
  then show ?case by auto
next
  case (Suc n a v)
  then show ?case
    using conjugate_square_positive[of a] conjugate_square_ge_0_vec[of v]
    by (auto simp: le_less add_nonneg_eq_0_iff zero_vec_Suc)
qed

lemma conjugate_square_greater_0_vec[simp]:
  fixes v :: "'a :: {conjugatable_ordered_ring,semiring_no_zero_divisors} vec"
  assumes "v \<in> carrier_vec n"
  shows "v \<bullet>c v > 0 \<longleftrightarrow> v \<noteq> 0\<^sub>v n"
  using assms by (auto simp: less_le)

lemma vec_conjugate_rat[simp]: "(conjugate :: rat vec \<Rightarrow> rat vec) = (\<lambda>x. x)" by force
lemma vec_conjugate_real[simp]: "(conjugate :: real vec \<Rightarrow> real vec) = (\<lambda>x. x)" by force


end
