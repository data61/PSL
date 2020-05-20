(* Author: Alexander Maletzky *)

section \<open>Computable Term Orders\<close>

theory Term_Order
  imports OAlist_Poly_Mapping "HOL-Library.Product_Lexorder"
begin

subsection \<open>Type Class \<open>nat\<close>\<close>

class nat = zero + plus + minus + order + equal +
  fixes rep_nat :: "'a \<Rightarrow> nat"
    and abs_nat :: "nat \<Rightarrow> 'a"
  assumes rep_inverse [simp]: "abs_nat (rep_nat x) = x"
    and abs_inverse [simp]: "rep_nat (abs_nat n) = n"
    and abs_zero [simp]: "abs_nat 0 = 0"
    and abs_plus: "abs_nat m + abs_nat n = abs_nat (m + n)"
    and abs_minus: "abs_nat m - abs_nat n = abs_nat (m - n)"
    and abs_ord: "m \<le> n \<Longrightarrow> abs_nat m \<le> abs_nat n"
begin

lemma rep_inj:
  assumes "rep_nat x = rep_nat y"
  shows "x = y"
proof -
  have "abs_nat (rep_nat x) = abs_nat (rep_nat y)" by (simp only: assms)
  thus ?thesis by (simp only: rep_inverse)
qed

corollary rep_eq_iff: "(rep_nat x = rep_nat y) \<longleftrightarrow> (x = y)"
  by (auto elim: rep_inj)

lemma abs_inj:
  assumes "abs_nat m = abs_nat n"
  shows "m = n"
proof -
  have "rep_nat (abs_nat m) = rep_nat (abs_nat n)" by (simp only: assms)
  thus ?thesis by (simp only: abs_inverse)
qed

corollary abs_eq_iff: "(abs_nat m = abs_nat n) \<longleftrightarrow> (m = n)"
  by (auto elim: abs_inj)

lemma rep_zero [simp]: "rep_nat 0 = 0"
  using abs_inverse abs_zero by fastforce

lemma rep_zero_iff: "(rep_nat x = 0) \<longleftrightarrow> (x = 0)"
  using rep_eq_iff by fastforce

lemma plus_eq: "x + y = abs_nat (rep_nat x + rep_nat y)"
  by (metis abs_plus rep_inverse)

lemma rep_plus: "rep_nat (x + y) = rep_nat x + rep_nat y"
  by (simp add: plus_eq)

lemma minus_eq: "x - y = abs_nat (rep_nat x - rep_nat y)"
  by (metis abs_minus rep_inverse)

lemma rep_minus: "rep_nat (x - y) = rep_nat x - rep_nat y"
  by (simp add: minus_eq)

lemma ord_iff:
  "x \<le> y \<longleftrightarrow> rep_nat x \<le> rep_nat y" (is ?thesis1)
  "x < y \<longleftrightarrow> rep_nat x < rep_nat y" (is ?thesis2)
proof -
  show ?thesis1
  proof
    assume "x \<le> y"
    show "rep_nat x \<le> rep_nat y"
    proof (rule ccontr)
      assume "\<not> rep_nat x \<le> rep_nat y"
      hence "rep_nat y \<le> rep_nat x" and "rep_nat x \<noteq> rep_nat y" by simp_all
      from this(1) have "abs_nat (rep_nat y) \<le> abs_nat (rep_nat x)" by (rule abs_ord)
      hence "y \<le> x" by (simp only: rep_inverse)
      moreover from \<open>rep_nat x \<noteq> rep_nat y\<close> have "y \<noteq> x" using rep_inj by auto
      ultimately have "y < x" by simp
      with \<open>x \<le> y\<close> show False by simp
    qed
  next
    assume "rep_nat x \<le> rep_nat y"
    hence "abs_nat (rep_nat x) \<le> abs_nat (rep_nat y)" by (rule abs_ord)
    thus "x \<le> y" by (simp only: rep_inverse)
  qed
  thus ?thesis2 using rep_inj[of x y] by (auto simp: less_le Nat.nat_less_le)
qed

lemma ex_iff_abs: "(\<exists>x::'a. P x) \<longleftrightarrow> (\<exists>n::nat. P (abs_nat n))"
  by (metis rep_inverse)

lemma ex_iff_abs': "(\<exists>x<abs_nat m. P x) \<longleftrightarrow> (\<exists>n::nat<m. P (abs_nat n))"
  by (metis abs_inverse rep_inverse ord_iff(2))

lemma all_iff_abs: "(\<forall>x::'a. P x) \<longleftrightarrow> (\<forall>n::nat. P (abs_nat n))"
  by (metis rep_inverse)

lemma all_iff_abs': "(\<forall>x<abs_nat m. P x) \<longleftrightarrow> (\<forall>n::nat<m. P (abs_nat n))"
  by (metis abs_inverse rep_inverse ord_iff(2))

subclass linorder by (standard, auto simp: ord_iff rep_inj)

lemma comparator_of_rep [simp]: "comparator_of (rep_nat x) (rep_nat y) = comparator_of x y"
  by (simp add: comparator_of_def linorder_class.comparator_of_def ord_iff rep_inj)

subclass wellorder
proof
  fix P::"'a \<Rightarrow> bool" and a::'a
  let ?P = "\<lambda>n::nat. P (abs_nat n)"
  assume a: "\<And>x. (\<And>y. y < x \<Longrightarrow> P y) \<Longrightarrow> P x"
  have "P (abs_nat (rep_nat a))"
  proof (rule less_induct[of _ "rep_nat a"])
    fix n::nat
    assume b: "\<And>m. m < n \<Longrightarrow> ?P m"
    show "?P n"
    proof (rule a)
      fix y
      assume "y < abs_nat n"
      hence "rep_nat y < n" by (simp only: ord_iff abs_inverse)
      hence "?P (rep_nat y)" by (rule b)
      thus "P y" by (simp only: rep_inverse)
    qed
  qed
  thus "P a" by (simp only: rep_inverse)
qed

subclass comm_monoid_add by (standard, auto simp: plus_eq intro: arg_cong)

lemma sum_rep: "sum (rep_nat \<circ> f) A = rep_nat (sum f A)" for f :: "'b \<Rightarrow> 'a" and A :: "'b set"
proof (induct A rule: infinite_finite_induct)
  case (infinite A)
  thus ?case by simp
next
  case empty
  show ?case by simp
next
  case (insert a A)
  from insert(1, 2) show ?case by (simp del: comp_apply add: insert(3) rep_plus, simp)
qed

subclass ordered_comm_monoid_add by (standard, simp add: ord_iff plus_eq)

subclass countable by intro_classes (intro exI[of _ rep_nat] injI, elim rep_inj)

subclass cancel_comm_monoid_add
  apply standard
  subgoal by (simp add: minus_eq rep_plus)
  subgoal by (simp add: minus_eq rep_plus)
  done

subclass add_wellorder
  apply standard
  subgoal by (simp add: ord_iff rep_plus)
  subgoal unfolding ord_iff by (drule le_imp_add, metis abs_plus rep_inverse)
  subgoal by (simp add: ord_iff)
  done

end

lemma the_min_eq_zero: "the_min = (0::'a::{the_min,nat})"
proof -
  have "the_min \<le> (0::'a)" by (fact the_min_min)
  hence "rep_nat (the_min::'a) \<le> rep_nat (0::'a)" by (simp only: ord_iff)
  also have "... = 0" by simp
  finally have "rep_nat (the_min::'a) = 0" by simp
  thus ?thesis by (simp only: rep_zero_iff)
qed

instantiation nat :: nat
begin

definition rep_nat_nat :: "nat \<Rightarrow> nat" where rep_nat_nat_def [code_unfold]: "rep_nat_nat = (\<lambda>x. x)"
definition abs_nat_nat :: "nat \<Rightarrow> nat" where abs_nat_nat_def [code_unfold]: "abs_nat_nat = (\<lambda>x. x)"

instance by (standard, simp_all add: rep_nat_nat_def abs_nat_nat_def)

end

instantiation natural :: nat
begin

definition rep_nat_natural :: "natural \<Rightarrow> nat"
  where rep_nat_natural_def [code_unfold]: "rep_nat_natural = nat_of_natural"
definition abs_nat_natural :: "nat \<Rightarrow> natural"
  where abs_nat_natural_def [code_unfold]: "abs_nat_natural = natural_of_nat"

instance by (standard, simp_all add: rep_nat_natural_def abs_nat_natural_def, metis minus_natural.rep_eq nat_of_natural_of_nat of_nat_of_natural)

end

subsection \<open>Term Orders\<close>

subsubsection \<open>Type Classes\<close>

class nat_pp_compare = linorder + zero + plus +
  fixes rep_nat_pp :: "'a \<Rightarrow> (nat, nat) pp"
    and abs_nat_pp :: "(nat, nat) pp \<Rightarrow> 'a"
    and lex_comp' :: "'a comparator"
    and deg' :: "'a \<Rightarrow> nat"
  assumes rep_nat_pp_inverse [simp]: "abs_nat_pp (rep_nat_pp x) = x"
    and abs_nat_pp_inverse [simp]: "rep_nat_pp (abs_nat_pp t) = t"
    and lex_comp': "lex_comp' x y = comp_of_ord lex_pp (rep_nat_pp x) (rep_nat_pp y)"
    and deg': "deg' x = deg_pp (rep_nat_pp x)"
    and le_pp: "rep_nat_pp x \<le> rep_nat_pp y \<Longrightarrow> x \<le> y"
    and zero_pp: "rep_nat_pp 0 = 0"
    and plus_pp: "rep_nat_pp (x + y) = rep_nat_pp x + rep_nat_pp y"
begin

lemma less_pp:
  assumes "rep_nat_pp x < rep_nat_pp y"
  shows "x < y"
proof -
  from assms have 1: "rep_nat_pp x \<le> rep_nat_pp y" and 2: "rep_nat_pp x \<noteq> rep_nat_pp y" by simp_all
  from 1 have "x \<le> y" by (rule le_pp)
  moreover from 2 have "x \<noteq> y" by auto
  ultimately show ?thesis by simp
qed

lemma rep_nat_pp_inj:
  assumes "rep_nat_pp x = rep_nat_pp y"
  shows "x = y"
proof -
  have "abs_nat_pp (rep_nat_pp x) = abs_nat_pp (rep_nat_pp y)" by (simp only: assms)
  thus ?thesis by simp
qed

lemma lex_comp'_EqD:
  assumes "lex_comp' x y = Eq"
  shows "x = y"
proof (rule rep_nat_pp_inj)
  from assms show "rep_nat_pp x = rep_nat_pp y" by (simp add: lex_comp' comp_of_ord_def split: if_split_asm)
qed

lemma lex_comp'_valE:
  assumes "lex_comp' s t \<noteq> Eq"
  obtains x where "x \<in> keys_pp (rep_nat_pp s) \<union> keys_pp (rep_nat_pp t)"
    and "comparator_of (lookup_pp (rep_nat_pp s) x) (lookup_pp (rep_nat_pp t) x) = lex_comp' s t"
    and "\<And>y. y < x \<Longrightarrow> lookup_pp (rep_nat_pp s) y = lookup_pp (rep_nat_pp t) y"
proof (cases "lex_comp' s t")
  case Eq
  with assms show ?thesis ..
next
  case Lt
  hence "rep_nat_pp s \<noteq> rep_nat_pp t" and "lex_pp (rep_nat_pp s) (rep_nat_pp t)"
    by (auto simp: lex_comp' comp_of_ord_def split: if_split_asm)
  hence "\<exists>x. lookup_pp (rep_nat_pp s) x < lookup_pp (rep_nat_pp t) x \<and>
             (\<forall>y<x. lookup_pp (rep_nat_pp s) y = lookup_pp (rep_nat_pp t) y)"
    by (simp add: lex_pp_alt)
  then obtain x where 1: "lookup_pp (rep_nat_pp s) x < lookup_pp (rep_nat_pp t) x"
    and 2: "\<And>y. y < x \<Longrightarrow> lookup_pp (rep_nat_pp s) y = lookup_pp (rep_nat_pp t) y" by blast
  show ?thesis
  proof
    show "x \<in> keys_pp (rep_nat_pp s) \<union> keys_pp (rep_nat_pp t)"
    proof (rule ccontr)
      assume "x \<notin> keys_pp (rep_nat_pp s) \<union> keys_pp (rep_nat_pp t)"
      with 1 show False by (simp add: keys_pp_iff)
    qed
  next
    show "comparator_of (lookup_pp (rep_nat_pp s) x) (lookup_pp (rep_nat_pp t) x) = lex_comp' s t"
      by (simp add: linorder_class.comparator_of_def 1 Lt)
  qed (fact 2)
next
  case Gt
  hence "\<not> lex_pp (rep_nat_pp s) (rep_nat_pp t)"
    by (auto simp: lex_comp' comp_of_ord_def split: if_split_asm)
  hence "lex_pp (rep_nat_pp t) (rep_nat_pp s)" by (rule lex_pp_lin')
  moreover have "rep_nat_pp t \<noteq> rep_nat_pp s"
  proof
    assume "rep_nat_pp t = rep_nat_pp s"
    moreover from this have "lex_pp (rep_nat_pp s) (rep_nat_pp t)" by (simp add: lex_pp_refl)
    ultimately have "lex_comp' s t = Eq" by (simp add: lex_comp' comp_of_ord_def)
    with Gt show False by simp
  qed
  ultimately have "\<exists>x. lookup_pp (rep_nat_pp t) x < lookup_pp (rep_nat_pp s) x \<and>
                    (\<forall>y<x. lookup_pp (rep_nat_pp t) y = lookup_pp (rep_nat_pp s) y)"
    by (simp add: lex_pp_alt)
  then obtain x where 1: "lookup_pp (rep_nat_pp t) x < lookup_pp (rep_nat_pp s) x"
    and 2: "\<And>y. y < x \<Longrightarrow> lookup_pp (rep_nat_pp t) y = lookup_pp (rep_nat_pp s) y" by blast
  show ?thesis
  proof
    show "x \<in> keys_pp (rep_nat_pp s) \<union> keys_pp (rep_nat_pp t)"
    proof (rule ccontr)
      assume "x \<notin> keys_pp (rep_nat_pp s) \<union> keys_pp (rep_nat_pp t)"
      with 1 show False by (simp add: keys_pp_iff)
    qed
  next
    from 1 have "\<not> lookup_pp (rep_nat_pp s) x < lookup_pp (rep_nat_pp t) x"
      and "lookup_pp (rep_nat_pp s) x \<noteq> lookup_pp (rep_nat_pp t) x" by simp_all
    thus "comparator_of (lookup_pp (rep_nat_pp s) x) (lookup_pp (rep_nat_pp t) x) = lex_comp' s t"
      by (simp add: linorder_class.comparator_of_def Gt)
  qed (simp add: 2)
qed

end

class nat_term_compare = linorder + nat_term +
  fixes is_scalar :: "'a itself \<Rightarrow> bool"
    and lex_comp :: "'a comparator"
    and deg_comp :: "'a comparator \<Rightarrow> 'a comparator"
    and pot_comp :: "'a comparator \<Rightarrow> 'a comparator"
  assumes zero_component: "\<exists>x. snd (rep_nat_term x) = 0"
    and is_scalar: "is_scalar = (\<lambda>_. \<forall>x. snd (rep_nat_term x) = 0)"
    and lex_comp: "lex_comp = lex_comp_aux" \<comment>\<open>For being able to implement \<open>lex_comp\<close> efficiently.\<close>
    and deg_comp: "deg_comp cmp = (\<lambda>x y. case comparator_of (deg_pp (fst (rep_nat_term x))) (deg_pp (fst (rep_nat_term y))) of Eq \<Rightarrow> cmp x y | val \<Rightarrow> val)"
    and pot_comp: "pot_comp cmp = (\<lambda>x y. case comparator_of (snd (rep_nat_term x)) (snd (rep_nat_term y)) of Eq \<Rightarrow> cmp x y | val \<Rightarrow> val)"
    and le_term: "rep_nat_term x \<le> rep_nat_term y \<Longrightarrow> x \<le> y"
begin

text \<open>There is no need to add something like \<open>top_comp\<close> for TOP orders to class @{class nat_term_compare},
  because by default all comparators should @{emph \<open>first\<close>} compare power-products and @{emph \<open>then\<close>} positions.
  \<open>lex_comp\<close> obviously does.\<close>

lemma less_term:
  assumes "rep_nat_term x < rep_nat_term y"
  shows "x < y"
proof -
  from assms have 1: "rep_nat_term x \<le> rep_nat_term y" and 2: "rep_nat_term x \<noteq> rep_nat_term y" by simp_all
  from 1 have "x \<le> y" by (rule le_term)
  moreover from 2 have "x \<noteq> y" by auto
  ultimately show ?thesis by simp
qed

lemma lex_comp_alt: "lex_comp = (comparator_of::'a comparator)"
proof -
  from lex_pp_antisym have as: "antisymp lex_pp" by (rule antisympI)
  interpret lex: comparator "comp_of_ord (lex_pp::(nat, nat) pp \<Rightarrow> _)"
    unfolding comp_of_ord_eq_comp_of_ords[OF as]
    by (rule comp_of_ords, unfold_locales,
        auto simp: lex_pp_refl intro: lex_pp_trans lex_pp_lin' elim!: lex_pp_antisym)

  have 1: "x = y" if "fst (rep_nat_term x) = fst (rep_nat_term y)"
                  and "snd (rep_nat_term x) = snd (rep_nat_term y)" for x y
    by (rule rep_nat_term_inj, rule prod_eqI, fact+)
  have 2: "x < y" if "fst (rep_nat_term x) = fst (rep_nat_term y)"
                  and "snd (rep_nat_term x) < snd (rep_nat_term y)" for x y
    by (rule less_term, simp add: less_prod_def that)
  have 3: False if "fst (rep_nat_term x) = fst (rep_nat_term y)"
                and "\<not> snd (rep_nat_term x) < snd (rep_nat_term y)" and "x < y" for x y
  proof -
    from that(2) have a: "snd (rep_nat_term y) \<le> snd (rep_nat_term x)" by simp
    have "y \<le> x" by (rule le_term, simp add: less_eq_prod_def that(1) a)
    also have "... < y" by fact
    finally show False ..
  qed
  have 4: "x < y" if "fst (rep_nat_term x) \<noteq> fst (rep_nat_term y)"
                  and "lex_pp (fst (rep_nat_term x)) (fst (rep_nat_term y))" for x y
  proof -
    from that(2) have "fst (rep_nat_term x) \<le> fst (rep_nat_term y)" by (simp only: less_eq_pp_def)
    with that(1) have "fst (rep_nat_term x) < fst (rep_nat_term y)" by simp
    hence "rep_nat_term x < rep_nat_term y" by (simp add: less_prod_def)
    thus ?thesis by (rule less_term)
  qed
  have 5: False if "fst (rep_nat_term x) \<noteq> fst (rep_nat_term y)"
                and "\<not> lex_pp (fst (rep_nat_term x)) (fst (rep_nat_term y))" and "x < y" for x y
  proof -
    from that(2) have a: "lex_pp (fst (rep_nat_term y)) (fst (rep_nat_term x))" by (rule lex_pp_lin')
    with that(1)[symmetric] have "y < x" by (rule 4)
    also have "... < y" by fact
    finally show False ..
  qed

  show ?thesis
    by (intro ext, simp add: lex_comp lex_comp_aux_def comparator_of_def linorder_class.comparator_of_def lex.eq split: order.splits,
        auto simp: lex_pp_refl comp_of_ord_def elim: 1 2 3 4 5)
qed

lemma full_component_zeroE: obtains x where "rep_nat_term x = (t, 0)"
proof -
  from zero_component obtain x' where "snd (rep_nat_term x') = 0" ..
  then obtain x where "rep_nat_term x = (t, 0)" by (rule full_componentE)
  thus ?thesis ..
qed

end

(* For some reason, the following lemmas cannot be stated in context "nat_term_compare". *)

lemma comparator_lex_comp: "comparator lex_comp"
  unfolding lex_comp by (fact comparator_lex_comp_aux)

lemma nat_term_comp_lex_comp: "nat_term_comp lex_comp"
  unfolding lex_comp by (fact nat_term_comp_lex_comp_aux)

lemma comparator_deg_comp:
  assumes "comparator cmp"
  shows "comparator (deg_comp cmp)"
  unfolding deg_comp using comparator_of assms by (rule comparator_lexicographic)

lemma comparator_pot_comp:
  assumes "comparator cmp"
  shows "comparator (pot_comp cmp)"
  unfolding pot_comp using comparator_of assms by (rule comparator_lexicographic)

lemma deg_comp_zero_min:
  assumes "comparator cmp" and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "fst (rep_nat_term u) = 0"
  shows "deg_comp cmp u v \<noteq> Gt"
proof (simp add: deg_comp assms(3) comparator_of_def split: order.split, intro impI)
  assume "fst (rep_nat_term v) = 0"
  with assms(3) have "fst (rep_nat_term u) = fst (rep_nat_term v)" by simp
  hence "rep_nat_term u = rep_nat_term v" using assms(2) by (rule prod_eqI)
  hence "u = v" by (rule rep_nat_term_inj)
  from assms(1) interpret c: comparator cmp .
  show "cmp u v \<noteq> Gt" by (simp add: \<open>u = v\<close>)
qed

lemma deg_comp_pos:
  assumes "cmp u v = Lt" and "fst (rep_nat_term u) = fst (rep_nat_term v)"
  shows "deg_comp cmp u v = Lt"
  by (simp add: deg_comp assms split: order.split)

lemma deg_comp_monotone:
  assumes "cmp u v = Lt \<Longrightarrow> cmp (splus t u) (splus t v) = Lt" and "deg_comp cmp u v = Lt"
  shows "deg_comp cmp (splus t u) (splus t v) = Lt"
  using assms(2) by (auto simp: deg_comp splus_term pprod.splus_def comparator_of_def deg_pp_plus
                          split: order.splits if_splits intro: assms(1))

lemma pot_comp_zero_min:
  assumes "cmp u v \<noteq> Gt" and "snd (rep_nat_term u) = snd (rep_nat_term v)"
  shows "pot_comp cmp u v \<noteq> Gt"
  by (simp add: pot_comp comparator_of_def assms split: order.split)

lemma pot_comp_pos:
  assumes "snd (rep_nat_term u) < snd (rep_nat_term v)"
  shows "pot_comp cmp u v = Lt"
  by (simp add: pot_comp comparator_of_def assms split: order.split)

lemma pot_comp_monotone:
  assumes "cmp u v = Lt \<Longrightarrow> cmp (splus t u) (splus t v) = Lt" and "pot_comp cmp u v = Lt"
  shows "pot_comp cmp (splus t u) (splus t v) = Lt"
  using assms(2) by (auto simp: pot_comp splus_term pprod.splus_def comparator_of_def deg_pp_plus
                          split: order.splits if_splits intro: assms(1))

lemma deg_comp_cong:
  assumes "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v)) \<Longrightarrow> to1 u v = to2 u v"
  shows "deg_comp to1 u v = deg_comp to2 u v"
  using assms by (simp add: deg_comp comparator_of_def split: order.split)

lemma pot_comp_cong:
  assumes "snd (rep_nat_term u) = snd (rep_nat_term v) \<Longrightarrow> to1 u v = to2 u v"
  shows "pot_comp to1 u v = pot_comp to2 u v"
  using assms by (simp add: pot_comp comparator_of_def split: order.split)

instantiation pp :: (nat, nat) nat_pp_compare
begin

definition rep_nat_pp_pp :: "('a, 'b) pp \<Rightarrow> (nat, nat) pp"
  where rep_nat_pp_pp_def [code del]: "rep_nat_pp_pp x = pp_of_fun (\<lambda>n::nat. rep_nat (lookup_pp x (abs_nat n)))"

definition abs_nat_pp_pp :: "(nat, nat) pp \<Rightarrow> ('a, 'b) pp"
  where abs_nat_pp_pp_def [code del]: "abs_nat_pp_pp t = pp_of_fun (\<lambda>n::'a. abs_nat (lookup_pp t (rep_nat n)))"

definition lex_comp'_pp :: "('a, 'b) pp comparator"
  where lex_comp'_pp_def [code del]: "lex_comp'_pp = comp_of_ord lex_pp"

definition deg'_pp :: "('a, 'b) pp \<Rightarrow> nat"
  where "deg'_pp x = rep_nat (deg_pp x)"

lemma lookup_rep_nat_pp_pp:
  "lookup_pp (rep_nat_pp t) = (\<lambda>n::nat. rep_nat (lookup_pp t (abs_nat n)))"
  unfolding rep_nat_pp_pp_def
proof (rule lookup_pp_of_fun)
  have "{n. lookup_pp t (abs_nat n) \<noteq> 0} \<subseteq> rep_nat ` {x. lookup_pp t x \<noteq> 0}"
  proof
    fix n
    have "n = rep_nat (abs_nat n)" by (simp only: nat_class.abs_inverse)
    assume "n \<in> {n. lookup_pp t (abs_nat n) \<noteq> 0}"
    hence "abs_nat n \<in> {x. lookup_pp t x \<noteq> 0}" by simp
    with \<open>n = rep_nat (abs_nat n)\<close> show "n \<in> rep_nat ` {x. lookup_pp t x \<noteq> 0}" ..
  qed
  also have "finite ..." by (rule finite_imageI, transfer, simp)
  also (finite_subset) have "{n. lookup_pp t (abs_nat n) \<noteq> 0} = {n. rep_nat (lookup_pp t (abs_nat n)) \<noteq> 0}"
    by (metis rep_inj rep_zero)
  finally show "finite {x. rep_nat (lookup_pp t (abs_nat x)) \<noteq> 0}" .
qed

lemma lookup_abs_nat_pp_pp:
  "lookup_pp (abs_nat_pp t) = (\<lambda>n::'a. abs_nat (lookup_pp t (rep_nat n)))"
  unfolding abs_nat_pp_pp_def
proof (rule lookup_pp_of_fun)
  have "{n::'a. lookup_pp t (rep_nat n) \<noteq> 0} \<subseteq> abs_nat ` {x. lookup_pp t x \<noteq> 0}"
  proof
    fix n :: 'a
    have "n = abs_nat (rep_nat n)" by (simp only: nat_class.rep_inverse)
    assume "n \<in> {n. lookup_pp t (rep_nat n) \<noteq> 0}"
    hence "rep_nat n \<in> {x. lookup_pp t x \<noteq> 0}" by simp
    with \<open>n = abs_nat (rep_nat n)\<close> show "n \<in> abs_nat ` {x. lookup_pp t x \<noteq> 0}" ..
  qed
  also have "finite ..." by (rule finite_imageI, transfer, simp)
  also (finite_subset) have "{n::'a. lookup_pp t (rep_nat n) \<noteq> 0} = {n. abs_nat (lookup_pp t (rep_nat n)) \<noteq> 0}"
    by (metis abs_inverse abs_zero)
  finally show "finite {n::'a. abs_nat (lookup_pp t (rep_nat n)) \<noteq> 0}" .
qed

lemma keys_rep_nat_pp_pp: "keys_pp (rep_nat_pp t) = rep_nat ` keys_pp t"
  by (rule set_eqI,
      simp add: keys_pp_iff lookup_rep_nat_pp_pp image_iff Bex_def ex_iff_abs[where 'a='a] rep_zero_iff del: neq0_conv)

lemma rep_nat_pp_pp_inverse: "abs_nat_pp (rep_nat_pp x) = x" for x::"('a, 'b) pp"
  by (rule pp_eqI, simp add: lookup_abs_nat_pp_pp lookup_rep_nat_pp_pp)

lemma abs_nat_pp_pp_inverse: "rep_nat_pp ((abs_nat_pp t)::('a, 'b) pp) = t"
  by (rule pp_eqI, simp add: lookup_abs_nat_pp_pp lookup_rep_nat_pp_pp)

corollary rep_nat_pp_pp_inj:
  fixes x y :: "('a, 'b) pp"
  assumes "rep_nat_pp x = rep_nat_pp y"
  shows "x = y"
  by (metis (no_types) rep_nat_pp_pp_inverse assms)

corollary rep_nat_pp_pp_eq_iff: "(rep_nat_pp x = rep_nat_pp y) \<longleftrightarrow> (x = y)" for x y :: "('a, 'b) pp"
  by (auto elim: rep_nat_pp_pp_inj)

lemma lex_rep_nat_pp: "lex_pp (rep_nat_pp x) (rep_nat_pp y) \<longleftrightarrow> lex_pp x y"
  by (simp add: lex_pp_alt rep_nat_pp_pp_eq_iff lookup_rep_nat_pp_pp rep_eq_iff
      ord_iff[symmetric] ex_iff_abs[where 'a='a] all_iff_abs')

corollary lex_comp'_pp: "lex_comp' x y = comp_of_ord lex_pp (rep_nat_pp x) (rep_nat_pp y)" for x y :: "('a, 'b) pp"
  by (simp add: lex_comp'_pp_def comp_of_ord_def rep_nat_pp_pp_eq_iff lex_rep_nat_pp)

corollary le_pp_pp: "rep_nat_pp x \<le> rep_nat_pp y \<Longrightarrow> x \<le> y" for x y :: "('a, 'b) pp"
  by (simp only: less_eq_pp_def lex_rep_nat_pp)

lemma deg_rep_nat_pp: "deg_pp (rep_nat_pp t) = rep_nat (deg_pp t)" for t :: "('a, 'b) pp"
proof -
  have "keys_pp (rep_nat_pp t) = rep_nat ` keys_pp t"
    by (rule set_eqI, simp add: keys_pp_iff image_iff lookup_rep_nat_pp_pp Bex_def ex_iff_abs[where 'a='a] rep_zero_iff del: neq0_conv)
  hence "deg_pp (rep_nat_pp t) = sum (lookup_pp (rep_nat_pp t)) (rep_nat ` keys_pp t)"
    by (simp add: deg_pp_alt)
  also have "... = sum (lookup_pp (rep_nat_pp t) \<circ> rep_nat) (keys_pp t)"
    by (rule sum.reindex, rule inj_onI, elim rep_inj)
  also have "... = sum (rep_nat \<circ> (lookup_pp t)) (keys_pp t)"
    by (simp add: lookup_rep_nat_pp_pp)
  also have "... = rep_nat (deg_pp t)" by (simp only: deg_pp_alt sum_rep)
  finally show ?thesis .
qed

corollary deg'_pp: "deg' t = deg_pp (rep_nat_pp t)" for t :: "('a, 'b) pp"
  by (simp add: deg'_pp_def deg_rep_nat_pp)

lemma zero_pp_pp: "rep_nat_pp (0::('a, 'b) pp) = 0"
  by (rule pp_eqI, simp add: lookup_rep_nat_pp_pp)

lemma plus_pp_pp: "rep_nat_pp (x + y) = rep_nat_pp x + rep_nat_pp y"
  for x y :: "('a, 'b) pp"
  by (rule pp_eqI, simp add: lookup_rep_nat_pp_pp lookup_plus_pp rep_plus)

instance
  apply intro_classes
  subgoal by (fact rep_nat_pp_pp_inverse)
  subgoal by (fact abs_nat_pp_pp_inverse)
  subgoal by (fact lex_comp'_pp)
  subgoal by (fact deg'_pp)
  subgoal by (rule le_pp_pp)
  subgoal by (fact zero_pp_pp)
  subgoal by (fact plus_pp_pp)
  done

end

instantiation pp :: (nat, nat) nat_term
begin

definition rep_nat_term_pp :: "('a, 'b) pp \<Rightarrow> (nat, nat) pp \<times> nat"
  where rep_nat_term_pp_def [code del]: "rep_nat_term_pp t = (rep_nat_pp t, 0)"

definition splus_pp :: "('a, 'b) pp \<Rightarrow> ('a, 'b) pp \<Rightarrow> ('a, 'b) pp"
  where splus_pp_def [code del]: "splus_pp = (+)"

instance proof
  fix x y :: "('a, 'b) pp"
  assume "rep_nat_term x = rep_nat_term y"
  hence "rep_nat_pp x = rep_nat_pp y" by (simp add: rep_nat_term_pp_def)
  thus "x = y" by (rule rep_nat_pp_pp_inj)
next
  fix x::"('a, 'b) pp" and i t
  assume "snd (rep_nat_term x) = i"
  hence "i = 0" by (simp add: rep_nat_term_pp_def)
  show "\<exists>y::('a, 'b) pp. rep_nat_term y = (t, i)" unfolding \<open>i = 0\<close>
  proof
    show "rep_nat_term ((abs_nat_pp t)::('a, 'b) pp) = (t, 0)" by (simp add: rep_nat_term_pp_def)
  qed
next
  fix x y :: "('a, 'b) pp"
  show "rep_nat_term (splus x y) = pprod.splus (fst (rep_nat_term x)) (rep_nat_term y)"
    by (simp add: splus_pp_def rep_nat_term_pp_def pprod.splus_def plus_pp_pp)
qed

end

instantiation pp :: (nat, nat) nat_term_compare
begin

definition is_scalar_pp :: "('a, 'b) pp itself \<Rightarrow> bool"
  where is_scalar_pp_def [code_unfold]: "is_scalar_pp = (\<lambda>_. True)"

definition lex_comp_pp :: "('a, 'b) pp comparator"
  where lex_comp_pp_def [code_unfold]: "lex_comp_pp = lex_comp'"

definition deg_comp_pp :: "('a, 'b) pp comparator \<Rightarrow> ('a, 'b) pp comparator"
  where deg_comp_pp_def: "deg_comp_pp cmp = (\<lambda>x y. case comparator_of (deg_pp x) (deg_pp y) of Eq \<Rightarrow> cmp x y | val \<Rightarrow> val)"

definition pot_comp_pp :: "('a, 'b) pp comparator \<Rightarrow> ('a, 'b) pp comparator"
  where pot_comp_pp_def [code_unfold]: "pot_comp_pp = (\<lambda>cmp. cmp)"

instance proof
  show "\<exists>x::('a, 'b) pp. snd (rep_nat_term x) = 0"
  proof
    show "snd (rep_nat_term (0::('a, 'b) pp)) = 0" by (simp add: rep_nat_term_pp_def)
  qed
next
  show "is_scalar = (\<lambda>_::('a, 'b) pp itself. \<forall>x::('a, 'b) pp. snd (rep_nat_term x) = 0)"
    by (simp add: is_scalar_pp_def rep_nat_term_pp_def)
next
  show "lex_comp = (lex_comp_aux::('a, 'b) pp comparator)"
    by (auto simp: lex_comp_pp_def lex_comp_aux_def rep_nat_term_pp_def lex_comp'_pp split: order.split intro!: ext)
next
  fix cmp :: "('a, 'b) pp comparator"
  show "deg_comp cmp =
         (\<lambda>x y. case comparator_of (deg_pp (fst (rep_nat_term x))) (deg_pp (fst (rep_nat_term y))) of Eq \<Rightarrow> cmp x y
                      | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
    by (simp add: rep_nat_term_pp_def deg_comp_pp_def deg_rep_nat_pp comparator_of_rep)
next
  fix cmp :: "('a, 'b) pp comparator"
  show "pot_comp cmp =
         (\<lambda>x y. case comparator_of (snd (rep_nat_term x)) (snd (rep_nat_term y)) of Eq \<Rightarrow> cmp x y | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
    by (simp add: rep_nat_term_pp_def pot_comp_pp_def)
next
  fix x y :: "('a, 'b) pp"
  assume "rep_nat_term x \<le> rep_nat_term y"
  hence "rep_nat_pp x \<le> rep_nat_pp y" by (auto simp: rep_nat_term_pp_def)
  thus "x \<le> y" by (rule le_pp_pp)
qed

end

instance pp :: (nat, nat) nat_pp_term
proof
  show "rep_nat_term (0::('a, 'b) pp) = (0, 0)"
    by (simp add: rep_nat_term_pp_def) (metis deg_pp_eq_0_iff deg_rep_nat_pp rep_zero)
next
  show "splus = ((+)::('a, 'b) pp \<Rightarrow> _)" by (simp add: splus_pp_def)
qed

instantiation prod :: ("{nat_pp_compare, comm_powerprod}", nat) nat_term
begin

definition rep_nat_term_prod :: "('a \<times> 'b) \<Rightarrow> ((nat, nat) pp \<times> nat)"
  where rep_nat_term_prod_def [code del]: "rep_nat_term_prod u = (rep_nat_pp (fst u), rep_nat (snd u))"

definition splus_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> ('a \<times> 'b)"
  where splus_prod_def [code del]: "splus_prod t u = pprod.splus (fst t) u"

instance proof
  fix x y :: "'a \<times> 'b"
  assume "rep_nat_term x = rep_nat_term y"
  hence 1: "rep_nat_pp (fst x) = rep_nat_pp (fst y)" and 2: "rep_nat (snd x) = rep_nat (snd y)"
    by (simp_all add: rep_nat_term_prod_def)
  from 1 have "fst x = fst y" by (rule rep_nat_pp_inj)
  moreover from 2 have "snd x = snd y" by (rule rep_inj)
  ultimately show "x = y" by (rule prod_eqI)
next
  fix i t
  show "\<exists>y::'a \<times> 'b. rep_nat_term y = (t, i)"
  proof
    show "rep_nat_term (abs_nat_pp t, abs_nat i) = (t, i)" by (simp add: rep_nat_term_prod_def)
  qed
next
  fix x y :: "'a \<times> 'b"
  show "rep_nat_term (splus x y) = pprod.splus (fst (rep_nat_term x)) (rep_nat_term y)"
    by (simp add: splus_prod_def rep_nat_term_prod_def pprod.splus_def plus_pp)
qed

end

instantiation prod :: ("{nat_pp_compare, comm_powerprod}", nat) nat_term_compare
begin

definition is_scalar_prod :: "('a \<times> 'b) itself \<Rightarrow> bool"
  where is_scalar_prod_def [code_unfold]: "is_scalar_prod = (\<lambda>_. False)"

definition lex_comp_prod :: "('a \<times> 'b) comparator"
  where "lex_comp_prod = (\<lambda>u v. case lex_comp' (fst u) (fst v) of Eq \<Rightarrow> comparator_of (snd u) (snd v) | val \<Rightarrow> val)"

definition deg_comp_prod :: "('a \<times> 'b) comparator \<Rightarrow> ('a \<times> 'b) comparator"
  where deg_comp_prod_def: "deg_comp_prod cmp = (\<lambda>x y. case comparator_of (deg' (fst x)) (deg' (fst y)) of Eq \<Rightarrow> cmp x y | val \<Rightarrow> val)"

definition pot_comp_prod :: "('a \<times> 'b) comparator \<Rightarrow> ('a \<times> 'b) comparator"
  where "pot_comp_prod cmp = (\<lambda>u v. case comparator_of (snd u) (snd v) of Eq \<Rightarrow> cmp u v | val \<Rightarrow> val)"

instance proof
  show "\<exists>x::'a \<times> 'b. snd (rep_nat_term x) = 0"
  proof
    show "snd (rep_nat_term (abs_nat_pp 0, 0)) = 0" by (simp add: rep_nat_term_prod_def)
  qed
next
  have "\<not> (\<forall>a. rep_nat (a::'b) = 0)"
  proof
    assume "\<forall>a. rep_nat (a::'b) = 0"
    hence "rep_nat ((abs_nat 1)::'b) = 0" by blast
    hence "((abs_nat 1)::'b) = 0" by (simp only: rep_zero_iff)
    hence "(1::nat) = 0" by (metis abs_inj abs_zero)
    thus False by simp
  qed
  thus "is_scalar = (\<lambda>_::('a \<times> 'b) itself. \<forall>x. snd (rep_nat_term (x::'a \<times> 'b)) = 0)"
    by (auto simp add: is_scalar_prod_def rep_nat_term_prod_def intro!: ext)
next
  show "lex_comp = (lex_comp_aux::('a \<times> 'b) comparator)"
    by (auto simp: lex_comp_prod_def lex_comp_aux_def rep_nat_term_prod_def lex_comp' comparator_of_rep split: order.split intro!: ext)
next
  fix cmp :: "('a \<times> 'b) comparator"
  show "deg_comp cmp =
         (\<lambda>x y. case comparator_of (deg_pp (fst (rep_nat_term x))) (deg_pp (fst (rep_nat_term y))) of Eq \<Rightarrow> cmp x y
                   | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
    by (simp add: rep_nat_term_prod_def deg_comp_prod_def deg')
next
  fix cmp :: "('a \<times> 'b) comparator"
  show "pot_comp cmp =
         (\<lambda>x y. case comparator_of (snd (rep_nat_term x)) (snd (rep_nat_term y)) of Eq \<Rightarrow> cmp x y | Lt \<Rightarrow> Lt | Gt \<Rightarrow> Gt)"
    by (simp add: rep_nat_term_prod_def pot_comp_prod_def comparator_of_rep)
next
  fix x y :: "'a \<times> 'b"
  assume "rep_nat_term x \<le> rep_nat_term y"
  hence "rep_nat_pp (fst x) < rep_nat_pp (fst y) \<or> (rep_nat_pp (fst x) \<le> rep_nat_pp (fst y) \<and> rep_nat (snd x) \<le> rep_nat (snd y))"
    by (simp add: rep_nat_term_prod_def)
  thus "x \<le> y" by (auto simp: less_eq_prod_def ord_iff[symmetric] intro: le_pp less_pp)
qed

end

lemmas [code del] = deg_pp.rep_eq plus_pp.abs_eq minus_pp.abs_eq

lemma rep_nat_pp_nat [code_unfold]: "(rep_nat_pp::(nat, nat) pp \<Rightarrow> (nat, nat) pp) = (\<lambda>x. x)"
  by (intro ext pp_eqI, simp add: lookup_rep_nat_pp_pp abs_nat_nat_def rep_nat_nat_def)

subsubsection \<open>\<open>LEX\<close>, \<open>DRLEX\<close>, \<open>DEG\<close> and \<open>POT\<close>\<close>

definition LEX :: "'a::nat_term_compare nat_term_order" where "LEX = Abs_nat_term_order lex_comp"

definition DRLEX :: "'a::nat_term_compare nat_term_order"
  where "DRLEX = Abs_nat_term_order (deg_comp (pot_comp (\<lambda>x y. lex_comp y x)))"

definition DEG :: "'a::nat_term_compare nat_term_order \<Rightarrow> 'a nat_term_order"
  where "DEG to = Abs_nat_term_order (deg_comp (nat_term_compare to))"

definition POT :: "'a::nat_term_compare nat_term_order \<Rightarrow> 'a nat_term_order"
  where "POT to = Abs_nat_term_order (pot_comp (nat_term_compare to))"

text \<open>@{const DRLEX} must apply @{const pot_comp}, for otherwise it does not satisfy
  the second condition of @{const nat_term_comp}.\<close>

text \<open>Instead of @{const DRLEX} one could also introduce another unary constructor \<open>DEGREV\<close>, analogous
  to @{const DEG} and @{const POT}. Then, however, proving (in)equalities of the term orders gets
  really messy (think of @{prop "DEG (POT to) = DEGREV (DEGREV to)"}, for instance).
  So, we restrict the formalization to @{const DRLEX} only.\<close>

abbreviation "DLEX \<equiv> DEG LEX"

code_datatype LEX DRLEX DEG POT

lemma nat_term_compare_LEX [code]: "nat_term_compare LEX = lex_comp"
  unfolding LEX_def using comparator_lex_comp nat_term_comp_lex_comp
  by (rule nat_term_compare_Abs_nat_term_order_id)

lemma nat_term_compare_DRLEX [code]: "nat_term_compare DRLEX = deg_comp (pot_comp (\<lambda>x y. lex_comp y x))"
proof -
  have cmp: "comparator (pot_comp (\<lambda>x y. lex_comp y x))"
    by (rule comparator_pot_comp, rule comparator_converse, fact comparator_lex_comp)
  show ?thesis unfolding DRLEX_def
  proof (rule nat_term_compare_Abs_nat_term_order_id)
    from cmp show "comparator (deg_comp (pot_comp (\<lambda>x y::'a. lex_comp y x)))"
      by (rule comparator_deg_comp)
  next
    show "nat_term_comp (deg_comp (pot_comp (\<lambda>x y::'a. lex_comp y x)))"
    proof (rule nat_term_compI)
      fix u v :: 'a
      assume "snd (rep_nat_term u) = snd (rep_nat_term v)" and "fst (rep_nat_term u) = 0"
      with cmp show "deg_comp (pot_comp (\<lambda>x y::'a. lex_comp y x)) u v \<noteq> Gt"
        by (rule deg_comp_zero_min)
    next
      fix u v :: 'a
      assume "snd (rep_nat_term u) < snd (rep_nat_term v)"
      hence "pot_comp (\<lambda>x y. lex_comp y x) u v = Lt" by (rule pot_comp_pos)
      moreover assume "fst (rep_nat_term u) = fst (rep_nat_term v)"
      ultimately show "deg_comp (pot_comp (\<lambda>x y. lex_comp y x)) u v = Lt" by (rule deg_comp_pos)
    next
      fix t u v :: 'a
      have "pot_comp (\<lambda>x y. lex_comp y x) (splus t u) (splus t v) = Lt"
        if "pot_comp (\<lambda>x y. lex_comp y x) u v = Lt" using _ that
      proof (rule pot_comp_monotone)
        assume "lex_comp v u = Lt"
        with nat_term_comp_lex_comp show "lex_comp (splus t v) (splus t u) = Lt"
          by (rule nat_term_compD3)
      qed
      moreover assume "deg_comp (pot_comp (\<lambda>x y. lex_comp y x)) u v = Lt"
      ultimately show "deg_comp (pot_comp (\<lambda>x y. lex_comp y x)) (splus t u) (splus t v) = Lt"
        by (rule deg_comp_monotone)
    next
      fix u v a b :: 'a
      assume "fst (rep_nat_term v) = fst (rep_nat_term b)" and "fst (rep_nat_term u) = fst (rep_nat_term a)"
        and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "snd (rep_nat_term a) = snd (rep_nat_term b)"
      moreover from comparator_lex_comp nat_term_comp_lex_comp this(1, 2) this(3, 4)[symmetric]
      have "lex_comp v u = lex_comp b a" by (rule nat_term_compD4')
      moreover assume "deg_comp (pot_comp (\<lambda>x y. lex_comp y x)) a b = Lt"
      ultimately show "deg_comp (pot_comp (\<lambda>x y. lex_comp y x)) u v = Lt"
        by (simp add: deg_comp pot_comp split: order.splits)
    qed
  qed
qed

lemma nat_term_compare_DEG [code]: "nat_term_compare (DEG to) = deg_comp (nat_term_compare to)"
  unfolding DEG_def
proof (rule nat_term_compare_Abs_nat_term_order_id)
  from comparator_nat_term_compare show "comparator (deg_comp (nat_term_compare to))"
    by (rule comparator_deg_comp)
next
  show "nat_term_comp (deg_comp (nat_term_compare to))"
  proof (rule nat_term_compI)
    fix u v :: 'a
    assume "snd (rep_nat_term u) = snd (rep_nat_term v)" and "fst (rep_nat_term u) = 0"
    with comparator_nat_term_compare show "deg_comp (nat_term_compare to) u v \<noteq> Gt"
      by (rule deg_comp_zero_min)
  next
    fix u v :: 'a
    assume a: "fst (rep_nat_term u) = fst (rep_nat_term v)" and "snd (rep_nat_term u) < snd (rep_nat_term v)"
    with nat_term_comp_nat_term_compare have "nat_term_compare to u v = Lt" by (rule nat_term_compD2)
    thus "deg_comp (nat_term_compare to) u v = Lt" using a by (rule deg_comp_pos)
  next
    fix t u v :: 'a
    from nat_term_comp_nat_term_compare
    have "nat_term_compare to u v = Lt \<Longrightarrow> nat_term_compare to (splus t u) (splus t v) = Lt"
      by (rule nat_term_compD3)
    moreover assume "deg_comp (nat_term_compare to) u v = Lt"
    ultimately show "deg_comp (nat_term_compare to) (splus t u) (splus t v) = Lt" by (rule deg_comp_monotone)
  next
    fix u v a b :: 'a
    assume "fst (rep_nat_term u) = fst (rep_nat_term a)" and "fst (rep_nat_term v) = fst (rep_nat_term b)"
      and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "snd (rep_nat_term a) = snd (rep_nat_term b)"
    moreover from comparator_nat_term_compare nat_term_comp_nat_term_compare this
    have "nat_term_compare to u v = nat_term_compare to a b"
      by (rule nat_term_compD4')
    moreover assume "deg_comp (nat_term_compare to) a b = Lt"
    ultimately show "deg_comp (nat_term_compare to) u v = Lt"
      by (simp add: deg_comp split: order.splits)
  qed
qed

lemma nat_term_compare_POT [code]: "nat_term_compare (POT to) = pot_comp (nat_term_compare to)"
  unfolding POT_def
proof (rule nat_term_compare_Abs_nat_term_order_id)
  from comparator_nat_term_compare show "comparator (pot_comp (nat_term_compare to))"
    by (rule comparator_pot_comp)
next
  show "nat_term_comp (pot_comp (nat_term_compare to))"
  proof (rule nat_term_compI)
    fix u v :: 'a
    assume a: "snd (rep_nat_term u) = snd (rep_nat_term v)" and "fst (rep_nat_term u) = 0"
    with nat_term_comp_nat_term_compare have "nat_term_compare to u v \<noteq> Gt" by (rule nat_term_compD1)
    thus "pot_comp (nat_term_compare to) u v \<noteq> Gt" using a by (rule pot_comp_zero_min)
  next
    fix u v :: 'a
    assume "snd (rep_nat_term u) < snd (rep_nat_term v)"
    thus "pot_comp (nat_term_compare to) u v = Lt" by (rule pot_comp_pos)
  next
    fix t u v :: 'a
    from nat_term_comp_nat_term_compare
    have "nat_term_compare to u v = Lt \<Longrightarrow> nat_term_compare to (splus t u) (splus t v) = Lt"
      by (rule nat_term_compD3)
    moreover assume "pot_comp (nat_term_compare to) u v = Lt"
    ultimately show "pot_comp (nat_term_compare to) (splus t u) (splus t v) = Lt" by (rule pot_comp_monotone)
  next
    fix u v a b :: 'a
    assume "fst (rep_nat_term u) = fst (rep_nat_term a)" and "fst (rep_nat_term v) = fst (rep_nat_term b)"
      and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "snd (rep_nat_term a) = snd (rep_nat_term b)"
    moreover from comparator_nat_term_compare nat_term_comp_nat_term_compare this
    have "nat_term_compare to u v = nat_term_compare to a b"
      by (rule nat_term_compD4')
    moreover assume "pot_comp (nat_term_compare to) a b = Lt"
    ultimately show "pot_comp (nat_term_compare to) u v = Lt"
      by (simp add: pot_comp split: order.splits)
  qed
qed

lemma nat_term_compare_POT_DRLEX [code]:
  "nat_term_compare (POT DRLEX) = pot_comp (deg_comp (\<lambda>x y. lex_comp y x))"
  unfolding nat_term_compare_POT nat_term_compare_DRLEX
  by (intro ext pot_comp_cong deg_comp_cong, simp add: pot_comp)

lemma compute_lex_pp [code]: "lex_pp p q = (lex_comp' p q \<noteq> Gt)"
  by (simp add: lex_comp'_pp_def comp_of_ord_def)

lemma compute_dlex_pp [code]: "dlex_pp p q = (deg_comp lex_comp' p q \<noteq> Gt)"
  by (simp add: deg_comp_pp_def dlex_pp_alt compute_lex_pp comparator_of_def)

lemma compute_drlex_pp [code]: "drlex_pp p q = (deg_comp (\<lambda>x y. lex_comp' y x) p q \<noteq> Gt)"
  by (simp add: deg_comp_pp_def drlex_pp_alt compute_lex_pp comparator_of_def)

lemma nat_pp_order_of_le_nat_pp [code]: "nat_term_order_of_le = LEX"
  by (simp add: nat_term_order_of_le_def LEX_def lex_comp_alt)

subsubsection \<open>Equality of Term Orders\<close>

definition nat_term_order_eq :: "'a nat_term_order \<Rightarrow> 'a::nat_term_compare nat_term_order \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where nat_term_order_eq_def [code del]:
      "nat_term_order_eq to1 to2 dg ps =
                (\<forall>u v. (dg \<longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))) \<longrightarrow>
                       (ps \<longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)) \<longrightarrow>
                       nat_term_compare to1 u v = nat_term_compare to2 u v)"

lemma nat_term_order_eqI:
  assumes "\<And>u v. (dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))) \<Longrightarrow>
                  (ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)) \<Longrightarrow>
                  nat_term_compare to1 u v = nat_term_compare to2 u v"
  shows "nat_term_order_eq to1 to2 dg ps"
  unfolding nat_term_order_eq_def using assms by blast

lemma nat_term_order_eqD:
  assumes "nat_term_order_eq to1 to2 dg ps"
    and "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
    and "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
  shows "nat_term_compare to1 u v = nat_term_compare to2 u v"
  using assms unfolding nat_term_order_eq_def by blast

lemma nat_term_order_eq_sym: "nat_term_order_eq to1 to2 dg ps \<longleftrightarrow> nat_term_order_eq to2 to1 dg ps"
  by (auto simp: nat_term_order_eq_def)

lemma nat_term_order_eq_DEG_dg:
  "nat_term_order_eq (DEG to1) to2 True ps \<longleftrightarrow> nat_term_order_eq to1 to2 True ps"
  by (auto simp: nat_term_order_eq_def nat_term_compare_DEG deg_comp)

lemma nat_term_order_eq_DEG_dg':
  "nat_term_order_eq to1 (DEG to2) True ps \<longleftrightarrow> nat_term_order_eq to1 to2 True ps"
  by (simp add: nat_term_order_eq_sym[of to1] nat_term_order_eq_DEG_dg)

lemma nat_term_order_eq_POT_ps:
  assumes "ps \<or> is_scalar TYPE('a::nat_term_compare)"
  shows "nat_term_order_eq (POT (to1::'a nat_term_order)) to2 dg ps \<longleftrightarrow> nat_term_order_eq to1 to2 dg ps"
  using assms
proof
  assume "ps"
  thus ?thesis by (auto simp: nat_term_order_eq_def nat_term_compare_POT pot_comp)
next
  assume "is_scalar TYPE('a)"
  hence "snd (rep_nat_term x) = 0" for x::'a by (simp add: is_scalar)
  thus ?thesis by (auto simp: nat_term_order_eq_def nat_term_compare_POT pot_comp)
qed

lemma nat_term_order_eq_POT_ps':
  assumes "ps \<or> is_scalar TYPE('a::nat_term_compare)"
  shows "nat_term_order_eq to1 (POT (to2::'a nat_term_order)) dg ps \<longleftrightarrow> nat_term_order_eq to1 to2 dg ps"
  using assms by (simp add: nat_term_order_eq_sym[of to1] nat_term_order_eq_POT_ps)

lemma snd_rep_nat_term_eqI:
  assumes "ps \<or> is_scalar TYPE('a::nat_term_compare)" and "ps \<Longrightarrow> snd (rep_nat_term (u::'a)) = snd (rep_nat_term (v::'a))"
  shows "snd (rep_nat_term u) = snd (rep_nat_term v)"
  using assms(1)
proof
  assume "is_scalar TYPE('a)"
  thus ?thesis by (simp add: is_scalar)
qed (fact assms(2))

definition of_exps :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::nat_term_compare"
  where "of_exps a b i =
        (THE u. rep_nat_term u = (pp_of_fun (\<lambda>x. if x = 0 then a else if x = 1 then b else 0),
                                  if (\<exists>v::'a. snd (rep_nat_term v) = i) then i else 0))"

text \<open>@{const of_exps} is an auxiliary function needed for proving the equalities of the various
  term orders.\<close>

lemma rep_nat_term_of_exps:
  "rep_nat_term ((of_exps a b i)::'a::nat_term_compare) =
    (pp_of_fun (\<lambda>x::nat. if x = 0 then a else if x = 1 then b else 0), if (\<exists>y::'a. snd (rep_nat_term y) = i) then i else 0)"
proof (cases "\<exists>y::'a. snd (rep_nat_term y) = i")
  case True
  then obtain y::'a where "snd (rep_nat_term y) = i" ..
  then obtain u::'a where u: "rep_nat_term u = (pp_of_fun (\<lambda>x::nat. if x = 0 then a else if x = 1 then b else 0), i)"
    by (rule full_componentE)
  from True have eq: "(if \<exists>y::'a. snd (rep_nat_term y) = i then i else 0) = i" by simp
  show ?thesis unfolding of_exps_def eq
  proof (rule theI)
    fix v :: 'a
    assume "rep_nat_term v = (pp_of_fun (\<lambda>x::nat. if x = 0 then a else if x = 1 then b else 0), i)"
    thus "v = u" unfolding u[symmetric] by (rule rep_nat_term_inj)
  qed (fact u)
next
  case False
  hence eq: "(if \<exists>y::'a. snd (rep_nat_term y) = i then i else 0) = 0" by simp
  obtain u::'a where u: "rep_nat_term u = (pp_of_fun (\<lambda>x::nat. if x = 0 then a else if x = 1 then b else 0), 0)"
    by (rule full_component_zeroE)
  show ?thesis unfolding of_exps_def eq
  proof (rule theI)
    fix v :: 'a
    assume "rep_nat_term v = (pp_of_fun (\<lambda>x::nat. if x = 0 then a else if x = 1 then b else 0), 0)"
    thus "v = u" unfolding u[symmetric] by (rule rep_nat_term_inj)
  qed (fact u)
qed

lemma lookup_pp_of_exps:
  "lookup_pp (fst (rep_nat_term (of_exps a b i))) = (\<lambda>x. if x = 0 then a else if x = 1 then b else 0)"
  unfolding rep_nat_term_of_exps fst_conv
proof (rule lookup_pp_of_fun)
  have "{x. (if x = 0 then a else if x = 1 then b else 0) \<noteq> 0} \<subseteq> {0, 1}"
    by (rule, simp split: if_split_asm)
  also have "finite ..." by simp
  finally(finite_subset) show "finite {x. (if x = 0 then a else if x = 1 then b else 0) \<noteq> 0}" .
qed

lemma keys_pp_of_exps: "keys_pp (fst (rep_nat_term (of_exps a b i))) \<subseteq> {0, 1}"
  by (rule, simp add: keys_pp_iff lookup_pp_of_exps split: if_split_asm)

lemma deg_pp_of_exps [simp]: "deg_pp (fst (rep_nat_term ((of_exps a b i)::'a::nat_term_compare))) = a + b"
proof -
  let ?u = "(of_exps a b i)::'a"
  have "sum (lookup_pp (fst (rep_nat_term ?u))) (keys_pp (fst (rep_nat_term ?u))) =
        sum (lookup_pp (fst (rep_nat_term ?u))) {0, 1}"
  proof (rule sum.mono_neutral_left, simp, fact keys_pp_of_exps, intro ballI)
    fix x
    assume "x \<in> {0, 1} - keys_pp (fst (rep_nat_term ?u))"
    thus "lookup_pp (fst (rep_nat_term ?u)) x = 0" by (simp add: keys_pp_iff)
  qed
  also have "... = a + b" by (simp add: lookup_pp_of_exps)
  finally show ?thesis by (simp only: deg_pp_alt)
qed

lemma snd_of_exps:
  assumes "snd (rep_nat_term (x::'a)) = i"
  shows "snd (rep_nat_term ((of_exps a b i)::'a::nat_term_compare)) = i"
proof -
  from assms have "\<exists>x::'a. snd (rep_nat_term (x::'a)) = i" ..
  thus ?thesis by (simp add: rep_nat_term_of_exps)
qed

lemma snd_of_exps_zero [simp]: "snd (rep_nat_term ((of_exps a b 0)::'a::nat_term_compare)) = 0"
proof -
  from zero_component obtain x::'a where "snd (rep_nat_term (x::'a)) = 0" ..
  thus ?thesis by (rule snd_of_exps)
qed

lemma eq_of_exps:
  "(fst (rep_nat_term (of_exps a1 b1 i)) = fst (rep_nat_term (of_exps a2 b2 j))) \<longleftrightarrow> (a1 = a2 \<and> b1 = b2)"
proof -
  have "a1 = a2 \<and> b1 = b2"
    if "(\<lambda>x::nat. if x = 0 then a1 else if x = 1 then b1 else 0) = (\<lambda>x. if x = 0 then a2 else if x = 1 then b2 else 0)"
  proof
    from fun_cong[OF that, of 0] show "a1 = a2" by simp
  next
    from fun_cong[OF that, of 1] show "b1 = b2" by simp
  qed
  thus ?thesis by (auto simp: pp_eq_iff lookup_pp_of_exps)
qed

lemma lex_pp_of_exps:
  "lex_pp (fst (rep_nat_term ((of_exps a1 b1 i)::'a))) (fst (rep_nat_term ((of_exps a2 b2 j)::'a::nat_term_compare))) \<longleftrightarrow>
    (a1 < a2 \<or> (a1 = a2 \<and> b1 \<le> b2))" (is "?L \<longleftrightarrow> ?R")
proof -
  let ?u = "fst (rep_nat_term ((of_exps a1 b1 i)::'a))"
  let ?v = "fst (rep_nat_term ((of_exps a2 b2 j)::'a))"
  show ?thesis
  proof
    assume ?L
    hence "?u = ?v \<or> (\<exists>x. lookup_pp ?u x < lookup_pp ?v x \<and> (\<forall>y<x. lookup_pp ?u y = lookup_pp ?v y))"
      by (simp only: lex_pp_alt)
    thus ?R
    proof
      assume "?u = ?v"
      thus ?thesis by (simp add: eq_of_exps)
    next
      assume "\<exists>x. lookup_pp ?u x < lookup_pp ?v x \<and> (\<forall>y<x. lookup_pp ?u y = lookup_pp ?v y)"
      then obtain x where 1: "lookup_pp ?u x < lookup_pp ?v x" and 2: "\<And>y. y < x \<Longrightarrow> lookup_pp ?u y = lookup_pp ?v y"
        by auto
      from 1 have "lookup_pp ?v x \<noteq> 0" by simp
      hence "x \<in> keys_pp ?v" by (simp add: keys_pp_iff)
      also have "... \<subseteq> {0, 1}" by (fact keys_pp_of_exps)
      finally have "x = 0 \<or> x = 1" by simp
      thus ?thesis
      proof
        assume "x = 0"
        from 1 show ?thesis by (simp add: lookup_pp_of_exps \<open>x = 0\<close>)
      next
        assume "x = 1"
        hence "0 < x" by simp
        hence "lookup_pp ?u 0 = lookup_pp ?v 0" by (rule 2)
        hence "a1 = a2" by (simp add: lookup_pp_of_exps)
        from 1 show ?thesis by (simp add: lookup_pp_of_exps \<open>x = 1\<close> \<open>a1 = a2\<close>)
      qed
    qed
  next
    assume ?R
    thus ?L
    proof
      assume "a1 < a2"
      show ?thesis unfolding lex_pp_alt
      proof (intro disjI2 exI conjI allI impI)
        from \<open>a1 < a2\<close> show "lookup_pp ?u 0 < lookup_pp ?v 0" by (simp add: lookup_pp_of_exps)
      next
        fix y::nat
        assume "y < 0"
        thus "lookup_pp ?u y = lookup_pp ?v y" by simp
      qed
    next
      assume "a1 = a2 \<and> b1 \<le> b2"
      hence "a1 = a2" and "b1 \<le> b2" by simp_all
      from this(2) have "b1 < b2 \<or> b1 = b2" by auto
      thus ?thesis
      proof
        assume "b1 < b2"
        show ?thesis unfolding lex_pp_alt
        proof (intro disjI2 exI conjI allI impI)
          from \<open>b1 < b2\<close> show "lookup_pp ?u 1 < lookup_pp ?v 1" by (simp add: lookup_pp_of_exps)
        next
          fix y::nat
          assume "y < 1"
          hence "y = 0" by simp
          show "lookup_pp ?u y = lookup_pp ?v y" by (simp add: lookup_pp_of_exps \<open>y = 0\<close> \<open>a1 = a2\<close>)
        qed
      next
        assume "b1 = b2"
        show ?thesis by (simp add: lex_pp_alt eq_of_exps \<open>a1 = a2\<close> \<open>b1 = b2\<close>)
      qed
    qed
  qed
qed

lemma LEX_eq [code]:
  "nat_term_order_eq LEX (LEX::'a nat_term_order) dg ps = True" (is ?thesis1)
  "nat_term_order_eq LEX (DRLEX::'a nat_term_order) dg ps = False" (is ?thesis2)
  "nat_term_order_eq LEX (DEG (to::'a nat_term_order)) dg ps =
    (dg \<and> nat_term_order_eq LEX to dg ps)" (is ?thesis3)
  "nat_term_order_eq LEX (POT (to::'a nat_term_order)) dg ps =
    ((ps \<or> is_scalar TYPE('a::nat_term_compare)) \<and> nat_term_order_eq LEX to dg ps)" (is ?thesis4)
proof -
  show ?thesis1 by (simp add: nat_term_order_eq_def)
next
  show ?thesis2
  proof (intro iffI)
    assume a: "nat_term_order_eq LEX (DRLEX::'a nat_term_order) dg ps"
    let ?u = "(of_exps 0 1 0)::'a"
    let ?v = "(of_exps 1 0 0)::'a"
    have "nat_term_compare LEX ?u ?v = nat_term_compare DRLEX ?u ?v"
      by (rule nat_term_order_eqD, fact a, simp_all)
    thus False
      by (simp add: nat_term_compare_LEX lex_comp lex_comp_aux_def nat_term_compare_DRLEX deg_comp
          pot_comp comparator_of_def comp_of_ord_def lex_pp_of_exps eq_of_exps)
  qed (rule FalseE)
next
  show ?thesis3
  proof (intro iffI)
    assume a: "nat_term_order_eq LEX (DEG to) dg ps"
    have dg
    proof (rule ccontr)
      assume "\<not> dg"
      let ?u = "(of_exps 0 2 0)::'a"
      let ?v = "(of_exps 1 0 0)::'a"
      have "nat_term_compare LEX ?u ?v = nat_term_compare (DEG to) ?u ?v"
        by (rule nat_term_order_eqD, fact a, simp_all add: \<open>\<not> dg\<close>)
      thus False
        by (simp add: nat_term_compare_LEX lex_comp lex_comp_aux_def nat_term_compare_DEG deg_comp
            comparator_of_def comp_of_ord_def lex_pp_of_exps eq_of_exps)
    qed
    show "dg \<and> nat_term_order_eq LEX to dg ps"
    proof (intro conjI \<open>dg\<close> nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      from \<open>dg\<close> have eq: "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))" by (rule 1)
      assume "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with a 1 have "nat_term_compare LEX u v = nat_term_compare (DEG to) u v"
        by (rule nat_term_order_eqD)
      also have "... = nat_term_compare to u v" by (simp add: nat_term_compare_DEG deg_comp eq)
      finally show "nat_term_compare LEX u v = nat_term_compare to u v" .
    qed
  next
    assume "dg \<and> nat_term_order_eq LEX to dg ps"
    hence dg and a: "nat_term_order_eq LEX to dg ps" by auto
    show "nat_term_order_eq LEX (DEG to) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      from \<open>dg\<close> have eq: "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))" by (rule 1)
      assume "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with a 1 have "nat_term_compare LEX u v = nat_term_compare to u v" by (rule nat_term_order_eqD)
      also have "... = nat_term_compare (DEG to) u v" by (simp add: nat_term_compare_DEG deg_comp eq)
      finally show "nat_term_compare LEX u v = nat_term_compare (DEG to) u v" .
    qed
  qed
next
  show ?thesis4
  proof (intro iffI)
    assume a: "nat_term_order_eq LEX (POT to) dg ps"
    have *: "ps \<or> is_scalar TYPE('a)"
    proof (rule ccontr)
      assume "\<not> (ps \<or> is_scalar TYPE('a))"
      hence "\<not> ps" and "\<not> is_scalar TYPE('a)" by simp_all
      from this(2) obtain x::'a where "snd (rep_nat_term x) \<noteq> 0" unfolding is_scalar by auto
      moreover define i::nat where "i = snd (rep_nat_term x)"
      ultimately have "i \<noteq> 0" by simp
      let ?u = "(of_exps 0 1 i)::'a"
      let ?v = "(of_exps 1 0 0)::'a"
      from i_def[symmetric] have eq: "snd (rep_nat_term ?u) = i" by (rule snd_of_exps)
      have "nat_term_compare LEX ?u ?v = nat_term_compare (POT to) ?u ?v"
        by (rule nat_term_order_eqD, fact a, simp_all add: \<open>\<not> ps\<close>)
      thus False
        by (simp add: nat_term_compare_LEX lex_comp lex_comp_aux_def pot_comp nat_term_compare_POT
            comparator_of_def comp_of_ord_def lex_pp_of_exps eq_of_exps eq \<open>i \<noteq> 0\<close> del: One_nat_def)
    qed
    show "(ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq LEX to dg ps"
    proof (intro conjI * nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      assume 2: "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with * have eq: "snd (rep_nat_term u) = snd (rep_nat_term v)" by (rule snd_rep_nat_term_eqI)
      from a 1 2 have "nat_term_compare LEX u v = nat_term_compare (POT to) u v"
        by (rule nat_term_order_eqD)
      also have "... = nat_term_compare to u v" by (simp add: nat_term_compare_POT eq pot_comp)
      finally show "nat_term_compare LEX u v = nat_term_compare to u v" .
    qed
  next
    assume "(ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq LEX to dg ps"
    hence *: "ps \<or> is_scalar TYPE('a)" and a: "nat_term_order_eq LEX to dg ps" by auto
    show "nat_term_order_eq LEX (POT to) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      assume 2: "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with * have eq: "snd (rep_nat_term u) = snd (rep_nat_term v)" by (rule snd_rep_nat_term_eqI)
      from a 1 2 have "nat_term_compare LEX u v = nat_term_compare to u v" by (rule nat_term_order_eqD)
      also have "... = nat_term_compare (POT to) u v" by (simp add: nat_term_compare_POT eq pot_comp)
      finally show "nat_term_compare LEX u v = nat_term_compare (POT to) u v" .
    qed
  qed
qed

lemma DRLEX_eq [code]:
  "nat_term_order_eq DRLEX (LEX::'a nat_term_order) dg ps = False" (is ?thesis1)
  "nat_term_order_eq DRLEX DRLEX dg ps = True" (is ?thesis2)
  "nat_term_order_eq DRLEX (DEG (to::'a nat_term_order)) dg ps =
    nat_term_order_eq DRLEX to True ps" (is ?thesis3)
  "nat_term_order_eq DRLEX (POT (to::'a nat_term_order)) dg ps =
    ((dg \<or> ps \<or> is_scalar TYPE('a::nat_term_compare)) \<and> nat_term_order_eq DRLEX to dg True)" (is ?thesis4)
proof -
  from nat_term_order_eq_sym[of "DRLEX::'a nat_term_order"] show ?thesis1 by (simp only: LEX_eq)
next
  show ?thesis2 by (simp add: nat_term_order_eq_def)
next
  show ?thesis3
  proof (intro iffI)
    assume a: "nat_term_order_eq DRLEX (DEG to) dg ps"
    show "nat_term_order_eq DRLEX to True ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "True \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
        and "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with a have "nat_term_compare DRLEX u v = nat_term_compare (DEG to) u v"
        by (rule nat_term_order_eqD, blast+)
      also have "... = nat_term_compare to u v" by (simp add: nat_term_compare_DEG deg_comp 1)
      finally show "nat_term_compare DRLEX u v = nat_term_compare to u v" .
    qed
  next
    assume a: "nat_term_order_eq DRLEX to True ps"
    show "nat_term_order_eq DRLEX (DEG to) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      show "nat_term_compare DRLEX u v = nat_term_compare (DEG to) u v"
      proof (simp add: nat_term_compare_DRLEX nat_term_compare_DEG deg_comp comparator_of_def split: order.split, rule)
        assume 2: "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
        with a have "nat_term_compare DRLEX u v = nat_term_compare to u v"
          using 1 by (rule nat_term_order_eqD)
        thus "pot_comp (\<lambda>x y. lex_comp y x) u v = nat_term_compare to u v"
          by (simp add: nat_term_compare_DRLEX deg_comp 2)
      qed
    qed
  qed
next
  show ?thesis4
  proof (intro iffI)
    assume a: "nat_term_order_eq DRLEX (POT to) dg ps"
    have *: "dg \<or> ps \<or> is_scalar TYPE('a)"
    proof (rule ccontr)
      assume "\<not> (dg \<or> ps \<or> is_scalar TYPE('a))"
      hence "\<not> dg" and "\<not> ps" and "\<not> is_scalar TYPE('a)" by simp_all
      from this(3) obtain x::'a where "snd (rep_nat_term x) \<noteq> 0" unfolding is_scalar by auto
      moreover define i::nat where "i = snd (rep_nat_term x)"
      ultimately have "i \<noteq> 0" by simp
      let ?u = "(of_exps 1 0 i)::'a"
      let ?v = "(of_exps 2 0 0)::'a"
      from i_def[symmetric] have eq: "snd (rep_nat_term ?u) = i" by (rule snd_of_exps)
      have "nat_term_compare DRLEX ?u ?v = nat_term_compare (POT to) ?u ?v"
        by (rule nat_term_order_eqD, fact a, simp_all add: \<open>\<not> ps\<close> \<open>\<not> dg\<close>)
      thus False
        by (simp add: nat_term_compare_DRLEX deg_comp pot_comp nat_term_compare_POT
            comparator_of_def eq \<open>i \<noteq> 0\<close> del: One_nat_def)
    qed
    show "(dg \<or> ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq DRLEX to dg True"
    proof (intro conjI * nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      assume 2: "True \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      from a 1 2 have "nat_term_compare DRLEX u v = nat_term_compare (POT to) u v"
        by (rule nat_term_order_eqD, blast+)
      also have "... = nat_term_compare to u v" by (simp add: nat_term_compare_POT 2 pot_comp)
      finally show "nat_term_compare DRLEX u v = nat_term_compare to u v" .
    qed
  next
    assume "(dg \<or> ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq DRLEX to dg True"
    hence disj: "dg \<or> ps \<or> is_scalar TYPE('a)" and a: "nat_term_order_eq DRLEX to dg True" by auto
    show "nat_term_order_eq DRLEX (POT to) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume 1: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      assume 2: "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      from disj show "nat_term_compare DRLEX u v = nat_term_compare (POT to) u v"
      proof
        assume dg
        hence eq1: "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))" by (rule 1)
        show ?thesis
        proof (simp add: nat_term_compare_DRLEX deg_comp eq1 nat_term_compare_POT pot_comp comparator_of_def split: order.split, rule)
          assume eq2: "snd (rep_nat_term u) = snd (rep_nat_term v)"
          with a 1 have "nat_term_compare DRLEX u v = nat_term_compare to u v" by (rule nat_term_order_eqD)
          thus "lex_comp v u = nat_term_compare to u v"
            by (simp add: nat_term_compare_DRLEX deg_comp eq1 pot_comp eq2)
        qed
      next
        assume "ps \<or> is_scalar TYPE('a)"
        hence eq: "snd (rep_nat_term u) = snd (rep_nat_term v)" using 2 by (rule snd_rep_nat_term_eqI)
        with a 1 have "nat_term_compare DRLEX u v = nat_term_compare to u v" by (rule nat_term_order_eqD)
        also have "... = nat_term_compare (POT to) u v" by (simp add: nat_term_compare_POT pot_comp eq)
        finally show ?thesis .
      qed
    qed
  qed
qed

lemma DEG_eq [code]:
  "nat_term_order_eq (DEG to) (LEX::'a nat_term_order) dg ps = nat_term_order_eq LEX (DEG to) dg ps"
  "nat_term_order_eq (DEG to) (DRLEX::'a nat_term_order) dg ps = nat_term_order_eq DRLEX (DEG to) dg ps"
  "nat_term_order_eq (DEG to1) (DEG (to2::'a nat_term_order)) dg ps =
    nat_term_order_eq to1 to2 True ps" (is ?thesis3)
  "nat_term_order_eq (DEG to1) (POT (to2::'a nat_term_order)) dg ps =
    (if dg then nat_term_order_eq to1 (POT to2) dg ps
    else ((ps \<or> is_scalar TYPE('a::nat_term_compare)) \<and> nat_term_order_eq (DEG to1) to2 dg ps))" (is ?thesis4)
proof -
  show ?thesis3
  proof (rule iffI)
    assume a: "nat_term_order_eq (DEG to1) (DEG to2) dg ps"
    show "nat_term_order_eq to1 to2 True ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume b: "True \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
        and "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with a have "nat_term_compare (DEG to1) u v = nat_term_compare (DEG to2) u v"
        by (rule nat_term_order_eqD, blast+)
      thus "nat_term_compare to1 u v = nat_term_compare to2 u v"
        by (simp add: nat_term_compare_DEG deg_comp comparator_of_def b)
    qed
  next
    assume a: "nat_term_order_eq to1 to2 True ps"
    show "nat_term_order_eq (DEG to1) (DEG to2) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume b: "ps \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      show "nat_term_compare (DEG to1) u v = nat_term_compare (DEG to2) u v"
      proof (simp add: nat_term_compare_DEG deg_comp comparator_of_def split: order.split, rule impI)
        assume "deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
        with a show "nat_term_compare to1 u v = nat_term_compare to2 u v" using b by (rule nat_term_order_eqD)
      qed
    qed
  qed
next
  show ?thesis4
  proof (simp add: nat_term_order_eq_DEG_dg split: if_split, intro impI)
    show "nat_term_order_eq (DEG to1) (POT to2) False ps =
            ((ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq (DEG to1) to2 False ps)"
    proof (intro iffI)
      assume a: "nat_term_order_eq (DEG to1) (POT to2) False ps"
      have *: "ps \<or> is_scalar TYPE('a)"
      proof (rule ccontr)
        assume "\<not> (ps \<or> is_scalar TYPE('a))"
        hence "\<not> ps" and "\<not> is_scalar TYPE('a)" by simp_all
        from this(2) obtain x::'a where "snd (rep_nat_term x) \<noteq> 0" unfolding is_scalar by auto
        moreover define i::nat where "i = snd (rep_nat_term x)"
        ultimately have "i \<noteq> 0" by simp
        let ?u = "(of_exps 1 0 i)::'a"
        let ?v = "(of_exps 2 0 0)::'a"
        from i_def[symmetric] have eq: "snd (rep_nat_term ?u) = i" by (rule snd_of_exps)
        have "nat_term_compare (DEG to1) ?u ?v = nat_term_compare (POT to2) ?u ?v"
          by (rule nat_term_order_eqD, fact a, simp_all add: \<open>\<not> ps\<close>)
        thus False
          by (simp add: nat_term_compare_DEG deg_comp pot_comp nat_term_compare_POT
              comparator_of_def comp_of_ord_def lex_pp_of_exps eq_of_exps eq \<open>i \<noteq> 0\<close> del: One_nat_def)
      qed
      moreover from this a have "nat_term_order_eq (DEG to1) to2 False ps" by (simp add: nat_term_order_eq_POT_ps')
      ultimately show "(ps \<or> is_scalar TYPE('a)) \<and> nat_term_order_eq (DEG to1) to2 False ps" ..
    qed (simp add: nat_term_order_eq_POT_ps')
  qed
qed (fact nat_term_order_eq_sym)+

lemma POT_eq [code]:
  "nat_term_order_eq (POT to) LEX dg ps = nat_term_order_eq LEX (POT to) dg ps"
  "nat_term_order_eq (POT to1) (DEG to2) dg ps = nat_term_order_eq (DEG to2) (POT to1) dg ps"
  "nat_term_order_eq (POT to1) DRLEX dg ps = nat_term_order_eq DRLEX (POT to1) dg ps"
  "nat_term_order_eq (POT to1) (POT (to2::'a::nat_term_compare nat_term_order)) dg ps =
    nat_term_order_eq to1 to2 dg True" (is ?thesis4)
proof -
  show ?thesis4
  proof (rule iffI)
    assume a: "nat_term_order_eq (POT to1) (POT to2) dg ps"
    show "nat_term_order_eq to1 to2 dg True"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
        and b: "True \<Longrightarrow> snd (rep_nat_term u) = snd (rep_nat_term v)"
      with a have "nat_term_compare (POT to1) u v = nat_term_compare (POT to2) u v"
        by (rule nat_term_order_eqD, blast+)
      thus "nat_term_compare to1 u v = nat_term_compare to2 u v"
        by (simp add: nat_term_compare_POT pot_comp comparator_of_def b)
    qed
  next
    assume a: "nat_term_order_eq to1 to2 dg True"
    show "nat_term_order_eq (POT to1) (POT to2) dg ps"
    proof (rule nat_term_order_eqI)
      fix u v :: 'a
      assume b: "dg \<Longrightarrow> deg_pp (fst (rep_nat_term u)) = deg_pp (fst (rep_nat_term v))"
      show "nat_term_compare (POT to1) u v = nat_term_compare (POT to2) u v"
      proof (simp add: nat_term_compare_POT pot_comp comparator_of_def split: order.split, rule impI)
        assume "snd (rep_nat_term u) = snd (rep_nat_term v)"
        with a b show "nat_term_compare to1 u v = nat_term_compare to2 u v" by (rule nat_term_order_eqD)
      qed
    qed
  qed
qed (fact nat_term_order_eq_sym)+

lemma nat_term_order_equal [code]: "HOL.equal to1 to2 = nat_term_order_eq to1 to2 False False"
  by (auto simp: nat_term_order_eq_def equal_eq nat_term_compare_inject[symmetric])

hide_const (open) of_exps

value [code] "DEG (POT DRLEX) = (DRLEX::((nat, nat) pp \<times> nat) nat_term_order)"

value [code] "POT LEX = (LEX::((nat, nat) pp \<times> nat) nat_term_order)"

value [code] "POT LEX = (LEX::(nat, nat) pp nat_term_order)"

end (*theory*)
