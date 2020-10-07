(* Author: Alexander Maletzky *)

section \<open>Ordered Associative Lists for Polynomials\<close>

theory OAlist_Poly_Mapping
  imports PP_Type MPoly_Type_Class_Ordered OAlist
begin

text \<open>We introduce a dedicated type for ordered associative lists (oalists) representing polynomials.
  To that end, we require the order relation the oalists are sorted wrt. to be admissible term orders,
  and furthermore sort the lists @{emph \<open>descending\<close>} rather than @{emph \<open>ascending\<close>}, because this
  allows to implement various operations more efficiently.
  For technical reasons, we must restrict the type of terms to types embeddable into
  @{typ "(nat, nat) pp \<times> nat"}, though. All types we are interested in meet this requirement.\<close>

lemma comparator_lexicographic:
  fixes f::"'a \<Rightarrow> 'b" and g::"'a \<Rightarrow> 'c"
  assumes "comparator c1" and "comparator c2" and "\<And>x y. f x = f y \<Longrightarrow> g x = g y \<Longrightarrow> x = y"
  shows "comparator (\<lambda>x y. case c1 (f x) (f y) of Eq \<Rightarrow> c2 (g x) (g y) | val \<Rightarrow> val)"
          (is "comparator ?c3")
proof -
  from assms(1) interpret c1: comparator c1 .
  from assms(2) interpret c2: comparator c2 .
  show ?thesis
  proof
    fix x y :: 'a
    show "invert_order (?c3 x y) = ?c3 y x"
      by (simp add: c1.eq c2.eq split: order.split,
          metis invert_order.simps(1) invert_order.simps(2) c1.sym c2.sym order.distinct(5))
  next
    fix x y :: 'a
    assume "?c3 x y = Eq"
    hence "f x = f y" and "g x = g y" by (simp_all add: c1.eq c2.eq split: order.splits if_split_asm)
    thus "x = y" by (rule assms(3))
  next
    fix x y z :: 'a
    assume "?c3 x y = Lt"
    hence d1: "c1 (f x) (f y) = Lt \<or> (c1 (f x) (f y) = Eq \<and> c2 (g x) (g y) = Lt)"
      by (simp split: order.splits)
    assume "?c3 y z = Lt"
    hence d2: "c1 (f y) (f z) = Lt \<or> (c1 (f y) (f z) = Eq \<and> c2 (g y) (g z) = Lt)"
      by (simp split: order.splits)
    from d1 show "?c3 x z = Lt"
    proof
      assume 1: "c1 (f x) (f y) = Lt"
      from d2 show ?thesis
      proof
        assume "c1 (f y) (f z) = Lt"
        with 1 have "c1 (f x) (f z) = Lt" by (rule c1.trans)
        thus ?thesis by simp
      next
        assume "c1 (f y) (f z) = Eq \<and> c2 (g y) (g z) = Lt"
        hence "f z = f y" and "c2 (g y) (g z) = Lt" by (simp_all add: c1.eq)
        with 1 show ?thesis by simp
      qed
    next
      assume "c1 (f x) (f y) = Eq \<and> c2 (g x) (g y) = Lt"
      hence 1: "f x = f y" and 2: "c2 (g x) (g y) = Lt" by (simp_all add: c1.eq)
      from d2 show ?thesis
      proof
        assume "c1 (f y) (f z) = Lt"
        thus ?thesis by (simp add: 1)
      next
        assume "c1 (f y) (f z) = Eq \<and> c2 (g y) (g z) = Lt"
        hence 3: "f y = f z" and "c2 (g y) (g z) = Lt" by (simp_all add: c1.eq)
        from 2 this(2) have "c2 (g x) (g z) = Lt" by (rule c2.trans)
        thus ?thesis by (simp add: 1 3)
      qed
    qed
  qed
qed

class nat_term =
  fixes rep_nat_term :: "'a \<Rightarrow> ((nat, nat) pp \<times> nat)"
    and splus :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes rep_nat_term_inj: "rep_nat_term x = rep_nat_term y \<Longrightarrow> x = y"
    and full_component: "snd (rep_nat_term x) = i \<Longrightarrow> (\<exists>y. rep_nat_term y = (t, i))"
    and splus_term: "rep_nat_term (splus x y) = pprod.splus (fst (rep_nat_term x)) (rep_nat_term y)"
begin

definition "lex_comp_aux = (\<lambda>x y. case comp_of_ord lex_pp (fst (rep_nat_term x)) (fst (rep_nat_term y)) of
                                      Eq \<Rightarrow> comparator_of (snd (rep_nat_term x)) (snd (rep_nat_term y)) | val \<Rightarrow> val)"

lemma full_componentE:
  assumes "snd (rep_nat_term x) = i"
  obtains y where "rep_nat_term y = (t, i)"
proof -
  from assms have "\<exists>y. rep_nat_term y = (t, i)" by (rule full_component)
  then obtain y where "rep_nat_term y = (t, i)" ..
  thus ?thesis ..
qed

end

class nat_pp_term = nat_term + zero + plus +
  assumes rep_nat_term_zero: "rep_nat_term 0 = (0, 0)"
    and splus_pp_term: "splus = (+)"

definition nat_term_comp :: "'a::nat_term comparator \<Rightarrow> bool"
  where "nat_term_comp cmp \<longleftrightarrow>
              (\<forall>u v. snd (rep_nat_term u) = snd (rep_nat_term v) \<longrightarrow> fst (rep_nat_term u) = 0 \<longrightarrow> cmp u v \<noteq> Gt) \<and>
              (\<forall>u v. fst (rep_nat_term u) = fst (rep_nat_term v) \<longrightarrow> snd (rep_nat_term u) < snd (rep_nat_term v) \<longrightarrow> cmp u v = Lt) \<and>
              (\<forall>t u v. cmp u v = Lt \<longrightarrow> cmp (splus t u) (splus t v) = Lt) \<and>
              (\<forall>u v a b. fst (rep_nat_term u) = fst (rep_nat_term a) \<longrightarrow> fst (rep_nat_term v) = fst (rep_nat_term b) \<longrightarrow>
                  snd (rep_nat_term u) = snd (rep_nat_term v) \<longrightarrow> snd (rep_nat_term a) = snd (rep_nat_term b) \<longrightarrow>
                  cmp a b = Lt \<longrightarrow> cmp u v = Lt)"

lemma nat_term_compI:
  assumes "\<And>u v. snd (rep_nat_term u) = snd (rep_nat_term v) \<Longrightarrow> fst (rep_nat_term u) = 0 \<Longrightarrow> cmp u v \<noteq> Gt"
    and "\<And>u v. fst (rep_nat_term u) = fst (rep_nat_term v) \<Longrightarrow> snd (rep_nat_term u) < snd (rep_nat_term v) \<Longrightarrow> cmp u v = Lt"
    and "\<And>t u v. cmp u v = Lt \<Longrightarrow> cmp (splus t u) (splus t v) = Lt"
    and "\<And>u v a b. fst (rep_nat_term u) = fst (rep_nat_term a) \<Longrightarrow> fst (rep_nat_term v) = fst (rep_nat_term b) \<Longrightarrow>
                  snd (rep_nat_term u) = snd (rep_nat_term v) \<Longrightarrow> snd (rep_nat_term a) = snd (rep_nat_term b) \<Longrightarrow>
                  cmp a b = Lt \<Longrightarrow> cmp u v = Lt"
  shows "nat_term_comp cmp"
  unfolding nat_term_comp_def fst_conv snd_conv using assms by blast

lemma nat_term_compD1:
  assumes "nat_term_comp cmp" and "snd (rep_nat_term u) = snd (rep_nat_term v)" and "fst (rep_nat_term u) = 0"
  shows "cmp u v \<noteq> Gt"
  using assms unfolding nat_term_comp_def fst_conv by blast

lemma nat_term_compD2:
  assumes "nat_term_comp cmp" and "fst (rep_nat_term u) = fst (rep_nat_term v)" and "snd (rep_nat_term u) < snd (rep_nat_term v)"
  shows "cmp u v = Lt"
  using assms unfolding nat_term_comp_def fst_conv snd_conv by blast

lemma nat_term_compD3:
  assumes "nat_term_comp cmp" and "cmp u v = Lt"
  shows "cmp (splus t u) (splus t v) = Lt"
  using assms unfolding nat_term_comp_def snd_conv by blast

lemma nat_term_compD4:
  assumes "nat_term_comp cmp" and "fst (rep_nat_term u) = fst (rep_nat_term a)"
    and "fst (rep_nat_term v) = fst (rep_nat_term b)" and "snd (rep_nat_term u) = snd (rep_nat_term v)"
    and "snd (rep_nat_term a) = snd (rep_nat_term b)" and "cmp a b = Lt"
  shows "cmp u v = Lt"
  using assms unfolding nat_term_comp_def snd_conv by blast

lemma nat_term_compD1':
  assumes "comparator cmp" and "nat_term_comp cmp" and "snd (rep_nat_term u) \<le> snd (rep_nat_term v)"
    and "fst (rep_nat_term u) = 0"
  shows "cmp u v \<noteq> Gt"
proof (cases "snd (rep_nat_term u) = snd (rep_nat_term v)")
  case True
  with assms(2) show ?thesis using assms(4) by (rule nat_term_compD1)
next
  from assms(1) interpret cmp: comparator cmp .
  case False
  with assms(3) have a: "snd (rep_nat_term u) < snd (rep_nat_term v)" by simp
  from refl obtain w::'a where eq: "rep_nat_term w = (0, snd (rep_nat_term v))" by (rule full_componentE)
  have "cmp u w = Lt" by (rule nat_term_compD2, fact assms(2), simp_all add: eq assms(4) a)
  moreover have "cmp w v \<noteq> Gt" by (rule nat_term_compD1, fact assms(2), simp_all add: eq)
  ultimately show "cmp u v \<noteq> Gt" by (simp add: cmp.nGt_le_conv cmp.Lt_lt_conv)
qed

lemma nat_term_compD4':
  assumes "comparator cmp" and "nat_term_comp cmp" and "fst (rep_nat_term u) = fst (rep_nat_term a)"
    and "fst (rep_nat_term v) = fst (rep_nat_term b)" and "snd (rep_nat_term u) = snd (rep_nat_term v)"
    and "snd (rep_nat_term a) = snd (rep_nat_term b)"
  shows "cmp u v = cmp a b"
proof -
  from assms(1) interpret cmp: comparator cmp .
  show ?thesis
  proof (cases "cmp a b")
    case Eq
    hence "fst (rep_nat_term u) = fst (rep_nat_term v)" by (simp add: cmp.eq assms(3, 4))
    hence "rep_nat_term u = rep_nat_term v" using assms(5) by (rule prod_eqI)
    hence "u = v" by (rule rep_nat_term_inj)
    thus ?thesis by (simp add: Eq)
  next
    case Lt
    with assms(2, 3, 4, 5, 6) have "cmp u v = Lt" by (rule nat_term_compD4)
    thus ?thesis by (simp add: Lt)
  next
    case Gt
    hence "cmp b a = Lt" by (simp only: cmp.Gt_lt_conv cmp.Lt_lt_conv)
    with assms(2, 4, 3) assms(5, 6)[symmetric] have "cmp v u = Lt" by (rule nat_term_compD4)
    hence "cmp u v = Gt" by (simp only: cmp.Gt_lt_conv cmp.Lt_lt_conv)
    thus ?thesis by (simp add: Gt)
  qed
qed

lemma nat_term_compD4'':
  assumes "comparator cmp" and "nat_term_comp cmp" and "fst (rep_nat_term u) = fst (rep_nat_term a)"
    and "fst (rep_nat_term v) = fst (rep_nat_term b)" and "snd (rep_nat_term u) \<le> snd (rep_nat_term v)"
    and "snd (rep_nat_term a) = snd (rep_nat_term b)" and "cmp a b \<noteq> Gt"
  shows "cmp u v \<noteq> Gt"
proof (cases "snd (rep_nat_term u) = snd (rep_nat_term v)")
  case True
  with assms(1, 2, 3, 4) have "cmp u v = cmp a b" using assms(6) by (rule nat_term_compD4')
  thus ?thesis using assms(7) by simp
next
  case False
  from assms(1) interpret cmp: comparator cmp .
  from refl obtain w::'a where w: "rep_nat_term w = (fst (rep_nat_term u), snd (rep_nat_term v))"
    by (rule full_componentE)
  have 1: "fst (rep_nat_term w) = fst (rep_nat_term a)" and 2: "snd (rep_nat_term w) = snd (rep_nat_term v)"
    by (simp_all add: w assms(3))
  from False assms(5) have *: "snd (rep_nat_term u) < snd (rep_nat_term v)" by simp
  have "cmp u w = Lt" by (rule nat_term_compD2, fact assms(2), simp_all add: * w)
  moreover from assms(1, 2) 1 assms(4) 2 assms(6) have "cmp w v = cmp a b" by (rule nat_term_compD4')
  ultimately show ?thesis using assms(7) by (metis cmp.nGt_le_conv cmp.nLt_le_conv cmp.trans)
qed

lemma comparator_lex_comp_aux: "comparator (lex_comp_aux::'a::nat_term comparator)"
  unfolding lex_comp_aux_def
proof (rule comparator_composition)
  from lex_pp_antisym have as: "antisymp lex_pp" by (rule antisympI)
  have "comparator (comp_of_ord (lex_pp::(nat, nat) pp \<Rightarrow> _))"
    unfolding comp_of_ord_eq_comp_of_ords[OF as]
    by (rule comp_of_ords, unfold_locales,
        auto simp: lex_pp_refl intro: lex_pp_trans lex_pp_lin' elim!: lex_pp_antisym)
  thus "comparator (\<lambda>x y::((nat, nat) pp \<times> nat). case comp_of_ord lex_pp (fst x) (fst y) of
                                          Eq \<Rightarrow> comparator_of (snd x) (snd y) | val \<Rightarrow> val)"
    using comparator_of prod_eqI by (rule comparator_lexicographic)
next
  from rep_nat_term_inj show "inj rep_nat_term" by (rule injI)
qed

lemma nat_term_comp_lex_comp_aux: "nat_term_comp (lex_comp_aux::'a::nat_term comparator)"
proof -
  from lex_pp_antisym have as: "antisymp lex_pp" by (rule antisympI)
  interpret lex: comparator "comp_of_ord (lex_pp::(nat, nat) pp \<Rightarrow> _)"
    unfolding comp_of_ord_eq_comp_of_ords[OF as]
    by (rule comp_of_ords, unfold_locales,
        auto simp: lex_pp_refl intro: lex_pp_trans lex_pp_lin' elim!: lex_pp_antisym)
  show ?thesis
  proof (rule nat_term_compI)
    fix u v :: 'a
    assume 1: "snd (rep_nat_term u) = snd (rep_nat_term v)" and 2: "fst (rep_nat_term u) = 0"
    show "lex_comp_aux u v \<noteq> Gt"
      by (simp add: lex_comp_aux_def 1 2 split: order.split, simp add: comp_of_ord_def lex_pp_zero_min)
  next
    fix u v :: 'a
    assume 1: "fst (rep_nat_term u) = fst (rep_nat_term v)" and 2: "snd (rep_nat_term u) < snd (rep_nat_term v)"
    show "lex_comp_aux u v = Lt"
      by (simp add: lex_comp_aux_def 1 split: order.split, simp add: comparator_of_def 2)
  next
    fix t u v :: 'a
    show "lex_comp_aux u v = Lt \<Longrightarrow> lex_comp_aux (splus t u) (splus t v) = Lt"
      by (auto simp: lex_comp_aux_def splus_term pprod.splus_def comp_of_ord_def lex_pp_refl
          split: order.splits if_splits intro: lex_pp_plus_monotone')
  next
    fix u v a b :: 'a
    assume "fst (rep_nat_term u) = fst (rep_nat_term a)" and "fst (rep_nat_term v) = fst (rep_nat_term b)"
      and "snd (rep_nat_term a) = snd (rep_nat_term b)" and "lex_comp_aux a b = Lt"
    thus "lex_comp_aux u v = Lt" by (simp add: lex_comp_aux_def split: order.splits)
  qed
qed

typedef (overloaded) 'a nat_term_order =
  "{cmp::'a::nat_term comparator. comparator cmp \<and> nat_term_comp cmp}"
  morphisms nat_term_compare Abs_nat_term_order
proof (rule, simp)
  from comparator_lex_comp_aux nat_term_comp_lex_comp_aux
  show "comparator lex_comp_aux \<and> nat_term_comp lex_comp_aux" ..
qed

lemma nat_term_compare_Abs_nat_term_order_id:
  assumes "comparator cmp" and "nat_term_comp cmp"
  shows "nat_term_compare (Abs_nat_term_order cmp) = cmp"
  by (rule Abs_nat_term_order_inverse, simp add: assms)

instantiation nat_term_order :: (type) equal
begin

definition equal_nat_term_order :: "'a nat_term_order \<Rightarrow> 'a nat_term_order \<Rightarrow> bool" where "equal_nat_term_order = (=)"

instance by (standard, simp add: equal_nat_term_order_def)

end

definition nat_term_compare_inv :: "'a nat_term_order \<Rightarrow> 'a::nat_term comparator"
  where "nat_term_compare_inv to = (\<lambda>x y. nat_term_compare to y x)"

definition key_order_of_nat_term_order :: "'a nat_term_order \<Rightarrow> 'a::nat_term key_order"
  where key_order_of_nat_term_order_def [code del]:
    "key_order_of_nat_term_order to = Abs_key_order (nat_term_compare to)"

definition key_order_of_nat_term_order_inv :: "'a nat_term_order \<Rightarrow> 'a::nat_term key_order"
  where key_order_of_nat_term_order_inv_def [code del]:
    "key_order_of_nat_term_order_inv to = Abs_key_order (nat_term_compare_inv to)"

definition le_of_nat_term_order :: "'a nat_term_order \<Rightarrow> 'a \<Rightarrow> 'a::nat_term \<Rightarrow> bool"
  where "le_of_nat_term_order to = le_of_key_order (key_order_of_nat_term_order to)"

definition lt_of_nat_term_order :: "'a nat_term_order \<Rightarrow> 'a \<Rightarrow> 'a::nat_term \<Rightarrow> bool"
  where "lt_of_nat_term_order to = lt_of_key_order (key_order_of_nat_term_order to)"

definition nat_term_order_of_le :: "'a::{linorder,nat_term} nat_term_order"
  where "nat_term_order_of_le = Abs_nat_term_order (comparator_of)"

lemma comparator_nat_term_compare: "comparator (nat_term_compare to)"
  using nat_term_compare by blast

lemma nat_term_comp_nat_term_compare: "nat_term_comp (nat_term_compare to)"
  using nat_term_compare by blast

lemma nat_term_compare_splus: "nat_term_compare to (splus t u) (splus t v) = nat_term_compare to u v"
proof -
  from comparator_nat_term_compare interpret cmp: comparator "nat_term_compare to" .
  show ?thesis
  proof (cases "nat_term_compare to u v")
    case Eq
    hence "splus t u = splus t v" by (simp add: cmp.eq)
    thus ?thesis by (simp add: cmp.eq Eq)
  next
    case Lt
    moreover from nat_term_comp_nat_term_compare this have "nat_term_compare to (splus t u) (splus t v) = Lt"
      by (rule nat_term_compD3)
    ultimately show ?thesis by simp
  next
    case Gt
    hence "nat_term_compare to v u = Lt" using cmp.Gt_lt_conv cmp.Lt_lt_conv by auto
    with nat_term_comp_nat_term_compare have "nat_term_compare to (splus t v) (splus t u) = Lt"
      by (rule nat_term_compD3)
    hence "nat_term_compare to (splus t u) (splus t v) = Gt" using cmp.Gt_lt_conv cmp.Lt_lt_conv by auto
    with Gt show ?thesis by simp
  qed
qed

lemma nat_term_compare_conv: "nat_term_compare to = key_compare (key_order_of_nat_term_order to)"
  unfolding key_order_of_nat_term_order_def
  by (rule sym, rule Abs_key_order_inverse, simp add: comparator_nat_term_compare)

lemma comparator_nat_term_compare_inv: "comparator (nat_term_compare_inv to)"
  unfolding nat_term_compare_inv_def using comparator_nat_term_compare by (rule comparator_converse)

lemma nat_term_compare_inv_conv: "nat_term_compare_inv to = key_compare (key_order_of_nat_term_order_inv to)"
  unfolding key_order_of_nat_term_order_inv_def
  by (rule sym, rule Abs_key_order_inverse, simp add: comparator_nat_term_compare_inv)

lemma nat_term_compare_inv_alt [code_unfold]: "nat_term_compare_inv to x y = nat_term_compare to y x"
  by (simp only: nat_term_compare_inv_def)

lemma le_of_nat_term_order [code]: "le_of_nat_term_order to x y = (nat_term_compare to x y \<noteq> Gt)"
  by (simp add: le_of_key_order_alt le_of_nat_term_order_def nat_term_compare_conv)

lemma lt_of_nat_term_order [code]: "lt_of_nat_term_order to x y = (nat_term_compare to x y = Lt)"
  by (simp add: lt_of_key_order_alt lt_of_nat_term_order_def nat_term_compare_conv)

lemma le_of_nat_term_order_alt:
  "le_of_nat_term_order to = (\<lambda>u v. ko.le (key_order_of_nat_term_order_inv to) v u)"
  by (intro ext, simp add: le_of_comp_def nat_term_compare_inv_conv[symmetric] le_of_nat_term_order_def
      le_of_key_order_def nat_term_compare_conv[symmetric] nat_term_compare_inv_alt)

lemma lt_of_nat_term_order_alt:
  "lt_of_nat_term_order to = (\<lambda>u v. ko.lt (key_order_of_nat_term_order_inv to) v u)"
  by (intro ext, simp add: lt_of_comp_def nat_term_compare_inv_conv[symmetric] lt_of_nat_term_order_def
      lt_of_key_order_def nat_term_compare_conv[symmetric] nat_term_compare_inv_alt)

lemma linorder_le_of_nat_term_order: "class.linorder (le_of_nat_term_order to) (lt_of_nat_term_order to)"
  unfolding le_of_nat_term_order_alt lt_of_nat_term_order_alt using ko.linorder
  by (rule linorder.dual_linorder)

lemma le_of_nat_term_order_zero_min: "le_of_nat_term_order to 0 (t::'a::nat_pp_term)"
  unfolding le_of_nat_term_order
  by (rule nat_term_compD1', fact comparator_nat_term_compare, fact nat_term_comp_nat_term_compare, simp_all add: rep_nat_term_zero)

lemma le_of_nat_term_order_plus_monotone:
  assumes "le_of_nat_term_order to s (t::'a::nat_pp_term)"
  shows "le_of_nat_term_order to (u + s) (u + t)"
  using assms by (simp add: le_of_nat_term_order splus_pp_term[symmetric] nat_term_compare_splus)

global_interpretation ko_ntm: comparator "nat_term_compare_inv ko"
  defines lookup_pair_ko_ntm = ko_ntm.lookup_pair
  and update_by_pair_ko_ntm = ko_ntm.update_by_pair
  and update_by_fun_pair_ko_ntm = ko_ntm.update_by_fun_pair
  and update_by_fun_gr_pair_ko_ntm = ko_ntm.update_by_fun_gr_pair
  and map2_val_pair_ko_ntm = ko_ntm.map2_val_pair
  and lex_ord_pair_ko_ntm = ko_ntm.lex_ord_pair
  and prod_ord_pair_ko_ntm = ko_ntm.prod_ord_pair
  and sort_oalist_ko_ntm' = ko_ntm.sort_oalist
  by (fact comparator_nat_term_compare_inv)

lemma ko_ntm_le: "ko_ntm.le to = (\<lambda>x y. le_of_nat_term_order to y x)"
  by (intro ext, simp add: le_of_comp_def le_of_nat_term_order nat_term_compare_inv_def split: order.split)

global_interpretation ko_ntm: oalist_raw key_order_of_nat_term_order_inv
  rewrites "comparator.lookup_pair (key_compare (key_order_of_nat_term_order_inv ko)) = lookup_pair_ko_ntm ko"
  and "comparator.update_by_pair (key_compare (key_order_of_nat_term_order_inv ko)) = update_by_pair_ko_ntm ko"
  and "comparator.update_by_fun_pair (key_compare (key_order_of_nat_term_order_inv ko)) = update_by_fun_pair_ko_ntm ko"
  and "comparator.update_by_fun_gr_pair (key_compare (key_order_of_nat_term_order_inv ko)) = update_by_fun_gr_pair_ko_ntm ko"
  and "comparator.map2_val_pair (key_compare (key_order_of_nat_term_order_inv ko)) = map2_val_pair_ko_ntm ko"
  and "comparator.lex_ord_pair (key_compare (key_order_of_nat_term_order_inv ko)) = lex_ord_pair_ko_ntm ko"
  and "comparator.prod_ord_pair (key_compare (key_order_of_nat_term_order_inv ko)) = prod_ord_pair_ko_ntm ko"
  and "comparator.sort_oalist (key_compare (key_order_of_nat_term_order_inv ko)) = sort_oalist_ko_ntm' ko"
  defines sort_oalist_aux_ko_ntm = ko_ntm.sort_oalist_aux
  and lookup_ko_ntm = ko_ntm.lookup_raw
  and sorted_domain_ko_ntm = ko_ntm.sorted_domain_raw
  and tl_ko_ntm = ko_ntm.tl_raw
  and min_key_val_ko_ntm = ko_ntm.min_key_val_raw
  and update_by_ko_ntm = ko_ntm.update_by_raw
  and update_by_fun_ko_ntm = ko_ntm.update_by_fun_raw
  and update_by_fun_gr_ko_ntm = ko_ntm.update_by_fun_gr_raw
  and map2_val_ko_ntm = ko_ntm.map2_val_raw
  and lex_ord_ko_ntm = ko_ntm.lex_ord_raw
  and prod_ord_ko_ntm = ko_ntm.prod_ord_raw
  and oalist_eq_ko_ntm = ko_ntm.oalist_eq_raw
  and sort_oalist_ko_ntm = ko_ntm.sort_oalist_raw
  subgoal by (simp only: lookup_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: update_by_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: update_by_fun_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: update_by_fun_gr_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: map2_val_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: lex_ord_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: prod_ord_pair_ko_ntm_def nat_term_compare_inv_conv)
  subgoal by (simp only: sort_oalist_ko_ntm'_def nat_term_compare_inv_conv)
  done

lemma compute_min_key_val_ko_ntm [code]:
  "min_key_val_ko_ntm ko (xs, ox) =
      (if ko = ox then hd else min_list_param (\<lambda>x y. (le_of_nat_term_order ko) (fst y) (fst x))) xs"
proof -
  have "ko.le (key_order_of_nat_term_order_inv ko) = (\<lambda>x y. le_of_nat_term_order ko y x)"
    by (metis ko.nGt_le_conv le_of_nat_term_order nat_term_compare_inv_conv nat_term_compare_inv_def)
  thus ?thesis by (simp only: min_key_val_ko_ntm_def oalist_raw.min_key_val_raw.simps)
qed

typedef (overloaded) ('a, 'b) oalist_ntm =
    "{xs::('a, 'b::zero, 'a::nat_term nat_term_order) oalist_raw. ko_ntm.oalist_inv xs}"
  morphisms list_of_oalist_ntm Abs_oalist_ntm
  by (auto simp: ko_ntm.oalist_inv_def intro: ko.oalist_inv_raw_Nil)

lemma oalist_ntm_eq_iff: "xs = ys \<longleftrightarrow> list_of_oalist_ntm xs = list_of_oalist_ntm ys"
  by (simp add: list_of_oalist_ntm_inject)

lemma oalist_ntm_eqI: "list_of_oalist_ntm xs = list_of_oalist_ntm ys \<Longrightarrow> xs = ys"
  by (simp add: oalist_ntm_eq_iff)

text \<open>Formal, totalized constructor for @{typ "('a, 'b) oalist_ntm"}:\<close>

definition OAlist_ntm :: "('a \<times> 'b) list \<times> 'a nat_term_order \<Rightarrow> ('a::nat_term, 'b::zero) oalist_ntm"
  where "OAlist_ntm xs = Abs_oalist_ntm (sort_oalist_ko_ntm xs)"

definition "oalist_of_list_ntm = OAlist_ntm"

lemma oalist_inv_list_of_oalist_ntm: "ko_ntm.oalist_inv (list_of_oalist_ntm xs)"
  using list_of_oalist_ntm[of xs] by simp

lemma list_of_oalist_OAlist_ntm: "list_of_oalist_ntm (OAlist_ntm xs) = sort_oalist_ko_ntm xs"
proof -
  obtain xs' ox where xs: "xs = (xs', ox)" by fastforce
  have "ko_ntm.oalist_inv (sort_oalist_ko_ntm' ox xs', ox)"
    using ko_ntm.oalist_inv_sort_oalist_raw by fastforce
  thus ?thesis by (simp add: xs OAlist_ntm_def Abs_oalist_ntm_inverse)
qed

lemma OAlist_list_of_oalist_ntm [simp, code abstype]: "OAlist_ntm (list_of_oalist_ntm xs) = xs"
proof -
  obtain xs' ox where xs: "list_of_oalist_ntm xs = (xs', ox)" by fastforce
  have "ko_ntm.oalist_inv_raw ox xs'"
    by (simp add: xs[symmetric] ko_ntm.oalist_inv_alt[symmetric] nat_term_compare_inv_conv oalist_inv_list_of_oalist_ntm)
  thus ?thesis by (simp add: xs OAlist_ntm_def ko_ntm.sort_oalist_id, simp add: list_of_oalist_ntm_inverse xs[symmetric])
qed

lemma [code abstract]: "list_of_oalist_ntm (oalist_of_list_ntm xs) = sort_oalist_ko_ntm xs"
  by (simp add: list_of_oalist_OAlist_ntm oalist_of_list_ntm_def)

global_interpretation oa_ntm: oalist_abstract key_order_of_nat_term_order_inv list_of_oalist_ntm OAlist_ntm
  defines OAlist_lookup_ntm = oa_ntm.lookup
  and OAlist_sorted_domain_ntm = oa_ntm.sorted_domain
  and OAlist_empty_ntm = oa_ntm.empty
  and OAlist_reorder_ntm = oa_ntm.reorder
  and OAlist_tl_ntm = oa_ntm.tl
  and OAlist_hd_ntm = oa_ntm.hd
  and OAlist_except_min_ntm = oa_ntm.except_min
  and OAlist_min_key_val_ntm = oa_ntm.min_key_val
  and OAlist_insert_ntm = oa_ntm.insert
  and OAlist_update_by_fun_ntm = oa_ntm.update_by_fun
  and OAlist_update_by_fun_gr_ntm = oa_ntm.update_by_fun_gr
  and OAlist_filter_ntm = oa_ntm.filter
  and OAlist_map2_val_neutr_ntm = oa_ntm.map2_val_neutr
  and OAlist_eq_ntm = oa_ntm.oalist_eq
  apply unfold_locales
  subgoal by (fact oalist_inv_list_of_oalist_ntm)
  subgoal by (simp only: list_of_oalist_OAlist_ntm sort_oalist_ko_ntm_def)
  subgoal by (fact OAlist_list_of_oalist_ntm)
  done

global_interpretation oa_ntm: oalist_abstract3 key_order_of_nat_term_order_inv
    "list_of_oalist_ntm::('a, 'b) oalist_ntm \<Rightarrow> ('a, 'b::zero, 'a::nat_term nat_term_order) oalist_raw" OAlist_ntm
    "list_of_oalist_ntm::('a, 'c) oalist_ntm \<Rightarrow> ('a, 'c::zero, 'a nat_term_order) oalist_raw" OAlist_ntm
    "list_of_oalist_ntm::('a, 'd) oalist_ntm \<Rightarrow> ('a, 'd::zero, 'a nat_term_order) oalist_raw" OAlist_ntm
  defines OAlist_map_val_ntm = oa_ntm.map_val
  and OAlist_map2_val_ntm = oa_ntm.map2_val
  and OAlist_map2_val_rneutr_ntm = oa_ntm.map2_val_rneutr
  and OAlist_lex_ord_ntm = oa_ntm.lex_ord
  and OAlist_prod_ord_ntm = oa_ntm.prod_ord ..

lemmas OAlist_lookup_ntm_single = oa_ntm.lookup_oalist_of_list_single[folded oalist_of_list_ntm_def]

end (* theory *)
