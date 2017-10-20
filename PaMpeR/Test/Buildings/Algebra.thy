section {* Algebra *}

text {*
  In this section, we develop the necessary algebra for developing the theory of Coxeter systems,
  including groups, quotient groups, free groups, group presentations, and words in a group over a
  set of generators.
*}

theory Algebra
imports Prelim "HOL-Library.Set_Algebras"

begin

subsection {* Miscellaneous algebra facts *}

lemma times2_conv_add: "(j::nat) + j = 2*j"
  by (induct j) auto

lemma (in comm_semiring_1) odd_n0: "odd m \<Longrightarrow> m\<noteq>0"
  using dvd_0_right by fast

lemma (in semigroup_add) add_assoc4: "a + b + c + d = a + (b + c + d)"
  using add.assoc by simp

lemmas (in monoid_add) sum_list_map_cong =
  arg_cong[OF map_cong, OF refl, of _ _ _ sum_list]

context group_add
begin

lemma map_uminus_order2:
  "\<forall>s\<in>set ss. s+s=0 \<Longrightarrow> map (uminus) ss = ss"
  by (induct ss) (auto simp add: minus_unique)

lemma uminus_sum_list: "- sum_list as = sum_list (map uminus (rev as))"
  by (induct as) (auto simp add: minus_add)

lemma uminus_sum_list_order2:
  "\<forall>s\<in>set ss. s+s=0 \<Longrightarrow> - sum_list ss = sum_list (rev ss)"
  using uminus_sum_list map_uminus_order2 by simp

end (* context group_add *)

subsection {* The type of permutations of a type *}

text {*
  Here we construct a type consisting of all bijective functions on a type. This is the
  prototypical example of a group, where the group operation is composition, and every group can
  be embedded into such a type. It is for this purpose that we construct this type, so that we may
  confer upon suitable subsets of types that are not of class @{class group_add} the properties of
  that class, via a suitable injective correspondence to this permutation type.
*}

typedef 'a permutation = "{f::'a\<Rightarrow>'a. bij f}"
  morphisms permutation Abs_permutation
  by fast

setup_lifting type_definition_permutation

abbreviation permutation_apply :: "'a permutation \<Rightarrow> 'a \<Rightarrow> 'a " (infixr "\<rightarrow>" 90)
  where "p \<rightarrow> a \<equiv> permutation p a"
abbreviation permutation_image :: "'a permutation \<Rightarrow> 'a set \<Rightarrow> 'a set"
  (infixr "`\<rightarrow>" 90)
  where "p `\<rightarrow> A \<equiv> permutation p ` A"

lemma permutation_eq_image: "a `\<rightarrow> A = a `\<rightarrow> B \<Longrightarrow> A=B"
  using permutation[of a] inj_eq_image[OF bij_is_inj] by auto

instantiation permutation :: (type) zero
begin
lift_definition zero_permutation :: "'a permutation" is "id::'a\<Rightarrow>'a" by simp
instance ..
end

instantiation permutation :: (type) plus
begin
lift_definition plus_permutation :: "'a permutation \<Rightarrow> 'a permutation \<Rightarrow> 'a permutation"
  is    "comp"
  using bij_comp
  by    fast
instance ..
end

lemma plus_permutation_abs_eq:
  "bij f \<Longrightarrow> bij g \<Longrightarrow>
    Abs_permutation f + Abs_permutation g = Abs_permutation (f\<circ>g)"
  by (simp add: plus_permutation.abs_eq eq_onp_same_args)

instance permutation :: (type) semigroup_add
proof
  fix a b c :: "'a permutation" show "a + b + c = a + (b + c)"
    using comp_assoc[of "permutation a" "permutation b" "permutation c"]
    by    transfer simp
qed

instance permutation :: (type) monoid_add
proof
  fix a :: "'a permutation"
  show "0 + a = a" by transfer simp
  show "a + 0 = a" by transfer simp
qed

instantiation permutation :: (type) uminus
begin
lift_definition uminus_permutation :: "'a permutation \<Rightarrow> 'a permutation"
  is    "\<lambda>f. the_inv f"
  using bij_betw_the_inv_into
  by    fast
instance ..
end

instantiation permutation :: (type) minus
begin
lift_definition minus_permutation :: "'a permutation \<Rightarrow> 'a permutation \<Rightarrow> 'a permutation"
  is    "\<lambda>f g. f \<circ> (the_inv g)"
  using bij_betw_the_inv_into bij_comp
  by    fast
instance ..
end

lemma minus_permutation_abs_eq:
  "bij f \<Longrightarrow> bij g \<Longrightarrow>
    Abs_permutation f - Abs_permutation g = Abs_permutation (f \<circ> the_inv g)"
  by (simp add: minus_permutation.abs_eq eq_onp_same_args)

instance permutation :: (type) group_add
proof
  fix a b :: "'a permutation"
  show "- a + a = 0" using the_inv_leftinv[of "permutation a"] by transfer simp
  show "a + - b = a - b" by transfer simp
qed


subsection {* Natural action of @{typ nat} on types of class @{class monoid_add} *}

subsubsection {* Translation from class @{class power}. *}

text {* 
  Here we translate the @{class power} class to apply to types of class @{class monoid_add}.
*}

context monoid_add
begin

sublocale nataction: power 0 plus .
sublocale add_mult_translate: monoid_mult 0 plus
  by unfold_locales (auto simp add: add.assoc)

abbreviation nataction :: "'a \<Rightarrow> nat \<Rightarrow> 'a" (infix "+^" 80)
  where "a+^n  \<equiv> nataction.power a n"

lemmas nataction_2    = add_mult_translate.power2_eq_square
lemmas nataction_Suc2 = add_mult_translate.power_Suc2

lemma alternating_sum_list_conv_nataction:
  "sum_list (alternating_list (2*n) s t) = (s+t)+^n"
  by (induct n) (auto simp add: nataction_Suc2[THEN sym])

lemma nataction_add_flip: "(a+b)+^(Suc n) = a + (b+a)+^n + b"
  using nataction_Suc2 add.assoc by (induct n arbitrary: a b) auto

end (* context monoid_add *)

lemma (in group_add) nataction_add_eq0_flip:
  assumes "(a+b)+^n = 0"
  shows   "(b+a)+^n = 0"
proof (cases n)
  case (Suc k) with assms show ?thesis
    using nataction_add_flip add.assoc[of "-a" "a+b" "(a+b)+^k"] by simp
qed simp

subsubsection {* Additive order of an element *}

context monoid_add
begin

definition add_order :: "'a \<Rightarrow> nat"
  where "add_order a \<equiv> if (\<exists>n>0. a+^n = 0) then
          (LEAST n. n>0 \<and> a+^n = 0) else 0"

lemma add_order: "a+^(add_order a) = 0"
  using LeastI_ex[of "\<lambda>n. n>0 \<and> a+^n = 0"] add_order_def by simp

lemma add_order_least: "n>0 \<Longrightarrow> a+^n = 0 \<Longrightarrow> add_order a \<le> n"
  using Least_le[of "\<lambda>n. n>0 \<and> a+^n = 0"] add_order_def by simp

lemma add_order_equality:
  "\<lbrakk> n>0; a+^n = 0; (\<And>m. m>0 \<Longrightarrow> a+^m = 0 \<Longrightarrow> n\<le>m) \<rbrakk> \<Longrightarrow>
    add_order a = n"
  using Least_equality[of "\<lambda>n. n>0 \<and> a+^n = 0"] add_order_def by auto

lemma add_order0: "add_order 0 = 1"
  using add_order_equality by simp

lemma add_order_gt0: "(add_order a > 0) = (\<exists>n>0. a+^n = 0)"
  using LeastI_ex[of "\<lambda>n. n>0 \<and> a+^n = 0"] add_order_def by simp

lemma add_order_eq0: "add_order a = 0 \<Longrightarrow> n>0 \<Longrightarrow> a+^n \<noteq> 0"
  using add_order_gt0 by force

lemma less_add_order_eq_0:
  assumes "a+^k = 0" "k < add_order a"
  shows   "k = 0"
proof (cases "k=0")
  case False
  moreover with assms(1) have "\<exists>n>0. a+^n = 0" by fast
  ultimately show ?thesis
    using assms add_order_def not_less_Least[of k "\<lambda>n. n>0 \<and> a+^n = 0"]
    by    auto
qed simp

lemma less_add_order_eq_0_contra: "k>0 \<Longrightarrow> k < add_order a \<Longrightarrow> a+^k \<noteq> 0"
  using less_add_order_eq_0 by fast

lemma add_order_relator: "add_order (a+^(add_order a)) = 1"
  using add_order by (auto intro: add_order_equality)

abbreviation pair_relator_list :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "pair_relator_list s t \<equiv> alternating_list (2*add_order (s+t)) s t"
abbreviation pair_relator_halflist :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "pair_relator_halflist s t \<equiv> alternating_list (add_order (s+t)) s t"
abbreviation pair_relator_halflist2 :: "'a \<Rightarrow> 'a \<Rightarrow> 'a list"
  where "pair_relator_halflist2 s t \<equiv>
    (if even (add_order (s+t)) then pair_relator_halflist s t else
      pair_relator_halflist t s)"

lemma sum_list_pair_relator_list: "sum_list (pair_relator_list s t) = 0"
  by (auto simp add: add_order alternating_sum_list_conv_nataction)

end (* context monoid_add *)

context group_add
begin

lemma add_order_add_eq1: "add_order (s+t) = 1 \<Longrightarrow> t = -s"
  using add_order[of "s+t"] by (simp add: minus_unique)

lemma add_order_add_sym: "add_order (t+s) = add_order (s+t)"
proof (cases "add_order (t+s) = 0" "add_order (s+t) = 0" rule: two_cases)
  case one thus ?thesis
    using add_order nataction_add_eq0_flip[of s t] add_order_eq0 by auto
next
  case other thus ?thesis
    using add_order nataction_add_eq0_flip[of t s] add_order_eq0 by auto
next
  case neither thus ?thesis
    using add_order[of "s+t"] add_order[of "t+s"]
          nataction_add_eq0_flip[of s t] nataction_add_eq0_flip[of t s]
          add_order_least[of "add_order (s+t)"] add_order_least[of "add_order (t+s)"]
    by fastforce
qed simp

lemma pair_relator_halflist_append:
  "pair_relator_halflist s t @ pair_relator_halflist2 s t = pair_relator_list s t"
  using alternating_list_split[of "add_order (s+t)" "add_order (s+t)" s t]
  by    (auto simp add: times2_conv_add add_order_add_sym)

lemma rev_pair_relator_list: "rev (pair_relator_list s t) = pair_relator_list t s"
  by (simp add:rev_alternating_list add_order_add_sym)

lemma pair_relator_halflist2_conv_rev_pair_relator_halflist:
  "pair_relator_halflist2 s t = rev (pair_relator_halflist t s)"
  by (auto simp add: add_order_add_sym rev_alternating_list)
 
end (* context group_add *)

subsection {* Partial sums of a list *}

text {*
  Here we construct a list that collects the results of adding the elements of a given list
  together one-by-one.
*}

context monoid_add
begin

primrec sums :: "'a list \<Rightarrow> 'a list"
  where
    "sums [] = [0]"
  | "sums (x#xs) = 0 # map (op + x) (sums xs)"

lemma length_sums: "length (sums xs) = Suc (length xs)"
  by (induct xs) auto

lemma sums_snoc: "sums (xs@[x]) = sums xs @ [sum_list (xs@[x])]"
  by (induct xs) (auto simp add: add.assoc)

lemma sums_append2:
  "sums (xs@ys) = butlast (sums xs) @ map (op + (sum_list xs)) (sums ys)"
proof (induct ys rule: rev_induct)
  case Nil show ?case by (cases xs rule: rev_cases) (auto simp add: sums_snoc)
next
  case (snoc y ys) thus ?case using sums_snoc[of "xs@ys"] by (simp add: sums_snoc)
qed

lemma sums_Cons_conv_append_tl:
  "sums (x#xs) = 0 # x # map (op + x) (tl (sums xs))"
  by (cases xs) auto

lemma pullback_sums_map_middle2:
  "map F (sums xs) = ds@[d,e]@es \<Longrightarrow>
    \<exists>as a bs. xs = as@[a]@bs \<and> map F (sums as) = ds@[d] \<and>
      d = F (sum_list as) \<and> e = F (sum_list (as@[a]))"
proof (induct xs es rule: list_induct2_snoc)
  case (Nil2 xs)
  show ?case
  proof (cases xs rule: rev_cases)
    case Nil with Nil2 show ?thesis by simp
  next
    case (snoc ys y) have ys: "xs = ys@[y]" by fact
    with Nil2(1) have y: "map F (sums ys) = ds@[d]" "e = F (sum_list (ys@[y]))"
      by (auto simp add: sums_snoc)
    show ?thesis
    proof (cases ys rule: rev_cases)
      case Nil
      with ys y have
        "xs = []@[y]@[]" "map F (sums []) = ds@[d]"
        "d = F (sum_list [])" "e = F (sum_list ([]@[y]))"
        by auto
      thus ?thesis by fast
    next
      case (snoc zs z)
      with y(1) have z: "map F (sums zs) = ds" "d = F (sum_list (zs@[z]))"
        by (auto simp add: sums_snoc)
      from z(1) ys y snoc have
        "xs = (zs@[z])@[y]@[]" "map F (sums (zs@[z])) = ds@[d]"
        "e = F (sum_list ((zs@[z])@[y]))"
        by auto
      with z(2) show ?thesis by fast
    qed
  qed
next
  case snoc thus ?case by (fastforce simp add: sums_snoc)
qed simp

lemma pullback_sums_map_middle3:
  "map F (sums xs) = ds@[d,e,f]@fs \<Longrightarrow>
    \<exists>as a b bs. xs = as@[a,b]@bs \<and> d = F (sum_list as) \<and>
      e = F (sum_list (as@[a])) \<and> f = F (sum_list (as@[a,b]))"
proof (induct xs fs rule: list_induct2_snoc)
  case (Nil2 xs)
  show ?case
  proof (cases xs rule: rev_cases)
    case Nil with Nil2 show ?thesis by simp
  next
    case (snoc ys y)
    with Nil2 have y: "map F (sums ys) = ds@[d,e]" "f = F (sum_list (ys@[y]))"
      by (auto simp add: sums_snoc)
    from y(1) obtain as a bs where asabs:
      "ys = as@[a]@bs" "map F (sums as) = ds@[d]"
      "d = F (sum_list as)" "e = F (sum_list (as@[a]))"
      using pullback_sums_map_middle2[of F ys ds]
      by    fastforce
    have "bs = []"
    proof-
      from y(1) asabs(1,2) have "Suc (length bs) = Suc 0"
        by (auto simp add: sums_append2 map_butlast length_sums[THEN sym])
      thus ?thesis by fast
    qed
    with snoc asabs(1) y(2) have "xs = as@[a,y]@[]" "f = F (sum_list (as@[a,y]))"
      by auto
    with asabs(3,4) show ?thesis by fast
  qed
next
  case snoc thus ?case by (fastforce simp add: sums_snoc)
qed simp

lemma pullback_sums_map_double_middle2:
  assumes "map F (sums xs) = ds@[d,e]@es@[f,g]@gs"
  shows   "\<exists>as a bs b cs. xs = as@[a]@bs@[b]@cs \<and> d = F (sum_list as) \<and>
            e = F (sum_list (as@[a])) \<and> f = F (sum_list (as@[a]@bs)) \<and>
            g = F (sum_list (as@[a]@bs@[b]))"
proof-
  from assms obtain As b cs where Asbcs:
    "xs = As@[b]@cs" "map F (sums As) = ds@[d,e]@es@[f]"
    "f = F (sum_list As)" "g = F (sum_list (As@[b]))"
    using pullback_sums_map_middle2[of F xs "ds@[d,e]@es"]
    by    fastforce
  from Asbcs show ?thesis
    using pullback_sums_map_middle2[of F As ds d e "es@[f]"] by fastforce
qed

end (* context monoid_add *)

subsection {* Sums of alternating lists *}

lemma (in group_add) uminus_sum_list_alternating_order2:
  "s+s=0 \<Longrightarrow> t+t=0 \<Longrightarrow> - sum_list (alternating_list n s t) =
    sum_list (if even n then alternating_list n t s else alternating_list n s t)"
  using uminus_sum_list_order2 set_alternating_list[of n] rev_alternating_list[of n s]
  by    fastforce

context monoid_add
begin

lemma alternating_order2_cancel_1left:
  "s+s=0 \<Longrightarrow>
    sum_list (s # (alternating_list (Suc n) s t)) = sum_list (alternating_list n t s)"
  using add.assoc[of s s] alternating_list_Suc_Cons[of n s] by simp

lemma alternating_order2_cancel_2left:
  "s+s=0 \<Longrightarrow> t+t=0 \<Longrightarrow>
    sum_list (t # s # (alternating_list (Suc (Suc n)) s t)) =
      sum_list (alternating_list n s t)"
    using alternating_order2_cancel_1left[of s "Suc n"]
          alternating_order2_cancel_1left[of t n]
    by    simp

lemma alternating_order2_even_cancel_right:
  assumes st    : "s+s=0" "t+t=0"
  and     even_n: "even n"
  shows   "m \<le> n \<Longrightarrow> sum_list (alternating_list n s t @ alternating_list m t s) =
            sum_list (alternating_list (n-m) s t)"
proof (induct n arbitrary: m rule: nat_even_induct, rule even_n)
  case (SucSuc k) with st show ?case
    using alternating_order2_cancel_2left[of t s]
    by    (cases m rule: nat_cases_2Suc) auto
qed simp

end (* context monoid_add *)

subsection {* Conjugation in @{class group_add} *}

subsubsection {* Abbreviations and basic facts *}

context group_add
begin

abbreviation lconjby :: "'a\<Rightarrow>'a\<Rightarrow>'a"
  where "lconjby x y \<equiv> x+y-x"

abbreviation rconjby :: "'a\<Rightarrow>'a\<Rightarrow>'a"
  where "rconjby x y \<equiv> -x+y+x"

lemma lconjby_add: "lconjby (x+y) z = lconjby x (lconjby y z)"
  by (auto simp add: algebra_simps)

lemma rconjby_add: "rconjby (x+y) z = rconjby y (rconjby x z)"
  by (simp add: minus_add add.assoc[THEN sym])

lemma add_rconjby: "rconjby x y + rconjby x z = rconjby x (y+z)"
  by (simp add: add.assoc)

lemma lconjby_uminus: "lconjby x (-y) = - lconjby x y"
  using minus_unique[of "lconjby x y", THEN sym] by (simp add: algebra_simps)

lemma rconjby_uminus: "rconjby x (-y) = - rconjby x y"
  using minus_unique[of "rconjby x y"] add_assoc4[of "rconjby x y" "-x" "-y" x] by simp

lemma lconjby_rconjby: "lconjby x (rconjby x y) = y"
  by (simp add: algebra_simps)

lemma rconjby_lconjby: "rconjby x (lconjby x y) = y"
  by (simp add: algebra_simps)

lemma lconjby_inj: "inj (lconjby x)"
  using rconjby_lconjby by (fast intro: inj_on_inverseI)

lemma rconjby_inj: "inj (rconjby x)"
  using lconjby_rconjby by (fast intro: inj_on_inverseI)

lemma lconjby_surj: "surj (lconjby x)"
  using lconjby_rconjby surjI[of "lconjby x"] by fast

lemma lconjby_bij: "bij (lconjby x)"
  unfolding bij_def using lconjby_inj lconjby_surj by fast

lemma the_inv_lconjby: "the_inv (lconjby x) = (rconjby x)"
  using bij_betw_f_the_inv_into_f[OF lconjby_bij, of _ x] lconjby_rconjby
  by    (force intro: inj_onD[OF lconjby_inj, of x])

lemma lconjby_eq_conv_rconjby_eq: "w = lconjby x y \<Longrightarrow> y = rconjby x w"
  using the_inv_lconjby the_inv_into_f_f[OF lconjby_inj] by force

lemma rconjby_order2: "s+s = 0 \<Longrightarrow> rconjby x s + rconjby x s = 0"
  by (simp add: add_rconjby)

lemma rconjby_order2_eq_lconjby:
  assumes "s+s=0"
  shows   "rconjby s = lconjby s"
proof-
  have "rconjby s = lconjby (-s)" by simp
  with assms show ?thesis using minus_unique by simp
qed

lemma lconjby_alternating_list_order2:
  assumes "s+s=0" "t+t=0"
  shows   "lconjby (sum_list (alternating_list k s t)) (if even k then s else t) =
            sum_list (alternating_list (Suc (2*k)) s t)"
proof (induct k rule: nat_induct_step2)
  case (SucSuc m)
  have "lconjby (sum_list (alternating_list (Suc (Suc m)) s t))
          (if even (Suc (Suc m)) then s else t) = s + t +
          lconjby (sum_list (alternating_list m s t)) (if even m then s else t) - t - s"
    using alternating_list_SucSuc_ConsCons[of m s t]
    by    (simp add: algebra_simps)
  also from assms SucSuc
    have  "\<dots> = sum_list (alternating_list (Suc (2*Suc (Suc m))) s t)"
    using alternating_list_SucSuc_ConsCons[of "Suc (2*m)" s t]
          sum_list.append[of "alternating_list (Suc (2*Suc m)) s t" "[t]"]
    by    (simp add: algebra_simps)
  finally show ?case by fast
qed (auto simp add: assms(1) algebra_simps)

end (* context group_add *)

subsubsection {* The conjugation sequence *}

text {*
  Given a list in @{class group_add}, we create a new list by conjugating each term by all the
  previous terms. This sequence arises in Coxeter systems.
*}

context group_add
begin

primrec lconjseq :: "'a list \<Rightarrow> 'a list"
  where
    "lconjseq []     = []"
  | "lconjseq (x#xs) = x # (map (lconjby x) (lconjseq xs))"

lemma length_lconjseq: "length (lconjseq xs) = length xs"
  by (induct xs) auto

lemma lconjseq_snoc: "lconjseq (xs@[x]) = lconjseq xs @ [lconjby (sum_list xs) x]"
  by (induct xs) (auto simp add: lconjby_add)

lemma lconjseq_append:
  "lconjseq (xs@ys) = lconjseq xs @ (map (lconjby (sum_list xs)) (lconjseq ys))"
proof (induct ys rule: rev_induct)
  case (snoc y ys) thus ?case
    using lconjseq_snoc[of "xs@ys"] lconjseq_snoc[of ys] by (simp add: lconjby_add)
qed simp

lemma lconjseq_alternating_order2_repeats':
  fixes   s t :: 'a
  defines altst: "altst \<equiv> \<lambda>n. alternating_list n s t"
  and     altts: "altts \<equiv> \<lambda>n. alternating_list n t s"
  assumes st   : "s+s=0" "t+t=0" "(s+t)+^k = 0"
  shows   "map (lconjby (sum_list (altst k)))
            (lconjseq (if even k then altst m else altts m)) = lconjseq (altst m)"
proof (induct m)
  case (Suc j)
  with altst altts
    have  "map (lconjby (sum_list (altst k)))
            (lconjseq (if even k then altst (Suc j) else altts (Suc j))) =
            lconjseq (altst j) @
            [lconjby (sum_list (altst k @ (if even k then altst j else altts j)))
            (if even k then (if even j then s else t) else (if even j then t else s))]"
    by    (auto simp add: lconjseq_snoc lconjby_add)
  also from altst altts st(1,2)
    have  "\<dots> = lconjseq (altst j) @ [sum_list (altst (Suc (2*(k+j))))]"
    using lconjby_alternating_list_order2[of s t "k+j"] 
    by    (cases "even k")
          (auto simp add: alternating_list_append[of k])
  finally show ?case using altst st
    by    (auto simp add:
            alternating_list_append(1)[THEN sym]
            alternating_sum_list_conv_nataction
            lconjby_alternating_list_order2 lconjseq_snoc
          )
qed (simp add: altst altts)

lemma lconjseq_alternating_order2_repeats:
  fixes   s t :: 'a and k :: nat
  defines altst: "altst \<equiv> \<lambda>n. alternating_list n s t"
  and     altts: "altts \<equiv> \<lambda>n. alternating_list n t s"
  assumes st: "s+s=0" "t+t=0" "(s+t)+^k = 0"
  shows   "lconjseq (altst (2*k)) = lconjseq (altst k) @ lconjseq (altst k)"
proof-
  from altst altts
    have "lconjseq (altst (2*k)) = lconjseq (altst k) @
            map (lconjby (sum_list (altst k)))
              (lconjseq (if even k then altst k else altts k))"
    using alternating_list_append[THEN sym, of k k s t]
    by    (auto simp add: times2_conv_add lconjseq_append)
  with altst altts st show ?thesis
    using lconjseq_alternating_order2_repeats'[of s t k k] by auto
qed

lemma even_count_lconjseq_alternating_order2:
  fixes   s t :: 'a
  assumes "s+s=0" "t+t=0" "(s+t)+^k = 0"
  shows   "even (count_list (lconjseq (alternating_list (2*k) s t)) x)"
proof-
  define xs where xs: "xs \<equiv> lconjseq (alternating_list (2*k) s t)"
  with assms obtain as where "xs = as@as"
    using lconjseq_alternating_order2_repeats by fast
  hence "count_list xs x = 2 * (count_list as x)"
    by (simp add: count_list_append times2_conv_add)
  with xs show ?thesis by simp
qed

lemma order2_hd_in_lconjseq_deletion:
  shows "s+s=0 \<Longrightarrow> s \<in> set (lconjseq ss)
            \<Longrightarrow> \<exists>as b bs. ss = as@[b]@bs \<and> sum_list (s#ss) = sum_list (as@bs)"
proof (induct ss arbitrary: s rule: rev_induct)
  case (snoc t ts) show ?case
  proof (cases "s \<in> set (lconjseq ts)")
    case True
    with snoc(1,2) obtain as b bs
      where   asbbs: "ts = as @[b]@bs" "sum_list (s#ts) = sum_list (as@bs)"
      by      fastforce
    from asbbs(2) have "sum_list (s#ts@[t]) = sum_list (as@(bs@[t]))"
      using sum_list.append[of "s#ts" "[t]"] sum_list.append[of "as@bs" "[t]"] by simp
    with asbbs(1) show ?thesis by fastforce
  next
    case False
    with snoc(3) have s: "s = lconjby (sum_list ts) t" by (simp add: lconjseq_snoc)
    with snoc(2) have "t+t=0"
      using lconjby_eq_conv_rconjby_eq[of s "sum_list ts" t]
            rconjby_order2[of s "sum_list ts"]
      by    simp
    moreover from s have "sum_list (s#ts@[t]) = sum_list ts + t + t"
      using add.assoc[of "sum_list ts + t - sum_list ts" "sum_list ts"]
      by    (simp add: algebra_simps)
    ultimately have "sum_list (s#ts@[t]) = sum_list (ts@[])"
      by (simp add: algebra_simps)
    thus ?thesis by fast
  qed
qed simp

end (* context group_add *)

subsubsection {* The action on signed @{class group_add} elements *}

text {*
  Here we construct an action of a group on itself by conjugation, where group elements are
  endowed with an auxiliary sign by pairing with a boolean element. In multiple applications of
  this action, the auxiliary sign helps keep track of how many times the elements conjugating and
  being conjugated are the same. This action arises in exploring reduced expressions of group
  elements as words in a set of generators of order two (in particular, in a Coxeter group).
*}

type_synonym 'a signed = "'a\<times>bool"

definition signed_funaction :: "('a\<Rightarrow>'a\<Rightarrow>'a) \<Rightarrow> 'a \<Rightarrow> 'a signed \<Rightarrow> 'a signed"
  where "signed_funaction f s x \<equiv> map_prod (f s) (\<lambda>b. b \<noteq> (fst x = s)) x"
  -- {* so the sign of @{term x} is flipped precisely when its first component is equal to
@{term s} *}

context group_add
begin

abbreviation "signed_lconjaction \<equiv> signed_funaction lconjby"
abbreviation "signed_rconjaction \<equiv> signed_funaction rconjby"

lemmas signed_lconjactionD = signed_funaction_def[of lconjby]
lemmas signed_rconjactionD = signed_funaction_def[of rconjby]

abbreviation signed_lconjpermutation :: "'a \<Rightarrow> 'a signed permutation"
  where "signed_lconjpermutation s \<equiv> Abs_permutation (signed_lconjaction s)"

abbreviation signed_list_lconjaction :: "'a list \<Rightarrow> 'a signed \<Rightarrow> 'a signed"
  where "signed_list_lconjaction ss \<equiv> foldr signed_lconjaction ss"

lemma signed_lconjaction_fst: "fst (signed_lconjaction s x) = lconjby s (fst x)"
  using signed_lconjactionD by simp

lemma signed_lconjaction_rconjaction:
  "signed_lconjaction s (signed_rconjaction s x) = x"
proof-
  obtain a::'a and b::bool where "x = (a,b)" by fastforce
  thus ?thesis
    using signed_lconjactionD signed_rconjactionD injD[OF rconjby_inj, of s a]
          lconjby_rconjby[of s a]
    by    auto
qed

lemma signed_rconjaction_by_order2_eq_lconjaction:
  "s+s=0 \<Longrightarrow> signed_rconjaction s = signed_lconjaction s"
  using signed_funaction_def[of lconjby s] signed_funaction_def[of rconjby s]
        rconjby_order2_eq_lconjby[of s]
  by    auto

lemma inj_signed_lconjaction: "inj (signed_lconjaction s)"
proof (rule injI)
  fix x y assume 1: "signed_lconjaction s x = signed_lconjaction s y"
  moreover obtain a1 a2 :: 'a and b1 b2 :: bool
    where xy: "x = (a1,b1)" "y = (a2,b2)"
    by    fastforce
  ultimately show "x=y"
    using injD[OF lconjby_inj, of s a1 a2] signed_lconjactionD 
    by    (cases "a1=s" "a2=s" rule: two_cases) auto
qed

lemma surj_signed_lconjaction: "surj (signed_lconjaction s)"
  using signed_lconjaction_rconjaction[THEN sym] by fast

lemma bij_signed_lconjaction: "bij (signed_lconjaction s)"
  using inj_signed_lconjaction surj_signed_lconjaction by (fast intro: bijI)

lemma the_inv_signed_lconjaction:
  "the_inv (signed_lconjaction s) = signed_rconjaction s"
proof
  fix x
  show "the_inv (signed_lconjaction s) x = signed_rconjaction s x"
  proof (rule the_inv_into_f_eq, rule inj_signed_lconjaction)
    show "signed_lconjaction s (signed_rconjaction s x) = x"
      using signed_lconjaction_rconjaction by fast
  qed (simp add: surj_signed_lconjaction)
qed

lemma the_inv_signed_lconjaction_by_order2:
  "s+s=0 \<Longrightarrow> the_inv (signed_lconjaction s) = signed_lconjaction s"
  using the_inv_signed_lconjaction signed_rconjaction_by_order2_eq_lconjaction
  by    simp

lemma signed_list_lconjaction_fst:
  "fst (signed_list_lconjaction ss x) = lconjby (sum_list ss) (fst x)"
  using signed_lconjaction_fst lconjby_add by (induct ss) auto

lemma signed_list_lconjaction_snd:
  shows "\<forall>s\<in>set ss. s+s=0 \<Longrightarrow> snd (signed_list_lconjaction ss x)
          = (if even (count_list (lconjseq (rev ss)) (fst x)) then snd x else \<not>snd x)"
proof (induct ss)
  case (Cons s ss) hence prevcase:
    "snd (signed_list_lconjaction ss x) =
      (if even (count_list (lconjseq (rev ss)) (fst x)) then snd x else \<not> snd x)"
    by simp
  have 1: "snd (signed_list_lconjaction (s # ss) x) =
            snd (signed_lconjaction s (signed_list_lconjaction ss x))"
    by simp
  show ?case
  proof (cases "fst (signed_list_lconjaction ss x) = s")
    case True
    with 1 prevcase
      have  "snd (signed_list_lconjaction (s # ss) x) =
              (if even (count_list (lconjseq (rev ss)) (fst x)) then \<not> snd x else snd x)"
      by    (simp add: signed_lconjactionD)
    with True Cons(2) show ?thesis
      by    (simp add:
              signed_list_lconjaction_fst lconjby_eq_conv_rconjby_eq
              uminus_sum_list_order2[THEN sym] lconjseq_snoc count_list_snoc
            )
  next
    case False
    hence "rconjby (sum_list ss) (lconjby (sum_list ss) (fst x)) \<noteq>
            rconjby (sum_list ss) s"
      by (simp add: signed_list_lconjaction_fst)
    with Cons(2)
      have  "count_list (lconjseq (rev (s#ss))) (fst x) =
              count_list (lconjseq (rev ss)) (fst x)"
      by    (simp add:
              rconjby_lconjby uminus_sum_list_order2[THEN sym]
              lconjseq_snoc count_list_snoc
            )
    moreover from False 1 prevcase
      have "snd (signed_list_lconjaction (s # ss) x) =
              (if even (count_list (lconjseq (rev ss)) (fst x)) then snd x else \<not> snd x)"
      by (simp add: signed_lconjactionD)
    ultimately show ?thesis by simp
  qed
qed simp

end (* context group_add *)

subsection {* Cosets *}

subsubsection {* Basic facts *}

lemma set_zero_plus' [simp]: "(0::'a::monoid_add) +o C = C"
-- {* lemma @{text "Set_Algebras.set_zero_plus"} is restricted to types of class
@{class comm_monoid_add}; here is a version in @{class monoid_add}. *}
  by (auto simp add: elt_set_plus_def)

lemma lcoset_0: "(w::'a::monoid_add) +o 0 = {w}"
  using elt_set_plus_def[of w] by simp

lemma lcoset_refl: "(0::'a::monoid_add) \<in> A \<Longrightarrow> a \<in> a +o A"
  using elt_set_plus_def by force

lemma lcoset_eq_reps_subset: 
  "(a::'a::group_add) +o A \<subseteq> a +o B \<Longrightarrow> A \<subseteq> B"
  using elt_set_plus_def[of a] by auto

lemma lcoset_eq_reps: "(a::'a::group_add) +o A = a +o B \<Longrightarrow> A = B"
  using lcoset_eq_reps_subset[of a A B] lcoset_eq_reps_subset[of a B A] by auto

lemma lcoset_inj_on: "inj (op +o (a::'a::group_add))"
  using lcoset_eq_reps inj_onI[of UNIV "op +o a"] by auto

lemma lcoset_conv_set: "(a::'g::group_add) \<in> b +o A \<Longrightarrow> -b + a \<in> A"
  by (auto simp add: elt_set_plus_def)

subsubsection {* The supset order on cosets *}

lemma supset_lbound_lcoset_shift:
  "supset_lbound_of X Y B \<Longrightarrow>
    ordering.lbound_of (op \<supseteq>) (a +o X) (a +o Y) (a +o B)"
  using ordering.lbound_of_def[OF supset_poset, of X Y B] 
  by    (fast intro: ordering.lbound_ofI supset_poset)

lemma supset_glbound_in_of_lcoset_shift:
  fixes   P :: "'a::group_add set set"
  assumes "supset_glbound_in_of P X Y B"
  shows   "supset_glbound_in_of (op +o a ` P) (a +o X) (a +o Y) (a +o B)"
  using   ordering.glbound_in_ofD_in[OF supset_poset, OF assms]
          ordering.glbound_in_ofD_lbound[OF supset_poset, OF assms]
          supset_lbound_lcoset_shift[of X Y B a]
          supset_lbound_lcoset_shift[of "a +o X" "a +o Y" _ "-a"]
          ordering.glbound_in_ofD_glbound[OF supset_poset, OF assms]
          ordering.glbound_in_ofI[
            OF supset_poset, of "a +o B" "op +o a ` P" "a +o X" "a +o Y"
          ]
  by      (fastforce simp add: set_plus_rearrange2)

subsubsection {* The afforded partition *}

definition lcoset_rel :: "'a::{uminus,plus} set \<Rightarrow> ('a\<times>'a) set"
  where "lcoset_rel A \<equiv> {(x,y). -x + y \<in> A}"

lemma lcoset_relI: "-x+y \<in> A \<Longrightarrow> (x,y) \<in> lcoset_rel A"
  using lcoset_rel_def by fast


subsection {* Groups *}

text {* We consider groups as closed sets in a type of class @{class group_add}. *}

subsubsection {* Locale definition and basic facts *}

locale    Group =
  fixes   G :: "'g::group_add set"
  assumes nonempty   : "G \<noteq> {}"
  and     diff_closed: "\<And>g h. g \<in> G \<Longrightarrow> h \<in> G \<Longrightarrow> g - h \<in> G"
begin

abbreviation Subgroup :: "'g set \<Rightarrow> bool"
  where "Subgroup H \<equiv> Group H \<and> H \<subseteq> G"

lemma SubgroupD1: "Subgroup H \<Longrightarrow> Group H" by fast

lemma zero_closed : "0 \<in> G"
proof-
  from nonempty obtain g where "g \<in> G" by fast
  hence "g - g \<in> G" using diff_closed by fast
  thus ?thesis by simp
qed

lemma uminus_closed: "g\<in>G \<Longrightarrow> -g\<in>G"
  using zero_closed diff_closed[of 0 g] by simp

lemma add_closed: "g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> g+h \<in> G"
  using uminus_closed[of h] diff_closed[of g "-h"] by simp

lemma uminus_add_closed: "g \<in> G \<Longrightarrow> h \<in> G \<Longrightarrow> -g + h \<in> G"
  using uminus_closed add_closed by fast

lemma lconjby_closed: "g\<in>G \<Longrightarrow> x\<in>G \<Longrightarrow> lconjby g x \<in> G"
  using add_closed diff_closed by fast

lemma lconjby_set_closed: "g\<in>G \<Longrightarrow> A\<subseteq>G \<Longrightarrow> lconjby g ` A \<subseteq> G"
  using lconjby_closed by fast

lemma set_lconjby_subset_closed:
  "H\<subseteq>G \<Longrightarrow> A\<subseteq>G \<Longrightarrow> (\<Union>h\<in>H. lconjby h ` A) \<subseteq> G"
  using lconjby_set_closed[of _ A] by fast

lemma sum_list_map_closed: "set (map f as) \<subseteq> G \<Longrightarrow> (\<Sum>a\<leftarrow>as. f a) \<in> G"
  using zero_closed add_closed by (induct as) auto

lemma sum_list_closed: "set as \<subseteq> G \<Longrightarrow> sum_list as \<in> G"
    using sum_list_map_closed by force

end (* context Group *)

subsubsection {* Sets with a suitable binary operation *}

text {*
  We have chosen to only consider groups in types of class @{class group_add} so that we can take
  advantage of all the algebra lemmas already proven in @{theory Groups} in HOL, as well as
  constructs like @{const sum_list}. The following locale builds a bridge between this restricted
  view of groups and the usual notion of a binary operation on a set satisfying the group axioms,
  by constructing an injective map into type @{type permutation} (which is of class
  @{class group_add} with respect to the composition operation) that respects the group operation.
  This bridge will be necessary to define quotient groups, in particular.
*}

locale BinOpSetGroup =
  fixes G     :: "'a set"
  and   binop :: "'a\<Rightarrow>'a\<Rightarrow>'a"
  and   e     :: "'a"
  assumes closed  : "g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> binop g h \<in> G"
  and     assoc   :
    "\<lbrakk> g\<in>G; h\<in>G; k\<in>G \<rbrakk> \<Longrightarrow> binop (binop g h) k = binop g (binop h k)"
  and     identity: "e\<in>G" "g\<in>G \<Longrightarrow> binop g e = g" "g\<in>G \<Longrightarrow> binop e g = g"
  and     inverses: "g\<in>G \<Longrightarrow> \<exists>h\<in>G. binop g h = e \<and> binop h g = e"
begin

lemma unique_identity1: "g\<in>G \<Longrightarrow> \<forall>x\<in>G. binop g x = x \<Longrightarrow> g = e"
  using identity(1,2) by auto

lemma unique_inverse:
  assumes "g\<in>G"
  shows   "\<exists>!h. h\<in>G \<and> binop g h = e \<and> binop h g = e"
proof (rule ex_ex1I)
  from assms show "\<exists>h. h \<in> G \<and> binop g h = e \<and> binop h g = e"
    using inverses by fast
next
  fix h k
  assume "h\<in>G \<and> binop g h = e \<and> binop h g = e" "k\<in>G \<and>
            binop g k = e \<and> binop k g = e"
  hence h: "h\<in>G" "binop g h = e" "binop h g = e"
    and k: "k\<in>G" "binop g k = e" "binop k g = e"
    by  auto
  from assms h(1,3) k(1,2) show "h=k" using identity(2,3) assoc by force
qed

abbreviation "G_perm g \<equiv> restrict1 (binop g) G"

definition Abs_G_perm :: "'a \<Rightarrow> 'a permutation"
  where "Abs_G_perm g \<equiv> Abs_permutation (G_perm g)"

abbreviation "\<pp> \<equiv> Abs_G_perm" -- {* the injection into type @{type permutation} *}
abbreviation "\<ii>\<pp> \<equiv> the_inv_into G \<pp>" -- {* the reverse correspondence *}
abbreviation "pG \<equiv> \<pp>`G" -- {* the resulting @{const Group} of type @{type permutation} *}

lemma G_perm_comp:
  "g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> G_perm g \<circ> G_perm h = G_perm (binop g h)"
  using closed by (auto simp add: assoc)

definition the_inverse :: "'a \<Rightarrow> 'a"
  where "the_inverse g \<equiv> (THE h. h\<in>G \<and> binop g h = e \<and> binop h g = e)"

abbreviation "\<ii> \<equiv> the_inverse"

lemma the_inverseD:
  assumes   "g\<in>G"
  shows     "\<ii> g \<in> G" "binop g (\<ii> g) = e" "binop (\<ii> g) g = e"
  using     assms theI'[OF unique_inverse]
  unfolding the_inverse_def
  by        auto

lemma binop_G_comp_binop_\<ii>G: "g\<in>G \<Longrightarrow> x\<in>G \<Longrightarrow> binop g (binop (\<ii> g) x) = x"
  using the_inverseD(1) assoc[of g "\<ii> g" x] by (simp add: identity(3) the_inverseD(2))

lemma bij_betw_binop_G:
  assumes   "g\<in>G"
  shows     "bij_betw (binop g) G G"
  unfolding bij_betw_def
proof
  show "inj_on (binop g) G"
  proof (rule inj_onI)
    fix h k assume hk: "h\<in>G" "k\<in>G" "binop g h = binop g k"
    with assms have "binop (binop (\<ii> g) g) h = binop (binop (\<ii> g) g) k"
      using the_inverseD(1) by (simp add: assoc)
    with assms hk(1,2) show "h=k" using the_inverseD(3) identity by simp
  qed
  show "binop g ` G = G"
  proof
    from assms show "binop g ` G \<subseteq> G" using closed by fast
    from assms show "binop g ` G \<supseteq> G"
      using binop_G_comp_binop_\<ii>G[THEN sym] the_inverseD(1) closed by fast
  qed
qed

lemma the_inv_into_G_binop_G:
  assumes "g\<in>G" "x\<in>G"
  shows   "the_inv_into G (binop g) x = binop (\<ii> g) x"
proof (rule the_inv_into_f_eq)
  from assms(1) show "inj_on (binop g) G"
    using bij_betw_imp_inj_on[OF bij_betw_binop_G] by fast
  from assms show "binop g (binop (\<ii> g) x) = x"
    using binop_G_comp_binop_\<ii>G by fast
  from assms show "binop (\<ii> g) x \<in> G" using closed the_inverseD(1) by fast
qed

lemma restrict1_the_inv_into_G_binop_G:
  "g\<in>G \<Longrightarrow> restrict1 (the_inv_into G (binop g)) G = G_perm (\<ii> g)"
  using the_inv_into_G_binop_G by auto

lemma bij_G_perm: "g\<in>G \<Longrightarrow> bij (G_perm g)"
  using set_permutation_bij_restrict1 bij_betw_binop_G by fast

lemma G_perm_apply: "g\<in>G \<Longrightarrow> x\<in>G \<Longrightarrow> \<pp> g \<rightarrow> x = binop g x"
  using Abs_G_perm_def Abs_permutation_inverse bij_G_perm by fastforce

lemma G_perm_apply_identity: "g\<in>G \<Longrightarrow> \<pp> g \<rightarrow> e = g"
  using G_perm_apply identity(1,2) by simp

lemma the_inv_G_perm:
  "g\<in>G \<Longrightarrow> the_inv (G_perm g) = G_perm (\<ii> g)"
  using set_permutation_the_inv_restrict1 bij_betw_binop_G
        restrict1_the_inv_into_G_binop_G
  by    fastforce

lemma Abs_G_perm_diff:
  "g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> \<pp> g - \<pp> h = \<pp> (binop g (\<ii> h))"
  using Abs_G_perm_def minus_permutation_abs_eq[OF bij_G_perm bij_G_perm]
        the_inv_G_perm G_perm_comp the_inverseD(1)
  by    simp

lemma Group: "Group pG"
  using identity(1) Abs_G_perm_diff the_inverseD(1) closed by unfold_locales auto

lemma inj_on_\<pp>_G: "inj_on \<pp> G"
proof (rule inj_onI)
  fix x y assume xy: "x\<in>G" "y\<in>G" "\<pp> x = \<pp> y"
  hence "Abs_permutation (G_perm (binop x (\<ii> y))) = Abs_permutation id"
    using Abs_G_perm_diff Abs_G_perm_def
    by (fastforce simp add: zero_permutation.abs_eq)
  moreover from xy(1,2) have 1: "binop x (\<ii> y) \<in> G"
    using bij_id closed the_inverseD(1) by fast
  ultimately have 2: "G_perm (binop x (\<ii> y)) = id"
    using Abs_permutation_inject[of "G_perm (binop x (\<ii> y))"] bij_G_perm bij_id
    by    simp
  have "\<forall>z\<in>G. binop (binop x (\<ii> y)) z = z"
  proof
    fix z assume "z\<in>G"
    thus "binop (binop x (\<ii> y)) z = z" using fun_cong[OF 2, of z] by simp
  qed
  with xy(1,2) have "binop x (binop (\<ii> y) y) = y"
    using unique_identity1[OF 1] the_inverseD(1) by (simp add: assoc)
  with xy(1,2) show "x = y" using the_inverseD(3) identity(2) by simp
qed

lemma homs:
  "\<And>g h. g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> \<pp> (binop g h) = \<pp> g + \<pp> h"
  "\<And>x y. x\<in>pG \<Longrightarrow> y\<in>pG \<Longrightarrow> binop (\<ii>\<pp> x) (\<ii>\<pp> y) = \<ii>\<pp> (x+y)"
proof-
  show 1: "\<And>g h. g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> \<pp> (binop g h) = \<pp> g + \<pp> h"
    using Abs_G_perm_def G_perm_comp
          plus_permutation_abs_eq[OF bij_G_perm bij_G_perm]
    by    simp
  show "\<And>x y. x\<in>pG \<Longrightarrow> y\<in>pG \<Longrightarrow> binop (\<ii>\<pp> x) (\<ii>\<pp> y) = \<ii>\<pp> (x+y)"
  proof-
    fix x y assume "x\<in>pG" "y\<in>pG"
    moreover hence "\<ii>\<pp> (\<pp> (binop (\<ii>\<pp> x) (\<ii>\<pp> y))) = \<ii>\<pp> (x + y)"
      using 1 the_inv_into_into[OF inj_on_\<pp>_G] f_the_inv_into_f[OF inj_on_\<pp>_G]
      by    simp
    ultimately show "binop (\<ii>\<pp> x) (\<ii>\<pp> y) = \<ii>\<pp> (x+y)" 
      using the_inv_into_into[OF inj_on_\<pp>_G] closed the_inv_into_f_f[OF inj_on_\<pp>_G]
      by    simp
  qed
qed

lemmas inv_correspondence_into =
  the_inv_into_into[OF inj_on_\<pp>_G, of _ G, simplified]

lemma inv_correspondence_conv_apply: "x \<in> pG \<Longrightarrow> \<ii>\<pp> x = x\<rightarrow>e"
  using G_perm_apply_identity inj_on_\<pp>_G by (auto intro: the_inv_into_f_eq)

end (* context BinOpSetGroup *)


subsubsection {* Cosets of a @{const Group} *}

context Group
begin

lemma lcoset_refl: "a \<in> a +o G"
  using lcoset_refl zero_closed by fast

lemma lcoset_el_reduce:
  assumes "a \<in> G"
  shows "a +o G = G"
proof (rule seteqI)
  fix x assume "x \<in> a +o G"
  from this obtain g where "g\<in>G" "x = a+g" using elt_set_plus_def[of a] by auto
  with assms show "x\<in>G" by (simp add: add_closed)
next
  fix x assume "x\<in>G"
  with assms have "-a + x \<in> G" by (simp add: uminus_add_closed)
  thus "x \<in> a +o G" using elt_set_plus_def by force
qed

lemma lcoset_el_reduce0: "0 \<in> a +o G \<Longrightarrow> a +o G = G"
  using elt_set_plus_def[of a G] minus_unique uminus_closed[of "-a"]
        lcoset_el_reduce
  by    fastforce

lemma lcoset_subgroup_imp_eq_reps:
  "Group H \<Longrightarrow> w +o H \<subseteq> w' +o G \<Longrightarrow> w' +o G = w +o G"
  using Group.lcoset_refl[of H w] lcoset_conv_set[of w] lcoset_el_reduce
        set_plus_rearrange2[of w' "-w'+w" G]
  by    force

lemma lcoset_closed: "a\<in>G \<Longrightarrow> A\<subseteq>G \<Longrightarrow> a +o A \<subseteq> G"
  using elt_set_plus_def[of a] add_closed by auto

lemma lcoset_rel_sym: "sym (lcoset_rel G)"
proof (rule symI)
  fix a b show "(a,b) \<in> lcoset_rel G \<Longrightarrow> (b,a) \<in> lcoset_rel G"
    using uminus_closed minus_add[of "-a" b] lcoset_rel_def[of G] by fastforce
qed

lemma lcoset_rel_trans: "trans (lcoset_rel G)"
proof (rule transI)
  fix x y z assume xy: "(x,y) \<in> lcoset_rel G" and yz: "(y,z) \<in> lcoset_rel G"
  from this obtain g g' where "g\<in>G" "-x+y = g" "g'\<in>G" "-y+z = g'"
    using lcoset_rel_def[of G] by fast
  thus "(x, z) \<in> lcoset_rel G"
    using add.assoc[of g "-y" z] add_closed lcoset_rel_def[of G] by auto
qed

abbreviation LCoset_rel :: "'g set \<Rightarrow> ('g\<times>'g) set"
  where "LCoset_rel H \<equiv> lcoset_rel H \<inter> (G\<times>G)"

lemma refl_on_LCoset_rel: "0\<in>H \<Longrightarrow> refl_on G (LCoset_rel H)"
  using lcoset_rel_def by (fastforce intro: refl_onI)

lemmas subgroup_refl_on_LCoset_rel =
  refl_on_LCoset_rel[OF Group.zero_closed, OF SubgroupD1]
lemmas LCoset_rel_quotientI        = quotientI[of _ G "LCoset_rel _"]
lemmas LCoset_rel_quotientE        = quotientE[of _ G "LCoset_rel _"]

lemma lcoset_subgroup_rel_equiv:
  "Subgroup H \<Longrightarrow> equiv G (LCoset_rel H)"
  using Group.lcoset_rel_sym sym_sym sym_Int Group.lcoset_rel_trans trans_sym
        trans_Int subgroup_refl_on_LCoset_rel
  by    (blast intro: equivI)

lemma trivial_LCoset: "H\<subseteq>G \<Longrightarrow> H = LCoset_rel H `` {0}"
  using zero_closed unfolding lcoset_rel_def by auto

end (* context Group *)

subsubsection {* The @{const Group} generated by a set *}

inductive_set genby :: "'a::group_add set \<Rightarrow> 'a set" ("\<langle>_\<rangle>")
  for S :: "'a set"
  where
      genby_0_closed     : "0\<in>\<langle>S\<rangle>"  --{* just in case @{term S} is empty *}
    | genby_genset_closed: "s\<in>S \<Longrightarrow> s\<in>\<langle>S\<rangle>"
    | genby_diff_closed  : "w\<in>\<langle>S\<rangle> \<Longrightarrow> w'\<in>\<langle>S\<rangle> \<Longrightarrow> w - w' \<in> \<langle>S\<rangle>"

lemma genby_Group: "Group \<langle>S\<rangle>"
  using genby_0_closed genby_diff_closed by unfold_locales fast

lemmas genby_uminus_closed             = Group.uminus_closed     [OF genby_Group]
lemmas genby_add_closed                = Group.add_closed        [OF genby_Group]
lemmas genby_uminus_add_closed         = Group.uminus_add_closed [OF genby_Group]
lemmas genby_lcoset_refl               = Group.lcoset_refl       [OF genby_Group]
lemmas genby_lcoset_el_reduce          = Group.lcoset_el_reduce  [OF genby_Group]
lemmas genby_lcoset_el_reduce0         = Group.lcoset_el_reduce0 [OF genby_Group]
lemmas genby_lcoset_closed             = Group.lcoset_closed     [OF genby_Group]

lemmas genby_lcoset_subgroup_imp_eq_reps =
  Group.lcoset_subgroup_imp_eq_reps[OF genby_Group, OF genby_Group]

lemma genby_genset_subset: "S \<subseteq> \<langle>S\<rangle>"
  using genby_genset_closed by fast

lemma genby_uminus_genset_subset: "uminus ` S \<subseteq> \<langle>S\<rangle>"
  using genby_genset_subset genby_uminus_closed by auto

lemma genby_in_sum_list_lists:
  fixes   S
  defines S_sum_lists: "S_sum_lists \<equiv> (\<Union>ss\<in>lists (S \<union> uminus ` S). {sum_list ss})"
  shows   "w \<in> \<langle>S\<rangle> \<Longrightarrow> w \<in> S_sum_lists"
proof (erule genby.induct)
  have "0 = sum_list []" by simp
  with S_sum_lists show "0 \<in> S_sum_lists" by blast
next
  fix s assume "s\<in>S"
  hence "[s] \<in> lists (S \<union> uminus ` S)" by simp
  moreover have "s = sum_list [s]" by simp
  ultimately show "s \<in> S_sum_lists" using S_sum_lists by blast
next
  fix w w' assume ww': "w \<in> S_sum_lists" "w' \<in> S_sum_lists"
  with S_sum_lists obtain ss ts
    where ss: "ss \<in> lists (S \<union> uminus ` S)" "w = sum_list ss"
    and   ts: "ts \<in> lists (S \<union> uminus ` S)" "w' = sum_list ts"
    by fastforce
  from ss(2) ts(2) have "w-w' = sum_list (ss @ map uminus (rev ts))"
    by (simp add: diff_conv_add_uminus uminus_sum_list)
  moreover from ss(1) ts(1)
    have  "ss @ map uminus (rev ts) \<in> lists (S \<union> uminus ` S)"
    by    fastforce
  ultimately show "w - w' \<in> S_sum_lists" using S_sum_lists by fast
qed

lemma sum_list_lists_in_genby: "ss \<in> lists (S \<union> uminus ` S) \<Longrightarrow> sum_list ss \<in> \<langle>S\<rangle>"
proof (induct ss)
  case Nil show ?case using genby_0_closed by simp
next
  case (Cons s ss) thus ?case
    using genby_genset_subset[of S] genby_uminus_genset_subset
          genby_add_closed[of s S "sum_list ss"]
    by    auto
qed

lemma sum_list_lists_in_genby_sym:
  "uminus ` S \<subseteq> S \<Longrightarrow> ss \<in> lists S \<Longrightarrow> sum_list ss \<in> \<langle>S\<rangle>"
  using sum_list_lists_in_genby by fast

lemma genby_eq_sum_lists: "\<langle>S\<rangle> = (\<Union>ss\<in>lists (S \<union> uminus ` S). {sum_list ss})"
  using genby_in_sum_list_lists sum_list_lists_in_genby by fast

lemma genby_mono: "T \<subseteq> S \<Longrightarrow> \<langle>T\<rangle> \<subseteq> \<langle>S\<rangle>"
  using genby_eq_sum_lists[of T] genby_eq_sum_lists[of S] by force

lemma (in Group) genby_closed:
  assumes "S \<subseteq> G"
  shows "\<langle>S\<rangle> \<subseteq> G"
proof
  fix x show "x \<in> \<langle>S\<rangle> \<Longrightarrow> x \<in> G"
  proof (erule genby.induct, rule zero_closed)
    from assms show "\<And>s. s\<in>S \<Longrightarrow> s\<in>G" by fast
    show "\<And>w w'. w\<in>G \<Longrightarrow> w'\<in>G \<Longrightarrow> w-w' \<in> G" using diff_closed by fast
  qed
qed

lemma (in Group) genby_subgroup: "S \<subseteq> G \<Longrightarrow> Subgroup \<langle>S\<rangle>"
  using genby_closed genby_Group by simp

lemma genby_sym_eq_sum_lists:
  "uminus ` S \<subseteq> S \<Longrightarrow> \<langle>S\<rangle> = (\<Union>ss\<in>lists S. {sum_list ss})"
  using lists_mono genby_eq_sum_lists[of S] by force

lemma genby_empty': "w \<in> \<langle>{}\<rangle> \<Longrightarrow> w = 0"
proof (erule genby.induct) qed auto

lemma genby_order2':
  assumes "s+s=0"
  shows   "w \<in> \<langle>{s}\<rangle> \<Longrightarrow> w = 0 \<or> w = s"
proof (erule genby.induct)
  fix w w' assume "w = 0 \<or> w = s" "w' = 0 \<or> w' = s"
  with assms show "w - w' = 0 \<or> w - w' = s"
    by (cases "w'=0") (auto simp add: minus_unique)
qed auto

lemma genby_order2: "s+s=0 \<Longrightarrow> \<langle>{s}\<rangle> = {0,s}"
  using genby_order2'[of s] genby_0_closed genby_genset_closed by auto

lemma genby_empty: "\<langle>{}\<rangle> = 0"
  using genby_empty' genby_0_closed by auto

lemma genby_lcoset_order2: "s+s=0 \<Longrightarrow> w +o \<langle>{s}\<rangle> = {w,w+s}"
  using elt_set_plus_def[of w] by (auto simp add: genby_order2)

lemma genby_lcoset_empty: "(w::'a::group_add) +o \<langle>{}\<rangle> = {w}"
proof-
  have "\<langle>{}::'a set\<rangle> = (0::'a set)" using genby_empty by fast
  thus ?thesis using lcoset_0 by simp
qed

lemma (in Group) genby_set_lconjby_set_lconjby_closed:
  fixes   A :: "'g set"
  defines "S \<equiv> (\<Union>g\<in>G. lconjby g ` A)"
  assumes "g\<in>G"
  shows   "x \<in> \<langle>S\<rangle> \<Longrightarrow> lconjby g x \<in> \<langle>S\<rangle>"
proof (erule genby.induct)
  show "lconjby g 0 \<in> \<langle>S\<rangle>" using genby_0_closed by simp
  from assms show "\<And>s. s \<in> S \<Longrightarrow> lconjby g s \<in> \<langle>S\<rangle>"
    using add_closed genby_genset_closed[of _ S] by (force simp add: lconjby_add)
next
  fix w w'
  assume ww': "lconjby g w \<in> \<langle>S\<rangle>" "lconjby g w' \<in> \<langle>S\<rangle>"
  have "lconjby g (w - w') = lconjby g w + lconjby g (-w')"
    by (simp add: algebra_simps)
  with ww' show "lconjby g (w - w') \<in> \<langle>S\<rangle>"
    using lconjby_uminus[of g] diff_conv_add_uminus[of _ "lconjby g w'"]
          genby_diff_closed
    by    fastforce
qed

lemma (in Group) genby_set_lconjby_set_rconjby_closed:
  fixes   A :: "'g set"
  defines "S \<equiv> (\<Union>g\<in>G. lconjby g ` A)"
  assumes "g\<in>G" "x \<in> \<langle>S\<rangle>"
  shows   "rconjby g x \<in> \<langle>S\<rangle>"
  using   assms uminus_closed genby_set_lconjby_set_lconjby_closed
  by      fastforce

subsubsection {* Homomorphisms and isomorphisms *}

locale GroupHom = Group G
  for   G :: "'g::group_add set"
+ fixes T :: "'g \<Rightarrow> 'h::group_add"
  assumes hom : "g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow> T (g + g') = T g + T g'"
  and     supp: "supp T \<subseteq> G" 
begin

lemma im_zero: "T 0 = 0"
  using zero_closed hom[of 0 0] add_diff_cancel[of "T 0" "T 0"] by simp

lemma im_uminus: "T (- g) = - T g"
  using im_zero hom[of g "- g"] uminus_closed[of g] minus_unique[of "T g"]
        uminus_closed[of "-g"] supp suppI_contra[of g T]
        suppI_contra[of "-g" T]
  by    fastforce

lemma im_uminus_add: "g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow> T (-g + g') = - T g + T g'"
  by (simp add: uminus_closed hom im_uminus)

lemma im_diff: "g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow> T (g - g') = T g - T g'"
  using hom uminus_closed hom[of g "-g'"] im_uminus by simp

lemma im_lconjby: "x \<in> G \<Longrightarrow> g \<in> G \<Longrightarrow> T (lconjby x g) = lconjby (T x) (T g)"
  using add_closed by (simp add: im_diff hom)

lemma im_sum_list_map:
  "set (map f as) \<subseteq> G \<Longrightarrow> T (\<Sum>a\<leftarrow>as. f a) = (\<Sum>a\<leftarrow>as. T (f a))"
  using hom im_zero sum_list_closed by (induct as) auto

lemma comp:
  assumes "GroupHom H S" "T`G \<subseteq> H" 
  shows   "GroupHom G (S \<circ> T)"
proof
  fix g g' assume "g \<in> G" "g' \<in> G"
  with hom assms(2) show "(S \<circ> T) (g + g') = (S \<circ> T) g + (S \<circ> T) g'"
    using GroupHom.hom[OF assms(1)] by fastforce
next
  from supp have "\<And>g. g \<notin> G \<Longrightarrow> (S \<circ> T) g = 0"
    using suppI_contra GroupHom.im_zero[OF assms(1)] by fastforce
  thus "supp (S \<circ> T) \<subseteq> G" using suppD_contra by fast
qed

end (* context GroupHom *)


definition ker :: "('a\<Rightarrow>'b::zero) \<Rightarrow> 'a set"
  where "ker f = {a. f a = 0}"

lemma ker_subset_ker_restrict0: "ker f \<subseteq> ker (restrict0 f A)"
  unfolding ker_def by auto

context GroupHom
begin

abbreviation "Ker \<equiv> ker T \<inter> G"

lemma uminus_add_in_Ker_eq_eq_im:
  "g\<in>G \<Longrightarrow> h\<in>G \<Longrightarrow> (-g + h \<in> Ker) = (T g = T h)"
  using neg_equal_iff_equal
  by    (simp add: uminus_add_closed ker_def im_uminus_add eq_neg_iff_add_eq_0)

end (* context GroupHom *)

locale UGroupHom = GroupHom UNIV T
  for T :: "'g::group_add \<Rightarrow> 'h::group_add"
begin

lemmas im_zero       = im_zero
lemmas im_uminus     = im_uminus

lemma hom: "T (g+g') = T g + T g'"
  using hom by simp

lemma im_diff: "T (g - g') = T g - T g'"
  using im_diff by simp

lemma im_lconjby: "T (lconjby x g) = lconjby (T x) (T g)"
  using im_lconjby by simp

lemma restrict0:
  assumes "Group G"
  shows   "GroupHom G (restrict0 T G)"
proof (intro_locales, rule assms, unfold_locales)
  from hom 
    show  "\<And>g g'. g \<in> G \<Longrightarrow> g' \<in> G \<Longrightarrow>
            restrict0 T G (g + g') = restrict0 T G g + restrict0 T G g'"
    using Group.add_closed[OF assms]
    by    auto
  show "supp (restrict0 T G) \<subseteq> G" using supp_restrict0[of G T] by fast
qed

end (* context UGroupHom *)

lemma UGroupHomI:
  assumes "\<And>g g'. T (g + g') = T g + T g'"
  shows   "UGroupHom T"
  using   assms
  by      unfold_locales auto

locale GroupIso = GroupHom G T
  for   G :: "'g::group_add set"
  and   T :: "'g \<Rightarrow> 'h::group_add"
+ assumes inj_on: "inj_on T G"

lemma (in GroupHom) isoI:
  assumes "\<And>k. k\<in>G \<Longrightarrow> T k = 0 \<Longrightarrow> k=0"
  shows   "GroupIso G T"
proof (unfold_locales, rule inj_onI)
  fix x y from assms show "\<lbrakk> x\<in>G; y\<in>G; T x = T y \<rbrakk> \<Longrightarrow> x = y"
    using im_diff diff_closed by force
qed

text {*
  In a @{const BinOpSetGroup}, any map from the set into a type of class @{class group_add} that respects the
  binary operation induces a @{const GroupHom}.
*}

abbreviation (in BinOpSetGroup) "lift_hom T \<equiv> restrict0 (T \<circ> \<ii>\<pp>) pG"

lemma (in BinOpSetGroup) lift_hom:
  fixes T :: "'a \<Rightarrow> 'b::group_add"
  assumes "\<forall>g\<in>G. \<forall>h\<in>G. T (binop g h) = T g + T h"
  shows   "GroupHom pG (lift_hom T)"
proof (intro_locales, rule Group, unfold_locales)
  from assms
    show  "\<And>x y. x\<in>pG \<Longrightarrow> y\<in>pG \<Longrightarrow>
            lift_hom T (x+y) = lift_hom T x + lift_hom T y"
    using Group.add_closed[OF Group] inv_correspondence_into
    by    (simp add: homs(2)[THEN sym])
qed (rule supp_restrict0)




subsubsection {* Normal subgroups *}

definition rcoset_rel :: "'a::{minus,plus} set \<Rightarrow> ('a\<times>'a) set"
  where "rcoset_rel A \<equiv> {(x,y). x-y \<in> A}"

context Group
begin

lemma rcoset_rel_conv_lcoset_rel:
  "rcoset_rel G = map_prod uminus uminus ` (lcoset_rel G)"
proof (rule set_eqI)
  fix x :: "'g\<times>'g"
  obtain a b where ab: "x=(a,b)" by fastforce
  hence "(x \<in> rcoset_rel G) = (a-b \<in> G)"  using rcoset_rel_def by auto
  also have "\<dots> = ( (-b,-a) \<in> lcoset_rel G )"
    using uminus_closed lcoset_rel_def by fastforce
  finally
    show  "(x \<in> rcoset_rel G) = (x \<in> map_prod uminus uminus ` (lcoset_rel G))"
    using ab symD[OF lcoset_rel_sym] map_prod_def
    by    force
qed

lemma rcoset_rel_sym: "sym (rcoset_rel G)"
  using rcoset_rel_conv_lcoset_rel map_prod_sym lcoset_rel_sym by simp

abbreviation RCoset_rel :: "'g set \<Rightarrow> ('g\<times>'g) set"
  where "RCoset_rel H \<equiv> rcoset_rel H \<inter> (G\<times>G)"

definition normal :: "'g set \<Rightarrow> bool"
  where "normal H \<equiv> (\<forall>g\<in>G. LCoset_rel H `` {g} = RCoset_rel H `` {g})"

lemma normalI:
  assumes   "Group H" "\<forall>g\<in>G. \<forall>h\<in>H. \<exists>h'\<in>H. g+h = h'+g"
            "\<forall>g\<in>G. \<forall>h\<in>H. \<exists>h'\<in>H. h+g = g+h'"
  shows     "normal H"
  unfolding normal_def
proof
  fix g assume g: "g\<in>G"
  show "LCoset_rel H `` {g} = RCoset_rel H `` {g}"
  proof (rule seteqI)
    fix x assume "x \<in> LCoset_rel H `` {g}"
    with g have x: "x\<in>G" "-g+x \<in> H" unfolding lcoset_rel_def by auto
    from g x(2) assms(2) obtain h where h: "h\<in>H" "g-x = -h"
    by   (fastforce simp add: algebra_simps)
    with assms(1) g x(1) show "x \<in> RCoset_rel H `` {g}"
      using Group.uminus_closed unfolding rcoset_rel_def by simp
  next
    fix x assume "x \<in> RCoset_rel H `` {g}"
    with g have x: "x\<in>G" "g-x \<in> H" unfolding rcoset_rel_def by auto
    with assms(3) obtain h where h: "h\<in>H" "-g+x = -h"
      by (fastforce simp add: algebra_simps minus_add)
    with assms(1) g x(1) show "x \<in> LCoset_rel H `` {g}"
      using Group.uminus_closed unfolding lcoset_rel_def by simp
  qed
qed

lemma normal_lconjby_closed:
  "\<lbrakk> Subgroup H; normal H; g\<in>G; h\<in>H \<rbrakk> \<Longrightarrow> lconjby g h \<in> H"
  using lcoset_relI[of g "g+h" H] add_closed[of g h] normal_def[of H]
        symD[OF Group.rcoset_rel_sym, of H g "g+h"] rcoset_rel_def[of H]
  by    auto

lemma normal_rconjby_closed:
  "\<lbrakk> Subgroup H; normal H; g\<in>G; h\<in>H \<rbrakk> \<Longrightarrow> rconjby g h \<in> H"
  using normal_lconjby_closed[of H "-g" h] uminus_closed[of g] by auto

abbreviation "normal_closure A \<equiv> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>"

lemma (in Group) normal_closure:
  assumes "A\<subseteq>G"
  shows   "normal (normal_closure A)"
proof (rule normalI, rule genby_Group)
  show "\<forall>x\<in>G. \<forall>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>.
        \<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + h = h' + x"
  proof
    fix x assume x: "x\<in>G"
    show "\<forall>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>.
          \<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + h = h' + x"
    proof (rule ballI, erule genby.induct)
      show "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + 0 = h + x"
        using genby_0_closed by force
    next
      fix s assume "s \<in> (\<Union>g\<in>G. lconjby g ` A)"
      from this obtain g a where ga: "g\<in>G" "a\<in>A" "s = lconjby g a" by fast
      from ga(3) have "x + s = lconjby x (lconjby g a) + x"
        by (simp add: algebra_simps)
      hence "x + s = lconjby (x+g) a + x" by (simp add: lconjby_add)
      with x ga(1,2) show "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + s = h + x"
        using add_closed by (blast intro: genby_genset_closed)
    next
      fix w w'
      assume w :  "w \<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>"
                  "\<exists>h \<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + w  = h + x"
        and  w':  "w'\<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>"
                  "\<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + w' = h'+ x"
      from w(2) w'(2) obtain h h'
        where h : "h \<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>" "x + w  = h + x"
        and   h': "h'\<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>" "x + w' = h'+ x"
        by    fast
      have "x + (w - w') = x + w - (-x + (x + w'))"
        by (simp add: algebra_simps)
      also from h(2) h'(2) have "\<dots> = h + x + (-(h' + x) + x)"
        by (simp add: algebra_simps)
      also have "\<dots> = h + x + (-x + -h') + x"
        by (simp add: minus_add add.assoc)
      finally have "x + (w-w') = h - h' + x"
        using add.assoc[of "h+x" "-x" "-h'"] by simp
      with h(1) h'(1)
        show  "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. x + (w - w') = h + x"
        using genby_diff_closed
        by    fast
    qed
  qed
  show "\<forall>x\<in>G. \<forall>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>.
        \<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. h + x = x + h'"
  proof
    fix x assume x: "x\<in>G"
    show "\<forall>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>.
            \<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. h + x = x + h'"
    proof (rule ballI, erule genby.induct)
      show "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. 0 + x = x + h"
        using genby_0_closed by force
    next
      fix s assume "s \<in> (\<Union>g\<in>G. lconjby g ` A)"
      from this obtain g a where ga: "g\<in>G" "a\<in>A" "s = lconjby g a" by fast
      from ga(3) have "s + x = x + (((-x + g) + a) + -g) + x"
        by (simp add: algebra_simps)
      also have "\<dots> = x + (-x + g + a + -g + x)" by (simp add: add.assoc)
      finally have "s + x = x + lconjby (-x+g) a"
        by (simp add: algebra_simps lconjby_add)
      with x ga(1,2) show "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. s + x = x + h"
        using uminus_add_closed by (blast intro: genby_genset_closed)
    next
      fix w w'
      assume w :  "w \<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>"
                  "\<exists>h \<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. w  + x = x + h"
        and  w':  "w'\<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>"
                  "\<exists>h'\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. w' + x = x + h'"
      from w(2) w'(2) obtain h h'
        where h : "h \<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>" "w + x = x + h"
        and   h': "h'\<in> \<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>" "w' + x = x + h'"
        by    fast
      have "w - w' + x = w + x + (-x + -w') + x" by (simp add: algebra_simps)
      also from h(2) h'(2) have "\<dots> = x + h + (-h'+-x) + x" 
        using minus_add[of w' x] minus_add[of x h'] by simp
      finally have "w - w' + x = x + (h - h')" by (simp add: algebra_simps)
      with h(1) h'(1) show "\<exists>h\<in>\<langle>\<Union>g\<in>G. lconjby g ` A\<rangle>. w - w' + x = x + h"
        using genby_diff_closed by fast
    qed
  qed
qed 

end (* context Group *)

subsubsection {* Quotient groups *}

text {*
  Here we use the bridge built by @{const BinOpSetGroup} to make the quotient of a @{const Group}
  by a normal subgroup into a @{const Group} itself.
*}

context Group
begin

lemma normal_quotient_add_well_defined:
  assumes "Subgroup H" "normal H" "g\<in>G" "g'\<in>G"
  shows   "LCoset_rel H `` {g} + LCoset_rel H `` {g'} = LCoset_rel H `` {g+g'}"
proof (rule seteqI)
  fix x assume "x \<in> LCoset_rel H `` {g} + LCoset_rel H `` {g'}"
  from this obtain y z
    where     "y \<in> LCoset_rel H `` {g}" "z \<in> LCoset_rel H `` {g'}" "x = y+z"
    unfolding set_plus_def
    by        fast
  with assms show "x \<in> LCoset_rel H `` {g + g'}"
    using lcoset_rel_def[of H] normal_lconjby_closed[of H g' "-g'+z"]
          Group.add_closed
          normal_rconjby_closed[of H g' "-g + y + (z - g')"]
          add.assoc[of "-g'" "-g"]
          add_closed lcoset_relI[of "g+g'" "y+z"]
    by    (fastforce simp add: add.assoc minus_add)
next
  fix x assume "x \<in> LCoset_rel H `` {g + g'}"
  moreover define h where "h \<equiv> -(g+g') + x"
  moreover hence "x = g + (g' + h)"
    using add.assoc[of "-g'" "-g" x] by (simp add: add.assoc minus_add)
  ultimately show "x \<in> LCoset_rel H `` {g} + LCoset_rel H `` {g'}"
    using assms(1,3,4) lcoset_rel_def[of H] add_closed
          refl_onD[OF subgroup_refl_on_LCoset_rel, of H]
    by    force
qed

abbreviation "quotient_set H \<equiv> G // LCoset_rel H"

lemma BinOpSetGroup_normal_quotient:
  assumes "Subgroup H" "normal H"
  shows   "BinOpSetGroup (quotient_set H) (op +) H"
proof
  from assms(1) have H0: "H = LCoset_rel H `` {0}"
    using trivial_LCoset by auto

  from assms(1) show "H \<in> quotient_set H"
    using H0 zero_closed LCoset_rel_quotientI[of 0 H] by simp

  fix x assume "x \<in> quotient_set H"
  from this obtain gx where gx: "gx\<in>G" "x = LCoset_rel H `` {gx}"
    by (fast elim: LCoset_rel_quotientE)
  with assms(1,2) show "x+H = x" "H+x = x"
    using normal_quotient_add_well_defined[of H gx 0]
          normal_quotient_add_well_defined[of H 0 gx]
          H0 zero_closed
    by    auto

  from gx(1) have "LCoset_rel H `` {-gx} \<in> quotient_set H"
    using uminus_closed by (fast intro: LCoset_rel_quotientI)
  moreover from assms(1,2) gx
    have  "x + LCoset_rel H `` {-gx} = H" "LCoset_rel H `` {-gx} + x = H"
    using H0 uminus_closed normal_quotient_add_well_defined
    by    auto
  ultimately show "\<exists>x'\<in>quotient_set H. x + x' = H \<and> x' + x = H" by fast

  fix y assume "y \<in> quotient_set H"
  from this obtain gy where gy: "gy\<in>G" "y = LCoset_rel H `` {gy}"
    by (fast elim: LCoset_rel_quotientE)
  with assms gx show "x+y \<in> quotient_set H"
    using add_closed normal_quotient_add_well_defined
    by    (auto intro: LCoset_rel_quotientI)

qed (rule add.assoc)

abbreviation "abs_lcoset_perm H \<equiv>
                BinOpSetGroup.Abs_G_perm (quotient_set H) (op +)"
abbreviation "abs_lcoset_perm_lift H g \<equiv> abs_lcoset_perm H (LCoset_rel H `` {g})"
abbreviation "abs_lcoset_perm_lift_arg_permutation g H \<equiv> abs_lcoset_perm_lift H g"

notation abs_lcoset_perm_lift_arg_permutation ("\<lceil>_|_\<rceil>" [51,51] 50)

end (* context Group *)

abbreviation "Group_abs_lcoset_perm_lift_arg_permutation G' g H \<equiv>
  Group.abs_lcoset_perm_lift_arg_permutation G' g H"
notation Group_abs_lcoset_perm_lift_arg_permutation ("\<lceil>_|_|_\<rceil>" [51,51,51] 50)

context Group
begin

lemmas lcoset_perm_def =
  BinOpSetGroup.Abs_G_perm_def[OF BinOpSetGroup_normal_quotient]
lemmas lcoset_perm_comp =
  BinOpSetGroup.G_perm_comp[OF BinOpSetGroup_normal_quotient]
lemmas bij_lcoset_perm =
  BinOpSetGroup.bij_G_perm[OF BinOpSetGroup_normal_quotient]

lemma trivial_lcoset_perm:
  assumes "Subgroup H" "normal H" "h\<in>H"
  shows   "restrict1 (op + (LCoset_rel H `` {h})) (quotient_set H) = id"
proof (rule ext, simp, rule impI)
  fix x assume x: "x \<in> quotient_set H"
  then obtain k where k: "k\<in>G" "x = LCoset_rel H `` {k}"
    by (blast elim: LCoset_rel_quotientE)
  with x have "LCoset_rel H `` {h} + x = LCoset_rel H `` {h+k}"
    using assms normal_quotient_add_well_defined by auto
  with assms k show "LCoset_rel H `` {h} + x = x"
    using add_closed[of h k] lcoset_relI[of k "h+k" H]
          normal_rconjby_closed[of H k h]
          eq_equiv_class_iff[OF lcoset_subgroup_rel_equiv, of H]
    by    (auto simp add: add.assoc)
qed

definition quotient_group :: "'g set \<Rightarrow> 'g set permutation set" where
  "quotient_group H \<equiv> BinOpSetGroup.pG (quotient_set H) (op +)"

abbreviation "natural_quotient_hom H \<equiv> restrict0 (\<lambda>g. \<lceil>g|H\<rceil>) G"

theorem quotient_group:
  "Subgroup H \<Longrightarrow> normal H \<Longrightarrow> Group (quotient_group H)"
  unfolding quotient_group_def
  using     BinOpSetGroup.Group[OF BinOpSetGroup_normal_quotient]
  by        auto

lemma natural_quotient_hom:
  "Subgroup H \<Longrightarrow> normal H \<Longrightarrow> GroupHom G (natural_quotient_hom H)"
  using add_closed bij_lcoset_perm lcoset_perm_def supp_restrict0
        normal_quotient_add_well_defined[THEN sym]
        LCoset_rel_quotientI[of _ H]
  by    unfold_locales
        (force simp add: lcoset_perm_comp plus_permutation_abs_eq)

lemma natural_quotient_hom_image:
  "natural_quotient_hom H ` G = quotient_group H"
  unfolding quotient_group_def
  by        (force elim: LCoset_rel_quotientE intro: LCoset_rel_quotientI) 

lemma quotient_group_UN: "quotient_group H = (\<lambda>g. \<lceil>g|H\<rceil>) ` G"
  using natural_quotient_hom_image by auto

lemma quotient_identity_rule: "\<lbrakk> Subgroup H; normal H; h\<in>H \<rbrakk> \<Longrightarrow> \<lceil>h|H\<rceil> = 0"
  using lcoset_perm_def
  by    (simp add: trivial_lcoset_perm zero_permutation.abs_eq)
  
lemma quotient_group_lift_to_quotient_set:
  "\<lbrakk> Subgroup H; normal H; g\<in>G \<rbrakk> \<Longrightarrow> (\<lceil>g|H\<rceil>) \<rightarrow> H = LCoset_rel H `` {g}"
  using LCoset_rel_quotientI
        BinOpSetGroup.G_perm_apply_identity[
          OF BinOpSetGroup_normal_quotient
        ]
  by    simp

end (* context Group *)

subsubsection {* The induced homomorphism on a quotient group *}

text {*
  A normal subgroup contained in the kernel of a homomorphism gives rise to a homomorphism on the
  quotient group by that subgroup. When the subgroup is the kernel itself (which is always normal),
  we obtain an isomorphism on the quotient.
*}

context GroupHom
begin

lemma respects_Ker_lcosets: "H \<subseteq> Ker \<Longrightarrow> T respects (LCoset_rel H)"
  using     uminus_add_in_Ker_eq_eq_im
  unfolding lcoset_rel_def
  by        (blast intro: congruentI)

abbreviation "quotient_hom H \<equiv>
  BinOpSetGroup.lift_hom (quotient_set H) (op +) (quotientfun T)"

lemmas normal_subgroup_quotientfun_classrep_equality =
  quotientfun_classrep_equality[
    OF subgroup_refl_on_LCoset_rel, OF _ respects_Ker_lcosets
  ]

lemma quotient_hom_im:
  "\<lbrakk> Subgroup H; normal H; H \<subseteq> Ker; g\<in>G \<rbrakk> \<Longrightarrow> quotient_hom H (\<lceil>g|H\<rceil>) = T g"
  using quotient_group_def quotient_group_UN quotient_group_lift_to_quotient_set
        BinOpSetGroup.inv_correspondence_conv_apply[
          OF BinOpSetGroup_normal_quotient
        ]
        normal_subgroup_quotientfun_classrep_equality
  by    auto

lemma quotient_hom:
  assumes "Subgroup H" "normal H" "H \<subseteq> Ker"
  shows   "GroupHom (quotient_group H) (quotient_hom H)"
  unfolding quotient_group_def
proof (
  rule BinOpSetGroup.lift_hom, rule BinOpSetGroup_normal_quotient, rule assms(1),
  rule assms(2)
)
  from assms
    show  "\<forall>x \<in> quotient_set H. \<forall>y \<in> quotient_set H.
            quotientfun T (x + y) = quotientfun T x + quotientfun T y"
    using normal_quotient_add_well_defined normal_subgroup_quotientfun_classrep_equality
          add_closed hom
    by    (fastforce elim: LCoset_rel_quotientE)
qed

end (* context GroupHom *)


subsection {* Free groups *}

subsubsection {* Words in letters of @{type signed} type *}

paragraph {* Definitions and basic fact *}

text {*
  We pair elements of some type with type @{typ bool}, where the @{typ bool} part of the pair
  indicates inversion.
*}

abbreviation "pairtrue  \<equiv> \<lambda>s. (s,True)"
abbreviation "pairfalse \<equiv> \<lambda>s. (s,False)"

abbreviation flip_signed :: "'a signed \<Rightarrow> 'a signed"
  where "flip_signed \<equiv> apsnd (\<lambda>b. \<not>b)"

abbreviation nflipped_signed :: "'a signed \<Rightarrow> 'a signed \<Rightarrow> bool"
  where "nflipped_signed x y \<equiv> y \<noteq> flip_signed x"

lemma flip_signed_order2: "flip_signed (flip_signed x) = x"
  using apsnd_conv[of "\<lambda>b. \<not>b" "fst x" "snd x"] by simp

abbreviation charpair :: "'a::uminus set \<Rightarrow> 'a \<Rightarrow> 'a signed"
  where "charpair S s \<equiv> if s\<in>S then (s,True) else (-s,False)"

lemma map_charpair_uniform:
  "ss\<in>lists S \<Longrightarrow> map (charpair S) ss = map pairtrue ss"
  by (induct ss) auto

lemma fst_set_map_charpair_un_uminus:
  fixes ss :: "'a::group_add list"
  shows "ss\<in>lists (S \<union> uminus ` S) \<Longrightarrow> fst ` set (map (charpair S) ss) \<subseteq> S"
  by (induct ss) auto

abbreviation apply_sign :: "('a\<Rightarrow>'b::uminus) \<Rightarrow> 'a signed \<Rightarrow> 'b"
  where "apply_sign f x \<equiv> (if snd x then f (fst x) else - f (fst x))"

text {* 
  A word in such pairs will be considered proper if it does not contain consecutive letters that
  have opposite signs (and so are considered inverse), since such consecutive letters would be
  cancelled in a group.
*}

abbreviation proper_signed_list :: "'a signed list \<Rightarrow> bool"
  where "proper_signed_list \<equiv> binrelchain nflipped_signed"

lemma proper_map_flip_signed:
  "proper_signed_list xs \<Longrightarrow> proper_signed_list (map flip_signed xs)"
  by (induct xs rule: list_induct_CCons) auto

lemma proper_rev_map_flip_signed:
  "proper_signed_list xs \<Longrightarrow> proper_signed_list (rev (map flip_signed xs))"
  using proper_map_flip_signed binrelchain_sym_rev[of nflipped_signed] by fastforce

lemma uniform_snd_imp_proper_signed_list:
  "snd ` set xs \<subseteq> {b} \<Longrightarrow> proper_signed_list xs"
proof (induct xs rule: list_induct_CCons)
  case CCons thus ?case by force
qed auto

lemma proper_signed_list_map_uniform_snd:
  "proper_signed_list (map (\<lambda>s. (s,b)) as)"
  using uniform_snd_imp_proper_signed_list[of _ b] by force

paragraph {* Algebra *}

text {* 
  Addition is performed by appending words and recursively removing any newly created adjacent
  pairs of inverse letters. Since we will only ever be adding proper words, we only need to care
  about newly created adjacent inverse pairs in the middle.
*}

function prappend_signed_list :: "'a signed list \<Rightarrow> 'a signed list \<Rightarrow> 'a signed list"
  where "prappend_signed_list xs [] = xs"
      | "prappend_signed_list [] ys = ys"
      | "prappend_signed_list (xs@[x]) (y#ys) = (
          if y = flip_signed x then prappend_signed_list xs ys else xs @ x # y # ys
        )"
  by (auto, rule two_prod_lists_cases_snoc_Cons)
  termination by (relation "measure (\<lambda>(xs,ys). length xs + length ys)") auto

lemma proper_prappend_signed_list:
  "proper_signed_list xs \<Longrightarrow> proper_signed_list ys
    \<Longrightarrow> proper_signed_list (prappend_signed_list xs ys)"
proof (induct xs ys rule: list_induct2_snoc_Cons)
  case (snoc_Cons xs x y ys)
  show ?case
  proof (cases "y = flip_signed x")
    case True with snoc_Cons show ?thesis
      using binrelchain_append_reduce1[of nflipped_signed]
            binrelchain_Cons_reduce[of nflipped_signed y]
      by    auto
  next
    case False with snoc_Cons(2,3) show ?thesis
      using binrelchain_join[of nflipped_signed] by simp
  qed
qed auto

lemma fully_prappend_signed_list:
  "prappend_signed_list (rev (map flip_signed xs)) xs = []"
  by (induct xs) auto

lemma prappend_signed_list_single_Cons:
  "prappend_signed_list [x] (y#ys) = (if y = flip_signed x then ys else x#y#ys)"
  using prappend_signed_list.simps(3)[of "[]" x] by simp

lemma prappend_signed_list_map_uniform_snd:
  "prappend_signed_list (map (\<lambda>s. (s,b)) xs) (map (\<lambda>s. (s,b)) ys) =
    map (\<lambda>s. (s,b)) xs @ map (\<lambda>s. (s,b)) ys"
  by (cases xs ys rule: two_lists_cases_snoc_Cons) auto

lemma prappend_signed_list_assoc_conv_snoc2Cons:
  assumes "proper_signed_list (xs@[y])" "proper_signed_list (y#ys)"
  shows   "prappend_signed_list (xs@[y]) ys = prappend_signed_list xs (y#ys)"
proof (cases xs ys rule: two_lists_cases_snoc_Cons')
  case Nil1 with assms(2) show ?thesis
    by (simp add: prappend_signed_list_single_Cons)
next
  case Nil2 with assms(1) show ?thesis
    using binrelchain_append_reduce2 by force
next
  case (snoc_Cons as a b bs)
  with assms show ?thesis 
    using prappend_signed_list.simps(3)[of "as@[a]"]
          binrelchain_append_reduce2[of nflipped_signed as "[a,y]"]
    by    simp
qed simp

lemma prappend_signed_list_assoc:
  "\<lbrakk> proper_signed_list xs; proper_signed_list ys; proper_signed_list zs \<rbrakk> \<Longrightarrow>
    prappend_signed_list (prappend_signed_list xs ys) zs =
      prappend_signed_list xs (prappend_signed_list ys zs)"
proof (induct xs ys zs rule: list_induct3_snoc_Conssnoc_Cons_pairwise)
  case (snoc_single_Cons xs x y z zs)
  thus ?case
    using prappend_signed_list.simps(3)[of "[]" y]
          prappend_signed_list.simps(3)[of "xs@[x]"]
    by    (cases "y = flip_signed x" "z = flip_signed y" rule: two_cases)
          (auto simp add:
            flip_signed_order2 prappend_signed_list_assoc_conv_snoc2Cons
          )
next
  case (snoc_Conssnoc_Cons xs x y ys w z zs)
  thus ?case
    using binrelchain_Cons_reduce[of nflipped_signed y "ys@[w]"]
          binrelchain_Cons_reduce[of nflipped_signed z zs]
          binrelchain_append_reduce1[of nflipped_signed xs]
          binrelchain_append_reduce1[of nflipped_signed "y#ys"]
          binrelchain_Conssnoc_reduce[of nflipped_signed y ys]
          prappend_signed_list.simps(3)[of "y#ys"]
          prappend_signed_list.simps(3)[of "xs@x#y#ys"]
    by    (cases "y = flip_signed x" "z = flip_signed w" rule: two_cases) auto
qed auto

lemma fst_set_prappend_signed_list:
  "fst ` set (prappend_signed_list xs ys) \<subseteq> fst ` (set xs \<union> set ys)"
  by (induct xs ys rule: list_induct2_snoc_Cons) auto

lemma collapse_flipped_signed:
  "prappend_signed_list [(s,b)] [(s,\<not>b)] = []"
  using prappend_signed_list.simps(3)[of "[]" "(s,b)"] by simp



subsubsection {* The collection of proper signed lists as a type *}

text {*
  Here we create a type out of the collection of proper signed lists. This type will be of class
  @{class group_add}, with the empty list as zero, the modified append operation
  @{const prappend_signed_list} as addition, and inversion performed by flipping the signs of the
  elements in the list and then reversing the order.
*}

paragraph {* Type definition, instantiations, and instances *}

text {* Here we define the type and instantiate it with respect to various type classes. *}

typedef 'a freeword = "{as::'a signed list. proper_signed_list as}"
  morphisms freeword Abs_freeword
  using binrelchain.simps(1) by fast

text {*
  These two functions act as the natural injections of letters and words in the letter type into
  the @{type freeword} type.
*}

abbreviation Abs_freeletter :: "'a \<Rightarrow> 'a freeword"
  where "Abs_freeletter s \<equiv> Abs_freeword [pairtrue s]"

abbreviation Abs_freelist :: "'a list \<Rightarrow> 'a freeword"
  where "Abs_freelist as \<equiv> Abs_freeword (map pairtrue as)"

abbreviation Abs_freelistfst :: "'a signed list \<Rightarrow> 'a freeword"
  where "Abs_freelistfst xs \<equiv> Abs_freelist (map fst xs)"

setup_lifting type_definition_freeword

instantiation freeword :: (type) zero
begin
lift_definition zero_freeword :: "'a freeword" is "[]::'a signed list" by simp
instance ..
end

instantiation freeword :: (type) plus
begin
lift_definition plus_freeword :: "'a freeword \<Rightarrow> 'a freeword \<Rightarrow> 'a freeword"
  is    "prappend_signed_list"
  using proper_prappend_signed_list
  by    fast
instance ..
end

instantiation freeword :: (type) uminus
begin
lift_definition uminus_freeword :: "'a freeword \<Rightarrow> 'a freeword"
  is "\<lambda>xs. rev (map flip_signed xs)"
  by (rule proper_rev_map_flip_signed)
instance ..
end

instantiation freeword :: (type) minus
begin
lift_definition minus_freeword :: "'a freeword \<Rightarrow> 'a freeword \<Rightarrow> 'a freeword"
  is "\<lambda>xs ys. prappend_signed_list xs (rev (map flip_signed ys))"
  using proper_rev_map_flip_signed proper_prappend_signed_list by fast
instance ..
end

instance freeword :: (type) semigroup_add
proof
  fix a b c :: "'a freeword" show "a + b + c = a + (b + c)"
    using prappend_signed_list_assoc[of "freeword a" "freeword b" "freeword c"]
    by    transfer simp
qed

instance freeword :: (type) monoid_add
proof
  fix a b c :: "'a freeword"
  show "0 + a = a" by transfer simp
  show "a + 0 = a" by transfer simp
qed

instance freeword :: (type) group_add
proof
  fix a b :: "'a freeword"
  show "- a + a = 0"
    using fully_prappend_signed_list[of "freeword a"] by transfer simp
  show "a + - b = a - b" by transfer simp
qed

paragraph {* Basic algebra and transfer facts in the @{type freeword} type *}

text {*
  Here we record basic algebraic manipulations for the @{type freeword} type as well as various
  transfer facts for dealing with representations of elements of @{type freeword} type as lists of
  signed letters.
*}

abbreviation Abs_freeletter_add :: "'a \<Rightarrow> 'a \<Rightarrow> 'a freeword" (infixl "[+]" 65)
  where "s [+] t \<equiv> Abs_freeletter s + Abs_freeletter t"

lemma Abs_freeword_Cons:
  assumes "proper_signed_list (x#xs)"
  shows "Abs_freeword (x#xs) = Abs_freeword [x] + Abs_freeword xs"
proof (cases xs)
  case Nil thus ?thesis
    using add_0_right[of "Abs_freeword [x]"] by (simp add: zero_freeword.abs_eq)
next
  case (Cons y ys) 
  with assms
    have  "freeword (Abs_freeword (x#xs)) =
            freeword (Abs_freeword [x] + Abs_freeword xs)"
    by    (simp add:
            plus_freeword.rep_eq Abs_freeword_inverse
            prappend_signed_list_single_Cons
          )
  thus ?thesis using freeword_inject by fast
qed

lemma Abs_freelist_Cons: "Abs_freelist (x#xs) = Abs_freeletter x + Abs_freelist xs"
  using proper_signed_list_map_uniform_snd[of True "x#xs"] Abs_freeword_Cons
  by    simp

lemma plus_freeword_abs_eq:
  "proper_signed_list xs \<Longrightarrow> proper_signed_list ys \<Longrightarrow>
    Abs_freeword xs + Abs_freeword ys = Abs_freeword (prappend_signed_list xs ys)"
  using plus_freeword.abs_eq unfolding eq_onp_def by simp

lemma Abs_freeletter_add: "s [+] t = Abs_freelist [s,t]"
  using Abs_freelist_Cons[of s "[t]"] by simp

lemma uminus_freeword_Abs_eq:
  "proper_signed_list xs \<Longrightarrow>
    - Abs_freeword xs = Abs_freeword (rev (map flip_signed xs))"
  using uminus_freeword.abs_eq unfolding eq_onp_def by simp

lemma uminus_Abs_freeword_singleton:
  "- Abs_freeword [(s,b)] = Abs_freeword [(s,\<not> b)]"
  using uminus_freeword_Abs_eq[of "[(s,b)]"] by simp

lemma Abs_freeword_append_uniform_snd:
  "Abs_freeword (map (\<lambda>s. (s,b)) (xs@ys)) =
    Abs_freeword (map (\<lambda>s. (s,b)) xs) + Abs_freeword (map (\<lambda>s. (s,b)) ys)"
  using proper_signed_list_map_uniform_snd[of b xs]
        proper_signed_list_map_uniform_snd[of b ys]
        plus_freeword_abs_eq prappend_signed_list_map_uniform_snd[of b xs ys]
  by    force

lemmas Abs_freelist_append = Abs_freeword_append_uniform_snd[of True]

lemma Abs_freelist_append_append:
  "Abs_freelist (xs@ys@zs) = Abs_freelist xs + Abs_freelist ys + Abs_freelist zs"
  using Abs_freelist_append[of "xs@ys"] Abs_freelist_append by simp

lemma Abs_freelist_inverse: "freeword (Abs_freelist as) = map pairtrue as"
  using proper_signed_list_map_uniform_snd Abs_freeword_inverse by fast

lemma Abs_freeword_singleton_conv_apply_sign_freeletter:
  "Abs_freeword [x] = apply_sign Abs_freeletter x"
  by (cases x) (auto simp add: uminus_Abs_freeword_singleton)

lemma Abs_freeword_conv_freeletter_sum_list:
  "proper_signed_list xs \<Longrightarrow>
    Abs_freeword xs = (\<Sum>x\<leftarrow>xs. apply_sign Abs_freeletter x)"
proof (induct xs)
  case (Cons x xs) thus ?case
    using Abs_freeword_Cons[of x] binrelchain_Cons_reduce[of _ x]
    by (simp add: Abs_freeword_singleton_conv_apply_sign_freeletter)
qed (simp add: zero_freeword.abs_eq)

lemma freeword_conv_freeletter_sum_list:
  "x = (\<Sum>s\<leftarrow>freeword x. apply_sign Abs_freeletter s)"
  using Abs_freeword_conv_freeletter_sum_list[of "freeword x"] freeword
  by    (auto simp add: freeword_inverse)

lemma Abs_freeletter_prod_conv_Abs_freeword:
  "snd x \<Longrightarrow> Abs_freeletter (fst x) = Abs_freeword [x]"
  using prod_eqI[of x "pairtrue (fst x)"] by simp


subsubsection {* Lifts of functions on the letter type *}

text {*
  Here we lift functions on the letter type to type @{type freeword}. In particular, we are
  interested in the case where the function being lifted has codomain of class @{class group_add}.
*}

paragraph {* The universal property *}

text {* 
  The universal property for free groups says that every function from the letter type to some
  @{class group_add} type gives rise to a unique homomorphism.
*}

lemma extend_map_to_freeword_hom':
  fixes   f :: "'a \<Rightarrow> 'b::group_add"
  defines h: "h::'a signed \<Rightarrow> 'b \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  defines g: "g::'a signed list \<Rightarrow> 'b \<equiv> \<lambda>xs. sum_list (map h xs)"
  shows   "g (prappend_signed_list xs ys) = g xs + g ys"
proof (induct xs ys rule: list_induct2_snoc_Cons)
  case (snoc_Cons xs x y ys)
  show ?case
  proof (cases "y = flip_signed x")
    case True
    with h have "h y = - h x"
      using split_beta'[of "\<lambda>s b. if b then f s else - (f s)"] by simp
    with g have "g (xs @ [x]) + g (y # ys) = g xs + g ys"
      by (simp add: algebra_simps)
    with True snoc_Cons show ?thesis by simp
  next
    case False with g show ?thesis
      using sum_list.append[of "map h (xs@[x])" "map h (y#ys)"] by simp
  qed
qed (auto simp add: h g)

lemma extend_map_to_freeword_hom1:
  fixes   f :: "'a \<Rightarrow> 'b::group_add"
  defines "h::'a signed \<Rightarrow> 'b \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  defines "g::'a freeword \<Rightarrow> 'b \<equiv> \<lambda>x. sum_list (map h (freeword x))"
  shows   "g (Abs_freeletter s) = f s"
  using   assms
  by      (simp add: Abs_freeword_inverse)

lemma extend_map_to_freeword_hom2:
  fixes   f :: "'a \<Rightarrow> 'b::group_add"
  defines "h::'a signed \<Rightarrow> 'b \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  defines "g::'a freeword \<Rightarrow> 'b \<equiv> \<lambda>x. sum_list (map h (freeword x))"
  shows   "UGroupHom g"
  using   assms
  by      (
            auto intro: UGroupHomI
            simp add: plus_freeword.rep_eq extend_map_to_freeword_hom'
          )

lemma uniqueness_of_extended_map_to_freeword_hom':
  fixes   f :: "'a \<Rightarrow> 'b::group_add"
  defines h: "h::'a signed \<Rightarrow> 'b \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  defines g: "g::'a signed list \<Rightarrow> 'b \<equiv> \<lambda>xs. sum_list (map h xs)"
  assumes singles: "\<And>s. k [(s,True)] = f s"
  and     adds   : "\<And>xs ys. proper_signed_list xs \<Longrightarrow> proper_signed_list ys
            \<Longrightarrow> k (prappend_signed_list xs ys) = k xs + k ys"
  shows   "proper_signed_list xs \<Longrightarrow> k xs = g xs"
proof-
  have knil: "k [] = 0" using adds[of "[]" "[]"] add.assoc[of "k []" "k []" "- k []"] by simp
  have ksingle: "\<And>x. k [x] = g [x]"
  proof-
    fix x :: "'a signed"
    obtain s b where x: "x = (s,b)" by fastforce
    show "k [x] = g [x]"
    proof (cases b)
      case False
      from adds x singles
        have  "k (prappend_signed_list [x] [(s,True)]) = k [x] + f s"
        by    simp
      moreover have "prappend_signed_list [(s,False)] [(s,True)] = []"
        using collapse_flipped_signed[of s False] by simp
      ultimately have "- f s = k [x] + f s + - f s" using x False knil by simp
      with x False g h show "k [x] = g [x]" by (simp add: algebra_simps)
    qed (simp add: x g h singles)
  qed
  show "proper_signed_list xs \<Longrightarrow> k xs = g xs"
  proof (induct xs rule: list_induct_CCons)
    case (CCons x y xs)
    with g h show ?case
      using adds[of "[x]" "y#xs"]
      by    (simp add:
              prappend_signed_list_single_Cons
              ksingle extend_map_to_freeword_hom'
            )
  qed (auto simp add: g h knil ksingle)
qed

lemma uniqueness_of_extended_map_to_freeword_hom:
  fixes   f :: "'a \<Rightarrow> 'b::group_add"
  defines "h::'a signed \<Rightarrow> 'b \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  defines "g::'a freeword \<Rightarrow> 'b \<equiv> \<lambda>x. sum_list (map h (freeword x))"
  assumes k: "k \<circ> Abs_freeletter = f" "UGroupHom k"
  shows   "k = g"
proof
  fix x::"'a freeword"
  define k' where k': "k' \<equiv> k \<circ> Abs_freeword"
  have "k' (freeword x) = g x" unfolding h_def g_def
  proof (rule uniqueness_of_extended_map_to_freeword_hom')
    from k' k(1) show "\<And>s. k' [pairtrue s] = f s" by auto
    show "\<And>xs ys. proper_signed_list xs \<Longrightarrow> proper_signed_list ys
            \<Longrightarrow> k' (prappend_signed_list xs ys) = k' xs + k' ys"
    proof-
      fix xs ys :: "'a signed list"
      assume xsys: "proper_signed_list xs" "proper_signed_list ys"
      with k'
        show  "k' (prappend_signed_list xs ys) = k' xs + k' ys"
        using UGroupHom.hom[OF k(2), of "Abs_freeword xs" "Abs_freeword ys"]
        by    (simp add: plus_freeword_abs_eq)      
    qed
    show "proper_signed_list (freeword x)" using freeword by fast
  qed
  with k' show "k x = g x" using freeword_inverse[of x] by simp
qed

theorem universal_property:
  fixes f :: "'a \<Rightarrow> 'b::group_add"
  shows "\<exists>!g::'a freeword\<Rightarrow>'b. g \<circ> Abs_freeletter = f \<and> UGroupHom g"
proof
  define h where h: "h \<equiv> \<lambda>(s,b). if b then f s else - (f s)"
  define g where g: "g \<equiv> \<lambda>x. sum_list (map h (freeword x))"
  from g h show "g \<circ> Abs_freeletter = f \<and> UGroupHom g"
    using extend_map_to_freeword_hom1[of f] extend_map_to_freeword_hom2
    by    auto
  from g h show "\<And>k. k \<circ> Abs_freeletter = f \<and> UGroupHom k \<Longrightarrow> k = g"
    using uniqueness_of_extended_map_to_freeword_hom by auto
qed

paragraph {* Properties of homomorphisms afforded by the universal property *}

text {* 
  The lift of a function on the letter set is the unique additive function on @{type freeword}
  that agrees with the original function on letters.
*}

definition freeword_funlift :: "('a \<Rightarrow> 'b::group_add) \<Rightarrow> ('a freeword\<Rightarrow>'b::group_add)"
  where "freeword_funlift f \<equiv> (THE g. g \<circ> Abs_freeletter = f \<and> UGroupHom g)"

lemma additive_freeword_funlift: "UGroupHom (freeword_funlift f)"
  using theI'[OF universal_property, of f] unfolding freeword_funlift_def by simp

lemma freeword_funlift_Abs_freeletter: "freeword_funlift f (Abs_freeletter s) = f s"
  using     theI'[OF universal_property, of f]
            comp_apply[of "freeword_funlift f" Abs_freeletter]
  unfolding freeword_funlift_def
  by        fastforce

lemmas freeword_funlift_add         = UGroupHom.hom        [OF additive_freeword_funlift]
lemmas freeword_funlift_0           = UGroupHom.im_zero    [OF additive_freeword_funlift]
lemmas freeword_funlift_uminus      = UGroupHom.im_uminus  [OF additive_freeword_funlift]
lemmas freeword_funlift_diff        = UGroupHom.im_diff    [OF additive_freeword_funlift]
lemmas freeword_funlift_lconjby     = UGroupHom.im_lconjby [OF additive_freeword_funlift]

lemma freeword_funlift_uminus_Abs_freeletter:
  "freeword_funlift f (Abs_freeword [(s,False)]) = - f s"
  using freeword_funlift_uminus[of f "Abs_freeword [(s,False)]"]
        uminus_freeword_Abs_eq[of "[(s,False)]"]
        freeword_funlift_Abs_freeletter[of f]
  by    simp

lemma freeword_funlift_Abs_freeword_singleton:
  "freeword_funlift f (Abs_freeword [x]) = apply_sign f x"
proof-
  obtain s b where x: "x = (s,b)" by fastforce
  thus ?thesis
    using freeword_funlift_Abs_freeletter freeword_funlift_uminus_Abs_freeletter
    by    (cases b) auto
qed

lemma freeword_funlift_Abs_freeword_Cons:
  assumes "proper_signed_list (x#xs)"
  shows   "freeword_funlift f (Abs_freeword (x#xs)) =
            apply_sign f x + freeword_funlift f (Abs_freeword xs)"
proof-
  from assms
    have "freeword_funlift f (Abs_freeword (x#xs)) =
            freeword_funlift f (Abs_freeword [x]) +
            freeword_funlift f (Abs_freeword xs)"
    using Abs_freeword_Cons[of x xs] freeword_funlift_add by simp
  thus ?thesis
    using freeword_funlift_Abs_freeword_singleton[of f x] by simp
qed

lemma freeword_funlift_Abs_freeword:
  "proper_signed_list xs \<Longrightarrow> freeword_funlift f (Abs_freeword xs) =
    (\<Sum>x\<leftarrow>xs. apply_sign f x)"
proof (induct xs)
  case (Cons x xs) thus ?case
    using freeword_funlift_Abs_freeword_Cons[of _ _ f]
          binrelchain_Cons_reduce[of _ x xs]
    by    simp
qed (simp add: zero_freeword.abs_eq[THEN sym] freeword_funlift_0)

lemma freeword_funlift_Abs_freelist:
  "freeword_funlift f (Abs_freelist xs) = (\<Sum>x\<leftarrow>xs. f x)"
proof (induct xs)
  case (Cons x xs) thus ?case
    using Abs_freelist_Cons[of x xs]
    by    (simp add: freeword_funlift_add freeword_funlift_Abs_freeletter)
qed (simp add: zero_freeword.abs_eq[THEN sym] freeword_funlift_0)

lemma freeword_funlift_im':
  "proper_signed_list xs \<Longrightarrow> fst ` set xs \<subseteq> S \<Longrightarrow>
    freeword_funlift f (Abs_freeword xs) \<in> \<langle>f`S\<rangle>"
proof (induct xs)
  case Nil
  have "Abs_freeword ([]::'a signed list) = (0::'a freeword)"
    using zero_freeword.abs_eq[THEN sym] by simp
  thus "freeword_funlift f (Abs_freeword ([]::'a signed list)) \<in> \<langle>f`S\<rangle>"
    using freeword_funlift_0[of f] genby_0_closed by simp
next
  case (Cons x xs)
  define y where y: "y \<equiv> apply_sign f x"
  define z where z: "z \<equiv> freeword_funlift f (Abs_freeword xs)"
  from Cons(3) have "fst ` set xs \<subseteq> S" by simp
  with z Cons(1,2) have "z \<in> \<langle>f`S\<rangle>" using binrelchain_Cons_reduce by fast
  with y Cons(3) have "y + z \<in> \<langle>f`S\<rangle>"
    using genby_genset_closed[of _ "f`S"]
          genby_uminus_closed genby_add_closed[of y]
    by    fastforce
  with Cons(2) y z show ?case
    using freeword_funlift_Abs_freeword_Cons
          subst[
            OF  sym,
            of  "freeword_funlift f (Abs_freeword (x#xs))" "y+z"
                "\<lambda>b. b\<in>\<langle>f`S\<rangle>"
          ]
    by    fast
qed


subsubsection {* Free groups on a set *}

text {* 
  We now take the free group on a set to be the set in the @{type freeword} type with letters
  restricted to the given set.
*}

paragraph {* Definition and basic facts *}

text {*
  Here we define the set of elements of the free group over a set of letters, and record basic
  facts about that set.
*}

definition FreeGroup :: "'a set \<Rightarrow> 'a freeword set"
  where "FreeGroup S \<equiv> {x. fst ` set (freeword x) \<subseteq> S}"

lemma FreeGroupI_transfer:
  "proper_signed_list xs \<Longrightarrow> fst ` set xs \<subseteq> S \<Longrightarrow> Abs_freeword xs \<in> FreeGroup S"
  using Abs_freeword_inverse unfolding FreeGroup_def by fastforce

lemma FreeGroupD: "x \<in> FreeGroup S \<Longrightarrow> fst ` set (freeword x) \<subseteq> S"
  using FreeGroup_def by fast

lemma FreeGroupD_transfer:
  "proper_signed_list xs \<Longrightarrow> Abs_freeword xs \<in> FreeGroup S \<Longrightarrow> fst ` set xs \<subseteq> S"
  using Abs_freeword_inverse unfolding FreeGroup_def by fastforce

lemma FreeGroupD_transfer':
  "Abs_freelist xs \<in> FreeGroup S \<Longrightarrow> xs \<in> lists S"
  using proper_signed_list_map_uniform_snd FreeGroupD_transfer by fastforce

lemma FreeGroup_0_closed: "0 \<in> FreeGroup S"
proof-
  have "(0::'a freeword) = Abs_freeword []" using zero_freeword.abs_eq by fast
  moreover have "Abs_freeword [] \<in> FreeGroup S"
    using FreeGroupI_transfer[of "[]"] by simp
  ultimately show ?thesis by simp
qed

lemma FreeGroup_diff_closed:
  assumes "x \<in> FreeGroup S" "y \<in> FreeGroup S"
  shows   "x-y \<in> FreeGroup S"
proof-
  define xs where xs: "xs \<equiv> freeword x"
  define ys where ys: "ys \<equiv> freeword y"
  have "freeword (x-y) =
        prappend_signed_list (freeword x) (rev (map flip_signed (freeword y)))"
    by transfer simp
  hence "fst ` set (freeword (x-y)) \<subseteq> fst ` (set (freeword x) \<union> set (freeword y))"
    using fst_set_prappend_signed_list by force
  with assms show ?thesis unfolding FreeGroup_def by fast
qed

lemma FreeGroup_Group: "Group (FreeGroup S)"
  using FreeGroup_0_closed FreeGroup_diff_closed by unfold_locales fast

lemmas FreeGroup_add_closed    = Group.add_closed    [OF FreeGroup_Group]
lemmas FreeGroup_uminus_closed = Group.uminus_closed [OF FreeGroup_Group]

lemmas FreeGroup_genby_set_lconjby_set_rconjby_closed =
  Group.genby_set_lconjby_set_rconjby_closed[OF FreeGroup_Group]

lemma Abs_freelist_in_FreeGroup: "ss \<in> lists S \<Longrightarrow> Abs_freelist ss \<in> FreeGroup S"
  using proper_signed_list_map_uniform_snd by (fastforce intro: FreeGroupI_transfer)

lemma Abs_freeletter_in_FreeGroup_iff: "(Abs_freeletter s \<in> FreeGroup S) = (s\<in>S)"
  using Abs_freeword_inverse[of "[pairtrue s]"] unfolding FreeGroup_def by simp

paragraph {* Lifts of functions from the letter set to some type of class @{class group_add} *}

text {*
  We again obtain a universal property for functions from the (restricted) letter set to some type
  of class @{class group_add}.
*}

abbreviation "res_freeword_funlift f S \<equiv>
                restrict0 (freeword_funlift f) (FreeGroup S)"

lemma freeword_funlift_im: "x \<in> FreeGroup S \<Longrightarrow> freeword_funlift f x \<in> \<langle>f ` S\<rangle>"
  using     freeword[of x] freeword_funlift_im'[of "freeword x"]
            freeword_inverse[of x]
  unfolding FreeGroup_def
  by        auto

lemma freeword_funlift_surj':
  "ys \<in> lists (f`S \<union> uminus`f`S) \<Longrightarrow> sum_list ys \<in> freeword_funlift f ` FreeGroup S"
proof (induct ys)
  case Nil thus ?case using FreeGroup_0_closed freeword_funlift_0 by fastforce
next
  case (Cons y ys)
  from this obtain x
    where x: "x \<in> FreeGroup S" "sum_list ys = freeword_funlift f x"
    by    auto
  show "sum_list (y#ys) \<in> freeword_funlift f ` FreeGroup S"
  proof (cases "y \<in> f`S")
    case True
    from this obtain s where s: "s\<in>S" "y = f s" by fast
    from s(1) x(1) have "Abs_freeletter s + x \<in> FreeGroup S"
      using FreeGroupI_transfer[of _ S] FreeGroup_add_closed[of _ S] by force
    moreover from s(2) x(2)
      have  "freeword_funlift f (Abs_freeletter s + x) = sum_list (y#ys)"
      using freeword_funlift_add[of f] freeword_funlift_Abs_freeletter
      by    simp
    ultimately show ?thesis by force
  next
    case False
    with Cons(2) obtain s where s: "s\<in>S" "y = - f s" by auto
    from s(1) x(1) have "Abs_freeword [(s,False)] + x \<in> FreeGroup S"
      using FreeGroupI_transfer[of _ S] FreeGroup_add_closed[of _ S] by force
    moreover from s(2) x(2)
      have  "freeword_funlift f (Abs_freeword [(s,False)] + x) = sum_list (y#ys)"
      using freeword_funlift_add[of f] freeword_funlift_uminus_Abs_freeletter
      by    simp
    ultimately show ?thesis by force
  qed
qed

lemma freeword_funlift_surj:
  fixes f :: "'a \<Rightarrow> 'b::group_add"
  shows "freeword_funlift f ` FreeGroup S = \<langle>f`S\<rangle>"
proof (rule seteqI)
  show "\<And>a. a \<in> freeword_funlift f ` FreeGroup S \<Longrightarrow> a \<in> \<langle>f`S\<rangle>"
    using freeword_funlift_im by auto
next
  fix w assume "w\<in>\<langle>f`S\<rangle>"
  from this obtain ys where ys: "ys \<in> lists (f`S \<union> uminus`f`S)" "w = sum_list ys"
    using genby_eq_sum_lists[of "f`S"] by auto
  thus "w \<in> freeword_funlift f ` FreeGroup S" using freeword_funlift_surj' by simp
qed

lemma hom_restrict0_freeword_funlift:
  "GroupHom (FreeGroup S) (res_freeword_funlift f S)"
  using UGroupHom.restrict0 additive_freeword_funlift FreeGroup_Group
  by    auto

lemma uniqueness_of_restricted_lift:
  assumes "GroupHom (FreeGroup S) T" "\<forall>s\<in>S. T (Abs_freeletter s) = f s"
  shows   "T = res_freeword_funlift f S"
proof
  fix x
  define F where "F \<equiv> res_freeword_funlift f S"
  define u_Abs where "u_Abs \<equiv> \<lambda>a::'a signed. apply_sign Abs_freeletter a"
  show "T x = F x"
  proof (cases "x \<in> FreeGroup S")
    case True
    have 1: "set (map u_Abs (freeword x)) \<subseteq> FreeGroup S"
      using u_Abs_def FreeGroupD[OF True]
            Abs_freeletter_in_FreeGroup_iff[of _ S]
            FreeGroup_uminus_closed
      by    auto
    moreover from u_Abs_def have  "x = (\<Sum>a\<leftarrow>freeword x. u_Abs a)"
      using freeword_conv_freeletter_sum_list by fast
    ultimately
      have  "T x = (\<Sum>a\<leftarrow>freeword x. T (u_Abs a))"
            "F x = (\<Sum>a\<leftarrow>freeword x. F (u_Abs a))"
      using F_def
            GroupHom.im_sum_list_map[OF assms(1), of u_Abs "freeword x"]
            GroupHom.im_sum_list_map[
              OF hom_restrict0_freeword_funlift,
              of u_Abs "freeword x" S f
            ]
      by auto
    moreover have "\<forall>a\<in>set (freeword x). T (u_Abs a) = F (u_Abs a)"
    proof
      fix a assume "a \<in> set (freeword x)"
      moreover define b where "b \<equiv> Abs_freeletter (fst a)"
      ultimately show "T (u_Abs a) = F (u_Abs a)"
        using F_def u_Abs_def True assms(2) FreeGroupD[of x S]
              GroupHom.im_uminus[OF assms(1)] 
              Abs_freeletter_in_FreeGroup_iff[of "fst a" S]
              GroupHom.im_uminus[OF hom_restrict0_freeword_funlift, of b S f]
              freeword_funlift_Abs_freeletter[of f]
        by    auto
    qed
    ultimately show ?thesis
      using F_def
            sum_list_map_cong[of "freeword x" "\<lambda>s. T (u_Abs s)" "\<lambda>s. F (u_Abs s)"]
      by    simp
  next
    case False
    with assms(1) F_def show ?thesis
      using hom_restrict0_freeword_funlift GroupHom.supp suppI_contra[of x T]
            suppI_contra[of x F]
      by    fastforce
  qed
qed

theorem FreeGroup_universal_property:
  fixes f :: "'a \<Rightarrow> 'b::group_add"
  shows "\<exists>!T::'a freeword\<Rightarrow>'b. (\<forall>s\<in>S. T (Abs_freeletter s) = f s) \<and>
          GroupHom (FreeGroup S) T"
proof (rule ex1I, rule conjI)
  show "\<forall>s\<in>S. res_freeword_funlift f S (Abs_freeletter s) = f s"
    using Abs_freeletter_in_FreeGroup_iff[of _ S] freeword_funlift_Abs_freeletter
    by    auto
  show "\<And>T. (\<forall>s\<in>S. T (Abs_freeletter s) = f s) \<and>
          GroupHom (FreeGroup S) T \<Longrightarrow>
          T = restrict0 (freeword_funlift f) (FreeGroup S)"
    using uniqueness_of_restricted_lift by auto
qed (rule hom_restrict0_freeword_funlift)


subsubsection {* Group presentations *}

text {* 
  We now define a group presentation to be the quotient of a free group by the subgroup generated by
  all conjugates of a set of relators. We are most concerned with lifting functions on the letter
  set to the free group and with the associated induced homomorphisms on the quotient.
*}

paragraph {* A first group presentation locale and basic facts *}

text {*
  Here we define a locale that provides a way to construct a group by providing sets of generators
  and relator words.
*}

locale GroupByPresentation =
  fixes   S :: "'a set"  -- {* the set of generators *}
  and     P :: "'a signed list set" -- {* the set of relator words *}
  assumes P_S: "ps\<in>P \<Longrightarrow> fst ` set ps \<subseteq> S"
  and     proper_P: "ps\<in>P \<Longrightarrow> proper_signed_list ps"
begin

abbreviation "P' \<equiv> Abs_freeword ` P" -- {* the set of relators *}
abbreviation "Q \<equiv> Group.normal_closure (FreeGroup S) P'"
-- {* the normal subgroup generated by relators inside the free group *}
abbreviation "G \<equiv> Group.quotient_group (FreeGroup S) Q"

lemmas G_UN = Group.quotient_group_UN[OF FreeGroup_Group, of S Q]

lemma P'_FreeS: "P' \<subseteq> FreeGroup S"
  using P_S proper_P by (blast intro: FreeGroupI_transfer)

lemma relators: "P' \<subseteq> Q"
  using FreeGroup_0_closed genby_genset_subset by fastforce

lemmas lconjby_P'_FreeS =
  Group.set_lconjby_subset_closed[
    OF FreeGroup_Group _ P'_FreeS, OF basic_monos(1)
  ]

lemmas Q_FreeS =
  Group.genby_closed[OF FreeGroup_Group lconjby_P'_FreeS]

lemmas Q_subgroup_FreeS =
  Group.genby_subgroup[OF FreeGroup_Group lconjby_P'_FreeS]

lemmas normal_Q = Group.normal_closure[OF FreeGroup_Group, OF P'_FreeS]

lemmas natural_hom =
  Group.natural_quotient_hom[
    OF FreeGroup_Group Q_subgroup_FreeS normal_Q
  ]

lemmas natural_hom_image =
  Group.natural_quotient_hom_image[OF FreeGroup_Group, of S Q]

end (* context GroupByPresentation *)

paragraph {* Functions on the quotient induced from lifted functions *}

text {*
  A function on the generator set into a type of class @{class group_add} lifts to a unique
  homomorphism on the free group. If this lift is trivial on relators, then it factors to a
  homomorphism of the group described by the generators and relators.
*}

locale GroupByPresentationInducedFun = GroupByPresentation S P
  for     S :: "'a set"
  and     P :: "'a signed list set" -- {* the set of relator words *}
+ fixes   f :: "'a \<Rightarrow> 'b::group_add"
  assumes lift_f_trivial_P:
    "ps\<in>P \<Longrightarrow> freeword_funlift f (Abs_freeword ps) = 0"
begin

abbreviation "lift_f \<equiv> freeword_funlift f"

definition induced_hom :: "'a freeword set permutation \<Rightarrow> 'b"
  where "induced_hom \<equiv> GroupHom.quotient_hom (FreeGroup S)
          (restrict0 lift_f (FreeGroup S)) Q"
  -- {* the @{const restrict0} operation is really only necessary to make
@{const GroupByPresentationInducedFun.induced_hom} a @{const GroupHom} *}
abbreviation "F \<equiv> induced_hom"

lemma lift_f_trivial_P': "p\<in>P' \<Longrightarrow> lift_f p = 0"
  using lift_f_trivial_P by fast

lemma lift_f_trivial_lconjby_P': "p\<in>P' \<Longrightarrow> lift_f (lconjby w p) = 0"
  using freeword_funlift_lconjby[of f] lift_f_trivial_P' by simp

lemma lift_f_trivial_Q: "q\<in>Q \<Longrightarrow> lift_f q = 0"
proof (erule genby.induct, rule freeword_funlift_0)
  show "\<And>s. s \<in> (\<Union>w \<in> FreeGroup S. lconjby w ` P') \<Longrightarrow> lift_f s = 0"
    using lift_f_trivial_lconjby_P' by fast
next
  fix w w' :: "'a freeword" assume ww': "lift_f w = 0" "lift_f w' = 0"
  have "lift_f (w - w') = lift_f w - lift_f w'"
    using freeword_funlift_diff[of f w] by simp
  with ww' show "lift_f (w-w') = 0" by simp
qed

lemma lift_f_ker_Q: "Q \<subseteq> ker lift_f"
  using lift_f_trivial_Q unfolding ker_def by auto

lemma lift_f_Ker_Q: "Q \<subseteq> GroupHom.Ker (FreeGroup S) lift_f"
  using lift_f_ker_Q Q_FreeS by fast

lemma restrict0_lift_f_Ker_Q:
  "Q \<subseteq> GroupHom.Ker (FreeGroup S) (restrict0 lift_f (FreeGroup S))"
  using lift_f_Ker_Q ker_subset_ker_restrict0 by fast

lemma induced_hom_equality:
  "w \<in> FreeGroup S \<Longrightarrow> F (\<lceil>FreeGroup S|w|Q\<rceil>) = lift_f w"
-- {* 
  algebraic properties of the induced homomorphism could be proved using its properties as a group
  homomorphism, but it's generally easier to prove them using the algebraic properties of the lift
  via this lemma
*}
  unfolding induced_hom_def
  using     GroupHom.quotient_hom_im hom_restrict0_freeword_funlift
            Q_subgroup_FreeS normal_Q restrict0_lift_f_Ker_Q
  by        fastforce

lemma hom_induced_hom: "GroupHom G F"
  unfolding induced_hom_def
  using     GroupHom.quotient_hom hom_restrict0_freeword_funlift
            Q_subgroup_FreeS normal_Q restrict0_lift_f_Ker_Q
  by        fast

lemma induced_hom_Abs_freeletter_equality:
  "s\<in>S \<Longrightarrow> F (\<lceil>FreeGroup S|Abs_freeletter s|Q\<rceil>) = f s"
  using Abs_freeletter_in_FreeGroup_iff[of s S]        
  by    (simp add: induced_hom_equality freeword_funlift_Abs_freeletter)

lemma uniqueness_of_induced_hom':
  defines "q \<equiv> Group.natural_quotient_hom (FreeGroup S) Q"
  assumes "GroupHom G T" "\<forall>s\<in>S. T (\<lceil>FreeGroup S|Abs_freeletter s|Q\<rceil>) = f s"
  shows   "T \<circ> q = F \<circ> q"
proof-
  from assms have "T\<circ>q = res_freeword_funlift f S"
    using natural_hom natural_hom_image Abs_freeletter_in_FreeGroup_iff[of _ S]
    by    (force intro: uniqueness_of_restricted_lift GroupHom.comp)
  moreover from q_def have "F \<circ> q = res_freeword_funlift f S"
    using induced_hom_equality GroupHom.im_zero[OF hom_induced_hom]
    by    auto
  ultimately show ?thesis by simp  
qed

lemma uniqueness_of_induced_hom:
  assumes "GroupHom G T" "\<forall>s\<in>S. T (\<lceil>FreeGroup S|Abs_freeletter s|Q\<rceil>) = f s"
  shows   "T = F"
proof
  fix x
  show "T x = F x"
  proof (cases "x\<in>G")
    case True
    define q where "q \<equiv> Group.natural_quotient_hom (FreeGroup S) Q"
    from True obtain w where "w \<in> FreeGroup S" "x = (\<lceil>FreeGroup S|w|Q\<rceil>)"
      using G_UN by fast
    with q_def have "T x = (T\<circ>q) w" "F x = (F\<circ>q) w" by auto
    with assms q_def show ?thesis using uniqueness_of_induced_hom' by simp
  next
    case False
    with assms(1) show ?thesis
      using hom_induced_hom GroupHom.supp suppI_contra[of x T]
            suppI_contra[of x F]
      by    fastforce
  qed
qed

theorem induced_hom_universal_property:
  "\<exists>!F. GroupHom G F \<and> (\<forall>s\<in>S. F (\<lceil>FreeGroup S|Abs_freeletter s|Q\<rceil>) = f s)"
  using hom_induced_hom induced_hom_Abs_freeletter_equality
        uniqueness_of_induced_hom
  by    blast

lemma induced_hom_Abs_freelist_conv_sum_list:
  "ss\<in>lists S \<Longrightarrow> F (\<lceil>FreeGroup S|Abs_freelist ss|Q\<rceil>) = (\<Sum>s\<leftarrow>ss. f s)"
  by  (simp add:
        Abs_freelist_in_FreeGroup induced_hom_equality freeword_funlift_Abs_freelist
      )

lemma induced_hom_surj: "F`G = \<langle>f`S\<rangle>"
proof (rule seteqI)
  show "\<And>x. x\<in>F`G \<Longrightarrow> x\<in>\<langle>f`S\<rangle>"
    using G_UN induced_hom_equality freeword_funlift_surj[of f S] by auto
next
  fix x assume "x\<in>\<langle>f`S\<rangle>"
  hence "x \<in> lift_f ` FreeGroup S" using freeword_funlift_surj[of f S] by fast
  thus "x \<in> F`G" using induced_hom_equality G_UN by force
qed

end (* context GroupByPresentationInducedFun *)

paragraph {* Groups affording a presentation *}

text {*
  The locale @{const GroupByPresentation} allows the construction of a @{const Group} out of any
  type from a set of generating letters and a set of relator words in (signed) letters. The
  following locale concerns the question of when the @{const Group} generated by a set in class
  @{class group_add} is isomorphic to a group presentation.
*}

locale GroupWithGeneratorsRelators =
  fixes S :: "'g::group_add set" -- {* the set of generators *}
  and   R :: "'g list set" -- {* the set of relator words *}
  assumes relators: "rs\<in>R \<Longrightarrow> rs \<in> lists (S \<union> uminus ` S)"
                    "rs\<in>R \<Longrightarrow> sum_list rs = 0"
                    "rs\<in>R \<Longrightarrow> proper_signed_list (map (charpair S) rs)"
begin

abbreviation "P \<equiv> map (charpair S) ` R"
abbreviation "P' \<equiv> GroupByPresentation.P' P"
abbreviation "Q \<equiv> GroupByPresentation.Q S P"
abbreviation "G \<equiv> GroupByPresentation.G S P"
abbreviation "relator_freeword rs \<equiv> Abs_freeword (map (charpair S) rs)"
-- {* this maps R onto P' *}

abbreviation "freeliftid \<equiv> freeword_funlift id"

abbreviation induced_id :: "'g freeword set permutation \<Rightarrow> 'g"
  where "induced_id \<equiv> GroupByPresentationInducedFun.induced_hom S P id"

lemma GroupByPresentation_S_P: "GroupByPresentation S P"
proof
  show "\<And>ps. ps \<in> P \<Longrightarrow> fst ` set ps \<subseteq> S"
    using fst_set_map_charpair_un_uminus relators(1) by fast
  show "\<And>ps. ps \<in> P \<Longrightarrow> proper_signed_list ps" using relators(3) by fast
qed

lemmas G_UN     = GroupByPresentation.G_UN[OF GroupByPresentation_S_P]
lemmas P'_FreeS = GroupByPresentation.P'_FreeS[OF GroupByPresentation_S_P]

lemma freeliftid_trivial_relator_freeword_R:
  "rs\<in>R \<Longrightarrow> freeliftid (relator_freeword rs) = 0"
  using relators(2,3) freeword_funlift_Abs_freeword[of "map (charpair S) rs" id]
        sum_list_map_cong[of rs "(apply_sign id) \<circ> (charpair S)" id]
  by    simp

lemma freeliftid_trivial_P: "ps\<in>P \<Longrightarrow> freeliftid (Abs_freeword ps) = 0"
  using freeliftid_trivial_relator_freeword_R by fast

lemma GroupByPresentationInducedFun_S_P_id:
  "GroupByPresentationInducedFun S P id"
  by  (
        intro_locales, rule GroupByPresentation_S_P,
        unfold_locales, rule freeliftid_trivial_P
      )

lemma induced_id_Abs_freelist_conv_sum_list:
  "ss\<in>lists S \<Longrightarrow> induced_id (\<lceil>FreeGroup S|Abs_freelist ss|Q\<rceil>) = sum_list ss"
  by  (simp add:
        GroupByPresentationInducedFun.induced_hom_Abs_freelist_conv_sum_list[
          OF GroupByPresentationInducedFun_S_P_id
        ]
      )

lemma lconj_relator_freeword_R:
  "\<lbrakk> rs\<in>R; proper_signed_list xs; fst ` set xs \<subseteq> S \<rbrakk> \<Longrightarrow>
    lconjby (Abs_freeword xs) (relator_freeword rs) \<in> Q"
  by (blast intro: genby_genset_closed FreeGroupI_transfer)

lemma rconj_relator_freeword:
  assumes "rs\<in>R" "proper_signed_list xs" "fst ` set xs \<subseteq> S"
  shows   "rconjby (Abs_freeword xs) (relator_freeword rs) \<in> Q"
proof (rule genby_genset_closed, rule UN_I)
  show "- Abs_freeword xs \<in> FreeGroup S"
    using FreeGroupI_transfer[OF assms(2,3)] FreeGroup_uminus_closed by fast
  from assms(1)
    show  "rconjby (Abs_freeword xs) (relator_freeword rs) \<in>
            lconjby (- Abs_freeword xs) ` Abs_freeword ` P"
    by    simp
qed

lemma lconjby_Abs_freelist_relator_freeword:
  "\<lbrakk> rs\<in>R; xs\<in>lists S \<rbrakk> \<Longrightarrow> lconjby (Abs_freelist xs) (relator_freeword rs) \<in> Q"
  using proper_signed_list_map_uniform_snd by (force intro: lconj_relator_freeword_R)

text {*
  Here we record that the lift of the identity map to the free group on @{term S} induces a
  homomorphic surjection onto the group generated by @{term S} from the group presentation on
  @{term S}, subject to the same relations as the elements of @{term S}.
*}

theorem induced_id_hom_surj: "GroupHom G induced_id" "induced_id ` G = \<langle>S\<rangle>"
  using GroupByPresentationInducedFun.hom_induced_hom[
          OF GroupByPresentationInducedFun_S_P_id
        ]
        GroupByPresentationInducedFun.induced_hom_surj[
          OF GroupByPresentationInducedFun_S_P_id
        ]
  by    auto

end (* context GroupWithGeneratorsRelators *)

locale GroupPresentation = GroupWithGeneratorsRelators S R
  for S :: "'g::group_add set" -- {* the set of generators *}
  and R :: "'g list set" -- {* the set of relator words *}
+ assumes induced_id_inj: "inj_on induced_id G"
begin

abbreviation "inv_induced_id \<equiv> the_inv_into G induced_id"

lemma inv_induced_id_sum_list_S:
  "ss \<in> lists S \<Longrightarrow> inv_induced_id (sum_list ss) = (\<lceil>FreeGroup S|Abs_freelist ss|Q\<rceil>)"
  using G_UN induced_id_inj induced_id_Abs_freelist_conv_sum_list
        Abs_freelist_in_FreeGroup
  by    (blast intro: the_inv_into_f_eq)

end (* GroupPresentation *)

subsection {* Words over a generating set *}

text {*
  Here we gather the necessary constructions and facts for studying a group generated by some set
  in terms of words in the generators.
*}

context monoid_add
begin

abbreviation "word_for A a as \<equiv> as \<in> lists A \<and> sum_list as = a"

definition reduced_word_for :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool"
  where "reduced_word_for A a as \<equiv> is_arg_min length (word_for A a) as"

abbreviation "reduced_word A as \<equiv> reduced_word_for A (sum_list as) as"
abbreviation "reduced_words_for A a \<equiv> Collect (reduced_word_for A a)"

abbreviation reduced_letter_set :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a set"
  where "reduced_letter_set A a \<equiv> \<Union>( set ` (reduced_words_for A a) )"
  -- {* will be empty if @{term a} is not in the set generated by @{term A} *}

definition word_length :: "'a set \<Rightarrow> 'a \<Rightarrow> nat"
  where "word_length A a \<equiv> length (arg_min length (word_for A a))"

lemma reduced_word_forI:
  assumes   "as \<in> lists A" "sum_list as = a"
            "\<And>bs. bs \<in> lists A \<Longrightarrow> sum_list bs = a \<Longrightarrow> length as \<le> length bs"
  shows     "reduced_word_for A a as"
  using     assms 
  unfolding reduced_word_for_def
  by        (force intro: is_arg_minI)

lemma reduced_word_forI_compare:
  "\<lbrakk> reduced_word_for A a as; bs \<in> lists A; sum_list bs = a; length bs = length as \<rbrakk>
    \<Longrightarrow> reduced_word_for A a bs"
  using reduced_word_for_def is_arg_min_eq[of length] by fast

lemma reduced_word_for_lists: "reduced_word_for A a as \<Longrightarrow> as \<in> lists A"
  using reduced_word_for_def is_arg_minD1 by fast

lemma reduced_word_for_sum_list: "reduced_word_for A a as \<Longrightarrow> sum_list as = a"
  using reduced_word_for_def is_arg_minD1 by fast

lemma reduced_word_for_minimal:
  "\<lbrakk> reduced_word_for A a as; bs \<in> lists A; sum_list bs = a \<rbrakk> \<Longrightarrow>
    length as \<le> length bs"
  using reduced_word_for_def is_arg_minD2[of length]
  by fastforce

lemma reduced_word_for_length:
  "reduced_word_for A a as \<Longrightarrow> length as = word_length A a"
  unfolding word_length_def reduced_word_for_def is_arg_min_def
  by (fastforce intro: arg_min_equality[THEN sym])

lemma reduced_word_for_eq_length:
  "reduced_word_for A a as \<Longrightarrow> reduced_word_for A a bs \<Longrightarrow> length as = length bs"
  using reduced_word_for_length by simp

lemma reduced_word_for_arg_min:
  "as \<in> lists A \<Longrightarrow> sum_list as = a \<Longrightarrow>
    reduced_word_for A a (arg_min length (word_for A a))"
  using     is_arg_min_arg_min_nat[of "word_for A a"]
  unfolding reduced_word_for_def
  by        fast

lemma nil_reduced_word_for_0: "reduced_word_for A 0 []"
  by (auto intro: reduced_word_forI)

lemma reduced_word_for_0_imp_nil: "reduced_word_for A 0 as \<Longrightarrow> as = []"
  using     nil_reduced_word_for_0[of A] reduced_word_for_minimal[of A 0 as]
  unfolding reduced_word_for_def is_arg_min_def
  by (metis (mono_tags, hide_lams) length_0_conv length_greater_0_conv)

lemma not_reduced_word_for:
  "\<lbrakk> bs \<in> lists A; sum_list bs = a; length bs < length as \<rbrakk> \<Longrightarrow>
    \<not> reduced_word_for A a as"
  using reduced_word_for_minimal by fastforce

lemma reduced_word_for_imp_reduced_word:
  "reduced_word_for A a as \<Longrightarrow> reduced_word A as"
unfolding reduced_word_for_def is_arg_min_def
by (fast intro: reduced_word_forI)

lemma sum_list_zero_nreduced:
  "as \<noteq> [] \<Longrightarrow> sum_list as = 0 \<Longrightarrow> \<not> reduced_word A as"
  using not_reduced_word_for[of "[]"] by simp

lemma order2_nreduced: "a+a=0 \<Longrightarrow> \<not> reduced_word A [a,a]"
  using sum_list_zero_nreduced by simp

lemma reduced_word_append_reduce_contra1:
  assumes "\<not> reduced_word A as"
  shows   "\<not> reduced_word A (as@bs)"
proof (cases "as \<in> lists A" "bs \<in> lists A" rule: two_cases)
  case both
  define cs where cs: "cs \<equiv> ARG_MIN length cs. cs \<in> lists A \<and> sum_list cs = sum_list as"
  with both(1) have "reduced_word_for A (sum_list as) cs"
    using reduced_word_for_def is_arg_min_arg_min_nat[of "word_for A (sum_list as)"]
    by    auto
  with assms both show ?thesis
    using reduced_word_for_lists reduced_word_for_sum_list
          reduced_word_for_minimal[of A "sum_list as" cs as]
          reduced_word_forI_compare[of A "sum_list as" cs as]
          not_reduced_word_for[of "cs@bs" A "sum_list (as@bs)"]
    by    fastforce
next
  case one thus ?thesis using reduced_word_for_lists by fastforce
next
  case other thus ?thesis using reduced_word_for_lists by fastforce
next
  case neither thus ?thesis using reduced_word_for_lists by fastforce
qed

lemma reduced_word_append_reduce_contra2:
  assumes "\<not> reduced_word A bs"
  shows   "\<not> reduced_word A (as@bs)"
proof (cases "as \<in> lists A" "bs \<in> lists A" rule: two_cases)
  case both
  define cs where cs: "cs \<equiv> ARG_MIN length cs. cs \<in> lists A \<and> sum_list cs = sum_list bs"
  with both(2) have "reduced_word_for A (sum_list bs) cs"
    using reduced_word_for_def is_arg_min_arg_min_nat[of "word_for A (sum_list bs)" ]
    by    auto
  with assms both show ?thesis
    using reduced_word_for_lists reduced_word_for_sum_list
          reduced_word_for_minimal[of A "sum_list bs" cs bs]
          reduced_word_forI_compare[of A "sum_list bs" cs bs]
          not_reduced_word_for[of "as@cs" A "sum_list (as@bs)"]
    by    fastforce
next
  case one thus ?thesis using reduced_word_for_lists by fastforce
next
  case other thus ?thesis using reduced_word_for_lists by fastforce
next
  case neither thus ?thesis using reduced_word_for_lists by fastforce
qed

lemma contains_nreduced_imp_nreduced:
  "\<not> reduced_word A bs \<Longrightarrow> \<not> reduced_word A (as@bs@cs)"
  using reduced_word_append_reduce_contra1 reduced_word_append_reduce_contra2
  by    fast

lemma contains_order2_nreduced: "a+a=0 \<Longrightarrow> \<not> reduced_word A (as@[a,a]@bs)"
  using order2_nreduced contains_nreduced_imp_nreduced by fast

lemma reduced_word_Cons_reduce_contra:
  "\<not> reduced_word A as \<Longrightarrow> \<not> reduced_word A (a#as)"
  using reduced_word_append_reduce_contra2[of A as "[a]"] by simp

lemma reduced_word_Cons_reduce: "reduced_word A (a#as) \<Longrightarrow> reduced_word A as"
  using reduced_word_Cons_reduce_contra by fast

lemma reduced_word_singleton:
  assumes "a\<in>A" "a\<noteq>0"
  shows   "reduced_word A [a]"
proof (rule reduced_word_forI)
  from assms(1) show "[a] \<in> lists A" by simp
next
  fix bs assume bs: "bs \<in> lists A" "sum_list bs = sum_list [a]"
  with assms(2) show "length [a] \<le> length bs" by (cases bs) auto
qed simp

lemma el_reduced:
  assumes "0 \<notin> A" "as \<in> lists A" "sum_list as \<in> A" "reduced_word A as"
  shows "length as = 1"
proof-
  define n where n: "n \<equiv> length as"
  from assms(3) obtain a where "[a]\<in>lists A" "sum_list as = sum_list [a]" by auto
  with n assms(1,3,4) have "n\<le>1" "n>0"
    using reduced_word_for_minimal[of A _ as "[a]"] by auto
  hence "n = 1" by simp
  with n show ?thesis by fast
qed

lemma reduced_letter_set_0: "reduced_letter_set A 0 = {}"
  using reduced_word_for_0_imp_nil by simp

lemma reduced_letter_set_subset: "reduced_letter_set A a \<subseteq> A"
  using reduced_word_for_lists by fast

lemma reduced_word_forI_length:
  "\<lbrakk> as \<in> lists A; sum_list as = a; length as = word_length A a \<rbrakk> \<Longrightarrow>
    reduced_word_for A a as"
  using reduced_word_for_arg_min reduced_word_for_length
        reduced_word_forI_compare[of A a _ as]
  by    fastforce

lemma word_length_le:
  "as \<in> lists A \<Longrightarrow> sum_list as = a \<Longrightarrow> word_length A a \<le> length as"
  using reduced_word_for_arg_min reduced_word_for_length
        reduced_word_for_minimal[of A]
  by    fastforce

lemma reduced_word_forI_length':
  "\<lbrakk> as \<in> lists A; sum_list as = a; length as \<le> word_length A a \<rbrakk> \<Longrightarrow>
    reduced_word_for A a as"
  using word_length_le[of as A] reduced_word_forI_length[of as A] by fastforce

lemma word_length_lt:
  "as \<in> lists A \<Longrightarrow> sum_list as = a \<Longrightarrow> \<not> reduced_word_for A a as \<Longrightarrow>
    word_length A a < length as"
  using reduced_word_forI_length' by fastforce

end (* context monoid_add *)

lemma in_genby_reduced_letter_set:
  assumes "as \<in> lists A" "sum_list as = a"
  shows   "a \<in> \<langle>reduced_letter_set A a\<rangle>"
proof-
  define xs where xs: "xs \<equiv> arg_min length (word_for A a)"
  with assms have "xs \<in> lists (reduced_letter_set A a)" "sum_list xs = a"
    using reduced_word_for_arg_min[of as A] reduced_word_for_sum_list by auto
  thus ?thesis using genby_eq_sum_lists by force
qed

lemma reduced_word_for_genby_arg_min:
  fixes   A :: "'a::group_add set"
  defines "B \<equiv> A \<union> uminus ` A"
  assumes "a\<in>\<langle>A\<rangle>"
  shows   "reduced_word_for B a (arg_min length (word_for B a))"
  using   assms genby_eq_sum_lists[of A] reduced_word_for_arg_min[of _ B a]
  by      auto

lemma reduced_word_for_genby_sym_arg_min:
  assumes "uminus ` A \<subseteq> A" "a\<in>\<langle>A\<rangle>"
  shows   "reduced_word_for A a (arg_min length (word_for A a))"
proof-
  from assms(1) have "A = A \<union> uminus ` A" by auto
  with assms(2) show ?thesis
    using reduced_word_for_genby_arg_min[of a A] by simp
qed

lemma in_genby_imp_in_reduced_letter_set:
  fixes   A :: "'a::group_add set"
  defines "B \<equiv> A \<union> uminus ` A"
  assumes "a \<in> \<langle>A\<rangle>"
  shows   "a \<in> \<langle>reduced_letter_set B a\<rangle>"
  using   assms genby_eq_sum_lists[of A] in_genby_reduced_letter_set[of _ B]
  by      auto

lemma in_genby_sym_imp_in_reduced_letter_set:
  "uminus ` A \<subseteq> A \<Longrightarrow> a \<in> \<langle>A\<rangle> \<Longrightarrow> a \<in> \<langle>reduced_letter_set A a\<rangle>"
  using in_genby_imp_in_reduced_letter_set by (fastforce simp add: Un_absorb2)

end (* theory *)
