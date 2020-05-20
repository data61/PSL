(*  Author: Andreas Lochbihler, ETH Zurich
    Author: Joshua Schneider, ETH Zurich
*)

subsection \<open>Pointwise arithmetic on infinite binary trees\<close>

theory Cotree_Algebra
imports Cotree
begin

subsubsection \<open>Constants and operators\<close>

instantiation tree :: (zero) zero begin
definition [applicative_unfold]: "0 = pure_tree 0"
instance ..
end

instantiation tree :: (one) one begin
definition [applicative_unfold]: "1 = pure_tree 1"
instance ..
end

instantiation tree :: (plus) plus begin
definition [applicative_unfold]: "plus x y = pure (+) \<diamondop> x \<diamondop> (y :: 'a tree)"
instance ..
end

lemma plus_tree_simps [simp]:
  "root (t + t') = root t + root t'"
  "left (t + t') = left t + left t'"
  "right (t + t') = right t + right t'"
by(simp_all add: plus_tree_def)

friend_of_corec plus where "t + t' = Node (root t + root t') (left t + left t') (right t + right t')"
subgoal by(rule tree.expand; simp)
subgoal by transfer_prover
done

instantiation tree :: (minus) minus begin
definition [applicative_unfold]: "minus x y = pure (-) \<diamondop> x \<diamondop> (y :: 'a tree)"
instance ..
end

lemma minus_tree_simps [simp]:
  "root (t - t') = root t - root t'"
  "left (t - t') = left t - left t'"
  "right (t - t') = right t - right t'"
by(simp_all add: minus_tree_def)

instantiation tree :: (uminus) uminus begin
definition [applicative_unfold tree]: "uminus = ((\<diamondop>) (pure uminus) :: 'a tree \<Rightarrow> 'a tree)"
instance ..
end

instantiation tree :: (times) times begin
definition [applicative_unfold]: "times x y = pure (*) \<diamondop> x \<diamondop> (y :: 'a tree)"
instance ..
end

lemma times_tree_simps [simp]:
  "root (t * t') = root t * root t'"
  "left (t * t') = left t * left t'"
  "right (t * t') = right t * right t'"
by(simp_all add: times_tree_def)

instance tree :: (Rings.dvd) Rings.dvd ..

instantiation tree :: (modulo) modulo begin
definition [applicative_unfold]: "x div y = pure_tree (div) \<diamondop> x \<diamondop> (y :: 'a tree)"
definition [applicative_unfold]: "x mod y = pure_tree (mod) \<diamondop> x \<diamondop> (y :: 'a tree)"
instance ..
end

lemma mod_tree_simps [simp]:
  "root (t mod t') = root t mod root t'"
  "left (t mod t') = left t mod left t'"
  "right (t mod t') = right t mod right t'"
by(simp_all add: modulo_tree_def)


subsubsection \<open>Algebraic instances\<close>

instance tree :: (semigroup_add) semigroup_add
using add.assoc by intro_classes applicative_lifting

instance tree :: (ab_semigroup_add) ab_semigroup_add
using add.commute by intro_classes applicative_lifting

instance tree :: (semigroup_mult) semigroup_mult
using mult.assoc by intro_classes applicative_lifting

instance tree :: (ab_semigroup_mult) ab_semigroup_mult
using mult.commute by intro_classes applicative_lifting

instance tree :: (monoid_add) monoid_add
by intro_classes (applicative_lifting, simp)+

instance tree :: (comm_monoid_add) comm_monoid_add
by intro_classes (applicative_lifting, simp)

instance tree :: (comm_monoid_diff) comm_monoid_diff
by intro_classes (applicative_lifting, simp add: diff_diff_add)+

instance tree :: (monoid_mult) monoid_mult
by intro_classes (applicative_lifting, simp)+

instance tree :: (comm_monoid_mult) comm_monoid_mult
by intro_classes (applicative_lifting, simp)

instance tree :: (cancel_semigroup_add) cancel_semigroup_add
proof
  fix a b c :: "'a tree"
  assume "a + b = a + c"
  thus "b = c"
  proof (coinduction arbitrary: a b c)
    case (Eq_tree a b c)
    hence "root (a + b) = root (a + c)"
          "left (a + b) = left (a + c)"
          "right (a + b) = right (a + c)"
      by simp_all
    thus ?case by (auto)
  qed
next
  fix a b c :: "'a tree"
  assume "b + a = c + a"
  thus "b = c"
  proof (coinduction arbitrary: a b c)
    case (Eq_tree a b c)
    hence "root (b + a) = root (c + a)"
          "left (b + a) = left (c + a)"
          "right (b + a) = right (c + a)"
      by simp_all
    thus ?case by (auto)
  qed
qed


instance tree :: (cancel_ab_semigroup_add) cancel_ab_semigroup_add
by intro_classes (applicative_lifting, simp add: diff_diff_eq)+

instance tree :: (cancel_comm_monoid_add) cancel_comm_monoid_add ..

instance tree :: (group_add) group_add
by intro_classes (applicative_lifting, simp)+

instance tree :: (ab_group_add) ab_group_add
by intro_classes (applicative_lifting, simp)+

instance tree :: (semiring) semiring
by intro_classes (applicative_lifting, simp add: ring_distribs)+

instance tree :: (mult_zero) mult_zero
by intro_classes (applicative_lifting, simp)+

instance tree :: (semiring_0) semiring_0 ..

instance tree :: (semiring_0_cancel) semiring_0_cancel ..

instance tree :: (comm_semiring) comm_semiring
by intro_classes(rule distrib_right)

instance tree :: (comm_semiring_0) comm_semiring_0 ..

instance tree :: (comm_semiring_0_cancel) comm_semiring_0_cancel ..

lemma pure_tree_inject[simp]: "pure_tree x = pure_tree y \<longleftrightarrow> x = y"
proof
  assume "pure_tree x = pure_tree y"
  hence "root (pure_tree x) = root (pure_tree y)" by simp
  thus "x = y" by simp
qed simp

instance tree :: (zero_neq_one) zero_neq_one
by intro_classes (applicative_unfold tree)

instance tree :: (semiring_1) semiring_1 ..

instance tree :: (comm_semiring_1) comm_semiring_1 ..

instance tree :: (semiring_1_cancel) semiring_1_cancel ..

instance tree :: (comm_semiring_1_cancel) comm_semiring_1_cancel
by(intro_classes; applicative_lifting, rule right_diff_distrib')

instance tree :: (ring) ring ..

instance tree :: (comm_ring) comm_ring ..

instance tree :: (ring_1) ring_1 ..

instance tree :: (comm_ring_1) comm_ring_1 ..

instance tree :: (numeral) numeral ..

instance tree :: (neg_numeral) neg_numeral ..

instance tree :: (semiring_numeral) semiring_numeral ..

lemma of_nat_tree: "of_nat n = pure_tree (of_nat n)"
proof (induction n)
  case 0 show ?case by (simp add: zero_tree_def)
next
  case (Suc n)
  have "1 + pure (of_nat n) = pure (1 + of_nat n)" by applicative_nf rule
  with Suc.IH show ?case by simp
qed

instance tree :: (semiring_char_0) semiring_char_0
by intro_classes (simp add: inj_on_def of_nat_tree)

lemma numeral_tree_simps [simp]:
  "root (numeral n) = numeral n"
  "left (numeral n) = numeral n"
  "right (numeral n) = numeral n"
by(induct n)(auto simp add: numeral.simps plus_tree_def one_tree_def)

lemma numeral_tree_conv_pure [applicative_unfold]: "numeral n = pure (numeral n)"
by(rule pure_tree_unique)(rule tree.expand; simp)

instance tree :: (ring_char_0) ring_char_0 ..

end
