subsection \<open>Index\<close>

theory Index
  imports Main
begin

definition injective :: "nat \<Rightarrow> ('k \<Rightarrow> nat) \<Rightarrow> bool" where
  "injective size to_index \<equiv> \<forall> a b.
      to_index a = to_index b
    \<and> to_index a < size
    \<and> to_index b < size
    \<longrightarrow> a = b"
  for size to_index

lemma index_mono:
  fixes a b a0 b0 :: nat
  assumes a: "a < a0" and b: "b < b0"
  shows "a * b0 + b < a0 * b0"
proof -
  have "a * b0 + b < (Suc a) * b0"
    using b by auto
  also have "\<dots> \<le> a0 * b0"
    using a[THEN Suc_leI, THEN mult_le_mono1] .
  finally show ?thesis .
qed

lemma index_eq_iff:
  fixes a b c d b0 :: nat
  assumes "b < b0" "d < b0" "a * b0 + b = c * b0 + d"
  shows "a = c \<and> b = d"
proof (rule conjI)
  { fix a b c d :: nat
    assume ac: "a < c" and b: "b < b0"
    have "a * b0 + b < (Suc a) * b0"
      using b by auto
    also have "\<dots> \<le> c * b0"
      using ac[THEN Suc_leI, THEN mult_le_mono1] .
    also have "\<dots> \<le> c * b0 + d"
      by auto
    finally have "a * b0 + b \<noteq> c * b0 + d"
      by auto
  } note ac = this

  { assume "a \<noteq> c"
    then consider (le) "a < c" | (ge) "a > c"
      by fastforce
    hence False proof cases
      case le show ?thesis using ac[OF le assms(1)] assms(3) ..
    next
      case ge show ?thesis using ac[OF ge assms(2)] assms(3)[symmetric] ..
    qed
  }
  
  then show "a = c"
    by auto

  with assms(3) show "b = d"
    by auto
qed


locale prod_order_def =
  order0: ord less_eq0 less0 +
  order1: ord less_eq1 less1
  for less_eq0 less0 less_eq1 less1
begin

fun less :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less (a,b) (c,d) \<longleftrightarrow> less0 a c \<and> less1 b d"

fun less_eq :: "'a \<times> 'b \<Rightarrow> 'a \<times> 'b \<Rightarrow> bool" where
  "less_eq ab cd \<longleftrightarrow> less ab cd \<or> ab = cd"

end

locale prod_order =
  prod_order_def less_eq0 less0 less_eq1 less1 +
  order0: order less_eq0 less0 +
  order1: order less_eq1 less1
  for less_eq0 less0 less_eq1 less1
begin

sublocale order less_eq less
proof qed fastforce+

end

locale option_order =
  order0: order less_eq0 less0
  for less_eq0 less0
begin

fun less_eq_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_eq_option None _ \<longleftrightarrow> True"
| "less_eq_option (Some _) None \<longleftrightarrow> False"
| "less_eq_option (Some a) (Some b) \<longleftrightarrow> less_eq0 a b"

fun less_option :: "'a option \<Rightarrow> 'a option \<Rightarrow> bool" where
  "less_option ao bo \<longleftrightarrow> less_eq_option ao bo \<and> ao \<noteq> bo"

sublocale order less_eq_option less_option
  apply standard
  subgoal for x y by (cases x; cases y) auto
  subgoal for x by (cases x) auto
  subgoal for x y z by (cases x; cases y; cases z) auto
  subgoal for x y by (cases x; cases y) auto
  done

end

datatype 'a bound = Bound (lower: 'a) (upper:'a)

definition in_bound :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a bound \<Rightarrow> 'a \<Rightarrow> bool" where
  "in_bound less_eq less bound x \<equiv> case bound of Bound l r \<Rightarrow> less_eq l x \<and> less x r" for less_eq less

locale index_locale_def = ord less_eq less for less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool" +
  fixes idx :: "'a bound \<Rightarrow> 'a \<Rightarrow> nat"
    and size :: "'a bound \<Rightarrow> nat"

locale index_locale = index_locale_def + idx_ord: order +
  assumes idx_valid: "in_bound less_eq less bound x \<Longrightarrow> idx bound x < size bound"
    and idx_inj : "\<lbrakk>in_bound less_eq less bound x; in_bound less_eq less bound y; idx bound x = idx bound y\<rbrakk> \<Longrightarrow> x = y"

locale prod_index_def =
  index0: index_locale_def less_eq0 less0 idx0 size0 +
  index1: index_locale_def less_eq1 less1 idx1 size1
  for less_eq0 less0 idx0 size0 less_eq1 less1 idx1 size1
begin

fun idx :: "('a \<times> 'b) bound \<Rightarrow> 'a \<times> 'b \<Rightarrow> nat" where
  "idx (Bound (l0, r0) (l1, r1)) (a, b) = (idx0 (Bound l0 l1) a) * (size1 (Bound r0 r1)) + idx1 (Bound r0 r1) b"

fun size :: "('a \<times> 'b) bound \<Rightarrow> nat" where
  "size (Bound (l0, r0) (l1, r1)) = size0 (Bound l0 l1) * size1 (Bound r0 r1)"

end

locale prod_index = prod_index_def less_eq0 less0 idx0 size0 less_eq1 less1 idx1 size1 +
  index0: index_locale less_eq0 less0 idx0 size0 +
  index1: index_locale less_eq1 less1 idx1 size1
  for less_eq0 less0 idx0 size0 less_eq1 less1 idx1 size1
begin

sublocale prod_order less_eq0 less0 less_eq1 less1 ..

sublocale index_locale less_eq less idx size proof
  { fix ab :: "'a \<times> 'b" and bound :: "('a \<times> 'b) bound"
    assume bound: "in_bound less_eq less bound ab"

    obtain a b l0 r0 l1 r1 where defs:"ab = (a, b)" "bound = Bound (l0, r0) (l1, r1)"
      by (cases ab; cases bound) auto

    with bound have a: "in_bound less_eq0 less0 (Bound l0 l1) a" and b: "in_bound less_eq1 less1 (Bound r0 r1) b"
      unfolding in_bound_def by auto

    have "idx (Bound (l0, r0) (l1, r1)) (a, b) < size (Bound (l0, r0) (l1, r1))"
      using index_mono[OF index0.idx_valid[OF a] index1.idx_valid[OF b]] by auto

    thus "idx bound ab < size bound"
      unfolding defs .
  }

  { fix ab cd :: "'a \<times> 'b" and bound :: "('a \<times> 'b) bound"
    assume bound: "in_bound less_eq less bound ab" "in_bound less_eq less bound cd"
      and idx_eq: "idx bound ab = idx bound cd"

    obtain a b c d l0 r0 l1 r1 where
      defs: "ab = (a, b)" "cd = (c, d)" "bound = Bound (l0, l1) (r0, r1)"
      by (cases ab; cases cd; cases bound) auto

    from defs bound have
          a: "in_bound less_eq0 less0 (Bound l0 r0) a"
      and b: "in_bound less_eq1 less1 (Bound l1 r1) b"
      and c: "in_bound less_eq0 less0 (Bound l0 r0) c"
      and d: "in_bound less_eq1 less1 (Bound l1 r1) d"
      unfolding in_bound_def by auto

    from index_eq_iff[OF index1.idx_valid[OF b] index1.idx_valid[OF d] idx_eq[unfolded defs, simplified]]
    have ac: "idx0 (Bound l0 r0) a = idx0 (Bound l0 r0) c" and bd: "idx1 (Bound l1 r1) b = idx1 (Bound l1 r1) d" by auto
    show "ab = cd"
      unfolding defs using index0.idx_inj[OF a c ac] index1.idx_inj[OF b d bd] by auto
  }
qed
end

locale option_index =
  index0: index_locale less_eq0 less0 idx0 size0
  for less_eq0 less0 idx0 size0
begin

fun idx :: "'a option bound \<Rightarrow> 'a option \<Rightarrow> nat" where
  "idx (Bound (Some l) (Some r)) (Some a) = idx0 (Bound l r) a"
| "idx _ _ = undefined"
(* option is NOT an index *)

end

locale nat_index_def = ord "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool" "(<)"
begin

fun idx :: "nat bound \<Rightarrow> nat \<Rightarrow> nat" where
  "idx (Bound l _) i = i - l"

fun size :: "nat bound \<Rightarrow> nat" where
  "size (Bound l r) = r - l"

sublocale index_locale "(\<le>)" "(<)" idx size
proof qed (auto simp: in_bound_def split: bound.splits) 

end

locale nat_index = nat_index_def + order "(\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool" "(<)"

locale int_index_def = ord "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" "(<)"
begin

fun idx :: "int bound \<Rightarrow> int \<Rightarrow> nat" where
  "idx (Bound l _) i = nat (i - l)"

fun size :: "int bound \<Rightarrow> nat" where
  "size (Bound l r) = nat (r - l)"

sublocale index_locale "(\<le>)" "(<)" idx size
proof qed (auto simp: in_bound_def split: bound.splits) 

end

locale int_index = int_index_def + order "(\<le>) :: int \<Rightarrow> int \<Rightarrow> bool" "(<)"

class index =
  fixes less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    and idx :: "'a bound \<Rightarrow> 'a \<Rightarrow> nat"
    and size :: "'a bound \<Rightarrow> nat"
  assumes is_locale: "index_locale less_eq less idx size"

locale bounded_index =
  fixes bound :: "'k :: index bound"
begin

interpretation index_locale less_eq less idx size
  using is_locale .

definition "size \<equiv> index_class.size bound" for size

definition "checked_idx x \<equiv> if in_bound less_eq less bound x then idx bound x else size"

lemma checked_idx_injective:
  "injective size checked_idx"
  unfolding injective_def
  unfolding checked_idx_def
  using idx_inj by (fastforce split: if_splits)
end

instantiation nat :: index
begin

interpretation nat_index ..
thm index_locale_axioms

definition [simp]: "less_eq_nat \<equiv> (\<le>) :: nat \<Rightarrow> nat \<Rightarrow> bool"
definition [simp]: "less_nat \<equiv> (<) :: nat \<Rightarrow> nat \<Rightarrow> bool"
definition [simp]: "idx_nat \<equiv> idx"
definition size_nat where [simp]: "size_nat \<equiv> size"

instance by (standard, simp, fact index_locale_axioms)

end

instantiation int :: index
begin

interpretation int_index ..
thm index_locale_axioms

definition [simp]: "less_eq_int \<equiv> (\<le>) :: int \<Rightarrow> int \<Rightarrow> bool"
definition [simp]: "less_int \<equiv> (<) :: int \<Rightarrow> int \<Rightarrow> bool"
definition [simp]: "idx_int \<equiv> idx"
definition [simp]: "size_int \<equiv> size"

lemmas size_int = size.simps

instance by (standard, simp, fact index_locale_axioms)
end

instantiation prod :: (index, index) index
begin

interpretation prod_index
  "less_eq::'a \<Rightarrow> 'a \<Rightarrow> bool" less idx size
  "less_eq::'b \<Rightarrow> 'b \<Rightarrow> bool" less idx size
  by (rule prod_index.intro; fact is_locale)
thm index_locale_axioms

definition [simp]: "less_eq_prod \<equiv> less_eq"
definition [simp]: "less_prod \<equiv> less"
definition [simp]: "idx_prod \<equiv> idx"
definition [simp]: "size_prod \<equiv> size" for size_prod

lemmas size_prod = size.simps

instance by (standard, simp, fact index_locale_axioms)

end

lemma bound_int_simp[code]:
  "bounded_index.size (Bound (l1, l2) (u1, u2)) = nat (u1 - l1) * nat (u2 - l2)"
  by (simp add: bounded_index.size_def,unfold size_int_def[symmetric] size_prod,simp add: size_int)

lemmas [code] = bounded_index.size_def bounded_index.checked_idx_def

lemmas [code] =
  nat_index_def.size.simps
  nat_index_def.idx.simps

lemmas [code] =
  int_index_def.size.simps
  int_index_def.idx.simps

lemmas [code] =
  prod_index_def.size.simps
  prod_index_def.idx.simps

lemmas [code] =
  prod_order_def.less_eq.simps
  prod_order_def.less.simps

lemmas index_size_defs =
  prod_index_def.size.simps int_index_def.size.simps nat_index_def.size.simps bounded_index.size_def

end
