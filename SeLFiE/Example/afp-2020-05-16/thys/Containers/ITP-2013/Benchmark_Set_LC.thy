theory Benchmark_Set_LC
imports 
  Benchmark_Set
  Containers.Set_Impl
  "HOL-Library.Code_Target_Nat"
begin

lemma [code_unfold del]: "card \<equiv> Cardinality.card'" by(simp)

instantiation word :: (len0) ceq begin
definition "CEQ('a word) = Some (=)"
instance by(intro_classes)(simp add: ceq_word_def)
end

instantiation word :: (len0) compare begin
definition "compare_word = (comparator_of :: 'a word comparator)"
instance by(intro_classes)(simp add: compare_word_def comparator_of)
end

instantiation word :: (len0) ccompare begin
definition "CCOMPARE('a word) = Some compare"
instance by(intro_classes)(simp add: ccompare_word_def comparator_compare)
end

instantiation word :: (len0) set_impl begin
definition "SET_IMPL('a word) = Phantom('a word) set_RBT"
instance ..
end

instantiation word :: (len) proper_interval begin

fun proper_interval_word :: "'a word option \<Rightarrow> 'a word option \<Rightarrow> bool"
where
  "proper_interval_word None None = True"
| "proper_interval_word None (Some y) = (y \<noteq> 0)"
| "proper_interval_word (Some x) None = (x \<noteq> max_word)"
| "proper_interval_word (Some x) (Some y) = (x < y \<and> x \<noteq> y - 1)"

instance
proof
  let ?pi = "proper_interval :: 'a word proper_interval"
  show "?pi None None = True" by simp
  fix y
  show "?pi None (Some y) = (\<exists>z. z < y)"
    by simp (metis word_gt_0 word_not_simps(1))
  fix x
  show "?pi (Some x) None = (\<exists>z. x < z)"
    by simp (metis eq_iff max_word_max not_le)

  have "(x < y \<and> x \<noteq> y - 1) = (\<exists>z>x. z < y)" (is "?lhs \<longleftrightarrow> ?rhs")
  proof
    assume ?lhs
    then obtain "x < y" "x \<noteq> y - 1" ..
    have "0 \<le> uint x" by simp
    also have "\<dots> < uint y" using \<open>x < y\<close> by(simp add: word_less_def)
    finally have "0 < uint y" .
    then have "y - 1 < y" by(simp add: word_less_def uint_sub_if' not_le)
    moreover from \<open>0 < uint y\<close> \<open>x < y\<close> \<open>x \<noteq> y - 1\<close>
    have "x < y - 1" by(simp add: word_less_def uint_sub_if' uint_arith_simps(3))
    ultimately show ?rhs by blast
  next
    assume ?rhs
    then obtain z where z: "x < z" "z < y" by blast
    have "0 \<le> uint z" by simp
    also have "\<dots> < uint y" using \<open>z < y\<close> by(simp add: word_less_def)
    finally show ?lhs using z by(auto simp add: word_less_def uint_sub_if')
  qed
  thus "?pi (Some x) (Some y) = (\<exists>z>x. z < y)" by simp
qed

end

instantiation word :: (len) cproper_interval begin
definition "cproper_interval = (proper_interval :: 'a word proper_interval)"
instance by( intro_classes, simp add: cproper_interval_word_def ccompare_word_def 
  compare_word_def le_lt_comparator_of ID_Some proper_interval_class.axioms)
end

instantiation word :: (len0) cenum begin
definition "CENUM('a word) = None"
instance by(intro_classes)(simp_all add: cEnum_word_def)
end

notepad begin
  have "Benchmark_Set.complete 30 40 (12345, 67899) = (32, 4294967296)" by eval
end

end
