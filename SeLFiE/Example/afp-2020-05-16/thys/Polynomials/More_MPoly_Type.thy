(* Author: Alexander Bentkamp, Universität des Saarlandes
*)

theory More_MPoly_Type
imports MPoly_Type
begin

abbreviation "lookup == Poly_Mapping.lookup"
abbreviation "keys == Poly_Mapping.keys"

section "MPpoly Mapping extenion"

lemma lookup_Abs_poly_mapping_when_finite:
assumes "finite S"
shows "lookup (Abs_poly_mapping (\<lambda>x. f x when x\<in>S)) = (\<lambda>x. f x when x\<in>S)"
proof -
  have "finite {x. (f x when x\<in>S) \<noteq> 0}" using assms by auto
  then show ?thesis using lookup_Abs_poly_mapping by fast
qed

definition remove_key::"'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b::monoid_add) \<Rightarrow> ('a \<Rightarrow>\<^sub>0 'b)" where
  "remove_key k0 f = Abs_poly_mapping (\<lambda>k. lookup f k when k \<noteq> k0)"

lemma remove_key_lookup:
  "lookup (remove_key k0 f) k = (lookup f k when k \<noteq> k0)"
unfolding remove_key_def using finite_subset by (simp add: lookup_Abs_poly_mapping)

lemma remove_key_keys: "keys f - {k} = keys (remove_key k f)" (is "?A = ?B")
proof (rule antisym; rule subsetI)
  fix x assume "x \<in> ?A"
  then show "x \<in> ?B" using remove_key_lookup lookup_not_eq_zero_eq_in_keys DiffD1 DiffD2 insertCI
    by (metis (mono_tags, lifting) when_def)
next
  fix x assume "x \<in> ?B"
  then have "lookup (remove_key k f) x \<noteq> 0"  by blast
  then show "x \<in> ?A"
    by (simp add: lookup_not_eq_zero_eq_in_keys remove_key_lookup)
qed


lemma remove_key_sum: "remove_key k f + Poly_Mapping.single k (lookup f k) = f"
proof -
  {
  fix k'
  have rem:"(lookup f k' when k' \<noteq> k) = lookup (remove_key k f) k'"
    using when_def by (simp add: remove_key_lookup)
  have sin:"(lookup f k when k'=k) =  lookup (Poly_Mapping.single k (lookup f k)) k'"
    by (simp add: lookup_single_not_eq when_def)
  have "lookup f k' = (lookup f k' when k' \<noteq> k) + ((lookup f k) when k'=k)"
    unfolding when_def by fastforce
  with rem sin have "lookup f k' = lookup ((remove_key k f) + Poly_Mapping.single k (lookup f k)) k'"
    using lookup_add by metis
  }
  then show ?thesis by (metis poly_mapping_eqI)
qed

lemma remove_key_single[simp]: "remove_key v (Poly_Mapping.single v n) = 0"
proof -
 have 0:"\<And>k. (lookup (Poly_Mapping.single v n) k when k \<noteq> v) = 0" by (simp add: lookup_single_not_eq when_def)
 show ?thesis unfolding remove_key_def 0
   by auto
qed

lemma remove_key_add: "remove_key v m + remove_key v m' = remove_key v (m + m')"
  by (rule poly_mapping_eqI; simp add: lookup_add remove_key_lookup when_add_distrib)

lemma poly_mapping_induct [case_names single sum]:
fixes P::"('a, 'b::monoid_add) poly_mapping \<Rightarrow> bool"
assumes single:"\<And>k v. P (Poly_Mapping.single k v)"
and sum:"(\<And>f g k v. P f \<Longrightarrow> P g \<Longrightarrow> g = (Poly_Mapping.single k v) \<Longrightarrow> k \<notin> keys f \<Longrightarrow> P (f+g))"
shows "P f" using finite_keys[of f]
proof (induction "keys f" arbitrary: f rule: finite_induct)
  case (empty)
  then show ?case using single[of _ 0] by (metis (full_types) aux empty_iff not_in_keys_iff_lookup_eq_zero single_zero)
next
  case (insert k K f)
  obtain f1 f2 where f12_def: "f1 = remove_key k f" "f2 = Poly_Mapping.single k (lookup f k)" by blast
  have "P f1"
  proof -
    have "Suc (card (keys f1)) = card (keys f)"
      using remove_key_keys finite_keys f12_def(1) by (metis (no_types) Diff_insert_absorb card_insert_disjoint insert.hyps(2) insert.hyps(4))
    then show ?thesis using insert lessI by (metis Diff_insert_absorb f12_def(1) remove_key_keys)
  qed
  have "P f2" by (simp add: single f12_def(2))
  have "f1 + f2 = f" using remove_key_sum f12_def by auto
  have "k \<notin> keys f1" using remove_key_keys f12_def by fast
  then show ?case using \<open>P f1\<close> \<open>P f2\<close> sum[of f1 f2 k "lookup f k"] \<open>f1 + f2 = f\<close> f12_def by auto
qed


lemma map_lookup:
assumes "g 0 = 0"
shows "lookup (Poly_Mapping.map g f) x = g ((lookup f) x)"
proof -
  have "(g (lookup f x) when lookup f x \<noteq> 0) = g (lookup f x)"
    by (metis (mono_tags, lifting) assms when_def)
  then have "(g (lookup f x) when x \<in> keys f) = g (lookup f x)"
    using lookup_not_eq_zero_eq_in_keys [of f] by simp
  then show ?thesis 
    by (simp add: Poly_Mapping.map_def map_fun_def in_keys_iff)
qed

lemma keys_add:
assumes "keys f \<inter> keys g = {}"
shows "keys f \<union> keys g = keys (f+g)"
proof
  have "keys f \<subseteq> keys (f+g)"
  proof
    fix x assume "x\<in>keys f"
    then have "lookup (f+g) x = lookup f x " by (metis add.right_neutral assms disjoint_iff_not_equal not_in_keys_iff_lookup_eq_zero plus_poly_mapping.rep_eq)
    then show "x\<in>keys (f+g)" using \<open>x\<in>keys f\<close> by (metis not_in_keys_iff_lookup_eq_zero)
  qed
  moreover have "keys g \<subseteq> keys (f+g)"
  proof
    fix x assume "x\<in>keys g"
    then have "lookup (f+g) x = lookup g x "  by (metis IntI add.left_neutral assms empty_iff not_in_keys_iff_lookup_eq_zero plus_poly_mapping.rep_eq)
    then show "x\<in>keys (f+g)" using \<open>x\<in>keys g\<close> by (metis not_in_keys_iff_lookup_eq_zero)
  qed
  ultimately show "keys f \<union> keys g \<subseteq> keys (f+g)" by simp
next
  show "keys (f + g) \<subseteq> keys f \<union> keys g" by (simp add: keys_add)
qed

lemma fun_when:
"f 0 = 0 \<Longrightarrow> f (a when P) = (f a when P)" by (simp add: when_def)

section "MPoly extension"

lemma coeff_all_0:"(\<And>m. coeff p m = 0) \<Longrightarrow> p=0"
  by (metis aux coeff_def mapping_of_inject zero_mpoly.rep_eq)

definition vars::"'a::zero mpoly \<Rightarrow> nat set" where
  "vars p = \<Union> (keys ` keys (mapping_of p))"

lemma vars_finite: "finite (vars p)" unfolding vars_def by auto

lemma vars_monom_single: "vars (monom (Poly_Mapping.single v k) a) \<subseteq> {v}"
proof
  fix w assume "w \<in> vars (monom (Poly_Mapping.single v k) a)"
  then have "w = v" using vars_def by (metis UN_E lookup_eq_zero_in_keys_contradict lookup_single_not_eq monom.rep_eq)
  then show "w \<in> {v}" by auto
qed

lemma vars_monom_keys:
assumes "a\<noteq>0"
shows "vars (monom m a) = keys m"
proof (rule antisym; rule subsetI)
  fix w assume "w \<in> vars (monom m a)"
  then have "lookup m w \<noteq> 0" using vars_def by (metis UN_E lookup_eq_zero_in_keys_contradict lookup_single_not_eq monom.rep_eq)
  then show "w \<in> keys m" by (meson lookup_not_eq_zero_eq_in_keys)
next
  fix w assume "w \<in> keys m"
  then have "lookup m w \<noteq> 0" by (meson lookup_not_eq_zero_eq_in_keys)
  then show "w \<in> vars (monom m a)" unfolding vars_def using assms by (metis UN_iff lookup_not_eq_zero_eq_in_keys lookup_single_eq monom.rep_eq)
qed

lemma vars_monom_subset:
shows "vars (monom m a) \<subseteq> keys m"
  by (cases "a=0"; simp add: vars_def vars_monom_keys)

lemma vars_monom_single_cases: "vars (monom (Poly_Mapping.single v k) a) = (if k=0 \<or> a=0 then {} else {v})"
proof(cases "k=0")
  assume "k=0"
  then have "(Poly_Mapping.single v k) = 0" by simp
  then have "vars (monom (Poly_Mapping.single v k) a) = {}"
    by (metis (mono_tags, lifting) single_zero singleton_inject subset_singletonD vars_monom_single zero_neq_one)
  then show ?thesis using \<open>k=0\<close> by auto
next
  assume "k\<noteq>0"
  then show ?thesis
  proof (cases "a=0")
    assume "a=0"
    then have "monom (Poly_Mapping.single v k) a = 0" by (metis monom.abs_eq monom_zero single_zero)
    then show ?thesis by (metis (mono_tags, hide_lams) \<open>k \<noteq> 0\<close> \<open>a=0\<close> monom.abs_eq single_zero singleton_inject subset_singletonD vars_monom_single)
  next
    assume "a\<noteq>0"
    then have "v \<in> vars (monom (Poly_Mapping.single v k) a)" by (simp add: \<open>k \<noteq> 0\<close> vars_def)
    then show ?thesis using \<open>a\<noteq>0\<close> \<open>k \<noteq> 0\<close> vars_monom_single by fastforce
  qed
qed

lemma vars_monom:
assumes "a\<noteq>0"
shows "vars (monom m (1::'a::zero_neq_one)) = vars (monom m (a::'a))"
  unfolding vars_monom_keys[OF assms] using vars_monom_keys[of 1] one_neq_zero by blast

lemma vars_add: "vars (p1 + p2) \<subseteq> vars p1 \<union> vars p2"
proof
  fix w assume "w \<in> vars (p1 + p2)"
  then obtain m where "w \<in> keys m" "m \<in> keys (mapping_of (p1 + p2))" by (metis UN_E vars_def)
  then have "m \<in> keys (mapping_of (p1)) \<union> keys (mapping_of (p2))"
    by (metis Poly_Mapping.keys_add plus_mpoly.rep_eq subset_iff)
  then show "w \<in> vars p1 \<union> vars p2" using vars_def \<open>w \<in> keys m\<close> by fastforce
qed

lemma vars_mult: "vars (p*q) \<subseteq> vars p \<union> vars q"
proof
  fix x assume "x\<in>vars (p*q)"
  then obtain m where "m\<in>keys (mapping_of (p*q))" "x\<in>keys m"
    using vars_def  by blast
  then have "m\<in>keys (mapping_of p * mapping_of q)"
    by (simp add: times_mpoly.rep_eq)
  then obtain a b where "m=a + b" "a \<in> keys (mapping_of p)" "b \<in> keys (mapping_of q)"
    using keys_mult by blast
  then have "x \<in> keys a \<union> keys b"
    using Poly_Mapping.keys_add \<open>x \<in> keys m\<close> by force
  then show "x \<in> vars p \<union> vars q" unfolding vars_def
    using \<open>a \<in> keys (mapping_of p)\<close> \<open>b \<in> keys (mapping_of q)\<close> by blast
qed

lemma vars_add_monom:
assumes "p2 = monom m a" "m \<notin> keys (mapping_of p1)"
shows "vars (p1 + p2) = vars p1 \<union> vars p2"
proof -
  have "keys (mapping_of p2) \<subseteq> {m}" using monom_def keys_single assms by auto
  have "keys (mapping_of (p1+p2)) = keys (mapping_of p1) \<union> keys (mapping_of p2)"
    using keys_add by (metis Int_insert_right_if0 \<open>keys (mapping_of p2) \<subseteq> {m}\<close> assms(2) inf_bot_right plus_mpoly.rep_eq subset_singletonD)
  then show ?thesis unfolding vars_def by simp
qed

lemma vars_setsum: "finite S \<Longrightarrow> vars (\<Sum>m\<in>S. f m) \<subseteq> (\<Union>m\<in>S. vars (f m))"
proof (induction S rule:finite_induct)
  case empty
  then show ?case by (metis UN_empty eq_iff monom_zero sum.empty single_zero vars_monom_single_cases)
next
  case (insert s S)
  then have "vars (sum f (insert s S)) = vars (f s + sum f S)" by (metis sum.insert)
  also have "... \<subseteq> vars (f s) \<union> vars (sum f S)" by (simp add: vars_add)
  also have "... \<subseteq> (\<Union>m\<in>insert s S. vars (f m))" using insert.IH by auto
  finally show ?case by metis
qed

lemma coeff_monom: "coeff (monom m a) m' = (a when m'=m)"
  by (simp add: coeff_def lookup_single_not_eq when_def)

lemma coeff_add: "coeff p m + coeff q m = coeff (p+q) m"
  by (simp add: coeff_def lookup_add plus_mpoly.rep_eq)

lemma coeff_eq: "coeff p = coeff q \<longleftrightarrow> p=q" by (simp add: coeff_def lookup_inject mapping_of_inject)

lemma coeff_monom_mult: "coeff ((monom m' a)  * q) (m' + m)  = a * coeff q m"
  unfolding coeff_def times_mpoly.rep_eq lookup_mult mapping_of_monom lookup_single when_mult
  Sum_any_when_equal' Groups.cancel_semigroup_add_class.add_left_cancel by metis

lemma one_term_is_monomial:
assumes "card (keys (mapping_of p)) \<le> 1"
obtains m where "p = monom m (coeff p m)"
proof (cases "keys (mapping_of p) = {}")
  case True
  then show ?thesis using aux coeff_def empty_iff mapping_of_inject mapping_of_monom not_in_keys_iff_lookup_eq_zero single_zero by (metis (no_types) that)
next
  case False
  then obtain m where "keys (mapping_of p) = {m}" using assms by (metis One_nat_def Suc_leI antisym card_0_eq card_eq_SucD finite_keys neq0_conv)
  have "p = monom m (coeff p m)"
    unfolding mapping_of_inject[symmetric]
    by (rule poly_mapping_eqI, metis (no_types, lifting) \<open>keys (mapping_of p) = {m}\<close>
    coeff_def keys_single lookup_single_eq  mapping_of_monom not_in_keys_iff_lookup_eq_zero
    singletonD)
  then show ?thesis ..
qed

(* remove_term is eventually unnessecary *)
definition remove_term::"(nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a::zero mpoly \<Rightarrow> 'a mpoly" where
  "remove_term m0 p = MPoly (Abs_poly_mapping (\<lambda>m. coeff p m when m \<noteq> m0))"

lemma remove_term_coeff: "coeff (remove_term m0 p) m = (coeff p m when m \<noteq> m0)"
proof -
  have "{m. (coeff p m when m \<noteq> m0) \<noteq> 0} \<subseteq> {m. coeff p m \<noteq> 0}" by auto
  then have "finite {m. (coeff p m when m \<noteq> m0) \<noteq> 0}" unfolding coeff_def using finite_subset by auto
  then have "lookup (Abs_poly_mapping (\<lambda>m. coeff p m when m \<noteq> m0)) m = (coeff p m when m \<noteq> m0)" using lookup_Abs_poly_mapping by fastforce
  then show ?thesis unfolding remove_term_def using coeff_def by (metis (mono_tags, lifting) Quotient_mpoly Quotient_rep_abs_fold_unmap)
qed

lemma coeff_keys: "m \<in> keys (mapping_of p) \<longleftrightarrow> coeff p m \<noteq> 0"
  by (simp add: coeff_def in_keys_iff)

lemma remove_term_keys:
shows "keys (mapping_of p) - {m} = keys (mapping_of (remove_term m p))" (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix m' assume "m'\<in>?A"
    then show "m' \<in> ?B" by (simp add: coeff_keys remove_term_coeff)
  qed
  show "?B \<subseteq> ?A"
  proof
    fix m' assume "m'\<in> ?B"
    then show "m' \<in> ?A" by (simp add: coeff_keys remove_term_coeff)
  qed
qed


lemma remove_term_sum: "remove_term m p + monom m (coeff p m) = p"
proof -
  have "coeff p = (\<lambda>m'. (coeff p m' when m' \<noteq> m) + ((coeff p m) when m'=m))" unfolding when_def by fastforce
  moreover have "coeff (remove_term m p + monom m (coeff p m)) = ..."
    using remove_term_coeff coeff_monom coeff_add by (metis (no_types))
  ultimately show ?thesis using coeff_eq by auto
qed

lemma mpoly_induct [case_names monom sum]:
assumes monom:"\<And>m a. P (monom m a)"
and sum:"(\<And>p1 p2 m a. P p1 \<Longrightarrow> P p2 \<Longrightarrow> p2 = (monom m a) \<Longrightarrow> m \<notin> keys (mapping_of p1) \<Longrightarrow> P (p1+p2))"
shows "P p" using assms
  using poly_mapping_induct[of "\<lambda>p :: (nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a. P (MPoly p)"] MPoly_induct monom.abs_eq plus_mpoly.abs_eq
  by (metis (no_types) MPoly_inverse UNIV_I)

lemma monom_pow:"monom (Poly_Mapping.single v n0) a ^ n = monom (Poly_Mapping.single v (n0*n)) (a ^ n)"
apply (induction n)
apply auto
by (metis (no_types, lifting) mult_monom single_add)

lemma insertion_fun_single: "insertion_fun f (\<lambda>m. (a when (Poly_Mapping.single (v::nat) (n::nat)) = m)) = a * f v ^ n" (is "?i = _")
proof -
  have setsum_single:"\<And> a f. (\<Sum>m\<in>{a}. f m) = f a"
   by (metis add.right_neutral empty_Diff finite.emptyI sum.empty sum.insert_remove)

  have 1:"?i = (\<Sum>m. (a when Poly_Mapping.single v n = m) * (\<Prod>v. f v ^ lookup m v))"
    unfolding insertion_fun_def by metis
  have "\<forall>m. m \<noteq> Poly_Mapping.single v n \<longrightarrow> (a when Poly_Mapping.single v n = m) = 0" by simp

  have "(\<Sum>m\<in>{Poly_Mapping.single v n}. (a when Poly_Mapping.single v n = m) * (\<Prod>v. f v ^ lookup m v)) = ?i"
    unfolding 1 when_mult unfolding when_def by auto
  then have 2:"?i = a * (\<Prod>va. f va ^ lookup (Poly_Mapping.single v n) va)"
    unfolding setsum_single[of "\<lambda>m. (a when Poly_Mapping.single v n = m) * (\<Prod>v. f v ^ lookup m v)" "Poly_Mapping.single k v"]
    by auto
  have "\<forall>v0. v0\<noteq>v \<longrightarrow> lookup (Poly_Mapping.single v n) v0 = 0" by (simp add: lookup_single_not_eq)
  then have "\<forall>va. va\<noteq>v \<longrightarrow> f va ^ lookup (Poly_Mapping.single v n) va = 1"  by simp
  then have "a * (\<Prod>va\<in>{v}. f va ^ lookup (Poly_Mapping.single v n) va) = ?i" unfolding 2
    using Prod_any.expand_superset[of "{v}" "\<lambda>va. f va ^ lookup (Poly_Mapping.single v n) va", simplified]
    by fastforce
  then show ?thesis by simp
qed

lemma insertion_single[simp]: "insertion f (monom (Poly_Mapping.single (v::nat) (n::nat)) a) = a * f v ^ n"
  using insertion_fun_single  Sum_any.cong insertion.rep_eq insertion_aux.rep_eq insertion_fun_def
  mapping_of_monom single.rep_eq by (metis (no_types, lifting))

lemma insertion_fun_irrelevant_vars:
fixes p::"((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow> 'a::comm_ring_1)"
assumes "\<And>m v. p m \<noteq> 0 \<Longrightarrow> lookup m v \<noteq> 0 \<Longrightarrow> f v = g v"
shows "insertion_fun f p = insertion_fun g p"
proof -
  {
    fix m::"nat\<Rightarrow>\<^sub>0nat"
    assume "p m \<noteq> 0"
    then have "(\<Prod>v. f v ^ lookup m v) = (\<Prod>v. g v ^ lookup m v)"
      using assms by (metis power_0)
  }
  then show ?thesis unfolding insertion_fun_def by (metis (no_types, lifting) mult_not_zero)
qed

lemma insertion_aux_irrelevant_vars:
fixes p::"((nat \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
assumes "\<And>m v. lookup p m \<noteq> 0 \<Longrightarrow> lookup m v \<noteq> 0 \<Longrightarrow> f v = g v"
shows "insertion_aux f p = insertion_aux g p"
  using insertion_fun_irrelevant_vars[of "lookup p" f g] assms
  by (metis insertion_aux.rep_eq)

lemma insertion_irrelevant_vars:
fixes p::"'a::comm_ring_1 mpoly"
assumes "\<And>v. v\<in>vars p \<Longrightarrow> f v = g v"
shows "insertion f p = insertion g p"
proof -
  {
    fix m v assume "lookup (mapping_of p) m \<noteq> 0" "lookup m v \<noteq> 0"
    then have "v \<in> vars p" unfolding vars_def by (meson UN_I lookup_not_eq_zero_eq_in_keys)
    then have "f v = g v" using assms by auto
  }
  then show ?thesis
    unfolding insertion_def using insertion_aux_irrelevant_vars[of "mapping_of p"]
    by (metis insertion.rep_eq insertion_def)
qed

section "Nested MPoly"

definition reduce_nested_mpoly::"'a::comm_ring_1 mpoly mpoly \<Rightarrow> 'a mpoly" where
  "reduce_nested_mpoly pp = insertion (\<lambda>v. monom (Poly_Mapping.single v 1) 1) pp"

lemma reduce_nested_mpoly_sum:
fixes p1::"'a::comm_ring_1 mpoly mpoly"
shows "reduce_nested_mpoly (p1 + p2) = reduce_nested_mpoly p1 + reduce_nested_mpoly p2"
  by (simp add: insertion_add reduce_nested_mpoly_def)

lemma reduce_nested_mpoly_prod:
fixes p1::"'a::comm_ring_1 mpoly mpoly"
shows "reduce_nested_mpoly (p1 * p2) = reduce_nested_mpoly p1 * reduce_nested_mpoly p2"
  by (simp add: insertion_mult reduce_nested_mpoly_def)

lemma reduce_nested_mpoly_0:
shows "reduce_nested_mpoly 0 = 0" by (simp add: reduce_nested_mpoly_def)

lemma insertion_nested_poly:
fixes pp::"'a::comm_ring_1 mpoly mpoly"
shows "insertion f (insertion (\<lambda>v. monom 0 (f v)) pp) = insertion f (reduce_nested_mpoly pp)"
proof (induction pp rule:mpoly_induct)
  case (monom m a)
  then show ?case
  proof (induction m arbitrary:a rule:poly_mapping_induct)
    case (single v n)
    show ?case unfolding reduce_nested_mpoly_def
      apply (simp add: insertion_mult monom_pow)
      using monom_pow[of 0 0 "f v" n] apply simp
      using insertion_single[of f 0 0] by auto
  next
    case (sum m1 m2 k v)
    then have "insertion f (insertion (\<lambda>v. monom 0 (f v)) (monom m1 a * monom m2 1))
             = insertion f (reduce_nested_mpoly (monom m1 a * monom m2 1))" unfolding reduce_nested_mpoly_prod insertion_mult by metis
    then show ?case using mult_monom[of m1 a m2 1] by auto
  qed
next
  case (sum p1 p2 m a)
  then show ?case by (simp add: reduce_nested_mpoly_sum insertion_add)
qed

definition extract_var::"'a::comm_ring_1 mpoly \<Rightarrow> nat \<Rightarrow> 'a::comm_ring_1 mpoly mpoly" where
"extract_var p v = (\<Sum>m. monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"

lemma extract_var_finite_set:
assumes "{m'. coeff p m' \<noteq> 0} \<subseteq> S"
assumes "finite S"
shows "extract_var p v = (\<Sum>m\<in>S. monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"
proof-
  {
    fix m' assume "coeff p m' = 0"
    then have "monom (remove_key v m') (monom (Poly_Mapping.single v (lookup m' v)) (coeff p m')) = 0"
      using monom.abs_eq monom_zero single_zero by metis
  }
  then have 0:"{a. monom (remove_key v a) (monom (Poly_Mapping.single v (lookup a v)) (coeff p a)) \<noteq> 0} \<subseteq> S"
    using \<open>{m'. coeff p m' \<noteq> 0} \<subseteq> S\<close> by fastforce
  then show ?thesis
    unfolding extract_var_def using Sum_any.expand_superset [OF \<open>finite S\<close> 0] by metis
qed

lemma extract_var_non_zero_coeff: "extract_var p v = (\<Sum>m\<in>{m'. coeff p m' \<noteq> 0}. monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"
  using extract_var_finite_set  coeff_def finite_lookup order_refl by (metis (no_types, lifting) Collect_cong sum.cong)

lemma extract_var_sum: "extract_var (p+p') v = extract_var p v + extract_var p' v"
proof -
  define S where "S = {m. coeff p m \<noteq> 0} \<union> {m. coeff p' m \<noteq> 0} \<union> {m. coeff (p+p') m \<noteq> 0}"
  have subsets:"{m. coeff p m \<noteq> 0} \<subseteq> S" "{m. coeff p' m \<noteq> 0} \<subseteq> S" "{m. coeff (p+p') m \<noteq> 0} \<subseteq> S"
    unfolding S_def by auto
  have "finite S" unfolding S_def using coeff_def finite_lookup
    by (metis (mono_tags) Collect_disj_eq finite_Collect_disjI)
  then show ?thesis  unfolding
    extract_var_finite_set[OF subsets(1) \<open>finite S\<close>]
    extract_var_finite_set[OF subsets(2) \<open>finite S\<close>]
    extract_var_finite_set[OF subsets(3) \<open>finite S\<close>]
    coeff_add[symmetric] monom_add sum.distrib
    by metis
qed



lemma extract_var_monom:
shows "extract_var (monom m a) v = monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) a)"
proof (cases "a = 0")
  assume "a \<noteq> 0"
  have 0:"{m'. coeff (monom m a) m' \<noteq> 0} = {m}"
    unfolding coeff_monom using \<open>a \<noteq> 0\<close> by auto
  show ?thesis
    unfolding extract_var_non_zero_coeff unfolding 0 unfolding coeff_monom
    using sum.insert[OF finite.emptyI, unfolded sum.empty add.right_neutral] when_def
    by auto
next
  assume "a = 0"
  have 0:"{m'. coeff (monom m a) m' \<noteq> 0} = {}"
    unfolding coeff_monom using \<open>a = 0\<close> by auto
  show ?thesis unfolding extract_var_non_zero_coeff 0
    using \<open>a = 0\<close> monom.abs_eq monom_zero sum.empty single_zero by (metis (no_types, lifting))
qed


lemma extract_var_monom_mult:
shows "extract_var (monom (m+m') (a*b)) v = extract_var (monom m a) v * extract_var (monom m' b) v"
unfolding extract_var_monom remove_key_add lookup_add single_add mult_monom by auto

lemma extract_var_single: "extract_var (monom (Poly_Mapping.single v n) a) v = monom 0 (monom (Poly_Mapping.single v n) a)"
unfolding extract_var_monom by simp

lemma extract_var_single':
assumes "v \<noteq> v'"
shows "extract_var (monom (Poly_Mapping.single v n) a) v' = monom (Poly_Mapping.single v n) (monom 0 a)"
unfolding extract_var_monom using assms by (metis add.right_neutral lookup_single_not_eq remove_key_sum single_zero)

lemma reduce_nested_mpoly_extract_var:
fixes p::"'a::comm_ring_1 mpoly"
shows "reduce_nested_mpoly (extract_var p v) = p"
proof (induction p rule:mpoly_induct)
  case (monom m a)
  then show ?case
  proof (induction m arbitrary:a rule:poly_mapping_induct)
    case (single v' n)
    show ?case
    proof (cases "v' = v")
      case True
      then show ?thesis
        by (metis (no_types, lifting) insertion_single mult.right_neutral power_0
        reduce_nested_mpoly_def single_zero extract_var_single)
    next
      case False
      then show ?thesis unfolding extract_var_single'[OF False] reduce_nested_mpoly_def insertion_single
        by (simp add: monom_pow mult_monom)
    qed
  next
    case (sum m m' v n a)
    then show ?case
      using extract_var_monom_mult[of m m' a 1] reduce_nested_mpoly_prod by (metis mult.right_neutral mult_monom)
  qed
next
  case (sum p1 p2 m a)
  then show ?case unfolding extract_var_sum reduce_nested_mpoly_sum by auto
qed


lemma vars_extract_var_subset: "vars (extract_var p v) \<subseteq> vars p"
proof
  have "finite {m'. coeff p m' \<noteq> 0}" by (simp add: coeff_def)
  fix x assume "x \<in> vars (extract_var p v)"
  then have "x \<in> vars (\<Sum>m\<in>{m'. coeff p m' \<noteq> 0}. monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"
    unfolding extract_var_non_zero_coeff by metis
  then have "x \<in> (\<Union>m\<in>{m'. coeff p m' \<noteq> 0}. vars (monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m))))"
    using vars_setsum[OF \<open>finite {m'. coeff p m' \<noteq> 0}\<close>] by auto
  then obtain m where "m\<in>{m'. coeff p m' \<noteq> 0}" "x \<in> vars (monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"
    by blast
  show "x \<in> vars p" by (metis (mono_tags, lifting) DiffD1 UN_I \<open>m \<in> {m'. coeff p m' \<noteq> 0}\<close>
    \<open>x \<in> vars (monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))\<close>
    coeff_keys mem_Collect_eq remove_key_keys subsetCE vars_def vars_monom_subset)
qed

lemma v_not_in_vars_extract_var: "v \<notin> vars (extract_var p v)"
proof -
  have "finite {m'. coeff p m' \<noteq> 0}" by (simp add: coeff_def)
  have "\<And>m. m\<in>{m'. coeff p m' \<noteq> 0} \<Longrightarrow> v \<notin> vars (monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m)))"
    by (metis Diff_iff remove_key_keys singletonI subsetCE vars_monom_subset)
  then have "v \<notin> (\<Union>m\<in>{m'. coeff p m' \<noteq> 0}. vars (monom (remove_key v m) (monom (Poly_Mapping.single v (lookup m v)) (coeff p m))))"
    by simp
  then show ?thesis
   unfolding extract_var_non_zero_coeff using vars_setsum[OF \<open>finite {m'. coeff p m' \<noteq> 0}\<close>] by blast
qed

lemma vars_coeff_extract_var: "vars (coeff (extract_var p v) j) \<subseteq> {v}"
proof (induction p rule:mpoly_induct)
  case (monom m a)
  then show ?case unfolding extract_var_monom coeff_monom vars_monom_single_cases
    by (metis monom_zero single_zero vars_monom_single when_def)
next
  case (sum p1 p2 m a)
  then show ?case unfolding extract_var_sum coeff_add[symmetric]
    by (metis (no_types, lifting) Un_insert_right insert_absorb2 subset_insertI2 subset_singletonD sup_bot.right_neutral vars_add)
qed

definition replace_coeff
where "replace_coeff f p = MPoly (Abs_poly_mapping (\<lambda>m. f (lookup (mapping_of p) m)))"

lemma coeff_replace_coeff:
assumes "f 0 = 0"
shows "coeff (replace_coeff f p) m = f (coeff p m)"
proof -
  have 0:"finite {m. f (lookup (mapping_of p) m) \<noteq> 0}"
    unfolding coeff_def[symmetric] by (metis (mono_tags, lifting) Collect_mono assms(1) coeff_def finite_lookup finite_subset)+
  then show ?thesis unfolding replace_coeff_def coeff_def using lookup_Abs_poly_mapping[OF 0]
    by (metis (mono_tags, lifting) Quotient_mpoly Quotient_rep_abs_fold_unmap)
qed

lemma replace_coeff_monom:
assumes "f 0 = 0"
shows "replace_coeff f (monom m a) = monom m (f a)"
  unfolding replace_coeff_def
  unfolding  mapping_of_inject[symmetric] lookup_inject[symmetric] apply (rule HOL.ext)
  unfolding lookup_single  mapping_of_monom fun_when[of f, OF \<open>f 0 = 0\<close>]
  by (metis coeff_def coeff_monom lookup_single lookup_single_not_eq monom.abs_eq single.abs_eq)

lemma replace_coeff_add:
assumes "f 0 = 0"
assumes "\<And>a b. f (a+b) = f a + f b"
shows "replace_coeff f (p1 + p2) = replace_coeff f p1 + replace_coeff f p2"
proof -
  have "finite {m. f (lookup (mapping_of p1) m) \<noteq> 0}"
       "finite {m. f (lookup (mapping_of p2) m) \<noteq> 0}"
    unfolding coeff_def[symmetric] by (metis (mono_tags, lifting) Collect_mono assms(1) coeff_def finite_lookup finite_subset)+
  then show ?thesis
    unfolding replace_coeff_def plus_mpoly.rep_eq unfolding Poly_Mapping.plus_poly_mapping.rep_eq
    unfolding assms(2) plus_mpoly.abs_eq using Poly_Mapping.plus_poly_mapping.abs_eq[unfolded eq_onp_def] by fastforce
qed

lemma insertion_replace_coeff:
fixes pp::"'a::comm_ring_1 mpoly mpoly"
shows "insertion f (replace_coeff (insertion f) pp) = insertion f (reduce_nested_mpoly pp)"
proof (induction pp rule:mpoly_induct)
  case (monom m a)
  then show ?case
  proof (induction m arbitrary:a rule:poly_mapping_induct)
    case (single v n)
    show ?case unfolding reduce_nested_mpoly_def  unfolding replace_coeff_monom[of "insertion f", OF insertion_zero]
      insertion_single insertion_mult using insertion_single by (simp add: monom_pow)
  next
    case (sum m1 m2 k v)
    have "replace_coeff (insertion f) (monom m1 a * monom m2 1) = replace_coeff (insertion f) (monom m1 a) * replace_coeff (insertion f) (monom m2 1)"
      by (simp add: mult_monom replace_coeff_monom)
    then have "insertion f (replace_coeff (insertion f) (monom m1 a * monom m2 1)) = insertion f (reduce_nested_mpoly (monom m1 a * monom m2 1))"
      unfolding reduce_nested_mpoly_prod insertion_mult
      by (simp add: insertion_mult sum.IH(1) sum.IH(2))
    then show ?case using mult_monom[of m1 a m2 1] by auto
  qed
next
  case (sum p1 p2 m a)
  then show ?case using reduce_nested_mpoly_sum insertion_add
    replace_coeff_add[of "insertion f", OF insertion_zero insertion_add] by metis
qed

lemma replace_coeff_extract_var_cong:
assumes "f v = g v"
shows "replace_coeff (insertion f) (extract_var p v) = replace_coeff (insertion g) (extract_var p v)"
  by (induction p rule:mpoly_induct;simp add: assms extract_var_monom replace_coeff_monom
  extract_var_sum insertion_add replace_coeff_add)

lemma vars_replace_coeff:
assumes "f 0 = 0"
shows "vars (replace_coeff f p) \<subseteq> vars p"
  unfolding vars_def apply (rule subsetI) unfolding mem_simps(8) coeff_keys
  using assms coeff_replace_coeff by (metis coeff_keys)

(* Polynomial functions *)

definition polyfun :: "nat set \<Rightarrow> ((nat \<Rightarrow> 'a::comm_semiring_1) \<Rightarrow> 'a) \<Rightarrow> bool"
  where "polyfun N f = (\<exists>p. vars p \<subseteq> N \<and> (\<forall>x. insertion x p = f x))"

lemma polyfunI: "(\<And>P. (\<And>p. vars p \<subseteq> N \<Longrightarrow> (\<And>x. insertion x p = f x) \<Longrightarrow> P) \<Longrightarrow> P) \<Longrightarrow> polyfun N f"
  unfolding polyfun_def by metis

lemma polyfun_subset: "N\<subseteq>N' \<Longrightarrow> polyfun N f \<Longrightarrow> polyfun N' f"
  unfolding polyfun_def by blast

lemma polyfun_const: "polyfun N (\<lambda>_. c)"
proof -
  have "\<And>x. insertion x (monom 0 c) = c" using insertion_single by (metis insertion_one monom_one mult.commute mult.right_neutral single_zero)
  then show ?thesis unfolding polyfun_def by (metis (full_types) empty_iff keys_single single_zero subsetI subset_antisym vars_monom_subset)
qed

lemma polyfun_add:
assumes "polyfun N f" "polyfun N g"
shows "polyfun N (\<lambda>x. f x + g x)"
proof -
  obtain p1 p2 where "vars p1 \<subseteq> N" "\<forall>x. insertion x p1 = f x"
                     "vars p2 \<subseteq> N" "\<forall>x. insertion x p2 = g x"
    using polyfun_def assms by metis
  then have "vars (p1 + p2) \<subseteq> N" "\<forall>x. insertion x (p1 + p2) = f x + g x"
    using vars_add using Un_iff subsetCE subsetI apply blast
    by (simp add: \<open>\<forall>x. insertion x p1 = f x\<close> \<open>\<forall>x. insertion x p2 = g x\<close> insertion_add)
  then show ?thesis using polyfun_def by blast
qed

lemma polyfun_mult:
assumes "polyfun N f" "polyfun N g"
shows "polyfun N (\<lambda>x. f x * g x)"
proof -
  obtain p1 p2 where "vars p1 \<subseteq> N" "\<forall>x. insertion x p1 = f x"
                     "vars p2 \<subseteq> N" "\<forall>x. insertion x p2 = g x"
    using polyfun_def assms by metis
  then have "vars (p1 * p2) \<subseteq> N" "\<forall>x. insertion x (p1 * p2) = f x * g x"
    using vars_mult using Un_iff subsetCE subsetI apply blast
    by (simp add: \<open>\<forall>x. insertion x p1 = f x\<close> \<open>\<forall>x. insertion x p2 = g x\<close> insertion_mult)
  then show ?thesis using polyfun_def by blast
qed

lemma polyfun_Sum:
assumes "finite I"
assumes "\<And>i. i\<in>I \<Longrightarrow> polyfun N (f i)"
shows "polyfun N (\<lambda>x. \<Sum>i\<in>I. f i x)"
  using assms
  apply (induction I rule:finite_induct)
  apply (simp add: polyfun_const)
  using comm_monoid_add_class.sum.insert polyfun_add by fastforce

lemma polyfun_Prod:
assumes "finite I"
assumes "\<And>i. i\<in>I \<Longrightarrow> polyfun N (f i)"
shows "polyfun N (\<lambda>x. \<Prod>i\<in>I. f i x)"
  using assms
  apply (induction I rule:finite_induct)
  apply (simp add: polyfun_const)
  using comm_monoid_add_class.sum.insert polyfun_mult by fastforce

lemma polyfun_single:
assumes "i\<in>N"
shows "polyfun N (\<lambda>x. x i)"
proof -
  have "\<forall>f. insertion f (monom (Poly_Mapping.single i 1) 1) = f i" using insertion_single by simp
  then show ?thesis unfolding polyfun_def
    using vars_monom_single[of i 1 1] One_nat_def assms singletonD subset_eq
    by blast
qed

end
