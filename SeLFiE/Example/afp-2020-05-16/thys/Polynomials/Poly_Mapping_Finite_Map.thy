(* Author: Fabian Immler, TU Muenchen
*)
theory Poly_Mapping_Finite_Map
  imports
    "More_MPoly_Type"
    "HOL-Library.Finite_Map"
begin

subsection \<open>TODO: move!\<close>

lemma fmdom'_fmap_of_list: "fmdom' (fmap_of_list xs) = set (map fst xs)"
  by (auto simp: fmdom'_def fmdom'I fmap_of_list.rep_eq weak_map_of_SomeI)
    (metis map_of_eq_None_iff option.distinct(1))


text \<open>In this theory, type @{typ "('a, 'b) poly_mapping"} is represented as association lists.
  Code equations are proved in order actually perform computations (addition, multiplication, etc.).\<close>

subsection \<open>Utilities\<close>

instantiation poly_mapping :: (type, "{equal, zero}") equal
begin
definition equal_poly_mapping::"('a, 'b) poly_mapping \<Rightarrow> ('a, 'b) poly_mapping \<Rightarrow> bool" where
  "equal_poly_mapping p q \<equiv> (\<forall>t. lookup p t = lookup q t)"

instance by standard (auto simp add: equal_poly_mapping_def poly_mapping_eqI)
end

definition "clearjunk0 m = fmfilter (\<lambda>k. fmlookup m k \<noteq> Some 0) m"

definition "fmlookup_default d m x = (case fmlookup m x of Some v \<Rightarrow> v | None \<Rightarrow> d)"
abbreviation "lookup0 \<equiv> fmlookup_default 0"

lemma fmlookup_default_fmmap:
  "fmlookup_default d (fmmap f M) x = (if x \<in> fmdom' M then f (fmlookup_default d M x) else d)"
  by (auto simp: fmlookup_default_def fmdom'_notI split: option.splits)

lemma fmlookup_default_fmmap_keys: "fmlookup_default d (fmmap_keys f M) x =
  (if x \<in> fmdom' M then f x (fmlookup_default d M x) else d)"
  by (auto simp: fmlookup_default_def fmdom'_notI split: option.splits)

lemma fmlookup_default_add[simp]:
  "fmlookup_default d (m ++\<^sub>f n) x =
    (if x |\<in>| fmdom n then the (fmlookup n x)
    else fmlookup_default d m x)"
  by (auto simp: fmlookup_default_def)

lemma fmlookup_default_if[simp]:
  "fmlookup ys a = Some r \<Longrightarrow> fmlookup_default d ys a = r"
  "fmlookup ys a = None \<Longrightarrow> fmlookup_default d ys a = d"
  by (auto simp: fmlookup_default_def)

lemma finite_lookup_default:
  "finite {x. fmlookup_default d xs x \<noteq> d}"
proof -
  have "{x. fmlookup_default d xs x \<noteq> d} \<subseteq> fmdom' xs"
    by (auto simp: fmlookup_default_def fmdom'I split: option.splits)
  also have "finite \<dots>"
    by simp
  finally (finite_subset) show ?thesis .
qed

lemma lookup0_clearjunk0: "lookup0 xs s = lookup0 (clearjunk0 xs) s"
  unfolding clearjunk0_def fmlookup_default_def
  by auto

lemma clearjunk0_nonzero:
  assumes "t \<in> fmdom' (clearjunk0 xs)"
  shows "fmlookup xs t \<noteq> Some 0"
  using assms unfolding clearjunk0_def by simp

lemma clearjunk0_map_of_SomeD:
  assumes a1: "fmlookup xs t = Some c" and "c \<noteq> 0"
  shows "t \<in> fmdom' (clearjunk0 xs)"
  using assms
  by (auto simp: clearjunk0_def fmdom'I)


subsection \<open>Implementation of Polynomial Mappings as Association Lists\<close>

lift_definition Pm_fmap::"('a, 'b::zero) fmap \<Rightarrow> 'a \<Rightarrow>\<^sub>0 'b" is lookup0
  by (rule finite_lookup_default)

lemmas [simp] = Pm_fmap.rep_eq

code_datatype Pm_fmap

lemma PM_clearjunk0_cong:
  "Pm_fmap (clearjunk0 xs) = Pm_fmap xs"
  by (metis Pm_fmap.rep_eq lookup0_clearjunk0 poly_mapping_eqI)

lemma PM_all_2:
  assumes "P 0 0"
  shows "(\<forall>x. P (lookup (Pm_fmap xs) x) (lookup (Pm_fmap ys) x)) =
    fmpred (\<lambda>k v. P (lookup0 xs k) (lookup0 ys k)) (xs ++\<^sub>f ys)"
  using assms unfolding list_all_def
  by (force simp: fmlookup_default_def fmlookup_dom_iff
      split: option.splits if_splits)

lemma compute_keys_pp[code]: "keys (Pm_fmap xs) = fmdom' (clearjunk0 xs)"
  by transfer
    (auto simp: fmlookup_dom'_iff clearjunk0_def fmlookup_default_def fmdom'I split: option.splits)

lemma compute_zero_pp[code]: "0 = Pm_fmap fmempty"
  by (auto intro!: poly_mapping_eqI simp: fmlookup_default_def)

lemma compute_plus_pp [code]:
  "Pm_fmap xs + Pm_fmap ys = Pm_fmap (clearjunk0 (fmmap_keys (\<lambda>k v. lookup0 xs k + lookup0 ys k) (xs ++\<^sub>f ys)))"
  by (auto intro!: poly_mapping_eqI
      simp: fmlookup_default_def lookup_add fmlookup_dom_iff PM_clearjunk0_cong
      split: option.splits)

lemma compute_lookup_pp[code]:
  "lookup (Pm_fmap xs) x = lookup0 xs x"
  by (transfer, simp)

lemma compute_minus_pp [code]:
  "Pm_fmap xs - Pm_fmap ys = Pm_fmap (clearjunk0 (fmmap_keys (\<lambda>k v. lookup0 xs k - lookup0 ys k) (xs ++\<^sub>f ys)))"
  by (auto intro!: poly_mapping_eqI
      simp: fmlookup_default_def lookup_minus fmlookup_dom_iff PM_clearjunk0_cong
      split: option.splits)

lemma compute_uminus_pp[code]:
  "- Pm_fmap ys = Pm_fmap (fmmap_keys (\<lambda>k v. - lookup0 ys k) ys)"
  by (auto intro!: poly_mapping_eqI
      simp: fmlookup_default_def
      split: option.splits)

lemma compute_equal_pp[code]:
  "equal_class.equal (Pm_fmap xs) (Pm_fmap ys) = fmpred (\<lambda>k v. lookup0 xs k = lookup0 ys k) (xs ++\<^sub>f ys)"
  unfolding equal_poly_mapping_def by (simp only: PM_all_2)

lemma compute_map_pp[code]:
  "Poly_Mapping.map f (Pm_fmap xs) = Pm_fmap (fmmap (\<lambda>x. f x when x \<noteq> 0) xs)"
  by (auto intro!: poly_mapping_eqI
      simp: fmlookup_default_def map.rep_eq
      split: option.splits)

lemma fmran'_fmfilter_eq: "fmran' (fmfilter p fm) = {y | y. \<exists>x \<in> fmdom' fm. p x \<and> fmlookup fm x = Some y}"
  by (force simp: fmlookup_ran'_iff fmdom'I split: if_splits)

lemma compute_range_pp[code]:
  "Poly_Mapping.range (Pm_fmap xs) = fmran' (clearjunk0 xs)"
  by (force simp: range.rep_eq clearjunk0_def fmran'_fmfilter_eq fmdom'I
      fmlookup_default_def split: option.splits)

subsubsection \<open>Constructors\<close>

definition "sparse\<^sub>0 xs = Pm_fmap (fmap_of_list xs)" \<comment>\<open>sparse representation\<close>
definition "dense\<^sub>0 xs = Pm_fmap (fmap_of_list (zip [0..<length xs] xs))" \<comment>\<open>dense representation\<close>

lemma compute_single[code]: "Poly_Mapping.single k v = sparse\<^sub>0 [(k, v)]"
  by (auto simp: sparse\<^sub>0_def fmlookup_default_def lookup_single intro!: poly_mapping_eqI )

end
