theory Compiler_Utils
imports
  "HOL-Library.Monad_Syntax"
  "HOL-Library.FSet"
  "HOL-Library.Finite_Map"
begin

section \<open>Miscellaneous\<close>

notation undefined ("\<^undefined>")

lemma distinct_sorted_list_of_fset[simp, intro]: "distinct (sorted_list_of_fset S)"
including fset.lifting
by transfer (rule distinct_sorted_list_of_set)

lemma sum_nat_le_single:
  fixes x :: nat
  assumes y: "y \<in> S" and x: "x \<le> f y" and finite: "finite S"
  shows "x \<le> sum f S"
proof -
  have "sum f S = sum f (insert y S)"
    using y by (metis insert_absorb)
  with finite have "sum f S = f y + sum f (S - {y})"
    by (metis sum.insert_remove)
  with x show ?thesis
    by linarith
qed

lemma sum_nat_less_single:
  fixes x :: nat
  assumes y: "y \<in> S" and x: "x < f y" and finite: "finite S"
  shows "x < sum f S"
proof -
  have "sum f S = sum f (insert y S)"
    using y by (metis insert_absorb)
  with finite have "sum f S = f y + sum f (S - {y})"
    by (metis sum.insert_remove)
  with x show ?thesis
    by linarith
qed

lemma prod_BallI: "(\<And>a b. (a, b) \<in> M \<Longrightarrow> P a b) \<Longrightarrow> Ball M (\<lambda>(a, b). P a b)"
by auto

lemma fset_map_snd_id:
  assumes "\<And>a b e. (a, b) \<in> fset cs \<Longrightarrow> f a b = b"
  shows "(\<lambda>(a, b). (a, f a b)) |`| cs = cs"
proof -
  have "(\<lambda>(a, b). (a, f a b)) |`| cs = id |`| cs"
    proof (rule fset.map_cong0, safe)
      fix a b
      assume "(a, b) \<in> fset cs"
      hence "f a b = b"
        using assms by auto
      thus "(a, f a b) = id (a, b)"
        by simp
    qed
  thus ?thesis
    by simp
qed

lemmas disj_cases = disjE[case_names 1 2, consumes 1]

lemma case_prod_twice: "case_prod f (case_prod (\<lambda>a b. (g a b, h a b)) x) = case_prod (\<lambda>a b. f (g a b) (h a b)) x"
by (simp add: split_beta)

lemma map_of_map_keyed:
  "map_of (map (\<lambda>(k, v). (k, f k v)) xs) = (\<lambda>k. map_option (f k) (map_of xs k))"
  by (induction xs) (auto simp: fun_eq_iff)

locale rekey =
  fixes f :: "'a \<Rightarrow> 'b"
  assumes bij: "bij f"
begin

lemma map_of_rekey:
  "map_of (map (\<lambda>(k, v). (f k, g k v)) xs) k = map_option (g (inv f k)) (map_of xs (inv f k))"
using bij
by (induction xs) (auto simp: bij_def surj_f_inv_f)

lemma map_of_rekey': "map_of (map (map_prod f g) xs) k = map_option g (map_of xs (inv f k))"
unfolding map_prod_def
by (rule map_of_rekey)

lemma fst_distinct: "distinct (map fst xs) \<Longrightarrow> distinct (map (\<lambda>(k, _). f k) xs)"
proof (induction xs)
  case Cons
  thus ?case
    apply (auto split: prod.splits)
    using bij unfolding bij_def
    by (metis fst_conv injD rev_image_eqI)
qed auto

lemma inv: "rekey (inv f)"
apply standard
using bij
by (simp add: bij_imp_bij_inv)

end

section \<open>Finite sets\<close>

lemma fset_eq_empty_iff: "M = {||} \<longleftrightarrow> (\<forall>x. x |\<notin>| M)"
by auto

context
  includes fset.lifting
begin

lemma fbind_subset_eqI: "fBall S (\<lambda>s. f s |\<subseteq>| T) \<Longrightarrow> fbind S f |\<subseteq>| T"
by transfer' fastforce

lemma prod_fBallI: "(\<And>a b. (a, b) |\<in>| M \<Longrightarrow> P a b) \<Longrightarrow> fBall M (\<lambda>(a, b). P a b)"
by transfer (rule prod_BallI)

lemma ffUnion_subset_elem: "x |\<in>| X \<Longrightarrow> x |\<subseteq>| ffUnion X"
including fset.lifting
by transfer auto

lemma fbindE:
  assumes "x |\<in>| fbind S f"
  obtains s where "x |\<in>| f s" "s |\<in>| S"
using assms by transfer' auto

lemma ffUnion_least_rev: "ffUnion A |\<subseteq>| C \<Longrightarrow> fBall A (\<lambda>X. X |\<subseteq>| C)"
by transfer blast

lemma inj_on_fimage_set_diff:
  assumes "inj_on f (fset C)" "A |\<subseteq>| C" "B |\<subseteq>| C"
  shows "f |`| (A - B) = f |`| A - f |`| B"
using assms
by transfer (meson Diff_subset inj_on_image_set_diff order_trans)

lemma list_all_iff_fset: "list_all P xs \<longleftrightarrow> fBall (fset_of_list xs) P"
by transfer (rule list_all_iff)

lemma fbind_fun_funion: "fbind M (\<lambda>x. f x |\<union>| g x) = fbind M f |\<union>| fbind M g"
by transfer' auto

end

lemma funion_strictE:
  assumes "c |\<in>| A |\<union>| B"
  obtains (A) "c |\<in>| A" | (B) "c |\<notin>| A" "c |\<in>| B"
using assms by auto

lemma max_decr:
  fixes X :: "nat set"
  assumes "\<exists>x \<in> X. x \<ge> k" "finite X"
  shows "Max ((\<lambda>x. x - k) ` X) = Max X - k"
proof (rule mono_Max_commute[symmetric])
  show "mono (\<lambda>x. x - k)"
    by (rule monoI) linarith
  show "finite X"
    by fact
  show "X \<noteq> {}"
    using assms by auto
qed

lemma max_ex_gr: "\<exists>x \<in> X. k < x \<Longrightarrow> finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> k < Max X"
by (simp add: Max_gr_iff)

context includes fset.lifting begin

lemma fmax_decr:
  fixes X :: "nat fset"
  assumes "fBex X (\<lambda>x. x \<ge> k)"
  shows "fMax ((\<lambda>x. x - k) |`| X) = fMax X - k"
using assms by transfer (rule max_decr)

lemma fmax_ex_gr: "fBex X (\<lambda>x. k < x) \<Longrightarrow> X \<noteq> {||} \<Longrightarrow> k < fMax X"
by transfer (rule max_ex_gr)

lemma fMax_le: "fBall M (\<lambda>x. x \<le> k) \<Longrightarrow> M \<noteq> {||} \<Longrightarrow> fMax M \<le> k"
by transfer auto

end

section \<open>Sets\<close>

subsection \<open>Code setup trickery\<close>

definition compress :: "'a set \<Rightarrow> 'a set" where
"compress = id"

lemma [code]: "compress (set xs) = set (remdups xs)"
unfolding compress_def id_apply by simp

definition the_elem' :: "'a::linorder set \<Rightarrow> 'a" where
"the_elem' S = the_elem (set (sorted_list_of_set S))"

lemma the_elem_id: "finite S \<Longrightarrow> the_elem' S = the_elem S"
unfolding the_elem'_def
by auto

context
  includes fset.lifting
begin

lift_definition fcompress :: "'a fset \<Rightarrow> 'a fset" is compress
unfolding compress_def by simp

lemma fcompress_eq[simp]: "fcompress M = M"
by transfer' (auto simp: compress_def)

lift_definition fthe_elem' :: "'a::linorder fset \<Rightarrow> 'a" is the_elem' .

lemma fthe_elem'_eq: "fthe_elem' = fthe_elem"
proof
  fix S :: "'a fset"
  show "fthe_elem' S = fthe_elem S"
    by transfer (fastforce intro: the_elem_id)
qed

end


subsection \<open>@{type set}s as maps\<close>

definition is_map :: "('a \<times> 'b) set \<Rightarrow> bool" where
"is_map M = Ball M (\<lambda>(a\<^sub>1, b\<^sub>1). Ball M (\<lambda>(a\<^sub>2, b\<^sub>2). a\<^sub>1 = a\<^sub>2 \<longrightarrow> b\<^sub>1 = b\<^sub>2))"

lemma is_mapI[intro]:
  assumes "\<And>a b\<^sub>1 b\<^sub>2. (a, b\<^sub>1) \<in> M \<Longrightarrow> (a, b\<^sub>2) \<in> M \<Longrightarrow> b\<^sub>1 = b\<^sub>2"
  shows "is_map M"
using assms unfolding is_map_def by auto

lemma distinct_is_map:
  assumes "distinct (map fst m)"
  shows "is_map (set m)"
using assms
by (metis Some_eq_map_of_iff is_mapI option.inject)

lemma is_map_image:
  assumes "is_map M"
  shows "is_map ((\<lambda>(a, b). (a, f a b)) ` M)"
using assms unfolding is_map_def by auto

lemma is_mapD:
  assumes "is_map M" "(a, b\<^sub>1) \<in> M" "(a, b\<^sub>2) \<in> M"
  shows "b\<^sub>1 = b\<^sub>2"
using assms unfolding is_map_def by auto

lemma is_map_subset: "is_map N \<Longrightarrow> M \<subseteq> N \<Longrightarrow> is_map M"
unfolding is_map_def by blast

lemma map_of_is_map: "(k, v) \<in> set m \<Longrightarrow> is_map (set m) \<Longrightarrow> map_of m k = Some v"
by (metis is_mapD map_of_SomeD weak_map_of_SomeI)

definition get_map :: "('a \<times> 'b) set \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b)" where
"get_map M k = the_elem (Set.filter (\<lambda>(k', _). k = k') M)"

lemma get_map_elem:
  assumes "is_map M"
  assumes "(k, v) \<in> M"
  shows "get_map M k = (k, v)"
proof -
  from assms have "Set.filter (\<lambda>(k', _). k = k') M = {(k, v)}"
    unfolding is_map_def by fastforce
  thus ?thesis
    unfolding get_map_def by simp
qed

lemma get_map_map:
  assumes "is_map S" "k \<in> fst ` S"
  shows "get_map ((\<lambda>(a, b). (a, f a b)) ` S) k = (case get_map S k of (a, b) \<Rightarrow> (a, f a b))"
proof -
  from assms obtain v where "(k, v) \<in> S"
    by force
  hence "get_map S k = (k, v)"
    using assms by (simp add: get_map_elem)

  have "(k, f k v) \<in> (\<lambda>(a, b). (a, f a b)) ` S"
    using \<open>(k, v) \<in> S\<close> by auto
  hence "get_map ((\<lambda>(a, b). (a, f a b)) ` S) k = (k, f k v)"
    using assms by (metis get_map_elem is_map_image) (* takes long *)

  show ?thesis
    unfolding \<open>get_map S k = _\<close> \<open>get_map (_ ` S) k = _\<close>
    by simp
qed

lemma is_map_fst_inj: "is_map S \<Longrightarrow> inj_on fst S"
by (fastforce intro: inj_onI dest: is_mapD)

context
  includes fset.lifting
begin

lemma is_map_transfer:
  fixes A :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
  assumes [transfer_rule]: "bi_unique A"
  shows "rel_fun (rel_set (rel_prod (=) A)) (=) is_map is_map"
unfolding is_map_def[abs_def]
by transfer_prover

lift_definition is_fmap :: "('a \<times> 'b) fset \<Rightarrow> bool" is is_map parametric is_map_transfer .

lemma is_fmapI[intro]:
  assumes "\<And>a b\<^sub>1 b\<^sub>2. (a, b\<^sub>1) |\<in>| M \<Longrightarrow> (a, b\<^sub>2) |\<in>| M \<Longrightarrow> b\<^sub>1 = b\<^sub>2"
  shows "is_fmap M"
using assms by transfer' auto

lemma is_fmap_image: "is_fmap M \<Longrightarrow> is_fmap ((\<lambda>(a, b). (a, f a b)) |`| M)"
by transfer' (rule is_map_image)

lemma is_fmapD:
  assumes "is_fmap M" "(a, b\<^sub>1) |\<in>| M" "(a, b\<^sub>2) |\<in>| M"
  shows "b\<^sub>1 = b\<^sub>2"
using assms by transfer' (rule is_mapD)

lemma is_fmap_subset: "is_fmap N \<Longrightarrow> M |\<subseteq>| N \<Longrightarrow> is_fmap M"
by transfer' (rule is_map_subset)

end


subsection \<open>Conversion into sorted lists\<close>

definition ordered_map :: "('a::linorder \<times> 'b) set \<Rightarrow> ('a \<times> 'b) list" where
"ordered_map S = map (get_map S) (sorted_list_of_set (fst ` S))"

lemma ordered_map_set_eq:
  assumes "finite S" "is_map S"
  shows "set (ordered_map S) = S"
proof -
  have "set (ordered_map S) = get_map S ` set (sorted_list_of_set (fst ` S))"
    unfolding ordered_map_def by simp
  also have "\<dots> = get_map S ` (fst ` S)"
    using assms by (auto simp: sorted_list_of_set)
  also have "\<dots> = (get_map S \<circ> fst) ` S"
    unfolding o_def by auto
  also have "\<dots> = id ` S"
    using assms
    by (force simp: get_map_elem)
  finally show ?thesis
    by simp
qed

lemma ordered_map_image:
  assumes "finite S" "is_map S"
  shows "map (\<lambda>(a, b). (a, f a b)) (ordered_map S) = ordered_map ((\<lambda>(a, b). (a, f a b)) ` S)"
using assms
unfolding ordered_map_def list.map_comp image_comp
by (auto simp: fst_def[abs_def] comp_def case_prod_twice get_map_map)

lemma ordered_map_distinct:
  assumes "finite S" "is_map S"
  shows "distinct (map fst (ordered_map S))"
proof -
  have "inj_on (fst \<circ> get_map S) (set (sorted_list_of_set (fst ` S)))"
    apply rule
    using sorted_list_of_set assms(1)
    apply simp
    apply (erule imageE)
    apply (erule imageE)
    subgoal for x y x' y'
      apply (cases x', cases y')
      apply simp
      apply (subst (asm) get_map_elem)
        apply (rule assms)
       apply assumption
      apply (subst (asm) get_map_elem)
        apply (rule assms)
       apply assumption
      apply simp
      done
    done
  then show ?thesis
    unfolding ordered_map_def
    by (auto intro: distinct_sorted_list_of_set simp: distinct_map)
qed

lemma ordered_map_keys:
  assumes "finite S" "is_map S"
  shows "map fst (ordered_map S) = sorted_list_of_set (fst ` S)"
proof -
  have "fst (get_map S z) = z" if "z \<in> fst ` S" for z
    using assms that by (fastforce simp: get_map_elem)
  moreover have "set (sorted_list_of_set (fst ` S)) = fst ` S"
    using assms by (force simp: sorted_list_of_set)
  ultimately show ?thesis
    unfolding ordered_map_def
    by (metis (no_types, lifting) map_idI map_map o_apply)
qed

corollary ordered_map_sound:
  assumes "is_map S" "finite S" "(a, b) \<in> set (ordered_map S)"
  shows "(a, b) \<in> S"
using assms by (metis ordered_map_set_eq)

lemma ordered_map_nonempty:
  assumes "is_map S" "ordered_map S \<noteq> []" "finite S"
  shows "S \<noteq> {}"
using assms unfolding ordered_map_def by auto

lemma ordered_map_remove:
  assumes "is_map S" "finite S" "x \<in> S"
  shows "ordered_map (S - {x}) = remove1 x (ordered_map S)"
proof -
  have distinct: "distinct (sorted_list_of_set (fst ` S))"
    using assms
    by (fastforce simp: sorted_list_of_set)

  have "inj_on (get_map S) (fst ` S)"
    using assms
    by (fastforce simp: get_map_elem intro: inj_onI)

  hence inj: "inj_on (get_map S) (set (sorted_list_of_set (fst ` S)))"
    using assms
    by (simp add: sorted_list_of_set)

  have "ordered_map (S - {x}) = map (get_map (S - {x})) (sorted_list_of_set (fst ` (S - {x})))"
    unfolding ordered_map_def by simp
  also have "\<dots> = map (get_map (S - {x})) (sorted_list_of_set (fst ` S - {fst x}))"
    proof (subst inj_on_image_set_diff)
      show "inj_on fst S"
        by (rule is_map_fst_inj) fact
    next
      show "{x} \<subseteq> S"
        using assms by simp
    qed auto
  also have "\<dots> = map (get_map (S - {x})) (remove1 (fst x) (sorted_list_of_set (fst ` S)))"
    proof (subst sorted_list_of_set_remove)
      show "finite (fst ` S)"
        using assms by simp
    qed simp
  also have "\<dots> = map (get_map S) (remove1 (fst x) (sorted_list_of_set (fst ` S)))"
    proof (rule list.map_cong0)
      fix z
      assume "z \<in> set (remove1 (fst x) (sorted_list_of_set (fst ` S)))"
      with distinct have "z \<noteq> fst x"
        by simp
      thus "get_map (S - {x}) z = get_map S z"
        unfolding get_map_def Set.filter_def
        by (metis (full_types, lifting) case_prodE fst_conv member_remove remove_def)
    qed
  also have "\<dots> = map (get_map S) (removeAll (fst x) (sorted_list_of_set (fst ` S)))"
    using distinct
    by (auto simp: distinct_remove1_removeAll)
  also have "\<dots> = removeAll (get_map S (fst x)) (map (get_map S) (sorted_list_of_set (fst ` S)))"
    proof (subst map_removeAll_inj_on)
      have "fst x \<in> set (sorted_list_of_set (fst ` S))"
        using assms by (fastforce simp: sorted_list_of_set)
      hence "insert (fst x) (set (sorted_list_of_set (fst ` S))) = set (sorted_list_of_set (fst ` S))"
        by auto
      with inj show "inj_on (get_map S) (insert (fst x) (set (sorted_list_of_set (fst ` S))))"
        by auto
    qed simp
  also have "\<dots> = removeAll x (map (get_map S) (sorted_list_of_set (fst ` S)))"
    using assms by (auto simp: get_map_elem[where v = "snd x"])
  also have "\<dots> = remove1 x (map (get_map S) (sorted_list_of_set (fst ` S)))"
    using distinct inj
    by (simp add: distinct_remove1_removeAll distinct_map)
  finally show ?thesis
    unfolding ordered_map_def .
qed

lemma ordered_map_list_all:
  assumes "finite S" "is_map S"
  shows "list_all P (ordered_map S) = Ball S P"
unfolding list_all_iff
using assms by (simp add: ordered_map_set_eq)

lemma ordered_map_singleton[simp]: "ordered_map {(x, y)} = [(x, y)]"
unfolding ordered_map_def get_map_def Set.filter_def the_elem_def
by auto

context
  includes fset.lifting
begin

lift_definition ordered_fmap :: "('a::linorder \<times> 'b) fset \<Rightarrow> ('a \<times> 'b) list" is ordered_map .

lemma ordered_fmap_set_eq: "is_fmap S \<Longrightarrow> fset_of_list (ordered_fmap S) = S"
by transfer (rule ordered_map_set_eq)

lemma ordered_fmap_image:
  assumes "is_fmap S"
  shows "map (\<lambda>(a, b). (a, f a b)) (ordered_fmap S) = ordered_fmap ((\<lambda>(a, b). (a, f a b)) |`| S)"
using assms by transfer (rule ordered_map_image)

lemma ordered_fmap_distinct:
  assumes "is_fmap S"
  shows "distinct (map fst (ordered_fmap S))"
using assms
by transfer (rule ordered_map_distinct)

lemma ordered_fmap_keys:
  assumes "is_fmap S"
  shows "map fst (ordered_fmap S) = sorted_list_of_fset (fst |`| S)"
using assms
by transfer (rule ordered_map_keys)

lemma ordered_fmap_sound:
  assumes "is_fmap S" "(a, b) \<in> set (ordered_fmap S)"
  shows "(a, b) |\<in>| S"
using assms by transfer (rule ordered_map_sound)

lemma ordered_fmap_nonempty:
  assumes "is_fmap S" "ordered_fmap S \<noteq> []"
  shows "S \<noteq> {||}"
using assms by transfer (rule ordered_map_nonempty)

lemma ordered_fmap_remove:
  assumes "is_fmap S" "x |\<in>| S"
  shows "ordered_fmap (S - {| x |}) = remove1 x (ordered_fmap S)"
using assms by transfer (rule ordered_map_remove)

lemma ordered_fmap_list_all:
  assumes "is_fmap S"
  shows "list_all P (ordered_fmap S) = fBall S P"
unfolding list_all_iff
using assms by transfer (simp add: ordered_map_set_eq)

lemma ordered_fmap_singleton[simp]: "ordered_fmap {| (x, y) |} = [(x, y)]"
by transfer' simp

end


subsection \<open>Grouping into sets\<close>

definition group_by :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'c set) set" where
"group_by f s = {(fst (f a), {snd (f a')| a'. a' \<in> s \<and> fst (f a) = fst (f a') }) |a. a \<in> s}"

lemma group_by_nonempty: "M \<noteq> {} \<Longrightarrow> group_by f M \<noteq> {}"
unfolding group_by_def by blast

lemma group_by_nonempty_inner:
  assumes "(b, cs) \<in> group_by f as"
  obtains c where "c \<in> cs"
using assms unfolding group_by_def by blast

lemma group_by_sound: "c \<in> cs \<Longrightarrow> (b, cs) \<in> group_by f as \<Longrightarrow> \<exists>a \<in> as. f a = (b, c)"
unfolding group_by_def by force

lemma group_byD: "(b, cs) \<in> group_by f as \<Longrightarrow> f a = (b, c) \<Longrightarrow> a \<in> as \<Longrightarrow> c \<in> cs"
unfolding group_by_def by force

lemma group_byE[elim]:
  assumes "c \<in> cs" "(b, cs) \<in> group_by f as"
  obtains a where "a \<in> as" "f a = (b, c)"
using assms by (metis group_by_sound)

lemma group_byE2:
  assumes "(b, cs) \<in> group_by f as"
  obtains a where "a \<in> as" "fst (f a) = b"
using assms
by (metis group_byE group_by_nonempty_inner prod.sel(1))

lemma group_by_complete:
  assumes "a \<in> as"
  obtains cs where "(fst (f a), cs) \<in> group_by f as" "snd (f a) \<in> cs"
using assms unfolding group_by_def by auto

lemma group_by_single: "(a, x) \<in> group_by f s \<Longrightarrow> (a, y) \<in> group_by f s \<Longrightarrow> x = y"
unfolding group_by_def
by force

definition group_by' :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a set \<Rightarrow> ('b \<times> 'c set) set" where
"group_by' f s = (\<lambda>a. let (fa, _) = f a in (fa, (snd \<circ> f) ` Set.filter (\<lambda>a'. fa = fst (f a')) s)) ` s"

lemma group_by'_eq[code, code_unfold]: "group_by = group_by'"
apply (rule ext)+
unfolding group_by_def group_by'_def Set.filter_def
by (auto simp: Let_def split_beta)

lemma is_map_group_by[intro]: "is_map (group_by f M)"
unfolding group_by_def by force

lemma group_by_keys[simp]: "fst ` group_by f M = fst ` f ` M"
unfolding group_by_def by force

context
  includes fset.lifting
begin

lift_definition fgroup_by :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a fset \<Rightarrow> ('b \<times> 'c fset) fset" is group_by
unfolding inf_apply inf_bool_def group_by_def by auto

lemma fgroup_by_nonempty: "M \<noteq> {||} \<Longrightarrow> fgroup_by f M \<noteq> {||}"
by transfer' (rule group_by_nonempty)

lemma fgroup_by_nonempty_inner:
  assumes "(b, cs) |\<in>| fgroup_by f as"
  obtains c where "c |\<in>| cs"
using assms by transfer' (rule group_by_nonempty_inner)

lemma fgroup_by_sound: "c |\<in>| cs \<Longrightarrow> (b, cs) |\<in>| fgroup_by f as \<Longrightarrow> fBex as (\<lambda>a. f a = (b, c))"
by transfer (metis group_by_sound)

lemma fgroup_byD: "(b, cs) |\<in>| fgroup_by f as \<Longrightarrow> f a = (b, c) \<Longrightarrow> a |\<in>| as \<Longrightarrow> c |\<in>| cs"
by transfer' (metis group_byD)

lemma fgroup_byE[elim]:
  assumes "c |\<in>| cs" "(b, cs) |\<in>| fgroup_by f as"
  obtains a where "a |\<in>| as" "f a = (b, c)"
using assms by transfer' auto

lemma fgroup_byE2:
  assumes "(b, cs) |\<in>| fgroup_by f as"
  obtains a where "a |\<in>| as" "fst (f a) = b"
using assms by transfer' (rule group_byE2)

lemma fgroup_by_complete:
  assumes "a |\<in>| as"
  obtains cs where "(fst (f a), cs) |\<in>| fgroup_by f as" "snd (f a) |\<in>| cs"
using assms proof (transfer)
  fix a :: 'a and as :: "'a set"
  fix f :: "'a \<Rightarrow> ('c \<times> 'b)"
  fix thesis

  assume as: "finite as"
  assume "a \<in> as"
  then obtain cs where cs: "(fst (f a), cs) \<in> group_by f as" "snd (f a) \<in> cs"
    by (metis group_by_complete)
  hence "finite cs"
    unfolding group_by_def using as by force

  assume thesis: "\<And>cs. finite cs \<Longrightarrow> (fst (f a), cs) \<in> group_by f as \<Longrightarrow> snd (f a) \<in> cs \<Longrightarrow> thesis"
  show thesis
    by (rule thesis) fact+
qed

lemma fgroup_by_single: "(a, x) |\<in>| fgroup_by f s \<Longrightarrow> (a, y) |\<in>| fgroup_by f s \<Longrightarrow> x = y"
by transfer (metis group_by_single)

definition fgroup_by' :: "('a \<Rightarrow> ('b \<times> 'c)) \<Rightarrow> 'a fset \<Rightarrow> ('b \<times> 'c fset) fset" where
"fgroup_by' f s = fcompress ((\<lambda>a. let (fa, _) = f a in (fa, (snd \<circ> f) |`| ffilter (\<lambda>a'. fa = fst (f a')) s)) |`| s)"

lemma fgroup_by'_eq[code, code_unfold]: "fgroup_by = fgroup_by'"
unfolding fgroup_by'_def[abs_def] fcompress_eq
by transfer' (metis group_by'_def group_by'_eq)

lemma is_fmap_group_by[intro]: "is_fmap (fgroup_by f M)"
by transfer' (rule is_map_group_by)

lemma fgroup_by_keys[simp]: "fst |`| fgroup_by f M = fst |`| f |`| M"
by transfer' (rule group_by_keys)

end


subsection \<open>Singletons\<close>

lemma singleton_set_holds:
  assumes "\<forall>x \<in> M. \<forall>y \<in> M. f x = f y" "m \<in> M"
  shows "f m = the_elem (f ` M)"
proof -
  let ?n = "the_elem (f ` M)"
  have "f ` M = {f m}"
    using assms(1) assms(2) by blast
  hence "?n = (THE n. {f m} = {n})"
    unfolding the_elem_def by simp
  thus ?thesis by auto
qed

lemma singleton_set_is:
  assumes "\<forall>x \<in> M. x = y" "M \<noteq> {}"
  shows "M = {y}"
using assms by auto

context
  includes fset.lifting
begin

lemma singleton_fset_holds:
  assumes "fBall M (\<lambda>x. fBall M (\<lambda>y. f x = f y))" "m |\<in>| M"
  shows "f m = fthe_elem (f |`| M)"
using assms
by transfer (rule singleton_set_holds)

lemma singleton_fset_is:
  assumes "fBall M (\<lambda>x. x = y)" "M \<noteq> {||}"
  shows "M = {| y |}"
using assms by transfer' (rule singleton_set_is)

end


subsection \<open>Pairwise relations\<close>

definition pairwise :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set \<Rightarrow> bool" where
"pairwise P M \<longleftrightarrow> (\<forall>m \<in> M. \<forall>n \<in> M. P m n)"

lemma pairwiseI[intro!]:
  assumes "\<And>m n. m \<in> M \<Longrightarrow> n \<in> M \<Longrightarrow> P m n"
  shows "pairwise P M"
using assms unfolding pairwise_def by simp

lemma pairwiseD[dest]:
  assumes "pairwise P M" "m \<in> M" "n \<in> M"
  shows "P m n"
using assms unfolding pairwise_def by simp

lemma pairwise_subset: "pairwise P M \<Longrightarrow> N \<subseteq> M \<Longrightarrow> pairwise P N"
unfolding pairwise_def by blast

lemma pairwise_weaken: "pairwise P M \<Longrightarrow> (\<And>x y. x \<in> M \<Longrightarrow> y \<in> M \<Longrightarrow> P x y \<Longrightarrow> Q x y) \<Longrightarrow> pairwise Q M"
by auto

lemma pairwise_image[simp]: "pairwise P (f ` M) = pairwise (\<lambda>x y. P (f x) (f y)) M"
by auto

context
  includes fset.lifting
begin

lift_definition fpairwise :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a fset \<Rightarrow> bool" is pairwise .

lemma fpairwise_alt_def[code]: "fpairwise P M \<longleftrightarrow> fBall M (\<lambda>m. fBall M (\<lambda>n. P m n))"
by transfer' auto

lemma fpairwiseI[intro!]:
  assumes "\<And>m n. m |\<in>| M \<Longrightarrow> n |\<in>| M \<Longrightarrow> P m n"
  shows "fpairwise P M"
using assms unfolding fpairwise_alt_def by blast

lemma fpairwiseD:
  assumes "fpairwise P M" "m |\<in>| M" "n |\<in>| M"
  shows "P m n"
  using assms unfolding fpairwise_alt_def by auto

lemma fpairwise_image[simp]: "fpairwise P (f |`| M) = fpairwise (\<lambda>x y. P (f x) (f y)) M"
by (auto dest: fpairwiseD)

end

lemma fpairwise_subset: "fpairwise P M \<Longrightarrow> N |\<subseteq>| M \<Longrightarrow> fpairwise P N"
unfolding fpairwise_alt_def by auto

lemma fpairwise_weaken: "fpairwise P M \<Longrightarrow> (\<And>x y. x |\<in>| M \<Longrightarrow> y |\<in>| M \<Longrightarrow> P x y \<Longrightarrow> Q x y) \<Longrightarrow> fpairwise Q M"
unfolding fpairwise_alt_def by auto


subsection \<open>Relators\<close>

lemma rel_set_eq_eq: "rel_set (=) A B \<Longrightarrow> A = B"
unfolding rel_set_def by fast

lemma rel_set_image:
  assumes "rel_set P A B"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> P a b \<Longrightarrow> Q (f a) (g b)"
  shows "rel_set Q (f ` A) (g ` B)"
using assms
by (force intro!: rel_setI dest: rel_setD1 rel_setD2)

corollary rel_set_image_eq:
  assumes "rel_set P A B"
  assumes "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> P a b \<Longrightarrow> f a = g b"
  shows "f ` A = g ` B"
proof -
  have "rel_set (=) (f ` A) (g ` B)"
    by (rule rel_set_image) fact+
  thus ?thesis
    by (rule rel_set_eq_eq)
qed

lemma rel_set_refl_strong[intro]:
  assumes "\<And>x. x \<in> S \<Longrightarrow> P x x"
  shows "rel_set P S S"
proof (rule rel_setI)
  fix x
  assume "x \<in> S"
  thus "\<exists>y \<in> S. P x y"
    using assms by blast
next
  fix y
  assume "y \<in> S"
  thus "\<exists>x \<in> S. P x y"
    using assms by blast
qed

context
  includes fset.lifting
begin

lemma rel_fsetE1:
  assumes "rel_fset P M N" "x |\<in>| M"
  obtains y where "y |\<in>| N" "P x y"
using assms by transfer' (auto dest: rel_setD1)

lemma rel_fsetE2:
  assumes "rel_fset P M N" "y |\<in>| N"
  obtains x where "x |\<in>| M" "P x y"
using assms by transfer' (auto dest: rel_setD2)

lemma rel_fsetI:
  assumes "\<And>x. x |\<in>| A \<Longrightarrow> fBex B (R x)" "\<And>y. y |\<in>| B \<Longrightarrow> fBex A (\<lambda>x. R x y)"
  shows "rel_fset R A B"
using assms by transfer' (rule rel_setI)

lemma rel_fset_image:
  assumes "rel_fset P A B"
  assumes "\<And>a b. a |\<in>| A \<Longrightarrow> b |\<in>| B \<Longrightarrow> P a b \<Longrightarrow> Q (f a) (g b)"
  shows "rel_fset Q (f |`| A) (g |`| B)"
using assms by transfer' (rule rel_set_image)

corollary rel_fset_image_eq:
  assumes "rel_fset P A B"
  assumes "\<And>a b. a |\<in>| A \<Longrightarrow> b |\<in>| B \<Longrightarrow> P a b \<Longrightarrow> f a = g b"
  shows "f |`| A = g |`| B"
using assms by transfer' (rule rel_set_image_eq)

lemma rel_fset_refl_strong:
  assumes "\<And>x. x |\<in>| S \<Longrightarrow> P x x"
  shows "rel_fset P S S"
using assms
by transfer' (rule rel_set_refl_strong)

end


subsection \<open>Selecting values from keys\<close>

definition select :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set" where
"select f S = {z|z. \<exists>x \<in> S. f x = Some z}"

lemma select_finite:
  assumes "finite S"
  shows "finite (select f S)"
proof -
  have "finite (f ` S)"
    using assms by simp
  moreover have "Some ` (select f S) \<subseteq> f ` S"
    unfolding select_def by force
  ultimately have "finite (Some ` select f S)"
    by (rule rev_finite_subset)
  moreover have "\<And>S. inj_on Some S"
    by simp
  ultimately show ?thesis
    by (rule finite_imageD)
qed

lemma select_memberI: "x \<in> S \<Longrightarrow> f x = Some y \<Longrightarrow> y \<in> select f S"
unfolding select_def by blast

lemma select_memberE:
  assumes "y \<in> select f S"
  obtains x where "x \<in> S" "f x = Some y"
using assms unfolding select_def by blast

context
  includes fset.lifting
begin

lift_definition fselect :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a fset \<Rightarrow> 'b fset" is select
by (rule select_finite)

lemma fselect_memberI[intro]: "x |\<in>| S \<Longrightarrow> f x = Some y \<Longrightarrow> y |\<in>| fselect f S"
by transfer' (rule select_memberI)

lemma fselect_memberE[elim]:
  assumes "y |\<in>| fselect f S"
  obtains x where "x |\<in>| S" "f x = Some y"
using assms by transfer' (rule select_memberE)

end


subsection \<open>Miscellaneous\<close>

lemma set_of_list_singletonE:
  assumes "set xs = {x}" "distinct xs"
  shows "xs = [x]"
using assms
by (metis distinct.simps(2) empty_iff insertI1 insert_ident list.simps(15) neq_Nil_conv set_empty2 singletonD)

lemma fset_of_list_singletonE:
  assumes "fset_of_list xs = {|x|}" "distinct xs"
  shows "xs = [x]"
including fset.lifting
  using assms by transfer (rule set_of_list_singletonE)

section \<open>Finite maps\<close>

definition fmlookup_default :: "('a, 'b) fmap \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where
"fmlookup_default m f x = (case fmlookup m x of None \<Rightarrow> f x | Some b \<Rightarrow> b)"

lemma fmpred_foldl[intro]:
  assumes "fmpred P init" "\<And>x. x \<in> set xs \<Longrightarrow> fmpred P x"
  shows "fmpred P (foldl (++\<^sub>f) init xs)"
using assms proof (induction xs arbitrary: init)
  case (Cons x xs)
  have "fmpred P (foldl (++\<^sub>f) (init ++\<^sub>f x) xs)"
    proof (rule Cons)
      show "fmpred P (init ++\<^sub>f x)"
        using Cons by auto
    next
      fix x
      assume "x \<in> set xs"
      thus "fmpred P x"
        using Cons by auto
    qed
  thus ?case
    by simp
qed auto

lemma fmdom_foldl_add: "fmdom (foldl (++\<^sub>f) m ns) = fmdom m |\<union>| ffUnion (fmdom |`| fset_of_list ns)"
by (induction ns arbitrary: m) auto

lemma fmimage_fmmap[simp]: "fmimage (fmmap f m) S = f |`| fmimage m S"
including fmap.lifting fset.lifting
by transfer' auto

lemma fmmap_total:
  assumes "\<And>k v. fmlookup m k = Some v \<Longrightarrow> (\<exists>v'. f v' = v)"
  obtains m' where "m = fmmap f m'"
apply (rule that[of "fmmap (inv f) m"])
unfolding fmap.map_comp
apply (subst fmap.map_id[symmetric])
apply (rule fmap.map_cong)
apply (auto simp: fmran'_def f_inv_into_f dest!: assms)
done

lemma set_of_map_upd: "set_of_map (map_upd k v m) = set_of_map (map_drop k m) \<union> {(k, v)}"
unfolding set_of_map_def map_upd_def map_drop_def map_filter_def
by (auto split: if_splits)

lemma map_drop_delete: "map_drop k (map_of ps) = map_of (AList.delete k ps)"
unfolding AList.delete_eq map_drop_def
apply (subst map_filter_map_of)
apply (rule arg_cong[where f = "map_of"])
apply (rule filter_cong[OF refl])
by auto

lemma set_of_map_map_of: "set_of_map (map_of xs) = set (AList.clearjunk xs)"
proof (induction xs rule: clearjunk.induct)
  case (2 p ps)

  (* honourable mention: int-e on IRC, but it's way to short to understand what's going on *)
  have ?case by (simp add: 2[symmetric] delete_conv) (auto simp: set_of_map_def)

  obtain k v where "p = (k, v)"
    by (cases p) auto
  have "set_of_map (map_of (p # ps)) = set_of_map (map_upd k v (map_of ps))"
    unfolding \<open>p = _\<close> map_upd_def by simp
  also have "\<dots> = set_of_map (map_drop k (map_of ps)) \<union> {(k, v)}"
    by (rule set_of_map_upd)
  also have "\<dots> = set_of_map (map_of (AList.delete k ps)) \<union> {(k, v)}"
    by (simp only: map_drop_delete)
  also have "\<dots> =  set (AList.clearjunk (AList.delete k ps)) \<union> {(k, v)}"
    using 2 unfolding \<open>p = _\<close> by simp
  also have "\<dots> = set (AList.clearjunk (p # ps))"
    unfolding \<open>p = _\<close> by simp
  finally show ?case .
qed (simp add: set_of_map_def)

lemma fset_of_fmap_code[code]: "fset_of_fmap (fmap_of_list x) = fset_of_list (AList.clearjunk x)"
including fmap.lifting fset.lifting
  by transfer (rule set_of_map_map_of)

lemma distinct_sorted_list_of_fmap[simp, intro]: "distinct (sorted_list_of_fmap m)"
unfolding sorted_list_of_fmap_def
apply (subst distinct_map)
apply rule
subgoal by simp
subgoal by (rule inj_on_convol_ident)
done

section \<open>Lists\<close>

lemma rev_induct2[consumes 1, case_names nil snoc]:
  assumes "length xs = length ys"
  assumes "P [] []"
  assumes "\<And>x xs y ys. length xs = length ys \<Longrightarrow> P xs ys \<Longrightarrow> P (xs @ [x]) (ys @ [y])"
  shows "P xs ys"
proof -
  have "length (rev xs) = length (rev ys)"
    using assms by simp
  hence "P (rev (rev xs)) (rev (rev ys))"
    using assms by (induct rule: list_induct2) auto
  thus ?thesis
    by simp
qed

lemma list_allI[intro]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> P x"
  shows "list_all P xs"
using assms unfolding list_all_iff by auto

lemma list_map_snd_id:
  assumes "\<And>a b e. (a, b) \<in> set cs \<Longrightarrow> f a b = b"
  shows "map (\<lambda>(a, b). (a, f a b)) cs = cs"
proof -
  have "map (\<lambda>(a, b). (a, f a b)) cs = map id cs"
    proof (rule list.map_cong0, safe)
      fix a b
      assume "(a, b) \<in> set cs"
      hence "f a b = b"
        using assms by auto
      thus "(a, f a b) = id (a, b)"
        by simp
    qed
  thus ?thesis
    by simp
qed

lemma list_all2_leftE:
  assumes "list_all2 P xs ys" "x \<in> set xs"
  obtains y where "y \<in> set ys" "P x y"
using assms by induct auto

lemma list_all2_rightE:
  assumes "list_all2 P xs ys" "y \<in> set ys"
  obtains x where "x \<in> set xs" "P x y"
using assms by induct auto

fun list_all3 where
"list_all3 P (x # xs) (y # ys) (z # zs) \<longleftrightarrow> P x y z \<and> list_all3 P xs ys zs" |
"list_all3 P [] [] [] \<longleftrightarrow> True" |
"list_all3 _ _ _ _ \<longleftrightarrow> False"

lemma list_all3_empty[intro]: "list_all3 P [] [] []"
by simp

lemma list_all3_cons[intro]: "list_all3 P xs ys zs \<Longrightarrow> P x y z \<Longrightarrow> list_all3 P (x # xs) (y # ys) (z # zs)"
by simp

lemma list_all3_induct[consumes 1, case_names Nil Cons, induct set: list_all3]:
  assumes P: "list_all3 P xs ys zs"
  assumes Nil: "Q [] [] []"
  assumes Cons: "\<And>x xs y ys z zs.
    P x y z \<Longrightarrow> Q xs ys zs \<Longrightarrow> list_all3 P xs ys zs \<Longrightarrow> Q (x # xs) (y # ys) (z # zs)"
  shows "Q xs ys zs"
using P
proof (induction P\<equiv>P xs ys zs rule: list_all3.induct, goal_cases cons)
  show "Q [] [] []" by fact
next
  case (cons x xs y ys z zs)
  thus ?case
    using Cons by auto
qed auto

lemma list_all3_from_list_all2s:
  assumes "list_all2 P xs ys" "list_all2 Q xs zs"
  assumes "\<And>x y z. x \<in> set xs \<Longrightarrow> y \<in> set ys \<Longrightarrow> z \<in> set zs \<Longrightarrow> P x y \<Longrightarrow> Q x z \<Longrightarrow> R x y z"
  shows "list_all3 R xs ys zs"
using assms proof (induction arbitrary: zs)
  case Nil
  hence "zs = []" by blast
  thus ?case by simp
next
  case (Cons x y xs ys zs0)
  then obtain z zs where "zs0 = z # zs" by (cases zs0) auto
  show ?case
    using Cons unfolding \<open>zs0 = _\<close>
    by auto
qed

lemma those_someD:
  assumes "those xs = Some ys"
  shows "xs = map Some ys"
using assms by (induction xs arbitrary: ys) (auto split: if_splits option.splits)

end