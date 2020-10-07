(* Authors:  Florian Haftmann and René Neumann, TU Muenchen *)

section \<open>Abstract priority queues\<close>

theory PQ
imports Main
begin

subsection \<open>Generic Lemmas\<close>

lemma tl_set:
  "distinct q \<Longrightarrow> set (tl q) = set q - {hd q}"
  by (cases q) simp_all


subsection \<open>Type of abstract priority queues\<close>

typedef (overloaded) ('a, 'b::linorder) pq =
  "{xs :: ('a \<times> 'b) list. distinct (map fst xs) \<and> sorted (map snd xs)}"
  morphisms alist_of Abs_pq
proof -
  have "[] \<in> ?pq" by simp
  then show ?thesis by blast
qed

lemma alist_of_Abs_pq:
  assumes "distinct (map fst xs)"
    and "sorted (map snd xs)"
  shows "alist_of (Abs_pq xs) = xs"
  by (rule Abs_pq_inverse) (simp add: assms)

lemma [code abstype]:
  "Abs_pq (alist_of q) = q"
  by (fact alist_of_inverse)

lemma distinct_fst_alist_of [simp]:
  "distinct (map fst (alist_of q))"
  using alist_of [of q] by simp

lemma distinct_alist_of [simp]:
  "distinct (alist_of q)"
  using distinct_fst_alist_of [of q] by (simp add: distinct_map)

lemma sorted_snd_alist_of [simp]:
  "sorted (map snd (alist_of q))"
  using alist_of [of q] by simp

lemma alist_of_eqI:
  "alist_of p = alist_of q \<Longrightarrow> p = q"
proof -
  assume "alist_of p = alist_of q"
  then have "Abs_pq (alist_of p) = Abs_pq (alist_of q)" by simp
  thus "p = q" by (simp add: alist_of_inverse)
qed

definition "values" :: "('a, 'b::linorder) pq \<Rightarrow> 'a list" ("|(_)|") where
  "values q = map fst (alist_of q)"

definition priorities :: "('a, 'b::linorder) pq \<Rightarrow> 'b list" ("\<parallel>(_)\<parallel>") where
  "priorities q = map snd (alist_of q)"

lemma values_set:
  "set |q| = fst ` set (alist_of q)"
  by (simp add: values_def)

lemma priorities_set:
  "set \<parallel>q\<parallel> = snd ` set (alist_of q)"
  by (simp add: priorities_def)

definition is_empty :: "('a, 'b::linorder) pq \<Rightarrow> bool" where
  "is_empty q \<longleftrightarrow> alist_of q = []"

definition priority :: "('a, 'b::linorder) pq \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "priority q = map_of (alist_of q)"

definition min :: "('a, 'b::linorder) pq \<Rightarrow> 'a" where
  "min q = fst (hd (alist_of q))"

definition empty :: "('a, 'b::linorder) pq" where 
  "empty = Abs_pq []"

lemma is_empty_alist_of [dest]:
  "is_empty q \<Longrightarrow> alist_of q = []"
  by (simp add: is_empty_def)

lemma not_is_empty_alist_of [dest]:
  "\<not> is_empty q \<Longrightarrow> alist_of q \<noteq> []"
  by (simp add: is_empty_def)

lemma alist_of_empty [simp, code abstract]:
  "alist_of empty = []"
  by (simp add: empty_def Abs_pq_inverse)

lemma values_empty [simp]:
  "|empty| = []"
  by (simp add: values_def)

lemma priorities_empty [simp]:
  "\<parallel>empty\<parallel> = []"
  by (simp add: priorities_def)

lemma values_empty_nothing [simp]:
  "\<forall>k. k \<notin> set |empty|"
  by (simp add: values_def)

lemma is_empty_empty:
  "is_empty q \<longleftrightarrow> q = empty"
proof (rule iffI)
  assume "is_empty q"
  then have "alist_of q = []" by (simp add: is_empty_alist_of)
  then have "Abs_pq (alist_of q) = Abs_pq []" by simp
  then show "q = empty" by (simp add: empty_def alist_of_inverse)
qed (simp add: is_empty_def)

lemma is_empty_empty_simp [simp]:
  "is_empty empty"
by (simp add: is_empty_empty)

lemma map_snd_alist_of:
  "map (the \<circ> priority q) (values q) = map snd (alist_of q)"
  by (auto simp add: values_def priority_def)

lemma image_snd_alist_of:
  "the ` priority q ` set (values q) = snd ` set (alist_of q)"
proof -
  from map_snd_alist_of [of q]
    have "set (map (the \<circ> priority q) (values q)) = set (map snd (alist_of q))"
      by (simp only:)
  then show ?thesis by (simp add: image_comp)
qed

lemma Min_snd_alist_of:
  assumes "\<not> is_empty q"
  shows "Min (snd ` set (alist_of q)) = snd (hd (alist_of q))"
proof -
  from assms obtain ps p where q: "map snd (alist_of q) = p # ps"
    by (cases "map snd (alist_of q)") auto
  then have "hd (map snd (alist_of q)) = p" by simp
  with assms have p: "snd (hd (alist_of q)) = p" by (auto simp add: hd_map)
  have "sorted (map snd (alist_of q))" by simp
  with q have "sorted (p # ps)" by simp
  then have "\<forall>p'\<in>set ps. p' \<ge> p" by (simp)
  then have "Min (set (p # ps)) = p" by (auto intro: Min_eqI)
  with p q have "Min (set (map snd (alist_of q))) = snd (hd (alist_of q))"
    by simp
  then show ?thesis by simp
qed

lemma priority_fst:
  assumes "xp \<in> set (alist_of q)"
  shows "priority q (fst xp) = Some (snd xp)"
  using assms by (simp add: priority_def)

lemma priority_Min:
  assumes "\<not> is_empty q"
  shows "priority q (min q) = Some (Min (the ` priority q ` set (values q)))"
  using assms
    by (auto simp add: min_def image_snd_alist_of Min_snd_alist_of priority_fst)

lemma priority_Min_priorities:
  assumes "\<not> is_empty q"
  shows "priority q (min q) = Some (Min (set \<parallel>q\<parallel>))"
  using assms
    by (simp add: priority_Min image_snd_alist_of priorities_def)

definition push :: "'a \<Rightarrow> 'b::linorder \<Rightarrow> ('a, 'b) pq \<Rightarrow> ('a, 'b) pq" where
  "push k p q = Abs_pq (if k \<notin> set (values q)
           then insort_key snd (k, p) (alist_of q)
           else alist_of q)"

lemma Min_snd_hd:
  "q \<noteq> [] \<Longrightarrow> sorted (map snd q) \<Longrightarrow> Min (snd ` set q) = snd (hd q)" 
proof (induct q)
  case (Cons x xs) then show ?case by (cases xs) (auto simp add: ord_class.min_def)
qed simp

lemma hd_construct:
  assumes "\<not> is_empty q"
  shows "hd (alist_of q) = (min q, the (priority q (min q)))"
proof -
  from assms have "the (priority q (min q)) = snd (hd (alist_of q))"
    using Min_snd_hd [of "alist_of q"]
      by (auto simp add: priority_Min_priorities priorities_def)
  then show ?thesis by (simp add: min_def)
qed

lemma not_in_first_image:
  "x \<notin> fst ` s \<Longrightarrow> (x, p) \<notin> s"
  by (auto simp add: image_def)

lemma alist_of_push [simp, code abstract]:
  "alist_of (push k p q) =
    (if k \<notin> set (values q) then insort_key snd (k, p) (alist_of q) else alist_of q)"
  using distinct_fst_alist_of [of q]
    by (auto simp add: distinct_map set_insort_key distinct_insort not_in_first_image
      push_def values_def sorted_insort_key intro: alist_of_Abs_pq)

lemma push_values [simp]:
  "set |push k p q| = set |q| \<union> {k}"
  by (auto simp add: values_def set_insort_key)

lemma push_priorities [simp]:
  "k \<notin> set |q| \<Longrightarrow> set \<parallel>push k p q\<parallel> = set \<parallel>q\<parallel> \<union> {p}"
  "k \<in> set |q| \<Longrightarrow> set \<parallel>push k p q\<parallel> = set \<parallel>q\<parallel>"
  by (auto simp add: priorities_def set_insort_key)

lemma not_is_empty_push [simp]:
  "\<not> is_empty (push k p q)"
  by (auto simp add: values_def is_empty_def)

lemma push_commute:
  assumes "a \<noteq> b" and "v \<noteq> w"
  shows "push w b (push v a q) = push v a (push w b q)"
  using assms by (auto intro!: alist_of_eqI insort_key_left_comm)

definition remove_min :: "('a, 'b::linorder) pq \<Rightarrow> ('a, 'b::linorder) pq" where
  "remove_min q = (if is_empty q then empty else Abs_pq (tl (alist_of q)))"

lemma alift_of_remove_min_if [code abstract]:
  "alist_of (remove_min q) = (if is_empty q then [] else tl (alist_of q))"
  by (auto simp add: remove_min_def map_tl sorted_tl distinct_tl alist_of_Abs_pq)

lemma remove_min_empty [simp]:
  "is_empty q \<Longrightarrow> remove_min q = empty"
  by (simp add: remove_min_def)

lemma alist_of_remove_min [simp]:
  "\<not> is_empty q \<Longrightarrow> alist_of (remove_min q) = tl (alist_of q)"
  by (simp add: alift_of_remove_min_if)

lemma values_remove_min [simp]:
  "\<not> is_empty q \<Longrightarrow> values (remove_min q) = tl (values q)"
  by (simp add: values_def map_tl)

lemma set_alist_of_remove_min:
  "\<not> is_empty q \<Longrightarrow> set (alist_of (remove_min q)) =
    set (alist_of q) - {(min q, the (priority q (min q)))}"
  by (simp add: tl_set hd_construct)

definition pop :: "('a, 'b::linorder) pq \<Rightarrow> ('a \<times> ('a, 'b) pq) option" where
  "pop q = (if is_empty q then None else Some (min q, remove_min q))"

lemma pop_simps [simp]:
  "is_empty q \<Longrightarrow> pop q = None"
  "\<not> is_empty q \<Longrightarrow> pop q = Some (min q, remove_min q)"
  by (simp_all add: pop_def)

hide_const (open) Abs_pq alist_of "values" priority empty is_empty push min pop

no_notation
  "PQ.values" ("|(_)|")
  and "PQ.priorities" ("\<parallel>(_)\<parallel>")

end
