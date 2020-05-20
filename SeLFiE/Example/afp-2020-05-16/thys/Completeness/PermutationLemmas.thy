section "Permutation Lemmas"

theory PermutationLemmas
imports "HOL-Library.Permutation" "HOL-Library.Multiset"
begin

  \<comment> \<open>following function is very close to that in multisets- now we can make the connection that x <~~> y iff the multiset of x is the same as that of y\<close>

subsection "perm, count equivalence"

primrec count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat"
where
  "count x [] = 0"
| "count x (y#ys) = (if x=y then 1 else 0) + count x ys"

lemma perm_count: "A <~~> B \<Longrightarrow> (\<forall> x. count x A = count x B)"
  by(induct set: perm) auto

lemma count_0: "(\<forall>x. count x B = 0) = (B = [])"
  by(induct B) auto

lemma count_Suc: "count a B = Suc m \<Longrightarrow> a : set B"
  apply(induct B)
   apply auto
  apply(case_tac "a = aa")
   apply auto
  done

lemma count_append: "count a (xs@ys) = count a xs + count a ys"
  by(induct xs) auto

lemma count_perm: "!! B. (\<forall> x. count x A = count x B) \<Longrightarrow> A <~~> B"
  apply(induct A)
  apply(simp add: count_0)
proof -
  fix a list B
  assume a: "\<And>B. \<forall>x. count x list = count x B \<Longrightarrow> list <~~> B"
    and b: "\<forall>x. count x (a # list) = count x B"
  from b have "a : set B"
    apply auto
    apply (drule_tac x=a in spec, simp) apply(metis count_Suc) done
  from split_list[OF this] obtain xs ys where B: "B = xs@a#ys" by blast
  let ?B' = "xs@ys"
  from b have "\<forall>x. count x list = count x ?B'" by(simp add: count_append B)
  from a[OF this] have c: "list <~~> xs@ys" .
  hence "a#list <~~> a#(xs@ys)" by rule
  also have "a#(xs@ys) <~~> xs@a#ys" by(rule perm_append_Cons)
  also (perm.trans) note B[symmetric]
  finally show "a # list <~~> B" .
qed

lemma perm_count_conv: "A <~~> B = (\<forall> x. count x A = count x B)"
  apply(blast intro!: perm_count count_perm) done 


subsection "Properties closed under Perm and Contr hold for x iff hold for remdups x"

lemma remdups_append: "y : set ys --> remdups (ws@y#ys) = remdups (ws@ys)"
  apply (induct ws, simp)
  apply (case_tac "y = a", simp, simp)
  done

lemma perm_contr': assumes perm[rule_format]: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr'[rule_format]: "! x xs. P(x#x#xs) = P (x#xs)" 
  shows "! xs. length xs = n --> (P xs = P (remdups xs))"
  apply(induct n rule: nat_less_induct)
proof (safe)
  fix xs :: "'a list"
  assume a[rule_format]: "\<forall>m<length xs. \<forall>ys. length ys = m \<longrightarrow> P ys = P (remdups ys)"
  show "P xs = P (remdups xs)"
  proof (cases "distinct xs")
    case True
    thus ?thesis by(simp add:distinct_remdups_id)
  next
    case False
    from not_distinct_decomp[OF this] obtain ws ys zs y where xs: "xs = ws@[y]@ys@[y]@zs" by force
    have "P xs = P (ws@[y]@ys@[y]@zs)" by (simp add: xs)
    also have "... = P ([y,y]@ws@ys@zs)" 
      apply(rule perm) apply(rule iffD2[OF perm_count_conv]) apply rule apply(simp add: count_append) done
    also have "... = P ([y]@ws@ys@zs)" apply simp apply(rule contr') done
    also have "... = P (ws@ys@[y]@zs)" 
      apply(rule perm) apply(rule iffD2[OF perm_count_conv]) apply rule apply(simp add: count_append) done
    also have "... = P (remdups (ws@ys@[y]@zs))"
      apply(rule a) by(auto simp: xs)
    also have "(remdups (ws@ys@[y]@zs)) = (remdups xs)"
      apply(simp add: xs remdups_append) done 
    finally show "P xs = P (remdups xs)" .
  qed
qed

lemma perm_contr: assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr': "! x xs. P(x#x#xs) = P (x#xs)" 
  shows "(P xs = P (remdups xs))"
  apply(rule perm_contr'[OF perm contr', rule_format]) by force


subsection "List properties closed under Perm, Weak and Contr are monotonic in the set of the list"

definition
  rem :: "'a => 'a list => 'a list" where
  "rem x xs = filter (%y. y ~= x) xs"

lemma rem: "x ~: set (rem x xs)"
  by(simp add: rem_def)

lemma length_rem: "length (rem x xs) <= length xs"
  by(simp add: rem_def)

lemma rem_notin: "x ~: set xs ==> rem x xs = xs"
  apply(simp add: rem_def)
  apply(rule filter_True)
  apply force
  done


lemma perm_weak_filter': assumes perm[rule_format]: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and weak[rule_format]: "! x xs. P xs --> P (x#xs)"
  shows "! ys. P (ys@filter Q xs) --> P (ys@xs)"
  apply (induct xs, simp, rule)
  apply rule
  apply simp
  apply (case_tac "Q a", simp)
   apply(drule_tac x="ys@[a]" in spec) apply simp
  apply simp
  apply(drule_tac x="ys@[a]" in spec) apply simp
  apply(erule impE)
   apply(subgoal_tac "(ys @ a # filter Q xs) <~~> a#ys@filter Q xs")
    apply(simp add: perm)
    apply(rule weak) apply simp
   apply(rule perm_sym) apply(rule perm_append_Cons)
  .

lemma perm_weak_filter: assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and weak: "! x xs. P xs --> P (x#xs)"
  shows "P (filter Q xs) ==> P xs"
  using perm_weak_filter'[OF perm weak, rule_format, of "[]", simplified]
  by blast

  \<comment> \<open>right, now in a position to prove that in presence of perm, contr and weak, set x leq set y and x : ded implies y : ded\<close>

lemma perm_weak_contr_mono: 
  assumes perm: "! xs ys. xs <~~> ys --> (P xs = P ys)"
  and contr: "! x xs. P (x#x#xs) --> P (x#xs)"
  and weak: "! x xs. P xs --> P (x#xs)"
  and xy: "set x <= set y"
  and Px : "P x"
  shows "P y"
proof -
  from contr weak have contr': "! x xs. P(x#x#xs) = P (x#xs)" by blast

  define y' where "y' = filter (% z. z : set x) y"
  from xy have "set x = set y'" apply(simp add: y'_def) apply blast done
  hence rxry': "remdups x <~~> remdups y'" by(simp add: perm_remdups_iff_eq_set)

  from Px perm_contr[OF perm contr'] have Prx: "P (remdups x)" by simp
  with rxry' have "P (remdups y')" by(simp add: perm)
  
  with perm_contr[OF perm contr'] have "P y'" by simp
  thus "P y" 
    apply(simp add: y'_def)
    apply(rule perm_weak_filter[OF perm weak]) .
qed

(* No, not used
subsection "Following used in Soundness"

primrec multiset_of_list :: "'a list \<Rightarrow> 'a multiset"
where
  "multiset_of_list [] = {#}"
| "multiset_of_list (x#xs) = {#x#} + multiset_of_list xs"

lemma count_count[symmetric]: "count x A = Multiset.count (multiset_of_list A) x"
  by (induct A) simp_all

lemma perm_multiset: "A <~~> B = (multiset_of_list A = multiset_of_list B)"
  apply(simp add: perm_count_conv)
  apply(simp add: multiset_eq_iff)
  apply(simp add: count_count)
  done

lemma set_of_multiset_of_list: "set_of (multiset_of_list A) = set A"
  by (induct A) auto
*)
end
