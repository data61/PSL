(*  Title:       General Algorithms for Iterators
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>General Algorithms for Iterators over Finite Sets\<close>
theory SetIteratorGA
imports Main SetIteratorOperations
begin

subsection \<open>Quantification\<close>

definition iterate_ball where
    "iterate_ball (it::('x,bool) set_iterator) P = it id (\<lambda>x \<sigma>. P x) True"

lemma iterate_ball_correct :
assumes it: "set_iterator it S0"
shows "iterate_ball it P = (\<forall>x\<in>S0. P x)"
unfolding iterate_ball_def
apply (rule set_iterator_rule_P [OF it,
            where I = "\<lambda>S \<sigma>. \<sigma> = (\<forall>x\<in>S0-S. P x)"])
apply auto
done

definition iterate_bex where
    "iterate_bex (it::('x,bool) set_iterator) P = it (\<lambda>\<sigma>. \<not>\<sigma>) (\<lambda>x \<sigma>. P x) False"

lemma iterate_bex_correct :
assumes it: "set_iterator it S0"
shows "iterate_bex it P = (\<exists>x\<in>S0. P x)"
unfolding iterate_bex_def
apply (rule set_iterator_rule_P [OF it, where I = "\<lambda>S \<sigma>. \<sigma> = (\<exists>x\<in>S0-S. P x)"])
apply auto
done

subsection \<open>Iterator to List\<close>

definition iterate_to_list where
    "iterate_to_list (it::('x,'x list) set_iterator) = it (\<lambda>_. True) (\<lambda>x \<sigma>. x # \<sigma>) []"

lemma iterate_to_list_foldli [simp] :
  "iterate_to_list (foldli xs) = rev xs"
unfolding iterate_to_list_def
by (induct xs rule: rev_induct, simp_all add: foldli_snoc) 

lemma iterate_to_list_genord_correct :
assumes it: "set_iterator_genord it S0 R"
shows "set (iterate_to_list it) = S0 \<and> distinct (iterate_to_list it) \<and>
       sorted_wrt R (rev (iterate_to_list it))"
using it unfolding set_iterator_genord_foldli_conv by auto

lemma iterate_to_list_correct :
assumes it: "set_iterator it S0"
shows "set (iterate_to_list it) = S0 \<and> distinct (iterate_to_list it)"
using iterate_to_list_genord_correct [OF it[unfolded set_iterator_def]]
by simp

lemma (in linorder) iterate_to_list_linord_correct :
fixes S0 :: "'a set"
assumes it_OK: "set_iterator_linord it S0"
shows "set (iterate_to_list it) = S0 \<and> distinct (iterate_to_list it) \<and>
       sorted (rev (iterate_to_list it))"
using it_OK unfolding set_iterator_linord_foldli_conv by auto

lemma (in linorder) iterate_to_list_rev_linord_correct :
fixes S0 :: "'a set"
assumes it_OK: "set_iterator_rev_linord it S0"
shows "set (iterate_to_list it) = S0 \<and> distinct (iterate_to_list it) \<and>
       sorted (iterate_to_list it)"
using it_OK unfolding set_iterator_rev_linord_foldli_conv by auto

lemma (in linorder) iterate_to_list_map_linord_correct :
assumes it_OK: "map_iterator_linord it m"
shows "map_of (iterate_to_list it) = m \<and> distinct (map fst (iterate_to_list it)) \<and>
       sorted (map fst (rev (iterate_to_list it)))"
using it_OK unfolding map_iterator_linord_foldli_conv 
by clarify (simp add: rev_map[symmetric])

lemma (in linorder) iterate_to_list_map_rev_linord_correct :
assumes it_OK: "map_iterator_rev_linord it m"
shows "map_of (iterate_to_list it) = m \<and> distinct (map fst (iterate_to_list it)) \<and>
       sorted (map fst (iterate_to_list it))"
using it_OK unfolding map_iterator_rev_linord_foldli_conv 
by clarify (simp add: rev_map[symmetric])


subsection \<open>Size\<close>

lemma set_iterator_finite :
assumes it: "set_iterator it S0"
shows "finite S0"
using set_iterator_genord.finite_S0 [OF it[unfolded set_iterator_def]] .

lemma map_iterator_finite :
assumes it: "map_iterator it m"
shows "finite (dom m)"
using set_iterator_genord.finite_S0 [OF it[unfolded set_iterator_def]]
by (simp add: finite_map_to_set) 

definition iterate_size where
    "iterate_size (it::('x,nat) set_iterator) = it (\<lambda>_. True) (\<lambda>x \<sigma>. Suc \<sigma>) 0"

lemma iterate_size_correct :
assumes it: "set_iterator it S0"
shows "iterate_size it = card S0 \<and> finite S0"
unfolding iterate_size_def
apply (rule_tac set_iterator_rule_insert_P [OF it, 
    where I = "\<lambda>S \<sigma>. \<sigma> = card S \<and> finite S"])
apply auto
done

definition iterate_size_abort where
  "iterate_size_abort (it::('x,nat) set_iterator) n = it (\<lambda>\<sigma>. \<sigma> < n) (\<lambda>x \<sigma>. Suc \<sigma>) 0"

lemma iterate_size_abort_correct :
assumes it: "set_iterator it S0"
shows "iterate_size_abort it n = (min n (card S0)) \<and> finite S0"
unfolding iterate_size_abort_def
proof (rule set_iterator_rule_insert_P [OF it,
   where I = "\<lambda>S \<sigma>. \<sigma> = (min n (card S)) \<and> finite S"], goal_cases)
  case (4 \<sigma> S)
  assume "S \<subseteq> S0" "S \<noteq> S0" "\<not> \<sigma> < n" "\<sigma> = min n (card S) \<and> finite S" 

  from \<open>\<sigma> = min n (card S) \<and> finite S\<close> \<open>\<not> \<sigma> < n\<close> 
  have "\<sigma> = n" "n \<le> card S"
    by (auto simp add: min_less_iff_disj)

  note fin_S0 = set_iterator_genord.finite_S0 [OF it[unfolded set_iterator_def]]
  from card_mono [OF fin_S0 \<open>S \<subseteq> S0\<close>] have "card S \<le> card S0" .
  
  with \<open>\<sigma> = n\<close> \<open>n \<le> card S\<close> fin_S0
  show "\<sigma> = min n (card S0) \<and> finite S0" by simp
qed simp_all

subsection \<open>Emptyness Check\<close>

definition iterate_is_empty_by_size where
    "iterate_is_empty_by_size it = (iterate_size_abort it 1 = 0)"

lemma iterate_is_empty_by_size_correct :
assumes it: "set_iterator it S0"
shows "iterate_is_empty_by_size it = (S0 = {})"
using iterate_size_abort_correct[OF it, of 1]
unfolding iterate_is_empty_by_size_def
by (cases "card S0") auto

definition iterate_is_empty where
    "iterate_is_empty (it::('x,bool) set_iterator) = (it (\<lambda>b. b) (\<lambda>_ _. False) True)"

lemma iterate_is_empty_correct :
assumes it: "set_iterator it S0"
shows "iterate_is_empty it = (S0 = {})"
unfolding iterate_is_empty_def
apply (rule set_iterator_rule_insert_P [OF it,
   where I = "\<lambda>S \<sigma>. \<sigma> \<longleftrightarrow> S = {}"])
apply auto
done

subsection \<open>Check for singleton Sets\<close>

definition iterate_is_sng where
    "iterate_is_sng it = (iterate_size_abort it 2 = 1)"

lemma iterate_is_sng_correct :
assumes it: "set_iterator it S0"
shows "iterate_is_sng it = (card S0 = 1)"
using iterate_size_abort_correct[OF it, of 2]
unfolding iterate_is_sng_def
apply (cases "card S0", simp, rename_tac n')
apply (case_tac n')
apply auto
done

subsection \<open>Selection\<close>

definition iterate_sel where
    "iterate_sel (it::('x,'y option) set_iterator) f = it (\<lambda>\<sigma>. \<sigma> = None) (\<lambda>x \<sigma>. f x) None"

lemma iterate_sel_genord_correct :
assumes it_OK: "set_iterator_genord it S0 R"
shows "iterate_sel it f = None \<longleftrightarrow> (\<forall>x\<in>S0. (f x = None))"
      "iterate_sel it f = Some y \<Longrightarrow> (\<exists>x \<in> S0. f x = Some y \<and> (\<forall>x' \<in> S0-{x}. \<forall>y. f x' = Some y' \<longrightarrow> R x x'))"
proof -
  show "iterate_sel it f = None \<longleftrightarrow> (\<forall>x\<in>S0. (f x = None))"
    unfolding iterate_sel_def
    apply (rule_tac set_iterator_genord.iteratei_rule_insert_P [OF it_OK, 
       where I = "\<lambda>S \<sigma>. (\<sigma> = None) \<longleftrightarrow> (\<forall>x\<in>S. (f x = None))"])
    apply auto
  done
next
  have "iterate_sel it f = Some y \<longrightarrow> (\<exists>x \<in> S0. f x = Some y \<and> (\<forall>x' \<in> S0-{x}. \<forall>y'. f x' = Some y' \<longrightarrow> R x x'))"
    unfolding iterate_sel_def
    apply (rule_tac set_iterator_genord.iteratei_rule_insert_P [OF it_OK, 
       where I = "\<lambda>S \<sigma>. (\<forall>y. \<sigma> = Some y \<longrightarrow> (\<exists>x \<in> S. f x = Some y \<and> (\<forall>x' \<in> S-{x}.\<forall>y'. f x' = Some y' \<longrightarrow> R x x'))) \<and>
                        ((\<sigma> = None) \<longleftrightarrow> (\<forall>x\<in>S. f x = None))"])
    apply simp
    apply (auto simp add: Bex_def subset_iff Ball_def)
    apply metis
  done
  moreover assume "iterate_sel it f = Some y" 
  finally show "(\<exists>x \<in> S0. f x = Some y \<and> (\<forall>x' \<in> S0-{x}. \<forall>y. f x' = Some y' \<longrightarrow> R x x'))" by blast
qed


definition iterate_sel_no_map where
    "iterate_sel_no_map it P = iterate_sel it (\<lambda>x. if P x then Some x else None)" 
lemmas iterate_sel_no_map_alt_def = iterate_sel_no_map_def[unfolded iterate_sel_def, code]

lemma iterate_sel_no_map_genord_correct :
assumes it_OK: "set_iterator_genord it S0 R"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
      "iterate_sel_no_map it P = Some x \<Longrightarrow> (x \<in> S0 \<and> P x \<and> (\<forall>x' \<in> S0-{x}. P x' \<longrightarrow> R x x'))"
unfolding iterate_sel_no_map_def
using iterate_sel_genord_correct[OF it_OK, of "\<lambda>x. if P x then Some x else None"]
apply (simp_all add: Bex_def)
apply (metis option.inject option.simps(2)) 
done

lemma iterate_sel_no_map_correct :
assumes it_OK: "set_iterator it S0"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
      "iterate_sel_no_map it P = Some x \<Longrightarrow> x \<in> S0 \<and> P x"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
       "iterate_sel_no_map it P = Some x \<Longrightarrow> x \<in> S0 \<and> P x"
    by simp_all
qed

lemma (in linorder) iterate_sel_no_map_linord_correct :
assumes it_OK: "set_iterator_linord it S0"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
      "iterate_sel_no_map it P = Some x \<Longrightarrow> (x \<in> S0 \<and> P x \<and> (\<forall>x'\<in>S0. P x' \<longrightarrow> x \<le> x'))"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_linord_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
       "iterate_sel_no_map it P = Some x \<Longrightarrow> (x \<in> S0 \<and> P x \<and> (\<forall>x'\<in>S0. P x' \<longrightarrow> x \<le> x'))"
    by auto
qed

lemma (in linorder) iterate_sel_no_map_rev_linord_correct :
assumes it_OK: "set_iterator_rev_linord it S0"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
      "iterate_sel_no_map it P = Some x \<Longrightarrow> (x \<in> S0 \<and> P x \<and> (\<forall>x'\<in>S0. P x' \<longrightarrow> x' \<le> x))"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_rev_linord_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>x\<in>S0. \<not>(P x))"
       "iterate_sel_no_map it P = Some x \<Longrightarrow> (x \<in> S0 \<and> P x \<and> (\<forall>x'\<in>S0. P x' \<longrightarrow> x' \<le> x))"
    by auto
qed


lemma iterate_sel_no_map_map_correct :
assumes it_OK: "map_iterator it m"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
      "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v))"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
       "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v))"
    by (auto simp add: map_to_set_def)
qed

lemma (in linorder) iterate_sel_no_map_map_linord_correct :
assumes it_OK: "map_iterator_linord it m"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
      "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v) \<and> (\<forall>k' v' . m k' = Some v' \<and>
           P (k', v') \<longrightarrow> k \<le> k'))"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_map_linord_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
       "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v) \<and> (\<forall>k' v' . m k' = Some v' \<and>
           P (k', v') \<longrightarrow> k \<le> k'))"
    apply (auto simp add: map_to_set_def Ball_def) 
  done
qed

lemma (in linorder) iterate_sel_no_map_map_rev_linord_correct :
assumes it_OK: "map_iterator_rev_linord it m"
shows "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
      "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v) \<and> (\<forall>k' v' . m k' = Some v' \<and>
           P (k', v') \<longrightarrow> k' \<le> k))"
proof -
  note iterate_sel_no_map_genord_correct [OF it_OK[unfolded set_iterator_map_rev_linord_def], of P]
  thus "iterate_sel_no_map it P = None \<longleftrightarrow> (\<forall>k v. m k = Some v \<longrightarrow> \<not>(P (k, v)))"
       "iterate_sel_no_map it P = Some (k, v) \<Longrightarrow> (m k = Some v \<and> P (k, v) \<and> (\<forall>k' v' . m k' = Some v' \<and>
           P (k', v') \<longrightarrow> k' \<le> k))"
    apply (auto simp add: map_to_set_def Ball_def) 
  done
qed


subsection \<open>Creating ordered iterators\<close>

text \<open>One can transform an iterator into an ordered one by converting it to list, 
        sorting this list and then converting back to an iterator. In general, this brute-force
        method is inefficient, though.\<close>

definition iterator_to_ordered_iterator where
  "iterator_to_ordered_iterator sort_fun it =
   foldli (sort_fun (iterate_to_list it))"

lemma iterator_to_ordered_iterator_correct :
assumes sort_fun_OK: "\<And>l. sorted_wrt R (sort_fun l) \<and> mset (sort_fun l) = mset l"
    and it_OK: "set_iterator it S0"
shows "set_iterator_genord (iterator_to_ordered_iterator sort_fun it) S0 R"
proof -
  define l where "l = iterate_to_list it"
  have l_props: "set l = S0" "distinct l" 
    using iterate_to_list_correct [OF it_OK, folded l_def] by simp_all

  with sort_fun_OK[of l] have sort_l_props:
    "sorted_wrt R (sort_fun l)"
    "set (sort_fun l) = S0" "distinct (sort_fun l)"
    apply (simp_all)
    apply (metis set_mset_mset)
    apply (metis distinct_count_atmost_1 set_mset_mset)
  done

  show ?thesis
    apply (rule set_iterator_genord_I[of "sort_fun l"])
    apply (simp_all add: sort_l_props iterator_to_ordered_iterator_def l_def[symmetric])
  done
qed


definition iterator_to_ordered_iterator_quicksort where
  "iterator_to_ordered_iterator_quicksort R it =
   iterator_to_ordered_iterator (quicksort_by_rel R []) it"

lemmas iterator_to_ordered_iterator_quicksort_code[code] =
  iterator_to_ordered_iterator_quicksort_def[unfolded iterator_to_ordered_iterator_def]

lemma iterator_to_ordered_iterator_quicksort_correct :
assumes lin : "\<And>x y. (R x y) \<or> (R y x)"
    and trans_R: "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
    and it_OK: "set_iterator it S0"
shows "set_iterator_genord (iterator_to_ordered_iterator_quicksort R it) S0 R"
unfolding iterator_to_ordered_iterator_quicksort_def
apply (rule iterator_to_ordered_iterator_correct [OF _ it_OK])
apply (simp_all add: sorted_wrt_quicksort_by_rel[OF lin trans_R])
done

definition iterator_to_ordered_iterator_mergesort where
  "iterator_to_ordered_iterator_mergesort R it =
   iterator_to_ordered_iterator (mergesort_by_rel R) it"

lemmas iterator_to_ordered_iterator_mergesort_code[code] =
  iterator_to_ordered_iterator_mergesort_def[unfolded iterator_to_ordered_iterator_def]

lemma iterator_to_ordered_iterator_mergesort_correct :
assumes lin : "\<And>x y. (R x y) \<or> (R y x)"
    and trans_R: "\<And>x y z. R x y \<Longrightarrow> R y z \<Longrightarrow> R x z"
    and it_OK: "set_iterator it S0"
shows "set_iterator_genord (iterator_to_ordered_iterator_mergesort R it) S0 R"
unfolding iterator_to_ordered_iterator_mergesort_def
apply (rule iterator_to_ordered_iterator_correct [OF _ it_OK])
apply (simp_all add: sorted_wrt_mergesort_by_rel[OF lin trans_R])
done

end


