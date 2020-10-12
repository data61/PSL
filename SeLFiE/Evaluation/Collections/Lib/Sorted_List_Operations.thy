section \<open>\isaheader{Operations on sorted Lists}\<close>
theory Sorted_List_Operations
imports Main Automatic_Refinement.Misc
begin 

fun inter_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "inter_sorted [] l2 = []"
 | "inter_sorted l1 [] = []"
 | "inter_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then (inter_sorted l1 (x2 # l2)) else 
     (if (x1 = x2) then x1 # (inter_sorted l1 l2) else inter_sorted (x1 # l1) l2))"

lemma inter_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "distinct (inter_sorted l1 l2) \<and> sorted (inter_sorted l1 l2) \<and> 
       set (inter_sorted l1 l2) = set l1 \<inter> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply (auto simp add: Ball_def)
        apply (metis linorder_not_le)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis by (simp add: x1_eq_x2 Ball_def)
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from ind_hyp_l2 x2_le_x1 x1_neq_x2 x2_le x2_nin_l2 x1_le
        show ?thesis 
          apply (auto simp add: x2_less_x1 Ball_def)
          apply (metis linorder_not_le x2_less_x1)
        done
      qed
    qed
  qed
qed

fun diff_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
   "diff_sorted [] l2 = []"
 | "diff_sorted l1 [] = l1"
 | "diff_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then x1 # (diff_sorted l1 (x2 # l2)) else 
     (if (x1 = x2) then (diff_sorted l1 l2) else diff_sorted (x1 # l1) l2))"

lemma diff_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "distinct (diff_sorted l1 l2) \<and> sorted (diff_sorted l1 l2) \<and> 
       set (diff_sorted l1 l2) = set l1 - set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply simp
        apply (simp add: Ball_def set_eq_iff)
        apply (metis linorder_not_le order_less_imp_not_eq2)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis by (simp add: x1_eq_x2 Ball_def)
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from x2_less_x1 x1_le have x2_nin_l1: "x2 \<notin> set l1"
           by (metis linorder_not_less)

        from ind_hyp_l2 x1_le x2_nin_l1
        show ?thesis 
          apply (simp add: x2_less_x1 x1_neq_x2 x2_le_x1 x1_nin_l1 Ball_def set_eq_iff)
          apply (metis x1_neq_x2)
        done
      qed
    qed
  qed
qed

fun subset_sorted :: "'a::{linorder} list \<Rightarrow> 'a list \<Rightarrow> bool" where
   "subset_sorted [] l2 = True"
 | "subset_sorted (x1 # l1) [] = False"
 | "subset_sorted (x1 # l1) (x2 # l2) =
    (if (x1 < x2) then False else 
     (if (x1 = x2) then (subset_sorted l1 l2) else subset_sorted (x1 # l1) l2))"

lemma subset_sorted_correct :
assumes l1_OK: "distinct l1 \<and> sorted l1"
assumes l2_OK: "distinct l2 \<and> sorted l2"
shows "subset_sorted l1 l2 \<longleftrightarrow> set l1 \<subseteq> set l2"
using assms
proof (induct l1 arbitrary: l2) 
  case Nil thus ?case by simp
next
  case (Cons x1 l1 l2) 
  note x1_l1_props = Cons(2)
  note l2_props = Cons(3)

  from x1_l1_props have l1_props: "distinct l1 \<and> sorted l1"
                    and x1_nin_l1: "x1 \<notin> set l1"
                    and x1_le: "\<And>x. x \<in> set l1 \<Longrightarrow> x1 \<le> x"
    by (simp_all add: Ball_def)

  note ind_hyp_l1 = Cons(1)[OF l1_props]

  show ?case
  using l2_props 
  proof (induct l2)
    case Nil with x1_l1_props show ?case by simp
  next
    case (Cons x2 l2)
    note x2_l2_props = Cons(2)
    from x2_l2_props have l2_props: "distinct l2 \<and> sorted l2"
                    and x2_nin_l2: "x2 \<notin> set l2"
                    and x2_le: "\<And>x. x \<in> set l2 \<Longrightarrow> x2 \<le> x"
    by (simp_all add: Ball_def)

    note ind_hyp_l2 = Cons(1)[OF l2_props]
    show ?case
    proof (cases "x1 < x2")
      case True note x1_less_x2 = this

      from ind_hyp_l1[OF x2_l2_props] x1_less_x2 x1_nin_l1 x1_le x2_le
      show ?thesis
        apply (auto simp add: Ball_def)
        apply (metis linorder_not_le)
      done
    next
      case False note x2_le_x1 = this
      
      show ?thesis
      proof (cases "x1 = x2")
        case True note x1_eq_x2 = this

        from ind_hyp_l1[OF l2_props] x1_le x2_le x2_nin_l2 x1_eq_x2 x1_nin_l1
        show ?thesis 
          apply (simp add: subset_iff x1_eq_x2 Ball_def)
          apply metis
        done
      next
        case False note x1_neq_x2 = this
        with x2_le_x1 have x2_less_x1 : "x2 < x1" by auto

        from ind_hyp_l2 x2_le_x1 x1_neq_x2 x2_le x2_nin_l2 x1_le
        show ?thesis 
          apply (simp add: subset_iff x2_less_x1 Ball_def)
          apply (metis linorder_not_le x2_less_x1)
        done
      qed
    qed
  qed
qed

lemma set_eq_sorted_correct :
  assumes l1_OK: "distinct l1 \<and> sorted l1"
  assumes l2_OK: "distinct l2 \<and> sorted l2"
  shows "l1 = l2 \<longleftrightarrow> set l1 = set l2"
  using assms
proof -
  have l12_eq: "l1 = l2 \<longleftrightarrow> subset_sorted l1 l2 \<and> subset_sorted l2 l1"
  proof (induct l1 arbitrary: l2)
    case Nil thus ?case by (cases l2) auto
  next
    case (Cons x1 l1')
    note ind_hyp = Cons(1)

    show ?case
    proof (cases l2)
      case Nil thus ?thesis by simp
    next
      case (Cons x2 l2')
      thus ?thesis by (simp add: ind_hyp)
    qed
  qed
  also have "\<dots> \<longleftrightarrow> ((set l1 \<subseteq> set l2) \<and> (set l2 \<subseteq> set l1))"
    using subset_sorted_correct[OF l1_OK l2_OK] subset_sorted_correct[OF l2_OK l1_OK]
    by simp
  also have "\<dots> \<longleftrightarrow> set l1 = set l2" by auto
  finally show ?thesis .
qed

fun memb_sorted where
   "memb_sorted [] x = False"
 | "memb_sorted (y # xs) x =
    (if (y < x) then memb_sorted xs x else (x = y))"

lemma memb_sorted_correct :
  "sorted xs \<Longrightarrow> memb_sorted xs x \<longleftrightarrow> x \<in> set xs"
by (induct xs) (auto simp add: Ball_def)


fun insertion_sort where
   "insertion_sort x [] = [x]"
 | "insertion_sort x (y # xs) =
    (if (y < x) then y # insertion_sort x xs else 
     (if (x = y) then y # xs else x # y # xs))"

lemma insertion_sort_correct :
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow>
   distinct (insertion_sort x xs) \<and> 
   sorted (insertion_sort x xs) \<and>
   set (insertion_sort x xs) = set (x # xs)"
by (induct xs) (auto simp add: Ball_def)

fun delete_sorted where
   "delete_sorted x [] = []"
 | "delete_sorted x (y # xs) =
    (if (y < x) then y # delete_sorted x xs else 
     (if (x = y) then xs else y # xs))"

lemma delete_sorted_correct :
  "sorted xs \<Longrightarrow> distinct xs \<Longrightarrow>
   distinct (delete_sorted x xs) \<and> 
   sorted (delete_sorted x xs) \<and>
   set (delete_sorted x xs) = set xs - {x}"
apply (induct xs) 
apply simp
apply (simp add: Ball_def set_eq_iff)
apply (metis order_less_le)
done

end
