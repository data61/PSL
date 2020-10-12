section \<open>Challenge 2.B\<close>
theory Challenge2B
  imports Challenge2A
begin

text \<open>We did not get very far on this part of the competition. Only Task 2 was finished.\<close>

subsection \<open>Basic Definitions\<close>

datatype tree = Leaf | Node int (lc: tree) (rc: tree)

text \<open>Analogous to @{term left_spec} from 2.A.\<close>
definition
  "right_spec xs j =
  (if (\<exists>i>j. xs ! i < xs ! j) then Some (LEAST i. i > j \<and> xs ! i < xs ! j) else None)"

context
  fixes xs :: "int list"
  assumes "distinct xs"
begin

subsection \<open>Specification of the Parent\<close>
definition
  "parent i = (
    case (left_spec xs i, right_spec xs i) of
      (None, None) \<Rightarrow> None
    | (Some x, None) \<Rightarrow> Some x
    | (None, Some y) \<Rightarrow> Some y
    | (Some x, Some y) \<Rightarrow> Some (max x y)
  )"

subsection \<open>The Heap Property (Task 2)\<close>

lemma parent_heap:
  assumes "parent j = Some p"
  shows "xs ! j > xs ! p"
proof -
  note [simp del] = left_spec_None_iff swap_adhoc
  show ?thesis
  proof (cases "(\<exists>i<j. xs ! i < xs ! j)")
    case True
    then have *: "xs ! the (left_spec xs j) < xs ! j" "left_spec xs j \<noteq> None"
      unfolding left_spec_def by auto (metis (no_types, lifting) GreatestI_nat True less_le)
    show ?thesis
    proof (cases "(\<exists>i>j. xs ! i < xs ! j)")
      case True
      then have "xs ! the (right_spec xs j) < xs ! j" "right_spec xs j \<noteq> None"
        unfolding right_spec_def by auto (metis (no_types, lifting) LeastI)
      then show ?thesis
        using * assms unfolding parent_def by auto
    next
      case False
      then have "right_spec xs j = None"
        unfolding right_spec_def by auto
      then show ?thesis
        using * assms unfolding parent_def by auto
    qed
  next
    case False
    then have [simp]: "left_spec xs j = None"
      unfolding left_spec_def by auto
    show ?thesis
    proof (cases "(\<exists>i>j. xs ! i < xs ! j)")
      case True
      then have "xs ! the (right_spec xs j) < xs ! j" "right_spec xs j \<noteq> None"
        unfolding right_spec_def by auto (metis (no_types, lifting) LeastI)
      then show ?thesis
        using assms unfolding parent_def by auto
    next
      case False
      then have "right_spec xs j = None"
        unfolding right_spec_def by auto
      then show ?thesis
        using assms unfolding parent_def by auto
    qed
  qed
qed

end

end