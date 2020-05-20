(*  Title:       Deriving class instances for datatypes
    Author:      Christian Sternagel and René Thiemann  <christian.sternagel|rene.thiemann@uibk.ac.at>
    Maintainer:  Christian Sternagel and René Thiemann 
    License:     LGPL
*)
subsection \<open>Defining Compare-Order-Instances for Common Types\<close>

theory Compare_Order_Instances
imports
  Compare_Instances
  "HOL-Library.List_Lexorder"
  "HOL-Library.Product_Lexorder"
  "HOL-Library.Option_ord"
begin

text \<open>We now also instantiate class @{class compare_order} and not only @{class compare}.
  Here, we also prove that our definitions do not clash with existing orders on
  @{type list}, @{type option}, and @{type prod}.
  
  For @{type sum} we just define the linear orders via their comparator.\<close>

derive compare_order sum

instance list :: (compare_order)compare_order
proof
  note [simp] = le_of_comp_def lt_of_comp_def comparator_of_def
  show "le_of_comp (compare :: 'a list comparator) = (\<le>)" 
    unfolding compare_list_def compare_is_comparator_of 
  proof (intro ext)
    fix xs ys :: "'a list"
    show "le_of_comp (comparator_list comparator_of) xs ys = (xs \<le> ys)"
    proof (induct xs arbitrary: ys)
      case (Nil ys)
      show ?case
        by (cases ys, simp_all)
    next
      case (Cons x xs yys) note IH = this
      thus ?case
      proof (cases yys)
        case Nil
        thus ?thesis by auto
      next
        case (Cons y ys)
        show ?thesis unfolding Cons
          using IH[of ys]
          by (cases x y rule: linorder_cases, auto)
      qed
    qed
  qed
  show "lt_of_comp (compare :: 'a list comparator) = (<)" 
    unfolding compare_list_def compare_is_comparator_of 
  proof (intro ext)
    fix xs ys :: "'a list"
    show "lt_of_comp (comparator_list comparator_of) xs ys = (xs < ys)"
    proof (induct xs arbitrary: ys)
      case (Nil ys)
      show ?case
        by (cases ys, simp_all)
    next
      case (Cons x xs yys) note IH = this
      thus ?case
      proof (cases yys)
        case Nil
        thus ?thesis by auto
      next
        case (Cons y ys)
        show ?thesis unfolding Cons
          using IH[of ys]
          by (cases x y rule: linorder_cases, auto)
      qed
    qed
  qed
qed

instance prod :: (compare_order, compare_order)compare_order
proof
  note [simp] = le_of_comp_def lt_of_comp_def comparator_of_def
  show "le_of_comp (compare :: ('a,'b)prod comparator) = (\<le>)" 
    unfolding compare_prod_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "('a,'b)prod"
    show "le_of_comp (comparator_prod comparator_of comparator_of) xy1 xy2 = (xy1 \<le> xy2)"
      by (cases xy1, cases xy2, auto)
  qed
  show "lt_of_comp (compare :: ('a,'b)prod comparator) = (<)" 
    unfolding compare_prod_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "('a,'b)prod"
    show "lt_of_comp (comparator_prod comparator_of comparator_of) xy1 xy2 = (xy1 < xy2)"
      by (cases xy1, cases xy2, auto)
  qed
qed

instance option :: (compare_order)compare_order
proof
  note [simp] = le_of_comp_def lt_of_comp_def comparator_of_def
  show "le_of_comp (compare :: 'a option comparator) = (\<le>)" 
    unfolding compare_option_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "'a option"
    show "le_of_comp (comparator_option comparator_of) xy1 xy2 = (xy1 \<le> xy2)"
      by (cases xy1, (cases xy2, auto split: if_splits)+)
  qed
  show "lt_of_comp (compare :: 'a option comparator) = (<)" 
    unfolding compare_option_def compare_is_comparator_of 
  proof (intro ext)
    fix xy1 xy2 :: "'a option"
    show "lt_of_comp (comparator_option comparator_of) xy1 xy2 = (xy1 < xy2)"
      by (cases xy1, (cases xy2, auto split: if_splits)+)
  qed
qed

end
