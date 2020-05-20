theory Efficient_Distinct
imports 
  Automatic_Refinement.Misc (*mergesort*)
  "HOL-Library.List_Lexorder"
  "HOL-Library.Product_Lexorder"
  "HOL-Library.Char_ord"
  TopoS_Util
begin

text \<open>efficient distinct code\<close>

  lemma list_length_iff_distinct: 
  "\<lbrakk>set xs = set ys; distinct ys\<rbrakk> \<Longrightarrow> distinct xs \<longleftrightarrow> length xs = length ys"
  by (metis distinct_card card_distinct)

  lemma distinct_by_mergesort: "(length (mergesort_remdups xs) = length xs) \<longleftrightarrow> distinct xs"
  by (metis list_length_iff_distinct mergesort_remdups_correct)

  lemma [code]: "distinct xs = (length (mergesort_remdups xs) = length xs)"
  by (fact distinct_by_mergesort[symmetric])

  text\<open>providing tail recursive versions of certain functions\<close>
  (*otherwise scala code generated with this code always produces a StackOverflowException for large inputs*)

text\<open>@{const List.map}\<close>

  fun map_tailrec ::  "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "map_tailrec f [] accs = accs" | 
  "map_tailrec f (a#as) accs = (map_tailrec f as ((f a)#accs))"

  lemma map_tailrec_is_listmap: "rev (map_tailrec f l accs) = (rev accs)@(List.map f l)"
  by (induction l accs rule: map_tailrec.induct) auto

  definition efficient_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
    "efficient_map f l \<equiv> rev (map_tailrec f l [])"

  lemma [code]: "List.map f l = efficient_map f l"
  by (simp add: efficient_map_def map_tailrec_is_listmap)

text\<open>@{const merge}\<close>

 (*inefficient version*)
 fun merge_tailrec_inefficient :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "merge_tailrec_inefficient (a#as) (b#bs) accs = (if a < b
      then merge_tailrec_inefficient (as) (b#bs) (accs@[a])
      else if a = b then merge_tailrec_inefficient (as) (bs) (accs@[a])
      else merge_tailrec_inefficient (a#as) (bs) (accs@[b]))"
  | "merge_tailrec_inefficient [] bs accs= accs@bs"
  | "merge_tailrec_inefficient as [] accs = accs@as"

  lemma merge_tailrec_inefficient_prepend:
  "merge_tailrec_inefficient as bs (a # accs) = a # merge_tailrec_inefficient as bs accs"
  by (induction as bs accs rule: merge_tailrec_inefficient.induct) auto

  lemma merge_as_tailrec_inefficient: "merge as bs = merge_tailrec_inefficient as bs []"
  by (induction as bs rule: merge.induct)  (auto simp: merge_tailrec_inefficient_prepend)

 fun merge_tailrec :: "('a::linorder) list \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
    "merge_tailrec (a#as) (b#bs) accs = (if a < b
      then merge_tailrec (as) (b#bs) (a#accs)
      else if a = b then merge_tailrec (as) (bs) (a#accs)
      else merge_tailrec (a#as) (bs) (b#accs))"
  | "merge_tailrec [] bs accs= (rev accs)@bs"
  | "merge_tailrec as [] accs = (rev accs)@as"

  lemma merge_tailrec_listappend:
    "merge_tailrec as bs (accs1@accs2) = (rev accs2)@(merge_tailrec as bs accs1)"
  proof (induction as bs "accs1@accs2" arbitrary: accs1 accs2 rule: merge_tailrec.induct)
    case (1 a as b bs)
    thus ?case
      by (cases a b rule: linorder_cases) (metis append_Cons merge_tailrec.simps(1))+
  qed auto

  lemma merge_tailrec_acc_append: 
    "merge_tailrec as bs (accs@[a]) = a#(merge_tailrec as bs (accs))"
  by (induction as bs accs rule: merge_tailrec.induct) auto

  lemma merge_inefficient_as_efficient:
    "merge_tailrec_inefficient as bs (rev accs) = (merge_tailrec as bs accs)"
  proof (induction as bs accs arbitrary: accs rule: merge_tailrec_inefficient.induct)
    case (1 a as b bs)
    thus ?case
      by (cases a b rule: linorder_cases) (metis merge_tailrec.simps(1) merge_tailrec_inefficient.simps(1) rev.simps(2))+
  qed auto

  lemma [code]: "merge as bs = merge_tailrec as bs []"
  apply (subst merge_as_tailrec_inefficient)
  apply (subst merge_inefficient_as_efficient[where accs = "[]", unfolded rev.simps(1)])
  apply (rule refl)
  done

(*import scala.annotation.tailrec*)
  export_code distinct checking Scala


  value "distinct [(CHR ''A'')]"
  value "distinct [''a'', ''b'']"
  value "distinct [(''a'', ''b'')]" 
  value "distinct (map fst [(''a'', ''b''), (''a'', ''c'')])"

end
