theory TTree
imports Main ConstOn "List-Interleavings"
begin

subsubsection \<open>Prefix-closed sets of lists\<close>

definition downset :: "'a list set \<Rightarrow> bool" where
  "downset xss = (\<forall>x n. x \<in> xss \<longrightarrow> take n x \<in> xss)"

lemma downsetE[elim]:
  "downset xss  \<Longrightarrow> xs \<in> xss \<Longrightarrow> butlast xs \<in> xss"
by (auto simp add: downset_def butlast_conv_take)

lemma downset_appendE[elim]:
  "downset xss \<Longrightarrow> xs@ys \<in> xss \<Longrightarrow> xs \<in> xss"
by (auto simp add: downset_def) (metis append_eq_conv_conj)

lemma downset_hdE[elim]:
  "downset xss \<Longrightarrow> xs \<in> xss \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> [hd xs] \<in> xss"
by (auto simp add: downset_def) (metis take_0 take_Suc)


lemma downsetI[intro]:
  assumes "\<And> xs. xs \<in> xss \<Longrightarrow> xs \<noteq> [] \<Longrightarrow> butlast xs \<in> xss"
  shows  "downset xss"
unfolding downset_def
proof(intro impI allI )
  from assms
  have butlast: "\<And> xs. xs \<in> xss \<Longrightarrow> butlast xs \<in> xss"
    by (metis butlast.simps(1))

  fix xs n
  assume "xs \<in> xss"
  show "take n xs \<in> xss"
  proof(cases "n \<le> length xs")
  case True
    from this
    show ?thesis
    proof(induction rule: inc_induct)
    case base with \<open>xs \<in> xss\<close> show ?case by simp
    next
    case (step n')
      from butlast[OF step.IH] step(2)
      show ?case by (simp add: butlast_take)
    qed      
  next
  case False with \<open>xs \<in> xss\<close> show ?thesis by simp
  qed
qed

lemma [simp]: "downset {[]}" by auto

lemma downset_mapI: "downset xss \<Longrightarrow> downset (map f ` xss)"
  by (fastforce simp add: map_butlast[symmetric])

lemma downset_filter:
  assumes "downset xss"
  shows "downset (filter P ` xss)"
proof(rule, elim imageE, clarsimp)
  fix xs
  assume "xs \<in> xss"
  thus "butlast (filter P xs) \<in> filter P ` xss"
  proof (induction xs rule: rev_induct)
    case Nil thus ?case by force
  next
    case snoc
    thus ?case using \<open>downset xss\<close>  by (auto intro: snoc.IH)
  qed
qed

lemma downset_set_subset:
  "downset ({xs. set xs \<subseteq> S})"
by (auto dest: in_set_butlastD)

subsubsection \<open>The type of infinite labeled trees\<close>

typedef 'a ttree = "{xss :: 'a list set . [] \<in> xss \<and> downset xss}" by auto

setup_lifting type_definition_ttree

subsubsection \<open>Deconstructors\<close>

lift_definition possible ::"'a ttree \<Rightarrow> 'a \<Rightarrow> bool"
  is "\<lambda> xss x. \<exists> xs. x#xs \<in> xss".

lift_definition nxt ::"'a ttree \<Rightarrow> 'a \<Rightarrow> 'a ttree"
  is "\<lambda> xss x. insert [] {xs | xs. x#xs \<in> xss}"
  by (auto simp add: downset_def take_Suc_Cons[symmetric] simp del: take_Suc_Cons)

subsubsection \<open>Trees as set of paths\<close>

lift_definition paths :: "'a ttree \<Rightarrow> 'a list set" is "(\<lambda> x. x)".

lemma paths_inj: "paths t = paths t' \<Longrightarrow> t = t'" by transfer auto

lemma paths_injs_simps[simp]: "paths t = paths t' \<longleftrightarrow> t = t'" by transfer auto

lemma paths_Nil[simp]: "[] \<in> paths t" by transfer simp

lemma paths_not_empty[simp]: "(paths t = {}) \<longleftrightarrow> False" by transfer auto

lemma paths_Cons_nxt:
  "possible t x \<Longrightarrow> xs \<in> paths (nxt t x) \<Longrightarrow> (x#xs) \<in> paths t"
  by transfer auto

lemma paths_Cons_nxt_iff:
  "possible t x \<Longrightarrow> xs \<in> paths (nxt t x) \<longleftrightarrow> (x#xs) \<in> paths t"
  by transfer auto

lemma possible_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> possible t x \<Longrightarrow> possible t' x"
  by transfer auto

lemma nxt_mono:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (nxt t x) \<subseteq> paths (nxt t' x)"
  by transfer auto

lemma ttree_eqI: "(\<And> x xs. x#xs \<in> paths t \<longleftrightarrow> x#xs \<in> paths t') \<Longrightarrow> t = t'"
  apply (rule paths_inj)
  apply (rule set_eqI)
  apply (case_tac x)
  apply auto
  done

lemma paths_nxt[elim]:
 assumes "xs \<in> paths (nxt t x)"
 obtains "x#xs \<in> paths t"  | "xs = []"
 using assms by transfer auto

lemma Cons_path: "x # xs \<in> paths t \<longleftrightarrow> possible t x \<and> xs \<in> paths (nxt t x)"
 by transfer auto

lemma Cons_pathI[intro]:
  assumes "possible t x \<longleftrightarrow> possible t' x"
  assumes "possible t x \<Longrightarrow> possible t' x \<Longrightarrow> xs \<in> paths (nxt t x) \<longleftrightarrow> xs \<in> paths (nxt t' x)"
  shows  "x # xs \<in> paths t \<longleftrightarrow> x # xs \<in> paths t'"
using assms by (auto simp add: Cons_path)

lemma paths_nxt_eq: "xs \<in> paths (nxt t x) \<longleftrightarrow> xs = [] \<or> x#xs \<in> paths t"
 by transfer auto

lemma ttree_coinduct:
  assumes "P t t'"
  assumes "\<And> t t' x . P t t' \<Longrightarrow> possible t x \<longleftrightarrow> possible t' x"
  assumes "\<And> t t' x . P t t' \<Longrightarrow> possible t x \<Longrightarrow> possible t' x \<Longrightarrow> P (nxt t x) (nxt t' x)"
  shows "t = t'"
proof(rule paths_inj, rule set_eqI)
  fix xs
  from assms(1)
  show "xs \<in> paths t \<longleftrightarrow> xs \<in> paths t'"
  proof (induction xs arbitrary: t t')
  case Nil thus ?case by simp
  next
  case (Cons x xs t t')
    show ?case
    proof (rule Cons_pathI)
      from \<open>P t t'\<close>
      show "possible t x \<longleftrightarrow> possible t' x" by (rule assms(2))
    next
      assume "possible t x" and "possible t' x"
      with \<open>P t t'\<close>
      have "P (nxt t x) (nxt t' x)" by (rule assms(3))
      thus "xs \<in> paths (nxt t x) \<longleftrightarrow> xs \<in> paths (nxt t' x)" by (rule Cons.IH)
    qed
  qed
qed

subsubsection \<open>The carrier of a tree\<close>

lift_definition carrier :: "'a ttree \<Rightarrow> 'a set" is "\<lambda> xss. \<Union>(set ` xss)".

lemma carrier_mono: "paths t \<subseteq> paths t' \<Longrightarrow> carrier t \<subseteq> carrier t'" by transfer auto

lemma carrier_possible:
  "possible t x \<Longrightarrow> x \<in> carrier t" by transfer force

lemma carrier_possible_subset:
   "carrier t \<subseteq> A \<Longrightarrow> possible t x \<Longrightarrow> x \<in> A" by transfer force

lemma carrier_nxt_subset:
  "carrier (nxt t x) \<subseteq> carrier t"
  by transfer auto

lemma Union_paths_carrier: "(\<Union>x\<in>paths t. set x) = carrier t"
  by transfer auto


subsubsection \<open>Repeatable trees\<close>

definition repeatable where "repeatable t = (\<forall>x . possible t x \<longrightarrow> nxt t x = t)"

lemma nxt_repeatable[simp]: "repeatable t \<Longrightarrow> possible t x \<Longrightarrow> nxt t x = t"
  unfolding repeatable_def by auto

subsubsection \<open>Simple trees\<close>

lift_definition empty :: "'a ttree" is "{[]}" by auto

lemma possible_empty[simp]: "possible empty x' \<longleftrightarrow> False"
  by transfer auto

lemma nxt_not_possible[simp]: "\<not> possible t x \<Longrightarrow> nxt t x = empty"
  by transfer auto

lemma paths_empty[simp]: "paths empty = {[]}" by transfer auto

lemma carrier_empty[simp]: "carrier empty = {}" by transfer auto

lemma repeatable_empty[simp]: "repeatable empty" unfolding repeatable_def by transfer auto
  

lift_definition single :: "'a \<Rightarrow> 'a ttree" is "\<lambda> x. {[], [x]}"
  by auto

lemma possible_single[simp]: "possible (single x) x' \<longleftrightarrow> x = x'"
  by transfer auto

lemma nxt_single[simp]: "nxt (single x) x' =  empty"
  by transfer auto

lemma carrier_single[simp]: "carrier (single y) = {y}"
  by transfer auto

lemma paths_single[simp]: "paths (single x) = {[], [x]}"
  by transfer auto

lift_definition many_calls :: "'a \<Rightarrow> 'a ttree" is "\<lambda> x. range (\<lambda> n. replicate n x)"
  by (auto simp add: downset_def)

lemma possible_many_calls[simp]: "possible (many_calls x) x' \<longleftrightarrow> x = x'"
  by transfer (force simp add: Cons_replicate_eq)

lemma nxt_many_calls[simp]: "nxt (many_calls x) x' = (if x' =  x then many_calls x else empty)"
  by transfer (force simp add: Cons_replicate_eq)

lemma repeatable_many_calls: "repeatable (many_calls x)"
  unfolding repeatable_def by auto

lemma carrier_many_calls[simp]: "carrier (many_calls x) = {x}" by transfer auto

lift_definition anything :: "'a ttree" is "UNIV"
  by auto

lemma possible_anything[simp]: "possible anything x' \<longleftrightarrow> True"
  by transfer auto

lemma nxt_anything[simp]: "nxt anything x = anything"
  by  transfer auto

lemma paths_anything[simp]:
  "paths anything = UNIV" by transfer auto

lemma carrier_anything[simp]:
  "carrier anything = UNIV" 
  apply (auto simp add: Union_paths_carrier[symmetric])
  apply (rule_tac x = "[x]" in exI)
  apply simp
  done

lift_definition many_among :: "'a set \<Rightarrow> 'a ttree" is "\<lambda> S. {xs . set xs \<subseteq> S}"
  by (auto intro: downset_set_subset)

lemma carrier_many_among[simp]: "carrier (many_among S) = S"
 by transfer (auto, metis List.set_insert bot.extremum insertCI insert_subset list.set(1))

subsubsection \<open>Intersection of two trees\<close>

lift_definition intersect :: "'a ttree \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree" (infixl "\<inter>\<inter>" 80)
  is "(\<inter>)"
  by (auto simp add: downset_def)

lemma paths_intersect[simp]: "paths (t \<inter>\<inter> t') = paths t \<inter> paths t'"
  by transfer auto

lemma carrier_intersect: "carrier (t \<inter>\<inter> t') \<subseteq> carrier t \<inter> carrier t'"
  unfolding Union_paths_carrier[symmetric]
  by auto
  

subsubsection \<open>Disjoint union of trees\<close>

lift_definition either :: "'a ttree \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree" (infixl "\<oplus>\<oplus>" 80)
  is "(\<union>)"
  by (auto simp add: downset_def)
  
lemma either_empty1[simp]: "empty \<oplus>\<oplus> t = t"
  by transfer auto
lemma either_empty2[simp]: "t \<oplus>\<oplus> empty = t"
  by transfer auto
lemma either_sym[simp]: "t \<oplus>\<oplus> t2 = t2 \<oplus>\<oplus> t"
  by transfer auto
lemma either_idem[simp]: "t \<oplus>\<oplus> t = t"
  by transfer auto

lemma possible_either[simp]: "possible (t \<oplus>\<oplus> t') x \<longleftrightarrow> possible t x \<or> possible t' x"
  by transfer auto

lemma nxt_either[simp]: "nxt (t \<oplus>\<oplus> t') x = nxt t x \<oplus>\<oplus> nxt t' x"
  by transfer auto

lemma paths_either[simp]: "paths (t \<oplus>\<oplus> t') = paths t \<union> paths t'"
  by transfer simp

lemma carrier_either[simp]:
  "carrier (t \<oplus>\<oplus> t') = carrier t \<union> carrier t'"
  by transfer simp

lemma either_contains_arg1: "paths t \<subseteq> paths (t \<oplus>\<oplus> t')"
  by transfer fastforce

lemma either_contains_arg2: "paths t' \<subseteq> paths (t \<oplus>\<oplus> t')"
  by transfer fastforce

lift_definition Either :: "'a ttree set \<Rightarrow> 'a ttree"  is "\<lambda> S. insert [] (\<Union>S)"
  by (auto simp add: downset_def)

lemma paths_Either: "paths (Either ts) = insert [] (\<Union>(paths ` ts))"
  by transfer auto

subsubsection \<open>Merging of trees\<close>

lemma ex_ex_eq_hint: "(\<exists>x. (\<exists>xs ys. x = f xs ys \<and> P xs ys) \<and> Q x) \<longleftrightarrow> (\<exists>xs ys. Q (f xs ys) \<and> P xs ys)"
  by auto

lift_definition both :: "'a ttree \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree" (infixl "\<otimes>\<otimes>" 86)
  is "\<lambda> xss yss . \<Union> {xs \<otimes> ys | xs ys. xs \<in> xss \<and> ys \<in> yss}"
  by (force simp: ex_ex_eq_hint dest: interleave_butlast)

lemma both_assoc[simp]: "t \<otimes>\<otimes> (t' \<otimes>\<otimes> t'') = (t \<otimes>\<otimes> t') \<otimes>\<otimes> t''"
  apply transfer
  apply auto
  apply (metis interleave_assoc2)
  apply (metis interleave_assoc1)
  done

lemma both_comm: "t \<otimes>\<otimes> t' = t' \<otimes>\<otimes> t"
  by transfer (auto, (metis interleave_comm)+)

lemma both_empty1[simp]: "empty \<otimes>\<otimes> t = t"
  by transfer auto

lemma both_empty2[simp]: "t \<otimes>\<otimes> empty = t"
  by transfer auto

lemma paths_both: "xs \<in> paths (t \<otimes>\<otimes> t') \<longleftrightarrow> (\<exists> ys \<in> paths t. \<exists> zs \<in> paths t'. xs \<in> ys \<otimes> zs)"
  by transfer fastforce

lemma both_contains_arg1: "paths t \<subseteq> paths (t \<otimes>\<otimes> t')"
  by transfer fastforce

lemma both_contains_arg2: "paths t' \<subseteq> paths (t \<otimes>\<otimes> t')"
  by transfer fastforce

lemma both_mono1:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (t \<otimes>\<otimes> t'') \<subseteq> paths (t' \<otimes>\<otimes> t'')"
  by transfer auto

lemma both_mono2:
  "paths t \<subseteq> paths t' \<Longrightarrow> paths (t'' \<otimes>\<otimes> t) \<subseteq> paths (t'' \<otimes>\<otimes> t')"
  by transfer auto

lemma possible_both[simp]: "possible (t \<otimes>\<otimes> t') x \<longleftrightarrow> possible t x \<or> possible t' x"
proof
  assume "possible (t \<otimes>\<otimes> t') x"
  then obtain xs where "x#xs \<in> paths (t \<otimes>\<otimes> t')"
    by transfer auto
  
  from \<open>x#xs \<in> paths (t \<otimes>\<otimes> t')\<close>
  obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "x#xs \<in> ys \<otimes> zs"
    by transfer auto

  from \<open>x#xs \<in> ys \<otimes> zs\<close>
  have "ys \<noteq> [] \<and> hd ys = x  \<or> zs \<noteq> [] \<and> hd zs = x"
    by (auto elim: interleave_cases)
  thus "possible t x \<or> possible t' x"
    using  \<open>ys \<in> paths t\<close>   \<open>zs \<in> paths t'\<close>
    by transfer auto
next
  assume "possible t x \<or> possible t' x"
  then obtain xs where "x#xs\<in> paths t \<or> x#xs\<in> paths t'"
    by transfer auto
  from this have "x#xs \<in> paths (t \<otimes>\<otimes> t')" by (auto dest: subsetD[OF both_contains_arg1]  subsetD[OF both_contains_arg2])
  thus "possible (t \<otimes>\<otimes> t') x" by transfer auto
qed

lemma nxt_both:
    "nxt (t' \<otimes>\<otimes> t) x = (if possible t' x \<and> possible t x then nxt t' x \<otimes>\<otimes> t \<oplus>\<oplus> t' \<otimes>\<otimes> nxt t x else
                           if possible t' x then nxt t' x \<otimes>\<otimes> t else
                           if possible t x then t' \<otimes>\<otimes> nxt t x else
                           empty)"
  by (transfer, auto 4 4 intro: interleave_intros)

lemma Cons_both:
    "x # xs \<in> paths (t' \<otimes>\<otimes> t) \<longleftrightarrow> (if possible t' x \<and> possible t x then xs \<in> paths (nxt t' x \<otimes>\<otimes> t) \<or> xs \<in> paths (t' \<otimes>\<otimes> nxt t x) else
                           if possible t' x then xs \<in> paths (nxt t' x \<otimes>\<otimes> t) else
                           if possible t x then xs \<in> paths (t' \<otimes>\<otimes> nxt t x) else
                           False)"
  apply (auto simp add: paths_Cons_nxt_iff[symmetric] nxt_both)
  by (metis paths.rep_eq possible.rep_eq possible_both)

lemma Cons_both_possible_leftE: "possible t x \<Longrightarrow> xs \<in> paths (nxt t x \<otimes>\<otimes> t') \<Longrightarrow> x#xs \<in> paths (t \<otimes>\<otimes> t')"
  by (auto simp add: Cons_both)
lemma Cons_both_possible_rightE: "possible t' x \<Longrightarrow> xs \<in> paths (t \<otimes>\<otimes> nxt t' x) \<Longrightarrow> x#xs \<in> paths (t \<otimes>\<otimes> t')"
  by (auto simp add: Cons_both)

lemma either_both_distr[simp]:
  "t' \<otimes>\<otimes> t \<oplus>\<oplus> t' \<otimes>\<otimes> t'' = t' \<otimes>\<otimes> (t \<oplus>\<oplus> t'')"
  by transfer auto

lemma either_both_distr2[simp]:
  "t' \<otimes>\<otimes> t \<oplus>\<oplus> t'' \<otimes>\<otimes> t = (t' \<oplus>\<oplus> t'') \<otimes>\<otimes> t"
  by transfer auto

lemma nxt_both_repeatable[simp]:
  assumes [simp]: "repeatable t'"
  assumes [simp]: "possible t' x"
  shows "nxt (t' \<otimes>\<otimes> t) x = t' \<otimes>\<otimes> (t \<oplus>\<oplus> nxt t x)"
  by (auto simp add: nxt_both)

lemma nxt_both_many_calls[simp]: "nxt (many_calls x \<otimes>\<otimes> t) x = many_calls x \<otimes>\<otimes> (t  \<oplus>\<oplus> nxt t x)"
  by (simp add: repeatable_many_calls)

lemma repeatable_both_self[simp]:
  assumes [simp]: "repeatable t"
  shows "t \<otimes>\<otimes> t = t"
  apply (intro paths_inj set_eqI)
  apply (induct_tac x)
  apply (auto simp add: Cons_both paths_Cons_nxt_iff[symmetric])
  apply (metis Cons_both both_empty1 possible_empty)+
  done

lemma repeatable_both_both[simp]:
  assumes "repeatable t"
  shows "t \<otimes>\<otimes> t' \<otimes>\<otimes> t = t \<otimes>\<otimes> t'"
  by (metis repeatable_both_self[OF assms]  both_assoc both_comm)

lemma repeatable_both_both2[simp]:
  assumes "repeatable t"
  shows "t' \<otimes>\<otimes> t \<otimes>\<otimes> t = t' \<otimes>\<otimes> t"
  by (metis repeatable_both_self[OF assms]  both_assoc both_comm)


lemma repeatable_both_nxt:
  assumes "repeatable t"
  assumes "possible t' x"
  assumes "t' \<otimes>\<otimes> t = t'"
  shows "nxt t' x \<otimes>\<otimes> t = nxt t' x"
proof(rule classical)
  assume "nxt t' x \<otimes>\<otimes> t \<noteq> nxt t' x"
  hence "(nxt t' x \<oplus>\<oplus> t') \<otimes>\<otimes> t \<noteq> nxt t' x" by (metis (no_types) assms(1) both_assoc repeatable_both_self)
  thus "nxt t' x \<otimes>\<otimes> t = nxt t' x"  by (metis (no_types) assms either_both_distr2 nxt_both nxt_repeatable)
qed

lemma repeatable_both_both_nxt:
  assumes "t' \<otimes>\<otimes> t = t'"
  shows "t' \<otimes>\<otimes> t'' \<otimes>\<otimes> t = t' \<otimes>\<otimes> t''"
  by (metis assms both_assoc both_comm)


lemma carrier_both[simp]:
  "carrier (t \<otimes>\<otimes> t') = carrier t \<union> carrier t'"
proof-
  {
  fix x
  assume "x \<in> carrier (t \<otimes>\<otimes> t')"
  then obtain xs where "xs \<in> paths (t \<otimes>\<otimes> t')" and "x \<in> set xs" by transfer auto
  then obtain ys zs where "ys \<in> paths t" and "zs \<in> paths t'" and "xs \<in> interleave ys zs"
    by (auto simp add: paths_both)
  from this(3) have "set xs = set ys \<union> set zs" by (rule interleave_set)
  with \<open>ys \<in> _\<close> \<open>zs \<in> _\<close> \<open>x \<in> set xs\<close>
  have "x \<in> carrier t \<union> carrier t'"  by transfer auto
  }
  moreover
  note subsetD[OF carrier_mono[OF both_contains_arg1[where t=t and t' = t']]]
       subsetD[OF carrier_mono[OF both_contains_arg2[where t=t and t' = t']]]
  ultimately
  show ?thesis by auto
qed

subsubsection \<open>Removing elements from a tree\<close>

lift_definition without :: "'a \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree"
  is "\<lambda> x xss. filter (\<lambda> x'. x' \<noteq> x) ` xss"
  by (auto intro: downset_filter)(metis filter.simps(1) imageI)

lemma paths_withoutI:
  assumes "xs \<in> paths t"
  assumes "x \<notin> set xs"
  shows "xs \<in> paths (without x t)"
proof-
  from assms(2)
  have "filter (\<lambda> x'. x' \<noteq> x) xs = xs"  by (auto simp add: filter_id_conv)
  with assms(1)
  have "xs \<in> filter (\<lambda> x'. x' \<noteq> x)` paths t" by (metis imageI)
  thus ?thesis by transfer
qed

lemma carrier_without[simp]: "carrier (without x t) = carrier t - {x}"
  by transfer auto

lift_definition ttree_restr :: "'a set \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree" is "\<lambda> S xss. filter (\<lambda> x'. x' \<in> S) ` xss"
  by (auto intro: downset_filter)(metis filter.simps(1) imageI)

lemma filter_paths_conv_free_restr:
  "filter (\<lambda> x' . x' \<in> S) ` paths t = paths (ttree_restr S t)" by transfer auto

lemma filter_paths_conv_free_restr2:
  "filter (\<lambda> x' . x' \<notin> S) ` paths t = paths (ttree_restr (- S) t)" by transfer auto

lemma filter_paths_conv_free_without:
  "filter (\<lambda> x' . x' \<noteq> y) ` paths t = paths (without y t)" by transfer auto

lemma ttree_restr_is_empty: "carrier t \<inter> S = {} \<Longrightarrow> ttree_restr S t = empty"
  apply transfer
  apply (auto del: iffI )
  apply (metis SUP_bot_conv(2) SUP_inf inf_commute inter_set_filter set_empty)
  apply force
  done

lemma ttree_restr_noop: "carrier t \<subseteq> S \<Longrightarrow> ttree_restr S t = t"
  apply transfer
  apply (auto simp add: image_iff)
  apply (metis SUP_le_iff contra_subsetD filter_True)
  apply (rule_tac x = x in bexI)
  apply (metis SUP_upper contra_subsetD filter_True)
  apply assumption
  done

lemma ttree_restr_tree_restr[simp]:
  "ttree_restr S (ttree_restr S' t) = ttree_restr (S' \<inter> S) t"
  by transfer (simp add: image_comp comp_def)

lemma ttree_restr_both:
  "ttree_restr S (t \<otimes>\<otimes> t') = ttree_restr S t \<otimes>\<otimes> ttree_restr S t'"
  by (force simp add: paths_both filter_paths_conv_free_restr[symmetric] intro: paths_inj filter_interleave  elim: interleave_filter)

lemma ttree_restr_nxt_subset: "x \<in> S \<Longrightarrow> paths (ttree_restr S (nxt t x)) \<subseteq> paths (nxt (ttree_restr S t) x)"
  by transfer (force simp add: image_iff)

lemma ttree_restr_nxt_subset2: "x \<notin> S \<Longrightarrow> paths (ttree_restr S (nxt t x)) \<subseteq> paths (ttree_restr S t)"
  apply transfer
  apply auto
  apply force
  by (metis filter.simps(2) imageI)

lemma ttree_restr_possible: "x \<in> S \<Longrightarrow> possible t x \<Longrightarrow> possible (ttree_restr S t) x"
  by transfer force

lemma ttree_restr_possible2: "possible (ttree_restr S t') x \<Longrightarrow> x \<in> S" 
  by transfer (auto, metis filter_eq_Cons_iff)

lemma carrier_ttree_restr[simp]:
  "carrier (ttree_restr S t) = S \<inter> carrier t"
  by transfer auto

(*
lemma intersect_many_among: "t \<inter>\<inter> many_among S = ttree_restr S t"
  apply transfer
  apply auto
*)

subsubsection \<open>Multiple variables, each called at most once\<close>

lift_definition singles :: "'a set \<Rightarrow> 'a ttree" is "\<lambda> S. {xs. \<forall> x \<in> S. length (filter (\<lambda> x'. x' = x) xs) \<le> 1}"
  apply auto
  apply (rule downsetI)
  apply auto
  apply (subst (asm) append_butlast_last_id[symmetric]) back
  apply simp
  apply (subst (asm) filter_append)
  apply auto
  done

lemma possible_singles[simp]: "possible (singles S) x"
  apply transfer'
  apply (rule_tac x = "[]" in exI)
  apply auto
  done

lemma length_filter_mono[intro]:
  assumes "(\<And> x. P x \<Longrightarrow> Q x)"
  shows "length (filter P xs) \<le> length (filter Q xs)"
by (induction xs) (auto dest: assms)

lemma nxt_singles[simp]: "nxt (singles S) x' =  (if x' \<in> S then without x' (singles S) else singles S)"
  apply transfer'
  apply auto
  apply (rule rev_image_eqI[where x = "[]"], auto)[1]
  apply (rule_tac x = x in rev_image_eqI)
  apply (simp, rule ballI, erule_tac x = xa in ballE, auto)[1]
  apply (rule sym)
  apply (simp add: filter_id_conv filter_empty_conv)[1]
  apply (erule_tac x = xb in ballE)
  apply (erule order_trans[rotated])
  apply (rule length_filter_mono)
  apply auto
  done

lemma carrier_singles[simp]:
  "carrier (singles S) = UNIV"
  apply transfer
  apply auto
  apply (rule_tac x = "[x]" in exI)
  apply auto
  done

lemma singles_mono:
  "S \<subseteq> S' \<Longrightarrow> paths (singles S') \<subseteq> paths (singles S)"
by transfer auto


lemma paths_many_calls_subset:
  "paths t \<subseteq> paths (many_calls x \<otimes>\<otimes> without x t)"
proof
  fix xs
  assume "xs \<in> paths t"
  
  have "filter (\<lambda>x'. x' = x) xs = replicate (length (filter (\<lambda>x'. x' = x) xs)) x"
    by (induction xs) auto
  hence "filter (\<lambda>x'. x' = x) xs \<in> paths (many_calls x)" by transfer auto
  moreover
  from \<open>xs \<in> paths t\<close>
  have "filter (\<lambda>x'. x' \<noteq> x) xs \<in> paths (without x t)" by transfer auto
  moreover
  have "xs \<in> interleave (filter (\<lambda>x'. x' = x) xs)  (filter (\<lambda>x'. x' \<noteq> x) xs)" by (rule interleave_filtered)
  ultimately show "xs \<in> paths (many_calls x \<otimes>\<otimes> without x t)" by transfer auto
qed



subsubsection \<open>Substituting trees for every node\<close>

definition f_nxt :: "('a \<Rightarrow> 'a ttree) \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a ttree)"
  where "f_nxt f T x = (if x \<in> T then f(x:=empty) else f)"

fun substitute' :: "('a \<Rightarrow> 'a ttree) \<Rightarrow> 'a set \<Rightarrow> 'a ttree \<Rightarrow> 'a list \<Rightarrow> bool" where
    substitute'_Nil: "substitute' f T t [] \<longleftrightarrow> True"
  | substitute'_Cons: "substitute' f T t (x#xs) \<longleftrightarrow>
        possible t x \<and> substitute' (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x) xs"

lemma f_nxt_mono1: "(\<And> x. paths (f x) \<subseteq> paths (f' x)) \<Longrightarrow> paths (f_nxt f T x x') \<subseteq> paths (f_nxt f' T x x')"
  unfolding f_nxt_def by auto
  
lemma f_nxt_empty_set[simp]: "f_nxt f {} x = f" by (simp add: f_nxt_def)

lemma downset_substitute: "downset (Collect (substitute' f T t))"
apply (rule) unfolding mem_Collect_eq
proof-
  fix x
  assume "substitute' f T t x"
  thus "substitute' f T t (butlast x)" by(induction t x rule: substitute'.induct) (auto)
qed

lift_definition substitute :: "('a \<Rightarrow> 'a ttree) \<Rightarrow> 'a set \<Rightarrow> 'a ttree \<Rightarrow> 'a ttree"
  is "\<lambda> f T t. Collect (substitute' f T t)"
  by (simp add: downset_substitute)

lemma elim_substitute'[pred_set_conv]: "substitute' f T t xs \<longleftrightarrow> xs \<in> paths (substitute f T t)" by transfer auto

lemmas substitute_induct[case_names Nil Cons] = substitute'.induct
lemmas substitute_simps[simp] = substitute'.simps[unfolded elim_substitute']

lemma substitute_mono2: 
  assumes "paths t \<subseteq> paths t'"
  shows "paths (substitute f T t) \<subseteq> paths (substitute f T t')"
proof
  fix xs
  assume "xs \<in> paths (substitute f T t)"
  thus "xs \<in> paths (substitute f T t')"
  using assms
  proof(induction xs arbitrary:f t t')
  case Nil
    thus ?case by simp
  next
  case (Cons x xs)
    from Cons.prems
    show ?case
    by (auto dest: possible_mono elim: Cons.IH intro!:  both_mono1 nxt_mono)
  qed
qed

lemma substitute_mono1: 
  assumes "\<And>x. paths (f x) \<subseteq> paths (f' x)"
  shows "paths (substitute f T t) \<subseteq> paths (substitute f' T t)"
proof
  fix xs
  assume "xs \<in> paths (substitute f T t)"
  from this assms
  show "xs \<in> paths (substitute f' T t)"
  proof (induction xs arbitrary: f f' t)
    case Nil
    thus ?case by simp
  next
  case (Cons x xs)
    from Cons.prems
    show ?case
    by (auto elim!: Cons.IH dest: subsetD dest!: subsetD[OF f_nxt_mono1[OF Cons.prems(2)]] subsetD[OF substitute_mono2[OF  both_mono2[OF Cons.prems(2)]]])
  qed
qed

lemma substitute_monoT:
  assumes "T \<subseteq> T'"
  shows "paths (substitute f T' t) \<subseteq> paths (substitute f T t)"
proof
  fix xs
  assume "xs \<in> paths (substitute f T' t)"
  thus "xs \<in> paths (substitute f T t)"
  using assms
  proof(induction f T' t xs arbitrary: T rule: substitute_induct)
  case Nil
    thus ?case by simp
  next
  case (Cons f T' t x xs T)
    from \<open>x # xs \<in> paths (substitute f T' t)\<close>
    have [simp]: "possible t x" and "xs \<in> paths (substitute (f_nxt f T' x) T' (nxt t x \<otimes>\<otimes> f x))" by auto
    from Cons.IH[OF this(2) Cons.prems(2)]
    have "xs \<in> paths (substitute (f_nxt f T' x) T (nxt t x \<otimes>\<otimes> f x))".
    hence "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))"
      by (rule subsetD[OF substitute_mono1, rotated])
         (auto simp add: f_nxt_def subsetD[OF Cons.prems(2)])
    thus ?case by auto
  qed
qed


lemma substitute_contains_arg: "paths t \<subseteq> paths (substitute f T t)"
proof
  fix xs
  show "xs \<in> paths t \<Longrightarrow> xs \<in> paths (substitute f T t)"
  proof (induction xs arbitrary: f t)
    case Nil
    show ?case by simp
  next
    case (Cons x xs)
    from \<open>x # xs \<in> paths t\<close> 
    have "possible t x" by transfer auto
    moreover
    from \<open>x # xs \<in> paths t\<close> have "xs \<in> paths (nxt t x)"
      by (auto simp add: paths_nxt_eq)
    hence "xs \<in> paths (nxt t x \<otimes>\<otimes> f x)" by (rule subsetD[OF both_contains_arg1])
    note Cons.IH[OF this]
    ultimately
    show ?case by simp
  qed
qed


lemma possible_substitute[simp]: "possible (substitute f T t) x \<longleftrightarrow> possible t x"
  by (metis Cons_both both_empty2 paths_Nil substitute_simps(2))

lemma nxt_substitute[simp]: "possible t x \<Longrightarrow> nxt (substitute f T t) x = substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x)"
  by (rule ttree_eqI) (simp add: paths_nxt_eq)

lemma substitute_either: "substitute f T (t \<oplus>\<oplus> t') = substitute f T t \<oplus>\<oplus> substitute f T t'"
proof-
  have [simp]: "\<And> t t' x . (nxt t x \<oplus>\<oplus> nxt t' x) \<otimes>\<otimes> f x = nxt t x \<otimes>\<otimes> f x \<oplus>\<oplus> nxt t' x \<otimes>\<otimes> f x" by (metis both_comm either_both_distr)
  {
  fix xs
  have "xs \<in> paths (substitute f T (t \<oplus>\<oplus> t'))  \<longleftrightarrow> xs \<in> paths (substitute f T t) \<or> xs \<in> paths (substitute f T t')"
  proof (induction xs arbitrary: f t t')
    case Nil thus ?case by simp
  next
    case (Cons x xs)
    note IH = Cons.IH[where f = "f_nxt f T x" and t = "nxt t' x \<otimes>\<otimes> f x" and t' = "nxt t x \<otimes>\<otimes> f x"]
    show ?case
    apply (auto simp del: either_both_distr2 simp add: either_both_distr2[symmetric] IH)
    apply (metis IH both_comm either_both_distr either_empty2 nxt_not_possible)
    apply (metis IH both_comm both_empty1 either_both_distr either_empty1 nxt_not_possible)
    done
  qed
  }
  thus ?thesis by (auto intro: paths_inj)
qed


(*
lemma substitute_both: "substitute f (t \<otimes>\<otimes> t') = substitute f t \<otimes>\<otimes> substitute f t'"
proof (intro paths_inj set_eqI)
  fix xs
  show "(xs \<in> paths (substitute f (t \<otimes>\<otimes> t'))) = (xs \<in> paths (substitute f t \<otimes>\<otimes> substitute f t'))"
  proof (induction xs arbitrary: t t')
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    have [simp]: "nxt t x \<otimes>\<otimes> t' \<otimes>\<otimes> f x = nxt t x \<otimes>\<otimes> f x \<otimes>\<otimes> t'"
      by (metis both_assoc both_comm)
    have [simp]: "t \<otimes>\<otimes> nxt t' x \<otimes>\<otimes> f x = t \<otimes>\<otimes> (nxt t' x \<otimes>\<otimes> f x)"
      by (metis both_assoc both_comm)
    note Cons[where t = "nxt t x \<otimes>\<otimes> f x" and t' = t', simp]
    note Cons[where t = t and t' = "nxt t' x \<otimes>\<otimes> f x", simp]
    show ?case
      by (auto simp add: Cons_both nxt_both either_both_distr2[symmetric] substitute_either
                  simp del: both_assoc )
  qed
qed
*)

lemma f_nxt_T_delete:
  assumes "f x = empty"
  shows "f_nxt f (T - {x}) x' = f_nxt f T x'"
using assms
by (auto simp add: f_nxt_def)

lemma f_nxt_empty[simp]:
  assumes "f x = empty"
  shows "f_nxt f T x' x = empty"
using assms
by (auto simp add: f_nxt_def)

lemma f_nxt_empty'[simp]:
  assumes "f x = empty"
  shows "f_nxt f T x = f"
using assms
by (auto simp add: f_nxt_def)


lemma substitute_T_delete:
  assumes "f x = empty"
  shows "substitute f (T - {x}) t = substitute f T t"
proof (intro paths_inj  set_eqI)
  fix xs
  from assms
  show "xs \<in> paths (substitute f (T - {x}) t) \<longleftrightarrow> xs \<in> paths (substitute f T t)"
  by (induction xs arbitrary: f t) (auto simp add: f_nxt_T_delete )
qed


lemma substitute_only_empty:
  assumes "const_on f (carrier t) empty"
  shows "substitute f T t = t"
proof (intro paths_inj  set_eqI)
  fix xs
  from assms
  show "xs \<in> paths (substitute f T t) \<longleftrightarrow> xs \<in> paths t"
  proof (induction xs arbitrary: f t)
  case Nil thus ?case by simp
  case (Cons x xs f t)
  
    note const_onD[OF Cons.prems carrier_possible, where y = x, simp]

    have [simp]: "possible t x \<Longrightarrow> f_nxt f T x = f"
      by (rule f_nxt_empty', rule const_onD[OF Cons.prems carrier_possible, where y = x])

    from Cons.prems carrier_nxt_subset
    have "const_on f (carrier (nxt t x)) empty"
      by (rule const_on_subset)
    hence "const_on (f_nxt f T x) (carrier (nxt t x)) empty"
      by (auto simp add: const_on_def f_nxt_def)
    note Cons.IH[OF this]
    hence [simp]: "possible t x \<Longrightarrow> (xs \<in> paths (substitute f T (nxt t x))) = (xs \<in> paths (nxt t x))"
      by simp

    show ?case by (auto simp add: Cons_path)
  qed
qed

lemma substitute_only_empty_both: "const_on f (carrier t') empty \<Longrightarrow> substitute f T (t \<otimes>\<otimes> t') = substitute f T t \<otimes>\<otimes> t'"
proof (intro paths_inj set_eqI)
  fix xs
  assume "const_on f (carrier t') TTree.empty"
  thus "(xs \<in> paths (substitute f T (t \<otimes>\<otimes> t'))) = (xs \<in> paths (substitute f T t \<otimes>\<otimes> t'))"
  proof (induction xs arbitrary: f t t')
  case Nil thus ?case by simp
  next
  case (Cons x xs)
    show ?case
    proof(cases "possible t' x")
      case True 
      hence "x \<in> carrier t'" by (metis carrier_possible)
      with Cons.prems have [simp]: "f x = empty" by auto
      hence [simp]: "f_nxt f T x = f" by (auto simp add: f_nxt_def)

      note Cons.IH[OF Cons.prems, where t = "nxt t x", simp]

      from Cons.prems
      have "const_on f (carrier (nxt t' x)) empty" by (metis carrier_nxt_subset const_on_subset)
      note Cons.IH[OF this, where t = t, simp]

      show ?thesis using True
        by (auto simp add: Cons_both nxt_both  substitute_either)
    next
      case False

      have [simp]: "nxt t x \<otimes>\<otimes> t' \<otimes>\<otimes> f x = nxt t x \<otimes>\<otimes> f x \<otimes>\<otimes> t'"
        by (metis both_assoc both_comm)

      from Cons.prems
      have "const_on (f_nxt f T x) (carrier t') empty" 
        by (force simp add: f_nxt_def)
      note Cons.IH[OF this, where t = "nxt t x \<otimes>\<otimes> f x", simp]

      show ?thesis using False
        by (auto simp add: Cons_both nxt_both  substitute_either)
    qed
  qed
qed
  
lemma f_nxt_upd_empty[simp]:
  "f_nxt (f(x' := empty)) T x = (f_nxt f T x)(x' := empty)"
  by (auto simp add: f_nxt_def)

lemma repeatable_f_nxt_upd[simp]:
  "repeatable (f x) \<Longrightarrow> repeatable (f_nxt f T x' x)"
  by (auto simp add: f_nxt_def)

lemma substitute_remove_anyways_aux:
  assumes "repeatable (f x)"
  assumes "xs \<in> paths (substitute f T t)"
  assumes "t \<otimes>\<otimes> f x = t"
  shows "xs \<in> paths (substitute (f(x := empty)) T t)"
  using assms(2,3) assms(1)
proof (induction f T t xs  rule: substitute_induct)
  case Nil thus ?case by simp
next
  case (Cons f T t x' xs)
  show ?case
  proof(cases "x' = x")
    case False
    hence [simp]: "(f(x := TTree.empty)) x' = f x'" by simp
    have [simp]: "f_nxt f T x' x = f x" using False by (auto simp add: f_nxt_def)
    show ?thesis using Cons by (auto  simp add: repeatable_both_nxt repeatable_both_both_nxt   simp del: fun_upd_apply)
  next
    case True
    hence [simp]: "(f(x := TTree.empty)) x = empty" by simp
    (*  have [simp]: "f_nxt f T x' x = f x" using False by (auto simp add: f_nxt_def) *)

    have *: "(f_nxt f T x) x = f x \<or> (f_nxt f T x) x = empty" by (simp add: f_nxt_def)
    thus ?thesis
      using Cons True
      by (auto  simp add: repeatable_both_nxt repeatable_both_both_nxt   simp del: fun_upd_apply)
  qed
qed
      

lemma substitute_remove_anyways:
  assumes "repeatable t"
  assumes "f x = t"
  shows "substitute f T (t \<otimes>\<otimes> t') = substitute (f(x := empty)) T (t \<otimes>\<otimes> t')"
proof (rule paths_inj, rule, rule subsetI)
  fix xs
  have "repeatable (f x)" using assms by simp
  moreover
  assume "xs \<in> paths (substitute f T (t \<otimes>\<otimes> t'))"
  moreover
  have "t \<otimes>\<otimes> t' \<otimes>\<otimes> f x = t \<otimes>\<otimes> t'"
    by (metis assms both_assoc both_comm repeatable_both_self)
  ultimately
  show "xs \<in> paths (substitute (f(x := empty)) T (t \<otimes>\<otimes> t'))"
      by (rule substitute_remove_anyways_aux)
next
  show "paths (substitute (f(x := empty)) T (t \<otimes>\<otimes> t')) \<subseteq> paths (substitute f T (t \<otimes>\<otimes> t'))"
    by (rule substitute_mono1) auto
qed 

lemma carrier_f_nxt: "carrier (f_nxt f T x x') \<subseteq> carrier (f x')"
  by (simp add: f_nxt_def)

lemma f_nxt_cong: "f x' = f' x' \<Longrightarrow> f_nxt f T x x' = f_nxt f' T x x'"
  by (simp add: f_nxt_def)

lemma substitute_cong':
  assumes "xs \<in> paths (substitute f T t)"
  assumes "\<And> x n. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> f x = f' x"
  shows "xs \<in> paths (substitute f' T t)"
  using assms
proof (induction f T t xs arbitrary: f' rule: substitute_induct )
  case Nil thus ?case by simp
next
  case (Cons f T t x xs)
  hence "possible t x" by auto
  hence "x \<in> carrier t" by (metis carrier_possible)
  hence "x \<in> A" using Cons.prems(3) by auto
  with Cons.prems have [simp]: "f' x = f x" by auto
  have "carrier (f x) \<subseteq> A" using \<open>x \<in> A\<close> by (rule Cons.prems(2))

  from Cons.prems(1,2) Cons.prems(4)[symmetric]
  show ?case
    by (auto elim!: Cons.IH
          dest!: subsetD[OF carrier_f_nxt] subsetD[OF carrier_nxt_subset] subsetD[OF Cons.prems(3)] subsetD[OF \<open>carrier (f x) \<subseteq> A\<close>]
          intro: f_nxt_cong
          )
qed


lemma substitute_cong_induct:
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> f x = f' x"
  shows "substitute f T t = substitute f' T t"
  apply (rule paths_inj)
  apply (rule set_eqI)
  apply (rule iffI)
  apply (erule (2) substitute_cong'[OF _ assms])
  apply (erule substitute_cong'[OF _ _ assms(2)])
  apply (metis assms(1,3))
  apply (metis assms(3))
  done


lemma carrier_substitute_aux:
  assumes "xs \<in> paths (substitute f T t)"
  assumes "carrier t \<subseteq> A"
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A" 
  shows   "set xs \<subseteq> A"
  using assms
  apply(induction  f T t xs rule: substitute_induct)
  apply auto
  apply (metis carrier_possible_subset)
  apply (metis carrier_f_nxt carrier_nxt_subset carrier_possible_subset contra_subsetD order_trans)
  done

lemma carrier_substitute_below:
  assumes "\<And> x. x \<in> A \<Longrightarrow> carrier (f x) \<subseteq> A"
  assumes "carrier t \<subseteq> A"
  shows "carrier (substitute f T t) \<subseteq> A"
proof-
  have "\<And> xs. xs \<in> paths (substitute f T t) \<Longrightarrow> set xs \<subseteq> A" by (rule carrier_substitute_aux[OF _ assms(2,1)])
  thus ?thesis by (auto simp add:  Union_paths_carrier[symmetric])
qed

lemma f_nxt_eq_empty_iff:
  "f_nxt f T x x' = empty \<longleftrightarrow> f x' = empty \<or> (x' = x \<and> x \<in> T)"
  by (auto simp add: f_nxt_def)

lemma substitute_T_cong':
  assumes "xs \<in> paths (substitute f T t)"
  assumes "\<And> x.  (x \<in> T \<longleftrightarrow> x \<in> T') \<or> f x = empty"
  shows "xs \<in> paths (substitute f T' t)"
  using assms
proof (induction f T t xs  rule: substitute_induct )
  case Nil thus ?case by simp
next
  case (Cons f T t x xs)
  from Cons.prems(2)[where x = x]
  have [simp]: "f_nxt f T x = f_nxt f T' x"
    by (auto simp add: f_nxt_def)

  from Cons.prems(2)
  have "(\<And>x'. (x' \<in> T) = (x' \<in> T') \<or> f_nxt f T x x' = TTree.empty)"
    by (auto simp add: f_nxt_eq_empty_iff)
  from Cons.prems(1) Cons.IH[OF _ this]
  show ?case
    by auto
qed

lemma substitute_cong_T:
  assumes "\<And> x.  (x \<in> T \<longleftrightarrow> x \<in> T') \<or> f x = empty"
  shows "substitute f T = substitute f T'"
  apply rule
  apply (rule paths_inj)
  apply (rule set_eqI)
  apply (rule iffI)
  apply (erule substitute_T_cong'[OF _ assms])
  apply (erule substitute_T_cong')
  apply (metis assms)
  done

lemma carrier_substitute1: "carrier t \<subseteq> carrier (substitute f T t)"
    by (rule carrier_mono) (rule substitute_contains_arg)

lemma substitute_cong:
  assumes "\<And> x. x \<in> carrier (substitute f T t) \<Longrightarrow> f x = f' x"
  shows "substitute f T t = substitute f' T t"
proof(rule substitute_cong_induct[OF _ _ assms])
  show "carrier t \<subseteq> carrier (substitute f T t)"
    by (rule carrier_substitute1)
next
  fix x
  assume "x \<in> carrier (substitute f T t)"
  then obtain xs where "xs \<in> paths (substitute f T t)"  and "x \<in> set xs"  by transfer auto
  thus "carrier (f x) \<subseteq> carrier (substitute f T t)"
  proof (induction xs arbitrary: f t)
  case Nil thus ?case by simp
  next
  case (Cons x' xs f t)
    from \<open>x' # xs \<in> paths (substitute f T t)\<close>
    have "possible t x'" and "xs \<in> paths (substitute (f_nxt f T x') T (nxt t x' \<otimes>\<otimes> f x'))" by auto

    from \<open>x \<in> set (x' # xs)\<close>
    have "x = x' \<or> (x \<noteq> x' \<and> x \<in> set xs)" by auto
    hence "carrier (f x) \<subseteq> carrier (substitute (f_nxt f T x') T (nxt t x' \<otimes>\<otimes> f x'))"
    proof(elim conjE disjE)
      assume "x = x'"
      have "carrier (f x) \<subseteq> carrier (nxt t x \<otimes>\<otimes> f x)" by simp
      also have "\<dots> \<subseteq> carrier (substitute (f_nxt f T x') T (nxt t x \<otimes>\<otimes> f x))" by (rule carrier_substitute1)
      finally show ?thesis unfolding \<open>x = x'\<close>.
    next
      assume "x \<noteq> x'"
      hence [simp]: "(f_nxt f T x' x) = f x" by (simp add: f_nxt_def)

      assume "x \<in> set xs" 
      from Cons.IH[OF \<open>xs \<in> _ \<close> this]
      show "carrier (f x) \<subseteq> carrier (substitute (f_nxt f T x') T (nxt t x' \<otimes>\<otimes> f x'))" by simp
    qed
    also
    from \<open>possible t x'\<close>
    have "carrier (substitute (f_nxt f T x') T (nxt t x' \<otimes>\<otimes> f x')) \<subseteq>  carrier (substitute f T t)"
      apply transfer
      apply auto
      apply (rule_tac x = "x'#xa" in exI)
      apply auto
      done
    finally show ?case.
  qed
qed

lemma substitute_substitute:
  assumes "\<And> x. const_on f' (carrier (f x)) empty"
  shows "substitute f T (substitute f' T t) = substitute (\<lambda> x. f x \<otimes>\<otimes> f' x) T t"
proof (rule paths_inj, rule set_eqI)
  fix xs
  have [simp]: "\<And> f f' x'. f_nxt (\<lambda>x. f x \<otimes>\<otimes> f' x) T x' = (\<lambda>x. f_nxt f T x' x \<otimes>\<otimes> f_nxt f' T x' x)"
    by (auto simp add: f_nxt_def)

  from  assms
  show "xs \<in> paths (substitute f T (substitute f' T t)) \<longleftrightarrow> xs \<in> paths (substitute (\<lambda>x. f x \<otimes>\<otimes> f' x) T t)"
  proof (induction xs arbitrary: f f' t )
  case Nil thus ?case by simp
  case (Cons x xs)
    thus ?case
    proof (cases "possible t x")
      case True

      from Cons.prems
      have prem': "\<And> x'. const_on (f_nxt f' T x) (carrier (f x')) empty"
        by (force simp add: f_nxt_def)
      hence "\<And>x'. const_on (f_nxt f' T x) (carrier ((f_nxt f T x) x')) empty" 
        by (metis carrier_empty const_onI emptyE f_nxt_def fun_upd_apply)
      note Cons.IH[where f = "f_nxt f T x" and f' = "f_nxt f' T x", OF this, simp]

      have [simp]: "nxt t x \<otimes>\<otimes> f x \<otimes>\<otimes> f' x = nxt t x \<otimes>\<otimes> f' x \<otimes>\<otimes> f x"
        by (metis both_comm both_assoc)

      show ?thesis using True
        by (auto del: iffI simp add: substitute_only_empty_both[OF prem'[where x' = x] , symmetric])
    next
    case False
      thus ?thesis by simp
    qed
  qed
qed


lemma ttree_rest_substitute:
  assumes "\<And> x. carrier (f x) \<inter> S = {}"
  shows "ttree_restr S (substitute f T t) = ttree_restr S t"
proof(rule paths_inj, rule set_eqI, rule iffI)
  fix xs
  assume "xs \<in> paths (ttree_restr S (substitute f T t))"
  then
  obtain xs' where [simp]: "xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths (substitute f T t)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2) assms
  have "filter (\<lambda> x'. x' \<in> S) xs' \<in>  paths (ttree_restr S t)"
  proof (induction xs' arbitrary: f t)
  case Nil thus ?case by simp
  next
  case (Cons x xs f t)
    from Cons.prems
    have "possible t x" and "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by auto

    from Cons.prems(2)
    have "(\<And>x'. carrier (f_nxt f T x x') \<inter> S = {})" by (auto simp add: f_nxt_def)
    
    from  Cons.IH[OF \<open>xs \<in> _\<close> this]
    have "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (ttree_restr S (nxt t x) \<otimes>\<otimes> ttree_restr S (f x))" by (simp add: ttree_restr_both)
    hence "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (ttree_restr S (nxt t x))" by (simp add: ttree_restr_is_empty[OF Cons.prems(2)])
    with \<open>possible t x\<close>
    show "[x'\<leftarrow>x#xs . x' \<in> S] \<in> paths (ttree_restr S t)"
      by (cases "x \<in> S") (auto simp add: Cons_path ttree_restr_possible  dest: subsetD[OF ttree_restr_nxt_subset2]  subsetD[OF ttree_restr_nxt_subset])
  qed
  thus "xs \<in> paths (ttree_restr S t)" by simp
next
  fix xs
  assume "xs \<in> paths (ttree_restr S t)"
  then obtain xs' where [simp]:"xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths t" 
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2)
  have "xs' \<in> paths (substitute f T t)" by (rule subsetD[OF substitute_contains_arg])
  thus "xs \<in> paths (ttree_restr S (substitute f T t))"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
qed

text \<open>An alternative characterization of substitution\<close>

inductive substitute'' :: "('a \<Rightarrow> 'a ttree) \<Rightarrow> 'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  substitute''_Nil: "substitute'' f T [] []"
  | substitute''_Cons:
    "zs \<in> paths (f x) \<Longrightarrow> xs' \<in> interleave xs zs \<Longrightarrow> substitute'' (f_nxt f T x) T xs' ys
       \<Longrightarrow> substitute'' f T (x#xs) (x#ys)"
inductive_cases substitute''_NilE[elim]: "substitute'' f T xs []"  "substitute'' f T [] xs"
inductive_cases substitute''_ConsE[elim]: "substitute'' f T (x#xs) ys"

lemma substitute_substitute'':
  "xs \<in> paths (substitute f T t) \<longleftrightarrow> (\<exists> xs' \<in> paths t. substitute'' f T xs' xs)"
proof
  assume "xs \<in> paths (substitute f T t)"
  thus "\<exists> xs' \<in> paths t. substitute'' f T xs' xs"
  proof(induction xs arbitrary: f t)
    case Nil
    have "substitute'' f T [] []"..
    thus ?case by auto
  next
    case (Cons x xs f t)
    from \<open>x # xs \<in> paths (substitute f T t)\<close>
    have "possible t x" and "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by (auto simp add: Cons_path)
    from Cons.IH[OF this(2)]
    obtain xs' where "xs' \<in> paths (nxt t x \<otimes>\<otimes> f x)" and "substitute'' (f_nxt f T x) T xs' xs" by auto
    from this(1)
    obtain ys' zs' where "ys' \<in> paths (nxt t x)" and "zs' \<in> paths (f x)" and "xs' \<in> interleave ys' zs'" 
      by (auto simp add: paths_both)
  
    from this(2,3) \<open>substitute'' (f_nxt f T x) T xs' xs\<close>
    have "substitute'' f T (x # ys') (x # xs)"..
    moreover
    from \<open>ys' \<in> paths (nxt t x)\<close> \<open>possible t x\<close>
    have "x # ys' \<in> paths t"  by (simp add: Cons_path)
    ultimately
    show ?case by auto
  qed
next
  assume "\<exists> xs' \<in> paths t. substitute'' f T xs' xs"
  then obtain xs' where  "substitute'' f T xs' xs" and "xs' \<in> paths t"  by auto
  thus "xs \<in> paths (substitute f T t)"
  proof(induction arbitrary: t rule: substitute''.induct[case_names Nil Cons])
  case Nil thus ?case by simp
  next
  case (Cons zs x xs' xs ys t)
    from Cons.prems Cons.hyps
    show ?case by (force simp add: Cons_path paths_both intro!: Cons.IH)
  qed
qed

lemma paths_substitute_substitute'':
  "paths (substitute f T t) = \<Union>((\<lambda> xs . Collect (substitute'' f T xs)) ` paths t)"
  by (auto simp add: substitute_substitute'')

lemma ttree_rest_substitute2:
  assumes "\<And> x. carrier (f x) \<subseteq> S"
  assumes "const_on f (-S) empty"
  shows "ttree_restr S (substitute f T t) = substitute f T (ttree_restr S t)"
proof(rule paths_inj, rule set_eqI, rule iffI)
  fix xs
  assume "xs \<in> paths (ttree_restr S (substitute f T t))"
  then
  obtain xs' where [simp]: "xs = filter (\<lambda> x'. x' \<in> S) xs'" and "xs' \<in> paths (substitute f T t)"
    by (auto simp add: filter_paths_conv_free_restr[symmetric])
  from this(2) assms
  have "filter (\<lambda> x'. x' \<in> S) xs' \<in> paths (substitute f T (ttree_restr S t))"
  proof (induction f T t xs' rule: substitute_induct)
  case Nil thus ?case by simp
  next
  case (Cons f T t x xs)
    from Cons.prems(1)
    have "possible t x" and "xs \<in> paths (substitute (f_nxt f T x) T (nxt t x \<otimes>\<otimes> f x))" by auto
    note this(2)
    moreover
    from  Cons.prems(2)
    have "\<And> x'. carrier (f_nxt f T x x') \<subseteq> S" by (auto simp add: f_nxt_def)
    moreover
    from  Cons.prems(3)
    have "const_on (f_nxt f T x) (-S) empty" by (force simp add: f_nxt_def)
    ultimately
    have "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (substitute (f_nxt f T x) T (ttree_restr S (nxt t x \<otimes>\<otimes> f x)))" by (rule Cons.IH)
    hence *: "[x'\<leftarrow>xs . x' \<in> S] \<in> paths (substitute (f_nxt f T x) T (ttree_restr S (nxt t x \<otimes>\<otimes> f x)))" by (simp add: ttree_restr_both)
    show ?case
    proof (cases "x \<in> S")
      case True
      show ?thesis
        using \<open>possible t x\<close> Cons.prems(3) * True
        by (auto simp add: ttree_restr_both ttree_restr_noop[OF Cons.prems(2)] intro: ttree_restr_possible
                    dest: subsetD[OF substitute_mono2[OF both_mono1[OF ttree_restr_nxt_subset]]])
    next
      case False
      with \<open>const_on f (- S) TTree.empty\<close> have [simp]: "f x = empty" by auto
      hence [simp]: "f_nxt f T x = f" by (auto simp add: f_nxt_def)
      show ?thesis
      using * False
      by (auto dest:  subsetD[OF substitute_mono2[OF ttree_restr_nxt_subset2]])
    qed
  qed
  thus "xs \<in> paths (substitute f T (ttree_restr S t))" by simp
next
  fix xs
  assume "xs \<in> paths (substitute f T (ttree_restr S t))"
  then obtain xs' where "xs' \<in> paths t" and "substitute'' f T (filter (\<lambda> x'. x'\<in>S) xs') xs "
    unfolding substitute_substitute''
    by (auto simp add: filter_paths_conv_free_restr[symmetric])

  from this(2) assms
  have "\<exists> xs''. xs = filter (\<lambda> x'. x'\<in>S) xs'' \<and> substitute'' f T xs' xs''"
  proof(induction "(xs',xs)" arbitrary: f xs' xs rule: measure_induct_rule[where f = "\<lambda> (xs,ys). length (filter (\<lambda> x'. x' \<notin> S) xs) + length ys"])
  case (less xs ys)
    note \<open>substitute'' f T [x'\<leftarrow>xs . x' \<in> S] ys\<close>

    show ?case
    proof(cases xs)
    case Nil with less.prems have "ys = []" by auto
      thus ?thesis using Nil by (auto,  metis filter.simps(1) substitute''_Nil)
    next
    case (Cons x xs')
      show ?thesis
      proof (cases "x \<in> S")
      case True with Cons less.prems
        have "substitute'' f T (x# [x'\<leftarrow>xs' . x' \<in> S]) ys" by simp
        from substitute''_ConsE[OF this]
        obtain zs xs'' ys' where "ys = x # ys'" and "zs \<in> paths (f x)" and "xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] zs" and "substitute'' (f_nxt f T x) T xs'' ys'".
        from \<open>zs \<in> paths (f x)\<close>  less.prems(2)
        have "set zs \<subseteq> S" by (auto simp add: Union_paths_carrier[symmetric])
        hence [simp]: "[x'\<leftarrow>zs . x' \<in> S] = zs" "[x'\<leftarrow>zs . x' \<notin> S] = []" 
            by (metis UnCI Un_subset_iff eq_iff filter_True,
               metis \<open>set zs \<subseteq> S\<close> filter_False insert_absorb insert_subset)
        
        from \<open>xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] zs\<close>
        have "xs'' \<in> interleave [x'\<leftarrow>xs' . x' \<in> S] [x'\<leftarrow>zs . x' \<in> S]" by simp
        then obtain xs''' where "xs'' = [x'\<leftarrow>xs''' . x' \<in> S]" and "xs''' \<in> interleave xs' zs" by (rule interleave_filter)

        from \<open>xs''' \<in> interleave xs' zs\<close>
        have l: "\<And> P. length (filter P xs''') = length (filter P xs') + length (filter P zs)"
          by (induction) auto
        
        from \<open>substitute'' (f_nxt f T x) T xs'' ys'\<close> \<open>xs'' = _\<close>
        have "substitute'' (f_nxt f T x) T [x'\<leftarrow>xs''' . x' \<in> S] ys'" by simp
        moreover
        from less.prems(2)
        have "\<And>xa. carrier (f_nxt f T x xa) \<subseteq> S"
          by (auto simp add: f_nxt_def)
        moreover
        from less.prems(3)
        have "const_on (f_nxt f T x) (- S) TTree.empty" by (force simp add: f_nxt_def)
        ultimately
        have "\<exists>ys''. ys' = [x'\<leftarrow>ys'' . x' \<in> S] \<and> substitute'' (f_nxt f T x) T xs''' ys''"
            by (rule less.hyps[rotated])
               (auto simp add: \<open>ys = _ \<close> \<open>xs =_\<close> \<open>x \<in> S\<close> \<open>xs'' = _\<close>[symmetric] l)[1]
        then obtain ys'' where "ys' = [x'\<leftarrow>ys'' . x' \<in> S]" and "substitute'' (f_nxt f T x) T xs''' ys''" by blast
        hence "ys = [x'\<leftarrow>x#ys'' . x' \<in> S]" using \<open>x \<in> S\<close> \<open>ys = _\<close> by simp
        moreover
        from \<open>zs \<in> paths (f x)\<close> \<open>xs''' \<in> interleave xs' zs\<close> \<open>substitute'' (f_nxt f T x) T xs''' ys''\<close>
        have "substitute'' f T (x#xs') (x#ys'')"
          by rule
        ultimately
        show ?thesis unfolding Cons by blast
      next
      case False with Cons less.prems
        have "substitute'' f T ([x'\<leftarrow>xs' . x' \<in> S]) ys" by simp
        hence "\<exists>ys'. ys = [x'\<leftarrow>ys' . x' \<in> S] \<and> substitute'' f T xs' ys'"
            by (rule less.hyps[OF _ _ less.prems(2,3), rotated]) (auto simp add:  \<open>xs =_\<close> \<open>x \<notin>  S\<close>)
        then obtain ys' where "ys = [x'\<leftarrow>ys' . x' \<in> S]" and "substitute'' f T xs' ys'" by auto
        
        from this(1)
        have "ys = [x'\<leftarrow>x#ys' . x' \<in> S]" using \<open>x \<notin> S\<close> \<open>ys = _\<close> by simp
        moreover
        have [simp]: "f x = empty" using \<open>x \<notin> S\<close> less.prems(3) by force
        hence "f_nxt f T x = f" by (auto simp add: f_nxt_def)
        with \<open>substitute'' f T xs' ys'\<close>
        have "substitute'' f T (x#xs') (x#ys')"
          by (auto intro: substitute''.intros)
        ultimately
        show ?thesis unfolding Cons by blast
      qed
    qed
  qed
  then obtain xs'' where "xs = filter (\<lambda> x'. x'\<in>S) xs''" and "substitute'' f T xs' xs''" by auto
  from this(2) \<open>xs' \<in> paths t\<close>
  have "xs'' \<in> paths (substitute f T t)" by (auto simp add: substitute_substitute'')
  with \<open>xs = _\<close>
  show "xs \<in> paths (ttree_restr S (substitute f T t))"
    by (auto simp add:  filter_paths_conv_free_restr[symmetric])
qed

end

