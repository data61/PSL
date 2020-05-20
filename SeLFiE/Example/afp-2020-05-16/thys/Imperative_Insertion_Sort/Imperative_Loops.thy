(*  Title:      Imperative_Loops
    Author:     Christian Sternagel
*)

section \<open>Looping Constructs for Imperative HOL\<close>

theory Imperative_Loops
imports "HOL-Imperative_HOL.Imperative_HOL"
begin

subsection \<open>While Loops\<close>

text \<open>
  We would have liked to restrict to read-only loop conditions using a condition of
  type @{typ "heap \<Rightarrow> bool"} together with @{const tap}. However, this does not allow
  for code generation due to breaking the heap-abstraction.
\<close>
partial_function (heap) while :: "bool Heap \<Rightarrow> 'b Heap \<Rightarrow> unit Heap"
where
  [code]: "while p f = do {
    b \<leftarrow> p;
    if b then f \<then> while p f
    else return ()
  }"

definition "cond p h \<longleftrightarrow> fst (the (execute p h))"

text \<open>A locale that restricts to read-only loop conditions.\<close>
locale ro_cond =
  fixes p :: "bool Heap"
  assumes read_only: "success p h \<Longrightarrow> snd (the (execute p h)) = h"
begin

lemma ro_cond: "ro_cond p"
  using read_only by (simp add: ro_cond_def)

lemma cond_cases [execute_simps]:
  "success p h \<Longrightarrow> cond p h \<Longrightarrow> execute p h = Some (True, h)"
  "success p h \<Longrightarrow> \<not> cond p h \<Longrightarrow> execute p h = Some (False, h)"
  using read_only [of h] by (auto simp: cond_def success_def)

lemma execute_while_unfolds [execute_simps]:
  "success p h \<Longrightarrow> cond p h \<Longrightarrow> execute (while p f) h = execute (f \<then> while p f) h"
  "success p h \<Longrightarrow> \<not> cond p h \<Longrightarrow> execute (while p f) h = execute (return ()) h"
  by (auto simp: while.simps execute_simps)

lemma
  success_while_cond: "success p h \<Longrightarrow> cond p h \<Longrightarrow> effect f h h' r \<Longrightarrow> success (while p f) h' \<Longrightarrow>
    success (while p f) h" and
  success_while_not_cond: "success p h \<Longrightarrow> \<not> cond p h \<Longrightarrow> success (while p f) h"
  by (auto simp: while.simps effect_def execute_simps intro!: success_intros)

lemma success_cond_effect:
  "success p h \<Longrightarrow> cond p h \<Longrightarrow> effect p h h True"
  using read_only [of h] by (auto simp: effect_def execute_simps)

lemma success_not_cond_effect:
  "success p h \<Longrightarrow> \<not> cond p h \<Longrightarrow> effect p h h False"
  using read_only [of h] by (auto simp: effect_def execute_simps)

end

text \<open>The loop-condition does no longer hold after the loop is finished.\<close>
lemma ro_cond_effect_while_post:
  assumes "ro_cond p"
    and "effect (while p f) h h' r"
  shows "success p h' \<and> \<not> cond p h'"
  using assms(1)
  apply (induct rule: while.raw_induct [OF _ assms(2)])
  apply (auto elim!: effect_elims effect_ifE simp: cond_def)
  apply (metis effectE ro_cond.read_only)+
done

text \<open>A rule for proving partial correctness of while loops.\<close>
lemma ro_cond_effect_while_induct:
  assumes "ro_cond p"
  assumes "effect (while p f) h h' u"
    and "I h"
    and "\<And>h h' u. I h \<Longrightarrow> success p h \<Longrightarrow> cond p h \<Longrightarrow> effect f h h' u \<Longrightarrow> I h'"
  shows "I h'"
using assms(1, 3-)
proof (induction p f h h' u rule: while.raw_induct)
  case (1 w p f h h' u)
  obtain b
    where "effect p h h b"
    and *: "effect (if b then f \<then> w p f else return ()) h h' u"
    using "1.hyps" and \<open>ro_cond p\<close>
    by (auto elim!: effect_elims intro: effect_intros) (metis effectE ro_cond.read_only)
  then have cond: "success p h" "cond p h = b" by (auto simp: cond_def elim!: effect_elims effectE)
  show ?case
  proof (cases "b")
    assume "\<not> b"
    then show ?thesis using * and \<open>I h\<close> by (auto elim: effect_elims)
  next
    assume "b"
    moreover
    with * obtain h'' and r
      where "effect f h h'' r" and "effect (w p f) h'' h' u" by (auto elim: effect_elims)
    moreover
    ultimately
    show ?thesis using 1 and cond by blast
  qed
qed fact

lemma effect_success_conv:
  "(\<exists>h'. effect c h h' () \<and> I h') \<longleftrightarrow> success c h \<and> I (snd (the (execute c h)))"
  by (auto simp: success_def effect_def)

context ro_cond
begin

lemmas
  effect_while_post = ro_cond_effect_while_post [OF ro_cond] and
  effect_while_induct [consumes 1, case_names base step] = ro_cond_effect_while_induct [OF ro_cond]

text \<open>A rule for proving total correctness of while loops.\<close>
lemma wf_while_induct [consumes 1, case_names success_cond success_body base step]:
  assumes "wf R" \<comment> \<open>a well-founded relation on heaps proving termination of the loop\<close>
    and success_p: "\<And>h. I h \<Longrightarrow> success p h" \<comment> \<open>the loop-condition terminates\<close>
    and success_f: "\<And>h. I h \<Longrightarrow> success p h \<Longrightarrow> cond p h \<Longrightarrow> success f h" \<comment> \<open>the loop-body terminates\<close>
    and "I h" \<comment> \<open>the invariant holds before the loop is entered\<close>
    and step: "\<And>h h' r. I h \<Longrightarrow> success p h \<Longrightarrow> cond p h \<Longrightarrow> effect f h h' r \<Longrightarrow> (h', h) \<in> R \<and> I h'"
       \<comment> \<open>the invariant is preserved by iterating the loop\<close>
  shows "\<exists>h'. effect (while p f) h h' () \<and> I h'"
using \<open>wf R\<close> and \<open>I h\<close>
proof (induction h)
  case (less h)
  show ?case
  proof (cases "cond p h")
    assume "\<not> cond p h" then show ?thesis
      using \<open>I h\<close> and success_p [of h] by (simp add: effect_def execute_simps)
  next
    assume "cond p h"
    with \<open>I h\<close> and success_f [of h] and step [of h] and success_p [of h]
      obtain h' and r where "effect f h h' r" and "(h', h) \<in> R" and "I h'" and "success p h"
      by (auto simp: success_def effect_def)
    with less.IH [of h'] show ?thesis
      using \<open>cond p h\<close> by (auto simp: execute_simps effect_def)
  qed
qed

text \<open>A rule for proving termination of while loops.\<close>
lemmas
  success_while_induct [consumes 1, case_names success_cond success_body base step] =
    wf_while_induct [unfolded effect_success_conv, THEN conjunct1]

end


subsection \<open>For Loops\<close>

fun "for" :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b Heap) \<Rightarrow> unit Heap"
where
  "for [] f = return ()" |
  "for (x # xs) f = f x \<then> for xs f"

text \<open>A rule for proving partial correctness of for loops.\<close>
lemma effect_for_induct [consumes 2, case_names base step]:
  assumes "i \<le> j"
    and "effect (for [i ..< j] f) h h' u"
    and "I i h"
    and "\<And>k h h' r. i \<le> k \<Longrightarrow> k < j \<Longrightarrow> I k h \<Longrightarrow> effect (f k) h h' r \<Longrightarrow> I (Suc k) h'"
  shows "I j h'"
using assms
proof (induction "j - i" arbitrary: i h)
  case 0
  then show ?case by (auto elim: effect_elims)
next
  case (Suc k)
  show ?case
  proof (cases "j = i")
    case True
    with Suc show ?thesis by auto
  next
    case False
    with \<open>i \<le> j\<close> and \<open>Suc k = j - i\<close>
      have "i < j" and "k = j - Suc i" and "Suc i \<le> j" by auto
    then have "[i ..< j] = i # [Suc i ..< j]" by (metis upt_rec)
    with \<open>effect (for [i ..< j] f) h h' u\<close> obtain h'' r
      where *: "effect (f i) h h'' r" and **: "effect (for [Suc i ..< j] f) h'' h' u"
      by (auto elim: effect_elims)
    from Suc(6) [OF _ _ \<open>I i h\<close> *] and \<open>i < j\<close>
      have "I (Suc i) h''" by auto
    show ?thesis
      by (rule Suc(1) [OF \<open>k = j - Suc i\<close> \<open>Suc i \<le> j\<close> ** \<open>I (Suc i) h''\<close> Suc(6)]) auto
  qed
qed

text \<open>A rule for proving total correctness of for loops.\<close>
lemma for_induct [consumes 1, case_names succeed base step]:
  assumes "i \<le> j"
    and "\<And>k h. I k h \<Longrightarrow> i \<le> k \<Longrightarrow> k < j \<Longrightarrow> success (f k) h"
    and "I i h"
    and "\<And>k h h' r. I k h \<Longrightarrow> i \<le> k \<Longrightarrow> k < j \<Longrightarrow> effect (f k) h h' r \<Longrightarrow> I (Suc k) h'"
  shows "\<exists>h'. effect (for [i ..< j] f) h h' () \<and> I j h'" (is "?P i h")
using assms
proof (induction "j - i" arbitrary: i h)
  case 0
  then show ?case by (auto simp: effect_def execute_simps)
next
  case (Suc k)
  show ?case
  proof (cases "j = i")
    assume "j = i"
    with Suc show ?thesis by auto
  next
    assume "j \<noteq> i"
    with \<open>i \<le> j\<close> and \<open>Suc k = j - i\<close>
      have "i < j" and "k = j - Suc i" and "Suc i \<le> j" by auto
    then have [simp]: "[i ..< j] = i # [Suc i ..< j]" by (metis upt_rec)
    obtain h' r where *: "effect (f i) h h' r"
      using Suc(4) [OF \<open>I i h\<close> le_refl \<open>i < j\<close>] by (auto elim!: success_effectE)
    moreover
    then have "I (Suc i) h'" using Suc by auto
    moreover
    have "?P (Suc i) h'"
      by (rule Suc(1) [OF \<open>k = j - Suc i\<close> \<open>Suc i \<le> j\<close> Suc(4) \<open>I (Suc i) h'\<close> Suc(6)]) auto
    ultimately
    show ?case by (auto simp: effect_def execute_simps)
  qed
qed

text \<open>A rule for proving termination of for loops.\<close>
lemmas
  success_for_induct [consumes 1, case_names succeed base step] =
    for_induct [unfolded effect_success_conv, THEN conjunct1]

end

