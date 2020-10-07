section \<open>Compositional Reasoning\<close>

(*<*)
theory Compositional_Reasoning
imports BD_Security
begin
(*>*)


context BD_Security begin


subsection\<open>Preliminaries\<close>

definition "disjAll \<Delta>s s vl s1 vl1 \<equiv> (\<exists>\<Delta> \<in> \<Delta>s. \<Delta> s vl s1 vl1)"

lemma disjAll_simps[simp]:
  "disjAll {} \<equiv> \<lambda>_ _ _ _. False"
  "disjAll (insert \<Delta> \<Delta>s) \<equiv> \<lambda>s vl s1 vl1. \<Delta> s vl s1 vl1 \<or> disjAll \<Delta>s s vl s1 vl1"
  unfolding disjAll_def[abs_def] by auto


lemma iaction_mono:
assumes 1: "iaction \<Delta> s vl s1 vl1" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "iaction \<Delta>' s vl s1 vl1"
proof-
  obtain a1 ou1 s1' vl1'
  where "step s1 a1 = (ou1, s1')" and "\<phi> (Trans s1 a1 ou1 s1')"
  and "consume (Trans s1 a1 ou1 s1') vl1 vl1'" and "\<not> \<gamma> (Trans s1 a1 ou1 s1')"
  and "\<Delta> s vl s1' vl1'" using 1 unfolding iaction_def by auto
  thus ?thesis unfolding iaction_def using 2 apply -
  by (rule exI[of _ a1], rule exI[of _ ou1], rule exI[of _ s1'], rule exI[of _ vl1']) auto
qed

lemma match_mono:
assumes 1: "match \<Delta> s s1 vl1 a ou s' vl'" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "match \<Delta>' s s1 vl1 a ou s' vl'"
proof-
  obtain a1 ou1 s1' vl1'
  where "\<Delta> s' vl' s1' vl1'"
  and "step s1 a1 = (ou1, s1')"
  and "consume (Trans s1 a1 ou1 s1') vl1 vl1'"
  and "\<gamma> (Trans s a ou s') = \<gamma> (Trans s1 a1 ou1 s1')"
  and "(\<gamma> (Trans s a ou s') \<longrightarrow> g (Trans s a ou s') = g (Trans s1 a1 ou1 s1'))"
  using 1 unfolding match_def by auto
  thus ?thesis unfolding match_def using 2 apply -
  by (rule exI[of _ a1], rule exI[of _ ou1], rule exI[of _ s1'], rule exI[of _ vl1']) auto
qed

lemma ignore_mono:
assumes 1: "ignore \<Delta> s s1 vl1 a ou s' vl'" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "ignore \<Delta>' s s1 vl1 a ou s' vl'"
using assms unfolding ignore_def by auto

lemma reaction_mono:
assumes 1: "reaction \<Delta> s vl s1 vl1" and 2: "\<And> s vl s1 vl1. \<Delta> s vl s1 vl1 \<Longrightarrow> \<Delta>' s vl s1 vl1"
shows "reaction \<Delta>' s vl s1 vl1"
proof
  fix a ou s' vl'
  assume "step s a = (ou, s')" and "\<not> T (Trans s a ou s')" and "consume (Trans s a ou s') vl vl'"
  hence "match \<Delta> s s1 vl1 a ou s' vl' \<or> ignore \<Delta> s s1 vl1 a ou s' vl'" (is "?m \<or> ?i")
  using 1 unfolding reaction_def by auto
  thus "match \<Delta>' s s1 vl1 a ou s' vl' \<or> ignore \<Delta>' s s1 vl1 a ou s' vl'" (is "?m' \<or> ?i'")
  proof
    assume ?m from match_mono[OF this 2] show ?thesis by simp
  next
    assume ?i from ignore_mono[OF this 2] show ?thesis by simp
  qed
qed


subsection\<open>Decomposition into an arbitrary network of components\<close>

(* Unwind not to itself, but to a disjunction of other relations: *)
definition unwind_to where
"unwind_to \<Delta> \<Delta>s \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   vl \<noteq> [] \<and> exit s (hd vl)
   \<or>
   iaction (disjAll \<Delta>s) s vl s1 vl1
   \<or>
   (vl \<noteq> [] \<or> vl1 = []) \<and> reaction (disjAll \<Delta>s) s vl s1 vl1"

lemma unwind_toI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reach s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   vl \<noteq> [] \<and> exit s (hd vl)
   \<or>
   iaction (disjAll \<Delta>s) s vl s1 vl1
   \<or>
   (vl \<noteq> [] \<or> vl1 = []) \<and> reaction (disjAll \<Delta>s) s vl s1 vl1"
shows "unwind_to \<Delta> \<Delta>s"
using assms unfolding unwind_to_def by auto

(* Decomposition: *)
lemma unwind_dec:
assumes ne: "\<And> \<Delta>. \<Delta> \<in> \<Delta>s \<Longrightarrow> next \<Delta> \<subseteq> \<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
shows "unwind (disjAll \<Delta>s)" (is "unwind ?\<Delta>")
proof
  fix s s1 :: 'state and vl vl1 :: "'value list"
  assume r: "reachNT s" "reach s1" and \<Delta>: "?\<Delta> s vl s1 vl1"
  then obtain \<Delta> where \<Delta>: "\<Delta> \<in> \<Delta>s" and 2: "\<Delta> s vl s1 vl1" unfolding disjAll_def by auto
  let ?\<Delta>s' = "next \<Delta>"  let ?\<Delta>' = "disjAll ?\<Delta>s'"
  have "(vl \<noteq> [] \<and> exit s (hd vl)) \<or>
        iaction ?\<Delta>' s vl s1 vl1 \<or>
        ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction ?\<Delta>' s vl s1 vl1)"
  using 2 \<Delta> ne r unfolding unwind_to_def by auto
  moreover have "\<And> s vl s1 vl1. ?\<Delta>' s vl s1 vl1 \<Longrightarrow> ?\<Delta> s vl s1 vl1"
  using ne[OF \<Delta>] unfolding disjAll_def by auto
  ultimately show
       "(vl \<noteq> [] \<and> exit s (hd vl)) \<or>
        iaction ?\<Delta> s vl s1 vl1 \<or>
        ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction ?\<Delta> s vl s1 vl1)"
  using iaction_mono[of ?\<Delta>' _ _ _ _ ?\<Delta>] reaction_mono[of ?\<Delta>' _ _ _ _ ?\<Delta>] by blast
qed

lemma init_dec:
assumes \<Delta>0: "\<Delta>0 \<in> \<Delta>s"
and i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta>0 istate vl istate vl1"
shows "\<forall> vl vl1. B vl vl1 \<longrightarrow> disjAll \<Delta>s istate vl istate vl1"
using assms unfolding disjAll_def by auto

theorem unwind_dec_secure:
assumes \<Delta>0: "\<Delta>0 \<in> \<Delta>s"
and i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta>0 istate vl istate vl1"
and ne: "\<And> \<Delta>. \<Delta> \<in> \<Delta>s \<Longrightarrow> next \<Delta> \<subseteq> \<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
shows secure
using init_dec[OF \<Delta>0 i] unwind_dec[OF ne] unwind_secure by metis


subsection\<open>A customization for linear modular reasoning\<close>

(* The customization assumes that each component unwinds only into itself,
its successor or an exit component.  *)

definition unwind_cont where
"unwind_cont \<Delta> \<Delta>s \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta> s vl s1 vl1
   \<longrightarrow>
   iaction (disjAll \<Delta>s) s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction (disjAll \<Delta>s) s vl s1 vl1)"

lemma unwind_contI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reach s1; \<Delta> s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   iaction (disjAll \<Delta>s) s vl s1 vl1
   \<or>
   ((vl \<noteq> [] \<or> vl1 = []) \<and> reaction (disjAll \<Delta>s) s vl s1 vl1)"
shows "unwind_cont \<Delta> \<Delta>s"
using assms unfolding unwind_cont_def by auto

definition unwind_exit where
"unwind_exit \<Delta>e \<equiv>
 \<forall> s vl s1 vl1.
   reachNT s \<and> reach s1 \<and> \<Delta>e s vl s1 vl1
   \<longrightarrow>
   vl \<noteq> [] \<and> exit s (hd vl)"

lemma unwind_exitI[intro?]:
assumes
"\<And> s vl s1 vl1.
   \<lbrakk>reachNT s; reach s1; \<Delta>e s vl s1 vl1\<rbrakk>
   \<Longrightarrow>
   vl \<noteq> [] \<and> exit s (hd vl)"
shows "unwind_exit \<Delta>e"
using assms unfolding unwind_exit_def by auto

fun allConsec :: "'a list \<Rightarrow> ('a * 'a) set" where
  "allConsec [] = {}"
| "allConsec [a] = {}"
| "allConsec (a # b # as) = insert (a,b) (allConsec (b#as))"


lemma set_allConsec:
assumes "\<Delta> \<in> set \<Delta>s'" and "\<Delta>s = \<Delta>s' ## \<Delta>1"
shows "\<exists> \<Delta>2. (\<Delta>,\<Delta>2) \<in> allConsec \<Delta>s"
using assms proof (induction \<Delta>s' arbitrary: \<Delta>s)
  case Nil thus ?case by auto
next
  case (Cons \<Delta>3 \<Delta>s' \<Delta>s)
  show ?case proof(cases "\<Delta> = \<Delta>3")
    case True
    show ?thesis proof(cases \<Delta>s')
      case Nil
      show ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> Nil True by (rule exI[of _ \<Delta>1]) simp
    next
      case (Cons \<Delta>4 \<Delta>s'')
      show ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> Cons True by (rule exI[of _ \<Delta>4]) simp
    qed
  next
    case False hence "\<Delta> \<in> set \<Delta>s'" using Cons by auto
    then obtain \<Delta>2 where "(\<Delta>, \<Delta>2) \<in> allConsec (\<Delta>s' ## \<Delta>1)" using Cons by auto
    thus ?thesis unfolding \<open>\<Delta>s = (\<Delta>3 # \<Delta>s') ## \<Delta>1\<close> by (intro exI[of _ \<Delta>2]) (cases \<Delta>s', auto)
  qed
qed

lemma allConsec_set:
assumes "(\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s"
shows "\<Delta>1 \<in> set \<Delta>s \<and> \<Delta>2 \<in> set \<Delta>s"
using assms by (induct \<Delta>s rule: allConsec.induct) auto

(* Liniar decomposition: *)
theorem unwind_decomp_secure:
assumes n: "\<Delta>s \<noteq> []"
and i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> hd \<Delta>s istate vl istate vl1"
and c: "\<And> \<Delta>1 \<Delta>2. (\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s \<Longrightarrow> unwind_cont \<Delta>1 {\<Delta>1, \<Delta>2, \<Delta>e}"
and l: "unwind_cont (last \<Delta>s) {last \<Delta>s, \<Delta>e}"
and e: "unwind_exit \<Delta>e"
shows secure
proof-
  let ?\<Delta>0 = "hd \<Delta>s"  let ?\<Delta>s = "insert \<Delta>e (set \<Delta>s)"
  define "next" where "next \<Delta>1 =
    (if \<Delta>1 = \<Delta>e then {}
     else if \<Delta>1 = last \<Delta>s then {\<Delta>1,\<Delta>e}
     else {\<Delta>1,SOME \<Delta>2. (\<Delta>1,\<Delta>2) \<in> allConsec \<Delta>s,\<Delta>e})" for \<Delta>1
  show ?thesis
  proof(rule unwind_dec_secure)
    show "?\<Delta>0 \<in> ?\<Delta>s" using n by auto
  next
    fix vl vl1 assume "B vl vl1"
    thus "?\<Delta>0 istate vl istate vl1" by fact
  next
    fix \<Delta>
    assume 1: "\<Delta> \<in> ?\<Delta>s" show "next \<Delta> \<subseteq> ?\<Delta>s \<and> unwind_to \<Delta> (next \<Delta>)"
    proof-
      {assume "\<Delta> = \<Delta>e"
       hence ?thesis using e unfolding next_def unwind_exit_def unwind_to_def by auto
      }
      moreover
      {assume "\<Delta> = last \<Delta>s" and "\<Delta> \<noteq> \<Delta>e"
       hence ?thesis using n l unfolding next_def unwind_cont_def unwind_to_def by simp
      }
      moreover
      {assume 1: "\<Delta> \<in> set \<Delta>s" and 2: "\<Delta> \<noteq> last \<Delta>s" "\<Delta> \<noteq> \<Delta>e"
       then obtain \<Delta>' \<Delta>s' where \<Delta>s: "\<Delta>s = \<Delta>s' ## \<Delta>'" and \<Delta>: "\<Delta> \<in> set \<Delta>s'"
       by (metis (no_types) append_Cons append_assoc in_set_conv_decomp last_snoc rev_exhaust)
       have "\<exists> \<Delta>2. (\<Delta>, \<Delta>2) \<in> allConsec \<Delta>s" using set_allConsec[OF \<Delta> \<Delta>s] .
       hence "(\<Delta>, SOME \<Delta>2. (\<Delta>, \<Delta>2) \<in> allConsec \<Delta>s) \<in> allConsec \<Delta>s" by (metis (lifting) someI_ex)
       hence ?thesis using 1 2 c unfolding next_def unwind_cont_def unwind_to_def
       by simp (metis (no_types) allConsec_set)
      }
      ultimately show ?thesis using 1 by blast
    qed
  qed
qed

subsection\<open>Instances\<close>

corollary unwind_decomp3_secure:
assumes
i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta>1 istate vl istate vl1"
and c1: "unwind_cont \<Delta>1 {\<Delta>1, \<Delta>2, \<Delta>e}"
and c2: "unwind_cont \<Delta>2 {\<Delta>2, \<Delta>3, \<Delta>e}"
and l: "unwind_cont \<Delta>3 {\<Delta>3, \<Delta>e}"
and e: "unwind_exit \<Delta>e"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3]" \<Delta>e])
using assms by auto

corollary unwind_decomp4_secure:
assumes
i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta>1 istate vl istate vl1"
and c1: "unwind_cont \<Delta>1 {\<Delta>1, \<Delta>2, \<Delta>e}"
and c2: "unwind_cont \<Delta>2 {\<Delta>2, \<Delta>3, \<Delta>e}"
and c3: "unwind_cont \<Delta>3 {\<Delta>3, \<Delta>4, \<Delta>e}"
and l: "unwind_cont \<Delta>4 {\<Delta>4, \<Delta>e}"
and e: "unwind_exit \<Delta>e"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3, \<Delta>4]" \<Delta>e])
using assms by auto

corollary unwind_decomp5_secure:
assumes
i: "\<And> vl vl1. B vl vl1 \<Longrightarrow> \<Delta>1 istate vl istate vl1"
and c1: "unwind_cont \<Delta>1 {\<Delta>1, \<Delta>2, \<Delta>e}"
and c2: "unwind_cont \<Delta>2 {\<Delta>2, \<Delta>3, \<Delta>e}"
and c3: "unwind_cont \<Delta>3 {\<Delta>3, \<Delta>4, \<Delta>e}"
and c4: "unwind_cont \<Delta>4 {\<Delta>4, \<Delta>5, \<Delta>e}"
and l: "unwind_cont \<Delta>5 {\<Delta>5, \<Delta>e}"
and e: "unwind_exit \<Delta>e"
shows secure
apply(rule unwind_decomp_secure[of "[\<Delta>1, \<Delta>2, \<Delta>3, \<Delta>4, \<Delta>5]" \<Delta>e])
using assms by auto




(*<*)

end (* context BD_Security *)


end

(*>*)
