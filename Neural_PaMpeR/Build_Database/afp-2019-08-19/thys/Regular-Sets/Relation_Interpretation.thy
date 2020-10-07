section \<open>Regular Expressions as Homogeneous Binary Relations\<close>

theory Relation_Interpretation
imports Regular_Exp
begin

primrec rel :: "('a \<Rightarrow> ('b * 'b) set) \<Rightarrow> 'a rexp \<Rightarrow> ('b * 'b) set"
where
  "rel v Zero = {}" |
  "rel v One = Id" |
  "rel v (Atom a) = v a" |
  "rel v (Plus r s) = rel v r \<union> rel v s" |
  "rel v (Times r s) = rel v r O rel v s" |
  "rel v (Star r) = (rel v r)^*"

primrec word_rel :: "('a \<Rightarrow> ('b * 'b) set) \<Rightarrow> 'a list \<Rightarrow> ('b * 'b) set"
where
  "word_rel v [] = Id"
| "word_rel v (a#as) = v a O word_rel v as"

lemma word_rel_append: 
  "word_rel v w O word_rel v w' = word_rel v (w @ w')"
by (rule sym) (induct w, auto)

lemma rel_word_rel: "rel v r = (\<Union>w\<in>lang r. word_rel v w)"
proof (induct r)
  case Times thus ?case 
    by (auto simp: rel_def word_rel_append conc_def relcomp_UNION_distrib relcomp_UNION_distrib2)
next
  case (Star r)
  { fix n
    have "(rel v r) ^^ n = (\<Union>w \<in> lang r ^^ n. word_rel v w)"
    proof (induct n)
      case 0 show ?case by simp
    next
      case (Suc n) thus ?case
        unfolding relpow.simps relpow_commute[symmetric]
        by (auto simp add: Star conc_def word_rel_append
          relcomp_UNION_distrib relcomp_UNION_distrib2)
    qed }

  thus ?case unfolding rel.simps
    by (force simp: rtrancl_power star_def)
qed auto


text \<open>Soundness:\<close>

lemma soundness:
 "lang r = lang s \<Longrightarrow> rel v r = rel v s"
unfolding rel_word_rel by auto

end
