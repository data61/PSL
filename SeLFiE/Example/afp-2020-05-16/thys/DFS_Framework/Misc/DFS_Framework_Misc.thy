theory DFS_Framework_Misc
imports Automatic_Refinement.Misc
begin

(* General *)
lemma tri_caseE:
  "\<lbrakk>\<lbrakk>\<not>P;\<not>Q\<rbrakk> \<Longrightarrow> R; P \<Longrightarrow> R; \<lbrakk>\<not>P; Q\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
by auto

(* TODO: How often have we formalized this now? *)
definition "opt_tag x y \<equiv> x=y"
lemma opt_tagI: "opt_tag x x" unfolding opt_tag_def by simp
lemma opt_tagD: "opt_tag x y \<Longrightarrow> x=y" unfolding opt_tag_def by simp

(* Usage example, to simplify term
  schematic_lemma "term = ?c"
    apply (rule opt_tagD)
    apply simp, unfold, whatever ...
    by (rule opt_tagI)
*)

end

