theory Sep_Algebra_Add
  imports "Separation_Algebra.Separation_Algebra" "Separation_Algebra.Sep_Heap_Instance"
    Product_Separation_Algebra
begin

definition puree :: "bool \<Rightarrow> 'h::sep_algebra \<Rightarrow> bool" ("\<up>") where "puree P \<equiv> \<lambda>h. h=0 \<and> P"

lemma puree_alt: "\<up>\<Phi> = (\<langle>\<Phi>\<rangle> and \<box>)"
  by (auto simp: puree_def sep_empty_def)

lemma pure_alt: "\<langle>\<Phi>\<rangle> = (\<up>\<Phi> ** sep_true)"
  apply (clarsimp simp: puree_def)
proof -
  { fix aa :: 'a
    obtain aaa :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a" where
      ff1: "\<And>p pa a pb pc aa. (\<not> (p \<and>* pa) a \<or> p (aaa p pb) \<or> (pb \<and>*
pa) a) \<and> (\<not> pb (aaa p pb) \<or> \<not> (p \<and>* pc) aa \<or> (pb \<and>* pc) aa)"
      by (metis (no_types) sep_globalise)
    then have "\<exists>p. ((\<lambda>a. a = 0) \<and>* p) aa"
      by (metis (full_types) sep_conj_commuteI sep_conj_sep_emptyE
sep_empty_def)
    then have "\<not> \<Phi> \<or> \<Phi> \<and> ((\<lambda>a. a = 0) \<and>* (\<lambda>a. True)) aa"
      using ff1 by (metis (no_types) sep_conj_commuteI) }
  then show "(\<lambda>a. \<Phi>) = (\<lambda>a. \<Phi> \<and> ((\<lambda>a. (a::'a) = 0) \<and>* (\<lambda>a. True)) a)"
    by blast
qed
  
abbreviation NO_PURE :: "bool \<Rightarrow> ('h::sep_algebra \<Rightarrow> bool) \<Rightarrow> bool" 
  where "NO_PURE X Q \<equiv> (NO_MATCH (\<langle>X\<rangle>::'h\<Rightarrow>bool) Q \<and> NO_MATCH ((\<up>X)::'h\<Rightarrow>bool) Q)"

named_theorems sep_simplify \<open>Assertion simplifications\<close>

lemma sep_reorder[sep_simplify]:  
  "((a \<and>* b) \<and>* c) = (a \<and>* b \<and>* c)"
  "(NO_PURE X a) \<Longrightarrow> (a ** b) = (b ** a)"
  "(NO_PURE X b) \<Longrightarrow> (b \<and>* a \<and>* c) = (a \<and>* b \<and>* c)"
  "(Q ** \<langle>P\<rangle>) = (\<langle>P\<rangle> ** Q)"
  "(Q ** \<up>P) = (\<up>P ** Q)"
  "NO_PURE X Q \<Longrightarrow> (Q ** \<langle>P\<rangle> ** F) = (\<langle>P\<rangle> ** Q ** F)"
  "NO_PURE X Q \<Longrightarrow> (Q ** \<up>P ** F) = (\<up>P ** Q ** F)"
  by (simp_all add: sep.add_ac)

lemma sep_combine1[simp]:
  "(\<up>P ** \<up>Q) = \<up>(P\<and>Q)"
  "(\<langle>P\<rangle> ** \<langle>Q\<rangle>) = \<langle>P\<and>Q\<rangle>"
  "(\<up>P ** \<langle>Q\<rangle>) = \<langle>P\<and>Q\<rangle>"
  "(\<langle>P\<rangle> ** \<up>Q) = \<langle>P\<and>Q\<rangle>"
  apply (auto simp add: sep_conj_def puree_def intro!: ext)
  apply (rule_tac x=0 in exI)
  apply simp
  done

lemma sep_combine2[simp]:
  "(\<up>P ** \<up>Q ** F) = (\<up>(P\<and>Q) ** F)"
  "(\<langle>P\<rangle> ** \<langle>Q\<rangle> ** F) = (\<langle>P\<and>Q\<rangle> ** F)"
  "(\<up>P ** \<langle>Q\<rangle> ** F) = (\<langle>P\<and>Q\<rangle> ** F)"
  "(\<langle>P\<rangle> ** \<up>Q ** F) = (\<langle>P\<and>Q\<rangle> ** F)"
  apply (subst sep.add_assoc[symmetric]; simp)+
  done

lemma sep_extract_pure[simp]:
  "NO_MATCH True P \<Longrightarrow> (\<langle>P\<rangle> ** Q) h = (P \<and> (sep_true ** Q) h)"
  "(\<up>P ** Q) h = (P \<and> Q h)"
  "\<up>True = \<box>"
  "\<up>False = sep_false"
  using sep_conj_sep_true_right apply fastforce
  by (auto simp: puree_def sep_empty_def[symmetric])

lemma sep_pure_front2[simp]: 
  "(\<up>P ** A ** \<up>Q ** F) = (\<up>(P \<and> Q) ** F ** A)"
  apply (simp add: sep_reorder)
  done

lemma ex_h_simps[simp]: 
  "Ex (\<up>\<Phi>) \<longleftrightarrow> \<Phi>"
  "Ex (\<up>\<Phi> ** P) \<longleftrightarrow> (\<Phi> \<and> Ex P)"
  apply (cases \<Phi>; auto)
  apply auto
  done
  
lemma
  fixes h :: "('a \<Rightarrow> 'b option) * nat"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)
    
(* map_le *)
lemma map_le_substate_conv: "map_le = sep_substate"
  unfolding map_le_def sep_substate_def sep_disj_fun_def plus_fun_def domain_def dom_def none_def apply (auto intro!: ext)
  subgoal for m1 m2 apply(rule exI[where x="%x. if (\<exists>y. m1 x = Some y) then None else m2 x"])
    by auto
  by blast


end