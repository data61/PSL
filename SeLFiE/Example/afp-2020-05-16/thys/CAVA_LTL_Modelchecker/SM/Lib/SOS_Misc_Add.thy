theory SOS_Misc_Add
imports Main "HOL-Library.Monad_Syntax"
begin

lemma finite_ImageI:
  assumes "finite A"  
  assumes "\<And>a. a\<in>A \<Longrightarrow> finite (R``{a})"
  shows "finite (R``A)"
proof -
  note [[simproc add: finite_Collect]]
  have "R``A = \<Union>{R``{a} | a. a:A}"
    by auto
  also have "finite (\<Union>{R``{a} | a. a:A})"
    apply (rule finite_Union)
    apply (simp add: assms)
    apply (clarsimp simp: assms)
    done
  finally show ?thesis .
qed

  (* Set monad utilities *)

  lemma do_set_push_Image:
    "\<And>g f m. g`(do {x\<leftarrow>m; f x}) = do {x\<leftarrow>m; g`f x}"
    "\<And>g f m. g`(do {let x = m; f x}) = (do {let x=m; g`f x})"
    by fastforce+
    
  lemma case_option_distrib: "f (case x of Some v \<Rightarrow> fs v | None \<Rightarrow> fn) 
    = (case x of Some v \<Rightarrow> f (fs v) | None \<Rightarrow> f fn)" 
    by (auto split: option.split)

  lemma case_sum_distrib: "f (case x of Inl x \<Rightarrow> fl x | Inr x \<Rightarrow> fr x) = 
    (case x of Inl x \<Rightarrow> f (fl x) | Inr x \<Rightarrow> f (fr x))"
    by (auto split: sum.split)

  lemma do_set_eq_bind:
    assumes "m'=m"
    assumes "\<And>x. x\<in>m \<Longrightarrow> f x = g x"
    shows "do {x\<leftarrow>m; f x} = do {x\<leftarrow>m'; g x}"  
    using assms by auto

  lemma finite_bindI[intro]:
    assumes "finite m"
    assumes "\<And>x. x\<in>m \<Longrightarrow> finite (f x)"
    shows "finite (do { x\<leftarrow>m; f x })"
  proof -
    have S: "do { x\<leftarrow>m; f x } = \<Union>(f`m)"
      by auto
  
    show ?thesis  
      apply (subst S)
      using assms
      by blast
  qed        
  

(* Option monad utilities *)

  primrec assert_option :: "bool \<Rightarrow> unit option" where
    "assert_option True = Some ()" | "assert_option False = None"

  lemma assert_option_eqs[simp]:
    "assert_option \<Phi> = Some x \<longleftrightarrow> \<Phi>"  
    "assert_option \<Phi> = None \<longleftrightarrow> \<not>\<Phi>"  
    by (cases \<Phi>) auto


  (* TODO: Move *)
  lemma disj_eq_nota_conv[simp]:
    "(a \<or> b \<longleftrightarrow> \<not>a) \<longleftrightarrow> (a=False \<and> b=True)" 
    "(b \<or> a \<longleftrightarrow> \<not>a) \<longleftrightarrow> (a=False \<and> b=True)" 
    "(\<not>a \<or> b \<longleftrightarrow> a) \<longleftrightarrow> (a=True \<and> b=True)" 
    "(b \<or> \<not>a \<longleftrightarrow> a) \<longleftrightarrow> (a=True \<and> b=True)" 
    by auto

  lemma all_disjx_conv[simp]:
    "(\<forall>x. x \<or> P x) \<longleftrightarrow> P False"  
    "(\<forall>x. x \<or> P (\<not>x)) \<longleftrightarrow> P True"
    apply safe
    apply (drule spec[where x=False], simp)
    apply (case_tac x, auto) []
    apply (drule spec[where x=False], simp)
    apply (case_tac x, auto) []
    done

  lemma neq_Some_bool_cases[consumes 1, case_names None Some]:
    assumes "a\<noteq>Some x"  
    obtains "a=None" | "a = Some (\<not>x)"
    using assms by auto



  primrec find_min_idx :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<rightharpoonup> nat" where
    "find_min_idx P [] = None"
  | "find_min_idx P (x#xs) = (
      if P x then Some 0 else
      map_option Suc (find_min_idx P xs)
    )"
  
  lemma find_min_idx_None_conv: 
    "find_min_idx P l = None \<longleftrightarrow> (\<forall>a\<in>set l. \<not>P a)"
    apply (induction l)
    apply auto
    done

  lemma find_min_idx_SomeD:
    "find_min_idx P l = Some i \<Longrightarrow> P (l!i) \<and> i < length l"
    by (induction l arbitrary: i) (auto split: if_split_asm)

  lemma find_min_idx_SomeD_complete: 
    "find_min_idx P l = Some i \<Longrightarrow> (P (l!i) \<and> i < length l \<and> (\<forall>j<i. \<not>P (l!j)))"
    apply (induction l arbitrary: i) 
    apply (auto split: if_split_asm)
    apply (case_tac j)
    apply auto
    done

end

