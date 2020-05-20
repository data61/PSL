theory DRAT_Misc
imports "Refine_Imperative_HOL.IICF"
begin
  
  hide_const (open) Word.slice

    
    
(** NOT MOVED **)    
subsection \<open>Maybe-Head Insertion into Distinct List\<close>    
text \<open>
  Insertion into distinct list, where the inserted element is either the head of the list, or
  not contained into the list. Useful to avoid duplicate insertions into the 
  literal->clause map.
\<close>  
    
definition "mbhd_invar x l \<equiv> distinct l \<and> x\<notin>set (tl l)"
definition (in -) "mbhd_insert x l \<equiv> if l=[] then [x] else if (x = hd l) then l else x#l"

lemma mbhd_insert_invar: "mbhd_invar x l \<Longrightarrow> mbhd_invar x (mbhd_insert x l)"
  unfolding mbhd_invar_def mbhd_insert_def by (cases l) auto

lemma mbhd_insert_correct: "set (mbhd_insert x l) = insert x (set l)"
  unfolding mbhd_insert_def by auto

lemma mbhd_invar_init: "distinct l \<and> x\<notin>set l \<Longrightarrow> mbhd_invar x l"
  unfolding mbhd_invar_def by (cases l) auto

lemma mbhd_invar_exit: "mbhd_invar x l \<Longrightarrow> distinct l"
  unfolding mbhd_invar_def by (cases l) auto
    
end
