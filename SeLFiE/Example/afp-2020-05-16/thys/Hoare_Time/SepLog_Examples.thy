subsection "Examples"
theory SepLog_Examples
imports SepLog_Hoare
begin


      
subsubsection \<open>nice example\<close>
  
     
lemmas strongAssign = Assign''''[OF _ strengthen_post, OF _ Frame_R, OF _ Assign''']  
    
lemma myrule: assumes "case s of (s, n) \<Rightarrow> ($ (2 * x) \<and>* ''x'' \<hookrightarrow> int x) (s, n) \<and> lmaps_to_axpr' (Less (N 0) (V ''x'')) True s" 
    and "symevalb ($ (2 * x) ** ''x'' \<hookrightarrow> int x) (Less (N 0) (V ''x'')) v"
    shows "(\<up>(v=True) ** $ (2 * x) ** ''x'' \<hookrightarrow> int x) s"
      using assms unfolding symevalb_def lmaps_to_axpr'_def by auto 
  
fun sum :: "int \<Rightarrow> int" where
"sum i = (if i \<le> 0 then 0 else sum (i - 1) + i)"

abbreviation "wsum ==
  WHILE Less (N 0) (V ''x'')
  DO ( 
      ''x'' ::= Plus (V ''x'') (N (- 1)))"
  
  
  
  
lemma E4_R: "\<turnstile>\<^sub>3 {\<up>(v>0) ** $(2*v) ** pointsto ''x'' (int v) } 
            ''x'' ::= Plus (V ''x'') (N (- 1))
           {\<up>(v>0) ** $(2*v-1) ** pointsto ''x'' (int v-1) }"
      apply(rule pureI)
  apply(rule strongAssign)
    apply(rule symeval | frame_inference)+   
     by (simp add:  sep_reorder_dollar ) 
     
  
  
lemma prod_0: 
  shows "(\<lambda>(s::char list \<Rightarrow> int option, c::nat). s = Map.empty \<and> c = 0) h \<Longrightarrow> h = 0" by (auto simp: zero_prod_def zero_fun_def)
 
 

lemma example2: "\<turnstile>\<^sub>3 { (pointsto ''x'' n) ** (pointsto ''y'' n) ** $1 } ''x'' ::= Plus (V ''x'') (N (- 1)) { (pointsto ''x'' (n-1)) ** (pointsto ''y'' n) }"
  apply(rule conseq)    
  apply(rule Frame[where F="(pointsto ''y'' n)" and P="lmaps_to_expr_x ''x'' ( Plus (V ''x'') (N (- 1))) (n-1) ** $1"])
    apply (rule Assign)
   apply (simp add: sep_conj_assoc)  apply (rule sep_conj_impl)
     apply auto[1]
    subgoal for s h unfolding pointsto_def apply auto
      by (meson option.distinct(1))    
     apply (simp add: sep_conj_commute) 
    apply simp apply (rule sep_conj_impl)
      apply auto[1]
     apply auto
      unfolding sep_conj_def
      using prod_0 by fastforce   
    

end