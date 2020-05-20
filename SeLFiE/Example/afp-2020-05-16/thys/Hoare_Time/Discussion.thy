section "Discussion"
subsection \<open>Relation between the explicit Hoare logics\<close>
theory Discussion
imports Quant_Hoare SepLog_Hoare
begin
 
subsubsection \<open>Relation SepLogic to quantHoare\<close>
     
definition em where "em P' = (%(ps,n). P' (emb ps (%_. 0)) \<le> enat n )"  (* with equality next lemma also works *)
  
lemma assumes s: "\<Turnstile>\<^sub>3 { em P'} c { em Q' }"
shows  "\<Turnstile>\<^sub>2 { P' } c { Q' }"
proof -
  from s have s': "\<And>ps n. em P' (ps, n) \<Longrightarrow> (\<exists>ps' m. (c, ps) \<Rightarrow>\<^sub>A m \<Down> ps' \<and> m \<le> n \<and> em Q' (ps', n - m))" unfolding hoare3_valid_def  by auto
  {
    fix s
    assume P': "P' s < \<infinity>" 
    then obtain n where n: "P' s = enat n"
      by fastforce
    with P' have "em P' (part s, n)" unfolding em_def by auto 
    with s' obtain ps' m where c: "(c, part s) \<Rightarrow>\<^sub>A m \<Down> ps'" and m: "m \<le> n" and Q': "em Q' (ps', n - m)" by blast
        
    from Q' have q: "Q' (emb ps' (\<lambda>_. 0)) \<le> enat ( n - m)" unfolding em_def by auto
        
        
    thm full_to_part  part_to_full
    have i: "(c, s) \<Rightarrow> m \<Down> emb ps' (\<lambda>_. 0)" using  part_to_full'[OF c] apply simp done 
                
        
    have ii: "enat m + Q' (emb ps' (\<lambda>_. 0)) \<le> P' s" unfolding  n using q m
      using enat_ile by fastforce 
      
    from i ii have "(\<exists>t p. (c, s) \<Rightarrow> p \<Down> t \<and> enat p + Q' t \<le> P' s)" by auto
  } then
  show ?thesis unfolding hoare2_valid_def by blast
qed 
  

end