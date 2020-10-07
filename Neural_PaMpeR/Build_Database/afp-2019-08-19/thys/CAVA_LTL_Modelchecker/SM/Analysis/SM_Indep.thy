theory SM_Indep
imports 
  "../Refine/SM_Finite_Reachable" 
  Partial_Order_Reduction.Transition_System_Interpreted_Traces
  SM_Variables
begin

context visible_prog
begin
  
  fun ind :: "global_action option \<Rightarrow> global_action option \<Rightarrow> bool" where
    "ind None None \<longleftrightarrow> True"
  | "ind (Some _) None \<longleftrightarrow> False"
  | "ind None (Some _) \<longleftrightarrow> False"
  | "ind (Some (pid1,c1,a1,c1')) (Some (pid2,c2,a2,c2')) 
    \<longleftrightarrow> 
      pid1\<noteq>pid2
    \<and> (write_globals a1 \<inter> read_globals a2 = {})
    \<and> (write_globals a2 \<inter> read_globals a1 = {})
    \<and> (write_globals a1 \<inter> write_globals a2 = {})
    \<and> (\<not>( Some (pid1,c1,a1,c1')\<in>jsys.visible 
        \<and> Some (pid2,c2,a2,c2') \<in> jsys.visible))"
  
  lemma ind_symmetric: "ind a b \<longleftrightarrow> ind b a"
    by (cases "(a,b)" rule: ind.cases) auto
  
  lemma ga_ex_swap:
    assumes PIDNE: "pid1\<noteq>pid2"
    assumes DJ: 
      "write_globals a1 \<inter> read_globals a2 = {}"
      "write_globals a2 \<inter> read_globals a1 = {}"
      "write_globals a1 \<inter> write_globals a2 = {}"
    shows "ga_ex (Some (pid1,c1,a1,c1')) (ga_ex (Some (pid2,c2,a2,c2')) gc) 
         = ga_ex (Some (pid2,c2,a2,c2')) (ga_ex (Some (pid1,c1,a1,c1')) gc)"
    using PIDNE
    apply (auto 
      simp: ga_ex_def ga_gex_def 
      simp: list_update_swap dest: ex_swap_global[OF DJ]
      split: prod.splits)
    done
  
  corollary ind_swap:
    "ind ga1 ga2 \<Longrightarrow> ga_ex ga2 (ga_ex ga1 gc) = ga_ex ga1 (ga_ex ga2 gc)"
    apply (cases "(ga1,ga2)" rule: ind.cases)
    apply (auto intro: ga_ex_swap)
    done
  
  
  lemma ind_en: "\<lbrakk>ind a b; a \<in> ga_en p\<rbrakk>
         \<Longrightarrow> (b \<in> ga_en (ga_ex a p)) = (b \<in> ga_en p)"
    apply (cases "(a,b)" rule: ind.cases, simp_all)
    apply (auto 
      simp: ga_ex_def ga_en_def ga_gex_def ga_gen_def ex_pres_en
      split: prod.splits
      )
    done
  
  sublocale jsys: transition_system_traces ga_ex "\<lambda> a p. a \<in> ga_en p" ind
    apply unfold_locales
    apply (simp_all add: ind_symmetric ind_en ind_swap)
    done
      
  sublocale jsys: transition_system_interpreted_traces 
    ga_ex "\<lambda> a p. a \<in> ga_en p" pid_interp_gc
    ind
    apply unfold_locales
    apply (case_tac "(a,b)" rule: ind.cases)
    apply (auto simp: jsys.visible_def)
    done
  
  end
end

