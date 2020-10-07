section \<open>Preparing Partial Order Reduction\<close>
theory SM_Visible
imports "../RefPoint/SM_LTL" Rename_Cfg
begin

  section \<open>Visible Part of State\<close>

  locale visible_prog = well_typed_prog +
    fixes is_vis_var :: "ident \<Rightarrow> bool"
  begin
    abbreviation "vis_vars \<equiv> Collect is_vis_var"

    definition interp_gs :: "global_state \<Rightarrow> exp set" where
      "interp_gs gs \<equiv> sm_props (global_state.variables gs |` vis_vars)"
  
    definition interp_gc :: "global_config \<Rightarrow> exp set" where
      "interp_gc gc \<equiv> interp_gs (global_config.state gc)"
    
    sublocale lv: Gen_Scheduler'_linit
      cfgc la_en' la_ex' 
      "{init_gc}" interp_gc .

    lemma lv_accept_conv: "lv.sa.accept w 
      \<longleftrightarrow> (\<exists>w'. w=interp_gs o w' \<and> ref_accept prog w')"
      unfolding lih'_accept_eq[symmetric]
      unfolding lih'.sa.accept_def lv.sa.accept_def
      unfolding lih'.sa.is_run_def
      unfolding lv.sa.is_run_def
      apply simp
      unfolding interp_gc_def[abs_def]
      by fastforce

  end
end

