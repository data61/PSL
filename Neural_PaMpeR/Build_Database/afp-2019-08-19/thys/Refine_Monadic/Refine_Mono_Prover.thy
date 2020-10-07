theory Refine_Mono_Prover
imports Main Automatic_Refinement.Refine_Lib
begin
  ML_file \<open>refine_mono_prover.ML\<close>

  setup Refine_Mono_Prover.setup
  declaration Refine_Mono_Prover.decl_setup

  method_setup refine_mono = 
    \<open>Scan.succeed (fn ctxt => SIMPLE_METHOD' (
      Refine_Mono_Prover.untriggered_mono_tac ctxt
    ))\<close> 
    "Refinement framework: Monotonicity prover"

  locale mono_setup_loc = 
    \<comment> \<open>Locale to set up monotonicity prover for given ordering operator\<close>
    fixes le :: "'a \<Rightarrow> 'a \<Rightarrow> bool" 
    assumes refl: "le x x"
  begin
    lemma monoI: "(\<And>f g x. (\<And>x. le (f x) (g x)) \<Longrightarrow> le (B f x) (B g x)) 
      \<Longrightarrow> monotone (fun_ord le) (fun_ord le) B"
      unfolding monotone_def fun_ord_def by blast
    
    lemma mono_if: "\<lbrakk>le t t'; le e e'\<rbrakk> \<Longrightarrow> le (If b t e) (If b t' e')" by auto
    lemma mono_let: "(\<And>x. le (f x) (f' x)) \<Longrightarrow> le (Let x f) (Let x f')" by auto

    lemmas mono_thms[refine_mono] = monoI mono_if mono_let refl

    declaration \<open>Refine_Mono_Prover.declare_mono_triggers @{thms monoI}\<close>

  end

  interpretation order_mono_setup: mono_setup_loc "(\<le>) :: 'a::preorder \<Rightarrow> _"
    by standard auto

  declaration \<open>Refine_Mono_Prover.declare_mono_triggers @{thms Orderings.monoI}\<close>

  lemmas [refine_mono] = 
    lfp_mono[OF le_funI, THEN le_funD] 
    gfp_mono[OF le_funI, THEN le_funD]

end

