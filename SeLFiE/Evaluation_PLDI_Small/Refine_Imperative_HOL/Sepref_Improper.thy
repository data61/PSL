section \<open>Ad-Hoc Solutions\<close>
theory Sepref_Improper
imports
  Sepref_Tool
  Sepref_HOL_Bindings
  (*Sepref_IICF_Bindings*)
  Sepref_Foreach
  Sepref_Intf_Util
begin
  text \<open>This theory provides some ad-hoc solutions to practical problems, 
    that, however, still need a more robust/clean solution\<close>

  subsection \<open>Pure Higher-Order Functions\<close>
  text \<open>Ad-Hoc way to support pure higher-order arguments\<close>
  
  (* TODO: Cleaner way for pure higher-order functions! 
    Alternative: Work in context with fixed tgt
  *)
  definition pho_apply :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> 'b" where [code_unfold,simp]: "pho_apply f x = f x"
  sepref_register pho_apply
  
  lemmas fold_pho_apply = pho_apply_def[symmetric]

  lemma pure_fun_refine[sepref_fr_rules]: "hn_refine 
    (hn_val (A\<rightarrow>B) f fi * hn_val A x xi) 
    (return (pho_apply$fi$xi)) 
    (hn_val (A\<rightarrow>B) f fi * hn_val A x xi)
    (pure B)
    (RETURN$(pho_apply$f$x))"
    by (sep_auto intro!: hn_refineI simp: pure_def hn_ctxt_def dest: fun_relD)







end
