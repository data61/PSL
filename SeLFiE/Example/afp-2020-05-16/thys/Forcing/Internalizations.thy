section\<open>Aids to internalize formulas\<close>
theory Internalizations
  imports 
    "ZF-Constructible.DPow_absolute" 
begin

text\<open>We found it useful to have slightly different versions of some 
results in ZF-Constructible:\<close>
lemma nth_closed :
  assumes "0\<in>A" "env\<in>list(A)"
  shows "nth(n,env)\<in>A" 
  using assms(2,1) unfolding nth_def by (induct env; simp)

lemmas FOL_sats_iff = sats_Nand_iff sats_Forall_iff sats_Neg_iff sats_And_iff
  sats_Or_iff sats_Implies_iff sats_Iff_iff sats_Exists_iff 

lemma nth_ConsI: "\<lbrakk>nth(n,l) = x; n \<in> nat\<rbrakk> \<Longrightarrow> nth(succ(n), Cons(a,l)) = x"
by simp

lemmas nth_rules = nth_0 nth_ConsI nat_0I nat_succI
lemmas sep_rules = nth_0 nth_ConsI FOL_iff_sats function_iff_sats
                   fun_plus_iff_sats successor_iff_sats
                    omega_iff_sats FOL_sats_iff Replace_iff_sats

text\<open>Also a different compilation of lemmas (term\<open>sep_rules\<close>) used in formula
 synthesis\<close>
lemmas fm_defs = omega_fm_def limit_ordinal_fm_def empty_fm_def typed_function_fm_def
                 pair_fm_def upair_fm_def domain_fm_def function_fm_def succ_fm_def
                 cons_fm_def fun_apply_fm_def image_fm_def big_union_fm_def union_fm_def
                 relation_fm_def composition_fm_def field_fm_def ordinal_fm_def range_fm_def
                 transset_fm_def subset_fm_def Replace_fm_def


end
