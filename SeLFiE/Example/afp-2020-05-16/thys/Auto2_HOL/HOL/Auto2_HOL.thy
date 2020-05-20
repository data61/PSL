(*
  File: Auto2_HOL.thy
  Author: Bohua Zhan

  Main file for auto2 setup in HOL.
*)

theory Auto2_HOL
  imports HOL_Base
  keywords "@proof" :: prf_block % "proof"
    and "@have" "@case" "@obtain" "@let" "@contradiction" "@strong_induct" :: prf_decl % "proof"
    and "@unfold" :: prf_decl % "proof"
    and "@induct" "@fun_induct" "@case_induct" "@prop_induct" "@cases" :: prf_decl % "proof"
    and "@apply_induct_hyp" :: prf_decl % "proof"
    and "@subgoal" "@endgoal" "@end" :: prf_decl % "proof"
    and "@qed" :: qed_block % "proof"
    and "@with" "where" "arbitrary" "@rule" :: quasi_command
begin

ML_file \<open>../util.ML\<close>
ML_file \<open>../util_base.ML\<close>
ML_file \<open>auto2_hol.ML\<close>
ML_file \<open>../util_logic.ML\<close>
ML_file \<open>../box_id.ML\<close>
ML_file \<open>../consts.ML\<close>
ML_file \<open>../property.ML\<close>
ML_file \<open>../wellform.ML\<close>
ML_file \<open>../wfterm.ML\<close>
ML_file \<open>../rewrite.ML\<close>
ML_file \<open>../propertydata.ML\<close>
ML_file \<open>../matcher.ML\<close>
ML_file \<open>../items.ML\<close>
ML_file \<open>../wfdata.ML\<close>
ML_file \<open>../auto2_data.ML\<close>
ML_file \<open>../status.ML\<close>
ML_file \<open>../normalize.ML\<close>
ML_file \<open>../proofsteps.ML\<close>
ML_file \<open>../auto2_state.ML\<close>
ML_file \<open>../logic_steps.ML\<close>
ML_file \<open>../auto2.ML\<close>
ML_file \<open>../auto2_outer.ML\<close>

ML_file \<open>acdata.ML\<close>
ML_file \<open>ac_steps.ML\<close>
ML_file \<open>unfolding.ML\<close>
ML_file \<open>induct_outer.ML\<close>
ML_file \<open>extra_hol.ML\<close>

method_setup auto2 = \<open>Scan.succeed (SIMPLE_METHOD o Auto2.auto2_tac)\<close> "auto2 prover"

attribute_setup forward = \<open>setup_attrib add_forward_prfstep\<close>
attribute_setup backward = \<open>setup_attrib add_backward_prfstep\<close>
attribute_setup backward1 = \<open>setup_attrib add_backward1_prfstep\<close>
attribute_setup backward2 = \<open>setup_attrib add_backward2_prfstep\<close>
attribute_setup resolve = \<open>setup_attrib add_resolve_prfstep\<close>
attribute_setup rewrite = \<open>setup_attrib add_rewrite_rule\<close>
attribute_setup rewrite_back = \<open>setup_attrib add_rewrite_rule_back\<close>
attribute_setup rewrite_bidir = \<open>setup_attrib add_rewrite_rule_bidir\<close>
attribute_setup forward_arg1 = \<open>setup_attrib add_forward_arg1_prfstep\<close>
attribute_setup forward_arg = \<open>setup_attrib add_forward_arg_prfstep\<close>
attribute_setup rewrite_arg = \<open>setup_attrib add_rewrite_arg_rule\<close>

end
