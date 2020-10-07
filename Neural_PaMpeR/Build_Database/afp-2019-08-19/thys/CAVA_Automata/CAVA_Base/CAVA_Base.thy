section "Setup of Environment for CAVA Model Checker"
theory CAVA_Base
  imports 
  Collections.CollectionsV1  (*-- {* Compatibility with ICF 1.0 *}*)
  Collections.Refine_Dflt      

  Statistics (*-- {* Collecting statistics by instrumenting the formalization *}*)

  CAVA_Code_Target (*-- {* Code Generator Setup *}*)
begin

hide_const (open) CollectionsV1.ahs_rel

(*
(* Select-function that selects element from set *)
(* TODO: Move! Is select properly integrated into autoref? *)
  definition select where
    "select S \<equiv> if S={} then RETURN None else RES {Some s | s. s\<in>S}"

lemma select_correct: 
  "select X \<le> SPEC (\<lambda>r. case r of None \<Rightarrow> X={} | Some x \<Rightarrow> x\<in>X)"
  unfolding select_def
  apply (refine_rcg refine_vcg)
  by auto
*)
  
  text \<open>Cleaning up the namespace a bit\<close>
  
  hide_type (open) Word.word
  no_notation test_bit (infixl "!!" 100)

  text \<open>Some custom setup in cava, that does not match HOL defaults:\<close>
  declare Let_def[simp add]

end
