(******************************************************************************)
(* Project: The Isabelle/UTP Proof System                                     *)
(* File: utp_tactics.thy                                                      *)
(* Authors: Simon Foster & Frank Zeyda (University of York, UK)               *)
(* Emails: simon.foster@york.ac.uk frank.zeyda@york.ac.uk                     *)
(******************************************************************************)

text_raw \<open> \newpage \<close>

section \<open> UTP Tactics \<close>

theory utp_tactics
  imports 
    utp_expr utp_unrest utp_usedby
keywords "update_uexpr_rep_eq_thms" :: thy_decl
begin

declare image_comp [simp]

text \<open>
  In this theory, we define several automatic proof tactics that use transfer
  techniques to re-interpret proof goals about UTP predicates and relations in
  terms of pure HOL conjectures. The fundamental tactics to achieve this are
  \<open>pred_simp\<close> and \<open>rel_simp\<close>; a more detailed explanation of their
  behaviour is given below. The tactics can be given optional arguments to
  fine-tune their behaviour. By default, they use a weaker but faster form of
  transfer using rewriting; the option \<open>robust\<close>, however, forces them to
  use the slower but more powerful transfer of Isabelle's lifting package. A
  second option \<open>no_interp\<close> suppresses the re-interpretation of state
  spaces in order to eradicate record for tuple types prior to automatic proof.
\<close>

text \<open>
  In addition to \<open>pred_simp\<close> and \<open>rel_simp\<close>, we also provide the
  tactics \<open>pred_auto\<close> and \<open>rel_auto\<close>, as well as \<open>pred_blast\<close>
  and \<open>rel_blast\<close>; they, in essence, sequence the simplification tactics
  with the methods @{method auto} and @{method blast}, respectively.
\<close>

subsection \<open> Theorem Attributes \<close>

text \<open>
  The following named attributes have to be introduced already here since our
  tactics must be able to see them. Note that we do not want to import the
  theories \<open>utp_pred\<close> and \<open>utp_rel\<close> here, so that both can
  potentially already make use of the tactics we define in this theory.
\<close>

named_theorems upred_defs "upred definitional theorems"
named_theorems urel_defs "urel definitional theorems"

subsection \<open> Generic Methods \<close>

text \<open>
  We set up several automatic tactics that recast theorems on UTP predicates
  into equivalent HOL predicates, eliminating artefacts of the mechanisation
  as much as this is possible. Our approach is first to unfold all relevant
  definition of the UTP predicate model, then perform a transfer, and finally
  simplify by using lens and variable definitions, the split laws of alphabet
  records, and interpretation laws to convert record-based state spaces into
  products. The definition of the respective methods is facilitated by the
  Eisbach tool: we define generic methods that are parametrised by the tactics
  used for transfer, interpretation and subsequent automatic proof. Note that
  the tactics only apply to the head goal.
\<close>

text \<open> \textsf{Generic Predicate Tactics} \<close>

method gen_pred_tac methods transfer_tac interp_tac prove_tac = (
  ((unfold upred_defs) [1])?;
  (transfer_tac),
  (simp add: fun_eq_iff
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?,
  (interp_tac)?);
  (prove_tac)

text \<open> \textsf{Generic Relational Tactics} \<close>

method gen_rel_tac methods transfer_tac interp_tac prove_tac = (
  ((unfold upred_defs urel_defs) [1])?;
  (transfer_tac),
  (simp add: fun_eq_iff relcomp_unfold OO_def
    lens_defs upred_defs alpha_splits Product_Type.split_beta)?,
  (interp_tac)?);
  (prove_tac)

subsection \<open> Transfer Tactics \<close>

text \<open> Next, we define the component tactics used for transfer. \<close>

subsubsection \<open> Robust Transfer \<close>

text \<open> Robust transfer uses the transfer method of the lifting package. \<close>

method slow_uexpr_transfer = (transfer)

subsubsection \<open> Faster Transfer \<close>

text \<open>
  Fast transfer side-steps the use of the (@{method transfer}) method in favour
  of plain rewriting with the underlying \<open>rep_eq_...\<close> laws of lifted
  definitions. For moderately complex terms, surprisingly, the transfer step
  turned out to be a bottle-neck in some proofs; we observed that faster
  transfer resulted in a speed-up of approximately 30\% when building the UTP
  theory heaps. On the downside, tactics using faster transfer do not always
  work but merely in about 95\% of the cases. The approach typically works well
  when proving predicate equalities and refinements conjectures.

  A known limitation is that the faster tactic, unlike lifting transfer, does
  not turn free variables into meta-quantified ones. This can, in some cases,
  interfere with the interpretation step and cause subsequent application of
  automatic proof tactics to fail. A fix is in progress [TODO].
\<close>
paragraph \<open> Attribute Setup \<close>

text \<open>
  We first configure a dynamic attribute \<open>uexpr_rep_eq_thms\<close> to
  automatically collect all \<open>rep_eq_\<close> laws of lifted definitions on the
  @{type uexpr} type.
\<close>

ML_file "uexpr_rep_eq.ML"

setup \<open>
  Global_Theory.add_thms_dynamic (@{binding uexpr_rep_eq_thms},
    uexpr_rep_eq.get_uexpr_rep_eq_thms o Context.theory_of)
\<close>

text \<open>
  We next configure a command @{command update_uexpr_rep_eq_thms} in order to
  update the content of the \<open>uexpr_rep_eq_thms\<close> attribute. Although the
  relevant theorems are collected automatically, for efficiency reasons, the
  user has to manually trigger the update process. The command must hence be
  executed whenever new lifted definitions for type @{type uexpr} are created.
  The updating mechanism uses @{command find_theorems} under the hood.
\<close>

ML \<open>
  Outer_Syntax.command @{command_keyword update_uexpr_rep_eq_thms}
    "reread and update content of the uexpr_rep_eq_thms attribute"
    (Scan.succeed (Toplevel.theory uexpr_rep_eq.read_uexpr_rep_eq_thms));
\<close>

update_uexpr_rep_eq_thms \<comment> \<open> Read @{thm [source] uexpr_rep_eq_thms} here. \<close>
  
text \<open>
  Lastly, we require several named-theorem attributes to record the manual
  transfer laws and extra simplifications, so that the user can dynamically
  extend them in child theories.
\<close>

named_theorems uexpr_transfer_laws "uexpr transfer laws"

declare uexpr_eq_iff [uexpr_transfer_laws]
(*<*)(* declare uexpr_ref_iff [uexpr_transfer_laws] *)(*>*)

named_theorems uexpr_transfer_extra "extra simplifications for uexpr transfer"
  
declare unrest_uexpr.rep_eq [uexpr_transfer_extra]
  usedBy_uexpr.rep_eq [uexpr_transfer_extra]
  utp_expr.numeral_uexpr_rep_eq [uexpr_transfer_extra]
  utp_expr.less_eq_uexpr.rep_eq [uexpr_transfer_extra]
  Abs_uexpr_inverse [simplified, uexpr_transfer_extra]
  Rep_uexpr_inverse [uexpr_transfer_extra]
  
paragraph \<open> Tactic Definition \<close>

text \<open>
  We have all ingredients now to define the fast transfer tactic as a single
  simplification step.
\<close>

method fast_uexpr_transfer =
  (simp add: uexpr_transfer_laws uexpr_rep_eq_thms uexpr_transfer_extra)
  
subsection \<open> Interpretation \<close>

text \<open>
  The interpretation of record state spaces as products is done using the laws
  provided by the utility theory \emph{Interp}. Note that this step can be
  suppressed by using the \<open>no_interp\<close> option.
\<close>

method uexpr_interp_tac = (simp add: lens_interp_laws)?

subsection \<open> User Tactics \<close>

text \<open>
  In this section, we finally set-up the six user tactics: \<open>pred_simp\<close>,
  \<open>rel_simp\<close>, \<open>pred_auto\<close>, \<open>rel_auto\<close>, \<open>pred_blast\<close>
  and \<open>rel_blast\<close>. For this, we first define the proof strategies that
  are to be applied \emph{after} the transfer steps.
\<close>

method utp_simp_tac = (clarsimp)?
method utp_auto_tac = ((clarsimp)?; auto)
method utp_blast_tac = ((clarsimp)?; blast)

text \<open>
  The ML file below provides ML constructor functions for tactics that process
  arguments suitable and invoke the generic methods @{method gen_pred_tac} and
  @{method gen_rel_tac} with suitable arguments.
\<close>

ML_file "utp_tactics.ML"

text \<open>
  Finally, we execute the relevant outer commands for method setup. Sadly,
  this cannot be done at the level of Eisbach since the latter does not
  provide a convenient mechanism to process symbolic flags as arguments.
  It may be worth to put in a feature request with the developers of the
  Eisbach tool.
\<close>

method_setup pred_simp = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
  (fn args => fn ctxt =>
    let val prove_tac = Basic_Tactics.utp_simp_tac in
      (UTP_Tactics.inst_gen_pred_tac args prove_tac ctxt)
    end)
\<close>

method_setup rel_simp = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
    (fn args => fn ctxt =>
      let val prove_tac = Basic_Tactics.utp_simp_tac in
        (UTP_Tactics.inst_gen_rel_tac args prove_tac ctxt)
      end)
\<close>

method_setup pred_auto = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
    (fn args => fn ctxt =>
      let val prove_tac = Basic_Tactics.utp_auto_tac in
        (UTP_Tactics.inst_gen_pred_tac args prove_tac ctxt)
      end)
\<close>

method_setup rel_auto = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
    (fn args => fn ctxt =>
      let val prove_tac = Basic_Tactics.utp_auto_tac in
        (UTP_Tactics.inst_gen_rel_tac args prove_tac ctxt)
      end)
\<close>

method_setup pred_blast = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
    (fn args => fn ctxt =>
      let val prove_tac = Basic_Tactics.utp_blast_tac in
        (UTP_Tactics.inst_gen_pred_tac args prove_tac ctxt)
      end)
\<close>

method_setup rel_blast = \<open>
  (Scan.lift UTP_Tactics.scan_args) >>
    (fn args => fn ctxt =>
      let val prove_tac = Basic_Tactics.utp_blast_tac in
        (UTP_Tactics.inst_gen_rel_tac args prove_tac ctxt)
      end)
\<close>
  
text \<open> Simpler, one-shot versions of the above tactics, but without the possibility of dynamic arguments. \<close>
  
method rel_simp' 
  uses simp 
  = (simp add: upred_defs urel_defs lens_defs prod.case_eq_if relcomp_unfold uexpr_transfer_laws uexpr_transfer_extra uexpr_rep_eq_thms simp)

method rel_auto' 
  uses simp intro elim dest
  = (auto intro: intro elim: elim dest: dest simp add: upred_defs urel_defs lens_defs relcomp_unfold uexpr_transfer_laws uexpr_transfer_extra uexpr_rep_eq_thms simp)

method rel_blast' 
  uses simp intro elim dest
  = (rel_simp' simp: simp, blast intro: intro elim: elim dest: dest)
  
text_raw \<open> \newpage \<close>
end