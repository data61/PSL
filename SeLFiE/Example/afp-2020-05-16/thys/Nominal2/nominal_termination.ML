(*  Nominal Termination
    Author: Christian Urban

    heavily based on the code of Alexander Krauss
    (code forked on 18 July 2011)

Redefinition of the termination command
*)

signature NOMINAL_FUNCTION_TERMINATION =
sig
  include NOMINAL_FUNCTION_DATA

  val termination : bool -> term option -> local_theory -> Proof.state
  val termination_cmd : bool -> string option -> local_theory -> Proof.state

end

structure Nominal_Function_Termination : NOMINAL_FUNCTION_TERMINATION =
struct

open Function_Lib
open Function_Common
open Nominal_Function_Common

val simp_attribs = map (Attrib.internal o K)
  [Simplifier.simp_add,
   Named_Theorems.add @{named_theorems nitpick_simp}]

val eqvt_attrib =  Attrib.internal (K Nominal_ThmDecls.eqvt_add)

fun prepare_termination_proof prep_term is_eqvt raw_term_opt lthy =
  let
    val term_opt = Option.map (prep_term lthy) raw_term_opt
    val info = the (case term_opt of
                      SOME t => (import_function_data t lthy
                        handle Option.Option =>
                          error ("Not a function: " ^ quote (Syntax.string_of_term lthy t)))
                    | NONE => (import_last_function lthy handle Option.Option => error "Not a function"))

      val { termination, fs, R, add_simps, case_names, psimps,
        pinducts, defname, eqvts, ...} = info
      val domT = domain_type (fastype_of R)

      val goal = HOLogic.mk_Trueprop
                   (HOLogic.mk_all ("x", domT, mk_acc domT R $ Free ("x", domT)))
      fun afterqed [[totality]] lthy =
        let
          val totality = Thm.close_derivation \<^here> totality
          val remove_domain_condition =
            full_simplify (put_simpset HOL_basic_ss lthy
              addsimps [totality, @{thm True_implies_equals}])
          val tsimps = map remove_domain_condition psimps
          val tinducts = map remove_domain_condition pinducts
          val teqvts = map remove_domain_condition eqvts

          fun qualify n = Binding.name n
            |> Binding.qualify true defname
        in
          lthy
          |> add_simps I "simps" I simp_attribs tsimps
          ||>> Local_Theory.note ((qualify "eqvt", if is_eqvt then [eqvt_attrib] else []), teqvts)
          ||>> Local_Theory.note
             ((qualify "induct",
               [Attrib.internal (K (Rule_Cases.case_names case_names))]),
              tinducts)
          |-> (fn ((simps, (_, eqvts)), (_, inducts)) => fn lthy =>
            let val info' = { is_partial=false, defname=defname, add_simps=add_simps,
              case_names=case_names, fs=fs, R=R, psimps=psimps, pinducts=pinducts,
              simps=SOME simps, inducts=SOME inducts, termination=termination, eqvts=teqvts }
            in
              lthy
              |> Local_Theory.declaration {syntax = false, pervasive = false}
                   (add_function_data o morph_function_data info')
              |> Spec_Rules.add Binding.empty Spec_Rules.equational_recdef fs tsimps
              |> Code.declare_default_eqns (map (rpair true) tsimps)
              |> pair info'
            end)
        end
  in
    (goal, afterqed, termination)
  end

fun gen_termination prep_term is_eqvt raw_term_opt lthy =
  let
    val (goal, afterqed, termination) = prepare_termination_proof prep_term is_eqvt raw_term_opt lthy
  in
    lthy
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.rule_del]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.empty, [Context_Rules.intro_bang (SOME 1)]), [([allI], [])])] |> snd
    |> Proof_Context.note_thmss ""
       [((Binding.name "termination", [Context_Rules.intro_bang (SOME 0)]),
         [([Goal.norm_result lthy termination], [])])] |> snd
    |> Proof.theorem NONE (snd oo afterqed) [[(goal, [])]]
  end

val termination = gen_termination Syntax.check_term
val termination_cmd = gen_termination Syntax.read_term

(* outer syntax *)

val option_parser =
  (Scan.optional (@{keyword "("} |-- Parse.!!!
    ((Parse.reserved "eqvt" >> K true) ||
     (Parse.reserved "no_eqvt" >> K false)) --| @{keyword ")"}) (false))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_keyword nominal_termination}
    "prove termination of a recursive nominal function"
      (option_parser -- Scan.option Parse.term >>
        (fn (is_eqvt, opt_trm) => termination_cmd is_eqvt opt_trm))

end
