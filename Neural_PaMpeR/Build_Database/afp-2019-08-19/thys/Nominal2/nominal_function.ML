(*  Nominal Mutual Functions
    Author:  Christian Urban

    heavily based on the code of Alexander Krauss
    (code forked on 14 January 2011)

Main entry points to the nominal function package.
*)

signature NOMINAL_FUNCTION =
sig
  include NOMINAL_FUNCTION_DATA

  val add_nominal_function: (binding * typ option * mixfix) list ->
    Specification.multi_specs ->  Nominal_Function_Common.nominal_function_config ->
    (Proof.context -> tactic) -> local_theory -> nominal_info * local_theory

  val add_nominal_function_cmd: (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd ->  Nominal_Function_Common.nominal_function_config ->
    (Proof.context -> tactic) -> bool -> local_theory -> nominal_info * local_theory

  val nominal_function: (binding * typ option * mixfix) list ->
    Specification.multi_specs ->  Nominal_Function_Common.nominal_function_config ->
    local_theory -> Proof.state

  val nominal_function_cmd: (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd ->  Nominal_Function_Common.nominal_function_config ->
    bool -> local_theory -> Proof.state

  val get_info : Proof.context -> term -> nominal_info
end


structure Nominal_Function : NOMINAL_FUNCTION =
struct

open Function_Lib
open Function_Common
open Nominal_Function_Common


(* Check for all sorts of errors in the input - nominal needs a different checking function *)
fun nominal_check_defs ctxt fixes eqs =
  let
    val fnames = map (fst o fst) fixes

    fun check geq =
      let
        fun input_error msg = error (cat_lines [msg, Syntax.string_of_term ctxt geq])

        fun check_head fname =
          member (op =) fnames fname orelse
          input_error ("Illegal equation head. Expected " ^ commas_quote fnames)

        val (fname, qs, gs, args, rhs) = split_def ctxt check_head geq

        val _ = length args > 0 orelse input_error "Function has no arguments:"

        fun add_bvs t is = add_loose_bnos (t, 0, is)
        val rvs = (subtract (op =) (fold add_bvs args []) (add_bvs rhs []))
                    |> map (fst o nth (rev qs))

        val _ = forall (not o Term.exists_subterm
          (fn Free (n, _) => member (op =) fnames n | _ => false)) (gs @ args)
          orelse input_error "Defined function may not occur in premises or arguments"

        val freeargs = map (fn t => subst_bounds (rev (map Free qs), t)) args
        val funvars = filter (fn q =>
          exists (exists_subterm (fn (Free q') $ _ => q = q' | _ => false)) freeargs) qs
        val _ = null funvars orelse (warning (cat_lines
          ["Bound variable" ^ plural " " "s " funvars ^
          commas_quote (map fst funvars) ^ " occur" ^ plural "s" "" funvars ^
          " in function position.", "Misspelled constructor???"]); true)
      in
        (fname, length args)
      end

    val grouped_args = AList.group (op =) (map check eqs)
    val _ = grouped_args
      |> map (fn (fname, ars) =>
        length (distinct (op =) ars) = 1
        orelse error ("Function " ^ quote fname ^
          " has different numbers of arguments in different equations"))

    val not_defined = subtract (op =) (map fst grouped_args) fnames
    val _ = null not_defined
      orelse error ("No defining equations for function" ^
        plural " " "s " not_defined ^ commas_quote not_defined)

    fun check_sorts ((fname, fT), _) =
      Sorts.of_sort (Sign.classes_of (Proof_Context.theory_of ctxt)) (fT, @{sort "pt"})
      orelse error (cat_lines
      ["Type of " ^ quote fname ^ " is not of sort " ^ quote "pt" ^ ":",
       Syntax.string_of_typ (Config.put show_sorts true ctxt) fT])

    val _ = map check_sorts fixes
  in
    ()
  end



val psimp_attribs = map (Attrib.internal o K)
  [Named_Theorems.add @{named_theorems nitpick_psimp}]

fun mk_defname fixes = fixes |> map (fst o fst) |> space_implode "_"

fun add_simps fnames post sort extra_qualify label mod_binding moreatts
  simps lthy =
  let
    val spec = post simps
      |> map (apfst (apsnd (fn ats => moreatts @ ats)))
      |> map (apfst (apfst extra_qualify))

    val (saved_spec_simps, lthy) =
      fold_map Local_Theory.note spec lthy

    val saved_simps = maps snd saved_spec_simps
    val simps_by_f = sort saved_simps

    fun add_for_f fname simps =
      Local_Theory.note
        ((mod_binding (Binding.qualify true fname (Binding.name label)), []), simps)
      #> snd
  in
    (saved_simps, fold2 add_for_f fnames simps_by_f lthy)
  end

(* nominal *)
fun prepare_nominal_function do_print prep default_constraint fixspec eqns config lthy =
  let
    val constrn_fxs = map (fn (b, T, mx) => (b, SOME (the_default default_constraint T), mx))
    val ((fixes0, spec0), ctxt') = prep (constrn_fxs fixspec) eqns lthy
    val fixes = map (apfst (apfst Binding.name_of)) fixes0;
    val spec = map (fn (bnd, prop) => (bnd, [prop])) spec0;
    val (eqs, post, sort_cont, cnames) =
      empty_preproc nominal_check_defs (Function_Common.default_config) ctxt' fixes spec (* nominal *)

    val defname = mk_defname fixes
    val NominalFunctionConfig {partials, ...} = config

    val ((goal_state, cont), lthy') =
      Nominal_Function_Mutual.prepare_nominal_function_mutual config defname fixes eqs lthy

    fun afterqed [[proof]] lthy =
      let
        val NominalFunctionResult {fs, R, psimps, simple_pinducts,
          termination, domintros, cases, eqvts, ...} =
          cont lthy (Thm.close_derivation proof)

        val fnames = map (fst o fst) fixes
        fun qualify n = Binding.name n
          |> Binding.qualify true defname
        val concealed_partial = if partials then I else Binding.concealed

        val addsmps = add_simps fnames post sort_cont

        val (((psimps', pinducts'), (_, [termination'])), lthy) =
          lthy
          |> addsmps (concealed_partial o Binding.qualify false "partial")
               "psimps" concealed_partial psimp_attribs psimps
          ||>> Local_Theory.note ((concealed_partial (qualify "pinduct"),
                 [Attrib.internal (K (Rule_Cases.case_names cnames)),
                  Attrib.internal (K (Rule_Cases.consumes 1)),
                  Attrib.internal (K (Induct.induct_pred ""))]), simple_pinducts)
          ||>> Local_Theory.note ((Binding.concealed (qualify "termination"), []), [termination])
          ||> (snd o Local_Theory.note ((qualify "cases",
                 [Attrib.internal (K (Rule_Cases.case_names cnames))]), [cases]))
          ||> (case domintros of NONE => I | SOME thms =>
                   Local_Theory.note ((qualify "domintros", []), thms) #> snd)

        val info = { add_simps=addsmps, case_names=cnames, psimps=psimps',
          pinducts=snd pinducts', simps=NONE, inducts=NONE, termination=termination',
          fs=fs, R=R, defname=defname, is_partial=true, eqvts=eqvts}

        val _ = Proof_Display.print_consts do_print
          (Position.thread_data ()) lthy (K false) (map fst fixes)
      in
        (info,
         lthy |> Local_Theory.declaration {syntax = false, pervasive = false}
           (add_function_data o morph_function_data info))
      end
  in
    ((goal_state, afterqed), lthy')
  end

fun gen_add_nominal_function do_print prep default_constraint fixspec eqns config tac lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_nominal_function do_print prep default_constraint fixspec eqns config lthy
    val pattern_thm =
      case SINGLE (tac lthy') goal_state of
        NONE => error "pattern completeness and compatibility proof failed"
      | SOME st => Goal.finish lthy' st
  in
    lthy'
    |> afterqed [[pattern_thm]]
  end

val add_nominal_function =
  gen_add_nominal_function false Specification.check_multi_specs (Type_Infer.anyT @{sort type})
fun add_nominal_function_cmd a b c d int =
  gen_add_nominal_function int Specification.read_multi_specs "_::type" a b c d

fun gen_nominal_function do_print prep default_constraint fixspec eqns config lthy =
  let
    val ((goal_state, afterqed), lthy') =
      prepare_nominal_function do_print prep default_constraint fixspec eqns config lthy
  in
    lthy'
    |> Proof.theorem NONE (snd oo afterqed) [[(Logic.unprotect (Thm.concl_of goal_state), [])]]
    |> Proof.refine_singleton (Method.primitive_text (K (K goal_state)))
  end

val nominal_function =
  gen_nominal_function false Specification.check_multi_specs (Type_Infer.anyT @{sort type})
fun nominal_function_cmd a b c int =
  gen_nominal_function int Specification.read_multi_specs "_::type" a b c

fun get_info ctxt t = Item_Net.retrieve (get_function ctxt) t
  |> the_single |> snd


(* outer syntax *)

local
  val option_parser = Parse.group (fn () => "option")
    ((Parse.reserved "sequential" >> K Sequential)
     || ((Parse.reserved "default" |-- Parse.term) >> Default)
     || (Parse.reserved "domintros" >> K DomIntros)
     || (Parse.reserved "no_partials" >> K No_Partials)
     || ((Parse.reserved "invariant" |-- Parse.term) >> Invariant))

  fun config_parser default =
    (Scan.optional (@{keyword "("} |-- Parse.!!! (Parse.list1 option_parser) --| @{keyword ")"}) [])
     >> (fn opts => fold apply_opt opts default)
in
  fun nominal_function_parser default_cfg =
      config_parser default_cfg -- Parse_Spec.specification
end

val _ =
  Outer_Syntax.local_theory_to_proof' @{command_keyword nominal_function}
    "define general recursive nominal functions"
       (nominal_function_parser nominal_default_config
          >> (fn (config, (fixes, specs)) => nominal_function_cmd fixes specs config))

end
