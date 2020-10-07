(*  Title:      nominal_permeq.ML
    Author:     Christian Urban
    Author:     Brian Huffman
*)

infix 4 addpres addposts addexcls

signature NOMINAL_PERMEQ =
sig
  datatype eqvt_config =
    Eqvt_Config of {strict_mode: bool, pre_thms: thm list, post_thms: thm list, excluded: string list}

  val eqvt_relaxed_config: eqvt_config
  val eqvt_strict_config: eqvt_config
  val addpres : (eqvt_config * thm list) -> eqvt_config
  val addposts : (eqvt_config * thm list) -> eqvt_config
  val addexcls : (eqvt_config * string list) -> eqvt_config
  val delpres : eqvt_config -> eqvt_config
  val delposts : eqvt_config -> eqvt_config

  val eqvt_conv: Proof.context -> eqvt_config -> conv
  val eqvt_rule: Proof.context -> eqvt_config -> thm -> thm
  val eqvt_tac: Proof.context -> eqvt_config -> int -> tactic

  val perm_simp_meth: thm list * string list -> Proof.context -> Proof.method
  val perm_strict_simp_meth: thm list * string list -> Proof.context -> Proof.method
  val args_parser: (thm list * string list) context_parser

  val trace_eqvt: bool Config.T
end;

(*

- eqvt_tac and eqvt_rule take a  list of theorems which
  are first tried to simplify permutations

- the string list contains constants that should not be
  analysed (for example there is no raw eqvt-lemma for
  the constant The); therefore it should not be analysed

- setting [[trace_eqvt = true]] switches on tracing
  information

*)

structure Nominal_Permeq: NOMINAL_PERMEQ =
struct

open Nominal_ThmDecls;

datatype eqvt_config = Eqvt_Config of
  {strict_mode: bool, pre_thms: thm list, post_thms: thm list, excluded: string list}

fun (Eqvt_Config {strict_mode, pre_thms, post_thms, excluded}) addpres thms =
  Eqvt_Config { strict_mode = strict_mode,
                pre_thms = thms @ pre_thms,
                post_thms = post_thms,
                excluded = excluded }

fun (Eqvt_Config {strict_mode, pre_thms, post_thms, excluded}) addposts thms =
  Eqvt_Config { strict_mode = strict_mode,
                pre_thms = pre_thms,
                post_thms = thms @ post_thms,
                excluded = excluded }

fun (Eqvt_Config {strict_mode, pre_thms, post_thms, excluded}) addexcls excls =
  Eqvt_Config { strict_mode = strict_mode,
                pre_thms = pre_thms,
                post_thms = post_thms,
                excluded = excls @ excluded }

fun delpres (Eqvt_Config {strict_mode, pre_thms, post_thms, excluded}) =
  Eqvt_Config { strict_mode = strict_mode,
                pre_thms = [],
                post_thms = post_thms,
                excluded = excluded }

fun delposts (Eqvt_Config {strict_mode, pre_thms, post_thms, excluded}) =
  Eqvt_Config { strict_mode = strict_mode,
                pre_thms = pre_thms,
                post_thms = [],
                excluded = excluded }

val eqvt_relaxed_config =
  Eqvt_Config { strict_mode = false,
                pre_thms = @{thms eqvt_bound},
                post_thms = @{thms permute_pure},
                excluded = [] }

val eqvt_strict_config =
  Eqvt_Config { strict_mode = true,
                pre_thms = @{thms eqvt_bound},
                post_thms = @{thms permute_pure},
                excluded = [] }


(* tracing infrastructure *)
val trace_eqvt = Attrib.setup_config_bool @{binding "trace_eqvt"} (K false);

fun trace_enabled ctxt = Config.get ctxt trace_eqvt

fun trace_msg ctxt result =
  let
    val lhs_str = Syntax.string_of_term ctxt (Thm.term_of (Thm.lhs_of result))
    val rhs_str = Syntax.string_of_term ctxt (Thm.term_of (Thm.rhs_of result))
  in
    warning (Pretty.string_of (Pretty.strs ["Rewriting", lhs_str, "to", rhs_str]))
  end

fun trace_conv ctxt conv ctrm =
  let
    val result = conv ctrm
  in
    if Thm.is_reflexive result
    then result
    else (trace_msg ctxt result; result)
  end

(* this conversion always fails, but prints
   out the analysed term  *)
fun trace_info_conv ctxt ctrm =
  let
    val trm = Thm.term_of ctrm
    val _ = case (head_of trm) of
        @{const "Trueprop"} => ()
      | _ => warning ("Analysing term " ^ Syntax.string_of_term ctxt trm)
  in
    Conv.no_conv ctrm
  end

(* conversion for applications *)
fun eqvt_apply_conv ctrm =
  case Thm.term_of ctrm of
    Const (@{const_name "permute"}, _) $ _ $ (_ $ _) =>
      let
        val (perm, t) = Thm.dest_comb ctrm
        val (_, p) = Thm.dest_comb perm
        val (f, x) = Thm.dest_comb t
        val a = Thm.ctyp_of_cterm x;
        val b = Thm.ctyp_of_cterm t;
        val ty_insts = map SOME [b, a]
        val term_insts = map SOME [p, f, x]
      in
        Thm.instantiate' ty_insts term_insts @{thm eqvt_apply}
      end
  | _ => Conv.no_conv ctrm

(* conversion for lambdas *)
fun eqvt_lambda_conv ctrm =
  case Thm.term_of ctrm of
    Const (@{const_name "permute"}, _) $ _ $ (Abs _) =>
      Conv.rewr_conv @{thm eqvt_lambda} ctrm
  | _ => Conv.no_conv ctrm


(* conversion that raises an error or prints a warning message,
   if a permutation on a constant or application cannot be analysed *)

fun is_excluded excluded (Const (a, _)) = member (op=) excluded a
  | is_excluded _ _ = false

fun progress_info_conv ctxt strict_flag excluded ctrm =
  let
    fun msg trm =
      if is_excluded excluded trm then () else
        (if strict_flag then error else warning)
          ("Cannot solve equivariance for " ^ (Syntax.string_of_term ctxt trm))

    val _ =
      case Thm.term_of ctrm of
        Const (@{const_name "permute"}, _) $ _ $ (trm as Const _) => msg trm
      | Const (@{const_name "permute"}, _) $ _ $ (trm as _ $ _) => msg trm
      | _ => ()
  in
    Conv.all_conv ctrm
  end

(* main conversion *)
fun main_eqvt_conv ctxt config ctrm =
  let
    val Eqvt_Config {strict_mode, pre_thms, post_thms, excluded} = config

    val first_conv_wrapper =
      if trace_enabled ctxt
      then Conv.first_conv o (cons (trace_info_conv ctxt)) o (map (trace_conv ctxt))
      else Conv.first_conv

    val all_pre_thms = map safe_mk_equiv (pre_thms @ get_eqvts_raw_thms ctxt)
    val all_post_thms = map safe_mk_equiv post_thms
  in
    first_conv_wrapper
      [ Conv.rewrs_conv all_pre_thms,
        eqvt_apply_conv,
        eqvt_lambda_conv,
        Conv.rewrs_conv all_post_thms,
        progress_info_conv ctxt strict_mode excluded
      ] ctrm
  end


(* the eqvt-conversion first eta-normalises goals in
   order to avoid problems with inductions in the
   equivariance command. *)
fun eqvt_conv ctxt config =
  Conv.top_conv (fn ctxt => Thm.eta_conversion then_conv (main_eqvt_conv ctxt config)) ctxt

(* thms rewriter *)
fun eqvt_rule ctxt config =
  Conv.fconv_rule (eqvt_conv ctxt config)

(* tactic *)
fun eqvt_tac ctxt config =
  CONVERSION (eqvt_conv ctxt config)


(** methods **)
fun unless_more_args scan = Scan.unless (Scan.lift ((Args.$$$ "exclude") -- Args.colon)) scan

val add_thms_parser = Scan.optional (Scan.lift (Args.add -- Args.colon) |--
   Scan.repeat (unless_more_args Attrib.multi_thm) >> flat) [];

val exclude_consts_parser = Scan.optional (Scan.lift ((Args.$$$ "exclude") -- Args.colon) |--
  (Scan.repeat (Args.const {proper = true, strict = true}))) []

val args_parser = add_thms_parser -- exclude_consts_parser

fun perm_simp_meth (thms, consts) ctxt =
  SIMPLE_METHOD (HEADGOAL (eqvt_tac ctxt (eqvt_relaxed_config addpres thms addexcls consts)))

fun perm_strict_simp_meth (thms, consts) ctxt =
  SIMPLE_METHOD (HEADGOAL (eqvt_tac ctxt (eqvt_strict_config addpres thms addexcls consts)))

end; (* structure *)
