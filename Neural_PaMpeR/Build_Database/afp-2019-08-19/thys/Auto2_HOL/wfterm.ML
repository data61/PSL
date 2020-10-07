(*
  File: wfterm.ML
  Author: Bohua Zhan

  Definition and basic functions on Wellformed terms.
*)

(* A wellformed term is a cterm combined with wellform data (usually
   only for a particular function head.
 *)
datatype wfterm
  = WfTerm of cterm
  | WfComb of cterm * wfterm list * thm list

infix 1 then_wfconv
infix 0 else_wfconv

(* Conversion between wellformed terms. Produce a new wellformed term,
   together with an equality between corresponding terms.
 *)
type wfconv = wfterm -> wfterm * thm

signature WFTERM =
sig
  (* Conversion between term and wfterm. *)
  val cterm_of: wfterm -> cterm
  val term_of: wfterm -> term
  val theory_of_wft: wfterm -> theory
  val wellform_ths_of: wfterm -> thm list
  val find_target_on_ths: thm list -> term -> thm
  val cterm_to_wfterm_on_ths: thm list -> term list -> cterm -> wfterm
  val cterm_to_wfterm_assume: term list -> cterm -> wfterm

  (* Wellformed version of conv. *)
  val strip_comb: wfterm -> cterm * wfterm list
  val all_conv: wfconv
  val no_conv: wfconv
  val argn_conv: int -> wfconv -> wfconv
  val arg_conv: wfconv -> wfconv
  val arg1_conv: wfconv -> wfconv
  val rewr_obj_eq: term list -> thm -> wfconv
  val then_wfconv: wfconv * wfconv -> wfconv
  val else_wfconv: wfconv * wfconv -> wfconv
  val try_conv: wfconv -> wfconv
  val repeat_conv: wfconv -> wfconv
  val first_conv: wfconv list -> wfconv
  val every_conv: wfconv list -> wfconv
  val binop_conv: wfconv -> wfconv
  val conv_of: conv -> wfconv

  (* Some debugging facilities. *)
  val string_of_wfterm: Proof.context -> wfterm -> string
  val test_wfconv: Proof.context -> term list -> wfconv -> string -> string * string -> unit

  (* Rewriting a wellformed expression. *)
  val rewrite_on_eqs: term list -> (wfterm * thm) list -> wfconv
end;

structure WfTerm : WFTERM =
struct

(* Extract a regular cterm from a wellformed term. *)
fun cterm_of wft =
    case wft of
        WfTerm ct => ct
      | WfComb (cf, args, _) => Drule.list_comb (cf, map cterm_of args)

fun term_of wft =
    Thm.term_of (cterm_of wft)

fun theory_of_wft wft =
    Thm.theory_of_cterm (cterm_of wft)

fun wellform_ths_of wft =
    case wft of
        WfTerm _ => []
      | WfComb (_, args, ths) => ths @ (maps wellform_ths_of args)

fun find_target_on_ths ths prop =
    let
      fun get_on_th th = if prop_of' th aconv prop then SOME th else NONE
    in
      the (get_first get_on_th ths)
      handle Option.Option =>
             raise Fail "find_target_on_ths: not found"
    end

(* Obtain a wellformed term from a cterm and a list of
   theorems. Traverse only through combinations whose function head
   agrees with one of fheads. Throws an exception if any wellform data
   is not found.
 *)
fun cterm_to_wfterm_on_ths assum_ths fheads ct =
    case Thm.term_of ct of
        _ $ _ =>
        let
          val thy = Thm.theory_of_cterm ct
          val t = Thm.term_of ct
          val (cf, cargs) = Drule.strip_comb ct
        in
          if forall (fn fhead => not (Util.is_head fhead t)) fheads then
            WfTerm ct
          else let
            val ths =
                map (find_target_on_ths assum_ths)
                    (WellForm.lookup_wellform_data thy t)
                handle Fail "find_target_on_ths: not found" =>
                       raise Fail "cterm_to_wfterm_on_ths"
            val wfargs = map (cterm_to_wfterm_on_ths assum_ths fheads) cargs
          in
            WfComb (cf, wfargs, ths)
          end
        end
      | _ => WfTerm ct

fun cterm_to_wfterm_assume fheads ct =
    case Thm.term_of ct of
        _ $ _ =>
        let
          val thy = Thm.theory_of_cterm ct
          val t = Thm.term_of ct
          val (cf, cargs) = Drule.strip_comb ct
        in
          if forall (fn fhead => not (Util.is_head fhead t)) fheads then
            WfTerm ct
          else let
            val ths = map (Thm.assume o Thm.global_cterm_of thy o mk_Trueprop)
                          (WellForm.lookup_wellform_data thy t)
            val wfargs = map (cterm_to_wfterm_assume fheads) cargs
          in
            WfComb (cf, wfargs, ths)
          end
        end
      | _ => WfTerm ct

fun strip_comb wft =
    case wft of
        WfTerm ct => (ct, [])
      | WfComb (cf, args, _) => (cf, args)

fun all_conv wft =
    (wft, Thm.reflexive (cterm_of wft))

fun no_conv _ =
    raise Fail "WfTerm.no_conv"

(* Apply wfcv to the nth argument of wft (counting from the
   left). Remember to update the wellform data at head.
 *)
fun argn_conv n wfcv wft =
    case wft of
        WfTerm _ => raise Fail "argn_conv: applied to atom."
      | WfComb (cf, args, ths) =>
        let
          val _ = assert (n < length args) "argn_conv: n out of bounds."
          val thy = Thm.theory_of_cterm cf
          val (wft', eq_th) = wfcv (nth args n)

          (* New list of arguments, and equalities between the two lists. *)
          val args' = take n args @ [wft'] @ drop (n + 1) args
          val eq_ths' = map (Thm.reflexive o cterm_of) (take n args) @
                        [eq_th] @
                        map (Thm.reflexive o cterm_of) (drop (n + 1) args)

          fun convert_th th =
              let
                (* Obtain pattern from theory. *)
                val (pat, data_pat) =
                    the (WellForm.lookup_wellform_pattern
                             thy (term_of wft, prop_of' th))
                    handle Option.Option =>
                           raise Fail "convert_th: invalid input."

                val pat_args = Util.dest_args pat
              in
                apply_to_thm' (
                  Util.pattern_rewr_conv data_pat (pat_args ~~ eq_ths')) th
              end
        in
          (WfComb (cf, args', map convert_th ths), Util.comb_equiv (cf, eq_ths'))
        end

fun arg_conv wfcv wft =
    let
      val (_, args) = Term.strip_comb (term_of wft)
    in
      argn_conv (length args - 1) wfcv wft
    end

fun arg1_conv wfcv wft =
    let
      val (_, args) = Term.strip_comb (term_of wft)
    in
      argn_conv (length args - 2) wfcv wft
    end

(* Apply the given theorem as a rewrite rule. th is assumed to be in
   the form P_1 ==> ... ==> P_m ==> l = r & Q_1 & ... & Q_n, where P_1
   through P_m provide wellform data for l, and Q_1 through Q_n
   provide additional wellform data for r.
 *)
fun rewr_obj_eq fheads th wft =
    let
      val thy = theory_of_wft wft
      val t = term_of wft
      val wf_ths = wellform_ths_of wft

      (* First need to instantiate th by matching l with the term of wft. *)
      val pat_l = th |> concl_of' |> strip_conj |> hd |> dest_eq |> fst
      val inst = Pattern.first_order_match thy (pat_l, t) fo_init
      val th' = Util.subst_thm_thy thy inst th

      (* Second, find theorems justifying premises of th'. *)
      val prems = map dest_Trueprop (Thm.prems_of th')
      val prems_th = map (find_target_on_ths wf_ths) prems
                     handle Fail "find_target_on_ths: not found" =>
                            raise Fail "WfTerm.rewr_obj_eq"
      val th'' = prems_th MRS th'

      (* Finally, apply rewrite rule and fill in wellform data on rhs. *)
      val th_splits = UtilLogic.split_conj_th th''
      val (eq_th, wf_ths') = (hd th_splits, tl th_splits)
      val c_rhs = eq_th |> Thm.cprop_of |> Thm.dest_arg |> Thm.dest_arg
      val wf_rhs = cterm_to_wfterm_on_ths (wf_ths @ wf_ths') fheads c_rhs
    in
      (wf_rhs, to_meta_eq eq_th)
    end
    handle Pattern.MATCH => raise Fail "WfTerm.rewr_obj_eq failed"

fun (wfcv1 then_wfconv wfcv2) wft =
    let
      val (wft', eq_th1) = wfcv1 wft
      val (wft'', eq_th2) = wfcv2 wft'
    in
      (wft'', Util.transitive_list [eq_th1, eq_th2])
    end

fun (wfcv1 else_wfconv wfcv2) wft =
    (wfcv1 wft
     handle THM _ => wfcv2 wft
          | CTERM _ => wfcv2 wft
          | TERM _ => wfcv2 wft
          | TYPE _ => wfcv2 wft
          | Fail _ => wfcv2 wft)

fun try_conv wfcv = wfcv else_wfconv all_conv
fun repeat_conv wfcv wft = try_conv (wfcv then_wfconv repeat_conv wfcv) wft
fun first_conv wfcvs = fold_rev (curry op else_wfconv) wfcvs no_conv
fun every_conv wfcvs = fold_rev (curry op then_wfconv) wfcvs all_conv
fun binop_conv wfcv = arg1_conv wfcv then_wfconv arg_conv wfcv

(* Transforming a regular conversion to a well-formed conversion. This
   should be used only when the output of the conversion is guaranteed
   to not have further wellform structure.
 *)
fun conv_of cv wft =
    let
      val ct = cterm_of wft
      val eq_th = cv ct
    in
      (WfTerm (Thm.rhs_of eq_th), eq_th)
    end

fun string_of_wfterm ctxt wft =
    case wft of
        WfTerm ct => "@(" ^ Syntax.string_of_term ctxt (Thm.term_of ct) ^ ")"
      | WfComb (ct, wfts, _) =>
        Syntax.string_of_term ctxt (Thm.term_of ct) ^ " $ " ^
        (space_implode " $ " (map (string_of_wfterm ctxt) wfts))

(* Apply wfcv on the term given by str_t, and compare the result to
   the term given by str_res.
 *)
fun test_wfconv ctxt fheads wfcv err_str (str1, str2) =
    let
      val (t1, t2) = (Syntax.read_term ctxt str1, Syntax.read_term ctxt str2)
      val wft = cterm_to_wfterm_assume fheads (Thm.cterm_of ctxt t1)
      val th = snd (wfcv wft)
               handle Fail err =>
                      let val _ = trace_t ctxt "Input:" t1 in
                        raise Fail (err ^ " -- " ^ err_str)
                      end
    in
      if t1 aconv (Util.lhs_of th) andalso t2 aconv (Util.rhs_of th) then ()
      else let
        val _ = trace_t ctxt "Input:" t1
        val _ = trace_t ctxt "Expected:" t2
        val _ = trace_t ctxt "Actual:" (Thm.prop_of th)
      in
        raise Fail err_str
      end
    end

(* Given a well-formed term wft, and a list of equations to
   well-formed terms, rewrite all subterms of wft that are equal to
   the left side of one of the equations. Assume that all fheads are
   binary functions.
 *)
fun rewrite_on_eqs fheads wf_eqs wft =
    let
      val t = term_of wft
    in
      if member (op aconv) fheads (Term.head_of t) then
        binop_conv (rewrite_on_eqs fheads wf_eqs) wft
      else
        case find_first (fn (_, eq) => t aconv (Util.lhs_of eq)) wf_eqs of
            NONE => all_conv wft
          | SOME (wft, eq_th) => (wft, eq_th)
    end

end  (* structure WfTerm *)

fun (wfcv1 then_wfconv wfcv2) = WfTerm.then_wfconv (wfcv1, wfcv2)
fun (wfcv1 else_wfconv wfcv2) = WfTerm.else_wfconv (wfcv1, wfcv2)
