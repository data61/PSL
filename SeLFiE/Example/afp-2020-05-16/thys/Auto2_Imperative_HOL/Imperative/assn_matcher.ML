(*
  File: assn_matcher.ML
  Author: Bohua Zhan

  Matching of assertions.
*)

(* Given arguments ctxt (pat, t) (id, inst), match pat with t. Assume
   pat is not a product. Produce t ==> pat(s) or t ==> pat(s) * t' for
   those in AssnMatchData. Produce pat(s) or pat(s) * t' ==> t for
   those in AssnInvMatchData.
 *)
type assn_matcher = Proof.context -> term * cterm -> id_inst -> id_inst_th list

signature ASSN_MATCHER =
sig
  val add_assn_matcher: assn_matcher -> theory -> theory
  val assn_match_term:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_match_all:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val assn_match_strict:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list
  val triv_assn_matcher: assn_matcher
  val emp_assn_matcher: assn_matcher
  val true_assn_matcher: assn_matcher
  val add_entail_matcher: thm -> theory -> theory

  val assn_match_single:
      Proof.context -> term * cterm -> id_inst -> id_inst_th list

  val add_assn_matcher_proofsteps: theory -> theory
end

(* Due to strange interaction between functors and Theory_Data, this
   must be put outside.
 *)
structure MatchData = Theory_Data (
  type T = assn_matcher list
  val empty = []
  val extend = I;
  val merge = merge (op pointer_eq)
)

functor AssnMatcher(SepUtil: SEP_UTIL): ASSN_MATCHER =
struct

open SepUtil

(* Matching in the forward direction *)

fun add_assn_matcher matcher = MatchData.map (cons matcher)

(* Assume pat is not in the form A * B. Match pat with one or more
   terms of t. Return theorem of form t ==> pat(s) * t'.
 *)
fun assn_match_term ctxt (pat, ct) (id, inst) =
    let
      val _ = assert (not (Term.is_Var pat))
                     "assn_match_term: pat should not be Var."
      val thy = Proof_Context.theory_of ctxt
      fun apply_matcher matcher = matcher ctxt (pat, ct) (id, inst)

      (* th must be an entailment, and the right side must be
             pat(s), pat(s) * t', or t' * pat(s).
       *)
      fun process_res ((id, inst'), th) =
          let
            val _ = assert (is_entail (prop_of' th)) "assn_match_term"
            val (_, rhs) = th |> prop_of' |> dest_entail
            val exp_rhs = Util.subst_term_norm inst' pat
          in
            if rhs aconv exp_rhs then
              ((id, inst'), th |> apply_to_entail_r mult_emp_right)
            else if UtilArith.is_times rhs andalso
                    dest_arg1 rhs aconv exp_rhs then
              ((id, inst'), th)
            else if UtilArith.is_times rhs andalso
                    dest_arg rhs aconv exp_rhs then
              ((id, inst'),
               th |> apply_to_entail_r (ACUtil.comm_cv assn_ac_info))
            else
              raise Fail "assn_match_term"
          end
    in
      (maps apply_matcher (MatchData.get thy))
          |> map process_res
    end

(* Match each term of pat with some term in t. Returns t ==> pat(s) * t'. *)
fun assn_match_all ctxt (pat, ct) (id, inst) =
    if UtilArith.is_times pat then
      let
        val (A, B) = Util.dest_binop_args pat
        val insts = assn_match_all ctxt (A, ct) (id, inst)

        (* th is t ==> A(s) * t'. Match B(s) with t', with result t'
           ==> B(s) * t''. Produce t ==> (A(s) * B(s)) * t''
         *)
        fun process_inst ((id', inst'), th) =
            let
              val ct' = th |> cprop_of' |> cdest_entail |> snd |> Thm.dest_arg
              val B' = Util.subst_term_norm inst' B
              val insts' = assn_match_all ctxt (B', ct') (id', inst')

              (* th' is t' ==> B(s) * t''. *)
              fun process_inst' ((id'', inst''), th') =
                  let
                    val res = ([th, th'] MRS entails_trans2_th)
                                  |> apply_to_entail_r (
                                ACUtil.assoc_sym_cv assn_ac_info)
                  in
                    ((id'', inst''), res)
                  end
            in
              map process_inst' insts'
            end
      in
        maps process_inst insts
      end
    else
      assn_match_term ctxt (pat, ct) (id, inst)

(* Guarantees that every term in t is matched. Returns t ==> pat(s). *)
fun assn_match_strict ctxt (pat, ct) (id, inst) =
    let
      val inst = assn_match_all ctxt (pat, ct) (id, inst)
      fun process_inst ((id', inst'), th) =
          let
            val rhs = th |> prop_of' |> dest_entail |> snd
            val _ = assert (UtilArith.is_times rhs andalso
                            dest_arg1 rhs aconv Util.subst_term_norm inst' pat)
                           "assn_match_strict"
          in
            if dest_arg rhs aconv emp then
              [((id', inst'), th |> apply_to_entail_r reduce_emp_right)]
            else []
          end
    in
      maps process_inst inst
    end

(* Specific assertion matchers *)

(* Matcher using the theorem A ==> A. *)
fun triv_assn_matcher ctxt (pat, ct) (id, inst) =
    if pat aconv emp then []  (* leave to emp_assn_matcher *)
    else let
      val cts = ACUtil.cdest_ac assn_ac_info ct

      fun match_i i =
          let
            val ct' = nth cts i
            val insts = Matcher.rewrite_match ctxt (pat, ct') (id, inst)

            (* eq_th is of form pat(inst') == t'. *)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val th = entail_triv_th ctxt (Thm.term_of ct)
                  val cv = Conv.every_conv [
                        ACUtil.move_outmost assn_ac_info (Thm.term_of ct'),
                        ACUtil.ac_last_conv
                            assn_ac_info (Conv.rewr_conv (meta_sym eq_th))]
                in
                  ((id', inst'), th |> apply_to_entail_r cv)
                end
          in
            map process_inst insts
          end
    in
      maps match_i (0 upto (length cts - 1))
    end

(* Consider the case where pat = emp. Return t ==> emp * t. *)
fun emp_assn_matcher ctxt (pat, ct) (id, inst) =
    if not (pat aconv emp) then []
    else [((id, inst), ct |> Thm.term_of |> entail_triv_th ctxt
                          |> apply_to_entail_r mult_emp_left)]

(* If pat = true, match all of t. Return t ==> emp * true. *)
fun true_assn_matcher ctxt (pat, ct) (id, inst) =
    if not (pat aconv assn_true) then []
    else [((id, inst), ct |> Thm.term_of |> entail_true_th ctxt
                          |> apply_to_entail_r mult_emp_left)]

(* We now consider the case of generating a matcher from an entailment
   theorem of a particular form.

   Given an entailment A ==> B, where B is of the form f ?xs pat_r,
   where f is a constant, and pat_r may contain additional schematic
   variables. Attempt to find a term of form f xs r within t, for the
   input term r, by matching the pattern A. For each match, return the
   implication t ==> f xs r or t ==> t' * f xs r. This function serves
   as the first step of entail_matcher.
 *)
fun entail_matcher' entail_th ctxt r ct id =
    let
      (* Match pat_r with r. *)
      val pat_r = entail_th |> prop_of' |> dest_entail |> snd |> dest_arg
      val inst_r = Matcher.rewrite_match ctxt (pat_r, Thm.cterm_of ctxt r) (id, fo_init)

      (* For each match, recursively match the instantiated version of
         A (named pat here) with t.
       *)
      fun process_inst_r ((id', inst'), eq_th) =
          let
            val entail_th' = Util.subst_thm ctxt inst' entail_th
            val pat = entail_th' |> prop_of' |> dest_arg1
            val matches = assn_match_all ctxt (pat, ct) (id', fo_init)

            (* th is of form t ==> pat(s) * t'. Convert to t ==> t' *
               pat(s). Then use entailment theorem to convert to t ==>
               t' * B. Finally, convert the argument in B to the given
               r.
             *)
            fun process_match ((id'', _), th) =
                let
                  val cv = eq_th |> Conv.rewr_conv |> Util.argn_conv 1
                                 |> ACUtil.ac_last_conv assn_ac_info
                  val th' = th |> apply_to_entail_r (ACUtil.comm_cv assn_ac_info)
                in
                  (id'', ([th', entail_th'] MRS entails_trans2_th)
                             |> apply_to_entail_r cv)
                end
          in
            map process_match matches
          end
    in
      maps process_inst_r inst_r
    end

(* Given entailment theorem A ==> B, with same condition as in
   entail_matcher', attempt to match pat with t, and return t ==> t' *
   pat(s). For any matching to be performed, pat must be in the form f
   pat_xs r, where pat_xs may contain schematic variables, but r
   cannot. First, find f xs r using entail_matcher', then match pat_xs
   with xs.
 *)
fun entail_matcher entail_th ctxt (pat, ct) (id, inst) =
    let
      val (f, args) = Term.strip_comb pat
      val pat_f = entail_th |> prop_of' |> dest_entail |> snd |> Term.head_of
    in
      if not (Term.aconv_untyped (f, pat_f)) orelse
         Util.has_vars (nth args 1) then []
      else let
        val (pat_xs, r) = the_pair args
        val matches = entail_matcher' entail_th ctxt r ct id

        fun process_res (id', th) =
            let
              val xs = th |> cprop_of' |> Thm.dest_arg
                          |> ACUtil.cdest_ac assn_ac_info
                          |> List.last |> Drule.strip_comb |> snd |> hd
              val insts = Matcher.rewrite_match ctxt (pat_xs, xs) (id', inst)

              fun process_inst ((id'', inst'), eq_th) =
                  let
                    val cv = eq_th |> meta_sym |> Conv.rewr_conv
                                   |> Conv.arg1_conv
                                   |> ACUtil.ac_last_conv assn_ac_info
                  in
                    ((id'', inst'), th |> apply_to_entail_r cv)
                  end
            in
              map process_inst insts
            end
      in
        maps process_res matches
      end
    end

fun add_entail_matcher th =
    let
      val (pat_f, pat_args) = th |> prop_of' |> dest_entail |> snd
                                 |> Term.strip_comb

      val _ = assert (length pat_args = 2 andalso Term.is_Const pat_f)
                     "add_entail_matcher: th must be in form A ==> f ?xs pat_r."
    in
      add_assn_matcher (entail_matcher th)
    end

(* Matching in the backward direction *)

(* Given a pattern pat, write t in the form pat(inst) * t'. *)
fun assn_match_single ctxt (pat, ct) (id, inst) =
    let
      val cts = ACUtil.cdest_ac assn_ac_info ct

      fun match_i i =
          let
            val ct' = nth cts i
            val t' = Thm.term_of ct'
            val insts = Matcher.rewrite_match ctxt (pat, ct') (id, inst)

            (* eq_th is of form pat(inst) == t'. *)
            fun process_inst ((id', inst'), eq_th) =
                let
                  val eq_th' =
                      if length cts = 1 then
                        eq_th |> meta_sym
                              |> apply_to_rhs mult_emp_right
                      else
                        Conv.every_conv [
                          ACUtil.move_outmost assn_ac_info t',
                          Conv.arg_conv (Conv.rewr_conv (meta_sym eq_th)),
                          ACUtil.comm_cv assn_ac_info] ct
                in
                  ((id', inst'), eq_th')
                end
          in
            map process_inst insts
          end
    in
      maps match_i (0 upto (length cts - 1))
    end

val add_assn_matcher_proofsteps =
    fold add_assn_matcher [
      triv_assn_matcher, emp_assn_matcher, true_assn_matcher
    ]

end  (* structure AssnMatcher. *)
