(*
  File: proofsteps.ML
  Author: Bohua Zhan

  Definition of type proofstep, and facility for adding basic proof steps.
*)

datatype proofstep_fn
  = OneStep of Proof.context -> box_item -> raw_update list
  | TwoStep of Proof.context -> box_item -> box_item -> raw_update list

type proofstep = {
  name: string,
  args: match_arg list,
  func: proofstep_fn
}

datatype prfstep_descriptor = WithFact of term
                            | WithItem of string * term
                            | WithProperty of term
                            | WithWellForm of term * term
                            | WithScore of int
                            | GetFact of term * thm
                            | ShadowFirst | ShadowSecond
                            | CreateCase of term | CreateConcl of term
                            | Filter of prfstep_filter

signature PROOFSTEP =
sig
  val eq_prfstep: proofstep * proofstep -> bool
  val apply_prfstep: Proof.context -> box_item list -> proofstep -> raw_update list
  val WithGoal: term -> prfstep_descriptor
  val WithTerm: term -> prfstep_descriptor
  val WithProp: term -> prfstep_descriptor
  val string_of_desc: theory -> prfstep_descriptor -> string
  val string_of_descs: theory -> prfstep_descriptor list -> string

  (* prfstep_filter *)
  val all_insts: prfstep_filter
  val neq_filter: term -> prfstep_filter
  val order_filter: string -> string -> prfstep_filter
  val size1_filter: string -> prfstep_filter
  val not_type_filter: string -> typ -> prfstep_filter

  (* First level proofstep writing functions. *)
  val apply_pat_r: Proof.context -> id_inst_ths -> term * thm -> thm
  val retrieve_args: prfstep_descriptor list -> match_arg list
  val retrieve_pats_r: prfstep_descriptor list -> (term * thm) list
  val retrieve_filts: prfstep_descriptor list -> prfstep_filter
  val retrieve_cases: prfstep_descriptor list -> term list
  val retrieve_shadows: prfstep_descriptor list -> int list
  val get_side_ths:
      Proof.context -> id_inst -> match_arg list -> (box_id * thm list) list
  val prfstep_custom:
      string -> prfstep_descriptor list ->
      (id_inst_ths -> box_item list -> Proof.context -> raw_update list) -> proofstep
  val gen_prfstep: string -> prfstep_descriptor list -> proofstep
  val prfstep_pre_conv: string -> prfstep_descriptor list ->
                        (Proof.context -> conv) -> proofstep
  val prfstep_conv: string -> prfstep_descriptor list -> conv -> proofstep
end;

structure ProofStep : PROOFSTEP =
struct

fun eq_prfstep (prfstep1, prfstep2) = (#name prfstep1 = #name prfstep2)

fun apply_prfstep ctxt items {func, ...} =
    case func of
        OneStep f => f ctxt (the_single items)
      | TwoStep f => f ctxt (hd items) (nth items 1)

fun WithGoal t =
    let
      val _ = assert (type_of t = boolT) "WithGoal: pat should have type bool."
    in
      WithFact (get_neg t)
    end

fun WithTerm t = WithItem (TY_TERM, t)

fun WithProp t =
    let
      val _ = assert (type_of t = boolT) "WithProp: pat should have type bool."
    in
      WithItem (TY_PROP, t)
    end

fun string_of_desc thy desc =
    let
      val print = Syntax.string_of_term_global thy
    in
      case desc of
          WithFact t =>
          if is_neg t then "WithGoal " ^ (print (get_neg t))
          else "WithFact " ^ (print t)
        | WithItem (ty_str, t) =>
          if ty_str = TY_TERM then "WithTerm " ^ (print t)
          else "WithItem " ^ ty_str ^ " " ^ (print t)
        | WithProperty t => "WithProperty " ^ (print t)
        | WithWellForm (_, req) => "WithWellForm " ^ (print req)
        | WithScore n => "WithScore " ^ (string_of_int n)
        | GetFact (t, th) =>
          if t aconv @{term False} then
            "GetResolve " ^ (Util.name_of_thm th)
          else if is_neg t then
            "GetGoal (" ^ (print (get_neg t)) ^ ", " ^ (Util.name_of_thm th) ^ ")"
          else
            "GetFact (" ^ (print t) ^ ", " ^ (Util.name_of_thm th) ^ ")"
        | ShadowFirst => "Shadow first" | ShadowSecond => "Shadow second"
        | CreateCase assum => "CreateCase " ^ (print assum)
        | CreateConcl concl => "CreateConcl " ^ (print concl)
        | Filter _ => "Filter (...)"
    end

fun string_of_descs thy descs =
    let
      fun is_filter desc = case desc of Filter _ => true | _ => false
      val (filts, non_filts) = filter_split is_filter descs
    in
      (cat_lines (map (string_of_desc thy) non_filts)) ^
      (if length filts > 0 then
         (" + " ^ (string_of_int (length filts)) ^ " filters") else "")
    end

(* prfstep_filter *)

val all_insts = fn _ => fn _ => true

fun neq_filter cond ctxt (id, inst) =
    let
      val (lhs, rhs) =
          cond |> dest_not |> dest_eq
          handle Fail "dest_not" => raise Fail "neq_filter: not an inequality."
               | Fail "dest_eq" => raise Fail "neq_filter: not an inequality."
      val _ = assert (null (Term.add_frees cond []))
                     "neq_filter: should not contain free variable."

      val t1 = Util.subst_term_norm inst lhs
      val t2 = Util.subst_term_norm inst rhs
    in
      if Util.has_vars t1 andalso Util.has_vars t2 then true
      else if Util.has_vars t1 then
        (Matcher.rewrite_match ctxt (t1, Thm.cterm_of ctxt t2) (id, fo_init))
            |> filter (fn ((id', _), _) => id = id') |> null
      else if Util.has_vars t2 then
        (Matcher.rewrite_match ctxt (t2, Thm.cterm_of ctxt t1) (id, fo_init))
            |> filter (fn ((id', _), _) => id = id') |> null
      else
        not (RewriteTable.is_equiv_t id ctxt (t1, t2))
    end

fun order_filter s1 s2 _ (_, inst) =
    not (Term_Ord.term_ord (lookup_inst inst s2, lookup_inst inst s1) = LESS)

fun size1_filter s1 ctxt (id, inst) =
    size_of_term (RewriteTable.simp_val_t id ctxt (lookup_inst inst s1)) = 1

fun not_type_filter s ty _ (_, inst) =
    not (Term.fastype_of (lookup_inst inst s) = ty)

(* First level proofstep writing functions. *)
fun apply_pat_r ctxt ((_, inst), ths) (pat_r, th) =
    let
      val _ = assert (fastype_of pat_r = boolT)
                     "apply_pat_r: pat_r should be of type bool"

      (* Split into meta equalities (usually produced by term
         matching, not applied to th, and others (assumptions for th).
       *)
      val (eqs, ths') = ths |> filter_split (Util.is_meta_eq o Thm.prop_of)
      val _ = assert (length ths' = Thm.nprems_of th)
                     "apply_pat_r: wrong number of assumptions."

      val inst_new = Util.subst_term_norm inst (mk_Trueprop pat_r)
      val th' = th |> Util.subst_thm ctxt inst |> fold Thm.elim_implies ths'
      val _ = if inst_new aconv (Thm.prop_of th') then () else
              raise Fail "apply_pat_r: conclusion mismatch"

      (* Rewrite on subterms, top sweep order. *)
      fun rewr_top eq_th =
          Conv.top_sweep_conv (K (Conv.rewr_conv eq_th)) ctxt
    in
      th' |> apply_to_thm (Conv.every_conv (map rewr_top eqs))
    end

fun retrieve_args descs =
    maps (fn desc => case desc of
                         WithFact t => [PropMatch t]
                       | WithItem (ty_str, t) => [TypedMatch (ty_str, t)]
                       | WithProperty t => [PropertyMatch t]
                       | WithWellForm t => [WellFormMatch t]
                       | _ => [])
         descs

fun retrieve_pats_r descs =
    maps (fn desc => case desc of
                         GetFact (pat_r, th) => [(pat_r, th)]
                       | _ => [])
         descs

fun retrieve_filts descs =
    let
      val filts = maps (fn Filter filt => [filt] | _ => []) descs
    in
      fn ctxt => fn inst => forall (fn f => f ctxt inst) filts
    end

fun retrieve_cases descs =
    let
      fun retrieve_case desc =
          case desc of
              CreateCase assum => [mk_Trueprop assum]
            | CreateConcl concl => [mk_Trueprop (get_neg concl)]
            | _ => []
    in
      maps retrieve_case descs
    end

fun retrieve_shadows descs =
    let
      fun retrieve_shadow desc =
          case desc of ShadowFirst => [0] | ShadowSecond => [1] | _ => []
    in
      maps retrieve_shadow descs
    end

fun retrieve_score descs =
    let
      fun retrieve_score desc =
          case desc of WithScore n => SOME n | _ => NONE
    in
      get_first retrieve_score descs
    end

(* Given list of PropertyMatch and WellFormMatch arguments, attempt to
   find the corresponding theorems in the rewrite table. Return the
   list of theorems for each possible (mutually non-comparable) box
   IDs.
 *)
fun get_side_ths ctxt (id, inst) side_args =
    if null side_args then
      [(id, [])]
    else let
      val side_args' = map (ItemIO.subst_arg inst) side_args
      fun process_side_arg side_arg =
          case side_arg of
              PropertyMatch prop =>
              PropertyData.get_property_t ctxt (id, prop)
            | WellFormMatch (t, req) =>
              (WellformData.get_wellform_t ctxt (id, t))
                  |> filter (fn (_, th) => prop_of' th aconv req)
            | _ => raise Fail "get_side_ths: wrong kind of arg."
      val side_ths = map process_side_arg side_args'
    in
      if exists null side_ths then []
      else side_ths |> BoxID.get_all_merges_info ctxt
                    |> Util.max_partial (BoxID.id_is_eq_ancestor ctxt)
    end

(* Creates a proofstep with specified patterns and filters (in descs),
   and a custom function converting any instantiations into updates.
 *)
fun prfstep_custom name descs updt_fn =
    let
      val args = retrieve_args descs
      val (item_args, side_args) = filter_split ItemIO.is_ordinary_match args
      val filt = retrieve_filts descs
      val shadows = retrieve_shadows descs

      (* Processing an instantiation after matching the one or two
         main matchers: apply filters, remove trivial True from
         matchings, find properties, and replace incremental ids.
       *)
      fun process_inst ctxt ((id, inst), ths) =
          (get_side_ths ctxt (id, inst) side_args)
              |> filter (BoxID.has_incr_id o fst)
              |> map (fn (id', p_ths) => ((id', inst), p_ths @ ths))
              |> filter (filt ctxt o fst)

      fun shadow_to_update items ((id, _), _) n =
          ShadowItem {id = id, item = nth items n}
    in
      if length item_args = 1 then
        let
          val arg = the_single item_args
          fun prfstep ctxt item =
              let
                val inst_ths = (ItemIO.match_arg ctxt arg item ([], fo_init))
                                |> map (fn (inst, th) => (inst, [th]))
                                |> maps (process_inst ctxt)

                fun process_inst inst_th =
                    updt_fn inst_th [item] ctxt @
                    map (shadow_to_update [item] inst_th) shadows
              in
                maps process_inst inst_ths
              end
        in
          {name = name, args = args, func = OneStep prfstep}
        end
      else if length item_args = 2 then
        let
          val (arg1, arg2) = the_pair item_args
          fun prfstep1 ctxt item1 =
              let
                val inst_ths = ItemIO.match_arg ctxt arg1 item1 ([], fo_init)

                fun process_inst1 item2 ((id, inst), th) =
                    let
                      val arg2' = ItemIO.subst_arg inst arg2
                      val inst_ths' =
                          (ItemIO.match_arg ctxt arg2' item2 (id, inst))
                              |> map (fn (inst', th') => (inst', [th, th']))
                              |> maps (process_inst ctxt)

                      fun process_inst inst_th' =
                          updt_fn inst_th' [item1, item2] ctxt @
                          map (shadow_to_update [item1, item2] inst_th') shadows
                    in
                      maps process_inst inst_ths'
                    end
              in
                fn item2 => maps (process_inst1 item2) inst_ths
              end
        in
          {name = name, args = args, func = TwoStep prfstep1}
        end
      else
        raise Fail "prfstep_custom: must have 1 or 2 patterns."
    end

(* Create a proofstep from a list of proofstep descriptors. See
   datatype prfstep_descriptor for allowed types of descriptors.
 *)
fun gen_prfstep name descs =
    let
      val args = retrieve_args descs
      val pats_r = retrieve_pats_r descs
      val cases = retrieve_cases descs
      val sc = retrieve_score descs
      val input_descs =
          filter (fn desc => case desc of GetFact _ => false
                                        | CreateCase _ => false
                                        | CreateConcl _ => false
                                        | _ => true) descs

      (* Verify that all schematic variables appearing in pats_r /
         cases appear in pats.
       *)
      val pats = map ItemIO.pat_of_match_arg args
      val vars = map Var (fold Term.add_vars pats [])
      fun check_pat_r (pat_r, _) =
          subset (op aconv) (map Var (Term.add_vars pat_r []), vars)
      fun check_case assum =
          subset (op aconv) (map Var (Term.add_vars assum []), vars)
      val _ = assert (forall check_pat_r pats_r andalso forall check_case cases)
                     "gen_prfstep: new schematic variable in pats_r / cases."

      fun pats_r_to_update ctxt (inst_ths as ((id, _), _)) =
          if null pats_r then [] else
          let
            val ths = map (apply_pat_r ctxt inst_ths) pats_r
          in
            if length ths = 1 andalso
               Thm.prop_of (the_single ths) aconv pFalse then
              [ResolveBox {id = id, th = the_single ths}]
            else
              [AddItems {id = id, sc = sc,
                         raw_items = map Update.thm_to_ritem ths}]
          end

      fun case_to_update ((id, inst), _) assum =
          AddBoxes {id = id, sc = sc,
                    init_assum = Util.subst_term_norm inst assum}
      fun cases_to_update inst_ths = map (case_to_update inst_ths) cases

      fun updt_fn inst_th _ ctxt =
          pats_r_to_update ctxt inst_th @ cases_to_update inst_th
    in
      prfstep_custom name input_descs updt_fn
    end

fun prfstep_pre_conv name descs pre_cv =
    let
      val args = retrieve_args descs
      val _ = case args of
                  [TypedMatch ("TERM", _)] => ()
                | _ => raise Fail ("prfstep_conv: should have exactly one " ^
                                   "term pattern.")
      val filt = retrieve_filts descs

      fun prfstep ctxt item =
          let
            val inst_ths =
                (ItemIO.match_arg ctxt (the_single args) item ([], fo_init))
                    |> filter (BoxID.has_incr_id o fst o fst)
                    |> filter (filt ctxt o fst)

            fun inst_to_updt ((id, _), eq1) =
                (* Here eq1 is meta_eq from pat(inst) to item. *)
                let
                  val ct = Thm.lhs_of eq1
                  val err = name ^ ": cv failed."
                  val eq_th = pre_cv ctxt ct
                              handle CTERM _ => raise Fail err
                in
                  if Thm.is_reflexive eq_th then [] else
                  if RewriteTable.is_equiv id ctxt (Thm.rhs_of eq1, Thm.rhs_of eq_th)
                  then []
                  else let
                    val th = to_obj_eq (Util.transitive_list [meta_sym eq1, eq_th])
                  in
                    [Update.thm_update (id, th)]
                  end
                end
          in
            maps inst_to_updt inst_ths
          end
    in
      {name = name, args = args, func = OneStep prfstep}
    end

fun prfstep_conv name descs cv = prfstep_pre_conv name descs (K cv)

end  (* structure ProofStep *)

val WithTerm = ProofStep.WithTerm
val WithGoal = ProofStep.WithGoal
val WithProp = ProofStep.WithProp
val neq_filter = ProofStep.neq_filter
val order_filter = ProofStep.order_filter
val size1_filter = ProofStep.size1_filter
val not_type_filter = ProofStep.not_type_filter

signature PROOFSTEP_DATA =
sig
  val add_prfstep: proofstep -> theory -> theory
  val del_prfstep_pred: (string -> bool) -> theory -> theory
  val del_prfstep: string -> theory -> theory
  val del_prfstep_thm: thm -> theory -> theory
  val del_prfstep_thm_str: string -> thm -> theory -> theory
  val del_prfstep_thm_eqforward: thm -> theory -> theory
  val get_prfsteps: theory -> proofstep list

  val add_prfstep_custom:
      (string * prfstep_descriptor list *
       (id_inst_ths -> box_item list -> Proof.context -> raw_update list)) ->
      theory -> theory

  val add_gen_prfstep: string * prfstep_descriptor list -> theory -> theory
  val add_prfstep_pre_conv: string * prfstep_descriptor list *
                            (Proof.context -> conv) -> theory -> theory
  val add_prfstep_conv:
      string * prfstep_descriptor list * conv -> theory -> theory

  (* Constructing conditional prfstep_descriptors. *)
  type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor
  val with_term: string -> pre_prfstep_descriptor
  val with_cond: string -> pre_prfstep_descriptor
  val with_conds: string list -> pre_prfstep_descriptor list
  val with_filt: prfstep_filter -> pre_prfstep_descriptor
  val with_filts: prfstep_filter list -> pre_prfstep_descriptor list
  val with_score: int -> pre_prfstep_descriptor

  (* Second level proofstep writing functions. *)
  datatype prfstep_mode = MODE_FORWARD | MODE_FORWARD' | MODE_BACKWARD
                          | MODE_BACKWARD1 | MODE_BACKWARD2 | MODE_RESOLVE
  val add_prfstep_check_req: string * string -> theory -> theory
  val add_forward_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward'_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward1_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_backward2_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_resolve_prfstep_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_forward_prfstep: thm -> theory -> theory
  val add_forward'_prfstep: thm -> theory -> theory
  val add_backward_prfstep: thm -> theory -> theory
  val add_backward1_prfstep: thm -> theory -> theory
  val add_backward2_prfstep: thm -> theory -> theory
  val add_resolve_prfstep: thm -> theory -> theory

  val add_rewrite_rule_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_back_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory
  val add_rewrite_rule_bidir_cond:
      thm -> pre_prfstep_descriptor list -> theory -> theory

  val add_rewrite_rule: thm -> theory -> theory
  val add_rewrite_rule_back: thm -> theory -> theory
  val add_rewrite_rule_bidir: thm -> theory -> theory

  val setup_attrib: (thm -> theory -> theory) -> attribute context_parser
end;

structure ProofStepData : PROOFSTEP_DATA =
struct

structure Data = Theory_Data (
  type T = proofstep list;
  val empty = [];
  val extend = I;
  fun merge (ps1, ps2) = Library.merge ProofStep.eq_prfstep (ps1, ps2)
)

(* Add the given proof step. *)
fun add_prfstep (prfstep as {args, ...}) =
    Data.map (fn prfsteps =>
       if Util.is_prefix_str "$" (#name prfstep) then
         error "Add prfstep: names beginning with $ is reserved."
       else let
         val num_args = length (filter_out ItemIO.is_side_match args)
       in
         if num_args >= 1 andalso num_args <= 2 then prfsteps @ [prfstep]
         else error "add_proofstep: need 1 or 2 patterns."
       end)

(* Deleting a proofstep. For string inputs, try adding theory
   name. For theorem inputs, try all @-suffixes.
 *)
fun del_prfstep_pred pred =
    Data.map (fn prfsteps =>
       let
         val names = map #name prfsteps
         val to_delete = filter pred names
         fun eq_name (key, {name, ...}) = (key = name)
       in
         if null to_delete then
           error "Delete prfstep: not found"
         else let
           val _ = writeln (cat_lines (map (fn name => "Delete " ^ name)
                                           to_delete))
         in
           subtract eq_name to_delete prfsteps
         end
       end)

fun del_prfstep prfstep_name thy =
    del_prfstep_pred (equal prfstep_name) thy

(* Delete all proofsteps for a given theorem. *)
fun del_prfstep_thm th =
    let
      val th_name = Util.name_of_thm th
    in
      del_prfstep_pred (equal th_name orf Util.is_prefix_str (th_name ^ "@"))
    end

(* Delete proofsteps for a given theorem, with the given postfix. *)
fun del_prfstep_thm_str str th =
    del_prfstep_pred (equal (Util.name_of_thm th ^ str))

val del_prfstep_thm_eqforward = del_prfstep_thm_str "@eqforward"

fun get_prfsteps thy = Data.get thy

fun add_prfstep_custom (name, descs, updt_fn) =
    add_prfstep (ProofStep.prfstep_custom name descs updt_fn)

fun add_gen_prfstep (name, descs) =
    add_prfstep (ProofStep.gen_prfstep name descs)

fun add_prfstep_pre_conv (name, descs, pre_cv) =
    add_prfstep (ProofStep.prfstep_pre_conv name descs pre_cv)

fun add_prfstep_conv (name, descs, cv) =
    add_prfstep (ProofStep.prfstep_conv name descs cv)

(* Constructing conditional prfstep_descriptors. *)

type pre_prfstep_descriptor = Proof.context -> prfstep_descriptor

fun with_term str ctxt =
    let
      val t = Proof_Context.read_term_pattern ctxt str
      val _ = assert (null (Term.add_frees t []))
                     "with_term: should not contain free variable."
    in
      WithTerm t
    end

fun with_cond str ctxt =
    Filter (neq_filter (Proof_Context.read_term_pattern ctxt str))

fun with_conds strs = map with_cond strs

fun with_filt filt = K (Filter filt)
fun with_filts filts = map with_filt filts
fun with_score n = K (WithScore n)

(* Second level proofstep writing functions. *)

fun add_and_print_prfstep prfstep_name descs thy =
    let
      val _ = writeln (prfstep_name ^ "\n" ^ (ProofStep.string_of_descs thy descs))
    in
      add_gen_prfstep (prfstep_name, descs) thy
    end

(* Add a proofstep checking a requirement. *)
fun add_prfstep_check_req (t_str, req_str) thy =
    let
      val ctxt = Proof_Context.init_global thy
      val t = Proof_Context.read_term_pattern ctxt t_str
      val vars = map Free (Term.add_frees t [])
      val c = Util.get_head_name t
      val ctxt' = fold Util.declare_free_term vars ctxt
      val req = Proof_Context.read_term_pattern ctxt' req_str

      fun get_subst var =
          case var of Free (x, T) => (var, Var ((x, 0), T))
                    | _ => raise Fail "add_prfstep_check_req"
      val subst = map get_subst vars
      val t' = Term.subst_atomic subst t
      val req' = Term.subst_atomic subst req
    in
      add_and_print_prfstep
          (c ^ "_case") [WithTerm t', CreateConcl req'] thy
    end

datatype prfstep_mode = MODE_FORWARD | MODE_FORWARD' | MODE_BACKWARD
                        | MODE_BACKWARD1 | MODE_BACKWARD2 | MODE_RESOLVE

(* Maximum number of term matches for the given mode. *)
fun max_term_matches mode =
    case mode of
        MODE_FORWARD => 2
      | MODE_FORWARD' => 1
      | MODE_BACKWARD => 1
      | MODE_RESOLVE => 1
      | _ => 0

(* Obtain the first several premises of th that are either properties
   or wellformed-ness data. ts is the list of term matches.
 *)
fun get_side_prems thy mode ts th =
    let
      val (prems, concl) = UtilLogic.strip_horn' th
      val _ = assert (length ts <= max_term_matches mode)
                     "get_side_prems: too many term matches."

      (* Helper function. Consider the case where the first n premises
         are side conditions. Find the additional terms to match
         against for each mode.
       *)
      fun additional_matches n =
          let
            val prems' = drop n prems
          in
            case mode of
                MODE_FORWARD => take (2 - length ts) prems'
              | MODE_FORWARD' =>
                if null ts andalso length prems' >= 2 then
                  [hd prems', List.last prems']
                else [List.last prems']
              | MODE_BACKWARD => [get_neg concl]
              | MODE_BACKWARD1 => [get_neg concl, List.last prems']
              | MODE_BACKWARD2 => [get_neg concl, hd prems']
              | MODE_RESOLVE =>
                if null ts andalso length prems' > 0 then
                  [get_neg concl, List.last prems']
                else [get_neg concl]
          end

      (* Determine whether t is a valid side premises, relative to the
         matches ts'. If yes, return the corresponding side
         matching. Otherwise return NONE.
       *)
      fun to_side_prems ts' t =
          case WellForm.is_subterm_wellform_data thy t ts' of
              SOME (t, req) => SOME (WithWellForm (t, req))
            | NONE => if Property.is_property_prem thy t then SOME (WithProperty t)
                      else NONE

      (* Attempt to convert the first n premises to side matchings. *)
      fun to_side_prems_n n =
          let
            val ts' = additional_matches n @ ts
            val side_prems' = prems |> take n
                                    |> map (to_side_prems ts')
          in
            if forall is_some side_prems' then
              SOME (map the side_prems')
            else NONE
          end

      (* Minimum number of premises for the given mode. *)
      val min_prems =
          case mode of
              MODE_FORWARD => 1 - length ts
            | MODE_FORWARD' => 1
            | MODE_BACKWARD => 1
            | MODE_BACKWARD1 => 2
            | MODE_BACKWARD2 => 2
            | MODE_RESOLVE => 0

      val _ = assert (length prems >= min_prems)
                     "get_side_prems: too few premises."
      val to_test = rev (0 upto (length prems - min_prems))
    in
      (* Always succeeds at 0. *)
      the (get_first to_side_prems_n to_test)
    end

(* Convert theorems of the form A1 ==> ... ==> An ==> C to A1 & ... &
   An ==> C. If keep_last = true, the last assumption is kept in
   implication form.
 *)
fun atomize_conj_cv keep_last ct =
    if length (Logic.strip_imp_prems (Thm.term_of ct)) <=
       (if keep_last then 2 else 1) then
      Conv.all_conv ct
    else
      Conv.every_conv [Conv.arg_conv (atomize_conj_cv keep_last),
                       Conv.rewr_conv UtilBase.atomize_conjL_th] ct

(* Swap the last premise to become the first. *)
fun swap_prem_to_front ct =
    let
      val n = length (Logic.strip_imp_prems (Thm.term_of ct))
    in
      if n < 2 then
        Conv.all_conv ct
      else if n = 2 then
        Conv.rewr_conv Drule.swap_prems_eq ct
      else
        ((Conv.arg_conv swap_prem_to_front)
             then_conv (Conv.rewr_conv Drule.swap_prems_eq)) ct
    end

(* Using cv, rewrite all assumptions and conclusion in ct. *)
fun horn_conv cv ct =
    (case Thm.term_of ct of
         @{const Pure.imp} $ _ $ _ =>
         (Conv.arg1_conv (Trueprop_conv cv))
             then_conv (Conv.arg_conv (horn_conv cv))
       | _ => Trueprop_conv cv) ct

(* Try to cancel terms of the form ~~A. *)
val try_nn_cancel_cv = Conv.try_conv (rewr_obj_eq UtilBase.nn_cancel_th)

(* Post-processing of the given theorem according to mode. *)
fun post_process_th ctxt mode side_count ts th =
    case mode of
        MODE_FORWARD =>
        let
          val to_skip = side_count + (2 - length ts)
        in
          th |> apply_to_thm (Util.skip_n_conv to_skip (UtilLogic.to_obj_conv ctxt))
             |> Util.update_name_of_thm th ""
        end
      | MODE_FORWARD' =>
        let
          val cv =
              swap_prem_to_front
                  then_conv (Util.skip_n_conv (2 - length ts) (UtilLogic.to_obj_conv ctxt))
        in
          th |> apply_to_thm (Util.skip_n_conv side_count cv)
             |> Util.update_name_of_thm th ""
        end
      | MODE_BACKWARD =>
        let
          val cv = (atomize_conj_cv false)
                       then_conv (Conv.rewr_conv UtilBase.backward_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
        in
          th |> apply_to_thm (Util.skip_n_conv side_count cv)
             |> Util.update_name_of_thm th "@back"
        end
      | MODE_BACKWARD1 =>
        let
          val cv = (atomize_conj_cv true)
                       then_conv (Conv.rewr_conv UtilBase.backward1_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
        in
          th |> apply_to_thm (Util.skip_n_conv side_count cv)
             |> Util.update_name_of_thm th "@back1"
        end
      | MODE_BACKWARD2 =>
        let
          val cv = (Conv.arg_conv (atomize_conj_cv false))
                       then_conv (Conv.rewr_conv UtilBase.backward2_conv_th)
                       then_conv (horn_conv try_nn_cancel_cv)
        in
          th |> apply_to_thm (Util.skip_n_conv side_count cv)
             |> Util.update_name_of_thm th "@back2"
        end
      | MODE_RESOLVE =>
        let
          val rewr_th =
              case Thm.nprems_of th - side_count of
                  0 => if is_neg (concl_of' th) then UtilBase.to_contra_form_th'
                       else UtilBase.to_contra_form_th
                | 1 => UtilBase.resolve_conv_th
                | _ => raise Fail "resolve: too many hypothesis in th."
          val cv = (Conv.rewr_conv rewr_th)
                       then_conv (horn_conv try_nn_cancel_cv)
        in
          th |> apply_to_thm (Util.skip_n_conv side_count cv)
             |> Util.update_name_of_thm th "@res"
        end

(* Add basic proofstep for the given theorem and mode. *)
fun add_basic_prfstep_cond th mode conds thy =
    let
      val ctxt = Proof_Context.init_global thy
      val ctxt' = ctxt |> Variable.declare_term (Thm.prop_of th)

      (* Replace variable definitions, obtaining list of replacements
         and the new theorem.
       *)
      val (pairs, th) =
          th |> apply_to_thm (UtilLogic.to_obj_conv_on_horn ctxt')
             |> Normalizer.meta_use_vardefs
             |> apsnd (Util.update_name_of_thm th "")

      (* List of definitions used. *)
      fun print_def_subst (lhs, rhs) =
          writeln ("Apply def " ^ (Syntax.string_of_term ctxt' lhs) ^ " = " ^
                   (Syntax.string_of_term ctxt' rhs))
      val _ = map print_def_subst pairs

      fun def_subst_fun cond =
          case cond of
              WithItem ("TERM", t) =>
              WithItem ("TERM", Normalizer.def_subst pairs t)
            | _ => cond
    in
      if null conds andalso
         (mode = MODE_FORWARD orelse mode = MODE_FORWARD') andalso
         Property.can_add_property_update th thy then
        Property.add_property_update th thy
      else let
        fun is_term_cond cond =
            case cond of WithItem ("TERM", _) => true | _ => false

        fun extract_term_cond cond =
            case cond of
                WithItem ("TERM", t) => t | _ => raise Fail "extract_term_cond"

        (* Instantiate each element of conds with ctxt', then separate
           into term and other (filter and shadow) conds.
         *)
        val (term_conds, filt_conds) =
            conds |> map (fn cond => cond ctxt')
                  |> filter_split is_term_cond
                  |> apfst (map def_subst_fun)

        (* Get list of assumptions to be obtained from either the
           property table or the wellform table.
         *)
        val ts = map extract_term_cond term_conds
        val side_prems = get_side_prems thy mode ts th
        val side_count = length side_prems
        val th' = th |> post_process_th ctxt' mode side_count ts

        val (assums, concl) =
            th' |> UtilLogic.strip_horn' |> apfst (drop side_count)
        val pats = map extract_term_cond term_conds @ assums
        val match_descs = term_conds @ map WithFact assums
        val _ = assert (Util.is_pattern_list pats)
                       "add_basic_prfstep: invalid patterns."
        val _ = assert (length pats > 0 andalso length pats <= 2)
                       "add_basic_prfstep: invalid number of patterns."
      in
        (* Switch two assumptions if necessary. *)
        if length pats = 2 andalso not (Util.is_pattern (hd pats)) then
          let
            val _ = writeln "Switching two patterns."
            val swap_prems_cv = Conv.rewr_conv Drule.swap_prems_eq
            val th'' =
                if length assums = 1 then th'
                else th' |> apply_to_thm (Util.skip_n_conv side_count swap_prems_cv)
                         |> Util.update_name_of_thm th' ""
            val swap_match_descs = [nth match_descs 1, hd match_descs]
            val descs = side_prems @ swap_match_descs @ filt_conds @
                        [GetFact (concl, th'')]
          in
            add_and_print_prfstep (Util.name_of_thm th') descs thy
          end
        else
          let
            val descs = side_prems @ match_descs @ filt_conds @
                        [GetFact (concl, th')]
          in
            add_and_print_prfstep (Util.name_of_thm th') descs thy
          end
      end
    end

fun add_forward_prfstep_cond th = add_basic_prfstep_cond th MODE_FORWARD
fun add_forward'_prfstep_cond th = add_basic_prfstep_cond th MODE_FORWARD'
fun add_backward_prfstep_cond th = add_basic_prfstep_cond th MODE_BACKWARD
fun add_backward1_prfstep_cond th = add_basic_prfstep_cond th MODE_BACKWARD1
fun add_backward2_prfstep_cond th = add_basic_prfstep_cond th MODE_BACKWARD2
fun add_resolve_prfstep_cond th = add_basic_prfstep_cond th MODE_RESOLVE

fun add_forward_prfstep th = add_forward_prfstep_cond th []
fun add_forward'_prfstep th = add_forward'_prfstep_cond th []
fun add_backward_prfstep th = add_backward_prfstep_cond th []
fun add_backward1_prfstep th = add_backward1_prfstep_cond th []
fun add_backward2_prfstep th = add_backward2_prfstep_cond th []
fun add_resolve_prfstep th = add_resolve_prfstep_cond th []

fun add_rewrite_eq_rule_cond th conds thy =
    let
      val th = if Util.is_meta_eq (Thm.concl_of th) then
                 UtilLogic.to_obj_eq_th th else th
      val (lhs, _) = th |> concl_of' |> strip_conj |> hd |> dest_eq
    in
      thy |> add_forward_prfstep_cond th (K (WithTerm lhs) :: conds)
    end

fun add_rewrite_iff_rule_cond th conds thy =
    let
      val th = if Util.is_meta_eq (Thm.concl_of th) then
                 UtilLogic.to_obj_eq_iff_th th else th
      val (lhs, _) = th |> concl_of' |> dest_eq
      val _ = assert (fastype_of lhs = boolT)
                     "add_rewrite_iff: argument not of type bool."

      val forward_th = th |> equiv_forward_th
      val nforward_th = th |> inv_backward_th
                           |> apply_to_thm (horn_conv try_nn_cancel_cv)
                           |> Util.update_name_of_thm th "@invbackward"
    in
      thy |> add_basic_prfstep_cond forward_th MODE_FORWARD' conds
          |> add_basic_prfstep_cond nforward_th MODE_FORWARD' conds
    end

fun add_rewrite_rule_cond th conds thy =
    let
      val th = if Util.is_meta_eq (Thm.concl_of th) then to_obj_eq_th th else th
      val (lhs, _) = th |> concl_of' |> strip_conj |> hd |> dest_eq
    in
      if fastype_of lhs = boolT then
        add_rewrite_iff_rule_cond th conds thy
      else
        add_rewrite_eq_rule_cond th conds thy
    end

fun add_rewrite_rule_back_cond th conds =
    add_rewrite_rule_cond (obj_sym_th th) conds

fun add_rewrite_rule_bidir_cond th conds =
    (add_rewrite_rule_cond th conds)
        #> add_rewrite_rule_back_cond th conds

fun add_rewrite_rule th = add_rewrite_rule_cond th []
fun add_rewrite_rule_back th = add_rewrite_rule_back_cond th []
fun add_rewrite_rule_bidir th = add_rewrite_rule th #> add_rewrite_rule_back th

fun setup_attrib f =
    Attrib.add_del
        (Thm.declaration_attribute (
            fn th => Context.mapping (f th) I))
        (Thm.declaration_attribute (
            fn _ => fn _ => raise Fail "del_step: not implemented."))

end  (* structure ProofStepData. *)

open ProofStepData
