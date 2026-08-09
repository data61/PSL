(*  Title:      Abduction/Top_Down_Util.ML
    Author:     Yutaka Nagashima, Huawei Technologies Research & Development (UK) Limited.
    Author:     Daniel Goc Sebastian, Huawei Technologies Research & Development (UK) Limited.

Utility functions for our top-down approach, as known as "deep conjecturing".
*)
(*** signature TOP_DOWN_UTIL ***)
signature TOP_DOWN_UTIL =
sig

exception NOT_THE_SAME_TERMS;
val standardize_vnames               : term -> term;
val standardize_vnames_with_mapping  : term -> term * (string * string) list;
(* Emission-time renaming, so an assembled proof's variable names are unique across its nodes.
   The canonical numbering above is per-term and starts at zero by design; this is the other
   half of that split. See offset_vnames for why no per-term function can do this. *)
val offset_vnames                    : int -> term -> term * (string * string) list;
val advance_past_vnames              : term -> int;
val standardize_vnames_with_mapping_in_ctxt:
  Proof.context -> term -> term * (string * string) list;
val alpha_eq_over_fvar               : term -> term -> bool;
val remove_Trueprop                  : term -> term;
val mk_free_variable_of_typ          : typ -> int -> term;
val numb_of_distinct_fvars           : term -> int;
val numb_of_distinct_bvars           : term -> int;
val get_both_sides_of_eqs_in_term    : term -> (term * term) list;
val get_consts_for_conjecturing      : Proof.context -> term -> terms;
val read_terms                       : Proof.context -> strings -> terms;
val read_props                       : Proof.context -> strings -> terms;
val check_terms                      : Proof.context -> terms -> terms;
val get_fresh_free_var_of_typ_in_trm : Proof.context -> typ -> term -> term;
val get_fresh_free_vars_of_typ_in_trm: Proof.context -> typ -> term -> int -> terms;
val is_prop                          : term -> bool;
val mk_prop                          : Proof.context -> term -> term;
val mk_unbound_bound_vars_free_vars  : Proof.context -> term -> term;
val get_lemma_names_from_sh_output   : theory -> string -> strings;
val is_thm_name_registered           : Proof.context -> string -> bool;
val mk_new_lemma_name                :
  Proof.context -> bool(*is_final_goal*) -> string (*lemma_type*) -> string;
val term_compare                     : term * term -> order;
val term_to_thm                      : Proof.context -> term -> thm;
val timeout_config                   : real Config.T;
val suggestion_target                : string Config.T;
val suggestion_target_for            : Position.T -> string;
(* Write a found proof to a persistent file. A proof is a result, not a message: it must never be
   droppable. See the implementation for the three destinations and why silence is not one. *)
val write_proof_to_file              : Proof.context -> string -> unit;
(* Records whether the search proved the goal, where a batch harness can read it. The _applied
   form is for solve, which closes the caller's goal instead of emitting a script, so no proof
   file is expected of it and none is demanded. *)
(* Says, once per search, that PSL_PROOF_OUTPUT_DIR is unset while other PSL_* harness
   variables are set. A feature gated on an unset environment variable does not fail, it is
   absent - measured by the first external consumer: their runner exported a similarly-named
   variable, every verdict and snapshot silently went nowhere, and the only symptom was a new
   feature never firing. Absence should be audible when the context says a harness is
   driving. *)
val warn_if_proof_output_dir_unset   : unit -> unit;
val write_verdict                    : Proof.context -> bool -> real -> unit;
val write_verdict_applied            : Proof.context -> bool -> real -> unit;
(* The root goal itself has a genuine counterexample: there is nothing to prove, and a
   webservice runner reading verdicts.csv must be able to tell that apart from "unproved". *)
val write_verdict_refuted            : Proof.context -> real -> unit;
(* CONTRACT SURFACE, pinned by Contract_Test and consumed by the Heinzelmen webservice:
   the verdict vocabulary and the artifact names. Change these only together with the
   fixtures and after coordinating with consumers. *)
val verdict_proved                   : string;
val verdict_unproved                 : string;
val verdict_proved_applied           : string;
val verdict_refuted                  : string;
val verdicts_file_name               : string;
val progress_file_suffix             : string;
val refutation_file_suffix           : string;
(* Budgets for the root refutation watchdog (quickcheck, then nitpick, run in parallel with
   the search). A value <= 0 disables that tool. *)
val refute_root_quickcheck_timeout   : real Config.T;
val refute_root_nitpick_timeout      : real Config.T;
(* Seconds between progress reports while the graph search runs: the completely-proved
   auxiliary lemmas so far, printed to the Output pane and written beside verdicts.csv as
   <theory>_progress.thy for an external manager to read. <= 0 disables. *)
val progress_report_interval         : real Config.T;
val limit_for_first_decrement        : int Config.T;
val limit_for_other_decrement        : int Config.T;
val is_in                            : term -> term -> bool;
val is_only_in_subtrm_of             : term -> term -> term -> bool;
val is_compound                      : term -> bool;
val has_fvar_appearing_only_in_the_same_compound_trm: term -> bool;
val mk_pst_to_prove_from_term        : Proof.state -> term -> Proof.state;
val non_prop_trm_to_dummy_eq         : Proof.context -> term -> thm option;
val simp_non_prop_term               : Proof.context -> term -> term;
val strip_outermost_meta_quantifier  : term -> (bool * term);
val strip_outermost_meta_quantifiers : term -> term;
val mk_extended_rhses                : Proof.context -> terms -> term -> terms;
val replace_redundant_compound_subtrm_with_free_var:
  Proof.context -> (term * term) -> (term * term);
val parallel_filter                  : ('a -> bool) -> 'a list -> 'a list;
val parallel_filter_out              : ('a -> bool) -> 'a list -> 'a list;
val is_template_based                : string -> bool;

end;

(*** structure Top_Down_Util ***)
structure Top_Down_Util: TOP_DOWN_UTIL =
struct

structure IU = Isabelle_Utils;

(* How to standardize variable names to var_n? *)
exception NOT_THE_SAME_TERMS;

(* keep names a free variable that must NOT be renamed.
 *
 * Renaming every free is wrong as soon as some of them are fixed by the surrounding context
 * rather than being the goal's own variables. Inside a locale or class body the parameters -
 * the operation and its unit, say - appear as ordinary frees, so standardizing turned
 *
 *   f (f x y) e = f x y     into     var_0 (var_0 var_1 var_2) var_3 = var_0 var_1 var_2
 *
 * and the locale's own assumptions, which still speak of f and e, then matched nothing. The
 * search was left hunting for a proof about variables it knew nothing about, having discarded
 * exactly the facts that would have proved the goal. Measured before this change: a goal that
 * is a direct instance of a locale assumption was not solved in three attempts, nor in 1m42s
 * of "suggest".
 *
 * The same applies to anything the enclosing proof has fixed - "fix x", or the variables a
 * "case (S x)" introduces - since a script that renames those refers to nothing that exists
 * where it is pasted. *)
fun standardize_vnames'' (keep: string -> bool) (Free (fvar_name, typ))
    (mapping:(string * string) list): term * ((string * string) list) =
(*TODO: check if we have a constant of the same name.*)
    if keep fvar_name then (Free (fvar_name, typ), mapping)
    else if AList.defined (op =) mapping fvar_name
      then (Free (the (AList.lookup (op =) mapping fvar_name), typ), mapping)
      else (Free ("var_" ^ Int.toString (length mapping), typ),
             (fvar_name, "var_" ^ Int.toString (length mapping))::mapping)
  | standardize_vnames'' keep (Abs (_, typ, trm)) mapping =
      let
        val (new_trm, new_mapping) = standardize_vnames'' keep trm mapping
      in
        (Abs ("", typ, new_trm), new_mapping)
      end
  | standardize_vnames'' keep (trm1 $ trm2) mapping =
      let
        val (new_trm1, new_mapping1) = standardize_vnames'' keep trm1 mapping
        val (new_trm2, new_mapping2) = standardize_vnames'' keep trm2 new_mapping1
      in
        (new_trm1 $ new_trm2, new_mapping2)
      end
  | standardize_vnames'' _ trm mapping = (trm, mapping);

(* offset_vnames *)
(* The other half of the split that standardize_vnames only does one side of.
 *
 * standardize_vnames numbers each term's frees var_0, var_1, ... FROM ZERO, PER TERM. That is
 * exactly right for what it is mostly for - a canonical form, so that two alpha-equivalent
 * conjectures compare equal and the search does not explore the same lemma twice. It is exactly
 * wrong for the other thing those names are used for: naming variables in a proof that is
 * assembled from several independently-standardised nodes. Every node calls its first variable
 * var_0, so an assembled proof has as many unrelated var_0s as it has nodes, of whatever types
 * their own branches gave them.
 *
 * The three existing variants all address the first use or the bridge back from it -
 * standardize_vnames (canonical), _with_mapping (keep the bridge), _with_mapping_in_ctxt (leave
 * the caller's own fixed variables alone). None of them makes the emitted names unique, because
 * that is a property of the assembled proof rather than of any one term, and no per-term function
 * can establish it.
 *
 * So this is applied at assembly time, threading a counter across the nodes: node n's variables
 * become var_k, var_(k+1), ... where k is one past the highest index any earlier node used. The
 * canonical form is untouched - comparison and deduplication keep numbering from zero - and the
 * emitted names become unique by construction rather than by luck.
 *
 * Returns the renamed term and the mapping, because the node's proof SCRIPT has to be renamed
 * with the same mapping (see rename_vars_in_script) or the statement and the script that proves
 * it will disagree about what the variables are called - which is this repository's most familiar
 * shape of defect, arriving by yet another door.
 *
 * The caller must pass an offset at least as large as the number of var_N frees in the term;
 * threading a running total does this by construction, and it is what keeps the rename from
 * colliding with a name already present in the same term. *)
fun offset_vnames (offset:int) (trm:term): term * (string * string) list =
  let
    fun is_standard n =
      String.isPrefix "var_" n andalso size n > 4
      andalso CharVector.all Char.isDigit (String.extract (n, 4, NONE));
    fun index_of n = the_default 0 (Int.fromString (String.extract (n, 4, NONE)));
    val names   = Term.add_free_names trm [] |> filter is_standard;
    val mapping =
      map (fn n => (n, "var_" ^ string_of_int (offset + index_of n))) names
      : (string * string) list;
    fun rename (Free (n, T)) =
          Free (the_default n (AList.lookup (op =) mapping n), T)
      | rename aterm = aterm;
  in
    (Term.map_aterms rename trm, mapping)
  end;

(* How far a caller threading offset_vnames must advance to clear this term: one past the highest
   var_N index it uses.
 *
 * This counted the variables instead, which is only the same thing while the indices run
 * contiguously from zero. That holds for a freshly standardised term and is not a property anything
 * enforces - a term carrying var_0 and var_5 has two variables and needs an advance of six, and
 * counting would let a later node be renumbered straight onto that var_5. Nothing produces such a
 * term today; the point is that this function no longer cares whether anything does.
 *
 * Suggested by the project owner, who asked why this did not use serial() - Isabelle's global
 * unique counter, which mk_new_lemma_name already uses for lemma names. serial() would make the
 * names unique by construction and remove the arithmetic entirely, at the cost of emitting
 * var_5149904 where a reader wants var_2. Contiguous names are worth keeping for a proof somebody
 * has to read, so the arithmetic stays - but it is now correct without an unstated assumption. *)
fun advance_past_vnames (trm:term): int =
  let
    fun index n =
      if String.isPrefix "var_" n andalso size n > 4
         andalso CharVector.all Char.isDigit (String.extract (n, 4, NONE))
      then Int.fromString (String.extract (n, 4, NONE))
      else NONE;
  in
    Term.add_free_names trm []
    |> map_filter index
    |> (fn [] => 0 | is => fold (fn i => fn m => Int.max (i, m)) is 0 + 1)
  end;

(* Rename every free, keeping nothing: the original behaviour, for callers that hold a bare
 * term with no context to consult. *)
fun standardize_vnames' trm mapping = standardize_vnames'' (K false) trm mapping;

fun standardize_vnames trm = fst (standardize_vnames' trm []);

(* standardize_vnames_with_mapping *)
(* Like standardize_vnames, but also returns the (original_name, standardized_name) mapping
 * that standardize_vnames' computes internally and standardize_vnames itself throws away.
 * Needed wherever a standardized term's printed proof script has to be translated back to
 * whatever names its free variables actually have in some other, non-standardized context -
 * see rename_vars_in_script. *)
fun standardize_vnames_with_mapping trm = standardize_vnames' trm [];

(* Like standardize_vnames_with_mapping, but leaves alone any free that the surrounding proof
 * context has fixed - locale and class parameters, and whatever "fix"/"case" introduced. See
 * standardize_vnames'' for why renaming those breaks the search outright. *)
fun standardize_vnames_with_mapping_in_ctxt (ctxt:Proof.context) trm =
  standardize_vnames'' (Variable.is_fixed ctxt) trm [];

fun remove_Trueprop (Abs (name, typ, trm)) = Abs (name, typ, remove_Trueprop trm)
  | remove_Trueprop (Const ("HOL.Trueprop", _) $ trm2) = remove_Trueprop trm2
  | remove_Trueprop (trm1 $ trm2) = remove_Trueprop trm1 $ remove_Trueprop trm2
  | remove_Trueprop atom = atom;

fun alpha_eq_over_fvar trm1 trm2 =
  let
    val (non_prop1, non_prop2) = Utils.map_pair remove_Trueprop (trm1, trm2): (term * term);
    val converted1 = standardize_vnames non_prop1
    val converted2 = standardize_vnames non_prop2
  in
    converted1 = converted2
  end;

(* How to make a free variable of a particular type and a name of "var_i"? *)
fun mk_free_variable_of_typ (typ:typ) (i:int) = Free ("var_" ^ Int.toString i, typ);

fun numb_of_distinct_atom (is_atom:term -> bool) (trm:term) =
   Term.fold_aterms (fn t => fn acc => if is_atom t then t :: acc else acc) trm []
|> distinct (op =)
|> length;

fun numb_of_distinct_fvars (trm:term) = numb_of_distinct_atom is_Free trm;

fun numb_of_distinct_bvars (trm:term) = numb_of_distinct_atom is_Bound trm;

fun get_both_sides_of_eqs_in_term (term:term): (term * term) list =
  let
    val subtrms = Proof_Goal_Transformer.get_subtrms term: terms;
    val pairs   = List.mapPartial (try HOLogic.dest_eq) subtrms;
  in
    pairs
  end;

(* How can I find a list of constants used in the definitions of the constants appearing in a
   term? *)
fun get_consts_for_conjecturing (ctxt:Proof.context) (trm:term) =
  let
    val cnames_in_trm   = IU.get_cnames_in_trm trm: string list;
    val simp_rules      =
          map (Find_Theorems2.get_thms_of_name_with_suffix ctxt "simps") cnames_in_trm |> flat;
    val consts_in_simps = map IU.get_consts_in_thm simp_rules |> flat |> distinct (op =);
  in
    consts_in_simps : terms
  end;

fun read_terms ctxt    = List.mapPartial (try (Syntax.read_term ctxt)): strings -> terms;
fun read_props ctxt    = List.mapPartial (try (Syntax.read_prop ctxt)): strings -> terms;
fun check_terms ctxt   = List.mapPartial (try (Syntax.check_term ctxt)): terms -> terms;

fun clean_type_of_term (term:term) = Term.map_types (map_atyps (K dummyT)) term: term;

fun is_prop trm = body_type (type_of trm) = @{typ "prop"};

fun mk_prop (ctxt:Proof.context) (term:term) =
  let
    val term_w_clean_typ = clean_type_of_term term;
    val prop    = if is_prop term then term else HOLogic.mk_Trueprop term_w_clean_typ;
    val checked = clean_type_of_term prop |> Syntax.check_term ctxt: term;
  in
    checked
  end;

fun get_all_names_in_trm trm =
  IU.get_cnames_in_trm trm @ IU.get_abs_names_in_trm trm @ IU.get_free_var_names_in_trm trm;

fun get_fresh_free_var_name_in_trm' (ctxt:Proof.context) (trm:term) (n:int) =
  let
    val numb_of_fvars = numb_of_distinct_fvars trm + n;
    val fst_candidate = mk_free_variable_of_typ dummyT numb_of_fvars |> dest_Free |> fst: string;
    fun is_free_in_ctxt (name:string) = is_Free (Syntax.read_term ctxt name): bool;
    val all_names_in_trm  = get_all_names_in_trm trm |> distinct (op =): strings;
    fun is_fresh (current_candidate:string) =
        not (member (op =) all_names_in_trm current_candidate)
        andalso is_free_in_ctxt current_candidate;
    fun add_a_if_taken (current_candidate:string): string =
      if is_fresh current_candidate then current_candidate
      else add_a_if_taken (current_candidate ^ "a");
    val result = add_a_if_taken fst_candidate: string
  in
    result
  end;

local

fun get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
  Free (get_fresh_free_var_name_in_trm' ctxt trm n, typ);

in

fun get_fresh_free_var_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) =
    get_fresh_free_var_of_typ_in_trm' (ctxt:Proof.context) (typ:typ) (trm:term) (0:int)

fun get_fresh_free_vars_of_typ_in_trm (ctxt:Proof.context) (typ:typ) (trm:term) (n:int) =
    map (get_fresh_free_var_of_typ_in_trm' ctxt typ trm) (List.tabulate (n, I)): terms;

end;

fun strip_all_body_nested (Const ("Pure.all", _) $ Abs (_, _, t)) = strip_all_body_nested t
  | strip_all_body_nested (Abs (str, typ, trm)) = Abs (str, typ, strip_all_body_nested trm)
  | strip_all_body_nested (trm1 $ trm2) = strip_all_body_nested trm1 $ strip_all_body_nested trm2
  | strip_all_body_nested t = t;

fun mk_unbound_bound_vars_free_vars (ctxt:Proof.context) (trm:term) =
  let
    val trm = standardize_vnames trm;
    val stripped_trm = strip_all_body_nested trm;
    val bvars =
          Term.fold_aterms (fn t => fn acc => if is_Bound t then t :: acc else acc) stripped_trm
            [];
    val distinct_bvars = distinct (op =) bvars: terms;
    val numb_of_distinct_bvars = length distinct_bvars: int;
    val fvars =
          get_fresh_free_vars_of_typ_in_trm ctxt dummyT stripped_trm numb_of_distinct_bvars
          : terms;
    val bvar_fvar_pairs = distinct_bvars ~~ fvars: (term * term) list;
    fun replace_bvar (bvar:term, fvar: term) (trm as Bound _) =
          if trm = bvar then fvar else trm
      | replace_bvar  p (Abs (str, typ, trm)) = Abs (str, typ, replace_bvar p trm)
      | replace_bvar  p (trm1 $ trm2)         = replace_bvar p trm1 $ replace_bvar p trm2
      | replace_bvar  _  trm                  = trm;
    val result = fold replace_bvar bvar_fvar_pairs trm: term;
  in
    result: term
  end;

fun get_lemma_names_from_sh_output (thy:theory) (sh_output:string) =
  let
    val keywords      = Thy_Header.get_keywords thy                       : Keyword.keywords;
    val tokens        = Token.explode keywords Position.none sh_output    : Token.T list;
    val strings       = map Token.unparse tokens                          : strings;
    fun get_base_name (name:string) =
          if Long_Name.is_qualified name then Long_Name.base_name name else name;
    val base_names    = map get_base_name strings: strings;
    val filtered      = filter (String.isPrefix "abduced_lemma_") base_names: strings;
in
    filtered
end;

fun is_thm_name_registered (ctxt:Proof.context) (thm_name:string) =
      try (Proof_Context.get_thm ctxt) thm_name |> is_some: bool;

fun mk_new_lemma_name (ctxt:Proof.context) (is_final_goal:bool) (lemma_type:string): string =
  let
    val name_header    =
          (if is_final_goal then "original_goal" else "abduced_lemma_") ^ lemma_type ^ "_";
    val candidate_name = name_header ^ Int.toString (serial()): string;
    val this_name_is_already_taken = is_thm_name_registered ctxt candidate_name;
  in
    if   this_name_is_already_taken
    then mk_new_lemma_name ctxt is_final_goal lemma_type
    else candidate_name
  end

fun term_compare (trm1, trm2) =
  Term_Ord.term_ord (standardize_vnames trm1, standardize_vnames trm2);

fun term_to_thm (ctxt:Proof.context) (cnjctr:term) =
  let
    val prop              = if is_prop cnjctr then cnjctr else HOLogic.mk_Trueprop cnjctr;
    val prop_wo_typ_const = IU.strip_atyp prop: term;
    val checked_prop      = Syntax.check_prop ctxt prop_wo_typ_const: term;
    val fvar_names        = IU.get_free_var_names_in_trm prop |> distinct (op =): strings;
    fun cheat _           = ALLGOALS (Skip_Proof.cheat_tac ctxt);
    val thm               = Goal.prove ctxt fvar_names [] checked_prop cheat: thm;
  in
    thm
  end;

(* Attrib.setup_config_* rather than Config.declare_*: only the former registers the attribute
   that makes "declare [[prove_timeout = 60]]" work from a theory. These were previously
   declared and so reachable only from ML via Config.put, which meant a caller could not bound
   a search at all - awkward for interactive use and prohibitive for tests, since the default
   is ten hours and a goal the prover cannot solve would simply sit there. *)
(*default overall timeout is 10 hours*)
val timeout_config =
      Attrib.setup_config_real \<^binding>\<open>prove_timeout\<close> (K (60.0 * 60.0 * 10.0))
      : real Config.T;

val limit_for_first_decrement =
      Attrib.setup_config_int \<^binding>\<open>limit_for_first_decrement\<close> (K 15): int Config.T;

val limit_for_other_decrement =
      Attrib.setup_config_int \<^binding>\<open>limit_for_other_decrement\<close> (K  5): int Config.T;


(* suggestion_target *)
(* Where a suggestion should be written, carried in the context rather than looked up where it
 * is needed.
 *
 * Proof_By_Abduction.write_suggestion_beside_theory derives the file from
 * Position.thread_data (), which is right only on the thread the command itself runs on. The
 * printer does not run there: the whole search is wrapped in with_memory_monitor's task and
 * forks freely, so by the time a suggestion exists, thread-local position data is whatever
 * that worker happens to carry - no file, and the write was silently skipped. Measured: a
 * "suggest" that ran for four and a half minutes and printed its script produced no .proof
 * file at all.
 *
 * The proof state is threaded through every one of those layers already, so its context is the
 * natural place to carry this. The command computes it once, on its own thread, where the
 * position is still trustworthy. Empty means "no file" - an unsaved buffer, or a caller that
 * never set it - and the write is then skipped, as before. *)
val suggestion_target =
      Config.declare_string ("suggestion_target", \<^here>) (K ""): string Config.T;

(* The file a suggestion made at this position belongs in: "Foo_line42.proof" beside "Foo.thy".
   Empty when the position carries no file, e.g. a buffer that has never been saved. *)
fun suggestion_target_for (pos: Position.T): string =
  case (Position.file_of pos, Position.line_of pos) of
    (SOME file, SOME line) =>
      let
        val path = Path.explode file;
        val base = Path.file_name (Path.base path);
        val stem =
          if String.isSuffix ".thy" base then String.substring (base, 0, size base - 4) else base;
      in
        Path.append (Path.dir path) (Path.basic (stem ^ "_line" ^ string_of_int line ^ ".proof"))
        |> Path.implode
      end
  | _ => "";

fun is_in (small:term) (big:term) =
  let
    fun is_in' (small':term) (big':term) =
      if small' = big'
      then true
      else case big' of
          Abs (_, _, middle) => is_in' small' middle
        | mid1 $ mid2 => is_in' small' mid1 orelse is_in' small' mid2
        | _ => false
  in
    is_in' (clean_type_of_term small) (clean_type_of_term big)
  end;

(*Names a proof file when no theory position is available - see write_proof_to_file.*)
val proof_file_counter = Unsynchronized.ref 0;

(* write_proof_to_file *)
(* A found proof is a result, not a message, and must not be droppable.
 *
 * The original wrote only beside the theory, and only when a target could be derived from
 * Position.thread_data - which belongs to the command's own thread and is absent on a worker. It
 * then returned unit in silence. Measured: of five goals proved by prove_by_abduction, one left a
 * file behind; four proofs were found, reported as successes and thrown away.
 *
 * That matters beyond evaluation. This is to run server-side, receiving goals and returning
 * proofs to a client, and a path that silently produces nothing is the one failure such a service
 * cannot have.
 *
 * Three destinations, tried in order, and a warning carrying the proof if none works:
 *   PSL_PROOF_OUTPUT_DIR - a directory, needing no position, which is what a server sets;
 *   the context's target - recorded while still on the command's thread;
 *   the thread position  - the original interactive behaviour.
 *
 * It lives here rather than in Proof_By_Abduction because the graph printer needs it too and sits
 * below that file; putting it beside suggestion_target, which it reads, is what lets both call it. *)
fun write_proof_to_file (ctxt: Proof.context) (script: string): unit =
  let
    val from_context = Config.get ctxt suggestion_target;
    val beside_theory =
      if from_context <> "" then from_context
      else suggestion_target_for (Position.thread_data ());
    val in_output_dir =
      case getenv "PSL_PROOF_OUTPUT_DIR" of
        "" => NONE
      | dir =>
          let
            val stem =
              if beside_theory <> "" then Path.file_name (Path.explode beside_theory)
              else "proof_" ^ string_of_int (Unsynchronized.inc proof_file_counter) ^ ".proof";
          in SOME (dir ^ "/" ^ stem) end;
    fun write_to path = is_some (try (File.write (Path.explode path)) (script ^ "\n"));
    val wrote_dir = case in_output_dir of NONE => false | SOME p => write_to p;
    val wrote_beside = beside_theory <> "" andalso write_to beside_theory;
  in
    if wrote_dir orelse wrote_beside then ()
    else warning ("AbductionProver found a proof but could not write it anywhere. Set \
                  \PSL_PROOF_OUTPUT_DIR to a writable directory to keep it. The proof follows.\n"
                  ^ script)
  end;

(* write_verdict *)
(* Whether the search proved the goal is a result, not a message, and it was reported only by
 * tracing - which Isabelle's batch build does not surface. So a harness had no way to read the
 * prover's own answer, and the evaluation run of 3-4 August fell back to grepping the build log
 * for Isabelle's "Finished <session>" line instead.
 *
 * That line says the THEORY COMPILED. "prove_by_abduction" is an Outer_Syntax.local_theory
 * command: it runs the search, discards the result, and returns its context unchanged whether or
 * not a proof was found, so the theory compiles either way. Every target that did not crash was
 * therefore recorded as PROVED - which is why two evaluations reported 14 of 15 and 18 of 20
 * proved while keeping 4 and 7 proof files, and why that gap was read as proofs being discarded.
 * Nothing was being discarded: docs/2026_08_04_overnight_eval.html and docs/2026_08_04_partial_proof_eval.html
 * were counting compiled theories. Note also that the converse does not hold either - an unproved
 * goal still writes a file, because a failed search emits the auxiliaries it did prove - so a
 * .proof file is not evidence of success. That is what this verdict is for.
 *
 * The verdict goes to the same channel as the proof itself (PSL_PROOF_OUTPUT_DIR) and for the
 * same reason given at write_proof_to_file: it is available on a worker thread and does not
 * depend on a position. Appended, so a run over many goals accumulates one file.
 *
 * The invariant "proved implies a proof file exists" is checked here because this is the one
 * place that knows both halves. It warns rather than fails: warning survives a batch build,
 * which is the property tracing lacked and this whole function exists to restore.
 *
 * "solve" is the exception, and needs write_verdict_applied instead. It does not emit a script at
 * all - it drives the caller's own Proof.state and closes the goal there - so for it the invariant
 * is not merely unmet but wrong, and checking it would warn on every successful run. Its rows say
 * "proved-applied" so a harness can tell the two apart rather than reading a legitimately absent
 * file as a lost proof, which is the exact confusion this whole mechanism exists to end. *)
(* The contract constants. Single-sourced here and used by every writer below, so the
   vocabulary a consumer greps cannot drift from the vocabulary we write. *)
val verdict_proved         = "proved";
val verdict_unproved       = "unproved";
val verdict_proved_applied = "proved-applied";
val verdict_refuted        = "refuted";
val verdicts_file_name     = "verdicts.csv";
val progress_file_suffix   = "_progress.thy";
val refutation_file_suffix = "_refutation.txt";

fun warn_if_proof_output_dir_unset (): unit =
  if getenv "PSL_PROOF_OUTPUT_DIR" <> "" then ()
  else
    let
      val harness_vars =
        ["PSL_SOLVE_TRACE", "PSL_MEMORY_MONITOR_LOG", "PSL_MEMORY_GUARD_TRIP_AFTER",
         "PSL_EVAL_TBC_PREPROCESS_ROUNDS", "PSL_EVAL_ATTEMPT_TIMEOUT",
         "PSL_EVAL_ATTEMPT_AUX_IN_FINAL_ROUND", "PSL_EVAL_USE_WORKER_POOL_LOOP"];
      val set_ones = filter (fn v => getenv v <> "") harness_vars;
    in
      if null set_ones then ()  (*plain interactive use: silence is correct*)
      else
        warning ("PSL_PROOF_OUTPUT_DIR is unset, so no verdicts.csv row and no progress\n\
                 \snapshot will be written for this search - but these harness variables are\n\
                 \set: " ^ commas set_ones ^ ". If a harness is driving, it is reading a\n\
                 \channel this run will never write.")
    end;

fun write_verdict_gen (expect_proof_file: bool) (ctxt: Proof.context) (solved: bool)
    (elapsed_sec: real): unit =
  case getenv "PSL_PROOF_OUTPUT_DIR" of
    "" => ()
  | dir =>
      let
        val theory_name = Context.theory_long_name (Proof_Context.theory_of ctxt): string;
        val verdict =
          (if not solved then verdict_unproved
           else if expect_proof_file then verdict_proved
           else verdict_proved_applied): string;
        (* This goal's own files, not the directory's. A run over many goals accumulates them all
           here, so counting the directory would let one goal's proof satisfy another goal's
           invariant - and would report a cumulative total as if it were this goal's. Proof files
           are named after the theory they came from; see write_proof_to_file. *)
        val stem_prefix = Context.theory_base_name (Proof_Context.theory_of ctxt): string;
        val proof_files =
          (case try (File.read_dir o Path.explode) dir of
             NONE => []
           | SOME entries =>
               filter (fn e => String.isSuffix ".proof" e andalso String.isPrefix stem_prefix e)
                 entries): string list;
        val line =
          theory_name ^ "," ^ verdict ^ "," ^ Real.toString elapsed_sec ^ ","
          ^ string_of_int (length proof_files) ^ "\n";
        val _ = try (File.append (Path.explode (dir ^ "/" ^ verdicts_file_name))) line;
      in
        if expect_proof_file andalso solved andalso null proof_files
        then warning ("AbductionProver reported the goal proved, but no .proof file exists in "
                      ^ dir ^ ". A found proof must not be lost; please report this.")
        else ()
      end;

(* For the commands that emit a script: prove, prove_by_abduction, suggest. *)
val write_verdict = write_verdict_gen true;

(* For solve, which applies the proof to the caller's state instead of emitting one. *)
val write_verdict_applied = write_verdict_gen false;

(* The refutation watchdog found a genuine counterexample to the root goal. A separate verdict
 * value rather than "unproved", because they call for different reactions: unproved says "try
 * a bigger budget or a better prover", refuted says "the statement is wrong, stop submitting
 * it". No proof-file invariant applies - nothing was meant to be written. The row shape stays
 * theory,verdict,elapsed,proof_files so existing readers keep parsing. *)
fun write_verdict_refuted (ctxt: Proof.context) (elapsed_sec: real): unit =
  case getenv "PSL_PROOF_OUTPUT_DIR" of
    "" => ()
  | dir =>
      let
        val theory_name = Context.theory_long_name (Proof_Context.theory_of ctxt): string;
        val stem_prefix = Context.theory_base_name (Proof_Context.theory_of ctxt): string;
        val proof_files =
          (case try (File.read_dir o Path.explode) dir of
             NONE => []
           | SOME entries =>
               filter (fn e => String.isSuffix ".proof" e andalso String.isPrefix stem_prefix e)
                 entries): string list;
        val line =
          theory_name ^ "," ^ verdict_refuted ^ "," ^ Real.toString elapsed_sec ^ ","
          ^ string_of_int (length proof_files) ^ "\n";
      in
        ignore (try (File.append (Path.explode (dir ^ "/" ^ verdicts_file_name))) line)
      end;

(* Root-refutation budgets. Larger than the one/two seconds the conjecture filter spends per
 * candidate (pst_n_conjecture_has_counterexample): there is exactly one root, a false root
 * wastes the entire prove_timeout, and the watchdog runs beside the search rather than in
 * front of it, so its budget costs no wall-clock on true goals.
 *
 * Measured against real refutable traffic (Heinzelmen webservice, 2026-08-09, nine
 * plausible-looking false statements - arithmetic, list identities, a sort, a filter):
 * quickcheck refuted nine of nine in 1.7-6.7s, median 2.4s, so its 10s default is validated;
 * nitpick was reached zero times, so its 30s stands on judgment, uncontradicted and untested
 * - it governs only goals quickcheck misses, which makes it a tail-risk setting rather than a
 * latency one. Narrowed from below the same day: with quickcheck disabled, nitpick landed
 * two of those goals in 8.3s and 10.1s - threefold headroom on goals of that size, though
 * still not the quickcheck-misses case the budget exists for. Calibrating it would need false goals with no small witness; a synthetic set
 * of those was considered and declined as unrepresentative (per-tool numbers now come from
 * <theory>_refutation.txt, so a future dataset can settle it without code change). *)
val refute_root_quickcheck_timeout =
      Attrib.setup_config_real \<^binding>\<open>refute_root_quickcheck_timeout\<close> (K 10.0)
      : real Config.T;

val refute_root_nitpick_timeout =
      Attrib.setup_config_real \<^binding>\<open>refute_root_nitpick_timeout\<close> (K 30.0)
      : real Config.T;

(* Five minutes: a web-facing manager that gives a search twenty minutes gets three or four
 * snapshots of usable auxiliary lemmas before it has to give up, without the report itself
 * costing anything measurable (it reads the synchronized graph and writes one small file). *)
val progress_report_interval =
      Attrib.setup_config_real \<^binding>\<open>progress_report_interval\<close> (K 300.0)
      : real Config.T;

fun is_only_in_subtrm_of (small:term) (subtrm:term) (big:term) =
  let
    val small'  = clean_type_of_term small;
    val subtrm' = clean_type_of_term subtrm;
    val big'    = clean_type_of_term big;
    fun is_only_in_subtrm_of' (big' as Abs (_, _, mid)) =
        if   subtrm' = big'
        then true
        else (is_only_in_subtrm_of' mid)
      | is_only_in_subtrm_of' (big' as mid1 $ mid2) =
        if subtrm' = big'
        then true
        else
            (if (is_only_in_subtrm_of' mid1) then true else not (is_in small' mid1))
          andalso
            (if (is_only_in_subtrm_of' mid2) then true else not (is_in small' mid2))
      | is_only_in_subtrm_of' atom = subtrm' = atom;
  in
            is_in small'  subtrm'
    andalso is_in subtrm' big'
    andalso is_only_in_subtrm_of' big'
  end;

fun is_compound (trm:term) = IU.is_Abs trm orelse IU.is_App trm: bool;

fun has_fvar_appearing_only_in_the_same_compound_trm (trm:term) =
(* this might be strictly more powerful than replace_redundant_compound_subtrm_with_free_var' *)
  let
  (*flatten ignores Abs.*)
    val subtrms = IU.flatten_trm trm |> map clean_type_of_term |> distinct (op =): terms;
    val compound_subtrms = filter is_compound subtrms: terms;
    val free_vars = filter is_Free subtrms: terms;
    fun fvar_appears_only_in_the_same_compound_trm (fvar:term) =
          exists (fn sub => is_only_in_subtrm_of fvar sub trm) compound_subtrms;
    val result = exists fvar_appears_only_in_the_same_compound_trm free_vars
  in
    result
  end

fun mk_pst_to_prove_from_term (pst:Proof.state) (term:term): Proof.state =
    let
      val ctxt    = Proof.context_of pst;
      val prop    = if is_prop term then term else HOLogic.mk_Trueprop term;
      val checked = clean_type_of_term prop |> Syntax.check_term ctxt: term;
      (*A fresh Proof.state has no chained facts, so restating here would drop whatever the
        caller chained in with "using"/"from". See TBC_Utils.inherit_chained_facts.*)
      val chained = these (try (#facts o Proof.goal) pst): thm list;
    in
      Proof.theorem NONE (K I) [[(checked, [])]] ctxt
      |> (if null chained then I else Proof.using_facts chained): Proof.state
    end;

fun non_prop_trm_to_dummy_eq (ctxt:Proof.context) (lhs:term) =
  let
    val new_free_var  = get_fresh_free_var_of_typ_in_trm ctxt dummyT lhs;
    val dummy_eq      = HOLogic.mk_eq (lhs, new_free_var);
    val dummy_eq_prop = HOLogic.mk_Trueprop dummy_eq;
    val checked_eq    = try (Syntax.check_prop ctxt) dummy_eq_prop;
    val dummy_cterm   = Option.map (Thm.cterm_of ctxt) checked_eq;
    val dummy_thm     = Option.map Thm.trivial dummy_cterm;
  in
    dummy_thm
  end;

fun simp_non_prop_term (ctxt:Proof.context) (trm:term) =
  let
    val dummy_thm            = non_prop_trm_to_dummy_eq ctxt trm: thm option;
    val simplifier           = Basic_Simplifier.asm_full_simplify ctxt
    val simped_dummy_thm     =
          Option.mapPartial (try (IU.timeout_apply (Time.fromSeconds 1) simplifier)) dummy_thm
          : thm option;
    val simped_fst_goal      = Option.map Thm.concl_of simped_dummy_thm: term option;
    val simped_fst_pair      =
          Option.mapPartial (try (HOLogic.dest_eq o HOLogic.dest_Trueprop)) simped_fst_goal
          : (term * term) option;
    val simped_lhs           = Option.map fst simped_fst_pair: term option;
    val possibly_simped_term = if is_some simped_lhs then the simped_lhs else trm: term;
  in
    possibly_simped_term: term
  end;

fun strip_outermost_meta_quantifier (trm as (quantifier $ abstraction)) =
   (case quantifier of
      Const ("Pure.all", _) => (case abstraction of
        Abs (var_name, var_type, _) =>
          (let
             val variable = Term.Free (var_name, var_type)
           in (true, Term.betapply (abstraction, variable))
           end)
      | _ => (false, trm))
    | _ => (false, trm))
  | strip_outermost_meta_quantifier trm = (false, trm);

fun strip_outermost_meta_quantifiers (trm:term) =
    let
      val (worked, res) = strip_outermost_meta_quantifier trm
    in
      if worked
      then
        strip_outermost_meta_quantifiers res
      else
        res
    end;

fun mk_extended_rhses
    (ctxt:Proof.context) (candidate_args:terms) (candidate_func as Const _:term): terms =
  let
    val candidate_func_wo_type_consts = IU.strip_atyp candidate_func             : term;
    val candidate_args_wo_type_consts = map IU.strip_atyp candidate_args         : terms;
    val arg_numb                      = type_of candidate_func |> Term.binder_types |> length: int;
    fun mk_rhses (n:int) (partial_cnjct:term) =
      if n > 0
      then
        let
          val unchecked_partial_terms =
                map (fn arg => partial_cnjct $ arg) candidate_args_wo_type_consts: terms;
          val checked_partial_terms        = check_terms ctxt unchecked_partial_terms: terms;
          val partial_terms_wo_type_consts = map IU.strip_atyp checked_partial_terms: terms;
          val result =
                map (mk_rhses (n-1)) partial_terms_wo_type_consts |> flat: terms;
        in
          result
        end
      else [partial_cnjct];
    val rhses = mk_rhses arg_numb candidate_func_wo_type_consts: terms;
    val rhses_wo_type_consts = map IU.strip_atyp rhses: terms;
    val simped_rhses = map (simp_non_prop_term ctxt) rhses_wo_type_consts;
    val rhses_wo_duplications =  distinct (op =) simped_rhses: terms;
  in
    rhses_wo_duplications |> map IU.strip_atyp
  end
  | mk_extended_rhses _ _ _ = [];

fun replace_redundant_compound_subtrm_with_free_var' (ctxt:Proof.context) (lhs, rhs) =
  let
    val ((*func*)_, args) = strip_comb lhs: (term * terms);
    val fvars_in_rhs = IU.get_free_var_names_in_trm rhs: strings;
    fun in_rhs (fvar_name:string) = exists (equal fvar_name) fvars_in_rhs: bool;
    fun has_fvar_that_is_not_in_rhs (arg:term) =
      let
        val fvar_names_in_arg = IU.get_free_var_names_in_trm arg: strings;
        val result = forall (fn fvar_in_arg => not (in_rhs fvar_in_arg)) fvar_names_in_arg: bool;
      in
        result
      end;
    val compound_args = filter (fn arg => IU.is_Abs arg orelse IU.is_App arg) args: terms;
    val args_to_be_abstracted = filter has_fvar_that_is_not_in_rhs compound_args;
    val numb_of_args_to_be_abstracted = length args_to_be_abstracted: int
    val fresh_free_vars =
          get_fresh_free_vars_of_typ_in_trm ctxt dummyT (lhs $ rhs) numb_of_args_to_be_abstracted
          : terms;
    val subst = subst_free (args_to_be_abstracted ~~ fresh_free_vars)
    val new_lhs = subst lhs: term;
  in
    (new_lhs, rhs)
  end;

fun replace_redundant_compound_subtrm_with_free_var ctxt (lhs, rhs) =
   replace_redundant_compound_subtrm_with_free_var' ctxt (lhs, rhs)
|> swap
|> replace_redundant_compound_subtrm_with_free_var' ctxt
|> swap;

fun parallel_filter_in_or_out (filter_in:bool) (condition:'a -> bool) (xs:'a list) =
  let
    val bools          = Par_List.map condition xs: bool list;
    val pairs          = xs ~~ bools              : ('a * bool) list;
    val filtered_pairs = if filter_in
                         then filter     snd pairs
                         else filter_out snd pairs: ('a * bool) list;
    val result         = map fst filtered_pairs   : 'a list;
  in
    result
  end;

fun parallel_filter (condition:'a -> bool) (xs:'a list) =
      parallel_filter_in_or_out true condition xs;
fun parallel_filter_out (condition:'a -> bool) (xs:'a list) =
      parallel_filter_in_or_out false condition xs;

val isPrefix = String.isPrefix;

fun is_template_based (name:string) =
    isPrefix "abduced_lemma_associativity"           name orelse
    isPrefix "abduced_lemma_identity"                name orelse
    isPrefix "abduced_lemma_invertibility"           name orelse
    isPrefix "abduced_lemma_commutativity"           name orelse
    isPrefix "abduced_lemma_idempotent_element"      name orelse
    isPrefix "abduced_lemma_idempotency"             name orelse
    isPrefix "abduced_lemma_zero_element"            name orelse
    isPrefix "abduced_lemma_distributivity"          name orelse
    isPrefix "abduced_lemma_ant_distributivity"      name orelse
    isPrefix "abduced_lemma_homomorphism_2"          name orelse
    isPrefix "abduced_lemma_transitivity"            name orelse
    isPrefix "abduced_lemma_symmetry"                name orelse
    isPrefix "abduced_lemma_connexity"               name orelse
    isPrefix "abduced_lemma_reflexivity"             name orelse
    isPrefix "abduced_lemma_involution"              name orelse
    isPrefix "abduced_lemma_square_root"             name orelse
    isPrefix "abduced_lemma_idempotence"             name orelse
    isPrefix "abduced_lemma_swap_constructor"        name orelse
    isPrefix "abduced_lemma_swap_unary"              name orelse
    isPrefix "abduced_lemma_composite_commutativity" name;

end;