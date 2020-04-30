(*  Title:      PGT/PGT.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file presents the functions for automatic generalization of tactics.
*)

signature PROOF_GOAL_TRANSFORMER =
sig

val generalize_str : Proof.context -> thm -> string list;
val conjecture_strs: Proof.context -> thm -> string list;

end;

structure Proof_Goal_Transformer: PROOF_GOAL_TRANSFORMER =
struct

(* Utility functions *)
(*TODO: move these utility functions to Isabelle_Util*)
val typs_to_dummyT = Term.map_types (K dummyT);
val atyps_to_dummyT = Term.map_types (Term.map_atyps (K dummyT));

(* How to get the list of subterms? *)
fun get_subtrms (Const p:term) = [Const p]
 |  get_subtrms (Free p:term) = [Free p]
 |  get_subtrms (Var p:term) = [Var p]
 |  get_subtrms (Bound i) = [Bound i]
 |  get_subtrms (trm as Abs (_, _, sub)) = trm :: get_subtrms sub
 |  get_subtrms (trm as trm1 $ trm2) = trm :: get_subtrms trm1 @ get_subtrms trm2;

(* How to get the maximum de-Bruijn index? *)
fun max_opt (NONE, NONE) = NONE
 |  max_opt (SOME i, NONE) = SOME i
 |  max_opt (NONE, SOME i) = SOME i
 |  max_opt (SOME i, SOME j) = SOME (Int.max (i, j));
fun get_max_Bound (Bound i) = SOME i
 |  get_max_Bound (Abs (_,_,trm)) = get_max_Bound trm
 |  get_max_Bound (trm1 $ trm2) = apply2 get_max_Bound (trm1, trm2) |> max_opt
 |  get_max_Bound _ = NONE;
(*TODO: handle nested \<And>s.*)

(* How to generalize a term using a sub-term? *)
fun is_prop  (trm1 $ trm2:term) = is_prop trm1 orelse is_prop trm2
 |  is_prop  (Abs (_, _, trm)) = is_prop trm
 |  is_prop  (trm as Const _) = trm = HOLogic.Trueprop
 |  is_prop _ = false;

fun generalize_trm (ctxt:Proof.context) (original:term) (subtrm:term) =
   Logic.all subtrm (if is_prop original then original else HOLogic.mk_Trueprop original)
|> atyps_to_dummyT
|> Syntax.check_term ctxt;

(* How to print new subgoals? *)
fun trm_to_string (ctxt:Proof.context) (trm:term) =  Syntax.string_of_term ctxt trm
 |> YXML.parse_body
 |> XML.content_of : string;

(* How to create a proof obligation from a term? *)
fun trm_to_thm (ctxt:Proof.context) (trm:term) =
  let
    val prop = if is_prop trm then trm else HOLogic.mk_Trueprop trm;
    val ctrm = Thm.cterm_of ctxt prop;
    val thm  = Goal.init ctrm;
  in thm end;
(* Now, this question is not meaningful, because I am not going to apply quick-check only after
   applying fastforce within the same atomic step. *)

(* How to create a subgoal_tac? *)
fun generalize (ctxt:Proof.context) (goal:thm) =
 if Isabelle_Utils.get_1st_subg goal |> is_none then [] else 
 let
   val fst_subg     = Isabelle_Utils.get_1st_subg goal |> the: term;
   val consts       = Term.add_consts fst_subg [] |> map Const;
   val dup_subtrms  = get_subtrms fst_subg |> duplicates (op =): term list;
   val abstracteds  = distinct (op =) (consts @ dup_subtrms): term list;
   val generalizeds = map (generalize_trm ctxt fst_subg) abstracteds: term list;
 in
   generalizeds : term list
 end;

fun generalize_str (ctxt:Proof.context) (goal:thm) =
 if Isabelle_Utils.get_1st_subg goal |> is_none then [] else 
 let
   val generalizeds = generalize ctxt goal: term list;
   val gen_strs     = map (trm_to_string ctxt) generalizeds: string list;
   val subgoals     = map (fn x => " \"" ^ x ^ "\"") gen_strs;
 in
   subgoals:string list
 end;

(* How to apply quickcheck to a raw thm? *)
(* No, I only apply quickcheck after applying fastforce. 
   So, I can use quickcheck as part of PSL strategies. *)

fun get_max' (xs:int list) = fold (curry Int.max) xs;
fun get_max xs = get_max' xs 0;

(* How to measure how many arguments a function should take? *)
fun typ_to_arg_numb (Type (name, typs)) = if name = "fun" then 1 + get_max (map typ_to_arg_numb typs) else 0
 |  typ_to_arg_numb _ = 0

val trm_to_arg_numb = typ_to_arg_numb o type_of;

(* How to replace sub-terms? *)
fun replace_with (trm:term) (subterm:term) (new:term) =
  let
    val new_dummyT = atyps_to_dummyT new;
    fun repl (trm as Abs (name, typ, in_trm):term) subt = if trm = subt then new_dummyT else Abs (name, typ, repl in_trm subt)
     |  repl (trm as trm1 $ trm2:term) (subt:term) = if trm = subt then new_dummyT else repl trm1 subt $ repl trm2 subt
     |  repl (atomic_trm:term) (subt:term) = if atomic_trm = subt then new_dummyT else atomic_trm;
  in
    repl (atyps_to_dummyT trm) (atyps_to_dummyT subterm)
  end;

(* How to create a new term from a function, a term, and the maximum de-Bruijn index? *)
fun get_new_trms' (func as Const _) (subt:term) (max_bound:int) =
  let
    (*I have to add 1 because max_bound is 0 for \<And>x. x.*)
    val bounds = List.tabulate (max_bound + 1, I):int list;
    val arg_numb = trm_to_arg_numb func: int;
    fun mk_trm (n:int) (cnjct:term) =
      if n > 0
      then
        let
          fun combine (head_trm:term) (new:term) = head_trm $ new: term ;
          val with_subterm = combine cnjct subt: term;
          val with_Bounds  = map (fn i => combine cnjct (Bound i)) bounds: term  list;
          val partial_trms = with_subterm :: with_Bounds: term list;
        in
           map (mk_trm (n-1)) partial_trms |> flat
        end
      else [cnjct];
  in
    mk_trm arg_numb func
  end
 |  get_new_trms' (_:term) (_:term) (_:int) = [];

fun get_new_trms (orig_trm:term) (subtrm:term) (func:term) : term list =
  let
    val some_max_Bound = get_max_Bound orig_trm: int option;
    val new_subtrms = if is_none some_max_Bound then []
      else get_new_trms' func subtrm (the some_max_Bound);
  in
    map (replace_with orig_trm subtrm) new_subtrms |> distinct (op =): term list
  end;

(* How can I find a list of constants used in the definitions of the constants appearing in a term? *)
fun get_consts_to_conjecture (ctxt:Proof.context) (trm:term) =
let
  val cnames_in_trm = Isabelle_Utils.get_cnames_in_trm trm: string list;
  val simp_rules = map (Find_Theorems2.get_thms_of_name_with_suffix ctxt "simps") cnames_in_trm |> flat;
  val consts_to_conjecture = map Isabelle_Utils.get_consts_in_thm simp_rules |> flat |> distinct (op =);
in
  consts_to_conjecture : term list
end;

(* How to conjecture a new term from a term and its background context? *)
fun conjecture (ctxt:Proof.context) (orig_trm: term) =
  let
    val consts = get_consts_to_conjecture ctxt orig_trm: term list;
    fun map_conj (term:term) = map (get_new_trms orig_trm term) consts |> flat;
    fun cnjct (trm as Abs (_, _, subtrm): term) = map_conj trm @ cnjct subtrm
     |  cnjct (trm as trm1 $ trm2: term) = map_conj trm @ cnjct trm1 @ cnjct trm2
     |  cnjct (trm:term) = map_conj trm;
    val unchecked = cnjct orig_trm: term list
    val checked = List.mapPartial ((try o Syntax.check_term) ctxt) unchecked: term list;
  in
    checked
  end;

fun conjecture_strs (ctxt:Proof.context) (goal:thm) =
 if Isabelle_Utils.get_1st_subg goal |> is_none then [] else
 let
   val fst_subg       = Isabelle_Utils.get_1st_subg goal |> the: term;
   val generalizeds   = generalize ctxt goal: term list;
   val conjectures    = map (conjecture ctxt) (fst_subg::generalizeds) |> flat |> distinct (op =): term list;
   val checked_cnjcts = List.mapPartial ((try o Syntax.check_term) ctxt) conjectures: term list;
   val cnjct_strs     = map (trm_to_string ctxt) checked_cnjcts: string list;
   val subgoals       = map (fn x => " \"" ^ x ^ "\"") cnjct_strs;
   val _ = tracing ("PGT creates " ^ Int.toString (length subgoals) ^ " conjectures.");
 in
   subgoals:string list
 end;

end;