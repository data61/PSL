(*  Title:      PGT/PGT.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

This file presents the functions for automatic generalization of tactics.
*)

(* Utility functions *)
val typs_to_dummyT = Term.map_types (K dummyT);
val atyps_to_dummyT = Term.map_types (Term.map_atyps (K dummyT));

(* How to create new subgoal? *)
fun generalize_trm (ctxt:Proof.context) (original:term) (subtrm:term) =
   Logic.all subtrm (HOLogic.mk_Trueprop original)
|> atyps_to_dummyT
|> Syntax.check_term ctxt;

(* How to print new subgoals? *)
fun trm_to_string (ctxt:Proof.context) (trm:term) =  Syntax.string_of_term ctxt trm
 |> YXML.parse_body
 |> XML.content_of : string;

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
   applying fastforce. *)

(* How to create a subgoal_tac? *)
fun generalize (ctxt:Proof.context) (goal:thm) =
 if Isabelle_Utils.get_1st_subg goal |> is_none then [] else 
 let
   val fst_subg = Isabelle_Utils.get_1st_subg goal |> the: term;
   val dup_subtrms = get_subtrms fst_subg |> duplicates (op =): term list;
   val conjectures = map (generalize_trm ctxt fst_subg) dup_subtrms: term list;
   val cnjct_strs  = map (trm_to_string ctxt) conjectures: string list;
   val subgoals    = map (fn x => " \"" ^ x ^ "\"") cnjct_strs;
 in
   subgoals:string list
 end;

(* How to apply quickcheck to a raw thm? *)
(* No, I only apply quickcheck after applying fastforce. 
   So, I can use quickcheck as part of PSL strategies. *)