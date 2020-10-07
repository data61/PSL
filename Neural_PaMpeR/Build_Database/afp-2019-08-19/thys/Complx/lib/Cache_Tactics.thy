(*
 * Copyright 2016, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Cache_Tactics
imports Main
begin

ML \<open>
signature CACHE_TACTICS =
sig

type cache_id = int

val new_subgoal_cache: unit -> cache_id
val SUBGOAL_CACHE: cache_id -> (term * int -> tactic) -> int -> tactic
val clear_subgoal_cache: cache_id -> unit
val cacheify_tactic:
  int -> (Proof.context * (cache_id list) -> int -> tactic) ->
  Proof.context -> int -> tactic

val PARALLEL_GOALS_CACHE: cache_id -> tactic -> tactic

end;

\<close>

ML\<open>

structure Cache_Tactics: CACHE_TACTICS =
struct
type cache_id = int
(* Stateful cache of intermediate tactic results.
   
   USE WITH CARE: Each "function" (pair of function and configuration parameters)
   needs a unique cache.

   Some more experiments with which sub-caches
   get the best speedup?
*)             

val caches = Synchronized.var "caches" ((~1,[]) : int * ((int * (thm option Termtab.table)) list))

fun new_subgoal_cache () = Synchronized.change_result caches 
      (fn (maxidx,cache_list) => ( 
      (maxidx,(maxidx + 1,(maxidx,Termtab.empty) :: cache_list))))

fun SUBGOAL_CACHE id (tac : (term * int) -> tactic) i st = 
CSUBGOAL (fn (prem,i) =>
  (fn st =>
   let
      val tab = case (AList.lookup (op =) (Synchronized.value caches |> snd) id)
      of SOME x => x | NONE => error "Missing cache"

      val pprem = Thm.term_of prem;
      val othm = 
        (case (Termtab.lookup tab pprem)
          of SOME (othm) => othm
            | NONE => 
               let
                val othm = Option.map fst (Seq.pull (tac (pprem,1) (Goal.init prem)))
                val _ = Synchronized.change caches (fn (maxidx,nets) =>
                        (maxidx,AList.map_entry (op =) id
                            (Termtab.update (pprem,othm)) nets))
               in
                othm
               end)
      
   in
      case othm of
      SOME thm => Thm.bicompose NONE {flatten = false, match = false, incremented = false}
        (false, Goal.conclude thm, Thm.nprems_of thm) i st
     | NONE => Seq.empty
   end)

      
  ) i st


fun clear_subgoal_cache id = Synchronized.change caches
  (fn (maxidx,cache_list) => (maxidx,AList.delete (op =) id cache_list))

local

val pcaches = Synchronized.var "pcaches" ([] : ((int * (term Termtab.table)) list))

val (_,cache_oracle) = Context.>>> (Context.map_theory_result (Thm.add_oracle (@{binding "cache"},I)))

exception FAILED of unit;

fun retrofit st' =
  rotate_prems ~1 #>
  Thm.bicompose NONE {flatten = false, match = false, incremented = false}
      (false, Goal.conclude st', Thm.nprems_of st') 1;

in

fun PARALLEL_GOALS_CACHE cache_id tac = if cache_id < 0 then 
  (Synchronized.change pcaches (AList.map_default (op =) (~cache_id,Termtab.empty) (K Termtab.empty));PARALLEL_GOALS tac) else
  Thm.adjust_maxidx_thm ~1 #>
  (fn st =>
    if not (Future.enabled ()) orelse Thm.maxidx_of st >= 0 orelse Thm.nprems_of st <= 1
    then DETERM tac st
    else
      let
         val tab = Synchronized.change_result pcaches (fn caches =>
              case (AList.lookup (op =) caches cache_id) of SOME net => (net,caches)
                | NONE => (Termtab.empty,(AList.update (op =) (cache_id,Termtab.empty) caches)))

        fun do_cache p result = 
        let
          val cresult = Thm.global_cterm_of (Thm.theory_of_cterm p) result
        in
          try cache_oracle cresult
        end

        fun try_cache (i,p) (cached,uncached)  = case (Termtab.lookup tab (Thm.term_of p))
        of SOME result => (case do_cache p result of SOME thm => ((i,thm) :: cached,uncached)
                                                    | NONE => (cached, (i,p) :: uncached))
        | NONE => (cached,(i,p) :: uncached)

        fun try_tac (i,p) = 
          (case SINGLE tac (Goal.init p) of
            NONE => raise FAILED ()
          | SOME g' => (i,g'))

        val goals = Drule.strip_imp_prems (Thm.cprop_of st);
        val (cached,uncached) = fold try_cache (goals |> tag_list 0) ([],[])

        val results = Par_List.map (`try_tac) uncached;

        val _ = Synchronized.change pcaches (
          AList.map_default (op =) (cache_id,Termtab.empty)
            (fold (fn ((_,result),(_,goal))  =>
               Termtab.update (Thm.term_of goal,Thm.prop_of result)
             ) results))
        
        val _ = if null cached then () 
          else (warning 
          ("WARNING: Used cached result for PARALLEL_GOALS_CACHE.\n" ^
          "Give ~x to clear cache x and ensure correctness."))
         
        val full_results = (map fst results) @ cached |> order_list;

      in EVERY (map retrofit (rev full_results)) st end
      handle FAILED () => Seq.empty);

fun cacheify_tactic n tac ctxt i st =
  let
    val caches = List.tabulate (n, fn _ => new_subgoal_cache ());
    fun clear_caches _ = app clear_subgoal_cache caches ;
  in
      st |>
      (tac (ctxt,caches) i
      THEN (PRIMITIVE Drule.implies_intr_hyps)
      THEN (PRIMITIVE (fn thm => (clear_caches ();thm))))
      
  end


end;

end;
\<close>

end
