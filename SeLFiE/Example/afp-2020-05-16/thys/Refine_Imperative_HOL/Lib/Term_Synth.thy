section \<open>Rule-Based Synthesis of Terms\<close>
theory Term_Synth
imports Sepref_Misc
begin
  definition SYNTH_TERM :: "'a::{} \<Rightarrow> 'b::{} \<Rightarrow> bool"
    \<comment> \<open>Indicate synthesis of @{term y} from @{term x}.\<close>
    where [simp]: "SYNTH_TERM x y \<equiv> True"
  consts SDUMMY :: "'a :: {}"
    \<comment> \<open>After synthesis has been completed, these are replaced by fresh schematic variable\<close>

  named_theorems_rev synth_rules \<open>Term synthesis rules\<close>

  text \<open>Term synthesis works by proving @{term "SYNTH_TERM t v"}, by repeatedly applying the 
    first matching intro-rule from \<open>synth_rules\<close>.  \<close>


ML \<open>
  signature TERM_SYNTH = sig
    (* Synthesize something from term t. The initial list of theorems is
      added to beginning of synth_rules, and can be used to install intro-rules
      for SYNTH_TERM.*)
    val synth_term: thm list -> Proof.context -> term -> term
  end


  structure Term_Synth : TERM_SYNTH = struct

    (* Assumption: Term does not contain dummy variables *)
    fun replace_sdummies t = let
      fun r (t1$t2) n = let
              val (t1,n) = r t1 n
              val (t2,n) = r t2 n
            in (t1$t2,n) end
        | r (Abs (x,T,t)) n = let
              val (t,n) = r t n
            in (Abs (x,T,t),n) end
        | r @{mpat (typs) "SDUMMY::?'v_T"} n = (Var (("_dummy",n),T),n+1)
        | r (t' as (Var ((name,_),_))) n = if String.isPrefix "_" name then raise TERM ("replace_sdummies: Term already contains dummy patterns",[t',t]) else (t',n)
        | r t n = (t,n)
    in
      fst (r t 0)
    end    

    (* Use synthesis rules to transform the given term *)
    fun synth_term thms ctxt t = let
      val orig_ctxt = ctxt
      val (t,ctxt) = yield_singleton (Variable.import_terms true) t ctxt
      val v = Var (("result",0),TVar (("T",0),[]))
      val goal = @{mk_term "Trueprop (SYNTH_TERM ?t ?v)"} |> Thm.cterm_of ctxt
  
      val rules = thms @ Named_Theorems_Rev.get ctxt @{named_theorems_rev synth_rules}
        |> Tactic.build_net
      fun tac ctxt = ALLGOALS (TRY_SOLVED' (
        REPEAT_DETERM' (CHANGED o resolve_from_net_tac ctxt rules)))
      
      val thm = Goal.prove_internal ctxt [] goal (fn _ => tac ctxt)

      val res = case Thm.concl_of thm of
          @{mpat "Trueprop (SYNTH_TERM _ ?res)"} => res 
        | _ => raise THM("Synth_Term: Proved a different theorem?",~1,[thm])

      val res = singleton (Variable.export_terms ctxt orig_ctxt) res
        |> replace_sdummies
  
    in
      res
    end
  end  
\<close>



end
