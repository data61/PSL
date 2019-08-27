theory IMP2_Utils
imports Main
begin

  ML \<open>
    (*
      Explicit refinement of goal state, deterministic and with error messages.
      
      TODO:
        Add functions to extract subgoals, prove them externally, and then discharge them.
          This is currently done by hand in recursive_spec command   
        
    *)
    structure Det_Goal_Refine : sig
      (* Apply tactic *)
      val apply: string -> tactic -> thm -> thm
      
      (* Apply tactic to first goal *)
      val apply1: string -> (int -> tactic) -> thm -> thm
      
      (* Apply tactic on goal obtained from theorem *)
      val apply_on_thm: string -> tactic -> thm -> thm
      
      (* Extract first element from seq, error message if empty *)
      val seq_first: string -> 'a Seq.seq -> 'a
    end = struct
      fun seq_first msg seq = case Seq.pull seq of 
        NONE => error (if msg="" then "Empty result sequence" else msg) 
      | SOME (x,_) => x
      
      fun apply msg (tac:tactic) = tac #> seq_first msg
      fun apply1 msg tac = apply msg (HEADGOAL tac)
    
      fun apply_on_thm msg tac thm = Goal.protect (Thm.nprems_of thm) thm |> apply msg tac |> Goal.conclude
    end
  
  
  
  \<close>

  ML \<open>
    (*
      ML-level interface to option datatype. 
      
      I would have expected this in HOLogic, but it isn't there!
    *)
    structure HOLOption : sig
      val mk_None: typ -> term
      val mk_Some: term -> term
      val mk_optionT: typ -> typ
      
      val mk_fun_upd: term * term -> term -> term
      
      val mk_map_empty: typ -> typ -> term
      val mk_map_sng: term * term -> term
      val mk_map_upd: term * term -> term -> term
      val mk_map_list: typ -> typ -> (term * term) list -> term
    end = struct
      fun mk_fun_upd (x,y) f = let
        val xT = fastype_of x
        val yT = fastype_of y
      in
        Const (@{const_name Fun.fun_upd}, (xT-->yT) --> xT --> yT --> (xT --> yT))$f$x$y
      end
    
      fun mk_optionT T = Type(@{type_name option},[T])
      fun mk_Some x = Const (@{const_name Option.Some},fastype_of x --> mk_optionT (fastype_of x))$x
      fun mk_None T = Const (@{const_name Option.None}, mk_optionT T)
      
      fun mk_map_upd (k,v) m = mk_fun_upd (k,mk_Some v) m
      fun mk_map_empty K V = Abs ("uu_",K,mk_None V)
    
      fun mk_map_list K V kvs = fold mk_map_upd kvs (mk_map_empty K V)
      
      fun mk_map_sng (k,v) = mk_map_upd (k,v) (mk_map_empty (fastype_of k) (fastype_of v))
    end
  
  \<close>

  ML \<open>
    (*
      Application of rules (thm -> thm) to premises of subgoals
    *)
    structure Thm_Mapping : sig
      val thin_fst_prem_tac: Proof.context -> int -> tactic
      val thin_fst_prems_tac: int -> Proof.context -> int -> tactic
    
      type rule = Proof.context -> thm -> thm
      
      (* Map first premises with respective rules *)
      val map_prems_tac: rule list -> Proof.context -> int -> tactic
      (* Map all premises with rule *)
      val map_all_prems_tac: rule -> Proof.context -> int -> tactic
      
      (* Apply ith rule to ith thm *)
      val map_thms: Proof.context -> rule list -> thm list -> thm list
    end = struct

      type rule = Proof.context -> thm -> thm
        
      fun thin_fst_prem_tac ctxt i = DETERM (eresolve_tac ctxt [Drule.thin_rl] i)
      
      fun thin_fst_prems_tac 0 _ _ = all_tac
        | thin_fst_prems_tac n ctxt i = thin_fst_prem_tac ctxt i THEN thin_fst_prems_tac (n-1) ctxt i
      
      fun map_prems_tac fs ctxt = SUBGOAL (fn (t,i) => let
        val nprems = length (Logic.strip_assums_hyp t)
      in (
          Subgoal.FOCUS_PREMS (fn {context=ctxt, prems, ...} => HEADGOAL (
            Method.insert_tac ctxt (map (fn (f,prem) => f ctxt prem) (fs~~take (length fs) prems))
          )) ctxt
          THEN' thin_fst_prems_tac (length fs) ctxt
          THEN' rotate_tac (nprems - length fs)
        ) i
      end)
    
      fun map_all_prems_tac f ctxt = SUBGOAL (fn (t,i) => let
        val n = length (Logic.strip_assums_hyp t)
      in map_prems_tac (replicate n f) ctxt i end)
       
      fun map_thms ctxt rls thms = rls ~~ thms
        |> map (fn (rl,thm) => rl ctxt thm)
  
  
    end
  \<close>
  
  
  ML \<open>
    infix 0 RS_fst

    (* Resolve with first matching rule
    
      Common idiom: thm RS_fst [\<dots>,asm_rl] to keep original thm if no other rule matches
     *)  
    fun _ RS_fst [] = error "RS_fst"
      | thma RS_fst (thm::thms) = case try (op RS) (thma,thm) of
          SOME thm => thm
        | NONE => thma RS_fst thms  
  
  \<close>



end
