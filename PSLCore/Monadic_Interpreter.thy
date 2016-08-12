(* This file is the core of PSL.
 * This file provides the skeleton of PSL.
 * Monadic_Interpreter_Params flesh out this skeleton with concrete evaluation functions. *)
theory Monadic_Interpreter
imports 
  "../Category/Category"
  "../Category/Seq"
  "../Category/Strings"
  "../Category/State"
  "../Category/Writer"
  "../Runtime/Dynamic_Utils"
begin

text{* tactic as data-type*}

ML{* signature MONADIC_INTERPRETER =
sig
  include TMONAD_0PLUS
  datatype prim_tac = (* default tactics     *) CClarsimp | CSimp | CFastforce | CAuto | CInduct |
                                                CCase | CRule | CErule |
                      (* diagnostic commands *) CHammer |
                      (* assertion tactics   *) CIs_Solved | CQuickcheck | CNitpick |
                      (* special purpose     *) CDefer;
  datatype para_tac = CPara_Clarsimp
                    | CPara_Simp
                    | CPara_Fastforce
                    | CPara_Induct
                    | CPara_Rule
                    | CPara_Erule;
  type atom_tac;
  datatype atom_tactical = CSolve1 | CRepeatN;
  type core_tac;
  type 'a stttac;
  type 'a params;
  type 'a interpret = 'a params -> core_tac -> 'a stttac;
  datatype tac =
  (* prim_tac *)
    Clarsimp
  | Simp
  | Fastforce
  | Auto
  | Induct
  | Case
  | Rule
  | Erule
  (* diagnostic command *)
  | Hammer
  (* assertion tactic / diagnostic command *)
  | Is_Solved
  | Quickcheck
  | Nitpick
  (* special purpose *)
  | Defer
  (* para_tac *)
  | Para_Clarsimp
  | Para_Simp
  | Para_Fastforce
  | Para_Induct
  | Para_Rule
  | Para_Erule
  (* monadic tactical *)
  | Skip
  | Fail
  | Seq of tac Seq.seq
  | Alt of tac Seq.seq
  (* non-monadic tacticals that have dedicated clauses in "inter".*)
  | RepBT of tac
  | RepNB of tac
  | Fails of tac
  | Or of tac Seq.seq
  (* non-monadic tacticals that are syntactic sugar.*)
  | Try of tac
  (* non-monadic tacticals that are handled by "eval_tactical".*)
  | Solve1 of tac
  | RepNT of tac   (* Repeat n times.*)
  (* parallel tactical *)
  | PAlt of (tac * tac)
  | POr  of (tac * tac);
  val interpret : 'a interpret;
  val desugar : tac -> core_tac;
end;
*}

ML{* functor mk_Monadic_Interpreter (mt0p : TMONAD_0PLUS) : MONADIC_INTERPRETER =
struct
  open mt0p;
  datatype prim_tac = CClarsimp | CSimp | CFastforce | CAuto | CInduct | CCase | CRule | CErule
                    | CIs_Solved | CQuickcheck | CNitpick
                    | CHammer | CDefer;
  datatype para_tac = CPara_Clarsimp
                    | CPara_Simp
                    | CPara_Fastforce
                    | CPara_Induct
                    | CPara_Rule
                    | CPara_Erule;
  datatype combine = Unique | First;
  datatype atom_tac = CPrim of prim_tac | CPara of para_tac;
  (* atom_tacticals have no monadic-interpretation.*)
  datatype atom_tactical = CSolve1 | CRepeatN;
  infix 0 CSeq CAlt  COr CPAlt CPOr;
  datatype core_tac =
    CAtom of atom_tac
  | CSkip
  | CFail
  | CTry      of core_tac
  | COr       of (core_tac * core_tac)
  | CPOr      of (core_tac * core_tac)
  | CSeq      of (core_tac * core_tac)
  | CAlt      of (core_tac * core_tac)
  | CPAlt     of (core_tac * core_tac)
  | CRepBT    of core_tac
  | CRepNB    of core_tac
  | CFails    of core_tac (* Fails cannot be defined as just a syntactic sugar as the definition(desugaring) involves (goal:thm).*)
  | CTactical of (atom_tactical * core_tac list);
  type 'a stttac        = 'a -> 'a monad;
  type 'a eval_prim     = prim_tac -> 'a stttac;
  type 'a eval_para     = para_tac -> 'a -> 'a stttac Seq.seq;
  type 'a eval_tactical = atom_tactical * 'a stttac list -> 'a stttac;
  type 'a equal         = 'a monad -> 'a monad -> bool;
  type 'a iddfc         = int -> (atom_tac -> 'a stttac) -> (atom_tac -> 'a stttac);
  type depths           = (int * int);
  type 'a params        = ('a eval_prim * 'a eval_para * 'a eval_tactical * 'a equal * 'a iddfc * depths);
  type 'a interpret     = 'a params -> core_tac -> 'a stttac;

  (* interpret function similar to that of "A Monadic Interpretation of Tactics" by A. Martin et. al.*)
  (* (-`\<omega>-) *)
  fun interpret (eval_prim, eval_para, eval_tactical, m_equal, iddfc, (n_deepenings, n_steps_each)) (tac:core_tac) goal =
    let
       fun is_mzero monad        = m_equal monad mzero;
       fun eval (CPrim tac) goal = eval_prim tac goal
         | eval (CPara tac) goal =
           let
             (* should I factor this out to Monadic_Interpreter_Params ? *)
             fun how_to_combine_results CPara_Clarsimp  = Unique
              |  how_to_combine_results CPara_Simp      = Unique
              |  how_to_combine_results CPara_Fastforce = First
              |  how_to_combine_results CPara_Induct    = Unique
              |  how_to_combine_results CPara_Rule      = Unique
              |  how_to_combine_results CPara_Erule     = Unique;
             fun rm_useless First  results =
               (Seq.filter (not o is_mzero) results |> Seq.hd handle Option.Option => mzero)
              |  rm_useless Unique results = distinct (uncurry m_equal) (Seq.list_of results)
                                            |> Seq.of_list |> msum;
             val combination          = how_to_combine_results tac;
             val tactics              = eval_para tac goal;
             (* Sometimes, Isabelle does not have appropriate rules.*)
             val tactics_with_handler = Seq.map (fn tactic => fn g => tactic g handle ERROR _ => mzero) tactics;
             val all_results          = Seq2.map_arg goal tactics_with_handler;
             val results              = rm_useless combination all_results;
            in
              results
            end;
      fun inter_with_limit limit =
        let
          fun inter (CAtom atom) goal     = iddfc limit eval atom goal
            | inter CSkip        goal     = return goal
            | inter CFail        _        = mzero
            | inter (CTry ttac)   goal    = inter (ttac COr CSkip) goal (* should be removed *)
            | inter (tac1 COr tac2)  goal =
              (* similar to the implementation of ORELSE *)
              let
                val res1   = inter tac1 goal;
                fun res2 _ = inter tac2 goal;
                val result = if is_mzero res1 then res2 () else res1;
              in
                result
              end
            | inter (tac1 CPOr tac2)  goal =
              let
                val res2      = Future.fork (fn () => inter tac2 goal);
                val res1      = inter tac1 goal;
                val res1_fail = is_mzero res1;
                val result    = if res1_fail then Future.join res2 else (Future.cancel res2; res1);
              in
                result
              end
            | inter (tac1 CSeq tac2) goal  = bind (inter tac1 goal) (inter tac2)
            | inter (tac1 CAlt tac2) goal  = mplus (inter tac1 goal, inter tac2 goal)
            | inter (tac1 CPAlt tac2) goal =
              let
                val par_inter = mplus o Utils.list_to_pair o Par_List.map (uncurry inter);
                val result    = par_inter [(tac1, goal), (tac2, goal)];
              in
               result
              end
            | inter (CRepBT rtac) goal = (* idea: CRepBT rtac = (rtac CSeq (CRepBT rtac)) CAlt CSkip *)
              let
                fun inter_CRepBT res0 =
                  let
                    val res1             = inter rtac res0;
                    fun get_next current = bind current inter_CRepBT;
                    val result           = if is_mzero res1 then return res0 
                                                            else mplus (get_next res1, return res0)
                  in
                    result
                  end;
              in
                inter_CRepBT goal
              end
            | inter (CRepNB rtac) goal = (* idea: CRepNB rtac = (rtac CSeq (CRepNB rtac)) COr CSkip *)
              let
                val first_failed_result = inter rtac goal;
                fun inter_CRepNB res0 =
                  let
                    val res1             = inter rtac res0;
                    fun get_next current = bind current inter_CRepNB;
                    val result           = if is_mzero res1 then return res0 else get_next res1;
                  in
                    result
                  end;
              in
                bind first_failed_result inter_CRepNB
              end

            (* Note that it's not possible to treat Rep as a syntactic sugar. Desugaring gets stuck. *)
            | inter (CFails ftac) goal = if is_mzero (inter ftac goal) then return goal else mzero
            | inter (CTactical (tactical, tacs)) goal = eval_tactical (tactical, map inter tacs) goal;
      in
        inter tac goal
      end
    (* n_steps_each steps deeper for each iteration. *)
    fun nth_inter n = inter_with_limit (n_steps_each * n);
    (* n_deepenings times of deepening in total. *)
    val results = Seq2.foldr1 mplus (List.tabulate (n_deepenings, nth_inter) |> Seq.of_list);
  in 
    results
  end
  infix 0 PAlt POr
  datatype tac =
  (* prim_tac *)
    Clarsimp
  | Simp
  | Fastforce
  | Auto
  | Induct
  | Case
  | Rule
  | Erule
  (* diagnostic command *)
  | Hammer
  (* assertion tactic / diagnostic command *)
  | Is_Solved
  | Quickcheck
  | Nitpick
  (* special purpose *)
  | Defer
  (* para_tac *)
  | Para_Clarsimp
  | Para_Simp
  | Para_Fastforce
  | Para_Induct
  | Para_Rule
  | Para_Erule
  (* monadic tactical *)
  | Skip
  | Fail
  | Seq of tac Seq.seq
  | Alt of tac Seq.seq
  (* parallel tactical *)
  | PAlt of (tac * tac)
  | POr of (tac * tac)
  (* non-monadic tacticals that have dedicated clauses in "inter".*)
  | RepBT of tac
  | RepNB of tac
  | Fails of tac
  (* non-monadic tacticals that are syntactic sugar.*)
  | Or of tac Seq.seq
  | Try of tac
  (* non-monadic tacticals that are handled by "eval_tactical".*)
  | Solve1 of tac
  | RepNT  of tac

  local 
    val prim = CAtom o CPrim;
    val para = CAtom o CPara;
  in
    fun (* prim_tac *)
        desugar Clarsimp         = prim CClarsimp
     |  desugar Fastforce        = prim CFastforce
     |  desugar Simp             = prim CSimp
     |  desugar Auto             = prim CAuto
     |  desugar Induct           = prim CInduct
     |  desugar Case             = prim CCase
     |  desugar Rule             = prim CRule
     |  desugar Erule            = prim CErule
        (* diagnostic command *)
     |  desugar Hammer           = prim CHammer
        (* assertion tactic *)
     |  desugar Is_Solved        = prim CIs_Solved
     |  desugar Quickcheck       = prim CQuickcheck
     |  desugar Nitpick          = prim CNitpick
        (* special purpose *)
     |  desugar Defer            = prim CDefer
        (* para_tac *)
     |  desugar Para_Simp        = para CPara_Simp
     |  desugar Para_Clarsimp    = para CPara_Clarsimp
     |  desugar Para_Fastforce   = para CPara_Fastforce
     |  desugar Para_Induct      = para CPara_Induct
     |  desugar Para_Rule        = para CPara_Rule
     |  desugar Para_Erule       = para CPara_Erule
        (* monadic tactical *)
     |  desugar Skip             = CSkip
     |  desugar Fail             = CFail
     |  desugar (Seq tacs1)      = (case Seq.pull tacs1 of
         NONE             => error "Seq needs at least one arguement."
       | SOME (t1, tacs2) => case Seq.pull tacs2 of
           NONE   => desugar t1
         | SOME _ => desugar t1 CSeq (desugar (Seq tacs2)))
     |  desugar (Alt tacs1)      = (case Seq.pull tacs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (t1, tacs2) => case Seq.pull tacs2 of
           NONE   => desugar t1
         | SOME _ => desugar t1 CAlt (desugar (Alt tacs2)))
        (* parallel tactical *)
     |  desugar (t1 PAlt t2)     = desugar t1 CPAlt desugar t2
     |  desugar (t1 POr t2)      = desugar t1 CPOr desugar t2
        (* non-monadic tacticals that have dedicated clauses in "inter".*)
     |  desugar (RepBT tac)      = CRepBT (desugar tac)
     |  desugar (RepNB tac)      = CRepNB (desugar tac)
     |  desugar (Fails tac)      = CFails (desugar tac)
        (* non-monadic tacticals that are syntactic sugar.*)
        (* desugar (tac1 Or tac2) = desugar (tac1 Alt (Fails tac1 Seq tac2)) is very inefficient.*)
     |  desugar (Or tacs1)       = (case Seq.pull tacs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (t1, tacs2) => case Seq.pull tacs2 of
           NONE   => desugar t1
         | SOME _ => desugar t1 COr (desugar (Or tacs2)))
       (* desugar (Try tac) = desugar (tac Or Skip) is very inefficient.*)
     |  desugar (Try tac)        = CTry (desugar tac)
        (* non-monadic tacticals that are handled by "eval_tactical".*)
     |  desugar (Solve1 tac)     = CTactical (CSolve1, [desugar tac])
     |  desugar (RepNT tac)      = CTactical (CRepeatN, [desugar tac])
  end;

end;
*}

ML{* functor mk_Monadic_Interpreter_from_Monad_0plus_Min
 (structure Log : MONOID; structure M0P_Min : MONAD_0PLUS_MIN) =
let
  structure MT0Plus = mk_state_M0PT(struct structure Log = Log; structure Base = M0P_Min end);
  structure Monadic_Prover = mk_Monadic_Interpreter(MT0Plus);
in
  Monadic_Prover : MONADIC_INTERPRETER
end;
*}

ML{* structure Log_Min : MONOID_MIN =
struct
  type monoid_min = Dynamic_Utils.log;
  val mempty = [];
  fun mappend src1 src2 = src1 @ src2;
end;

structure Log = mk_Monoid (Log_Min) : MONOID;
*}


ML{* structure Monadic_Interpreter = mk_Monadic_Interpreter_from_Monad_0plus_Min
 (struct structure Log = Log; structure M0P_Min = Seq_M0P_Min end); *}
end