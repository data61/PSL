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

text{* strategy as data-type*}

ML{* signature MONADIC_INTERPRETER =
sig
  include TMONAD_0PLUS
  datatype prim_str = (* default tactics     *) CClarsimp | CSimp | CFastforce | CAuto | CInduct |
                                                CCase | CRule | CErule |
                      (* diagnostic commands *) CHammer |
                      (* assertion strategy  *) CIs_Solved | CQuickcheck | CNitpick |
                      (* special purpose     *) CDefer;
  datatype para_str = CPara_Clarsimp
                    | CPara_Simp
                    | CPara_Fastforce
                    | CPara_Induct
                    | CPara_Rule
                    | CPara_Erule;
  type atom_str;
  datatype atom_strategic = CSolve1 | CRepeatN;
  type core_str;
  type 'a stttac;
  type 'a params;
  type 'a interpret = 'a params -> core_str -> 'a stttac;
  datatype str =
  (* prim_str *)
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
  (* assertion strategy / diagnostic command *)
  | Is_Solved
  | Quickcheck
  | Nitpick
  (* special purpose *)
  | Defer
  (* para_str *)
  | Para_Clarsimp
  | Para_Simp
  | Para_Fastforce
  | Para_Induct
  | Para_Rule
  | Para_Erule
  (* monadic strategic *)
  | Skip
  | Fail
  | Seq of str Seq.seq
  | Alt of str Seq.seq
  (* non-monadic strategics that have dedicated clauses in "inter".*)
  | RepBT of str
  | RepNB of str
  | Fails of str
  | Or of str Seq.seq
  (* non-monadic strategics that are syntactic sugar.*)
  | Try of str
  (* non-monadic strategics that are handled by "eval_strategic".*)
  | Solve1 of str
  | RepNT of str   (* Repeat n times.*)
  (* parallel strategic *)
  | PAlt of str Seq.seq
  | POr  of str Seq.seq;
  val interpret : 'a interpret;
  val desugar : str -> core_str;
end;
*}

ML{* functor mk_Monadic_Interpreter (mt0p : TMONAD_0PLUS) : MONADIC_INTERPRETER =
struct
  open mt0p;
  datatype prim_str = CClarsimp | CSimp | CFastforce | CAuto | CInduct | CCase | CRule | CErule
                    | CIs_Solved | CQuickcheck | CNitpick
                    | CHammer | CDefer;
  datatype para_str = CPara_Clarsimp
                    | CPara_Simp
                    | CPara_Fastforce
                    | CPara_Induct
                    | CPara_Rule
                    | CPara_Erule;
  datatype combine = Unique | First;
  datatype atom_str = CPrim of prim_str | CPara of para_str;
  (* atom_strategic without monadic-interpretation.*)
  datatype atom_strategic = CSolve1 | CRepeatN;
  infix 0 CSeq CAlt  COr CPAlt CPOr;
  datatype core_str =
    CAtom of atom_str
  | CSkip
  | CFail
  | CTry      of core_str
  | COr       of (core_str * core_str)
  | CPOr      of (core_str * core_str)
  | CSeq      of (core_str * core_str)
  | CAlt      of (core_str * core_str)
  | CPAlt     of (core_str * core_str)
  | CRepBT    of core_str
  | CRepNB    of core_str
  | CFails    of core_str (* Fails cannot be defined as just a syntactic sugar as the definition(desugaring) involves (goal:thm).*)
  | CStrategic of (atom_strategic * core_str list);
  type 'a stttac         = 'a -> 'a monad;
  type 'a eval_prim      = prim_str -> 'a stttac;
  type 'a eval_para      = para_str -> 'a -> 'a stttac Seq.seq;
  type 'a eval_strategic = atom_strategic * 'a stttac list -> 'a stttac;
  type 'a equal          = 'a monad -> 'a monad -> bool;
  type 'a iddfc          = int -> (atom_str -> 'a stttac) -> (atom_str -> 'a stttac);
  type depths            = (int * int);
  type 'a params         = ('a eval_prim * 'a eval_para * 'a eval_strategic * 'a equal * 'a iddfc * depths);
  type 'a interpret      = 'a params -> core_str -> 'a stttac;

  (* interpret function similar to that of "A Monadic Interpretation of Tactics" by A. Martin et. al.*)
  (* (-`\<omega>-) *)
  fun interpret (eval_prim, eval_para, eval_strategic, m_equal, iddfc, (n_deepenings, n_steps_each))
                (strategy:core_str) goal =
    let
       fun is_mzero monad        = m_equal monad mzero;
       fun eval (CPrim str) goal = eval_prim str goal
         | eval (CPara str) goal =
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
             val combination          = how_to_combine_results str;
             val tactics              = eval_para str goal;
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
            | inter (CTry str)   goal    = inter (str COr CSkip) goal (* should be removed *)
            | inter (str1 COr str2)  goal =
              (* similar to the implementation of ORELSE *)
              let
                val res1   = inter str1 goal;
                fun res2 _ = inter str2 goal;
                val result = if is_mzero res1 then res2 () else res1;
              in
                result
              end
            | inter (str1 CPOr str2)  goal =
              let
                val res2      = Future.fork (fn () => inter str2 goal);
                val res1      = inter str1 goal;
                val res1_fail = is_mzero res1;
                val result    = if res1_fail then Future.join res2 else (Future.cancel res2; res1);
              in
                result
              end
            | inter (str1 CSeq str2) goal  = bind (inter str1 goal) (inter str2)
            | inter (str1 CAlt str2) goal  = mplus (inter str1 goal, inter str2 goal)
            | inter (str1 CPAlt str2) goal =
              let
                val par_inter = mplus o Utils.list_to_pair o Par_List.map (uncurry inter);
                val result    = par_inter [(str1, goal), (str2, goal)];
              in
               result
              end
            | inter (CRepBT str) goal = (* idea: CRepBT str = (str CSeq (CRepBT str)) CAlt CSkip *)
              let
                fun inter_CRepBT res0 =
                  let
                    val res1             = inter str res0;
                    fun get_next current = bind current inter_CRepBT;
                    val result           = if is_mzero res1 then return res0 
                                                            else mplus (get_next res1, return res0)
                  in
                    result
                  end;
              in
                inter_CRepBT goal
              end
            | inter (CRepNB str) goal = (* idea: CRepNB str = (str CSeq (CRepNB str)) COr CSkip *)
              let
                val first_failed_result = inter str goal;
                fun inter_CRepNB res0 =
                  let
                    val res1             = inter str res0;
                    fun get_next current = bind current inter_CRepNB;
                    val result           = if is_mzero res1 then return res0 else get_next res1;
                  in
                    result
                  end;
              in
                bind first_failed_result inter_CRepNB
              end

            (* Note that it's not possible to treat Rep as a syntactic sugar. Desugaring gets stuck. *)
            | inter (CFails str) goal = if is_mzero (inter str goal) then return goal else mzero
            | inter (CStrategic (sttgic, strs)) goal = eval_strategic (sttgic, map inter strs) goal;
      in
        inter strategy goal
      end
    (* n_steps_each steps deeper for each iteration. *)
    fun nth_inter n = inter_with_limit (n_steps_each * n);
    (* n_deepenings times of deepening in total. *)
    val results = Seq2.foldr1 mplus (List.tabulate (n_deepenings, nth_inter) |> Seq.of_list);
  in 
    results
  end
  datatype str =
  (* prim_str *)
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
  (* assertion strategy / diagnostic command *)
  | Is_Solved
  | Quickcheck
  | Nitpick
  (* special purpose *)
  | Defer
  (* para_str *)
  | Para_Clarsimp
  | Para_Simp
  | Para_Fastforce
  | Para_Induct
  | Para_Rule
  | Para_Erule
  (* monadic strategic *)
  | Skip
  | Fail
  | Seq of str Seq.seq
  | Alt of str Seq.seq
  (* parallel tactical *)
  | PAlt of str Seq.seq
  | POr  of str Seq.seq
  (* non-monadic strategics that have dedicated clauses in "inter".*)
  | RepBT of str
  | RepNB of str
  | Fails of str
  (* non-monadic strategics that are syntactic sugar.*)
  | Or of str Seq.seq
  | Try of str
  (* non-monadic strategics that are handled by "eval_strategic".*)
  | Solve1 of str
  | RepNT  of str

  local 
    val prim = CAtom o CPrim;
    val para = CAtom o CPara;
  in
    fun (* prim_str *)
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
        (* assertion strategy *)
     |  desugar Is_Solved        = prim CIs_Solved
     |  desugar Quickcheck       = prim CQuickcheck
     |  desugar Nitpick          = prim CNitpick
        (* special purpose *)
     |  desugar Defer            = prim CDefer
        (* para_str *)
     |  desugar Para_Simp        = para CPara_Simp
     |  desugar Para_Clarsimp    = para CPara_Clarsimp
     |  desugar Para_Fastforce   = para CPara_Fastforce
     |  desugar Para_Induct      = para CPara_Induct
     |  desugar Para_Rule        = para CPara_Rule
     |  desugar Para_Erule       = para CPara_Erule
        (* monadic strategic *)
     |  desugar Skip             = CSkip
     |  desugar Fail             = CFail
     |  desugar (Seq strs1)      = (case Seq.pull strs1 of
         NONE             => error "Seq needs at least one arguement."
       | SOME (str1, strs2) => case Seq.pull strs2 of
           NONE   => desugar str1
         | SOME _ => desugar str1 CSeq (desugar (Seq strs2)))
     |  desugar (Alt strs1)      = (case Seq.pull strs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (str1, strs2) => case Seq.pull strs2 of
           NONE   => desugar str1
         | SOME _ => desugar str1 CAlt (desugar (Alt strs2)))
        (* parallel strategic *)
     |  desugar (PAlt strs1)      = (case Seq.pull strs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (str1, strs2) => case Seq.pull strs2 of
           NONE   => desugar str1
         | SOME _ => desugar str1 CPAlt (desugar (PAlt strs2)))
     |  desugar (POr strs1)       = (case Seq.pull strs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (str1, strs2) => case Seq.pull strs2 of
           NONE   => desugar str1
         | SOME _ => desugar str1 CPOr (desugar (POr strs2)))
        (* non-monadic strategics that have dedicated clauses in "inter".*)
     |  desugar (RepBT str)      = CRepBT (desugar str)
     |  desugar (RepNB str)      = CRepNB (desugar str)
     |  desugar (Fails str)      = CFails (desugar str)
        (* non-monadic strategics that are syntactic sugar.*)
        (* desugar (str1 Or str2) = desugar (str1 Alt (Fails str1 Seq str2)) is very inefficient.*)
     |  desugar (Or strs1)       = (case Seq.pull strs1 of
         NONE             => error "Alt needs at least one arguement."
       | SOME (str1, strs2) => case Seq.pull strs2 of
           NONE   => desugar str1
         | SOME _ => desugar str1 COr (desugar (Or strs2)))
       (* desugar (Try str) = desugar (str Or Skip) is very inefficient.*)
     |  desugar (Try str)        = CTry (desugar str)
        (* non-monadic strategics that are handled by "eval_strategic".*)
     |  desugar (Solve1 str)     = CStrategic (CSolve1, [desugar str])
     |  desugar (RepNT str)      = CStrategic (CRepeatN, [desugar str])
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