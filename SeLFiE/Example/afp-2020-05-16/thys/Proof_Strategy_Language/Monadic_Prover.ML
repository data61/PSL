(*  Title:      Monadic_Prover.ML
    Author:     Yutaka Nagashima, Data61, CSIRO

The core of PSL. This file provides the skeleton of PSL.
Monadic_Interpreter_Params flesh out this skeleton with concrete evaluation functions.
*)

(*** MONADIC_INTERPRETER_CORE: The core of PSL with the core-syntax. ***)
signature MONADIC_INTERPRETER_CORE =
sig
  include TMONAD_0PLUS
  datatype csubtool =  CQuickcheck | CNitpick | CHammer;
  datatype cspecial =  CIsSolved | CDefer | CIntroClasses | CTransfer | CNormalization
                     | CSubgoal;
  datatype cprim_str = CClarsimp | CSimp | CBlast | CFastforce | CAuto | CInduct
                     | CInductTac | CCoinduction | CCases | CCaseTac | CRule | CErule;
  datatype cstatic = CPrim of cprim_str | CSpec of cspecial | CSubt of csubtool | CUser of string;
  datatype catom_str = CSttc of cstatic | CDyn of cprim_str;
  (*CPThen cannot be a part of core_str, as the constructor class does not provide enough information.*)
  datatype cstrategic = CSolve1 | CRepeatN | CCut of int | CPSeq | CPSeq1 | CPOr | CPAlt;
  datatype core_str =
    CAtom of catom_str
  | CSkip
  | CFail
  | COr       of (core_str * core_str)
  | CSeq      of (core_str * core_str)
  | CAlt      of (core_str * core_str)
  | CRepBT    of core_str
  | CRepNB    of core_str
  | CFails    of core_str (*Fails cannot be defined as just a syntactic sugar as the definition involves goal.*)
  | CStrategic of (cstrategic * core_str list);
  type 'a stttac;
  type 'a params;
  type 'a interpret = 'a params -> core_str -> 'a stttac;
  val interpret : 'a interpret;
end;

(*** mk_Monadic_Interpreter_Core: makes the core of PSL, abstracted to TMONAD_0PLUS. ***)
functor mk_Monadic_Interpreter_Core (Mt0p : TMONAD_0PLUS) : MONADIC_INTERPRETER_CORE =
struct
  open Mt0p;
  datatype csubtool =  CQuickcheck | CNitpick | CHammer;
  datatype cspecial =  CIsSolved | CDefer | CIntroClasses | CTransfer | CNormalization
                     | CSubgoal;
  (*default tactics*)
  datatype cprim_str = CClarsimp | CSimp | CBlast | CFastforce | CAuto | CInduct
                     | CInductTac | CCoinduction | CCases | CCaseTac | CRule | CErule;
  datatype combine = Unique | First;
  datatype cstatic = CPrim of cprim_str | CSpec of cspecial | CSubt of csubtool | CUser of string;
  datatype catom_str = CSttc of cstatic | CDyn of cprim_str;
  (*atom_strategic with less-monadic interpretation.*)
  datatype cstrategic = CSolve1 | CRepeatN | CCut of int | CPSeq | CPSeq1 | CPOr | CPAlt;
  infix 0 CSeq CAlt  COr CPAlt;
  datatype core_str =
    CAtom of catom_str
  | CSkip
  | CFail
  | COr       of (core_str * core_str)
  | CSeq      of (core_str * core_str)
  | CAlt      of (core_str * core_str)
  | CRepBT    of core_str
  | CRepNB    of core_str
  | CFails    of core_str (*I cannot Fails as a syntactic sugar as the definition involves goal.*)
  | CStrategic of (cstrategic * core_str list);
  type 'a stttac         = 'a -> 'a monad;
  type 'a eval_prim      = cstatic -> 'a stttac;
  type 'a eval_para      = cprim_str -> 'a -> 'a stttac Seq.seq;
  type 'a eval_strategic = cstrategic * 'a stttac list -> 'a stttac;
  type 'a equal          = 'a monad -> 'a monad -> bool;
  type 'a iddfc          = int -> (catom_str -> 'a stttac) -> (catom_str -> 'a stttac);
  type depths            = (int * int);
  type 'a params         = ('a eval_prim * 'a eval_para * 'a eval_strategic * 'a equal * 'a iddfc * depths);
  type 'a interpret      = 'a params -> core_str -> 'a stttac;

  (*Interpret function similar to that of "A Monadic Interpretation of Tactics" by A. Martin et. al.*)
  fun interpret (eval_prim, eval_para, eval_strategic, m_equal, iddfc, (n_deepenings, n_steps_each))
                (strategy:core_str) goal =
    let
       fun is_mzero monad        = m_equal monad mzero;
       fun eval (CSttc str) goal = Utils.try_with mzero (eval_prim str) goal
         | eval (CDyn str) goal =
           let
             (*Should I factor this out to Monadic_Interpreter_Params?*)
             fun how_to_combine_results CClarsimp    = Unique
              |  how_to_combine_results CSimp        = Unique
              |  how_to_combine_results CBlast       = Unique
              |  how_to_combine_results CFastforce   = First
              |  how_to_combine_results CAuto        = Unique
              |  how_to_combine_results CInduct      = Unique
              |  how_to_combine_results CInductTac   = Unique
              |  how_to_combine_results CCoinduction = Unique
              |  how_to_combine_results CCases       = Unique
              |  how_to_combine_results CCaseTac     = Unique
              |  how_to_combine_results CRule        = Unique
              |  how_to_combine_results CErule       = Unique;
             fun rm_useless First  results =
                 (Seq.filter (not o is_mzero) results |> Seq.hd handle Option.Option => mzero)
              |  rm_useless Unique results =
                 (distinct (uncurry m_equal) (Seq.list_of results)
                  |> Seq.of_list |> msum handle Empty => mzero | ERROR _ => mzero);
             val combination          = how_to_combine_results str;
             val tactics              = Seq2.try_seq (eval_para str) goal;
             (*Sometimes, Isabelle does not have appropriate rules.*)
             val tactics_with_handler = Seq.map (fn tactic => fn goal =>
                                        Utils.try_with mzero tactic goal) tactics;
             val all_results          = Seq2.try_seq (Seq2.map_arg goal) tactics_with_handler;
             val results              = rm_useless combination all_results;
            in
              results
            end;
      fun inter_with_limit limit =
        let
          fun inter (CAtom atom) goal     = iddfc limit eval atom goal
            | inter CSkip        goal     = return goal
            | inter CFail        _        = mzero
            | inter (str1 COr str2)  goal =
              (*similar to the implementation of ORELSE*)
              let
                val res1   = inter str1 goal;
                fun res2 _ = inter str2 goal;
                val result = if is_mzero res1 then res2 () else res1;
              in
                result
              end
            | inter (str1 CSeq str2) goal  = bind (inter str1 goal) (inter str2)
            | inter (str1 CAlt str2) goal  = mplus (inter str1 goal, inter str2 goal)
            | inter (CRepBT str) goal = (*idea: CRepBT str = (str CSeq (CRepBT str)) CAlt CSkip*)
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
            | inter (CRepNB str) goal = (*idea: CRepNB str = (str CSeq (CRepNB str)) COr CSkip*)
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
            (*Note that it's not possible to treat Rep as a syntactic sugar. Desugaring gets stuck.*)
            | inter (CFails str) goal = if is_mzero (inter str goal) then return goal else mzero
            | inter (CStrategic (sttgic, strs)) goal = eval_strategic (sttgic, map inter strs) goal;
      in
        inter strategy goal
      end
    fun results' 0 = mzero
      | results' m =
          let
            val current_result = inter_with_limit (((n_deepenings - m) + 1) * n_steps_each)
            val not_solved = m_equal current_result mzero
          in
            if not_solved then results' (m - 1) else current_result
          end
    val results = results' n_deepenings
  in 
    results
  end
end;

(*** Monadic_Interpreter_Core: The core of PSL. ***)
(** mk_Monadic_Interpreter_Core_from_Monad_0plus_Min: makes the core of PSL from a monoid and a
 monad with a zero and plus **)
functor mk_Monadic_Interpreter_Core_from_Monad_0plus_Min
 (structure Log : MONOID; structure M0P_Min : MONAD_0PLUS_MIN) =
let
  structure MT0Plus = mk_state_M0PT(struct structure Log = Log; structure Base = M0P_Min end);
  structure Monadic_Interpreter = mk_Monadic_Interpreter_Core(MT0Plus);
in
  Monadic_Interpreter : MONADIC_INTERPRETER_CORE
end;

(** Log_Min and Log: The "state" of PSL, which is used to produce efficient proof scripts. **)
structure Log_Min : MONOID_MIN =
struct
  type monoid_min = Dynamic_Utils.log;
  val mempty = [];
  fun mappend src1 src2 = src1 @ src2;
end;

structure Log = mk_Monoid (Log_Min) : MONOID;

(** Monadic_Interpreter_Core: The core of PSL. **)
structure Monadic_Interpreter_Core : MONADIC_INTERPRETER_CORE =
 mk_Monadic_Interpreter_Core_from_Monad_0plus_Min
 (struct structure Log = Log; structure M0P_Min = Seq_M0P_Min end);

(*** MONADIC_INTERPRETER: The surface-syntax of PSL with de-sugaring. ***)
signature MONADIC_INTERPRETER =

sig

(* str *)
datatype str =
(*prim_str*)
  Clarsimp
| Simp
| Blast
| Fastforce
| Auto
| Induct
| InductTac
| Coinduction
| Cases
| CaseTac
| Rule
| Erule
(*diagnostic command*)
| Hammer
(*assertion strategy / diagnostic command*)
| IsSolved
| Quickcheck
| Nitpick
(*special purpose*)
| Defer
| Subgoal
| IntroClasses
| Transfer
| Normalization
| User of string
(*para_str*)
| ParaClarsimp
| ParaSimp
| ParaBlast
| ParaFastforce
| ParaAuto
| ParaInduct
| ParaInductTac
| ParaCoinduction
| ParaCases
| ParaCaseTac
| ParaRule
| ParaErule
(*monadic strategic*)
| Skip
| Fail
| Seq of str Seq.seq
| Alt of str Seq.seq
(*non-monadic strategics that have dedicated clauses in "inter".*)
| RepBT of str
| RepNB of str
| Fails of str
(*non-monadic strategics that are syntactic sugar.*)
| Or of str Seq.seq
| Try of str
(*non-monadic strategics that are handled by "eval_strategic".*)
| Solve1 of str
| RepNT  of str
| Cut    of (int * str)
| PSeq   of str Seq.seq
| PSeq1  of str Seq.seq
| POr    of str Seq.seq
| PAlt   of str Seq.seq;

(* desugar *)
val desugar : str -> Monadic_Interpreter_Core.core_str;

end;

(*** Monadic_Interpreter: The surface-syntax of PSL with de-sugaring. ***)
structure Monadic_Interpreter : MONADIC_INTERPRETER =
struct

open Monadic_Interpreter_Core;

(* str *)
datatype str =
(*prim_str*)
  Clarsimp
| Simp
| Blast
| Fastforce
| Auto
| Induct
| InductTac
| Coinduction
| Cases
| CaseTac
| Rule
| Erule
(*diagnostic command*)
| Hammer
(*assertion strategy / diagnostic command*)
| IsSolved
| Quickcheck
| Nitpick
(*special purpose*)
| Defer
| Subgoal
| IntroClasses
| Transfer
| Normalization
| User of string
(*para_str*)
| ParaClarsimp
| ParaSimp
| ParaBlast
| ParaFastforce
| ParaAuto
| ParaInduct
| ParaInductTac
| ParaCoinduction
| ParaCases
| ParaCaseTac
| ParaRule
| ParaErule
(*monadic strategic*)
| Skip
| Fail
| Seq of str Seq.seq
| Alt of str Seq.seq
(*non-monadic strategics that have dedicated clauses in "inter".*)
| RepBT of str
| RepNB of str
| Fails of str
(*non-monadic strategics that are syntactic sugar.*)
| Or of str Seq.seq
| Try of str
(*non-monadic strategics that are handled by "eval_strategic".*)
| Solve1 of str
| RepNT  of str
| Cut    of (int * str)
| PSeq   of str Seq.seq
| PSeq1  of str Seq.seq
| POr    of str Seq.seq
| PAlt   of str Seq.seq;

infix 0 CSeq CAlt  COr;

local
  val prim = CAtom o CSttc o CPrim;
  val dyna = CAtom o CDyn;
  val subt = CAtom o CSttc o CSubt;
  val spec = CAtom o CSttc o CSpec;
  val user = CAtom o CSttc o CUser;
in

(* desugar *)
fun desugar Clarsimp        = prim CClarsimp
 |  desugar Blast           = prim CBlast
 |  desugar Fastforce       = prim CFastforce
 |  desugar Simp            = prim CSimp
 |  desugar Auto            = prim CAuto
 |  desugar Induct          = prim CInduct
 |  desugar InductTac       = prim CInductTac
 |  desugar Coinduction     = prim CCoinduction
 |  desugar Cases           = prim CCases
 |  desugar CaseTac         = prim CCaseTac
 |  desugar Rule            = prim CRule
 |  desugar Erule           = prim CErule
 |  desugar Hammer          = subt CHammer
    (*assertion strategy*)
 |  desugar IsSolved        = spec CIsSolved
 |  desugar Quickcheck      = subt CQuickcheck
 |  desugar Nitpick         = subt CNitpick
    (*special purpose*)
 |  desugar Defer           = spec CDefer
 |  desugar Subgoal         = spec CSubgoal
 |  desugar IntroClasses    = spec CIntroClasses
 |  desugar Transfer        = spec CTransfer
 |  desugar Normalization   = spec CNormalization
 |  desugar (User tac_name) = user tac_name
    (*para_str*)
 |  desugar ParaSimp        = dyna CSimp
 |  desugar ParaBlast       = dyna CBlast
 |  desugar ParaClarsimp    = dyna CClarsimp
 |  desugar ParaFastforce   = dyna CFastforce
 |  desugar ParaAuto        = dyna CAuto
 |  desugar ParaInduct      = dyna CInduct
 |  desugar ParaInductTac   = dyna CInductTac
 |  desugar ParaCoinduction = dyna CCoinduction
 |  desugar ParaCases       = dyna CCases
 |  desugar ParaCaseTac     = dyna CCaseTac
 |  desugar ParaRule        = dyna CRule
 |  desugar ParaErule       = dyna CErule
    (*monadic strategic*)
 |  desugar Skip            = CSkip
 |  desugar Fail            = CFail
 |  desugar (Seq strs1)     = (case Seq.pull strs1 of
     NONE               => error "Seq needs at least one arguement."
   | SOME (str1, strs2) => case Seq.pull strs2 of
       NONE   => desugar str1
     | SOME _ => desugar str1 CSeq (desugar (Seq strs2)))
 |  desugar (Alt strs1)     = (case Seq.pull strs1 of
     NONE               => error "Alt needs at least one arguement."
   | SOME (str1, strs2) => case Seq.pull strs2 of
       NONE   => desugar str1
     | SOME _ => desugar str1 CAlt (desugar (Alt strs2)))
    (*non-monadic strategics that have dedicated clauses in "inter".*)
 |  desugar (RepBT str)     = CRepBT (desugar str)
 |  desugar (RepNB str)     = CRepNB (desugar str)
 |  desugar (Fails str)     = CFails (desugar str)
    (*non-monadic strategics that are syntactic sugar.*)
    (*desugar (str1 Or str2) = desugar (str1 Alt (Fails str1 Seq str2)) is very inefficient.*)
 |  desugar (Or strs1)      = (case Seq.pull strs1 of
     NONE               => error "Alt needs at least one arguement."
   | SOME (str1, strs2) => case Seq.pull strs2 of
       NONE   => desugar str1
     | SOME _ => desugar str1 COr (desugar (Or strs2)))
    (*desugar (Try str) = desugar (str Or Skip) is very inefficient.*)
 |  desugar (Try str)       = desugar str COr CSkip
    (*non-monadic strategics that are handled by "eval_strategic".*)
 |  desugar (Solve1 str)    = CStrategic (CSolve1, [desugar str])
 |  desugar (RepNT str)     = CStrategic (CRepeatN, [desugar str])
 |  desugar (Cut (i, str))  = CStrategic (CCut i, [desugar str])
 |  desugar (PSeq strs)     = CStrategic (CPSeq, (Seq.map desugar strs |> Seq.list_of))
 |  desugar (PSeq1 strs)    = CStrategic (CPSeq1,(Seq.map desugar strs |> Seq.list_of))
 |  desugar (POr   strs)    = CStrategic (CPOr,  (Seq.map desugar strs |> Seq.list_of))
 |  desugar (PAlt  strs)    = CStrategic (CPAlt, (Seq.map desugar strs |> Seq.list_of))
end;

end;

(*** MONADIC_INTERPRETER_PARAMS: fleshes out MONADIC_INTERPRETER with evaluation functions. ***)
signature MONADIC_INTERPRETER_PARAMS =
sig
  type eval_prim;
  type eval_para;
  type eval_strategic;
  type m_equal;
  type iddfc;
  val eval_prim      : eval_prim;
  val eval_para      : eval_para;
  val eval_strategic : eval_strategic;
  val m_equal        : m_equal;
  val iddfc          : iddfc;
end;

(*** Monadic_Interpreter_Params: fleshes out Monadic_Interpreter with evaluation functions. ***)
structure Monadic_Interpreter_Params : MONADIC_INTERPRETER_PARAMS =
struct

structure MIC = Monadic_Interpreter_Core;
structure DU         = Dynamic_Utils;
type state           = Proof.state;
type 'a seq          = 'a Seq.seq;
type ctxt            = Proof.context;
type thms            = thm list;
type strings         = string list;
type eval_prim       = MIC.cstatic -> state MIC.stttac;
type eval_para       = MIC.cprim_str -> state -> state MIC.stttac Seq.seq;
type eval_strategic  = MIC.cstrategic * state MIC.stttac list -> state MIC.stttac;
type m_equal         = state MIC.monad -> state MIC.monad -> bool;
type iddfc           = int -> (MIC.catom_str -> state MIC.stttac) -> MIC.catom_str -> state MIC.stttac;
type log             = Dynamic_Utils.log;
type monad           = state Dynamic_Utils.st_monad;
type monad_tac       = state Dynamic_Utils.stttac;
(*do_trace and show_trace are for debugging only.*)
val do_trace         = false;
fun show_trace text  = if do_trace then tracing text else ();

local
structure User_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct
  type modifier           = string;
  type modifiers          = string list;
  fun get_all_modifiers _ = [];
  fun mods_to_string mods = String.concatWith " " mods;
  val reordered_mods      = single o I;
end;
structure User_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (User_Seed);
in
fun user_stttac (meth:string) =
  User_Tactic_Generator.meth_name_n_modifiers_to_stttac_on_state meth [(* ignores log *)];
end;

(* eval_prim *)
(*I cannot move the definition of "eval_prim" into mk_Monadic_Interpreter,
  because its type signature is too specific.*)
fun eval_prim (prim:MIC.cstatic) (goal_state:state) =
  let
    (*For eval_prim.*)
    val string_to_stttac = Dynamic_Utils.string_to_stttac_on_pstate;
    val tac_on_proof_state : state MIC.stttac = case prim of
      MIC.CPrim MIC.CClarsimp =>     (show_trace "CClarsimp";      string_to_stttac "clarsimp")
    | MIC.CPrim MIC.CSimp =>         (show_trace "CSimp";          string_to_stttac "simp")
    | MIC.CPrim MIC.CBlast =>        (show_trace "CBlast";         string_to_stttac "blast")
    | MIC.CPrim MIC.CFastforce =>    (show_trace "CFastforce";     string_to_stttac "fastforce")
    | MIC.CPrim MIC.CAuto =>         (show_trace "CAuto";          string_to_stttac "auto")
    | MIC.CPrim MIC.CInduct =>       (show_trace "CInduct";        string_to_stttac "induct")
    | MIC.CPrim MIC.CInductTac =>    (show_trace "CInductTac";     string_to_stttac "induct_tac")
    | MIC.CPrim MIC.CCoinduction =>  (show_trace "CCoinduct";      string_to_stttac "coinduction")
    | MIC.CPrim MIC.CCases  =>       (show_trace "CCases";         string_to_stttac "cases")
    | MIC.CPrim MIC.CCaseTac =>      (show_trace "CCaseTac";       string_to_stttac "case_tac")
    | MIC.CPrim MIC.CRule   =>       (show_trace "CRule";          string_to_stttac "rule")
    | MIC.CPrim MIC.CErule  =>       (show_trace "CErule";         string_to_stttac "erule")
    | MIC.CSpec MIC.CIntroClasses => (show_trace "CIntro_Classes"; string_to_stttac "intro_classes")
    | MIC.CSpec MIC.CTransfer =>     (show_trace "CTransfer";      string_to_stttac "transfer")
    | MIC.CSpec MIC.CNormalization =>(show_trace "CNormalization"; string_to_stttac "normalization")
    | MIC.CSpec MIC.CSubgoal =>      (show_trace "CSubgoal";       Subtools.subgoal)
    | MIC.CSubt MIC.CHammer =>       (show_trace "CHammer";        Subtools.hammer)
    | MIC.CSpec MIC.CIsSolved =>     (show_trace "CIs_Solved";     Subtools.is_solved)
    | MIC.CSubt MIC.CQuickcheck=>    (show_trace "CQuickcheck";    Subtools.quickcheck)
    | MIC.CSubt MIC.CNitpick   =>    (show_trace "CNitpick";       Subtools.nitpick)
    | MIC.CSpec MIC.CDefer     =>    (show_trace "CDefer";         Subtools.defer)
    | MIC.CUser tac_name =>          (show_trace tac_name;         user_stttac tac_name);
  in
     Utils.try_with MIC.mzero tac_on_proof_state goal_state : state MIC.monad
  end;

(* eval_para *)
fun eval_para (str:MIC.cprim_str) (state:Proof.state) =
  let
    val get_state_stttacs = case str of
        MIC.CSimp =>        (show_trace "CPara_Simp";        Dynamic_Tactic_Generation.simp)
      | MIC.CBlast =>       (show_trace "CBlast";            Dynamic_Tactic_Generation.blast)
      | MIC.CInduct =>      (show_trace "CPara_Induct";      Dynamic_Tactic_Generation.induct)
      | MIC.CInductTac =>   (show_trace "CPara_InductTac";   Dynamic_Tactic_Generation.induct_tac)
      | MIC.CCoinduction => (show_trace "CPara_Coinduction"; Dynamic_Tactic_Generation.coinduction)
      | MIC.CCases =>       (show_trace "CPara_Cases";       Dynamic_Tactic_Generation.cases)
      | MIC.CCaseTac =>     (show_trace "CPara_CaseTac";     Dynamic_Tactic_Generation.case_tac)
      | MIC.CRule =>        (show_trace "CPara_Rule";        Dynamic_Tactic_Generation.rule)
      | MIC.CErule =>       (show_trace "CPara_Erule";       Dynamic_Tactic_Generation.erule)
      | MIC.CFastforce =>   (show_trace "CPara_Fastforce";   Dynamic_Tactic_Generation.fastforce)
      | MIC.CAuto =>        (show_trace "CPara_Auto";        Dynamic_Tactic_Generation.auto)
      | MIC.CClarsimp =>    (show_trace "CPara_Clarsimp";    Dynamic_Tactic_Generation.clarsimp)
  in
    (*It is okay to use the type list internally,
      as long as the overall monadic interpretation framework is instantiated to Seq.seq for
      monad with 0 and plus.*)
    Seq2.try_seq get_state_stttacs state : monad_tac seq
  end;

(* m_equal *)
fun m_equal (st_mona1:monad) (st_mona2:state MIC.monad) =
(*Probably, I do not have to check the entire sequence in most cases.
  As the length of sequences can be infinite in general, I prefer to test a subset of these.*)
  let
    type lstt   = Log_Min.monoid_min * state;
    type lstts  = lstt seq;
    fun are_same_one (x : lstt,  y : lstt)  = apply2 (#goal o Proof.goal o snd) (x, y)
                                           |> Thm.eq_thm;
    fun are_same_seq (xs: lstts, ys: lstts) = Seq2.same_seq are_same_one (xs, ys) ;
    (*Note that the state representing log is not always []. This is only for equality check.*)
    val xs_5 : lstts                        = st_mona1 [] |> Seq.take 5;
    val ys_5 : lstts                        = st_mona2 [] |> Seq.take 5;
  in
    are_same_seq (xs_5, ys_5)
  end;

(* solve_1st_subg *)
fun solve_1st_subg (tac:monad_tac) (goal:state) (log:log) =
  let
    val get_thm = Isabelle_Utils.proof_state_to_thm;
    fun same_except_for_fst_prem' x y = Isabelle_Utils.same_except_for_fst_prem (get_thm x) (get_thm y)
  in
    tac goal log
    |> Seq.filter (fn (_, st')  => same_except_for_fst_prem' goal st'):(log * state) Seq.seq
  end;

(* repeat_n *)
fun repeat_n (tac : monad_tac) (goal : state) = (fn (log:log) =>
  let
    fun repeat_n' (0:int) (g:state) = MIC.return g
     |  repeat_n' (n:int) (g:state) = if n < 0 then error "repeat_n failed: n < 0" else
          MIC.bind (tac g) (repeat_n' (n - 1));
    val subgoal_num = Isabelle_Utils.proof_state_to_thm goal |> Thm.nprems_of;
  in
    (*We have to add 1 because of Isabelle's strange evaluation (parse-twice thingy).*)
    repeat_n' subgoal_num goal log : (log * state) Seq.seq
  end) : monad;

(* cut *)
fun cut (limit:int) (tac:monad_tac) (goal:state) = Seq.take limit o tac goal : monad;

local

val list_of = Seq.list_of;
val of_list = Seq.of_list;

in

(* pseq *)
(*Note that pthen locally introduces strict evaluation.*)
fun pseq (tac1::[tac2]:monad_tac list) : monad_tac = (fn goal:state =>
  let
     val pmap = Par_List.map;
     fun pbind (monad:monad) (tactic:monad_tac) : monad = fn state0 : log => (fn seq => fn func =>
       of_list (flat (pmap (list_of o func) (list_of seq)))) (monad state0) (fn (state1, result1) =>
       tactic result1 state1);
  in
    pbind (tac1 goal) tac2
  end) : monad_tac
 |  pseq _ = error "pthen takes exactly two strategies.";

(* pseq1 *)
(*Note that pthen1 does not satisfy the monad law as a bind.*)
(*Nevertheless, pthen1 is useful to exploit parallelism.*)
fun pseq1 (tac1::[tac2]:monad_tac list) : monad_tac = (fn goal:state =>
  let
     val get_some   = Par_List.get_some;
     val seq_to_opt = Seq2.seq_to_option;
     fun pbind (monad:monad) (tactic:monad_tac) : monad = fn state0 : log => (fn seq => fn func =>
       of_list (the_list (get_some (seq_to_opt o func) (list_of seq)))) (monad state0) (fn (state1, result1) =>
       tactic result1 state1);
  in
    pbind (tac1 goal) tac2
  end) : monad_tac
 |  pseq1 _ = error "pthen1 takes exactly two strategies.";


(* pors *)
fun pors' (goal:state, tactic:monad_tac) : monad option =
  let
    val result      = (fn (log:log) => tactic goal log) : monad;
    (*some_result forces evaluation to exploit parallelism.*)
    val some_result = if m_equal MIC.mzero result then NONE else SOME result : monad option;
  in
    some_result
end;

fun pors (tactics:monad_tac list) : monad_tac = (fn goal:state =>
  let
    val states = replicate (length tactics) goal : state list;
    val some_monad = Par_List.get_some pors' (ListPair.zip (states, tactics));
    val result = case some_monad of
      NONE       => MIC.mzero
    | SOME monad => monad;
  in
    result:monad
  end);

(* palts *)
fun palts (tactics:monad_tac list) : monad_tac = (fn goal:state => (fn log:log =>
  let
    val goal_n_log  = replicate (length tactics) (log, goal) : (log * state) list;
    val get_result  = fn ((log:log, goal:state), tactic:monad_tac) => tactic goal log : (log * state) seq;
    val result_list = Par_List.map get_result (ListPair.zip (goal_n_log, tactics))
                    : (log * state) seq list;
    val result_seq  = result_list |> of_list |> Seq.flat : (log * state) seq;
  in
    result_seq
  end) : monad) : monad_tac;

end;

(* eval_strategic *)
fun eval_strategic (MIC.CSolve1, [tac:monad_tac])  = solve_1st_subg tac
 |  eval_strategic (MIC.CSolve1, _)  = error "eval_strategic failed. M.Solve1 needs exactly one tactic."
 |  eval_strategic (MIC.CRepeatN, [tac:monad_tac]) = repeat_n tac
 |  eval_strategic (MIC.CRepeatN, _) = error "eval_strategic failed. M.RepeatN needs exactly one tactic."
 |  eval_strategic (MIC.CCut lim, [tac:monad_tac]) =
      if lim > 0 then cut lim tac
      else error "eval_strategic failed. The limit for CCut has to be larger than 0."
 |  eval_strategic (MIC.CCut _, _)   = error "eval strategic failed. M.CCut needs exactly one tactic."
 |  eval_strategic (MIC.CPSeq1, tac1::[tac2]) = pseq1 (tac1::[tac2])
 |  eval_strategic (MIC.CPSeq1, _)   = error "eval strategic failed. MIC.CPSeq1 needs exactly two tactics."
 |  eval_strategic (MIC.CPSeq, tac1::[tac2]) = pseq (tac1::[tac2])
 |  eval_strategic (MIC.CPSeq, _)    = error "eval strategic failed. MIC.CPSeq needs exactly two tactics."
 |  eval_strategic (MIC.CPOr, [])    = error "eval strategic failed. MIC.CPSeq needs at least one tactic."
 |  eval_strategic (MIC.CPOr, tacs)  = pors tacs
 |  eval_strategic (MIC.CPAlt,[])    = error "eval strategic failed. M.PAlt needs at least one tactic."
 |  eval_strategic (MIC.CPAlt,tacs)  = palts tacs;

(* iddfc *)
fun iddfc (limit:int)
  (smt_eval:'atom_str -> 'state MIC.stttac) (atac:'atom_str) (goal:'state) (trace:log) =
  let
    val wmt_eval_results = Seq2.try_seq (smt_eval atac goal) trace |> Seq.pull;
    val trace_leng = wmt_eval_results |> Option.map fst |> Option.map fst |> Option.map length;
    infix is_maybe_less_than
    fun (NONE is_maybe_less_than   (_:int)) = false
     |  (SOME x is_maybe_less_than (y:int)) = x < y;
    val smt_eval_results = if is_none trace_leng orelse trace_leng is_maybe_less_than limit
                          then Seq.make (fn () => wmt_eval_results) else Seq.empty;
  in
    smt_eval_results
  end;

end;

(*** MONADIC_PROVER: Put skeleton and flesh together. ***)
signature MONADIC_PROVER =
sig
  include MONADIC_INTERPRETER_CORE;
  include MONADIC_INTERPRETER;
  include MONADIC_INTERPRETER_PARAMS;
end;

(*** Monadic_Prover: Put skeleton and flesh together. ***)
structure Monadic_Prover : MONADIC_PROVER =
struct
  open Monadic_Interpreter_Core;
  open Monadic_Interpreter;
  open Monadic_Interpreter_Params;
end;