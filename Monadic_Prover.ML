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
  datatype cprim_str = CClarsimp | CSimp | CFastforce | CAuto | CInduct
                     | CInductTac | CCoinduction | CCases | CCaseTac | CRule | CErule;
  datatype cstatic = CPrim of cprim_str | CSpec of cspecial | CSubt of csubtool | CUser of string;
  datatype catom_str = CSttc of cstatic | CDyn of cprim_str;
  datatype cstrategic = CSolve1 | CRepeatN | CCut of int;
  datatype core_str =
    CAtom of catom_str
  | CSkip
  | CFail
  | COr       of (core_str * core_str)
  | CPOr      of (core_str * core_str)
  | CSeq      of (core_str * core_str)
  | CAlt      of (core_str * core_str)
  | CPAlt     of (core_str * core_str)
  | CRepBT    of core_str
  | CRepNB    of core_str
  | CFails    of core_str (* Fails cannot be defined as just a syntactic sugar as the definition involves goal.*)
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
  datatype cprim_str = (*default tactics*) CClarsimp | CSimp | CFastforce | CAuto | CInduct
                     | CInductTac | CCoinduction | CCases | CCaseTac | CRule | CErule;
  datatype combine = Unique | First;
  datatype cstatic = CPrim of cprim_str | CSpec of cspecial | CSubt of csubtool | CUser of string;
  datatype catom_str = CSttc of cstatic | CDyn of cprim_str;
  (*atom_strategic without monadic-interpretation.*)
  datatype cstrategic = CSolve1 | CRepeatN | CCut of int;
  infix 0 CSeq CAlt  COr CPAlt CPOr;
  datatype core_str =
    CAtom of catom_str
  | CSkip
  | CFail
  | COr       of (core_str * core_str)
  | CPOr      of (core_str * core_str)
  | CSeq      of (core_str * core_str)
  | CAlt      of (core_str * core_str)
  | CPAlt     of (core_str * core_str)
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
       fun eval (CSttc str) goal = (eval_prim str goal
                                    handle THM _   => mzero
                                         | ERROR _ => mzero
                                         | Empty   => mzero
                                         | TERM _  => mzero
                                         | TYPE _  => mzero)
         | eval (CDyn str) goal =
           let
             (*Should I factor this out to Monadic_Interpreter_Params?*)
             fun how_to_combine_results CClarsimp    = Unique
              |  how_to_combine_results CSimp        = Unique
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
                  |> Seq.of_list |> msum handle Empty => mzero);
             val combination          = how_to_combine_results str;
             val tactics              = eval_para str goal;
             (*Sometimes, Isabelle does not have appropriate rules.*)
             val tactics_with_handler = Seq.map (fn tactic => fn g => tactic g
                                        handle THM _   => mzero
                                             | ERROR _ => mzero
                                             | Empty   => mzero
                                             | TERM _  => mzero
                                             | TYPE _  => mzero) tactics;
             val all_results          = Seq2.map_arg goal tactics_with_handler
                                        handle THM _   => Seq.empty
                                             | ERROR _ => Seq.empty
                                             | TERM _  => Seq.empty
                                             | TYPE _  => Seq.empty
                                             | Empty   => Seq.empty;
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

(*** Monadic_Interpreter_Core: The core of PSL with the core-syntax. ***)
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

(*** Monadic_Interpreter_Core: The core of PSL with the core-syntax. ***)
structure Monadic_Interpreter_Core : MONADIC_INTERPRETER_CORE =
 mk_Monadic_Interpreter_Core_from_Monad_0plus_Min
 (struct structure Log = Log; structure M0P_Min = Seq_M0P_Min end);

(*** MONADIC_INTERPRETER: The core of PSL with the surface-syntax. ***)
signature MONADIC_INTERPRETER =

sig

datatype str =
(*prim_str*)
  Clarsimp
| Simp
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
(*parallel tactical*)
| PAlt of str Seq.seq
| POr  of str Seq.seq
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

val desugar : str -> Monadic_Interpreter_Core.core_str;

end;

(*** Monadic_Interpreter: The core of PSL with the surface-syntax. ***)
structure Monadic_Interpreter : MONADIC_INTERPRETER =
struct

open Monadic_Interpreter_Core;

datatype str =
(*prim_str*)
  Clarsimp
| Simp
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
(*parallel tactical*)
| PAlt of str Seq.seq
| POr  of str Seq.seq
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

infix 0 CSeq CAlt  COr CPAlt CPOr;

local
  val prim = CAtom o CSttc o CPrim;
  val dyna = CAtom o CDyn;
  val subt = CAtom o CSttc o CSubt;
  val spec = CAtom o CSttc o CSpec;
  val user = CAtom o CSttc o CUser;
in

fun desugar Clarsimp        = prim CClarsimp
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
    (*parallel strategic*)
 |  desugar (PAlt strs1)    = (case Seq.pull strs1 of
     NONE               => error "Alt needs at least one arguement."
   | SOME (str1, strs2) => case Seq.pull strs2 of
       NONE   => desugar str1
     | SOME _ => desugar str1 CPAlt (desugar (PAlt strs2)))
 |  desugar (POr strs1)     = (case Seq.pull strs1 of
     NONE               => error "Alt needs at least one arguement."
   | SOME (str1, strs2) => case Seq.pull strs2 of
       NONE   => desugar str1
     | SOME _ => desugar str1 CPOr (desugar (POr strs2)))
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
    (* on-monadic strategics that are handled by "eval_strategic".*)
 |  desugar (Solve1 str)    = CStrategic (CSolve1, [desugar str])
 |  desugar (RepNT str)     = CStrategic (CRepeatN, [desugar str])
 |  desugar (Cut (i, str))  = CStrategic (CCut i, [desugar str])
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
(*do_trace and show_trace are for debugging only.*)
val do_trace = false;
fun show_trace text = if do_trace then tracing text else ();

local
structure User_Seed : DYNAMIC_TACTIC_GENERATOR_SEED =
struct
  type modifier  = string;
  type modifiers = string list;
  fun get_all_modifiers _ = [];
  fun mods_to_string mods = String.concatWith " " mods;
end;
structure User_Tactic_Generator : DYNAMIC_TACTIC_GENERATOR =
  mk_Dynamic_Tactic_Generator (User_Seed);
in
fun user_stttac (meth:string) =
  User_Tactic_Generator.meth_name_n_modifiers_to_stttac_on_state meth [(* ignores log *)];
end;

(*I cannot move the definition of "eval_prim" into mk_Monadic_Interpreter,
  because its type signature is too specific.*)
fun eval_prim (prim:MIC.cstatic) (goal_state:state) =
  let
    (*For eval_prim.*)
    val string_to_stttac = Dynamic_Utils.string_to_stttac_on_pstate;
    val tac_on_proof_state : state MIC.stttac = case prim of
      MIC.CPrim MIC.CClarsimp =>     (show_trace "CClarsimp";      string_to_stttac "clarsimp")
    | MIC.CPrim MIC.CSimp =>         (show_trace "CSimp";          string_to_stttac "simp")
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
    | MIC.CUser tac_name =>      (show_trace tac_name;         user_stttac tac_name);
  in
     tac_on_proof_state goal_state
        handle THM _ =>   MIC.mzero
             | ERROR _ => MIC.mzero
             | TERM _ =>  MIC.mzero
             | Empty =>   MIC.mzero
             | TYPE _ =>  MIC.mzero : state MIC.monad
  end;

fun eval_para (str:MIC.cprim_str) (state:Proof.state) =
  let
    type 'a stttac = 'a Dynamic_Utils.stttac;
    val get_state_stttacs = case str of
        MIC.CSimp =>        (show_trace "CPara_Simp";        Dynamic_Tactic_Generation.simp)
      | MIC.CInduct =>      (show_trace "CPara_Induct";      Dynamic_Tactic_Generation.induct)
      | MIC.CInductTac =>   (show_trace "CPara_InductTac";   Dynamic_Tactic_Generation.induct_tac)
      | MIC.CCoinduction => (show_trace "CPara_Coinduction"; Dynamic_Tactic_Generation.coinduction)
      | MIC.CCases =>       (show_trace "CPara_Cases";       Dynamic_Tactic_Generation.cases)
      | MIC.CCaseTac =>     (show_trace "CPara_CaseTac";     Dynamic_Tactic_Generation.case_tac)
      | MIC.CRule =>        (show_trace "CPara_Rule";        Dynamic_Tactic_Generation.rule)
      | MIC.CErule =>       (show_trace "CPara_Erule";       Dynamic_Tactic_Generation.erule)
      | MIC.CFastforce =>   (show_trace "CPara_Fastforce";   Dynamic_Tactic_Generation.clarsimp)
      | MIC.CAuto =>        (show_trace "CPara_Auto";        Dynamic_Tactic_Generation.auto)
      | MIC.CClarsimp =>    (show_trace "CPara_Clarsimp";    Dynamic_Tactic_Generation.clarsimp)
  in
    (*It is okay to use the type list internally,
      as long as the overall monadic interpretation framework is instantiated to Seq.seq for
      monad with 0 and plus.*)
    get_state_stttacs state
    handle THM _   => Seq.empty
         | ERROR _ => Seq.empty
         | Empty   => Seq.empty
         | TERM _  => Seq.empty
         | TYPE _  => Seq.empty: state stttac Seq.seq
  end;

fun m_equal (st_mona1:state MIC.monad) (st_mona2:state MIC.monad) =
(*Probably, I do not have to check the entire sequence in most cases.
  As the length of sequences can be infinite in general, I prefer to test a subset of these.*)
  let
    type lstt   = Log_Min.monoid_min * state;
    type lstts  = lstt seq;
    fun are_same_one (x : lstt,  y : lstt)  = apply2 (#goal o Proof.goal o snd) (x, y)
                                           |> Thm.eq_thm;
    fun are_same_seq (xs: lstts, ys: lstts) = Seq2.same_seq are_same_one (xs, ys) ;
    val xs_5 : lstts                        = st_mona1 [] |> Seq.take 5;
    val ys_5 : lstts                        = st_mona2 [] |> Seq.take 5;
  in
    are_same_seq (xs_5, ys_5)
  end;

fun solve_1st_subg (tac : state MIC.stttac) (goal:state) (log:log) =
  let
    val get_thm = Isabelle_Utils.proof_state_to_thm;
    fun same_except_for_fst_prem' x y = Isabelle_Utils.same_except_for_fst_prem (get_thm x) (get_thm y)
  in
    tac goal log
    |> Seq.filter (fn (_, st')  => same_except_for_fst_prem' goal st'):(log * state) Seq.seq
  end;

fun repeat_n (tac : state MIC.stttac) (goal : state) = (fn (log:log) =>
  let
    fun repeat_n' (0:int) (g:state) = MIC.return g
     |  repeat_n' (n:int) (g:state) = if n < 0 then error "" else
          MIC.bind (tac g) (repeat_n' (n - 1));
    val subgoal_num = Isabelle_Utils.proof_state_to_thm goal |> Thm.nprems_of;
  in
    (*We have to add 1 because of Isabelle's strange evaluation (parse-twice thingy).*)
    repeat_n' subgoal_num goal log : (log * state) Seq.seq
  end) : state MIC.monad;

fun cut (limit:int) (tac:state MIC.stttac) (goal:state) = Seq.take limit o tac goal : state MIC.monad;

fun eval_strategic (MIC.CSolve1, [tac : state MIC.stttac])  = solve_1st_subg tac
 |  eval_strategic (MIC.CSolve1, _)  = error "eval_strategic failed. M.Solve1 needs exactly one tactic."
 |  eval_strategic (MIC.CRepeatN, [tac : state MIC.stttac]) = repeat_n tac
 |  eval_strategic (MIC.CRepeatN, _) = error "eval_strategic failed. M.RepeatN needs exactly one tactic."
 |  eval_strategic (MIC.CCut lim, [tac : state MIC.stttac]) =
      if lim > 0 then cut lim tac
      else error "eval_strategic failed. The limit for CCut has to be larger than 0."
 |  eval_strategic (MIC.CCut _, _)   = error "eval strategic failed. M.CCut needs exactly one tactic.";

fun iddfc (limit:int)
  (smt_eval:'atom_str -> 'state MIC.stttac) (atac:'atom_str) (goal:'state) (trace:log) =
  let
    val wmt_eval_results = (smt_eval atac goal trace
                            handle THM _  => Seq.empty
                                 | Empty  => Seq.empty
                                 | TERM _ => Seq.empty
                                 | TYPE _ => Seq.empty) |> Seq.pull;
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