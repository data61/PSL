signature RANDOMISED_SOCIAL_CHOICE =
sig

type lottery

val lotteryT : typ -> typ
val sdsT : typ -> typ -> typ

val probability : lottery -> term list -> Rat.rat
val stochastic_dominance : Preference_Profiles.prefs -> lottery * lottery -> bool
val strict_stochastic_dominance : Preference_Profiles.prefs -> lottery * lottery -> bool
val mk_support_witness : Preference_Profiles.profile -> Preference_Profiles.support * lottery -> 
  Preference_Profiles.support * lottery * term

(* Construct the linear program that encodes SD inefficiency of the given support *)
val mk_inefficiency_lp : 
  Preference_Profiles.profile -> Preference_Profiles.support -> (string list * string * int) list

(* Find a lottery that is strictly SD-preferred to the given support and the agent who
   strictly prefers it. *)
val find_inefficiency_witness : 
  Preference_Profiles.profile -> Preference_Profiles.support -> (lottery * term) option

(* Finds all non-singleton inefficient supports with a inefficiency certificate for each one.
   (non-singleton because singleton inefficient supports are simply Pareto losers *)
val find_minimal_inefficient_supports : 
  Preference_Profiles.profile -> (Preference_Profiles.support * lottery * term) list

end

structure Randomised_Social_Choice : RANDOMISED_SOCIAL_CHOICE =
struct

type lottery = (term * Rat.rat) list

local
  open Rat_Linear_Program
  open Preference_Profiles
in

fun lotteryT altT = Type (@{type_name pmf}, [altT])
fun sdsT agentT altT = pref_profileT agentT altT --> lotteryT altT

fun mk_inefficiency_lp p support =
  let
    val alts = alts_of_profile p
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    val in_support = member op aconv support
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    fun mk_slack_var i j = "r" ^ Int.toString i ^ "_" ^ Int.toString j

    fun mk_ineqs_for_agent acc _ [] _ _ = acc
      | mk_ineqs_for_agent acc _ [_] _ _ = acc
      | mk_ineqs_for_agent acc (lhs, rhs) (xs::xss) j i =
          let
            val lhs' = map mk_lottery_var xs @ lhs
            val rhs' = length (filter in_support xs) + rhs
          in
            mk_ineqs_for_agent ((lhs',mk_slack_var i j,rhs')::acc) (lhs',rhs') xss (j+1) i
          end
  in
    fold (fn (_, r) => fn (i,acc) => (i+1, mk_ineqs_for_agent acc ([],0) r 0 i)) p (0, []) |> snd
  end

fun lp_constr_to_qsopt_constr n (lhs, slack, rhs) =
  let
    val n = Rat.of_int n
    val lhs' = (@~1, slack) :: map (fn x => (n, x)) lhs
  in
    (lhs', EQ, Rat.of_int rhs)
  end

fun mk_inefficiency_lp_qsopt p support =
  let
    val constrs = mk_inefficiency_lp p support
    val alts = alts_of_profile p
    val n = length support
    val sum = map (fn x => (@1, x))
    val alt_ids = alts ~~ List.tabulate (length alts, Int.toString);
    fun mk_lottery_var x = "q" ^ the (AList.lookup op aconv alt_ids x)
    val lottery_vars = map mk_lottery_var alts
    val slack_vars = map #2 constrs
 
    val constrs' = map (lp_constr_to_qsopt_constr n) constrs
    val eq = (sum lottery_vars, EQ, @1)
  in
    (MAXIMIZE, sum slack_vars, eq :: constrs', [])
  end


fun find_inefficiency_witness p lottery =
  let
    val alts = alts_of_profile p
    val lottery_vars = List.tabulate (length alts, fn x => "q" ^ Int.toString x);
    val slack_vars = 
      p ~~ List.tabulate (length p, Int.toString)
      |> map (fn ((x,prefs),i) => 
           (x, List.tabulate (length prefs - 1, fn j => "r" ^ i ^ "_" ^ Int.toString j)))
    fun the_default x NONE = x
      | the_default _ (SOME y) = y

    fun process_solution (diff, assignments) = 
      let
        val get_val = the_default @0 o AList.lookup op= assignments
        val i =
          slack_vars 
          |> find_first (snd #> exists (fn x => get_val x > @0)) 
          |> Option.map fst
      in 
        if diff = @0 then 
          NONE 
        else 
          Option.map (fn i => (alts ~~ map get_val lottery_vars, i)) i
      end
  in 
    case solve_program (mk_inefficiency_lp_qsopt p lottery) of
      Optimal x => process_solution x
    | _ => raise Match
  end

fun power_set xs =
  let
    fun go acc [] = [acc]
      | go acc (x::xs) = go acc xs @ go (x::acc) xs
  in
    go [] xs |> sort (int_ord o apply2 length)
  end

fun is_singleton [_] = true
  | is_singleton _ = false

fun find_minimal_inefficient_supports p =
  let
    val alts = subtract op aconv (map #1 (pareto_losers p)) (alts_of_profile p)
    fun go supp acc =
      if List.null supp orelse is_singleton supp orelse
            member (fn (a, b) => subset op aconv (#1 b, a)) acc supp then
        acc
      else 
        case find_inefficiency_witness p supp of
          NONE => acc
        | SOME (lott, i) => (supp, lott, i) :: acc
  in
    fold go (power_set alts) []
  end

end

fun probability (lott1 : lottery) xs =
  lott1 |> filter (member op aconv xs o fst) |> (fn xs => fold (fn x => fn y => snd x + y) xs @0)

fun uniform_lottery xs = 
  let
    val p = Rat.make (1, length xs)
  in
    map (fn x => (x, p)) xs
  end

fun stochastic_dominance p (lott1, lott2) =
  let
    fun go _ [] = true
      | go _ [_] = true
      | go (prob1 : Rat.rat, prob2 : Rat.rat) (xs::xss) = 
          let 
            val (prob1, prob2) = (prob1 + probability lott1 xs, prob2 + probability lott2 xs)
          in  
            prob1 <= prob2 andalso go (prob1, prob2) xss
          end
  in
    go (@0, @0) p
  end

fun strict_stochastic_dominance p (lott1, lott2) =
  stochastic_dominance p (lott1, lott2) andalso not (stochastic_dominance p (lott2, lott1))  

fun mk_support_witness p (supp, lott) =
  let
    val lott' = uniform_lottery supp
    val i = find_first (fn (_, ps) => not (stochastic_dominance ps (lott, lott'))) p
            |> Option.map fst
  in
    case i of
      NONE => error "Not a proper inefficiency wittnes."
    | SOME i => (supp, lott, i)
  end

end