open Complementation
open String
open List

fun eq x y = (x = y)

fun println w = print (w ^ "\n")

fun return x = [x]
fun bind xs f = concat (map f xs)
fun foldl' y f [] = y
  | foldl' y f (x :: xs) = foldl f x xs
fun takeWhile P [] = []
  | takeWhile P (x :: xs) = if P x then x :: takeWhile P xs else []
fun lookup x [] = NONE |
    lookup x ((k, v) :: xs) = if x = k then SOME v else lookup x xs
fun upto k = if k = 0 then [] else (k - 1) :: upto (k - 1)

fun splitFirst u w =
	if w = ""
	then if u = "" then SOME ("", "") else NONE
	else
		if isPrefix u w
		then SOME ("", extract (w, size u, NONE))
		else case splitFirst u (extract (w, 1, NONE)) of
			NONE => NONE |
			SOME (v, w') => SOME (str (sub (w, 0)) ^ v, w')
fun split u w = case splitFirst u w of NONE => [w] | SOME (v, w') => v :: split u w'

fun showInt k = Int.toString k
fun parseInt w = case Int.fromString w of SOME n => n

fun showNat k = showInt (integer_of_nat k)
fun parseNat w = nat_of_integer (parseInt w)

fun showString w = "\"" ^ w ^ "\""
fun parseString w = substring (w, 1, size w - 2)

fun showTuple f g (x, y) = "(" ^ f x ^ ", " ^ g y ^ ")"
fun showSequence f xs = concatWith ", " (map f xs)
fun showList f xs = "[" ^ showSequence f xs ^ "]"
fun showSet f (Set xs) = "{" ^ showSequence f xs ^ "}"
  | showSet f (Coset xs) = "- {" ^ showSequence f xs ^ "}"

fun showFormula f False = "f"
  | showFormula f True = "t"
  | showFormula f (Variable v) = f v
  | showFormula f (Negation x) = "!" ^ showFormula f x
  | showFormula f (Conjunction (x, y)) = "(" ^ showFormula f x ^ " & " ^ showFormula f y ^ ")"
  | showFormula f (Disjunction (x, y)) = "(" ^ showFormula f x ^ " | " ^ showFormula f y ^ ")"
fun parseFormula parseVariable input = let
  fun parseConstant w cs = if isPrefix w (implode cs) then [(w, drop (cs, size w))] else []
  fun parseAtom input1 =
    bind (parseConstant "f" input1) (fn (_, input2) =>
    return (False, input2))
    @
    bind (parseConstant "t" input1) (fn (_, input2) =>
    return (True, input2))
    @
    bind (parseVariable input1) (fn (variable, input2) =>
    return (Variable variable, input2))
    @
    bind (parseConstant "(" input1) (fn (_, input2) =>
    bind (parseDisjunction input2) (fn (disjunction, input3) =>
    bind (parseConstant ")" input3) (fn (_, input4) =>
    return (disjunction, input4))))
  and parseLiteral input1 =
    bind (parseAtom input1) (fn (atom, input2) =>
    return (atom, input2))
    @
    bind (parseConstant "!" input1) (fn (_, input2) =>
    bind (parseAtom input2) (fn (atom, input3) =>
    return (Negation atom, input3)))
  and parseConjunction input1 =
    bind (parseLiteral input1) (fn (literal, input2) =>
    return (literal, input2))
    @
    bind (parseLiteral input1) (fn (literal, input2) =>
    bind (parseConstant "&" input2) (fn (_, input3) =>
    bind (parseConjunction input3) (fn (conjunction, input4) =>
    return (Conjunction (literal, conjunction), input4))))
  and parseDisjunction input1 =
    bind (parseConjunction input1) (fn (conjunction, input2) =>
    return (conjunction, input2))
    @
    bind (parseConjunction input1) (fn (conjunction, input2) =>
    bind (parseConstant "|" input2) (fn (_, input3) =>
    bind (parseDisjunction input3) (fn (disjunction, input4) =>
    return (Disjunction (conjunction, disjunction), input4))))
  val input' = filter (not o Char.isSpace) (explode input)
  val result = map (fn (exp, _) => exp) (filter (fn (exp, rest) => null rest) (parseDisjunction input'))
  in hd result end

datatype hoaProperty =
  HoaVersion of string |
  HoaName of string |
  HoaProperties of string list |
  HoaAtomicPropositions of nat * string list |
  HoaAcceptanceConditionName of string |
  HoaAcceptanceCondition of string |
  HoaStartState of nat |
  HoaStateCount of nat
datatype hoaTransition = HoaTransition of nat formula * nat
datatype hoaState = HoaState of nat * nat list * hoaTransition list
datatype hoaAutomaton = HoaAutomaton of hoaProperty list * hoaState list

fun showHoaAutomaton (HoaAutomaton (ps, ss)) = let
  fun showProperty (HoaVersion w) = "HOA: " ^ w ^ "\n"
    | showProperty (HoaName w) = "name: " ^ showString w ^ "\n"
    | showProperty (HoaProperties ws) = "properties: " ^ concatWith " " ws ^ "\n"
    | showProperty (HoaAtomicPropositions (n, ps)) = "AP: " ^ showNat n ^ " " ^ concatWith " " (map showString ps) ^ "\n"
    | showProperty (HoaAcceptanceConditionName w) = "acc-name: " ^ w ^ "\n"
    | showProperty (HoaAcceptanceCondition w) = "Acceptance: " ^ w ^ "\n"
    | showProperty (HoaStartState p) = "Start: " ^ showNat p ^ "\n"
    | showProperty (HoaStateCount n) = "States: " ^ showNat n ^ "\n"
  fun showTransition (HoaTransition (a, q)) = "[" ^ showFormula showNat a ^ "]" ^ " " ^ showNat q ^ "\n"
  fun showState (HoaState (p, cs, ts)) = "State: " ^ showNat p ^ " " ^ showSet showNat (Set cs) ^ "\n" ^ String.concat (map showTransition ts)
  in String.concat (map showProperty ps) ^ "--BODY--" ^ "\n" ^ String.concat (map showState ss) ^ "--END--" ^ "\n" end
fun parseHoaAutomaton path = let
  fun parseVariable cs = case takeWhile Char.isDigit cs of
    [] => [] | xs => [(parseNat (implode xs), drop (cs, length xs))]
	fun inputLine input = case TextIO.inputLine input of SOME w => substring (w, 0, size w - 1)
	fun parseProperty w = case split ": " w of
	  ["HOA", u] => HoaVersion u |
	  ["name", u] => HoaName (substring (u, 1, size u - 2)) |
	  ["properties", u] => HoaProperties (split " " u) |
	  ["AP", u] => (case split " " u of v :: vs => HoaAtomicPropositions (parseNat v, map parseString vs)) |
	  ["acc-name", u] => HoaAcceptanceConditionName u |
	  ["Acceptance", u] => HoaAcceptanceCondition u |
	  ["Start", u] => HoaStartState (parseNat u) |
	  ["States", u] => HoaStateCount (parseNat u)
	fun parseProperties input = case inputLine input of w =>
	  if w = "--BODY--" then []
	  else parseProperty w :: parseProperties input
	fun parseTransition w = case split "] " (substring (w, 1, size w - 1)) of
	  [u, v] => HoaTransition (parseFormula parseVariable u, parseNat v)
	fun parseTransitions input = case inputLine input of w =>
	  if isPrefix "State" w orelse w = "--END--" then ([], w)
	  else case parseTransitions input of (ts, w') => (parseTransition w :: ts, w')
	fun parseStateHeader w = case split " {" w of
	  [u] => (parseNat u, []) |
	  [u, "}"] => (parseNat u, []) |
	  [u, v] => (parseNat u, map parseNat (split ", " (substring (v, 0, size v - 1))))
	fun parseState input w =
	  case split ": " w of ["State", u] =>
	  case parseStateHeader u of (p, cs) =>
	  case parseTransitions input of (ts, w') =>
	  (HoaState (p, cs, ts), w')
	fun parseStates input w =
	  if w = "--END--" then []
	  else case parseState input w of (p, w') => p :: parseStates input w'
	val input = TextIO.openIn path
	val properties = parseProperties input
	val states = parseStates input (inputLine input)
	in HoaAutomaton (properties, states) before TextIO.closeIn input end

fun toNbaei (HoaAutomaton (properties, states)) = let
  fun atomicPropositions (HoaAtomicPropositions (_, ps) :: properties) = ps
    | atomicPropositions (_ :: properties) = atomicPropositions properties
  val aps = atomicPropositions properties
  val alphabet = case pow {equal = eq} (image nat_of_integer (Set (upto (length aps)))) of Set pps => pps
  fun startStates [] = []
    | startStates (HoaStartState p :: properties) = p :: startStates properties
    | startStates (property :: properties) = startStates properties
  val initial = startStates properties
  fun expandTransition p f q = map (fn P => (p, (P, q))) (filter (fn x => satisfies {equal = eq} x f) alphabet)
  fun stateTransitions (HoaState (p, cs, ts)) = concat (map (fn HoaTransition (f, q) => expandTransition p f q) ts)
  val transitions = concat (map stateTransitions states)
  val accepting = map (fn HoaState (p, cs, ts) => p) (filter (fn HoaState (p, cs, ts) => not (null cs)) states)
  in (aps, Nbaei (alphabet, initial, transitions, accepting)) end
fun toHoaAutomaton aps (Nbaei (a, i, t, c)) = let
  val Set nodes = sup_seta {equal = eq}
    (image (fn (p, (_, q)) => insert {equal = eq} p (insert {equal = eq} q bot_set)) (Set t));
  val properties =
    [HoaVersion "v1"] @
    [HoaProperties ["trans-labels", "explicit-labels", "state-acc"]] @
    [HoaAtomicPropositions (nat_of_integer (length aps), aps)] @
    [HoaAcceptanceConditionName "Buchi"] @
    [HoaAcceptanceCondition "1 Inf(0)"] @
    map HoaStartState i @
    [HoaStateCount (nat_of_integer (length nodes))]
  fun literal ps ap = if member {equal = eq} ap ps then Variable ap else Negation (Variable ap)
  fun formula ps = foldl' True Conjunction (map (literal ps) (map nat_of_integer (upto (length aps))))
  fun transitions p = map (fn (p, (a, q)) => HoaTransition (formula a, q)) (filter (fn (p', (a, q)) => p' = p) t)
  fun state p = HoaState (p, if member {equal = eq} p (Set c) then [nat_of_integer 0] else [], transitions p)
  val states = map state nodes
  in HoaAutomaton (properties, states) end

fun showNbaei f g (Nbaei (a, i, t, c)) =
  showList f a ^ "\n" ^
  showList g i ^ "\n" ^
  showList (showTuple g (showTuple f g)) t ^ "\n" ^
  showList g c ^ "\n"
fun write_automaton f path automaton = let
	fun t (p, (a, q)) = Int.toString (integer_of_nat p) ^ " " ^ f a ^ " " ^ Int.toString (integer_of_nat q) ^ "\n"
	val output = TextIO.openOut path
	fun write [] = () | write (x :: xs) = (TextIO.output (output, t x); write xs)
	val _ = write (transitionei automaton)
	val _ = TextIO.closeOut output
	in () end

(* TODO: output number of explored states in emptiness check *)

val parameters = CommandLine.arguments ()
val _ = case hd parameters of
	"help" => println "Available Commands: help | complement <automaton> | equivalence <automaton1> <automaton2>" |
	"complement" => let
	  val (aps, nbaei) = toNbaei (parseHoaAutomaton (nth (parameters, 1)))
	  val nbai = nbae_nba_impl eq eq nbaei
	  val complement = toHoaAutomaton aps (complement_impl nbai)
	  in print (showHoaAutomaton complement) end |
	"complement_quick" => let
	  val (aps, nbaei) = toNbaei (parseHoaAutomaton (nth (parameters, 1)))
	  val nbai = nbae_nba_impl eq eq nbaei
	  val complement = complement_impl nbai
	  in write_automaton (showSet showNat) (nth (parameters, 2)) complement end |
	"equivalence" => let
	  val (aps1, nbaei1) = toNbaei (parseHoaAutomaton (nth (parameters, 1)))
	  val (aps2, nbaei2) = toNbaei (parseHoaAutomaton (nth (parameters, 2)))
	  val nbai1 = nbae_nba_impl eq eq nbaei1
	  val nbai2 = nbae_nba_impl eq eq nbaei2
	  in println (Bool.toString (language_equal_impl {equal = eq} nbai1 nbai2)) end |
	"product" => let
	  val (aps1, nbaei1) = toNbaei (parseHoaAutomaton (nth (parameters, 1)))
	  val (aps2, nbaei2) = toNbaei (parseHoaAutomaton (nth (parameters, 2)))
	  val nbai1 = nbae_nba_impl eq eq nbaei1
	  val nbai2 = nbae_nba_impl eq eq nbaei2
	  val product = product_impl {equal = eq} nbai1 nbai2
	  in write_automaton (showSet showNat) (nth (parameters, 3)) product end |
	"parse" => let
	  val ha = parseHoaAutomaton (nth (parameters, 1))
	  val (aps, nbaei) = toNbaei ha
	  val _ = println (showNbaei (showSet showNat) showNat nbaei)
	  in print (showHoaAutomaton (toHoaAutomaton aps nbaei)) end