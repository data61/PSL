(*
    Serialization of DRAs in the HOA format.

    Benedikt Seidl
*)

open LTL

structure HOA : sig
  val serialize : string ltlc -> (string set, nat) draei -> string
end = struct

  (* Metadata *)

  val tool = "LTL to DRA translation based on the Master Theorem"
  val version = "0.1"
  val properties = ["transition-labels", "state-acc", "deterministic"]
  val acc_name = "Rabin"

  fun quote s = "\"" ^ s ^ "\""

  fun bracket true s = "(" ^ s ^ ")"
    | bracket false s = s

  fun nat_to_string n = IntInf.toString (integer_of_nat n)

  fun ltlc_to_string b True_ltlc = "true"
    | ltlc_to_string b False_ltlc = "false"
    | ltlc_to_string b (Prop_ltlc s) = s
    | ltlc_to_string b (Not_ltlc x) = "!" ^ ltlc_to_string true x
    | ltlc_to_string b (And_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " & " ^ ltlc_to_string true x2)
    | ltlc_to_string b (Or_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " | " ^ ltlc_to_string true x2)
    | ltlc_to_string b (Implies_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " -> " ^ ltlc_to_string true x2)
    | ltlc_to_string b (Next_ltlc x) = bracket b ("X " ^ ltlc_to_string true x)
    | ltlc_to_string b (Final_ltlc x) = bracket b ("F " ^ ltlc_to_string true x)
    | ltlc_to_string b (Global_ltlc x) = bracket b ("G " ^ ltlc_to_string true x)
    | ltlc_to_string b (Until_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " U " ^ ltlc_to_string true x2)
    | ltlc_to_string b (Release_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " R " ^ ltlc_to_string true x2)
    | ltlc_to_string b (WeakUntil_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " W " ^ ltlc_to_string true x2)
    | ltlc_to_string b (StrongRelease_ltlc (x1, x2)) = bracket b (ltlc_to_string true x1 ^ " M " ^ ltlc_to_string true x2)

  fun mapi f xs =
    let
      fun inner (x, (i, xs)) = (i + 1, f (i, x) :: xs)
    in
      List.rev (#2 (foldl inner (0, []) xs))
    end

  (* TODO formalize in Isabelle *)
  fun group_sorted f xs =
    let
      fun inner (t, ([], acc)) = ([t], acc)
        | inner (t, (x :: xs, acc)) = if f (t, x)
            then ([t], (x :: xs) :: acc)
            else (t :: x :: xs, acc)
      val (grp, acc) = foldl inner ([], []) xs
    in
      case grp of
           [] => acc
         | x :: xs => (x :: xs) :: acc
    end

  (* Header *)

  fun serialize_aps aps =
    Int.toString (List.length aps) ^ " " ^ String.concatWith " " (List.map quote aps)

  fun serialize_rabin_pair (i, _) =
    "Inf(" ^ Int.toString (2 * i) ^ ") & Fin(" ^ Int.toString (2 * i + 1) ^ ")"

  fun serialize_acceptance acc =
    Int.toString (2 * List.length acc) ^ " "
      ^ String.concatWith " | " (mapi serialize_rabin_pair acc)

  fun serialize_header phi aut states =
    "HOA: v1\n"
      ^ "tool: " ^ quote tool ^ " " ^ quote version ^ "\n"
      ^ "name: " ^ quote ("DRA for " ^ ltlc_to_string false phi) ^ "\n"
      ^ "properties: " ^ String.concatWith " " properties ^ "\n"
      ^ "States: " ^ Int.toString (List.length states) ^ "\n"
      ^ "Start: " ^ nat_to_string (initialei aut) ^ "\n"
      ^ "AP: " ^ serialize_aps (atoms_ltlc_list_literals phi) ^ "\n"
      ^ "Acceptance: " ^ serialize_acceptance (conditionei aut) ^ "\n"
      ^ "acc-name: " ^ acc_name ^ "\n"

  (* Body *)

  fun iterate_aps phi f =
    let
      fun inner (i, a) = if f a
        then Int.toString i
        else "!" ^ Int.toString i
    in
      case atoms_ltlc_list_literals phi of
        [] => "[t]"
      | xs => "[" ^ String.concatWith "&" (mapi inner xs) ^ "]"
    end

  fun serialize_label phi (Set xs) =
        iterate_aps phi (fn a => List.exists (fn b => a = b) xs)
    | serialize_label phi (Coset xs) =
        iterate_aps phi (fn a => List.all (fn b => a <> b) xs)

  fun serialize_transition phi (from, (label, to)) =
    serialize_label phi label ^ " " ^ nat_to_string to ^ "\n"

  fun serialize_state_labels acc state =
    let
      fun inner (i, (inf, fin)) =
        (if (List.exists (fn j => state = j) inf) then [Int.toString (2 * i)] else [])
          @ (if (List.exists (fn j => state = j) fin) then [Int.toString (2 * i + 1)] else [])
    in
      "{" ^ String.concatWith " " (List.concat (mapi inner acc)) ^ "}"
    end

  fun serialize_state phi aut state =
    "State: " ^ nat_to_string (#1 (List.hd state)) ^ " "
      ^ serialize_state_labels (conditionei aut) (#1 (List.hd state)) ^ "\n"
      ^ String.concat (List.map (serialize_transition phi) state)

  fun serialize_body phi aut states =
    String.concatWith "\n" (List.map (serialize_state phi aut) states)

  (* Automaton *)

  fun serialize phi aut =
    let
      val states = group_sorted (fn (x, y) => integer_of_nat (#1 x) <
      integer_of_nat (#1 y)) (List.rev (sort_transitions (transitionei aut)))
    in
      serialize_header phi aut states
        ^ "\n--BODY--\n"
        ^ serialize_body phi aut states
        ^ "--END--"
    end
end;
