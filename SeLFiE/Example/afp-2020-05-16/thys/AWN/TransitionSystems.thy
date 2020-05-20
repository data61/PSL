(*  Title:       TransitionSystems.thy
    License:     BSD 2-Clause. See LICENSE.
    Author:      Timothy Bourke
*)

section "Transition systems (automata)"

theory TransitionSystems
imports Main
begin

type_synonym ('s, 'a) transition = "'s \<times> 'a \<times> 's"

record ('s, 'a) automaton =
  init :: "'s set"
  trans :: "('s, 'a) transition set"

end

