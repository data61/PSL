section \<open>Deterministic Büchi Transition Automata\<close>

theory DBTA
imports "../Deterministic"
begin

  datatype ('label, 'state) dbta = dbta
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "('state \<times> 'label \<times> 'state) pred")

  global_interpretation dbta: automaton dbta alphabet initial transition accepting
    defines path = dbta.path and run = dbta.run and reachable = dbta.reachable and nodes = dbta.nodes
    by unfold_locales auto
  global_interpretation dbta: automaton_run dbta alphabet initial transition accepting
    "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    defines language = dbta.language
    by standard

  abbreviation target where "target \<equiv> dbta.target"
  abbreviation states where "states \<equiv> dbta.states"
  abbreviation trace where "trace \<equiv> dbta.trace"
  abbreviation successors where "successors \<equiv> dbta.successors TYPE('label)"

end