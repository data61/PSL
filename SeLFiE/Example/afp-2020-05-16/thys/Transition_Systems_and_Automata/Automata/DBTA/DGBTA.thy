section \<open>Deterministic Generalized Büchi Transition Automata\<close>

theory DGBTA
imports "../Deterministic"
begin

  datatype ('label, 'state) dgbta = dgbta
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "('state \<times> 'label \<times> 'state) pred gen")

  global_interpretation dgbta: automaton dgbta alphabet initial transition accepting
    defines path = dgbta.path and run = dgbta.run and reachable = dgbta.reachable and nodes = dgbta.nodes
    by unfold_locales auto
  global_interpretation dgbta: automaton_run dgbta alphabet initial transition accepting
    "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
    defines language = dgbta.language
    by standard

  abbreviation target where "target \<equiv> dgbta.target"
  abbreviation states where "states \<equiv> dgbta.states"
  abbreviation trace where "trace \<equiv> dgbta.trace"
  abbreviation successors where "successors \<equiv> dgbta.successors TYPE('label)"

end