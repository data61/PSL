section \<open>Nondeterministic Büchi Transition Automata\<close>

theory NBTA
imports "../Nondeterministic"
begin

  datatype ('label, 'state) nbta = nbta
    (alphabet: "'label set")
    (initial: "'state set")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state set")
    (accepting: "('state \<times> 'label \<times> 'state) pred")

  global_interpretation nbta: automaton nbta alphabet initial transition accepting
    defines path = nbta.path and run = nbta.run and reachable = nbta.reachable and nodes = nbta.nodes
    by unfold_locales auto
  global_interpretation nbta: automaton_run nbta alphabet initial transition accepting
    "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    defines language = nbta.language
    by standard

  abbreviation target where "target \<equiv> nbta.target"
  abbreviation states where "states \<equiv> nbta.states"
  abbreviation trace where "trace \<equiv> nbta.trace"
  abbreviation successors where "successors \<equiv> nbta.successors TYPE('label)"

end