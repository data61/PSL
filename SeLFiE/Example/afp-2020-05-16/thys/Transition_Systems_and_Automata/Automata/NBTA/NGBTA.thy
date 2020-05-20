section \<open>Nondeterministic Generalized Büchi Transition Automata\<close>

theory NGBTA
imports "../Nondeterministic"
begin

  datatype ('label, 'state) ngbta = ngbta
    (alphabet: "'label set")
    (initial: "'state set")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state set")
    (accepting: "('state \<times> 'label \<times> 'state) pred gen")

  global_interpretation ngbta: automaton ngbta alphabet initial transition accepting
    defines path = ngbta.path and run = ngbta.run and reachable = ngbta.reachable and nodes = ngbta.nodes
    by unfold_locales auto
  global_interpretation ngbta: automaton_run ngbta alphabet initial transition accepting
    "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
    defines language = ngbta.language
    by standard

  abbreviation target where "target \<equiv> ngbta.target"
  abbreviation states where "states \<equiv> ngbta.states"
  abbreviation trace where "trace \<equiv> ngbta.trace"
  abbreviation successors where "successors \<equiv> ngbta.successors TYPE('label)"

end