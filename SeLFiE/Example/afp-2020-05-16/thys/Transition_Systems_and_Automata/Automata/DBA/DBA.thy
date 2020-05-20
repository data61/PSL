section \<open>Deterministic Büchi Automata\<close>

theory DBA
imports "../Deterministic"
begin

  datatype ('label, 'state) dba = dba
    (alphabet: "'label set")
    (initial: "'state")
    (transition: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (accepting: "'state pred")

  (* TODO: if we interpret everything at once, some abbreviations don't get folded back
    see DBA_Combine.intersection_list.combine_finite *)
  global_interpretation dba: automaton dba alphabet initial transition accepting
    defines path = dba.path and run = dba.run and reachable = dba.reachable and nodes = dba.nodes
    by unfold_locales auto
  global_interpretation dba: automaton_run dba alphabet initial transition accepting "\<lambda> P w r p. infs P (p ## r)"
    defines language = dba.language
    by standard

  abbreviation target where "target \<equiv> dba.target"
  abbreviation states where "states \<equiv> dba.states"
  abbreviation trace where "trace \<equiv> dba.trace"
  (* TODO: why does this happen? if I can fix it here, why can't the interpretation do it?
    same happens with reachable, requiring the use of defines directives *)
  abbreviation successors where "successors \<equiv> dba.successors TYPE('label)"

end