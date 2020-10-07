(*File: Lattice.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory Lattice imports Main begin
section\<open>Lattices\<close>

text\<open>In preparation of the encoding of the type system of Hunt and
Sands, we define some abstract type of lattices, together with the
operations $\bot$, $\sqsubseteq$ and $\sqcup$, and some obvious
axioms.\<close>

typedecl L (*The lattice*)

axiomatization
  bottom :: L and
  LEQ :: "L \<Rightarrow> L \<Rightarrow> bool" and
  LUB :: "L \<Rightarrow> L \<Rightarrow> L"
where
  LAT1: "LEQ bottom p" and
  LAT2: "LEQ p1 p2 \<Longrightarrow> LEQ p2 p3 \<Longrightarrow> LEQ p1 p3" and
  LAT3: "LEQ p (LUB p q)" and
  LAT4: "LUB p q = LUB q p" and
  LAT5: "LUB p (LUB q r) = LUB (LUB p q) r" and
  LAT6: "LEQ x x" and
  LAT7: "p = LUB p p"
text\<open>End of theory Lattice\<close>
end
