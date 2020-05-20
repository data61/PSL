(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Eval
imports
  Extra
  Kripke
  ODList
begin
(*>*)

subsection\<open>Algorithmic evaluation\<close>

text\<open>

\label{sec:kbps-theory-eval}

Generically evaluate a knowledge formula with respect to a few
operations.

Intuition: Tableau, returns the subset of X where the formula
holds. Could generalise that to the set of \emph{all} states where the
formula holds, at least for the propositional part. This is closer to
the BDD interpretation. However in an explicit-state setup we want the
smallest sets that work.

Given an implementation of the relations, compute the subset of @{term
"X"} where @{term "X"} holds. Here we reduce space consumption by
only considering the reachable states at the cost of possible
reevaluation... BDDs give us some better primitives in some cases (but
not all). Something to ponder.

\<close>

function
  eval_rec :: "(('rep :: linorder) odlist \<Rightarrow> 'p \<Rightarrow> 'rep odlist)
             \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'rep odlist)
             \<Rightarrow> ('a list \<Rightarrow> 'rep \<Rightarrow> 'rep odlist)
             \<Rightarrow> 'rep odlist
             \<Rightarrow> ('a, 'p) Kform
             \<Rightarrow> 'rep odlist"
where
  "eval_rec val R CR X (Kprop p)     = val X p"
| "eval_rec val R CR X (Knot \<phi>)      = ODList.difference X (eval_rec val R CR X \<phi>)"
| "eval_rec val R CR X (Kand \<phi> \<psi>)    = ODList.intersect (eval_rec val R CR X \<phi>) (eval_rec val R CR X \<psi>)"
| "eval_rec val R CR X (Kknows a \<phi>)  = ODList.filter (\<lambda>s. eval_rec val R CR (R a s) (Knot \<phi>) = ODList.empty) X"
| "eval_rec val R CR X (Kcknows as \<phi>) = (if as = [] then X else ODList.filter (\<lambda>s. eval_rec val R CR (CR as s) (Knot \<phi>) = ODList.empty) X)"
(*<*)
  by pat_completeness auto

fun
  kf_k_measure :: "('a, 'p) Kform \<Rightarrow> nat"
where
  "kf_k_measure (Kprop p)  = 0"
| "kf_k_measure (Knot \<phi>)   = kf_k_measure \<phi>"
| "kf_k_measure (Kand \<phi> \<psi>) = kf_k_measure \<phi> + kf_k_measure \<psi>"
| "kf_k_measure (Kknows a \<phi>) = 1 + kf_k_measure \<phi>"
| "kf_k_measure (Kcknows as \<phi>) = 1 + kf_k_measure \<phi>"

termination eval_rec
  apply (relation "measures [\<lambda>(_, _, _, _, \<phi>). size \<phi>, \<lambda>(_, _, _, _, \<phi>). kf_k_measure \<phi>]")
  apply auto
  done

(*>*)
text\<open>

This function terminates because (recursively) either the formula
decreases in size or it contains fewer knowledge modalities.

We need to work a bit to interpret subjective formulas.

Expect @{term "X"} to be the set of states we need to evaluate @{term
"\<phi>"} at for @{term "K a \<phi>"} to be true.

Kcknows can be treated the same as Kknows... Just deals with top-level
boolean combinations of knowledge formulas.

The K cases are terrible. For CK we actually show @{term "K (CK
\<phi>)"}. might be easier to futz that here.

\<close>

fun
  evalS :: "(('rep :: linorder) odlist \<Rightarrow> 'p \<Rightarrow> 'rep odlist)
          \<Rightarrow> ('a \<Rightarrow> 'rep \<Rightarrow> 'rep odlist)
          \<Rightarrow> ('a list \<Rightarrow> 'rep \<Rightarrow> 'rep odlist)
          \<Rightarrow> 'rep odlist
          \<Rightarrow> ('a, 'p) Kform \<Rightarrow> bool"
where
  "evalS val R CR X (Kprop p)      = undefined"
| "evalS val R CR X (Knot \<phi>)       = (\<not>evalS val R CR X \<phi>)"
| "evalS val R CR X (Kand \<phi> \<psi>)     = (evalS val R CR X \<phi> \<and> evalS val R CR X \<psi>)"
| "evalS val R CR X (Kknows a \<phi>)   = (eval_rec val R CR X (Knot \<phi>) = ODList.empty)"
| "evalS val R CR X (Kcknows as \<phi>) = (eval_rec val R CR (ODList.big_union (CR as) (toList X)) (Knot \<phi>) = ODList.empty)"

text\<open>

We'd like some generic proofs about these functions but it's simpler
just to prove concrete instances.

The K cases are inefficient -- we'd like to memoise them,
etc. However it is suggestive of the ``real'' BDD
implementations. Compare with Halpern/Moses who do it more efficiently
in time (linear?) at the cost of space. In practice the knowledge
formulas are not deeply nested, so it is not worth trying too hard
here.

In general this is less efficient than the tableau approach of
\citet[Proposition~3.2.1]{FHMV:1995}, which labels all states with all
formulas. However it is often the case that the set of relevant worlds
is much smaller than the set of all system states.

\<close>
(*<*)

end
(*>*)
