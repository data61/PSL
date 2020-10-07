(* Author: Andreas Lochbihler, ETH Zurich *)

subsection \<open>Ultrafilter\<close>

theory Applicative_Star imports
  Applicative
  "HOL-Nonstandard_Analysis.StarDef"
begin

applicative star (C, K, W)
for
  pure: star_of
  ap: Ifun
proof -
  show "star_of f \<star> star_of x = star_of (f x)" for f x by(fact Ifun_star_of)
qed(transfer; rule refl)+

end
