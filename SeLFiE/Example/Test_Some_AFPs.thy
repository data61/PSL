(*  Title:      SeLFiE/Example/Test_Some_AFPs.thy
    Author:     Yutaka Nagashima

Smoke-test theory that merely imports a handful of AFP entries, to check that
they still load under the current Isabelle/AFP versions.
*)
theory Test_Some_AFPs
  imports
    "afp-2020-05-16/thys/KD_Tree/Nearest_Neighbors"
    "afp-2020-05-16/thys/Hybrid_Logic/Hybrid_Logic"
    "afp-2020-05-16/thys/Goodstein_Lambda/Goodstein_Lambda"
begin

end