(* Author: Tobias Nipkow *)

section \<open>Archive\<close>

theory Arch
imports Main "HOL-Library.Code_Target_Numeral"
begin

setup \<open>fn thy =>
  let
    val T = @{typ "integer list list list"}
    val dir = Resources.master_directory thy
  in
    thy |>
    Code_Runtime.polyml_as_definition
      [(@{binding Tri'}, T), (@{binding Quad'}, T), (@{binding Pent'}, T),
       (@{binding Hex'}, T)]
      (map (Path.append dir o Path.explode)
        ["Archives/Tri.ML", "Archives/Quad.ML",
          "Archives/Pent.ML", "Archives/Hex.ML"])
  end
\<close>

text \<open>The definition of these constants is only ever needed at the ML level
when running the eval proof method.\<close>

definition Tri :: "nat list list list"
where
  "Tri = (map \<circ> map \<circ> map) nat_of_integer Tri'"

definition Quad :: "nat list list list"
where
  "Quad = (map \<circ> map \<circ> map) nat_of_integer Quad'"

definition Pent :: "nat list list list"
where
  "Pent = (map \<circ> map \<circ> map) nat_of_integer Pent'"

definition Hex :: "nat list list list"
where
  "Hex = (map \<circ> map \<circ> map) nat_of_integer Hex'"

end

