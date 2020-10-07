(*  
    Title:      Rank.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section\<open>Rank of a matrix\<close>

theory Rank
imports 
      Rank_Nullity_Theorem.Dim_Formula
begin

subsection\<open>Row rank, column rank and rank\<close>

text\<open>Definitions of row rank, column rank and rank\<close>

definition row_rank :: "'a::{field}^'n^'m=>nat"
  where "row_rank A = vec.dim (row_space A)"

definition col_rank :: "'a::{field}^'n^'m=>nat"
  where "col_rank A = vec.dim (col_space A)"

lemma rank_def: "rank A = row_rank A"
  by (auto simp: row_rank_def row_rank_def_gen row_space_def)

subsection\<open>Properties\<close>

lemma rrk_is_preserved:
fixes A::"'a::{field}^'cols^'rows::{finite, wellorder}"
  and P::"'a::{field}^'rows::{finite, wellorder}^'rows::{finite, wellorder}"
assumes inv_P: "invertible P"
shows "row_rank A = row_rank (P**A)"
by (metis row_space_is_preserved row_rank_def inv_P)

lemma crk_is_preserved:
fixes A::"'a::{field}^'cols::{finite, wellorder}^'rows"
  and P::"'a::{field}^'rows^'rows"
assumes inv_P: "invertible P"
shows "col_rank A = col_rank (P**A)"
  using rank_nullity_theorem_matrices unfolding ncols_def 
  by (metis col_rank_def inv_P nat_add_left_cancel null_space_is_preserved) 

end

