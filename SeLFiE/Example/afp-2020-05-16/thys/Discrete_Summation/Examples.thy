
(* Author: Florian Haftmann, TU Muenchen *)

section \<open>Simple examples\<close>

theory Examples
imports Summation_Conversion
begin

ML \<open>
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>q::rat. q ^ Suc (Suc (Suc 0)) + 3) 0 j"}
\<close>

ML \<open>
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>x::real. x ^ Suc (Suc (Suc 0)) + 3) 0 j"}
\<close>

ML \<open>
  Summation.conv @{context}
  @{cterm "\<Sigma> (\<lambda>k::int. k ^ Suc (Suc (Suc 0)) + 3) 0 j"}
\<close>

ML \<open>
  Summation.conv @{context}
  @{cterm "\<Sigma>\<^sub>\<nat> (\<lambda>n::nat. n ^ Suc (Suc (Suc 0)) + 3) 0 m"}
\<close>

end
