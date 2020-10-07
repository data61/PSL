(*
  File:     Miller_Rabin.thy
  Authors:  Daniel Stüwe, Manuel Eberl

  The Miller--Rabin primality test.
*)
section \<open>The Miller--Rabin Test\<close>
theory Miller_Rabin_Test
imports 
  Fermat_Witness
  Generalized_Primality_Test
begin

definition "miller_rabin = primality_test (\<lambda>n a. strong_fermat_liar a n)"

text \<open>
  The test is actually $\frac{1}{4}$ good, but we only show $\frac{1}{2}$, since the former
  is much more involved.
\<close>
interpretation miller_rabin: good_prob_primality_test "\<lambda>n a. strong_fermat_liar a n" n "1 / 2"
  rewrites "primality_test (\<lambda>n a. strong_fermat_liar a n) = miller_rabin"
proof -
  show "good_prob_primality_test (\<lambda>n a. strong_fermat_liar a n) n (1 / 2)"
    by standard (use strong_fermat_witness_lower_bound prime_imp_strong_fermat_witness in auto)
qed (simp_all add: miller_rabin_def)

end