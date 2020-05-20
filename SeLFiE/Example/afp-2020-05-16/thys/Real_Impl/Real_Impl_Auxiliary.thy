(*  Title:       Implementing field extensions of the form Q[sqrt(b)]
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2009-2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
section \<open>Auxiliary lemmas which might be moved into the Isabelle distribution.\<close>

theory Real_Impl_Auxiliary
imports 
  "HOL-Computational_Algebra.Primes"
begin

lemma multiplicity_prime: 
  assumes p: "prime (i :: nat)" and ji: "j \<noteq> i"
  shows "multiplicity j i = 0"
  using assms
  by (metis dvd_refl prime_nat_iff multiplicity_eq_zero_iff 
        multiplicity_unit_left multiplicity_zero)

end
