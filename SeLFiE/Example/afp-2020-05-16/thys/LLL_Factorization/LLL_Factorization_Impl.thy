(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>The LLL factorization algorithm\<close>

text \<open>This theory contains an implementation of a polynomial time factorization algorithm. 
  It first constructs a modular factorization. Afterwards it recursively 
  invokes the LLL basis reduction algorithm on one lattice to either split a polynomial into  
  two non-trivial factors, or to deduce irreducibility.\<close>

theory LLL_Factorization_Impl
  imports LLL_Basis_Reduction.LLL_Certification
    Factor_Bound_2
    Missing_Dvd_Int_Poly
    Berlekamp_Zassenhaus.Berlekamp_Zassenhaus
begin

hide_const (open) up_ring.coeff up_ring.monom
  Unique_Factorization.factors Divisibility.factors
  Unique_Factorization.factor Divisibility.factor 
  Divisibility.prime

(*
  Implementation of a polynomial-time factoring algorithm for \<int>[X], based on the book 
  "Modern Computer Algebra", second edition, pages 477-480.
*)

(*The following function obtains the generators of the lattice L \<subseteq> Z^j
 - L = {ux^i: 0\<le>i\<le>j-d}\<union>{mx^i: 0\<le>i\<le>d}
 - d = degree u.
 - We have to complete with zeroes up to dimension j
*)
definition factorization_lattice where "factorization_lattice u k m \<equiv>
    map (\<lambda>i. vec_of_poly_n (u * monom 1 i) (degree u + k)) [k>..0] @
    map (\<lambda>i. vec_of_poly_n (monom m i) (degree u + k)) [degree u >..0]"

fun min_degree_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly"
  where "min_degree_poly a b = (if degree a \<le> degree b then a else b)"

fun choose_u :: "int poly list \<Rightarrow> int poly"
  where "choose_u [] = undefined"
  | "choose_u [gi] = gi" 
  | "choose_u (gi # gj # gs) = min_degree_poly gi (choose_u (gj # gs))"

lemma factorization_lattice_code[code]: "factorization_lattice u k m = (
  let n = degree u in
 map 
  (\<lambda>i. vec_of_poly_n (monom_mult i u) (n+k)) [k>..0] 
  @ map (\<lambda>i. vec_of_poly_n (monom m i) (n+k)) [n>..0]
)" unfolding factorization_lattice_def monom_mult_def
  by (auto simp: ac_simps Let_def)

text \<open>Optimization: directly try to minimize coefficients of polynomial $u$.\<close>
definition LLL_short_polynomial where
  "LLL_short_polynomial pl n u = poly_of_vec (short_vector_hybrid 2 (factorization_lattice 
     (poly_mod.inv_Mp pl (poly_mod.Mp pl u)) (n - degree u) pl))" 

locale LLL_implementation =
  fixes p pl :: int
begin

function LLL_many_reconstruction where 
  "LLL_many_reconstruction f us = (let 
     d = degree f;
     d2 = d div 2;
     f2_opt = find_map_filter 
        (\<lambda> u. gcd f (LLL_short_polynomial pl (Suc d2) u)) 
        (\<lambda> f2. let deg = degree f2 in deg > 0 \<and> deg < d)
        (filter (\<lambda> u. degree u \<le> d2) us)
    in case f2_opt of None \<Rightarrow> [f] 
    | Some f2 \<Rightarrow> let f1 = f div f2;
       (us1, us2) = List.partition (\<lambda> gi. poly_mod.dvdm p gi f1) us
       in LLL_many_reconstruction f1 us1 @ LLL_many_reconstruction f2 us2)"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda> (f,us). degree f)", goal_cases)
  case (3 f us d d2 f2_opt f2 f1 pair us1 us2)
  from find_map_filter_Some[OF 3(4)[unfolded 3(3) Let_def]] 3(1,5)
  show ?case by auto
next
  case (2 f us d d2 f2_opt f2 f1 pair us1 us2)
  from find_map_filter_Some[OF 2(4)[unfolded 2(3) Let_def]] 2(1,5)
  have f: "f = f1 * f2" and f0: "f \<noteq> 0" 
    and deg: "degree f2 > 0" "degree f2 < degree f" by auto
  have "degree f = degree f1 + degree f2" using f0 unfolding f
    by (subst degree_mult_eq, auto)
  with deg show ?case by auto
qed auto

function LLL_reconstruction where 
  "LLL_reconstruction f us = (let 
     d = degree f;
     u = choose_u us;
     g = LLL_short_polynomial pl d u;
     f2 = gcd f g;
     deg = degree f2
    in if deg = 0 \<or> deg \<ge> d then [f] 
      else let f1 = f div f2;
       (us1, us2) = List.partition (\<lambda> gi. poly_mod.dvdm p gi f1) us
       in LLL_reconstruction f1 us1 @ LLL_reconstruction f2 us2)"
  by pat_completeness auto

termination
proof (relation "measure (\<lambda> (f,us). degree f)", goal_cases)
  case (2 f us d u g f2 deg f1 pair us1 us2)
  hence f: "f = f1 * f2" and f0: "f \<noteq> 0" by auto
  have deg: "degree f = degree f1 + degree f2" using f0 unfolding f
    by (subst degree_mult_eq, auto)
  from 2 have "degree f2 > 0" "degree f2 < degree f" by auto
  thus ?case using deg by auto
qed auto
end

declare LLL_implementation.LLL_reconstruction.simps[code]
declare LLL_implementation.LLL_many_reconstruction.simps[code]

definition LLL_factorization :: "int poly \<Rightarrow> int poly list" where
  "LLL_factorization f = (let 
     \<comment> \<open>find suitable prime\<close>
     p = suitable_prime_bz f;
     \<comment> \<open>compute finite field factorization\<close>
     (_, fs) = finite_field_factorization_int p f;
     \<comment> \<open>determine exponent l and B\<close>
     n = degree f;
     no = \<parallel>f\<parallel>\<^sup>2;
     B = sqrt_int_ceiling (2^(5 * (n - 1) * (n - 1)) * no^(2 * (n - 1)));
     l = find_exponent p B;
     \<comment> \<open>perform hensel lifting to lift factorization to mod $p^l$\<close>
     us = hensel_lifting p l f fs;
     \<comment> \<open>reconstruct integer factors via LLL algorithm\<close>
     pl = p^l
   in LLL_implementation.LLL_reconstruction p pl f us)"

definition LLL_many_factorization :: "int poly \<Rightarrow> int poly list" where
  "LLL_many_factorization f = (let 
     \<comment> \<open>find suitable prime\<close>
     p = suitable_prime_bz f;
     \<comment> \<open>compute finite field factorization\<close>
     (_, fs) = finite_field_factorization_int p f;
     \<comment> \<open>determine exponent l and B\<close>
     n = degree f;
     no = \<parallel>f\<parallel>\<^sup>2;
     B = sqrt_int_ceiling (2^(5 * (n div 2) * (n div 2)) * no^(2 * (n div 2)));
     l = find_exponent p B;
     \<comment> \<open>perform hensel lifting to lift factorization to mod $p^l$\<close>
     us = hensel_lifting p l f fs;
     \<comment> \<open>reconstruct integer factors via LLL algorithm\<close>
     pl = p^l
   in LLL_implementation.LLL_many_reconstruction p pl f us)"

end
