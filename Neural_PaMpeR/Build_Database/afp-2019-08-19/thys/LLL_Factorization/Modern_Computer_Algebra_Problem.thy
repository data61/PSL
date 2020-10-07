(*
    Authors:    Jose Divasón
                Sebastiaan Joosten
                René Thiemann
                Akihisa Yamada
    License:    BSD
*)

section \<open>Mistakes in the textbook Modern Computer Algebra (2nd edition)\<close>

theory Modern_Computer_Algebra_Problem
  imports Factorization_Algorithm_16_22
begin

fun max_degree_poly :: "int poly \<Rightarrow> int poly \<Rightarrow> int poly"
  where "max_degree_poly a b = (if degree a \<ge> degree b then a else b)"
 
fun choose_u :: "int poly list \<Rightarrow> int poly"
   where "choose_u [] = undefined"
 | "choose_u [gi] = gi" 
 | "choose_u (gi # gj # gs) = max_degree_poly gi (choose_u (gj # gs))"

subsection \<open>A real problem of Algorithm 16.22\<close>

text \<open>Bogus example for Modern Computer Algebra (2nd edition), Algorithm 16.22, step 9:
  After having detected the factor @{term "[:1,1,0,1 :: int:]"}, the remaining polynomial
  $f^*$ will be 1, and the remaining list of modular factors will be empty.\<close>

lemma "let f = [:1,1:] * [:1,1,0,1:];
   p = suitable_prime_bz f;
   b = lead_coeff f;
   A = linf_norm_poly f; n = degree f; B = sqrt_int_ceiling (n+1) * 2^n * A;
   Bnd = 2^(n^2 div 2) * B^(2*n); l = log_ceiling p Bnd;
   (_, fs) = finite_field_factorization_int p f;
   gs = hensel_lifting p l f fs;
   u = choose_u gs;
   d = degree u;
   g_star = [:2,2,0,2 :: int :];
   (gs',hs') = List.partition (\<lambda>gi. poly_mod.dvdm p gi g_star) gs;
   h_star = smult b (prod_list hs');
   f_star = primitive_part h_star
  in (hs' = [] \<and> f_star = 1)" by eval

subsection \<open>Another potential problem of Algorithm 16.22\<close>

text \<open>
  Suppose that $g^*$ is $p^l$. (It is is not yet clear whether lattices exists 
  where this $g^*$ is short enough).
  Then $pp(g^*) = 1$ is detected as \emph{irreducible} factor and the algorithm stops.
\<close>


definition "input_poly = [: 1,0,0,0,1,1,0,0,1,0,1,0,1 :: int :]" 

text \<open>For @{const input_poly} the factorization will result in a lattice where
  each initial basis element has a Euclidean norm of at least $p^l$ (since the
  input polynomial $u$ has a norm larger than $p^l$.)
  So, just from the norm of the basis one cannot infer that the lattice contains small vectors.\<close>

lemma "let f = input_poly;
   p = suitable_prime_bz f;
   b = lead_coeff f;
   A = linf_norm_poly f; n = degree f; B = sqrt_int_ceiling (n+1) * 2^n * A;
   Bnd = 2^(n^2 div 2) * B^(2*n); l = log_ceiling p Bnd;
   (_, fs) = finite_field_factorization_int p f;
   gs = hensel_lifting p l f fs;
   u = choose_u gs;
   pl = p^l;
   pl2 = pl div 2;  
   u' = poly_mod.inv_Mp2 pl pl2 (poly_mod.Mp pl (smult b u))
  in sqrt_int_floor (sq_norm u') > pl" by eval

text \<open>The following calculation will show that the norm of $g^*$ is not that much
  shorter than $p^l$ which is an indication that it is not obvious that in general
  $p^l$ cannot be chosen as short polynomial.\<close>

definition "compute_norms = (let f = input_poly;
   p = suitable_prime_bz f;
   b = lead_coeff f;
   A = linf_norm_poly f; n = degree f; B = sqrt_int_ceiling (n+1) * 2^n * A;
   Bnd = 2^(n^2 div 2) * B^(2*n); l = log_ceiling p Bnd;
   (_, fs) = finite_field_factorization_int p f;
   gs = hensel_lifting p l f fs;
   u = choose_u gs;
   pl = p^l;
   pl2 = pl div 2;  
   u' = poly_mod.inv_Mp2 pl pl2 (poly_mod.Mp pl (smult b u));
   d = degree u;
   pl = p^l;
   L = factorization_lattice u' 1 pl;
   g_star = short_vector 2 L 
  in (
     ''p^l:         '' @ show pl @ shows_nl [] @ 
     ''norm u:      '' @ show (sqrt_int_floor (sq_norm_poly u')) @ shows_nl [] @
     ''norm g_star: '' @ show (sqrt_int_floor (sq_norm_vec g_star)) @ shows_nl [] @ shows_nl [] 
))"

export_code compute_norms in Haskell 

text \<open>
\<^item> @{term "p^l"}:         $\approx 6.61056 \cdot 10^{122}$, namely 661055968790248598951915308032771039828404682964281219284648795274405791236311345825189210439715284847591212025023358304256
\<^item> @{term "norm u"}:      $\approx 6.67555 \cdot 10^{122}$, namely 667555058938127908386141559707490406617756492853269306735125739182352318769782701477339940304992057299993307341153235059302
\<^item> @{term "norm g_star"}: $\approx 5.02568 \cdot 10^{110}$, namely 502567871888893789258107599397950338997348731386301514804539180088146716526330518979464688385872213886910747667
\<close>

subsection \<open>Verified wrong results\<close>

text \<open>An equality in example 16.24 of the textbook which is not valid.\<close> 

lemma "let g2 = [:-984,1:];
           g3 = [:-72,1:];
           g4 = [:-6828,1:];
           rhs = [:-1728,-840,-420,6:]
  in \<not> poly_mod.eq_m (5^6) (smult 6 (g2*g3*g4)) (rhs)" by eval

end
