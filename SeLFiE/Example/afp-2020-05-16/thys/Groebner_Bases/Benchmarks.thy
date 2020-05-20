(* Author: Alexander Maletzky *)

section \<open>Benchmark Problems for Computing Gr\"obner Bases\<close>

theory Benchmarks
  imports Polynomials.MPoly_Type_Class_OAlist
begin

text \<open>This theory defines various well-known benchmark problems for computing Gr\"obner bases. The
  actual tests of the different algorithms on these problems are contained in the theories whose
  names end with \<open>_Examples\<close>.\<close>

subsection \<open>Cyclic\<close>

definition cycl_pp :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat, nat) pp"
  where "cycl_pp n d i = sparse\<^sub>0 (map (\<lambda>k. (modulo (k + i) n, 1)) [0..<d])"

definition cyclic :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::{zero,one,uminus}) list"
  where "cyclic to n =
            (let xs = [0..<n] in
              (map (\<lambda>d. distr\<^sub>0 to (map (\<lambda>i. (cycl_pp n d i, 1)) xs)) [1..<n]) @
              [distr\<^sub>0 to [(cycl_pp n n 0, 1), (0, -1)]]
            )"

text \<open>@{term "cyclic n"} is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates, with maximum degree \<open>n\<close>.\<close>

(*
Input: n
Define: m \<equiv> n - 1
Variables: x(0), ..., x(m)
Polynomials: p(0), ..., p(m)

p(0)  = x(0) + ... + x(m)
p(1)  = x(0)*x(1) + x(1)*x(2) + ... + x(m-1)*x(m) + x(m)*x(0)
p(1)  = x(0)*x(1)*x(2) + x(1)*x(2)*x(3) + ... + x(m-1)*x(m)*x(0) + x(m)*x(0)*x(1)
...
p(m)  = x(0)*x(1)*...*x(m) - 1
*)

subsection \<open>Katsura\<close>

definition katsura_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
  where "katsura_poly to n i =
            change_ord to ((\<Sum>j::int=-int n..<n + 1. if abs (i - j) \<le> n then V\<^sub>0 (nat (abs j)) * V\<^sub>0 (nat (abs (i - j))) else 0) - V\<^sub>0 i)"

definition katsura :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1) list"
  where "katsura to n =
          (let xs = [0..<n] in
            (distr\<^sub>0 to ((sparse\<^sub>0 [(0, 1)], 1) # (map (\<lambda>i. (sparse\<^sub>0 [(Suc i, 1)], 2)) xs) @ [(0, -1)])) #
            (map (katsura_poly to n) xs)
          )"

text \<open>For @{prop "1 \<le> n"}, @{term "katsura n"} is a system of \<open>n + 1\<close> polynomials in \<open>n + 1\<close>
  indeterminates, with maximum degree \<open>2\<close>.\<close>

(*
Input: n
Variables: x(0), ..., x(n)
Polynomials: p(0), ..., p(n)

p(0)    = x(0) + 2 * (x(1) + ... + x(n)) - 1
p(i+1)  = (\<Sum>j=-n..n. if |i - j| \<le> n then x(|j|) * x(|i - j|) else 0) - x(i)    for 0 \<le> i < n
*)

subsection \<open>Eco\<close>

definition eco_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
  where "eco_poly to m i =
            distr\<^sub>0 to ((sparse\<^sub>0 [(i, 1), (m, 1)], 1) # map (\<lambda>j. (sparse\<^sub>0 [(j, 1), (j + i + 1, 1), (m, 1)], 1)) [0..<m - i - 1])"

definition eco :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1) list"
  where "eco to n =
          (let m = n - 1 in
            (distr\<^sub>0 to ((map (\<lambda>j. (sparse\<^sub>0 [(j, 1)], 1)) [0..<m]) @ [(0, 1)])) #
            (distr\<^sub>0 to [(sparse\<^sub>0 [(m-1, 1), (m,1)], 1), (0, - of_nat m)]) #
            (rev (map (eco_poly to m) [0..<m-1]))
          )"

text \<open>For @{prop "2 \<le> n"}, @{term "eco n"} is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates,
  with maximum degree \<open>3\<close>.\<close>

(*
Input: n
Define: m \<equiv> n - 1
Variables: x(0), ..., x(m)
Polynomials: p(m), ..., p(0)

p(i)    = x(i)*x(m) + x(0)*x(i+1)*x(m) + ... + x(m-i-2)*x(m-1)*x(m)    for 0 \<le> i < m-1
p(m-1)  = x(m-1)*x(m) - m
p(m)    = x(0) + ... + x(m-1) + 1
*)

subsection \<open>Noon\<close>

definition noon_poly :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1)"
  where "noon_poly to n i =
            (let ten = of_nat 10; eleven = - of_nat 11 in
              distr\<^sub>0 to ((map (\<lambda>j. if j = i then (sparse\<^sub>0 [(i, 1)], eleven) else (sparse\<^sub>0 [(j, 2), (i, 1)], ten)) [0..<n]) @
              [(0, ten)]))"

definition noon :: "(nat, nat) pp nat_term_order \<Rightarrow> nat \<Rightarrow> ((nat, nat) pp \<Rightarrow>\<^sub>0 'a::comm_ring_1) list"
  where "noon to n = (noon_poly to n 1) # (noon_poly to n 0) # (map (noon_poly to n) [2..<n])"

text \<open>For @{prop "2 \<le> n"}, @{term "noon n"} is a system of \<open>n\<close> polynomials in \<open>n\<close> indeterminates,
  with maximum degree \<open>3\<close>.\<close>

(*
Input: n
Define: m \<equiv> n - 1
Variables: x(0), ..., x(m)
Polynomials: p(1), p(0), p(2), ..., p(m)

p(i)  = 10 * (x(0)\<^sup>2*x(i) + x(1)\<^sup>2*x(i) + ... + x(i-1)\<^sup>2*x(i) + x(i+1)\<^sup>2*x(i) + ... + x(m)\<^sup>2*x(i)) - 11*x(i) + 10
    for 0 \<le> i \<le> m
*)

(* https://raw.githubusercontent.com/ederc/singular-benchmarks/master/benchs.lib *)

end (* theory *)
