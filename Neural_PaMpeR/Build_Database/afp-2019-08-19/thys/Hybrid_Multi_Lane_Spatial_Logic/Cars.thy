(*  Title:      Cars.thy
    Author:     Sven Linker

A countably infinite type to denote cars in the model of HMLSL.
*)

section\<open>Cars\<close>

text \<open>
We define a type to refer to cars. For simplicity, we assume that (countably)
infinite cars exist.
\<close>

theory Cars
  imports Main
begin

text \<open>
The type of cars consists of the natural numbers. However, we do not
define or prove any additional structure about it.
\<close>

typedef cars = "{n::nat. True} " by blast 

locale cars 
begin

text \<open>
For the construction of possible counterexamples, it is beneficial to 
prove that at least two cars exist. Furthermore, we show that there indeed
exist infinitely many cars.
\<close>

lemma at_least_two_cars_exists:"\<exists>c d ::cars . c\<noteq>d" 
proof -
  have "(0::nat) \<noteq> 1" by simp
  then have "Abs_cars (0::nat) \<noteq> Abs_cars(1) " by (simp add:Abs_cars_inject) 
  thus ?thesis by blast
qed

lemma infinite_cars:"infinite {c::cars . True}" 
proof -
  have "infinite {n::nat. True}" by auto 
  then show ?thesis 
    by (metis UNIV_def finite_imageI type_definition.Rep_range type_definition_cars)
qed

end
end
