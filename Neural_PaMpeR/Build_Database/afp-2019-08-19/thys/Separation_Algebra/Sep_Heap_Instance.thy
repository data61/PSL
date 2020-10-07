(* Author: Gerwin Klein, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

section "Standard Heaps as an Instance of Separation Algebra"

theory Sep_Heap_Instance
imports Separation_Algebra
begin

text \<open>
  Example instantiation of a the separation algebra to a map, i.e.\ a
  function from any type to @{typ "'a option"}.
\<close>

class opt =
  fixes none :: 'a
begin
  definition "domain f \<equiv> {x. f x \<noteq> none}"
end

instantiation option :: (type) opt
begin
  definition none_def [simp]: "none \<equiv> None"
  instance ..
end

instantiation "fun" :: (type, opt) zero
begin
  definition zero_fun_def: "0 \<equiv> \<lambda>s. none"
  instance ..
end

instantiation "fun" :: (type, opt) sep_algebra
begin

definition
  plus_fun_def: "m1 + m2 \<equiv> \<lambda>x. if m2 x = none then m1 x else m2 x"

definition
  sep_disj_fun_def: "sep_disj m1 m2 \<equiv> domain m1 \<inter> domain m2 = {}"

instance
  apply standard
        apply (simp add: sep_disj_fun_def domain_def zero_fun_def)
       apply (fastforce simp: sep_disj_fun_def)
      apply (simp add: plus_fun_def zero_fun_def)
     apply (simp add: plus_fun_def sep_disj_fun_def domain_def)
     apply (rule ext)
     apply fastforce
    apply (rule ext)
    apply (simp add: plus_fun_def)
   apply (simp add: sep_disj_fun_def domain_def plus_fun_def)
   apply fastforce
  apply (simp add: sep_disj_fun_def domain_def plus_fun_def)
  apply fastforce
  done

end

text \<open>
  For the actual option type @{const domain} and \<open>+\<close> are
  just @{const dom} and \<open>++\<close>:
\<close>

lemma domain_conv: "domain = dom"
  by (rule ext) (simp add: domain_def dom_def)

lemma plus_fun_conv: "a + b = a ++ b"
  by (auto simp: plus_fun_def map_add_def split: option.splits)

lemmas map_convs = domain_conv plus_fun_conv

text \<open>
  Any map can now act as a separation heap without further work:
\<close>
lemma
  fixes h :: "(nat => nat) => 'foo option"
  shows "(P ** Q ** H) h = (Q ** H ** P) h"
  by (simp add: sep_conj_ac)

end

