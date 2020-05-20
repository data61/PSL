(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Divmod-Int\<close>

text \<open>We provide the divmod-operation on type int for efficiency reasons.\<close>

theory Divmod_Int
imports Main
begin

definition divmod_int :: "int \<Rightarrow> int \<Rightarrow> int \<times> int" where
  "divmod_int n m = (n div m, n mod m)"

text \<open>We implement @{const divmod_int} via @{const divmod_integer}
  instead of invoking both division and modulo separately.\<close>

context
includes integer.lifting
begin

lemma divmod_int_code[code]: "divmod_int m n = map_prod int_of_integer int_of_integer 
  (divmod_integer (integer_of_int m) (integer_of_int n))"
  unfolding divmod_int_def divmod_integer_def map_prod_def split prod.simps
proof 
  show "m div n = int_of_integer
     (integer_of_int m div integer_of_int n)"
    by (transfer, simp)
  show "m mod n = int_of_integer
     (integer_of_int m mod integer_of_int n)"
    by (transfer, simp)
qed
end

end
