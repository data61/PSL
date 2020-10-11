section \<open>Data: Functions\<close>

theory Data_Function
  imports HOLCF_Main
begin

fixrec flip :: "('a -> 'b -> 'c) -> 'b -> 'a -> 'c" where
  "flip\<cdot>f\<cdot>x\<cdot>y = f\<cdot>y\<cdot>x"

fixrec const :: "'a \<rightarrow> 'b \<rightarrow> 'a" where
  "const\<cdot>x\<cdot>_ = x"

fixrec dollar :: "('a -> 'b) -> 'a -> 'b" where
  "dollar\<cdot>f\<cdot>x = f\<cdot>x"

fixrec dollarBang :: "('a -> 'b) -> 'a -> 'b" where
  "dollarBang\<cdot>f\<cdot>x = seq\<cdot>x\<cdot>(f\<cdot>x)"

fixrec on :: "('b -> 'b -> 'c) -> ('a -> 'b) -> 'a -> 'a -> 'c" where
  "on\<cdot>g\<cdot>f\<cdot>x\<cdot>y = g\<cdot>(f\<cdot>x)\<cdot>(f\<cdot>y)"

end
