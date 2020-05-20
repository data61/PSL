section\<open>Operations\<close>

theory Operations
imports Main
begin

class left_imp = 
  fixes imp_l :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "l\<rightarrow>" 65)

class right_imp = 
  fixes imp_r :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "r\<rightarrow>" 65)

class left_uminus =
  fixes uminus_l :: "'a => 'a"  ("-l _" [81] 80)

class right_uminus =
  fixes uminus_r :: "'a => 'a"  ("-r _" [81] 80)

end
