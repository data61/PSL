(*
Title: Strong-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Domain_example
imports Expr
begin

\<comment> \<open>When interpreting, we have to instantiate the type for domains. As an example, we take a type containing 'low' and 'high' as domains.\<close>

datatype Dom = low | high

instantiation Dom :: order
begin

definition
less_eq_Dom_def: "d1 \<le> d2 = (if d1 = d2 then True 
  else (if d1 = low then True else False))"

definition
less_Dom_def: "d1 < d2 = (if d1 = d2 then False
  else (if d1 = low then True else False))"

instance proof
fix x y z :: Dom
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" 
    unfolding less_eq_Dom_def less_Dom_def by auto
  show "x \<le> x" unfolding less_eq_Dom_def by auto
  show "\<lbrakk>x \<le> y; y \<le> z\<rbrakk> \<Longrightarrow> x \<le> z" 
    unfolding less_eq_Dom_def by ((split if_split_asm)+, auto)
  show "\<lbrakk>x \<le> y; y \<le> x\<rbrakk> \<Longrightarrow> x = y" 
    unfolding less_eq_Dom_def by ((split if_split_asm)+, 
      auto, (split if_split_asm)+, auto)
qed

end

end

