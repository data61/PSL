(*  Title:       The Partial Cost Model of the List Update Problem
    Author:      Max Haslbeck
*)

section "Partial cost model"

theory Partial_Cost_Model
imports Move_to_Front
begin

definition t\<^sub>p :: "'a state \<Rightarrow> 'a \<Rightarrow> answer \<Rightarrow> nat" where
"t\<^sub>p s q a = (let (mf,sws) = a in index (swaps sws s) q + size sws)"

notation (latex) t\<^sub>p ("\<^latex>\<open>$t^{*}$\<close>")

lemma t\<^sub>pt: "t\<^sub>p s q a + 1 = t s q a" unfolding t\<^sub>p_def t_def by(simp add: split_def)

interpretation On_Off step t\<^sub>p static .
                 
abbreviation "T\<^sub>p == T"
abbreviation "T\<^sub>p_opt == T_opt" 
abbreviation "T\<^sub>p_on == T_on"
abbreviation "T\<^sub>p_on_rand' == T_on_rand'"
abbreviation "T\<^sub>p_on_n == T_on_n"
abbreviation "T\<^sub>p_on_rand == T_on_rand"
abbreviation "T\<^sub>p_on_rand_n == T_on_rand_n"
abbreviation "config\<^sub>p == config "
abbreviation "compet\<^sub>p == compet"
                                            


end
