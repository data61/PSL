section \<open>Circus variables\<close>

theory Var_list
imports Main
begin

text \<open>Circus variables are represented by a stack (list) of values. 
they are characterized by two functions, $select$ and $update$.
The Circus variable type is defined as a tuple ($select$ * $update$) with a 
list of values instead of a single value.\<close>

type_synonym ('a, '\<sigma>) var_list = "('\<sigma> \<Rightarrow> 'a list) * (('a list \<Rightarrow> 'a list) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>)"

text \<open>The $select$ function returns the top value of the stack.\<close>

definition select :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'a"
where "select f \<equiv> \<lambda> A. hd ((fst f) A)"

text \<open>The $increase$ function pushes a new value to the top of the stack.\<close>

definition increase :: "('a, 'r) var_list \<Rightarrow> 'a \<Rightarrow> 'r \<Rightarrow> 'r"
where "increase f val \<equiv> (snd f) (\<lambda> l. val#l)"

text \<open>The $increase0$ function pushes an arbitrary value to the top of the stack.\<close>

definition increase0 :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'r"
where "increase0 f \<equiv> (snd f) (\<lambda> l. ((SOME val. True)#l))"

text \<open>The $decrease$ function pops the top value of the stack.\<close>

definition decrease :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'r"
where "decrease f \<equiv> (snd f) (\<lambda> l. (tl l))"

text \<open>The $update$ function updates the top value of the stack.\<close>

definition update :: "('a, 'r) var_list \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> 'r \<Rightarrow> 'r"
where "update f upd \<equiv> (snd f) (\<lambda> l. (upd (hd l))#(tl l))"

text \<open>The $update0$ function initializes the top of the stack with an arbitrary value.\<close>

definition update0 :: "('a, 'r) var_list \<Rightarrow> 'r \<Rightarrow> 'r"
where "update0 f \<equiv> (snd f) (\<lambda> l. ((SOME upd. True) (hd l))#(tl l))"

axiomatization  where select_increase: "(select v (increase v a s)) = a"


text \<open>The $VAR-LIST$ function allows to retrieve a Circus variable from its name.\<close>

syntax "_VAR_LIST" :: "id \<Rightarrow> ('a, 'r) var_list"  ("VAR'_LIST _")
translations "VAR_LIST x" => "(x, _update_name x)"

end
