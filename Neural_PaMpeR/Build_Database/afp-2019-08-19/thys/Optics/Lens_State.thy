section \<open>State and Lens integration\<close>

theory Lens_State
imports
  "HOL-Library.State_Monad"
  Lens_Algebra
begin
text \<open>Inspired by Haskell's lens package\<close>

definition zoom :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('a, 'c) state \<Rightarrow> ('b, 'c) state" where
"zoom l m = State (\<lambda>b. case run_state m (lens_get l b) of (c, a) \<Rightarrow> (c, lens_put l b a))"

definition use :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b, 'a) state" where
"use l = zoom l State_Monad.get"

definition modify :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('b, unit) state" where
"modify l f = zoom l (State_Monad.update f)"

definition assign :: "('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Rightarrow> ('b, unit) state" where
"assign l b = zoom l (State_Monad.set b)"

context begin

qualified abbreviation "add l n \<equiv> modify l (\<lambda>x. x + n)"
qualified abbreviation "sub l n \<equiv> modify l (\<lambda>x. x - n)"
qualified abbreviation "mul l n \<equiv> modify l (\<lambda>x. x * n)"
qualified abbreviation "inc l \<equiv> add l 1"
qualified abbreviation "dec l \<equiv> sub l 1"

end

bundle lens_state_notation begin
  notation zoom (infixr "\<rhd>" 80)
  notation modify (infix "%=" 80)
  notation assign (infix ".=" 80)
  notation Lens_State.add (infix "+=" 80)
  notation Lens_State.sub (infix "-=" 80)
  notation Lens_State.mul (infix "*=" 80)
  notation Lens_State.inc ("_ ++")
  notation Lens_State.dec ("_ --")
end

context includes lens_state_notation begin

lemma zoom_comp1: "l1 \<rhd> l2 \<rhd> s = (l2 ;\<^sub>L l1) \<rhd> s"
unfolding zoom_def lens_comp_def
by (auto split: prod.splits)

lemma zoom_zero[simp]: "zero_lens \<rhd> s = s"
unfolding zoom_def zero_lens_def
by simp

lemma zoom_id[simp]: "id_lens \<rhd> s = s"
unfolding zoom_def id_lens_def
by simp

end

lemma (in mwb_lens) zoom_comp2[simp]: "zoom x m \<bind> (\<lambda>a. zoom x (n a)) = zoom x (m \<bind> n)"
unfolding zoom_def State_Monad.bind_def
by (auto split: prod.splits simp: put_get put_put)

lemma (in wb_lens) use_alt_def: "use x = map_state (lens_get x) State_Monad.get"
unfolding State_Monad.get_def use_def zoom_def
by (simp add: comp_def get_put)

lemma (in wb_lens) modify_alt_def: "modify x f = State_Monad.update (update f)"
unfolding modify_def zoom_def update_def State_Monad.update_def State_Monad.get_def State_Monad.set_def State_Monad.bind_def
by auto

lemma (in wb_lens) modify_id[simp]: "modify x (\<lambda>x. x) = State_Monad.return ()"
unfolding update_def modify_alt_def
by (simp add: get_put)

lemma (in mwb_lens) modify_comp[simp]: "bind (modify x f) (\<lambda>_. modify x g) = modify x (g \<circ> f)"
unfolding modify_def
by simp

end
