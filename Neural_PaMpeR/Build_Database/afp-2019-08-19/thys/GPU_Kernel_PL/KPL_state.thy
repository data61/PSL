section \<open>Thread, group and kernel states\<close>

theory KPL_state imports 
  KPL_syntax
begin

text \<open>Thread state\<close>
record thread_state =
  (* We use "V + bool" to indicate that the domain of
     l is extended with two extra values. Let's say
     that "l (Inr True)" returns the gid, and that
     "l (Inr False)" returns the lid. *)
  l :: "V + bool \<Rightarrow> word" 
  sh :: "nat \<Rightarrow> word"
  R :: "nat set"
  W :: "nat set"

abbreviation "GID \<equiv> Inr True"
abbreviation "LID \<equiv> Inr False"

text \<open>Group state\<close>
record group_state = 
  thread_states :: "lid \<rightharpoonup> thread_state" ("_ \<^sub>t\<^sub>s" [1000] 1000)
  R_group :: "(lid \<times> nat) set"
  W_group :: "(lid \<times> nat) set"

text \<open>Valid group state\<close>
fun valid_group_state :: "(gid \<rightharpoonup> lid set) \<Rightarrow> gid \<Rightarrow> group_state \<Rightarrow> bool"
where
  "valid_group_state T i \<gamma> = (
  dom (\<gamma> \<^sub>t\<^sub>s) = the (T i) \<and>
  (\<forall>j \<in> the (T i).
  l (the (\<gamma> \<^sub>t\<^sub>s j)) GID = i \<and>
  l (the (\<gamma> \<^sub>t\<^sub>s j)) LID = j))"

text \<open>Predicated statements\<close>
type_synonym pred_stmt = "stmt \<times> local_expr"
type_synonym pred_basic_stmt = "basic_stmt \<times> local_expr"

text \<open>Kernel state\<close>
type_synonym kernel_state = 
  "(gid \<rightharpoonup> group_state) \<times> pred_stmt list \<times> V list"

text \<open>Valid kernel state\<close>
fun valid_kernel_state :: "threadset \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_kernel_state (G,T) (\<kappa>, ss, _) = (
  dom \<kappa> = G \<and>
  (\<forall>i \<in> G. valid_group_state T i (the (\<kappa> i))))"

text \<open>Valid initial kernel state\<close>
fun valid_initial_kernel_state :: "stmt \<Rightarrow> threadset \<Rightarrow> kernel_state \<Rightarrow> bool"
where
  "valid_initial_kernel_state S (G,T) (\<kappa>, ss, vs) = ( 
  valid_kernel_state (G,T) (\<kappa>, ss, vs) \<and>
  (ss = [(S, eTrue)]) \<and>
  (\<forall>i \<in> G. R_group (the (\<kappa> i)) = {} \<and> W_group (the (\<kappa> i)) = {}) \<and>
  (\<forall>i \<in> G. \<forall>j \<in> the (T i). R (the ((the (\<kappa> i))\<^sub>t\<^sub>s j)) = {}
    \<and> W (the ((the (\<kappa> i))\<^sub>t\<^sub>s j)) = {}) \<and>
  (\<forall>i \<in> G. \<forall>j \<in> the (T i). \<forall>v :: V. 
    l (the ((the (\<kappa> i))\<^sub>t\<^sub>s j)) (Inl v) = 0) \<and>
  (\<forall>i \<in> G. \<forall>i' \<in> G. \<forall>j \<in> the (T i). \<forall>j' \<in> the (T i').
    sh (the ((the (\<kappa> i))\<^sub>t\<^sub>s j)) = 
    sh (the ((the (\<kappa> i'))\<^sub>t\<^sub>s j'))) \<and>
  (vs = []))"

end
