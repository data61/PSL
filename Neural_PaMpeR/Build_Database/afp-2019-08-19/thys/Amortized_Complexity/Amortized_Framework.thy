section "Amortized Complexity Framework"

theory Amortized_Framework
imports Complex_Main
begin

text\<open>This theory provides a framework for amortized analysis.\<close>

datatype 'a rose_tree = T 'a "'a rose_tree list"

declare length_Suc_conv [simp]

locale Amortized =
fixes arity :: "'op \<Rightarrow> nat"
fixes exec :: "'op \<Rightarrow> 's list \<Rightarrow> 's"
fixes inv :: "'s \<Rightarrow> bool"
fixes cost :: "'op \<Rightarrow> 's list \<Rightarrow> nat"
fixes \<Phi> :: "'s \<Rightarrow> real"
fixes U :: "'op \<Rightarrow> 's list \<Rightarrow> real"
assumes inv_exec: "\<lbrakk>\<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk> \<Longrightarrow> inv(exec f ss)"
assumes ppos: "inv s \<Longrightarrow> \<Phi> s \<ge> 0"
assumes U: "\<lbrakk> \<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk>
 \<Longrightarrow> cost f ss + \<Phi>(exec f ss) - sum_list (map \<Phi> ss) \<le> U f ss"
begin

fun wf :: "'op rose_tree \<Rightarrow> bool" where
"wf (T f ts) = (length ts = arity f \<and> (\<forall>t \<in> set ts. wf t))"

fun state :: "'op rose_tree \<Rightarrow> 's" where
"state (T f ts) = exec f (map state ts)"

lemma inv_state: "wf ot \<Longrightarrow> inv(state ot)"
by(induction ot)(simp_all add: inv_exec)

definition acost :: "'op \<Rightarrow> 's list \<Rightarrow> real" where
"acost f ss = cost f ss + \<Phi> (exec f ss) - sum_list (map \<Phi> ss)"

fun acost_sum :: "'op rose_tree \<Rightarrow> real" where
"acost_sum (T f ts) = acost f (map state ts) + sum_list (map acost_sum ts)"

fun cost_sum :: "'op rose_tree \<Rightarrow> real" where
"cost_sum (T f ts) = cost f (map state ts) + sum_list (map cost_sum ts)"

fun U_sum :: "'op rose_tree \<Rightarrow> real" where
"U_sum (T f ts) = U f (map state ts) + sum_list (map U_sum ts)"

lemma t_sum_a_sum: "wf ot \<Longrightarrow> cost_sum ot = acost_sum ot - \<Phi>(state ot)"
  by (induction ot) (auto simp: acost_def Let_def sum_list_subtractf cong: map_cong)

corollary t_sum_le_a_sum: "wf ot \<Longrightarrow> cost_sum ot \<le> acost_sum ot"
by (metis add.commute t_sum_a_sum diff_add_cancel le_add_same_cancel2 ppos[OF inv_state])

lemma a_le_U: "\<lbrakk> \<forall>s \<in> set ss. inv s; length ss = arity f \<rbrakk> \<Longrightarrow> acost f ss \<le> U f ss"
by(simp add: acost_def U)

lemma u_sum_le_U_sum: "wf ot \<Longrightarrow> acost_sum ot \<le> U_sum ot"
proof(induction ot)
  case (T f ts)
  with a_le_U[of "map state ts" f] sum_list_mono show ?case
    by (force simp: inv_state)
qed

corollary t_sum_le_U_sum: "wf ot \<Longrightarrow> cost_sum ot \<le> U_sum ot"
by (blast intro: t_sum_le_a_sum u_sum_le_U_sum order.trans)

end

hide_const T

text
\<open>\<open>Amortized2\<close> supports the transfer of amortized analysis of one datatype
(\<open>Amortized arity exec inv cost \<Phi> U\<close> on type \<open>'s\<close>) to an implementation
(primed identifiers on type \<open>'t\<close>).
Function \<open>hom\<close> is assumed to be a homomorphism from \<open>'t\<close> to \<open>'s\<close>,
not just w.r.t. \<open>exec\<close> but also \<open>cost\<close> and \<open>U\<close>. The assumptions about
\<open>inv'\<close> are weaker than the obvious \<open>inv' = inv \<circ> hom\<close>: the latter does
not allow \<open>inv\<close> to be weaker than \<open>inv'\<close> (which we need in one application).\<close>

locale Amortized2 = Amortized arity exec inv cost \<Phi> U
  for arity :: "'op \<Rightarrow> nat" and exec and inv :: "'s \<Rightarrow> bool" and cost \<Phi> U +
fixes exec' :: "'op \<Rightarrow> 't list \<Rightarrow> 't"
fixes inv' :: "'t \<Rightarrow> bool"
fixes cost' :: "'op \<Rightarrow> 't list \<Rightarrow> nat"
fixes U' :: "'op \<Rightarrow> 't list \<Rightarrow> real"
fixes hom :: "'t \<Rightarrow> 's"
assumes exec': "\<lbrakk>\<forall>s \<in> set ts. inv' s; length ts = arity f \<rbrakk>
  \<Longrightarrow> hom(exec' f ts) = exec f (map hom ts)"
assumes inv_exec': "\<lbrakk>\<forall>s \<in> set ss. inv' s; length ss = arity f \<rbrakk>
  \<Longrightarrow> inv'(exec' f ss)"
assumes inv_hom: "inv' t \<Longrightarrow> inv (hom t)"
assumes cost': "\<lbrakk>\<forall>s \<in> set ts. inv' s; length ts = arity f \<rbrakk>
  \<Longrightarrow> cost' f ts = cost f (map hom ts)"
assumes U': "\<lbrakk>\<forall>s \<in> set ts. inv' s; length ts = arity f \<rbrakk>
  \<Longrightarrow> U' f ts = U f (map hom ts)"
begin

sublocale A': Amortized arity exec' inv' cost' "\<Phi> o hom" U'
proof (standard, goal_cases)
  case 1 thus ?case by(simp add: exec' inv_exec' inv_exec)
next
  case 2 thus ?case by(simp add: inv_hom ppos)
next
  case 3 thus ?case
    by(simp add: U exec' U' map_map[symmetric] cost' inv_exec inv_hom del: map_map)
qed

end

end