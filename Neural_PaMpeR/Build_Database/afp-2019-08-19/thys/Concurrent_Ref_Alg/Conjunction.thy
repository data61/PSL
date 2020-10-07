section \<open>Weak Conjunction Operator \label{S:conjunction}\<close>

theory Conjunction
imports Refinement_Lattice
begin

text \<open>
  The weak conjunction operator $\doublecap$ is similar to
  least upper bound ($\sqcup$) 
  but is abort strict,
  i.e.\ the lattice bottom is an annihilator: $c \doublecap \bot = \bot$. 
  It has identity the command chaos that allows any non-aborting behaviour.
\<close>

locale chaos =
  fixes chaos :: "'a::refinement_lattice"    ("chaos") 
(*
The weak conjunction operator uses a special symbol: double intersection.
To see this symbol in your Isabelle PIDE, install DejaVu Sans fonts
(available freely online at http://dejavu-fonts.org/wiki/Download)
and add the following line to ~/.isabelle/Isabelle2015/etc/symbols
(create the file if it does not exist):

\<iinter>               code: 0x0022d2  group: operator  font: DejaVuSans

Note: if the symbol is rendering correctly, you do not need to do anything.
*)
locale conj =
  fixes conj :: "'a::refinement_lattice \<Rightarrow> 'a \<Rightarrow> 'a"   (infixl "\<iinter>" 80)
  assumes conj_bot_right: "c \<iinter> \<bottom> = \<bottom>"

text \<open>
  Conjunction forms an idempotent, commutative monoid
  (i.e. a semi-lattice), with identity chaos.
\<close>

locale conjunction = conj + chaos + conj: semilattice_neutr conj chaos

begin
lemmas [algebra_simps, field_simps] =
  conj.assoc
  conj.commute
  conj.left_commute

lemmas conj_assoc = conj.assoc             (* 42 *)
lemmas conj_commute = conj.commute         (* 43 *)
lemmas conj_idem = conj.idem               (* 44 *)
lemmas conj_chaos = conj.right_neutral     (* 45 *)            
lemmas conj_chaos_left = conj.left_neutral (* 45 + 43 *)

lemma conj_bot_left [simp]: "\<bottom> \<iinter> c = \<bottom>"
using conj_bot_right local.conj_commute by fastforce

lemma conj_not_bot: "a \<iinter> b \<noteq> \<bottom> \<Longrightarrow> a \<noteq> \<bottom> \<and> b \<noteq> \<bottom>"
  using conj_bot_right by auto

lemma conj_distrib1: "c \<iinter> (d\<^sub>0 \<iinter> d\<^sub>1) = (c \<iinter> d\<^sub>0) \<iinter> (c \<iinter> d\<^sub>1)"
  by (metis conj_assoc conj_commute conj_idem)

end



subsection \<open>Distributed weak conjunction\<close>

text \<open>
  The weak conjunction operator distributes across arbitrary non-empty infima.
\<close>

locale conj_distrib = conjunction +
  assumes Inf_conj_distrib: "D \<noteq> {} \<Longrightarrow> (\<Sqinter> D) \<iinter> c = (\<Sqinter>d\<in>D. d \<iinter> c)"   (* 48 *)
  (* and sup_conj_distrib: "(c\<^sub>0 \<squnion> c\<^sub>1) \<iinter> d = (c\<^sub>0 \<iinter> d) \<squnion> (c\<^sub>1 \<iinter> d)"  *)       (* 49+ *)
begin

lemma conj_Inf_distrib: "D \<noteq> {} \<Longrightarrow> c \<iinter> (\<Sqinter> D) = (\<Sqinter>d\<in>D. c \<iinter> d)"
  using Inf_conj_distrib conj_commute by auto

lemma inf_conj_distrib: "(c\<^sub>0 \<sqinter> c\<^sub>1) \<iinter> d = (c\<^sub>0 \<iinter> d) \<sqinter> (c\<^sub>1 \<iinter> d)"
proof -
  have "(c\<^sub>0 \<sqinter> c\<^sub>1) \<iinter> d = (\<Sqinter> {c\<^sub>0, c\<^sub>1}) \<iinter> d" by simp
  also have "... = (\<Sqinter>c \<in> {c\<^sub>0, c\<^sub>1}. c \<iinter> d)" by (rule Inf_conj_distrib, simp)
  also have "... = (c\<^sub>0 \<iinter> d) \<sqinter> (c\<^sub>1 \<iinter> d)" by simp
  finally show ?thesis .
qed

lemma inf_conj_product: "(a \<sqinter> b) \<iinter> (c \<sqinter> d) = (a \<iinter> c) \<sqinter> (a \<iinter> d) \<sqinter> (b \<iinter> c) \<sqinter> (b \<iinter> d)"
  by (metis inf_conj_distrib conj_commute inf_assoc)

lemma conj_mono: "c\<^sub>0 \<sqsubseteq> d\<^sub>0 \<Longrightarrow> c\<^sub>1 \<sqsubseteq> d\<^sub>1 \<Longrightarrow> c\<^sub>0 \<iinter> c\<^sub>1 \<sqsubseteq> d\<^sub>0 \<iinter> d\<^sub>1"
  by (metis inf.absorb_iff1 inf_conj_product inf_right_idem)

lemma conj_mono_left: "c\<^sub>0 \<sqsubseteq> c\<^sub>1 \<Longrightarrow> c\<^sub>0 \<iinter> d \<sqsubseteq> c\<^sub>1 \<iinter> d"
  by (simp add: conj_mono)

lemma conj_mono_right: "c\<^sub>0 \<sqsubseteq> c\<^sub>1 \<Longrightarrow> d \<iinter> c\<^sub>0 \<sqsubseteq> d \<iinter> c\<^sub>1"
  by (simp add: conj_mono)

lemma conj_refine: "c\<^sub>0 \<sqsubseteq> d \<Longrightarrow> c\<^sub>1 \<sqsubseteq> d \<Longrightarrow> c\<^sub>0 \<iinter> c\<^sub>1 \<sqsubseteq> d" (* law 'refine-conjunction' *)
  by (metis conj_idem conj_mono)

lemma refine_to_conj: "c \<sqsubseteq> d\<^sub>0 \<Longrightarrow> c \<sqsubseteq> d\<^sub>1 \<Longrightarrow> c \<sqsubseteq> d\<^sub>0 \<iinter> d\<^sub>1"
  by (metis conj_idem conj_mono)

lemma conjoin_non_aborting: "chaos \<sqsubseteq> c \<Longrightarrow> d \<sqsubseteq> d \<iinter> c"
  by (metis conj_mono order.refl conj_chaos)

lemma conjunction_sup: "c \<iinter> d \<sqsubseteq> c \<squnion> d"
  by (simp add: conj_refine)

lemma conjunction_sup_nonaborting: 
  assumes "chaos \<sqsubseteq> c" and "chaos \<sqsubseteq> d"
  shows "c \<iinter> d = c \<squnion> d"
proof (rule antisym)
  show "c \<squnion> d \<sqsubseteq> c \<iinter> d" using assms(1) assms(2) conjoin_non_aborting local.conj_commute by fastforce 
next
  show "c \<iinter> d \<sqsubseteq> c \<squnion> d" by (metis conjunction_sup)
qed

lemma conjoin_top: "chaos \<sqsubseteq> c \<Longrightarrow> c \<iinter> \<top> = \<top>"
by (simp add: conjunction_sup_nonaborting)

end

end
