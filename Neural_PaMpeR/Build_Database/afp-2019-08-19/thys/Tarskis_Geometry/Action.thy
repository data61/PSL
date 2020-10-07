(*  Title:       Right group actions
    Author:      Tim Makarios <tjm1983 at gmail.com>, 2012
    Maintainer:  Tim Makarios <tjm1983 at gmail.com>
*)

(* After Isabelle 2012, this may be moved to ~~/src/HOL/Algebra *)

section "Right group actions"

theory Action
  imports "HOL-Algebra.Group"
begin

locale action = group +
  fixes act :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" (infixl "<o" 69)
  assumes id_act [simp]: "b <o \<one> = b"
  and act_act':
  "g \<in> carrier G \<and> h \<in> carrier G \<longrightarrow> (b <o g) <o h = b <o (g \<otimes> h)"
begin

lemma act_act:
  assumes "g \<in> carrier G" and "h \<in> carrier G"
  shows "(b <o g) <o h = b <o (g \<otimes> h)"
proof -
  from \<open>g \<in> carrier G\<close> and \<open>h \<in> carrier G\<close> and act_act'
  show "(b <o g) <o h = b <o (g \<otimes> h)" by simp
qed

lemma act_act_inv [simp]:
  assumes "g \<in> carrier G"
  shows "b <o g <o inv g = b"
proof -
  from \<open>g \<in> carrier G\<close> have "inv g \<in> carrier G" by (rule inv_closed)
  with \<open>g \<in> carrier G\<close> have "b <o g <o inv g = b <o g \<otimes> inv g" by (rule act_act)
  with \<open>g \<in> carrier G\<close> show "b <o g <o inv g = b" by simp
qed

lemma act_inv_act [simp]:
  assumes "g \<in> carrier G"
  shows "b <o inv g <o g = b"
  using \<open>g \<in> carrier G\<close> and act_act_inv [of "inv g"]
  by simp

lemma act_inv_iff:
  assumes "g \<in> carrier G"
  shows "b <o inv g = c \<longleftrightarrow> b = c <o g"
proof
  assume "b <o inv g = c"
  hence "b <o inv g <o g = c <o g" by simp
  with \<open>g \<in> carrier G\<close> show "b = c <o g" by simp
next
  assume "b = c <o g"
  hence "b <o inv g = c <o g <o inv g" by simp
  with \<open>g \<in> carrier G\<close> show "b <o inv g = c" by simp
qed

end

end
