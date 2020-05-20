section\<open>The Axiom of Infinity in $M[G]$\<close>
theory Infinity_Axiom
  imports Pairing_Axiom Union_Axiom Separation_Axiom
begin

context G_generic begin

interpretation mg_triv: M_trivial"##M[G]"
  using transitivity_MG zero_in_MG generic Union_MG pairing_in_MG
  by unfold_locales auto

lemma infinity_in_MG : "infinity_ax(##M[G])"
proof -
  from infinity_ax obtain I where
    Eq1: "I\<in>M" "0 \<in> I" "\<forall>y\<in>M. y \<in> I \<longrightarrow> succ(y) \<in> I"
    unfolding infinity_ax_def  by auto
  then
  have "check(I) \<in> M"
    using check_in_M by simp
  then
  have "I\<in> M[G]"
    using valcheck generic one_in_G one_in_P GenExtI[of "check(I)" G] by simp
  with \<open>0\<in>I\<close>
  have "0\<in>M[G]" using transitivity_MG by simp
  with \<open>I\<in>M\<close>
  have "y \<in> M" if "y \<in> I" for y
    using  transitivity[OF _ \<open>I\<in>M\<close>] that by simp
  with \<open>I\<in>M[G]\<close>
  have "succ(y) \<in> I \<inter> M[G]" if "y \<in> I" for y
    using that Eq1 transitivity_MG by blast
  with Eq1 \<open>I\<in>M[G]\<close> \<open>0\<in>M[G]\<close>
  show ?thesis
    unfolding infinity_ax_def by auto
qed

end (* G_generic' *)
end