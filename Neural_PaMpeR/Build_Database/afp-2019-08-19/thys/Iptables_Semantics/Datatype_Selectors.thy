theory Datatype_Selectors
imports Main
begin

text\<open>
  Running Example: \<open>datatype_new iptrule_match = is_Src: Src (src_range: ipt_iprange)\<close>

  A discriminator \<open>disc\<close> tells whether a value is of a certain constructor.
    Example: \<open>is_Src\<close>

  A selector \<open>sel\<close> select the inner value.
    Example: \<open>src_range\<close>

  A constructor \<open>C\<close> constructs a value
    Example: \<open>Src\<close>


  The are well-formed if the belong together.
\<close>
fun wf_disc_sel :: "(('a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'b)) \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> bool" where
  "wf_disc_sel (disc, sel) C \<longleftrightarrow> (\<forall>a. disc a \<longrightarrow> C (sel a) = a) \<and> (\<forall>a. \<^cancel>\<open>disc (C a) \<longrightarrow>\<close> sel (C a) = a)"

(* should the following be added to the definition?
 the discriminator is true for all C independent of the a
 for example: is_Src_IP is true for all Src_IPs, independent of the numberic value of the ip.
lemma "wf_disc_sel (disc, sel) C \<Longrightarrow> (\<exists>a. disc (C a)) \<longrightarrow> (\<forall>a. disc (C a))"
*)

declare wf_disc_sel.simps[simp del]

end
