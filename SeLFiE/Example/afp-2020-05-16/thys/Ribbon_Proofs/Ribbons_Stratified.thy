section \<open>Syntax and proof rules for stratified diagrams\<close>

theory Ribbons_Stratified imports 
  Ribbons_Interfaces
  Proofchain
begin

text \<open>We define the syntax of stratified diagrams. We give proof rules 
  for stratified diagrams, and prove them sound with respect to the 
  ordinary rules of separation logic.\<close>

subsection \<open>Syntax of stratified diagrams\<close>

datatype sdiagram = SDiagram "(cell \<times> interface) list" 
and cell = 
  Filler "interface"
| Basic "interface" "command" "interface"
| Exists_sdia "string" "sdiagram"
| Choose_sdia "interface" "sdiagram" "sdiagram" "interface"
| Loop_sdia "interface" "sdiagram" "interface"

datatype_compat sdiagram cell

type_synonym row = "cell \<times> interface"

text \<open>Extracting the command from a stratified diagram.\<close>
fun
  com_sdia :: "sdiagram \<Rightarrow> command" and
  com_cell :: "cell \<Rightarrow> command"
where
  "com_sdia (SDiagram \<rho>s) = foldr (;;) (map (com_cell \<circ> fst) \<rho>s) Skip"
| "com_cell (Filler P) = Skip"
| "com_cell (Basic P c Q) = c"
| "com_cell (Exists_sdia x D) = com_sdia D"
| "com_cell (Choose_sdia P D E Q) = Choose (com_sdia D) (com_sdia E)"
| "com_cell (Loop_sdia P D Q) = Loop (com_sdia D)"

text \<open>Extracting the program variables written by a stratified diagram.\<close>
fun
  wr_sdia :: "sdiagram \<Rightarrow> string set" and
  wr_cell :: "cell \<Rightarrow> string set" 
where
  "wr_sdia (SDiagram \<rho>s) = (\<Union>r \<in> set \<rho>s. wr_cell (fst r))"
| "wr_cell (Filler P) = {}"
| "wr_cell (Basic P c Q) = wr_com c"
| "wr_cell (Exists_sdia x D) = wr_sdia D"
| "wr_cell (Choose_sdia P D E Q) = wr_sdia D \<union> wr_sdia E"
| "wr_cell (Loop_sdia P D Q) = wr_sdia D"

text \<open>The program variables written by a stratified diagram correspond to
  those written by the commands therein.\<close>
lemma wr_sdia_is_wr_com:
  fixes \<rho>s :: "row list"
  and \<rho> :: row
  shows "(wr_sdia D = wr_com (com_sdia D))"
  and "(wr_cell \<gamma> = wr_com (com_cell \<gamma>))"
  and "(\<Union>\<rho> \<in> set \<rho>s. wr_cell (fst \<rho>)) 
    = wr_com (foldr (;;) (map (\<lambda>(\<gamma>,F). com_cell \<gamma>) \<rho>s) Skip)"
  and "wr_cell (fst \<rho>) = wr_com (com_cell (fst \<rho>))"
apply (induct D and \<gamma> and \<rho>s and \<rho> rule: compat_sdiagram.induct compat_cell.induct
  compat_cell_interface_prod_list.induct compat_cell_interface_prod.induct)
apply (auto simp add: wr_com_skip wr_com_choose
  wr_com_loop wr_com_seq split_def o_def)
done

subsection \<open>Proof rules for stratified diagrams\<close>

inductive 
  prov_sdia :: "[sdiagram, interface, interface] \<Rightarrow> bool" and
  prov_row :: "[row, interface, interface] \<Rightarrow> bool" and
  prov_cell :: "[cell, interface, interface] \<Rightarrow> bool"
where
  SRibbon: "prov_cell (Filler P) P P"
| SBasic: "prov_triple (asn P, c, asn Q) \<Longrightarrow> prov_cell (Basic P c Q) P Q"
| SExists: "prov_sdia D P Q 
    \<Longrightarrow> prov_cell (Exists_sdia x D) (Exists_int x P) (Exists_int x Q)"
| SChoice: "\<lbrakk> prov_sdia D P Q ; prov_sdia E P Q \<rbrakk> 
    \<Longrightarrow> prov_cell (Choose_sdia P D E Q) P Q"
| SLoop: "prov_sdia D P P \<Longrightarrow> prov_cell (Loop_sdia P D P) P P"
| SRow: "\<lbrakk> prov_cell \<gamma> P Q ; wr_cell \<gamma> \<inter> rd_int F = {} \<rbrakk>
    \<Longrightarrow> prov_row (\<gamma>, F) (P \<otimes> F) (Q \<otimes> F)"
| SMain: "\<lbrakk> chain_all (\<lambda>(P,\<rho>,Q). prov_row \<rho> P Q) \<Pi> ; 0 < chainlen \<Pi> \<rbrakk>
    \<Longrightarrow> prov_sdia (SDiagram (comlist \<Pi>)) (pre \<Pi>) (post \<Pi>)"

subsection \<open>Soundness\<close>

lemma soundness_strat_helper:
  "(prov_sdia D P Q \<longrightarrow> prov_triple (asn P, com_sdia D, asn Q)) \<and>
   (prov_row \<rho> P Q \<longrightarrow> prov_triple (asn P, com_cell (fst \<rho>), asn Q)) \<and>
   (prov_cell \<gamma> P Q \<longrightarrow> prov_triple (asn P, com_cell \<gamma>, asn Q))"
proof (induct rule: prov_sdia_prov_row_prov_cell.induct)
  case (SRibbon P)
  show ?case by (auto simp add: prov_triple.skip)
next
  case (SBasic P c Q)
  thus ?case by auto
next
  case (SExists D P Q x)
  thus ?case by (auto simp add: prov_triple.exists)
next
  case (SChoice D P Q E)
  thus ?case by (auto simp add: prov_triple.choose)
next
  case (SLoop D P)
  thus ?case by (auto simp add: prov_triple.loop)
next
  case (SRow \<gamma> P Q F)
  thus ?case
  by (simp add: prov_triple.frame rd_int_is_rd_ass wr_sdia_is_wr_com(2))
next
  case (SMain \<Pi>)
  thus ?case
  apply (unfold com_sdia.simps)
  apply (intro seq_fold[of _ \<Pi>])
  apply (simp_all add: len_comlist_chainlen)[3]
  apply (induct \<Pi>, simp)
  apply (case_tac i, auto simp add: fst3_simp thd3_simp)
  done
qed
  
corollary soundness_strat:
  assumes "prov_sdia D P Q"
  shows "prov_triple (asn P, com_sdia D, asn Q)"
using assms soundness_strat_helper by auto

end
