theory Compiler imports Compiler1 Compiler2 begin

definition J2JVM :: "'addr J_prog \<Rightarrow> 'addr jvm_prog"
where [code del]: "J2JVM \<equiv> compP2 \<circ> compP1"

lemma J2JVM_code [code]:
  "J2JVM = compP (\<lambda>C M Ts T (pns, body). compMb2 (compE1 (this#pns) body))"
by(simp add: J2JVM_def compP2_def o_def compP_compP split_def)

end
