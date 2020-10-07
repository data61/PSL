theory vertex_example_simps
imports "Lib/FiniteGraph" TopoS_Vertices
begin
(*<*)
\<comment> \<open>The follwoing lemmata are used in the @{text "\<exists>"}-style uniqueness proof\<close>
lemma False_set: "{(e1, e2). False} = {}" by blast
lemma succ_tran_empty: "(succ_tran \<lparr>nodes = V, edges = {}\<rparr> v) = {}"
  by(simp add: succ_tran_def)
lemma vertex_1_vertex_2_set_simp: "{vertex_1, vertex_2, vertex_1, vertex_2} = {vertex_1, vertex_2}" by blast
lemma unique_default_example1: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_1, vertex_2)}\<rparr> vertex_1 = {vertex_2}"
apply (simp add: succ_tran_def)
by (metis (lifting, no_types) Collect_cong Range.intros Range_empty Range_insert mem_Collect_eq singleton_conv singleton_iff trancl.r_into_trancl trancl_range)
lemma unique_default_example2: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_2, vertex_1)}\<rparr> vertex_1 = {}"
apply (simp add: succ_tran_def)
by (metis Domain.DomainI Domain_empty Domain_insert distinct_vertices12 singleton_iff trancl_domain)
lemma unique_default_example3: "succ_tran \<lparr>nodes = {vertex_1, vertex_2}, edges = {(vertex_2, vertex_1)}\<rparr> vertex_2 = {vertex_1}"
apply (simp add: succ_tran_def)
by (metis (lifting, no_types) Collect_cong Range.intros Range_empty Range_insert mem_Collect_eq singleton_conv singleton_iff trancl.r_into_trancl trancl_range)
lemma unique_default_example_simp1: "{(e1, e2). e1 = vertex_1 \<and> e2 = vertex_2 \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> vertex_2)} = {}" by blast
lemma unique_default_example_simp2: "{(vertex_1, vertex_2)}\<^sup>+ = {(vertex_1, vertex_2)}"
  apply(rule)
   apply(rule)
   apply(clarify)
   apply(rule_tac P="\<lambda> a b. a = vertex_1 \<and> b = vertex_2" in trancl.induct)
     apply auto
done
lemma unique_default_example_simp3: "{(e1, e2). e1 = vertex_2 \<and> e2 = vertex_1 \<and> (e1 = vertex_2 \<longrightarrow> e2 \<noteq> vertex_1)} = {}" 
  by(blast)
lemma vertex_set_simp2: "{vertex_2, vertex_1, vertex_2} = {vertex_1, vertex_2}" by blast
lemma canAccessThis_simp1: "canAccessThis \<noteq> vertex_1 \<Longrightarrow> succ_tran \<lparr>nodes = {vertex_1, canAccessThis}, edges = {(vertex_1, canAccessThis)}\<rparr> vertex_1 = {canAccessThis}"
apply (simp add: succ_tran_def)
by (metis (lifting, no_types) Collect_cong Range.intros Range_empty Range_insert mem_Collect_eq singleton_conv singleton_iff trancl.r_into_trancl trancl_range)
lemma canAccessThis_simp2: "canAccessThis \<noteq> vertex_1 \<Longrightarrow> succ_tran \<lparr>nodes = {vertex_1, canAccessThis}, edges = {(vertex_1, canAccessThis)}\<rparr> canAccessThis = {}"
apply (simp add: succ_tran_def)
by (metis Domain.DomainI Domain_empty Domain_insert singleton_iff trancl_domain)
lemma canAccessThis_simp3: 
  "canAccessThis \<noteq> vertex_1 \<Longrightarrow> {(e1, e2). e1 = vertex_1 \<and> e2 = canAccessThis \<and> (e1 = vertex_1 \<longrightarrow> e2 \<noteq> canAccessThis)} = {}" by blast
lemma canAccessThis_simp4: 
  "canAccessThis \<noteq> vertex_1 \<Longrightarrow> {vertex_1, canAccessThis, vertex_1, canAccessThis} = {vertex_1, canAccessThis}" by blast
lemmas example_simps = unique_default_example_simp1 unique_default_example2 unique_default_example3 
    unique_default_example_simp2 unique_default_example1 succ_tran_empty vertex_1_vertex_2_set_simp
    unique_default_example_simp3 vertex_set_simp2 canAccessThis_simp1 canAccessThis_simp2 canAccessThis_simp3
    canAccessThis_simp4
(*>*)
end
