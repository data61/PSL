section \<open>Static data dependence\<close>

theory DataDependence imports "../Basic/DynDataDependence" begin

context CFG_wf begin

definition data_dependence :: "'node \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> bool"
    ("_ influences _ in _" [51,0])
where data_dependences_eq:"n influences V in n' \<equiv> \<exists>as. n influences V in n' via as"

lemma data_dependence_def: "n influences V in n' = 
  (\<exists>a' as'. (V \<in> Def n) \<and> (V \<in> Use n') \<and>
                 (n -a'#as'\<rightarrow>* n') \<and> (\<forall>n'' \<in> set (sourcenodes as'). V \<notin> Def n''))"
by(auto simp:data_dependences_eq dyn_data_dependence_def)

end

end
