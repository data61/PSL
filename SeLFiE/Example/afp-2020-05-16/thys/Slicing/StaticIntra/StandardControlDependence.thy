section \<open>Static Standard Control Dependence\<close>

theory StandardControlDependence imports 
  "../Basic/Postdomination" 
  "../Basic/DynStandardControlDependence"
begin

context Postdomination begin

subsubsection \<open>Definition and some lemmas\<close>

definition standard_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ controls\<^sub>s _" [51,0])
where standard_control_dependences_eq:"n controls\<^sub>s n' \<equiv> \<exists>as. n controls\<^sub>s n' via as"

lemma standard_control_dependence_def:"n controls\<^sub>s n' =
    (\<exists>a a' as. (n' \<notin> set(sourcenodes (a#as))) \<and> (n -a#as\<rightarrow>* n') \<and>
                   (n' postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' postdominates (targetnode a')))"
by(auto simp:standard_control_dependences_eq dyn_standard_control_dependence_def)


lemma Exit_not_standard_control_dependent:
  "n controls\<^sub>s (_Exit_) \<Longrightarrow> False"
by(auto simp:standard_control_dependences_eq 
        intro:Exit_not_dyn_standard_control_dependent)
             

lemma standard_control_dependence_def_variant:
  "n controls\<^sub>s n' = (\<exists>as. (n -as\<rightarrow>* n') \<and> (n \<noteq> n') \<and>
    (\<not> n' postdominates n) \<and> (n' \<notin> set(sourcenodes as)) \<and>
  (\<forall>n'' \<in> set(targetnodes as). n' postdominates n''))"
by(auto simp:standard_control_dependences_eq 
             dyn_standard_control_dependence_def_variant)


lemma inner_node_standard_control_dependence_predecessor:
  assumes "inner_node n" "(_Entry_) -as\<rightarrow>* n" "n -as'\<rightarrow>* (_Exit_)"
  obtains n' where "n' controls\<^sub>s n"
using assms
by(auto elim!:inner_node_dyn_standard_control_dependence_predecessor
        simp:standard_control_dependences_eq)

end

end
