section \<open>Static Weak Control Dependence\<close>

theory WeakControlDependence imports 
  "../Basic/Postdomination" 
  "../Basic/DynWeakControlDependence"
begin

context StrongPostdomination begin

definition 
  weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> bool" 
  ("_ weakly controls _" [51,0])
where weak_control_dependences_eq:
    "n weakly controls n' \<equiv> \<exists>as. n weakly controls n' via as"

lemma 
  weak_control_dependence_def:"n weakly controls n' = 
    (\<exists>a a' as. (n' \<notin> set(sourcenodes (a#as))) \<and> (n -a#as\<rightarrow>* n') \<and>
                   (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"
by(auto simp:weak_control_dependences_eq dyn_weak_control_dependence_def)


lemma Exit_not_weak_control_dependent:
  "n weakly controls (_Exit_) \<Longrightarrow> False"
by(auto simp:weak_control_dependences_eq 
        intro:Exit_not_dyn_weak_control_dependent)

end

end
