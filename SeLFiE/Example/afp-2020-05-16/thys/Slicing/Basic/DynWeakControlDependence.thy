section \<open>Dynamic Weak Control Dependence\<close>

theory DynWeakControlDependence imports Postdomination begin

context StrongPostdomination begin

definition
  dyn_weak_control_dependence :: "'node \<Rightarrow> 'node \<Rightarrow> 'edge list \<Rightarrow> bool" 
  ("_ weakly controls _ via _" [51,0,0])
where dyn_weak_control_dependence_def:"n weakly controls n' via as \<equiv> 
    (\<exists>a a' as'. (as = a#as') \<and> (n' \<notin> set(sourcenodes as)) \<and> (n -as\<rightarrow>* n') \<and>
                   (n' strongly-postdominates (targetnode a)) \<and>
                   (valid_edge a') \<and> (sourcenode a' = n) \<and> 
                   (\<not> n' strongly-postdominates (targetnode a')))"


lemma Exit_not_dyn_weak_control_dependent:
  assumes control:"n weakly controls (_Exit_) via as" shows "False"
proof -
  from control obtain as a as' where path:"n -as\<rightarrow>* (_Exit_)" and as:"as = a#as'"
    and pd:"(_Exit_) postdominates (targetnode a)"
    by(auto simp:dyn_weak_control_dependence_def strong_postdominate_def)
  from path as have "n -[]@a#as'\<rightarrow>* (_Exit_)" by simp
  hence "valid_edge a" by(fastforce dest:path_split)
  with pd show False by -(rule Exit_no_postdominator,auto)
qed

end

end
