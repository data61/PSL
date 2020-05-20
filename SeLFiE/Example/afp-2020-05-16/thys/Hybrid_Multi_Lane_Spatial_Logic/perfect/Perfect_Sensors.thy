(*  Title:      perfect/Perfect_Sensors.thy
    Author:     Sven Linker

Instantiation of the sensor function to model "perfect sensors". That is,
each car can perceive both the physical size as well as the concrete
braking distance of all other cars.
*)

section \<open>Perfect Sensors\<close>
text\<open>
This section contains an instantiations of the sensor function for 
"perfect sensors". That is, each car can perceive both the physical
size as well as the braking distance of each other car. 
\<close>

theory Perfect_Sensors
  imports  "../Length"
begin
  
definition perfect::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  where "perfect e ts c \<equiv> traffic.physical_size ts c + traffic.braking_distance ts c " 
    
locale perfect_sensors = traffic+view
begin

interpretation perfect_sensors : sensors "perfect :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
proof unfold_locales
  fix e ts c
  show " 0 < perfect e ts c" 
    by (metis less_add_same_cancel2 less_trans perfect_def traffic.psGeZero traffic.sdGeZero)
qed
  
notation perfect_sensors.space ("space")
notation perfect_sensors.len ("len")

text\<open>
With this sensor definition, we can show that the perceived length of a car
is independent of the spatial transitions between traffic snapshots. The 
length may only change during evolutions, in particular if the car changes its dynamical
behaviour.
\<close>

lemma create_reservation_length_stable:
  "(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.create_reservation_def perfect_sensors.space_def perfect_def
    by (simp)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: perfect_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: perfect_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: perfect_sensors.len_def)
    qed
  qed
qed
  
lemma create_claim_length_stable:
  "(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.create_claim_def perfect_sensors.space_def perfect_def
    by (simp)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: perfect_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: perfect_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: perfect_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_reservation_length_stable:
  "(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.withdraw_reservation_def perfect_sensors.space_def perfect_def 
    by (simp)      
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: perfect_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: perfect_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: perfect_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_claim_length_stable:
  "(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.withdraw_claim_def perfect_sensors.space_def perfect_def 
    by (simp)      
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: perfect_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: perfect_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: perfect_sensors.len_def)
    qed
  qed
qed

text\<open>
The following lemma shows that the perceived length is independent from
the owner of the view. That is, as long as two views consist of the same 
extension, the perceived length of each car is the same in both views.
\<close>
  
lemma all_own_ext_eq_len_eq:
  "ext v = ext v'  \<longrightarrow> len v ts c = len v' ts c"
proof
  assume assm:"ext v = ext v'"
  hence sp:"space ts v c = space ts v' c" 
    by (simp add: perfect_def  perfect_sensors.space_def)
  have left_eq:"left (ext v) = left (ext v')" using assm by simp
  have right_eq:"right (ext v) = right (ext v')" using assm by simp
  show "len v ( ts) c = len v' ( ts) c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts v) c) > right (ext v')" 
      using right_eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: perfect_sensors.len_def right_eq assm sp)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts v) c) > right (ext v')" 
      using right_eq by simp
    show "len v ( ts) c = len v' ( ts) c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v') > right ((space ts v) c) "
        using left_eq by simp
      from outside_left and outside_left' show ?thesis 
        using perfect_sensors.len_def left_eq sp right_eq
        by auto
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v') > right ((space ts v) c) "
        using left_eq by simp
      from inside_left inside_right inside_left' inside_right' left_eq right_eq
      show ?thesis by (simp add:perfect_sensors.len_def sp)
    qed
  qed
qed

text\<open>
Finally, switching the perspective of a view does not change the
perceived length.
\<close>
    
lemma switch_length_stable:"(v=d>v') \<longrightarrow> len v ts c = len v' ts c"
  using all_own_ext_eq_len_eq view.switch_def  by metis

end
end
