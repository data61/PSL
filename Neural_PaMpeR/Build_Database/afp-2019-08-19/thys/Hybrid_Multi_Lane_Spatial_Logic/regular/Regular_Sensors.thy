(*  Title:      regular/Regular_Sensors.thy
    Author:     Sven Linker

Instantiation of the sensor function to model "regular sensors". That is,
each car can perceive its the physical size and the concrete
braking distance, but can only perceive the physical size of all other cars.
*)

section \<open>Regular Sensors\<close>
text\<open>
This section contains an instantiations of the sensor function for 
"regular sensors". That is, each car can perceive its own physical
size and braking distance. However, it can only perceive
the physical size of other cars, and does not know about
their braking distance.
\<close>

theory Regular_Sensors
  imports  "../Length"
begin
  
definition regular::"cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real"
  where "regular e ts c \<equiv> 
    if (e = c) then traffic.physical_size ts c + traffic.braking_distance ts c 
               else traffic.physical_size ts c "  
    
locale regular_sensors = traffic + view
begin

interpretation regular_sensors: sensors "regular :: cars \<Rightarrow> traffic \<Rightarrow> cars \<Rightarrow> real "
proof unfold_locales
  fix e ts c
  show " 0 < regular e ts c" 
    by (metis (no_types, hide_lams) less_add_same_cancel2 less_trans regular_def
        traffic.psGeZero traffic.sdGeZero)
qed        
  
notation regular_sensors.space ("space")
notation regular_sensors.len ("len")

text\<open>
Similar to the situation with perfect sensors, we can show that the perceived length of a car
is independent of the spatial transitions between traffic snapshots. The 
length may only change during evolutions, in particular if the car changes its dynamical
behaviour.
\<close>

lemma create_reservation_length_stable:
  "(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>r(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.create_reservation_def sensors.space_def regular_def 
    by (simp add: regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma create_claim_length_stable:
  "(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>c(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.create_claim_def sensors.space_def regular_def  
    by (simp add: regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_reservation_length_stable:
  "(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdr(d,n)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c"
    using traffic.withdraw_reservation_def sensors.space_def regular_def
    by (simp add: regular_sensors.sensors_axioms)      
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed
  
lemma withdraw_claim_length_stable:
  "(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts') \<longrightarrow> len v ts c = len v ts' c"
proof
  assume assm:"(ts\<^bold>\<midarrow>wdc(d)\<^bold>\<rightarrow>ts')"
  hence eq:"space ts v c = space ts' v c" 
    using traffic.withdraw_claim_def sensors.space_def regular_def  
    by (simp add: regular_sensors.sensors_axioms)
  show "len v ( ts) c = len v ( ts') c"   
  proof (cases "left ((space ts v) c) > right (ext v)")
    assume outside_right:"left ((space ts v) c) > right (ext v)"
    hence outside_right':"left ((space ts' v) c) > right (ext v)" using eq by simp
    from outside_right and outside_right' show ?thesis 
      by (simp add: regular_sensors.len_def eq)
  next
    assume inside_right:"\<not> left ((space ts v) c) > right (ext v)"
    hence inside_right':"\<not> left ((space ts' v) c) > right (ext v)" using eq by simp
    show "len v ( ts) c = len v ( ts') c"
    proof (cases " left (ext v) > right ((space ts v) c) ")
      assume outside_left:" left (ext v) > right ((space ts v) c) "
      hence outside_left':" left (ext v) > right ((space ts' v) c) "using eq by simp
      from outside_left and outside_left' show ?thesis 
        by (simp add: regular_sensors.len_def eq)
    next
      assume inside_left:"\<not> left (ext v) > right ((space ts v) c) "
      hence inside_left':"\<not> left (ext v) > right ((space ts' v) c) " using eq by simp
      from inside_left inside_right inside_left' inside_right' eq 
      show ?thesis by (simp add: regular_sensors.len_def)
    qed
  qed
qed

text\<open>
Since the perceived length of cars depends on the owner of the view,
we can now prove how this perception changes if we change the
perspective of a view.
\<close>

lemma sensors_le:"e \<noteq> c \<longrightarrow> regular e ts c < regular c ts c"
  using  traffic.sdGeZero by (simp add: regular_def) 
   
lemma sensors_leq:" regular e ts c \<le> regular c ts c" 
  by (metis less_eq_real_def regular_sensors.sensors_le) 
    
lemma space_eq: "own v = own v' \<longrightarrow> space ts v c = space ts v' c" 
  using regular_sensors.space_def sensors_def by auto
    
lemma switch_space_le:"(own v) \<noteq> c \<and> (v=c>v') \<longrightarrow> space ts v c < space ts v' c" 
proof
  assume assm:"(own v) \<noteq> c \<and> (v=c>v')"
  hence sens:"regular (own v) ts c < regular (own v') ts c" 
    using sensors_le view.switch_def  by auto
  then have le:"pos ts c + regular (own v) ts c < pos ts c + regular (own v') ts c" 
    by auto     
  have left_eq:"left (space ts v c) = left (space ts v' c)" 
    using regular_sensors.left_space by auto 
  have r1:"right (space ts v c ) = pos ts c + regular (own v) ts c" 
    using regular_sensors.right_space  by auto      
  have r2:"right (space ts v' c ) = pos ts c + regular (own v') ts c" 
    using regular_sensors.right_space  by auto      
  then have "right (space ts v c) < right( space ts v' c)" 
    using r1 r2 le by auto
  then have "left (space ts v' c) \<ge> left (space ts v c)  
              \<and> (right (space ts v c) \<le> right( space ts v' c)) 
              \<and>  \<not>(left (space ts v c) \<ge> left (space ts v' c)  
                    \<and> right (space ts v' c) \<le> right (space ts v c))" 
    using regular_sensors.left_space left_eq by auto
  then show "space ts v c < space ts v' c" 
    using less_real_int_def left_eq by auto    
qed
  
lemma switch_space_leq:"(v=c>v') \<longrightarrow> space ts v c \<le> space ts v' c"
  by (metis less_imp_le order_refl switch_space_le view.switch_refl view.switch_unique)
end
end
