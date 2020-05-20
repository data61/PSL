(*  Title:     Sensors.thy
    Author:     Sven Linker

Defines perfect sensors for cars. Cars can perceive both
the physical size and braking distance of all other cars.
*)

section\<open> Sensors for Cars\<close>
text\<open>
This section presents the abstract definition of a function
determining the sensor capabilities of cars. Such a function
takes a car \(e\), a traffic snapshot \(ts\) and another
car \(c\), and returns the length of \(c\) as perceived
by \(e\) at the situation determined by \(ts\). The 
only restriction we impose is that this length is always
greater than zero.

With such a function, we define a derived notion of the
\emph{space} the car \(c\) occupies as perceived by \(e\).
However, this does not define the lanes \(c\) occupies, but
only a continuous interval. The lanes occupied by \(c\) 
are given by the reservation and claim functions of 
the traffic snapshot \(ts\).
\<close>
  
theory Sensors
  imports "Traffic" "Views"
begin 

locale sensors = traffic + view +
  fixes sensors::"(cars) \<Rightarrow> traffic \<Rightarrow> (cars) \<Rightarrow> real" 
  assumes sensors_ge:"(sensors e ts c) > 0"
begin
  
definition space ::" traffic \<Rightarrow> view \<Rightarrow> cars \<Rightarrow> real_int"
  where "space ts v c \<equiv> Abs_real_int (pos ts c, pos ts c + sensors (own v) ts c)"
    
lemma left_space: "left (space ts v c) = pos ts c" 
proof -
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_ge  
    by (metis (no_types, hide_lams)  less_add_same_cancel1  )
  show "left (space ts v c ) = pos ts c" 
    using space_def Abs_real_int_inverse 1 by simp 
qed
  
lemma right_space: "right (space ts v c) =   pos ts c + sensors (own v) ts c"
proof - 
  have 1:"pos ts c < pos ts c + sensors (own v) ts c" using sensors_ge  
    by (metis (no_types, hide_lams)  less_add_same_cancel1  )
  show 3:"right(space ts v c ) = pos ts c + sensors (own v) ts c" 
    using space_def Abs_real_int_inverse 1 by simp
qed
  
lemma space_nonempty:"left (space ts v c ) < right (space ts v c)" 
  using left_space right_space sensors_ge by simp
    
end
end
