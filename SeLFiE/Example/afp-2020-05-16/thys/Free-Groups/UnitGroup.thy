section \<open>The Unit Group\<close>

theory "UnitGroup"
imports
   "HOL-Algebra.Group"
   Generators
begin

text \<open>There is, up to isomorphisms, only one group with one element.\<close>

definition unit_group :: "unit monoid"
where 
  "unit_group \<equiv> \<lparr>
     carrier = UNIV,
     mult = \<lambda> x y. (),
     one = ()
  \<rparr>"

theorem unit_group_is_group: "group unit_group"
  by (rule groupI, auto simp add:unit_group_def)

theorem (in group) unit_group_unique:
  assumes "card (carrier G) = 1"
  shows "\<exists> h. h \<in> iso G unit_group"
proof-
  from assms obtain x where "carrier G = {x}" by (auto dest: card_eq_SucD)
  hence "(\<lambda> x. ()) \<in> iso G unit_group"  
    by -(rule group_isoI, auto simp add:unit_group_is_group is_group, simp add:unit_group_def)
  thus ?thesis by auto
qed

end
