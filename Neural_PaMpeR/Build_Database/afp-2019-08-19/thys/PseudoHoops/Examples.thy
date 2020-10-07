section\<open>Examples of Pseudo-Hoops\<close>

theory Examples
imports SpecialPseudoHoops LatticeProperties.Lattice_Ordered_Group
begin

declare add_uminus_conv_diff [simp del] right_minus [simp]
lemmas diff_minus = diff_conv_add_uminus

context lgroup
begin
lemma (in lgroup) less_eq_inf_2: "(x \<le> y) = (inf y x = x)"
  by (simp add: le_iff_inf inf_commute)
end


class lgroup_with_const = lgroup +
  fixes u::'a
  assumes [simp]: "0 \<le> u"

definition "G = {a::'a::lgroup_with_const. (0 \<le> a \<and> a \<le> u)}"
typedef (overloaded) 'a G = "G::'a::lgroup_with_const set"
proof
  show "0 \<in> G" by (simp add: G_def)
qed


instantiation "G" :: (lgroup_with_const) bounded_wajsberg_pseudo_hoop_algebra
begin

definition
  times_def: "a * b \<equiv> Abs_G (sup (Rep_G a - u + Rep_G b) 0)"

lemma [simp]: "sup (Rep_G a - u + Rep_G b) 0 \<in> G"
  apply (cut_tac x = a in Rep_G)
  apply (cut_tac x = b in Rep_G)
  apply (unfold G_def)
  apply safe
  apply (simp_all add: diff_minus)
  apply (rule right_move_to_right)
  apply (rule_tac y = 0 in order_trans)
  apply (rule right_move_to_right)
  apply simp
  apply (rule right_move_to_left)
  by simp
  

definition
  impl_def: "a l\<rightarrow> b \<equiv> Abs_G ((Rep_G b - Rep_G a + u) \<sqinter> u)"

lemma [simp]: "inf (Rep_G (b::'a G) - Rep_G a + u) u \<in> G"
  apply (cut_tac x = a in Rep_G)
  apply (cut_tac x = b in Rep_G)
  apply (unfold G_def)
  apply (simp_all add: diff_minus)
  apply safe
  apply (rule right_move_to_left) 
  apply (rule right_move_to_left) 
  apply simp
  apply (rule_tac y = 0 in order_trans)
  apply (rule left_move_to_right) 
  by simp_all
  
definition
  impr_def: "a r\<rightarrow> b \<equiv> Abs_G (inf (u - Rep_G a + Rep_G b) u)"

lemma [simp]: "inf (u - Rep_G a + Rep_G b) u \<in> G"
  apply (cut_tac x = a in Rep_G)
  apply (cut_tac x = b in Rep_G)
  apply (unfold G_def)
  apply (simp_all add: diff_minus)
  apply safe
  apply (rule right_move_to_left)
  apply (rule right_move_to_left) 
  apply simp
  apply (rule left_move_to_right)
  apply (rule_tac y = u in order_trans)
  apply  simp_all
  apply (rule right_move_to_left)
  by simp_all

definition
  one_def: "1 \<equiv> Abs_G u"

definition
  zero_def: "0 \<equiv> Abs_G 0"

definition
  order_def: "((a::'a G) \<le> b) \<equiv> (a l\<rightarrow> b = 1)"

definition
  strict_order_def: "(a::'a G) < b \<equiv> (a \<le> b \<and> \<not> b \<le> a)"

definition
  inf_def: "(a::'a G) \<sqinter> b = ((a l\<rightarrow> b) * a)"

lemma [simp]: "(u::'a) \<in> G"
  by (simp add: G_def)

lemma [simp]: "(1::'a G) * a = a"
  apply (simp add: one_def times_def)
  apply (cut_tac y = "u::'a" in Abs_G_inverse)
  apply simp_all
  apply (subgoal_tac "sup (Rep_G a) (0::'a) = Rep_G a")
  apply (simp add: Rep_G_inverse)
  apply (cut_tac x = a in Rep_G)
  apply (rule antisym)
  apply (simp add: G_def)
  by simp

lemma [simp]: "a * (1::'a G) = a"
  apply (simp add: one_def times_def)
  apply (cut_tac y = "u::'a" in Abs_G_inverse)
  apply (simp_all add: diff_minus add.assoc)
  apply (subgoal_tac "sup (Rep_G a) (0::'a) = Rep_G a")
  apply (simp add: Rep_G_inverse)
  apply (cut_tac x = a in Rep_G)
  apply (rule antisym)
  by (simp_all add: G_def)

lemma [simp]: "a l\<rightarrow> a = (1::'a G)"
  by (simp add: one_def impl_def)

lemma [simp]: "a r\<rightarrow> a = (1::'a G)"
  by (simp add: one_def impr_def diff_minus add.assoc)

lemma [simp]: "a \<in> G \<Longrightarrow> Rep_G (Abs_G a) = a"
  apply (rule Abs_G_inverse)
  by simp

lemma inf_def_1: "((a::'a G) l\<rightarrow> b) * a = Abs_G (inf (Rep_G a) (Rep_G b))"
  apply (simp add: times_def impl_def)
  apply (subgoal_tac "sup (inf (Rep_G b) (Rep_G a)) 0 = inf (Rep_G a) (Rep_G b)")
  apply simp
  apply (rule antisym)
  apply (cut_tac x = "a" in Rep_G)
  apply (cut_tac x = "b" in Rep_G)
  apply (simp add: G_def)
  apply (subgoal_tac "inf (Rep_G a) (Rep_G b) = inf (Rep_G b) (Rep_G a)")
  apply simp
  apply (rule antisym)
  by simp_all

lemma inf_def_2: "(a::'a G) * (a r\<rightarrow> b) = Abs_G (inf (Rep_G a) (Rep_G b))"
  apply (simp add: times_def impr_def)
  apply (simp add: diff_minus add.assoc [THEN sym])
  apply (simp add: add.assoc)
  apply (subgoal_tac "sup (inf (Rep_G b) (Rep_G a)) 0 = inf (Rep_G a) (Rep_G b)")
  apply simp
  apply (rule antisym)
  apply (cut_tac x = "a" in Rep_G)
  apply (cut_tac x = "b" in Rep_G)
  apply (simp add: G_def)
  apply (subgoal_tac "inf (Rep_G a) (Rep_G b) = inf (Rep_G b) (Rep_G a)")
  apply simp
  apply (rule antisym)
  by simp_all

lemma Rep_G_order: "(a \<le> b) = (Rep_G a \<le> Rep_G b)" 
  apply (simp add: order_def impl_def one_def)
  apply safe
  apply (subgoal_tac "Rep_G (Abs_G (inf (Rep_G b - Rep_G a + u) u)) = Rep_G (Abs_G u)")
  apply (drule drop_assumption)
  apply simp
  apply (subst (asm) less_eq_inf_2 [THEN sym])
  apply (simp add: diff_minus)
  apply (drule_tac a = "u" and b = " Rep_G b + - Rep_G a + u" and v = "-u" in add_order_preserving_right)
  apply (simp add: add.assoc)
  apply (drule_tac a = "0" and b = " Rep_G b + - Rep_G a" and v = "Rep_G a" in add_order_preserving_right)
  apply (simp add: add.assoc)
  apply simp
  apply (subgoal_tac "Rep_G (Abs_G (inf (Rep_G b - Rep_G a + u) u)) = Rep_G (Abs_G u)")
  apply simp
  apply simp
  apply (subst less_eq_inf_2 [THEN sym])
  apply (rule right_move_to_left)
  apply simp
  apply (simp add: diff_minus)
  apply (rule right_move_to_left)
  by simp

lemma ded_left: "((a::'a G) * b) l\<rightarrow> c = a l\<rightarrow> b l\<rightarrow> c"
  apply (simp add: times_def impl_def)
  apply (simp add: diff_minus minus_add)
  apply (simp add: add.assoc [THEN sym])
  apply (simp add: inf_assoc)
  apply (subgoal_tac "inf (Rep_G c + u) u = u")
  apply (subgoal_tac "inf (u + - Rep_G a + u) u = u")
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply (simp add: add.assoc)
  apply (rule add_pos)
  apply (cut_tac x = a in Rep_G)
  apply (simp add: G_def)
  apply (rule left_move_to_left)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply (rule add_pos_left)
  apply (cut_tac x = c in Rep_G)
  by (simp add: G_def)

lemma ded_right: "((a::'a G) * b) r\<rightarrow> c = b r\<rightarrow> a r\<rightarrow> c"
  apply (simp add: times_def impr_def)
  apply (simp add: diff_minus minus_add)
  apply (simp add: add.assoc [THEN sym])
  apply (simp add: inf_assoc)
  apply (subgoal_tac "inf (u + Rep_G c) u = u")
  apply (subgoal_tac "inf (u + - Rep_G b + u) u = u")
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply (simp add: add.assoc)
  apply (rule add_pos)
  apply (cut_tac x = b in Rep_G)
  apply (simp add: G_def)
  apply (rule left_move_to_left)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply (rule add_pos)
  apply (cut_tac x = c in Rep_G)
  by (simp add: G_def)


lemma [simp]: "0 \<in> G"
  by (simp add: G_def)

lemma [simp]: "0 \<le> (a::'a G)"
  apply (simp add: order_def impl_def zero_def one_def diff_minus)
  apply (subgoal_tac "inf (Rep_G a + u) u = u")
  apply simp
  apply (rule antisym)
  apply simp
  apply (cut_tac x = a in Rep_G)
  apply (unfold G_def)
  apply simp 
  apply (rule add_pos_left)
  by simp

lemma lemma_W1: "((a::'a G) l\<rightarrow> b) r\<rightarrow> b = (b l\<rightarrow> a) r\<rightarrow> a"
  apply (simp add: impl_def impr_def) 
  apply (simp add: diff_minus minus_add)
  apply (simp add: add.assoc)
  apply (subgoal_tac "Rep_G a \<squnion> Rep_G b = Rep_G b \<squnion> Rep_G a")
  apply simp
  apply (rule antisym)
  by simp_all
  (*by (simp add: sup_commute)*)

lemma lemma_W2: "((a::'a G) r\<rightarrow> b) l\<rightarrow> b = (b r\<rightarrow> a) l\<rightarrow> a"
  apply (simp add: impl_def impr_def) 
  apply (simp add: diff_minus minus_add)
  apply (simp add: add.assoc)
  apply (subgoal_tac "Rep_G a \<squnion> Rep_G b = Rep_G b \<squnion> Rep_G a")
  apply simp
  apply (rule antisym)
  by simp_all
  (*by (simp add: sup_commute)*)

instance proof
  fix a show "(1::'a G) * a = a" by simp
  fix a show "a * (1::'a G) = a" by simp
  fix a show "a l\<rightarrow> a = (1::'a G)" by simp
  fix a show "a r\<rightarrow> a = (1::'a G)" by simp
next
  fix a b have a: "((a::'a G) l\<rightarrow> b) * a = (b l\<rightarrow> a) * b" 
    by (simp add: inf_def_1 inf_commute) 
  show "((a::'a G) l\<rightarrow> b) * a = (b l\<rightarrow> a) * b" by (rule a)
next
  fix a b have a: "a * ((a::'a G) r\<rightarrow> b) = b * (b r\<rightarrow> a)" by (simp add: inf_def_2 inf_commute)  
  show "a * ((a::'a G) r\<rightarrow> b) = b * (b r\<rightarrow> a)" by (rule a)
next
  fix a b have "!!a b . ((a::'a G) l\<rightarrow> b) * a = a * (a r\<rightarrow> b)" by (simp add: inf_def_2 inf_def_1)  
  from this show "((a::'a G) l\<rightarrow> b) * a = a * (a r\<rightarrow> b)"  by simp
next
  fix a b c show "(a::'a G) * b l\<rightarrow> c = a l\<rightarrow> b l\<rightarrow> c" by (rule ded_left)
next
  fix a b c show "(a::'a G) * b r\<rightarrow> c = b r\<rightarrow> a r\<rightarrow> c" by (rule ded_right)
next
  fix a::"'a G" have "0 \<le> a" by simp
  from this show "0 \<le> a" by simp
next
  fix a b::"'a G" show "(a \<le> b) = (a l\<rightarrow> b = 1)" by (simp add: order_def)
next 
  fix a b::"'a G" show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)" by (simp add: strict_order_def)
next
  fix a b::"'a G" show "(a l\<rightarrow> b) r\<rightarrow> b = (b l\<rightarrow> a) r\<rightarrow> a" by (rule lemma_W1)
next
  fix a b::"'a G" show "(a r\<rightarrow> b) l\<rightarrow> b = (b r\<rightarrow> a) l\<rightarrow> a" by (rule lemma_W2)
next
  fix a b::"'a G" show "a \<sqinter> b = (a l\<rightarrow> b) * a" by (rule inf_def)
next
  fix a b::"'a G" show "a \<sqinter> b = a * (a r\<rightarrow> b)" by (simp add: inf_def inf_def_2 inf_def_1) 
qed

end

context order
begin
definition
  closed_interval::"'a\<Rightarrow>'a\<Rightarrow>'a set" ("|[ _ , _ ]|" [0, 0] 900) where
  "closed_interval a b = {c . a \<le> c \<and> c \<le> b}"

definition
  "convex = {A . \<forall> a b . a \<in> A \<and> b \<in> A \<longrightarrow> |[a, b]| \<subseteq> A}"

end

context group_add
begin
definition
  "subgroup = {A . 0 \<in> A \<and> (\<forall> a b . a \<in> A \<and> b \<in> A \<longrightarrow> a + b \<in> A \<and> -a \<in> A)}"

lemma [simp]: "A \<in> subgroup \<Longrightarrow> 0 \<in> A"
  by (simp add: subgroup_def)

lemma [simp]: "A \<in> subgroup \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> a + b \<in> A"
  apply (subst (asm) subgroup_def)
  by simp

lemma minus_subgroup: "A \<in> subgroup \<Longrightarrow> -a \<in> A \<Longrightarrow> a \<in> A"
  apply (subst (asm) subgroup_def)
  apply safe
  apply (drule_tac x="-a" in spec) 
  by simp


definition
  add_set:: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "+++" 70) where
  "add_set A B = {c . \<exists> a \<in> A .\<exists> b \<in> B . c = a + b}"

definition
  "normal = {A . (\<forall> a . A +++ {a} = {a} +++ A)}"
end

context lgroup
begin
definition
  "lsubgroup = {A . A \<in> subgroup \<and> (\<forall> a b . a \<in> A \<and> b \<in> A \<longrightarrow> inf a b \<in> A \<and> sup a b \<in> A)}"

lemma inf_lsubgroup:
  "A \<in> lsubgroup \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> inf a b \<in> A"
  by (simp add: lsubgroup_def)

lemma sup_lsubgroup:
  "A \<in> lsubgroup \<Longrightarrow> a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> sup a b \<in> A"
  by (simp add: lsubgroup_def)
end


definition
  "F K = {a:: 'a G . (u::'a::lgroup_with_const) - Rep_G a \<in> K}"

lemma F_def2: "K \<in> normal \<Longrightarrow> F K = {a:: 'a G . - Rep_G a + (u::'a::lgroup_with_const) \<in> K}"
  apply (simp add: normal_def F_def)
  apply safe
  apply (drule_tac x = "Rep_G x" in spec)
  apply (subgoal_tac "u \<in> K +++ {Rep_G x}")
  apply simp
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (simp add: add_set_def)
  apply safe
  apply (subgoal_tac "- Rep_G x + u = - Rep_G x + Rep_G x + b")
  apply simp
  apply (subst add.assoc)
  apply simp
  apply (subst add_set_def)
  apply simp
  apply (rule_tac x = "u - Rep_G x" in bexI)
  apply (simp add: diff_minus add.assoc)
  apply simp
  apply (drule_tac x = "Rep_G x" in spec)
  apply (subgoal_tac "u \<in> K +++ {Rep_G x}")
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (simp add: add_set_def)
  apply safe
  apply (subgoal_tac "u - Rep_G x = a +  (Rep_G x -  Rep_G x)")
  apply simp
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst add.assoc [THEN sym])
  apply simp
  apply simp
  apply (subst add_set_def)
  apply simp
  apply (rule_tac x = "- Rep_G x + u" in bexI)
  apply (simp add: add.assoc [THEN sym])
  by simp

context lgroup begin
lemma sup_assoc_lgroup: "a \<squnion> b \<squnion> c = a \<squnion> (b \<squnion> c)"
  by (rule sup_assoc)

end

lemma normal_1: "K \<in> normal \<Longrightarrow> K \<in> convex \<Longrightarrow> K \<in> lsubgroup \<Longrightarrow> x \<in> {a} ** F K \<Longrightarrow> x \<in> F K ** {a}"
  apply (subst (asm) times_set_def)
  apply simp
  apply safe
  apply (subst (asm) F_def2)
  apply simp_all
  apply (subgoal_tac "-u + Rep_G y \<in> K")
  apply (subgoal_tac "Rep_G a - u + Rep_G y \<in> K +++ {Rep_G a}")
  apply (subst (asm) add_set_def)
  apply simp
  apply safe
  apply (simp add: times_set_def)
  apply (rule_tac x = "Abs_G (inf (sup (aa + u) 0) u)" in bexI)
  apply (subgoal_tac "aa =  Rep_G a - u + Rep_G y - Rep_G a")
  apply (subgoal_tac "inf (sup (aa + u) (0::'a)) u \<in> G")
  apply safe
  apply simp
  apply (simp add: times_def)
  apply (subgoal_tac "(sup (Rep_G a - u + Rep_G y) 0) = (sup (inf (sup (Rep_G a - u + Rep_G y - Rep_G a + u - u + Rep_G a) (- u + Rep_G a)) (Rep_G a)) 0)")
  apply simp
  apply (simp add: diff_minus add.assoc)
  apply (subgoal_tac "inf (sup (Rep_G a + (- u + Rep_G y)) (- u + Rep_G a)) (Rep_G a) = (sup (Rep_G a + (- u + Rep_G y)) (- u + Rep_G a))")
  apply simp
  (*apply (subst sup_assoc) - why it does not work*)
  apply (subst sup_assoc_lgroup)
  apply (subgoal_tac "(sup (- u + Rep_G a) (0::'a)) = 0")
  apply simp
  apply (rule antisym)
  apply simp
  apply (rule left_move_to_right)
  apply simp
  apply (cut_tac x = a in Rep_G)
  apply (simp add: G_def)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply safe
  apply (rule left_move_to_right)
  apply simp
  apply (rule left_move_to_right)
  apply simp
  apply (cut_tac x = y in Rep_G)
  apply (simp add: G_def)
  apply (rule left_move_to_right)
  apply simp
  apply (rule right_move_to_left)
  apply simp
  apply (simp add: G_def)
  apply (simp add: diff_minus)
  apply (simp add: add.assoc)
  apply (simp add: F_def)
  apply (subgoal_tac "inf (sup (aa + u) (0::'a)) u \<in> G")
  apply simp
  apply (simp add: diff_minus minus_add add.assoc [THEN sym])
  apply (subst (asm) convex_def)
  apply simp
  apply (drule_tac x = 0 in spec)
  apply (drule_tac x = "sup (- aa) 0" in spec)
  apply safe
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply (rule sup_lsubgroup)
  apply simp
  apply (rule minus_subgroup)
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply simp
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply (subgoal_tac "sup (inf (- aa) u) (0::'a) \<in> |[ 0::'a , sup (- aa) (0::'a) ]|")
  apply blast
  apply (subst closed_interval_def)
  apply safe
  apply simp
  apply simp
(*
  apply (rule_tac y = "-aa" in order_trans)
  apply simp
  apply simp
*)
  apply (simp add: G_def)
  apply (subst (asm) normal_def)
  apply simp
  apply (drule drop_assumption)
  apply (simp add: add_set_def)
  apply (rule_tac x = "-u + Rep_G y" in bexI)
  apply (simp add: diff_minus add.assoc)
  apply simp
  apply (rule minus_subgroup)
  apply (simp add: lsubgroup_def)
  by (simp add: minus_add)

lemma normal_2: "K \<in> normal \<Longrightarrow> K \<in> convex \<Longrightarrow> K \<in> lsubgroup \<Longrightarrow> x \<in> F K ** {a} \<Longrightarrow> x \<in> {a} ** F K"
  apply (subst (asm) times_set_def)
  apply simp
  apply safe
  apply (subst (asm) F_def)
  apply simp_all
  apply hypsubst_thin
  apply (subgoal_tac "Rep_G x - u \<in> K")
  apply (subgoal_tac "Rep_G x - u + Rep_G a \<in> {Rep_G a} +++ K")
  apply (subst (asm) add_set_def)
  apply simp
  apply safe
  apply (simp add: times_set_def)
  apply (rule_tac x = "Abs_G (inf (sup (u + b) 0) u)" in bexI)
  apply (subgoal_tac "b =  - Rep_G a + Rep_G x - u + Rep_G a")
  apply (subgoal_tac "inf (sup (u + b) 0) u \<in> G")
  apply safe
  apply simp
  apply (simp add: times_def)
  apply (simp add: diff_minus add.assoc)
  apply (simp add: add.assoc [THEN sym])
  apply (subgoal_tac "sup (Rep_G x + - u + Rep_G a) 0 = sup (inf (sup (Rep_G x + - u + Rep_G a) (Rep_G a + - u)) (Rep_G a)) 0")
  apply simp
  apply (subgoal_tac "inf (sup (Rep_G x + - u + Rep_G a) (Rep_G a + - u)) (Rep_G a) = sup (Rep_G x + - u + Rep_G a) (Rep_G a + - u)")
  apply simp
  (*apply (subst sup_assoc) - why it does not work*)
  apply (subst sup_assoc_lgroup)
  apply (subgoal_tac "(sup (Rep_G a + - u) (0::'a)) = 0")
  apply simp
  apply (rule antisym)
  apply simp
  apply (rule right_move_to_right)
  apply simp
  apply (cut_tac x = a in Rep_G)
  apply (simp add: G_def)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply safe
  apply (rule right_move_to_right)
  apply simp
  apply (rule right_move_to_right)
  apply simp
  apply (cut_tac x = x in Rep_G)
  apply (simp add: G_def)
  apply (rule right_move_to_right)
  apply simp
  apply (rule left_move_to_left)
  apply simp
  apply (simp add: G_def)
  apply (simp add: diff_minus)
  apply (simp add: add.assoc)
  apply (simp add: F_def2)
  apply (subgoal_tac "inf (sup (u + b) (0::'a)) u \<in> G")
  apply simp
  apply (simp add: diff_minus minus_add add.assoc [THEN sym])
  apply (subst (asm) convex_def)
  apply simp
  apply (drule_tac x = 0 in spec)
  apply (drule_tac x = "sup (- b) 0" in spec)
  apply safe
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply (rule sup_lsubgroup)
  apply simp
  apply (rule minus_subgroup)
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply simp
  apply (subst (asm) lsubgroup_def)
  apply simp
  apply (simp add: add.assoc)
  apply (subgoal_tac "sup (inf (- b) u) (0::'a) \<in> |[ 0::'a , sup (-b) 0]|")
  apply blast
  apply (subst closed_interval_def)
  apply safe
  apply simp
  apply simp
(*
  apply (rule_tac y = "-b" in order_trans)
  apply simp
  apply simp
*)
  apply (simp add: G_def)
  apply (subgoal_tac  "{Rep_G a} +++ K = K +++ {Rep_G a}")
  apply simp
  apply (simp add: add_set_def)
  apply (subst (asm) normal_def)
  apply simp
  apply (rule minus_subgroup)
  apply (simp add: lsubgroup_def)
  by (simp add: diff_minus minus_add)

lemma "K \<in> normal \<Longrightarrow> K \<in> convex \<Longrightarrow> K \<in> lsubgroup \<Longrightarrow> F K \<in> normalfilters"
  apply (rule lemma_3_10_ii_i)
  apply (subgoal_tac "K \<in> subgroup")
  apply (subst filters_def)
  apply safe
  apply (subgoal_tac "1 \<in> F K")
  apply simp
  apply (subst F_def)
  apply safe
  apply (subst one_def)
  apply simp
  apply (simp add: F_def)
  apply (simp add: convex_def)
  apply (drule_tac x = 0 in spec)
  apply (drule_tac x = "(u - Rep_G b) + (u - Rep_G a) " in spec)
  apply simp
  apply (subgoal_tac "u - Rep_G (a * b) \<in> |[ 0::'a , u - Rep_G b + (u - Rep_G a) ]|")
  apply blast
  apply (simp add: closed_interval_def)
  apply safe
  apply (cut_tac x = "a * b" in Rep_G)
  apply (simp add: G_def diff_minus)
  apply (rule right_move_to_left)
  apply simp
  apply (simp add: times_def)
  apply (subgoal_tac "(u - (Rep_G a - u + Rep_G b)) = u - Rep_G b + (u - Rep_G a)")
  apply simp
  apply (simp add: diff_minus add.assoc minus_add)
  apply (subst (asm) Rep_G_order)

  apply (simp add: F_def)
  apply (subst (asm) convex_def)
  apply simp
  apply (drule_tac x = 0 in spec)
  apply (drule_tac x = " u - Rep_G a" in spec)
  apply simp
  apply (subgoal_tac "u - Rep_G b \<in> |[ 0::'a , u - Rep_G a ]|")
  apply blast
  apply (subst closed_interval_def)
  apply simp
  apply safe
  apply (cut_tac x = "b" in Rep_G)
  apply (simp add: G_def)
  apply (safe)
  apply (simp add: diff_minus)
  apply (rule right_move_to_left)
  apply simp
  apply (simp add: diff_minus)
  apply (rule add_order_preserving_left)
  apply (rule minus_order)
  apply simp
  apply (simp add: lsubgroup_def)
  apply (rule normal_1) 
  apply simp_all
  apply (rule normal_2) 
  by simp_all
    
definition "N = {a::'a::lgroup. a \<le> 0}"
typedef (overloaded) ('a::lgroup) N = "N :: 'a::lgroup set"
proof
  show "0 \<in> N" by (simp add: N_def)
qed

class cancel_product_pseudo_hoop_algebra = cancel_pseudo_hoop_algebra + product_pseudo_hoop_algebra

context group_add
begin
subclass cancel_semigroup_add
proof qed
(*
  fix a b c :: 'a
  assume "a + b = a + c"
  then have "- a + a + b = - a + a + c"
    unfolding add.assoc by simp
  then show "b = c" by simp
next
  fix a b c :: 'a
  assume "b + a = c + a"
  then have "b + a + - a = c + a  + - a" by simp
  then show "b = c" unfolding add.assoc by simp
qed
*)
end
  

instantiation "N" :: (lgroup) pseudo_hoop_algebra
begin

definition
  times_N_def: "a * b \<equiv> Abs_N (Rep_N a +  Rep_N b)"

lemma [simp]: "Rep_N a + Rep_N b \<in> N"
  apply (cut_tac x = a in Rep_N)
  apply (cut_tac x = b in Rep_N)
  apply (simp add: N_def)
  apply (rule_tac left_move_to_right)
  apply (rule_tac y = 0 in order_trans)
  apply simp_all
  apply (rule_tac minus_order)
  by simp

definition
  impl_N_def: "a l\<rightarrow> b \<equiv> Abs_N (inf (Rep_N b - Rep_N a) 0)"

definition 
  inf_N_def: "(a:: 'a N) \<sqinter> b = (a l\<rightarrow> b) * a"

lemma [simp]: "inf (Rep_N b - Rep_N a) 0 \<in> N"
  apply (cut_tac x = a in Rep_N)
  apply (cut_tac x = b in Rep_N)
  by (simp add: N_def)

definition
  impr_N_def: "a r\<rightarrow> b \<equiv> Abs_N (inf (- Rep_N a + Rep_N b) 0)"

lemma [simp]: "inf (- Rep_N a + Rep_N b) 0 \<in> N"
  apply (cut_tac x = a in Rep_N)
  apply (cut_tac x = b in Rep_N)
  by (simp add: N_def)

definition
  one_N_def: "1 \<equiv> Abs_N 0"

lemma [simp]: "0 \<in> N"
  by (simp add: N_def)


definition
  order_N_def: "((a::'a N) \<le> b) \<equiv> (a l\<rightarrow> b = 1)"

definition
  strict_order_N_def: "(a::'a N) < b \<equiv> (a \<le> b \<and> \<not> b \<le> a)"

lemma order_Rep_N:
  "((a::'a N) \<le> b) = (Rep_N a \<le> Rep_N b)"
  apply (subst order_N_def)
  apply (simp add: impl_N_def one_N_def)
  apply (subgoal_tac "(Abs_N (inf (Rep_N b - Rep_N a) (0::'a)) = Abs_N (0::'a)) = ((Rep_N (Abs_N (inf (Rep_N b - Rep_N a) (0::'a))) = Rep_N(Abs_N (0::'a))))")
  apply simp
  apply (drule drop_assumption)
  apply (simp add: Abs_N_inverse)
  apply safe
  apply (subgoal_tac "0 \<le> Rep_N b - Rep_N a")
  apply (drule_tac v = "Rep_N a" in add_order_preserving_right)
  apply (simp add: diff_minus add.assoc)
  apply (rule_tac y = "inf (Rep_N b - Rep_N a) (0::'a)" in order_trans)
  apply simp
  apply (drule drop_assumption)
  apply simp
  apply (rule antisym)
  apply simp
  apply simp
  apply (simp add: diff_minus)
  apply (rule right_move_to_left)
  apply simp
  apply simp
  by (simp add: Abs_N_inverse)


lemma order_Abs_N:
  "a \<in> N \<Longrightarrow> b \<in> N \<Longrightarrow> (a \<le> b) = (Abs_N a \<le> Abs_N b)"
  apply (subst order_N_def)
  apply (simp add: impl_N_def one_N_def)
  apply (simp add: Abs_N_inverse)
  apply (subgoal_tac "inf (b - a) 0 \<in> N")
  apply (subgoal_tac "(Abs_N (inf (b - a) (0::'a)) = Abs_N (0::'a)) = (Rep_N (Abs_N (inf (b - a) (0::'a))) = Rep_N (Abs_N (0::'a)))")
  apply simp
  apply (simp add: Abs_N_inverse)
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  apply simp
  apply safe
  apply (rule antisym)
  apply simp_all
  apply (simp add: diff_minus)
  apply (rule right_move_to_left)
  apply simp
  apply (subgoal_tac "0 \<le> b - a")
  apply (drule_tac v = "a" in add_order_preserving_right)
  apply (simp add: diff_minus add.assoc)
  apply (rule_tac y = "inf (b - a) (0::'a)" in order_trans)
  apply simp
  apply (drule drop_assumption)
  apply simp
  apply (simp add: Abs_N_inverse)
  by (simp add: N_def)

lemma [simp]: "(1::'a N) * a = a"
  by (simp add: one_N_def times_N_def Abs_N_inverse Rep_N_inverse)

lemma [simp]: "a * (1::'a N) = a"
  by (simp add: one_N_def times_N_def Abs_N_inverse Rep_N_inverse)
 
lemma [simp]: "a l\<rightarrow> a = (1::'a N)"
  by (simp add: impl_N_def one_N_def Abs_N_inverse Rep_N_inverse)
 
lemma [simp]: "a r\<rightarrow> a = (1::'a N)"
  by (simp add: impr_N_def one_N_def Abs_N_inverse Rep_N_inverse)

lemma impl_times: "(a l\<rightarrow> b) * a = (b l\<rightarrow> a) * (b::'a N)"
  apply (simp add: impl_N_def impr_N_def times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "inf (Rep_N b - Rep_N a + Rep_N a) (Rep_N a) = inf (Rep_N a - Rep_N b + Rep_N b) (Rep_N b)")
  apply simp
  apply (subgoal_tac "Rep_N b - Rep_N a + Rep_N a = Rep_N b ")
  apply simp
  apply (subgoal_tac "Rep_N a - Rep_N b + Rep_N b = Rep_N a")
  apply simp
  apply (rule antisym)
  by simp_all
 
lemma impr_times: "a * (a r\<rightarrow> b) = (b::'a N) * (b r\<rightarrow> a)"
  apply (simp add: impr_N_def times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "inf (Rep_N a + (- Rep_N a + Rep_N b)) (Rep_N a) = inf (Rep_N b + (- Rep_N b + Rep_N a)) (Rep_N b)")
  apply simp
  apply (simp add: add.assoc [THEN sym])
  apply (rule antisym)
  by simp_all

lemma impr_impl_times: "(a l\<rightarrow> b) * a = (a::'a N) * (a r\<rightarrow> b)"
  by (simp add: impl_N_def impr_N_def times_N_def Abs_N_inverse Rep_N_inverse) 

lemma impl_ded: "(a::'a N) * b l\<rightarrow> c = a l\<rightarrow> b l\<rightarrow> c"
  apply (simp add: impl_N_def impr_N_def times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "inf (Rep_N c - (Rep_N a + Rep_N b)) (0::'a) = inf (inf (Rep_N c - Rep_N b - Rep_N a) (- Rep_N a)) (0::'a)")
  apply simp
  apply (rule antisym)
  apply simp_all
  apply safe
  apply (rule_tac y = "Rep_N c - (Rep_N a + Rep_N b)" in order_trans)
  apply simp
  apply (simp add: diff_minus minus_add add.assoc)
  apply (rule_tac y = "0" in order_trans)
  apply simp
  apply (cut_tac x = a in "Rep_N")
  apply (simp add: N_def)
  apply (drule_tac u = 0 and v = "- Rep_N a" in add_order_preserving)
  apply simp
  apply (rule_tac y = "inf (Rep_N c - Rep_N b - Rep_N a) (- Rep_N a)" in order_trans)
  apply (rule inf_le1)
  apply (rule_tac y = "Rep_N c - Rep_N b - Rep_N a" in order_trans)
  apply simp
  by (simp add: diff_minus minus_add add.assoc)

lemma impr_ded: "(a::'a N) * b r\<rightarrow> c = b r\<rightarrow> a r\<rightarrow> c"
  apply (simp add: impr_N_def impr_N_def times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "inf (- (Rep_N a + Rep_N b) + Rep_N c) (0::'a) = inf (inf (- Rep_N b + (- Rep_N a + Rep_N c)) (- Rep_N b)) (0::'a)")
  apply simp
  apply (rule antisym)
  apply simp_all
  apply safe
  apply (rule_tac y = "- (Rep_N a + Rep_N b) + Rep_N c" in order_trans)
  apply simp
  apply (simp add: diff_minus minus_add add.assoc)
  apply (rule_tac y = "0" in order_trans)
  apply simp
  apply (cut_tac x = b in "Rep_N")
  apply (simp add: N_def)
  apply (drule_tac u = 0 and v = "- Rep_N b" in add_order_preserving)
  apply simp
  apply (rule_tac y = "inf (- Rep_N b + (- Rep_N a + Rep_N c)) (- Rep_N b)" in order_trans)
  apply (rule inf_le1)
  apply (rule_tac y = "- Rep_N b + (- Rep_N a + Rep_N c)" in order_trans)
  apply simp
  by (simp add: diff_minus minus_add add.assoc)


instance proof
  fix a show "(1::'a N) * a = a" by simp
  fix a show "a * (1::'a N) = a" by simp
  fix a show "a l\<rightarrow> a = (1::'a N)" by simp
  fix a show "a r\<rightarrow> a = (1::'a N)" by simp
next
  fix a b::"'a N" show "(a l\<rightarrow> b) * a = (b l\<rightarrow> a) * b" by (simp add: impl_times)
next
  fix a b::"'a N" show "a * (a r\<rightarrow> b) = b * (b r\<rightarrow> a)" by (simp add: impr_times)
next
  fix a b::"'a N" show "(a l\<rightarrow> b) * a = a * (a r\<rightarrow> b)" by (simp add: impr_impl_times)
next
  fix a b c::"'a N" show "a * b l\<rightarrow> c = a l\<rightarrow> b l\<rightarrow> c" by (simp add: impl_ded)
  fix a b c::"'a N" show "a * b r\<rightarrow> c = b r\<rightarrow> a r\<rightarrow> c" by (simp add: impr_ded)
next
  fix a b::"'a N" show "(a \<le> b) = (a l\<rightarrow> b = 1)" by (simp add: order_N_def)
next
  fix a b::"'a N" show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)" by (simp add: strict_order_N_def)
next
  fix a b::"'a N" show "a \<sqinter> b = (a l\<rightarrow> b) * a" by (simp add: inf_N_def)
next
  fix a b::"'a N" show "a \<sqinter> b = a * (a r\<rightarrow> b)" by (simp add: inf_N_def impr_impl_times)
qed

end

lemma Rep_N_inf: "Rep_N ((a::'a::lgroup N) \<sqinter> b) = (Rep_N a) \<sqinter> (Rep_N b)"
  apply (rule antisym)
  apply simp_all
  apply safe
  apply (simp add: order_Rep_N [THEN sym])
  apply (simp add: order_Rep_N [THEN sym])
  apply (subgoal_tac "inf (Rep_N a) (Rep_N b) \<in> N")
  apply (subst order_Abs_N)
  apply simp_all
  apply (cut_tac x = "a \<sqinter> b" in Rep_N)
  apply (simp add: N_def)
  apply (simp add: Rep_N_inverse)
  apply safe
  apply (subst order_Rep_N)
  apply (simp add: Abs_N_inverse)
  apply (subst order_Rep_N)
  apply (simp add: Abs_N_inverse)
  apply (simp add: N_def)
  apply (rule_tac y = "Rep_N a" in order_trans)
  apply simp
  apply (cut_tac x = a in Rep_N) 
  by (simp add: N_def)

context lgroup begin

lemma sup_inf_distrib2_lgroup: "(b \<sqinter> c) \<squnion> a = (b \<squnion> a) \<sqinter> (c \<squnion> a)"
  by (rule sup_inf_distrib2)

lemma inf_sup_distrib2_lgroup: "(b \<squnion> c) \<sqinter> a = (b \<sqinter> a) \<squnion> (c \<sqinter> a)"
  by (rule inf_sup_distrib2)
end

instantiation "N" :: (lgroup) cancel_product_pseudo_hoop_algebra
begin

lemma cancel_times_left: "(a::'a N) * b = a * c \<Longrightarrow> b = c"
  apply (simp add: times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "Rep_N (Abs_N (Rep_N a + Rep_N b)) = Rep_N (Abs_N (Rep_N a + Rep_N c))")
  apply (drule drop_assumption)
  apply (simp add: Abs_N_inverse)
  apply (subgoal_tac "Abs_N (Rep_N b) = Abs_N (Rep_N c)")
  apply (drule drop_assumption)
  apply (simp add: Rep_N_inverse)
  by simp_all

lemma cancel_times_right: "b * (a::'a N) = c * a \<Longrightarrow> b = c"
  apply (simp add: times_N_def Abs_N_inverse Rep_N_inverse) 
  apply (subgoal_tac "Rep_N (Abs_N (Rep_N b + Rep_N a)) = Rep_N (Abs_N (Rep_N c + Rep_N a))")
  apply (drule drop_assumption)
  apply (simp add: Abs_N_inverse)
  apply (subgoal_tac "Abs_N (Rep_N b) = Abs_N (Rep_N c)")
  apply (drule drop_assumption)
  apply (simp add: Rep_N_inverse)
  by simp_all

lemma prod_1: "((a::'a N) l\<rightarrow> b) l\<rightarrow> c \<le> ((b l\<rightarrow> a) l\<rightarrow> c) l\<rightarrow> c"
  apply (unfold impl_N_def times_N_def Abs_N_inverse Rep_N_inverse order_N_def one_N_def)
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subgoal_tac "inf (inf (Rep_N c - inf (Rep_N c - inf (Rep_N a - Rep_N b) 0) 0) 0 - inf (Rep_N c - inf (Rep_N b - Rep_N a) 0) 0) 0 = 0")
  apply simp
  apply (rule antisym)
  apply simp
  apply (rule inf_greatest)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (rule right_move_to_left)
  apply simp_all
  apply (simp add: diff_minus minus_add)
  (*apply (subst sup_inf_distrib2) - why it does not work*)
  apply (subst sup_inf_distrib2_lgroup)
  apply simp
  (*apply safe*)
  (*apply (subst inf_sup_distrib2) - why it does not work*)
  apply (subst inf_sup_distrib2_lgroup)
  apply simp
  (*apply safe*)
  apply (rule_tac y="Rep_N c + (Rep_N a + - Rep_N b + - Rep_N c)" in order_trans)
  apply simp_all
  apply (rule_tac y="Rep_N c + (Rep_N a + - Rep_N b)" in order_trans)
  apply simp_all
  apply (rule add_order_preserving_left)
  apply (simp add: add.assoc)
  apply (rule add_order_preserving_left)
  apply (rule left_move_to_left)
  apply simp
  apply (cut_tac x = c in Rep_N)
  apply (simp add: N_def)
  apply (rule minus_order)
  by simp


lemma prod_2: "((a::'a N) r\<rightarrow> b) r\<rightarrow> c \<le> ((b r\<rightarrow> a) r\<rightarrow> c) r\<rightarrow> c"
  apply (unfold impr_N_def times_N_def Abs_N_inverse Rep_N_inverse right_lesseq one_N_def)
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subst Abs_N_inverse)
  apply simp
  apply (subgoal_tac "inf (- inf (- inf (- Rep_N a + Rep_N b) (0::'a) + Rep_N c) (0::'a) + inf (- inf (- inf (- Rep_N b + Rep_N a) (0::'a) + Rep_N c) (0::'a) + Rep_N c) (0::'a))
            (0::'a) = 0")
  apply simp
  apply (rule antisym)
  apply simp
  apply (rule inf_greatest)
  apply (rule minus_order)
  apply (subst minus_add)
  apply (subst minus_minus)
  apply (subst minus_zero)
  apply (rule left_move_to_right)
  apply (subst minus_minus)
  apply simp
  apply (simp add: minus_add)
  apply simp_all
  (*apply (subst sup_inf_distrib2) - why it does not work*)
  apply (subst sup_inf_distrib2_lgroup)
  apply simp
(*  apply safe*)
  (*apply (subst inf_sup_distrib2) - why it does not work*)
  apply (subst inf_sup_distrib2_lgroup)
  apply simp
(*  apply safe*)
  apply (rule_tac y = "- Rep_N c + (- Rep_N b + Rep_N a) + Rep_N c" in order_trans)
  apply simp_all
  apply (rule_tac y = "- Rep_N b + Rep_N a + Rep_N c" in order_trans)
  apply simp_all
  apply (rule add_order_preserving_right)
  apply (simp add: add.assoc [THEN sym])
  apply (rule add_order_preserving_right)
  apply (rule left_move_to_left)
  apply (rule right_move_to_right)
  apply simp
  apply (cut_tac x = c in Rep_N)
  by (simp add: N_def)
  

lemma prod_3: "(b::'a N) l\<rightarrow> b * b \<le> a \<sqinter> (a l\<rightarrow> b) l\<rightarrow> b"
  apply (simp add: impl_N_def times_N_def Abs_N_inverse Rep_N_inverse order_N_def one_N_def Rep_N_inf)
  apply (subst Abs_N_inverse)
  apply (simp add: add.assoc N_def)
  apply (subst Abs_N_inverse)
  apply (simp add: add.assoc N_def)
  apply (subgoal_tac "inf (inf (sup (Rep_N b - Rep_N a) (sup (Rep_N b - (Rep_N b - Rep_N a)) (Rep_N b))) (0::'a) - inf (Rep_N b + Rep_N b - Rep_N b) (0::'a)) (0::'a) = 0")
  apply simp
  apply (rule antisym)
  apply simp
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (subst diff_minus)
  apply (rule inf_greatest)
  apply (rule right_move_to_left)
  apply (subst minus_minus)
  apply simp_all
  apply (simp add: add.assoc)
  apply (rule_tac y = "Rep_N b" in order_trans)
  by simp_all

lemma prod_4: "(b::'a N) r\<rightarrow> b * b \<le> a \<sqinter> (a r\<rightarrow> b) r\<rightarrow> b"
  apply (simp add: impr_N_def times_N_def Abs_N_inverse Rep_N_inverse Rep_N_inf minus_add)
  apply (subst order_Abs_N [THEN sym])
  apply (simp add:  N_def)
  apply (simp add:  N_def)
  apply simp
  apply (rule_tac y = "- Rep_N a + Rep_N b" in order_trans)
  apply simp_all
  apply (rule_tac y = "Rep_N b" in order_trans)
  apply simp
  apply (rule right_move_to_left)
  apply simp
  apply (rule minus_order)
  apply simp
  apply (cut_tac x = a in Rep_N)
  by (simp add: N_def)

lemma prod_5: "(((a::'a N) l\<rightarrow> b) l\<rightarrow> b) * (c * a l\<rightarrow> f * a) * (c * b l\<rightarrow> f * b) \<le> c l\<rightarrow> f"
  apply (simp add: impl_N_def times_N_def Abs_N_inverse Rep_N_inverse Rep_N_inf minus_add)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst order_Abs_N [THEN sym])
  apply (simp add: N_def inf_assoc [THEN sym])
  apply (simp add: N_def)
  apply (simp only: diff_minus minus_add minus_minus add.assoc)
  apply (subst (4) add.assoc [THEN sym])
  apply (subst (5) add.assoc [THEN sym])
  apply (simp only: right_minus add_0_left)
  apply (rule right_move_to_right)
  apply (simp only: minus_add add.assoc [THEN sym] add_0_left right_minus)
  by (simp add: minus_add)


lemma prod_6: "(((a::'a N) r\<rightarrow> b) r\<rightarrow> b) * (a * c r\<rightarrow> a * f) * (b * c r\<rightarrow> b * f) \<le> c r\<rightarrow> f"
  apply (simp add: impr_N_def times_N_def Abs_N_inverse Rep_N_inverse Rep_N_inf minus_add)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst Abs_N_inverse)
  apply (simp add: N_def)
  apply (subst order_Abs_N [THEN sym])
  apply (simp add: N_def inf_assoc [THEN sym])
  apply (simp add: N_def)
  apply (simp only: diff_minus minus_add minus_minus add.assoc)
  apply (subst (4) add.assoc [THEN sym])
  apply (subst (5) add.assoc [THEN sym])
  apply (simp only: left_minus add_0_left)
  apply (rule right_move_to_right)
  apply (simp only: minus_add add.assoc [THEN sym] add_0_left right_minus)
  by (simp add: minus_add)

instance
apply intro_classes
by (fact cancel_times_left cancel_times_right prod_1 prod_2 prod_3 prod_4 prod_5 prod_6)+

end

definition "OrdSum =
  {x. (\<exists>a::'a::pseudo_hoop_algebra. x = (a, 1::'b::pseudo_hoop_algebra)) \<or> (\<exists>b::'b. x = (1::'a, b))}"
typedef (overloaded) ('a, 'b) OrdSum = "OrdSum :: ('a::pseudo_hoop_algebra \<times> 'b::pseudo_hoop_algebra) set"
proof
  show "(1, 1) \<in> OrdSum" by (simp add: OrdSum_def)
qed

lemma [simp]: "(1, b) \<in> OrdSum"
  by (simp add: OrdSum_def)

lemma [simp]: "(a, 1) \<in> OrdSum"
  by (simp add: OrdSum_def)


definition
  "first x = fst (Rep_OrdSum x)"

definition
  "second x = snd (Rep_OrdSum x)" 

lemma if_unfold_left: "((if a then b else c) = d) = ((a\<longrightarrow> b = d) \<and> (\<not> a \<longrightarrow> c = d))"
  apply auto
  done

lemma if_unfold_right: "(d = (if a then b else c)) = ((a \<longrightarrow> d = b) \<and> (\<not> a \<longrightarrow> d = c))"
  apply auto
  done

lemma fst_snd_eq: "fst a = x \<Longrightarrow> snd a = y \<Longrightarrow> (x, y) = a"
  apply (subgoal_tac "x = fst a")
  apply (subgoal_tac "y = snd a")
  apply (drule drop_assumption)
  apply (drule drop_assumption)
  by simp_all

instantiation "OrdSum" :: (pseudo_hoop_algebra, pseudo_hoop_algebra) pseudo_hoop_algebra
begin

definition
  times_OrdSum_def: "a * b \<equiv> (
    if second a = 1 \<and> second b = 1 then 
      Abs_OrdSum (first a * first b, 1) 
    else if first a = 1 \<and> first b = 1 then
      Abs_OrdSum (1, second a * second b)
    else if first a = 1 \<and> second b = 1 then
      b
    else
      a)"

definition
  one_OrdSum_def: "1 \<equiv> Abs_OrdSum (1, 1)"

definition
  impl_OrdSum_def: "a l\<rightarrow> b \<equiv> 
    (if second a = 1 \<and> second b = 1 then 
      Abs_OrdSum (first a l\<rightarrow> first b, 1) 
    else if first a = 1 \<and> first b = 1 then
      Abs_OrdSum (1, second a l\<rightarrow> second b)
    else if first a = 1 \<and> second b = 1 then
      b
    else
      1)"

definition
  impr_OrdSum_def: "a r\<rightarrow> b \<equiv> 
    (if second a = 1 \<and> second b = 1 then 
      Abs_OrdSum (first a r\<rightarrow> first b, 1) 
    else if first a = 1 \<and> first b = 1 then
      Abs_OrdSum (1, second a r\<rightarrow> second b)
    else if first a = 1 \<and> second b = 1 then
      b
    else
      1)"

definition
  order_OrdSum_def: "((a::('a, 'b) OrdSum) \<le> b) \<equiv> (a l\<rightarrow> b = 1)"

definition 
  inf_OrdSum_def: "(a::('a, 'b) OrdSum) \<sqinter> b = (a l\<rightarrow> b) * a"

definition
  strict_order_OrdSum_def: "(a::('a, 'b) OrdSum) < b \<equiv> (a \<le> b \<and> \<not> b \<le> a)"

lemma OrdSum_first [simp]: "(a, 1) \<in> OrdSum"
  by (simp add: OrdSum_def)

lemma OrdSum_second [simp]: "(1, b) \<in> OrdSum"
  by (simp add: OrdSum_def)

lemma Rep_OrdSum_eq: "Rep_OrdSum x = Rep_OrdSum y \<Longrightarrow> x = y"
  apply (subgoal_tac "Abs_OrdSum (Rep_OrdSum x) = Abs_OrdSum (Rep_OrdSum y)")
  apply (drule drop_assumption)
  apply (simp add: Rep_OrdSum_inverse)
  by simp

lemma Abs_OrdSum_eq: "x \<in> OrdSum \<Longrightarrow> y \<in> OrdSum \<Longrightarrow> Abs_OrdSum x = Abs_OrdSum y \<Longrightarrow> x = y"
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum x) = Rep_OrdSum (Abs_OrdSum y)")
  apply (unfold Abs_OrdSum_inverse) [1]
  by simp_all

lemma [simp]: "fst (Rep_OrdSum a) \<noteq> 1 \<Longrightarrow> (snd (Rep_OrdSum a) \<noteq> 1 = False)"
  apply (cut_tac x = a in Rep_OrdSum)
  apply (simp add: OrdSum_def)
  by auto

lemma fst_not_one_snd: "fst (Rep_OrdSum a) \<noteq> 1 \<Longrightarrow> (snd (Rep_OrdSum a) = 1)"
  apply (cut_tac x = a in Rep_OrdSum)
  apply (simp add: OrdSum_def)
  by auto

lemma snd_not_one_fst: "snd (Rep_OrdSum a) \<noteq> 1 \<Longrightarrow> (fst (Rep_OrdSum a) = 1)"
  apply (cut_tac x = a in Rep_OrdSum)
  apply (simp add: OrdSum_def)
  by auto


lemma fst_not_one_simp [simp]: "fst (Rep_OrdSum c) \<noteq> 1 \<Longrightarrow> Abs_OrdSum (fst (Rep_OrdSum c), 1) = c"
  apply (rule  Rep_OrdSum_eq)
  apply (simp add: Abs_OrdSum_inverse)
  apply (rule fst_snd_eq)
  apply simp_all
  by (simp add: fst_not_one_snd)

lemma snd_not_one_simp [simp]: "snd (Rep_OrdSum c) \<noteq> 1 \<Longrightarrow> Abs_OrdSum (1, snd (Rep_OrdSum c)) = c"
  apply (rule  Rep_OrdSum_eq)
  apply (simp add: Abs_OrdSum_inverse)
  apply (rule fst_snd_eq)
  apply simp_all
  by (simp add: snd_not_one_fst)

lemma  A: fixes a b::"('a, 'b) OrdSum" shows "(a l\<rightarrow> b) * a = a * (a r\<rightarrow> b)"
  apply (simp add: one_OrdSum_def impr_OrdSum_def impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply safe
  apply (simp_all add: fst_snd_eq times_OrdSum_def left_right_impl_times first_def second_def Abs_OrdSum_inverse Rep_OrdSum_inverse )
  apply safe
  by simp_all

instance
proof
fix a::"('a, 'b) OrdSum" show "1 * a = a" 
  by (simp add: fst_snd_eq one_OrdSum_def times_OrdSum_def first_def second_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
next
fix a::"('a, 'b) OrdSum" show "a * 1 = a" 
  by (simp add: fst_snd_eq one_OrdSum_def times_OrdSum_def first_def second_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
next
fix a::"('a, 'b) OrdSum" show "a l\<rightarrow> a = 1" 
  by (simp add: one_OrdSum_def impl_OrdSum_def)
next
fix a::"('a, 'b) OrdSum" show "a r\<rightarrow> a = 1" 
  by (simp add: one_OrdSum_def impr_OrdSum_def)
next
fix a b::"('a, 'b) OrdSum" show "(a l\<rightarrow> b) * a = (b l\<rightarrow> a) * b" 
  apply (unfold one_OrdSum_def impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply simp
  apply safe
  by (simp_all add: times_OrdSum_def left_impl_times first_def second_def Abs_OrdSum_inverse Rep_OrdSum_inverse )
next
fix a b::"('a, 'b) OrdSum" show "a * (a r\<rightarrow> b) = b * (b r\<rightarrow> a)" 
  apply (unfold one_OrdSum_def impr_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp)
  apply safe
  by (simp_all add: fst_snd_eq times_OrdSum_def right_impl_times first_def second_def Abs_OrdSum_inverse Rep_OrdSum_inverse )
next
fix a b::"('a, 'b) OrdSum" show "(a l\<rightarrow> b) * a = a * (a r\<rightarrow> b)" by (rule A)
next
fix a b c::"('a, 'b) OrdSum" show "a * b l\<rightarrow> c = a l\<rightarrow> b l\<rightarrow> c" 
  apply (unfold times_OrdSum_def)
  apply simp apply safe
  apply (simp_all add: impl_OrdSum_def)
  apply (simp_all add: first_def second_def)
  apply (simp_all add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp_all add: fst_snd_eq)
  apply (simp_all add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp_all add: left_impl_ded)
  apply (simp_all add: fst_snd_eq one_OrdSum_def times_OrdSum_def left_impl_ded impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  by auto
next
fix a b c::"('a, 'b) OrdSum" show "a * b r\<rightarrow> c = b r\<rightarrow> a r\<rightarrow> c"
  apply (simp add: right_impl_ded impr_OrdSum_def second_def first_def one_OrdSum_def  times_OrdSum_def  second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  by auto
next
  fix a b::"('a, 'b) OrdSum" show "(a \<le> b) = (a l\<rightarrow> b = 1)"
    by (simp add:  order_OrdSum_def)
next
  fix a b::"('a, 'b) OrdSum" show "(a < b) = (a \<le> b \<and> \<not> b \<le> a)"
    by (simp add:  strict_order_OrdSum_def)
next
  fix a b::"('a, 'b) OrdSum" show "a \<sqinter> b = (a l\<rightarrow> b) * a" by (simp add: inf_OrdSum_def)
next
  fix a b::"('a, 'b) OrdSum" show "a \<sqinter> b = a * (a r\<rightarrow> b)" by (simp add: inf_OrdSum_def A)
  
qed

definition
   "Second = {x . \<exists> b . x =  Abs_OrdSum(1::'a, b::'b)}"

end

lemma "Second \<in> normalfilters"
  apply (unfold normalfilters_def)
  apply safe
  apply (unfold filters_def)
  apply safe
  apply (unfold Second_def)
  apply auto
  apply (rule_tac x = "ba * bb" in exI)
  apply (simp add: times_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (rule_tac x = "second b" in exI)
  apply (subgoal_tac "Abs_OrdSum (1::'a, second b) = Abs_OrdSum (first b, second b)")
  apply simp
  apply (simp add: first_def second_def Rep_OrdSum_inverse)
  apply (subgoal_tac "first b = 1")
  apply simp
  apply (simp add: order_OrdSum_def one_OrdSum_def impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (unfold second_def first_def)
  apply (case_tac "ba = (1::'b) \<and> snd (Rep_OrdSum b) = (1::'b)")
  apply simp
  apply (simp add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum (fst (Rep_OrdSum b), 1::'b)) = Rep_OrdSum (Abs_OrdSum (1::'a, 1::'b))")
  apply (drule drop_assumption)
  apply (simp add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply simp
  apply simp
  apply (simp add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (case_tac "fst (Rep_OrdSum b) = (1::'a)")
  apply simp
  apply simp
  apply (simp add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (case_tac "snd (Rep_OrdSum b) = (1::'b)")
  apply simp_all
  apply (simp add: Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp add: impr_OrdSum_def impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply safe
  apply (unfold second_def first_def)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (case_tac "snd (Rep_OrdSum a) = (1::'b)")
  apply simp_all
  apply auto
  apply (case_tac "snd (Rep_OrdSum a) = (1::'b)")
  apply auto
  apply (rule_tac x = 1 in exI) 
  apply (rule Rep_OrdSum_eq)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum (fst (Rep_OrdSum a) l\<rightarrow> fst (Rep_OrdSum b), 1::'b)) = Rep_OrdSum (Abs_OrdSum (1::'a, ba))")
  apply (drule drop_assumption)
  apply (simp add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp add: left_lesseq [THEN sym] right_lesseq [THEN sym])
  apply simp
  apply (rule_tac x = 1 in exI) 
  apply (rule Rep_OrdSum_eq)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum (fst (Rep_OrdSum a) l\<rightarrow> fst (Rep_OrdSum b), 1::'b)) = Rep_OrdSum (Abs_OrdSum (1::'a, ba))")
  apply (drule drop_assumption)
  apply (simp add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp add: left_lesseq [THEN sym] right_lesseq [THEN sym])
  apply simp

  apply (simp add: impr_OrdSum_def impl_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply safe
  apply (unfold second_def first_def)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (case_tac "snd (Rep_OrdSum a) = (1::'b)")
  apply simp_all
  apply auto
  apply (case_tac "snd (Rep_OrdSum a) = (1::'b)")
  apply auto
  apply (rule_tac x = 1 in exI) 
  apply (rule Rep_OrdSum_eq)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum (fst (Rep_OrdSum a) r\<rightarrow> fst (Rep_OrdSum b), 1::'b)) = Rep_OrdSum (Abs_OrdSum (1::'a, ba))")
  apply (drule drop_assumption)
  apply (simp add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp add: left_lesseq [THEN sym] right_lesseq [THEN sym])
  apply simp
  apply (rule_tac x = 1 in exI) 
  apply (rule Rep_OrdSum_eq)
  apply (simp_all add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (subgoal_tac "Rep_OrdSum (Abs_OrdSum (fst (Rep_OrdSum a) r\<rightarrow> fst (Rep_OrdSum b), 1::'b)) = Rep_OrdSum (Abs_OrdSum (1::'a, ba))")
  apply (drule drop_assumption)
  apply (simp add: second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
  apply (simp add: left_lesseq [THEN sym] right_lesseq [THEN sym])
  by simp


class linear_pseudo_hoop_algebra = pseudo_hoop_algebra + linorder

instantiation "OrdSum" :: (linear_pseudo_hoop_algebra, linear_pseudo_hoop_algebra) linear_pseudo_hoop_algebra
begin
instance
proof
  fix x y::"('a, 'b) OrdSum" show "x \<le> y \<or> y \<le> x"
    apply (simp add: order_OrdSum_def impl_OrdSum_def one_OrdSum_def second_def first_def Abs_OrdSum_inverse Rep_OrdSum_inverse)
    apply (cut_tac x = "fst (Rep_OrdSum x)" and y = "fst (Rep_OrdSum y)" in linear)
    apply (cut_tac x = "snd (Rep_OrdSum x)" and y = "snd (Rep_OrdSum y)" in linear)
    apply (simp add: left_lesseq)
    by auto [1]
qed
end

instantiation bool:: pseudo_hoop_algebra
begin
definition impl_bool_def:
  "a l\<rightarrow> b = (a \<longrightarrow> b)"

definition impr_bool_def:
  "a r\<rightarrow> b = (a \<longrightarrow> b)"

definition one_bool_def:
  "1 = True"

definition times_bool_def:
  "a * b = (a \<and> b)"

lemma inf_bool_def: "(a :: bool) \<sqinter> b = (a l\<rightarrow> b) * a"
  by (auto simp add: times_bool_def impl_bool_def)
  

instance
  apply intro_classes
  apply (simp_all add: impl_bool_def impr_bool_def one_bool_def times_bool_def le_bool_def less_bool_def inf_bool_def)
  by auto

end

context cancel_pseudo_hoop_algebra begin end

lemma "\<not> class.cancel_pseudo_hoop_algebra (*) (\<sqinter>)  (l\<rightarrow>) (\<le>) (<) (1:: bool) (r\<rightarrow>) "
  apply (unfold  class.cancel_pseudo_hoop_algebra_def)
  apply (unfold  class.cancel_pseudo_hoop_algebra_axioms_def)
  apply safe
  apply (drule drop_assumption)
  apply (drule_tac x = "False" in spec)
  apply (drule drop_assumption)
  apply (drule_tac x = "True" in spec)
  apply (drule_tac x = "False" in spec)
  by (simp add: times_bool_def)

context pseudo_hoop_algebra begin
lemma classorder: "class.order (\<le>) (<)"
  proof qed
end

lemma impl_OrdSum_first: "Abs_OrdSum (x, 1) l\<rightarrow> Abs_OrdSum (y, 1) = Abs_OrdSum (x l\<rightarrow> y, 1)"
  by (simp add: impl_OrdSum_def first_def second_def  Abs_OrdSum_inverse Rep_OrdSum_inverse)

lemma impl_OrdSum_second: "Abs_OrdSum (1, x) l\<rightarrow> Abs_OrdSum (1, y) = Abs_OrdSum (1, x l\<rightarrow> y)"
  by (simp add: impl_OrdSum_def first_def second_def  Abs_OrdSum_inverse Rep_OrdSum_inverse)

lemma impl_OrdSum_first_second: "x \<noteq> 1 \<Longrightarrow> Abs_OrdSum (x, 1) l\<rightarrow> Abs_OrdSum (1, y) = 1"
  by (simp add: one_OrdSum_def impl_OrdSum_def first_def second_def  Abs_OrdSum_inverse Rep_OrdSum_inverse)

lemma Abs_OrdSum_bijective: "x \<in> OrdSum \<Longrightarrow> y \<in> OrdSum \<Longrightarrow> (Abs_OrdSum x = Abs_OrdSum y) = (x = y)"
  apply safe
  apply (subgoal_tac  "Rep_OrdSum (Abs_OrdSum x) = Rep_OrdSum (Abs_OrdSum y)")
  apply (unfold Abs_OrdSum_inverse) [1]
  by simp_all

context pseudo_hoop_algebra begin end

context linear_pseudo_hoop_algebra begin end
context basic_pseudo_hoop_algebra begin end

lemma "class.pseudo_hoop_algebra (*) (\<sqinter>) (l\<rightarrow>) (\<le>) (<) (1::'a::pseudo_hoop_algebra) (r\<rightarrow>)
          \<Longrightarrow> \<not> (class.linear_pseudo_hoop_algebra (\<le>) (<)  (*) (\<sqinter>) (l\<rightarrow>) (1::'a) (r\<rightarrow>))
          \<Longrightarrow> \<not> class.basic_pseudo_hoop_algebra (*) (\<sqinter>) (l\<rightarrow>) (\<le>) (<) (1::('a, bool) OrdSum) (r\<rightarrow>)" 
  apply (unfold class.linear_pseudo_hoop_algebra_def)
  apply (unfold class.linorder_def)
  apply (unfold class.linorder_axioms_def)
  apply safe
  apply (rule classorder)
  apply (unfold class.basic_pseudo_hoop_algebra_def) [1]
  apply simp
  apply (unfold class.basic_pseudo_hoop_algebra_axioms_def) [1]
  apply safe
  apply (subgoal_tac "(Abs_OrdSum (x, 1) l\<rightarrow> Abs_OrdSum (y, 1)) l\<rightarrow> Abs_OrdSum (1, False) \<le> 
         ((Abs_OrdSum (y, 1) l\<rightarrow> Abs_OrdSum (x, 1)) l\<rightarrow> Abs_OrdSum (1, False)) l\<rightarrow> Abs_OrdSum (1, False)")
  apply (unfold impl_OrdSum_first) [1]
  apply (case_tac "x l\<rightarrow> y \<noteq> 1 \<and> y l\<rightarrow> x \<noteq> 1")
  apply (simp add: impl_OrdSum_first_second)
  apply (unfold order_OrdSum_def one_OrdSum_def one_bool_def impl_OrdSum_second impl_bool_def ) [1]
  apply simp
  apply (cut_tac x = "(1::'a, False)" and y = "(1::'a, True)" in  Abs_OrdSum_eq)
  apply simp_all
  apply (unfold left_lesseq)
  by simp

end
