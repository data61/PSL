section\<open>Modular and Distributive Lattices\<close>

(*
    Author: Viorel Preoteasa
*)

theory Modular_Distrib_Lattice
imports Lattice_Prop
begin

text \<open>
The main result of this theory is the fact that a lattice is distributive
if and only if it satisfies the following property:
\<close>

term "(\<forall> x y z . x \<sqinter> z = y \<sqinter> z \<and> x \<squnion> z = y \<squnion> z \<Longrightarrow> x = y)"

text\<open>
This result was proved by Bergmann in \cite{bergmann:1929}. The formalization
presented here is based on \cite{birkhoff:1967,burris:sankappanavar:1981}.
\<close>

class modular_lattice = lattice +
  assumes modular: "x \<le> y \<Longrightarrow>  x \<squnion> (y \<sqinter> z) = y \<sqinter> (x \<squnion> z)"

context distrib_lattice begin
subclass modular_lattice
  apply unfold_locales
  by (simp add: inf_sup_distrib inf_absorb2)
end

context lattice begin
definition
  "d_aux a b c = (a \<sqinter> b) \<squnion> (b \<sqinter> c) \<squnion> (c \<sqinter> a)"

lemma d_b_c_a: "d_aux b c a = d_aux a b c"
  by (metis d_aux_def sup.assoc sup_commute)

lemma d_c_a_b: "d_aux c a b = d_aux a b c"
  by (metis d_aux_def sup.assoc sup_commute)

definition
  "e_aux a b c = (a \<squnion> b) \<sqinter> (b \<squnion> c) \<sqinter> (c \<squnion> a)"

lemma e_b_c_a: "e_aux b c a = e_aux a b c"
  apply (simp add: e_aux_def)
  apply (rule antisym)
  by (simp_all add: sup_commute)

lemma e_c_a_b: "e_aux c a b = e_aux a b c"
  apply (simp add: e_aux_def)
  apply (rule antisym)
  by (simp_all add: sup_commute)

definition
  "a_aux a b c = (a \<sqinter> (e_aux a b c)) \<squnion> (d_aux a b c)"

definition
  "b_aux a b c = (b \<sqinter> (e_aux a b c)) \<squnion> (d_aux a b c)"

definition
  "c_aux a b c = (c \<sqinter> (e_aux a b c)) \<squnion> (d_aux a b c)"

lemma b_a: "b_aux a b c = a_aux b c a" 
  by (simp add: a_aux_def b_aux_def e_b_c_a d_b_c_a)

lemma c_a: "c_aux a b c = a_aux c a b" 
  by (simp add: a_aux_def c_aux_def e_c_a_b d_c_a_b)

lemma [simp]: "a_aux a b c \<le> e_aux a b c"
  apply (simp add: a_aux_def e_aux_def d_aux_def)
  apply (rule_tac y = "(a \<squnion> b) \<sqinter> (b \<squnion> c) \<sqinter> (c \<squnion> a)" in order_trans)
  apply (rule inf_le2)
  by simp

lemma [simp]: "b_aux a b c \<le> e_aux a b c"
  apply (unfold b_a)
  apply (subst e_b_c_a [THEN sym])
  by simp

lemma [simp]: "c_aux a b c \<le> e_aux a b c"
  apply (unfold c_a)
  apply (subst e_c_a_b [THEN sym])
  by simp

lemma [simp]: "d_aux a b c \<le> a_aux a b c"
  by (simp add: a_aux_def e_aux_def d_aux_def)

lemma [simp]: "d_aux a b c \<le> b_aux a b c"
  apply (unfold b_a)
  apply (subst d_b_c_a [THEN sym])
  by simp

lemma [simp]: "d_aux a b c \<le> c_aux a b c"
  apply (unfold c_a)
  apply (subst d_c_a_b [THEN sym])
  by simp

lemma a_meet_e: "a \<sqinter> (e_aux a b c) = a \<sqinter> (b \<squnion> c)"
  apply (simp add: e_aux_def)
  apply (rule antisym)
  apply simp_all
  apply (rule_tac y = "(a \<squnion> b) \<sqinter> (b \<squnion> c) \<sqinter> (c \<squnion> a)" in order_trans)
  apply (rule inf_le2)
  by simp
  
lemma b_meet_e: "b \<sqinter> (e_aux a b c) = b \<sqinter> (c \<squnion> a)"
  by (simp add: a_meet_e [THEN sym] e_b_c_a)

lemma c_meet_e: "c \<sqinter> (e_aux a b c) = c \<sqinter> (a \<squnion> b)"
  by (simp add: a_meet_e [THEN sym] e_c_a_b)

lemma a_join_d: "a \<squnion> d_aux a b c = a \<squnion> (b \<sqinter> c)"
  apply (simp add: d_aux_def)
  apply (rule antisym)
  apply simp_all
  apply (rule_tac y = "a \<sqinter> b \<squnion> b \<sqinter> c \<squnion> c \<sqinter> a" in order_trans)
  by simp_all

lemma b_join_d: "b \<squnion> d_aux a b c = b \<squnion> (c \<sqinter> a)"
  by (simp add: a_join_d [THEN sym] d_b_c_a)

end

context lattice begin
definition
  "no_distrib a b c = (a \<sqinter> b \<squnion> c \<sqinter> a < a \<sqinter> (b \<squnion> c))"

definition
  "incomp x y = (\<not> x \<le> y \<and> \<not> y \<le> x)"

definition 
  "N5_lattice a b c = (a \<sqinter> c = b \<sqinter> c \<and> a < b \<and> a \<squnion> c = b \<squnion> c)"

definition 
  "M5_lattice a b c = (a \<sqinter> b = b \<sqinter> c \<and> c \<sqinter> a = b \<sqinter> c \<and> a \<squnion> b = b \<squnion> c \<and> c \<squnion> a = b \<squnion> c \<and> a \<sqinter> b < a \<squnion> b)"

lemma M5_lattice_incomp: "M5_lattice a b c \<Longrightarrow> incomp a b"
  apply (simp add: M5_lattice_def incomp_def)
  apply safe
  apply (simp_all add: inf_absorb1 inf_absorb2 )
  apply (simp_all add: sup_absorb1 sup_absorb2 )
  apply (subgoal_tac "c \<sqinter> (b \<squnion> c) = c")
  apply simp
  apply (subst sup_commute)
  by simp
end


context modular_lattice begin

lemma a_meet_d: "a \<sqinter> (d_aux a b c) = (a \<sqinter> b) \<squnion> (c \<sqinter> a)"
  proof -
    have "a \<sqinter> (d_aux a b c) = a \<sqinter> ((a \<sqinter> b) \<squnion> (b \<sqinter> c) \<squnion> (c \<sqinter> a))" by (simp add: d_aux_def)
    also have "... = a \<sqinter> (a \<sqinter> b \<squnion> c \<sqinter> a \<squnion> b \<sqinter> c)" by (simp add: sup_assoc, simp add: sup_commute)
    also have "... = (a \<sqinter> b \<squnion> c \<sqinter> a) \<squnion> (a \<sqinter> (b \<sqinter> c))" by (simp add: modular)
    also have "... = (a \<sqinter> b) \<squnion> (c \<sqinter> a)" by (rule antisym, simp_all, rule_tac y = "a \<sqinter> b" in order_trans, simp_all)
    finally show ?thesis by simp
  qed
  
lemma b_meet_d: "b \<sqinter> (d_aux a b c) = (b \<sqinter> c) \<squnion> (a \<sqinter> b)"
  by (simp add: a_meet_d [THEN sym] d_b_c_a)

lemma c_meet_d: "c \<sqinter> (d_aux a b c) = (c \<sqinter> a) \<squnion> (b \<sqinter> c)"
  by (simp add: a_meet_d [THEN sym] d_c_a_b)

lemma d_less_e: "no_distrib a b c \<Longrightarrow> d_aux a b c < e_aux a b c"
  apply (subst less_le)
  apply(case_tac "d_aux a b c = e_aux a b c")
  apply simp_all
  apply (simp add: no_distrib_def a_meet_e [THEN sym] a_meet_d [THEN sym])
  apply (rule_tac y = "a_aux a b c" in order_trans)
  by simp_all

lemma a_meet_b_eq_d: " d_aux a b c \<le> e_aux a b c \<Longrightarrow> a_aux a b c \<sqinter> b_aux a b c = d_aux a b c"
  proof -
    assume d_less_e: " d_aux a b c \<le> e_aux a b c"
    have "(a \<sqinter> e_aux a b c \<squnion> d_aux a b c) \<sqinter> (b \<sqinter> e_aux a b c \<squnion> d_aux a b c) = (b \<sqinter> e_aux a b c \<squnion>  d_aux a b c) \<sqinter> (d_aux a b c \<squnion> a \<sqinter> e_aux a b c)"
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = d_aux a b c \<squnion> ((b \<sqinter> e_aux a b c \<squnion> d_aux a b c) \<sqinter> (a \<sqinter> e_aux a b c))" 
      by (simp add: modular)
    also have "\<dots> = d_aux a b c \<squnion> (d_aux a b c \<squnion> e_aux a b c \<sqinter> b) \<sqinter> (a \<sqinter> e_aux a b c)" 
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = d_aux a b c \<squnion> (e_aux a b c \<sqinter> (d_aux a b c \<squnion> b)) \<sqinter> (a \<sqinter> e_aux a b c)" 
      by (cut_tac d_less_e, simp add: modular [THEN sym] less_le)
    also have "\<dots> =  d_aux a b c \<squnion> ((a \<sqinter> e_aux a b c) \<sqinter> (e_aux a b c \<sqinter> (b \<squnion> d_aux a b c)))" 
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> e_aux a b c \<sqinter> (b \<squnion> d_aux a b c))" by (simp add: inf_assoc)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> e_aux a b c \<sqinter> (b \<squnion> (c \<sqinter> a)))" by (simp add: b_join_d)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> (b \<squnion> c) \<sqinter> (b \<squnion> (c \<sqinter> a)))" by (simp add: a_meet_e)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> ((b \<squnion> c) \<sqinter> (b \<squnion> (c \<sqinter> a))))" by (simp add: inf_assoc)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> (b \<squnion> ((b \<squnion> c) \<sqinter> (c \<sqinter> a))))" by (simp add: modular)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> (b \<squnion> (c \<sqinter> a)))" by (simp add: inf_absorb2)
    also have "\<dots> = d_aux a b c \<squnion> (a \<sqinter> ((c \<sqinter> a) \<squnion> b))" by (simp add: sup_commute inf_commute)
    also have "\<dots> = d_aux a b c \<squnion> ((c \<sqinter> a) \<squnion> (a \<sqinter> b))" by (simp add: modular)
    also have "\<dots> = d_aux a b c"
      by (rule antisym, simp_all add: d_aux_def)
    finally show ?thesis by (simp add: a_aux_def b_aux_def)
  qed

lemma b_meet_c_eq_d: " d_aux a b c \<le> e_aux a b c \<Longrightarrow> b_aux a b c \<sqinter> c_aux a b c = d_aux a b c"
  apply (subst b_a)
  apply (subgoal_tac "c_aux a b c = b_aux b c a")
  apply simp
  apply (subst a_meet_b_eq_d)
  by (simp_all add: c_aux_def b_aux_def d_b_c_a e_b_c_a)
  
lemma c_meet_a_eq_d: "d_aux a b c \<le> e_aux a b c \<Longrightarrow> c_aux a b c \<sqinter> a_aux a b c = d_aux a b c"
  apply (subst c_a)
  apply (subgoal_tac "a_aux a b c = b_aux c a b")
  apply simp
  apply (subst a_meet_b_eq_d)
  by (simp_all add: a_aux_def b_aux_def d_b_c_a e_b_c_a)
  
lemma a_def_equiv: "d_aux a b c \<le> e_aux a b c \<Longrightarrow> a_aux a b c = (a \<squnion> d_aux a b c) \<sqinter> e_aux a b c"
  apply (simp add: a_aux_def)
  apply (subst inf_commute) 
  apply (subst sup_commute)
  apply (simp add: modular)
  by (simp add: inf_commute sup_commute)

lemma b_def_equiv: "d_aux a b c \<le> e_aux a b c \<Longrightarrow> b_aux a b c = (b \<squnion> d_aux a b c) \<sqinter> e_aux a b c"
  apply (cut_tac a = b and b = c and c = a in a_def_equiv)
  by (simp_all add: d_b_c_a e_b_c_a b_a)

lemma c_def_equiv: "d_aux a b c \<le> e_aux a b c \<Longrightarrow> c_aux a b c = (c \<squnion> d_aux a b c) \<sqinter> e_aux a b c"
  apply (cut_tac a = c and b = a and c = b in a_def_equiv)
  by (simp_all add: d_c_a_b e_c_a_b c_a)

lemma a_join_b_eq_e: "d_aux a b c \<le> e_aux a b c \<Longrightarrow> a_aux a b c \<squnion> b_aux a b c = e_aux a b c"
  proof -
    assume d_less_e: " d_aux a b c \<le> e_aux a b c"
    have "((a \<squnion> d_aux a b c) \<sqinter> e_aux a b c) \<squnion> ((b \<squnion> d_aux a b c) \<sqinter> e_aux a b c) = ((b \<squnion> d_aux a b c) \<sqinter> e_aux a b c) \<squnion> (e_aux a b c \<sqinter> (a \<squnion> d_aux a b c))"
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = e_aux a b c \<sqinter> (((b \<squnion> d_aux a b c) \<sqinter> e_aux a b c) \<squnion> (a \<squnion> d_aux a b c))" 
      by (simp add: modular)
    also have "\<dots> = e_aux a b c \<sqinter> ((e_aux a b c \<sqinter> (d_aux a b c \<squnion> b)) \<squnion> (a \<squnion> d_aux a b c))" 
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = e_aux a b c \<sqinter> ((d_aux a b c \<squnion> (e_aux a b c \<sqinter> b)) \<squnion> (a \<squnion> d_aux a b c))" 
      by (cut_tac d_less_e, simp add: modular)
    also have "\<dots> = e_aux a b c \<sqinter> ((a \<squnion> d_aux a b c) \<squnion> (d_aux a b c \<squnion> (b \<sqinter> e_aux a b c)))" 
      by (simp add: inf_commute sup_commute)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> d_aux a b c \<squnion> (b \<sqinter> e_aux a b c))" by (simp add: sup_assoc)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> d_aux a b c \<squnion> (b \<sqinter> (c \<squnion> a)))" by (simp add: b_meet_e)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> (b \<sqinter> c) \<squnion> (b \<sqinter> (c \<squnion> a)))" by (simp add: a_join_d)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> ((b \<sqinter> c) \<squnion> (b \<sqinter> (c \<squnion> a))))" by (simp add: sup_assoc)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> (b \<sqinter> ((b \<sqinter> c) \<squnion> (c \<squnion> a))))" by (simp add: modular)
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> (b \<sqinter> (c \<squnion> a)))" by (simp add: sup_absorb2) 
    also have "\<dots> = e_aux a b c \<sqinter> (a \<squnion> ((c \<squnion> a) \<sqinter> b))" by (simp add: sup_commute inf_commute)
    also have "\<dots> = e_aux a b c \<sqinter> ((c \<squnion> a) \<sqinter> (a \<squnion> b))" by (simp add: modular)
    also have "\<dots> = e_aux a b c"
      by (rule antisym, simp_all, simp_all add: e_aux_def)
    finally show ?thesis by (cut_tac d_less_e, simp add: a_def_equiv b_def_equiv)
  qed

lemma b_join_c_eq_e: " d_aux a b c <= e_aux a b c \<Longrightarrow> b_aux a b c \<squnion> c_aux a b c = e_aux a b c"
  apply (subst b_a)
  apply (subgoal_tac "c_aux a b c = b_aux b c a")
  apply simp
  apply (subst a_join_b_eq_e)
  by (simp_all add: c_aux_def b_aux_def d_b_c_a e_b_c_a)
  
lemma c_join_a_eq_e: "d_aux a b c <= e_aux a b c \<Longrightarrow> c_aux a b c \<squnion> a_aux a b c = e_aux a b c"
  apply (subst c_a)
  apply (subgoal_tac "a_aux a b c = b_aux c a b")
  apply simp
  apply (subst a_join_b_eq_e)
  by (simp_all add: a_aux_def b_aux_def d_b_c_a e_b_c_a)

lemma "no_distrib a b c \<Longrightarrow> incomp a b"
  apply (simp add: no_distrib_def incomp_def)
  apply safe
  apply (simp add: inf_absorb1) 
  apply (subgoal_tac "a \<squnion> c \<sqinter> a = a \<and> a \<sqinter> (b \<squnion> c) = a")
  apply simp
  apply safe
  apply (rule antisym)
  apply simp
  apply simp
  apply (rule antisym)
  apply simp_all
  apply (rule_tac y = b in order_trans)
  apply simp_all
  apply (simp add: inf_absorb2) 
  apply (unfold modular [THEN sym])
  by (simp add: inf_commute)

lemma M5_modular: "no_distrib a b c \<Longrightarrow> M5_lattice (a_aux a b c) (b_aux a b c) (c_aux a b c)"
  apply (frule d_less_e)
  by (simp add: M5_lattice_def a_meet_b_eq_d b_meet_c_eq_d c_meet_a_eq_d a_join_b_eq_e b_join_c_eq_e c_join_a_eq_e)

lemma M5_modular_def: "M5_lattice a b c = (a \<sqinter> b = b \<sqinter> c \<and> c \<sqinter> a = b \<sqinter> c \<and> a \<squnion> b = b \<squnion> c \<and> c \<squnion> a = b \<squnion> c \<and> a \<sqinter> b < a \<squnion> b)"
  by (simp add: M5_lattice_def)


end

context lattice begin

lemma not_modular_N5: "(\<not> class.modular_lattice inf ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) sup) =
   (\<exists> a b c::'a . N5_lattice a b c)"
  apply (subgoal_tac "class.lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) sup")
  apply (unfold N5_lattice_def class.modular_lattice_def class.modular_lattice_axioms_def)
  apply simp_all
  apply safe
  apply (subgoal_tac "x \<squnion> y \<sqinter> z < y \<sqinter> (x \<squnion> z)")
  apply (rule_tac x = "x \<squnion> y \<sqinter> z" in exI)
  apply (rule_tac x = "y \<sqinter> (x \<squnion> z)" in exI)
  apply (rule_tac x = z in exI)
  apply safe
  apply (rule antisym)
  apply simp
  apply (rule_tac y = "x \<squnion> y \<sqinter> z" in order_trans)
  apply simp_all
  apply (rule_tac y = "y \<sqinter> z" in order_trans)
  apply simp_all
  apply (rule antisym)
  apply simp_all
  apply (rule_tac y = "y \<sqinter> (x \<squnion> z)" in order_trans)
  apply simp_all
  apply (rule_tac y = "x \<squnion> z" in order_trans)
  apply simp_all
  apply (rule neq_le_trans)
  apply simp
  apply simp
  apply (rule_tac x = a in exI)
  apply (rule_tac x = b in exI)
  apply safe
  apply (simp add: less_le)
  apply (rule_tac x = c in exI)
  apply simp
  apply (simp add: less_le)
  apply safe
  apply (subgoal_tac "a \<squnion> a \<sqinter> c = b")
  apply (unfold sup_inf_absorb) [1]
  apply simp
  apply simp
  proof qed

lemma not_distrib_N5_M5: "(\<not> class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)) =
   ((\<exists> a b c::'a . N5_lattice a b c) \<or> (\<exists> a b c::'a . M5_lattice a b c))"
  apply (unfold not_modular_N5 [THEN sym])
  proof
    assume A: "\<not> class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)"
    have B: "\<exists> a b c:: 'a . (a \<sqinter> b) \<squnion> (a \<sqinter> c) < a \<sqinter> (b \<squnion> c)"
      apply (cut_tac A)
      apply (unfold  class.distrib_lattice_def)
      apply safe
      apply simp_all
      proof
        fix x y z::'a
        assume A: "\<forall>(a::'a) (b::'a) c::'a. \<not> a \<sqinter> b \<squnion> a \<sqinter> c < a \<sqinter> (b \<squnion> c)"
        show "x \<squnion> y \<sqinter> z = (x \<squnion> y) \<sqinter> (x \<squnion> z)"
          apply (cut_tac A)
          apply (rule distrib_imp1)
          by (simp add: less_le)
      qed
    from B show "\<not> class.modular_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>) \<or> (\<exists>a b c::'a. M5_lattice a b c)"
      proof (unfold disj_not1, safe)
        fix a b c::'a
        assume A: "a \<sqinter> b \<squnion> a \<sqinter> c < a \<sqinter> (b \<squnion> c)"
        assume B: "class.modular_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)"
        interpret modular: modular_lattice "(\<sqinter>)" "((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool)" "(<)" "(\<squnion>)"
          by (fact B)

        have H: "M5_lattice (a_aux a b c) (b_aux a b c) (c_aux a b c)"
          apply (cut_tac a = a and b = b and c = c in  modular.M5_modular)
          apply (unfold no_distrib_def)
          by (simp_all add: A inf_commute)
        from H show "\<exists>a b c::'a. M5_lattice a b c" by blast
     qed
   next
     assume A: "\<not> class.modular_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>) \<or> (\<exists>(a::'a) (b::'a) c::'a. M5_lattice a b c)"
     show "\<not> class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)"
       apply (cut_tac A)
       apply safe
       apply (erule notE)
       apply unfold_locales
       apply (unfold class.distrib_lattice_def)
       apply (unfold class.distrib_lattice_axioms_def)
       apply safe
       apply (simp add: sup_absorb2)
       apply (frule M5_lattice_incomp)
       apply (unfold M5_lattice_def)
       apply (drule_tac x = a in spec)
       apply (drule_tac x = b in spec)
       apply (drule_tac x = c in spec)
       apply safe
       proof -
         fix a b c:: 'a
         assume A:"a \<squnion> b \<sqinter> c = (a \<squnion> b) \<sqinter> (a \<squnion> c)"
         assume B: "a \<sqinter> b = b \<sqinter> c"
         assume D: "a \<squnion> b = b \<squnion> c"
         assume E: "c \<squnion> a = b \<squnion> c"
         assume G: "incomp a b"
         have H: "a \<squnion> b \<sqinter> c = a" by (simp add: B [THEN sym] sup_absorb1)
         have I: "(a \<squnion> b) \<sqinter> (a \<squnion> c) = a \<squnion> b" by (cut_tac E, simp add: sup_commute D)
         have J: "a = a \<squnion> b" by (cut_tac A, simp add: H I)
         show False
           apply (cut_tac G J)
           apply (subgoal_tac "b \<le> a")
           apply (simp add: incomp_def)
           apply (rule_tac y = "a \<squnion> b" in order_trans)
           apply (rule sup_ge2)
           by simp
       qed
     qed
 
lemma distrib_not_N5_M5: "(class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)) =
   ((\<forall> a b c::'a . \<not> N5_lattice a b c) \<and> (\<forall> a b c::'a . \<not> M5_lattice a b c))"
  apply (cut_tac not_distrib_N5_M5)
  by auto

lemma distrib_inf_sup_eq:
  "(class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)) = 
    (\<forall> x y z::'a . x \<sqinter> z = y \<sqinter> z \<and> x \<squnion> z = y \<squnion> z \<longrightarrow> x = y)"
  apply safe
  proof -
    fix x y z:: 'a
    assume A: "class.distrib_lattice (\<sqinter>) ((\<le>) ::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)"
    interpret distrib: distrib_lattice "(\<sqinter>)" "(\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "(<)" "(\<squnion>)"
      by (fact A)
    assume B: "x \<sqinter> z = y \<sqinter> z"
    assume C: "x \<squnion> z = y \<squnion> z"
    have "x = x \<sqinter> (x \<squnion> z)" by simp
    also have "\<dots> = x \<sqinter> (y \<squnion> z)" by (simp add: C)
    also have "\<dots> = (x \<sqinter> y) \<squnion> (x \<sqinter> z)" by (simp add: distrib.inf_sup_distrib)
    also have "\<dots> = (y \<sqinter> x) \<squnion> (y \<sqinter> z)" by (simp add: B inf_commute)
    also have "\<dots> = y \<sqinter> (x \<squnion> z)" by (simp add: distrib.inf_sup_distrib)
    also have "\<dots> = y" by (simp add: C)
    finally show "x = y" .
  next
    assume A: "(\<forall>x y z:: 'a. x \<sqinter> z = y \<sqinter> z \<and> x \<squnion> z = y \<squnion> z \<longrightarrow> x = y)"
    have B: "!! x y z :: 'a. x \<sqinter> z = y \<sqinter> z \<and> x \<squnion> z = y \<squnion> z \<Longrightarrow> x = y"
      by (cut_tac A, blast)
    show "class.distrib_lattice (\<sqinter>) ((\<le>)::'a \<Rightarrow> 'a \<Rightarrow> bool) (<) (\<squnion>)"
      apply (unfold distrib_not_N5_M5)
      apply safe
      apply (unfold N5_lattice_def)
      apply (cut_tac x = a and y = b and z = c in B)
      apply (simp_all)
      apply (unfold M5_lattice_def)
      apply (cut_tac x = a and y = b and z = c in B)
      by (simp_all add: inf_commute sup_commute)
 qed
end

class inf_sup_eq_lattice = lattice +
  assumes inf_sup_eq: "x \<sqinter> z = y \<sqinter> z \<Longrightarrow> x \<squnion> z = y \<squnion> z \<Longrightarrow> x = y"
begin
subclass distrib_lattice
  by (metis distrib_inf_sup_eq inf_sup_eq)
end

end
