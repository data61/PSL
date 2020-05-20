section\<open>Lattice Orderd Groups\<close>

(*
    Author: Viorel Preoteasa
*)

theory Lattice_Ordered_Group
imports Modular_Distrib_Lattice
begin

text\<open>
This theory introduces lattice ordered groups \cite{birkhoff:1942} 
and proves some results about them. The most important result is 
that a lattice ordered group is also a distributive lattice.
\<close>

class lgroup = group_add + lattice +
assumes add_order_preserving: "a \<le> b \<Longrightarrow> u + a + v \<le> u + b + v"
begin

lemma add_order_preserving_left: "a \<le> b \<Longrightarrow> u + a \<le> u + b"
  apply (cut_tac a = a and b = b and u = u and v = 0 in add_order_preserving)
  by simp_all

lemma add_order_preserving_right: "a \<le> b \<Longrightarrow> a + v \<le> b + v"
  apply (cut_tac a = a and b = b and u = 0 and v = v in add_order_preserving)
  by simp_all


lemma minus_order: "-a \<le> -b \<Longrightarrow> b \<le> a"
  apply (cut_tac a = "-a" and b = "-b" and u = a and v = b in add_order_preserving)
  by simp_all


lemma right_move_to_left: "a + - c \<le> b \<Longrightarrow> a \<le> b + c"  
  apply (drule_tac v = "c" in add_order_preserving_right)
  by (simp add: add.assoc)
 
lemma right_move_to_right: "a \<le> b + -c \<Longrightarrow> a + c \<le> b"  
  apply (drule_tac v = "c" in add_order_preserving_right)
  by (simp add: add.assoc)
 

lemma [simp]: "(a \<sqinter> b) + c = (a + c) \<sqinter> (b + c)"
  apply (rule antisym)
  apply simp
  apply safe
  apply (rule add_order_preserving_right)
  apply simp
  apply (rule add_order_preserving_right)
  apply simp
  apply (rule right_move_to_left)
  apply simp
  apply safe
  apply (simp_all only: diff_conv_add_uminus)
  apply (rule right_move_to_right)
  apply simp
  apply (rule right_move_to_right)
  by simp

lemma [simp]: "(a \<sqinter> b) - c = (a - c) \<sqinter> (b - c)"
  by (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)


lemma left_move_to_left: "-c + a \<le> b \<Longrightarrow> a \<le> c + b"  
  apply (drule_tac u = "c" in add_order_preserving_left)
  by (simp add: add.assoc [THEN sym])
 
lemma left_move_to_right: "a \<le> - c + b \<Longrightarrow> c + a \<le> b"  
  apply (drule_tac u = "c" in add_order_preserving_left)
  by (simp add: add.assoc [THEN sym])

lemma [simp]: "c + (a \<sqinter> b) = (c + a) \<sqinter> (c + b)"
  apply (rule antisym)
  apply simp
  apply safe
  apply (rule add_order_preserving_left)
  apply simp
  apply (rule add_order_preserving_left)
  apply simp
  apply (rule left_move_to_left)
  apply simp
  apply safe
  apply (rule left_move_to_right)
  apply simp
  apply (rule left_move_to_right)
  by simp

lemma [simp]: "- (a \<sqinter> b) = (- a) \<squnion> (- b)"
  apply (rule antisym)
  apply (rule minus_order)
  apply simp
  apply safe
  apply (rule minus_order)
  apply simp
  apply (rule minus_order)
  apply simp
  apply simp
  apply safe
  apply (rule minus_order)
  apply simp
  apply (rule minus_order)
  by simp

lemma [simp]: "(a \<squnion> b) + c = (a + c) \<squnion> (b + c)"
  apply (rule antisym)
  apply (rule right_move_to_right)
  apply simp
  apply safe
  apply (simp_all only: diff_conv_add_uminus)
  apply (rule right_move_to_left)
  apply simp
  apply (rule right_move_to_left)
  apply simp
  apply simp
  apply safe
  apply (rule add_order_preserving_right)
  apply simp
  apply (rule add_order_preserving_right)
  by simp
  
lemma [simp]: "c + (a \<squnion> b) = (c + a) \<squnion> (c + b)"
  apply (rule antisym)
  apply (rule left_move_to_right)
  apply simp
  apply safe
  apply (rule left_move_to_left)
  apply simp
  apply (rule left_move_to_left)
  apply simp
  apply simp
  apply safe
  apply (rule add_order_preserving_left)
  apply simp
  apply (rule add_order_preserving_left)
  by simp

lemma [simp]: "c - (a \<sqinter> b) = (c - a) \<squnion> (c - b)"
  by (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)

lemma [simp]: "(a \<squnion> b) - c = (a - c) \<squnion>  (b - c)"
  by (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)

lemma [simp]: "- (a \<squnion> b) = (- a) \<sqinter> (- b)"
  apply (rule antisym)
  apply simp
  apply safe
  apply (rule minus_order)
  apply simp
  apply (rule minus_order)
  apply simp
  apply (rule minus_order)
  by simp
  
lemma [simp]: "c - (a \<squnion> b) = (c - a) \<sqinter> (c - b)"
  by (simp add: diff_conv_add_uminus del: add_uminus_conv_diff)
  
lemma add_pos: "0 \<le> a \<Longrightarrow> b \<le> b + a"
  apply (cut_tac a = 0 and b = a and u = b and v = 0 in add_order_preserving)
  by simp_all

lemma add_pos_left: "0 \<le> a \<Longrightarrow> b \<le> a + b"
  apply (rule right_move_to_left)
  by simp

lemma inf_sup: "a - (a \<sqinter> b) + b = a \<squnion> b"
  by (simp add: add.assoc sup_commute)

lemma inf_sup_2: "b = (a \<sqinter> b) - a + (a \<squnion> b)"
  apply (unfold inf_sup [THEN sym])
  proof -
    fix a b:: 'a
    have "b = (a \<sqinter> b) + (- a + a) + - (a \<sqinter> b) + b" by (simp only: right_minus left_minus add_0_right add_0_left)
    also have "\<dots> = (a \<sqinter> b) + - a + (a + - (a \<sqinter> b) + b)" by (unfold add.assoc, simp) 
    also have "\<dots> = (a \<sqinter> b) - a + (a - (a \<sqinter> b) + b)" by simp
    finally show "b = (a \<sqinter> b) - a + (a - (a \<sqinter> b) + b)" .
  qed


subclass inf_sup_eq_lattice
  proof
    fix x y z:: 'a
    assume A: "x \<sqinter> z = y \<sqinter> z"
    assume B: "x \<squnion> z = y \<squnion> z"
    have "x = (z \<sqinter> x) - z + (z \<squnion> x)" by (rule inf_sup_2)
    also have "\<dots> = (z \<sqinter> y) - z + (z \<squnion> y)" by (simp add: sup_commute inf_commute A B)
    also have "\<dots> = y" by (simp only: inf_sup_2 [THEN sym])
    finally show "x = y" .
  qed
end

end
