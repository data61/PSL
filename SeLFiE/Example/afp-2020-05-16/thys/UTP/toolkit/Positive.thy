(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Positive.thy                                                         *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Positive Subtypes \<close>

theory Positive
imports 
  Infinity
  "HOL-Library.Countable"
begin

subsection \<open> Type Definition \<close>

typedef (overloaded) 'a::"{zero, linorder}" pos = "{x::'a. x \<ge> 0}"
  apply (rule_tac x = "0" in exI)
  apply (clarsimp)
  done

syntax
  "_type_pos" :: "type \<Rightarrow> type" ("_\<^sup>+" [999] 999)

translations
  (type) "'a\<^sup>+" == (type) "'a pos"

setup_lifting type_definition_pos

type_synonym preal = "real pos"
  
subsection \<open> Operators \<close>
  
lift_definition mk_pos :: "'a::{zero, linorder} \<Rightarrow> 'a pos" is
"\<lambda> n. if (n \<ge> 0) then n else 0" by auto

lift_definition real_of_pos :: "real pos \<Rightarrow> real" is id .

declare [[coercion real_of_pos]]

subsection \<open> Instantiations \<close>

instantiation pos :: ("{zero, linorder}") zero
begin
  lift_definition zero_pos :: "'a pos"
    is "0 :: 'a" ..
  instance ..
end

instantiation pos :: ("{zero, linorder}") linorder
begin
  lift_definition less_eq_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
    is "(\<le>) :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .
  lift_definition less_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> bool"
    is "(<) :: 'a \<Rightarrow> 'a \<Rightarrow> bool" .
  instance
    apply (intro_classes; transfer)
        apply (auto)
  done
end

instance pos :: ("{zero, linorder, no_top}") no_top
  apply (intro_classes)
  apply (transfer)
  apply (clarsimp)
  apply (meson gt_ex less_imp_le order.strict_trans1)
  done

instance pos :: ("{zero, linorder, no_top}") infinite
  apply (intro_classes)
  apply (rule notI)
  apply (subgoal_tac "\<forall>x::'a pos. x \<le> Max UNIV")
  using gt_ex leD apply (blast)
  apply (simp)
  done

instantiation pos :: (linordered_semidom) linordered_semidom
begin
  lift_definition one_pos :: "'a pos"
    is "1 :: 'a" by (simp)
  lift_definition plus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
    is "(+)" by (simp)
  lift_definition minus_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
    is "\<lambda>x y. if y \<le> x then x - y else 0"
    by (simp add: add_le_imp_le_diff)
  lift_definition times_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
    is "times" by (simp)
  instance
    apply (intro_classes; transfer; simp?)
            apply (simp add: add.assoc)
           apply (simp add: add.commute)
          apply (safe; clarsimp?) [1]
             apply (simp add: diff_diff_add)
            apply (metis add_le_cancel_left le_add_diff_inverse)
           apply (simp add: add.commute add_le_imp_le_diff)
          apply (metis add_increasing2 antisym linear)
         apply (simp add: mult.assoc)
        apply (simp add: mult.commute)
       apply (simp add: comm_semiring_class.distrib)
      apply (simp add: mult_strict_left_mono)
     apply (safe; clarsimp?) [1]
       apply (simp add: right_diff_distrib')
      apply (simp add: mult_left_mono)
    using mult_left_le_imp_le apply (fastforce)
    apply (simp add: distrib_left)
    done
end

instantiation pos :: ("linordered_field") semidom_divide
begin
  lift_definition divide_pos :: "'a pos \<Rightarrow> 'a pos \<Rightarrow> 'a pos"
    is "divide" by (simp)
  instance
    apply (intro_classes; transfer)
     apply (simp_all)
    done
end
  
instantiation pos :: (linordered_field) inverse
begin
  lift_definition inverse_pos :: "'a pos \<Rightarrow> 'a pos"
    is "inverse" by (simp)
  instance ..
end

lemma pos_positive [simp]: "0 \<le> (x::'a::{zero,linorder} pos)"
  by (transfer, simp)
 
subsection \<open> Theorems \<close>
  
lemma mk_pos_zero [simp]: "mk_pos 0 = 0"
  by (transfer, simp)

lemma mk_pos_one [simp]: "mk_pos 1 = 1"
  by (transfer, simp)

lemma mk_pos_leq: 
  "\<lbrakk> 0 \<le> x; x \<le> y \<rbrakk> \<Longrightarrow> mk_pos x \<le> mk_pos y"
  by (transfer, auto)
    
lemma mk_pos_less: 
  "\<lbrakk> 0 \<le> x; x < y \<rbrakk> \<Longrightarrow> mk_pos x < mk_pos y"
  by (transfer, auto)
     
lemma real_of_pos [simp]: "x \<ge> 0 \<Longrightarrow> real_of_pos (mk_pos x) = x"
  by (transfer, simp) 
    
lemma mk_pos_real_of_pos [simp]: "mk_pos (real_of_pos x) = x"
  by (transfer, simp)
    
subsection \<open> Transfer to Reals \<close>
  
named_theorems pos_transfer
    
lemma real_of_pos_0 [pos_transfer]: 
  "real_of_pos 0 = 0"
  by (transfer, auto)

lemma real_of_pos_1 [pos_transfer]: 
  "real_of_pos 1 = 1"
  by (transfer, auto)
    
lemma real_op_pos_plus [pos_transfer]:
  "real_of_pos (x + y) = real_of_pos x + real_of_pos y"
  by (transfer, simp)

lemma real_op_pos_minus [pos_transfer]:
  "x \<ge> y \<Longrightarrow> real_of_pos (x - y) = real_of_pos x - real_of_pos y"
  by (transfer, simp)

lemma real_op_pos_mult [pos_transfer]:
  "real_of_pos (x * y) = real_of_pos x * real_of_pos y"
  by (transfer, simp)
   
lemma real_op_pos_div [pos_transfer]:
  "real_of_pos (x / y) = real_of_pos x / real_of_pos y"
  by (transfer, simp)

lemma real_of_pos_numeral [pos_transfer]:
  "real_of_pos (numeral n) = numeral n"
  by (induct n, simp_all only: numeral.simps pos_transfer)

lemma real_of_pos_eq_transfer [pos_transfer]:
  "x = y \<longleftrightarrow> real_of_pos x = real_of_pos y"
  by (transfer, auto)

lemma real_of_pos_less_eq_transfer [pos_transfer]:
  "x \<le> y \<longleftrightarrow> real_of_pos x \<le> real_of_pos y"
  by (transfer, auto)
    
lemma real_of_pos_less_transfer [pos_transfer]:
  "x < y \<longleftrightarrow> real_of_pos x < real_of_pos y"
  by (transfer, auto)
  
end