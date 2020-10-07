(**                Algebra1  
                                  author Hidetsune Kobayashi
                                  Department of Mathematics
                                  Nihon University
                                  hikoba@math.cst.nihon-u.ac.jp
                                  May 3, 2004.
                                  April 6, 2007 (revised)

 chapter 0. Preliminaries
   section 1.   Natural numbers and Integers
   section 2.   Sets
   section 3.   Functions
   section 4.   Nsets, set of natural numbers
   section 4'.  Lower bounded set of integers
   section 5.   Augmented integer: integer and \<infinity> -\<infinity> 
   section 6.   amin, amax 
   section 7.   cardinality of sets

 Note. Some lemmas in this chapter are already formalized by L. Paulson 
       and others. 

 chapter 1.  Ordered Set
   section 1.   Basic Concepts of Ordered Sets
**)

theory Algebra1
imports Main "HOL-Library.FuncSet"
begin

chapter "Preliminaries"

text\<open>Some of the lemmas of this section are proved in src/HOL/Integ
   of Isabelle version 2003.\<close>

section "Lemmas for logical manipulation"

lemma True_then:"True \<longrightarrow> P \<Longrightarrow> P"
by simp

lemma ex_conjI:"\<lbrakk>P c; Q c\<rbrakk> \<Longrightarrow> \<exists>c. P c \<and> Q c"
by blast

lemma forall_spec:"\<lbrakk> \<forall>b. P b \<longrightarrow> Q b; P a\<rbrakk> \<Longrightarrow> Q a" 
by simp

lemma a_b_exchange:"\<lbrakk>a; a = b\<rbrakk> \<Longrightarrow> b"
by simp

lemma eq_prop:"\<lbrakk> P; P = Q\<rbrakk> \<Longrightarrow> Q"
by simp

lemma forball_contra:"\<lbrakk>\<forall>y\<in>A. P x y \<longrightarrow> \<not> Q y; \<forall>y\<in>A. Q y \<or> R y\<rbrakk> \<Longrightarrow> 
                    \<forall>y\<in>A. (\<not> P x y) \<or> R y"
by blast

lemma forball_contra1:"\<lbrakk>\<forall>y\<in>A. P x y \<longrightarrow> Q y; \<forall>y\<in>A. \<not> Q y\<rbrakk> \<Longrightarrow> \<forall>y\<in>A. \<not> P x y"
by blast  

section "Natural numbers and Integers"

text\<open>Elementary properties of natural numbers and integers\<close>

lemma nat_nonzero_pos:"(a::nat) \<noteq> 0 \<Longrightarrow> 0 < a"
by simp

lemma add_both:"(a::nat) = b \<Longrightarrow> a + c = b + c"
by simp

lemma add_bothl:"a = b \<Longrightarrow> c + a = c + b"
by simp

lemma diff_Suc:"(n::nat) \<le> m \<Longrightarrow> m - n + Suc 0 = Suc m - n"
by arith

lemma le_convert:"\<lbrakk>a = b; a \<le> c\<rbrakk> \<Longrightarrow> b \<le> c"
by simp

lemma ge_convert:"\<lbrakk>a = b; c \<le> a\<rbrakk> \<Longrightarrow> c \<le> b"
by simp

lemma less_convert:"\<lbrakk> a = b; c < b \<rbrakk> \<Longrightarrow> c < a"
by auto

lemma ineq_conv1:"\<lbrakk>a = b; a < c\<rbrakk> \<Longrightarrow> b < c"
by simp

lemma diff_Suc_pos:"0 < a - Suc 0 \<Longrightarrow>  0 < a"
by simp

lemma minus_SucSuc:"a - Suc (Suc 0) = a - Suc 0 - Suc 0" 
by simp

lemma Suc_Suc_Tr:"Suc (Suc 0) \<le> n \<Longrightarrow> Suc (n - Suc (Suc 0)) = n - Suc 0"
by arith

lemma Suc_Suc_less:"Suc 0 < a \<Longrightarrow> Suc (a - Suc (Suc 0)) < a"
by arith

lemma diff_zero_eq:"n = (0::nat) \<Longrightarrow> m = m - n"
by simp

lemma Suc_less_le:"x < Suc n \<Longrightarrow> x \<le> n"
by auto

lemma less_le_diff:"x < n \<Longrightarrow> x \<le> n - Suc 0"
by arith

lemma le_pre_le:"x \<le> n - Suc 0 \<Longrightarrow> x \<le> n"
by arith

lemma nat_not_less:"\<not> (m::nat) < n \<Longrightarrow> n \<le> m"
by (rule contrapos_pp, simp+)

lemma less_neq:"n < (m::nat) \<Longrightarrow> n \<noteq> m"
by (simp add:nat_neq_iff[THEN sym, of "n" "m"])

lemma less_le_diff1:"n \<noteq> 0 \<Longrightarrow> ((m::nat) < n) = (m \<le> (n - Suc 0))"
by arith

lemma nat_not_less1:"n \<noteq> 0 \<Longrightarrow> (\<not> (m::nat) < n) = (\<not> m \<le> (n - Suc 0))"
by arith

lemma nat_eq_le:"m = (n::nat) \<Longrightarrow> m \<le> n"
by simp


subsection "Integers"

lemma non_zero_int:" (n::int) \<noteq> 0 \<Longrightarrow> 0 < n \<or> n < 0"
by arith

lemma zgt_0_zge_1:"(0::int) < z \<Longrightarrow> 1 \<le> z"
by arith

lemma not_zle:"(\<not> (n::int) \<le> m) =  (m < n)"
by auto

lemma not_zless:"(\<not> (n::int) < m) = (m \<le> n)"
by auto

lemma zle_imp_zless_or_eq:"(n::int) \<le> m \<Longrightarrow> n < m \<or> n = m"
by arith

lemma zminus_zadd_cancel:" - z + (z + w) = (w::int)"
by simp

lemma int_neq_iff:"((w::int) \<noteq> z) = (w < z) \<or> (z < w)"
by auto

lemma zless_imp_zle:"(z::int) < z' \<Longrightarrow> z \<le> z'"
by simp

lemma zdiff:"z - (w::int) = z + (- w)"
by simp

lemma zle_zless_trans:"\<lbrakk> (i::int) \<le> j; j < k\<rbrakk> \<Longrightarrow> i < k"
by arith

lemma zless_zle_trans:"\<lbrakk> (i::int) < j; j \<le> k\<rbrakk> \<Longrightarrow> i < k"
by arith

lemma zless_neq:"(i::int) < j \<Longrightarrow> i \<noteq> j"
by simp

lemma int_mult_mono:"\<lbrakk> i < j; (0::int) < k \<rbrakk> \<Longrightarrow> k * i < k * j"
apply (frule zmult_zless_mono2_lemma [of "i" "j" "nat k"])
apply simp apply simp
done

lemma int_mult_le:"\<lbrakk>i \<le> j; (0::int) \<le> k\<rbrakk> \<Longrightarrow> k * i \<le> k * j"
apply (simp add:order_le_less)
 apply (case_tac "i < j")
  apply (case_tac "0 < k")
   apply simp
  apply simp
 apply simp
done

lemma int_mult_le1:"\<lbrakk>i \<le> j; (0::int) \<le> k\<rbrakk> \<Longrightarrow> i * k \<le> j * k"
apply (simp add:mult.commute[of _ "k"])
apply (simp add:int_mult_le)
done

lemma zmult_zminus_right:"(w::int) * (- z) = - (w * z)"
apply (insert distrib_left[of "w" "z" "-z"]) 
apply simp
done

lemma zmult_zle_mono1_neg:"\<lbrakk>(i::int) \<le> j; k \<le> 0\<rbrakk> \<Longrightarrow> j * k \<le> i * k"
apply (subgoal_tac "0 \<le> - k") prefer 2 apply simp
apply (frule int_mult_le [of "i" "j" "- k"], assumption+)
apply (simp add:mult.commute)
done 

lemma zmult_zless_mono_neg:"\<lbrakk>(i::int) < j; k < 0\<rbrakk> \<Longrightarrow> j * k < i * k"
apply (subgoal_tac "0 < -k", 
       frule int_mult_mono[of "i" "j" "-k"], assumption+,
       simp add:mult.commute, simp)
done

lemma zmult_neg_neg:"\<lbrakk>i < (0::int); j < 0 \<rbrakk> \<Longrightarrow> 0 < i * j"
apply (frule zmult_zless_mono_neg[of "i" "0" "j"], assumption)
apply simp
done

lemma zmult_pos_pos:"\<lbrakk>(0::int) < i; 0 < j\<rbrakk> \<Longrightarrow> 0 < i * j"
apply (frule int_mult_mono[of "0" "i" "j"], assumption+)
apply (simp add:mult.commute)
done

lemma zmult_pos_neg:"\<lbrakk>(0::int) < i; j < 0\<rbrakk> \<Longrightarrow> i * j < 0"
apply (frule zmult_zless_mono_neg[of "0" "i" "j"], assumption+, simp)
done

lemma zmult_neg_pos:"\<lbrakk>i < (0::int); 0 < j\<rbrakk> \<Longrightarrow> i * j < 0"
apply (frule int_mult_mono[of "i" "0" "j"], assumption+, 
       simp add:mult.commute)
done

lemma zle:"((z::int) \<le> w) = (\<not> (w < z))" 
by auto

lemma times_1_both:"\<lbrakk>(0::int) < z; z * z' = 1\<rbrakk> \<Longrightarrow> z = 1 \<and> z' = 1"
apply (subgoal_tac "0 < z'")
 apply (frule zgt_0_zge_1[of "z'"],
        subgoal_tac "z' = 1", simp,
        subgoal_tac "1 < z' \<or> 1 = z'", thin_tac "1 \<le> z'", thin_tac "0 < z'") 
 apply (rule contrapos_pp, simp+,
        frule int_mult_mono[of "1" "z'" "z"], assumption+, simp, arith)
apply (rule contrapos_pp, simp+, simp add:zle[THEN sym], 
       frule zless_imp_zle[of "0" "z"], frule int_mult_le[of "z'" "0" "z"], 
       assumption+, simp)
done

lemma zminus_minus:"i - - (j::int) = i + j"
by simp

lemma zminus_minus_pos:"(n::int) < 0 \<Longrightarrow> 0 < - n"
by simp 

lemma zadd_zle_mono:"\<lbrakk>w' \<le> w; z' \<le> (z::int)\<rbrakk> \<Longrightarrow> w' + z' \<le> w + z" 
by simp

lemma zmult_zle_mono:"\<lbrakk>i \<le> (j::int); 0 < k\<rbrakk> \<Longrightarrow> k * i \<le>  k * j"
apply (case_tac "i = j") apply simp
apply (frule zle_imp_zless_or_eq[of "i" "j"]) 
 apply (thin_tac "i \<le> j") apply simp
done

lemma zmult_zle_mono_r:"\<lbrakk>i \<le> (j::int); 0 < k\<rbrakk> \<Longrightarrow> i * k \<le> j * k"
apply (frule zmult_zle_mono[of "i" "j" "k"], assumption)
apply (simp add:mult.commute)
done 

lemma pos_zmult_pos:"\<lbrakk> 0 \<le> (a::int); 0 < (b::int)\<rbrakk> \<Longrightarrow> a \<le> a * b"
apply (case_tac "a = 0") apply simp
apply (frule zle_imp_zless_or_eq[of "0" "a"]) apply (thin_tac "0 \<le> a")
apply simp
done 

lemma pos_mult_l_gt:"\<lbrakk>(0::int) < w; i \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i \<le> w * j"
by (metis not_zless pos_zmult_pos order_trans mult.commute)

lemma  pos_mult_r_gt:"\<lbrakk>(0::int) < w; i \<le> j; 0 \<le> i\<rbrakk> \<Longrightarrow> i \<le> j * w"
apply (frule pos_mult_l_gt[of "w" "i" "j"], assumption+)
apply (simp add:mult.commute[of "w" "j"])
done

lemma mult_pos_iff:"\<lbrakk>(0::int) < i; 0 \<le> i * j \<rbrakk> \<Longrightarrow> 0 \<le> j" 
apply (rule contrapos_pp, simp+) 
 apply (cut_tac linorder_linear[of "0" "j"]) apply simp
 apply (simp add:not_zle)
 apply (frule int_mult_mono[of "j" "0" "i"], assumption+)  apply simp
done

lemma zmult_eq:"\<lbrakk>(0::int) < w; z = z'\<rbrakk> \<Longrightarrow> w * z = w * z'"
by simp

lemma zmult_eq_r:"\<lbrakk>(0::int) < w; z = z'\<rbrakk> \<Longrightarrow> z * w =  z' * w"
by simp


lemma zdiv_eq_l:"\<lbrakk>(0::int) < w; z * w  = z' * w \<rbrakk> \<Longrightarrow> z = z'"
by simp

lemma zdiv_eq_r:"\<lbrakk>(0::int) < w; w * z  = w * z' \<rbrakk> \<Longrightarrow> z = z'"
by simp

lemma int_nat_minus:"0 < (n::int) \<Longrightarrow> nat (n - 1) = (nat n) - 1"
by arith

lemma int_nat_add:"\<lbrakk>0 < (n::int); 0 < (m::int)\<rbrakk> \<Longrightarrow> (nat (n - 1)) + (nat (m - 1)) + (Suc 0) = nat (n + m - 1)"
by arith

lemma int_equation:"(x::int) = y + z \<Longrightarrow> x - y = z"
by simp

lemma int_pos_mult_monor:"\<lbrakk> 0 < (n::int); 0 \<le> n * m \<rbrakk> \<Longrightarrow> 0 \<le> m" 
by (rule mult_pos_iff, assumption+)

lemma int_pos_mult_monol:"\<lbrakk> 0 < (m::int); 0 \<le> n * m \<rbrakk> \<Longrightarrow> 0 \<le> n" 
apply (rule int_pos_mult_monor, assumption+)
apply (simp add:mult.commute)
done

lemma zdiv_positive:"\<lbrakk>(0::int) \<le> a; 0 < b\<rbrakk> \<Longrightarrow> 0 \<le> a div b"
apply (frule_tac a = 0 and a' = a and b = b in zdiv_mono1, assumption+)
apply simp
done 

lemma zdiv_pos_mono_r:"\<lbrakk> (0::int) < w; w * z \<le> w * z'\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (rule contrapos_pp, simp+) 
done (** zmult_div_mono to rename **)

lemma zdiv_pos_mono_l:"\<lbrakk> (0::int) < w; z * w \<le> z' * w\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (simp add:mult.commute)
done

lemma zdiv_pos_pos_l:"\<lbrakk> (0::int) < w; 0 \<le> z * w\<rbrakk> \<Longrightarrow> 0 \<le> z"
by (simp add:mult.commute, frule zdiv_pos_mono_r[of "w" "0" "z"], simp, 
        assumption)

section "Sets"

(* Preliminary properties of sets are proved here. Some of them are 
 already proved by L. Paulson and others. *)

subsection "A short notes for proof steps" 

subsection "Sets" 

lemma inEx:"x \<in> A \<Longrightarrow> \<exists>y\<in>A. y = x"
by simp

lemma inEx_rev:" \<exists>y\<in>A. y = x \<Longrightarrow> x \<in> A"
by blast

lemma nonempty_ex:"A \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A" 
by blast

lemma ex_nonempty:"\<exists>x. x \<in> A \<Longrightarrow> A \<noteq> {}"
by blast

lemma not_eq_outside:"a \<notin> A \<Longrightarrow> \<forall>b\<in>A. b \<noteq> a"
by blast

lemma ex_nonempty_set:"\<exists>a. P a \<Longrightarrow> {x. P x} \<noteq> {}"
by blast

lemma nonempty: "x \<in> A \<Longrightarrow> A \<noteq> {}"
by blast

lemma subset_self:"A \<subseteq> A"
by simp

lemma conditional_subset:"{x\<in>A. P x} \<subseteq> A"
by blast

lemma bsubsetTr:"{x. x \<in> A \<and> P x} \<subseteq> A"
by blast

lemma sets_not_eq:"\<lbrakk>A \<noteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. a \<notin> B" 
by blast

lemma diff_nonempty:"\<lbrakk>A \<noteq> B; B \<subseteq> A\<rbrakk> \<Longrightarrow> A - B \<noteq> {}"
by blast

lemma sub_which1:"\<lbrakk>A \<subseteq> B \<or> B \<subseteq> A; x \<in> A; x \<notin> B\<rbrakk> \<Longrightarrow> B \<subseteq> A"
by blast

lemma sub_which2:"\<lbrakk>A \<subseteq> B \<or> B \<subseteq> A; x \<notin> A; x \<in> B\<rbrakk> \<Longrightarrow> A \<subseteq> B"
by blast

lemma nonempty_int: "A \<inter> B \<noteq> {} \<Longrightarrow> \<exists>x. x \<in> A \<inter> B "
by blast

lemma no_meet1:"A \<inter> B = {}\<Longrightarrow> \<forall>a \<in> A. a \<notin> B"
by blast

lemma no_meet2:"A \<inter> B = {}\<Longrightarrow> \<forall>a \<in> B. a \<notin> A"
by blast

lemma elem_some:"x \<in> A \<Longrightarrow> \<exists>y\<in>A. x = y"  
by blast

lemma singleton_sub:"a \<in> A \<Longrightarrow> {a} \<subseteq> A"
by blast

lemma eq_elem_in: "\<lbrakk> a \<in> A; a = b \<rbrakk> \<Longrightarrow> b \<in> A"
by simp

lemma eq_set_inc: "\<lbrakk> a \<in> A; A = B \<rbrakk> \<Longrightarrow> a \<in> B"
by simp

lemma eq_set_not_inc:"\<lbrakk>a \<notin> A; A = B \<rbrakk> \<Longrightarrow> a \<notin> B"
by simp

lemma int_subsets: "\<lbrakk> A1 \<subseteq> A; B1 \<subseteq> B \<rbrakk> \<Longrightarrow> A1 \<inter> B1 \<subseteq> A \<inter> B"
by blast

lemma inter_mono:"A \<subseteq> B \<Longrightarrow> A \<inter> C \<subseteq> B \<inter> C"
by blast

lemma sub_Un1:"B \<subseteq>  B \<union> C" 
by blast

lemma sub_Un2:"C \<subseteq>  B \<union> C" 
by blast

lemma subset_contr:"\<lbrakk> A \<subset> B; B \<subseteq> A \<rbrakk> \<Longrightarrow> False"
by blast

lemma psubset_contr:"\<lbrakk> A \<subset> B; B \<subset> A \<rbrakk> \<Longrightarrow> False"
by blast

lemma eqsets_sub:"A = B \<Longrightarrow> A \<subseteq> B"
by simp

lemma not_subseteq:" \<not> A \<subseteq> B \<Longrightarrow> \<exists>a \<in> A. a \<notin> B"
by blast

lemma in_un1:"\<lbrakk> x \<in> A \<union> B; x \<notin> B \<rbrakk> \<Longrightarrow> x \<in> A"
by blast

lemma proper_subset:"\<lbrakk>A \<subseteq> B; x \<notin> A; x \<in> B\<rbrakk> \<Longrightarrow> A \<noteq> B"
by blast

lemma in_un2:"\<lbrakk> x \<in> A \<union> B; x \<notin> A \<rbrakk> \<Longrightarrow> x \<in> B"
by simp

lemma diff_disj:"x \<notin> A \<Longrightarrow> A - {x} = A" 
by auto

lemma in_diff:"\<lbrakk>x \<noteq> a; x \<in> A\<rbrakk> \<Longrightarrow> x \<in> A - {a}"
by simp

lemma in_diff1:"x \<in> A - {a} \<Longrightarrow> x \<noteq> a"
by simp

lemma sub_inserted1:"\<lbrakk>Y \<subseteq> insert a X; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> a \<notin> X \<and> a \<in> Y"
by blast

lemma sub_inserted2:"\<lbrakk>Y \<subseteq> insert a X; \<not> Y \<subseteq> X\<rbrakk> \<Longrightarrow> Y = (Y - {a}) \<union> {a}"
by blast

lemma insert_sub:"\<lbrakk> A \<subseteq> B; a \<in> B\<rbrakk> \<Longrightarrow> (insert a A) \<subseteq> B"
by blast

lemma insert_diff:"A \<subseteq> (insert b B) \<Longrightarrow> A - {b} \<subseteq> B"
by blast

lemma insert_inc1:"A \<subseteq> insert a A"
by blast

lemma insert_inc2:"a \<in> insert a A"
by simp

lemma nonempty_some:"A \<noteq> {} \<Longrightarrow> (SOME x. x \<in> A) \<in> A" 
apply (frule nonempty_ex[of "A"])
apply (rule someI2_ex) apply simp+
done

lemma mem_family_sub_Un:"A \<in> C \<Longrightarrow> A \<subseteq> \<Union> C"
by blast

lemma sub_Union:"\<exists>X\<in>C. A \<subseteq> X \<Longrightarrow> A \<subseteq> \<Union> C" 
by blast

lemma family_subset_Un_sub:"\<forall>A\<in>C. A \<subseteq> B \<Longrightarrow> \<Union> C \<subseteq> B"
by blast

lemma in_set_with_P:"P x \<Longrightarrow> x \<in> {y. P y}"
by blast

lemma sub_single:"\<lbrakk>A \<noteq> {}; A \<subseteq> {a}\<rbrakk> \<Longrightarrow> A = {a}"
by blast

lemma not_sub_single:"\<lbrakk>A \<noteq> {}; A \<noteq> {a}\<rbrakk> \<Longrightarrow> \<not> A \<subseteq> {a}"
by blast

lemma not_sub:"\<not> A \<subseteq> B \<Longrightarrow> \<exists>a. a\<in>A \<and> a \<notin> B"
by blast


section "Functions"

definition
  cmp :: "['b \<Rightarrow> 'c, 'a \<Rightarrow> 'b] \<Rightarrow> ('a \<Rightarrow> 'c)" where
  "cmp g f = (\<lambda>x. g (f x))"

definition
  idmap :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a)" where
  "idmap A = (\<lambda>x\<in>A. x)" 

definition
  constmap :: "['a set, 'b set] \<Rightarrow> ('a \<Rightarrow>'b)" where
  "constmap A B = (\<lambda>x\<in>A. SOME y. y \<in> B)" 

definition
  invfun :: "['a set, 'b set, 'a \<Rightarrow> 'b] \<Rightarrow> ('b \<Rightarrow> 'a)" where
  "invfun A B (f :: 'a \<Rightarrow> 'b) = (\<lambda>y\<in>B.(SOME x. (x \<in> A \<and> f x = y)))"

abbreviation
  INVFUN :: "['a \<Rightarrow> 'b, 'b set, 'a set] \<Rightarrow> ('b \<Rightarrow> 'a)"  ("(3_\<inverse>\<^bsub>_,_\<^esub>)" [82,82,83]82) where
  "f\<inverse>\<^bsub>B,A\<^esub> == invfun A B f"

lemma eq_fun:"\<lbrakk> f \<in> A \<rightarrow> B; f = g \<rbrakk> \<Longrightarrow> g \<in> A \<rightarrow> B"
by simp

lemma eq_fun_eq_val:" f = g \<Longrightarrow> f x = g x"
by simp

lemma eq_elems_eq_val:"x = y \<Longrightarrow> f x = f y"
by simp

lemma cmp_fun:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C \<rbrakk> \<Longrightarrow> cmp g f \<in> A \<rightarrow> C"
by (auto simp add:cmp_def)

lemma cmp_fun_image:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C \<rbrakk> \<Longrightarrow> 
                          (cmp g f) ` A =  g ` (f ` A)"
apply (rule equalityI)
 apply (rule subsetI, simp add:image_def)
 apply (erule bexE, simp add:cmp_def, blast)
 apply (rule subsetI, simp add:image_def[of g])
 apply (erule bexE, simp)
 apply (simp add:image_def cmp_def)
 apply blast
done

lemma cmp_fun_sub_image:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; A1 \<subseteq> A\<rbrakk> \<Longrightarrow> 
                          (cmp g f) ` A1 =  g ` (f ` A1)"
apply (rule equalityI)
 apply (rule subsetI, simp add:image_def)
 apply (erule bexE, simp add:cmp_def, blast)
 apply (rule subsetI, simp add:image_def[of g])
 apply (erule bexE, simp)
 apply (simp add:image_def cmp_def)
 apply blast
done


lemma restrict_fun_eq:"\<forall>x\<in>A. f x = g x \<Longrightarrow> (\<lambda>x\<in>A. f x) = (\<lambda>x\<in>A. g x)"
 apply (simp add:fun_eq_iff)
done

lemma funcset_mem: "\<lbrakk>f \<in> A \<rightarrow> B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
apply (simp add: Pi_def)
done

lemma img_subset:"f \<in> A \<rightarrow> B \<Longrightarrow> f ` A \<subseteq> B"
apply (rule subsetI)
apply (simp add:image_def, erule bexE, simp)
apply (simp add:funcset_mem)
done

lemma funcset_mem1:"\<lbrakk>\<forall>l\<in>A. f l \<in> B; x \<in> A\<rbrakk> \<Longrightarrow> f x \<in> B"
apply simp
done

lemma func_to_img:"f \<in> A \<rightarrow> B \<Longrightarrow> f \<in> A \<rightarrow> f ` A"
by (simp add:Pi_def)

lemma restrict_in_funcset: "\<forall>x\<in> A. f x \<in> B \<Longrightarrow> 
                                     (\<lambda>x\<in>A. f x)\<in> A \<rightarrow> B"
apply (simp add:Pi_def restrict_def)
done

lemma funcset_eq:"\<lbrakk> f \<in> extensional A; g \<in> extensional A; \<forall>x\<in>A. f x = g x \<rbrakk> \<Longrightarrow>  f = g"
apply (simp add:extensionalityI)
done

lemma eq_funcs:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> A \<rightarrow> B; f = g; x \<in> A\<rbrakk> \<Longrightarrow> f x = g x"
by simp

lemma restriction_of_domain:"\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> 
  restrict f A1 \<in> A1 \<rightarrow> B"
by blast

lemma restrict_restrict:"\<lbrakk> restrict f A \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow>
      restrict (restrict f A) A1 = restrict f A1"
apply (rule funcset_eq[of _ "A1"])
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI) apply simp
 apply (simp add:subsetD)
done
 
lemma restr_restr_eq:"\<lbrakk> restrict f A \<in> A \<rightarrow> B; restrict f A = restrict g A;
A1 \<subseteq> A \<rbrakk> \<Longrightarrow> restrict f A1 = restrict g A1"
 apply (subst restrict_restrict[THEN sym, of "f" "A" "B" "A1"], assumption+)
 apply (simp add:restrict_restrict[THEN sym, of "g" "A" "B" "A1"])
done

lemma funcTr:"\<lbrakk> f \<in> A \<rightarrow> B; g \<in> A \<rightarrow> B; f = g; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
apply simp
done 

lemma funcTr1:"\<lbrakk>f = g; a \<in> A\<rbrakk> \<Longrightarrow> f a = g a"
apply simp
done

lemma restrictfun_im:"\<lbrakk> (restrict f A) \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow>
       (restrict f A) ` A1 = f ` A1"
apply (subgoal_tac "\<forall>x\<in>A1. x \<in> A")
apply (simp add:image_def)
apply (rule ballI) apply (simp add:subsetD)
done

lemma mem_in_image:"\<lbrakk> f \<in> A \<rightarrow> B; a \<in> A\<rbrakk> \<Longrightarrow> f a \<in> f ` A "
apply (simp add:image_def)
 apply blast
done

lemma mem_in_image1:"\<lbrakk> \<forall>l\<in>A. f l \<in> B; a \<in> A\<rbrakk> \<Longrightarrow> f a \<in> f ` A "
apply simp
done

lemma mem_in_image2:"a \<in> A \<Longrightarrow> f a \<in> f ` A"
apply simp
done

lemma mem_in_image3:"b \<in> f ` A \<Longrightarrow> \<exists>a \<in> A. b = f a"
by (simp add:image_def)

lemma elem_in_image2: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A; x \<in> A1\<rbrakk> \<Longrightarrow> f x \<in> f` A1"
 apply (simp add:image_def)
 apply blast
 done

lemma funcs_nonempty:"\<lbrakk> A \<noteq> {}; B \<noteq> {} \<rbrakk> \<Longrightarrow> (A \<rightarrow> B) \<noteq> {}"
apply (subgoal_tac "constmap A B \<in> A \<rightarrow> B") apply (simp add:nonempty)
apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:constmap_def)
 apply (frule nonempty_ex[of "B"])
 apply (rule someI2_ex) apply assumption+
done

lemma idmap_funcs: "idmap A \<in> A \<rightarrow> A"
 apply (simp add:Pi_def restrict_def idmap_def)
 done


lemma l_idmap_comp: "\<lbrakk>f \<in> extensional A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> 
                   compose A (idmap B) f = f"
apply (rule funcset_eq[of _ "A"])
 apply (simp add:compose_def) 
 apply assumption
 apply (rule ballI)
 apply (simp add:funcset_mem[of "f" "A" "B"] compose_def idmap_def)
 done
 
lemma r_idmap_comp:"\<lbrakk>f \<in> extensional A; f \<in> A \<rightarrow> B\<rbrakk> \<Longrightarrow> 
                                   compose A f (idmap A) = f"
apply (rule funcset_eq[of _ "A"])
 apply (simp add:compose_def) 
 apply assumption
 apply (rule ballI)
 apply (simp add:funcset_mem[of "f" "A" "B"] compose_def idmap_def)
 done
 
lemma extend_fun: "\<lbrakk> f \<in> A \<rightarrow> B; B \<subseteq> B1 \<rbrakk> \<Longrightarrow> f \<in> A \<rightarrow> B1"
 apply (simp add:Pi_def restrict_def)
 apply (rule allI) apply (rule impI)
 apply (simp add:subsetD)
 done

lemma restrict_fun: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> restrict f A1 \<in> A1 \<rightarrow> B"
 apply (simp add:Pi_def restrict_def)
 apply (rule allI) apply (rule impI) 
 apply (simp add:subsetD)
 done
 
lemma set_of_hom: "\<forall>x \<in> A. f x \<in> B \<Longrightarrow> restrict f A \<in> A \<rightarrow> B"
 apply (simp add:Pi_def restrict_def)
 done

lemma composition : "\<lbrakk> f \<in> A \<rightarrow>  B; g \<in> B \<rightarrow> C\<rbrakk> \<Longrightarrow> (compose A g f) \<in> A \<rightarrow>  C"
 apply (simp add:Pi_def restrict_def compose_def)
 done  

lemma comp_assoc:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; h \<in> C \<rightarrow> D \<rbrakk> \<Longrightarrow>
     compose A h (compose A g f) = compose A (compose B h g) f" 
apply (rule funcset_eq[of _ "A"])
 apply (simp add:compose_def)
 apply (simp add:compose_def)
apply (rule ballI)
 apply (simp add:funcset_mem[of "f" "A" "B"] compose_def)
 done

lemma restrictfun_inj: "\<lbrakk> inj_on f A; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> inj_on (restrict f A1) A1"
 apply (simp add:inj_on_def) 
 apply (simp add:subsetD)
done

lemma restrict_inj:"\<lbrakk>inj_on f A; A1 \<subseteq> A\<rbrakk> \<Longrightarrow> inj_on f A1"
apply (simp add:inj_on_def)
 apply ((rule ballI)+, rule impI)
 apply (frule_tac c = x in subsetD[of "A1" "A"], assumption+,
        frule_tac c = y in subsetD[of "A1" "A"], assumption+)
 apply simp
done

lemma injective:"\<lbrakk> inj_on f A; x \<in> A; y \<in> A; x \<noteq> y \<rbrakk> \<Longrightarrow> f x \<noteq> f y"
apply (rule contrapos_pp, simp+)
 apply (simp add:inj_on_def)
done

lemma injective_iff:"\<lbrakk> inj_on f A; x \<in> A; y \<in> A\<rbrakk> \<Longrightarrow> 
                        (x = y) = (f x = f y)"
apply (rule iffI, simp)
apply (rule contrapos_pp, simp+)
apply (frule injective[of "f" "A" "x" "y"], assumption+)
apply simp
done

lemma injfun_elim_image:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; x \<in> A\<rbrakk> \<Longrightarrow>
                f ` (A - {x}) = (f ` A) - {f x}"
apply (rule equalityI)
 apply (rule subsetI, simp add:image_def, erule bexE)
 apply (simp, (erule conjE)+)
 apply (rule contrapos_pp, simp+)
 apply (erule disjE, simp add:inj_on_def, blast)
 apply (frule_tac x = xaa and y = x in injective[of f A ], assumption+,
        blast)
 
 apply (rule subsetI, simp add:image_def)
 apply (rule contrapos_pp, simp+, erule conjE, erule bexE)
 apply (frule_tac x = xaa in bspec)
 apply (simp, rule contrapos_pp, simp+)
done

lemma cmp_inj:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; inj_on f A; inj_on g B \<rbrakk> \<Longrightarrow>
         inj_on (cmp g f) A" 
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+ 
apply (simp add:cmp_def) apply (rule impI)
apply (subgoal_tac "f x = f y")
apply (simp add:inj_on_def [of "f"])
apply (frule_tac x = x in funcset_mem [of "f" "A" "B"], assumption+) 
apply (frule_tac x = y in funcset_mem [of "f" "A" "B"], assumption+)
apply (simp add:inj_on_def [of "g"])
done

lemma cmp_assoc:"\<lbrakk>f \<in> A \<rightarrow> B; g \<in> B \<rightarrow> C; h \<in> C \<rightarrow> D; x \<in> A\<rbrakk> \<Longrightarrow>
                          (cmp h (cmp g f)) x  = (cmp (cmp h g) f) x"
apply (simp add:cmp_def)
done

lemma bivar_fun: "\<lbrakk> f \<in> A \<rightarrow> (B \<rightarrow> C); a \<in> A \<rbrakk> \<Longrightarrow> f a \<in> B \<rightarrow> C"
by (simp add:Pi_def)

lemma bivar_fun_mem: "\<lbrakk> f \<in> A \<rightarrow> (B \<rightarrow> C); a \<in> A; b \<in> B \<rbrakk> \<Longrightarrow> f a b \<in> C"
 apply (frule funcset_mem[of "f" "A" "B \<rightarrow> C"], assumption+) 
 apply (rule funcset_mem[of "f a" "B" "C"], assumption+)
 done

lemma bivar_func_eq:"\<lbrakk>\<forall>a\<in>A. \<forall>b\<in>B. f a b = g a b \<rbrakk> \<Longrightarrow>
                         (\<lambda>x\<in>A. \<lambda>y\<in>B. f x y) =  (\<lambda>x\<in>A. \<lambda>y\<in>B. g x y)"
apply (subgoal_tac "\<forall>x\<in>A. (\<lambda>y\<in>B. f x y) = (\<lambda>y\<in>B. g x y)")
apply (rule funcset_eq [of _ "A"]) 
 apply (simp add:extensional_def restrict_def)
 apply (simp add:extensional_def restrict_def)
 apply (rule ballI)
 apply simp
apply (rule ballI)
 apply (rule funcset_eq [of _ "B"]) 
 apply (simp add:restrict_def extensional_def)
 apply (simp add:restrict_def extensional_def)
apply (rule ballI) apply simp
done
 
lemma set_image: "\<lbrakk> f \<in> A \<rightarrow> B; A1 \<subseteq> A; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> 
            f`(A1 \<inter> A2) \<subseteq> (f` A1) \<inter> (f` A2)"
 apply (simp add: image_def) 
 apply auto
 done

lemma image_sub: "\<lbrakk>f \<in> A \<rightarrow> B; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> (f`A1) \<subseteq> B"
by (auto simp add:image_def)

lemma image_sub0: "f \<in> A \<rightarrow> B \<Longrightarrow> (f`A) \<subseteq> B"
by (simp add:image_sub[of "f" "A" "B" "A"])

lemma image_nonempty:"\<lbrakk>f \<in> A \<rightarrow> B; A1 \<subseteq> A; A1 \<noteq> {} \<rbrakk> \<Longrightarrow> f ` A1 \<noteq> {}"
by (frule nonempty_some[of "A1"], 
       frule elem_in_image2[of "f" "A" "B" "A1" "SOME x. x \<in> A1"], 
        assumption+, simp add:nonempty)

lemma im_set_mono: "\<lbrakk>f \<in>A \<rightarrow> B; A1 \<subseteq> A2; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> (f ` A1) \<subseteq> (f ` A2)"
 apply (simp add:image_def)
 apply auto
 done

lemma im_set_un:"\<lbrakk> f\<in>A \<rightarrow> B; A1 \<subseteq> A; A2 \<subseteq> A \<rbrakk> \<Longrightarrow> 
             f`(A1 \<union> A2) = (f`A1) \<union> (f`A2)"
apply (simp add:image_def)
 apply auto
 done

lemma im_set_un1:"\<lbrakk>\<forall>l\<in>A. f l \<in> B; A = A1 \<union> A2\<rbrakk> \<Longrightarrow> 
                                f `(A1 \<union> A2) = f `(A1) \<union> f `(A2)" 
apply (rule equalityI,
       rule subsetI, simp add:image_def, erule bexE)
 apply blast
apply (rule subsetI,
       simp add:image_def, erule disjE, erule bexE, blast)
 apply (erule bexE) apply blast
done

lemma im_set_un2:"A = A1 \<union> A2 \<Longrightarrow>  f `A = f `(A1) \<union> f `(A2)" 
apply (rule equalityI,
       rule subsetI, simp add:image_def, erule bexE, blast)
apply (rule subsetI,
       simp add:image_def, erule disjE, erule bexE, blast, erule bexE, blast)
done

definition
  invim::"['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> 'a set" where
  "invim f A B = {x. x\<in>A \<and> f x \<in> B}"

lemma invim: "\<lbrakk> f:A \<rightarrow> B; B1 \<subseteq> B \<rbrakk> \<Longrightarrow> invim f A B1 \<subseteq> A"
  by (auto simp add:invim_def)

lemma setim_cmpfn: "\<lbrakk> f:A \<rightarrow> B; g:B \<rightarrow> C; A1 \<subseteq> A \<rbrakk> \<Longrightarrow> 
               (compose A g f)` A1 = g`(f` A1)"
apply (simp add:image_def compose_def)
 apply auto
 done

definition
  surj_to :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where
  "surj_to f A B \<longleftrightarrow> f`A = B"

lemma surj_to_test:"\<lbrakk> f \<in> A \<rightarrow> B; \<forall>b\<in>B. \<exists>a\<in>A. f a = b \<rbrakk> \<Longrightarrow>
                                                  surj_to f A B"
by (auto simp add:surj_to_def image_def)

lemma surj_to_image:"f \<in> A \<rightarrow> B \<Longrightarrow> surj_to f A (f ` A)"
apply (rule surj_to_test[of "f" "A" "f ` A"])
apply (rule func_to_img[of "f" "A" "B"], assumption)
apply (rule ballI, simp add:image_def, erule bexE, simp)
apply blast
done

lemma surj_to_el:"\<lbrakk> f \<in> A \<rightarrow> B; surj_to f A B \<rbrakk> \<Longrightarrow> \<forall>b\<in>B. \<exists>a\<in>A. f a = b"
 apply (simp add:surj_to_def image_def)
 apply auto
 done

lemma surj_to_el1:"\<lbrakk> f \<in> A \<rightarrow> B; surj_to f A B; b\<in>B\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. f a = b"
 apply (simp add:surj_to_el)
 done

lemma surj_to_el2:"\<lbrakk>surj_to f A B; b \<in> B\<rbrakk> \<Longrightarrow> \<exists>a\<in>A. f a = b"
 apply (simp add:surj_to_def image_def)
 apply (frule sym, thin_tac "{y. \<exists>x\<in>A. y = f x} = B", simp)
 apply (erule bexE, simp, blast)
done

lemma compose_surj: "\<lbrakk>f:A \<rightarrow> B; surj_to f A B; g : B \<rightarrow> C; surj_to g B C \<rbrakk> 
                         \<Longrightarrow> surj_to (compose A g f) A C " 
apply (simp add:surj_to_def compose_def image_def)
 apply auto 
 done

lemma cmp_surj: "\<lbrakk>f:A \<rightarrow> B; surj_to f A B; g : B \<rightarrow> C; surj_to g B C \<rbrakk> 
                         \<Longrightarrow> surj_to (cmp g f) A C " 
apply (rule surj_to_test, simp add:cmp_fun) 
apply (rule ballI, simp add:surj_to_def [of "g"], frule sym,
       thin_tac "g ` B = C", simp, simp add:image_def,
       simp add:cmp_def)
 apply auto
apply (simp add:surj_to_def, frule sym,
       thin_tac " f ` A = B", simp add:image_def)
 apply auto
done

lemma inj_onTr0:"\<lbrakk> f \<in> A \<rightarrow> B; x \<in> A; y \<in> A; inj_on f A; f x = f y\<rbrakk> \<Longrightarrow> x = y"
apply (simp add:inj_on_def)
 done

lemma inj_onTr1:"\<lbrakk>inj_on f A; x \<in> A; y \<in> A; f x = f y\<rbrakk>  \<Longrightarrow> x = y"
apply (simp add:inj_on_def)
done

lemma inj_onTr2:"\<lbrakk>inj_on f A; x \<in> A; y \<in> A; f x \<noteq> f y\<rbrakk>  \<Longrightarrow> x \<noteq> y"
apply (rule contrapos_pp, simp+)
done  (* premis inj_on can be changed to some condition indicating f to be
         a function *)


lemma comp_inj: "\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; g \<in> B \<rightarrow> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (compose A g f) A "
apply (simp add:inj_on_def [of "compose A g f"])
 apply (rule ballI)+ apply (rule impI)
 apply (rule inj_onTr0 [of "f" "A" "B"], assumption+)
 apply (frule funcset_mem [of "f" "A" "B" _], assumption+)
 apply (rotate_tac -3)
 apply (frule funcset_mem [of "f" "A" "B" _], assumption+)
 apply (rule inj_onTr0 [of "g" "B" "C" _], assumption+)
 apply (simp add:compose_def)
 done

lemma cmp_inj_1: "\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; g \<in> B \<rightarrow> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (cmp g f) A "
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+ apply (rule impI)
apply (simp add:cmp_def)
apply (frule_tac x = x in funcset_mem [of "f" "A" "B"], assumption+)
apply (frule_tac x = y in funcset_mem [of "f" "A" "B"], assumption+)
apply (frule_tac x = "f x" and y = "f y" in inj_onTr1 [of "g" "B"],
                       assumption+)
apply (rule_tac x = x and y = y in inj_onTr1 [of "f" "A"], assumption+)
done

lemma cmp_inj_2: "\<lbrakk>\<forall>l\<in>A. f l \<in> B; inj_on f A; \<forall>k\<in>B. g k \<in> C; inj_on g B \<rbrakk> 
              \<Longrightarrow> inj_on (cmp g f) A "
apply (simp add:inj_on_def [of "cmp g f"])
apply (rule ballI)+ apply (rule impI)
apply (simp add:cmp_def)
apply (frule_tac x = x in funcset_mem1 [of "A" "f" "B"], assumption+)
apply (frule_tac x = y in funcset_mem1 [of "A" "f" "B"], assumption+)
apply (frule_tac x = "f x" and y = "f y" in inj_onTr1 [of "g" "B"],
                       assumption+)
apply (rule_tac x = x and y = y in inj_onTr1 [of "f" "A"], assumption+)
done

lemma invfun_mem:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B; b \<in> B \<rbrakk> 
                      \<Longrightarrow>  (invfun A B f) b \<in> A"
apply (simp add:invfun_def)
 apply (simp add:surj_to_def image_def) apply (frule sym)
 apply (thin_tac "{y. \<exists>x\<in>A. y = f x} = B") apply simp
 apply (thin_tac "B = {y. \<exists>x\<in>A. y = f x}") apply auto
 apply (rule someI2_ex)
 apply blast apply simp
 done


lemma inv_func:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  (invfun A B f) \<in> B \<rightarrow> A"
apply (simp add:Pi_def)
 apply (rule allI) apply (rule impI)
 apply (rule invfun_mem) apply (rule funcsetI)
 apply simp+
 done

lemma invfun_r:"\<lbrakk> f\<in>A \<rightarrow> B; inj_on f A; surj_to f A B; b \<in> B \<rbrakk> 
                      \<Longrightarrow> f ((invfun A B f) b) = b"
apply (simp add:invfun_def)
 apply (rule someI2_ex)
 apply (simp add:surj_to_def image_def)
 apply auto
 done

lemma invfun_l:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B; a \<in> A\<rbrakk> 
                      \<Longrightarrow> (invfun A B f) (f a) = a"
apply (simp add:invfun_def Pi_def restrict_def)
apply (rule someI2_ex) apply auto
apply (simp add:inj_on_def)
done

lemma invfun_inj:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  inj_on (invfun A B f) B"
apply (simp add:inj_on_def [of "invfun A B f" "B"] )
 apply auto
 apply (frule_tac b = y in invfun_r [of "f" "A" "B"], assumption+)
 apply (frule_tac b = x in invfun_r [of "f" "A" "B"], assumption+)
 apply simp
 done
     
lemma invfun_surj:"\<lbrakk>f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow>  surj_to (invfun A B f) B A "
apply (simp add:surj_to_def [of "invfun A B f" "B" "A"] image_def)
apply (rule equalityI)
 apply (rule subsetI) apply (simp add:CollectI)
 apply auto
apply (simp add:invfun_mem)
apply (frule funcset_mem [of "f" "A" "B"], assumption+)
 apply (frule_tac t = x in invfun_l [of "f" "A" "B", THEN sym], assumption+)
 apply auto
done

definition
  bij_to :: "['a \<Rightarrow> 'b, 'a set, 'b set] \<Rightarrow> bool" where
  "bij_to f A B \<longleftrightarrow> surj_to f A B \<and> inj_on f A"

lemma idmap_bij:"bij_to (idmap A) A A"
apply (simp add:bij_to_def)
apply (rule conjI)
apply (simp add:surj_to_def, simp add:image_def, simp add:idmap_def)

apply (simp add:inj_on_def, simp add:idmap_def)
done

lemma bij_invfun:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B\<rbrakk> \<Longrightarrow>
                              bij_to (invfun A B f) B A"
apply (simp add:bij_to_def)
apply (simp add:invfun_inj invfun_surj)
done

lemma l_inv_invfun:"\<lbrakk> f \<in> A \<rightarrow> B; inj_on f A; surj_to f A B\<rbrakk> 
                      \<Longrightarrow> compose A (invfun A B f) f = idmap A"
apply (rule ext) 
 apply (simp add:compose_def idmap_def)
apply (rule impI)
apply (simp add:invfun_l)
done

lemma invfun_mem1:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; b \<in> B\<rbrakk> \<Longrightarrow>
                 (invfun A B f) b \<in> A"
apply (simp add:bij_to_def, erule conjE)
apply (simp add:invfun_mem)
done

lemma invfun_r1:"\<lbrakk> f\<in>A \<rightarrow> B; bij_to f A B; b \<in> B \<rbrakk> 
                      \<Longrightarrow> f ((invfun A B f) b) = b"
apply (simp add:bij_to_def, erule conjE)
apply (rule invfun_r, assumption+)
done

lemma invfun_l1:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; a \<in> A\<rbrakk> 
                      \<Longrightarrow> (invfun A B f) (f a) = a"
apply (simp add:bij_to_def, erule conjE)
apply (rule invfun_l, assumption+)
done

lemma compos_invfun_r:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; g \<in> A \<rightarrow> C; h \<in> B \<rightarrow> C;
       g \<in> extensional A; compose B g (invfun A B f) = h\<rbrakk> \<Longrightarrow> 
       g = compose A h f"
apply (rule funcset_eq[of g A "compose A h f"], assumption)
 apply (simp add:compose_def extensional_def)
 apply (rule ballI)
 apply (frule sym, thin_tac "compose B g (invfun A B f) = h", simp)
 apply (simp add:compose_def Pi_def invfun_l1)
done

lemma compos_invfun_l:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; g \<in> C \<rightarrow> B; h \<in> C \<rightarrow> A;
       compose C (invfun A B f) g = h; g \<in> extensional C \<rbrakk> \<Longrightarrow> 
                     g = compose C f h"
apply (rule funcset_eq[of g C "compose C f h"], assumption)
       apply (simp add:compose_def extensional_def)
apply (rule ballI)
apply (frule sym, thin_tac "compose C (invfun A B f) g = h", 
       simp add:compose_def)
apply (frule_tac x = x in funcset_mem[of g C B], assumption)
apply (simp add:invfun_r1)
done

lemma invfun_set:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; C \<subseteq> B\<rbrakk> \<Longrightarrow>
                f ` ((invfun A B f)` C) = C"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def, erule exE,
        erule conjE, erule bexE, simp,
        frule_tac c = xb in subsetD[of "C" "B"], assumption+)
 apply (simp add:bij_to_def, erule conjE,
        simp add:invfun_r)

apply (rule subsetI, simp add:image_def)
 apply (frule_tac c = x in subsetD[of "C" "B"], assumption+,
        simp add:bij_to_def, erule conjE,
        frule_tac b = x in invfun_r[of "f" "A" "B"], assumption+)
 apply (frule sym, thin_tac "f (invfun A B f x) = x")
 apply blast
done

lemma compos_bij:"\<lbrakk>f \<in> A \<rightarrow> B; bij_to f A B; g \<in> B \<rightarrow> C; bij_to g B C\<rbrakk> \<Longrightarrow>
                   bij_to (compose A g f) A C"
apply (simp add:bij_to_def, (erule conjE)+)
apply (simp add:comp_inj[of "f" "A" "B" "g" "C"])
apply (simp add:compose_surj)
done

section "Nsets"

 (* NSet is the set of natural numbers, and "Nset n" is the set of 
natural numbers from 0 through n  *)

definition
  nset :: "[nat, nat] \<Rightarrow> (nat) set" where
  "nset i j = {k. i \<le> k \<and> k \<le> j}"

definition
  slide :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "slide i j == i + j"

definition
  sliden :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "sliden i j == j - i"

definition
  jointfun :: "[nat, nat \<Rightarrow> 'a, nat, nat \<Rightarrow> 'a] \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "(jointfun n f m g) = (\<lambda>i. if i \<le> n then f i else  g ((sliden (Suc n)) i))"

definition
  skip :: "nat \<Rightarrow> (nat \<Rightarrow> nat)" where
  "skip i = (\<lambda>x. (if i = 0 then Suc x else
                 (if x \<in> {j. j \<le> (i - Suc 0)} then x  else Suc x)))" 

lemma nat_pos:"0 \<le> (l::nat)"
apply simp
done

lemma Suc_pos:"Suc k \<le> r \<Longrightarrow> 0 < r"
apply simp
done

lemma nat_pos2:"(k::nat) < r \<Longrightarrow> 0 < r"
apply simp
done

lemma eq_le_not:"\<lbrakk>(a::nat) \<le> b; \<not> a < b \<rbrakk> \<Longrightarrow> a = b"
apply auto
done

lemma im_of_constmap:"(constmap {0} {a}) ` {0} = {a}" 
apply (simp add:constmap_def)
done

lemma noteq_le_less:"\<lbrakk> m \<le> (n::nat); m \<noteq> n \<rbrakk> \<Longrightarrow> m < n"
apply auto
done

lemma nat_not_le_less:"(\<not> (n::nat) \<le> m) = (m < n)"
by (simp add: not_le)

lemma self_le:"(n::nat) \<le> n"
apply simp
done

lemma n_less_Suc:"(n::nat) < Suc n"
apply simp
done

lemma less_diff_pos:"i < (n::nat) \<Longrightarrow> 0 < n - i"
apply auto
done

lemma less_diff_Suc:"i < (n::nat) \<Longrightarrow> n - (Suc i) = (n - i) - (Suc 0)"
apply auto
done

lemma less_pre_n:"0 < n \<Longrightarrow> n - Suc 0 < n"
apply simp
done

lemma Nset_inc_0:"(0::nat) \<in> {i. i \<le> n}"
apply simp 
done 

lemma Nset_1:"{i. i \<le> Suc 0} = {0, Suc 0}"
apply auto
done

lemma Nset_1_1:"(k \<le> Suc 0) = (k = 0 \<or> k = Suc 0)"
apply (rule iffI)
apply (case_tac "k = 0", simp+)
apply (erule disjE, simp+)
done

lemma Nset_2:"{i, j} = {j, i}"
apply auto
done

lemma Nset_nonempty:"{i. i \<le> (n::nat)} \<noteq> {}"
apply (subgoal_tac "0 \<in> {i. i \<le> n}")
apply (rule nonempty[of 0], assumption)
apply simp 
done

lemma Nset_le:"x \<in> {i. i \<le> n} \<Longrightarrow> x \<le> n"
apply simp 
done

lemma n_in_Nsetn:"(n::nat) \<in> {i. i \<le> n}"
apply simp 
done

lemma Nset_pre:"\<lbrakk> (x::nat) \<in> {i. i \<le> (Suc n)}; x \<noteq> Suc n \<rbrakk> \<Longrightarrow> x \<in> {i. i \<le> n}"
apply simp 
done

lemma Nset_pre1:"{i. i \<le> (Suc n)} - {Suc n} = {i. i \<le> n}"
apply (rule equalityI)
 apply (rule subsetI, simp)+
done

lemma le_Suc_mem_Nsetn:"x \<le> Suc n \<Longrightarrow> x - Suc 0 \<in> {i. i \<le> n}"
apply (frule diff_le_mono[of x "Suc n" "Suc 0"],
       thin_tac "x \<le> Suc n", simp)
done

lemma le_Suc_diff_le:"x \<le> Suc n \<Longrightarrow> x - Suc 0 \<le> n"
apply (frule diff_le_mono[of x "Suc n" "Suc 0"],
       thin_tac "x \<le> Suc n", simp)
done

lemma Nset_not_pre:"\<lbrakk> x \<notin> {i. i \<le> n}; x \<in> {i. i \<le> (Suc n)}\<rbrakk> \<Longrightarrow> x = Suc n"
by simp

lemma mem_of_Nset:"x \<le> (n::nat) \<Longrightarrow> x \<in> {i. i \<le> n}"
apply simp 
done

lemma less_mem_of_Nset:"x < (n::nat) \<Longrightarrow> x \<in> {i. i \<le> n}"
apply (frule less_imp_le [of "x" "n"])
apply simp
done

lemma Nset_nset:"{i. i \<le> (Suc (n + m))} = {i. i \<le> n} \<union> 
                                            nset (Suc n) (Suc (n + m))"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:nset_def)
  apply (auto simp add: nset_def)
done

lemma Nset_nset_1:"\<lbrakk>0 < n; i < n\<rbrakk> \<Longrightarrow> {j. j \<le> n} = {j. j \<le> i} \<union> 
                                                           nset (Suc i) n"
apply auto
 apply (simp add:nset_def)
 apply (simp add:nset_def)
done

lemma Nset_img0:"\<lbrakk>f \<in> {j. j \<le> Suc n} \<rightarrow> B; (f (Suc n)) \<in> f ` {j. j \<le> n}\<rbrakk> \<Longrightarrow>
                   f ` {j. j \<le> Suc n} = f ` {j. j \<le> n}"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def)
 apply (erule exE, erule conjE)
 apply (erule exE, simp, erule conjE)
 apply (case_tac "xb = Suc n", simp, blast)
 apply (frule_tac m = xb and n = "Suc n" in noteq_le_less, assumption,
         thin_tac "xb \<le> Suc n",
         frule_tac x = xb and n = "Suc n" in less_le_diff,
         thin_tac "xb < Suc n", simp, blast)
 apply (rule subsetI, simp add:image_def, (erule exE)+, (erule conjE)+)
 apply (simp,
        frule_tac x = xb and y = n and z = "Suc n" in le_less_trans,
        simp,
        frule_tac x = xb and y = "Suc n" in less_imp_le,
         blast)
done

lemma Nset_img:"f \<in> {j. j \<le> Suc n} \<rightarrow> B \<Longrightarrow>
         insert (f (Suc n)) (f ` {j. j \<le> n}) = f ` {j. j \<le> Suc n}"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def,
        erule disjE, blast,
        erule exE, erule conjE,
        frule_tac x = xa and y = n and z = "Suc n" in le_less_trans,
        simp+,
        frule_tac x = xa and y = "Suc n" in less_imp_le, blast)
 apply (rule subsetI,
        simp add:image_def,
        erule exE, simp, erule conjE,
        case_tac "xa = Suc n", simp)
 apply (frule_tac m = xa and n = "Suc n" in noteq_le_less, assumption,
        frule_tac x = xa and n = "Suc n" in less_le_diff,
        thin_tac "xa \<le> Suc n", thin_tac "xa < Suc n", simp)
 apply blast
done

primrec nasc_seq :: "[nat set, nat, nat] \<Rightarrow> nat"
where
  dec_seq_0: "nasc_seq A a 0 = a"
| dec_seq_Suc: "nasc_seq A a (Suc n) =
                     (SOME b. ((b \<in> A) \<and> (nasc_seq A a n) < b))"

lemma nasc_seq_mem:"\<lbrakk>(a::nat) \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                        (nasc_seq A a n) \<in> A"
apply (induct n)
apply (simp_all add: not_le)
apply (subgoal_tac "\<exists>x\<in>A. (nasc_seq A a n) < x") prefer 2 apply blast
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. m < x)",
        rule someI2_ex, blast, simp)
done

lemma nasc_seqn:"\<lbrakk>(a::nat) \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                               (nasc_seq A a n) < (nasc_seq A a (Suc n))"
apply (simp,
       frule nasc_seq_mem [of "a" "A" "n"], simp) 
apply (simp add: not_le,
       subgoal_tac "\<exists>x\<in>A. (nasc_seq A a n) < x") prefer 2 apply simp
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. m < x)",
        rule someI2_ex, blast, simp)
done

lemma nasc_seqn1:"\<lbrakk>(a::nat) \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                             Suc (nasc_seq A a n) \<le> (nasc_seq A a (Suc n))"
apply (frule nasc_seqn [of "a" "A" "n"], assumption+)
 apply simp
done

lemma ubs_ex_n_maxTr:"\<lbrakk>(a::nat) \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk>
      \<Longrightarrow>  (a + n) \<le> (nasc_seq A a n)"
apply (induct_tac n)
 apply simp
apply (frule_tac n = n in nasc_seqn1[of "a" "A"], assumption+,
       subgoal_tac "Suc (a + n) \<le> Suc (nasc_seq A a n)",
       frule_tac i = "Suc (a + n)" and j = "Suc (nasc_seq A a n)" and
                  k = "nasc_seq A a (Suc n)" in le_trans, assumption+,
       simp, thin_tac "Suc (nasc_seq A a n) \<le> nasc_seq A a (Suc n)",
       subst Suc_le_mono, assumption+) 
done

lemma ubs_ex_n_max:"\<lbrakk>A \<noteq> {}; A \<subseteq> {i. i \<le> (n::nat)}\<rbrakk> \<Longrightarrow> 
                                      \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m)"
apply (frule nonempty_ex[of "A"])
 apply (thin_tac "A \<noteq> {}")
 apply (erule exE)
apply (rename_tac a)
apply (rule ex_ex1I)
prefer 2
 apply (erule conjE)+
 apply (frule_tac x = y in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. x \<le> m",
        frule_tac x = m in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. x \<le> y", simp)

apply (rule contrapos_pp, simp+)
      
apply (frule_tac a = a and A = A and n = "n + 1" in ubs_ex_n_maxTr, simp) 
apply (frule_tac a = a in nasc_seq_mem[of _ "A" "n + 1"], simp) 
apply (frule_tac c = "nasc_seq A a (n + 1)" in subsetD[of "A" "{i. i \<le> n}"],
         assumption+, simp)
done
 
definition
  n_max :: "nat set \<Rightarrow> nat" where
  "n_max A = (THE m. m \<in> A \<and> (\<forall>x\<in>A. x \<le> m))"

lemma n_max:"\<lbrakk>A \<subseteq> {i. i \<le> (n::nat)}; A \<noteq> {}\<rbrakk> \<Longrightarrow> 
                    (n_max A) \<in> A \<and> (\<forall>x\<in>A. x \<le> (n_max A))" 
apply (simp add:n_max_def)
apply (frule ubs_ex_n_max[of "A" "n"], assumption)
apply (rule theI')
apply assumption
done

lemma n_max_eq_sets:"\<lbrakk>A = B; A \<noteq> {}; \<exists>n. A \<subseteq> {j. j \<le> n}\<rbrakk> \<Longrightarrow>
                          n_max A = n_max B"
by simp 
 (* n_max has no meaning unless conditions A \<noteq> {}; \<exists>n. A \<subseteq> {j. j \<le> n} *)

lemma skip_mem:"l \<in> {i. i \<le> n} \<Longrightarrow> (skip i l) \<in> {i. i \<le> (Suc n)}"
apply (case_tac "i = 0")
 apply (simp add:skip_def)
 apply (simp)+
apply (simp add:skip_def) 
done

lemma skip_fun:"(skip i) \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> (Suc n)}"
apply (rule Pi_I)
apply (rule skip_mem, assumption)
done

lemma skip_im_Tr0:"x \<in> {i. i \<le> n} \<Longrightarrow> skip 0 x = Suc x"
apply (simp add:skip_def)
done

lemma skip_im_Tr0_1:"0 < y \<Longrightarrow> skip 0 (y - Suc 0) = y"
apply (simp add:skip_def)
done

lemma skip_im_Tr1:"\<lbrakk> i \<in> {i. i \<le> (Suc n)}; 0 < i; x \<le> i - Suc 0 \<rbrakk> \<Longrightarrow>
           skip i x = x"
by (simp add:skip_def)

lemma skip_im_Tr1_1:"\<lbrakk> i \<in> {i. i \<le> (Suc n)}; 0 < i; x < i\<rbrakk> \<Longrightarrow>
                       skip i x = x"
apply (frule less_le_diff[of x i])
apply (simp add:skip_def)
done

lemma skip_im_Tr1_2:"\<lbrakk> i \<le> (Suc n); x < i\<rbrakk> \<Longrightarrow>  skip i x = x"
apply (rule skip_im_Tr1_1[of i n x], simp+) 
done

lemma skip_im_Tr2:"\<lbrakk> 0 < i; i \<in> {i. i \<le> (Suc n)}; i \<le> x\<rbrakk> \<Longrightarrow>
      skip i x = Suc x"
by (simp add:skip_def)

lemma skip_im_Tr2_1:"\<lbrakk>i \<in> {i. i \<le> (Suc n)}; i \<le> x\<rbrakk> \<Longrightarrow>
                             skip i x = Suc x"
apply (case_tac "i = 0")
   apply (simp add:skip_def)
apply (simp, rule skip_im_Tr2, assumption+, simp+)
done

lemma skip_im_Tr3:"x \<in> {i. i \<le> n} \<Longrightarrow> skip (Suc n) x = x"
apply (simp add:skip_def)
done

lemma skip_im_Tr4:"\<lbrakk>x \<le> Suc n; 0 < x\<rbrakk> \<Longrightarrow> x - Suc 0 \<le> n"
 apply (simp add:Suc_le_mono [of "x - Suc 0" "n", THEN sym])
done
   
lemma skip_fun_im:"i \<in> {j. j \<le> (Suc n)} \<Longrightarrow> 
              (skip i) ` {j. j \<le> n} = ({j. j \<le> (Suc n)} - {i})"
apply (rule equalityI)
 apply (rule subsetI)
 apply (case_tac "i = 0", simp)
 apply (simp add:image_def, erule exE, erule conjE)
 apply (cut_tac x = xa in skip_im_Tr0[of _ n], simp, simp)
 
 apply (simp add:image_def, erule exE, erule conjE, simp)
 apply (case_tac "xa < i")
 apply (frule_tac x = xa in skip_im_Tr1_2[of i n], simp+)
 apply (cut_tac m1 = xa and n1 = i in nat_not_le_less[THEN sym], simp)
 apply (cut_tac x = xa and n = n in skip_im_Tr2_1[of i], simp+)
 
apply (rule subsetI, simp, erule conjE)
 apply (cut_tac x = x and y = i in less_linear, simp)
 apply (erule disjE)
 apply (simp add:image_def)
 apply (frule_tac x = x in skip_im_Tr1_2[of i n], assumption,
        frule_tac x = x and y = i and z = "Suc n" in less_le_trans, 
        assumption+,
        frule_tac m = x and n = "Suc n" in Suc_leI,
        simp only:Suc_le_mono,
        frule sym, thin_tac "skip i x = x", blast)
 apply (cut_tac x = "x - Suc 0" in skip_im_Tr2_1[of i n],
        simp, simp add:less_le_diff)
 apply (cut_tac x = i and n = x in less_le_diff, assumption,
        simp add:image_def)
 apply (frule_tac m = x and n = "Suc n" and l = "Suc 0" in diff_le_mono,
        simp) 
 apply (frule sym, thin_tac "skip i (x - Suc 0) = x", blast)
done

lemma skip_fun_im1:"\<lbrakk>i \<in> {j. j \<le> (Suc n)}; x \<in> {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
                      (skip i) x \<in> ({j. j \<le> (Suc n)} - {i})"
by (subst skip_fun_im[THEN sym], assumption,
    simp add:image_def, blast)

lemma skip_id:"l < i \<Longrightarrow> skip i l = l"
apply (simp add:skip_def )
 done
   
lemma Suc_neq:"\<lbrakk>0 < i; i - Suc 0 < l\<rbrakk> \<Longrightarrow> i \<noteq> Suc l"
by (rule contrapos_pp, simp+)

lemma skip_il_neq_i:"skip i l \<noteq> i"
apply (auto simp add:skip_def)
done 

lemma skip_inj:"\<lbrakk>i \<in> {k. k \<le> n}; j \<in> {k. k \<le> n}; i \<noteq> j\<rbrakk> \<Longrightarrow> 
                         skip k i \<noteq> skip k j" 
apply (simp add:skip_def) 
done

lemma le_imp_add_int:" i \<le> (j::nat) \<Longrightarrow> \<exists>k. j = i + k"
 apply (case_tac "i = j")
 apply simp
 apply (frule le_imp_less_or_eq) apply (thin_tac "i \<le> j")
 apply simp
 apply (insert less_imp_add_positive [of "i" "j"])
 apply simp
 apply blast
 done

lemma jointfun_hom0:"\<lbrakk> f \<in> {j. j \<le> n} \<rightarrow> A; g \<in> {k. k \<le> m} \<rightarrow> B \<rbrakk> \<Longrightarrow> 
        (jointfun n f m g) \<in> {l. l \<le> (Suc (n + m))} \<rightarrow>  (A \<union> B)"
by (simp add:jointfun_def sliden_def Pi_def)

lemma jointfun_mem:"\<lbrakk>\<forall>j \<le> (n::nat). f j \<in> A; \<forall>j \<le> m. g j \<in> B; 
             l \<le> (Suc (n + m))\<rbrakk> \<Longrightarrow> (jointfun n f m g) l \<in> (A \<union> B)"
apply (rule funcset_mem[of "jointfun n f m g" "{j. j \<le> Suc (n + m)}" "A \<union> B"
       l])
apply (rule jointfun_hom0)
apply simp+
done

lemma jointfun_inj:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow> B; inj_on f {j. j \<le> n};
      b \<notin> f ` {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
      inj_on (jointfun n f 0 (\<lambda>k\<in>{0::nat}. b)) {j. j \<le> Suc n}"
  apply (simp add:inj_on_def, (rule allI, rule impI)+, rule impI)
  apply (case_tac "x = Suc n", simp)
        apply (case_tac "y = Suc n", simp)
        apply (frule_tac m = y and n = "Suc n" in noteq_le_less, assumption)
           apply (
               frule_tac x = y and n = "Suc n" in less_le_diff,
               thin_tac "y < Suc n", thin_tac "y \<le> Suc n", 
               simp add:jointfun_def sliden_def)
      apply (case_tac "y = Suc n", simp,
             frule_tac m = x and n = "Suc n" in noteq_le_less, assumption,
             frule_tac x = x and n = "Suc n" in less_le_diff,
             thin_tac "x < Suc n", thin_tac "x \<le> Suc n", 
             simp add:jointfun_def sliden_def)
      apply (rotate_tac -3, frule sym, thin_tac " f x = b", simp)
      apply (frule_tac m = x and n = "Suc n" in noteq_le_less, assumption,
             frule_tac x = x and n = "Suc n" in less_le_diff,
             thin_tac "x < Suc n", thin_tac "x \<le> Suc n", simp,
             frule_tac m = y and n = "Suc n" in noteq_le_less, assumption,
             frule_tac x = y and n = "Suc n" in less_le_diff,
             thin_tac "y < Suc n", thin_tac "y \<le> Suc n", simp,
             simp add:jointfun_def)
done
      
lemma slide_hom:"i \<le> j \<Longrightarrow> (slide i) \<in> {l. l \<le> (j - i)} \<rightarrow> nset i j"
apply (simp add:Pi_def restrict_def)
apply (rule allI) apply (rule impI)
   apply (simp add:slide_def)
apply (simp add:nset_def)
done

lemma slide_mem:"\<lbrakk> i \<le> j; l \<in> {k. k \<le> (j - i)}\<rbrakk> \<Longrightarrow> slide i l \<in> nset i j"
apply (frule slide_hom)
apply (rule funcset_mem, assumption+)
done

lemma slide_iM:"(slide i) ` {l. 0 \<le> l} = {k. i \<le> k}"
apply (simp add:image_def slide_def)
apply (rule equalityI)
 apply (rule subsetI) 
 apply simp
 apply auto
 apply (rule le_imp_add_int)
 apply assumption
done

lemma jointfun_hom:"\<lbrakk> f \<in> {i. i \<le> n} \<rightarrow> A; g \<in> {j. j \<le> m} \<rightarrow> B \<rbrakk> \<Longrightarrow> 
                   (jointfun n f m g) \<in> {j. j \<le> (Suc (n + m))} \<rightarrow> A \<union> B"
by (simp add:sliden_def Pi_def jointfun_def)

lemma im_jointfunTr1:"(jointfun n f m g) ` {i. i \<le> n} = f ` {i. i \<le> n}"
apply auto
  apply (simp add:jointfun_def)

  apply (simp add:jointfun_def)
 done
 
lemma im_jointfunTr2:"(jointfun n f m g) ` (nset (Suc n) (Suc (n + m))) = 
                       g ` ({j. j \<le> m})"
apply auto
 apply (simp add:nset_def) apply auto
 apply (frule_tac m = xa and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono)
  apply simp
  apply (simp add:jointfun_def sliden_def)

 apply (simp add:image_def)
  apply (cut_tac le_add1[of "n" "m"],
         simp only:Suc_le_mono[THEN sym, of "n" "n+m"])
  apply (frule_tac l = xa in slide_mem[of "Suc n" "Suc (n + m)"])
  apply simp
 apply (subst jointfun_def)
  apply (subgoal_tac "\<forall>i\<in>nset (Suc n) (Suc (n+m)). \<not> (i \<le> n) ")
  apply simp
  apply (thin_tac "\<forall>i\<in>nset (Suc n) (Suc (n + m)). \<not> i \<le> n")
  apply (subgoal_tac "g xa = g (sliden (Suc n) (slide (Suc n) xa))")
  apply blast
  apply (simp add:slide_def sliden_def)
  apply (auto simp add: nset_def)
done

lemma im_jointfun:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow> A; g \<in> {j. j \<le> m} \<rightarrow> B\<rbrakk> \<Longrightarrow> 
    (jointfun n f m g) `({j. j \<le> (Suc (n + m))}) = 
                           f `{j. j \<le> n} \<union> g `{j. j \<le>  m}"
 apply (cut_tac im_set_un1 [of "{j. j \<le> (Suc (n + m))}" "jointfun n f m g" 
        "A \<union> B"  "{i. i \<le> n}" "nset (Suc n) (Suc (n + m))"]) 
 apply (simp add:Nset_nset[THEN sym, of n m],
        simp add:im_jointfunTr1[of n f m g],
        simp add:im_jointfunTr2[of n f m g])
 apply (rule ballI)
 apply (simp add:jointfun_def,
        case_tac "l \<le> n", simp add:Pi_def,
        simp add:sliden_def,
        simp add:nat_not_le_less,
        frule_tac m = n and n = l in Suc_leI,
        frule_tac m = l and n = "Suc (n + m)" and l = "Suc n" in diff_le_mono,
        thin_tac "l \<le> Suc (n + m)", simp,
        simp add:Pi_def)
apply (simp add:Nset_nset[of n m])
done
        
lemma im_jointfun1:"(jointfun n f m g) `({j. j \<le> (Suc (n + m))}) = 
                                      f `{j. j \<le> n} \<union> g ` {j. j \<le> m}"
apply (cut_tac Nset_nset[of "n" "m"])
apply (subst  im_set_un2[of "{j. j \<le> (Suc (n + m))}" "{j. j \<le> n}" 
              "nset (Suc n) (Suc (n + m))" "jointfun n f m g"], assumption)
apply (simp add:im_jointfunTr1 im_jointfunTr2)
done

lemma jointfun_surj:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow> A; surj_to f {j. j \<le> (n::nat)} A; 
      g \<in> {j. j \<le> (m::nat)} \<rightarrow> B; surj_to g {j. j \<le> m} B\<rbrakk> \<Longrightarrow> 
       surj_to (jointfun n f m g) {j. j \<le> Suc (n + m)} (A \<union> B)"
 apply (simp add:surj_to_def [of "jointfun n f m g"])
 apply (simp add:im_jointfun)
 apply (simp add:surj_to_def)
 done

lemma Nset_un:"{j. j \<le> (Suc n)} = {j. j \<le> n} \<union> {Suc n}"
apply (rule equalityI)
apply (rule subsetI)
 apply simp 
 apply auto
done

lemma Nsetn_sub: "{j. j \<le> n} \<subseteq> {j. j \<le> (Suc n)}"
apply (rule subsetI)
apply simp 
done

lemma Nset_pre_sub:"(0::nat) < k \<Longrightarrow> {j. j \<le> (k - Suc 0)} \<subseteq> {j. j \<le> k}"
apply (rule subsetI)
apply simp
done

lemma Nset_pre_un:"(0::nat) < k \<Longrightarrow> {j. j \<le> k} = {j. j \<le> (k - Suc 0)} \<union> {k}"
apply (insert Nset_un [of "k - Suc 0"])
apply simp
done

lemma Nsetn_sub_mem:" l \<in> {j. j \<le> n} \<Longrightarrow> l \<in> {j. j \<le> (Suc n)}"
apply simp
done

lemma Nsetn_sub_mem1:"\<forall>j. j \<in> {j. j \<le> n} \<longrightarrow> j \<in> {j. j \<le> (Suc n)}"
by (simp add:Nsetn_sub_mem)

lemma Nset_Suc:"{j. j \<le> (Suc n)} = insert (Suc n) {j. j \<le> n}"
apply (rule equalityI)
apply (rule subsetI)
apply simp
apply auto
done

lemma nsetnm_sub_mem:"\<forall>j. j \<in>nset n (n + m) \<longrightarrow> j \<in> nset n (Suc (n + m))"
by (rule allI, simp add:nset_def) 

lemma Nset_0:"{j. j \<le> (0::nat)} = {0}"
by simp

lemma Nset_Suc0:"{i. i \<le> (Suc 0)} = {0, Suc 0}"
apply (rule equalityI)
 apply (rule subsetI, simp) 
 apply (case_tac "x = 0", simp) 
 apply simp+
done

lemma Nset_Suc_Suc:"Suc (Suc 0) \<le> n \<Longrightarrow>
       {j. j \<le> (n - Suc (Suc 0))} = {j. j \<le> n} - {n - Suc 0, n}" 
apply (insert Nset_un [of "n - (Suc 0)"])
apply (insert Nset_un [of "n - Suc (Suc 0)"])
apply (subgoal_tac "{j. j \<le> (Suc (n - Suc (Suc 0)))} = {j. j \<le> (n - Suc 0)}")
apply (simp,
       thin_tac "{j. j \<le> n} =
       insert n (insert (Suc (n - Suc (Suc 0))) {j. j \<le> n - Suc (Suc 0)})",
       thin_tac " {j. j \<le> n - Suc 0} =
        insert (Suc (n - Suc (Suc 0))) {j. j \<le> n - Suc (Suc 0)}",
       thin_tac "{j. j \<le> Suc (n - Suc (Suc 0))} =
        insert (Suc (n - Suc (Suc 0))) {j. j \<le> n - Suc (Suc 0)}")
apply (simp add:Suc_Suc_Tr)
apply (auto )
done

lemma func_pre:"f \<in> {j. j \<le> (Suc n)} \<rightarrow> A \<Longrightarrow> f \<in> {j. j \<le> n} \<rightarrow> A"
by (simp add:Pi_def)

lemma image_Nset_Suc:"f ` ({j. j \<le> (Suc n)}) =
                             insert (f (Suc n)) (f ` {j. j \<le> n})"
apply (cut_tac Nset_un[of "n"]) 
apply (frule im_set_un2[of "{j. j \<le> (Suc n)}" "{j. j \<le> n}" "{Suc n}" "f"]) 
apply (simp add:Un_commute)
done

definition
  Nleast :: "nat set \<Rightarrow> nat" where
  "Nleast A = (THE a. (a \<in> A \<and> (\<forall>x\<in>A. a \<le> x)))"  
 
definition
  Nlb :: "[nat set, nat] \<Rightarrow> bool" where
  "Nlb A n \<longleftrightarrow> (\<forall>a\<in>A. n \<le> a)"


primrec ndec_seq :: "[nat set, nat, nat] \<Rightarrow> nat" where
  ndec_seq_0  :"ndec_seq A a 0 = a"
| ndec_seq_Suc:"ndec_seq A a (Suc n) =
                      (SOME b. ((b \<in> A) \<and> b < (ndec_seq A a n)))"

lemma ndec_seq_mem:"\<lbrakk>a \<in> (A::nat set); \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (ndec_seq A a n) \<in> A"
apply (induct_tac n)
 apply simp apply simp
 apply (simp add: not_less [symmetric])
apply (subgoal_tac "\<exists>x\<in>A. x < (ndec_seq A a n)") prefer 2 apply blast
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
 apply (rule someI2_ex) apply blast
apply simp
done

lemma ndec_seqn:"\<lbrakk>a \<in> (A::nat set);\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (ndec_seq A a (Suc n)) < (ndec_seq A a n)"
 apply (frule ndec_seq_mem [of "a" "A" "n"], assumption+)
 apply simp
 apply (simp add: not_less [symmetric])
 apply (subgoal_tac "\<exists>x\<in>A. x < (ndec_seq A a n)") prefer 2 apply simp
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
apply (rule someI2_ex) apply blast
 apply simp
done

lemma ndec_seqn1:"\<lbrakk>a \<in> (A::nat set); \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (ndec_seq A a (Suc n)) \<le> (ndec_seq A a n) - 1"
apply (frule ndec_seqn [of "a" "A" "n"], assumption+,
       thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply (simp del:ndec_seq_Suc)
done

lemma ex_NleastTr:"\<lbrakk>a \<in> (A::nat set); \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (ndec_seq A a n) \<le> (a - n)"
apply (induct_tac n)
 apply simp
apply (frule_tac n = n in ndec_seqn1[of "a" "A"], assumption+)
 apply (subgoal_tac "ndec_seq A a n - 1 \<le> (a - n) - 1") prefer 2
  apply arith 
  apply arith
done

lemma nat_le:"((a::nat) - (a + 1)) \<le> 0"
apply arith
done

lemma ex_Nleast:"(A::nat set) \<noteq> {} \<Longrightarrow> \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x)"
apply (frule nonempty_ex[of "A"], thin_tac "A \<noteq> {}",
       erule exE, rename_tac a)
apply (case_tac "0 \<in> A")
 apply (rule ex_ex1I, subgoal_tac "\<forall>x\<in>A. 0 \<le> a", blast,
        rule ballI, simp)
 apply ((erule conjE)+, 
        subgoal_tac "m \<le> 0", thin_tac "\<forall>x\<in>A. m \<le> x",
        subgoal_tac "y \<le> 0", thin_tac "\<forall>x\<in>A. y \<le> x",
        simp, blast, blast)
apply (rule ex_ex1I)
prefer 2 apply (erule conjE)+
  apply (subgoal_tac "m \<le> y", thin_tac "\<forall>x\<in>A. m \<le> x",
         subgoal_tac "y \<le> m", thin_tac "\<forall>x\<in>A. y \<le> x",
         simp, blast, blast)
apply (rule contrapos_pp, simp, 
       frule_tac a = a and A = A and n = "a + 1" in ex_NleastTr, assumption+)
 apply (subgoal_tac "(a - (a + 1)) \<le> 0")
 prefer 2 apply (rule nat_le)
 apply (frule_tac i = "ndec_seq A a (a + 1)" and j = "a - (a + 1)" and k = 0 in le_trans, assumption+,
        frule_tac a = a and n = "a + 1" in ndec_seq_mem [of _ "A"], 
                                                          assumption+)
 apply (thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))",
        thin_tac "ndec_seq A a (a + 1) \<le> a - (a + 1)",
        thin_tac "a - (a + 1) \<le> 0")
apply simp
done 

lemma Nleast:"(A::nat set) \<noteq> {} \<Longrightarrow> Nleast A \<in> A \<and> (\<forall>x\<in>A. (Nleast A) \<le> x)"
apply (frule ex_Nleast [of "A"])
 apply (simp add:Nleast_def)
 apply (rule theI')
 apply simp
done

subsection "Lemmas for existence of reduced chain."
(* Later some of these lemmas should be removed. *)

lemma jointgd_tool1:" 0 < i \<Longrightarrow> 0 \<le> i - Suc 0"
by arith

lemma jointgd_tool2:" 0 < i \<Longrightarrow> i = Suc (i - Suc 0)"
by arith

lemma jointgd_tool3:"\<lbrakk>0 < i;  i \<le> m\<rbrakk> \<Longrightarrow> i - Suc 0 \<le> (m - Suc 0)"
by arith

lemma jointgd_tool4:"n < i \<Longrightarrow> i - n = Suc( i - Suc n)"
by arith

lemma pos_prec_less:"0 < i \<Longrightarrow> i - Suc 0 < i"
by arith

lemma Un_less_Un:"\<lbrakk>f \<in> {j. j \<le> (Suc n)} \<rightarrow> (X::'a set set); 
        A \<subseteq> \<Union>(f ` {j. j \<le> (Suc n)}); 
       i \<in> {j. j \<le> (Suc n)}; j \<in> {l. l \<le> (Suc n)}; i \<noteq> j \<and> f i \<subseteq> f j\<rbrakk>
       \<Longrightarrow> A \<subseteq> \<Union>(compose {j. j \<le> n} f (skip i) ` {j. j \<le> n})"
apply (simp add:compose_def)
 apply (rule subsetI, simp)
 apply (frule_tac c = x and A = A and B = "\<Union>x\<in>{j. j \<le> Suc n}. f x" in
        subsetD, assumption+, simp)
 apply (erule exE, (erule conjE)+)
 apply (case_tac "xa = i", simp,
        frule_tac c = x in subsetD[of "f i" "f j"], assumption+)
 apply (cut_tac less_linear[of i j], simp, erule disjE,
        frule less_le_diff[of i j],
        cut_tac skip_im_Tr2_1[of i n "j - Suc 0"],
        simp, 
        frule eq_elems_eq_val[THEN sym, of "skip i (j - Suc 0)" j f],
        cut_tac a = x in eq_set_inc[of _ "f j" "f (skip i (j - Suc 0))"],
              assumption+,
        frule le_Suc_diff_le[of j n], blast, simp, assumption, simp)
 apply (frule  skip_im_Tr1_2[of i n j], assumption,
        frule eq_elems_eq_val[THEN sym, of "skip i j" j f])
 apply (cut_tac a = x in eq_set_inc[of _ "f j" "f (skip i j)"],
              assumption+)
 apply (frule_tac x = j and y = i and z = "Suc n" in less_le_trans,
        assumption+,
        frule Suc_less_le[of j n], blast)
 apply (cut_tac x = xa and y = i in less_linear, simp,
        erule disjE,
        frule_tac x = xa in skip_im_Tr1_2[of i n], assumption)
 apply (frule_tac x1 = "skip i xa" and y1 = xa and f1 = f in 
                  eq_elems_eq_val[THEN sym],
        frule_tac a = x and A = "f xa" and B = "f (skip i xa)" in eq_set_inc,
        assumption,
        frule_tac x = xa and y = i and z = "Suc n" in less_le_trans,
        assumption+,
        frule_tac x = xa and n = n in Suc_less_le, blast)
 apply (frule_tac x = i and n = xa in less_le_diff,
        cut_tac x = "xa - Suc 0" and n = n in skip_im_Tr2_1 [of i],
        simp, assumption,
        simp,
        frule_tac x1 = "skip i (xa - Suc 0)" and y1 = xa and f1 = f in 
                  eq_elems_eq_val[THEN sym],
        frule_tac a = x and A = "f xa" and B = "f (skip i (xa - Suc 0))" in 
        eq_set_inc, assumption,
        frule_tac x = xa and n = n in le_Suc_diff_le)
        apply blast
done

section "Lower bounded set of integers"

(* In this section. I prove that a lower bounded set of integers
  has the minimal element *)

definition "Zset = {x. \<exists>(n::int). x = n}"

definition
  Zleast :: "int set \<Rightarrow> int" where
  "Zleast A = (THE a. (a \<in> A \<and> (\<forall>x\<in>A. a \<le> x)))"

definition
  LB :: "[int set, int] \<Rightarrow> bool" where
  "LB A n = (\<forall>a\<in>A. n \<le> a)"

lemma linorder_linear1:"(m::int) < n \<or> n \<le> m"
apply (subgoal_tac "m < n \<or> n = m \<or> n < m")
apply (case_tac "m < n") apply simp apply simp
apply (subgoal_tac "m < n \<or> m = n \<or> n < m") 
apply blast
apply (simp add:less_linear)
done

primrec dec_seq :: "[int set, int, nat] \<Rightarrow> int"
where
  dec_seq_0: "dec_seq A a 0 = a"
| dec_seq_Suc: "dec_seq A a (Suc n) = (SOME b. ((b \<in> A) \<and> b < (dec_seq A a n)))"

lemma dec_seq_mem:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (dec_seq A a n) \<in> A"
apply (induct_tac n)
 apply simp apply simp  apply (simp add:not_zle)
apply (subgoal_tac "\<exists>x\<in>A. x < (dec_seq A a n)") prefer 2 apply blast
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
 apply (rule someI2_ex) apply blast
apply simp
done

lemma dec_seqn:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (dec_seq A a (Suc n)) < (dec_seq A a n)"
apply simp
 apply (frule dec_seq_mem [of "a" "A" "n"], assumption+)
 apply simp
 apply (simp add:not_zle)
 apply (subgoal_tac "\<exists>x\<in>A. x < (dec_seq A a n)") prefer 2 apply simp
 apply (thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. x < m)")
apply (rule someI2_ex) apply blast
 apply simp
done

lemma dec_seqn1:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                       (dec_seq A a (Suc n)) \<le> (dec_seq A a n) - 1"
apply (frule dec_seqn [of "a" "A" "n"], assumption+)
 apply simp
done

lemma lbs_ex_ZleastTr:"\<lbrakk>a \<in> A; A \<subseteq> Zset;\<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x))\<rbrakk> \<Longrightarrow>
                        (dec_seq A a n) \<le> (a - int(n))"
apply (induct_tac n)
 apply simp
apply (frule_tac n = n in dec_seqn1[of "a" "A"], assumption+)
 apply (subgoal_tac "dec_seq A a n - 1 \<le> a - (int n) - 1") prefer 2 
   apply simp apply (thin_tac "dec_seq A a n \<le> a - int n")
 apply (frule_tac x = "dec_seq A a (Suc n)" and y = "dec_seq A a n - 1" and
 z = "a - int n - 1" in order_trans, assumption+)
 apply (thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply (thin_tac "dec_seq A a (Suc n) \<le> dec_seq A a n - 1")
 apply (thin_tac "dec_seq A a n - 1 \<le> a - int n - 1")
apply (subgoal_tac "a - int n - 1 = a - int (Suc n)") apply simp
 apply (thin_tac "dec_seq A a (Suc n) \<le> a - int n - 1")
apply simp
done

lemma big_int_less:"a - int(nat(abs(a) + abs(N) + 1)) < N"
apply (simp add:zabs_def)
done

lemma lbs_ex_Zleast:"\<lbrakk>A \<noteq> {}; A \<subseteq> Zset; LB A n\<rbrakk> \<Longrightarrow> \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x)"
apply (frule nonempty_ex[of "A"])
 apply (thin_tac "A \<noteq> {}")
 apply (erule exE)
 apply (rename_tac a)
apply (rule ex_ex1I)
prefer 2
 apply (thin_tac "LB A n") apply (erule conjE)+
 apply (subgoal_tac "m \<le> y") prefer 2 apply simp
 apply (subgoal_tac "y \<le> m") prefer 2 apply simp
 apply (thin_tac "\<forall>x\<in>A. m \<le> x") apply (thin_tac "\<forall>x\<in>A. y \<le> x")
 apply simp
apply (rule contrapos_pp) apply simp 
 apply (frule_tac a = a and A = A and n = "nat(abs(a) + abs(n) + 1)" in lbs_ex_ZleastTr, assumption+)
 apply (subgoal_tac "a - int(nat(abs(a) + abs(n) + 1)) < n")
 prefer 2 apply (rule big_int_less)
 apply (frule_tac x = "dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))" and y = "a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))" and z = n in order_le_less_trans, assumption+)
 apply (frule_tac a = a and n = "nat (\<bar>a\<bar> + \<bar>n\<bar> + 1)" in dec_seq_mem [of _ "A"], assumption+)
 apply (thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))")
 apply (thin_tac "dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))
           \<le> a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))")
 apply (thin_tac "a - int (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1)) < n")
apply (simp add:LB_def)
 apply (subgoal_tac "n \<le> dec_seq A a (nat (\<bar>a\<bar> + \<bar>n\<bar> + 1))")
 apply (thin_tac "\<forall>a\<in>A. n \<le> a") apply (simp add:not_zle)
 apply blast
done 

lemma Zleast:"\<lbrakk>A \<noteq> {}; A \<subseteq> Zset; LB A n\<rbrakk> \<Longrightarrow> Zleast A \<in> A \<and>
               (\<forall>x\<in>A. (Zleast A) \<le> x)"
apply (frule lbs_ex_Zleast [of "A" "n"], assumption+)
 apply (simp add:Zleast_def)
 apply (rule theI')
 apply simp
done

lemma less_convert1:"\<lbrakk> a = c; a < b \<rbrakk> \<Longrightarrow> c < b"
apply auto
done 

lemma less_convert2:"\<lbrakk>a = b; b < c\<rbrakk> \<Longrightarrow> a < c"
apply auto
done 

section \<open>Augmented integer: integer and \<open>\<infinity>-\<infinity>\<close>\<close>

definition
  zag :: "(int * int) set" where
  "zag = {(x,y) | x y. x * y = (0::int) \<and> (y = -1 \<or> y = 0 \<or> y = 1)}"

definition
  zag_pl::"[(int * int), (int * int)] \<Rightarrow> (int * int)" where
  "zag_pl x y == if (snd x + snd y) = 2 then (0, 1)
                 else if (snd x + snd y) = 1 then (0, 1)
                 else if (snd x + snd y) = 0 then (fst x + fst y, 0)
                 else if (snd x + snd y) = -1 then (0, -1)
                 else if (snd x + snd y) = -2 then (0, -1) else undefined"

definition
  zag_t :: "[(int * int), (int * int)] \<Rightarrow> (int * int)" where
  "zag_t x y = (if (snd x)*(snd y) = 0 then
                     (if 0 < (fst x)*(snd y) + (snd x)*(fst y) then (0,1)
                           else (if (fst x)*(snd y) + (snd x)*(fst y) = 0
                               then ((fst x)*(fst y), 0) else (0, -1)))
            else (if 0 < (snd x)*(snd y) then (0, 1) else (0, -1)))" 

definition "Ainteg = zag"

typedef ant = Ainteg
  morphisms Rep_Ainteg Abs_Ainteg
  unfolding Ainteg_def
proof
  show "(1, 0) \<in> zag" unfolding zag_def by auto
qed

definition
  ant :: "int \<Rightarrow> ant" where
  "ant m = Abs_Ainteg( (m, 0))"

definition
  tna :: "ant \<Rightarrow> int" where
  "tna z = (if Rep_Ainteg(z) \<noteq> (0,1) \<and> Rep_Ainteg(z) \<noteq> (0,-1) then
            fst (Rep_Ainteg(z)) else undefined)"

instantiation ant :: "{zero, one, plus, uminus, minus, times, ord}"
begin

definition
  Zero_ant_def  : "0 == ant 0"

definition
  One_ant_def   : "1 == ant 1"

definition
  add_ant_def:
   "z + w ==
       Abs_Ainteg (zag_pl (Rep_Ainteg z) (Rep_Ainteg w))"

definition
  minus_ant_def : "- z == 
         Abs_Ainteg((- (fst (Rep_Ainteg z)), - (snd (Rep_Ainteg z))))"

definition
    diff_ant_def:  "z - (w::ant) == z + (-w)"

definition 
    mult_ant_def:
      "z * w ==
       Abs_Ainteg (zag_t (Rep_Ainteg z) (Rep_Ainteg w))"

definition
    le_ant_def:
     "(z::ant) \<le> w == if (snd (Rep_Ainteg w)) = 1 then True 
       else (if (snd (Rep_Ainteg w)) = 0 then (if (snd (Rep_Ainteg z)) = 1 
       then False else (if (snd (Rep_Ainteg z)) = 0 then 
        (fst (Rep_Ainteg z)) \<le> (fst (Rep_Ainteg w))  else True))
          else (if snd (Rep_Ainteg z) = -1 then True else False))" 

definition
    less_ant_def: "((z::ant) < (w::ant)) == (z \<le> w \<and> z \<noteq> w)"            

instance ..

end

definition
  inf_ant :: ant  ("\<infinity>") where
  "\<infinity> = Abs_Ainteg((0,1))"

definition
  an :: "nat \<Rightarrow> ant" where
  "an m = ant (int m)"

definition
  na :: "ant \<Rightarrow> nat" where
  "na x = (if (x < 0) then 0 else 
           if x \<noteq> \<infinity> then (nat (tna x)) else undefined)" 

definition
  UBset :: "ant \<Rightarrow> ant set" where
  "UBset z = {(x::ant).  x \<le> z}"

definition
   LBset :: "ant \<Rightarrow> ant set" where
  "LBset z = {(x::ant). z \<le> x}"  

lemma ant_z_in_Ainteg:"(z::int, 0) \<in> Ainteg"
apply (simp add:Ainteg_def zag_def)
done

lemma ant_inf_in_Ainteg:"((0::int), 1) \<in> Ainteg"
apply (simp add:Ainteg_def zag_def)
done

lemma ant_minf_in_Ainteg:"((0::int), -1) \<in> Ainteg"
apply (simp add:Ainteg_def zag_def)
done

lemma ant_0_in_Ainteg:"((0::int), 0) \<in> Ainteg"
apply (simp add:Ainteg_def zag_def)
done

lemma an_0[simp]:"an 0 = 0"
by (simp add:an_def Zero_ant_def)

lemma an_1[simp]:"an 1 = 1"
by (simp add:an_def One_ant_def)

lemma mem_ant:"(a::ant) = -\<infinity> \<or> (\<exists>(z::int). a = ant z) \<or> a = \<infinity>"
apply (case_tac "a = -\<infinity> \<or> a = \<infinity>") 
 apply blast
apply (simp, simp add:ant_def,
       cut_tac Rep_Ainteg[of "a"],
       simp add:Ainteg_def zag_def,
       erule conjE, simp add:inf_ant_def,
       simp add:minus_ant_def,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply auto
apply (cut_tac Rep_Ainteg[of "a"],
       subgoal_tac "Abs_Ainteg (Rep_Ainteg a) = Abs_Ainteg ((0,-1))",
       thin_tac "Rep_Ainteg a = (0, -1)",
       simp add:Rep_Ainteg_inverse, simp)
apply (cut_tac Rep_Ainteg[of "a"],
       subgoal_tac "Abs_Ainteg (Rep_Ainteg a) = Abs_Ainteg ((0,0))",
       thin_tac "Rep_Ainteg a = (0, 0)",
       simp add:Rep_Ainteg_inverse, blast, simp)
apply (cut_tac Rep_Ainteg[of "a"],
       subgoal_tac "Abs_Ainteg (Rep_Ainteg a) = Abs_Ainteg ((0,1))",
       thin_tac "Rep_Ainteg a = (0, 1)",
       simp add:Rep_Ainteg_inverse, simp)
apply (cut_tac Rep_Ainteg[of "a"],
       subgoal_tac "Abs_Ainteg (Rep_Ainteg a) = Abs_Ainteg ((x,0))",
       thin_tac "Rep_Ainteg a = (x, 0)",
       simp add:Rep_Ainteg_inverse, blast, simp)
done

lemma minf:"-\<infinity> = Abs_Ainteg((0,-1))"
apply (simp add:inf_ant_def minus_ant_def,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
done

lemma z_neq_inf[simp]:"(ant z) \<noteq> \<infinity> "
apply (rule contrapos_pp, simp+)
apply (simp add:ant_def inf_ant_def)
apply (subgoal_tac "Rep_Ainteg (Abs_Ainteg (z,0)) = 
                      Rep_Ainteg (Abs_Ainteg (0,1))",
       thin_tac "Abs_Ainteg (z, 0) = Abs_Ainteg (0, 1)",
       cut_tac ant_z_in_Ainteg[of "z"],
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply simp
done

lemma z_neq_minf[simp]:"(ant z) \<noteq> -\<infinity>"
apply (rule contrapos_pp, simp+)
apply (subgoal_tac "ant (-z) = \<infinity>")
apply (cut_tac z_neq_inf[of "- z"], simp)
apply (simp add:ant_def inf_ant_def minus_ant_def)
apply (cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (subgoal_tac "- Abs_Ainteg (z, 0) = - Abs_Ainteg (0, -1)",
       thin_tac "Abs_Ainteg (z, 0) = Abs_Ainteg (0, -1)",
       simp add:minus_ant_def,
       cut_tac ant_z_in_Ainteg[of "z"],
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply simp
done

lemma minf_neq_inf[simp]:"-\<infinity> \<noteq> \<infinity>"
apply (cut_tac ant_inf_in_Ainteg,
       simp add:inf_ant_def minus_ant_def Abs_Ainteg_inverse)
apply (rule contrapos_pp, simp+,
       subgoal_tac "Rep_Ainteg (Abs_Ainteg (0,-1)) = 
                     Rep_Ainteg (Abs_Ainteg (0,1))",
       thin_tac "Abs_Ainteg (0, -1) = Abs_Ainteg (0, 1)",
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply simp
done


lemma a_ipi[simp]:"\<infinity> + \<infinity> = \<infinity>"
apply (simp add:add_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:zag_pl_def)
done

lemma a_zpi[simp]:"(ant z) + \<infinity>  = \<infinity>"
apply (simp add:add_ant_def inf_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "z"],
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:zag_pl_def)
done

lemma a_ipz[simp]:" \<infinity> + (ant z) = \<infinity>"
apply (simp add:add_ant_def inf_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "z"],
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:zag_pl_def)
done

lemma a_zpz:"(ant m) + (ant n) = ant (m + n)"
apply (simp add:add_ant_def inf_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "m"],
       cut_tac ant_z_in_Ainteg[of "n"],
       simp add:Abs_Ainteg_inverse,
       simp add:zag_pl_def)
done

lemma a_mpi[simp]:"-\<infinity> + \<infinity>  = 0"
apply (simp add:add_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse,
       simp add:Zero_ant_def ant_def zag_pl_def)
done

lemma a_ipm[simp]:"\<infinity> + (-\<infinity>) = 0"
apply (simp add:add_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse,
       simp add:Zero_ant_def ant_def zag_pl_def)
done

lemma a_mpm[simp]:"-\<infinity> + (-\<infinity>) = -\<infinity>"
apply (simp add:add_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse,
       simp add:Zero_ant_def ant_def zag_pl_def)
done

lemma a_mpz[simp]:"-\<infinity> + (ant m) = -\<infinity>"
apply (simp add:add_ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:ant_def,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse) 
apply (simp add:zag_pl_def)
done

lemma a_zpm[simp]:"(ant m) + (-\<infinity>) = -\<infinity>"
apply (simp add:add_ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:ant_def,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse) 
apply (simp add:zag_pl_def)
done

lemma a_mdi[simp]:"-\<infinity> - \<infinity>  = - \<infinity>"
apply (simp add:diff_ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (simp add:add_ant_def,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse, simp add:zag_pl_def)
done

lemma a_zdz:"(ant m) - (ant n) = ant (m - n)"
apply (simp add:diff_ant_def minus_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "n"],
       simp add:Abs_Ainteg_inverse)
apply (simp add:add_ant_def,
       cut_tac ant_z_in_Ainteg[of "m"],
       cut_tac ant_z_in_Ainteg[of "-n"],
       simp add:Abs_Ainteg_inverse zag_pl_def)
done

lemma a_i_i[simp]:"\<infinity> * \<infinity> = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def) 
done

lemma a_0_i[simp]:"0 * \<infinity> = 0"
by (simp add:mult_ant_def inf_ant_def Zero_ant_def, simp add:ant_def,
    cut_tac ant_inf_in_Ainteg, cut_tac ant_0_in_Ainteg,
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_i_0[simp]:"\<infinity> * 0 = 0"
by (simp add:mult_ant_def inf_ant_def Zero_ant_def, simp add:ant_def,
    cut_tac ant_inf_in_Ainteg, cut_tac ant_0_in_Ainteg,
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_0_m[simp]:"0 * (-\<infinity>) = 0"
by (simp add:mult_ant_def inf_ant_def Zero_ant_def, simp add:ant_def,
    cut_tac ant_inf_in_Ainteg, cut_tac ant_0_in_Ainteg, 
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_m_0[simp]:"(-\<infinity>) * 0 = 0"
by (simp add:mult_ant_def inf_ant_def Zero_ant_def, simp add:ant_def,
    cut_tac ant_inf_in_Ainteg, cut_tac ant_0_in_Ainteg, 
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_m_i[simp]:"(-\<infinity>) * \<infinity> = -\<infinity>"
by (simp add:mult_ant_def inf_ant_def minus_ant_def,
       cut_tac ant_inf_in_Ainteg, cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_i_m[simp]:"\<infinity> * (-\<infinity>) = - \<infinity>"
by (simp add:mult_ant_def inf_ant_def minus_ant_def,
       cut_tac ant_inf_in_Ainteg, cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse, simp add:zag_t_def) 

lemma a_pos_i[simp]:"0 < m \<Longrightarrow> (ant m) * \<infinity> = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def ant_def, 
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_i_pos[simp]:"0 < m \<Longrightarrow> \<infinity> * (ant m) = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def ant_def, 
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_neg_i[simp]:"m < 0 \<Longrightarrow> (ant m) * \<infinity> = -\<infinity>"
apply (simp add:mult_ant_def inf_ant_def ant_def, 
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_i_neg[simp]:"m < 0 \<Longrightarrow> \<infinity> * (ant m) = -\<infinity>"
apply (simp add:mult_ant_def inf_ant_def ant_def, 
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done


lemma a_z_z:"(ant m) * (ant n) = ant (m*n)"
apply (simp add:mult_ant_def ant_def, 
       cut_tac ant_z_in_Ainteg[of "m"],
       cut_tac ant_z_in_Ainteg[of "n"],
       simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_pos_m[simp]:"0 < m \<Longrightarrow> (ant m) * (-\<infinity>) = -\<infinity>"
apply (simp add:mult_ant_def inf_ant_def minus_ant_def ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "m"],
      simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)  
done

lemma a_m_pos[simp]:"0 < m \<Longrightarrow> (-\<infinity>) * (ant m) = -\<infinity>"
apply (simp add:mult_ant_def inf_ant_def minus_ant_def ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "m"],
      simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_neg_m[simp]:"m < 0 \<Longrightarrow> (ant m) * (-\<infinity>) = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def minus_ant_def ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "m"],
      simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma neg_a_m[simp]:"m < 0 \<Longrightarrow> (-\<infinity>) * (ant m) = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def minus_ant_def ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "m"],
      simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done

lemma a_m_m[simp]:"(-\<infinity>) * (-\<infinity>) = \<infinity>"
apply (simp add:mult_ant_def inf_ant_def minus_ant_def ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      simp add:Abs_Ainteg_inverse)
apply (simp add:zag_t_def)
done


lemma inj_on_Abs_Ainteg:"inj_on Abs_Ainteg Ainteg"
apply (simp add:inj_on_def)
apply (rule ballI)+
apply (rule impI,
       subgoal_tac "Rep_Ainteg (Abs_Ainteg x) = Rep_Ainteg (Abs_Ainteg y)",
       thin_tac "Abs_Ainteg x = Abs_Ainteg y",
       simp add:Abs_Ainteg_inverse, simp)
done

lemma an_Suc:"an (Suc n) = an n + 1"
    apply (subst an_1[THEN sym])
    apply (simp del:an_1 add:an_def) 
    apply (simp del:an_1 add:a_zpz, simp add:add.commute)
done

lemma aeq_zeq [iff]: "(ant m = ant n) = (m = n)"
apply (rule iffI)
apply (subgoal_tac "Rep_Ainteg (ant m) = Rep_Ainteg (ant n)",
       thin_tac "ant m = ant n",
       cut_tac ant_z_in_Ainteg[of "m"],
       cut_tac ant_z_in_Ainteg[of "n"],
       simp add:ant_def Abs_Ainteg_inverse)
apply simp+
done

lemma aminus:"- ant m = ant (-m)"
apply (simp add:ant_def minus_ant_def,
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse)
done

lemma aminusZero:"- ant 0 = ant 0"
apply (simp add:aminus)
done

lemma  ant_0: "ant 0 = (0::ant)"
by (simp add: Zero_ant_def)

lemma inf_neq_0[simp]:"\<infinity> \<noteq> 0"
apply (cut_tac z_neq_inf[of "0"], frule not_sym)
apply (simp add:ant_0)
done

lemma zero_neq_inf[simp]:"0 \<noteq> \<infinity>"
by (cut_tac inf_neq_0, frule not_sym, simp)

lemma minf_neq_0[simp]:"-\<infinity> \<noteq> 0"
apply (cut_tac z_neq_minf[of "0"], frule not_sym)
apply (simp add:ant_0)
done

lemma zero_neq_minf[simp]:"0 \<noteq> -\<infinity>"
by (cut_tac minf_neq_0, frule not_sym, simp)

lemma a_minus_zero[simp]:"-(0::ant) = 0"
by (cut_tac aminusZero, simp add:ant_0)

lemma a_minus_minus: "- (- z) = (z::ant)"
apply (cut_tac mem_ant[of "z"])
apply (erule disjE, simp add:minf, simp add: minus_ant_def,
       cut_tac ant_minf_in_Ainteg,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (erule disjE) apply (erule exE, simp add:aminus)
apply (simp add:minf, simp add: minus_ant_def,
       cut_tac ant_minf_in_Ainteg,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:inf_ant_def)
done

lemma aminus_0: "- (- 0) = (0::ant)"
apply (simp add:a_minus_minus)
done

lemma a_a_z_0:"\<lbrakk> 0 < z; a * ant z = 0\<rbrakk> \<Longrightarrow> a = 0"
by (rule contrapos_pp, simp+, cut_tac mem_ant[of "a"], erule disjE, 
       simp, erule disjE, erule exE, simp add:a_z_z, 
       simp only:ant_0[THEN sym], simp, simp)

lemma adiv_eq:"\<lbrakk> z \<noteq> 0; a * (ant z) = b * (ant z)\<rbrakk> \<Longrightarrow> a = b"
apply (cut_tac mem_ant[of "a"], cut_tac mem_ant[of "b"],
      (erule disjE)+, simp, erule disjE, erule exE,
       cut_tac less_linear[of "z" "0"], erule disjE, simp add:a_z_z,
       frule sym, thin_tac "\<infinity> = ant (za * z)", simp,
       simp add:a_z_z, frule sym, thin_tac "- \<infinity> = ant (za * z)", simp,
       cut_tac less_linear[of "z" "0"], erule disjE, simp,
       simp, erule disjE, erule exE)
apply (erule disjE,
        cut_tac less_linear[of "z" "0"], simp,
        erule disjE, simp add:a_z_z, simp add:a_z_z,
        erule disjE, erule exE, simp add:a_z_z,
        cut_tac less_linear[of "z" "0"], simp,
        erule disjE, simp add:a_z_z, simp add:a_z_z,
        erule disjE,
        cut_tac less_linear[of "z" "0"], simp,
        erule disjE, simp+)
apply (erule disjE, erule exE, simp add:a_z_z,
        cut_tac less_linear[of "z" "0"], simp, erule disjE, simp,
        frule sym, thin_tac "- \<infinity> = ant (za * z)", simp,
        simp, frule sym, thin_tac "\<infinity> = ant (za * z)", simp,
        cut_tac less_linear[of "z" "0"], simp) 
done

lemma aminus_add_distrib: "- (z + w) = (- z) + (- w::ant)"
apply (cut_tac mem_ant[of "z"], cut_tac mem_ant[of "w"],
       (erule disjE)+, simp add:a_minus_minus,
       erule disjE, erule exE, simp,
       simp add:a_minus_minus aminus, simp add:a_minus_minus) 
apply ((erule disjE)+, erule exE, 
       simp add:a_minus_minus, simp add:aminus,
       simp add:a_minus_minus) 
apply ((erule disjE)+, (erule exE)+, simp add:a_zpz aminus,
      erule exE, simp add:aminus,
      erule disjE, erule exE, simp add:aminus, simp)
done

lemma aadd_commute:"(x::ant) + y = y + x"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"])
apply (erule disjE, erule disjE, simp,
      erule disjE, erule exE, simp+,
      (erule disjE)+, erule exE, simp+)
apply ((erule disjE)+, (erule exE)+, simp add:a_zpz, 
      erule exE, simp, erule disjE, erule exE, simp+)
done

definition
  aug_inf :: "ant set"  ("Z\<^sub>\<infinity>") where
  "Z\<^sub>\<infinity> = {(z::ant). z \<noteq> -\<infinity> }" 

definition
  aug_minf :: "ant set"  ("Z\<^sub>-\<^sub>\<infinity>") where
  "Z\<^sub>-\<^sub>\<infinity> = {(z::ant). z \<noteq> \<infinity> }"

lemma z_in_aug_inf:"ant z \<in> Z\<^sub>\<infinity>"
apply (simp add:aug_inf_def)
done

lemma Zero_in_aug_inf:"0 \<in> Z\<^sub>\<infinity>"
by (simp only:Zero_ant_def, simp add: aug_inf_def)

lemma z_in_aug_minf:"ant z \<in> Z\<^sub>-\<^sub>\<infinity>"
by (simp add:aug_minf_def)

lemma mem_aug_minf:"a \<in> Z\<^sub>-\<^sub>\<infinity> \<Longrightarrow> a = - \<infinity> \<or> (\<exists>z. a = ant z)" 
by (cut_tac mem_ant[of a], simp add:aug_minf_def)

lemma minus_an_in_aug_minf:" - an n \<in>  Z\<^sub>-\<^sub>\<infinity>" 
apply (simp add:an_def)
apply (simp add:aminus)
apply (simp add:z_in_aug_minf)
done

lemma Zero_in_aug_minf:"0 \<in> Z\<^sub>-\<^sub>\<infinity>"
by (simp add:Zero_ant_def aug_minf_def)

lemma aadd_assoc_i: "\<lbrakk>x \<in> Z\<^sub>\<infinity>; y \<in> Z\<^sub>\<infinity>; z \<in> Z\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
apply (cut_tac mem_ant[of "x"], 
       cut_tac mem_ant[of "y"], 
       cut_tac mem_ant[of "z"], simp add:aug_inf_def,
      (erule disjE)+, (erule exE)+, (simp add:a_zpz)+,
      (erule exE)+, simp add:a_zpz)
apply ((erule disjE)+, (erule exE)+, simp,
        erule exE, simp,
      (erule disjE)+, (erule exE)+, simp add:a_zpz,
      erule exE, simp, erule disjE, erule exE, simp)
apply simp
done

lemma aadd_assoc_m: "\<lbrakk>x \<in> Z\<^sub>-\<^sub>\<infinity>; y \<in> Z\<^sub>-\<^sub>\<infinity>; z \<in> Z\<^sub>-\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> 
                                 (x + y) + z = x + (y + z)"
apply (cut_tac mem_ant[of "x"], 
       cut_tac mem_ant[of "y"], 
       cut_tac mem_ant[of "z"], simp add:aug_minf_def )
apply ((erule disjE)+, simp, erule exE, simp,
       erule disjE, erule exE, simp, (erule exE)+, simp add:a_zpz)
apply ((erule disjE)+, erule exE, simp, (erule exE)+, simp,
        erule disjE, erule exE, simp, erule exE, simp add:a_zpz)
apply ((erule exE)+, simp add:a_zpz)
done

lemma aadd_0_r: "x + (0::ant) = x"
apply (cut_tac mem_ant[of "x"], simp add:Zero_ant_def)
apply ((erule disjE)+, simp)
apply (erule disjE, erule exE, simp add:a_zpz,
       simp)
done

lemma aadd_0_l: "(0::ant) + x = x"
apply (cut_tac mem_ant[of "x"], simp add:Zero_ant_def)
apply ((erule disjE)+, simp)
apply (erule disjE, erule exE, simp, simp add:a_zpz, simp)
done

lemma aadd_minus_inv: "(- x) + x = (0::ant)"  (** \<longrightarrow> aadd_minus_l **)
apply (cut_tac mem_ant[of "x"],
       erule disjE, simp add:a_minus_minus,
       erule disjE, erule exE, simp add:aminus, simp add:a_zpz,
       simp add:Zero_ant_def, simp)
done

lemma aadd_minus_r: "x + (- x) = (0::ant)"
apply (cut_tac  aadd_minus_inv[of "x"])
apply (simp add:aadd_commute)
done

lemma ant_minus_inj:"ant z \<noteq> ant w \<Longrightarrow> - ant z \<noteq> - ant w"
by (simp add:aminus) 

lemma aminus_mult_minus: "(- (ant z)) * (ant w) = - ((ant z) * (ant w))"
apply (simp add:ant_def minus_ant_def,
       cut_tac ant_z_in_Ainteg[of "z"],
       cut_tac ant_z_in_Ainteg[of "-z"],
       cut_tac ant_z_in_Ainteg[of "w"],
       simp add:Abs_Ainteg_inverse)
apply (simp add:mult_ant_def) apply (simp add:Abs_Ainteg_inverse,
       simp add:zag_t_def,
       cut_tac ant_z_in_Ainteg[of "z * w"])
apply (simp add:Abs_Ainteg_inverse)
done

lemma amult_commute: "(x::ant) * y = y * x"
apply (cut_tac mem_ant[of "x"],
       cut_tac mem_ant[of "y"])
apply (erule disjE, erule disjE, simp)
apply (erule disjE, erule exE, simp)
apply (cut_tac x = 0 and y = z in less_linear)
apply (erule disjE, simp) 
apply (erule disjE, rotate_tac -1, frule sym, thin_tac "0 = z", simp)
apply (simp add:inf_ant_def ant_def, simp add:minus_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_z_in_Ainteg[of "0"],
       cut_tac ant_z_in_Ainteg[of "-1"], 
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (simp add:mult_ant_def, simp add:Abs_Ainteg_inverse,
       simp add:zag_t_def, simp)
apply (simp add:inf_ant_def)
apply (simp add:mult_ant_def minus_ant_def,
        cut_tac ant_inf_in_Ainteg,
        simp add:Abs_Ainteg_inverse,
        cut_tac ant_minf_in_Ainteg,
        simp add:Abs_Ainteg_inverse, simp add:zag_t_def)
apply (erule disjE, erule disjE, simp)
apply (erule exE,
       cut_tac x = 0 and y = z in less_linear)
apply (erule disjE, simp)
apply (erule disjE, rotate_tac -1, thin_tac "0 = z", simp add:mult_ant_def,
      simp add:ant_def inf_ant_def minus_ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac z = z in ant_z_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      simp add:Abs_Ainteg_inverse, simp add:zag_t_def,
      simp)
apply (simp add:inf_ant_def minus_ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac z = z in ant_z_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      simp add:Abs_Ainteg_inverse,
      simp add:mult_ant_def,
      simp add:Abs_Ainteg_inverse, simp add:zag_t_def)
apply ((erule disjE)+, (erule exE)+, simp add:a_z_z)
apply (erule exE,
       cut_tac  x = 0 and y = z in less_linear,
       erule disjE, simp)
apply (erule disjE, rotate_tac -1, frule sym, thin_tac "0 = z", simp,
      simp add:mult_ant_def ant_def inf_ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "0"],
      simp add:Abs_Ainteg_inverse, simp add:zag_t_def,
      simp)
apply (erule disjE, erule exE,
       cut_tac  x = 0 and y = z in less_linear,
       erule disjE, simp,
      erule disjE, rotate_tac -1, frule sym, thin_tac "0 = z", simp,
      simp add:mult_ant_def ant_def inf_ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_z_in_Ainteg[of "0"],
      simp add:Abs_Ainteg_inverse, simp add:zag_t_def,
      simp+) 
done

lemma z_le_i[simp]:"(ant x) \<le> \<infinity> "
apply (simp add:le_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "0"],
       cut_tac ant_z_in_Ainteg[of "x"],
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:inf_ant_def,
       simp add:Abs_Ainteg_inverse)
done

lemma z_less_i[simp]:"(ant x) < \<infinity> "
apply (cut_tac z_le_i[of "x"],
       cut_tac z_neq_inf[of "x"],
       simp add:less_ant_def)
done

lemma m_le_z:"-\<infinity> \<le> (ant x) "
apply (simp add:le_ant_def ant_def,
       cut_tac ant_z_in_Ainteg[of "0"],
       cut_tac ant_z_in_Ainteg[of "x"],
       cut_tac ant_minf_in_Ainteg,
       cut_tac ant_inf_in_Ainteg,
       simp add:Abs_Ainteg_inverse,
       simp add:inf_ant_def,
       simp add:minus_ant_def,
       simp add:Abs_Ainteg_inverse)
done

lemma m_less_z[simp]:"-\<infinity> < (ant x)"
apply (cut_tac m_le_z[of "x"],
       cut_tac z_neq_minf[of "x"],
       frule not_sym, thin_tac "ant x \<noteq> - \<infinity>",
       simp add:less_ant_def)
done

lemma noninf_mem_Z:"\<lbrakk>x \<in> Z\<^sub>\<infinity>; x \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> \<exists>(z::int). x = ant z"
apply (simp add:aug_inf_def)
apply (cut_tac mem_ant[of "x"], simp)
done

lemma z_mem_Z:"ant z \<in> Z\<^sub>\<infinity>" 
by (simp add:aug_inf_def)

lemma inf_ge_any[simp]:"x \<le> \<infinity>"
apply (cut_tac mem_ant[of "x"], erule disjE)
 apply (simp add:inf_ant_def minus_ant_def,
        cut_tac ant_minf_in_Ainteg,
        cut_tac ant_inf_in_Ainteg,
        simp add:Abs_Ainteg_inverse,
        simp add:le_ant_def, simp add:Abs_Ainteg_inverse)
 apply (erule disjE, erule exE, simp)
 apply (simp add:inf_ant_def,
        cut_tac ant_inf_in_Ainteg,
        simp add:le_ant_def, simp add:Abs_Ainteg_inverse)
done

lemma zero_lt_inf:"0 < \<infinity>"
by (simp add:less_ant_def)

lemma minf_le_any[simp]:"-\<infinity> \<le> x"
apply (cut_tac mem_ant[of "x"], erule disjE)
 apply (simp add:inf_ant_def minus_ant_def,
        cut_tac ant_minf_in_Ainteg,
        cut_tac ant_inf_in_Ainteg,
        simp add:Abs_Ainteg_inverse,
        simp add:le_ant_def, simp add:Abs_Ainteg_inverse)
 apply (erule disjE, erule exE, simp)
 apply (simp add:inf_ant_def, simp add:minus_ant_def,
        cut_tac ant_inf_in_Ainteg,
        cut_tac ant_minf_in_Ainteg,
        simp add:le_ant_def, simp add:Abs_Ainteg_inverse)
 apply simp
done

lemma minf_less_0:"-\<infinity> < 0"
by (simp add:less_ant_def)

lemma ale_antisym[simp]:"\<lbrakk>(x::ant) \<le> y; y \<le> x \<rbrakk> \<Longrightarrow> x = y"
apply (rule contrapos_pp, simp+)
apply (cut_tac  mem_ant[of "x"], cut_tac  mem_ant[of "y"])
apply (erule disjE, erule disjE, simp)
apply (erule disjE, erule exE, simp, simp add:ant_def,
      simp add:minus_ant_def inf_ant_def,
      cut_tac ant_inf_in_Ainteg,
      cut_tac ant_minf_in_Ainteg,
      cut_tac z = z in ant_z_in_Ainteg, simp add:Abs_Ainteg_inverse,
      simp add:le_ant_def Abs_Ainteg_inverse)
apply (thin_tac "x \<le> y",
       simp add:le_ant_def ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply (erule disjE, erule disjE, erule exE,
       thin_tac "y \<le> x",
       simp add:le_ant_def ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       cut_tac z = z in ant_z_in_Ainteg, simp add:Abs_Ainteg_inverse)
apply (thin_tac "y \<le> x",
       simp add:le_ant_def ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       simp add:Abs_Ainteg_inverse)
apply ((erule disjE)+, (erule exE)+,
       cut_tac z = z in ant_z_in_Ainteg,
       cut_tac z = za in ant_z_in_Ainteg,
       simp add:le_ant_def ant_def,
       simp add:Abs_Ainteg_inverse) 
apply (erule exE, 
        simp add:le_ant_def ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac z = z in ant_z_in_Ainteg, simp add:Abs_Ainteg_inverse)
apply (erule disjE, erule exE, thin_tac "y \<le> x",
       simp add:le_ant_def ant_def minus_ant_def inf_ant_def,
       cut_tac ant_inf_in_Ainteg,
       cut_tac ant_minf_in_Ainteg,
       cut_tac z = z in ant_z_in_Ainteg, simp add:Abs_Ainteg_inverse)
apply simp
done

lemma x_gt_inf[simp]:"\<infinity> \<le> x \<Longrightarrow> x = \<infinity>"
apply (cut_tac inf_ge_any[of "x"],
       rule ale_antisym[of "x" "\<infinity>"], assumption+)
done

lemma Zinf_pOp_closed:"\<lbrakk>x \<in> Z\<^sub>\<infinity>; y \<in> Z\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> x + y \<in> Z\<^sub>\<infinity>"
apply (cut_tac  mem_ant[of "x"], cut_tac  mem_ant[of "y"],
       simp add:aug_inf_def,
      (erule disjE)+, (erule exE)+, simp add:a_zpz,
       cut_tac z = "-(z + za)" in z_neq_inf,
       rule contrapos_pp, simp+,
       cut_tac m1 = "z+za" in aminus[THEN sym], simp add:a_minus_minus,
       erule exE, simp, simp add:minf_neq_inf[THEN not_sym],
       erule disjE, erule exE, simp, 
       simp add:minf_neq_inf[THEN not_sym],
       simp)
done

lemma Zminf_pOp_closed:"\<lbrakk>x \<in> Z\<^sub>-\<^sub>\<infinity>; y \<in> Z\<^sub>-\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> x + y \<in> Z\<^sub>-\<^sub>\<infinity>"
apply (cut_tac  mem_ant[of "x"], cut_tac  mem_ant[of "y"],
       simp add:aug_minf_def,
      (erule disjE)+, simp, erule exE, simp,
       erule disjE, erule exE, simp,
      (erule exE)+, simp add:a_zpz)
done

lemma amult_distrib1:"(ant z) \<noteq> 0 \<Longrightarrow> 
             (a + b) * (ant z) = a * (ant z) + b * (ant z)"
apply (cut_tac mem_ant[of "a"], cut_tac mem_ant[of "b"],
     (erule disjE)+, simp, cut_tac less_linear[of "z" "0"], 
      erule disjE, simp, erule disjE, simp, simp add:ant_0, simp,
      erule disjE, erule exE, simp,
      cut_tac less_linear[of "z" "0"], 
      erule disjE, simp add:a_z_z, erule disjE, simp add:ant_0,
      simp add:a_z_z,
      cut_tac less_linear[of "z" "0"], simp,
      erule disjE, simp add:ant_0[THEN sym] a_z_z)
apply (erule disjE, simp add:ant_0[THEN sym],
       simp, simp add:ant_0[THEN sym], simp add:a_z_z,
       (erule disjE)+, (erule exE)+, cut_tac less_linear[of "z" "0"], simp,
       erule disjE, simp add:a_z_z,
       erule disjE, simp add:ant_0, simp add:a_z_z,
       cut_tac less_linear[of "z" "0"],
       erule disjE, simp add:ant_0[THEN sym])
apply (simp add:a_z_z, simp, 
       erule disjE, simp add:ant_0, simp add:ant_0[THEN sym] a_z_z,
      (erule disjE)+, (erule exE)+, simp add:a_zpz a_z_z,
       simp add: distrib_right, erule exE, simp add:a_z_z,
       cut_tac less_linear[of "z" "0"], erule disjE, simp,
       erule disjE, simp add:ant_0, simp)
apply (erule disjE, erule exE, simp, 
       cut_tac less_linear[of "z" "0"], erule disjE, simp add:a_z_z,
       erule disjE, simp add:ant_0, simp add:a_z_z,
       cut_tac less_linear[of "z" "0"], erule disjE, simp,
       erule disjE, simp add:ant_0, simp)
done

lemma amult_0_r:"(ant z) * 0 = 0"
by (simp add:ant_0[THEN sym] a_z_z)

lemma amult_0_l:"0 * (ant z) = 0"
by (simp add:ant_0[THEN sym] a_z_z)
 

definition
  asprod :: "[int, ant] \<Rightarrow> ant" (infixl "*\<^sub>a" 200) where
  "m *\<^sub>a x == 
  if x = \<infinity> then (if 0 < m then \<infinity> else (if m < 0 then -\<infinity> else 
                 if m = 0 then 0 else undefined))
    else (if x = -\<infinity> then 
                    (if 0 < m then -\<infinity> else (if m < 0 then \<infinity> else 
                 if m = 0 then 0 else undefined))
          else (ant m) * x)"

lemma asprod_pos_inf[simp]:"0 < m \<Longrightarrow> m *\<^sub>a \<infinity> = \<infinity>"
apply (simp add:asprod_def)
done

lemma asprod_neg_inf[simp]:"m < 0 \<Longrightarrow> m *\<^sub>a \<infinity> = -\<infinity>"
apply (simp add:asprod_def)
done

lemma asprod_pos_minf[simp]:"0 < m \<Longrightarrow> m *\<^sub>a (-\<infinity>) = (-\<infinity>)"
apply (simp add:asprod_def)
done

lemma asprod_neg_minf[simp]:"m < 0 \<Longrightarrow> m *\<^sub>a (-\<infinity>) = \<infinity>"
apply (simp add:asprod_def)
done

lemma asprod_mult:" m *\<^sub>a (ant n) = ant(m * n)"
apply (cut_tac z_neq_inf[of "n"],
       cut_tac z_neq_minf[of "n"],
       simp add:asprod_def, simp add:a_z_z)
done

lemma asprod_1:"1 *\<^sub>a x = x"
by (cut_tac mem_ant[of "x"], erule disjE, simp,
       erule disjE, erule exE, simp add:asprod_mult, simp)
(** atode asprod_1_x to awaseru **)

lemma agsprod_assoc_a:"m *\<^sub>a (n *\<^sub>a (ant x)) = (m * n) *\<^sub>a (ant x)"
apply (simp add:asprod_mult)
done

lemma agsprod_assoc:"\<lbrakk>m \<noteq> 0; n \<noteq> 0\<rbrakk> \<Longrightarrow> m *\<^sub>a (n *\<^sub>a x) = (m * n) *\<^sub>a x"
apply (cut_tac less_linear[of "m" "0"], cut_tac less_linear[of "n" "0"],
       cut_tac mem_ant[of "x"],
      (erule disjE)+, simp,
      frule zmult_neg_neg[of "m" "n"], assumption+, simp)
apply (erule disjE, erule exE, simp add:asprod_mult,
      frule zmult_neg_neg[of "m" "n"], assumption+, simp+,
      erule disjE, simp,
      frule zmult_neg_pos[of "m" "n"], assumption+, simp,
      erule disjE, erule exE, simp,
      frule zmult_neg_pos[of "m" "n"], assumption+, simp add:asprod_mult,
      frule zmult_neg_pos[of "m" "n"], assumption+, simp)      
apply (simp, (erule disjE)+,
      frule zmult_pos_neg[of "m" "n"], assumption+,
      simp,
      erule disjE, erule exE, simp add:asprod_mult,
      frule zmult_pos_neg[of "m" "n"], assumption+, simp) 
apply (frule zmult_pos_pos[of "m" "n"], assumption+,
      erule disjE, simp,
      erule disjE, erule exE, simp add:asprod_mult, simp)
done

lemma asprod_distrib1:"m \<noteq> 0 \<Longrightarrow> m *\<^sub>a (x + y) = (m *\<^sub>a x) + (m *\<^sub>a y)"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"])
apply (cut_tac less_linear[of "m" "0"], 
      erule disjE,
      erule disjE, erule disjE, simp,
      erule disjE, simp add:asprod_def  add_ant_def, simp,
      simp, (erule disjE)+, erule exE, simp add:asprod_mult,
      simp add:Zero_ant_def asprod_mult)
apply (erule disjE, erule exE, simp add:asprod_mult,
      simp add: Zero_ant_def asprod_mult,
      erule disjE, erule disjE, erule disjE, erule exE,
      simp add:asprod_mult,
      simp add:Zero_ant_def asprod_mult,
      erule disjE, erule exE, simp add:asprod_mult,
      simp add:Zero_ant_def asprod_mult)
apply (simp, erule disjE, erule exE, simp,
      (erule disjE)+, erule exE, simp add:asprod_mult,
      simp add:a_zpz, simp add:asprod_mult distrib_left,
      simp add:asprod_mult)
apply (erule disjE, erule exE, simp add:a_zpz asprod_mult,
       simp add: distrib_left, simp add:asprod_mult,
      (erule disjE)+, erule exE, simp add:asprod_mult, simp,
      erule disjE, erule exE, simp add:asprod_mult, simp) 
done

lemma asprod_0_x[simp]:"0 *\<^sub>a x = 0"
 apply (simp add:asprod_def, (rule impI)+,
        cut_tac mem_ant[of "x"], simp, erule exE,
        simp add:asprod_def a_z_z, simp add:ant_0)
done

lemma asprod_n_0:"n *\<^sub>a 0 = 0"
apply (simp add:Zero_ant_def asprod_mult)
done

lemma asprod_distrib2:"\<lbrakk>0 < i; 0 < j\<rbrakk> \<Longrightarrow> (i + j) *\<^sub>a x = (i *\<^sub>a x) + (j *\<^sub>a x)"
by (cut_tac mem_ant[of "x"], erule disjE, simp,
       erule disjE, erule exE, simp add:asprod_mult,
       simp add: distrib_right a_zpz, simp)

lemma asprod_minus:"x \<noteq> -\<infinity> \<and> x \<noteq> \<infinity> \<Longrightarrow> - z *\<^sub>a x = z *\<^sub>a (- x)"
apply (cut_tac mem_ant[of "x"], erule disjE, simp+)
apply (erule exE, simp add:asprod_mult aminus)
done

lemma asprod_div_eq:"\<lbrakk>n \<noteq> 0; n *\<^sub>a x = n *\<^sub>a y\<rbrakk> \<Longrightarrow> x = y"
apply (cut_tac less_linear[of "n" "0"], simp)
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"])
apply ((erule disjE)+, simp,
      erule disjE, erule exE, rule contrapos_pp, simp+,
      simp add:asprod_mult)
apply (cut_tac z1 = "n * z" in z_neq_inf[THEN not_sym], simp+)
apply ((erule disjE)+, erule exE, simp add:asprod_mult,
       cut_tac z = "n * z" in z_neq_inf,
       rule contrapos_pp, simp, simp,
      (erule disjE)+, (erule exE)+, simp add:asprod_mult,
       erule exE, simp add: asprod_mult)
apply (erule disjE, erule exE, simp add:asprod_mult,
      simp add:z_neq_minf[THEN not_sym], simp)
apply ((erule disjE)+, simp,
      erule disjE, erule exE, rule contrapos_pp, simp+,
      simp add:asprod_mult,
      cut_tac z1 = "n * z" in z_neq_minf[THEN not_sym], simp,
      rule contrapos_pp, simp+)
apply ((erule disjE)+, (erule exE)+, simp add:asprod_mult,
      erule exE, simp add:asprod_mult,
      erule disjE, erule exE, simp add:asprod_mult
      z_neq_inf[THEN not_sym], simp)
apply (erule disjE, simp, erule disjE, erule exE, simp add:asprod_mult
        z_neq_inf[THEN not_sym], simp)
done

lemma asprod_0:"\<lbrakk>z \<noteq> 0; z *\<^sub>a x = 0 \<rbrakk> \<Longrightarrow> x = 0"
by (rule asprod_div_eq[of "z" "x" "0"], assumption, simp add:asprod_n_0)

lemma asp_z_Z:"z *\<^sub>a ant x \<in> Z\<^sub>\<infinity>" 
by (simp add:asprod_mult z_in_aug_inf)

lemma tna_ant:" tna (ant z) = z"
apply (cut_tac z_neq_minf[of "z"], cut_tac z_neq_inf[of "z"],
       simp add:ant_def tna_def)
apply (cut_tac ant_z_in_Ainteg[of "z"], simp add:Abs_Ainteg_inverse)
done

lemma ant_tna:"x \<noteq> \<infinity> \<and> x \<noteq> -\<infinity> \<Longrightarrow>  ant (tna x) = x"
apply (cut_tac mem_ant[of "x"], simp, erule exE)
apply (simp add:ant_def tna_def)
apply (cut_tac z = z in ant_z_in_Ainteg, simp add:Abs_Ainteg_inverse)
done

lemma ant_sol:"\<lbrakk>a \<in> Z\<^sub>\<infinity>; b \<in> Z\<^sub>\<infinity>; c \<in> Z\<^sub>\<infinity>; b \<noteq> \<infinity>; a = b + c\<rbrakk> \<Longrightarrow> a - b = c" 
apply (subgoal_tac "-b \<in> Z\<^sub>\<infinity>", simp add:diff_ant_def,
       subgoal_tac "a + (-b) = b + c + (-b)",
       subst aadd_commute[of "b" "c"], subst aadd_assoc_i, assumption+,
       simp add:aadd_minus_r, simp add:aadd_0_r, simp)
apply (cut_tac mem_ant[of "b"], simp add:aug_inf_def,
       erule exE, simp add:aminus)
done

subsection "Ordering of integers and ordering nats"

subsection \<open>The \<open>\<le>\<close> Ordering\<close>

lemma zneq_aneq:"(n \<noteq> m) = ((ant n) \<noteq> (ant m))" 
apply (rule iffI)
 apply (rule contrapos_pp, simp+)
done

lemma ale:"(n \<le> m) = ((ant n) \<le>(ant m))" 
apply (rule iffI)
apply (simp add:ant_def le_ant_def,
       cut_tac ant_z_in_Ainteg[of "n"],
       cut_tac ant_z_in_Ainteg[of "m"],
       simp add:Abs_Ainteg_inverse)+
done

lemma aless:"(n < m) = ((ant n) < (ant m))" 
apply (simp add:less_ant_def,
       cut_tac ale[of "n" "m"], arith)
done

lemma ale_refl: "w \<le> (w::ant)"
apply (cut_tac mem_ant[of "w"],
       erule disjE, simp,
       erule disjE, erule exE, simp,
       subst ale[THEN sym], simp+)
done 

lemma aeq_ale:"(a::ant) = b \<Longrightarrow> a \<le> b"
by (simp add:ale_refl)

lemma ale_trans: "\<lbrakk> (i::ant) \<le> j; j \<le> k \<rbrakk> \<Longrightarrow> i \<le> k"
apply (cut_tac mem_ant[of "i"], cut_tac mem_ant[of "j"], 
       cut_tac mem_ant[of "k"],
      (erule disjE)+, simp add:ale_refl, erule disjE, erule exE, simp+,
      (erule disjE)+, simp add:ale_refl, simp add:ale_refl)
apply ((erule disjE)+, erule exE, simp+,
  erule exE, simp,
       cut_tac x = "ant z" in minf_le_any,
       frule_tac x = "ant z" in ale_antisym[of _ "-\<infinity>"], assumption+,
       simp+,
       cut_tac minf_le_any[of "\<infinity>"], frule ale_antisym[of "-\<infinity>" "\<infinity>"],
       simp+)
apply (erule disjE, simp,
       (erule disjE)+, (erule exE)+, simp,
       cut_tac x = "ant za" in minf_le_any,
       frule_tac x = "ant za" in ale_antisym[of _ "-\<infinity>"], assumption+,
       simp, erule exE,
       cut_tac x = "ant z" in minf_le_any, simp) 
apply (cut_tac minf_le_any[of "\<infinity>"], 
       frule_tac ale_antisym[of "-\<infinity>" "\<infinity>"], assumption+,
       simp, erule disjE, erule exE, simp,
       cut_tac x = "ant z" in inf_ge_any, 
       frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], assumption+,
       simp)
apply (cut_tac minf_le_any[of "\<infinity>"], frule ale_antisym[of "-\<infinity>" "\<infinity>"],
       simp+,
       (erule disjE)+, (erule exE)+, simp add:ale[THEN sym],
       simp, (erule disjE)+, (erule exE)+,
       cut_tac x = "ant za" in inf_ge_any,
       frule_tac x = "ant za" in ale_antisym[of _ "\<infinity>"],
       simp+)
apply (erule disjE, erule exE,
       cut_tac inf_ge_any[of "j"],
       frule ale_antisym[of "j" "\<infinity>"], assumption+,
       cut_tac x = "ant z" in inf_ge_any, simp+) 
done

(* Axiom 'order_aless_le_not_le' of class 'order': *)
lemma aless_le_not_le: "((w::ant) < z) = (w \<le> z \<and> \<not> z \<le> w)"
by (auto simp add: less_ant_def) 

instance ant :: order
proof qed 
 (assumption |
  rule ale_refl ale_trans ale_antisym aless_le_not_le)+

(* Axiom 'linorder_linear' of class 'linorder': *)
lemma ale_linear: "(z::ant) \<le> w \<or> w \<le> z"
apply (cut_tac mem_ant[of "z"], cut_tac mem_ant[of "w"],
       erule disjE, simp,
       erule disjE, simp)
apply ((erule disjE)+, (erule exE)+, simp add:ale[THEN sym],
       simp add:linorder_linear)
apply simp+
done

instance ant :: linorder
proof qed (rule ale_linear)

lemmas aless_linear = less_linear [where 'a = ant]


lemma ant_eq_0_conv [simp]: "(ant n = 0) = (n = 0)"
apply (simp add:Zero_ant_def)
done

lemma aless_zless: "(ant m < ant n) = (m<n)"
by (simp add: ale ant_def linorder_not_le [symmetric]) 

lemma a0_less_int_conv [simp]: "(0 < ant n) = (0 < n)"
apply (simp add:Zero_ant_def)
apply (simp add:aless[THEN sym])
done

lemma a0_less_1: "0 < (1::ant)"
apply (simp add:Zero_ant_def One_ant_def) 
apply (subst aless_zless) apply simp
done 

lemma a0_neq_1 [simp]: "0 \<noteq> (1::ant)"
by (simp only:Zero_ant_def One_ant_def, subst zneq_aneq[THEN sym], simp)

lemma ale_zle [simp]: "((ant i) \<le> (ant j)) = (i\<le>j)"
by (subst ale[of "i" "j"], simp)

lemma ant_1 [simp]: "ant 1 = 1"
by (simp add: One_ant_def)

lemma zpos_apos:"(0 \<le> n) = (0 \<le> (ant n))"
apply (simp only:ale[of "0" "n"], simp only:ant_0[THEN sym]) 
done

lemma zposs_aposss:"(0 < n) = (0 < (ant n))"
apply (rule iffI)
 apply (unfold Zero_ant_def,
        subst aless[THEN sym, of "0" "n"], simp,
        subst aless[of "0" "n"], simp)
done

lemma an_nat_pos[simp]:"0 \<le> an n"
by (simp add:ant_0[THEN sym] an_def) 

lemma amult_one_l:" 1 * (x::ant) = x"
by (cut_tac mem_ant[of "x"], erule disjE, simp 
       only:ant_1[THEN sym], simp del:ant_1,
       erule disjE, erule exE, simp only:ant_1[THEN sym],
       simp del:ant_1 add:a_z_z,
       simp only:ant_1[THEN sym], simp del:ant_1)

lemma amult_one_r:"(x::ant)* 1 = x"
by (cut_tac amult_one_l[of "x"], simp add:amult_commute)

lemma amult_eq_eq_r:"\<lbrakk>z \<noteq> 0;  a * ant z = b * ant z\<rbrakk> \<Longrightarrow> a = b"
apply (cut_tac less_linear[of "z" "0"], simp,
       cut_tac mem_ant[of "a"], cut_tac mem_ant[of "b"],
       (erule disjE)+, simp,
      erule disjE, erule exE, simp add:a_z_z,
      frule sym, thin_tac "\<infinity> = ant (za * z)", simp,
      simp, (erule disjE)+, simp, erule exE, simp add:a_z_z, simp)
apply ((erule disjE)+, (erule exE)+, simp add:a_z_z,
      erule exE, simp add:a_z_z, erule disjE, erule exE, 
      simp add:a_z_z,
      frule sym, thin_tac "- \<infinity> = ant (za * z)", simp, simp,
      (erule disjE)+, simp, erule disjE, erule exE, simp add:a_z_z,
      frule sym, thin_tac "- \<infinity> = ant (za * z)", simp, simp)
apply ((erule disjE)+, erule exE, simp add:a_z_z, simp,
       (erule disjE)+, (erule exE)+, simp add:a_z_z,
       erule exE, simp add:a_z_z, erule disjE, erule exE, simp add:a_z_z,
       frule sym, thin_tac "\<infinity> = ant (za * z)", simp, simp)
done

lemma amult_eq_eq_l:"\<lbrakk>z \<noteq> 0;  (ant z) * a = (ant z) * b\<rbrakk> \<Longrightarrow> a = b"
by (simp add:amult_commute, rule amult_eq_eq_r, assumption+)

lemma amult_pos:"\<lbrakk>0 < b; 0 \<le> x\<rbrakk>  \<Longrightarrow> x \<le> (b *\<^sub>a x)" 
apply (cut_tac mem_ant[of "x"], erule disjE, simp,
       erule disjE, erule exE, simp add:asprod_mult,
       simp add:zpos_apos[THEN sym],
       frule_tac a = z and b = b in pos_zmult_pos, assumption+,
       simp add:mult.commute, simp)
done

lemma asprod_amult:"0 < z \<Longrightarrow> z *\<^sub>a x = (ant z) * x"
apply (simp add:asprod_def)
done

lemma amult_pos1:"\<lbrakk>0 < b; 0 \<le> x\<rbrakk>  \<Longrightarrow> x \<le> ((ant b) * x)" 
by (frule amult_pos[of "b" "x"], assumption, simp add:asprod_amult)

lemma amult_pos_mono_l:"0 < w \<Longrightarrow> (((ant w) * x) \<le> ((ant w) * y)) =  (x \<le> y)"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"],
      (erule disjE)+, simp, erule disjE, erule exE, simp, simp,
      (erule disjE)+, erule exE, simp add:a_z_z)
apply (rule iffI,
       cut_tac x = "ant (w * z)" in minf_le_any, frule_tac x = "ant (w * z)"
       in ale_antisym, assumption+, simp,
       cut_tac x = "ant z" in minf_le_any, frule_tac x = "ant z"
       in ale_antisym, assumption+, simp) 
 apply simp
apply ((erule disjE)+, (erule exE)+, simp add:a_z_z)
apply (erule exE, simp add:a_z_z)
apply (erule disjE, erule exE, simp add:a_z_z,
       rule iffI,
       cut_tac x = "ant (w * z)" in inf_ge_any, 
       frule_tac x = "ant (w * z)" in ale_antisym[of _ "\<infinity>"], assumption+,
       simp,
       cut_tac x = "ant z" in inf_ge_any, 
       frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], assumption+,
       simp, simp)
done

lemma amult_pos_mono_r:"0 < w \<Longrightarrow> ((x * (ant w)) \<le> (y * (ant w))) =  (x \<le> y)"
apply (simp add:amult_commute[of _ "ant w"])
apply (rule amult_pos_mono_l, assumption)
done

lemma apos_neq_minf:"0 \<le> a \<Longrightarrow> a \<noteq> -\<infinity>"
by (rule contrapos_pp, simp+,
       cut_tac minf_le_any[of "0"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+, simp)

lemma asprod_pos_mono:"0 < w \<Longrightarrow> ((w *\<^sub>a x) \<le> (w *\<^sub>a y)) =  (x \<le> y)"
by (simp add:asprod_amult, simp add:amult_pos_mono_l)

lemma a_inv:"(a::ant) + b = 0 \<Longrightarrow> a = -b"
apply (cut_tac mem_ant[of "a"], cut_tac mem_ant[of "b"],
       (erule disjE)+, frule sym, thin_tac "a + b = 0", 
       simp add:ant_0[THEN sym])
apply (erule disjE, erule exE, simp, simp,
      (erule disjE)+, erule exE, simp, simp,
      simp add:a_minus_minus,
      (erule disjE)+, (erule exE)+, simp add:aminus a_zpz,
      erule exE, simp,
      erule disjE, erule exE, simp, simp) 
done 

lemma asprod_pos_pos:"0 \<le> x \<Longrightarrow> 0 \<le> int n *\<^sub>a x" 
apply (cases "n = 0")
apply simp_all
using asprod_pos_mono [THEN sym, of "int n" "0" "x"]
apply (simp add:asprod_n_0)
done

lemma asprod_1_x[simp]:"1 *\<^sub>a x = x"
apply (simp add:asprod_def)
apply (rule impI)+
apply (cut_tac mem_ant[of "x"], simp, erule exE, simp add:a_z_z)
apply (simp only:ant_1[THEN sym], simp del:ant_1 add:a_z_z)
done

lemma asprod_n_1[simp]:"n *\<^sub>a 1 = ant n"
apply (simp only:ant_1[THEN sym]) apply (simp only:asprod_mult)
apply simp
done

subsection "Aug ordering"

lemma aless_imp_le:" x < (y::ant) \<Longrightarrow> x \<le> y"
by (simp add:less_ant_def)

lemma gt_a0_ge_1:"(0::ant) < x \<Longrightarrow> 1 \<le> x"
apply (cut_tac mem_ant[of "x"],
       erule disjE, unfold Zero_ant_def, simp)
apply (cut_tac less_ant_def[of "0" "-\<infinity>"], simp add:ant_0,
       cut_tac minf_le_any[of "0"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+,
       simp add:ant_0[THEN sym], blast)
apply (erule disjE, erule exE, unfold One_ant_def, simp del:ant_1,
       simp add:aless_zless, simp)
done  

lemma gt_a0_ge_aN:"\<lbrakk>0 < x; N \<noteq> 0\<rbrakk>  \<Longrightarrow> (ant (int N)) \<le> (int N) *\<^sub>a x"
 apply (cut_tac mem_ant[of "x"], erule disjE, simp) 
 apply (cut_tac aless_imp_le[of "0" "-\<infinity>"],
        cut_tac minf_le_any[of "0"], 
      frule ale_antisym[of "0" "-\<infinity>"], simp,
      simp only: Zero_ant_def, simp)
 apply (erule disjE, erule exE, simp add:asprod_mult, simp)
done

lemma aless_le_trans:"\<lbrakk>(x::ant) < y; y \<le> z\<rbrakk> \<Longrightarrow> x < z"
by auto

lemma ale_less_trans:"\<lbrakk>(x::ant) \<le> y; y < z\<rbrakk> \<Longrightarrow> x < z"
by auto

lemma aless_trans:"\<lbrakk>(x::ant) < y; y < z\<rbrakk> \<Longrightarrow> x < z"
by auto

lemma ale_neq_less:"\<lbrakk> (x::ant)\<le> y; x \<noteq> y\<rbrakk> \<Longrightarrow> x < y" 
apply (simp add:less_ant_def)
done

lemma aneg_le:"(\<not> (x::ant) \<le> y) = (y  <  x)"
apply (cut_tac ale_linear[of "y" "x"])
apply (rule iffI, simp) 
apply (rule contrapos_pp, simp+) 
done

lemma aneg_less:"(\<not> x < (y::ant)) = (y \<le> x)"
by auto

lemma aadd_le_mono:"x \<le> (y::ant) \<Longrightarrow> x + z \<le> y + z"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"], 
       cut_tac mem_ant[of "z"],
       (erule disjE)+, simp, erule disjE, erule exE, simp+,
      (erule disjE)+, erule exE, simp+,
      (erule disjE)+, (erule exE)+, simp, erule exE, simp,
       erule disjE, erule exE, simp+, (erule disjE)+, simp, 
       erule exE, simp+,
       cut_tac minf_le_any[of "\<infinity>"], frule ale_antisym[of "-\<infinity>" "\<infinity>"],
       assumption+, simp, (erule disjE)+, (erule exE)+, simp+,
       cut_tac x = "ant za" in minf_le_any,
       frule_tac x = "ant za" in ale_antisym[of _ "-\<infinity>"], assumption+, simp)
apply (erule exE, simp,
       cut_tac x = "ant za" in minf_le_any,
       frule_tac x = "ant za" in ale_antisym[of _ "-\<infinity>"], assumption+, simp,
       erule disjE, erule exE, simp+,
       cut_tac minf_le_any[of "\<infinity>"], frule ale_antisym[of "-\<infinity>" "\<infinity>"],
       assumption+, simp, (erule disjE)+, (erule exE)+, simp+,
       erule exE, simp, erule disjE, erule exE, simp+)
apply (cut_tac x = "ant za" in inf_ge_any, frule_tac x = "ant za" in 
       ale_antisym[of _ "\<infinity>"], assumption+, simp+,
      (erule disjE)+, (erule exE)+, simp add:a_zpz,
      (erule exE)+, simp add:a_zpz, (erule disjE)+, (erule exE)+,
      simp add:a_zpz, erule exE, simp,
      (erule disjE)+, (erule exE)+, simp add:a_zpz)
apply (cut_tac x = "ant za" in inf_ge_any, frule_tac x = "ant za" in 
       ale_antisym[of _ "\<infinity>"], assumption+, simp+,
       erule exE, simp, erule disjE, erule exE, simp+)
done

lemma aadd_less_mono_z:"(x::ant) < y \<Longrightarrow> (x + (ant z)) < (y + (ant z))"
apply (simp add:less_ant_def, simp add:aadd_le_mono)
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"])
apply auto
apply (metis a_inv a_ipi a_ipz a_zpz aadd_minus_r less_le diff_ant_def minf_less_0)
apply (metis a_inv a_ipi a_ipz a_zpz aadd_minus_r less_le diff_ant_def minf_less_0)
apply (metis a_zpz add_right_cancel aeq_zeq)
apply (metis a_zpz less_le z_less_i)
done

lemma aless_le_suc[simp]:"(a::ant) < b \<Longrightarrow> a + 1 \<le> b" 
apply (cut_tac mem_ant[of "b"])
apply (erule disjE,
       frule aless_imp_le[of "a" "b"], simp,
       cut_tac minf_le_any[of "a"], frule ale_antisym[of "a" "-\<infinity>"],
       assumption, simp)
apply (erule disjE, erule exE, cut_tac mem_ant[of "a"], erule disjE, 
       unfold One_ant_def, simp del:ant_1,
       erule disjE, erule exE, simp del:ant_1 add:a_zpz, simp only:aless_zless,
       frule aless_imp_le[of "a" "b"], simp del:ant_1, simp) 
done

lemma aposs_le_1:"(0::ant) < x \<Longrightarrow> 1 \<le> x"
apply (frule aless_le_suc[of "0" "x"],
       simp add:aadd_0_l)
done

lemma pos_in_aug_inf:"(0::ant) \<le> x \<Longrightarrow> x \<in> Z\<^sub>\<infinity>"
apply (simp add:aug_inf_def)
apply (rule contrapos_pp, simp+)
apply (cut_tac minf_le_any[of "0"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+,
       unfold Zero_ant_def,
       simp )
done

lemma aug_inf_noninf_is_z:"\<lbrakk>x \<in> Z\<^sub>\<infinity>; x \<noteq> \<infinity>\<rbrakk> \<Longrightarrow> \<exists>z. x = ant z"
apply (cut_tac mem_ant[of "x"], simp add:aug_inf_def)
done

lemma aadd_two_pos:"\<lbrakk>0 \<le> (x::ant); 0 \<le> y\<rbrakk> \<Longrightarrow> 0 \<le> x + y"
apply (cut_tac Zero_in_aug_inf,
       cut_tac pos_in_aug_inf[of "x"],
       cut_tac pos_in_aug_inf[of "y"])
apply (cut_tac aadd_le_mono[of "0" "x" "y"], simp add:aadd_0_l,
       assumption+)       
done

lemma aadd_pos_poss:"\<lbrakk>(0::ant) \<le> x; 0 < y\<rbrakk> \<Longrightarrow> 0 < (x + y)"
 apply (frule aless_imp_le[of "0" "y"],
        subst less_ant_def, rule conjI, simp add:aadd_two_pos,
        rule contrapos_pp, simp+)
 apply (cut_tac Zero_in_aug_inf,
        cut_tac pos_in_aug_inf[of "x"],
        cut_tac pos_in_aug_inf[of "y"],
        case_tac "y = \<infinity>", simp,
        cut_tac mem_ant[of "x"], erule disjE,
        simp add:aug_inf_def)
 apply (erule disjE, erule exE, simp, simp,
        case_tac "x = \<infinity>", unfold Zero_ant_def, 
        frule aug_inf_noninf_is_z[of "y"], assumption, erule exE,
        simp, frule sym, thin_tac "\<infinity> = ant 0", simp)
 apply (thin_tac "ant 0 \<le> y",
        frule aug_inf_noninf_is_z[of "x"], assumption, erule exE,
        frule aug_inf_noninf_is_z[of "y"], assumption, erule exE,
        simp add:a_zpz, simp add: aless_zless)
 apply (simp add:aless_imp_le)+
done

lemma aadd_poss_pos:"\<lbrakk>(0::ant) < x; 0 \<le> y\<rbrakk> \<Longrightarrow> 0 < (x + y)"
apply (subst aadd_commute, rule aadd_pos_poss, assumption+)
done

lemma aadd_pos_le:"0 \<le> (a::ant) \<Longrightarrow> b \<le> a + b"
apply (cut_tac mem_ant[of "a"], (erule disjE)+,
       simp, cut_tac minf_le_any[of "0"], frule ale_antisym[of "0" "-\<infinity>"],
       assumption+, simp) 
apply (erule disjE, erule exE,
      simp, thin_tac "a = ant z", cut_tac mem_ant[of "b"],
      erule disjE, simp,
      erule disjE, erule exE, simp add:a_zpz, simp only:ant_0[THEN sym], 
      simp only:ale, simp+)
apply (cut_tac mem_ant[of "b"],
      erule disjE, simp,
      erule disjE, erule exE, simp, simp)
done     

lemma aadd_poss_less:"\<lbrakk>b \<noteq> \<infinity>; b \<noteq> -\<infinity>; 0 < a\<rbrakk>  \<Longrightarrow> b < a + b" 
apply (cut_tac mem_ant[of "b"], simp)
apply (erule exE,
       cut_tac mem_ant[of "a"], erule disjE, simp,
       thin_tac "a = - \<infinity>", 
       cut_tac minf_le_any[of "0"],
       frule aless_imp_le[of "0" "-\<infinity>"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+,
       simp only:ant_0[THEN sym], simp)
apply (erule disjE, erule exE, simp add:a_zpz,
       subst aless[THEN sym], simp, simp)
done

lemma ale_neg:"(0::ant) \<le> x \<Longrightarrow> (- x) \<le> 0"
apply (frule pos_in_aug_inf[of "x"])
 apply (case_tac "x = \<infinity>", simp,
        frule aug_inf_noninf_is_z[of "x"], assumption, erule exE,
        simp add:aminus, unfold Zero_ant_def,
        simp only:ale_zle)
done

lemma ale_diff_pos:"(x::ant) \<le> y \<Longrightarrow> 0 \<le> (y - x)"
apply (case_tac "y = -\<infinity>", simp,
       cut_tac minf_le_any[of "x"],
       frule ale_antisym[of "x" "-\<infinity>"], assumption+, 
       simp add:diff_ant_def a_minus_minus,
       cut_tac mem_ant[of "y"], simp, thin_tac "y \<noteq> - \<infinity>",
       erule disjE, erule exE)
apply (case_tac "x = \<infinity>", simp,
       cut_tac x = "ant z" in inf_ge_any,
       frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], simp+,
      cut_tac mem_ant[of "x"], simp+, erule disjE,
      simp add:diff_ant_def a_minus_minus)
apply (erule exE, simp add:a_zdz, unfold Zero_ant_def,
       simp only:ale_zle,
       cut_tac mem_ant[of "x"], erule disjE, 
       simp add:diff_ant_def a_minus_minus,
       erule disjE, erule exE, simp add:diff_ant_def aminus,
       simp add:diff_ant_def ant_0)
done

lemma aless_diff_poss:"(x::ant) < y \<Longrightarrow> 0 < (y - x)"
apply (case_tac "y = -\<infinity>", simp,
       cut_tac minf_le_any[of "x"],
       frule less_imp_le[of "x" "-\<infinity>"],
       frule antisym[of "x" "-\<infinity>"], assumption+, 
       cut_tac less_le[of "x" "-\<infinity>"], simp) 
apply (case_tac "x = -\<infinity>", simp,
       case_tac "y = \<infinity>", simp add:diff_ant_def a_minus_minus,
       simp add:zero_lt_inf,
       cut_tac mem_ant[of "y"], simp, erule exE, simp add:diff_ant_def
        a_minus_minus, simp add:zero_lt_inf)
apply (case_tac "x = \<infinity>", simp,
       frule aless_imp_le[of "\<infinity>" "y"], 
       cut_tac inf_ge_any[of "y"], frule ale_antisym[of "y" "\<infinity>"],
       assumption+, simp,
       cut_tac mem_ant[of "x"], simp, erule exE,
       case_tac "y = \<infinity>", simp add:diff_ant_def aminus,
       simp add:zero_lt_inf)
apply (cut_tac mem_ant[of "y"], simp, erule exE, simp,
       simp add:diff_ant_def, simp add:aminus a_zpz, 
       simp add:aless_zless)
done

lemma ale_minus:" (x::ant) \<le> y \<Longrightarrow> - y \<le> - x"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"])
 apply ((erule disjE)+, simp, erule disjE, erule exE, 
        simp add:aminus a_minus_minus, simp add:a_minus_minus,
 (erule disjE)+, (erule exE)+,
  simp, cut_tac x = "ant z" in minf_le_any, frule_tac x = "ant z" in 
  ale_antisym[of _ "-\<infinity>"], assumption+, simp,
  simp, cut_tac x = \<infinity> in minf_le_any, 
  frule_tac x = \<infinity> in ale_antisym[of _ "-\<infinity>"], assumption+, simp)
 apply ((erule disjE)+, (erule exE)+, simp add:aminus, erule exE, simp,
        erule disjE, erule exE, simp, cut_tac x = "ant z" in inf_ge_any, 
        frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], assumption+, simp,
        simp)
done

lemma aless_minus:"(x::ant) < y \<Longrightarrow> - y < - x"
by (simp add:less_ant_def, erule conjE, simp add:ale_minus,
       rule not_sym, rule contrapos_pp, simp+,
       cut_tac a_minus_minus[of "x"], simp add:a_minus_minus)

lemma aadd_minus_le:"(a::ant) \<le> 0 \<Longrightarrow> a + b \<le> b"
apply (frule ale_minus[of "a" "0"],
       cut_tac aadd_pos_le[of "-a" "-b"], simp add:aminus_0)
apply (frule ale_minus[of "-b" "-a + -b"], simp add:aminus_add_distrib,
       simp add:a_minus_minus, simp add:aminus_0)
done

lemma aadd_minus_less:"\<lbrakk>b \<noteq> -\<infinity> \<and> b \<noteq> \<infinity>; (a::ant) < 0\<rbrakk> \<Longrightarrow> a + b < b"
apply (simp add:less_ant_def, erule conjE,
       simp add:aadd_minus_le)
apply (rule contrapos_pp, simp+,
      cut_tac mem_ant[of "a"], cut_tac mem_ant[of "b"],
      simp, erule disjE, erule exE, simp, 
      frule sym, thin_tac "- \<infinity> = ant z", simp,
      erule disjE, (erule exE)+, simp add:a_zpz,
      erule exE, simp, frule sym, thin_tac "\<infinity> = ant z", simp)
done

lemma an_inj:"an n = an m \<Longrightarrow> n = m"
apply (simp add:an_def)
done 

lemma nat_eq_an_eq:"n = m \<Longrightarrow> an n = an m"
apply simp
done

lemma aneq_natneq:"(an n \<noteq> an m) = (n \<noteq> m)"
apply (simp add:an_def)
done 

lemma ale_natle:" (an n \<le> an m) = (n \<le> m)"
apply (simp add:an_def)
done

lemma aless_natless:"(an n < an m) = (n < m)"
apply (simp add:an_def)
apply (simp add:aless_zless)
done

lemma na_an:"na (an n) = n"
by (simp only:na_def an_def,
       subgoal_tac "\<not> ant (int n) < 0", simp,
       simp add:tna_ant, subst aneg_less[of "ant (int n)" "0"],
       simp only:ant_0[THEN sym], subst ale_zle[of "0" "int n"], simp)

lemma asprod_ge:
  "0 < b \<Longrightarrow> N \<noteq> 0 \<Longrightarrow> an N \<le> int N *\<^sub>a b" 
apply (frule aposs_le_1[of "b"])
apply simp
using asprod_pos_mono [THEN sym, of "int N" "1" "b"]
apply (simp only: ant_1 [THEN sym], simp add: asprod_amult, simp add:an_def)
done

lemma an_npn:"an (n + m) = an n + an m"
by (unfold an_def, simp add:a_zpz)

lemma an_ndn:"n \<le> m \<Longrightarrow> an (m - n) = an m - an n"
apply (cut_tac an_npn[of "m - n" n], simp)
apply (unfold an_def)
 apply (simp add:a_zpz[of "int (m - n)" "int n"]) 
 apply (subst a_zdz[of "int (m - n) + int n" "int n"], simp)
done

section "Amin, amax"

definition
  amin :: "[ant, ant] \<Rightarrow> ant" where
  "amin x y = (if (x \<le> y) then x else y)"
  
definition
  amax :: "[ant, ant] \<Rightarrow> ant" where
  "amax x y = (if (x \<le> y) then y else x)"

primrec Amin :: "[nat, nat \<Rightarrow> ant] \<Rightarrow> ant"
where
  Amin_0 :  "Amin 0 f = (f 0)"
| Amin_Suc :"Amin (Suc n) f = amin (Amin n f) (f (Suc n))"

primrec Amax :: "[nat, nat \<Rightarrow> ant] \<Rightarrow> ant"
where
  Amax_0 : "Amax 0 f = f 0"
| Amax_Suc :"Amax (Suc n) f = amax (Amax n f) (f (Suc n))"

lemma amin_ge:"x \<le> amin x y \<or> y \<le> amin x y"
apply (simp add:amin_def)
done

lemma amin_le_l:"amin x y \<le> x"
apply (simp add:amin_def, cut_tac ale_linear[of "x" "y"],
       rule impI, simp)
done

lemma amin_le_r:"amin x y \<le> y"
apply (simp add:amin_def) 
done

lemma amax_le:"amax x y \<le> x \<or> amax x y \<le> y"
apply (simp add:amax_def)
done

lemma amax_le_n:"\<lbrakk>x \<le> n; y \<le> n\<rbrakk> \<Longrightarrow> amax x y \<le> n" 
by (simp add:amax_def)

lemma amax_ge_l:"x \<le> amax x y"
apply (simp add:amax_def)
done

lemma amax_ge_r:"y \<le> amax x y"
apply (simp add:amax_def, cut_tac ale_linear[of "x" "y"],
       rule impI, simp)
done

lemma amin_mem_i:"\<lbrakk>x \<in> Z\<^sub>\<infinity>; y \<in> Z\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> amin x y \<in> Z\<^sub>\<infinity>"  
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"], simp add:aug_inf_def,
      (erule disjE)+, (erule exE)+, cut_tac amin_ge[of "x" "y"],
      rule contrapos_pp, simp+,
      erule disjE,
      cut_tac x = "ant z" in minf_le_any,
      frule_tac x = "ant z" in ale_antisym[of _ "-\<infinity>"], assumption+, simp,
      cut_tac x = "ant za" in minf_le_any,
      frule_tac x = "ant za" in ale_antisym[of _ "-\<infinity>"], assumption+, simp)
 apply (erule exE, simp add:amin_def, erule disjE, 
        erule exE, simp add:amin_def, simp add:amin_def)
done

lemma amax_mem_m:"\<lbrakk>x \<in> Z\<^sub>-\<^sub>\<infinity>; y \<in> Z\<^sub>-\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> amax x y \<in> Z\<^sub>-\<^sub>\<infinity>"  
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "y"],
      simp add:aug_minf_def)
apply ((erule disjE)+, simp add:amax_def,
       erule exE, simp add:amax_def,
       erule disjE, erule exE, simp add:amax_def)
apply ((erule exE)+, cut_tac amax_le[of "x" "y"], 
       rule contrapos_pp, simp+) apply (erule disjE,
       cut_tac x = "ant z" in inf_ge_any,
       frule_tac x = "ant z" in ale_antisym[of _ "\<infinity>"], assumption+, simp,
       cut_tac x = "ant za" in inf_ge_any,
       frule_tac x = "ant za" in ale_antisym[of _ "\<infinity>"], assumption+, simp) 
done

lemma amin_commute:"amin x y = amin y x"
apply (cut_tac ale_linear[of "x" "y"], erule disjE, simp add:amin_def)
apply (simp add:amin_def)
done 

lemma amin_mult_pos:"0 < z \<Longrightarrow> amin (z *\<^sub>a x) (z *\<^sub>a y) = z *\<^sub>a amin x y"
by (simp add:amin_def, simp add:asprod_pos_mono)

lemma amin_amult_pos:"0 < z \<Longrightarrow> 
         amin ((ant z) * x) ((ant z) * y) = (ant z) * amin x y"
by (simp add:asprod_amult[THEN sym], simp add:amin_mult_pos)

lemma times_amin:"\<lbrakk>0 < a; amin (x * (ant a)) (y * (ant a)) \<le> z * (ant a)\<rbrakk> \<Longrightarrow>
                     amin x y \<le> z"
by (frule amin_mult_pos[of "a" "x" "y"], simp add:asprod_amult,
       simp add:amult_commute[of "ant a"], simp add:amult_pos_mono_r)

lemma Amin_memTr:"f \<in> {i. i \<le> n} \<rightarrow> Z\<^sub>\<infinity>  \<longrightarrow> Amin n f \<in>  Z\<^sub>\<infinity>" 
apply (induct_tac n,
       simp add:Pi_def)
apply (rule impI,
       frule_tac func_pre[of "f" _ "Z\<^sub>\<infinity>"],
       simp, rule amin_mem_i, assumption+,
       simp add:Pi_def)
done

lemma Amin_mem:"f \<in> {i. i \<le> n} \<rightarrow>  Z\<^sub>\<infinity> \<Longrightarrow> Amin n f \<in>  Z\<^sub>\<infinity>" 
apply (simp add:Amin_memTr)
done

lemma Amax_memTr:"f \<in> {i. i \<le> n} \<rightarrow> Z\<^sub>-\<^sub>\<infinity>  \<longrightarrow> Amax n f \<in>  Z\<^sub>-\<^sub>\<infinity>" 
apply (induct_tac n,
       simp add:Pi_def)
apply (rule impI,
       frule_tac func_pre[of "f" _ "Z\<^sub>-\<^sub>\<infinity>"],
       simp, rule amax_mem_m, assumption+,
       simp add:Pi_def)
done

lemma Amax_mem:"f \<in> {i. i \<le> n} \<rightarrow>  Z\<^sub>-\<^sub>\<infinity> \<Longrightarrow> Amax n f \<in>  Z\<^sub>-\<^sub>\<infinity>" 
apply (simp add:Amax_memTr)
done

lemma Amin_mem_mem:"\<forall>j\<le> n. f j \<in> Z\<^sub>\<infinity> \<Longrightarrow> Amin n f \<in> Z\<^sub>\<infinity>"
by (rule Amin_mem, simp)

lemma Amax_mem_mem:"\<forall>j \<le> n. f j \<in> Z\<^sub>-\<^sub>\<infinity> \<Longrightarrow> Amax n f \<in> Z\<^sub>-\<^sub>\<infinity>"
by (rule Amax_mem, simp)

lemma Amin_leTr:"f \<in> {i. i \<le> n} \<rightarrow>  Z\<^sub>\<infinity> \<longrightarrow> (\<forall>j\<in>{i. i \<le> n}. Amin n f \<le> (f j))"
apply (induct_tac n,
       rule impI, rule ballI,
       simp)
apply (rule impI, rule ballI, 
       frule func_pre, simp)
  
apply (case_tac "j = Suc n", simp, rule amin_le_r) 
apply (cut_tac x = j and n = n in Nset_pre, simp, assumption,
       cut_tac x = "Amin n f" and y = "f (Suc n)" in amin_le_l,
       thin_tac "j \<le> Suc n", simp) 
apply (frule_tac x = j in spec,
       thin_tac "\<forall>j\<le>n. Amin n f \<le> f j", simp) 
done

lemma Amin_le:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow>  Z\<^sub>\<infinity>; j \<in> {k. k \<le> n}\<rbrakk> \<Longrightarrow> Amin n f \<le> (f j)"
apply (simp add:Amin_leTr)
done

lemma Amax_geTr:"f \<in> {j. j \<le> n} \<rightarrow> Z\<^sub>-\<^sub>\<infinity> \<longrightarrow> (\<forall>j\<in>{j. j \<le> n}. (f j) \<le> Amax n f)"
apply (induct_tac n,
       rule impI, rule ballI,
       simp)
apply (rule impI, rule ballI,
       frule func_pre, simp,
       case_tac "j = Suc n", simp, rule amax_ge_r,
       cut_tac x = j and n = n in Nset_pre, simp, assumption,
       thin_tac "j \<le> Suc n",
       simp)
apply (cut_tac x = "Amax n f" and y = "f (Suc n)" in amax_ge_l,
       drule_tac x = j in spec, simp)
done

lemma Amax_ge:"\<lbrakk>f \<in> {j. j \<le> n} \<rightarrow> Z\<^sub>-\<^sub>\<infinity>; j \<in> {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
                                                 (f j) \<le> (Amax n f)"
apply (simp add:Amax_geTr)
done

lemma Amin_mem_le:"\<lbrakk>\<forall>j \<le> n. (f j) \<in>  Z\<^sub>\<infinity>; j \<in> {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
                                           (Amin n f) \<le> (f j)"
by (rule Amin_le, simp, simp)

lemma Amax_mem_le:"\<lbrakk>\<forall>j \<le> n. (f j) \<in>  Z\<^sub>-\<^sub>\<infinity>; j \<in> {j. j \<le> n}\<rbrakk> \<Longrightarrow> 
                                           (f j) \<le> (Amax n f)"
by (rule Amax_ge, simp, simp)

lemma amin_ge1:"\<lbrakk>(z::ant) \<le> x; z \<le> y \<rbrakk> \<Longrightarrow> z \<le> amin x y"
by (simp add:amin_def)

lemma amin_gt:"\<lbrakk>(z::ant) < x; z < y\<rbrakk> \<Longrightarrow> z < amin x y"
apply (simp add:less_ant_def, (erule conjE)+,
       rule conjI, simp add:amin_ge1)
apply (rule contrapos_pp, simp+,
       case_tac "x \<le> y", simp add:amin_def, simp add:amin_def)
done

lemma Amin_ge1Tr:"(\<forall>j\<le>(Suc n). (f j) \<in> Z\<^sub>\<infinity> \<and> z \<le> (f j)) \<longrightarrow> 
                                            z \<le> (Amin (Suc n) f)"
apply (induct_tac n)
 apply (rule impI)
 apply (frule_tac x = 0 in spec,
        frule_tac x = "Suc 0" in spec,
        thin_tac "\<forall>j\<le>Suc 0. f j \<in> Z\<^sub>\<infinity> \<and> z \<le> f j", simp, (erule conjE)+,
        simp add:amin_ge1)

apply (rule impI,
       simp,
       frule_tac a = "Suc (Suc n)" in forall_spec,
       thin_tac "\<forall>j\<le>Suc (Suc n). f j \<in> Z\<^sub>\<infinity> \<and> z \<le> f j", simp,
       thin_tac "\<forall>j\<le>Suc (Suc n). f j \<in> Z\<^sub>\<infinity> \<and> z \<le> f j", erule conjE)
 apply (rule amin_ge1, assumption+)
done

lemma Amin_ge1:"\<lbrakk> \<forall>j \<le> (Suc n). f j \<in> Z\<^sub>\<infinity>; \<forall>j \<le> (Suc n). z \<le> (f j)\<rbrakk> \<Longrightarrow> 
                             z \<le> (Amin (Suc n) f)"
apply (simp del:Amin_Suc add:Amin_ge1Tr)
done

lemma amin_trans1:"\<lbrakk>x \<in> Z\<^sub>\<infinity>; y \<in> Z\<^sub>\<infinity>; z \<in> Z\<^sub>\<infinity>; z \<le> x \<rbrakk> \<Longrightarrow> 
                           amin z y \<le> amin x y"
apply (case_tac "z \<le> y", simp add:amin_def)
 apply (simp add:amin_def)
 apply (simp only:aneg_le[of "z" "y"], frule aless_imp_le[of "y" "z"],
        frule ale_trans[of "y" "z" "x"], assumption+, rule impI,
        frule ale_antisym[of "y" "x"], assumption+) 
done

lemma inf_in_aug_inf:"\<infinity>  \<in> Z\<^sub>\<infinity>"
apply (simp add:aug_inf_def, simp add:not_sym)
done

subsection "Maximum element of a set of ants"

primrec aasc_seq :: "[ant set, ant, nat] \<Rightarrow> ant"
where
  aasc_seq_0   : "aasc_seq A a 0 = a"
| aasc_seq_Suc : "aasc_seq A a (Suc n) = 
                     (SOME b. ((b \<in> A) \<and> (aasc_seq A a n) < b))"

lemma aasc_seq_mem:"\<lbrakk>a \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                            (aasc_seq A a n) \<in> A"
apply (induct_tac n)
 apply (simp, simp) 
 apply (simp add:aneg_le,
        frule_tac a = "aasc_seq A a n" in forall_spec, assumption+,
        thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. m < x)",
        rule someI2_ex, blast, simp)
done

lemma aasc_seqn:"\<lbrakk>a \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                         (aasc_seq A a n) < (aasc_seq A a (Suc n))"
apply (frule aasc_seq_mem [of "a" "A" "n"], assumption+,
       simp add:aneg_le,
       frule_tac a = "aasc_seq A a n" in forall_spec, assumption+,
       thin_tac "\<forall>m. m \<in> A \<longrightarrow> (\<exists>x\<in>A. m < x)", rule someI2_ex, blast, simp)
done

lemma aasc_seqn1:"\<lbrakk>a \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                        (aasc_seq A a n) + 1 \<le> (aasc_seq A a (Suc n))"
by (frule aasc_seqn [of "a" "A" "n"], assumption+, simp) 

lemma aubs_ex_n_maxTr:"\<lbrakk>a \<in> A; \<not> (\<exists>m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m))\<rbrakk> \<Longrightarrow>
                                         (a + an n) \<le> (aasc_seq A a n)"
apply (induct_tac n) 
 apply (simp add:aadd_0_r,
        frule_tac n = n in aasc_seqn1[of "a" "A"], assumption+,
        cut_tac x = "a + an n" and y = "aasc_seq A a n" in 
        aadd_le_mono[of _ _ "1"], assumption, simp,
        frule_tac i = "a + an n + 1" and j = "aasc_seq A a n + 1" and
         k = "(SOME b. b \<in> A \<and> aasc_seq A a n < b)" in ale_trans, assumption+)
apply (simp add:an_Suc,
       case_tac "a = -\<infinity>",
       subst ant_1[THEN sym], simp del:ant_1 add:a_zpz an_def,
       subgoal_tac "a \<in> Z\<^sub>\<infinity>", subgoal_tac "an n \<in> Z\<^sub>\<infinity>", 
       subgoal_tac "1 \<in> Z\<^sub>\<infinity>", 
       subst aadd_assoc_i[THEN sym], assumption+)   
apply (subst ant_1[THEN sym], simp del:ant_1 add:aug_inf_def,
       (simp add:aug_inf_def an_def)+)
done  

lemma aubs_ex_AMax:"\<lbrakk>A \<subseteq> UBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. x \<le> m)"
apply (case_tac "A = {-\<infinity>}", simp,
      frule not_sub_single[of "A" "-\<infinity>"], assumption+,
      frule not_sub[of "A" "{-\<infinity>}"],
      erule exE, erule conjE, simp, rename_tac a, rule ex_ex1I)
prefer 2
 apply ((erule conjE)+, 
        frule_tac x = y in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. x \<le> m",
        frule_tac x = m in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. x \<le> y", simp)
apply (rule contrapos_pp, simp,
       subgoal_tac "\<exists>w. a = ant w", erule exE,
       frule_tac a = a and A = A  and n = "nat ((abs w) + (abs z) + 1)" in 
       aubs_ex_n_maxTr, simp, 
       frule_tac a = a and n = "nat ((abs w) + (abs z) + 1)" in 
       aasc_seq_mem[of _ "A"], assumption,
       thin_tac "\<not> (\<exists>m. m \<in> A \<and> (\<forall>x\<in>A. x \<le> m))",
       simp add:UBset_def)
apply (frule_tac c = "aasc_seq A (ant w) (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1))" in 
       subsetD[of "A" "{x. x \<le> ant z}"], assumption+,
       simp)
apply(frule_tac i = "ant w + an (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1))" and 
       j = "aasc_seq A (ant w) (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1))" and 
        k = "ant z" in ale_trans, assumption+)
apply (thin_tac "ant w + an (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1))
           \<le> aasc_seq A (ant w) (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1))",
       thin_tac "aasc_seq A (ant w) (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1)) \<in> A",
       thin_tac "aasc_seq A (ant w) (nat (\<bar>w\<bar> + \<bar>z\<bar> + 1)) \<le> ant z",
       simp add:an_def a_zpz)
 apply (cut_tac a = a in mem_ant, erule disjE, simp, erule disjE, erule exE,
        simp, simp add:UBset_def, frule subsetD[of "A" "{x. x \<le> ant z}" "\<infinity>"],
        assumption+, simp, cut_tac inf_ge_any[of "ant z"], 
        frule_tac ale_antisym[of "ant z" "\<infinity>"], assumption+, simp)
done

definition
  AMax :: "ant set \<Rightarrow> ant" where
  "AMax A = (THE m. m \<in> A \<and> (\<forall>x\<in>A. x \<le> m))"

definition
  AMin::"ant set \<Rightarrow> ant" where
  "AMin A = (THE m. m \<in> A \<and> (\<forall>x\<in>A. m \<le> x))"

definition
  rev_o :: "ant \<Rightarrow> ant" where
  "rev_o x = - x"

lemma AMax:"\<lbrakk>A \<subseteq> UBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> 
                    (AMax A) \<in> A \<and> (\<forall>x\<in>A. x \<le> (AMax A))" 
apply (simp add:AMax_def) 
apply (frule aubs_ex_AMax[of "A" "z"], assumption)
apply (rule theI')
apply assumption
done

lemma AMax_mem:"\<lbrakk>A \<subseteq> UBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> (AMax A) \<in> A" 
apply (simp add:AMax[of "A" "z"])
done

lemma rev_map_nonempty:"A \<noteq> {} \<Longrightarrow> rev_o ` A \<noteq> {}"
by (rule contrapos_pp, simp+)

lemma rev_map:"rev_o \<in> LBset (ant (-z)) \<rightarrow> UBset (ant z)"
by  (rule Pi_I, simp add:UBset_def LBset_def rev_o_def,
     frule_tac x = "ant (-z)" and y = x in ale_minus, simp add:aminus)

lemma albs_ex_AMin:"\<lbrakk>A \<subseteq> LBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>!m. m\<in>A \<and> (\<forall>x\<in>A. m \<le> x)"
apply (rule ex_ex1I)
prefer 2 apply ((erule conjE)+, 
        frule_tac x = y in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. m \<le> x",
        frule_tac x = m in bspec, assumption+,
        thin_tac "\<forall>x\<in>A. y \<le> x", simp)
apply (subgoal_tac "- AMax (rev_o ` A) \<in> A \<and> 
                       (\<forall>x \<in> A. (- AMax (rev_o ` A)) \<le> x)", blast,
       cut_tac rev_map[of "-z"], simp add:a_minus_minus,
       frule rev_map_nonempty[of "A"], 
       frule image_sub[of "rev_o" "LBset (ant z)" "UBset (ant (-z))" "A"],
       assumption+, frule AMax[of "rev_o ` A" "-z"], assumption+,
       erule conjE,
       rule conjI, thin_tac "\<forall>x\<in>rev_o ` A. x \<le> AMax (rev_o ` A)",
        thin_tac "rev_o \<in> LBset (ant z) \<rightarrow> UBset (ant (- z))", 
        thin_tac "rev_o ` A \<noteq> {}",
        thin_tac "rev_o ` A \<subseteq> UBset (ant (- z))")
apply (simp add:image_def rev_o_def,
       erule bexE, simp add:a_minus_minus, rule ballI,
       subgoal_tac "rev_o x \<in> rev_o ` A",
        frule_tac x = "rev_o x" in bspec, assumption+,
        thin_tac "\<forall>x\<in>rev_o ` A. x \<le> AMax (rev_o ` A)",
        thin_tac "rev_o \<in> LBset (ant z) \<rightarrow> UBset (ant (- z))", 
        thin_tac "rev_o ` A \<noteq> {}",
        thin_tac "rev_o ` A \<subseteq> UBset (ant (- z))")
apply (simp add:image_def rev_o_def, erule bexE, simp add:a_minus_minus,
       frule_tac x = "-x" and y = "-xa" in ale_minus, simp add:a_minus_minus,
       simp add:image_def, blast)
done

lemma AMin:"\<lbrakk>A \<subseteq> LBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> 
                    (AMin A) \<in> A \<and> (\<forall>x\<in>A. (AMin A) \<le> x)" 
apply (simp add:AMin_def) 
apply (frule albs_ex_AMin[of "A" "z"], assumption)
apply (rule theI')
apply assumption
done

lemma AMin_mem:"\<lbrakk>A \<subseteq> LBset (ant z); A \<noteq> {}\<rbrakk> \<Longrightarrow> (AMin A) \<in> A"
apply (simp add:AMin) 
done

primrec ASum :: "(nat \<Rightarrow> ant) \<Rightarrow> nat \<Rightarrow> ant"
where
  ASum_0: "ASum f 0 = f 0"
| ASum_Suc: "ASum f (Suc n) = (ASum f n) + (f (Suc n))"

lemma age_plus:"\<lbrakk>0 \<le> (a::ant); 0 \<le> b; a + b \<le> c\<rbrakk> \<Longrightarrow> a \<le> c"
apply (frule aadd_le_mono[of "0" "b" "a"]) 
apply (simp add:aadd_commute[of "b" "a"] aadd_0_l)
done

lemma age_diff_le:"\<lbrakk>(a::ant) \<le> c; 0 \<le> b\<rbrakk> \<Longrightarrow> a - b \<le> c"
apply (frule ale_minus[of "0" "b"], thin_tac "0 \<le> b", simp)
apply (frule aadd_le_mono[of "a" "c" "-b"])
apply (frule aadd_le_mono[of "-b" "0" "c"])
apply (thin_tac "a \<le> c", thin_tac "- b \<le> 0",
       simp add:aadd_commute[of "-b" "c"] aadd_0_l)
apply (simp add:diff_ant_def) 
done

lemma adiff_le_adiff:"a \<le> (a'::ant) \<Longrightarrow> a - b \<le> a' - b"
apply (simp add:diff_ant_def)
apply (rule aadd_le_mono[of "a" "a'" "-b"], assumption+)
done

lemma aplus_le_aminus:"\<lbrakk> a \<in>  Z\<^sub>-\<^sub>\<infinity>; b \<in>  Z\<^sub>-\<^sub>\<infinity>; c \<in>  Z\<^sub>-\<^sub>\<infinity>; -b \<in>  Z\<^sub>-\<^sub>\<infinity>\<rbrakk> \<Longrightarrow> 
                 ((a + b) \<le> (c::ant)) = (a \<le> c - b)"
apply (rule iffI)
apply (frule aadd_le_mono[of "a + b" "c" "-b"])
 apply (simp add:aadd_assoc_m, simp add:aadd_minus_r)
 apply (simp add:aadd_0_r, simp add:diff_ant_def)
 
apply (frule aadd_le_mono[of "a" "c - b" "b"])
apply (simp add:diff_ant_def)
apply (simp add:aadd_assoc_m) 
apply (simp add:aadd_minus_inv[of "b"])
apply (simp add: aadd_0_r)
done

section "Cardinality of sets"

text \<open>cardinality is defined for the finite sets only\<close>

lemma card_eq:"A = B \<Longrightarrow> card A = card B"
 apply simp
 done

lemma card0:"card {} = 0"
by  simp

lemma card_nonzero:"\<lbrakk>finite A; card A \<noteq> 0\<rbrakk> \<Longrightarrow> A \<noteq> {}"
by (rule contrapos_pp, simp+)

lemma finite1:"finite {a}"
by  simp

lemma card1:"card {a} = 1"
by simp

lemma nonempty_card_pos:"\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> 0 < card A"
apply (frule nonempty_ex [of "A"], erule exE,
       frule_tac a = x and A = A in singleton_sub) 
apply (frule_tac B = A and A = "{x}" in card_mono, assumption+,
       simp add:card1)
done

lemma nonempty_card_pos1:"\<lbrakk>finite A; A \<noteq> {}\<rbrakk> \<Longrightarrow> Suc 0 \<le> card A"
apply (frule nonempty_card_pos[of "A"], assumption+)
apply (rule Suc_leI[of "0" "card A"], assumption)
done

lemma card1_tr0:"\<lbrakk> finite A; card A = Suc 0; a \<in> A \<rbrakk> \<Longrightarrow> {a} = A"
apply (cut_tac card1[of "a"])
apply (rule card_seteq[of "A" "{a}"], assumption)
apply (rule singleton_sub[of "a" "A"], assumption)
apply simp
done

lemma card1_tr1:"(constmap {0::nat} {x}) \<in> {0} \<rightarrow> {x} \<and>
                       surj_to (constmap {0::nat} {x}) {0} {x}"
 apply (rule conjI, simp add:constmap_def Pi_def,
       simp add:surj_to_def image_def constmap_def)
 done

lemma card1_Tr2:"\<lbrakk>finite A; card A = Suc 0\<rbrakk> \<Longrightarrow> 
                  \<exists>f. f \<in> {0::nat} \<rightarrow> A \<and> surj_to f {0} A"
apply (frule card_nonzero[of "A"], simp)
apply (cut_tac nonempty_ex[of "A"], erule exE)
 apply (frule_tac a = x in card1_tr0[of "A"], assumption+)
 apply (rotate_tac -1, frule sym, thin_tac "{x} = A", simp)
 apply (cut_tac x = x in card1_tr1, blast, simp)
done
 
lemma card2:"\<lbrakk> finite A; a \<in> A; b \<in> A; a \<noteq> b \<rbrakk> \<Longrightarrow> Suc (Suc 0) \<le> card A"
apply (cut_tac card1[of "a"])
 apply (frule singleton_sub[of "b" "A"])
 apply (frule finite_subset[of "{b}" "A"], assumption)
 apply (frule card_insert_disjoint[of "{b}" "a"])
 apply simp
 apply (simp only:card1)
 apply (frule insert_sub[of "{b}" "A" "a"], assumption+)
   apply (frule card_mono [of "A" "{a, b}"], assumption) 
   apply simp
done

lemma card2_inc_two:"\<lbrakk>0 < (n::nat); x \<in> {j. j \<le> n}\<rbrakk> \<Longrightarrow>
                                  \<exists>y \<in> {j. j \<le> n}. x \<noteq> y"
apply (rule contrapos_pp, simp+)
 apply (frule_tac m = 0 and n = n in Suc_leI) apply (
        frule_tac a = "Suc 0" in forall_spec, assumption) 
 apply (frule_tac a = 0 in forall_spec)
 apply (rule less_imp_le, assumption)
 apply simp
done


lemma Nset2_prep1:"\<lbrakk>finite A; card A = Suc (Suc n) \<rbrakk> \<Longrightarrow> \<exists>x. x\<in>A" 
apply (frule card_nonzero[of "A"])
apply simp
apply (simp add:nonempty_ex)
done

lemma ex_least_set:"\<lbrakk>A = {H. finite H \<and> P H}; H \<in> A\<rbrakk> \<Longrightarrow> 
                       \<exists>K \<in> A. (LEAST j. j \<in> (card ` A)) =  card K" 
(* proof by L. C. Paulson *)
by (simp add:image_def, rule LeastI, rule_tac x = "H" in exI, simp)

lemma Nset2_prep2:"x \<in> A \<Longrightarrow> A - {x} \<union> {x} = A"
by auto

lemma Nset2_finiteTr:"\<forall>A. (finite A \<and>(card A = Suc n) \<longrightarrow> 
     (\<exists>f. f \<in> {i. i \<le> n} \<rightarrow> A \<and> surj_to f {i. i \<le> n} A))"
apply (induct_tac n, rule allI, rule impI, erule conjE)
apply (simp add: card1_Tr2 del: Pi_split_insert_domain)
  (* n *)
apply (rule allI, rule impI, erule conjE, frule Nset2_prep1, assumption+)
apply (erule exE)
apply(drule_tac a = "A - {x}" in forall_spec)
 apply simp
apply (erule exE)
apply (cut_tac x = x in card1_tr1, (erule conjE)+)
apply (frule_tac f = f and n = n and A = "A - {x}" and 
       g = "constmap {0} {x}" and m = 0 and B = "{x}" in jointfun_surj,
       assumption+)
  apply simp+
apply (frule_tac f = f and n = n and A = "A - {x}" and 
        g = "constmap {0} {x}" and m = 0 and B = "{x}" in jointfun_hom0,
        simp,
        frule_tac x = x and A = A in Nset2_prep2, simp, blast)
done

lemma Nset2_finite:"\<lbrakk> finite A; card A = Suc n\<rbrakk> \<Longrightarrow>
                       \<exists>f. f \<in> {i. i \<le> n} \<rightarrow> A \<and> surj_to f {i. i \<le> n} A "
by (simp add:Nset2_finiteTr)

lemma Nset2finite_inj_tr0:"j \<in> {i. i \<le> (n::nat)} \<Longrightarrow>
                                     card ({i. i \<le> n} - {j}) = n"
by simp


lemma Nset2finite_inj_tr1:"\<lbrakk> i \<le> (n::nat); j \<le> n; f i = f j; i \<noteq> j \<rbrakk> \<Longrightarrow> 
       f ` ({i. i \<le> n} - {j}) = f ` {i. i \<le> n}"
apply (simp add:image_def, rule equalityI, rule subsetI, simp add:CollectI,
       erule bexE, case_tac "xa = j", frule sym, thin_tac "f i = f j", 
       simp, blast)
apply (rule subsetI, simp, erule exE, case_tac "xa = j", frule sym, 
       thin_tac "f i = f j", blast, blast)
done

lemma Nset2finite_inj:"\<lbrakk>finite A; card A = Suc n; surj_to f {i. i \<le> n} A \<rbrakk> \<Longrightarrow> 
        inj_on f {i. i \<le> n}"
by (metis card_Collect_le_nat eq_card_imp_inj_on finite_Collect_le_nat surj_to_def)

definition
  zmax :: "[int, int] \<Rightarrow> int" where
  "zmax x y = (if (x \<le> y) then y else x)"

primrec Zmax :: "[nat, nat \<Rightarrow> int] \<Rightarrow> int"
where
  Zmax_0 : "Zmax 0 f = f 0"
| Zmax_Suc :"Zmax (Suc n) f = zmax (Zmax n f) (f (Suc n))"

lemma Zmax_memTr:"f \<in> {i. i \<le> (n::nat)} \<rightarrow> (UNIV::int set) \<longrightarrow>
                                       Zmax n f \<in> f ` {i. i \<le> n}"
apply (induct_tac n)
 apply simp 
apply (rule impI)
 apply (frule func_pre)
 apply (frule_tac f = f and A = "{i. i \<le> Suc n}" and B = UNIV and 
        ?A1.0 = "{i. i \<le> n}" and ?A2.0 = "{i. i \<le> Suc n}" in im_set_mono)
 apply (rule subsetI, simp, simp, simp)
 apply (case_tac "(Zmax n f) \<le> (f (Suc n))", simp add:zmax_def)
 apply (simp add:zmax_def)
 apply (simp add:subsetD)
done

lemma zmax_ge_r:"y \<le> zmax x y"
by (simp add:zmax_def)

lemma zmax_ge_l:"x \<le> zmax x y"
by (simp add:zmax_def)

lemma Zmax_geTr:"f \<in> {j. j \<le> (n::nat)} \<rightarrow> (UNIV::int set) \<longrightarrow> 
                    (\<forall>j\<in>{j. j \<le> n}. (f j) \<le> Zmax n f)"
apply (induct_tac n,
       rule impI, rule ballI,
       simp)
apply (rule impI, rule ballI,
       frule func_pre, simp,
       case_tac "j = Suc n", simp, rule zmax_ge_r,
       cut_tac x = j and n = n in Nset_pre, simp, assumption,
       thin_tac "j \<le> Suc n",
       simp)

apply (cut_tac x = "Zmax n f" and y = "f (Suc n)" in zmax_ge_l,
       frule_tac x = j in spec,
       thin_tac "\<forall>j\<le>n. f j \<le> Zmax n f")
apply  simp 
done

lemma Zmax_plus1:"f \<in> {j. j \<le> (n::nat)} \<rightarrow> (UNIV::int set) \<Longrightarrow>
           ((Zmax n f) + 1) \<notin> f ` {j. j \<le> n}"
apply (cut_tac  Zmax_geTr[of f n])
apply (rule contrapos_pp, simp+)
apply (simp add:image_def, erule exE, erule conjE)
apply (frule_tac a = x in forall_spec, assumption,
       thin_tac "\<forall>j\<le>n. f j \<le> Zmax n f")
apply (frule sym, thin_tac "Zmax n f + 1 = f x", simp)
  done

lemma image_Nsetn_card_pos:" 0 < card (f ` {i. i \<le> (n::nat)})"
apply(rule nonempty_card_pos)
apply auto
done

lemma card_image_Nsetn_Suc
:"\<lbrakk>f \<in> {j. j \<le> Suc n} \<rightarrow> B; 
      f (Suc n) \<notin> f ` {j. j \<le> n}\<rbrakk>  \<Longrightarrow> 
       card (f ` {j. j \<le> Suc n}) - Suc 0 = 
                     Suc (card (f ` {j. j \<le> n}) - Suc 0)"
apply (simp add:image_Nset_Suc)
apply (cut_tac image_Nsetn_card_pos[of f n], simp)
done

lemma slide_surj:"i < (j::nat) \<Longrightarrow> 
                    surj_to (slide i) {l. l \<le> (j - i)} (nset i j)"
proof -
 assume p1:"i < j"
 from p1 show ?thesis
  apply (simp add:surj_to_def image_def)
  apply (rule equalityI,
         rule subsetI, simp, erule exE, simp add:slide_def nset_def,
         frule less_imp_le [of i j], erule conjE,
         thin_tac "i < j", frule add_le_mono [of _ "j - i" "i" "i"],
         simp+, rule subsetI, simp)
 apply (simp add:nset_def slide_def, erule conjE, 
        frule_tac m = x and n = j and l = i in diff_le_mono,
        subgoal_tac "x = i + (x - i)", blast, simp)
 done
qed

lemma slide_inj:"i < j \<Longrightarrow> inj_on (slide i) {k. k \<le> (j - i)}"
apply (simp add:inj_on_def, (rule allI)+)
apply (rule impI, rule allI, rule impI, rule impI)
apply (simp add:slide_def)
done

lemma card_nset:"i < (j :: nat) \<Longrightarrow> card (nset i j) = Suc (j - i)"
apply (frule slide_inj [of "i" "j"])
apply (frule card_image [of "slide i" "{k. k \<le> (j - i)}"])
apply (simp, frule slide_surj [of "i" "j"], simp add:surj_to_def)
done

lemma sliden_hom:"i < j \<Longrightarrow> (sliden i) \<in> nset i j \<rightarrow>  {k. k \<le> (j - i)}"
by (simp add:Pi_def, rule allI, rule impI, simp add:sliden_def,
       simp add:nset_def, erule conjE, simp add:diff_le_mono)

lemma slide_sliden:"(sliden i) (slide i k) = k"
by (simp add:sliden_def slide_def)

lemma sliden_surj:"i < j \<Longrightarrow>  surj_to (sliden i) (nset i j) {k. k \<le> (j - i)}"
apply (simp add:surj_to_def image_def, rule equalityI)
apply (rule subsetI, simp, erule bexE, simp add:nset_def sliden_def,
       erule conjE, rule_tac m = xa in diff_le_mono[of _ "j" "i"], 
       assumption+)
apply (rule subsetI, simp add:nset_def sliden_def,
       frule_tac i = x in add_le_mono[of _ "j - i" "i" "i"], simp,
       simp, subgoal_tac "i \<le> x + i", subgoal_tac "x = (x + i) - i",
       blast) apply simp+
done
 
lemma sliden_inj: "i < j \<Longrightarrow>  inj_on (sliden i) (nset i j)"
 apply (simp add:inj_on_def, (rule ballI)+, rule impI, simp add:sliden_def)
 apply (simp add:nset_def, (erule conjE)+,  
        subgoal_tac "(x - i = y - i) = (x = y)", blast)
 apply (rule eq_diff_iff, assumption+)
done

definition
  transpos :: "[nat, nat] \<Rightarrow> (nat \<Rightarrow> nat)" where
  "transpos i j = (\<lambda>k. if k = i then j else if k = j then i else k)" 

lemma transpos_id:"\<lbrakk> i \<le> n; j \<le> n; i \<noteq> j ; x \<in> {k. k \<le> n} - {i, j} \<rbrakk>
  \<Longrightarrow> transpos i j x = x"
proof -
 assume p1:"i \<le> n" and p2:"j \<le> n" and p3:" i \<noteq> j" and 
 p4:"x \<in> {k. k \<le> n} - {i, j}"
 from p1 and p2 and p3 and p4 show ?thesis
  apply (simp add:transpos_def)
 done
qed


lemma transpos_id_1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; x \<le> n; x \<noteq> i; x \<noteq> j\<rbrakk> \<Longrightarrow> 
                       transpos i j x = x" 
proof -
 assume p1:"i \<le> n" and p2:"j \<le> n" and p3:"i \<noteq> j" and p4:"x \<le> n" and p5:"x \<noteq> i" and p6:"x \<noteq> j"
 from p1 and p2 and p3 and p4 and p5 and p6 show ?thesis
 apply (simp add:transpos_def)
done
qed

lemma transpos_id_2:"i \<le> n \<Longrightarrow> transpos i n (Suc n) = Suc n"
by (simp add:transpos_def)

lemma transpos_ij_1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j \<rbrakk> \<Longrightarrow>
                        transpos i j i = j"
by (simp add:transpos_def)

lemma transpos_ij_2:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j\<rbrakk> \<Longrightarrow> transpos i j j = i"
by (simp add:transpos_def)

lemma transpos_hom:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j\<rbrakk> \<Longrightarrow> 
                          (transpos i j)  \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}" 
apply (simp add:Pi_def, rule allI, rule impI)
apply (case_tac "x = i", simp add:transpos_def)
 apply (case_tac "x = j", simp add:transpos_def,
        subst transpos_id, assumption+, simp, assumption)
done

lemma transpos_mem:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; l \<le> n\<rbrakk> \<Longrightarrow> 
                           (transpos i j l) \<le> n"
apply (frule transpos_hom [of "i" "n" "j"], assumption+,
       cut_tac funcset_mem[of "transpos i j" "{i. i \<le> n}" "{i. i \<le> n}" l])
apply simp+
done

lemma transpos_inj:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j\<rbrakk> 
                          \<Longrightarrow> inj_on (transpos i j) {i. i \<le> n}"
 apply (simp add:inj_on_def, (rule allI, rule impI)+, rule impI,
        case_tac "x = i", case_tac "y = j",
        simp add:transpos_def)
 apply (simp add:transpos_ij_1, rule contrapos_pp, simp+,
        frule_tac x = y in transpos_id [of "i" "n" "j"], assumption+,
        simp+)
 apply (case_tac "x = j", simp, 
        simp add:transpos_ij_2, rule contrapos_pp, simp+,
        frule_tac x = y in transpos_id [of "i" "n" "j"], assumption+,
        simp, rule contrapos_pp, simp+, simp add:transpos_ij_1)
 apply (simp, simp add:transpos_ij_1, simp add:transpos_id_1, 
        thin_tac "x = transpos i j y",
        case_tac "y = i", simp add:transpos_ij_1,
        case_tac "y = j", simp add:transpos_ij_2)
 apply (simp add:transpos_id_1)
done

lemma transpos_surjec:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j\<rbrakk> 
                          \<Longrightarrow> surj_to (transpos i j) {i. i \<le> n} {i. i \<le> n}"
apply (simp add:surj_to_def,
       frule transpos_hom [of "i" "n" "j"], assumption+,
       frule image_sub [of "transpos i j" "{i. i \<le> n}" "{i. i \<le> n}" 
       "{i. i \<le> n}"], simp)
apply (frule transpos_inj [of "i" "n" "j"], assumption+,
       frule card_image [of "transpos i j" "{i. i \<le> n}"],
       simp add:card_seteq)
done

lemma comp_transpos:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j\<rbrakk> \<Longrightarrow>
      \<forall>k \<le> n. (compose {i. i \<le> n} (transpos i j) (transpos i j)) k = k"
proof -
 assume p1:"i \<le> n" and p2:"j \<le> n" and p3:"i \<noteq> j"
 from p1 and p2 and p3 show ?thesis
  apply (simp add:compose_def)
  apply (rule allI)
  apply (case_tac "k = i") apply simp
  apply (subst transpos_ij_1, assumption+) 
  apply (rule transpos_ij_2, simp+) 
  apply (rule impI)  
apply (case_tac "k = j") apply simp
  apply (subst transpos_ij_2, simp+) 
  apply (rule transpos_ij_1, simp+) 
  apply (subst transpos_id_1, assumption+) 
  apply (simp add:transpos_mem) 
  apply (simp add:transpos_id_1)+
 done
qed
 
lemma comp_transpos_1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; k \<le> n\<rbrakk> \<Longrightarrow>
                           (transpos i j) ((transpos i j) k) = k"
apply (frule comp_transpos [of "i" "n" "j"], assumption+)
 apply (simp add:compose_def)
done

lemma cmp_transpos1:"\<lbrakk>i \<le> n; j \<le> n; i \<noteq> j; k \<le> n\<rbrakk> \<Longrightarrow> 
                      (cmp (transpos i j) (transpos i j)) k = k"
apply (simp add:cmp_def)
apply (simp add:comp_transpos_1)
done

lemma cmp_transpos:"\<lbrakk>i \<le> n; i \<noteq> n; a \<le> (Suc n)\<rbrakk> \<Longrightarrow>
  (cmp (transpos i n) (cmp (transpos n (Suc n)) (transpos i n))) a =
               transpos i (Suc n) a"
apply (simp add:cmp_def)
apply (case_tac "a = Suc n", simp)
apply (simp add:transpos_id_2)
apply (cut_tac transpos_ij_2[of n "Suc n" "Suc n"], simp,
       cut_tac transpos_ij_2[of i "Suc n" "Suc n"], simp,
       cut_tac transpos_ij_2[of i n n], simp+)
apply (frule le_imp_less_or_eq[of a "Suc n"],
       thin_tac "a \<le> Suc n", simp,
       frule Suc_less_le[of a n])
apply (case_tac "a = n", simp,
       cut_tac transpos_ij_2[of i n n], simp, 
       cut_tac transpos_id[of i "Suc n" "Suc n" n], simp,
       cut_tac transpos_id[of n "Suc n" "Suc n" i], simp,
       cut_tac transpos_ij_1[of i n n], simp+)
apply (case_tac "a = i", simp,
       cut_tac transpos_ij_1[of i n n], simp+,
       cut_tac transpos_ij_1[of i "Suc n" "Suc n"], simp,
       cut_tac transpos_ij_1[of n "Suc n" "Suc n"], simp, 
       cut_tac transpos_id[of i "Suc n" n "Suc n"], simp+)
apply (cut_tac transpos_id[of i n n a], simp,
       cut_tac transpos_id[of i "Suc n" "Suc n" a], simp,
        cut_tac transpos_id[of n "Suc n" "Suc n" a], simp+)
done

lemma im_Nset_Suc:"insert (f (Suc n)) (f ` {i. i \<le> n}) = f ` {i. i\<le>(Suc n)}"
apply (simp add:image_def)
 apply (rule equalityI)
 apply (rule subsetI, simp)
 apply (erule disjE, blast) 
 apply (erule exE, erule conjE, simp,
        frule_tac i = xa and j = n and k = "Suc n" in le_trans,
        simp)
 apply blast
 apply (rule subsetI, simp, erule exE, erule conjE)
 apply (case_tac "xa = Suc n", simp)
 apply (metis le_SucE)
done

lemma Nset_injTr0:"\<lbrakk>f \<in> {i. i \<le> (Suc n)} \<rightarrow> {i. i \<le> (Suc n)}; 
      inj_on f {i. i \<le> (Suc n)}; f (Suc n) = Suc n\<rbrakk> \<Longrightarrow>
      f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n} \<and> inj_on f {i. i \<le> n}"
proof -
 assume p1:"f \<in> {i. i \<le> (Suc n)} \<rightarrow> {i. i \<le> (Suc n)}" and
        p2:"inj_on f {i. i \<le> (Suc n)}" and p3:"f (Suc n) = Suc n"
 have q1:"\<forall>l \<le> n. l \<le> (Suc n)" apply simp  done
 from p1 and p2 and p3 and q1 have q2:"f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}"
  apply (simp add:Pi_def)
  apply (rule allI, rule impI)
  apply (frule_tac a = x in forall_spec, simp,
         thin_tac "\<forall>x\<le>Suc n. f x \<le> Suc n")
  apply (rule contrapos_pp, simp+)
  apply (simp add:nat_not_le_less)
  apply (frule_tac n = "f x" in Suc_leI[of n], thin_tac "n < (f x)")
  apply (frule_tac m = "Suc n" and n = "f x" in le_antisym, assumption)
  apply(unfold inj_on_def)
  apply (frule_tac x = x in bspec, simp,
       thin_tac "\<forall>x\<in>{i. i \<le> Suc n}. \<forall>y\<in>{i. i \<le> Suc n}. f x = f y \<longrightarrow> x = y",
        frule_tac x = "Suc n" in bspec, simp)
  apply (frule_tac r = "f (Suc n)" and s = "Suc n" and t = "f x" in trans,
         assumption,
         thin_tac "f (Suc n) = Suc n", thin_tac "Suc n = f x",
         thin_tac "\<forall>y\<in>{i. i \<le> Suc n}. f x = f y \<longrightarrow> x = y")
  apply simp
done
from p2 have q3:"inj_on f {i. i \<le> n}"
   apply (simp add:inj_on_def) done
from q2 and q3 show ?thesis apply simp done
qed
 
lemma inj_surj:"\<lbrakk>f \<in> {i. i \<le> (n::nat)} \<rightarrow> {i. i \<le> n}; 
                inj_on f {i. i \<le> (n::nat)}\<rbrakk> \<Longrightarrow> f ` {i. i \<le> n} = {i. i \<le> n}"
proof -
 assume p1:"f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}" and p2:"inj_on f {i. i \<le> n}"
 have q1:"0 < Suc 0" apply simp done
 from p1 and p2 and q1 show ?thesis
 apply simp
 apply (frule image_sub [of "f" "{i. i \<le> n}" "{i. i \<le> n}" "{i. i \<le> n}"])
 apply simp+ 
 apply (cut_tac card_image [of "f" "{i. i \<le> n}"])
 apply (simp add:card_seteq) apply assumption
 done
qed

lemma Nset_pre_mem:"\<lbrakk>f:{i. i\<le>(Suc n)} \<rightarrow>{i. i\<le>(Suc n)}; 
      inj_on f {i. i\<le>(Suc n)}; f (Suc n) = Suc n; k \<le> n\<rbrakk> \<Longrightarrow> f k \<in> {i. i\<le>n}"
apply (frule Nset_injTr0[of f n], assumption+, erule conjE)
apply (frule_tac x = k in funcset_mem[of f "{i. i \<le> n}" "{i. i \<le> n}"],
       simp, assumption)
done

lemma Nset_injTr1:"\<lbrakk> \<forall>l \<le>(Suc n). f l \<le> (Suc n); inj_on f {i. i \<le> (Suc n)};
                    f (Suc n) = Suc n \<rbrakk> \<Longrightarrow> inj_on f {i. i \<le> n}"
by (cut_tac Nset_injTr0[of f n], simp, simp)

lemma Nset_injTr2:"\<lbrakk>\<forall>l\<le> (Suc n). f l \<le> (Suc n); inj_on f {i. i \<le> (Suc n)}; 
                    f (Suc n) = Suc n\<rbrakk> \<Longrightarrow> \<forall>l \<le> n. f l \<le> n"
apply (rule allI, rule impI)
apply (cut_tac k = l in Nset_pre_mem[of f n])
 apply (simp+)
done

lemma TR_inj_inj:"\<lbrakk>\<forall>l\<le> (Suc n). f l \<le> (Suc n); inj_on f {i. i \<le> (Suc n)};
                    i \<le> (Suc n); j \<le> (Suc n); i < j \<rbrakk> \<Longrightarrow>
      inj_on (compose {i. i \<le> (Suc n)} (transpos i j) f) {i. i \<le> (Suc n)}"
apply (frule transpos_inj[of i "Suc n" j], assumption+,
       simp )
apply (rule  comp_inj [of f "{i. i \<le> (Suc n)}" "{i. i \<le> (Suc n)}"
             "transpos i j" "{i. i \<le> (Suc n)}"])
 apply (simp, assumption,
        rule transpos_hom[of i "Suc n" j], simp+)
done

lemma enumeration:"\<lbrakk>f \<in> {i. i \<le> (n::nat)} \<rightarrow> {i. i \<le> m}; inj_on f {i. i \<le> n}\<rbrakk>
                     \<Longrightarrow>  n \<le> m"
apply (frule image_sub[of f "{i. i \<le> n}" "{i. i \<le> m}" "{i. i \<le> n}"])
 apply simp
apply (frule card_image[of f "{i. i \<le> n}"])
apply(drule card_mono[OF finite_Collect_le_nat])
apply simp
done
 
lemma enumerate_1:"\<lbrakk>\<forall>j \<le> (n::nat). f j \<in> A; \<forall>j \<le> (m::nat). g j \<in> A; 
     inj_on f {i. i \<le> n}; inj_on g {j. j \<le> m}; f `{j. j \<le> n} = A; 
     g ` {j. j \<le> m} = A \<rbrakk> \<Longrightarrow> n = m"
apply (frule card_image[of f "{i. i \<le> n}"],
       frule card_image[of g "{i. i \<le> m}"])
apply simp
done

definition
  ninv :: "[nat, (nat \<Rightarrow> nat)] \<Rightarrow> (nat \<Rightarrow> nat)" where
  "ninv n f = (\<lambda>y\<in>{i. i \<le> n}. (SOME x. (x \<le> n \<and> y = f x)))"

lemma ninv_hom:"\<lbrakk>f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}; inj_on f {i. i \<le> n}\<rbrakk> \<Longrightarrow>
                        ninv n f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}"
apply (rule Pi_I)
apply (simp add:ninv_def)
apply (frule inj_surj[of f n], assumption+,
       frule_tac x = x in funcset_mem[of f "{i. i \<le> n}" "{i. i \<le> n}"],
       simp)
apply (frule sym, thin_tac "f ` {i. i \<le> n} = {i. i \<le> n}",
       cut_tac a = x and A = "{i. i \<le> n}" and B = "f ` {i. i \<le> n}" in 
       eq_set_inc, simp, assumption,
       thin_tac "f x \<in> {i. i \<le> n}", thin_tac "{i. i \<le> n} = f ` {i. i \<le> n}",
       simp add:image_def, rule someI2_ex) 
   apply blast+
done

lemma ninv_r_inv:"\<lbrakk>f \<in> {i. i \<le> (n::nat)} \<rightarrow> {i. i \<le> n}; inj_on f {i. i \<le> n}; 
      b \<le> n\<rbrakk>  \<Longrightarrow>  f (ninv n f b) = b "
apply (simp add:ninv_def)
  apply (frule inj_surj, assumption+)
  apply (cut_tac a = b in eq_set_inc[of _ "{i. i \<le> n}" "f ` {i. i \<le> n}"])
  apply (simp, rule sym, assumption)
  apply (thin_tac "f ` {i. i \<le> n} = {i. i \<le> n}", simp add:image_def,
         erule exE, erule conjE, frule sym, thin_tac "b = f x")
  apply (rule someI2_ex, blast)
  apply (erule conjE, rule sym, assumption)
done

lemma ninv_inj:"\<lbrakk>f \<in> {i. i \<le> n} \<rightarrow> {i. i \<le> n}; inj_on f {i. i \<le> n}\<rbrakk> \<Longrightarrow>
                                inj_on  (ninv n f) {i. i \<le> n}"
apply (subst inj_on_def, simp)
 apply ((rule allI, rule impI)+, rule impI)
 apply (frule ninv_hom[of f n], assumption,
      frule_tac x = x in funcset_mem[of "ninv n f" "{i. i \<le> n}" "{i. i \<le> n}"],      simp,
      frule_tac x = y in funcset_mem[of "ninv n f" "{i. i \<le> n}" "{i. i \<le> n}"],
      simp,
      frule_tac b = x in ninv_r_inv  [of f n], assumption+)
apply (simp add:ninv_r_inv)
done

subsection "Lemmas required in Algebra6.thy"

lemma ge2_zmult_pos:
  "2 \<le> m \<Longrightarrow> 0 < z \<Longrightarrow> 1 < int m * z"
proof -
  assume a1: "0 < z"
  assume a2: "2 \<le> m"
  have "int m + - 1 * (int m * z) \<le> 0"
    using a1 by (simp add: pos_zmult_pos)
  then show ?thesis
    using a2 by linarith
qed

lemma zmult_pos_mono:"\<lbrakk> (0::int) < w; w * z \<le> w * z'\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (rule contrapos_pp, simp+) 
done 

lemma zmult_pos_mono_r:
         "\<lbrakk>(0::int) < w; z * w \<le> z' * w\<rbrakk> \<Longrightarrow> z \<le> z'"
apply (simp add:mult.commute)
done 

lemma an_neq_inf:"an n \<noteq> \<infinity>"
by (simp add:an_def)

lemma an_neq_minf:"an n \<noteq> -\<infinity>"
by (simp add:an_def)
 
lemma  aeq_mult:"\<lbrakk>z \<noteq> 0; a = b\<rbrakk> \<Longrightarrow> a * ant z = b * ant z" 
by simp

lemma tna_0[simp]:"tna 0 = 0"
by (simp add:ant_0[THEN sym] tna_ant)

lemma ale_nat_le:"(an n \<le> an m) = (n \<le> m)" 
by (simp add:an_def) 

lemma aless_nat_less:"(an n < an m) = (n < m)" 
by (simp add:an_def, subst aless_zless[of "int n" "int m"], simp)


lemma apos_natpos:"\<lbrakk>a \<noteq> \<infinity>; 0 \<le> a\<rbrakk> \<Longrightarrow> 0 \<le> na a"  
by (cut_tac ale_nat_le[of "0" "na a"], simp add:na_def an_def) 
  
lemma apos_tna_pos:"\<lbrakk>n \<noteq> \<infinity>; 0 \<le> n\<rbrakk> \<Longrightarrow> 0 \<le> tna n"
by (subst tna_0[THEN sym], 
       subst ale_zle[THEN sym, of "tna 0" "tna n"],
       frule apos_neq_minf[of "n"],
       simp add:ant_tna ant_0)

lemma apos_na_pos:"\<lbrakk>n \<noteq> \<infinity>; 0 \<le> n\<rbrakk> \<Longrightarrow> 0 \<le> na n"
by (frule apos_tna_pos[of "n"], assumption, 
        cut_tac tna_0[THEN sym], simp del:tna_0)

lemma aposs_tna_poss:"\<lbrakk>n \<noteq> \<infinity>; 0 < n\<rbrakk> \<Longrightarrow> 0 < tna n"
apply (subst tna_0[THEN sym], 
       subst aless_zless[THEN sym, of "tna 0" "tna n"],
       frule aless_imp_le[of "0" "n"],
       frule apos_neq_minf[of "n"],
       simp add:ant_tna ant_0)
done

lemma aposs_na_poss:"\<lbrakk>n \<noteq> \<infinity>; 0 < n\<rbrakk> \<Longrightarrow> 0 < na n"
apply (frule aless_imp_le[of "0" "n"],
       simp add:aneg_less[THEN sym, of "0" "n"],
       simp add:na_def)
apply (rule aposs_tna_poss, assumption+)
done

lemma nat_0_le: "0 \<le> z ==> int (nat z) = z"
apply simp
done 

lemma int_eq:"m = n \<Longrightarrow> int m = int n"
by simp

lemma box_equation:"\<lbrakk>a = b; a = c\<rbrakk> \<Longrightarrow> b = c"
apply simp
done 

lemma aeq_nat_eq:"\<lbrakk>n \<noteq> \<infinity>; 0 \<le> n; m \<noteq> \<infinity>; 0 \<le> m\<rbrakk> \<Longrightarrow> 
                    (n = m) = (na n = na m)"
apply (rule iffI, simp)
apply (cut_tac aneg_less[THEN sym, of "0" "n"],
       cut_tac aneg_less[THEN sym, of "0" "m"], simp,
       simp add:na_def,
       frule apos_neq_minf[of "n"],
       frule apos_neq_minf[of "m"])
apply (cut_tac mem_ant[of "m"],
       cut_tac mem_ant[of "n"], simp,
      (erule exE)+, simp,
       simp add:tna_ant,
       simp only:ant_0[THEN sym],
       simp only:ale_zle)
done

lemma na_minf:"na (-\<infinity>) = 0"
apply (simp add:na_def, rule impI,
       cut_tac minf_less_0, simp)
done

lemma an_na:"\<lbrakk>a \<noteq> \<infinity>; 0 \<le> a\<rbrakk> \<Longrightarrow> an (na a) = a"
apply (frule apos_tna_pos[of "a"], assumption,
       frule apos_neq_minf[of "a"],
       cut_tac mem_ant[of "a"], simp, erule exE,
       simp, simp add:an_def na_def)
apply (cut_tac y = 0 and x = "ant z" in aneg_less, simp,
       simp only:ant_0[THEN sym],
       simp only:ale_zle, simp add:tna_ant)
done

lemma not_na_le_minf:"\<not> (an n \<le> -\<infinity> )"
apply (rule contrapos_pp, simp+)
apply (cut_tac minf_le_any[of "an n"], frule ale_antisym[of "an n" "-\<infinity>"],
       assumption+, simp add:an_def)
done 

lemma not_na_less_minf:"\<not> (an n < -\<infinity>)" 
apply (simp add:aneg_less)
done 

lemma not_na_ge_inf:"\<not> \<infinity> \<le> (an n)"
apply (simp add:aneg_le, unfold an_def)
apply (simp add:z_less_i[of "int n"])
done

lemma an_na_le:"j \<le> an n \<Longrightarrow> na j \<le> n" 
apply (case_tac "j = -\<infinity>", simp add:na_minf)
apply (simp add:na_def)
apply (case_tac "j = \<infinity>", simp, rule impI) 
apply (cut_tac not_na_ge_inf[of n], simp)

apply simp 
apply (rule impI, simp add:aneg_less)
apply (frule an_na[of j], assumption)
apply (subgoal_tac "nat (tna j) = na j", simp,
                   thin_tac "nat (tna j) = na j")
apply (cut_tac ale_trans[of "an (na j)" j "an n"], thin_tac "j \<le> an n",
       thin_tac "an (na j) = j", simp add:ale_nat_le[of "na j" n],
       simp add:ale_refl[of j], assumption)
apply (thin_tac "an (na j) = j", simp add:na_def,
       rule impI)
apply (simp add:aneg_le[THEN sym, of j 0])
done

lemma aless_neq :"(x::ant) < y \<Longrightarrow> x \<noteq> y"
by (rule contrapos_pp, simp+)


chapter "Ordered Set"

(* In this chapter, I prove Zorn's lemma in general form. *)

section "Basic Concepts of Ordered Sets"

record 'a carrier =
  carrier :: "'a set"

record 'a Order = "'a carrier" +
  rel :: "('a \<times> 'a) set"

locale Order =
  fixes D (structure)
  assumes  closed: "rel D \<subseteq> carrier D \<times> carrier D"
      and    refl: "a \<in> carrier D \<Longrightarrow> (a, a) \<in> rel D"
      and antisym: "\<lbrakk>a \<in> carrier D; b \<in> carrier D; (a, b) \<in> rel D; 
                     (b, a) \<in> rel D\<rbrakk> \<Longrightarrow> a = b"
      and   trans: "\<lbrakk>a \<in> carrier D; b \<in> carrier D; c \<in> carrier D; 
                     (a, b) \<in> rel D; (b, c) \<in> rel D\<rbrakk> \<Longrightarrow> (a, c) \<in> rel D"

(* print_locale Order *)

definition
  ole :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"    (infix "\<preceq>\<index>" 60) where
  "a \<preceq>\<^bsub>D\<^esub> b \<longleftrightarrow> (a, b) \<in> rel D"

definition
  oless :: "_ \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"    (infix "\<prec>\<index>" 60) where
  "a \<prec>\<^bsub>D\<^esub> b \<equiv> a \<preceq>\<^bsub>D\<^esub> b \<and> a \<noteq> b"


lemma Order_component:"(E::'a Order) = \<lparr> carrier = carrier E, rel = rel E \<rparr>"
by simp  (** An ordered set consists of two components **) 

lemma Order_comp_eq:"\<lbrakk>carrier (E::'a Order) = carrier (F::'a Order);
                      rel E = rel F\<rbrakk> \<Longrightarrow> E = F"
by simp (* components coincide then ordered sets coincide. *)

lemma (in Order) le_rel:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                           (a \<preceq> b) = ((a, b) \<in> rel D)"
by (simp add:ole_def) 

lemma (in Order) less_imp_le:
      "\<lbrakk>a \<in> carrier D; b \<in> carrier D; a \<prec> b \<rbrakk> \<Longrightarrow> a \<preceq> b"
by (simp add:oless_def)

lemma (in Order) le_refl:"a \<in> carrier D \<Longrightarrow> a \<preceq> a"
apply (unfold ole_def) 
apply (rule refl, assumption)
done

lemma (in Order) le_antisym:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; 
      a \<preceq> b; b \<preceq> a \<rbrakk> \<Longrightarrow> a = b"
apply (unfold ole_def) 
apply (rule antisym)
apply assumption+
done

lemma (in Order) le_trans:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; c \<in> carrier D;
      a \<preceq> b; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<preceq> c" 
apply (unfold ole_def) 
apply (rule_tac a = a and b = b and c = c in trans)
apply assumption+
done

lemma (in Order) less_trans:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; c \<in> carrier D; 
      a \<prec> b; b \<prec> c \<rbrakk> \<Longrightarrow> a \<prec> c"
apply (unfold oless_def)
apply (erule conjE)+
apply (simp add:le_trans[of a b c])
apply (rule contrapos_pp, simp+)
apply (frule_tac le_antisym[of b c], assumption+)
apply simp
done

lemma (in Order) le_less_trans:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; c \<in> carrier D;
      a \<preceq> b; b \<prec> c \<rbrakk> \<Longrightarrow> a \<prec> c"
apply (simp add:oless_def)  
apply (erule conjE)
apply (simp add:le_trans[of a b c])
apply (rule contrapos_pp, simp+) 
apply (frule le_antisym[of "b" "c"]) 
apply assumption+
apply simp
done

lemma (in Order) less_le_trans:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; c \<in> carrier D;
      a \<prec> b; b \<preceq> c \<rbrakk> \<Longrightarrow> a \<prec> c"
apply (simp add:oless_def)
apply ( erule conjE)
apply (simp add:le_trans[of a b c])
apply (rule contrapos_pp, simp+)
apply (frule le_antisym[of "b" "c"])
apply assumption+
apply simp
done

lemma (in Order) le_imp_less_or_eq:
    "\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow> (a \<preceq> b) = (a \<prec> b \<or> a = b)"
apply (simp add:oless_def)
apply (rule iffI) 
apply simp
apply (erule disjE) 
apply simp
apply simp
apply (rule le_refl)
apply assumption
done

lemma (in Order) less_neq: "a \<prec> b \<Longrightarrow> a \<noteq> b"
  by (simp add: oless_def) 

lemma (in Order) le_neq_less: "\<lbrakk>a \<preceq> b; a \<noteq> b\<rbrakk> \<Longrightarrow> a \<prec> b"
  by (simp add: oless_def)  

lemma (in Order) less_irrefl: "\<lbrakk>a \<in> carrier D; a \<prec> a\<rbrakk> \<Longrightarrow> C"
 by (simp add:oless_def)

lemma (in Order) less_irrefl': "a \<in> carrier D \<Longrightarrow> \<not> a \<prec> a"
by (simp add:oless_def)  

lemma (in Order) less_asym:
  "a \<in> carrier D \<Longrightarrow> b \<in> carrier D \<Longrightarrow> a \<prec> b \<Longrightarrow> b \<prec> a \<Longrightarrow> C"
apply (simp add:oless_def) 
apply (erule conjE)+
apply (frule le_antisym[of "a" "b"])
apply assumption+
apply simp
done

lemma (in Order) less_asym':
  "a \<in> carrier D \<Longrightarrow> b \<in> carrier D \<Longrightarrow> a \<prec> b \<Longrightarrow> \<not> b \<prec> a"
apply (rule contrapos_pp, simp+)
apply (simp add:oless_def)
apply (erule conjE)+
apply (frule le_antisym[of "a" "b"])
apply assumption+
apply simp
done

lemma (in Order) gt_than_any_outside:"\<lbrakk>A \<subseteq> carrier D; b \<in> carrier D;
       \<forall>x\<in>A. x \<prec> b\<rbrakk> \<Longrightarrow> b \<notin> A"
apply (rule contrapos_pp, simp+)
apply (frule_tac x = b in bspec)
apply  (assumption,
       thin_tac "\<forall>x\<in>A. x \<prec> b", simp add:oless_def)
done

definition
  Iod :: "_ \<Rightarrow> 'a set \<Rightarrow> _" where
  "Iod D T =
    D \<lparr>carrier := T, rel := {(a, b). (a, b) \<in> rel D \<and> a \<in> T \<and> b \<in> T}\<rparr>"

definition
  SIod :: "'a Order \<Rightarrow> 'a set \<Rightarrow> 'a Order" where
  "SIod D T = \<lparr>carrier = T, rel = {(a, b). (a, b) \<in> rel D \<and> a \<in> T \<and> b \<in> T}\<rparr>"

lemma (in Order) Iod_self: "D = Iod D (carrier D)"
  apply (unfold  Iod_def)
  apply (cases D)
  apply (insert closed)
  apply (simp add:Iod_def)
  apply (rule equalityI)
  apply (rule subsetI)
  apply auto
done

lemma SIod_self:"Order D \<Longrightarrow> D = SIod D (carrier D)"
apply (unfold SIod_def)
 apply (cases D)
 apply (cut_tac Order.closed[of "D"])
 apply auto
done

lemma (in Order) Od_carrier:"carrier (D\<lparr>carrier := S, rel := R\<rparr>) = S"
by simp

lemma (in Order) Od_rel:"rel (D\<lparr>carrier := S, rel := R\<rparr>) = R"
by simp

lemma (in Order) Iod_carrier:
    "T \<subseteq> carrier D \<Longrightarrow> carrier (Iod D T) = T"
by (simp add: Iod_def) 

lemma SIod_carrier:"\<lbrakk>Order D; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> carrier (SIod D T) = T"
by (simp add:SIod_def)

lemma (in Order) Od_compare:"(S = S' \<and> R = R') = (D\<lparr>carrier := S, rel := R\<rparr> = D\<lparr>carrier := S', rel := R'\<rparr>)"
apply (rule iffI)
 apply simp 
 
 apply (cut_tac Od_carrier[of R S], cut_tac Od_carrier[of R' S'], simp)  
 apply (cut_tac Od_rel[of R S], cut_tac Od_rel[of R' S'])
 apply (thin_tac "S' = S") 
 apply simp
done

lemma (in Order) Iod_le:
  "\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T\<rbrakk> \<Longrightarrow> (a \<preceq>\<^bsub>Iod D T\<^esub> b) = (a \<preceq> b)"
apply (simp add: Iod_def) 
apply (simp add:ole_def)
done

lemma SIod_le:"\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T\<rbrakk> \<Longrightarrow> 
                     (a \<preceq>\<^bsub>SIod D T\<^esub> b) = (a \<preceq>\<^bsub>D\<^esub> b)" 
apply (simp add:SIod_def)
apply (simp add:ole_def)
done

lemma (in Order) Iod_less:
  "\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T\<rbrakk> \<Longrightarrow> (a \<prec>\<^bsub>Iod D T\<^esub> b) = (a \<prec> b)"
apply (simp add:oless_def)
apply (simp add:Iod_le)
done

lemma SIod_less:"\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T\<rbrakk> \<Longrightarrow> 
                     (a \<prec>\<^bsub>SIod D T\<^esub> b) = (a \<prec>\<^bsub>D\<^esub> b)" 
by (simp add:oless_def SIod_le)


lemma (in Order) Iod_Order:
    "T \<subseteq> carrier D \<Longrightarrow> Order (Iod D T)"
apply (rule Order.intro)
apply (simp add:Iod_def)
apply (rule subsetI)
apply (unfold split_paired_all)
apply simp 
apply (simp add:Iod_carrier)
apply (simp add:Iod_def)
apply (rule refl)
apply (rule subsetD, assumption+)
apply (simp add:Iod_carrier) 
apply (simp add:Iod_def)
 apply (rule_tac a = a and b = b in antisym)
apply (simp add:subsetD[of "T" "carrier D"])+
apply (simp add:Iod_def)
apply (rule_tac a = a and b = b and c = c in trans)
apply (simp add:subsetD[of "T" "carrier D"])+
done

lemma  SIod_Order:"\<lbrakk> Order D; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> Order (SIod D T)"
apply (rule Order.intro)
 apply (rule subsetI)
 apply (simp add:SIod_def)
 apply (unfold split_paired_all)
 apply simp
 apply (simp add:SIod_def)
 apply (frule_tac c = a in subsetD[of T "carrier D"], assumption+)
 apply (simp add:Order.refl[of D])

apply (simp add:SIod_def)
 apply (rule Order.antisym[of D], assumption+)
 apply (simp add:subsetD)+

apply (simp add:SIod_def)
 apply (frule_tac c = a in subsetD[of T "carrier D"], assumption+,
        frule_tac c = b in subsetD[of T "carrier D"], assumption+,
        frule_tac c = c in subsetD[of T "carrier D"], assumption+)
 apply (rule_tac a = a and b = b and c = c in Order.trans[of D], assumption+)
done

lemma (in Order) emptyset_Iod:"Order (Iod D {})"
apply (rule Iod_Order)
apply simp
 done
 
lemma (in Order) Iod_sub_sub:
     "\<lbrakk>S \<subseteq> T; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> Iod (Iod D T) S = Iod D S"
apply (simp add:Iod_def)
apply (subst Od_compare[THEN sym])
 apply simp   
 apply blast
done

lemma SIod_sub_sub:
     "\<lbrakk>S \<subseteq> T; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> SIod (SIod D T) S = SIod D S"
apply (simp add:SIod_def)
  apply blast  
done

lemma rel_SIod:"\<lbrakk>Order D; Order E; carrier E \<subseteq> carrier D; 
                  \<forall>a\<in>carrier E. \<forall>b\<in>carrier E. (a \<preceq>\<^bsub>E\<^esub> b) = (a \<preceq>\<^bsub>D\<^esub> b)\<rbrakk> \<Longrightarrow>
                  rel E = rel (SIod D (carrier E))"
apply (rule equalityI) (* show the equality of the sets *)
apply (rule subsetI)
apply (unfold split_paired_all)
apply (simp add:ole_def)
apply (simp add:SIod_def)
 apply (cut_tac Order.closed[of "E"])
apply blast   
apply assumption
apply (rule subsetI)
apply (unfold split_paired_all)
apply (simp add:SIod_def)
apply (simp add:ole_def)
done

lemma SIod_self_le:"\<lbrakk>Order D; Order E; 
         carrier E \<subseteq> carrier D;
        \<forall>a\<in>carrier E. \<forall>b\<in>carrier E. (a \<preceq>\<^bsub>E\<^esub> b) = (a \<preceq>\<^bsub>D\<^esub> b) \<rbrakk> \<Longrightarrow> 
         E = SIod D (carrier E)"  
apply (rule Order_comp_eq[of "E" "SIod D (carrier E)"])
apply (simp add:SIod_carrier)
apply (rule rel_SIod[of "D" "E"], assumption+)
done 

subsection \<open>Total ordering\<close>

locale Torder = Order + 
       assumes le_linear: "\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                            a \<preceq> b \<or> b \<preceq> a"

lemma (in Order) Iod_empty_Torder:"Torder (Iod D {})"
apply (rule Torder.intro)
apply(simp add:emptyset_Iod)
apply (rule Torder_axioms.intro)
apply (simp add:Iod_carrier)
done

lemma (in Torder) le_cases:
  "\<lbrakk>a \<in> carrier D; b \<in> carrier D; (a \<preceq> b \<Longrightarrow> C); (b \<preceq> a \<Longrightarrow> C)\<rbrakk> \<Longrightarrow> C"
by (cut_tac le_linear[of "a" "b"], blast, assumption+) 

lemma (in Torder) Order:"Order D" 
apply (rule Order_axioms)
done

lemma (in Torder) less_linear:
   "a \<in> carrier D \<Longrightarrow> b \<in> carrier D \<Longrightarrow> a \<prec> b \<or> a = b \<or> b \<prec> a"
apply (simp add:oless_def)
apply (rule le_cases[of "a" "b"])
apply assumption+
apply blast
apply blast
done

lemma (in Torder) not_le_less:
  "a \<in> carrier D \<Longrightarrow> b \<in> carrier D \<Longrightarrow>
    (\<not> a \<preceq> b) = (b \<prec> a)"
apply (unfold oless_def)
apply (cut_tac le_linear[of a b])
apply (rule iffI)
apply simp
apply (rule contrapos_pp, simp+)
apply (rule contrapos_pp, simp+)
apply (erule conjE)
apply (frule le_antisym[of b a])
apply assumption+
apply simp+
done

lemma (in Torder) not_less_le:
  "a \<in> carrier D \<Longrightarrow> b \<in> carrier D \<Longrightarrow>
    (\<not> a \<prec> b) = (b \<preceq> a)"
apply (unfold oless_def)
apply (rule iffI)
 apply (simp only:de_Morgan_conj[of "a \<preceq> b" "a \<noteq> b"])
 apply (simp only:not_le_less[of "a" "b"])
 apply (erule disjE)
  apply (simp add:less_imp_le) 
apply (simp add:le_imp_less_or_eq)
apply (rule contrapos_pp, simp+)
 apply (erule conjE)
 apply (frule le_antisym[of "a" "b"])
 apply assumption+
 apply simp
done

lemma (in Order) Iod_not_le_less:"\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T; 
       Torder (Iod D T)\<rbrakk> \<Longrightarrow> (\<not> a \<preceq>\<^bsub>(Iod D T)\<^esub> b) = b \<prec>\<^bsub>(Iod D T)\<^esub> a" 
apply (subst Torder.not_le_less)
apply assumption+ 
apply (simp add:Iod_carrier)+
done

lemma (in Order) Iod_not_less_le:"\<lbrakk>T \<subseteq> carrier D; a \<in> T; b \<in> T; 
       Torder (Iod D T)\<rbrakk> \<Longrightarrow> (\<not> a \<prec>\<^bsub>(Iod D T)\<^esub> b) = b \<preceq>\<^bsub>(Iod D T)\<^esub> a" 
apply (subst Torder.not_less_le)
apply assumption+ 
apply (simp add:Iod_carrier)+
done


subsection \<open>Two ordered sets\<close>

definition
  Order_Pow :: "'a set \<Rightarrow> 'a set Order"    ("(po _)" [999] 1000) where
  "po A =
    \<lparr>carrier = Pow A,
      rel = {(X, Y). X \<in> Pow A \<and> Y \<in> Pow A \<and> X \<subseteq> Y}\<rparr>"

interpretation order_Pow: Order "po A"
  apply (unfold Order_Pow_def)
  apply (rule Order.intro)
apply (rule subsetI)
apply (unfold split_paired_all)
apply simp
apply simp
apply simp
apply simp
done

definition
  Order_fs :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a set * ('a \<Rightarrow> 'b)) Order" where
  "Order_fs A B =
   \<lparr>carrier = {Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> 
                 f \<in> extensional A1 \<and> Z = (A1, f)}, 
 rel = {Y. Y \<in> ({Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1 
 \<and> Z = (A1, f)}) \<times> ({Z. \<exists>A1 f. A1 \<in> Pow A \<and> f \<in> A1 \<rightarrow> B \<and> f \<in> extensional A1
 \<and> Z = (A1, f)}) \<and> fst (fst Y) \<subseteq> fst (snd Y) \<and> 
       (\<forall>a\<in> (fst (fst Y)). (snd (fst Y)) a = (snd (snd Y)) a)}\<rparr>" 

lemma Order_fs:"Order (Order_fs A B)"
apply (simp add:Order_fs_def)
apply (rule Order.intro)
apply (rule subsetI)
apply (unfold split_paired_all)
apply (auto intro: funcset_eq)
done
 
subsection \<open>Homomorphism of ordered sets\<close>

definition
 ord_inj :: "[('a, 'm0) Order_scheme, ('b, 'm1) Order_scheme, 
                'a \<Rightarrow> 'b] \<Rightarrow> bool" where
 "ord_inj D E f \<longleftrightarrow> f \<in> extensional (carrier D) \<and> 
              f \<in> (carrier D) \<rightarrow> (carrier E) \<and> 
              (inj_on f (carrier D)) \<and> 
              (\<forall>a\<in>carrier D. \<forall>b\<in>carrier D. (a \<prec>\<^bsub>D\<^esub> b) = ((f a) \<prec>\<^bsub>E\<^esub> (f b)))"

definition
 ord_isom :: "[('a, 'm0) Order_scheme, ('b, 'm1) Order_scheme,
               'a \<Rightarrow> 'b] \<Rightarrow> bool" where
 "ord_isom D E f \<longleftrightarrow> ord_inj D E f \<and>
                    (surj_to f (carrier D) (carrier E))"

lemma (in Order) ord_inj_func:"\<lbrakk>Order E; ord_inj D E f\<rbrakk> \<Longrightarrow>
                      f \<in> carrier D \<rightarrow> carrier E"
by (simp add:ord_inj_def)

lemma (in Order) ord_isom_func:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow>
                      f \<in> carrier D \<rightarrow> carrier E"
by (simp add:ord_isom_def ord_inj_func)

lemma (in Order) ord_inj_restrict_isom:"\<lbrakk>Order E; ord_inj D E f; T \<subseteq> carrier D\<rbrakk>
    \<Longrightarrow> ord_isom (Iod D T) (Iod E (f ` T)) (restrict f T)"
apply (subst ord_isom_def) (*  The following two lemmas are preliminaries. *) 
 apply (frule ord_inj_func[of E f], assumption,
        frule image_sub[of f "carrier D" "carrier E" "T"], assumption+)

 apply (rule conjI) 
 apply (subst ord_inj_def)
 apply (simp add:Iod_carrier Order.Iod_carrier)

 apply (rule conjI)
    apply (rule restrict_inj[of f "carrier D" "T"])
 apply (simp add:ord_inj_def, assumption+)

 apply (rule ballI)+
 apply (frule_tac x = a in elem_in_image2[of f "carrier D" "carrier E" T],
        assumption+,
        frule_tac x = b in elem_in_image2[of f "carrier D" "carrier E" T],
        assumption+) 
 apply (simp add:Iod_less Order.Iod_less)
 apply (frule_tac c = a in subsetD[of T "carrier D"], assumption+,
        frule_tac c = b in subsetD[of T "carrier D"], assumption+)
 apply (simp add:ord_inj_def)

apply (subst surj_to_def)
 apply (simp add:Iod_carrier Order.Iod_carrier)
done

lemma ord_inj_Srestrict_isom:"\<lbrakk>Order D; Order E; ord_inj D E f; T \<subseteq> carrier D\<rbrakk>
    \<Longrightarrow> ord_isom (SIod D T) (SIod E (f ` T)) (restrict f T)"
apply (subst ord_isom_def) 
 apply (frule Order.ord_inj_func[of D E f], assumption+,
        frule image_sub[of f "carrier D" "carrier E" "T"], assumption+)

 apply (rule conjI) 
 apply (subst ord_inj_def)
 apply (simp add:SIod_carrier)

 apply (rule conjI)
    apply (rule restrict_inj[of f "carrier D" "T"])
 apply (simp add:ord_inj_def, assumption+)

 apply (rule ballI)+
 apply (frule_tac x = a in elem_in_image2[of f "carrier D" "carrier E" T],
        assumption+,
        frule_tac x = b in elem_in_image2[of f "carrier D" "carrier E" T],
        assumption+) 
 apply (simp add:SIod_less)
 apply (frule_tac c = a in subsetD[of T "carrier D"], assumption+,
        frule_tac c = b in subsetD[of T "carrier D"], assumption+)
 apply (simp add:ord_inj_def)

 apply (simp add:SIod_carrier)
 apply (simp add:surj_to_def)
done

lemma (in Order) id_ord_isom:"ord_isom D D (idmap (carrier D))"
apply (simp add:ord_isom_def)
apply (cut_tac idmap_bij[of "carrier D"])
apply (simp add:bij_to_def)
apply (simp add:ord_inj_def)
apply (simp add:idmap_def[of "carrier D"])
done

lemma (in Order) ord_isom_bij_to:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow>
                            bij_to f (carrier D) (carrier E)"
by (simp add:bij_to_def ord_isom_def,
       simp add:ord_inj_def)

lemma (in Order) ord_inj_mem:"\<lbrakk>Order E; ord_inj D E f; a \<in> carrier D\<rbrakk> \<Longrightarrow>
        (f a) \<in> carrier E"
apply (simp add:ord_inj_def, (erule conjE)+)
 apply (simp add:Pi_def)
done

lemma (in Order) ord_isom_mem:"\<lbrakk>Order E; ord_isom D E f; a \<in> carrier D\<rbrakk> \<Longrightarrow>
                (f a) \<in> carrier E"
apply (simp add:ord_isom_def, (erule conjE)+)
apply (simp add:ord_inj_mem)
done

lemma (in Order) ord_isom_surj:"\<lbrakk>Order E; ord_isom D E f; b \<in> carrier E\<rbrakk> \<Longrightarrow>
         \<exists>a\<in>carrier D. b = f a"
apply (simp add:ord_isom_def, (erule conjE)+)
apply (simp add:surj_to_def image_def)
apply (frule sym, thin_tac "{y. \<exists>x\<in>carrier D. y = f x} = carrier E",
       simp)
done

lemma (in Order) ord_isom_surj_forall:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow>
              \<forall>b \<in> carrier E. \<exists>a\<in>carrier D. b = f a"
apply (rule ballI)
apply (rule ord_isom_surj[of "E" "f"], assumption+)
done

lemma (in Order) ord_isom_onto:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow>
         f ` (carrier D) = carrier E "
apply (frule ord_isom_bij_to[of "E" "f"], assumption+)
apply(simp add:bij_to_def surj_to_def)
done

lemma (in Order) ord_isom_inj_on:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow> 
                                              inj_on f (carrier D)"
by (simp add:ord_isom_def ord_inj_def)

lemma (in Order) ord_isom_inj:"\<lbrakk>Order E; ord_isom D E f; 
      a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow> (a = b) = ((f a) = (f b))"
apply (frule ord_isom_inj_on[of E f], assumption)
 apply (simp add:injective_iff)
done

lemma (in Order) ord_isom_surj_to:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow> 
                                     surj_to f (carrier D) (carrier E)"
by (simp add:ord_isom_def)

lemma (in Order) ord_inj_less:"\<lbrakk>Order E; ord_inj D E f; a \<in> carrier D; 
       b \<in> carrier D\<rbrakk> \<Longrightarrow> (a \<prec>\<^bsub>D\<^esub> b) = ((f a) \<prec>\<^bsub>E\<^esub> (f b))"
by  (simp add:ord_inj_def)

lemma (in Order) ord_isom_less:"\<lbrakk>Order E; ord_isom D E f; 
      a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow> (a \<prec>\<^bsub>D\<^esub> b) = ((f a) \<prec>\<^bsub>E\<^esub> (f b))"
by (simp add:ord_isom_def ord_inj_less)

lemma (in Order) ord_isom_less_forall:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow> 
      \<forall>a \<in> carrier D. \<forall> b \<in> carrier D. (a \<prec>\<^bsub>D\<^esub> b) = ((f a) \<prec>\<^bsub>E\<^esub> (f b))"
by ((rule ballI)+,
    simp add:ord_isom_less)

lemma (in Order) ord_isom_le:"\<lbrakk>Order E; ord_isom D E f; 
      a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow> (a \<preceq>\<^bsub>D\<^esub> b) = ((f a) \<preceq>\<^bsub>E\<^esub> (f b))"
apply (frule_tac a = a in ord_isom_mem[of "E" "f"], assumption+,
       frule_tac a = b in ord_isom_mem[of "E" "f"], assumption+)
apply (simp add:le_imp_less_or_eq Order.le_imp_less_or_eq[of "E"]) 
apply (simp add:ord_isom_less ord_isom_inj)
done
 
lemma (in Order) ord_isom_le_forall:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow> 
      \<forall>a \<in> carrier D. \<forall> b \<in> carrier D. (a \<preceq> b) = ((f a) \<preceq>\<^bsub>E\<^esub> (f b))"
by ((rule ballI)+,
       rule ord_isom_le, assumption+)

lemma (in Order) ord_isom_convert:"\<lbrakk>Order E; ord_isom D E f; 
      x \<in> carrier D; a \<in> carrier D\<rbrakk> \<Longrightarrow> (\<forall>y\<in>carrier D. (x \<prec> y \<longrightarrow> \<not> y \<prec> a)) = 
       (\<forall>z\<in>carrier E. ((f x) \<prec>\<^bsub>E\<^esub> z \<longrightarrow> \<not> z \<prec>\<^bsub>E\<^esub> (f a)))"
apply (rule iffI)
 apply (rule ballI, rule impI)
apply (frule_tac b = z in ord_isom_surj[of "E" "f"], assumption+,
        erule bexE)
apply ( simp add:ord_isom_less[THEN sym, of "E" "f"])
apply (rule ballI, rule impI)
apply (simp add:ord_isom_less[of "E" "f"]) 
apply (frule_tac a = y in ord_isom_mem[of "E" "f"], assumption+) 
apply simp
done

lemma (in Order) ord_isom_sym:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow>
                   ord_isom E D (invfun (carrier D) (carrier E) f)"
apply (frule ord_isom_func[of E f], assumption+,
       frule ord_isom_inj_on[of E f], assumption+,
       frule ord_isom_surj_to[of E f], assumption+)

apply (subst ord_isom_def, subst ord_inj_def)
 apply (simp add:inv_func)
 apply (simp add:invfun_inj)
 apply (simp add:invfun_surj)
apply (rule conjI)
 apply (simp add:invfun_def extensional_def)

 apply (rule ballI)+
 apply (frule_tac b = a in invfun_mem[of "f" "carrier D" "carrier E"],
            assumption+,
       frule_tac b = b in invfun_mem[of "f" "carrier D" "carrier E"],
            assumption+)
 apply (frule_tac a = "(f\<inverse>\<^bsub>carrier E,carrier D\<^esub>) a" and b = "(f\<inverse>\<^bsub>carrier E,carrier D\<^esub>) b" 
        in ord_isom_less[of E f], assumption+)
 apply (simp add:invfun_r)
done

lemma (in Order) ord_isom_trans:"\<lbrakk>Order E; Order F; ord_isom D E f; 
       ord_isom E F g \<rbrakk> \<Longrightarrow>  ord_isom D F (compose (carrier D) g f)"
apply (frule ord_isom_func[of E f], assumption+,
       frule ord_isom_inj_on[of E f], assumption+,
       frule ord_isom_surj_to[of E f], assumption+,
       frule Order.ord_isom_func[of E F g], assumption+,
       frule Order.ord_isom_inj_on[of E F g], assumption+,
       frule Order.ord_isom_surj_to[of E F g], assumption+)

(* lemmas concerning compose require assumptions given above *)

apply (subst ord_isom_def, subst ord_inj_def)
 apply (simp add:composition)
 apply (simp add:comp_inj[of "f" "carrier D" "carrier E" "g" "carrier F"])
 apply (simp add:compose_surj)
apply (rule ballI)+
 
 apply (frule_tac x = a in funcset_mem[of f "carrier D" "carrier E"], 
                assumption+,
       frule_tac x = b in funcset_mem[of f "carrier D" "carrier E"], 
       assumption+)
apply (frule_tac a = a and b = b in ord_isom_less[of E f], assumption+,
       frule_tac a = "f a" and b = "f b" in Order.ord_isom_less[of E F g],
       assumption+)
       apply (simp add:compose_def)
done

definition
  ord_equiv :: "[_, ('b, 'm1) Order_scheme] \<Rightarrow> bool" where
  "ord_equiv D E \<longleftrightarrow> (\<exists>f. ord_isom D E f)"

lemma (in Order) ord_equiv:"\<lbrakk>Order E; ord_isom D E f\<rbrakk> \<Longrightarrow> ord_equiv D E"
by (simp add:ord_equiv_def, blast)

lemma (in Order) ord_equiv_isom:"\<lbrakk>Order E; ord_equiv D E\<rbrakk> \<Longrightarrow> 
       \<exists>f. ord_isom D E f"
by (simp add:ord_equiv_def)

lemma (in Order) ord_equiv_reflex:"ord_equiv D D" 
apply (simp add:ord_equiv_def)
apply (cut_tac id_ord_isom, blast)
done

lemma (in Order) eq_ord_equiv:"\<lbrakk>Order E; D = E\<rbrakk> \<Longrightarrow> ord_equiv D E" 
apply (frule sym, thin_tac "D = E")
apply ( simp add:ord_equiv_reflex)
done  

lemma (in Order) ord_equiv_sym:"\<lbrakk>Order E; ord_equiv D E \<rbrakk> \<Longrightarrow> ord_equiv E D"
apply (simp add:ord_equiv_def)
apply (erule exE,
       frule_tac E = E and f = f in ord_isom_sym, assumption+, blast)
done

lemma (in Order) ord_equiv_trans:"\<lbrakk>Order E; Order F; ord_equiv D E; 
       ord_equiv E F\<rbrakk> \<Longrightarrow>  ord_equiv D F"
apply (simp add:ord_equiv_def)
apply (erule exE)+
apply (frule_tac f = f and g = fa in ord_isom_trans [of "E" "F"], 
       assumption+, blast)
done

lemma (in Order) ord_equiv_box:"\<lbrakk>Order E; Order F; ord_equiv D E;
        ord_equiv D F\<rbrakk> \<Longrightarrow> ord_equiv E F"
apply (rule Order.ord_equiv_trans[of E D F])
    apply assumption
   apply (rule Order_axioms)
  apply assumption
 apply (rule ord_equiv_sym) apply assumption+
done

lemma SIod_isom_Iod:"\<lbrakk>Order D; T \<subseteq> carrier D \<rbrakk> \<Longrightarrow>
          ord_isom (SIod D T) (Iod D T) (\<lambda>x\<in>T. x)"
apply (simp add:ord_isom_def ord_inj_def)
apply (simp add:SIod_carrier Order.Iod_carrier)
apply (rule conjI)
 apply (fold idmap_def[of T])

 apply (simp add:SIod_less Order.Iod_less)

 apply (cut_tac A = T in idmap_bij,
        simp add:bij_to_def)
done

definition
  minimum_elem :: "[_ , 'a set, 'a] \<Rightarrow> bool" where
  "minimum_elem = (\<lambda>D X a. a \<in> X \<and> (\<forall>x\<in>X. a \<preceq>\<^bsub>D\<^esub> x))"  

locale Worder = Torder + 
       assumes ex_minimum: "\<forall>X. X \<subseteq> (carrier D) \<and> X \<noteq> {} \<longrightarrow>
  (\<exists>x. minimum_elem D X x)"

lemma (in Worder) Order:"Order D"
by (rule Order) 

lemma (in Worder) Torder:"Torder D"
apply (rule Torder_axioms)
done

lemma (in Worder) Worder:"Worder D" 
apply (rule Worder_axioms)
done

lemma (in Worder) equiv_isom:"\<lbrakk>Worder E; ord_equiv D E\<rbrakk> \<Longrightarrow> 
             \<exists>f. ord_isom D E f"
by (insert Order, frule Worder.Order[of "E"], simp add:ord_equiv_def)

lemma (in Order) minimum_elem_mem:"\<lbrakk>X \<subseteq> carrier D; minimum_elem D X a\<rbrakk>
                              \<Longrightarrow>  a \<in> X"
by (simp add:minimum_elem_def)

lemma (in Order) minimum_elem_unique:"\<lbrakk>X \<subseteq> carrier D; minimum_elem D X a1;
                    minimum_elem D X a2\<rbrakk> \<Longrightarrow> a1 = a2"
apply (frule minimum_elem_mem[of "X" "a1"], assumption+,
       frule minimum_elem_mem[of "X" "a2"], assumption+)
apply (simp add:minimum_elem_def) 
apply (drule_tac x = a2 in bspec, assumption)
apply (drule_tac x = a1 in bspec, assumption)
apply (rule le_antisym[of a1 a2])
apply (simp add:subsetD)+
done 
        
lemma (in Order) compare_minimum_elements:"\<lbrakk>S \<subseteq> carrier D; T \<subseteq> carrier D;
      S \<subseteq> T; minimum_elem D S s; minimum_elem D T t \<rbrakk> \<Longrightarrow> t \<preceq> s"
apply (frule minimum_elem_mem[of "S" "s"], assumption+)
apply (frule subsetD[of "S" "T" "s"], assumption+)
apply (simp add:minimum_elem_def)
done

lemma (in Order) minimum_elem_sub:"\<lbrakk>T \<subseteq> carrier D; X \<subseteq> T\<rbrakk>
        \<Longrightarrow> minimum_elem D X a = minimum_elem (Iod D T) X a"
apply (simp add:minimum_elem_def)
apply (simp add:subset_eq[of X T])
apply (rule iffI, erule conjE)
 apply simp
 apply (rule ballI)
 apply (simp add:Iod_le)
 apply simp
 apply (rule ballI)
 apply (erule conjE)
 apply (simp add:Iod_le)
done

lemma minimum_elem_Ssub:"\<lbrakk>Order D; T \<subseteq> carrier D; X \<subseteq> T\<rbrakk>
        \<Longrightarrow> minimum_elem D X a = minimum_elem (SIod D T) X a"
apply (simp add:minimum_elem_def)

apply (rule iffI)
 apply simp
 apply (rule ballI, erule conjE)
 apply (drule_tac x = x in bspec, assumption)

 apply (frule_tac c = x in subsetD[of "X" "T"], assumption+,
        frule_tac c = a in subsetD[of "X" "T"], assumption+)
 apply (simp add:SIod_le)

apply simp
 apply (rule ballI, erule conjE)
 apply (drule_tac x = x in bspec, assumption)

apply (frule_tac c = x in subsetD[of "X" "T"], assumption+,
        frule_tac c = a in subsetD[of "X" "T"], assumption+)
 apply (simp add:SIod_le)
done

lemma (in Order) augmented_set_minimum:"\<lbrakk>X \<subseteq> carrier D; a \<in> carrier D;
       Y - {a} \<subseteq> X; y - {a} \<noteq> {}; minimum_elem (Iod D X) (Y - {a}) x;
       \<forall>x\<in>X. x \<preceq> a\<rbrakk> \<Longrightarrow>  minimum_elem (Iod D (insert a X)) Y x"
apply (frule insert_mono[of "Y - {a}" "X" "a"])
 apply simp
 apply (frule insert_sub[of X "carrier D" a], assumption+)
 apply (simp add:minimum_elem_sub[THEN sym, of "insert a X" Y],
        simp add:minimum_elem_sub[THEN sym, of X "Y - {a}"])

 apply (simp add:subset_eq[of "Y - {a}" X])

 apply (simp add:minimum_elem_def, (erule conjE)+)
 apply (rule ballI)
 apply blast
done

lemma  augmented_Sset_minimum:"\<lbrakk>Order D; X \<subseteq> carrier D; a \<in> carrier D;
       Y - {a} \<subseteq> X; y - {a} \<noteq> {}; minimum_elem (SIod D X) (Y - {a}) x;
       \<forall>x\<in>X. x \<preceq>\<^bsub>D\<^esub> a\<rbrakk> \<Longrightarrow>  minimum_elem (SIod D (insert a X)) Y x"
apply (frule insert_mono[of "Y - {a}" "X" "a"])
 apply simp
 apply (frule insert_sub[of X "carrier D" a], assumption+)
 apply (simp add:minimum_elem_Ssub[THEN sym, of D "insert a X" Y],
        simp add:minimum_elem_Ssub[THEN sym, of D X "Y - {a}"])

 apply (simp add:subset_eq[of "Y - {a}" X])

 apply (simp add:minimum_elem_def, (erule conjE)+)
 apply (rule ballI)
 apply blast
done

lemma (in Order) ord_isom_minimum:"\<lbrakk>Order E; ord_isom D E f;
S \<subseteq> carrier D; a \<in> carrier D; minimum_elem D S a\<rbrakk> \<Longrightarrow>
              minimum_elem E (f`S) (f a)"
apply (subst minimum_elem_def,
       frule minimum_elem_mem[of "S" "a"], assumption+)
apply (simp add:ord_isom_mem)
apply (rule ballI)
apply (simp add:minimum_elem_def)
apply (frule_tac x = x in bspec, assumption,
       thin_tac "Ball S ((\<preceq>) a)")
apply (frule_tac b = x in ord_isom_le[of E f a], assumption+)
apply (simp add:subsetD)
apply simp
done  

lemma (in Worder) pre_minimum:"\<lbrakk>T \<subseteq> carrier D; minimum_elem D T t; 
s \<in> carrier D; s \<prec>\<^bsub>D\<^esub> t \<rbrakk> \<Longrightarrow> \<not> s \<in> T"
apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def, (erule conjE)+)
 apply (frule_tac x = s in bspec, assumption+,
        thin_tac "\<forall>x\<in>T. t \<preceq>\<^bsub>D\<^esub> x")
 apply (simp add:oless_def, erule conjE)
apply (frule le_antisym[of s t])
apply (simp add:subsetD[of "T" "carrier D"], assumption+)
apply simp
done

lemma bex_nonempty_subset:"\<exists>a. a \<in> A \<and> P a \<Longrightarrow> 
               {x. x \<in> A \<and> P x} \<subseteq> A \<and> {x. x \<in> A \<and> P x} \<noteq> {}"
apply (erule exE, rule conjI)
 apply (rule subsetI, simp)
apply (rule_tac A = "{x \<in> A. P x}" in nonempty, simp)
done 

lemma (in Worder) to_subset:"\<lbrakk>T \<subseteq> carrier D; ord_isom D (Iod D T) f\<rbrakk> \<Longrightarrow> 
            \<forall>a. a \<in> carrier D \<longrightarrow> a \<preceq> (f a)" 
apply (rule contrapos_pp, simp+) 
apply (cut_tac ex_minimum) 
apply (drule_tac a = "{a. a \<in> carrier D \<and> \<not> a \<preceq> f a}" in forall_spec) (*
       thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)") *)
apply (rule conjI)
 apply (rule subsetI, simp)
 apply (rule ex_nonempty, simp)
(*
apply (thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)",
       thin_tac "\<exists>a. a \<in> carrier D \<and> \<not> a \<preceq> f a") *)
apply ((erule exE)+, simp add:minimum_elem_def, (erule conjE)+)
apply (frule Iod_Order[of "T"],
       frule_tac a = x in ord_isom_mem[of "Iod D T" "f"], assumption+)
apply (frule_tac a = x and b = "f x" in ord_isom_le[of "Iod D T" "f"],
       assumption+)
apply (simp add:Iod_carrier subsetD)
apply (frule Iod_carrier[of "T"],
       frule_tac a = "f x" in eq_set_inc[of _ "carrier (Iod D T)" "T"],
           assumption+) 
apply (frule_tac c = "f x" in subsetD[of "T" "carrier D"], assumption+)
apply (frule_tac a = "f x" in ord_isom_mem[of "Iod D T" "f"], assumption+)
apply (frule_tac a = "f (f x)" in eq_set_inc[of _ "carrier (Iod D T)" "T"],
           assumption+)
apply (drule_tac a = "f x" in forall_spec)
   (*    thin_tac "\<forall>xa. xa \<in> carrier D \<and> \<not> xa \<preceq> f xa \<longrightarrow> x \<preceq> xa") *)
apply (simp add:subsetD Iod_le)
apply simp
done

lemma to_subsetS:"\<lbrakk>Worder D; T \<subseteq> carrier D; ord_isom D (SIod D T) f\<rbrakk> \<Longrightarrow> 
            \<forall>a. a \<in> carrier D \<longrightarrow> a \<preceq>\<^bsub>D\<^esub> (f a)"
apply (frule Worder.Order[of "D"],
       frule SIod_isom_Iod[of "D" "T"], assumption+,
       frule Order.ord_isom_trans[of "D" "SIod D T" "Iod D T" f "\<lambda>x\<in>T. x"])
  apply (simp add:SIod_Order, simp add:Order.Iod_Order, assumption+)

  apply (frule_tac D = D and T = T and f = "compose (carrier D) (\<lambda>x\<in>T. x) f" 
        in Worder.to_subset, assumption+) 
  apply (rule allI, rule impI)
  apply (drule_tac a = a in forall_spec, simp)
       (*  thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow> 
                          a \<preceq>\<^bsub>D\<^esub> compose (carrier D) (\<lambda>x\<in>T. x) f a") *)
  apply (frule_tac a = a in Order.ord_isom_mem[of "D" "SIod D T" "f"])
  apply (simp add:SIod_Order, assumption+)
  apply (simp add:SIod_carrier)
  apply (simp add:compose_def)
done

lemma (in Worder) isom_Worder:"\<lbrakk>Order T; ord_isom D T f\<rbrakk> \<Longrightarrow> Worder T"
apply (rule Worder.intro)
apply (rule Torder.intro) 
apply assumption
apply (rule Torder_axioms.intro)
apply (frule_tac b = a in ord_isom_surj[of T f], assumption+,
       frule_tac b = b in ord_isom_surj[of T f], assumption+,
       (erule bexE)+)
apply (cut_tac Torder_axioms, simp add:Torder_axioms_def)
  apply (meson le_cases ord_isom_le)
apply (rule Worder_axioms.intro)
 apply (rule allI, rule impI, erule conjE) 

 apply (frule ord_isom_func[of "T" "f"], assumption+)
 apply (frule ord_isom_bij_to[of "T" "f"], assumption+)
 apply (frule ord_isom_sym[of "T" "f"], assumption+,
        frule Order.ord_isom_func[of "T" "D" 
              "invfun (carrier D) (carrier T) f"])
 apply (rule Order, assumption) 
 apply (frule_tac ?A1.0 = X in  image_sub[of 
        "invfun (carrier D) (carrier T) f" "carrier T" "carrier D"],
        assumption+,
        frule_tac ?A1.0 = X in image_nonempty[of "invfun (carrier D) 
        (carrier T) f" "carrier T" "carrier D"], assumption+)
apply (cut_tac ex_minimum) (** Because D is well ordered **)
apply (drule_tac a = "invfun (carrier D) (carrier T) f ` X" in forall_spec,
   (*  thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)", *)
        simp) apply (
    (* thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)", *)
       erule exE) 
apply (frule_tac S = "invfun (carrier D) (carrier T) f ` X" and a = x in 
       ord_isom_minimum[of "T" "f"], assumption+)
 apply (frule_tac X = "invfun (carrier D) (carrier T) f ` X" and a = x in 
         minimum_elem_mem, assumption+)
 apply (simp add:subsetD) apply assumption 
 apply (simp add:invfun_set, blast)
done  

lemma (in Worder) equiv_Worder:"\<lbrakk>Order T; ord_equiv D T\<rbrakk> \<Longrightarrow> Worder T"
by (simp add:ord_equiv_def,
       erule exE, simp add:isom_Worder)

lemma (in Worder) equiv_Worder1:"\<lbrakk>Order T; ord_equiv T D\<rbrakk> \<Longrightarrow> Worder T"
apply (cut_tac Worder,
       frule Worder.Order[of D],
       frule Order.ord_equiv_sym[of T D], assumption+)
apply (rule equiv_Worder, assumption+)
done

lemma (in Worder) ord_isom_self_id:"ord_isom D D f \<Longrightarrow> f = idmap (carrier D)"
apply (cut_tac Order,
       frule ord_isom_sym [of "D" "f"], assumption+,
       frule ord_isom_func[of "D" "f"], assumption+) 
apply (rule funcset_eq[of "f" "carrier D" "idmap (carrier D)"])
 apply (simp add:ord_isom_def ord_inj_def, simp add:idmap_def)
apply (rule ballI)
 apply (simp add:idmap_def)
 apply (cut_tac subset_self[of "carrier D"],
        frule to_subset [of "carrier D" "f"],
        simp add:Iod_self[THEN sym]) 

 apply (drule_tac a = x in forall_spec, assumption
      (*  thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow>  a \<preceq> (f a)" *))
 apply (frule to_subset [of "carrier D" "invfun (carrier D) (carrier D) f"])
 apply (simp add:Iod_self[THEN sym])
 apply (drule_tac a = x in forall_spec, assumption) (*,
        thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow>  
                          a \<preceq> (invfun (carrier D) (carrier D) f a)") *) 
 apply (frule_tac x = x in funcset_mem [of "f" "carrier D" "carrier D"], 
                          assumption+)
 apply (frule_tac a = x in ord_isom_mem[of  "D" 
              "invfun (carrier D) (carrier D) f"], assumption+)
 apply (frule_tac a = x and b = "invfun (carrier D) (carrier D) f x" in 
        ord_isom_le[of "D" "f"], assumption+) 
apply simp

 apply (frule ord_isom_bij_to[of "D" "f"], assumption+,
        simp add:bij_to_def, erule conjE)
 apply (simp add:invfun_r[of "f" "carrier D" "carrier D"])
 apply (rule_tac a = "f x" and b = x in le_antisym, 
              assumption+) 
done

lemma (in Worder) isom_unique:"\<lbrakk>Worder E; ord_isom D E f; ord_isom D E g\<rbrakk>
      \<Longrightarrow> f = g"
apply (frule Worder.Order[of "E"])
apply (insert Order,
     frule ord_isom_sym[of "E" "g"], assumption+,
     frule ord_isom_trans [of "E" "D" "f"
                             "invfun (carrier D) (carrier E) g"], assumption+,
     frule ord_isom_func[of "D" 
      "compose (carrier D) (invfun (carrier D) (carrier E) g) f"], assumption+)
apply (frule ord_isom_self_id [of  
     "compose (carrier D) (invfun (carrier D) (carrier E) g) f"])
 apply (thin_tac "ord_isom E D (invfun (carrier D) (carrier E) g)")
 apply (cut_tac id_ord_isom, insert Order,
        frule ord_isom_func[of "D" "idmap (carrier D)"], assumption+)

apply (rule funcset_eq[of "f" "carrier D" "g"])
 apply (simp add:ord_isom_def ord_inj_def) 
 apply (simp add:ord_isom_def ord_inj_def)
apply (rule ballI) 
apply (frule_tac x = x in eq_funcs[of 
   "compose (carrier D) (invfun (carrier D) (carrier E) g) f"
   "carrier D" "carrier D" "idmap (carrier D)"], assumption+)
 apply (frule_tac a = x in ord_isom_mem [of "E" "f"], assumption+,
        thin_tac " compose (carrier D) (invfun (carrier D) (carrier E) g) f =
         idmap (carrier D)", 
        simp add:idmap_def compose_def)
 apply (simp add:ord_isom_def[of _ "E" "g"] ord_inj_def, (erule conjE)+)
 apply (frule_tac b = "f x" in invfun_r[of "g" "carrier D" "carrier E"],
        assumption+) 
 apply simp
done
 
definition
  segment :: "_ \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segment D a = (if a \<notin> carrier D then carrier D else
      {x.  x \<prec>\<^bsub>D\<^esub> a \<and> x \<in> carrier D})"

definition
  Ssegment :: "'a Order \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "Ssegment D a = (if a \<notin> carrier D then carrier D else
      {x.  x \<prec>\<^bsub>D\<^esub> a \<and> x \<in> carrier D})"   

lemma (in Order) segment_sub:"segment D a \<subseteq> carrier D"
apply (rule subsetI, simp add:segment_def)
apply (case_tac "a \<notin> carrier D", simp)
apply ( simp add:segment_def)
done

lemma Ssegment_sub:"Ssegment D a \<subseteq> carrier D"
by (rule subsetI, simp add:Ssegment_def,
       case_tac "a \<notin> carrier D", simp, simp add:Ssegment_def)

lemma (in Order) segment_free:"a \<notin> carrier D \<Longrightarrow> 
                 segment D a = carrier D"
by (simp add:segment_def)

lemma Ssegment_free:"a \<notin> carrier D \<Longrightarrow> 
                 Ssegment D a = carrier D"
by (simp add:Ssegment_def)

lemma (in Order) segment_sub_sub:"\<lbrakk>S \<subseteq> carrier D; d \<in> S\<rbrakk> \<Longrightarrow> 
                                  segment (Iod D S) d \<subseteq> segment D d" 
apply (rule subsetI)
 apply (frule_tac c = d in subsetD[of "S" "carrier D"], assumption+)
 apply (simp add:segment_def)
 apply (simp add:Iod_carrier)
 apply (erule conjE, simp add:Iod_less[of "S"])
 apply (simp add:subsetD)
done

lemma Ssegment_sub_sub:"\<lbrakk>Order D; S \<subseteq> carrier D; d \<in> S\<rbrakk> \<Longrightarrow> 
                                  Ssegment (SIod D S) d \<subseteq> Ssegment D d" 
apply (rule subsetI)
 apply (frule_tac c = d in subsetD[of "S" "carrier D"], assumption+)
 apply (simp add:Ssegment_def) 
 apply (simp add:SIod_carrier, erule conjE, simp add:SIod_less[of "S"])
 apply (simp add:subsetD)
done

lemma (in Order) a_notin_segment:"a \<notin> segment D a"
by (simp add:segment_def oless_def)

lemma a_notin_Ssegment:"a \<notin> Ssegment D a"
by (simp add:Ssegment_def oless_def)

lemma (in Order) Iod_carr_segment:
       "carrier (Iod D (segment D a)) = segment D a"
by (cut_tac segment_sub[of "a"], simp add:Iod_carrier)

lemma SIod_carr_Ssegment:"Order D \<Longrightarrow>
        carrier (SIod D (Ssegment D a)) = Ssegment D a"
apply (cut_tac Ssegment_sub[of "D" "a"]) 
apply (simp add:SIod_carrier)
done

lemma (in Order) segment_inc:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                  (a \<prec> b) = (a \<in> segment D b)"
by (simp add:segment_def)

lemma Ssegment_inc:"\<lbrakk>Order D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                  (a \<prec>\<^bsub>D\<^esub> b) = (a \<in> Ssegment D b)"
by (simp add:Ssegment_def)

lemma (in Order) segment_inc1:"b \<in> carrier D \<Longrightarrow>
                  (a \<prec> b \<and> a \<in> carrier D) = (a \<in> segment D b)" 
by (simp add:segment_def) 

lemma Ssegment_inc1:"\<lbrakk>Order D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                  (a \<prec>\<^bsub>D\<^esub> b \<and> a \<in> carrier D) = (a \<in> Ssegment D b)" 
by (simp add:Ssegment_def) 

lemma (in Order) segment_inc_if:"\<lbrakk>b \<in> carrier D;a \<in> segment D b\<rbrakk> \<Longrightarrow>
                                         a \<prec> b"
by (simp add:segment_def)

lemma Ssegment_inc_if:"\<lbrakk>Order D; b \<in> carrier D; a \<in> Ssegment D b\<rbrakk> \<Longrightarrow>
                                         a \<prec>\<^bsub>D\<^esub> b"
by (simp add:Ssegment_def)

lemma (in Order) segment_inc_less:"\<lbrakk>W \<subseteq> carrier D; a \<in> carrier D;
       y \<in> W; x \<in> segment (Iod D W) a; y \<prec> x\<rbrakk> \<Longrightarrow> y \<in> segment (Iod D W) a"
apply (frule Iod_Order[of "W"],
       frule Order.segment_sub[of "Iod D W" "a"],
       frule subsetD[of "segment (Iod D W) a" "carrier (Iod D W)" x],
              assumption+, simp add:Iod_carrier)
apply (case_tac "a \<in> carrier (Iod D W)")
apply (subst Order.segment_inc[THEN sym, of "Iod D W" "y" "a"], assumption,
       simp add:Iod_carrier, simp add:Iod_carrier)
apply (simp add:Iod_carrier, simp add:Iod_less)
apply (rule less_trans[of y x a], (simp add:subsetD)+)
apply (frule Order.segment_inc[THEN sym, of "Iod D W" "x" "a"],
       (simp add:Iod_carrier)+,
       frule_tac Order.segment_sub[of "Iod D W" x],
       frule subsetD[of "segment (Iod D W) a" "W" "x"], assumption+, 
       simp add:Iod_carrier,
       frule_tac subsetD[of "segment (Iod D W) a" W x], assumption+,
       simp add:Iod_less)
apply (simp add:Order.segment_free[of "Iod D W" a], simp add:Iod_carrier)
done  

lemma (in Order) segment_order_less:"\<forall>b\<in>carrier D. \<forall>x\<in> segment D b. \<forall>y\<in> segment D b. (x \<prec> y) = (x \<prec>\<^bsub>(Iod D (segment D b))\<^esub> y)"
by ((rule ballI)+, 
        cut_tac a = b in segment_sub, simp add:Iod_less) 

lemma Ssegment_order_less:"Order D \<Longrightarrow> 
      \<forall>b\<in>carrier D. \<forall>x\<in> Ssegment D b. \<forall>y\<in> Ssegment D b. 
                  (x \<prec>\<^bsub>D\<^esub> y) = (x \<prec>\<^bsub>(SIod D (Ssegment D b))\<^esub> y)"
by ((rule ballI)+, 
        cut_tac a = b in Ssegment_sub[of "D"], simp add:SIod_less) 

lemma (in Order) segment_order_le:"\<forall>b\<in>carrier D. \<forall>x\<in> segment D b. 
      \<forall>y\<in> segment D b. (x \<preceq> y) = (x \<preceq>\<^bsub>(Iod D (segment D b))\<^esub> y)"
by ((rule ballI)+, 
        cut_tac a = b in segment_sub, simp add:Iod_le) 

lemma Ssegment_order_le:"\<forall>b\<in>carrier D. \<forall>x\<in> Ssegment D b. 
      \<forall>y\<in> Ssegment D b. (x \<preceq>\<^bsub>D\<^esub> y) = (x \<preceq>\<^bsub>(SIod D (Ssegment D b))\<^esub> y)"
by ((rule ballI)+, 
        cut_tac a = b in Ssegment_sub[of "D"], simp add:SIod_le) 


lemma (in Torder) Iod_Torder:"X \<subseteq> carrier D \<Longrightarrow> Torder (Iod D X)"
apply (rule Torder.intro)
 apply (simp add:Iod_Order)
apply (rule Torder_axioms.intro)
 apply (simp add:Iod_carrier Iod_le)
  apply (meson contra_subsetD le_cases)
done

lemma  SIod_Torder:"\<lbrakk>Torder D; X \<subseteq> carrier D\<rbrakk> \<Longrightarrow> Torder (SIod D X)"
apply (simp add:Torder_def, simp add:SIod_Order, simp add:Torder_axioms_def)
apply ((rule allI, rule impI)+, 
       simp add:SIod_carrier SIod_le) apply (erule conjE)
 apply (frule_tac c = a in subsetD[of "X" "carrier D"], assumption+,
        frule_tac c = b in subsetD[of "X" "carrier D"], assumption+)
 apply blast
done

lemma (in Order) segment_not_inc:"\<lbrakk>a \<in> carrier D; b \<in> carrier D;
      a \<prec> b\<rbrakk> \<Longrightarrow> b \<notin> segment D a"
apply (rule contrapos_pp, simp+, simp add:segment_def)
apply (simp add:oless_def, (erule conjE)+)
apply (frule le_antisym[of "a" "b"], assumption+, simp)
done

lemma Ssegment_not_inc:"\<lbrakk>Order D; a \<in> carrier D; b \<in> carrier D; a \<prec>\<^bsub>D\<^esub> b\<rbrakk> \<Longrightarrow> 
               b \<notin> Ssegment D a"
apply (rule contrapos_pp, simp+, simp add:Ssegment_def)
apply (simp add:oless_def, (erule conjE)+)
apply (frule Order.le_antisym[of "D" "a" "b"], assumption+, simp)    
done  

lemma (in Torder) segment_not_inc_iff:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                  (a \<preceq> b) =  (b \<notin> segment D a)"
apply (rule iffI)
 apply (simp add:le_imp_less_or_eq,
        erule disjE, simp add:segment_not_inc, simp add:a_notin_segment)
apply (simp add:segment_def, simp add:not_less_le[THEN sym, of "b" "a"])
done

lemma Ssegment_not_inc_iff:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                  (a \<preceq>\<^bsub>D\<^esub> b) =  (b \<notin> Ssegment D a)"
apply (rule iffI)
 apply (frule Torder.Order[of "D"])
 apply (simp add:Order.le_imp_less_or_eq,
        erule disjE, rule Ssegment_not_inc, assumption+)

apply (simp add: a_notin_Ssegment)
apply (simp add:Ssegment_def) 
apply ( simp add:Torder.not_less_le[THEN sym, of "D" "b" "a"])
done

lemma (in Torder) minimum_segment_of_sub:"\<lbrakk>X \<subseteq> carrier D; 
       minimum_elem D (segment (Iod D X) d) m \<rbrakk> \<Longrightarrow> minimum_elem D X m"
apply (case_tac "d \<notin> carrier (Iod D X)")
 apply (simp add:segment_def)
 apply (simp add:Iod_carrier)

apply (simp add:Iod_carrier)
apply (subst minimum_elem_def) 
apply (frule Iod_Order[of "X"],
       frule Order.segment_sub[of "Iod D X" "d"],
       simp add:Iod_carrier,
       frule subset_trans[of "segment (Iod D X) d" "X" "carrier D"],
       assumption+,
       frule minimum_elem_mem[of "segment (Iod D X) d" m], assumption)
 apply (simp add:subsetD[of "segment (Iod D X) d" "X" m])
apply (rule ballI)
 apply (simp add:minimum_elem_def)
 apply (case_tac "x \<in> segment (Iod D X) d")
 apply (frule_tac a1 = x in Order.segment_inc[THEN sym, of "Iod D X" _ d])
 apply (simp add:Iod_carrier subsetD)
 apply (simp add:Iod_carrier)
 apply (simp add:Iod_less)
 apply (frule Iod_Torder[of "X"])
 apply (frule_tac b1 = x in Torder.segment_not_inc_iff[THEN sym, 
                of "Iod D X" d])
     apply (simp add:Iod_carrier)
     apply (simp add:Iod_carrier)
     apply simp
 apply (frule Order.segment_inc[THEN sym, of "Iod D X" m d],
        thin_tac "x \<notin> segment (Iod D X) d",
        frule Order.segment_sub[of "Iod D X" "d"])
        apply (simp add:Iod_carrier subsetD)
        apply (simp add:Iod_carrier)
 apply simp
 apply (frule subsetD[of "segment (Iod D X) d" "X" m], assumption)
 apply (simp add:Iod_le Iod_less) 
 apply (frule subsetD[of X "carrier D" m], assumption+,
        frule subsetD[of X "carrier D" d], assumption+,
        frule_tac c = x in subsetD[of X "carrier D"], assumption+)
 apply (frule_tac c = x in less_le_trans[of m d], assumption+)
 apply (simp add:less_imp_le)
done

lemma (in Torder) segment_out:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; 
      a \<prec> b\<rbrakk> \<Longrightarrow> segment (Iod D (segment D a)) b = segment D a"
apply (subst segment_def[of "Iod D (segment D a)"])
apply (frule segment_not_inc[of "a" "b"], assumption+)
apply (cut_tac segment_sub[of  "a"])       
apply (simp add:Iod_carrier)
done

lemma (in Torder) segment_minimum_minimum:"\<lbrakk>X \<subseteq> carrier D; d \<in> X;
       minimum_elem (Iod D (segment D d)) (X \<inter> (segment D d)) m\<rbrakk> \<Longrightarrow>
       minimum_elem D X m"
apply (cut_tac segment_sub[of d])
apply (subst minimum_elem_def)
apply (cut_tac Order.minimum_elem_mem[of "Iod D (segment D d)" 
                          "X \<inter> (segment D d)" m])
apply (cut_tac Int_lower1[of X "segment D d"],
       frule_tac subsetD[of "X \<inter> segment D d" X m], assumption+, simp)
apply (rule ballI)
apply (case_tac "x \<in> segment D d")
 apply (simp add:minimum_elem_def)
 apply (drule_tac x = x in bspec,
     (* thin_tac "Ball (X \<inter> segment D d) ((\<preceq>\<^bsub>Iod) D (segment D d)\<^esub> m)", *)
        simp) apply (
        simp add:Iod_le)
 apply (frule subsetD[of X "carrier D" d], assumption+,
        frule subsetD[of X "carrier D" m], assumption+,
        frule_tac c = x in subsetD[of X "carrier D"], assumption+)
 apply (simp add:segment_inc[THEN sym, of _ d],
        simp add:not_less_le)
 apply (frule_tac c = x in less_le_trans[of m d], assumption+)
 apply (simp add:less_imp_le)

apply (simp add:Iod_Order)
 apply (simp add:Iod_carrier)
 apply (simp add:Int_lower2)
done

lemma (in Torder) segment_mono:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<prec> b) = (segment D a \<subset> segment D b)"    
apply (rule iffI)
 apply (rule psubsetI, rule subsetI)
 apply (simp add:segment_def, erule conjE)
 apply (rule_tac a = x and b = a and c = b in less_trans,
          assumption+)  
 apply (cut_tac a_notin_segment[of "a"],
        simp add:segment_inc[of "a" "b"], blast)
apply (simp add:psubset_eq, erule conjE,
       frule not_sym[of "segment D a" "segment D b"],
       thin_tac "segment D a \<noteq> segment D b",
       frule sets_not_eq[of "segment D b" "segment D a"], assumption+)
 apply (erule bexE)
 apply (thin_tac "segment D a \<subseteq> segment D b", 
        thin_tac "segment D b \<noteq> segment D a")
 apply (simp add:segment_def, (erule conjE)+)
 apply (frule_tac  a = aa and b = a in not_less_le, assumption+,
        simp, simp add:oless_def, (erule conjE)+)
 apply (frule_tac a = a and b = aa and c = b in le_trans,
        assumption+, simp)
 apply (rule contrapos_pp, simp+)
done

lemma Ssegment_mono:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<prec>\<^bsub>D\<^esub> b) = (Ssegment D a \<subset> Ssegment D b)"
apply (frule Torder.Order)
apply (rule iffI)
 apply (rule psubsetI, rule subsetI)
 apply (simp add:Ssegment_def, erule conjE)
 apply (rule_tac a = x and b = a and c = b in Order.less_trans,
          assumption+)  
 apply (cut_tac a_notin_Ssegment[of "a"],
        simp add:Ssegment_inc[of "D" "a" "b"], blast)
apply (simp add:psubset_eq, erule conjE,
       frule not_sym[of "Ssegment D a" "Ssegment D b"],
       thin_tac "Ssegment D a \<noteq> Ssegment D b",
       frule sets_not_eq[of "Ssegment D b" "Ssegment D a"], assumption+)
 apply (erule bexE)
 apply (thin_tac "Ssegment D a \<subseteq> Ssegment D b", 
        thin_tac "Ssegment D b \<noteq> Ssegment D a")
 apply (simp add:Ssegment_def, (erule conjE)+)
 apply (frule_tac  a = aa and b = a in Torder.not_less_le, assumption+,
        simp, simp add:oless_def, (erule conjE)+)
 apply (frule_tac a = a and b = aa and c = b in Order.le_trans,
        assumption+, simp)
 apply (rule contrapos_pp, simp+)
done

lemma (in Torder) segment_le_mono:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<preceq> b) = (segment D a \<subseteq> segment D b)"
apply (simp add:le_imp_less_or_eq[of "a" "b"])

apply (rule iffI)
apply (erule disjE)
 apply (simp add:segment_mono[of "a" "b"], simp)
 apply (frule segment_mono[THEN sym, of "a" "b"], assumption+)
 apply (simp add:psubset_eq)
apply (case_tac "segment D a \<noteq> segment D b", simp)
 apply simp
 apply (rule contrapos_pp, simp+,
        frule less_linear[of "a" "b"], assumption+, simp,
        simp add:segment_mono[of "b" "a"])
done

lemma Ssegment_le_mono:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<preceq>\<^bsub>D\<^esub> b) = (Ssegment D a \<subseteq> Ssegment D b)"
apply (cut_tac Torder.Order[of "D"])
apply (simp add:Order.le_imp_less_or_eq[of "D" "a" "b"])

apply (rule iffI)
apply (erule disjE)
 apply (simp add: Ssegment_mono[of "D" "a" "b"])

 apply (frule Ssegment_mono[THEN sym, of "D" "a" "b"], assumption+)
 apply (simp add:psubset_eq)
apply (case_tac "Ssegment D a \<noteq> Ssegment D b") 
 apply (cut_tac Ssegment_mono[THEN sym, of "D" "a" "b"])
 apply (simp add:psubset_eq, assumption+)
 apply simp
 apply (cut_tac a_notin_Ssegment[of "a" "D"], simp)
 apply (simp add:Ssegment_not_inc_iff[THEN sym, of "D" "b" "a"])
 apply (frule sym, thin_tac "Ssegment D a = Ssegment D b")
 apply (cut_tac a_notin_Ssegment[of "b" "D"], simp)
 apply (simp add:Ssegment_not_inc_iff[THEN sym, of "D" "a" "b"])
 apply (frule Order.le_antisym[of "D" "a" "b"], assumption+, simp+)
done

lemma (in Torder) segment_inj:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a = b) = (segment D a = segment D b)" 
apply (rule iffI)
 apply simp
apply (rule equalityE[of "segment D a" "segment D b"], assumption) 
apply (thin_tac "segment D a = segment D b")
 apply (simp add:segment_le_mono[THEN sym, of  "a" "b"])
 apply (simp add:segment_le_mono[THEN sym, of  "b" "a"])

 apply (simp add:le_antisym)
done

lemma Ssegment_inj:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a = b) = (Ssegment D a = Ssegment D b)"
 apply (rule iffI)
 apply simp
apply (rule equalityE[of "Ssegment D a" "Ssegment D b"], assumption)

apply (thin_tac "Ssegment D a = Ssegment D b")
 apply (simp add:Ssegment_le_mono[THEN sym, of "D" "a" "b"])
 apply (simp add:Ssegment_le_mono[THEN sym, of  "D" "b" "a"])
 apply (cut_tac Torder.Order[of "D"])
 apply (simp add:Order.le_antisym, assumption)
done 

lemma (in Torder) segment_inj_neq:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<noteq> b) = (segment D a \<noteq> segment D b)" 
by (simp add:segment_inj)

lemma Ssegment_inj_neq:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
                       (a \<noteq> b) = (Ssegment D a \<noteq> Ssegment D b)"
by (simp add:Ssegment_inj) 

lemma (in Order) segment_inc_psub:"\<lbrakk>x \<in> segment D a\<rbrakk> \<Longrightarrow>
                                            segment D x \<subset> segment D a"
apply (simp add:psubset_eq) 
apply (rule conjI, rule subsetI)
 apply (simp add:segment_def)
 apply (case_tac "a \<notin> carrier D", simp)
 apply (simp, (erule conjE)+)
 apply (rule_tac a = xa and b = x and c = a in less_trans, assumption+)
 apply (cut_tac a_notin_segment[of "x"]) apply blast 
done

lemma Ssegment_inc_psub:"\<lbrakk>Order D; x \<in> Ssegment D a\<rbrakk> \<Longrightarrow>
                                            Ssegment D x \<subset> Ssegment D a"
apply (simp add:psubset_eq) 
apply (rule conjI, rule subsetI)
 apply (simp add:Ssegment_def)
 apply (case_tac "a \<notin> carrier D", simp)
 apply (simp, (erule conjE)+)
                             
 apply (rule_tac a = xa and b = x and c = a in Order.less_trans[of "D"], 
               assumption+)

 apply (cut_tac a_notin_Ssegment[of "x"]) apply blast 
done

lemma (in Order) segment_segment:"\<lbrakk>b \<in> carrier D; a \<in> segment D b\<rbrakk> \<Longrightarrow>
                  segment (Iod D (segment D b)) a = segment D a"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:segment_def[of "Iod D (segment D b)" "a"])
 apply (cut_tac segment_sub[of "b"], simp add:Iod_carrier) 
 apply (erule conjE)
 apply (simp add:Iod_less) 
 apply (frule_tac c = x in subsetD[of "segment D b" "carrier D"], assumption+,
        frule_tac c = a in subsetD[of "segment D b" "carrier D"], assumption+)
 apply (simp add:segment_inc[of _ "a"])

apply (rule subsetI)
apply (simp add:segment_def[of "Iod D (segment D b)" "a"])
 apply (cut_tac segment_sub[of "b"], simp add:Iod_carrier) 
 apply (frule segment_inc_psub[of "a" "b"],
        frule psubset_imp_subset[of "segment D a" "segment D b"],
        thin_tac "segment D a \<subset> segment D b",
        frule_tac c = x in subsetD[of "segment D a" "segment D b"], 
        assumption+)
 apply (simp add:Iod_less) apply (simp add:segment_def)
done

lemma Ssegment_Ssegment:"\<lbrakk>Order D; b \<in> carrier D; a \<in> Ssegment D b\<rbrakk> \<Longrightarrow>
                  Ssegment (SIod D (Ssegment D b)) a = Ssegment D a"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:Ssegment_def[of "SIod D (Ssegment D b)" "a"]) 
 apply (cut_tac Ssegment_sub[of "D" "b"], simp add:SIod_carrier) 
 apply (erule conjE)
 apply (simp add:SIod_less) 
 apply (frule_tac c = x in subsetD[of "Ssegment D b" "carrier D"], assumption+,
        frule_tac c = a in subsetD[of "Ssegment D b" "carrier D"], assumption+)
 apply (simp add:Ssegment_inc[of "D"_  "a"]) 

apply (rule subsetI)
apply (simp add:Ssegment_def[of "SIod D (Ssegment D b)" "a"])
 apply (cut_tac Ssegment_sub[of "D" "b"], simp add:SIod_carrier) 
 apply (frule Ssegment_inc_psub[of "D" "a" "b"], assumption,
        frule psubset_imp_subset[of "Ssegment D a" "Ssegment D b"],
        thin_tac "Ssegment D a \<subset> Ssegment D b",
        frule_tac c = x in subsetD[of "Ssegment D a" "Ssegment D b"], 
        assumption+)
 apply (simp add:SIod_less) apply (simp add:Ssegment_def)
done

lemma (in Order) Iod_segment_segment:"a \<in> carrier (Iod D (segment D b)) \<Longrightarrow> 
      Iod (Iod D (segment D b)) (segment (Iod D (segment D b)) a) =
      Iod D (segment D a)"
apply (case_tac "b \<in> carrier D")
apply (cut_tac segment_sub[of "b"])
 apply (simp add:Iod_carrier)
 apply (frule segment_inc_psub[of "a" "b"],
        frule psubset_imp_subset[of "segment D a" "segment D b"],
        thin_tac "segment D a \<subset> segment D b")
 apply (simp add:segment_segment[of "b" "a"])
 apply (simp add:Iod_sub_sub[of "segment D a" "segment D b"])
apply (simp add:segment_def[of D b])
 apply (simp add:Iod_self[THEN sym])
done

lemma SIod_Ssegment_Ssegment:"\<lbrakk>Order D; a \<in> carrier (SIod D (Ssegment D b))\<rbrakk> 
     \<Longrightarrow>
      SIod (SIod D (Ssegment D b)) (Ssegment (SIod D (Ssegment D b)) a) =
      SIod D (Ssegment D a)"
apply (case_tac "b \<in> carrier D")
apply (cut_tac Ssegment_sub[of "D" "b"]) 
 apply (simp add:SIod_carrier[of "D"]) 
 apply (frule Ssegment_inc_psub[of "D" "a" "b"], simp add:subsetD) apply (
        frule psubset_imp_subset[of "Ssegment D a" "Ssegment D b"],
        thin_tac "Ssegment D a \<subset> Ssegment D b")
 apply (simp add:Ssegment_Ssegment[of "D" "b" "a"])
 apply (simp add:SIod_sub_sub[of "Ssegment D a" "Ssegment D b"])
apply (simp add:Ssegment_def[of D b], simp add:SIod_self[THEN sym])
done

lemma (in Order) ord_isom_segment_mem:"\<lbrakk>Order E; 
      ord_isom D E f; a \<in> carrier D; x \<in> segment D a \<rbrakk> \<Longrightarrow> 
                     (f x) \<in> segment E (f a)"

apply (frule segment_inc_if[of "a" "x"], assumption+)
apply (frule ord_isom_less[of "E" "f" "x" "a"], assumption+)
  apply (simp add:segment_def, assumption, simp)

apply (frule ord_isom_mem[of "E" "f" "x"], assumption+,
       simp add:segment_def,
       frule ord_isom_mem[of "E" "f" "a"], assumption+)
apply (simp add:Order.segment_inc[of "E" "f x" "f a"])
done

lemma ord_isom_Ssegment_mem:"\<lbrakk>Order D; Order E; 
      ord_isom D E f; a \<in> carrier D; x \<in> Ssegment D a\<rbrakk> \<Longrightarrow> 
                     (f x) \<in> Ssegment E (f a)"
apply (frule Ssegment_inc_if[of "D" "a" "x"], assumption+)
apply (frule Order.ord_isom_less[of "D" "E" "f" "x" "a"], assumption+)
  apply (simp add:Ssegment_def, assumption, simp)

apply (frule Order.ord_isom_mem[of "D" "E" "f" "x"], assumption+,
       simp add:Ssegment_def,
       frule Order.ord_isom_mem[of "D" "E" "f" "a"], assumption+)
apply (simp add:Ssegment_def) 
done

lemma (in Order) ord_isom_segment_segment:"\<lbrakk>Order E; 
      ord_isom D E f; a \<in> carrier D \<rbrakk> \<Longrightarrow> 
      ord_isom (Iod D (segment D a)) (Iod E (segment E (f a))) 
                                    (\<lambda>x\<in>carrier (Iod D (segment D a)). f x)"
 apply (frule ord_isom_inj_on[of E f], assumption+)
 apply (cut_tac segment_sub[of a])
 apply (frule restrict_inj[of f "carrier D" "segment D a"], assumption)
 apply (frule ord_isom_surj_to[of E f], assumption+)

apply (subst ord_isom_def, subst ord_inj_def)
 apply (simp add:Iod_carr_segment Order.Iod_carr_segment)

 apply (subgoal_tac "restrict f (segment D a) \<in> 
                              segment D a \<rightarrow> segment E (f a)", simp)
 defer
 apply (simp add:ord_isom_segment_mem)

 apply (rule conjI)
 defer
 apply (rule surj_to_test, assumption+)
 apply (rule ballI, simp)
 apply (frule ord_isom_func[of E f], assumption+)
 apply (frule surj_to_el[of f "carrier D" "carrier E"], assumption+,
        
        frule ord_isom_mem[of E f a], assumption+,
        frule Order.segment_sub[of E "f a"],
        frule_tac c = b in subsetD[of "segment E (f a)" "carrier E"],
        assumption+,
 
        drule_tac x = b in bspec, assumption, (*
        thin_tac "\<forall>b\<in>carrier E. \<exists>a\<in>carrier D. f a = b", *)
        erule bexE)
 apply (simp add:Order.segment_inc[THEN sym, of E _ "f a"],
        rotate_tac -1, frule sym, thin_tac "f aa = b", simp,
        frule_tac a1 = aa and b1 = a in ord_isom_less[THEN sym, of E f], 
        assumption+, simp,
        simp add:segment_inc[of _ a], blast)

 apply (rule ballI)+
 apply (frule ord_isom_mem[of E f a], assumption+,
        frule Order.segment_sub[of E "f a"])
 apply (frule_tac x = aa in ord_isom_segment_mem[of E f a], assumption+,
        frule_tac x = b in ord_isom_segment_mem[of E f a], assumption+,

        simp add:Iod_less Order.Iod_less,
        subst ord_isom_less[of E f], assumption+, (simp add:subsetD)+)
done

lemma ord_isom_Ssegment_Ssegment:"\<lbrakk>Order D; Order E; 
      ord_isom D E f; a \<in> carrier D \<rbrakk> \<Longrightarrow> 
      ord_isom (SIod D (Ssegment D a)) (SIod E (Ssegment E (f a))) 
                                  (\<lambda>x\<in>carrier (SIod D (Ssegment D a)). f x)"
apply (frule_tac a = a in Order.ord_isom_mem[of D E f], assumption+) 
apply (cut_tac Ssegment_sub[of D a],
       cut_tac Ssegment_sub[of "E" "f a"]) 

apply (subst ord_isom_def, simp add:ord_inj_def)
apply (rule conjI) 
 apply (rule Pi_I)
 apply (simp add:SIod_carrier)
 apply (frule_tac c = x in subsetD[of "Ssegment D a" "carrier D"], assumption+)
  apply (frule_tac a = x in Order.ord_isom_mem[of D E f], assumption+)
 apply (subst Ssegment_inc[THEN sym, of "E" _ "f a"], assumption+)
 apply (subst Order.ord_isom_less[THEN sym, of D E f _ a], assumption+)
 apply (subst Ssegment_inc[of D _ a], assumption+) 
 apply (rule conjI)
  apply (simp add:SIod_carrier)
  apply (simp add:ord_isom_def bij_to_def, (erule conjE)+)
  apply (simp add:ord_inj_def, (erule conjE)+)
  apply (rule restrict_inj[of "f" "carrier D" "Ssegment D a"], assumption+)
apply (rule conjI)
 apply (rule ballI)+
 apply (simp add:SIod_carrier)
 apply (frule_tac c = aa in subsetD[of "Ssegment D a" "carrier D"], 
        assumption+,
        frule_tac c = b in subsetD[of "Ssegment D a" "carrier D"], assumption+)
 apply (frule_tac a1 = aa and b1 = a in Ssegment_inc[THEN sym], assumption+,
        frule_tac a1 = b and b1 = a in Ssegment_inc[THEN sym], assumption+,
        simp)
 apply (simp add:Order.ord_isom_less[of D E f]) 
 apply (frule_tac a = a in Order.ord_isom_mem[of D E f], assumption+,
        frule_tac a = aa in Order.ord_isom_mem[of D E f], assumption+,
        frule_tac a = b in Order.ord_isom_mem[of D E f], assumption+)
 apply (simp add:Ssegment_inc[of E])
 apply (simp add:SIod_less Order.ord_isom_less)
 apply (simp add:surj_to_def,
        simp add:SIod_carrier)
 apply (rule equalityI)
  apply (rule subsetI, simp add:image_def, erule bexE)
  apply (frule_tac c = xa in subsetD[of "Ssegment D a" "carrier D"], 
         assumption+)
  apply (frule_tac a = xa in Ssegment_inc[of D _ a], assumption+, simp)
  apply (simp add:Order.ord_isom_less[of D E f _ a])
  apply (frule_tac a = xa in Order.ord_isom_mem[of D E f], assumption+)
  apply (subst Ssegment_inc[THEN sym], assumption+)

 apply (rule subsetI)
  apply (frule_tac c = x in subsetD[of "Ssegment E (f a)" "carrier E"], 
         assumption+)
  apply (simp add:Ssegment_inc[THEN sym])
  apply (frule_tac b = x in Order.ord_isom_surj[of D E f], assumption+,
         erule bexE, simp, thin_tac "x = f aa")
  apply (simp add:Order.ord_isom_less[THEN sym])
  apply (simp add:Ssegment_inc[of D])
done

lemma (in Order) ord_equiv_segment_segment:
   "\<lbrakk>Order E; ord_equiv D E; a \<in> carrier D\<rbrakk>
    \<Longrightarrow> \<exists>t\<in>carrier E. ord_equiv (Iod D (segment D a)) (Iod E (segment E t))"

apply (simp add:ord_equiv_def, erule exE)
apply (frule_tac f = f in ord_isom_segment_segment[of E _ a], assumption+)
apply (frule_tac f = f in ord_isom_mem[of E _ a], assumption+)
apply blast
done

lemma ord_equiv_Ssegment_Ssegment:
  "\<lbrakk>Order D; Order E; ord_equiv D E; a \<in> carrier D\<rbrakk>
  \<Longrightarrow> \<exists>t\<in>carrier E. ord_equiv (SIod D (Ssegment D a)) (SIod E (Ssegment E t))"
apply (simp add:ord_equiv_def, erule exE)
apply (frule_tac f = f in  ord_isom_Ssegment_Ssegment[of "D" "E" _ "a"], 
       assumption+)
apply (frule_tac f = f in Order.ord_isom_mem[of D E _ a], assumption+)
apply blast
done

lemma (in Order) ord_isom_restricted:
      "\<lbrakk>Order E; ord_isom D E f; D1 \<subseteq> carrier D\<rbrakk> \<Longrightarrow> 
             ord_isom (Iod D D1) (Iod E (f ` D1)) (\<lambda>x\<in>D1. f x)"
apply (simp add:ord_isom_def[of D E f], erule conjE)
 apply (simp add:ord_inj_restrict_isom[of E f D1])
done

lemma ord_isom_restrictedS:
      "\<lbrakk>Order D; Order E; ord_isom D E f; D1 \<subseteq> carrier D\<rbrakk> \<Longrightarrow> 
             ord_isom (SIod D D1) (SIod E (f ` D1)) (\<lambda>x\<in>D1. f x)"
apply (simp add:ord_isom_def[of D E f], erule conjE)
 apply (simp add:ord_inj_Srestrict_isom[of D E f D1])
done

lemma (in Order) ord_equiv_induced:
      "\<lbrakk>Order E; ord_isom D E f; D1 \<subseteq> carrier D \<rbrakk> \<Longrightarrow> 
                         ord_equiv (Iod D D1) (Iod E (f ` D1))"
apply (simp add:ord_equiv_def) 
apply (frule ord_isom_restricted [of "E" "f" "D1"], assumption+)
 apply blast
done

lemma ord_equiv_inducedS:
      "\<lbrakk>Order D; Order E; ord_isom D E f; D1 \<subseteq> carrier D \<rbrakk> \<Longrightarrow> 
                        ord_equiv (SIod D D1) (SIod E (f ` D1))"
apply (simp add:ord_equiv_def)
apply (frule ord_isom_restrictedS [of "D" "E" "f" "D1"], assumption+)
 apply blast
done

lemma (in Order) equiv_induced_by_inj:"\<lbrakk>Order E; ord_inj D E f; 
      D1 \<subseteq> carrier D\<rbrakk> \<Longrightarrow>  ord_equiv (Iod D D1) (Iod E (f ` D1))"
apply (simp add:ord_equiv_def)
apply (frule ord_inj_restrict_isom [of E f D1], assumption+)
apply blast
done

lemma equiv_induced_by_injS:"\<lbrakk>Order D; Order E; ord_inj D E f; 
      D1 \<subseteq> carrier D\<rbrakk> \<Longrightarrow>  ord_equiv (SIod D D1) (SIod E (f ` D1))"
apply (simp add:ord_equiv_def)
apply (frule ord_inj_Srestrict_isom[of D E f D1], assumption+)
apply blast
done

lemma (in Torder) le_segment_segment:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
           (a \<preceq> b) = (segment (Iod D (segment D b)) a = segment D a)"
apply (cut_tac segment_sub[of b],
       frule Iod_Order[of "segment D b"])
apply (case_tac "a = b") apply simp
 apply (simp add:le_refl)
 apply ( cut_tac a_notin_segment[of "b"])
 apply (subst Order.segment_free[of "Iod D (segment D b)" b], assumption)
    apply (simp add:Iod_carrier)
    apply (simp add:Iod_carrier)
apply (subst le_imp_less_or_eq[of "a" "b"], assumption+, simp)

apply (rule iffI) 
 apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac a1 = x in Order.segment_inc[THEN sym, 
                    of "Iod D (segment D b)" _ a])
   apply (frule_tac Order.segment_sub[of "Iod D (segment D b)" a])
   apply (rule subsetD, assumption+)
   apply (simp add:Iod_carrier) apply (simp add:segment_inc)
   apply simp
   apply (subst segment_inc[THEN sym])
   apply (simp add:segment_def Iod_def) apply assumption
  apply (simp add:segment_inc)
  apply (frule Order.segment_sub[of "Iod D (segment D b)" a])
  apply (simp add:Iod_carrier)
  apply (simp add:subsetD Iod_less)
apply (rule subsetI)
  apply (subst Order.segment_inc[THEN sym, of "Iod D (segment D b)"],
         assumption+)
  apply (simp add:Iod_carrier)
  apply (simp add:segment_mono[of a b] psubset_eq, erule conjE)
  apply (rule subsetD[of "segment D a" "segment D b"], assumption+)
  apply (simp add:Iod_carrier segment_inc)
  apply (frule segment_inc[of a b], assumption, simp)
  apply (frule segment_mono[of a b], assumption, simp)
  apply (simp add:psubset_eq, (erule conjE)+)
  apply (frule_tac c = x in subsetD[of "segment D a" "segment D b"], 
         assumption+)
  apply (simp add:Iod_less)
  apply (subst segment_inc) apply (simp add:subsetD) apply assumption+
 apply (rule contrapos_pp, simp+)
 apply (simp add:not_less_le)
 apply (simp add:le_imp_less_or_eq) 
 apply (frule segment_not_inc[of b a], assumption+)
 apply (frule Order.segment_free[of "Iod D (segment D b)" a])
       apply (simp add:Iod_carrier)
       apply (simp add:Iod_carrier)
 apply (simp add:segment_inj[THEN sym, of b a])
done

lemma le_Ssegment_Ssegment:"\<lbrakk>Torder D; a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
           (a \<preceq>\<^bsub>D\<^esub> b) = (Ssegment (SIod D (Ssegment D b)) a = Ssegment D a)"
apply (frule Torder.Order[of "D"])
apply (case_tac "a = b") apply simp
 apply (simp add:Order.le_refl)

 apply (cut_tac Ssegment_sub[of "D" "b"])
 apply (frule SIod_Order[of "D" "Ssegment D b"], assumption)

apply (cut_tac a_notin_Ssegment[of "b" "D"])

 apply (frule SIod_carrier[THEN sym, of "D" "Ssegment D b"], assumption+)
 apply (frule eq_set_not_inc[of "b" "Ssegment D b" 
                         "carrier (SIod D (Ssegment D b))"], assumption+)
 apply (thin_tac "b \<notin> Ssegment D b",
        thin_tac "Ssegment D b = carrier (SIod D (Ssegment D b))")
 apply (cut_tac Ssegment_free[of "b" "SIod D (Ssegment D b)" ])
 apply (simp add:SIod_carrier) apply assumption+


apply (subst Order.le_imp_less_or_eq[of "D" "a" "b"], assumption+)
apply simp

apply (cut_tac Ssegment_sub[of "D" "b"])
apply (subst Ssegment_def[of "SIod D (Ssegment D b)"],
       subst SIod_carrier[of "D" "Ssegment D b"], assumption+) 
apply (subst Ssegment_inc[of "D" "a" "b"], assumption+)

apply (rule iffI) apply simp
 apply (simp add:SIod_carrier)
 apply (rule equalityI)
 apply (rule subsetI)
 apply (simp, erule conjE)
 apply (simp add:SIod_less)
 apply (subst Ssegment_def, simp add:Ssegment_def)

 apply (rule subsetI, simp)
 apply (simp add:Ssegment_inc[THEN sym, of "D" "a" "b"])
 apply (cut_tac a1 = x in Ssegment_inc[THEN sym, of  "D" _ "a"], assumption+)
  apply (simp add:Ssegment_def, assumption, simp)
  apply (cut_tac a = x in Order.less_trans[of "D"  _ "a" "b"], assumption)
   apply (simp add:Ssegment_def, assumption+)

 apply (cut_tac a = x in Ssegment_inc[of "D" _ "b"], assumption)
   apply (simp add:Ssegment_def)
   apply assumption+
   apply simp
 apply (cut_tac a = a in Ssegment_inc[of "D" _ "b"])
   apply assumption+
   apply simp
   apply (simp add:SIod_less)
 
apply (rule contrapos_pp, simp+)
 apply (simp add:SIod_carrier)
 apply (frule sym, thin_tac "Ssegment D b = Ssegment D a", simp)
 apply (simp add:Ssegment_inc[THEN sym, of "D" "a" "b"])
 apply (simp add:Torder.not_less_le[of "D" "a" "b"])
 
 apply (frule not_sym, thin_tac "a \<noteq> b")
 apply (simp add:Order.le_imp_less_or_eq[of "D" "b" "a"])
 apply (simp add:Ssegment_inc[of "D" "b" "a"])
 apply (simp add:a_notin_Ssegment[of "b" "D"])
done 

lemma (in Torder) inc_segment_segment:"\<lbrakk>b \<in> carrier D;
      a \<in> segment D b\<rbrakk> \<Longrightarrow> segment (Iod D (segment D b)) a = segment D a"

apply (cut_tac segment_sub[of "b"],
       frule subsetD[of "segment D b" "carrier D" "a"], assumption)
apply (subst le_segment_segment[THEN sym, of "a" "b"],
         assumption+)
 apply (simp add:segment_inc[THEN sym])
 apply (simp add:less_imp_le)
done

lemma (in Torder) segment_segment:"\<lbrakk>a \<in> carrier D; b \<in> carrier D\<rbrakk> \<Longrightarrow>
      (segment (Iod D (segment D b)) a = segment D a) =
      ((segment D a) \<subseteq>  (segment D b))" 
apply (subst le_segment_segment[THEN sym, of "a" "b"],
        assumption+)
apply (simp add:segment_le_mono[of "a" "b"])
done 

lemma (in Torder) less_in_Iod:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; a \<prec> b\<rbrakk>
      \<Longrightarrow> (a \<prec> b) = (a \<in> carrier (Iod D (segment D b)))"
apply (simp add:Iod_def segment_inc)
done


definition
  SS :: "_ \<Rightarrow> 'a set Order" where
  "SS D = \<lparr>carrier = {X. \<exists>a\<in>carrier D. X = segment D a}, rel =
    {XX. XX \<in> {X. \<exists>a\<in>carrier D. X = segment D a} \<times> 
    {X. \<exists>a\<in>carrier D. X = segment D a} \<and> ((fst XX) \<subseteq> (snd XX))} \<rparr>"
(** Ordered set consisting of segments **)

definition
  segmap::"_ \<Rightarrow> 'a \<Rightarrow> 'a set" where
  "segmap D = (\<lambda>x\<in>(carrier D). segment D x)"

lemma segmap_func:"segmap D \<in> carrier D \<rightarrow> carrier (SS D)"
by (simp add:SS_def segmap_def Pi_def) blast

lemma (in Worder) ord_isom_segmap:" ord_isom D (SS D) (segmap D)"
apply (simp add:ord_isom_def)
apply (rule conjI)
 apply (simp add:ord_inj_def)
apply (rule conjI)
 apply (simp add:segmap_def)

apply (rule conjI)
 apply (simp add:segmap_func)

apply (rule conjI)
 apply (simp add:inj_on_def)
 apply ((rule ballI)+, rule impI, simp add:segmap_def,
        simp add:segment_inj[THEN sym]) 
 apply (rule ballI)+
 apply (simp add:oless_def[of "SS D"]) apply (simp add:ole_def SS_def)
 apply (rule iffI)
  apply (simp add:oless_def, erule conjE)
  apply (frule_tac a = a and b = b in segment_le_mono, assumption+)
  apply (simp add:segment_inj segmap_def) 
  apply blast
 apply (erule conjE)+
   apply (thin_tac "\<exists>aa\<in>carrier D. segmap D a = segment D aa",
          thin_tac " \<exists>a\<in>carrier D. segmap D b = segment D a")
   apply (simp add:segmap_def segment_inj[THEN sym])
   apply (simp add:segment_le_mono[THEN sym])
   apply (simp add:oless_def)
  apply (rule surj_to_test[of "segmap D" "carrier D" "carrier (SS D)"])
  apply (simp add:segmap_func)
  apply (rule ballI)
  apply (simp add:SS_def, erule bexE, simp)
  apply (simp add:segmap_def, blast)
done

lemma (in Worder) nonequiv_segment:"a \<in> carrier D \<Longrightarrow>
                                   \<not> ord_equiv D (Iod D (segment D a))"
apply (rule contrapos_pp, simp+)
 apply (simp add:ord_equiv_def)
 apply (erule exE)
 apply (cut_tac segment_sub[of "a"]) 
 apply (frule Iod_Order[of "segment D a"])
 apply (frule_tac f = f in ord_isom_func[of "Iod D (segment D a)"],
               assumption+)
 apply (frule_tac f = f and a = a in ord_isom_mem[of "Iod D (segment D a)"]
        , assumption+)
 apply (frule_tac f = f in to_subset [of "segment D a"], assumption+)
 apply (drule_tac a = a in forall_spec, assumption) (*
 apply (thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow>  a \<preceq> (f a)") *)
        
 apply (simp add:Iod_carrier) 
 apply (frule_tac c = "f a" in subsetD[of "segment D a" "carrier D" ], 
         assumption+)
 apply (simp add:segment_inc[THEN sym])
 apply (simp add:not_le_less[THEN sym, of "a" _])
done

lemma nonequiv_Ssegment:"\<lbrakk>Worder D; a \<in> carrier D\<rbrakk> \<Longrightarrow>
                                   \<not> ord_equiv D (SIod D (Ssegment D a))"
apply (frule Worder.Order[of "D"], frule Worder.Torder[of "D"])
apply (rule contrapos_pp, simp+)
 apply (simp add:ord_equiv_def)
 apply (erule exE)

 apply (cut_tac Ssegment_sub[of "D" "a"]) 
 apply (frule SIod_Order[of "D" "Ssegment D a"], assumption)
 apply (frule_tac f = f in Order.ord_isom_func[of "D" "SIod D (Ssegment D a)"],
               assumption+,
 frule_tac f = f and a = a in Order.ord_isom_mem[of "D" 
                                       "SIod D (Ssegment D a)"], assumption+)
 apply (frule_tac f = f in to_subsetS [of "D" "Ssegment D a"], assumption+)
 apply (drule_tac a = a in forall_spec, assumption) (*
        thin_tac "\<forall>a. a \<in> carrier D \<longrightarrow> a \<preceq>\<^bsub>D\<^esub> f a") *)

 apply (simp add:SIod_carrier) 
 apply (frule_tac c = "f a" in subsetD[of "Ssegment D a" "carrier D"], 
        assumption+)
 apply (simp add:Ssegment_inc[THEN sym])
 apply (simp add:Torder.not_le_less[THEN sym, of "D" "a" _])
done

lemma (in Worder) subset_Worder:" T \<subseteq> carrier D \<Longrightarrow>
                    Worder (Iod D T)"
apply (rule Worder.intro)
 apply (simp add: Iod_Torder) 
 apply (rule Worder_axioms.intro)
 apply (rule allI, rule impI)
 apply (simp add:Iod_carrier, erule conjE)
 apply (cut_tac ex_minimum)
 apply (frule_tac A = X and B = T and C = "carrier D" in subset_trans, 
        assumption+)
 apply (frule_tac a = X in forall_spec, simp,
        thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)")
 apply (erule exE)
 apply (simp add:minimum_elem_sub)
 apply blast
done

lemma SIod_Worder:"\<lbrakk>Worder D; T \<subseteq> carrier D\<rbrakk> \<Longrightarrow> Worder (SIod D T)"
apply (frule Worder.Order[of "D"],
       frule Worder.Torder[of "D"])
apply (rule Worder.intro)
apply (simp add: SIod_Torder) 
apply (rule Worder_axioms.intro)
 apply (rule allI, rule impI, erule conjE, simp add:SIod_carrier)
 apply (frule Worder.ex_minimum)
 apply (frule_tac A = X and B = T and C = "carrier D" in subset_trans, 
        assumption+) 
 apply (frule_tac a = X in forall_spec, simp,
        thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)")
 apply (simp add:minimum_elem_Ssub)
done

lemma (in Worder) segment_Worder:"Worder (Iod D (segment D a))"
apply (rule subset_Worder [of "segment D a"])
 apply (rule segment_sub[of a])
done

lemma Ssegment_Worder:"Worder D \<Longrightarrow>Worder (SIod D (Ssegment D a))"
apply (rule SIod_Worder, assumption)
apply (rule Ssegment_sub[of "D" "a"])
done

lemma (in Worder) segment_unique1:"\<lbrakk>a \<in> carrier D; b \<in> carrier D; a \<prec> b\<rbrakk> \<Longrightarrow>
       \<not> ord_equiv (Iod D (segment D b)) (Iod D (segment D a))"
apply (cut_tac segment_Worder[of b],
       cut_tac segment_sub[of b],
       frule segment_mono[of a b], assumption, simp add:psubset_eq,
       erule conjE) 
apply (simp add:segment_inc,
       frule Worder.nonequiv_segment[of "Iod D (segment D b)" a],
       simp add:Iod_carrier)
 apply (frule segment_segment[THEN sym, of a b], assumption, simp)
 apply (simp add:Iod_sub_sub[of "segment D a" "segment D b"])
done
 
lemma Ssegment_unique1:"\<lbrakk>Worder D; a \<in> carrier D; b \<in> carrier D; a \<prec>\<^bsub>D\<^esub> b\<rbrakk> \<Longrightarrow>
       \<not> ord_equiv (SIod D (Ssegment D b)) (SIod D (Ssegment D a))"
apply (frule Worder.Order[of "D"], frule Worder.Torder[of "D"],
       frule Ssegment_inc[of "D" "a" "b"], assumption+, simp,
       frule Ssegment_Worder [of "D" "b"])

 apply (cut_tac Ssegment_sub[of "D" "b"]) apply (
        frule Ssegment_mono[of D a b], assumption+, simp)
 apply (frule nonequiv_Ssegment[of "SIod D (Ssegment D b)" "a"]) 
       apply (simp add:SIod_carrier)
       apply (frule le_Ssegment_Ssegment[of D a b], assumption+)
       apply (simp add:oless_def psubset_eq, (erule conjE)+)
 apply (simp add:SIod_sub_sub[of "Ssegment D a" "Ssegment D b"])
done

lemma (in Worder) segment_unique:"\<lbrakk>a \<in> carrier D; b \<in> carrier D;
      ord_equiv (Iod D (segment D a)) (Iod D (segment D b)) \<rbrakk> \<Longrightarrow> a = b"
apply (cut_tac segment_sub[of a],
       frule_tac Iod_Order[of "segment D a"],
       cut_tac segment_sub[of b],
       frule_tac Iod_Order[of "segment D b"])
apply (rule contrapos_pp, simp+)
apply (frule less_linear[of "a" "b"], assumption+)
apply simp
apply (erule disjE)
apply (frule segment_unique1[of "a" "b"], assumption+)
apply (simp add:Order.ord_equiv_sym[of "Iod D (segment D a)" 
                                                "Iod D (segment D b)"])

apply (simp add:segment_unique1[of "b" "a"])
done

lemma Ssegment_unique:"\<lbrakk>Worder D; a \<in> carrier D; b \<in> carrier D;
      ord_equiv (SIod D (Ssegment D a)) (SIod D (Ssegment D b)) \<rbrakk> \<Longrightarrow> a = b"
apply (frule Worder.Order[of "D"], frule Worder.Torder[of "D"],
       cut_tac Ssegment_sub[of "D" "b"],
       cut_tac Ssegment_sub[of "D" "a"],
       frule SIod_Order[of "D" "Ssegment D a"], assumption,
       frule SIod_Order[of "D" "Ssegment D b"], assumption)

apply (rule contrapos_pp, simp+)
apply (frule Torder.less_linear[of "D" "a" "b"], assumption+)
apply simp

apply (erule disjE)
apply (frule Ssegment_unique1[of "D" "a" "b"], assumption+)
apply (simp add:Order.ord_equiv_sym[of "SIod D (Ssegment D a)" 
                                                "SIod D (Ssegment D b)"])

apply (simp add:Ssegment_unique1[of "D" "b" "a"])
done

lemma (in Worder) subset_segment:"\<lbrakk>T \<subseteq> carrier D; 
      \<forall>b\<in>T. \<forall>x. x \<prec> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T;
      minimum_elem D (carrier D - T) a\<rbrakk> \<Longrightarrow> T = segment D a"
apply (cut_tac Diff_subset[of "carrier D" T],
       frule minimum_elem_mem [of "carrier D - T" a], assumption,
       simp, erule conjE)
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac c = x in subsetD[of T "carrier D"], assumption+)
 apply (subst segment_inc[THEN sym], assumption+)
  apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
  apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = a in not_less_le, assumption+)
 apply (simp add:le_imp_less_or_eq, thin_tac "\<not> x \<prec> a")
 apply (erule disjE)
 apply (frule_tac a = a in forall_spec) apply (
        thin_tac "\<forall>xa. xa \<prec> x \<and> xa \<in> carrier D \<longrightarrow> xa \<in> T")
        apply simp apply simp apply simp

 apply (rule subsetI)
 apply (cut_tac a = a in segment_sub)
 apply (frule_tac c = x and A = "segment D a" in subsetD[of _ "carrier D"],
        assumption+)
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
 apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def)
 apply (frule_tac x = x in bspec, simp)
 apply (simp add:segment_inc[THEN sym])
 apply (simp add:not_le_less[THEN sym])
done

lemma subset_Ssegment:"\<lbrakk>Worder D; T \<subseteq> carrier D; 
      \<forall>b\<in>T. \<forall>x. x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T;
      minimum_elem D (carrier D - T) a\<rbrakk> \<Longrightarrow> T = Ssegment D a"
apply (cut_tac Diff_subset[of "carrier D" T],
       frule Worder.Torder[of D],
       frule Worder.Order[of D],
       frule Order.minimum_elem_mem [of D "carrier D - T" a], assumption+,
       simp, erule conjE)
apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac c = x in subsetD[of T "carrier D"], assumption+)
 apply (subst Ssegment_inc[THEN sym], assumption+)
  apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
  apply (rule contrapos_pp, simp+)
 apply (frule_tac a = x and b = a in Torder.not_less_le, assumption+)
 apply (simp add:Order.le_imp_less_or_eq, thin_tac "\<not> x \<prec>\<^bsub>D\<^esub> a")
 apply (erule disjE)
 apply (frule_tac a = a in forall_spec) apply (
        thin_tac "\<forall>xa. xa \<prec>\<^bsub>D\<^esub> x \<and> xa \<in> carrier D \<longrightarrow> xa \<in> T")
        apply simp apply simp apply simp

 apply (rule subsetI)
 apply (cut_tac a = a in Ssegment_sub[of D])
 apply (frule_tac c = x and A = "Ssegment D a" in subsetD[of _ "carrier D"],
        assumption+)
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
 apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def)
 apply (frule_tac x = x in bspec, simp,
        thin_tac "Ball (carrier D - T) ((\<preceq>\<^bsub>D\<^esub>) a)")
 apply (simp add:Ssegment_inc[THEN sym])
 apply (simp add:Torder.not_le_less[THEN sym])
done


lemma (in Worder) segmentTr:"\<lbrakk>T \<subseteq> carrier D; 
         \<forall>b \<in> T. (\<forall>x.  (x \<prec> b \<and> x \<in> (carrier D) \<longrightarrow> x \<in> T))\<rbrakk> \<Longrightarrow> 
         (T = carrier D) \<or> (\<exists>a. a \<in> (carrier D) \<and> T = segment D a)"
apply (case_tac "T = carrier D")
 apply simp

apply simp

apply (frule not_sym, thin_tac "T \<noteq> carrier D",
       frule diff_nonempty[of "carrier D" "T"], assumption)
 apply (cut_tac ex_minimum)
 apply (frule_tac a = "carrier D - T" in forall_spec, simp)
 apply (thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)") 
 
 apply (erule exE, rename_tac a)
 apply (thin_tac "carrier D \<noteq> T", thin_tac "carrier D - T \<noteq> {}")
 apply (cut_tac Diff_subset[of "carrier D" "T"])
 apply (frule_tac a = a in minimum_elem_mem[of "carrier D - T"],
               assumption+,
        thin_tac "carrier D - T \<subseteq> carrier D")
 apply (simp only:Diff_iff, erule conjE)
 apply (frule_tac a = a in subset_segment[of T], assumption+)
 apply blast
done

lemma SsegmentTr:"\<lbrakk>Worder D; T \<subseteq> carrier D; 
         \<forall>b \<in> T. (\<forall>x.  (x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> (carrier D) \<longrightarrow> x \<in> T))\<rbrakk> \<Longrightarrow> 
         (T = carrier D) \<or> (\<exists>a. a \<in> (carrier D) \<and> T = Ssegment D a)"
apply (case_tac "T = carrier D")
 apply simp

apply simp
apply (frule not_sym, thin_tac "T \<noteq> carrier D",
       frule diff_nonempty[of "carrier D" "T"], assumption)
 apply (cut_tac Worder.ex_minimum[of D])
 apply (frule_tac a = "carrier D - T" in forall_spec, simp)
 apply (thin_tac "\<forall>X. X \<subseteq> carrier D \<and> X \<noteq> {} \<longrightarrow> (\<exists>x. minimum_elem D X x)") 
 
 apply (erule exE, rename_tac a)
 apply (thin_tac "carrier D \<noteq> T", thin_tac "carrier D - T \<noteq> {}")
 apply (cut_tac Diff_subset[of "carrier D" "T"])
 apply (frule Worder.Order[of D])
 apply (frule_tac a = a in Order.minimum_elem_mem[of D "carrier D - T"],
               assumption+,
        thin_tac "carrier D - T \<subseteq> carrier D")
 apply (simp only:Diff_iff, erule conjE)
 apply (subgoal_tac "T = Ssegment D a")
 apply blast

apply (rule equalityI)
 apply (rule subsetI)
 apply (frule_tac c = x in subsetD[of T "carrier D"], assumption+)
 apply (subst Ssegment_inc[THEN sym], assumption+)
  apply (frule_tac x = x in bspec, assumption,
        thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
  apply (rule contrapos_pp, simp+)
 apply (frule Worder.Torder[of D],
        frule_tac a = x and b = a in Torder.not_less_le[of D], assumption+)
 apply (simp add:Order.le_imp_less_or_eq, thin_tac "\<not> x \<prec>\<^bsub>D\<^esub> a")
 apply (erule disjE)
 apply (frule_tac a = a in forall_spec) apply (
        thin_tac "\<forall>xa. xa \<prec>\<^bsub>D\<^esub> x \<and> xa \<in> carrier D \<longrightarrow> xa \<in> T")
        apply simp apply simp apply simp

 apply (rule subsetI)
 apply (frule Worder.Torder[of D],
        frule Torder.Order[of D])
 apply (cut_tac a = a in Ssegment_sub[of D])
 apply (frule_tac c = x and A = "Ssegment D a" in subsetD[of _ "carrier D"],
        assumption+)
 apply (thin_tac "\<forall>b\<in>T. \<forall>x. x \<prec>\<^bsub>D\<^esub> b \<and> x \<in> carrier D \<longrightarrow> x \<in> T")
 apply (rule contrapos_pp, simp+)
 apply (simp add:minimum_elem_def)
 apply (frule_tac x = x in bspec, simp)
 apply (simp add:Ssegment_inc[THEN sym])
 apply (simp add:Torder.not_le_less[THEN sym])
apply assumption
done

lemma (in Worder) ord_isom_segment_segment:"\<lbrakk>Worder E; 
      ord_isom D E f; a \<in> carrier D \<rbrakk> \<Longrightarrow> 
      ord_isom (Iod D (segment D a)) (Iod E (segment E (f a))) 
                                    (\<lambda>x\<in>carrier (Iod D (segment D a)). f x)"
by (frule Worder.Order[of "E"],
       rule ord_isom_segment_segment[of "E" "f" "a"], assumption+) 

definition
  Tw :: "[_ , ('b, 'm1) Order_scheme] \<Rightarrow> 'a \<Rightarrow> 'b"  ("(2Tw\<^bsub>_,_\<^esub>)" [60,61]60) where
  "Tw\<^bsub>D,T\<^esub> = (\<lambda>a\<in> carrier D. SOME x. x\<in>carrier T \<and>
    ord_equiv (Iod D (segment D a)) (Iod T (segment T x)))"

lemma (in Worder) Tw_func:"\<lbrakk>Worder T; 
     \<forall>a\<in>carrier D. \<exists>b\<in>carrier T. ord_equiv (Iod D (segment D a)) 
         (Iod T (segment T b))\<rbrakk> \<Longrightarrow> Tw\<^bsub>D,T\<^esub> \<in> carrier D \<rightarrow> carrier T" 
apply (rule Pi_I)
 apply (simp add:Tw_def)
 apply (rule someI2_ex) apply blast apply simp
done

lemma (in Worder) Tw_mem:"\<lbrakk>Worder E; x \<in> carrier D;
     \<forall>a\<in>carrier D. \<exists>b\<in>carrier E. ord_equiv (Iod D (segment D a)) 
         (Iod E (segment E b))\<rbrakk> \<Longrightarrow> (Tw\<^bsub>D,E\<^esub>) x \<in> carrier E" 
by (frule Tw_func[of E], assumption,
       simp add:Pi_def)

lemma (in Worder) Tw_equiv:"\<lbrakk>Worder T; 
      \<forall>a\<in>carrier D. \<exists>b\<in>carrier T. ord_equiv (Iod D (segment D a)) 
                         (Iod T (segment T b)); x \<in> carrier D \<rbrakk> \<Longrightarrow> 
      ord_equiv (Iod D (segment D x)) (Iod T (segment T ((Tw\<^bsub>D,T\<^esub>) x)))"
apply (frule_tac x = x in bspec, assumption+,
      thin_tac "\<forall>a\<in>carrier D.
      \<exists>b\<in>carrier T. ord_equiv (Iod D (segment D a)) (Iod T (segment T b))")

apply (simp add:Tw_def)
apply (rule someI2_ex)
 apply blast apply simp
done 

lemma (in Worder) Tw_inj:"\<lbrakk>Worder E; 
      \<forall>a\<in>carrier D. \<exists>b\<in>carrier E.  ord_equiv (Iod D (segment D a)) 
       (Iod E (segment E b))\<rbrakk> \<Longrightarrow> inj_on (Tw\<^bsub>D,E\<^esub>) (carrier D)" 

 apply (simp add:inj_on_def)
 apply (rule ballI)+ apply (rule impI) 

 apply (frule_tac x = x in Tw_equiv [of "E"], assumption+)
 apply simp

apply (frule Tw_func[of "E"], assumption)
 apply (frule_tac x = x in funcset_mem[of "Tw D E" "carrier D" "carrier E"],
                    assumption+,
        frule_tac x = y in funcset_mem[of "Tw D E" "carrier D" "carrier E"],
                    assumption+)
 apply (frule Worder.Order[of "E"],
        cut_tac a = x in segment_sub,
        cut_tac a = y in segment_sub,
        cut_tac a = "Tw D E y" in Order.segment_sub[of "E"], assumption)

 apply (frule_tac T = "segment D x" in Iod_Order, 
        frule_tac T = "segment D y" in Iod_Order, 
        frule_tac T = "segment E (Tw D E y)" in Order.Iod_Order[of "E"],
        assumption) 
 
 apply (thin_tac "Tw D E x = Tw D E y")
 apply (frule_tac x = y in Tw_equiv[of "E"], assumption+)
 apply (frule_tac D = "Iod D (segment D y)" and 
        E = "Iod E (segment E (Tw D E y))" in Order.ord_equiv_sym,
        assumption+,
        thin_tac "ord_equiv (Iod D (segment D y))
                   (Iod E (segment E (Tw D E y)))")
 apply (frule_tac D = "Iod D (segment D x)" and 
        E = "Iod E (segment E (Tw D E y))" and 
        F = "Iod D (segment D y)" in Order.ord_equiv_trans, assumption+) 
 apply (simp add:segment_unique)
done

lemma (in Worder) Tw_eq_ord_isom:"\<lbrakk>Worder E; 
        \<forall>a\<in>carrier D. \<exists>b\<in>carrier E.
        ord_equiv (Iod D (segment D a)) (Iod E (segment E b)); a \<in> carrier D;
        ord_isom (Iod D (segment D a)) (Iod E (segment E (Tw D E a))) f;
        x \<in> segment D a \<rbrakk> \<Longrightarrow> f x = Tw D E x" 
apply (cut_tac segment_sub[of a]) 

 apply (frule_tac c = x in subsetD[of "segment D a" "carrier D"], assumption+,
        frule Tw_equiv[of E x], assumption+) 

 apply (frule Worder.Torder[of E],
        frule Torder.Order[of E])
 apply (cut_tac a = x in segment_Worder,
        frule_tac D = "Iod D (segment D x)" in Worder.Torder,
        frule_tac D = "Iod D (segment D x)" in Worder.Order)
 apply (frule_tac T = "segment D a" in Iod_Order)
 apply (frule_tac x = a in Tw_mem[of E], assumption+)
 apply (frule_tac a = "Tw D E x" in Order.segment_sub[of E])
 apply (frule_tac a = "Tw D E a" in Worder.segment_Worder,
        frule_tac D = "Iod E (segment E (Tw D E a))" in Worder.Order) 
 apply (frule_tac f = f and a = x in Order.ord_isom_segment_segment[of 
       "Iod D (segment D a)" "Iod E (segment E (Tw D E a))"], assumption+)
       apply (simp add:Iod_carrier)
 
 apply (frule_tac a = x and b = a in segment_le_mono, assumption+)
 apply (frule_tac a1 = x and b1 = a in segment_inc[THEN sym], assumption+)
 apply (simp add:oless_def) 
 apply (frule_tac a1 = x and b1 = a in segment_segment[THEN sym], assumption+)
 apply simp
 apply (simp add:Iod_sub_sub)

 apply (frule_tac f = f and a = x in Order.ord_isom_mem[of 
        "Iod D (segment D a)" "Iod E (segment E (Tw D E a))"],
        simp add:Iod_carrier,
        frule Order.segment_sub[of E "Tw D E a"],
        simp add:Order.Iod_carrier, simp add:Iod_carrier,
        frule Order.segment_sub[of E "Tw D E a"],
        simp add:Order.Iod_carrier[of E],
        frule_tac c = "f x" in subsetD[of "segment E (Tw D E a)"
               "carrier E"], assumption+)
 apply (frule_tac a1 = "f x" in Order.segment_inc[THEN sym, of E _ 
         "Tw D E a"], assumption+, simp)
 apply (simp add:oless_def, (erule conjE)+) 
 apply (frule_tac a = "f x" and b = "Tw D E a" in 
          Torder.segment_le_mono [of E], assumption+, simp)
 apply (frule_tac a = "f x" and b = "Tw D E a" in 
              Order.segment_segment[of E], assumption+)
 apply simp
 apply (simp add:Order.Iod_sub_sub)

 apply (frule_tac D = "Iod D (segment D x)" in Torder.Order)
 apply (frule_tac D = "Iod D (segment D x)" and E = "Iod E (segment E (f x))"
        and F = "Iod E (segment E (Tw D E x))" in Order.ord_equiv_box)
  apply (frule_tac a = "f x" in Order.segment_sub[of E])
  apply (frule_tac T = "segment E (f x)" in Order.Iod_Order[of E], assumption+)
  apply (frule_tac a = "f x" in Order.segment_sub[of E])
  apply (frule Tw_mem[of E x], assumption+)
  apply (frule Order.segment_sub[of E "Tw D E x"])
  apply (rule Order.Iod_Order[of E], assumption+)
  
  apply (simp add:ord_equiv_def, blast)
  apply assumption
 apply (frule_tac a = "f x" and b = "Tw D E x" in 
         Worder.segment_unique[of E], assumption+)
 apply (frule_tac x = x in Tw_mem[of E], assumption+)
done
     
lemma (in Worder) Tw_ord_injTr:"\<lbrakk>Worder E;
        \<forall>a\<in>carrier D. \<exists>b\<in>carrier E.
        ord_equiv (Iod D (segment D a)) (Iod E (segment E b));
        a \<in> carrier D; b \<in> carrier D;  a \<prec> b\<rbrakk> \<Longrightarrow>  
              Tw D E a \<prec>\<^bsub>E\<^esub> (Tw D E b)"
 apply (frule_tac x = b in Tw_equiv [of "E"], assumption+)
 apply (simp add:segment_inc)
 apply (simp add:ord_equiv_def, erule exE, fold ord_equiv_def)
 apply (frule_tac f = f in Tw_eq_ord_isom[of E b _ a], assumption+)
 apply (cut_tac segment_sub[of b])
 apply (frule Iod_Order[of "segment D b"])
 apply (frule Worder.Order[of E],
        frule Tw_mem[of  E b], assumption+,
        frule Order.segment_sub[of E "Tw D E b"],
        frule Order.Iod_Order[of E "segment E (Tw D E b)"], assumption)
 apply (frule_tac f = f and a = a in Order.ord_isom_mem[of 
        "Iod D (segment D b)" "Iod E (segment E (Tw D E b))"], assumption+)
        apply (simp add:Iod_carrier)
        apply (simp add:Order.Iod_carrier)
        apply (subst Order.segment_inc[of E], assumption+)
        apply (simp add:Tw_mem)+
done

lemma (in Worder) Tw_ord_inj:"\<lbrakk>Worder E; 
       \<forall>a\<in>carrier D. \<exists>b\<in>carrier E. ord_equiv (Iod D (segment D a)) 
            (Iod E (segment E b))\<rbrakk> \<Longrightarrow> ord_inj D E (Tw D E)"
apply (simp add:ord_inj_def)
 apply (rule conjI)
 apply (simp add:Tw_def extensional_def)
 apply (simp add:Tw_func)
apply (rule conjI)
 apply (simp add:Tw_inj)
apply (rule ballI)+

apply (rule iffI)
 apply (simp add:Tw_ord_injTr)

apply (rule contrapos_pp, simp+)
 apply (simp add:not_less_le)
 apply (simp add:le_imp_less_or_eq)
 apply (erule disjE)

 apply (frule_tac a = b and b = a in Tw_ord_injTr[of "E"], assumption+)
 apply (frule Tw_func [of "E"], assumption+)
 apply (frule_tac x = a in funcset_mem[of "Tw D E" "carrier D" "carrier E"],
           assumption+,
        frule_tac x = b in funcset_mem[of "Tw D E" "carrier D" "carrier E"],
           assumption+) 
  
 apply (frule Worder.Torder[of "E"],
        frule_tac a1 = "Tw D E b" and b1 = "Tw D E a" in 
           Torder.not_le_less[THEN sym, of "E"], assumption+, simp)

 apply (frule Worder.Order[of "E"],
        frule_tac a = "Tw D E b" and b = "Tw D E a" in 
           Order.less_imp_le[of "E"], assumption+, simp)
 apply (simp add:oless_def)
done

lemma (in Worder) ord_isom_restricted_by_Tw:"\<lbrakk>Worder E; 
      \<forall>a\<in>carrier D. \<exists>b\<in>carrier E.  
             ord_equiv (Iod D (segment D a)) (Iod E (segment E b));
       D1 \<subseteq> carrier D\<rbrakk> \<Longrightarrow> 
  ord_isom (Iod D D1) (Iod E ((Tw D E) ` D1)) 
                                  (restrict (Tw D E) D1)"
apply (frule Tw_ord_inj [of "E"], assumption+) 
apply (frule Worder.Order[of E])
apply (rule ord_inj_restrict_isom   [of E "Tw D E" "D1"], assumption+)
done

lemma (in Worder) Tw_segment_segment:"\<lbrakk>Worder E;
     \<forall>a\<in>carrier D.\<exists>b\<in>carrier E. 
        ord_equiv (Iod D (segment D a)) (Iod E (segment E b)); a \<in> carrier D\<rbrakk>
     \<Longrightarrow> Tw D E ` (segment D a) = segment E (Tw D E a)"
apply (rule equalityI)
 apply (rule subsetI)
 apply (simp add:image_def, erule bexE)
 apply (frule Tw_equiv[of "E" "a"], assumption+)
 apply (simp add:ord_equiv_def, erule exE, fold ord_equiv_def) 
 apply (frule_tac x = xa in Tw_eq_ord_isom[of E a], assumption+)
 apply (rotate_tac -1, frule sym, thin_tac "f xa = Tw D E xa", simp)
 apply (cut_tac segment_sub[of a],
        frule Iod_Order[of "segment D a"])
 apply (frule Worder.Order[of E],
        frule_tac a = "Tw D E a" in Order.segment_sub[of E],
        frule Tw_mem[of E a], assumption+,
        frule Order.segment_sub[of E "Tw D E a"])
 apply (frule_tac T = "segment E (Tw D E a)" in Order.Iod_Order[of E],
        assumption+)
 apply (frule_tac a = xa and f = f and D = "Iod D (segment D a)" and 
        E = "Iod E (segment E (Tw D E a))" in Order.ord_isom_mem,
        assumption+)
        apply (simp add:Iod_carrier)
        apply (simp add:Order.Iod_carrier)

 apply (rule subsetI)
 apply (simp add:image_def)
 apply (frule Tw_equiv[of "E" "a"], assumption+)
 apply (simp add:ord_equiv_def, erule exE, fold ord_equiv_def)
  apply (cut_tac segment_sub[of a],
        frule Iod_Order[of "segment D a"])
 apply (frule Worder.Order[of E],
        frule_tac a = "Tw D E a" in Order.segment_sub[of E],
        frule Tw_mem[of E a], assumption+,
        frule Order.segment_sub[of E "Tw D E a"])
 apply (frule_tac T = "segment E (Tw D E a)" in Order.Iod_Order[of E],
        assumption+)
 apply (frule Iod_Order[of "segment D a"])
 apply (frule_tac b = x in Order.ord_isom_surj [of "Iod D (segment D a)"
       "Iod E (segment E (Tw D E a))"], assumption+)
       apply (simp add:Order.Iod_carrier)
 apply (erule bexE, simp add:Iod_carrier)
 apply (frule_tac f = f and x = aa in Tw_eq_ord_isom[of E a], assumption+)
 apply (simp, blast)
done
  
lemma (in Worder) ord_isom_Tw_segment:"\<lbrakk>Worder E; 
 \<forall>a\<in>carrier D. \<exists>b\<in>carrier E. 
       ord_equiv (Iod D (segment D a)) (Iod E (segment E b)); a\<in>carrier D\<rbrakk> \<Longrightarrow>
  ord_isom (Iod D (segment D a)) (Iod E (segment E (Tw D E a))) 
              (restrict (Tw D E) (segment D a))"
apply (cut_tac segment_sub[of "a"],
       frule ord_isom_restricted_by_Tw[of "E" "segment D a"], assumption+,
       simp add:Tw_segment_segment[of "E" "a"])
done

lemma (in Worder) well_ord_compare1:"\<lbrakk>Worder E; 
      \<forall>a\<in>carrier D. \<exists>b\<in>carrier E. 
          ord_equiv (Iod D (segment D a)) (Iod E (segment E b))\<rbrakk> \<Longrightarrow> 
    (ord_equiv D E) \<or> (\<exists>c\<in>carrier E. ord_equiv D (Iod E (segment E c)))"
apply (frule Tw_ord_inj [of "E"], assumption+)
apply (frule Tw_func[of "E"], assumption+)

apply (frule ord_isom_restricted_by_Tw [of "E" "carrier D"], assumption+,
       simp)
      apply (simp add:Iod_self[THEN sym])

apply (frule image_sub0[of "Tw D E" "carrier D" "carrier E"], 
       frule Worder.segmentTr [of "E" "(Tw D E) ` (carrier D)"],
       assumption)

 apply (rule ballI, rule allI, rule impI, erule conjE)
 apply (thin_tac "ord_isom D (Iod E (Tw D E ` carrier D))
      (restrict (Tw D E) (carrier D))")
  
 apply (thin_tac "Tw D E ` carrier D \<subseteq> carrier E",
        simp add:image_def, erule bexE)
 apply (frule_tac a = xa in ord_isom_Tw_segment[of "E"], assumption+)
 apply (rename_tac b x c)
  apply (frule_tac x = c in funcset_mem[of "Tw D E" "carrier D" "carrier E"],
        assumption, simp, thin_tac "b = Tw D E c")
 apply (frule Worder.Order[of "E"],
        frule_tac a = "Tw D E c" in Order.segment_sub[of "E"],
        cut_tac a = c in segment_Worder,
        cut_tac a = "Tw D E c" in Worder.segment_Worder[of "E"], 
        assumption,
        frule_tac D = "Iod D (segment D c)" in Worder.Order,
        frule_tac D = "Iod E (segment E (Tw D E c))" in Worder.Order)
 apply (frule_tac D = "Iod D (segment D c)" and 
        E = "Iod E (segment E (Tw D E c))" and 
        f = "restrict (Tw D E) (segment D c)" and b = x in 
        Order.ord_isom_surj, assumption+)
        apply (simp add:Order.Iod_carrier[of "E"])
 apply (frule_tac a = x and b = "Tw D E c" in Order.segment_inc[of "E"],
        assumption+, simp)
 apply (insert Order,
        cut_tac a = c in segment_sub,
        simp add:Iod_carrier, erule bexE, blast)
 
apply (erule disjE)
 apply simp 
 apply (frule Worder.Order[of "E"],
        simp add:Order.Iod_self[THEN sym, of "E"],
        simp add:ord_equiv)

apply (erule exE, erule conjE, simp,
       frule Worder.Order[of "E"],
       frule_tac a = a in Order.segment_sub[of "E"],
       cut_tac a = a in Worder.segment_Worder[of "E"], 
       assumption,
       frule_tac D = "Iod E (segment E a)" in Worder.Order,
       frule_tac E = "Iod E (segment E a)" in ord_equiv, simp, blast)
done

lemma bex_nonempty_set:"\<exists>x \<in> A. P x \<Longrightarrow> {x. x \<in> A \<and> P x } \<noteq> {}" 
by blast

lemma nonempty_set_sub:"{x. x \<in> A \<and> P x } \<noteq> {} \<Longrightarrow> 
                                    {x. x \<in> A \<and> P x} \<subseteq> A"
by (rule subsetI, simp)

lemma (in Torder) less_minimum:"\<lbrakk>minimum_elem D {x. x \<in> carrier D \<and> P x} d\<rbrakk>
       \<Longrightarrow> \<forall>a. (((a \<prec> d) \<and> a \<in> carrier D) \<longrightarrow>  \<not> (P a))"
apply (rule allI, rule impI, erule conjE)
apply (rule contrapos_pp, simp+)
apply (simp add:minimum_elem_def, (erule conjE)+)
apply (frule_tac a = a in forall_spec, simp,
       thin_tac "\<forall>x. x \<in> carrier D \<and> P x \<longrightarrow> d \<preceq> x")
apply (simp add:not_le_less[THEN sym, of "d"])
done

lemma (in Torder) segment_minimum_empty:"\<lbrakk>X \<subseteq> carrier D; d \<in> X\<rbrakk> \<Longrightarrow> 
             (minimum_elem D X d) = (segment (Iod D X) d = {})"
apply (rule iffI)
apply (rule contrapos_pp, simp+)
apply (frule nonempty_ex[of "segment (Iod D X) d"], erule exE,
       thin_tac "segment (Iod D X) d \<noteq> {}",
       frule minimum_elem_mem[of "X" "d"], assumption+,
       frule_tac c = d in subsetD[of "X" "carrier D"], assumption+)
apply (simp add:segment_def,
       simp add:Iod_carrier, erule conjE,
       simp add:Iod_less[of "X"])
apply (simp add:minimum_elem_def,
       frule_tac x = x in bspec, assumption,
       frule_tac c = x in subsetD[of "X" "carrier D"], assumption+,
       frule_tac a1 = x and b1 = d in not_less_le[THEN sym], assumption+)
apply simp

apply (rule contrapos_pp, simp+)
apply (simp add:minimum_elem_def)
apply (erule bexE)
apply (frule_tac c = d in subsetD[of "X" "carrier D"], assumption+,
       frule_tac c = x in subsetD[of "X" "carrier D"], assumption+,
       simp add:not_le_less)  
apply (simp add:segment_def Iod_carrier,
       simp add:Iod_less[THEN sym, of "X"])
done

end
