(*  Title:      HOL/MicroJava/BV/Listn.thy
    Author:     Tobias Nipkow
    Copyright   2000 TUM

Lists of a fixed length.
*)

section \<open>Fixed Length Lists\<close>

theory Listn
imports Err
begin

definition list :: "nat \<Rightarrow> 'a set \<Rightarrow> 'a list set"
where
  "list n A = {xs. size xs = n \<and> set xs \<subseteq> A}"

definition le :: "'a ord \<Rightarrow> ('a list)ord"
where
  "le r = list_all2 (\<lambda>x y. x \<sqsubseteq>\<^sub>r y)"

abbreviation
  lesublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^bsub>r\<^esub>] y == x <=_(Listn.le r) y"

abbreviation
  lesssublist :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^bsub>_\<^esub>] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^bsub>r\<^esub>] y == x <_(Listn.le r) y"

(*<*)
notation (ASCII)
  lesublist  ("(_ /[<=_] _)" [50, 0, 51] 50) and
  lesssublist  ("(_ /[<_] _)" [50, 0, 51] 50)

abbreviation (input)
  lesublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubseteq>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubseteq>\<^sub>r] y == x [\<sqsubseteq>\<^bsub>r\<^esub>] y"

abbreviation (input)
  lesssublist2 :: "'a list \<Rightarrow> 'a ord \<Rightarrow> 'a list \<Rightarrow> bool"  ("(_ /[\<sqsubset>\<^sub>_] _)" [50, 0, 51] 50) where
  "x [\<sqsubset>\<^sub>r] y == x [\<sqsubset>\<^bsub>r\<^esub>] y"
(*>*)

abbreviation
  plussublist :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^bsub>_\<^esub>] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^bsub>f\<^esub>] y == x \<squnion>\<^bsub>map2 f\<^esub> y"

(*<*)
notation
  plussublist  ("(_ /[+_] _)" [65, 0, 66] 65)

abbreviation (input)
  plussublist2 :: "'a list \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'b list \<Rightarrow> 'c list"
    ("(_ /[\<squnion>\<^sub>_] _)" [65, 0, 66] 65) where
  "x [\<squnion>\<^sub>f] y == x [\<squnion>\<^bsub>f\<^esub>] y"
(*>*)


primrec coalesce :: "'a err list \<Rightarrow> 'a list err"
where
  "coalesce [] = OK[]"
| "coalesce (ex#exs) = Err.sup (#) ex (coalesce exs)"

definition sl :: "nat \<Rightarrow> 'a sl \<Rightarrow> 'a list sl"
where
  "sl n = (\<lambda>(A,r,f). (list n A, le r, map2 f))"

definition sup :: "('a \<Rightarrow> 'b \<Rightarrow> 'c err) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'c list err"
where
  "sup f = (\<lambda>xs ys. if size xs = size ys then coalesce(xs [\<squnion>\<^bsub>f\<^esub>] ys) else Err)"

definition upto_esl :: "nat \<Rightarrow> 'a esl \<Rightarrow> 'a list esl"
where
  "upto_esl m = (\<lambda>(A,r,f). (Union{list n A |n. n \<le> m}, le r, sup f))"


lemmas [simp] = set_update_subsetI

lemma unfold_lesub_list: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys = Listn.le r xs ys"
(*<*) by (simp add: lesub_def) (*>*)

lemma Nil_le_conv [iff]: "([] [\<sqsubseteq>\<^bsub>r\<^esub>] ys) = (ys = [])"
(*<*)
apply (unfold lesub_def Listn.le_def)
apply simp
done
(*>*)

lemma Cons_notle_Nil [iff]: "\<not> x#xs [\<sqsubseteq>\<^bsub>r\<^esub>] []"
(*<*)
apply (unfold lesub_def Listn.le_def)
apply simp
done
(*>*)

lemma Cons_le_Cons [iff]: "x#xs [\<sqsubseteq>\<^bsub>r\<^esub>] y#ys = (x \<sqsubseteq>\<^sub>r y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys)"
(*<*)
by (simp add: lesub_def Listn.le_def)
(*>*)

lemma Cons_less_Conss [simp]:
  "order r \<Longrightarrow>  x#xs [\<sqsubset>\<^sub>r] y#ys = (x \<sqsubset>\<^sub>r y \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<or> x = y \<and> xs [\<sqsubset>\<^sub>r] ys)"
(*<*)
apply (unfold lesssub_def)
apply blast
done
(*>*)

lemma list_update_le_cong:
  "\<lbrakk> i<size xs; xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; x \<sqsubseteq>\<^sub>r y \<rbrakk> \<Longrightarrow> xs[i:=x] [\<sqsubseteq>\<^bsub>r\<^esub>] ys[i:=y]"
(*<*)
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (simp add: list_all2_update_cong)
done
(*>*)


lemma le_listD: "\<lbrakk> xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; p < size xs \<rbrakk> \<Longrightarrow> xs!p \<sqsubseteq>\<^sub>r ys!p"
(*<*)
by (simp add: Listn.le_def lesub_def list_all2_nthD)
(*>*)

lemma le_list_refl: "\<forall>x. x \<sqsubseteq>\<^sub>r x \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs"
(*<*)
apply (simp add: unfold_lesub_list lesub_def Listn.le_def list_all2_refl)
done
(*>*)

lemma le_list_trans: "\<lbrakk> order r; xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<rbrakk> \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
(*<*)
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (rule list_all2_trans)
apply (erule order_trans)
apply assumption+
done
(*>*)

lemma le_list_antisym: "\<lbrakk> order r; xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys; ys [\<sqsubseteq>\<^bsub>r\<^esub>] xs \<rbrakk> \<Longrightarrow> xs = ys"
(*<*)
apply (unfold unfold_lesub_list)
apply (unfold Listn.le_def)
apply (rule list_all2_antisym)
apply (rule order_antisym)
apply assumption+
done
(*>*)

lemma order_listI [simp, intro!]: "order r \<Longrightarrow> order(Listn.le r)"
(*<*)
apply (subst order_def)
apply (blast intro: le_list_refl le_list_trans le_list_antisym
             dest: order_refl)
done
(*>*)

lemma lesub_list_impl_same_size [simp]: "xs [\<sqsubseteq>\<^bsub>r\<^esub>] ys \<Longrightarrow> size ys = size xs"
(*<*)
apply (unfold Listn.le_def lesub_def)
apply (simp add: list_all2_lengthD)
done
(*>*)

lemma lesssub_lengthD: "xs [\<sqsubset>\<^sub>r] ys \<Longrightarrow> size ys = size xs"
(*<*)
apply (unfold lesssub_def)
apply auto
done
(*>*)

lemma le_list_appendI: "a [\<sqsubseteq>\<^bsub>r\<^esub>] b \<Longrightarrow> c [\<sqsubseteq>\<^bsub>r\<^esub>] d \<Longrightarrow> a@c [\<sqsubseteq>\<^bsub>r\<^esub>] b@d"
(*<*)
apply (unfold Listn.le_def lesub_def)
apply (rule list_all2_appendI, assumption+)
done
(*>*)

lemma le_listI:
  assumes "length a = length b"
  assumes "\<And>n. n < length a \<Longrightarrow> a!n \<sqsubseteq>\<^sub>r b!n"
  shows "a [\<sqsubseteq>\<^bsub>r\<^esub>] b"
(*<*)
proof -
  from assms have "list_all2 r a b"
    by (simp add: list_all2_all_nthI lesub_def)
  then show ?thesis by (simp add: Listn.le_def lesub_def)
qed
(*>*)

lemma listI: "\<lbrakk> size xs = n; set xs \<subseteq> A \<rbrakk> \<Longrightarrow> xs \<in> list n A"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)

(* FIXME: remove simp *)
lemma listE_length [simp]: "xs \<in> list n A \<Longrightarrow> size xs = n"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)

lemma less_lengthI: "\<lbrakk> xs \<in> list n A; p < n \<rbrakk> \<Longrightarrow> p < size xs"
(*<*) by simp (*>*)

lemma listE_set [simp]: "xs \<in> list n A \<Longrightarrow> set xs \<subseteq> A"
(*<*)
apply (unfold list_def)
apply blast
done
(*>*)

lemma list_0 [simp]: "list 0 A = {[]}"
(*<*)
apply (unfold list_def)
apply auto
done
(*>*)

lemma in_list_Suc_iff:
  "(xs \<in> list (Suc n) A) = (\<exists>y\<in>A. \<exists>ys \<in> list n A. xs = y#ys)"
(*<*)
apply (unfold list_def)
apply (case_tac "xs")
apply auto
done
(*>*)

lemma Cons_in_list_Suc [iff]:
  "(x#xs \<in> list (Suc n) A) = (x\<in>A \<and> xs \<in> list n A)"
(*<*)
apply (simp add: in_list_Suc_iff)
done
(*>*)

lemma list_not_empty:
  "\<exists>a. a\<in>A \<Longrightarrow> \<exists>xs. xs \<in> list n A"
(*<*)
apply (induct "n")
 apply simp
apply (simp add: in_list_Suc_iff)
apply blast
done
(*>*)


lemma nth_in [rule_format, simp]:
  "\<forall>i n. size xs = n \<longrightarrow> set xs \<subseteq> A \<longrightarrow> i < n \<longrightarrow> (xs!i) \<in> A"
(*<*)
apply (induct "xs")
 apply simp
apply (simp add: nth_Cons split: nat.split)
done
(*>*)

lemma listE_nth_in: "\<lbrakk> xs \<in> list n A; i < n \<rbrakk> \<Longrightarrow> xs!i \<in> A"
(*<*) by auto (*>*)

lemma listn_Cons_Suc [elim!]:
  "l#xs \<in> list n A \<Longrightarrow> (\<And>n'. n = Suc n' \<Longrightarrow> l \<in> A \<Longrightarrow> xs \<in> list n' A \<Longrightarrow> P) \<Longrightarrow> P"
(*<*) by (cases n) auto (*>*)

lemma listn_appendE [elim!]:
  "a@b \<in> list n A \<Longrightarrow> (\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> list n1 A \<Longrightarrow> b \<in> list n2 A \<Longrightarrow> P) \<Longrightarrow> P"
(*<*)
proof -
  have "\<And>n. a@b \<in> list n A \<Longrightarrow> \<exists>n1 n2. n=n1+n2 \<and> a \<in> list n1 A \<and> b \<in> list n2 A"
    (is "\<And>n. ?list a n \<Longrightarrow> \<exists>n1 n2. ?P a n n1 n2")
  proof (induct a)
    fix n assume "?list [] n"
    hence "?P [] n 0 n" by simp
    thus "\<exists>n1 n2. ?P [] n n1 n2" by fast
  next
    fix n l ls
    assume "?list (l#ls) n"
    then obtain n' where n: "n = Suc n'" "l \<in> A" and n': "ls@b \<in> list n' A" by fastforce
    assume "\<And>n. ls @ b \<in> list n A \<Longrightarrow> \<exists>n1 n2. n = n1 + n2 \<and> ls \<in> list n1 A \<and> b \<in> list n2 A"
    from this and n' have "\<exists>n1 n2. n' = n1 + n2 \<and> ls \<in> list n1 A \<and> b \<in> list n2 A" .
    then obtain n1 n2 where "n' = n1 + n2" "ls \<in> list n1 A" "b \<in> list n2 A" by fast
    with n have "?P (l#ls) n (n1+1) n2" by simp
    thus "\<exists>n1 n2. ?P (l#ls) n n1 n2" by fastforce
  qed
  moreover
  assume "a@b \<in> list n A" "\<And>n1 n2. n=n1+n2 \<Longrightarrow> a \<in> list n1 A \<Longrightarrow> b \<in> list n2 A \<Longrightarrow> P"
  ultimately
  show ?thesis by blast
qed
(*>*)


lemma listt_update_in_list [simp, intro!]:
  "\<lbrakk> xs \<in> list n A; x\<in>A \<rbrakk> \<Longrightarrow> xs[i := x] \<in> list n A"
(*<*)
apply (unfold list_def)
apply simp
done
(*>*)

lemma list_appendI [intro?]:
  "\<lbrakk> a \<in> list n A; b \<in> list m A \<rbrakk> \<Longrightarrow> a @ b \<in> list (n+m) A"
(*<*) by (unfold list_def) auto (*>*)

lemma list_map [simp]: "(map f xs \<in> list (size xs) A) = (f ` set xs \<subseteq> A)"
(*<*) by (unfold list_def) simp (*>*)

lemma list_replicateI [intro]: "x \<in> A \<Longrightarrow> replicate n x \<in> list n A"
(*<*) by (induct n) auto (*>*)

lemma plus_list_Nil [simp]: "[] [\<squnion>\<^bsub>f\<^esub>] xs = []"
(*<*)
apply (unfold plussub_def)
apply simp
done
(*>*)

lemma plus_list_Cons [simp]:
  "(x#xs) [\<squnion>\<^bsub>f\<^esub>] ys = (case ys of [] \<Rightarrow> [] | y#ys \<Rightarrow> (x \<squnion>\<^sub>f y)#(xs [\<squnion>\<^bsub>f\<^esub>] ys))"
(*<*) by (simp add: plussub_def split: list.split) (*>*)

lemma length_plus_list [rule_format, simp]:
  "\<forall>ys. size(xs [\<squnion>\<^bsub>f\<^esub>] ys) = min(size xs) (size ys)"
(*<*)
apply (induct xs)
 apply simp
apply clarify
apply (simp (no_asm_simp) split: list.split)
done
(*>*)

lemma nth_plus_list [rule_format, simp]:
  "\<forall>xs ys i. size xs = n \<longrightarrow> size ys = n \<longrightarrow> i<n \<longrightarrow> (xs [\<squnion>\<^bsub>f\<^esub>] ys)!i = (xs!i) \<squnion>\<^sub>f (ys!i)"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (case_tac xs)
 apply simp
apply (force simp add: nth_Cons split: list.split nat.split)
done
(*>*)


lemma (in Semilat) plus_list_ub1 [rule_format]:
 "\<lbrakk> set xs \<subseteq> A; set ys \<subseteq> A; size xs = size ys \<rbrakk>
  \<Longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs [\<squnion>\<^bsub>f\<^esub>] ys"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) plus_list_ub2:
 "\<lbrakk>set xs \<subseteq> A; set ys \<subseteq> A; size xs = size ys \<rbrakk> \<Longrightarrow> ys [\<sqsubseteq>\<^bsub>r\<^esub>] xs [\<squnion>\<^bsub>f\<^esub>] ys"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) plus_list_lub [rule_format]:
shows "\<forall>xs ys zs. set xs \<subseteq> A \<longrightarrow> set ys \<subseteq> A \<longrightarrow> set zs \<subseteq> A
  \<longrightarrow> size xs = n \<and> size ys = n \<longrightarrow>
  xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<longrightarrow> xs [\<squnion>\<^bsub>f\<^esub>] ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
done
(*>*)

lemma (in Semilat) list_update_incr [rule_format]:
 "x\<in>A \<Longrightarrow> set xs \<subseteq> A \<longrightarrow>
  (\<forall>i. i<size xs \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] xs[i := x \<squnion>\<^sub>f xs!i])"
(*<*)
apply (unfold unfold_lesub_list)
apply (simp add: Listn.le_def list_all2_conv_all_nth)
apply (induct xs)
 apply simp
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: nth_Cons split: nat.split)
done
(*>*)

lemma acc_le_listI' [intro!]:
  "\<lbrakk> order r; acc A r \<rbrakk> \<Longrightarrow> acc (\<Union>n. list n A) (Listn.le r)"
(*<*)
apply (unfold acc_def)
apply (subgoal_tac
 "wf(UN n. {(ys,xs). xs \<in> list n A \<and> ys \<in> list n A \<and> xs <_(Listn.le r) ys})")
 apply (erule wf_subset)
 apply clarify
 apply(rule UN_I)
  prefer 2
  apply clarify
  apply(frule lesssub_lengthD)
  apply fastforce
 apply simp
apply (rule wf_UN)
 prefer 2
 apply (rename_tac m n)
 apply (case_tac "m=n")
  apply simp
 apply (clarsimp intro!: equals0I)
 apply (drule lesssub_lengthD)+
 apply simp
apply (induct_tac n)
 apply (simp add: lesssub_def cong: conj_cong)
apply (rename_tac k)
apply (simp add: wf_eq_minimal)
apply (simp (no_asm) add: in_list_Suc_iff cong: conj_cong)
apply clarify
apply (rename_tac M m)
apply (case_tac "\<exists>x\<in>A. \<exists>xs\<in>list k A. x#xs \<in> M")
 prefer 2
 apply (erule thin_rl)
 apply (erule thin_rl)
 apply blast
apply (erule_tac x = "{a. a \<in> A \<and> (\<exists>xs\<in>list k A. a#xs\<in>M)}" in allE)
apply (erule impE)
 apply blast
apply (thin_tac "\<exists>x\<in>A. \<exists>xs\<in>list k A. P x xs" for P)
apply clarify
apply (rename_tac maxA xs)
apply (erule_tac x = "{ys. ys \<in> list k A \<and> maxA#ys \<in> M}" in allE)
apply (erule impE)
 apply blast
apply clarify
apply (thin_tac "m \<in> M")
apply (thin_tac "maxA#xs \<in> M")
apply (rule bexI)
 prefer 2
 apply assumption
apply clarify
apply simp
apply (erule disjE)
 prefer 2
 apply blast
by fastforce

lemma acc_le_listI [intro!]:
  "\<lbrakk> order r; acc A r \<rbrakk> \<Longrightarrow> acc (list n A) (Listn.le r)"
apply(drule (1) acc_le_listI')
apply(erule thin_rl)
apply(unfold acc_def)
apply(erule wf_subset)
apply blast
done

lemma acc_le_list_uptoI [intro!]:
  "\<lbrakk> order r; acc A r \<rbrakk> \<Longrightarrow> acc (\<Union>{list n A|n. n \<le> mxs}) (Listn.le r)"
apply(drule (1) acc_le_listI')
apply(erule thin_rl)
apply(unfold acc_def)
apply(erule wf_subset)
apply blast
done

lemma closed_listI:
  "closed S f \<Longrightarrow> closed (list n S) (map2 f)"
(*<*)
apply (unfold closed_def)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply simp
done
(*>*)


lemma Listn_sl_aux:
assumes "Semilat A r f" shows "semilat (Listn.sl n (A,r,f))"
(*<*)
proof -
  interpret Semilat A r f by fact
  show ?thesis
  apply (unfold Listn.sl_def)
  apply (simp (no_asm) only: semilat_Def split_conv)
  apply (rule conjI)
   apply simp
  apply (rule conjI)
   apply (simp only: closedI closed_listI)
  apply (simp (no_asm) only: list_def)
  apply (simp (no_asm_simp) add: plus_list_ub1 plus_list_ub2 plus_list_lub)
  done
qed
(*>*)

lemma Listn_sl: "semilat L \<Longrightarrow> semilat (Listn.sl n L)"
(*<*) apply (cases L) apply simp
apply (drule Semilat.intro)
by (simp add: Listn_sl_aux split_tupled_all) (*>*)

lemma coalesce_in_err_list [rule_format]:
  "\<forall>xes. xes \<in> list n (err A) \<longrightarrow> coalesce xes \<in> err(list n A)"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm) add: plussub_def Err.sup_def lift2_def split: err.split)
apply force
done
(*>*)

lemma lem: "\<And>x xs. x \<squnion>\<^bsub>(#)\<^esub> xs = x#xs"
(*<*) by (simp add: plussub_def) (*>*)

lemma coalesce_eq_OK1_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow>
  (\<forall>zs. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<longrightarrow> xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
  apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK1)
done
(*>*)

lemma coalesce_eq_OK2_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow>
  (\<forall>zs. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<longrightarrow> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
apply (force simp add: semilat_le_err_OK2)
done
(*>*)

lemma lift2_le_ub:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f); x\<in>A; y\<in>A; x \<squnion>\<^sub>f y = OK z;
      u\<in>A; x \<sqsubseteq>\<^sub>r u; y \<sqsubseteq>\<^sub>r u \<rbrakk> \<Longrightarrow> z \<sqsubseteq>\<^sub>r u"
(*<*)
apply (unfold semilat_Def plussub_def err_def')
apply (simp add: lift2_def)
apply clarify
apply (rotate_tac -3)
apply (erule thin_rl)
apply (erule thin_rl)
apply force
done
(*>*)

lemma coalesce_eq_OK_ub_D [rule_format]:
  "semilat(err A, Err.le r, lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow>
  (\<forall>zs us. coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = OK zs \<and> xs [\<sqsubseteq>\<^bsub>r\<^esub>] us \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] us
           \<and> us \<in> list n A \<longrightarrow> zs [\<sqsubseteq>\<^bsub>r\<^esub>] us))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp (no_asm_use) split: err.split_asm add: lem Err.sup_def lift2_def)
apply clarify
apply (rule conjI)
 apply (blast intro: lift2_le_ub)
apply blast
done
(*>*)

lemma lift2_eq_ErrD:
  "\<lbrakk> x \<squnion>\<^sub>f y = Err; semilat(err A, Err.le r, lift2 f); x\<in>A; y\<in>A \<rbrakk>
  \<Longrightarrow> \<not>(\<exists>u\<in>A. x \<sqsubseteq>\<^sub>r u \<and> y \<sqsubseteq>\<^sub>r u)"
(*<*) by (simp add: OK_plus_OK_eq_Err_conv [THEN iffD1]) (*>*)


lemma coalesce_eq_Err_D [rule_format]:
  "\<lbrakk> semilat(err A, Err.le r, lift2 f) \<rbrakk>
  \<Longrightarrow> \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow>
      coalesce (xs [\<squnion>\<^bsub>f\<^esub>] ys) = Err \<longrightarrow>
      \<not>(\<exists>zs \<in> list n A. xs [\<sqsubseteq>\<^bsub>r\<^esub>] zs \<and> ys [\<sqsubseteq>\<^bsub>r\<^esub>] zs))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp split: err.split_asm add: lem Err.sup_def lift2_def)
 apply (blast dest: lift2_eq_ErrD)
done
(*>*)

lemma closed_err_lift2_conv:
  "closed (err A) (lift2 f) = (\<forall>x\<in>A. \<forall>y\<in>A. x \<squnion>\<^sub>f y \<in> err A)"
(*<*)
apply (unfold closed_def)
apply (simp add: err_def')
done
(*>*)

lemma closed_map2_list [rule_format]:
  "closed (err A) (lift2 f) \<Longrightarrow>
  \<forall>xs. xs \<in> list n A \<longrightarrow> (\<forall>ys. ys \<in> list n A \<longrightarrow>
  map2 f xs ys \<in> list n (err A))"
(*<*)
apply (induct n)
 apply simp
apply clarify
apply (simp add: in_list_Suc_iff)
apply clarify
apply (simp add: plussub_def closed_err_lift2_conv)
done
(*>*)

lemma closed_lift2_sup:
  "closed (err A) (lift2 f) \<Longrightarrow>
  closed (err (list n A)) (lift2 (sup f))"
(*<*) by (fastforce  simp add: closed_def plussub_def sup_def lift2_def
                          coalesce_in_err_list closed_map2_list
                split: err.split) (*>*)

lemma err_semilat_sup:
  "err_semilat (A,r,f) \<Longrightarrow>
  err_semilat (list n A, Listn.le r, sup f)"
(*<*)
apply (unfold Err.sl_def)
apply (simp only: split_conv)
apply (simp (no_asm) only: semilat_Def plussub_def)
apply (simp (no_asm_simp) only: Semilat.closedI [OF Semilat.intro] closed_lift2_sup)
apply (rule conjI)
 apply (drule Semilat.orderI [OF Semilat.intro])
 apply simp
apply (simp (no_asm) only: unfold_lesub_err Err.le_def err_def' sup_def lift2_def)
apply (simp (no_asm_simp) add: coalesce_eq_OK1_D coalesce_eq_OK2_D split: err.split)
apply (blast intro: coalesce_eq_OK_ub_D dest: coalesce_eq_Err_D)
done
(*>*)

lemma err_semilat_upto_esl:
  "\<And>L. err_semilat L \<Longrightarrow> err_semilat(upto_esl m L)"
(*<*)
apply (unfold Listn.upto_esl_def)
apply (simp (no_asm_simp) only: split_tupled_all)
apply simp
apply (fastforce intro!: err_semilat_UnionI err_semilat_sup
                dest: lesub_list_impl_same_size
                simp add: plussub_def Listn.sup_def)
done
(*>*)

end
