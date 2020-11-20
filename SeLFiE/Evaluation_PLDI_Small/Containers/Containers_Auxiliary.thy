(*  Title:      Containers/Containers_Auxiliary.thy
    Author:     Andreas Lochbihler, KIT *)

theory Containers_Auxiliary imports
  "HOL-Library.Monad_Syntax"
begin

chapter \<open>An executable linear order on sets\<close>
text_raw \<open>\label{chapter:linear:order:set}\<close>

section \<open>Auxiliary definitions\<close>

lemma insert_bind_set: "insert a A \<bind> f = f a \<union> (A \<bind> f)"
by(auto simp add: Set.bind_def)

lemma set_bind_iff:
  "set (List.bind xs f) = Set.bind (set xs) (set \<circ> f)"
by(induct xs)(simp_all add: insert_bind_set)

lemma set_bind_conv_fold: "set xs \<bind> f = fold ((\<union>) \<circ> f) xs {}"
by(induct xs rule: rev_induct)(simp_all add: insert_bind_set)

lemma card_gt_1D:
  assumes "card A > 1"
  shows "\<exists>x y. x \<in> A \<and> y \<in> A \<and> x \<noteq> y"
proof(rule ccontr)
  from assms have "A \<noteq> {}" by auto
  then obtain x where "x \<in> A" by auto
  moreover
  assume "\<not> ?thesis"
  ultimately have "A = {x}" by auto
  with assms show False by simp
qed

lemma card_eq_1_iff: "card A = 1 \<longleftrightarrow> (\<exists>x. A = {x})"
proof
  assume card: "card A = 1"
  hence [simp]: "finite A" using card_gt_0_iff[of A] by simp
  have "A = {THE x. x \<in> A}"
  proof(intro equalityI subsetI)
    fix x
    assume x: "x \<in> A"
    hence "(THE x. x \<in> A) = x"
    proof(rule the_equality)
      fix x'
      assume x': "x' \<in> A"
      show "x' = x"
      proof(rule ccontr)
        assume neq: "x' \<noteq> x"
        from x x' have eq: "A = insert x (insert x' (A - {x, x'}))" by auto
        have "card A = 2 + card (A - {x, x'})" using neq by(subst eq)(simp)
        with card show False by simp
      qed
    qed
    thus "x \<in> {THE x. x \<in> A}" by simp
  next
    fix x
    assume "x \<in> {THE x. x \<in> A}"
    hence x: "x = (THE x. x \<in> A)" by simp
    from card have "A \<noteq> {}" by auto
    then obtain x' where x': "x' \<in> A" by blast
    thus "x \<in> A" unfolding x
    proof(rule theI)
      fix x
      assume x: "x \<in> A"
      show "x = x'"
      proof(rule ccontr)
        assume neq: "x \<noteq> x'"
        from x x' have eq: "A = insert x (insert x' (A - {x, x'}))" by auto
        have "card A = 2 + card (A - {x, x'})" using neq by(subst eq)(simp)
        with card show False by simp
      qed
    qed
  qed
  thus "\<exists>x. A = {x}" ..
qed auto

lemma card_eq_Suc_0_ex1: "card A = Suc 0 \<longleftrightarrow> (\<exists>!x. x \<in> A)"
by(auto simp only: One_nat_def[symmetric] card_eq_1_iff)

context linorder begin

lemma sorted_last: "\<lbrakk> sorted xs; x \<in> set xs \<rbrakk> \<Longrightarrow> x \<le> last xs"
by(cases xs rule: rev_cases)(auto simp add: sorted_append)

end

lemma empty_filter_conv: "[] = filter P xs \<longleftrightarrow> (\<forall>x\<in>set xs. \<not> P x)"
by(auto dest: sym simp add: filter_empty_conv)


definition ID :: "'a \<Rightarrow> 'a" where "ID = id"

lemma ID_code [code, code_unfold]: "ID = (\<lambda>x. x)"
by(simp add: ID_def id_def)

lemma ID_Some: "ID (Some x) = Some x"
by(simp add: ID_def)

lemma ID_None: "ID None = None" 
by(simp add: ID_def)

text \<open>lexicographic order on pairs\<close>

context
  fixes leq_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>a" 50) 
  and less_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>a" 50) 
  and leq_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>b" 50) 
  and less_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>b" 50) 
begin

definition less_eq_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where "less_eq_prod = (\<lambda>(x1, x2) (y1, y2). x1 \<sqsubset>\<^sub>a y1 \<or> x1 \<sqsubseteq>\<^sub>a y1 \<and> x2 \<sqsubseteq>\<^sub>b y2)"

definition less_prod :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where "less_prod = (\<lambda>(x1, x2) (y1, y2). x1 \<sqsubset>\<^sub>a y1 \<or> x1 \<sqsubseteq>\<^sub>a y1 \<and> x2 \<sqsubset>\<^sub>b y2)"

lemma less_eq_prod_simps [simp]:
  "(x1, x2) \<sqsubseteq> (y1, y2) \<longleftrightarrow> x1 \<sqsubset>\<^sub>a y1 \<or> x1 \<sqsubseteq>\<^sub>a y1 \<and> x2 \<sqsubseteq>\<^sub>b y2"
by(simp add: less_eq_prod_def)

lemma less_prod_simps [simp]:
  "(x1, x2) \<sqsubset> (y1, y2) \<longleftrightarrow> x1 \<sqsubset>\<^sub>a y1 \<or> x1 \<sqsubseteq>\<^sub>a y1 \<and> x2 \<sqsubset>\<^sub>b y2"
by(simp add: less_prod_def)

end

context
  fixes leq_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>a" 50) 
  and less_a :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>a" 50) 
  and leq_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubseteq>\<^sub>b" 50) 
  and less_b :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<sqsubset>\<^sub>b" 50) 
  assumes lin_a: "class.linorder leq_a less_a" 
  and lin_b: "class.linorder leq_b less_b"
begin

abbreviation (input) less_eq_prod' :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where "less_eq_prod' \<equiv> less_eq_prod leq_a less_a leq_b"

abbreviation (input) less_prod' :: "('a \<times> 'b) \<Rightarrow> ('a \<times> 'b) \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where "less_prod' \<equiv> less_prod leq_a less_a less_b"

lemma linorder_prod:
  "class.linorder (\<sqsubseteq>) (\<sqsubset>)"
proof -
  interpret a: linorder "(\<sqsubseteq>\<^sub>a)" "(\<sqsubset>\<^sub>a)" by(fact lin_a)
  interpret b: linorder "(\<sqsubseteq>\<^sub>b)" "(\<sqsubset>\<^sub>b)" by(fact lin_b)
  show ?thesis by unfold_locales auto
qed

end

hide_const less_eq_prod' less_prod'

end
