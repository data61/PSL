(*
  File:     Indep_System.thy
  Author:   Jonas Keinholz

Independence systems
*)
section \<open>Independence systems\<close>
theory Indep_System
  imports Main
begin

lemma finite_psubset_inc_induct:
  assumes "finite A" "X \<subseteq> A"
  assumes "\<And>X. (\<And>Y. X \<subset> Y \<Longrightarrow> Y \<subseteq> A \<Longrightarrow> P Y) \<Longrightarrow> P X"
  shows "P X"
proof -
  have wf: "wf {(X,Y). Y \<subset> X \<and> X \<subseteq> A}"
    by (rule wf_bounded_set[where ub = "\<lambda>_. A" and f = id]) (auto simp add: \<open>finite A\<close>)
  show ?thesis
  proof (induction X rule: wf_induct[OF wf, case_names step])
    case (step X)
    then show ?case using assms(3)[of X] by blast
  qed
qed

text \<open>
  An \emph{independence system} consists of a finite ground set together with an independence
  predicate over the sets of this ground set. At least one set of the carrier is independent and
  subsets of independent sets are also independent.
\<close>

locale indep_system =
  fixes carrier :: "'a set"
  fixes indep :: "'a set \<Rightarrow> bool"
  assumes carrier_finite: "finite carrier"
  assumes indep_subset_carrier: "indep X \<Longrightarrow> X \<subseteq> carrier"
  assumes indep_ex: "\<exists>X. indep X"
  assumes indep_subset: "indep X \<Longrightarrow> Y \<subseteq> X \<Longrightarrow> indep Y"
begin

lemmas psubset_inc_induct [case_names carrier step] = finite_psubset_inc_induct[OF carrier_finite]
lemmas indep_finite [simp] = finite_subset[OF indep_subset_carrier carrier_finite]

text \<open>
  The empty set is independent.
\<close>

lemma indep_empty [simp]: "indep {}"
  using indep_ex indep_subset by auto

subsection \<open>Sub-independence systems\<close>

text \<open>
  A subset of the ground set induces an independence system.
\<close>

definition indep_in where "indep_in \<E> X \<longleftrightarrow> X \<subseteq> \<E> \<and> indep X"

lemma indep_inI:
  assumes "X \<subseteq> \<E>"
  assumes "indep X"
  shows "indep_in \<E> X"
  using assms unfolding indep_in_def by auto

lemma indep_in_subI: "indep_in \<E> X \<Longrightarrow> indep_in \<E>' (X \<inter> \<E>')"
  using indep_subset unfolding indep_in_def by auto

lemma dep_in_subI:
  assumes "X \<subseteq> \<E>'"
  shows "\<not> indep_in \<E>' X \<Longrightarrow> \<not> indep_in \<E> X"
  using assms unfolding indep_in_def by auto

lemma indep_in_subset_carrier: "indep_in \<E> X \<Longrightarrow> X \<subseteq> \<E>"
  unfolding indep_in_def by auto

lemma indep_in_subI_subset:
  assumes "\<E>' \<subseteq> \<E>"
  assumes "indep_in \<E>' X"
  shows "indep_in \<E> X"
proof -
  have "indep_in \<E> (X \<inter> \<E>)" using assms indep_in_subI by auto
  moreover have "X \<inter> \<E> = X" using assms indep_in_subset_carrier by auto
  ultimately show ?thesis by auto
qed

lemma indep_in_supI:
  assumes "X \<subseteq> \<E>'" "\<E>' \<subseteq> \<E>"
  assumes "indep_in \<E> X"
  shows "indep_in \<E>' X"
proof -
  have "X \<inter> \<E>' = X" using assms by auto
  then show ?thesis using assms indep_in_subI[where \<E> = \<E> and \<E>' = \<E>' and X = X] by auto
qed

lemma indep_in_indep: "indep_in \<E> X \<Longrightarrow> indep X"
  unfolding indep_in_def by auto

lemmas indep_inD = indep_in_subset_carrier indep_in_indep

lemma indep_system_subset [simp, intro]:
  assumes "\<E> \<subseteq> carrier"
  shows "indep_system \<E> (indep_in \<E>)"
  unfolding indep_system_def indep_in_def
  using finite_subset[OF assms carrier_finite] indep_subset by auto

text \<open>
  We will work a lot with different sub structures. Therefore, every definition `foo' will have
  a counterpart `foo\_in' which has the ground set as an additional parameter. Furthermore, every
  result about `foo' will have another result about `foo\_in'. With this, we usually don't have to
  work with @{command interpretation} in proofs.
\<close>

context
  fixes \<E>
  assumes "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma indep_in_sub_cong:
  assumes "\<E>' \<subseteq> \<E>"
  shows "\<E>.indep_in \<E>' X \<longleftrightarrow> indep_in \<E>' X"
  unfolding \<E>.indep_in_def indep_in_def using assms by auto

lemmas indep_in_ex = \<E>.indep_ex
lemmas indep_in_subset = \<E>.indep_subset
lemmas indep_in_empty = \<E>.indep_empty

end

subsection \<open>Bases\<close>

text \<open>
  A \emph{basis} is a maximal independent set, i.\,e.\ an independent set which becomes dependent on
  inserting any element of the ground set.
\<close>

definition basis where "basis X \<longleftrightarrow> indep X \<and> (\<forall>x \<in> carrier - X. \<not> indep (insert x X))"

lemma basisI:
  assumes "indep X"
  assumes "\<And>x. x \<in> carrier - X \<Longrightarrow> \<not> indep (insert x X)"
  shows "basis X"
  using assms unfolding basis_def by auto

lemma basis_indep: "basis X \<Longrightarrow> indep X"
  unfolding basis_def by auto

lemma basis_max_indep: "basis X \<Longrightarrow> x \<in> carrier - X \<Longrightarrow> \<not> indep (insert x X)"
  unfolding basis_def by auto

lemmas basisD = basis_indep basis_max_indep
lemmas basis_subset_carrier = indep_subset_carrier[OF basis_indep]
lemmas basis_finite [simp] = indep_finite[OF basis_indep]

lemma indep_not_basis:
  assumes "indep X"
  assumes "\<not> basis X"
  shows "\<exists>x \<in> carrier - X. indep (insert x X)"
  using assms basisI by auto

lemma basis_subset_eq:
  assumes "basis B\<^sub>1"
  assumes "basis B\<^sub>2"
  assumes "B\<^sub>1 \<subseteq> B\<^sub>2"
  shows "B\<^sub>1 = B\<^sub>2"
proof (rule ccontr)
  assume "B\<^sub>1 \<noteq> B\<^sub>2"
  then obtain x where x: "x \<in> B\<^sub>2 - B\<^sub>1" using assms by auto
  then have "insert x B\<^sub>1 \<subseteq> B\<^sub>2" using assms by auto
  then have "indep (insert x B\<^sub>1)" using assms basis_indep[of B\<^sub>2] indep_subset by auto
  moreover have "x \<in> carrier - B\<^sub>1" using assms x basis_subset_carrier by auto
  ultimately show False using assms basisD by auto
qed

definition basis_in where
  "basis_in \<E> X \<longleftrightarrow> indep_system.basis \<E> (indep_in \<E>) X"

lemma basis_iff_basis_in: "basis B \<longleftrightarrow> basis_in carrier B"
proof -
  interpret \<E>: indep_system carrier "indep_in carrier"
    by auto

  show "basis B \<longleftrightarrow> basis_in carrier B"
    unfolding basis_in_def
  proof (standard, goal_cases LTR RTL)
    case LTR
    show ?case
    proof (rule \<E>.basisI)
      show "indep_in carrier B" using LTR basisD indep_subset_carrier indep_inI by auto
    next
      fix x
      assume "x \<in> carrier - B"
      then have "\<not> indep (insert x B)" using LTR basisD by auto
      then show "\<not> indep_in carrier (insert x B)" using indep_inD by auto
    qed
  next
    case RTL
    show ?case
    proof (rule basisI)
      show "indep B" using RTL \<E>.basis_indep indep_inD by blast
    next
      fix x
      assume "x \<in> carrier - B"
      then have "\<not> indep_in carrier (insert x B)" using RTL \<E>.basisD by auto
      then show "\<not> indep (insert x B)" using indep_subset_carrier indep_inI by blast
    qed
  qed
qed

context
  fixes \<E>
  assumes "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma basis_inI_aux: "\<E>.basis X \<Longrightarrow> basis_in \<E> X"
  unfolding basis_in_def by auto

lemma basis_inD_aux: "basis_in \<E> X \<Longrightarrow> \<E>.basis X"
  unfolding basis_in_def by auto

lemma not_basis_inD_aux: "\<not> basis_in \<E> X \<Longrightarrow> \<not> \<E>.basis X"
  using basis_inI_aux by auto

lemmas basis_inI = basis_inI_aux[OF \<E>.basisI]
lemmas basis_in_indep_in = \<E>.basis_indep[OF basis_inD_aux]
lemmas basis_in_max_indep_in = \<E>.basis_max_indep[OF basis_inD_aux]
lemmas basis_inD = \<E>.basisD[OF basis_inD_aux]
lemmas basis_in_subset_carrier = \<E>.basis_subset_carrier[OF basis_inD_aux]
lemmas basis_in_finite = \<E>.basis_finite[OF basis_inD_aux]
lemmas indep_in_not_basis_in = \<E>.indep_not_basis[OF _ not_basis_inD_aux]
lemmas basis_in_subset_eq = \<E>.basis_subset_eq[OF basis_inD_aux basis_inD_aux]

end

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using * by auto

lemma basis_in_sub_cong:
  assumes "\<E>' \<subseteq> \<E>"
  shows "\<E>.basis_in \<E>' B \<longleftrightarrow> basis_in \<E>' B"
proof (safe, goal_cases LTR RTL)
  case LTR
  show ?case
  proof (rule basis_inI)
    show "\<E>' \<subseteq> carrier" using assms * by auto
  next
    show "indep_in \<E>' B"
      using * assms LTR \<E>.basis_in_subset_carrier \<E>.basis_in_indep_in indep_in_sub_cong by auto
  next
    fix x
    assume "x \<in> \<E>' - B"
    then show "\<not> indep_in \<E>' (insert x B)"
      using * assms LTR \<E>.basis_in_max_indep_in \<E>.basis_in_subset_carrier indep_in_sub_cong by auto
  qed
next
  case RTL
  show ?case
  proof (rule \<E>.basis_inI)
    show "\<E>' \<subseteq> \<E>" using assms by auto
  next
    show "\<E>.indep_in \<E>' B"
      using * assms RTL basis_in_subset_carrier basis_in_indep_in indep_in_sub_cong by auto
  next
    fix x
    assume "x \<in> \<E>' - B"
    then show "\<not> \<E>.indep_in \<E>' (insert x B)"
      using * assms RTL basis_in_max_indep_in basis_in_subset_carrier indep_in_sub_cong by auto
  qed
qed

end

subsection \<open>Circuits\<close>

text \<open>
  A \emph{circuit} is a minimal dependent set, i.\,e.\ a set which becomes independent on removing
  any element of the ground set.
\<close>

definition circuit where "circuit X \<longleftrightarrow> X \<subseteq> carrier \<and> \<not> indep X \<and> (\<forall>x \<in> X. indep (X - {x}))"

lemma circuitI:
  assumes "X \<subseteq> carrier"
  assumes "\<not> indep X"
  assumes "\<And>x. x \<in> X \<Longrightarrow> indep (X - {x})"
  shows "circuit X"
  using assms unfolding circuit_def by auto

lemma circuit_subset_carrier: "circuit X \<Longrightarrow> X \<subseteq> carrier"
  unfolding circuit_def by auto
lemmas circuit_finite [simp] = finite_subset[OF circuit_subset_carrier carrier_finite]

lemma circuit_dep: "circuit X \<Longrightarrow> \<not> indep X"
  unfolding circuit_def by auto

lemma circuit_min_dep: "circuit X \<Longrightarrow> x \<in> X \<Longrightarrow> indep (X - {x})"
  unfolding circuit_def by auto

lemmas circuitD = circuit_subset_carrier circuit_dep circuit_min_dep

lemma circuit_nonempty: "circuit X \<Longrightarrow> X \<noteq> {}"
  using circuit_dep indep_empty by blast

lemma dep_not_circuit:
  assumes "X \<subseteq> carrier"
  assumes "\<not> indep X"
  assumes "\<not> circuit X"
  shows "\<exists>x \<in> X. \<not> indep (X - {x})"
  using assms circuitI by auto

lemma circuit_subset_eq:
  assumes "circuit C\<^sub>1"
  assumes "circuit C\<^sub>2"
  assumes "C\<^sub>1 \<subseteq> C\<^sub>2"
  shows "C\<^sub>1 = C\<^sub>2"
proof (rule ccontr)
  assume "C\<^sub>1 \<noteq> C\<^sub>2"
  then obtain x where "x \<notin> C\<^sub>1" "x \<in> C\<^sub>2" using assms by auto
  then have "indep C\<^sub>1" using indep_subset \<open>C\<^sub>1 \<subseteq> C\<^sub>2\<close> circuit_min_dep[OF \<open>circuit C\<^sub>2\<close>, of x] by auto
  then show False using assms circuitD by auto
qed

definition circuit_in where
  "circuit_in \<E> X \<longleftrightarrow> indep_system.circuit \<E> (indep_in \<E>) X"

context
  fixes \<E>
  assumes "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma circuit_inI_aux: "\<E>.circuit X \<Longrightarrow> circuit_in \<E> X"
  unfolding circuit_in_def by auto

lemma circuit_inD_aux: "circuit_in \<E> X \<Longrightarrow> \<E>.circuit X"
  unfolding circuit_in_def by auto

lemma not_circuit_inD_aux: "\<not> circuit_in \<E> X \<Longrightarrow> \<not> \<E>.circuit X"
  using circuit_inI_aux by auto

lemmas circuit_inI = circuit_inI_aux[OF \<E>.circuitI]

lemmas circuit_in_subset_carrier = \<E>.circuit_subset_carrier[OF circuit_inD_aux]
lemmas circuit_in_finite = \<E>.circuit_finite[OF circuit_inD_aux]
lemmas circuit_in_dep_in = \<E>.circuit_dep[OF circuit_inD_aux]
lemmas circuit_in_min_dep_in = \<E>.circuit_min_dep[OF circuit_inD_aux]
lemmas circuit_inD = \<E>.circuitD[OF circuit_inD_aux]
lemmas circuit_in_nonempty = \<E>.circuit_nonempty[OF circuit_inD_aux]
lemmas dep_in_not_circuit_in = \<E>.dep_not_circuit[OF _ _ not_circuit_inD_aux]
lemmas circuit_in_subset_eq = \<E>.circuit_subset_eq[OF circuit_inD_aux circuit_inD_aux]

end

lemma circuit_in_subI:
  assumes "\<E>' \<subseteq> \<E>" "\<E> \<subseteq> carrier"
  assumes "circuit_in \<E>' C"
  shows "circuit_in \<E> C"
proof (rule circuit_inI)
  show "\<E> \<subseteq> carrier" using assms by auto
next
  show "C \<subseteq> \<E>" using assms circuit_in_subset_carrier[of \<E>' C] by auto
next
  show "\<not> indep_in \<E> C"
    using assms
      circuit_in_dep_in[where \<E> = \<E>' and X = C]
      circuit_in_subset_carrier dep_in_subI[where \<E>' = \<E>' and \<E> = \<E>]
    by auto
next
  fix x
  assume "x \<in> C"
  then show "indep_in \<E> (C - {x})"
    using assms circuit_in_min_dep_in indep_in_subI_subset by auto
qed

lemma circuit_in_supI:
  assumes "\<E>' \<subseteq> \<E>" "\<E> \<subseteq> carrier" "C \<subseteq> \<E>'"
  assumes "circuit_in \<E> C"
  shows "circuit_in \<E>' C"
proof (rule circuit_inI)
  show "\<E>' \<subseteq> carrier" using assms by auto
next
  show "C \<subseteq> \<E>'" using assms by auto
next
  have "\<not> indep_in \<E> C" using assms circuit_in_dep_in by auto
  then show "\<not> indep_in \<E>' C" using assms dep_in_subI[of C \<E>] by auto
next
  fix x
  assume "x \<in> C"
  then have "indep_in \<E> (C - {x})" using assms circuit_in_min_dep_in by auto
  then have "indep_in \<E>' ((C - {x}) \<inter> \<E>')" using indep_in_subI by auto
  moreover have "(C - {x}) \<inter> \<E>' = C - {x}" using assms circuit_in_subset_carrier by auto
  ultimately show "indep_in \<E>' (C - {x})" by auto
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using * by auto

lemma circuit_in_sub_cong:
  assumes "\<E>' \<subseteq> \<E>"
  shows "\<E>.circuit_in \<E>' C \<longleftrightarrow> circuit_in \<E>' C"
proof (safe, goal_cases LTR RTL)
  case LTR
  show ?case
  proof (rule circuit_inI)
    show "\<E>' \<subseteq> carrier" using assms * by auto
  next
    show "C \<subseteq> \<E>'"
      using assms LTR \<E>.circuit_in_subset_carrier by auto
  next
    show "\<not> indep_in \<E>' C"
      using assms LTR \<E>.circuit_in_dep_in indep_in_sub_cong[OF *] by auto
  next
    fix x
    assume "x \<in> C"
    then show "indep_in \<E>' (C - {x})"
      using assms LTR \<E>.circuit_in_min_dep_in indep_in_sub_cong[OF *] by auto
  qed
next
  case RTL
  show ?case
  proof (rule \<E>.circuit_inI)
    show "\<E>' \<subseteq> \<E>" using assms * by auto
  next
    show "C \<subseteq> \<E>'"
      using assms * RTL circuit_in_subset_carrier by auto
  next
    show "\<not> \<E>.indep_in \<E>' C"
      using assms * RTL circuit_in_dep_in indep_in_sub_cong[OF *] by auto
  next
    fix x
    assume "x \<in> C"
    then show "\<E>.indep_in \<E>' (C - {x})"
      using assms * RTL circuit_in_min_dep_in indep_in_sub_cong[OF *] by auto
  qed
qed

end

lemma circuit_imp_circuit_in:
  assumes "circuit C"
  shows "circuit_in carrier C"
proof (rule circuit_inI)
  show "C \<subseteq> carrier" using circuit_subset_carrier[OF assms] .
next
  show "\<not> indep_in carrier C" using circuit_dep[OF assms] indep_in_indep by auto
next
  fix x
  assume "x \<in> C"
  then have "indep (C - {x})" using circuit_min_dep[OF assms] by auto
  then show "indep_in carrier (C - {x})" using circuit_subset_carrier[OF assms] by (auto intro: indep_inI)
qed auto

subsection \<open>Relation between independence and bases\<close>

text \<open>
  A set is independent iff it is a subset of a basis.
\<close>

lemma indep_imp_subset_basis:
  assumes "indep X"
  shows "\<exists>B. basis B \<and> X \<subseteq> B"
  using assms
proof (induction X rule: psubset_inc_induct)
  case carrier
  show ?case using indep_subset_carrier[OF assms] .
next
  case (step X)
  {
    assume "\<not> basis X"
    then obtain x where "x \<in> carrier" "x \<notin> X" "indep (insert x X)"
      using step.prems indep_not_basis by auto
    then have ?case using step.IH[of "insert x X"] indep_subset_carrier by auto
  }
  then show ?case by auto
qed

lemmas subset_basis_imp_indep = indep_subset[OF basis_indep]

lemma indep_iff_subset_basis: "indep X \<longleftrightarrow> (\<exists>B. basis B \<and> X \<subseteq> B)"
  using indep_imp_subset_basis subset_basis_imp_indep by auto

lemma basis_ex: "\<exists>B. basis B"
  using indep_imp_subset_basis[OF indep_empty] by auto

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using * by auto

lemma indep_in_imp_subset_basis_in:
  assumes "indep_in \<E> X"
  shows "\<exists>B. basis_in \<E> B \<and> X \<subseteq> B"
  unfolding basis_in_def using \<E>.indep_imp_subset_basis[OF assms] .

lemmas subset_basis_in_imp_indep_in = indep_in_subset[OF * basis_in_indep_in[OF *]]

lemma indep_in_iff_subset_basis_in: "indep_in \<E> X \<longleftrightarrow> (\<exists>B. basis_in \<E> B \<and> X \<subseteq> B)"
  using indep_in_imp_subset_basis_in subset_basis_in_imp_indep_in by auto

lemma basis_in_ex: "\<exists>B. basis_in \<E> B"
  unfolding basis_in_def using \<E>.basis_ex .

lemma basis_in_subI:
  assumes "\<E>' \<subseteq> \<E>" "\<E> \<subseteq> carrier"
  assumes "basis_in \<E>' B"
  shows "\<exists>B' \<subseteq> \<E> - \<E>'. basis_in \<E> (B \<union> B')"
proof -
  have "indep_in \<E> B" using assms basis_in_indep_in indep_in_subI_subset by auto
  then obtain B' where B': "basis_in \<E> B'" "B \<subseteq> B'"
    using assms indep_in_imp_subset_basis_in[of B] by auto
  show ?thesis
  proof (rule exI)
    have "B' - B \<subseteq> \<E> - \<E>'"
    proof
      fix x
      assume *: "x \<in> B' - B"
      then have "x \<in> \<E>" "x \<notin> B"
        using assms \<open>basis_in \<E> B'\<close> basis_in_subset_carrier[of \<E>] by auto
      moreover {
        assume "x \<in> \<E>'"
        moreover have "indep_in \<E> (insert x B)"
          using * assms indep_in_subset[OF _ basis_in_indep_in] B' by auto
        ultimately have "indep_in \<E>' (insert x B)"
          using assms basis_in_subset_carrier unfolding indep_in_def by auto
        then have False using assms * \<open>x \<in> \<E>'\<close> basis_in_max_indep_in by auto
      }
      ultimately show "x \<in> \<E> - \<E>'"  by auto
    qed
    moreover have "B \<union> (B' - B) = B'" using \<open>B \<subseteq> B'\<close> by auto
    ultimately show "B' - B \<subseteq> \<E> - \<E>' \<and> basis_in \<E> (B \<union> (B' - B))"
      using \<open>basis_in \<E> B'\<close> by auto
  qed
qed

lemma basis_in_supI:
  assumes "B \<subseteq> \<E>'" "\<E>' \<subseteq> \<E>" "\<E> \<subseteq> carrier"
  assumes "basis_in \<E> B"
  shows "basis_in \<E>' B"
proof (rule basis_inI)
  show "\<E>' \<subseteq> carrier" using assms by auto
next
  show "indep_in \<E>' B"
  proof -
    have "indep_in \<E>' (B \<inter> \<E>')"
      using assms basis_in_indep_in[of \<E> B] indep_in_subI by auto
    moreover have "B \<inter> \<E>' = B" using assms by auto
    ultimately show ?thesis by auto
  qed
next
  show "\<And>x. x \<in> \<E>' - B \<Longrightarrow> \<not> indep_in \<E>' (insert x B)"
    using assms basis_in_subset_carrier basis_in_max_indep_in dep_in_subI[of _ \<E> \<E>'] by auto
qed

end

subsection \<open>Relation between dependence and circuits\<close>

text \<open>
  A set is dependent iff it contains a circuit.
\<close>

lemma dep_imp_supset_circuit:
  assumes "X \<subseteq> carrier"
  assumes "\<not> indep X"
  shows "\<exists>C. circuit C \<and> C \<subseteq> X"
  using assms
proof (induction X rule: remove_induct)
  case (remove X)
  {
    assume "\<not> circuit X"
    then obtain x where "x \<in> X" "\<not> indep (X - {x})"
      using remove.prems dep_not_circuit by auto
    then obtain C where "circuit C" "C \<subseteq> X - {x}"
      using remove.prems remove.IH[of x] by auto
    then have ?case by auto
  }
  then show ?case using remove.prems by auto
qed (auto simp add: carrier_finite finite_subset)

lemma supset_circuit_imp_dep:
  assumes "circuit C \<and> C \<subseteq> X"
  shows "\<not> indep X"
  using assms indep_subset circuit_dep by auto

lemma dep_iff_supset_circuit:
  assumes "X \<subseteq> carrier"
  shows "\<not> indep X \<longleftrightarrow> (\<exists>C. circuit C \<and> C \<subseteq> X)"
  using assms dep_imp_supset_circuit supset_circuit_imp_dep by auto

context
  fixes \<E>
  assumes "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma dep_in_imp_supset_circuit_in:
  assumes "X \<subseteq> \<E>"
  assumes "\<not> indep_in \<E> X"
  shows "\<exists>C. circuit_in \<E> C \<and> C \<subseteq> X"
  unfolding circuit_in_def using \<E>.dep_imp_supset_circuit[OF assms] .

lemma supset_circuit_in_imp_dep_in:
  assumes "circuit_in \<E> C \<and> C \<subseteq> X"
  shows "\<not> indep_in \<E> X"
  using assms \<E>.supset_circuit_imp_dep unfolding circuit_in_def by auto

lemma dep_in_iff_supset_circuit_in:
  assumes "X \<subseteq> \<E>"
  shows "\<not> indep_in \<E> X \<longleftrightarrow> (\<exists>C. circuit_in \<E> C \<and> C \<subseteq> X)"
  using assms dep_in_imp_supset_circuit_in supset_circuit_in_imp_dep_in by auto

end

subsection \<open>Ranks\<close>

definition lower_rank_of :: "'a set \<Rightarrow> nat" where
  "lower_rank_of carrier' \<equiv> Min {card B | B. basis_in carrier' B}"

definition upper_rank_of :: "'a set \<Rightarrow> nat" where
  "upper_rank_of carrier' \<equiv> Max {card B | B. basis_in carrier' B}"

lemma collect_basis_finite: "finite (Collect basis)"
proof -
  have "Collect basis \<subseteq> {X. X \<subseteq> carrier}"
    using basis_subset_carrier by auto
  moreover have "finite \<dots>"
    using carrier_finite by auto
  ultimately show ?thesis using finite_subset by auto
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: indep_system \<E> "indep_in \<E>"
  using * by auto

lemma collect_basis_in_finite: "finite (Collect (basis_in \<E>))"
  unfolding basis_in_def using \<E>.collect_basis_finite .

lemma lower_rank_of_le: "lower_rank_of \<E> \<le> card \<E>"
proof -
  have "\<exists>n \<in> {card B | B. basis_in \<E> B}. n \<le> card \<E>"
    using card_mono[OF \<E>.carrier_finite basis_in_subset_carrier[OF *]] basis_in_ex[OF *] by auto
  moreover have "finite {card B | B. basis_in \<E> B}"
    using collect_basis_in_finite by auto
  ultimately show ?thesis
    unfolding lower_rank_of_def using basis_ex Min_le_iff by auto
qed

lemma upper_rank_of_le: "upper_rank_of \<E> \<le> card \<E>"
proof -
  have "\<forall>n \<in> {card B | B. basis_in \<E> B}. n \<le> card \<E>"
    using card_mono[OF \<E>.carrier_finite basis_in_subset_carrier[OF *]] by auto
  then show ?thesis
    unfolding upper_rank_of_def using basis_in_ex[OF *] collect_basis_in_finite by auto
qed

context
  fixes \<E>'
  assumes **: "\<E>' \<subseteq> \<E>"
begin

interpretation \<E>'\<^sub>1: indep_system \<E>' "indep_in \<E>'"
  using * ** by auto
interpretation \<E>'\<^sub>2: indep_system \<E>' "\<E>.indep_in \<E>'"
  using * ** by auto

lemma lower_rank_of_sub_cong:
  shows "\<E>.lower_rank_of \<E>' = lower_rank_of \<E>'"
proof -
  have "\<And>B. \<E>'\<^sub>1.basis B \<longleftrightarrow> \<E>'\<^sub>2.basis B"
    using ** basis_in_sub_cong[OF *, of \<E>']
    unfolding basis_in_def \<E>.basis_in_def by auto
  then show ?thesis
    unfolding lower_rank_of_def \<E>.lower_rank_of_def
    using basis_in_sub_cong[OF * **]
    by auto
qed

lemma upper_rank_of_sub_cong:
  shows "\<E>.upper_rank_of \<E>' = upper_rank_of \<E>'"
proof -
  have "\<And>B. \<E>'\<^sub>1.basis B \<longleftrightarrow> \<E>'\<^sub>2.basis B"
    using ** basis_in_sub_cong[OF *, of \<E>']
    unfolding basis_in_def \<E>.basis_in_def by auto
  then show ?thesis
    unfolding upper_rank_of_def \<E>.upper_rank_of_def
    using basis_in_sub_cong[OF * **]
    by auto
qed

end

end

end

end
