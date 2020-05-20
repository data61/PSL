(* Title:      Kleene Algebra
   Author:     Alasdair Armstrong, Georg Struth, Tjark Weber
   Maintainer: Georg Struth <g.struth at sheffield.ac.uk>
               Tjark Weber <tjark.weber at it.uu.se>
*)

section \<open>Models of Omega Algebras\<close>

theory Omega_Algebra_Models
imports Omega_Algebra Kleene_Algebra_Models
begin

text \<open>The trace, path and language model are not really interesting
in this setting.\<close>

subsection \<open>Relation Omega Algebras\<close>

text \<open>In the relational model, the omega of a relation relates all
those elements in the domain of the relation, from which an infinite
chain starts, with all other elements; all other elements are not
related to anything~\cite{hofnerstruth10nontermination}. Thus, the
omega of a relation is most naturally defined coinductively.\<close>

coinductive_set omega :: "('a \<times> 'a) set \<Rightarrow> ('a \<times> 'a) set" for R where
  "\<lbrakk> (x, y) \<in> R; (y, z) \<in> omega R \<rbrakk> \<Longrightarrow> (x, z) \<in> omega R"

(* FIXME: The equivalent, but perhaps more elegant point-free version
  "x \<in> R O omega R \<Longrightarrow> x \<in> omega R"
fails due to missing monotonicity lemmas. *)

text \<open>Isabelle automatically derives a case rule and a coinduction
theorem for @{const omega}. We prove slightly more elegant
variants.\<close>

lemma omega_cases: "(x, z) \<in> omega R \<Longrightarrow>
  (\<And>y. (x, y) \<in> R \<Longrightarrow> (y, z) \<in> omega R \<Longrightarrow> P) \<Longrightarrow> P"
by (metis omega.cases)

lemma omega_coinduct: "X x z \<Longrightarrow>
  (\<And>x z. X x z \<Longrightarrow> \<exists>y. (x, y) \<in> R \<and> (X y z \<or> (y, z) \<in> omega R)) \<Longrightarrow>
  (x, z) \<in> omega R"
by (metis (full_types) omega.coinduct)

lemma omega_weak_coinduct: "X x z \<Longrightarrow>
  (\<And>x z. X x z \<Longrightarrow> \<exists>y. (x, y) \<in> R \<and> X y z) \<Longrightarrow>
  (x, z) \<in> omega R" 
by (metis omega.coinduct)

interpretation rel_omega_algebra: omega_algebra "(\<union>)" "(O)" Id "{}" "(\<subseteq>)" "(\<subset>)" rtrancl omega
proof
  fix x :: "'a rel"
  show "omega x \<subseteq> x O omega x"
    by (auto elim: omega_cases)
next
  fix x y z :: "'a rel"
  assume *: "y \<subseteq> z \<union> x O y"
  {
    fix a b
    assume 1: "(a,b) \<in> y" and 2: "(a,b) \<notin> x\<^sup>* O z"
    have "(a,b) \<in> omega x"
    proof (rule omega_weak_coinduct[where X="\<lambda>a b. (a,b) \<in> x O y \<and> (a,b) \<notin> x\<^sup>* O z"])
      show "(a,b) \<in> x O y \<and> (a,b) \<notin> x\<^sup>* O z"
        using "*" "1" "2" by auto
    next
      fix a c
      assume 1: "(a,c) \<in> x O y \<and> (a,c) \<notin> x\<^sup>* O z"
      then obtain b where 2: "(a,b) \<in> x" and "(b,c) \<in> y"
        by auto
      then have "(b,c) \<in> x O y"
        using "*" "1" by blast
      moreover have "(b,c) \<notin> x\<^sup>* O z"
        using "1" "2" by (meson relcomp.cases relcomp.intros converse_rtrancl_into_rtrancl)
      ultimately show "\<exists>b. (a,b) \<in> x \<and> (b,c) \<in> x O y \<and> (b,c) \<notin> x\<^sup>* O z"
        using "2" by blast
    qed
  }
  then show "y \<subseteq> omega x \<union> x\<^sup>* O z"
    by auto
qed

end
