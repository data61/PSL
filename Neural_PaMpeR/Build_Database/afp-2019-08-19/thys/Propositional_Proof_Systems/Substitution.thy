subsection\<open>Substitutions\<close>
theory Substitution
imports Formulas
begin

primrec subst where
"subst A F (Atom B) = (if A = B then F else Atom B)" |
"subst _ _ \<bottom> = \<bottom>" |
"subst A F (G \<^bold>\<or> H) = (subst A F G \<^bold>\<or> subst A F H)" |
"subst A F (G \<^bold>\<and> H) = (subst A F G \<^bold>\<and> subst A F H)" |
"subst A F (G \<^bold>\<rightarrow> H) = (subst A F G \<^bold>\<rightarrow> subst A F H)" |
"subst A F (\<^bold>\<not> H) = (\<^bold>\<not> (subst A F H))"
term subst
abbreviation subst_syntax ("(_[/(_/'//_)])" [70,70] 69) where
"A[B / C] \<equiv> subst C B A"

lemma no_subst[simp]: "k \<notin> atoms F \<Longrightarrow> F[G / k] = F" by(induction F; simp)
lemma subst_atoms: "k \<in> atoms F \<Longrightarrow> atoms (F[G / k]) = atoms F - {k} \<union> atoms G" 
proof(induction F)
  case (And F G) thus ?case by(cases "k \<in> atoms F"; force) next
  case (Or F G) thus ?case by(cases "k \<in> atoms F"; force) next
  case (Imp F G) thus ?case by(cases "k \<in> atoms F"; force) next
qed simp_all

lemma subst_atoms_simp: "atoms (F[G / k]) = atoms F - {k} \<union> (if k \<in> atoms F then atoms G else {})"
  by(simp add: subst_atoms)

end
