theory Iterative
imports "Env-HOLCF"
begin

text \<open>
A setup for defining a fixed point of mutual recursive environments iteratively
\<close>

locale iterative =
  fixes \<rho> :: "'a::type \<Rightarrow> 'b::pcpo"
   and e1 :: "('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b)"
   and e2 :: "('a \<Rightarrow> 'b) \<rightarrow> 'b"
   and S :: "'a set" and x :: 'a
  assumes ne:"x \<notin> S"
begin
  abbreviation "L == (\<Lambda> \<rho>'. (\<rho> ++\<^bsub>S\<^esub> e1 \<cdot> \<rho>')(x := e2 \<cdot> \<rho>'))"
  abbreviation "H == (\<lambda> \<rho>'. \<Lambda> \<rho>''. \<rho>' ++\<^bsub>S\<^esub> e1 \<cdot> \<rho>'')"
  abbreviation "R == (\<Lambda> \<rho>'. (\<rho> ++\<^bsub>S\<^esub> (fix \<cdot> (H \<rho>')))(x := e2 \<cdot> \<rho>'))"
  abbreviation "R' == (\<Lambda> \<rho>'. (\<rho> ++\<^bsub>S\<^esub> (fix \<cdot> (H \<rho>')))(x := e2 \<cdot> (fix \<cdot> (H \<rho>'))))"

  lemma split_x:
    fixes y
    obtains "y = x" and "y \<notin> S" | "y \<in> S" and "y \<noteq> x" | "y \<notin> S" and "y \<noteq> x" using ne by blast
  lemmas below = fun_belowI[OF split_x, where y1 = "\<lambda>x. x"]
  lemmas eq = ext[OF split_x, where y1 = "\<lambda>x. x"]

  lemma lookup_fix[simp]:
    fixes y and F :: "('a \<Rightarrow> 'b) \<rightarrow> ('a \<Rightarrow> 'b)"
    shows "(fix \<cdot> F) y = (F \<cdot> (fix \<cdot> F)) y"
    by (subst fix_eq, rule)

  lemma R_S: "\<And> y. y \<in> S \<Longrightarrow> (fix \<cdot> R) y = (e1 \<cdot> (fix \<cdot> (H (fix \<cdot> R)))) y"
    by (case_tac y rule: split_x) simp_all

  lemma R'_S: "\<And> y. y \<in> S \<Longrightarrow> (fix \<cdot> R') y = (e1 \<cdot> (fix \<cdot> (H (fix \<cdot> R')))) y"
    by (case_tac y rule: split_x) simp_all

  lemma HR_is_R[simp]: "fix\<cdot>(H (fix \<cdot> R)) = fix \<cdot> R"
    by (rule eq) simp_all

  lemma HR'_is_R'[simp]: "fix \<cdot> (H (fix \<cdot> R')) = fix \<cdot> R'"
    by (rule eq) simp_all

  lemma H_noop:
    fixes \<rho>' \<rho>''
    assumes "\<And> y. y \<in> S \<Longrightarrow> y \<noteq> x \<Longrightarrow> (e1 \<cdot> \<rho>'') y \<sqsubseteq> \<rho>' y"
    shows "H \<rho>' \<cdot> \<rho>'' \<sqsubseteq> \<rho>'"
      using assms
      by -(rule below, simp_all)

  lemma HL_is_L[simp]: "fix \<cdot> (H (fix \<cdot> L)) = fix \<cdot> L"
  proof (rule below_antisym)
    show "fix \<cdot> (H (fix \<cdot> L)) \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF H_noop]) simp
    hence *: "e2 \<cdot> (fix \<cdot> (H (fix \<cdot> L))) \<sqsubseteq> e2 \<cdot> (fix \<cdot> L)" by (rule monofun_cfun_arg)

    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> (H (fix \<cdot> L))"
      by (rule fix_least_below[OF below]) (simp_all add: ne *)
  qed
  
  lemma iterative_override_on:
    shows "fix \<cdot> L = fix \<cdot> R"
  proof(rule below_antisym)
    show "fix \<cdot> R \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF below]) simp_all

    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> R"
      apply (rule fix_least_below[OF below])
      apply simp
      apply (simp del: lookup_fix add: R_S)
      apply simp
      done
  qed

  lemma iterative_override_on':
    shows "fix \<cdot> L = fix \<cdot>  R'"
  proof(rule below_antisym)
    show "fix \<cdot> R' \<sqsubseteq> fix \<cdot> L"
      by (rule fix_least_below[OF below]) simp_all
  
    show "fix \<cdot> L \<sqsubseteq> fix \<cdot> R'"
      apply (rule fix_least_below[OF below])
      apply simp
      apply (simp del: lookup_fix add: R'_S)
      apply simp
      done
  qed
end

end
