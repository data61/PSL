section \<open>Fixpoint of Converging Program Transformations\<close>

theory Fixpoint
  imports Compiler
begin

context
  fixes
    m :: "'a \<Rightarrow> nat" and
    f :: "'a \<Rightarrow> 'a option"
begin

function fixpoint :: "'a \<Rightarrow> 'a option" where
  "fixpoint x = (
    case f x of
      None \<Rightarrow> None |
      Some x' \<Rightarrow> if m x' < m x then fixpoint x' else Some x'
  )"
by pat_completeness auto
termination
proof (relation "measure m")
  show "wf (measure m)" by auto
next
  fix x x'
  assume "f x = Some x'" and "m x' < m x"
  thus "(x', x) \<in> measure m" by simp
qed

end

lemma fixpoint_to_comp_pow:
  "fixpoint m f x = y \<Longrightarrow> \<exists>n. option_comp_pow f n x = y"
proof (induction x arbitrary: y rule: fixpoint.induct[where f = f and m = m])
  case (1 x)
  show ?case
  proof (cases "f x")
    case None
    then show ?thesis
      using "1.prems"
      by (metis (no_types, lifting) fixpoint.simps option.case_eq_if option_comp_pow.simps(1))
  next
    case (Some a)
    show ?thesis
    proof (cases "m a < m x")
      case True
      hence "fixpoint m f a = y"
        using "1.prems" Some by simp
      then show ?thesis
        using "1.IH"[OF Some True]
        by (metis Some bind.simps(2) old.nat.exhaust option_comp_def option_comp_pow.simps(1,3))
    next
      case False
      then show ?thesis
        using "1.prems" Some
        apply simp
        by (metis option_comp_pow.simps(2))
    qed
  qed
qed

lemma fixpoint_eq_comp_pow:
  "\<exists>n. fixpoint m f x = option_comp_pow f n x"
  by (metis fixpoint_to_comp_pow)

lemma compiler_composition_fixpoint:
  assumes
    "compiler step step final final load load order match compile"
  shows "compiler step step final final load load
    (lexp order\<^sup>+\<^sup>+) (rel_comp_pow match) (fixpoint m compile)"
proof (rule compiler.intro)
  show "compiler_axioms load load (rel_comp_pow match) (fixpoint m compile)"
  proof unfold_locales
    fix p1 p2 s1
    assume "fixpoint m compile p1 = Some p2" and "load p1 = Some s1"
    obtain n where "fixpoint m compile p1 = option_comp_pow compile n p1"
      using fixpoint_eq_comp_pow by metis

    thus "\<exists>s2 i. load p2 = Some s2 \<and> rel_comp_pow match i s1 s2"
      using \<open>fixpoint m compile p1 = Some p2\<close> assms compiler.compile_load compiler_composition_pow
      using \<open>load p1 = Some s1\<close> by fastforce
  qed
qed (auto intro: assms compiler.axioms backward_simulation_pow)

end
