theory C
imports HOLCF "Mono-Nat-Fun"
begin

default_sort cpo

text \<open>
The initial solution to the domain equation $C = C_\bot$, i.e. the completion of the natural numbers.
\<close>

domain C = C (lazy "C")

lemma below_C: "x \<sqsubseteq> C\<cdot>x"
  by (induct x) auto

definition Cinf ("C\<^sup>\<infinity>") where "C\<^sup>\<infinity> = fix\<cdot>C"

lemma C_Cinf[simp]: "C\<cdot>C\<^sup>\<infinity> = C\<^sup>\<infinity>" unfolding Cinf_def by (rule fix_eq[symmetric])

abbreviation Cpow ("C\<^bsup>_\<^esup>") where "C\<^bsup>n\<^esup> \<equiv> iterate n\<cdot>C\<cdot>\<bottom>"

lemma C_below_C[simp]: "(C\<^bsup>i\<^esup> \<sqsubseteq> C\<^bsup>j\<^esup>) \<longleftrightarrow> i \<le> j"
  apply (induction i arbitrary: j)
  apply simp
  apply (case_tac j, auto)
  done

lemma below_Cinf[simp]: "r \<sqsubseteq> C\<^sup>\<infinity>"
  apply (induct r)
  apply simp_all[2]
  apply (metis (full_types) C_Cinf monofun_cfun_arg)
  done

lemma C_eq_Cinf[simp]: "C\<^bsup>i\<^esup> \<noteq> C\<^sup>\<infinity>"
  by (metis C_below_C Suc_n_not_le_n below_Cinf)

lemma Cinf_eq_C[simp]: "C\<^sup>\<infinity> = C \<cdot> r \<longleftrightarrow> C\<^sup>\<infinity> = r"
  by (metis C.injects C_Cinf)

lemma C_eq_C[simp]: "(C\<^bsup>i\<^esup> = C\<^bsup>j\<^esup>) \<longleftrightarrow> i = j"
  by (metis C_below_C le_antisym le_refl)

lemma case_of_C_below: "(case r of C\<cdot>y \<Rightarrow> x) \<sqsubseteq> x"
  by (cases r) auto

lemma C_case_below: "C_case \<cdot> f \<sqsubseteq> f"
  by (metis cfun_belowI C.case_rews(2) below_C monofun_cfun_arg)

lemma C_case_bot[simp]: "C_case \<cdot> \<bottom> = \<bottom>"
  apply (subst eq_bottom_iff)
  apply (rule C_case_below)
  done

lemma C_case_cong:
  assumes "\<And> r'. r = C\<cdot>r' \<Longrightarrow> f\<cdot>r' = g\<cdot>r'"
  shows "C_case\<cdot>f\<cdot>r = C_case\<cdot>g\<cdot>r"
using assms by (cases r) auto


lemma C_cases:
  obtains n where "r = C\<^bsup>n\<^esup>" | "r = C\<^sup>\<infinity>"
proof-
  { fix m
    have "\<exists> n. C_take m \<cdot> r = C\<^bsup>n\<^esup> "
    proof (rule C.finite_induct)
      have "\<bottom> = C\<^bsup>0\<^esup>" by simp
      thus "\<exists>n. \<bottom> = C\<^bsup>n\<^esup>"..
    next
      fix r
      show "\<exists>n. r = C\<^bsup>n\<^esup> \<Longrightarrow> \<exists>n. C\<cdot>r = C\<^bsup>n\<^esup>"
        by (auto simp del: iterate_Suc simp add: iterate_Suc[symmetric])
    qed
  }
  then obtain f where take: "\<And> m. C_take m \<cdot> r = C\<^bsup>f m\<^esup>" by metis
  have "chain (\<lambda> m. C\<^bsup>f m\<^esup>)" using ch2ch_Rep_cfunL[OF C.chain_take, where x=r, unfolded take].
  hence "mono f" by (auto simp add: mono_iff_le_Suc chain_def elim!:chainE)
  have r: "r = (\<Squnion> m. C\<^bsup>f m\<^esup>)"  by (metis (lifting) take C.reach lub_eq)
  from \<open>mono f\<close>
  show thesis
  proof(rule nat_mono_characterization)
    fix n
    assume n: "\<And> m. n \<le> m ==> f n = f m"
    have "max_in_chain n (\<lambda> m. C\<^bsup>f m\<^esup>)"
      apply (rule max_in_chainI)
      apply simp
      apply (erule n)
      done
    hence "(\<Squnion> m. C\<^bsup>f m\<^esup>) = C\<^bsup>f n\<^esup>" unfolding  maxinch_is_thelub[OF \<open>chain _\<close>].
    thus ?thesis using that unfolding r by blast
  next
    assume "\<And>m. \<exists>n. m \<le> f n"
    hence "\<And> n. C\<^bsup>n\<^esup> \<sqsubseteq> r" unfolding r by (fastforce intro: below_lub[OF \<open>chain _\<close>])
    hence "(\<Squnion> n. C\<^bsup>n\<^esup>) \<sqsubseteq> r" 
      by (rule lub_below[OF chain_iterate])
    hence "C\<^sup>\<infinity> \<sqsubseteq> r" unfolding Cinf_def fix_def2.
    hence "C\<^sup>\<infinity> = r" using below_Cinf by (metis below_antisym)
    thus thesis using that by blast
  qed
qed


lemma C_case_Cinf[simp]: "C_case \<cdot> f \<cdot> C\<^sup>\<infinity> = f \<cdot> C\<^sup>\<infinity>"
  unfolding Cinf_def
  by (subst fix_eq) simp

end
