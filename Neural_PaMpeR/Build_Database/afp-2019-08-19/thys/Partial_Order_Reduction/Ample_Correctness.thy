section \<open>Correctness Theorem of Partial Order Reduction\<close>

theory Ample_Correctness
imports
  Ample_Abstract
  Formula
begin

  locale ample_correctness =
    S: transition_system_complete ex en init int +
    R: transition_system_complete ex ren init int +
    F: formula_next_free \<phi> +
    ample_abstract ex en init int ind src ren
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
    and src :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
    and ren :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and \<phi> :: "'interpretation pltl"
  begin

    lemma reduction_language_indistinguishable:
      assumes "R.language \<subseteq> F.language"
      shows "S.language \<subseteq> F.language"
    proof
      fix u
      assume 1: "u \<in> S.language"
      obtain v where 2: "v \<in> R.language" "snth u \<approx> snth v" using reduction_language_stuttering 1 by this
      have 3: "v \<in> F.language" using assms 2(1) by rule
      show "u \<in> F.language" using 2(2) 3 by auto
    qed

    theorem reduction_correct: "S.language \<subseteq> F.language \<longleftrightarrow> R.language \<subseteq> F.language"
      using reduction_language_subset reduction_language_indistinguishable by blast

  end

end