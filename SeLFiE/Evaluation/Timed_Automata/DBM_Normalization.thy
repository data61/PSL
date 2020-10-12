section \<open>Normalization of DBMs\<close>

theory DBM_Normalization
imports DBM_Basics
begin

text \<open>This is the implementation of the common approximation operation.\<close>

fun norm_upper :: "('t::time) DBMEntry \<Rightarrow> 't \<Rightarrow> ('t::time) DBMEntry"
where
  "norm_upper e t = (if Le t \<prec> e then \<infinity> else e)"
  
fun norm_lower :: "('t::time) DBMEntry \<Rightarrow> 't \<Rightarrow> ('t::time) DBMEntry"
where
  "norm_lower e t = (if e \<prec> Lt t then Lt t else e)"

text \<open>
  Note that literature pretends that \<open>\<zero>\<close> would have some (presumably infinite bound) in \<open>k\<close>
  and thus defines normalization uniformly. The easiest way to get around this seems to explicate
  this in the definition as below.
\<close>
definition norm :: "('t::time) DBM \<Rightarrow> (nat \<Rightarrow> 't) \<Rightarrow> nat \<Rightarrow> 't DBM"
where
  "norm M k n \<equiv> \<lambda> i j.
    let ub = if i > 0 then (k i) else 0 in
    let lb = if j > 0 then (- k j) else 0 in
    if i \<le> n \<and> j \<le> n then norm_lower (norm_upper (M i j) ub) lb else M i j
  "

section \<open>Normalization is a Widening Operator\<close>

lemma norm_mono:
  assumes "\<forall>c. v c > 0" "u \<in> [M]\<^bsub>v,n\<^esub>"
  shows "u \<in> [norm M k n]\<^bsub>v,n\<^esub>" (is "u \<in> [?M2]\<^bsub>v,n\<^esub>")
proof -
  note A = assms
  note M1 = A(2)[unfolded DBM_zone_repr_def DBM_val_bounded_def]
  show ?thesis
  proof (unfold DBM_zone_repr_def DBM_val_bounded_def, auto)
    show "Le 0 \<preceq> ?M2 0 0"
    using A unfolding norm_def DBM_zone_repr_def DBM_val_bounded_def dbm_le_def by auto
  next
    fix c assume "v c \<le> n"
    with M1 have M1: "dbm_entry_val u None (Some c) (M 0 (v c))" by auto
    from \<open>v c \<le> n\<close> A have *:
      "?M2 0 (v c) = norm_lower (norm_upper (M 0 (v c)) 0) (- k (v c))"
    unfolding norm_def by auto
    show "dbm_entry_val u None (Some c) (?M2 0 (v c))"
    proof (cases "M 0 (v c) \<prec> Lt (- k (v c))")
      case True
      show ?thesis
      proof (cases "Le 0 \<prec> M 0 (v c)")
        case True with * show ?thesis by auto
      next
        case False 
        with * True have "?M2 0 (v c) = Lt (- k (v c))" by auto
        moreover from True dbm_entry_val_mono_2[OF M1] have
          "dbm_entry_val u None (Some c) (Lt (- k (v c)))"
        by auto
        ultimately show ?thesis by auto
      qed
    next
      case False
      show ?thesis
      proof (cases "Le 0 \<prec> M 0 (v c)")
        case True with * show ?thesis by auto
      next
        case F: False
        with M1 * False show ?thesis by auto
      qed
    qed
  next
    fix c assume "v c \<le> n"
    with M1 have M1: "dbm_entry_val u (Some c) None (M (v c) 0)" by auto
    from \<open>v c \<le> n\<close> A have *:
      "?M2 (v c) 0 = norm_lower (norm_upper (M (v c) 0) (k (v c))) 0"
    unfolding norm_def by auto
    show "dbm_entry_val u (Some c) None (?M2 (v c) 0)"
    proof (cases "Le (k (v c)) \<prec> M (v c) 0")
      case True
      with A(1,2) \<open>v c \<le> n\<close> have "?M2 (v c) 0 = \<infinity>" unfolding norm_def by auto
      then show ?thesis by auto
    next
      case False
      show ?thesis
      proof (cases "M (v c) 0 \<prec> Lt 0")
        case True with False * dbm_entry_val_mono_3[OF M1] show ?thesis by auto
      next
        case F: False
        with M1 * False show ?thesis by auto
      qed
    qed
  next
    fix c1 c2 assume "v c1 \<le> n" "v c2 \<le> n"
    with M1 have M1: "dbm_entry_val u (Some c1) (Some c2) (M (v c1) (v c2))" by auto
    then show "dbm_entry_val u (Some c1) (Some c2) (?M2 (v c1) (v c2))"
    proof (cases "Le (k (v c1)) \<prec> M (v c1) (v c2)")
      case True
      with A(1,2) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have "?M2 (v c1) (v c2) = \<infinity>" unfolding norm_def by auto
      then show ?thesis by auto
    next
      case False
      with A(1,2) \<open>v c1 \<le> n\<close> \<open>v c2 \<le> n\<close> have
        *: "?M2 (v c1) (v c2) = norm_lower (M (v c1) (v c2)) (- k (v c2))"
      unfolding norm_def by auto
      show ?thesis
      proof (cases "M (v c1) (v c2) \<prec> Lt (- k (v c2))")
        case True
        with dbm_entry_val_mono_1[OF M1] have
          "dbm_entry_val u (Some c1) (Some c2) (Lt (- k (v c2)))"
        by auto
        then have "u c1 - u c2 < - k (v c2)" by auto
        with * True show ?thesis by auto
      next
        case False with M1 * show ?thesis by auto
      qed
    qed
  qed
qed

end
