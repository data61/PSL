section \<open>{Assert and Assume}\<close>
theory RefineG_Assert
imports RefineG_Transfer
begin

definition "iASSERT return \<Phi> \<equiv> if \<Phi> then return () else top"
definition "iASSUME return \<Phi> \<equiv> if \<Phi> then return () else bot"

  locale generic_Assert =
    fixes bind :: 
      "('mu::complete_lattice) \<Rightarrow> (unit \<Rightarrow> ('ma::complete_lattice)) \<Rightarrow> 'ma"
    fixes return :: "unit \<Rightarrow> 'mu"
    fixes ASSERT
    fixes ASSUME
    assumes ibind_strict: 
      "bind bot f = bot" 
      "bind top f = top"
    assumes imonad1: "bind (return u) f = f u"
    assumes ASSERT_eq: "ASSERT \<equiv> iASSERT return"
    assumes ASSUME_eq: "ASSUME \<equiv> iASSUME return"
  begin
     lemma ASSERT_simps[simp,code]: 
      "ASSERT True = return ()"
      "ASSERT False = top"
      unfolding ASSERT_eq iASSERT_def by auto

    lemma ASSUME_simps[simp,code]: 
      "ASSUME True = return ()"
      "ASSUME False = bot"
      unfolding ASSUME_eq iASSUME_def by auto

    lemma le_ASSERTI: "\<lbrakk> \<Phi> \<Longrightarrow> M\<le>M' \<rbrakk> \<Longrightarrow> M \<le> bind (ASSERT \<Phi>) (\<lambda>_. M')"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)

    lemma le_ASSERTI_pres: "\<lbrakk> \<Phi> \<Longrightarrow> M\<le>bind (ASSERT \<Phi>) (\<lambda>_. M') \<rbrakk> 
      \<Longrightarrow> M \<le> bind (ASSERT \<Phi>) (\<lambda>_. M')"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)

    lemma ASSERT_leI: "\<lbrakk> \<Phi>; \<Phi> \<Longrightarrow> M\<le>M' \<rbrakk> \<Longrightarrow> bind (ASSERT \<Phi>) (\<lambda>_. M) \<le> M'"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)


    lemma ASSUME_leI: "\<lbrakk> \<Phi> \<Longrightarrow> M\<le>M' \<rbrakk> \<Longrightarrow> bind (ASSUME \<Phi>) (\<lambda>_. M) \<le> M'"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)
    lemma ASSUME_leI_pres: "\<lbrakk> \<Phi> \<Longrightarrow> bind (ASSUME \<Phi>) (\<lambda>_. M)\<le>M' \<rbrakk> 
      \<Longrightarrow> bind (ASSUME \<Phi>) (\<lambda>_. M) \<le> M'"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)
    lemma le_ASSUMEI: "\<lbrakk> \<Phi>; \<Phi> \<Longrightarrow> M\<le>M' \<rbrakk> \<Longrightarrow> M \<le> bind (ASSUME \<Phi>) (\<lambda>_. M')"
      apply (cases \<Phi>) by (auto simp: ibind_strict imonad1)

    text \<open>The order of these declarations does matter!\<close>
    lemmas [intro?] = ASSERT_leI le_ASSUMEI
    lemmas [intro?] = le_ASSERTI ASSUME_leI

    lemma ASSERT_le_iff: 
      "bind (ASSERT \<Phi>) (\<lambda>_. S) \<le> S' \<longleftrightarrow> (S'\<noteq>top \<longrightarrow> \<Phi>) \<and> S\<le>S'"
      by (cases \<Phi>) (auto simp: ibind_strict imonad1 simp: top_unique)

    lemma ASSUME_le_iff:
      "bind (ASSUME \<Phi>) (\<lambda>_. S) \<le> S' \<longleftrightarrow> (\<Phi> \<longrightarrow> S\<le>S')"
      by (cases \<Phi>) (auto simp: ibind_strict imonad1)

    lemma le_ASSERT_iff:
      "S \<le> bind (ASSERT \<Phi>) (\<lambda>_. S') \<longleftrightarrow> (\<Phi> \<longrightarrow> S\<le>S')"
      by (cases \<Phi>) (auto simp: ibind_strict imonad1)

    lemma le_ASSUME_iff:
      "S \<le> bind (ASSUME \<Phi>) (\<lambda>_. S') \<longleftrightarrow> (S\<noteq>bot \<longrightarrow> \<Phi>) \<and> S\<le>S'"
      by (cases \<Phi>) (auto simp: ibind_strict imonad1 simp: bot_unique)
  end

  text \<open>
    This locale transfer's asserts and assumes. 
    To remove them, use the next locale.
\<close>
  locale transfer_generic_Assert = 
    c: generic_Assert cbind creturn cASSERT cASSUME +
    a: generic_Assert abind areturn aASSERT aASSUME +
    ordered_transfer \<alpha>
    for cbind :: "('muc::complete_lattice) 
      \<Rightarrow> (unit\<Rightarrow>'mac) \<Rightarrow> ('mac::complete_lattice)" 
    and creturn :: "unit \<Rightarrow> 'muc" and cASSERT and cASSUME
    and abind :: "('mua::complete_lattice) 
      \<Rightarrow> (unit\<Rightarrow>'maa) \<Rightarrow> ('maa::complete_lattice)"
    and areturn :: "unit \<Rightarrow> 'mua" and aASSERT and aASSUME
    and \<alpha> :: "'mac \<Rightarrow> 'maa"
  begin
    lemma transfer_ASSERT[refine_transfer]:
      "\<lbrakk>\<Phi> \<Longrightarrow> \<alpha> M \<le> M'\<rbrakk> 
      \<Longrightarrow> \<alpha> (cbind (cASSERT \<Phi>) (\<lambda>_. M)) \<le> (abind (aASSERT \<Phi>) (\<lambda>_. M'))"
      apply (cases \<Phi>)
      apply (auto simp: c.ibind_strict a.ibind_strict c.imonad1 a.imonad1)
      done

    lemma transfer_ASSUME[refine_transfer]:
      "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> \<alpha> M \<le> M'\<rbrakk> 
      \<Longrightarrow> \<alpha> (cbind (cASSUME \<Phi>) (\<lambda>_. M)) \<le> (abind (aASSUME \<Phi>) (\<lambda>_. M'))"
      apply (auto simp: c.ibind_strict a.ibind_strict c.imonad1 a.imonad1)
      done

  end


  locale transfer_generic_Assert_remove = 
    a: generic_Assert abind areturn aASSERT aASSUME +
    transfer \<alpha>
    for abind :: "('mua::complete_lattice) 
      \<Rightarrow> (unit\<Rightarrow>'maa) \<Rightarrow> ('maa::complete_lattice)"
    and areturn :: "unit \<Rightarrow> 'mua" and aASSERT and aASSUME
    and \<alpha> :: "'mac \<Rightarrow> 'maa"
  begin
    lemma transfer_ASSERT_remove[refine_transfer]: 
      "\<lbrakk> \<Phi> \<Longrightarrow> \<alpha> M \<le> M' \<rbrakk> \<Longrightarrow> \<alpha> M \<le> abind (aASSERT \<Phi>) (\<lambda>_. M')"
      by (rule a.le_ASSERTI)

    lemma transfer_ASSUME_remove[refine_transfer]: 
      "\<lbrakk> \<Phi>; \<Phi> \<Longrightarrow> \<alpha> M \<le> M' \<rbrakk> \<Longrightarrow> \<alpha> M \<le> abind (aASSUME \<Phi>) (\<lambda>_. M')"
      by (rule a.le_ASSUMEI)
  end

end
