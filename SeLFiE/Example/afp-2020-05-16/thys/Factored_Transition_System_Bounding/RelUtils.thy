theory RelUtils
  imports Main "HOL.Transitive_Closure"
begin

\<comment> \<open>NOTE added definition.\<close>
definition reflexive where 
  "reflexive R \<equiv> \<forall>x. R x x"

\<comment> \<open>NOTE translation of 'TC' in relationScript.sml:69.\<close>
\<comment> \<open>TODO can we replace this with something from 'HOL.Transitive\_Closure'?\<close>
definition TC where
  "TC R a b \<equiv> (\<forall>P. (\<forall>x y. R x y \<longrightarrow> P x y) \<and> (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> P a b)"

\<comment> \<open>NOTE adapts transitive closure definitions of Isabelle and HOL4.\<close>
lemma TC_equiv_tranclp: "TC R a b \<longleftrightarrow> (R\<^sup>+\<^sup>+ a b)"
proof -
  {
    have "TC R a b \<Longrightarrow> (R\<^sup>+\<^sup>+ a b)"
      unfolding TC_def 
      using tranclp.r_into_trancl tranclp_trans
      by metis
  }
  moreover 
  {
    have "(R\<^sup>+\<^sup>+ a b) \<Longrightarrow> TC R a b" proof(induction rule: tranclp.induct)
      case (r_into_trancl a b)
      then show ?case by(subst TC_def; auto)
    next
      case (trancl_into_trancl a b c)
      then show ?case unfolding TC_def by blast
    qed 
  }
  ultimately show ?thesis
    by fast
qed

lemma TC_IMP_NOT_TC_CONJ_1:
  fixes R P  and  x y
  assumes "\<not>(R\<^sup>+\<^sup>+ x y)"
  shows "\<not>((\<lambda>x y. R x y \<and> P x y)\<^sup>+\<^sup>+ x y)"
proof -
  from assms(1) have 1: "\<not>TC R x y"
    using TC_equiv_tranclp
    by fast
  {
    assume P: "\<not>TC R x y"
    then obtain P where a: "(\<forall>x y. R x y \<longrightarrow> P x y) \<and> (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> \<not>P x y" 
      unfolding TC_def
      by blast
    {
      assume P_1: "(\<forall>x y. R x y \<longrightarrow> P x y)" "(\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z)"
      then have "(\<forall>x y. R x y \<and> P x y \<longrightarrow> P x y)" "(\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z)"
        by blast+
      moreover from a and P_1 have "\<not>P x y"
        by blast
      then have "\<exists>P. (\<forall>x y. R x y \<and> P x y \<longrightarrow> P x y) \<and> (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> \<not>P x y"
        by blast
    }
    then have "\<exists>P. 
      (\<forall>x y. R x y \<and> P x y \<longrightarrow> P x y) \<and> (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> \<not>P x y" 
      by blast 
  }
  note 2 = this
  {
    from 1 2 have "\<exists>P. 
      (\<forall>x y. R x y \<and> P x y \<longrightarrow> P x y) \<and> (\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z) \<longrightarrow> \<not>P x y" 
      by blast
    then have "\<not>TC (\<lambda>x y. R x y \<and> P x y) x y" 
      unfolding TC_def  
      by (metis assms tranclp.r_into_trancl tranclp_trans)
    then have "\<not>(\<lambda>x y. R x y \<and> P x y)\<^sup>+\<^sup>+ x y" 
      using TC_equiv_tranclp
      by fast
  }
  then show ?thesis
    by blast
qed

lemma TC_IMP_NOT_TC_CONJ:
  fixes R R' P x y
  assumes "\<forall>x y. P x y \<longrightarrow> R' x y \<longrightarrow> R x y" "\<not>R\<^sup>+\<^sup>+ x y"
  shows "\<not>(\<lambda>x y. R' x y \<and> P x y)\<^sup>+\<^sup>+ x y" 
proof -
  from assms(2)
  have 1: "\<not>(\<lambda>x y. R x y \<and> P x  y)\<^sup>+\<^sup>+ x y"
    using TC_IMP_NOT_TC_CONJ_1[where P="\<lambda>x y. P x y"]
    by blast
  {
    {
      from 1 have  "\<not>TC (\<lambda>x y. R x y \<and> P x  y) x y" 
        using TC_equiv_tranclp 
        by fast
      then have "\<exists>Pa.
      (\<forall>x y. R x y \<and> P x y \<longrightarrow> Pa x y) \<and> (\<forall>x y z. Pa x y \<and> Pa y z \<longrightarrow> Pa x z) 
      \<longrightarrow> \<not>Pa x y"
        unfolding TC_def
        by blast
    }
    then obtain Pa where a: 
      "(\<forall>x y. R x y \<and> P x y \<longrightarrow> Pa x y) \<and> (\<forall>x y z. Pa x y \<and> Pa y z \<longrightarrow> Pa x z) \<longrightarrow> \<not>Pa x y"
      by blast
    then have "\<not>(\<forall>Pa. (\<forall>x y. R' x y \<and> P x y \<longrightarrow> Pa x y) \<and> (\<forall>x y z. Pa x y \<and> Pa y z \<longrightarrow> Pa x z) \<longrightarrow> Pa x y)"
      by (metis assms(1) assms(2) tranclp.r_into_trancl tranclp_trans) 
    then have "\<not>TC (\<lambda>x y. R' x y \<and> P x y) x y" 
      unfolding TC_def
      by blast
  }
  then show ?thesis
    using TC_equiv_tranclp
    by fast
qed

\<comment> \<open>NOTE added lemma (relationScript.sml:314)\<close> 
lemma TC_INDUCT:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P
  assumes "(\<forall>x y. R x y \<longrightarrow> P x y)" "(\<forall>x y z. P x y \<and> P y z \<longrightarrow> P x z)" 
  shows "\<forall>u v. (TC R) u v \<longrightarrow> P u v"
  using assms
  unfolding TC_def
  by metis

lemma REFL_IMP_3_CONJ_1:
  fixes R P x y
  assumes "((\<lambda>x y. R x y \<and> P x y)\<^sup>+\<^sup>+ x y)"
  shows "R\<^sup>+\<^sup>+ x y" 
  using assms 
proof -
  show ?thesis
    using assms TC_IMP_NOT_TC_CONJ_1
    by fast
qed

lemma REFL_IMP_3_CONJ:
  fixes R'
  assumes "reflexive R'" 
  shows "(\<forall>P x y. 
    (R'\<^sup>+\<^sup>+ x y) \<longrightarrow> ( ((\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y) \<or> (\<exists>z. \<not>P z \<and> R'\<^sup>+\<^sup>+ x z \<and> R'\<^sup>+\<^sup>+ z y)))"
proof -
  {
    fix P
    {
      have "\<forall>x y. R' x y \<longrightarrow> (\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y \<or> (\<exists>z. \<not> P z \<and> R'\<^sup>+\<^sup>+ x z \<and> R'\<^sup>+\<^sup>+ z y)" 
      proof (auto)
        fix x y
        assume P: "R' x y" "\<forall>z. R'\<^sup>+\<^sup>+ x z \<longrightarrow> P z \<or> \<not> R'\<^sup>+\<^sup>+ z y"
        then show "(\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y"
        proof -
          have a: "\<And>a. \<not> R' x a \<or> \<not> R' a y \<or> P a"
            using P(2)
            by blast
          have "reflexive R'"
            by (meson assms)
          then show ?thesis
            using a P(1)
            by (simp add: reflexive_def tranclp.r_into_trancl)
        qed
      qed
    }
    moreover {
      have "\<forall>x y z. ((\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y \<or> (\<exists>z. \<not> P z \<and> R'\<^sup>+\<^sup>+ x z \<and> R'\<^sup>+\<^sup>+ z y)) \<and>
         ((\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ y z \<or> (\<exists>za. \<not> P za \<and> R'\<^sup>+\<^sup>+ y za \<and> R'\<^sup>+\<^sup>+ za z)) \<longrightarrow>
         (\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x z \<or> (\<exists>za. \<not> P za \<and> R'\<^sup>+\<^sup>+ x za \<and> R'\<^sup>+\<^sup>+ za z)" 
      proof (auto)
        fix x y z za
        assume P: "\<forall>za. R'\<^sup>+\<^sup>+ x za \<longrightarrow> P za \<or> \<not> R'\<^sup>+\<^sup>+ za z" "(\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y"
          "\<not> P za" "R'\<^sup>+\<^sup>+ y za" "R'\<^sup>+\<^sup>+ za z" 
        then show "(\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x z"
          using P
          by (meson P rtranclp_tranclp_tranclp TC_IMP_NOT_TC_CONJ_1  tranclp_into_rtranclp)
      next 
        fix x y z za
        assume P: "\<forall>za. R'\<^sup>+\<^sup>+ x za \<longrightarrow> P za \<or> \<not> R'\<^sup>+\<^sup>+ za z" "\<not> P za" "R'\<^sup>+\<^sup>+ x za" "R'\<^sup>+\<^sup>+ za y" 
          "(\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ y z" 
        then show "(\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x z"
          by (meson P TC_IMP_NOT_TC_CONJ_1 tranclp_trans)
      qed
    }
    ultimately have "\<forall>u v. 
      TC R' u v 
      \<longrightarrow> (\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ u v \<or> (\<exists>z. \<not> P z \<and> R'\<^sup>+\<^sup>+ u z \<and> R'\<^sup>+\<^sup>+ z v)"
      using TC_INDUCT[where R="R'" and
          P="\<lambda>x y. ( ((\<lambda>x y. R' x y \<and> P x \<and> P y)\<^sup>+\<^sup>+ x y) \<or> (\<exists>z. \<not>P z \<and> R'\<^sup>+\<^sup>+ x z \<and> R'\<^sup>+\<^sup>+ z y))"]
      by fast
  }
  then show ?thesis 
    by (simp add: TC_equiv_tranclp)
qed

lemma REFL_TC_CONJ:
  fixes R R' :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and P x y
  assumes "reflexive R'" "\<forall>x y. P x \<and> P y \<longrightarrow> (R' x y \<longrightarrow> R x y)" "\<not>(R\<^sup>+\<^sup>+ x y)"
  shows "(\<not>(R'\<^sup>+\<^sup>+ x y) \<or> (\<exists>z. \<not>P z \<and> (R')\<^sup>+\<^sup>+ x z \<and> (R')\<^sup>+\<^sup>+ z y))"
  using assms
proof (cases "\<not>R'\<^sup>+\<^sup>+ x y")
next
  case False
  then show ?thesis using assms 
      TC_IMP_NOT_TC_CONJ[where P="\<lambda>x y. P x \<and> P y"]
      REFL_IMP_3_CONJ[of R']
    by blast
qed blast

\<comment> \<open>NOTE 
  This is not a trivial translation: 'TC\_INDUCT' in relationScript.sml:314 differs significantly
from 'trancl\_induct' and 'trancl\_trans\_induct' in Transitive\_Closure:375, 391\<close>
lemma TC_CASES1_NEQ:
  fixes R x z
  assumes "R\<^sup>+\<^sup>+ x z"
  shows "R x z \<or> (\<exists>y :: 'a. \<not>(x = y) \<and> \<not>(y = z) \<and> R x y \<and> R\<^sup>+\<^sup>+ y z)"
proof -
  {
    fix u v
    have "\<forall>x y. R x y \<longrightarrow> R x y \<or> (\<exists>ya. x \<noteq> ya \<and> ya \<noteq> y \<and> R x ya \<and> R\<^sup>+\<^sup>+ ya y)"
      by meson
    moreover have "\<forall>x y z. 
      (R x y \<or> (\<exists>ya. x \<noteq> ya \<and> ya \<noteq> y \<and> R x ya \<and> R\<^sup>+\<^sup>+ ya y)) 
      \<and> (R y z \<or> (\<exists>ya. y \<noteq> ya \<and> ya \<noteq> z \<and> R y ya \<and> R\<^sup>+\<^sup>+ ya z)) 
      \<longrightarrow> R x z \<or> (\<exists>y. x \<noteq> y \<and> y \<noteq> z \<and> R x y \<and> R\<^sup>+\<^sup>+ y z)"
      by (metis tranclp.r_into_trancl tranclp_trans)
    ultimately have "TC R u v \<longrightarrow> R u v \<or> (\<exists>y. u \<noteq> y \<and> y \<noteq> v \<and> R u y \<and> R\<^sup>+\<^sup>+ y v)" 
      using TC_INDUCT[where P="\<lambda>x z. R x z \<or> (\<exists>y :: 'a. \<not>(x = y) \<and> \<not>(y = z) \<and> R x y \<and> R\<^sup>+\<^sup>+ y z)"]
      by blast
  }
  then show ?thesis 
    using assms TC_equiv_tranclp
    by (simp add: TC_equiv_tranclp)
qed
end