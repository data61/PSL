theory "HOLCF-Join"
imports HOLCF
begin

subsubsection \<open>Binary Joins and compatibility\<close>

context cpo
begin
definition join :: "'a => 'a => 'a" (infixl "\<squnion>" 80) where
  "x \<squnion> y = (if \<exists> z. {x, y} <<| z then lub {x, y} else x)"

definition compatible :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  where "compatible x y = (\<exists> z. {x, y} <<| z)"

lemma compatibleI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "compatible x y"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding compatible_def by (metis)
qed

lemma is_joinI:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "x \<squnion> y = z"
proof-
  from assms
  have "{x,y} <<| z"
    by (auto intro: is_lubI)
  thus ?thesis unfolding join_def by (metis lub_eqI)
qed

lemma is_join_and_compatible:
  assumes "x \<sqsubseteq> z"
  assumes "y \<sqsubseteq> z"
  assumes "\<And> a. \<lbrakk> x \<sqsubseteq> a ; y \<sqsubseteq> a \<rbrakk> \<Longrightarrow> z \<sqsubseteq> a"
  shows "compatible x y \<and> x \<squnion> y = z"
by (metis compatibleI is_joinI assms)

lemma compatible_sym: "compatible x y \<Longrightarrow> compatible y x"
  unfolding compatible_def by (metis insert_commute)

lemma compatible_sym_iff: "compatible x y \<longleftrightarrow> compatible y x"
  unfolding compatible_def by (metis insert_commute)

lemma join_above1: "compatible x y \<Longrightarrow> x \<sqsubseteq> x \<squnion> y"
  unfolding compatible_def join_def
  apply auto
  by (metis is_lubD1 is_ub_insert lub_eqI)  

lemma join_above2: "compatible x y \<Longrightarrow> y \<sqsubseteq> x \<squnion> y"
  unfolding compatible_def join_def
  apply auto
  by (metis is_lubD1 is_ub_insert lub_eqI)  

lemma larger_is_join1: "y \<sqsubseteq> x \<Longrightarrow> x \<squnion> y = x"
  unfolding join_def
  by (metis doubleton_eq_iff lub_bin)

lemma larger_is_join2: "x \<sqsubseteq> y \<Longrightarrow> x \<squnion> y = y"
  unfolding join_def
  by (metis is_lub_bin lub_bin)

lemma join_self[simp]: "x \<squnion> x = x"
  unfolding join_def  by auto
end

lemma join_commute:  "compatible x y \<Longrightarrow> x \<squnion> y = y \<squnion> x"
  unfolding compatible_def unfolding join_def by (metis insert_commute)

lemma lub_is_join:
  "{x, y} <<| z \<Longrightarrow> x \<squnion> y = z"
unfolding join_def by (metis lub_eqI)

lemma compatible_refl[simp]: "compatible x x"
  by (rule compatibleI[OF below_refl below_refl])

lemma join_mono:
  assumes "compatible a b"
  and "compatible c d"
  and "a \<sqsubseteq> c"
  and "b \<sqsubseteq> d"
  shows "a \<squnion> b \<sqsubseteq> c \<squnion> d"
proof-
  from assms obtain x y where "{a, b} <<| x" "{c, d} <<| y" unfolding compatible_def by auto
  with assms have "a \<sqsubseteq> y" "b \<sqsubseteq> y" by (metis below.r_trans is_lubD1 is_ub_insert)+
  with \<open>{a, b} <<| x\<close> have "x \<sqsubseteq> y" by (metis is_lub_below_iff is_lub_singleton is_ub_insert)
  moreover
  from \<open>{a, b} <<| x\<close> \<open>{c, d} <<| y\<close> have "a \<squnion> b = x" "c \<squnion> d = y" by (metis lub_is_join)+
  ultimately
  show ?thesis by simp
qed

lemma
  assumes "compatible x y"
  shows join_above1: "x \<sqsubseteq> x \<squnion> y" and join_above2: "y \<sqsubseteq> x \<squnion> y"
proof-
  from assms obtain z where "{x,y} <<| z" unfolding compatible_def by auto
  hence  "x \<squnion> y = z" and "x \<sqsubseteq> z" and "y \<sqsubseteq> z" apply (auto intro: lub_is_join) by (metis is_lubD1 is_ub_insert)+
  thus "x \<sqsubseteq> x \<squnion> y" and "y \<sqsubseteq> x \<squnion> y" by simp_all
qed

lemma
  assumes "compatible x y"
  shows compatible_above1: "compatible x (x \<squnion> y)" and compatible_above2: "compatible y (x \<squnion> y)"
proof-
  from assms obtain z where "{x,y} <<| z" unfolding compatible_def by auto
  hence  "x \<squnion> y = z" and "x \<sqsubseteq> z" and "y \<sqsubseteq> z" apply (auto intro: lub_is_join) by (metis is_lubD1 is_ub_insert)+
  thus  "compatible x (x \<squnion> y)" and  "compatible y (x \<squnion> y)" by (metis below.r_refl compatibleI)+
qed

lemma join_below:
  assumes "compatible x y"
  and "x \<sqsubseteq> a" and "y \<sqsubseteq> a"
  shows "x \<squnion> y \<sqsubseteq> a"
proof-
  from assms obtain z where z: "{x,y} <<| z" unfolding compatible_def by auto
  with assms have "z \<sqsubseteq> a" by (metis is_lub_below_iff is_ub_empty is_ub_insert)
  moreover
  from z have "x \<squnion> y = z" by (rule lub_is_join) 
  ultimately show ?thesis by simp
qed

lemma join_below_iff:
  assumes "compatible x y"
  shows "x \<squnion> y \<sqsubseteq> a \<longleftrightarrow> (x \<sqsubseteq> a \<and> y \<sqsubseteq> a)"
  by (metis assms below_trans cpo_class.join_above1 cpo_class.join_above2 join_below)

lemma join_assoc:
  assumes "compatible x y"
  assumes "compatible x (y \<squnion> z)"
  assumes "compatible y z"
  shows "(x \<squnion> y) \<squnion> z = x \<squnion> (y \<squnion> z)"
  apply (rule is_joinI)
  apply (rule join_mono[OF assms(1) assms(2) below_refl join_above1[OF assms(3)]])
  apply (rule below_trans[OF join_above2[OF assms(3)] join_above2[OF assms(2)]])
  apply (rule join_below[OF assms(2)])
  apply (erule rev_below_trans)
  apply (rule join_above1[OF assms(1)])
  apply (rule join_below[OF assms(3)])
  apply (erule rev_below_trans)
  apply (rule join_above2[OF assms(1)])
  apply assumption
  done

lemma join_idem[simp]: "compatible x y \<Longrightarrow> x \<squnion> (x \<squnion> y) = x \<squnion> y"
  apply (subst join_assoc[symmetric])
  apply (rule compatible_refl)
  apply (erule compatible_above1)
  apply assumption
  apply (subst join_self)
  apply rule
  done

lemma join_bottom[simp]: "x \<squnion> \<bottom> = x" "\<bottom> \<squnion> x = x"
  by (auto intro: is_joinI)

lemma compatible_adm2:
  shows "adm (\<lambda> y. compatible x y)"
proof(rule admI)
  fix Y
  assume c: "chain Y" and "\<forall>i.  compatible x (Y i)"
  hence a: "\<And> i. compatible x (Y i)" by auto
  show "compatible x (\<Squnion> i. Y i)"
  proof(rule compatibleI)
    have c2: "chain (\<lambda>i. x \<squnion> Y i)"
      apply (rule chainI)
      apply (rule join_mono[OF a a below_refl chainE[OF \<open>chain Y\<close>]])
      done
    show "x \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c2] join_above1[OF a])
    show "(\<Squnion> i. Y i) \<sqsubseteq> (\<Squnion> i. x \<squnion> Y i)"
      by (auto intro: admD[OF _ c] below_lub[OF c2 join_above2[OF a]])
    fix a
    assume "x \<sqsubseteq> a" and "(\<Squnion> i. Y i) \<sqsubseteq> a"
    show "(\<Squnion> i. x \<squnion> Y i) \<sqsubseteq> a"
      apply (rule lub_below[OF c2])
      apply (rule join_below[OF a \<open>x \<sqsubseteq> a\<close>])
      apply (rule below_trans[OF is_ub_thelub[OF c] \<open>(\<Squnion> i. Y i) \<sqsubseteq> a\<close>])
      done
  qed
qed

lemma compatible_adm1: "adm (\<lambda> x. compatible x y)"
  by (subst compatible_sym_iff, rule compatible_adm2)

lemma join_cont1:
  assumes "chain Y"
  assumes compat: "\<And> i. compatible (Y i) y"
  shows "(\<Squnion>i. Y i) \<squnion> y = (\<Squnion> i. Y i \<squnion> y)"
proof-
  have c: "chain (\<lambda>i. Y i \<squnion> y)"
    apply (rule chainI)
    apply (rule join_mono[OF compat compat chainE[OF \<open>chain Y\<close>] below_refl])
    done

  show ?thesis
    apply (rule is_joinI)
    apply (rule lub_mono[OF \<open>chain Y\<close> c join_above1[OF compat]])
    apply (rule below_lub[OF c join_above2[OF compat]])
    apply (rule lub_below[OF c])
    apply (rule join_below[OF compat])
    apply (metis lub_below_iff[OF \<open>chain Y\<close>])
    apply assumption
    done
qed

lemma join_cont2:
  assumes "chain Y"
  assumes compat: "\<And> i. compatible x (Y i)"
  shows "x \<squnion> (\<Squnion>i. Y i) = (\<Squnion> i. x \<squnion> Y i)"
proof-
  have c: "chain (\<lambda>i. x \<squnion> Y i)"
    apply (rule chainI)
    apply (rule join_mono[OF compat compat below_refl chainE[OF \<open>chain Y\<close>]])
    done

  show ?thesis
    apply (rule is_joinI)
    apply (rule below_lub[OF c join_above1[OF compat]])
    apply (rule lub_mono[OF \<open>chain Y\<close> c join_above2[OF compat]])
    apply (rule lub_below[OF c])
    apply (rule join_below[OF compat])
    apply assumption
    apply (metis lub_below_iff[OF \<open>chain Y\<close>])
    done
qed

lemma join_cont12:
  assumes "chain Y" and "chain Z"
  assumes compat: "\<And> i j. compatible (Y i) (Z j)"
  shows "(\<Squnion>i. Y i) \<squnion> (\<Squnion>i. Z i) = (\<Squnion> i. Y i  \<squnion> Z i)"
proof-
  have "(\<Squnion>i. Y i) \<squnion> (\<Squnion>i. Z i) = (\<Squnion>i. Y i \<squnion> (\<Squnion>j. Z j))"
    by (rule join_cont1[OF \<open>chain Y\<close> admD[OF compatible_adm2 \<open>chain Z\<close> compat]])
  also have "... = (\<Squnion>i j. Y i \<squnion> Z j)"
    by (subst join_cont2[OF \<open>chain Z\<close> compat], rule)
  also have "... = (\<Squnion>i. Y i \<squnion> Z i)"
    apply (rule diag_lub)
    apply (rule chainI, rule join_mono[OF compat compat chainE[OF \<open>chain Y\<close>] below_refl])
    apply (rule chainI, rule join_mono[OF compat compat below_refl chainE[OF \<open>chain Z\<close>]])
    done
  finally show ?thesis.
qed

context pcpo
begin
  lemma bot_compatible[simp]:
    "compatible x \<bottom>" "compatible \<bottom> x"
    unfolding compatible_def by (metis insert_commute is_lub_bin minimal)+
end

end
