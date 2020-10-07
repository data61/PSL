section "Some Auxiliary Results"

theory Auxiliary imports Main
begin

lemma disjE3: "P \<or> Q \<or> R \<Longrightarrow> (P \<Longrightarrow> S) \<Longrightarrow> (Q \<Longrightarrow> S) \<Longrightarrow> (R \<Longrightarrow> S) \<Longrightarrow> S" by auto

lemma ge_induct[consumes 1, case_names step]:
  fixes i::nat and j::nat and P::"nat \<Rightarrow> bool"
  shows "i \<le> j \<Longrightarrow> (\<And>n. i \<le> n \<Longrightarrow> ((\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n)) \<Longrightarrow> P j"
proof -
  assume a0: "i \<le> j" and a1: "(\<And>n. i \<le> n \<Longrightarrow> ((\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n))"
  have "(\<And>n. \<forall>m<n. i \<le> m \<longrightarrow> P m \<Longrightarrow> i \<le> n \<longrightarrow> P n)"
  proof
    fix n
    assume a2: "\<forall>m<n. i \<le> m \<longrightarrow> P m"
    show "i \<le> n \<Longrightarrow> P n"
    proof -
      assume "i \<le> n"
      with a1 have "(\<forall>m \<ge> i.  m<n \<longrightarrow> P m) \<Longrightarrow> P n" by simp
      moreover from a2 have "\<forall>m \<ge> i.  m<n \<longrightarrow> P m" by simp
      ultimately show "P n" by simp
    qed
  qed
  with nat_less_induct[of "\<lambda>j. i \<le> j \<longrightarrow> P j" j] have "i \<le> j \<longrightarrow> P j" .
  with a0 show ?thesis by simp
qed

lemma my_induct[consumes 1, case_names base step]:
  fixes P::"nat\<Rightarrow>bool"
assumes less: "i \<le> j"
    and base: "P j"
    and step: "\<And>n. i \<le> n \<Longrightarrow> n < j \<Longrightarrow> (\<forall>n'>n. n'\<le>j \<longrightarrow> P n') \<Longrightarrow> P n"
  shows "P i"
proof cases
  assume "j=0"
  thus ?thesis using less base by simp
next
  assume "\<not> j=0"
  have "j - (j - i) \<ge> i \<longrightarrow> P (j - (j - i))"
  proof (rule less_induct[of "\<lambda>n::nat. j-n \<ge> i \<longrightarrow> P (j-n)" "j-i"])
    fix x assume asmp: "\<And>y. y < x \<Longrightarrow> i \<le> j - y \<longrightarrow> P (j - y)"
    show "i \<le> j - x \<longrightarrow> P (j - x)"
    proof cases
      assume "x=0"
      with base show ?thesis by simp
    next
      assume "\<not> x=0"
      with \<open>j \<noteq> 0\<close> have "j - x < j" by simp
      show ?thesis
      proof
        assume "i \<le> j - x"
        moreover have "\<forall>n'>j-x. n'\<le>j \<longrightarrow> P n'"
        proof
          fix n'
          show "n'>j-x \<longrightarrow> n'\<le>j \<longrightarrow> P n'"
          proof (rule HOL.impI[OF HOL.impI])
            assume "j - x < n'" and "n' \<le> j"
            hence "j - n' < x" by simp
            moreover from \<open>i \<le> j - x\<close> \<open>j - x < n'\<close> have "i \<le> n'" using le_less_trans less_imp_le_nat by blast
            with \<open>n' \<le> j\<close> have "i \<le> j - (j - n')" by simp
            ultimately have  "P (j - (j - n'))" using asmp by simp
            moreover from \<open>n' \<le> j\<close> have "j - (j - n') = n'" by simp
            ultimately show "P n'" by simp
          qed
        qed
        ultimately show "P (j - x)" using \<open>j-x<j\<close> step[of "j-x"] by simp
      qed
    qed
  qed
  moreover from less have "j - (j - i) = i" by simp
  ultimately show ?thesis by simp
qed

lemma Greatest_ex_le_nat: assumes "\<exists>k. P k \<and> (\<forall>k'. P k' \<longrightarrow> k' \<le> k)" shows "\<not>(\<exists>n'>Greatest P. P n')"
  by (metis Greatest_equality assms less_le_not_le)

lemma cardEx: assumes "finite A" and "finite B" and "card A > card B" shows "\<exists>x\<in>A. \<not> x\<in>B"
proof cases
  assume "A \<subseteq> B"
  with assms have "card A\<le>card B" using card_mono by blast
  with assms have False by simp
  thus ?thesis by simp
next
  assume "\<not> A \<subseteq> B" 
  thus ?thesis by auto
qed

lemma cardshift: "card {i::nat. i>n \<and> i \<le> n' \<and> p (n'' + i)} = card {i. i>(n + n'') \<and> i \<le> (n' + n'') \<and> p i}"
proof -
  let ?f="\<lambda>i. i+n''"
  have "bij_betw ?f {i::nat. i>n \<and> i \<le> n' \<and> p (n'' + i)} {i. i>(n + n'') \<and> i \<le> (n' + n'') \<and> p i}"
  proof (rule bij_betwI')
    fix x y assume "x \<in> {i. n < i \<and> i \<le> n' \<and> p (n'' + i)}" and "y \<in> {i. n < i \<and> i \<le> n' \<and> p (n'' + i)}"
    show "(x + n'' = y + n'') = (x = y)" by simp
  next
    fix x::nat assume "x \<in> {i. n < i \<and> i \<le> n' \<and> p (n'' + i)}"
    hence "n<x" and "x \<le> n'" and "p(n''+x)" by auto
    moreover have "n''+x=x+n''" by simp
    ultimately have "n + n'' < x + n''" and "x + n'' \<le> n' + n''" and "p (x + n'')" by auto
    thus "x + n'' \<in> {i. n + n'' < i \<and> i \<le> n' + n'' \<and> p i}" by auto
  next
    fix y::nat assume "y \<in> {i. n + n'' < i \<and> i \<le> n' + n'' \<and> p i}"
    hence "n+n''<y" and "y\<le>n'+n''" and "p y" by auto
    then obtain x where "x=y-n''" by simp
    with \<open>n+n''<y\<close> have "y=x+n''" by simp
    moreover from \<open>x=y-n''\<close> \<open>n+n''<y\<close> have "x>n" by simp
    moreover from \<open>x=y-n''\<close> \<open>y\<le>n'+n''\<close> have "x\<le>n'" by simp
    moreover from \<open>y=x+n''\<close> have "y=n''+x" by simp
    with \<open>p y\<close> have "p (n'' + x)" by simp
    ultimately show "\<exists>x\<in>{i. n < i \<and> i \<le> n' \<and> p (n'' + i)}. y = x + n''" by auto
  qed
  thus ?thesis using bij_betw_same_card by auto
qed

end