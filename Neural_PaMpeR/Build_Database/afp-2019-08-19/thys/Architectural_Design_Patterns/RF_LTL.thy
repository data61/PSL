section "Relative Frequency LTL"

theory RF_LTL
  imports Main "HOL-Library.Sublist" Auxiliary DynamicArchitectures.Dynamic_Architecture_Calculus
begin

type_synonym 's seq = "nat \<Rightarrow> 's"

abbreviation "ccard n n' p \<equiv> card {i. i>n \<and> i \<le> n' \<and> p i}"

lemma ccard_same:
  assumes "\<not> p (Suc n')"
  shows "ccard n n' p = ccard n (Suc n') p"
proof -
  have "{i. i > n \<and> i \<le> Suc n' \<and> p i} = {i. i>n \<and> i \<le> n' \<and> p i}"
  proof
    show "{i. n < i \<and> i \<le> Suc n' \<and> p i} \<subseteq> {i. n < i \<and> i \<le> n' \<and> p i}"
    proof
      fix x assume "x \<in> {i. n < i \<and> i \<le> Suc n' \<and> p i}"
      hence "n<x" and "x\<le>Suc n'" and "p x" by auto
      with assms (1) have "x\<noteq>Suc n'" by auto
      with \<open>x\<le>Suc n'\<close> have "x \<le> n'" by simp
      with \<open>n<x\<close> \<open>p x\<close> show "x \<in> {i. n < i \<and> i \<le> n' \<and> p i}" by simp
    qed
  next
    show "{i. n < i \<and> i \<le> n' \<and> p i} \<subseteq> {i. n < i \<and> i \<le> Suc n' \<and> p i}" by auto
  qed
  thus ?thesis by simp
qed

lemma ccard_zero[simp]:
  fixes n::nat
  shows "ccard n n p = 0"
  by auto

lemma ccard_inc:
  assumes "p (Suc n')"
    and "n' \<ge> n"
  shows "ccard n (Suc n') p = Suc (ccard n n' p)"
proof -
  let ?A = "{i. i > n \<and> i \<le> n' \<and> p i}"
  have "finite ?A" by simp
  moreover have "Suc n' \<notin> ?A" by simp
  ultimately have "card (insert (Suc n') ?A) = Suc (card ?A)" using card_insert_disjoint[of ?A] by simp
  moreover have "insert (Suc n') ?A = {i. i>n \<and> i \<le> (Suc n') \<and> p i}"
  proof
    show "insert (Suc n') ?A \<subseteq> {i. n < i \<and> i \<le> Suc n' \<and> p i}"
    proof
      fix x assume "x \<in> insert (Suc n') {i. n < i \<and> i \<le> n' \<and> p i}"
      hence "x=Suc n' \<or> n < x \<and> x \<le> n' \<and> p x" by simp
      thus "x \<in> {i. n < i \<and> i \<le> Suc n' \<and> p i}"
      proof
        assume "x = Suc n'"
        with assms (1) assms (2) show ?thesis by simp
      next
        assume "n < x \<and> x \<le> n' \<and> p x"
        thus ?thesis by simp
      qed
    qed
  next
    show "{i. n < i \<and> i \<le> Suc n' \<and> p i} \<subseteq> insert (Suc n') ?A" by auto
  qed
  ultimately show ?thesis by simp
qed

lemma ccard_mono:
  assumes "n'\<ge>n"
  shows "n''\<ge>n' \<Longrightarrow> ccard n (n''::nat) p \<ge> ccard n n' p"
proof (induction n'' rule: dec_induct)
  case base
  then show ?case ..
next
  case (step n'')
  then show ?case
  proof cases
    assume "p (Suc n'')"
    moreover from step.hyps assms have "n\<le>n''" by simp
    ultimately have "ccard n (Suc n'') p = Suc (ccard n n'' p)" using ccard_inc[of p n'' n] by simp
    also have "\<dots> \<ge> ccard n n' p" using step.IH by simp
    finally show ?case .
  next
    assume "\<not> p (Suc n'')"
    moreover from step.hyps assms have "n\<le>n''" by simp
    ultimately have "ccard n (Suc n'') p = ccard n n'' p" using ccard_same[of p n'' n] by simp
    also have "\<dots> \<ge> ccard n n' p" using step.IH by simp
    finally show ?case by simp
  qed
qed

lemma ccard_ub[simp]:
  "ccard n n' p \<le> Suc n' - n"
proof -
  have "{i. i>n \<and> i \<le> n' \<and> p i} \<subseteq> {i. i\<ge>n \<and> i \<le> n'}" by auto
  hence "ccard n n' p \<le> card {i. i\<ge>n \<and> i \<le> n'}" by (simp add: card_mono)
  moreover have "{i. i\<ge>n \<and> i \<le> n'} = {n..n'}" by auto
  hence "card {i. i\<ge>n \<and> i \<le> n'} = Suc n' - n" by simp
  ultimately show ?thesis by simp
qed

lemma ccard_sum:
  fixes n::nat
  assumes "n'\<ge>n''"
    and "n''\<ge>n"
  shows "ccard n n' P = ccard n n'' P + ccard n'' n' P"
proof -
  have "ccard n n' P = card {i. i>n \<and> i \<le> n' \<and> P i}" by simp
  moreover have "{i. i>n \<and> i \<le> n' \<and> P i} =
    {i. i>n \<and> i \<le> n'' \<and> P i} \<union> {i. i>n'' \<and> i \<le> n' \<and> P i}" (is "?LHS = ?RHS")
  proof
    show "?LHS \<subseteq> ?RHS" by auto
  next
    show "?RHS \<subseteq> ?LHS"
    proof
      fix x
      assume "x\<in>?RHS"
      hence "x>n \<and> x \<le> n'' \<and> P x \<or> x>n'' \<and> x \<le> n' \<and> P x" by auto
      thus "x\<in>?LHS"
      proof
        assume "n < x \<and> x \<le> n'' \<and> P x"
        with assms show ?thesis by simp
      next
        assume "n'' < x \<and> x \<le> n' \<and> P x"
        with assms show ?thesis by simp
      qed
    qed
  qed
  hence "card ?LHS = card ?RHS" by simp
  ultimately have "ccard n n' P = card ?RHS" by simp
  moreover have "card ?RHS = card {i. i>n \<and> i \<le> n'' \<and> P i} + card {i. i>n'' \<and> i \<le> n' \<and> P i}"
  proof (rule card_Un_disjoint)
    show "finite {i. n < i \<and> i \<le> n'' \<and> P i}" by simp
    show "finite {i. n'' < i \<and> i \<le> n' \<and> P i}" by simp
    show "{i. n < i \<and> i \<le> n'' \<and> P i} \<inter> {i. n'' < i \<and> i \<le> n' \<and> P i} = {}" by auto
  qed
  moreover have "ccard n n'' P = card {i. i>n \<and> i \<le> n'' \<and> P i}" by simp
  moreover have "ccard n'' n' P= card {i. i>n'' \<and> i \<le> n' \<and> P i}" by simp
  ultimately show ?thesis by simp
qed

lemma ccard_ex:
  fixes n::nat
  shows "c\<ge>1 \<Longrightarrow> c < ccard n n'' P \<Longrightarrow> \<exists>n'<n''. n'>n \<and> ccard n n' P = c"
proof (induction c rule: dec_induct)
  let ?l = "LEAST i::nat. n < i \<and> i < n'' \<and> P i"
  case base
  moreover have "ccard n n'' P \<le> Suc (card {i. n < i \<and> i < n'' \<and> P i})"
  proof -
    from \<open>ccard n n'' P > 1\<close> have "n''>n" using less_le_trans by force
    then obtain n' where "Suc n' = n''" and "Suc n' \<ge> n" by (metis lessE less_imp_le_nat)
    moreover have "{i. n < i \<and> i < Suc n' \<and> P i} = {i. n < i \<and> i \<le> n' \<and> P i}" by auto
    hence "card {i. n < i \<and> i < Suc n' \<and> P i} = card {i. n < i \<and> i \<le> n' \<and> P i}" by simp
    moreover have "card {i. n < i \<and> i \<le> Suc n' \<and> P i} \<le> Suc (card {i. n < i \<and> i \<le> n' \<and> P i})"
    proof cases
      assume "P (Suc n')"
      moreover from \<open>n''>n\<close> \<open>Suc n'=n''\<close> have "n'\<ge>n" by simp
      ultimately show ?thesis using ccard_inc[of P n' n] by simp
    next
      assume "\<not> P (Suc n')"
      moreover from \<open>n''>n\<close> \<open>Suc n'=n''\<close> have "n'\<ge>n" by simp
      ultimately show ?thesis using ccard_same[of P n' n] by simp
    qed
    ultimately show ?thesis by simp
  qed
  ultimately have "card {i. n < i \<and> i < n'' \<and> P i} \<ge> 1" by simp
  hence "{i. n < i \<and> i < n'' \<and> P i} \<noteq> {}" by fastforce
  hence "\<exists>i. n < i \<and> i < n'' \<and> P i" by auto
  hence "?l>n" and "?l<n''" and "P ?l" using LeastI_ex[of "\<lambda>i::nat. n < i \<and> i < n'' \<and> P i"] by auto
  moreover have "{i. n < i \<and> i \<le> ?l \<and> P i} = {?l}"
  proof
    show "{i. n < i \<and> i \<le> ?l \<and> P i} \<subseteq> {?l}"
    proof
      fix i
      assume "i\<in>{i. n < i \<and> i \<le> ?l \<and> P i}"
      hence "n < i" and "i \<le> ?l" and "P i" by auto
      with \<open>\<exists>i. n < i \<and> i < n'' \<and> P i\<close> have "i=?l"
        using Least_le[of "\<lambda>i. n < i \<and> i < n'' \<and> P i"] by (meson antisym le_less_trans)
      thus "i\<in>{?l}" by simp
    qed
  next
    show "{?l} \<subseteq> {i. n < i \<and> i \<le> ?l \<and> P i}"
    proof
      fix i
      assume "i\<in>{?l}"
      hence "i=?l" by simp
      with \<open>?l>n\<close> \<open>?l<n''\<close> \<open>P ?l\<close> show "i\<in>{i. n < i \<and> i \<le> ?l \<and> P i}" by simp
    qed
  qed
  hence "ccard n ?l P = 1" by simp
  ultimately show ?case by auto
next
  case (step c)
  moreover from step.prems have "Suc c<ccard n n'' P" by simp
  ultimately obtain n' where "n'<n''" and "n < n'" and "ccard n n' P = c" by auto
  hence "ccard n n'' P = ccard n n' P + ccard n' n'' P" using ccard_sum[of n' n'' n] by simp
  with \<open>Suc c<ccard n n'' P\<close> \<open>ccard n n' P = c\<close> have "ccard n' n'' P>1" by simp
  moreover have "ccard n' n'' P \<le> Suc (card {i. n' < i \<and> i < n'' \<and> P i})"
  proof -
    from \<open>ccard n' n'' P > 1\<close> have "n''>n'" using less_le_trans by force
    then obtain n''' where "Suc n''' = n''" and "Suc n''' \<ge> n'" by (metis lessE less_imp_le_nat)
    moreover have "{i. n' < i \<and> i < Suc n''' \<and> P i} = {i. n' < i \<and> i \<le> n''' \<and> P i}" by auto
    hence "card {i. n' < i \<and> i < Suc n''' \<and> P i} = card {i. n' < i \<and> i \<le> n''' \<and> P i}" by simp
    moreover have "card {i. n' < i \<and> i \<le> Suc n''' \<and> P i} \<le> Suc (card {i. n' < i \<and> i \<le> n''' \<and> P i})"
    proof cases
      assume "P (Suc n''')"
      moreover from \<open>n''>n'\<close> \<open>Suc n'''=n''\<close> have "n'''\<ge>n'" by simp
      ultimately show ?thesis using ccard_inc[of P n''' n'] by simp
    next
      assume "\<not> P (Suc n''')"
      moreover from \<open>n''>n'\<close> \<open>Suc n'''=n''\<close> have "n'''\<ge>n'" by simp
      ultimately show ?thesis using ccard_same[of P n''' n'] by simp
    qed
    ultimately show ?thesis by simp
  qed
  ultimately have "card {i. n' < i \<and> i < n'' \<and> P i} \<ge> 1" by simp
  hence "{i. n' < i \<and> i < n'' \<and> P i} \<noteq> {}" by fastforce
  hence "\<exists>i. n' < i \<and> i < n'' \<and> P i" by auto
  let ?l = "LEAST i::nat. n' < i \<and> i < n'' \<and> P i"
  from \<open>\<exists>i. n' < i \<and> i < n'' \<and> P i\<close> have "n' < ?l"
    using LeastI_ex[of "\<lambda>i::nat. n' < i \<and> i < n'' \<and> P i"] by auto
  with \<open>n < n'\<close> have "ccard n ?l P = ccard n n' P + ccard n' ?l P" using ccard_sum[of n' ?l n] by simp
  moreover have "{i. n' < i \<and> i \<le> ?l \<and> P i} = {?l}"
  proof
    show "{i. n' < i \<and> i \<le> ?l \<and> P i} \<subseteq> {?l}"
    proof
      fix i
      assume "i\<in>{i. n' < i \<and> i \<le> ?l \<and> P i}"
      hence "n' < i" and "i \<le> ?l" and "P i" by auto
      with \<open>\<exists>i. n' < i \<and> i < n'' \<and> P i\<close> have "i=?l"
        using Least_le[of "\<lambda>i. n' < i \<and> i < n'' \<and> P i"] by (meson antisym le_less_trans)
      thus "i\<in>{?l}" by simp
    qed
  next
    show "{?l} \<subseteq> {i. n' < i \<and> i \<le> ?l \<and> P i}"
    proof
      fix i
      assume "i\<in>{?l}"
      hence "i=?l" by simp
      moreover from \<open>\<exists>i. n' < i \<and> i < n'' \<and> P i\<close> have "?l<n''" and "P ?l"
        using LeastI_ex[of "\<lambda>i. n' < i \<and> i < n'' \<and> P i"] by auto
      ultimately show "i\<in>{i. n' < i \<and> i \<le> ?l \<and> P i}" using \<open>?l>n'\<close> by simp
    qed
  qed
  hence "ccard n' ?l P = 1" by simp
  ultimately have "card {i. n < i \<and> i \<le> ?l \<and> P i} = Suc c" using \<open>ccard n n' P = c\<close> by simp
  moreover from \<open>\<exists>i. n' < i \<and> i < n'' \<and> P i\<close> have "n' < ?l" and "?l < n''" and "P ?l"
    using LeastI_ex[of "\<lambda>i::nat. n' < i \<and> i < n'' \<and> P i"] by auto
  with \<open>n < n'\<close> have "n<?l" and "?l<n''" by auto
  ultimately show ?case by auto
qed

lemma ccard_freq:
  assumes "(n'::nat)\<ge>n"
    and "ccard n n' P > ccard n n' Q + cnf"
  shows "\<exists>n' n''. ccard n' n'' P > cnf \<and> ccard n' n'' Q \<le> cnf"
proof cases
  assume "cnf = 0"
  with assms(2) have "ccard n n' P > ccard n n' Q" by simp
  hence "card {i. n < i \<and> i \<le> n' \<and> P i}>card {i. n < i \<and> i \<le> n' \<and> Q i}" (is "card ?LHS>card ?RHS")
    by simp
  then obtain i where "i\<in>?LHS" and "\<not> i \<in> ?RHS" and "i>0" using cardEx[of ?LHS ?RHS] by auto
  hence "P i" and "\<not> Q i" by auto
  with \<open>i>0\<close> obtain n'' where "P (Suc n'')" and "\<not>Q (Suc n'')" using gr0_implies_Suc by auto
  hence "ccard n'' (Suc n'') P = 1" using ccard_inc by auto
  with \<open>cnf = 0\<close> have "ccard n'' (Suc n'') P > cnf" by simp
  moreover from \<open>\<not>Q (Suc n'')\<close> have "ccard n'' (Suc n'') Q = 0" using ccard_same[of Q n'' n''] by auto
  with \<open>cnf = 0\<close> have "ccard n'' (Suc n'') Q \<le> cnf" by simp
  ultimately show ?thesis by auto
next
  assume "\<not> cnf = 0"
  show ?thesis
  proof (rule ccontr)
    assume "\<not> (\<exists>n' n''. ccard n' n'' P > cnf \<and> ccard n' n'' Q \<le> cnf)"
    hence hyp: "\<forall>n' n''. ccard n' n'' Q \<le> cnf \<longrightarrow> ccard n' n'' P \<le> cnf"
      using leI less_imp_le_nat by blast
    show False
    proof cases
      assume "ccard n n' Q \<le> cnf"
      with hyp have "ccard n n' P \<le> cnf" by simp
      with assms show False by simp
    next
      let ?gcond="\<lambda>n''. n''\<ge>n \<and> n''\<le>n' \<and> (\<exists>x\<ge>1. ccard n n'' Q = x * cnf)"
      let ?g= "GREATEST n''. ?gcond n''"
      assume "\<not> ccard n n' Q \<le> cnf"
      hence "ccard n n' Q > cnf" by simp
      hence "\<exists>n''. ?gcond n''"
      proof -
        from \<open>ccard n n' Q > cnf\<close> \<open>\<not>cnf=0\<close> obtain n'' where "n''>n" and "n''\<le>n'" and "ccard n n'' Q = cnf"
          using ccard_ex[of cnf n n' Q ] by auto
        moreover from \<open>ccard n n'' Q = cnf\<close> have "\<exists>x\<ge>1. ccard n n'' Q = x * cnf" by auto
        ultimately show ?thesis using less_imp_le_nat by blast
      qed
      moreover have "\<forall>n''>n'. \<not> ?gcond n''" by simp
      ultimately have gex: "\<exists>n''. ?gcond n'' \<and> (\<forall>n'''. ?gcond n''' \<longrightarrow> n'''\<le>n'')"
        using boundedGreatest[of ?gcond _ n'] by blast
      hence "\<exists>x\<ge>1. ccard n ?g Q = x * cnf" and "?g \<ge> n" using GreatestI_ex_nat[of ?gcond] by auto
      moreover {fix n''
      have "n''\<ge>n \<Longrightarrow> \<exists>x\<ge>1. ccard n n'' Q = x * cnf \<Longrightarrow> ccard n n'' P \<le> ccard n n'' Q"
      proof (induction n'' rule: ge_induct)
        case (step n')
        from step.prems obtain x where "x\<ge>1" and cas: "ccard n n' Q = x * cnf" by auto
        then show ?case
        proof cases
          assume "x=1"
          with cas have "ccard n n' Q = cnf" by simp
          with hyp have "ccard n n' P \<le> cnf" by simp
          with \<open>ccard n n' Q = cnf\<close> show ?thesis by simp
        next
          assume "\<not>x=1"
          with \<open>x\<ge>1\<close> have "x>1" by simp
          hence "x-1 \<ge> 1" by simp
          moreover from \<open>cnf\<noteq>0\<close> \<open>x-1 \<ge> 1\<close> have "(x-1) * cnf < x * cnf \<and> (x - 1) * cnf \<noteq> 0" by auto
          with \<open>x-1 \<ge> 1\<close> \<open>cnf\<noteq>0\<close>\<open>ccard n n' Q = x * cnf\<close> obtain n''
            where "n''>n" and "n''<n'" and "ccard n n'' Q = (x-1) * cnf"
            using ccard_ex[of "(x-1)*cnf" n n' Q ] by auto
          ultimately have "\<exists>x\<ge>1. ccard n n'' Q = x * cnf" and "n''\<ge>n" by auto
          with \<open>n''\<ge>n\<close> \<open>n''<n'\<close> have "ccard n n'' P \<le> ccard n n'' Q" using step.IH by simp
          moreover have "ccard n'' n' Q = cnf"
          proof -
            from \<open>x-1 \<ge> 1\<close> have "x*cnf = ((x-1) * cnf) + cnf"
              using semiring_normalization_rules(2)[of "(x - 1)" cnf] by simp
            with \<open>ccard n n'' Q = (x-1) * cnf\<close> \<open>ccard n n' Q = x * cnf\<close>
            have "ccard n n' Q = ccard n n'' Q + cnf" by simp
            moreover from \<open>n''\<ge>n\<close> \<open>n''<n'\<close> have "ccard n n' Q = ccard n n'' Q + ccard n'' n' Q"
              using ccard_sum[of n'' n' n] by simp
            ultimately show ?thesis by simp
          qed
          moreover from \<open>ccard n'' n' Q = cnf\<close> have "ccard n'' n' P \<le> cnf" using hyp by simp
          ultimately show ?thesis using \<open>n''\<ge>n\<close> \<open>n''<n'\<close> ccard_sum[of n'' n' n] by simp
        qed
      qed } note geq = this
      ultimately have "ccard n ?g P \<le> ccard n ?g Q" by simp
      moreover have "ccard ?g n' P \<le> cnf"
      proof (rule ccontr)
        assume "\<not> ccard ?g n' P \<le> cnf"
        hence "ccard ?g n' P > cnf" by simp
        have "ccard ?g n' Q > cnf"
        proof (rule ccontr)
          assume "\<not>ccard ?g n' Q > cnf"
          hence "ccard ?g n' Q \<le> cnf" by simp
          with \<open>ccard ?g n' P > cnf\<close> show False
            using \<open>\<not> (\<exists>n' n''. ccard n' n'' P > cnf \<and> ccard n' n'' Q \<le> cnf)\<close> by simp
        qed
        with \<open>\<not> cnf=0\<close> obtain n'' where "n''>?g" and "n''<n'" and "ccard ?g n'' Q = cnf"
          using ccard_ex[of cnf ?g n' Q] by auto
        moreover have "\<exists>x\<ge>1. ccard n n'' Q = x * cnf"
        proof -
          from \<open>\<exists>x\<ge>1. ccard n ?g Q = x * cnf\<close> obtain x where "x\<ge>1" and "ccard n ?g Q = x * cnf" by auto
          from \<open>n''>?g\<close> \<open>?g\<ge>n\<close> have "ccard n n'' Q = ccard n ?g Q + ccard ?g n'' Q"
            using ccard_sum[of ?g n'' n Q] by simp
          with \<open>ccard n ?g Q = x * cnf\<close> have "ccard n n'' Q = x * cnf + ccard ?g n'' Q" by simp
          with \<open>ccard ?g n'' Q = cnf\<close> have "ccard n n'' Q = Suc x * cnf" by simp
          thus ?thesis by auto
        qed
        moreover from \<open>n''>?g\<close> \<open>?g\<ge>n\<close> have "n''\<ge>n" by simp
        ultimately have "\<exists>n''>?g. ?gcond n''" by auto
        moreover from gex have "\<forall>n'''. ?gcond n''' \<longrightarrow> n'''\<le>?g" using Greatest_le_nat[of ?gcond] by auto
        ultimately show False by auto
      qed
      moreover from gex have "n'\<ge>?g" using GreatestI_ex_nat[of ?gcond] by auto
      ultimately have "ccard n n' P\<le>ccard n n' Q + cnf" using ccard_sum[of ?g n' n] using \<open>?g \<ge> n\<close> by simp
      with assms show False by simp
    qed
  qed
qed

locale honest =
  fixes bc:: "('a list) seq"
    and n::nat
  assumes growth: "n'\<noteq>0 \<Longrightarrow> n'\<le>n \<Longrightarrow> bc n' = bc (n'-1) \<or> (\<exists>b. bc n' = bc (n' - 1) @ b)"
begin
end

locale dishonest =
  fixes bc:: "('a list) seq"
    and mining::"bool seq"
  assumes growth: "\<And>n::nat. prefix (bc (Suc n)) (bc n) \<or> (\<exists>b::'a. bc (Suc n) = bc n @ [b]) \<and> mining (Suc n)"
begin

lemma prefix_save:
  assumes "prefix sbc (bc n')"
    and "\<forall>n'''>n'. n'''\<le>n'' \<longrightarrow> length (bc n''') \<ge> length sbc"
  shows "n''\<ge>n' \<Longrightarrow> prefix sbc (bc n'')"
proof (induction n'' rule: dec_induct)
  case base
  with assms(1) show ?case by simp
next
  case (step n)
  from growth[of n] show ?case
  proof
    assume "prefix (bc (Suc n)) (bc n)"
    moreover from step.hyps have "length (bc (Suc n)) \<ge> length sbc" using assms(2) by simp
    ultimately show ?thesis using step.IH using prefix_length_prefix by auto
  next
    assume "(\<exists>b. bc (Suc n) = bc n @ [b]) \<and> mining (Suc n)"
    with step.IH show ?thesis by auto
  qed
qed

theorem prefix_length:
  assumes "prefix sbc (bc n')" and "\<not> prefix sbc (bc n'')" and "n'\<le>n''"
  shows "\<exists>n'''>n'. n'''\<le>n'' \<and> length (bc n''') < length sbc"
proof (rule ccontr)
  assume "\<not> (\<exists>n'''>n'. n'''\<le>n'' \<and> length (bc n''') < length sbc)"
  hence "\<forall>n'''>n'. n'''\<le>n'' \<longrightarrow> length (bc n''') \<ge> length sbc" by auto
  with assms have "prefix sbc (bc n'')" using prefix_save[of sbc n' n''] by simp
  with assms (2) show False by simp
qed

theorem grow_mining:
  assumes "length (bc n) < length (bc (Suc n))"
  shows "mining (Suc n)"
  using assms growth leD prefix_length_le by blast

lemma length_suc_length:
  "length (bc (Suc n)) \<le> Suc (length (bc n))"
  by (metis eq_iff growth le_SucI length_append_singleton prefix_length_le)

end

locale dishonest_growth =
  fixes bc:: "nat seq"
    and mining:: "nat \<Rightarrow> bool"
  assumes as1: "\<And>n::nat. bc (Suc n) \<le> Suc (bc n)"
    and as2: "\<And>n::nat. bc (Suc n) > bc n \<Longrightarrow> mining (Suc n)"
begin

end

sublocale dishonest \<subseteq> dishonest_growth "\<lambda>n. length (bc n)" using grow_mining length_suc_length by unfold_locales auto

context dishonest_growth
begin
  theorem ccard_diff_lgth:
    "n'\<ge>n \<Longrightarrow> ccard n n' (\<lambda>n. mining n) \<ge> (bc n' - bc n)"
  proof (induction n' rule: dec_induct)
    case base
    then show ?case by simp
    next
    case (step n')
    from as1 have "bc (Suc n') < Suc (bc n') \<or> bc (Suc n') = Suc (bc n')"
      using le_neq_implies_less by blast
    then show ?case
    proof
      assume "bc (Suc n') < Suc (bc n')"
      hence "bc (Suc n') - bc n \<le> bc n' - bc n" by simp
      moreover from step.hyps have "ccard n (Suc n') (\<lambda>n. mining n) \<ge> ccard n n' (\<lambda>n. mining n)"
        using ccard_mono[of n n' "Suc n'"] by simp
      ultimately show ?thesis using step.IH by simp
    next
      assume "bc (Suc n') = Suc (bc n')"
      hence "bc (Suc n') - bc n \<le> Suc (bc n' - bc n)" by simp
      moreover from \<open>bc (Suc n') = Suc (bc n')\<close> have "mining (Suc n')" using as2 by simp
      with step.hyps have "ccard n (Suc n') (\<lambda>n. mining n) \<ge> Suc (ccard n n' (\<lambda>n. mining n))"
        using ccard_inc by simp
      ultimately show ?thesis using step.IH by simp
    qed
  qed
end

locale honest_growth =
  fixes bc:: "nat seq"
    and mining:: "nat \<Rightarrow> bool"
    and init:: nat
  assumes as1: "\<And>n::nat. bc (Suc n) \<ge> bc n"
    and as2: "\<And>n::nat. mining (Suc n) \<Longrightarrow> bc (Suc n) > bc n"
begin
  lemma grow_mono: "n'\<ge>n\<Longrightarrow>bc n'\<ge>bc n"
  proof (induction n' rule: dec_induct)
    case base
    then show ?case by simp
  next
    case (step n')
    then show ?case using as1[of n'] by simp
  qed

  theorem ccard_diff_lgth:
    shows "n'\<ge>n \<Longrightarrow> bc n' - bc n \<ge> ccard n n' (\<lambda>n. mining n)"
  proof (induction n' rule: dec_induct)
    case base
    then show ?case by simp
  next
    case (step n')
    then show ?case
    proof cases
      assume "mining (Suc n')"
      with as2 have "bc (Suc n') > bc n'" by simp
      moreover from step.hyps have "bc n'\<ge>bc n" using grow_mono by simp
      ultimately have "bc (Suc n') - bc n > bc n' - bc n" by simp
      moreover from as1 have "bc (Suc n') - bc n \<ge> bc n' - bc n" by (simp add: diff_le_mono)
      moreover from \<open>mining (Suc n')\<close> step.hyps
        have "ccard n (Suc n') (\<lambda>n. mining n) \<le> Suc (ccard n n' (\<lambda>n. mining n))"
        using ccard_inc by simp
      ultimately show ?thesis using step.IH by simp
    next
      assume "\<not> mining (Suc n')"
      hence "ccard n (Suc n') (\<lambda>n. mining n) \<le> (ccard n n' (\<lambda>n. mining n))" using ccard_same by simp
      moreover from as1 have "bc (Suc n') - bc n \<ge> bc n' - bc n" by (simp add: diff_le_mono)
      ultimately show ?thesis using step.IH by simp
    qed
  qed
end

locale bounded_growth = hg: honest_growth hbc hmining + dg: dishonest_growth dbc dmining
    for hbc:: "nat seq"
    and dbc:: "nat seq"
    and hmining:: "nat \<Rightarrow> bool"
    and dmining:: "nat \<Rightarrow> bool"
    and sbc::nat
    and cnf::nat +
  assumes fair: "\<And>n n'. ccard n n' (\<lambda>n. dmining n) > cnf \<Longrightarrow> ccard n n' (\<lambda>n. hmining n) > cnf"
    and a2: "hbc 0 \<ge> sbc+cnf"
    and a3: "dbc 0 < sbc"
begin

theorem hn_upper_bound: shows "dbc n < hbc n"
proof (rule ccontr)
  assume "\<not> dbc n < hbc n"
  hence "dbc n \<ge> hbc n" by simp
  moreover from a2 a3 have "hbc 0 > dbc 0 + cnf" by simp
  moreover have "hbc n\<ge>hbc 0" using hg.grow_mono by simp
  ultimately have "dbc n - dbc 0 > hbc n - hbc 0 + cnf" by simp
  moreover have "ccard 0 n (\<lambda>n. hmining n) \<le> hbc n - hbc 0" using hg.ccard_diff_lgth by simp
  moreover have "dbc n - dbc 0 \<le> ccard 0 n (\<lambda>n. dmining n)" using dg.ccard_diff_lgth by simp
  ultimately have "ccard 0 n (\<lambda>n. dmining n) > ccard 0 n (\<lambda>n. hmining n) + cnf" by simp
  hence "\<exists>n' n''. ccard n' n'' (\<lambda>n. dmining n) > cnf \<and> ccard n' n'' (\<lambda>n. hmining n) \<le> cnf"
    using ccard_freq by blast
  with fair show False using leD by blast
qed

end

end