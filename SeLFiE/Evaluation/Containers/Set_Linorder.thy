(*  Title:      Containers/Set_Linorder.thy
    Author:     Andreas Lochbihler, KIT *)

theory Set_Linorder 
imports
  Containers_Auxiliary
  Lexicographic_Order
  Extend_Partial_Order
  "HOL-Library.Cardinality"
begin

section \<open>An executable linear order on sets\<close>

subsection \<open>Definition of the linear order\<close>

subsubsection \<open>Extending finite and cofinite sets\<close>

text \<open>
  Partition sets into finite and cofinite sets and distribute the rest arbitrarily such that
  complement switches between the two.
\<close>

consts infinite_complement_partition :: "'a set set"

specification (infinite_complement_partition)
  finite_complement_partition: "finite (A :: 'a set) \<Longrightarrow> A \<in> infinite_complement_partition"
  complement_partition: "\<not> finite (UNIV :: 'a set)
    \<Longrightarrow> (A :: 'a set) \<in> infinite_complement_partition \<longleftrightarrow> - A \<notin> infinite_complement_partition"
proof(cases "finite (UNIV :: 'a set)")
  case False
  define Field_r where "Field_r = {\<P> :: 'a set set. (\<forall>C \<in> \<P>. - C \<notin> \<P>) \<and> (\<forall>A. finite A \<longrightarrow> A \<in> \<P>)}"
  define r where "r = {(\<P>1, \<P>2). \<P>1 \<subseteq> \<P>2 \<and> \<P>1 \<in> Field_r \<and> \<P>2 \<in> Field_r}"
  have in_Field_r [simp]: "\<And>\<P>. \<P> \<in> Field_r \<longleftrightarrow> (\<forall>C \<in> \<P>. - C \<notin> \<P>) \<and> (\<forall>A. finite A \<longrightarrow> A \<in> \<P>)"
    unfolding Field_r_def by simp
  have in_r [simp]: "\<And>\<P>1 \<P>2. (\<P>1, \<P>2) \<in> r \<longleftrightarrow> \<P>1 \<subseteq> \<P>2 \<and> \<P>1 \<in> Field_r \<and> \<P>2 \<in> Field_r"
    unfolding r_def by simp
  have Field_r [simp]: "Field r = Field_r" by(auto simp add: Field_def Field_r_def)
  
  have "Partial_order r"
    by(auto simp add: Field_def r_def partial_order_on_def preorder_on_def intro!: refl_onI transI antisymI)
  moreover have "\<exists>\<B> \<in> Field r. \<forall>\<A> \<in> \<CC>. (\<A>, \<B>) \<in> r" if \<CC>: "\<CC> \<in> Chains r" for \<CC>
  proof -
    let ?\<B> = "\<Union>\<CC> \<union> {A. finite A}"
    have *: "?\<B> \<in> Field r" using False \<CC>
      by clarsimp(safe, drule (2) ChainsD, auto 4 4 dest: Chains_Field)
    hence "\<And>\<A>. \<A> \<in> \<CC> \<Longrightarrow> (\<A>, ?\<B>) \<in> r"
      using \<CC> by(auto simp del: in_Field_r dest: Chains_Field)
    with * show "\<exists>\<B> \<in> Field r. \<forall>\<A> \<in> \<CC>. (\<A>, \<B>) \<in> r" by blast
  qed
  ultimately have "\<exists>\<P> \<in> Field r. \<forall>\<A> \<in> Field r. (\<P>, \<A>) \<in> r \<longrightarrow> \<A> = \<P>"
    by(rule Zorns_po_lemma)
  then obtain \<P> where \<P>: "\<P> \<in> Field r" 
    and max: "\<And>\<A>. \<lbrakk> \<A> \<in> Field r; (\<P>, \<A>) \<in> r \<rbrakk> \<Longrightarrow> \<A> = \<P>" by blast
  have "\<forall>A. finite A \<longrightarrow> A \<in> \<P>" using \<P> by simp
  moreover {
    fix C
    have "C \<in> \<P> \<or> - C \<in> \<P>"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence C: "C \<notin> \<P>" "- C \<notin> \<P>" by simp_all
      let ?\<A> = "insert C \<P>"
      have *: "?\<A> \<in> Field r" using C \<P> by auto
      hence "(\<P>, ?\<A>) \<in> r" using \<P> by auto
      with * have "?\<A> = \<P>" by(rule max)
      thus False using C by auto
    qed
    hence "C \<in> \<P> \<longleftrightarrow> - C \<notin> \<P>" using \<P> by auto }
  ultimately have "\<exists>\<P> :: 'a set set. (\<forall>A. finite A \<longrightarrow> A \<in> \<P>) \<and> (\<forall>C. C \<in> \<P> \<longleftrightarrow> - C \<notin> \<P>)"
    by blast
  thus ?thesis by metis
qed auto

lemma not_in_complement_partition:
  "\<not> finite (UNIV :: 'a set)
  \<Longrightarrow> (A :: 'a set) \<notin> infinite_complement_partition \<longleftrightarrow> - A \<in> infinite_complement_partition"
by(metis complement_partition)

lemma not_in_complement_partition_False:
  "\<lbrakk> (A :: 'a set) \<in> infinite_complement_partition; \<not> finite (UNIV :: 'a set) \<rbrakk> 
  \<Longrightarrow> - A \<in> infinite_complement_partition = False"
by(simp add: not_in_complement_partition)

lemma infinite_complement_partition_finite [simp]:
  "finite (UNIV :: 'a set) \<Longrightarrow> infinite_complement_partition = (UNIV :: 'a set set)"
by(auto intro: finite_subset finite_complement_partition)

lemma Compl_eq_empty_iff: "- A = {} \<longleftrightarrow> A = UNIV"
by auto

subsubsection \<open>A lexicographic-style order on finite subsets\<close>

context ord begin

definition set_less_aux :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubset>''" 50)
where "A \<sqsubset>' B \<longleftrightarrow> finite A \<and> finite B \<and> (\<exists>y \<in> B - A. \<forall>z \<in> (A - B) \<union> (B - A). y \<le> z \<and> (z \<le> y \<longrightarrow> y = z))"

definition set_less_eq_aux :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>''" 50)
where "A \<sqsubseteq>' B \<longleftrightarrow> A \<in> infinite_complement_partition \<and> A = B \<or> A \<sqsubset>' B"

lemma set_less_aux_irrefl [iff]: "\<not> A \<sqsubset>' A"
by(auto simp add: set_less_aux_def)

lemma set_less_eq_aux_refl [iff]: "A \<sqsubseteq>' A \<longleftrightarrow> A \<in> infinite_complement_partition"
by(simp add: set_less_eq_aux_def)

lemma set_less_aux_empty [simp]: "\<not> A \<sqsubset>' {}"
by(auto simp add: set_less_aux_def intro: finite_subset finite_complement_partition)

lemma set_less_eq_aux_empty [simp]: "A \<sqsubseteq>' {} \<longleftrightarrow> A = {}"
by(auto simp add: set_less_eq_aux_def finite_complement_partition)

lemma set_less_aux_antisym: "\<lbrakk> A \<sqsubset>' B; B \<sqsubset>' A \<rbrakk> \<Longrightarrow> False"
by(auto simp add: set_less_aux_def split: if_split_asm)

lemma set_less_aux_conv_set_less_eq_aux:
  "A \<sqsubset>' B \<longleftrightarrow> A \<sqsubseteq>' B \<and> \<not> B \<sqsubseteq>' A"
by(auto simp add: set_less_eq_aux_def dest: set_less_aux_antisym)

lemma set_less_eq_aux_antisym: "\<lbrakk> A \<sqsubseteq>' B; B \<sqsubseteq>' A \<rbrakk> \<Longrightarrow> A = B"
by(auto simp add: set_less_eq_aux_def dest: set_less_aux_antisym)

lemma set_less_aux_finiteD: "A \<sqsubset>' B \<Longrightarrow> finite A \<and> B \<in> infinite_complement_partition"
by(auto simp add: set_less_aux_def finite_complement_partition)

lemma set_less_eq_aux_infinite_complement_partitionD:
  "A \<sqsubseteq>' B \<Longrightarrow> A \<in> infinite_complement_partition \<and> B \<in> infinite_complement_partition"
by(auto simp add: set_less_eq_aux_def dest: set_less_aux_finiteD intro: finite_complement_partition)

lemma Compl_set_less_aux_Compl:
  "finite (UNIV :: 'a set) \<Longrightarrow> - A \<sqsubset>' - B \<longleftrightarrow> B \<sqsubset>' A"
by(auto simp add: set_less_aux_def finite_subset[OF subset_UNIV])

lemma Compl_set_less_eq_aux_Compl: 
  "finite (UNIV :: 'a set) \<Longrightarrow> - A \<sqsubseteq>' - B \<longleftrightarrow> B \<sqsubseteq>' A"
by(auto simp add: set_less_eq_aux_def Compl_set_less_aux_Compl)

lemma set_less_aux_insert_same:
  "x \<in> A \<longleftrightarrow> x \<in> B \<Longrightarrow> insert x A \<sqsubset>' insert x B \<longleftrightarrow> A \<sqsubset>' B"
by(auto simp add: set_less_aux_def)

lemma set_less_eq_aux_insert_same:
  "\<lbrakk> A \<in> infinite_complement_partition; insert x B \<in> infinite_complement_partition;
    x \<in> A \<longleftrightarrow> x \<in> B \<rbrakk>
  \<Longrightarrow> insert x A \<sqsubseteq>' insert x B \<longleftrightarrow> A \<sqsubseteq>' B"
by(auto simp add: set_less_eq_aux_def set_less_aux_insert_same)

end

context order begin

lemma set_less_aux_singleton_iff: "A \<sqsubset>' {x} \<longleftrightarrow> finite A \<and> (\<forall>a\<in>A. x < a)"
by(auto simp add: set_less_aux_def less_le Bex_def)

end

context linorder begin

lemma wlog_le [case_names sym le]:
  assumes "\<And>a b. P a b \<Longrightarrow> P b a"
  and "\<And>a b. a \<le> b \<Longrightarrow> P a b"
  shows "P b a"
by (metis assms linear)

lemma empty_set_less_aux [simp]: "{} \<sqsubset>' A \<longleftrightarrow> A \<noteq> {} \<and> finite A"
by(auto 4 3 simp add: set_less_aux_def intro!: Min_eqI intro: bexI[where x="Min A"] order_trans[where y="Min A"] Min_in)

lemma empty_set_less_eq_aux [simp]: "{} \<sqsubseteq>' A \<longleftrightarrow> finite A"
by(auto simp add: set_less_eq_aux_def finite_complement_partition)

lemma set_less_aux_trans:
  assumes AB: "A \<sqsubset>' B" and BC: "B \<sqsubset>' C"
  shows "A \<sqsubset>' C"
proof -
  from AB BC have A: "finite A" and B: "finite B" and C: "finite C"
    by(auto simp add: set_less_aux_def)
  from AB A B obtain ab where ab: "ab \<in> B - A"
    and minAB: "\<And>x. \<lbrakk> x \<in> A; x \<notin> B \<rbrakk> \<Longrightarrow> ab \<le> x \<and> (x \<le> ab \<longrightarrow> ab = x)"
    and minBA: "\<And>x. \<lbrakk> x \<in> B; x \<notin> A \<rbrakk> \<Longrightarrow> ab \<le> x \<and> (x \<le> ab \<longrightarrow> ab = x)" 
    unfolding set_less_aux_def by auto
  from BC B C obtain bc where bc: "bc \<in> C - B"
    and minBC: "\<And>x. \<lbrakk> x \<in> B; x \<notin> C \<rbrakk> \<Longrightarrow> bc \<le> x \<and> (x \<le> bc \<longrightarrow> bc = x)"
    and minCB: "\<And>x. \<lbrakk> x \<in> C; x \<notin> B \<rbrakk> \<Longrightarrow> bc \<le> x \<and> (x \<le> bc \<longrightarrow> bc = x)"
    unfolding set_less_aux_def by auto
  show ?thesis
  proof(cases "ab \<le> bc")
    case True
    hence "ab \<in> C - A" "ab \<notin> A - C"
      using ab bc by(auto dest: minBC antisym)
    moreover {
      fix x
      assume x: "x \<in> (C - A) \<union> (A - C)"
      hence "ab \<le> x" 
        by(cases "x \<in> B")(auto dest: minAB minBA minBC minCB intro: order_trans[OF True])
      moreover hence "ab \<noteq> x \<longrightarrow> \<not> x \<le> ab" using ab bc x
        by(cases "x \<in> B")(auto dest: antisym)
      moreover note calculation }
    ultimately show ?thesis using A C unfolding set_less_aux_def by auto
  next
    case False
    with linear[of ab bc] have "bc \<le> ab" by simp
    with ab bc have "bc \<in> C - A" "bc \<notin> A - C" by(auto dest: minAB antisym)
    moreover {
      fix x
      assume x: "x \<in> (C - A) \<union> (A - C)"
      hence "bc \<le> x"
        by(cases "x \<in> B")(auto dest: minAB minBA minBC minCB intro: order_trans[OF \<open>bc \<le> ab\<close>])
      moreover hence "bc \<noteq> x \<longrightarrow> \<not> x \<le> bc" using ab bc x
        by(cases "x \<in> B")(auto dest: antisym) 
      moreover note calculation }
    ultimately show ?thesis using A C unfolding set_less_aux_def by auto
  qed
qed

lemma set_less_eq_aux_trans [trans]:
  "\<lbrakk> A \<sqsubseteq>' B; B \<sqsubseteq>' C \<rbrakk> \<Longrightarrow> A \<sqsubseteq>' C"
by(auto simp add: set_less_eq_aux_def dest: set_less_aux_trans)

lemma set_less_trans_set_less_eq [trans]:
  "\<lbrakk> A \<sqsubset>' B; B \<sqsubseteq>' C \<rbrakk> \<Longrightarrow> A \<sqsubset>' C"
by(auto simp add: set_less_eq_aux_def dest: set_less_aux_trans)

lemma set_less_eq_aux_porder: "partial_order_on infinite_complement_partition {(A, B). A \<sqsubseteq>' B}"
by(auto simp add: preorder_on_def partial_order_on_def intro!: refl_onI transI antisymI dest: set_less_eq_aux_infinite_complement_partitionD intro: set_less_eq_aux_antisym set_less_eq_aux_trans del: equalityI)

lemma psubset_finite_imp_set_less_aux:
  assumes AsB: "A \<subset> B" and B: "finite B"
  shows "A \<sqsubset>' B"
proof -
  from AsB B have A: "finite A" by(auto intro: finite_subset)
  moreover from AsB B have "Min (B - A) \<in> B - A" by - (rule Min_in, auto)
  ultimately show ?thesis using B AsB
    by(auto simp add: set_less_aux_def intro!: rev_bexI[where x="Min (B - A)"] Min_eqI dest: Min_ge_iff[THEN iffD1, rotated 2])
qed

lemma subset_finite_imp_set_less_eq_aux:
  "\<lbrakk> A \<subseteq> B; finite B \<rbrakk> \<Longrightarrow> A \<sqsubseteq>' B"
by(cases "A = B")(auto simp add: set_less_eq_aux_def finite_complement_partition intro: psubset_finite_imp_set_less_aux)

lemma empty_set_less_aux_finite_iff: 
  "finite A \<Longrightarrow> {} \<sqsubset>' A \<longleftrightarrow> A \<noteq> {}"
by(auto intro: psubset_finite_imp_set_less_aux)

lemma set_less_aux_finite_total:
  assumes A: "finite A" and B: "finite B"
  shows "A \<sqsubset>' B \<or> A = B \<or> B \<sqsubset>' A"
proof(cases "A \<subseteq> B \<or> B \<subseteq> A")
  case True thus ?thesis
    using A B psubset_finite_imp_set_less_aux[of A B] psubset_finite_imp_set_less_aux[of B A]
    by auto
next
  case False
  hence A': "\<not> A \<subseteq> B" and B': "\<not> B \<subseteq> A" and AnB: "A \<noteq> B" by auto
  thus ?thesis using A B
  proof(induct "Min (B - A)" "Min (A - B)" arbitrary: A B rule: wlog_le)
    case (sym m n)
    from sym.hyps[OF refl refl] sym.prems show ?case by blast
  next
    case (le A B)
    note A = \<open>finite A\<close> and B = \<open>finite B\<close>
      and A' = \<open>\<not> A \<subseteq> B\<close> and B' = \<open>\<not> B \<subseteq> A\<close>
    { fix z
      assume z: "z \<in> (A - B) \<union> (B - A)"
      hence "Min (B - A) \<le> z \<and> (z \<le> Min (B - A) \<longrightarrow> Min (B - A) = z)"
      proof
        assume "z \<in> B - A" 
        hence "Min (B - A) \<le> z" by(simp add: B)
        thus ?thesis by auto
      next
        assume "z \<in> A - B"
        hence "Min (A - B) \<le> z" by(simp add: A)
        with le.hyps show ?thesis by(auto)
      qed }
    moreover have "Min (B - A) \<in> B - A" by(rule Min_in)(simp_all add: B B')
    ultimately have "A \<sqsubset>' B" using A B by(auto simp add: set_less_aux_def)
    thus ?case ..
  qed
qed

lemma set_less_eq_aux_finite_total:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> A \<sqsubseteq>' B \<or> A = B \<or> B \<sqsubseteq>' A"
by(drule (1) set_less_aux_finite_total)(auto simp add: set_less_eq_aux_def)

lemma set_less_eq_aux_finite_total2:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> A \<sqsubseteq>' B \<or> B \<sqsubseteq>' A"
by(drule (1) set_less_eq_aux_finite_total)(auto simp add: finite_complement_partition)

lemma set_less_aux_rec:
  assumes A: "finite A" and B: "finite B"
  and A': "A \<noteq> {}" and B': "B \<noteq> {}"
  shows "A \<sqsubset>' B \<longleftrightarrow> Min B < Min A \<or> Min A = Min B \<and> A - {Min A} \<sqsubset>' B - {Min A}"
proof(cases "Min A = Min B")
  case True
  from A A' B B' have "insert (Min A) A = A" "insert (Min B) B = B"
    by(auto simp add: ex_in_conv[symmetric] exI)
  with True show ?thesis
    by(subst (2) set_less_aux_insert_same[symmetric, where x="Min A"]) simp_all
next
  case False
  have "A \<sqsubset>' B \<longleftrightarrow> Min B < Min A"
  proof
    assume AB: "A \<sqsubset>' B"
    with B A obtain ab where ab: "ab \<in> B - A"
      and AB: "\<And>x. \<lbrakk> x \<in> A; x \<notin> B \<rbrakk> \<Longrightarrow> ab \<le> x"
      by(auto simp add: set_less_aux_def)
    { fix a assume "a \<in> A"
      hence "Min B \<le> a" using A A' B B' ab
        by(cases "a \<in> B")(auto intro: order_trans[where y=ab] dest: AB) }
    hence "Min B \<le> Min A" using A A' by simp
    with False show "Min B < Min A" using False by auto
  next
    assume "Min B < Min A"
    hence "\<forall>z\<in>A - B \<union> (B - A). Min B \<le> z \<and> (z \<le> Min B \<longrightarrow> Min B = z)"
      using A B A' B' by(auto 4 4 intro: Min_in Min_eqI dest: bspec bspec[where x="Min B"])
    moreover have "Min B \<notin> A" using \<open>Min B < Min A\<close> by (metis A Min_le not_less)
    ultimately show "A \<sqsubset>' B" using A B A' B' by(simp add: set_less_aux_def bexI[where x="Min B"])
  qed
  thus ?thesis using False by simp
qed

lemma set_less_eq_aux_rec:
  assumes "finite A" "finite B" "A \<noteq> {}" "B \<noteq> {}"
  shows "A \<sqsubseteq>' B \<longleftrightarrow> Min B < Min A \<or> Min A = Min B \<and> A - {Min A} \<sqsubseteq>' B - {Min A}"
proof(cases "A = B")
  case True thus ?thesis using assms by(simp add: finite_complement_partition)
next
  case False
  moreover 
  hence "Min A = Min B \<Longrightarrow> A - {Min A} \<noteq> B - {Min B}"
    by (metis (lifting) assms Min_in insert_Diff)
  ultimately show ?thesis using set_less_aux_rec[OF assms]
    by(simp add: set_less_eq_aux_def cong: conj_cong)
qed

lemma set_less_aux_Min_antimono:
  "\<lbrakk> Min A < Min B;  finite A; finite B; A \<noteq> {} \<rbrakk> \<Longrightarrow> B \<sqsubset>' A"
using set_less_aux_rec[of B A] 
by(cases "B = {}")(simp_all add: empty_set_less_aux_finite_iff)

lemma sorted_Cons_Min: "sorted (x # xs) \<Longrightarrow> Min (insert x (set xs)) = x"
by(auto simp add: intro: Min_eqI)

lemma set_less_aux_code:
  "\<lbrakk> sorted xs; distinct xs; sorted ys; distinct ys \<rbrakk>
  \<Longrightarrow> set xs \<sqsubset>' set ys \<longleftrightarrow> ord.lexordp (>) xs ys"
apply(induct xs ys rule: list_induct2')
apply(simp_all add: empty_set_less_aux_finite_iff sorted_Cons_Min set_less_aux_rec neq_Nil_conv)
apply(auto simp add: cong: conj_cong)
done

lemma set_less_eq_aux_code:
  assumes "sorted xs" "distinct xs" "sorted ys" "distinct ys"
  shows "set xs \<sqsubseteq>' set ys \<longleftrightarrow> ord.lexordp_eq (>) xs ys"
proof -
  have dual: "class.linorder (\<ge>) (>)"
    by(rule linorder.dual_linorder) unfold_locales
  from assms show ?thesis
    by(auto simp add: set_less_eq_aux_def finite_complement_partition linorder.lexordp_eq_conv_lexord[OF dual] set_less_aux_code intro: sorted_distinct_set_unique)
qed

end

subsubsection \<open>Extending @{term set_less_eq_aux} to have @{term "{}"} as least element\<close>

context ord begin

definition set_less_eq_aux' :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>''''" 50)
where "A \<sqsubseteq>'' B \<longleftrightarrow> A \<sqsubseteq>' B \<or> A = {} \<and> B \<in> infinite_complement_partition"

lemma set_less_eq_aux'_refl:
  "A \<sqsubseteq>'' A \<longleftrightarrow> A \<in> infinite_complement_partition"
by(auto simp add: set_less_eq_aux'_def)

lemma set_less_eq_aux'_antisym: "\<lbrakk> A \<sqsubseteq>'' B; B \<sqsubseteq>'' A \<rbrakk> \<Longrightarrow> A = B"
by(auto simp add: set_less_eq_aux'_def intro: set_less_eq_aux_antisym del: equalityI)

lemma set_less_eq_aux'_infinite_complement_partitionD:
  "A \<sqsubseteq>'' B \<Longrightarrow> A \<in> infinite_complement_partition \<and> B \<in> infinite_complement_partition"
by(auto simp add: set_less_eq_aux'_def intro: finite_complement_partition dest: set_less_eq_aux_infinite_complement_partitionD)

lemma empty_set_less_eq_def [simp]: "{} \<sqsubseteq>'' B \<longleftrightarrow> B \<in> infinite_complement_partition"
by(auto simp add: set_less_eq_aux'_def dest: set_less_eq_aux_infinite_complement_partitionD)

end

context linorder begin

lemma set_less_eq_aux'_trans: "\<lbrakk> A \<sqsubseteq>'' B; B \<sqsubseteq>'' C \<rbrakk> \<Longrightarrow> A \<sqsubseteq>'' C"
by(auto simp add: set_less_eq_aux'_def del: equalityI intro: set_less_eq_aux_trans dest: set_less_eq_aux_infinite_complement_partitionD)

lemma set_less_eq_aux'_porder: "partial_order_on infinite_complement_partition {(A, B). A \<sqsubseteq>'' B}"
by(auto simp add: partial_order_on_def preorder_on_def intro!: refl_onI transI antisymI dest: set_less_eq_aux'_antisym set_less_eq_aux'_infinite_complement_partitionD simp add: set_less_eq_aux'_refl intro: set_less_eq_aux'_trans)

end

subsubsection \<open>Extend @{term set_less_eq_aux'} to a total order on @{term infinite_complement_partition}\<close>

context ord begin

definition set_less_eq_aux'' :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>''''''" 50)
where "set_less_eq_aux'' =
  (SOME sleq. 
    (linear_order_on UNIV {(a, b). a \<le> b} \<longrightarrow> linear_order_on infinite_complement_partition {(A, B). sleq A B}) \<and> order_consistent {(A, B). A \<sqsubseteq>'' B} {(A, B). sleq A B})"

lemma set_less_eq_aux''_spec:
  shows "linear_order {(a, b). a \<le> b} \<Longrightarrow> linear_order_on infinite_complement_partition {(A, B). A \<sqsubseteq>''' B}"
  (is "PROP ?thesis1")
  and "order_consistent {(A, B). A \<sqsubseteq>'' B} {(A, B). A \<sqsubseteq>''' B}" (is ?thesis2)
proof -
  let ?P = "\<lambda>sleq. (linear_order {(a, b). a \<le> b} \<longrightarrow> linear_order_on infinite_complement_partition {(A, B). sleq A B}) \<and> 
                  order_consistent {(A, B). A \<sqsubseteq>'' B} {(A, B). sleq A B}"
  have "Ex ?P"
  proof(cases "linear_order {(a, b). a \<le> b}")
    case False
    have "antisym {(a, b). a \<sqsubseteq>'' b}"
      by (rule antisymI) (simp add: set_less_eq_aux'_antisym)
    then show ?thesis using False
      by (auto intro: antisym_order_consistent_self)
  next
    case True
    hence "partial_order_on infinite_complement_partition {(A, B). A \<sqsubseteq>'' B}"
      by(rule linorder.set_less_eq_aux'_porder[OF linear_order_imp_linorder])
    then obtain s where "linear_order_on infinite_complement_partition s"
      and "order_consistent {(A, B). A \<sqsubseteq>'' B} s" by(rule porder_extend_to_linorder)
    thus ?thesis by(auto intro: exI[where x="\<lambda>A B. (A, B) \<in> s"])
  qed
  hence "?P (Eps ?P)" by(rule someI_ex)
  thus "PROP ?thesis1" ?thesis2 by(simp_all add: set_less_eq_aux''_def)
qed

end

context linorder begin

lemma set_less_eq_aux''_linear_order:
  "linear_order_on infinite_complement_partition {(A, B). A \<sqsubseteq>''' B}"
by(rule set_less_eq_aux''_spec)(rule linear_order)

lemma set_less_eq_aux''_refl [iff]: "A \<sqsubseteq>''' A \<longleftrightarrow> A \<in> infinite_complement_partition"
using set_less_eq_aux''_linear_order
by(auto simp add: linear_order_on_def partial_order_on_def preorder_on_def dest: refl_onD refl_onD1)

lemma set_less_eq_aux'_into_set_less_eq_aux'':
  assumes "A \<sqsubseteq>'' B" 
  shows "A \<sqsubseteq>''' B"
proof(rule ccontr)
  assume nleq: "\<not> ?thesis"
  moreover from assms have A: "A \<in> infinite_complement_partition" 
    and B: "B \<in> infinite_complement_partition"
    by(auto dest: set_less_eq_aux'_infinite_complement_partitionD)
  with set_less_eq_aux''_linear_order have "A \<sqsubseteq>''' B \<or> A = B \<or> B \<sqsubseteq>''' A"
    by(auto simp add: linear_order_on_def dest: total_onD)
  ultimately have "B \<sqsubseteq>''' A" using B by auto
  with assms have "A = B" using set_less_eq_aux''_spec(2)
    by(simp add: order_consistent_def)
  with A nleq show False by simp
qed

lemma finite_set_less_eq_aux''_finite:
  assumes "finite A" and "finite B"
  shows "A \<sqsubseteq>''' B \<longleftrightarrow> A \<sqsubseteq>'' B"
proof
  assume "A \<sqsubseteq>''' B"
  from assms have "A \<sqsubseteq>' B \<or> B \<sqsubseteq>' A" by(rule set_less_eq_aux_finite_total2)
  hence "A \<sqsubseteq>'' B \<or> B \<sqsubseteq>'' A" by(auto simp add: set_less_eq_aux'_def)
  thus "A \<sqsubseteq>'' B"
  proof
    assume "B \<sqsubseteq>'' A"
    hence "B \<sqsubseteq>''' A" by(rule set_less_eq_aux'_into_set_less_eq_aux'')
    with \<open>A \<sqsubseteq>''' B\<close> set_less_eq_aux''_linear_order have "A = B"
      by(auto simp add: linear_order_on_def partial_order_on_def dest: antisymD)
    thus ?thesis using assms by(simp add: finite_complement_partition set_less_eq_aux'_def)
  qed
qed(rule set_less_eq_aux'_into_set_less_eq_aux'')

lemma set_less_eq_aux''_finite:
  "finite (UNIV :: 'a set) \<Longrightarrow> set_less_eq_aux'' = set_less_eq_aux"
by(auto simp add: fun_eq_iff finite_set_less_eq_aux''_finite set_less_eq_aux'_def finite_subset[OF subset_UNIV])

lemma set_less_eq_aux''_antisym:
  "\<lbrakk> A \<sqsubseteq>''' B; B \<sqsubseteq>''' A; 
     A \<in> infinite_complement_partition; B \<in> infinite_complement_partition \<rbrakk>
  \<Longrightarrow> A = B"
using set_less_eq_aux''_linear_order 
by(auto simp add: linear_order_on_def partial_order_on_def dest: antisymD del: equalityI)

lemma set_less_eq_aux''_trans: "\<lbrakk> A \<sqsubseteq>''' B; B \<sqsubseteq>''' C \<rbrakk> \<Longrightarrow> A \<sqsubseteq>''' C"
using set_less_eq_aux''_linear_order
by(auto simp add: linear_order_on_def partial_order_on_def preorder_on_def dest: transD)

lemma set_less_eq_aux''_total:
  "\<lbrakk> A \<in> infinite_complement_partition; B \<in> infinite_complement_partition \<rbrakk>
  \<Longrightarrow> A \<sqsubseteq>''' B \<or> B \<sqsubseteq>''' A"
using set_less_eq_aux''_linear_order
by(auto simp add: linear_order_on_def dest: total_onD)

end

subsubsection \<open>Extend @{term set_less_eq_aux''} to cofinite sets\<close>

context ord begin

definition set_less_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
where 
  "A \<sqsubseteq> B \<longleftrightarrow> 
  (if A \<in> infinite_complement_partition then A \<sqsubseteq>''' B \<or> B \<notin> infinite_complement_partition
   else B \<notin> infinite_complement_partition \<and> - B \<sqsubseteq>''' - A)"

definition set_less :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" (infix "\<sqsubset>" 50)
where "A \<sqsubset> B \<longleftrightarrow> A \<sqsubseteq> B \<and> \<not> B \<sqsubseteq> A"

lemma set_less_eq_def2:
  "A \<sqsubseteq> B \<longleftrightarrow>
  (if finite (UNIV :: 'a set) then A \<sqsubseteq>''' B 
   else if A \<in> infinite_complement_partition then A \<sqsubseteq>''' B \<or> B \<notin> infinite_complement_partition
   else B \<notin> infinite_complement_partition \<and> - B \<sqsubseteq>''' - A)"
by(simp add: set_less_eq_def)

end

context linorder begin

lemma set_less_eq_refl [iff]: "A \<sqsubseteq> A"
by(auto simp add: set_less_eq_def2 not_in_complement_partition)

lemma set_less_eq_antisym: "\<lbrakk> A \<sqsubseteq> B; B \<sqsubseteq> A \<rbrakk> \<Longrightarrow> A = B"
by(auto simp add: set_less_eq_def2 set_less_eq_aux''_finite not_in_complement_partition not_in_complement_partition_False del: equalityI split: if_split_asm dest: set_less_eq_aux_antisym set_less_eq_aux''_antisym)

lemma set_less_eq_trans: "\<lbrakk> A \<sqsubseteq> B; B \<sqsubseteq> C \<rbrakk> \<Longrightarrow> A \<sqsubseteq> C"
by(auto simp add: set_less_eq_def split: if_split_asm intro: set_less_eq_aux''_trans)

lemma set_less_eq_total: "A \<sqsubseteq> B \<or> B \<sqsubseteq> A"
by(auto simp add: set_less_eq_def2 set_less_eq_aux''_finite not_in_complement_partition not_in_complement_partition_False intro: set_less_eq_aux_finite_total2 finite_subset[OF subset_UNIV] del: disjCI dest: set_less_eq_aux''_total)

lemma set_less_eq_linorder: "class.linorder (\<sqsubseteq>) (\<sqsubset>)"
by(unfold_locales)(auto simp add: set_less_def set_less_eq_antisym set_less_eq_total intro: set_less_eq_trans)

lemma set_less_eq_conv_set_less: "set_less_eq A B \<longleftrightarrow> A = B \<or> set_less A B"
by(auto simp add: set_less_def del: equalityI dest: set_less_eq_antisym)

lemma Compl_set_less_eq_Compl: "- A \<sqsubseteq> - B \<longleftrightarrow> B \<sqsubseteq> A"
by(auto simp add: set_less_eq_def2 not_in_complement_partition_False not_in_complement_partition set_less_eq_aux''_finite Compl_set_less_eq_aux_Compl)

lemma Compl_set_less_Compl: "- A \<sqsubset> - B \<longleftrightarrow> B \<sqsubset> A"
by(simp add: set_less_def Compl_set_less_eq_Compl)

lemma set_less_eq_finite_iff: "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> A \<sqsubseteq> B \<longleftrightarrow> A \<sqsubseteq>' B"
by(auto simp add: set_less_eq_def finite_complement_partition set_less_eq_aux'_def finite_set_less_eq_aux''_finite)

lemma set_less_finite_iff: "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> A \<sqsubset> B \<longleftrightarrow> A \<sqsubset>' B"
by(simp add: set_less_def set_less_aux_conv_set_less_eq_aux set_less_eq_finite_iff)

lemma infinite_set_less_eq_Complement:
  "\<lbrakk> finite A; finite B; \<not> finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow> A \<sqsubseteq> - B"
by(simp add: set_less_eq_def finite_complement_partition not_in_complement_partition)

lemma infinite_set_less_Complement:
  "\<lbrakk> finite A; finite B; \<not> finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow> A \<sqsubset> - B"
by(auto simp add: set_less_def dest: set_less_eq_antisym intro: infinite_set_less_eq_Complement)

lemma infinite_Complement_set_less_eq:
  "\<lbrakk> finite A; finite B; \<not> finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow> \<not> - A \<sqsubseteq> B"
using infinite_set_less_eq_Complement[of A B] Compl_set_less_eq_Compl[of A "- B"]
by(auto dest: set_less_eq_antisym)

lemma infinite_Complement_set_less:
  "\<lbrakk> finite A; finite B; \<not> finite (UNIV :: 'a set) \<rbrakk> \<Longrightarrow> \<not> - A \<sqsubset> B"
using infinite_Complement_set_less_eq[of A B]
by(simp add: set_less_def)

lemma empty_set_less_eq [iff]: "{} \<sqsubseteq> A"
by(auto simp add: set_less_eq_def finite_complement_partition intro: set_less_eq_aux'_into_set_less_eq_aux'')

lemma set_less_eq_empty [iff]: "A \<sqsubseteq> {} \<longleftrightarrow> A = {}"
by (metis empty_set_less_eq set_less_eq_antisym)

lemma empty_set_less_iff [iff]: "{} \<sqsubset> A \<longleftrightarrow> A \<noteq> {}"
by(simp add: set_less_def)

lemma not_set_less_empty [simp]: "\<not> A \<sqsubset> {}"
by(simp add: set_less_def)

lemma set_less_eq_UNIV [iff]: "A \<sqsubseteq> UNIV"
using Compl_set_less_eq_Compl[of "- A" "{}"] by simp

lemma UNIV_set_less_eq [iff]: "UNIV \<sqsubseteq> A \<longleftrightarrow> A = UNIV"
using Compl_set_less_eq_Compl[of "{}" "- A"]
by(simp add: Compl_eq_empty_iff)

lemma set_less_UNIV_iff [iff]: "A \<sqsubset> UNIV \<longleftrightarrow> A \<noteq> UNIV"
by(simp add: set_less_def)

lemma not_UNIV_set_less [simp]: "\<not> UNIV \<sqsubset> A"
by(simp add: set_less_def)

end

subsection \<open>Implementation based on sorted lists\<close>

type_synonym 'a proper_interval = "'a option \<Rightarrow> 'a option \<Rightarrow> bool"

class proper_intrvl = ord +
  fixes proper_interval :: "'a proper_interval"

class proper_interval = proper_intrvl +
  assumes proper_interval_simps:
  "proper_interval None None = True"
  "proper_interval None (Some y) = (\<exists>z. z < y)"
  "proper_interval (Some x) None = (\<exists>z. x < z)"
  "proper_interval (Some x) (Some y) = (\<exists>z. x < z \<and> z < y)"

context proper_intrvl begin

function set_less_eq_aux_Compl :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "set_less_eq_aux_Compl ao [] ys \<longleftrightarrow> True"
| "set_less_eq_aux_Compl ao xs [] \<longleftrightarrow> True"
| "set_less_eq_aux_Compl ao (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then proper_interval ao (Some x) \<or> set_less_eq_aux_Compl (Some x) xs (y # ys)
   else if y < x then proper_interval ao (Some y) \<or> set_less_eq_aux_Compl (Some y) (x # xs) ys
   else proper_interval ao (Some y))"
by(pat_completeness) simp_all
termination by(lexicographic_order)

fun Compl_set_less_eq_aux :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "Compl_set_less_eq_aux ao [] [] \<longleftrightarrow> \<not> proper_interval ao None"
| "Compl_set_less_eq_aux ao [] (y # ys) \<longleftrightarrow> \<not> proper_interval ao (Some y) \<and> Compl_set_less_eq_aux (Some y) [] ys"
| "Compl_set_less_eq_aux ao (x # xs) [] \<longleftrightarrow> \<not> proper_interval ao (Some x) \<and> Compl_set_less_eq_aux (Some x) xs []"
| "Compl_set_less_eq_aux ao (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then \<not> proper_interval ao (Some x) \<and> Compl_set_less_eq_aux (Some x) xs (y # ys)
   else if y < x then \<not> proper_interval ao (Some y) \<and> Compl_set_less_eq_aux (Some y) (x # xs) ys
   else \<not> proper_interval ao (Some y))"

fun set_less_aux_Compl :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "set_less_aux_Compl ao [] [] \<longleftrightarrow> proper_interval ao None"
| "set_less_aux_Compl ao [] (y # ys) \<longleftrightarrow> proper_interval ao (Some y) \<or> set_less_aux_Compl (Some y) [] ys"
| "set_less_aux_Compl ao (x # xs) [] \<longleftrightarrow> proper_interval ao (Some x) \<or> set_less_aux_Compl (Some x) xs []"
| "set_less_aux_Compl ao (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then proper_interval ao (Some x) \<or> set_less_aux_Compl (Some x) xs (y # ys)
   else if y < x then proper_interval ao (Some y) \<or> set_less_aux_Compl (Some y) (x # xs) ys
   else proper_interval ao (Some y))"

function Compl_set_less_aux :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "Compl_set_less_aux ao [] ys \<longleftrightarrow> False"
| "Compl_set_less_aux ao xs [] \<longleftrightarrow> False"
| "Compl_set_less_aux ao (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then \<not> proper_interval ao (Some x) \<and> Compl_set_less_aux (Some x) xs (y # ys)
   else if y < x then \<not> proper_interval ao (Some y) \<and> Compl_set_less_aux (Some y) (x # xs) ys
   else \<not> proper_interval ao (Some y))"
by pat_completeness simp_all
termination by lexicographic_order

end

lemmas [code] =
  proper_intrvl.set_less_eq_aux_Compl.simps
  proper_intrvl.set_less_aux_Compl.simps
  proper_intrvl.Compl_set_less_eq_aux.simps
  proper_intrvl.Compl_set_less_aux.simps

class linorder_proper_interval = linorder + proper_interval 
begin

theorem assumes fin: "finite (UNIV :: 'a set)"
  and xs: "sorted xs" "distinct xs"
  and ys: "sorted ys" "distinct ys"
  shows set_less_eq_aux_Compl2_conv_set_less_eq_aux_Compl:
  "set xs \<sqsubseteq>' - set ys \<longleftrightarrow> set_less_eq_aux_Compl None xs ys" (is ?Compl2)
  and Compl1_set_less_eq_aux_conv_Compl_set_less_eq_aux:
  "- set xs \<sqsubseteq>' set ys \<longleftrightarrow> Compl_set_less_eq_aux None xs ys" (is ?Compl1)
proof -
  note fin' [simp] = finite_subset[OF subset_UNIV fin]

  define above where "above = case_option UNIV (Collect \<circ> less)"
  have above_simps [simp]: "above None = UNIV" "\<And>x. above (Some x) = {y. x < y}"
    and above_upclosed: "\<And>x y ao. \<lbrakk> x \<in> above ao; x < y \<rbrakk> \<Longrightarrow> y \<in> above ao"
    and proper_interval_Some2: "\<And>x ao. proper_interval ao (Some x) \<longleftrightarrow> (\<exists>z\<in>above ao. z < x)"
    and proper_interval_None2: "\<And>ao. proper_interval ao None \<longleftrightarrow> above ao \<noteq> {}"
    by(simp_all add: proper_interval_simps above_def split: option.splits)

  { fix ao x A B
    assume ex: "proper_interval ao (Some x)"
      and A: "\<forall>a \<in> A. x \<le> a"
      and B: "\<forall>b \<in> B. x \<le> b"
    from ex obtain z where z_ao: "z \<in> above ao" and z: "z < x"
      by(auto simp add: proper_interval_Some2)
    with A have A_eq: "A \<inter> above ao = A"
      by(auto simp add: above_upclosed)
    from z_ao z B have B_eq: "B \<inter> above ao = B"
      by(auto simp add: above_upclosed)
    define w where "w = Min (above ao)"
    with z_ao have "w \<le> z" "\<forall>z \<in> above ao. w \<le> z" "w \<in> above ao"
      by(auto simp add: Min_le_iff intro: Min_in)
    hence "A \<inter> above ao \<sqsubset>' (- B) \<inter> above ao" (is "?lhs \<sqsubset>' ?rhs")
      using A B z by(auto simp add: set_less_aux_def intro!: bexI[where x="w"])
    hence "A \<sqsubseteq>' ?rhs" unfolding A_eq by(simp add: set_less_eq_aux_def)
    moreover 
    from z_ao z A B have "z \<in> - A \<inter> above ao" "z \<notin> B" by auto
    hence neq: "- A \<inter> above ao \<noteq> B \<inter> above ao" by auto
    have "\<not> - A \<inter> above ao \<sqsubset>' B \<inter> above ao" (is "\<not> ?lhs' \<sqsubset>' ?rhs'")
      using A B z z_ao by(force simp add: set_less_aux_def not_less dest: bspec[where x=z])
    with neq have "\<not> ?lhs' \<sqsubseteq>' B" unfolding B_eq by(auto simp add: set_less_eq_aux_def)
    moreover note calculation }
  note proper_interval_set_less_eqI = this(1)
    and proper_interval_not_set_less_eq_auxI = this(2)

  { fix ao
    assume "set xs \<union> set ys \<subseteq> above ao"
    with xs ys
    have "set_less_eq_aux_Compl ao xs ys \<longleftrightarrow> set xs \<sqsubseteq>' (- set ys) \<inter> above ao"
    proof(induction ao xs ys rule: set_less_eq_aux_Compl.induct)
      case 1 thus ?case by simp
    next
      case 2 thus ?case by(auto intro: subset_finite_imp_set_less_eq_aux)
    next
      case (3 ao x xs y ys)
      note ao = \<open>set (x # xs) \<union> set (y # ys) \<subseteq> above ao\<close>
      hence x_ao: "x \<in> above ao" and y_ao: "y \<in> above ao" by simp_all
      note yys = \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
      hence ys: "sorted ys" "distinct ys" and y_Min: "\<forall>y' \<in> set ys. y < y'"
        by(auto simp add: less_le)
      note xxs = \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
      hence xs: "sorted xs" "distinct xs" and x_Min: "\<forall>x' \<in> set xs. x < x'"
        by(auto simp add: less_le)
      let ?lhs = "set (x # xs)" and ?rhs = "- set (y # ys) \<inter> above ao"
      show ?case
      proof(cases "x < y")
        case True
        show ?thesis
        proof(cases "proper_interval ao (Some x)")
          case True
          hence "?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>x < y\<close>
            by(auto intro!: proper_interval_set_less_eqI)
          with True show ?thesis using \<open>x < y\<close> by simp
        next
          case False
          have "set xs \<union> set (y # ys) \<subseteq> above (Some x)" using True x_Min y_Min by auto
          with True xs yys
          have IH: "set_less_eq_aux_Compl (Some x) xs (y # ys) = 
            (set xs \<sqsubseteq>' - set (y # ys) \<inter> above (Some x))"
            by(rule "3.IH")
          from True y_Min x_ao have "x \<in> - set (y # ys) \<inter> above ao" by auto
          hence "?rhs \<noteq> {}" by blast
          moreover have "Min ?lhs = x" using x_Min x_ao by(auto intro!: Min_eqI)
          moreover have "Min ?rhs = x" using \<open>x < y\<close> y_Min x_ao False
            by(auto intro!: Min_eqI simp add: proper_interval_Some2)
          moreover have "set xs = set xs - {x}"
            using ao x_Min by auto
          moreover have "- set (y # ys) \<inter> above (Some x) = - set (y # ys) \<inter> above ao - {x}"
            using False x_ao by(auto simp add: proper_interval_Some2 intro: above_upclosed)
          ultimately show ?thesis using True False IH
            by(simp del: set_simps)(subst (2) set_less_eq_aux_rec, simp_all add: x_ao)
        qed
      next
        case False
        show ?thesis
        proof(cases "y < x")
          case True
          show ?thesis
          proof(cases "proper_interval ao (Some y)")
            case True
            hence "?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>\<not> x < y\<close>
              by(auto intro!: proper_interval_set_less_eqI)
            with True show ?thesis using \<open>\<not> x < y\<close> by simp
          next
            case False
            have "set (x # xs) \<union> set ys \<subseteq> above (Some y)"
              using \<open>y < x\<close> x_Min y_Min by auto
            with \<open>\<not> x < y\<close> \<open>y < x\<close> xxs ys
            have IH: "set_less_eq_aux_Compl (Some y) (x # xs) ys = 
              (set (x # xs) \<sqsubseteq>' - set ys \<inter> above (Some y))"
              by(rule "3.IH")
            moreover have "- set ys \<inter> above (Some y) = ?rhs"
              using y_ao False by(auto intro: above_upclosed simp add: proper_interval_Some2)
            ultimately show ?thesis using \<open>\<not> x < y\<close> True False by simp
          qed
        next
          case False with \<open>\<not> x < y\<close> have "x = y" by auto
          { assume "proper_interval ao (Some y)"
            hence "?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>x = y\<close>
              by(auto intro!: proper_interval_set_less_eqI) }
          moreover
          { assume "?lhs \<sqsubseteq>' ?rhs"
            moreover have "?lhs \<noteq> ?rhs"
            proof
              assume eq: "?lhs = ?rhs"
              have "x \<in> ?lhs" using x_ao by simp
              also note eq also note \<open>x = y\<close>
              finally show False by simp
            qed
            ultimately obtain z where "z \<in> above ao" "z < y" using \<open>x = y\<close> y_ao
              by(fastforce simp add: set_less_eq_aux_def set_less_aux_def not_le dest!: bspec[where x=y])
            hence "proper_interval ao (Some y)" by(auto simp add: proper_interval_Some2) }
          ultimately show ?thesis using \<open>x = y\<close> \<open>\<not> x < y\<close> \<open>\<not> y < x\<close> by auto
        qed
      qed
    qed }
  from this[of None] show ?Compl2 by simp
  
  { fix ao
    assume "set xs \<union> set ys \<subseteq> above ao"
    with xs ys
    have "Compl_set_less_eq_aux ao xs ys \<longleftrightarrow> (- set xs) \<inter> above ao \<sqsubseteq>' set ys"
    proof(induction ao xs ys rule: Compl_set_less_eq_aux.induct)
      case 1 thus ?case by(simp add: proper_interval_None2)
    next
      case (2 ao y ys)
      from \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
      have ys: "sorted ys" "distinct ys" and y_Min: "\<forall>y' \<in> set ys. y < y'"
        by(auto simp add: less_le)
      show ?case
      proof(cases "proper_interval ao (Some y)")
        case True 
        hence "\<not> - set [] \<inter> above ao \<sqsubseteq>' set (y # ys)" using y_Min
          by -(erule proper_interval_not_set_less_eq_auxI, auto)
        thus ?thesis using True by simp
      next
        case False
        note ao = \<open>set [] \<union> set (y # ys) \<subseteq> above ao\<close> 
        hence y_ao: "y \<in> above ao" by simp
        from ao y_Min have "set [] \<union> set ys \<subseteq> above (Some y)" by auto
        with \<open>sorted []\<close> \<open>distinct []\<close> ys
        have "Compl_set_less_eq_aux (Some y) [] ys \<longleftrightarrow> - set [] \<inter> above (Some y) \<sqsubseteq>' set ys"
          by(rule "2.IH")
        moreover have "above ao \<noteq> {}" using y_ao by auto
        moreover have "Min (above ao) = y" 
          and "Min (set (y # ys)) = y"
          using y_ao False ao by(auto intro!: Min_eqI simp add: proper_interval_Some2 not_less)
        moreover have "above ao - {y} = above (Some y)" using False y_ao
          by(auto simp add: proper_interval_Some2 intro: above_upclosed)
        moreover have "set ys - {y} = set ys" 
          using y_Min y_ao by(auto)
        ultimately show ?thesis using False y_ao
          by(simp)(subst (2) set_less_eq_aux_rec, simp_all)
      qed
    next
      case (3 ao x xs)
      from \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
      have xs: "sorted xs" "distinct xs" and x_Min: "\<forall>x'\<in>set xs. x < x'"
        by(auto simp add: less_le)
      show ?case
      proof(cases "proper_interval ao (Some x)")
        case True
        then obtain z where "z \<in> above ao" "z < x" by(auto simp add: proper_interval_Some2)
        hence "z \<in> - set (x # xs) \<inter> above ao" using x_Min by auto
        thus ?thesis using True by auto
      next
        case False
        note ao = \<open>set (x # xs) \<union> set [] \<subseteq> above ao\<close>
        hence x_ao: "x \<in> above ao" by simp
        from ao have "set xs \<union> set [] \<subseteq> above (Some x)" using x_Min by auto
        with xs \<open>sorted []\<close> \<open>distinct []\<close> 
        have "Compl_set_less_eq_aux (Some x) xs [] \<longleftrightarrow>
          - set xs \<inter> above (Some x) \<sqsubseteq>' set []"
          by(rule "3.IH")
        moreover have "- set (x # xs) \<inter> above ao = - set xs \<inter> above (Some x)" 
          using False x_ao by(auto simp add: proper_interval_Some2 intro: above_upclosed)
        ultimately show ?thesis using False by simp
      qed
    next
      case (4 ao x xs y ys)
      note ao = \<open>set (x # xs) \<union> set (y # ys) \<subseteq> above ao\<close>
      hence x_ao: "x \<in> above ao" and y_ao: "y \<in> above ao" by simp_all
      note xxs = \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
      hence xs: "sorted xs" "distinct xs" and x_Min: "\<forall>x'\<in>set xs. x < x'"
        by(auto simp add: less_le)
      note yys = \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
      hence ys: "sorted ys" "distinct ys" and y_Min: "\<forall>y'\<in>set ys. y < y'"
        by(auto simp add: less_le)
      let ?lhs = "- set (x # xs) \<inter> above ao" and ?rhs = "set (y # ys)"
      show ?case
      proof(cases "x < y")
        case True
        show ?thesis
        proof(cases "proper_interval ao (Some x)")
          case True
          hence "\<not> ?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>x < y\<close>
            by -(erule proper_interval_not_set_less_eq_auxI, auto)
          thus ?thesis using True \<open>x < y\<close> by simp
        next
          case False
          have "set xs \<union> set (y # ys) \<subseteq> above (Some x)" 
            using ao x_Min y_Min True by auto
          with True xs yys
          have "Compl_set_less_eq_aux (Some x) xs (y # ys) \<longleftrightarrow> 
            - set xs \<inter> above (Some x) \<sqsubseteq>' set (y # ys)"
            by(rule "4.IH")
          moreover have "- set xs \<inter> above (Some x) = ?lhs"
            using x_ao False by(auto intro: above_upclosed simp add: proper_interval_Some2)
          ultimately show ?thesis using False True by simp
        qed
      next
        case False
        show ?thesis
        proof(cases "y < x")
          case True
          show ?thesis
          proof(cases "proper_interval ao (Some y)")
            case True
            hence "\<not> ?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>y < x\<close>
              by -(erule proper_interval_not_set_less_eq_auxI, auto)
            thus ?thesis using True \<open>y < x\<close> \<open>\<not> x < y\<close> by simp
          next
            case False
            from ao True x_Min y_Min 
            have "set (x # xs) \<union> set ys \<subseteq> above (Some y)" by auto
            with \<open>\<not> x < y\<close> True xxs ys
            have "Compl_set_less_eq_aux (Some y) (x # xs) ys \<longleftrightarrow>
              - set (x # xs) \<inter> above (Some y) \<sqsubseteq>' set ys"
              by(rule "4.IH")
            moreover have "y \<in> ?lhs" using True x_Min y_ao by auto
            hence "?lhs \<noteq> {}" by auto
            moreover have "Min ?lhs = y" using True False x_Min y_ao
              by(auto intro!: Min_eqI simp add: not_le not_less proper_interval_Some2)
            moreover have "Min ?rhs = y" using y_Min y_ao by(auto intro!: Min_eqI)
            moreover have "- set (x # xs) \<inter> above (Some y) = ?lhs - {y}"
              using y_ao False by(auto intro: above_upclosed simp add: proper_interval_Some2)
            moreover have "set ys = set ys - {y}"
              using y_ao y_Min by(auto intro: above_upclosed)
            ultimately show ?thesis using True False \<open>\<not> x < y\<close> y_ao
              by(simp)(subst (2) set_less_eq_aux_rec, simp_all)
          qed
        next
          case False
          with \<open>\<not> x < y\<close> have "x = y" by auto
          { assume "proper_interval ao (Some y)"
            hence "\<not> ?lhs \<sqsubseteq>' ?rhs" using x_Min y_Min \<open>x = y\<close>
              by -(erule proper_interval_not_set_less_eq_auxI, auto) }
          moreover
          { assume "\<not> ?lhs \<sqsubseteq>' ?rhs"
            also have "?rhs = set (y # ys) \<inter> above ao"
              using ao by auto
            finally obtain z where "z \<in> above ao" "z < y" 
              using \<open>x = y\<close> x_ao x_Min[unfolded Ball_def]
              by(fastforce simp add: set_less_eq_aux_def set_less_aux_def simp add: less_le not_le dest!: bspec[where x=y])
            hence "proper_interval ao (Some y)" 
              by(auto simp add: proper_interval_Some2) }
          ultimately show ?thesis using \<open>x = y\<close> by auto
        qed
      qed
    qed }
  from this[of None] show ?Compl1 by simp
qed

lemma set_less_aux_Compl_iff:
  "set_less_aux_Compl ao xs ys \<longleftrightarrow> set_less_eq_aux_Compl ao xs ys \<and> \<not> Compl_set_less_eq_aux ao ys xs"
by(induct ao xs ys rule: set_less_aux_Compl.induct)(auto simp add: not_less_iff_gr_or_eq)

lemma Compl_set_less_aux_Compl_iff:
  "Compl_set_less_aux ao xs ys \<longleftrightarrow> Compl_set_less_eq_aux ao xs ys \<and> \<not> set_less_eq_aux_Compl ao ys xs"
by(induct ao xs ys rule: Compl_set_less_aux.induct)(auto simp add: not_less_iff_gr_or_eq)

theorem assumes fin: "finite (UNIV :: 'a set)"
  and xs: "sorted xs" "distinct xs"
  and ys: "sorted ys" "distinct ys"
  shows set_less_aux_Compl2_conv_set_less_aux_Compl:
  "set xs \<sqsubset>' - set ys \<longleftrightarrow> set_less_aux_Compl None xs ys" (is ?Compl2)
  and Compl1_set_less_aux_conv_Compl_set_less_aux:
  "- set xs \<sqsubset>' set ys \<longleftrightarrow> Compl_set_less_aux None xs ys" (is ?Compl1)
using assms
by(simp_all only: set_less_aux_conv_set_less_eq_aux set_less_aux_Compl_iff Compl_set_less_aux_Compl_iff set_less_eq_aux_Compl2_conv_set_less_eq_aux_Compl Compl1_set_less_eq_aux_conv_Compl_set_less_eq_aux)

end

subsection \<open>Implementation of proper intervals for sets\<close>

definition length_last :: "'a list \<Rightarrow> nat \<times> 'a"
where "length_last xs = (length xs, last xs)"

lemma length_last_Nil [code]: "length_last [] = (0, undefined)"
by(simp add: length_last_def last_def)

lemma length_last_Cons_code [symmetric, code]:
  "fold (\<lambda>x (n, _) . (n + 1, x)) xs (1, x) = length_last (x # xs)"
by(induct xs rule: rev_induct)(simp_all add: length_last_def)

context proper_intrvl begin

fun exhaustive_above :: "'a \<Rightarrow> 'a list \<Rightarrow> bool" where
  "exhaustive_above x [] \<longleftrightarrow> \<not> proper_interval (Some x) None"
| "exhaustive_above x (y # ys) \<longleftrightarrow> \<not> proper_interval (Some x) (Some y) \<and> exhaustive_above y ys"

fun exhaustive :: "'a list \<Rightarrow> bool" where 
  "exhaustive [] = False"
| "exhaustive (x # xs) \<longleftrightarrow> \<not> proper_interval None (Some x) \<and> exhaustive_above x xs"

fun proper_interval_set_aux :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "proper_interval_set_aux xs [] \<longleftrightarrow> False"
| "proper_interval_set_aux [] (y # ys) \<longleftrightarrow> ys \<noteq> [] \<or> proper_interval (Some y) None"
| "proper_interval_set_aux (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then False
   else if y < x then proper_interval (Some y) (Some x) \<or> ys \<noteq> [] \<or> \<not> exhaustive_above x xs
   else proper_interval_set_aux xs ys)"

fun proper_interval_set_Compl_aux :: "'a option \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "proper_interval_set_Compl_aux ao n [] [] \<longleftrightarrow>
   CARD('a) > n + 1"
| "proper_interval_set_Compl_aux ao n [] (y # ys) \<longleftrightarrow>
   (let m = CARD('a) - n; (len_y, y') = length_last (y # ys)
    in m \<noteq> len_y \<and> (m = len_y + 1 \<longrightarrow> \<not> proper_interval (Some y') None))"
| "proper_interval_set_Compl_aux ao n (x # xs) [] \<longleftrightarrow>
   (let m = CARD('a) - n; (len_x, x') = length_last (x # xs)
    in m \<noteq> len_x \<and> (m = len_x + 1 \<longrightarrow> \<not> proper_interval (Some x') None))"
| "proper_interval_set_Compl_aux ao n (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then 
     proper_interval ao (Some x) \<or> 
     proper_interval_set_Compl_aux (Some x) (n + 1) xs (y # ys)
   else if y < x then 
     proper_interval ao (Some y) \<or> 
     proper_interval_set_Compl_aux (Some y) (n + 1) (x # xs) ys
   else proper_interval ao (Some x) \<and> 
     (let m = card (UNIV :: 'a set) - n in m - length ys \<noteq> 2 \<or> m - length xs \<noteq> 2))"

fun proper_interval_Compl_set_aux :: "'a option \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
where
  "proper_interval_Compl_set_aux ao (x # xs) (y # ys) \<longleftrightarrow>
  (if x < y then 
     \<not> proper_interval ao (Some x) \<and> 
     proper_interval_Compl_set_aux (Some x) xs (y # ys)
   else if y < x then
     \<not> proper_interval ao (Some y) \<and>
     proper_interval_Compl_set_aux (Some y) (x # xs) ys
   else \<not> proper_interval ao (Some x) \<and> (ys = [] \<longrightarrow> xs \<noteq> []))"
| "proper_interval_Compl_set_aux ao _ _ \<longleftrightarrow> False"

end

lemmas [code] = 
  proper_intrvl.exhaustive_above.simps
  proper_intrvl.exhaustive.simps
  proper_intrvl.proper_interval_set_aux.simps
  proper_intrvl.proper_interval_set_Compl_aux.simps
  proper_intrvl.proper_interval_Compl_set_aux.simps

context linorder_proper_interval begin

lemma exhaustive_above_iff:
  "\<lbrakk> sorted xs; distinct xs; \<forall>x'\<in>set xs. x < x' \<rbrakk> \<Longrightarrow> exhaustive_above x xs \<longleftrightarrow> set xs = {z. z > x}"
proof(induction x xs rule: exhaustive_above.induct)
  case 1 thus ?case by(simp add: proper_interval_simps)
next
  case (2 x y ys)
  from \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
  have ys: "sorted ys" "distinct ys" and y: "\<forall>y'\<in>set ys. y < y'"
    by(auto simp add: less_le)
  hence "exhaustive_above y ys = (set ys = {z. y < z})" by(rule "2.IH")
  moreover from \<open>\<forall>y'\<in>set (y # ys). x < y'\<close> have "x < y" by simp
  ultimately show ?case using y 
    by(fastforce simp add: proper_interval_simps)
qed

lemma exhaustive_correct:
  assumes "sorted xs" "distinct xs"
  shows "exhaustive xs \<longleftrightarrow> set xs = UNIV"
proof(cases xs)
  case Nil thus ?thesis by auto
next
  case Cons
  show ?thesis using assms unfolding Cons exhaustive.simps
    apply(subst exhaustive_above_iff)
    apply(auto simp add: less_le proper_interval_simps not_less)
    by (metis List.set_simps(2) UNIV_I eq_iff set_ConsD)
qed

theorem proper_interval_set_aux:
  assumes fin: "finite (UNIV :: 'a set)"
  and xs: "sorted xs" "distinct xs" 
  and ys: "sorted ys" "distinct ys"
  shows "proper_interval_set_aux xs ys \<longleftrightarrow> (\<exists>A. set xs \<sqsubset>' A \<and> A \<sqsubset>' set ys)"
proof -
  note [simp] = finite_subset[OF subset_UNIV fin]
  show ?thesis using xs ys
  proof(induction xs ys rule: proper_interval_set_aux.induct)
    case 1 thus ?case by simp
  next
    case (2 y ys)
    hence "\<forall>y'\<in>set ys. y < y'" by(auto simp add: less_le)
    thus ?case
      by(cases ys)(auto simp add: proper_interval_simps set_less_aux_singleton_iff intro: psubset_finite_imp_set_less_aux)
  next
    case (3 x xs y ys)
    from \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
    have xs: "sorted xs" "distinct xs" and x: "\<forall>x'\<in>set xs. x < x'"
      by(auto simp add: less_le)
    from \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
    have ys: "sorted ys" "distinct ys" and y: "\<forall>y'\<in>set ys. y < y'"
      by(auto simp add: less_le)
    have Minxxs: "Min (set (x # xs)) = x" and xnxs: "x \<notin> set xs"
      using x by(auto intro!: Min_eqI)
    have Minyys: "Min (set (y # ys)) = y" and ynys: "y \<notin> set ys" 
      using y by(auto intro!: Min_eqI)
    show ?case
    proof(cases "x < y")
      case True
      hence "set (y # ys) \<sqsubset>' set (x # xs)" using Minxxs Minyys
        by -(rule set_less_aux_Min_antimono, simp_all)
      thus ?thesis using True by(auto dest: set_less_aux_trans set_less_aux_antisym)
    next
      case False
      show ?thesis
      proof(cases "y < x")
        case True
        { assume "proper_interval (Some y) (Some x)"
          then obtain z where z: "y < z" "z < x" by(auto simp add: proper_interval_simps)
          hence "set (x # xs) \<sqsubset>' {z}" using x
            by -(rule set_less_aux_Min_antimono, auto)
          moreover have "{z} \<sqsubset>' set (y # ys)" using z y Minyys
            by -(rule set_less_aux_Min_antimono, auto)
          ultimately have "\<exists>A. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' set (y # ys)" by blast }
        moreover
        { assume "ys \<noteq> []"
          hence "{y} \<sqsubset>' set (y # ys)" using y
            by -(rule psubset_finite_imp_set_less_aux, auto simp add: neq_Nil_conv)
          moreover have "set (x # xs) \<sqsubset>' {y}" using False True x
            by -(rule set_less_aux_Min_antimono, auto)
          ultimately have "\<exists>A. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' set (y # ys)" by blast }
        moreover
        { assume "\<not> exhaustive_above x xs"
          then obtain z where z: "z > x" "z \<notin> set xs" using x
            by(auto simp add: exhaustive_above_iff[OF xs x])
          let ?A = "insert z (set (x # xs))"
          have "set (x # xs) \<sqsubset>' ?A" using z
            by -(rule psubset_finite_imp_set_less_aux, auto)
          moreover have "?A \<sqsubset>' set (y # ys)" using Minyys False True z x
            by -(rule set_less_aux_Min_antimono, auto)
          ultimately have "\<exists>A. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' set (y # ys)" by blast }
        moreover
        { fix A
          assume A: "set (x # xs) \<sqsubset>' A" and A': "A \<sqsubset>' {y}"
            and pi: "\<not> proper_interval (Some y) (Some x)"
          from A have nempty: "A \<noteq> {}" by auto
          have "y \<notin> A"
          proof
            assume "y \<in> A"
            moreover with A' have "A \<noteq> {y}" by auto
            ultimately have "{y} \<sqsubset>' A" by -(rule psubset_finite_imp_set_less_aux, auto)
            with A' show False by(rule set_less_aux_antisym)
          qed
          have "y < Min A" unfolding not_le[symmetric]
          proof
            assume "Min A \<le> y"
            moreover have "Min A \<noteq> y" using \<open>y \<notin> A\<close> nempty by clarsimp
            ultimately have "Min A < Min {y}" by simp
            hence "{y} \<sqsubset>' A" by(rule set_less_aux_Min_antimono)(simp_all add: nempty)
            with A' show False by(rule set_less_aux_antisym)
          qed
          with pi nempty have "x \<le> Min A" by(auto simp add: proper_interval_simps)
          moreover
          from A obtain z where z: "z \<in> A" "z \<notin> set (x # xs)"
            by(auto simp add: set_less_aux_def)
          with \<open>x \<le> Min A\<close> nempty have "x < z" by auto
          with z have "\<not> exhaustive_above x xs"
            by(auto simp add: exhaustive_above_iff[OF xs x]) }
        ultimately show ?thesis using True False by fastforce
      next
        case False
        with \<open>\<not> x < y\<close> have "x = y" by auto
        from \<open>\<not> x < y\<close> False
        have "proper_interval_set_aux xs ys = (\<exists>A. set xs \<sqsubset>' A \<and> A \<sqsubset>' set ys)" 
          using xs ys by(rule "3.IH")
        also have "\<dots> = (\<exists>A. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' set (y # ys))"
          (is "?lhs = ?rhs")
        proof
          assume ?lhs
          then obtain A where A: "set xs \<sqsubset>' A" 
            and A': "A \<sqsubset>' set ys" by blast
          hence nempty: "A \<noteq> {}" "ys \<noteq> []" by auto
          let ?A = "insert y A"
          { assume "Min A \<le> y"
            also from y nempty have "y < Min (set ys)" by auto
            finally have "set ys \<sqsubset>' A" by(rule set_less_aux_Min_antimono)(simp_all add: nempty)
            with A' have False by(rule set_less_aux_antisym) }
          hence MinA: "y < Min A" by(metis not_le)
          with nempty have "y \<notin> A" by auto
          moreover
          with MinA nempty have MinyA: "Min ?A = y" by -(rule Min_eqI, auto)
          ultimately have A1: "set (x # xs) \<sqsubset>' ?A" using \<open>x = y\<close> A Minxxs xnxs
            by(subst set_less_aux_rec) simp_all
          moreover
          have "?A \<sqsubset>' set (y # ys)" using \<open>x = y\<close> MinyA \<open>y \<notin> A\<close> A' Minyys ynys
            by(subst set_less_aux_rec) simp_all
          ultimately show ?rhs by blast
        next
          assume "?rhs"
          then obtain A where A: "set (x # xs) \<sqsubset>' A"
            and A': "A \<sqsubset>' set (y # ys)" by blast
          let ?A = "A - {x}"
          from A have nempty: "A \<noteq> {}" by auto
          { assume "x < Min A"
            hence "Min (set (x # xs)) < Min A" unfolding Minxxs .
            hence "A \<sqsubset>' set (x # xs)"
              by(rule set_less_aux_Min_antimono) simp_all
            with A have False by(rule set_less_aux_antisym) }
          moreover
          { assume "Min A < x"
            hence "Min A < Min (set (y # ys))" unfolding \<open>x = y\<close> Minyys .
            hence "set (y # ys) \<sqsubset>' A" by(rule set_less_aux_Min_antimono)(simp_all add: nempty)
            with A' have False by(rule set_less_aux_antisym) }
          ultimately have MinA: "Min A = x" by(metis less_linear)
          hence "x \<in> A" using nempty by(metis Min_in \<open>finite A\<close>)
          
          from A nempty Minxxs xnxs have "set xs \<sqsubset>' ?A"
            by(subst (asm) set_less_aux_rec)(auto simp add: MinA)
          moreover from A' \<open>x = y\<close> nempty Minyys MinA ynys have "?A \<sqsubset>' set ys"
            by(subst (asm) set_less_aux_rec) simp_all
          ultimately show ?lhs by blast
        qed
        finally show ?thesis using \<open>x = y\<close> by simp
      qed
    qed
  qed
qed

lemma proper_interval_set_Compl_aux:
  assumes fin: "finite (UNIV :: 'a set)"
  and xs: "sorted xs" "distinct xs" 
  and ys: "sorted ys" "distinct ys" 
  shows "proper_interval_set_Compl_aux None 0 xs ys \<longleftrightarrow> (\<exists>A. set xs \<sqsubset>' A \<and> A \<sqsubset>' - set ys)"
proof -
  note [simp] = finite_subset[OF subset_UNIV fin]

  define above where "above = case_option UNIV (Collect \<circ> less)"
  have above_simps [simp]: "above None = UNIV" "\<And>x. above (Some x) = {y. x < y}"
    and above_upclosed: "\<And>x y ao. \<lbrakk> x \<in> above ao; x < y \<rbrakk> \<Longrightarrow> y \<in> above ao"
    and proper_interval_Some2: "\<And>x ao. proper_interval ao (Some x) \<longleftrightarrow> (\<exists>z\<in>above ao. z < x)"
    by(simp_all add: proper_interval_simps above_def split: option.splits)

  { fix ao n
    assume "set xs \<subseteq> above ao" "set ys \<subseteq> above ao"
    from xs \<open>set xs \<subseteq> above ao\<close> ys \<open>set ys \<subseteq> above ao\<close>
    have "proper_interval_set_Compl_aux ao (card (UNIV - above ao)) xs ys \<longleftrightarrow>
          (\<exists>A \<subseteq> above ao. set xs \<sqsubset>' A \<and> A \<sqsubset>' - set ys \<inter> above ao)"
    proof(induct ao n\<equiv>"card (UNIV - above ao)" xs ys rule: proper_interval_set_Compl_aux.induct)
      case (1 ao)
      have "card (UNIV - above ao) + 1 < CARD('a) \<longleftrightarrow> (\<exists>A \<subseteq> above ao. A \<noteq> {} \<and> A \<sqsubset>' above ao)"
        (is "?lhs \<longleftrightarrow> ?rhs")
      proof
        assume ?lhs
        hence "card (UNIV - (UNIV - above ao)) > 1" by(simp add: card_Diff_subset)
        from card_gt_1D[OF this]
        obtain x y where above: "x \<in> above ao" "y \<in> above ao"
          and neq: "x \<noteq> y" by blast
        hence "{x} \<sqsubset>' {x, y} \<inter> above ao"
          by(simp_all add: psubsetI psubset_finite_imp_set_less_aux)
        also have "\<dots> \<sqsubseteq>' above ao"
          by(auto intro: subset_finite_imp_set_less_eq_aux)
        finally show ?rhs using above by blast
      next
        assume ?rhs
        then obtain A where nempty: "A \<inter> above ao \<noteq> {}"
          and subset: "A \<subseteq> above ao"
          and less: "A \<sqsubset>' above ao" by blast
        from nempty obtain x where x: "x \<in> A" "x \<in> above ao" by blast
        show ?lhs
        proof(rule ccontr)
          assume "\<not> ?lhs"
          moreover have "CARD('a) \<ge> card (UNIV - above ao)" by(rule card_mono) simp_all
          moreover from card_Un_disjoint[of "UNIV - above ao" "above ao"]
          have "CARD('a) = card (UNIV - above ao) + card (above ao)" by auto
          ultimately have "card (above ao) = 1" using x
            by(cases "card (above ao)")(auto simp add: not_less_eq less_Suc_eq_le)
          with x have "above ao = {x}" unfolding card_eq_1_iff by auto
          moreover with x subset have A: "A = {x}" by auto
          ultimately show False using less by simp
        qed
      qed
      thus ?case by simp
    next
      case (2 ao y ys)
      note ys = \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close> \<open>set (y # ys) \<subseteq> above ao\<close>
      have len_ys: "length ys = card (set ys)"
        using ys by(auto simp add: List.card_set intro: sym)

      define m where "m = CARD('a) - card (UNIV - above ao)"
      have "CARD('a) = card (above ao) + card (UNIV - above ao)"
        using card_Un_disjoint[of "above ao" "UNIV - above ao"] by auto
      hence m_eq: "m = card (above ao)" unfolding m_def by simp
        
      have "m \<noteq> length ys + 1 \<and> (m = length ys + 2 \<longrightarrow> \<not> proper_interval (Some (last (y # ys))) None) \<longleftrightarrow>
        (\<exists>A \<subseteq> above ao. A \<noteq> {} \<and> A \<sqsubset>' - set (y # ys) \<inter> above ao)" (is "?lhs \<longleftrightarrow> ?rhs")
      proof
        assume ?lhs
        hence m: "m \<noteq> length ys + 1"
          and pi: "m = length ys + 2 \<Longrightarrow> \<not> proper_interval (Some (last (y # ys))) None"
          by simp_all
        have "length ys + 1 = card (set (y # ys))" using ys len_ys by simp
        also have "\<dots> \<le> m" unfolding m_eq by(rule card_mono)(simp, rule ys)
        finally have "length ys + 2 \<le> m" using m by simp
        show ?rhs
        proof(cases "m = length ys + 2")
          case True
          hence "card (UNIV - (UNIV - above ao) - set (y # ys)) = 1"
            using ys len_ys
            by(subst card_Diff_subset)(auto simp add: m_def card_Diff_subset)
          then obtain z where z: "z \<in> above ao" "z \<noteq> y" "z \<notin> set ys"
            unfolding card_eq_1_iff by auto
          from True have "\<not> proper_interval (Some (last (y # ys))) None" by(rule pi)
          hence "z \<le> last (y # ys)" by(simp add: proper_interval_simps not_less del: last.simps)
          moreover have ly: "last (y # ys) \<in> set (y # ys)" by(rule last_in_set) simp
          with z have "z \<noteq> last (y # ys)" by auto
          ultimately have "z < last (y # ys)" by simp
          hence "{last (y # ys)} \<sqsubset>' {z}"
            using z ly ys by(auto 4 3 simp add: set_less_aux_def)
          also have "\<dots> \<sqsubseteq>' - set (y # ys) \<inter> above ao"
            using z by(auto intro: subset_finite_imp_set_less_eq_aux)
          also have "{last (y # ys)} \<noteq> {}" using ly ys by blast
          moreover have "{last (y # ys)} \<subseteq> above ao" using ys by auto
          ultimately show ?thesis by blast
        next
          case False
          with \<open>length ys + 2 \<le> m\<close> ys len_ys
          have "card (UNIV - (UNIV - above ao) - set (y # ys)) > 1"
            by(subst card_Diff_subset)(auto simp add: card_Diff_subset m_def)
          from card_gt_1D[OF this]
          obtain x x' where x: "x \<in> above ao" "x \<noteq> y" "x \<notin> set ys"
            and x': "x' \<in> above ao" "x' \<noteq> y" "x' \<notin> set ys"
            and neq: "x \<noteq> x'" by auto
          hence "{x} \<sqsubset>' {x, x'} \<inter> above ao"
            by(simp_all add: psubsetI psubset_finite_imp_set_less_aux)
          also have "\<dots> \<sqsubseteq>' - set (y # ys) \<inter> above ao" using x x' ys
            by(auto intro: subset_finite_imp_set_less_eq_aux)
          also have "{x} \<inter> above ao \<noteq> {}" using x by simp
          ultimately show ?rhs by blast
        qed
      next
        assume ?rhs
        then obtain A where nempty: "A \<noteq> {}"
          and less: "A \<sqsubset>' - set (y # ys) \<inter> above ao"
          and subset: "A \<subseteq> above ao" by blast
        have "card (set (y # ys)) \<le> card (above ao)" using ys(3) by(simp add: card_mono)
        hence "length ys + 1 \<le> m" unfolding m_eq using ys by(simp add: len_ys)
        have "m \<noteq> length ys + 1"
        proof
          assume "m = length ys + 1"
          hence "card (above ao) \<le> card (set (y # ys))"
            unfolding m_eq using ys len_ys by auto
          from card_seteq[OF _ _ this] ys have "set (y # ys) = above ao" by simp
          with nempty less show False by(auto simp add: set_less_aux_def)
        qed
        moreover
        { assume "m = length ys + 2"
          hence "card (above ao - set (y # ys)) = 1"
            using ys len_ys m_eq by(auto simp add: card_Diff_subset)
          then obtain z where z: "above ao - set (y # ys) = {z}"
            unfolding card_eq_1_iff ..
          hence eq_z: "- set (y # ys) \<inter> above ao = {z}" by auto
          with less have "A \<sqsubset>' {z}" by simp
          have "\<not> proper_interval (Some (last (y # ys))) None"
          proof
            assume "proper_interval (Some (last (y # ys))) None"
            then obtain z' where z': "last (y # ys) < z'"
              by(clarsimp simp add: proper_interval_simps)
            have "last (y # ys) \<in> set (y # ys)" by(rule last_in_set) simp
            with ys z' have "z' \<in> above ao" "z' \<notin> set (y # ys)"
              by(auto simp del: last.simps sorted.simps(2) intro: above_upclosed dest: sorted_last)
            with eq_z have "z = z'" by fastforce
            from z' have "\<And>x. x \<in> set (y # ys) \<Longrightarrow> x < z'" using ys
              by(auto dest: sorted_last simp del: sorted.simps(2))
            with eq_z \<open>z = z'\<close>
            have "\<And>x. x \<in> above ao \<Longrightarrow> x \<le> z'" by(fastforce)
            with \<open>A \<sqsubset>' {z}\<close> nempty \<open>z = z'\<close> subset
            show False by(auto simp add: set_less_aux_def)
          qed }
        ultimately show ?lhs by simp
      qed
      thus ?case by(simp add: length_last_def m_def Let_def)
    next
      case (3 ao x xs)
      note xs = \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close> \<open>set (x # xs) \<subseteq> above ao\<close>
      have len_xs: "length xs = card (set xs)"
        using xs by(auto simp add: List.card_set intro: sym)
      
      define m where "m = CARD('a) - card (UNIV - above ao)"
      have "CARD('a) = card (above ao) + card (UNIV - above ao)"
        using card_Un_disjoint[of "above ao" "UNIV - above ao"] by auto
      hence m_eq: "m = card (above ao)" unfolding m_def by simp
      have "m \<noteq> length xs + 1 \<and> (m = length xs + 2 \<longrightarrow> \<not> proper_interval (Some (last (x # xs))) None) \<longleftrightarrow>
        (\<exists>A \<subseteq> above ao. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' above ao)" (is "?lhs \<longleftrightarrow> ?rhs")
      proof
        assume ?lhs
        hence m: "m \<noteq> length xs + 1"
          and pi: "m = length xs + 2 \<Longrightarrow> \<not> proper_interval (Some (last (x # xs))) None"
          by simp_all
        have "length xs + 1 = card (set (x # xs))" using xs len_xs by simp
        also have "\<dots> \<le> m" unfolding m_eq by(rule card_mono)(simp, rule xs)
        finally have "length xs + 2 \<le> m" using m by simp
        show ?rhs
        proof(cases "m = length xs + 2")
          case True
          hence "card (UNIV - (UNIV - above ao) - set (x # xs)) = 1"
            using xs len_xs
            by(subst card_Diff_subset)(auto simp add: m_def card_Diff_subset)
          then obtain z where z: "z \<in> above ao" "z \<noteq> x" "z \<notin> set xs"
            unfolding card_eq_1_iff by auto
          define A where "A = insert z {y. y \<in> set (x # xs) \<and> y < z}"

          from True have "\<not> proper_interval (Some (last (x # xs))) None" by(rule pi)
          hence "z \<le> last (x # xs)" by(simp add: proper_interval_simps not_less del: last.simps)
          moreover have lx: "last (x # xs) \<in> set (x # xs)" by(rule last_in_set) simp
          with z have "z \<noteq> last (x # xs)" by auto
          ultimately have "z < last (x # xs)" by simp
          hence "set (x # xs) \<sqsubset>' A" 
            using z xs by(auto simp add: A_def set_less_aux_def intro: rev_bexI[where x=z])
          moreover have "last (x # xs) \<notin> A" using xs \<open>z < last (x # xs)\<close>
            by(auto simp add: A_def simp del: last.simps)
          hence "A \<subset> insert (last (x # xs)) A" by blast
          hence less': "A \<sqsubset>' insert (last (x # xs)) A"
            by(rule psubset_finite_imp_set_less_aux) simp
          have "\<dots> \<subseteq> above ao" using xs lx z
            by(auto simp del: last.simps simp add: A_def)
          hence "insert (last (x # xs)) A \<sqsubseteq>' above ao"
            by(auto intro: subset_finite_imp_set_less_eq_aux)
          with less' have "A \<sqsubset>' above ao"
            by(rule set_less_trans_set_less_eq)
          moreover have "A \<subseteq> above ao" using xs z by(auto simp add: A_def)
          ultimately show ?thesis by blast
        next
          case False
          with \<open>length xs + 2 \<le> m\<close> xs len_xs
          have "card (UNIV - (UNIV - above ao) - set (x # xs)) > 1"
            by(subst card_Diff_subset)(auto simp add: card_Diff_subset m_def)
          from card_gt_1D[OF this]
          obtain y y' where y: "y \<in> above ao" "y \<noteq> x" "y \<notin> set xs"
            and y': "y' \<in> above ao" "y' \<noteq> x" "y' \<notin> set xs"
            and neq: "y \<noteq> y'" by auto
          define A where "A = insert y (set (x # xs) \<inter> above ao)"
          hence "set (x # xs) \<subset> A" using y xs by auto
          hence "set (x # xs) \<sqsubset>' \<dots>"
            by(fastforce intro: psubset_finite_imp_set_less_aux)
          moreover have *: "\<dots> \<subset> above ao"
            using y y' neq by(auto simp add: A_def)
          moreover from * have "A \<sqsubset>' above ao"
            by(auto intro: psubset_finite_imp_set_less_aux)
          ultimately show ?thesis by blast
        qed
      next
        assume ?rhs
        then obtain A where lessA: "set (x # xs) \<sqsubset>' A"
          and Aless: "A \<sqsubset>' above ao" and subset: "A \<subseteq> above ao" by blast
        have "card (set (x # xs)) \<le> card (above ao)" using xs(3) by(simp add: card_mono)
        hence "length xs + 1 \<le> m" unfolding m_eq using xs by(simp add: len_xs)
        have "m \<noteq> length xs + 1"
        proof
          assume "m = length xs + 1"
          hence "card (above ao) \<le> card (set (x # xs))"
            unfolding m_eq using xs len_xs by auto
          from card_seteq[OF _ _ this] xs have "set (x # xs) = above ao" by simp
          with lessA Aless show False by(auto dest: set_less_aux_antisym)
        qed
        moreover
        { assume "m = length xs + 2"
          hence "card (above ao - set (x # xs)) = 1"
            using xs len_xs m_eq by(auto simp add: card_Diff_subset)
          then obtain z where z: "above ao - set (x # xs) = {z}"
            unfolding card_eq_1_iff ..
          have "\<not> proper_interval (Some (last (x # xs))) None"
          proof
            assume "proper_interval (Some (last (x # xs))) None"
            then obtain z' where z': "last (x # xs) < z'"
              by(clarsimp simp add: proper_interval_simps)
            have "last (x # xs) \<in> set (x # xs)" by(rule last_in_set) simp
            with xs z' have "z' \<in> above ao" "z' \<notin> set (x # xs)"
              by(auto simp del: last.simps sorted.simps(2) intro: above_upclosed dest: sorted_last)
            with z have "z = z'" by fastforce
            from z' have y_less: "\<And>y. y \<in> set (x # xs) \<Longrightarrow> y < z'" using xs
              by(auto simp del: sorted.simps(2) dest: sorted_last)
            with z \<open>z = z'\<close> have "\<And>y. y \<in> above ao \<Longrightarrow> y \<le> z'" by(fastforce)
            
            from lessA subset obtain y where y: "y \<in> A" "y \<in> above ao" "y \<notin> set (x # xs)"
              and min: "\<And>y'. \<lbrakk> y' \<in> set (x # xs); y' \<in> above ao; y' \<notin> A \<rbrakk> \<Longrightarrow> y \<le> y'"
              by(auto simp add: set_less_aux_def)
            with z \<open>z = z'\<close> have "y = z'" by auto
            have "set (x # xs) \<subseteq> A"
            proof
              fix y'
              assume y': "y' \<in> set (x # xs)"
              show "y' \<in> A"
              proof(rule ccontr)
                assume "y' \<notin> A"
                from y' xs have "y' \<in> above ao" by auto
                with y' have "y \<le> y'" using \<open>y' \<notin> A\<close> by(rule min)
                moreover from y' have "y' < z'" by(rule y_less)
                ultimately show False using \<open>y = z'\<close> by simp
              qed
            qed
            moreover from z xs have "above ao = insert z (set (x # xs))" by auto
            ultimately have "A = above ao" using y \<open>y = z'\<close> \<open>z = z'\<close> subset by auto
            with Aless show False by simp
          qed }
        ultimately show ?lhs by simp
      qed
      thus ?case by(simp add: length_last_def m_def Let_def del: last.simps)
    next
      case (4 ao x xs y ys)
      note xxs = \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
        and yys = \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
        and xxs_above = \<open>set (x # xs) \<subseteq> above ao\<close>
        and yys_above = \<open>set (y # ys) \<subseteq> above ao\<close>
      from xxs have xs: "sorted xs" "distinct xs" and x_Min: "\<forall>x'\<in>set xs. x < x'"
        by(auto simp add: less_le)
      from yys have ys: "sorted ys" "distinct ys" and y_Min: "\<forall>y'\<in>set ys. y < y'"
        by(auto simp add: less_le)

      have len_xs: "length xs = card (set xs)"
        using xs by(auto simp add: List.card_set intro: sym)
      have len_ys: "length ys = card (set ys)"
        using ys by(auto simp add: List.card_set intro: sym)

      show ?case
      proof(cases "x < y")
        case True

        have "proper_interval ao (Some x) \<or>
          proper_interval_set_Compl_aux (Some x) (card (UNIV - above ao) + 1) xs (y # ys) \<longleftrightarrow>
          (\<exists>A \<subseteq> above ao. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' - set (y # ys) \<inter> above ao)"
          (is "?lhs \<longleftrightarrow> ?rhs")
        proof(cases "proper_interval ao (Some x)")
          case True
          then obtain z where z: "z \<in> above ao" "z < x"
            by(clarsimp simp add: proper_interval_Some2)
          moreover with xxs have "\<forall>x'\<in>set xs. z < x'" by(auto)
          ultimately have "set (x # xs) \<sqsubset>' {z}"
            by(auto simp add: set_less_aux_def intro!: bexI[where x=z])
          moreover {
            from z yys \<open>x < y\<close> have "z < y" "\<forall>y'\<in>set ys. z < y'"
              by(auto)
            hence subset: "{z} \<subseteq> - set (y # ys) \<inter> above ao"
              using ys \<open>x < y\<close> z by auto
            moreover have "x \<in> \<dots>" using yys xxs \<open>x < y\<close> xxs_above by(auto)
            ultimately have "{z} \<subset> \<dots>" using \<open>z < x\<close> by fastforce
            hence "{z} \<sqsubset>' \<dots>"
              by(fastforce intro: psubset_finite_imp_set_less_aux) }
          moreover have "{z} \<subseteq> above ao" using z by simp
          ultimately have ?rhs by blast
          thus ?thesis using True by simp
        next
          case False
          hence above_eq: "above ao = insert x (above (Some x))" using xxs_above
            by(auto simp add: proper_interval_Some2 intro: above_upclosed)
          moreover have "card (above (Some x)) < CARD('a)"
            by(rule psubset_card_mono)(auto)
          ultimately have card_eq: "card (UNIV - above ao) + 1 = card (UNIV - above (Some x))"
            by(simp add: card_Diff_subset)
          from xxs_above x_Min have xs_above: "set xs \<subseteq> above (Some x)" by(auto)
          from \<open>x < y\<close> y_Min have "set (y # ys) \<subseteq> above (Some x)" by(auto)
          with \<open>x < y\<close> card_eq xs xs_above yys
          have "proper_interval_set_Compl_aux (Some x) (card (UNIV - above ao) + 1) xs (y # ys) \<longleftrightarrow>
               (\<exists>A \<subseteq> above (Some x). set xs \<sqsubset>' A \<and> A \<sqsubset>' - set (y # ys) \<inter> above (Some x))"
            by(subst card_eq)(rule 4)
          also have "\<dots> \<longleftrightarrow> ?rhs" (is "?lhs' \<longleftrightarrow> _")
          proof
            assume ?lhs'
            then obtain A where less_A: "set xs \<sqsubset>' A"
              and A_less: "A \<sqsubset>' - set (y # ys) \<inter> above (Some x)"
              and subset: "A \<subseteq> above (Some x)" by blast
            let ?A = "insert x A"

            have Min_A': "Min ?A = x" using xxs_above False subset
              by(auto intro!: Min_eqI simp add: proper_interval_Some2)
            moreover have "Min (set (x # xs)) = x"
              using x_Min by(auto intro!: Min_eqI)
            moreover have Amx: "A - {x} = A"
              using False subset 
              by(auto simp add: proper_interval_Some2 intro: above_upclosed)
            moreover have "set xs - {x} = set xs" using x_Min by auto
            ultimately have less_A': "set (x # xs) \<sqsubset>' ?A"
              using less_A xxs_above x_Min by(subst set_less_aux_rec) simp_all
            
            have "x \<in> - insert y (set ys) \<inter> above ao"
              using \<open>x < y\<close> xxs_above y_Min by auto
            hence "- insert y (set ys) \<inter> above ao \<noteq> {}" by auto
            moreover have "Min (- insert y (set ys) \<inter> above ao) = x"
              using yys y_Min xxs_above \<open>x < y\<close> False
              by(auto intro!: Min_eqI simp add: proper_interval_Some2)
            moreover have "- set (y # ys) \<inter> above ao - {x} = - set (y # ys) \<inter> above (Some x)"
              using yys_above False xxs_above
              by(auto simp add: proper_interval_Some2 intro: above_upclosed)
            ultimately have A'_less: "?A \<sqsubset>' - set (y # ys) \<inter> above ao"
              using Min_A' A_less Amx xxs_above by(subst set_less_aux_rec) simp_all
            moreover have "?A \<subseteq> above ao" using subset xxs_above by(auto intro: above_upclosed)
            ultimately show ?rhs using less_A' by blast
          next
            assume ?rhs
            then obtain A where less_A: "set (x # xs) \<sqsubset>' A"
              and A_less: "A \<sqsubset>' - set (y # ys) \<inter> above ao" 
              and subset: "A \<subseteq> above ao" by blast
            let ?A = "A - {x}"

            from less_A subset xxs_above have "set (x # xs) \<inter> above ao \<sqsubset>' A \<inter> above ao"
              by(simp add: Int_absorb2)
            with False xxs_above subset have "x \<in> A"
              by(auto simp add: set_less_aux_def proper_interval_Some2)
            hence "\<dots> \<noteq> {}" by auto
            moreover from \<open>x \<in> A\<close> False subset
            have Min_A: "Min A = x"
              by(auto intro!: Min_eqI simp add: proper_interval_Some2 not_less)
            moreover have "Min (set (x # xs)) = x"
              using x_Min by(auto intro!: Min_eqI)
            moreover have eq_A: "?A \<subseteq> above (Some x)"
              using xxs_above False subset 
              by(fastforce simp add: proper_interval_Some2 not_less intro: above_upclosed)
            moreover have "set xs - {x} = set xs"
              using x_Min by(auto)
            ultimately have less_A': "set xs \<sqsubset>' ?A"
              using xxs_above less_A by(subst (asm) set_less_aux_rec)(simp_all cong: conj_cong)
            
            have "x \<in> - insert y (set ys) \<inter> above ao"
              using \<open>x < y\<close> xxs_above y_Min by auto
            hence "- insert y (set ys) \<inter> above ao \<noteq> {}" by auto
            moreover have "Min (- set (y # ys) \<inter> above ao) = x"
              using yys y_Min xxs_above \<open>x < y\<close> False
              by(auto intro!: Min_eqI simp add: proper_interval_Some2)
            moreover have "- set (y # ys) \<inter> above (Some x) = - set (y # ys) \<inter> above ao - {x}"
              by(auto simp add: above_eq)
            ultimately have "?A \<sqsubset>' - set (y # ys) \<inter> above (Some x)"
              using A_less \<open>A \<noteq> {}\<close> eq_A Min_A
              by(subst (asm) set_less_aux_rec) simp_all
            
            with less_A' eq_A show ?lhs' by blast
          qed
          finally show ?thesis using False by simp
        qed
        thus ?thesis using True by simp
      next
        case False
        show ?thesis
        proof(cases "y < x")
          case True
          have "proper_interval ao (Some y) \<or> 
                proper_interval_set_Compl_aux (Some y) (card (UNIV - above ao) + 1) (x # xs) ys \<longleftrightarrow>
               (\<exists>A \<subseteq> above ao. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' - set (y # ys) \<inter> above ao)"
            (is "?lhs \<longleftrightarrow> ?rhs")
          proof(cases "proper_interval ao (Some y)")
            case True
            then obtain z where z: "z \<in> above ao" "z < y"
              by(clarsimp simp add: proper_interval_Some2)
            from xxs \<open>y < x\<close> have "\<forall>x'\<in>set (x # xs). y < x'" by(auto)
            hence less_A: "set (x # xs) \<sqsubset>' {y}" 
              by(auto simp add: set_less_aux_def intro!: bexI[where x=y])

            have "{y} \<sqsubset>' {z}"
              using z y_Min by(auto simp add: set_less_aux_def intro: bexI[where x=z])
            also have "\<dots> \<subseteq> - set (y # ys) \<inter> above ao" using z y_Min by auto
            hence "{z} \<sqsubseteq>' \<dots>" by(auto intro: subset_finite_imp_set_less_eq_aux)
            finally have "{y} \<sqsubset>' \<dots>" .
            moreover have "{y} \<subseteq> above ao" using yys_above by auto
            ultimately have ?rhs using less_A by blast
            thus ?thesis using True by simp
          next
            case False
            hence above_eq: "above ao = insert y (above (Some y))" using yys_above
              by(auto simp add: proper_interval_Some2 intro: above_upclosed)
            moreover have "card (above (Some y)) < CARD('a)"
              by(rule psubset_card_mono)(auto)
            ultimately have card_eq: "card (UNIV - above ao) + 1 = card (UNIV - above (Some y))"
              by(simp add: card_Diff_subset)
            from yys_above y_Min have ys_above: "set ys \<subseteq> above (Some y)" by(auto)

            have eq_ys: "- set ys \<inter> above (Some y) = - set (y # ys) \<inter> above ao"
              by(auto simp add: above_eq)

            from \<open>y < x\<close> x_Min have "set (x # xs) \<subseteq> above (Some y)" by(auto)
            with \<open>\<not> x < y\<close> \<open>y < x\<close> card_eq xxs ys ys_above
            have "proper_interval_set_Compl_aux (Some y) (card (UNIV - above ao) + 1) (x # xs) ys \<longleftrightarrow>
              (\<exists>A \<subseteq> above (Some y). set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' - set ys \<inter> above (Some y))"
              by(subst card_eq)(rule 4)
            also have "\<dots> \<longleftrightarrow> ?rhs" (is "?lhs' \<longleftrightarrow> _")
            proof
              assume ?lhs'
              then obtain A where "set (x # xs) \<sqsubset>' A" and subset: "A \<subseteq> above (Some y)"
                and "A \<sqsubset>' - set ys \<inter> above (Some y)" by blast
              moreover from subset have "A - {y} = A" by auto
              ultimately have "set (x # xs) \<sqsubset>' A - {y}"
                and "A - {y} \<sqsubset>' - set (y # ys) \<inter> above ao"
                using eq_ys by simp_all
              moreover from subset have "A - {y} \<subseteq> above ao"
                using yys_above by(auto intro: above_upclosed)
              ultimately show ?rhs by blast
            next
              assume ?rhs
              then obtain A where "set (x # xs) \<sqsubset>' A" 
                and A_less: "A \<sqsubset>' - set (y # ys) \<inter> above ao" 
                and subset: "A \<subseteq> above ao" by blast
              moreover
              from A_less False yys_above have "y \<notin> A"
                by(auto simp add: set_less_aux_def proper_interval_Some2 not_less)
              ultimately have "set (x # xs) \<sqsubset>' A"
                and "A \<sqsubset>' - set ys \<inter> above (Some y)"
                using eq_ys by simp_all
              moreover from \<open>y \<notin> A\<close> subset above_eq have "A \<subseteq> above (Some y)" by auto
              ultimately show ?lhs' by blast
            qed
            finally show ?thesis using False by simp
          qed
          with False True show ?thesis by simp
        next
          case False
          with \<open>\<not> x < y\<close> have "x = y" by simp
          have "proper_interval ao (Some x) \<and> 
                (CARD('a) - (card (UNIV - above ao) + length ys) \<noteq> 2 \<or>
                 CARD('a) - (card (UNIV - above ao) + length xs) \<noteq> 2) \<longleftrightarrow>
               (\<exists>A \<subseteq> above ao. set (x # xs) \<sqsubset>' A \<and> A \<sqsubset>' - set (y # ys) \<inter> above ao)"
            (is "?below \<and> ?card \<longleftrightarrow> ?rhs")
          proof(cases "?below")
            case False
            hence "- set (y # ys) \<inter> above ao \<sqsubset>' set (x # xs)"
              using \<open>x = y\<close> yys_above xxs_above y_Min
              by(auto simp add: not_less set_less_aux_def proper_interval_Some2 intro!: bexI[where x=y])
            with False show ?thesis by(auto dest: set_less_aux_trans)
          next
            case True
            then obtain z where z: "z \<in> above ao" "z < x"
              by(clarsimp simp add: proper_interval_Some2)

            have "?card \<longleftrightarrow> ?rhs"
            proof
              assume ?rhs
              then obtain A where less_A: "set (x # xs)  \<sqsubset>' A"
                and A_less: "A \<sqsubset>' - set (y # ys) \<inter> above ao"
                and subset: "A \<subseteq> above ao" by blast

              { 
                assume c_ys: "CARD('a) - (card (UNIV - above ao) + length ys) = 2"
                  and c_xs: "CARD('a) - (card (UNIV - above ao) + length xs) = 2"
                from c_ys yys_above len_ys y_Min have "card (UNIV - (UNIV - above ao) - set (y # ys)) = 1"
                  by(subst card_Diff_subset)(auto simp add: card_Diff_subset)
                then obtain z' where eq_y: "- set (y # ys) \<inter> above ao = {z'}"
                  unfolding card_eq_1_iff by auto
                moreover from z have "z \<notin> set (y # ys)" using \<open>x = y\<close> y_Min by auto
                ultimately have "z' = z" using z by fastforce
                
                from c_xs xxs_above len_xs x_Min have "card (UNIV - (UNIV - above ao) - set (x # xs)) = 1"
                  by(subst card_Diff_subset)(auto simp add: card_Diff_subset)
                then obtain z'' where eq_x: "- set (x # xs) \<inter> above ao = {z''}"
                  unfolding card_eq_1_iff by auto
                moreover from z have "z \<notin> set (x # xs)" using x_Min by auto
                ultimately have "z'' = z" using z by fastforce

                from less_A subset obtain q where "q \<in> A" "q \<in> above ao" "q \<notin> set (x # xs)"
                  by(auto simp add: set_less_aux_def)
                hence "q \<in> {z''}" unfolding eq_x[symmetric] by simp
                hence "q = z''" by simp
                with \<open>q \<in> A\<close> \<open>z' = z\<close> \<open>z'' = z\<close> z 
                have "- set (y # ys) \<inter> above ao \<subseteq> A"
                  unfolding eq_y by simp
                hence "- set (y # ys) \<inter> above ao \<sqsubseteq>' A"
                  by(auto intro: subset_finite_imp_set_less_eq_aux)
                with A_less have False by(auto dest: set_less_trans_set_less_eq) }
              thus ?card by auto
            next
              assume ?card (is "?card_ys \<or> ?card_xs")
              thus ?rhs
              proof
                assume ?card_ys
                let ?YS = "UNIV - (UNIV - above ao) - set (y # ys)"
                from \<open>?card_ys\<close> yys_above len_ys y_Min have "card ?YS \<noteq> 1" 
                  by(subst card_Diff_subset)(auto simp add: card_Diff_subset)
                moreover have "?YS \<noteq> {}" using True y_Min yys_above \<open>x = y\<close>
                  by(fastforce simp add: proper_interval_Some2)
                hence "card ?YS \<noteq> 0" by simp
                ultimately have "card ?YS > 1" by(cases "card ?YS") simp_all
                from card_gt_1D[OF this] obtain x' y' 
                  where x': "x' \<in> above ao" "x' \<notin> set (y # ys)"
                  and y': "y' \<in> above ao" "y' \<notin> set (y # ys)"
                  and neq: "x' \<noteq> y'" by auto
                let ?A = "{z}"
                have "set (x # xs) \<sqsubset>' ?A" using z x_Min
                  by(auto simp add: set_less_aux_def intro!: rev_bexI)
                moreover
                { have "?A \<subseteq> - set (y # ys) \<inter> above ao"
                    using z \<open>x = y\<close> y_Min by(auto)
                  moreover have "x' \<notin> ?A \<or> y' \<notin> ?A" using neq by auto
                  with x' y' have "?A \<noteq> - set (y # ys) \<inter> above ao" by auto
                  ultimately have "?A \<subset> - set (y # ys) \<inter> above ao" by(rule psubsetI)
                  hence "?A \<sqsubset>' \<dots>" by(fastforce intro: psubset_finite_imp_set_less_aux) } 
                ultimately show ?thesis using z by blast
              next
                assume ?card_xs
                let ?XS = "UNIV - (UNIV - above ao) - set (x # xs)"
                from \<open>?card_xs\<close> xxs_above len_xs x_Min have "card ?XS \<noteq> 1" 
                  by(subst card_Diff_subset)(auto simp add: card_Diff_subset)
                moreover have "?XS \<noteq> {}" using True x_Min xxs_above
                  by(fastforce simp add: proper_interval_Some2)
                hence "card ?XS \<noteq> 0" by simp
                ultimately have "card ?XS > 1" by(cases "card ?XS") simp_all
                from card_gt_1D[OF this] obtain x' y' 
                  where x': "x' \<in> above ao" "x' \<notin> set (x # xs)"
                  and y': "y' \<in> above ao" "y' \<notin> set (x # xs)"
                  and neq: "x' \<noteq> y'" by auto

                define A
                  where "A = (if x' = Min (above ao) then insert y' (set (x # xs)) else insert x' (set (x # xs)))"
                hence "set (x # xs) \<subseteq> A" by auto
                moreover have "set (x # xs) \<noteq> \<dots>"
                  using neq x' y' by(auto simp add: A_def)
                ultimately have "set (x # xs) \<subset> A" ..
                hence "set (x # xs) \<sqsubset>' \<dots>"
                  by(fastforce intro: psubset_finite_imp_set_less_aux)
                moreover {
                  have nempty: "above ao \<noteq> {}" using z by auto
                  have "A \<sqsubset>' {Min (above ao)}" 
                    using z x' y' neq \<open>x = y\<close> x_Min xxs_above
                    by(auto 6 4 simp add: set_less_aux_def A_def nempty intro!: rev_bexI Min_eqI)
                  also have "Min (above ao) \<le> z" using z by(simp)
                  hence "Min (above ao) < x" using \<open>z < x\<close> by(rule le_less_trans)
                  with \<open>x = y\<close> y_Min have "Min (above ao) \<notin> set (y # ys)" by auto
                  hence "{Min (above ao)} \<subseteq> - set (y # ys) \<inter> above ao"
                    by(auto simp add: nempty)
                  hence "{Min (above ao)} \<sqsubseteq>' \<dots>" by(auto intro: subset_finite_imp_set_less_eq_aux)
                  finally have "A \<sqsubset>' \<dots>" . }
                moreover have "A \<subseteq> above ao" using xxs_above yys_above x' y' 
                  by(auto simp add: A_def)
                ultimately show ?rhs by blast
              qed
            qed
            thus ?thesis using True by simp
          qed            
          thus ?thesis using \<open>x = y\<close> by simp
        qed
      qed
    qed }
  from this[of None]
  show ?thesis by(simp)
qed

lemma proper_interval_Compl_set_aux:
  assumes fin: "finite (UNIV :: 'a set)"
  and xs: "sorted xs" "distinct xs" 
  and ys: "sorted ys" "distinct ys" 
  shows "proper_interval_Compl_set_aux None xs ys \<longleftrightarrow> (\<exists>A. - set xs \<sqsubset>' A \<and> A \<sqsubset>' set ys)"
proof -
  note [simp] = finite_subset[OF subset_UNIV fin]

  define above where "above = case_option UNIV (Collect \<circ> less)"
  have above_simps [simp]: "above None = UNIV" "\<And>x. above (Some x) = {y. x < y}"
    and above_upclosed: "\<And>x y ao. \<lbrakk> x \<in> above ao; x < y \<rbrakk> \<Longrightarrow> y \<in> above ao"
    and proper_interval_Some2: "\<And>x ao. proper_interval ao (Some x) \<longleftrightarrow> (\<exists>z\<in>above ao. z < x)"
    by(simp_all add: proper_interval_simps above_def split: option.splits)

  { fix ao n
    assume "set xs \<subseteq> above ao" "set ys \<subseteq> above ao"
    from xs \<open>set xs \<subseteq> above ao\<close> ys \<open>set ys \<subseteq> above ao\<close>
    have "proper_interval_Compl_set_aux ao xs ys \<longleftrightarrow>
          (\<exists>A. - set xs \<inter> above ao \<sqsubset>' A \<inter> above ao \<and> A \<inter> above ao \<sqsubset>' set ys \<inter> above ao)"
    proof(induction ao xs ys rule: proper_interval_Compl_set_aux.induct)
      case ("2_1" ao ys)
      { fix A
        assume "above ao \<sqsubset>' A \<inter> above ao"
        also have "\<dots> \<subseteq> above ao" by simp
        hence "A \<inter> above ao \<sqsubseteq>' above ao"
          by(auto intro: subset_finite_imp_set_less_eq_aux)
        finally have False by simp }
      thus ?case by auto
    next
      case ("2_2" ao xs) thus ?case by simp
    next
      case (1 ao x xs y ys)
      note xxs = \<open>sorted (x # xs)\<close> \<open>distinct (x # xs)\<close>
      hence xs: "sorted xs" "distinct xs" and x_Min: "\<forall>x' \<in> set xs. x < x'"
        by(auto simp add: less_le)
      note yys = \<open>sorted (y # ys)\<close> \<open>distinct (y # ys)\<close>
      hence ys: "sorted ys" "distinct ys" and y_Min: "\<forall>y'\<in>set ys. y < y'"
        by(auto simp add: less_le)
      note xxs_above = \<open>set (x # xs) \<subseteq> above ao\<close>
      note yys_above = \<open>set (y # ys) \<subseteq> above ao\<close>

      show ?case
      proof(cases "x < y")
        case True
        have "\<not> proper_interval ao (Some x) \<and> proper_interval_Compl_set_aux (Some x) xs (y # ys) \<longleftrightarrow>
              (\<exists>A. - set (x # xs) \<inter> above ao \<sqsubset>' A \<inter> above ao \<and> A \<inter> above ao \<sqsubset>' set (y # ys) \<inter> above ao)"
          (is "?lhs \<longleftrightarrow> ?rhs")
        proof(cases "proper_interval ao (Some x)")
          case True
          then obtain z where z: "z < x" "z \<in> above ao"
            by(auto simp add: proper_interval_Some2)
          hence nempty: "above ao \<noteq> {}" by auto
          with z have "Min (above ao) \<le> z" by auto
          hence "Min (above ao) < x" using \<open>z < x\<close> by(rule le_less_trans)
          hence "set (y # ys) \<inter> above ao \<sqsubset>' - set (x # xs) \<inter> above ao"
            using y_Min x_Min z \<open>x < y\<close>
            by(fastforce simp add: set_less_aux_def nempty intro!: Min_eqI bexI[where x="Min (above ao)"])
          thus ?thesis using True by(auto dest: set_less_aux_trans set_less_aux_antisym)
        next
          case False
          hence above_eq: "above ao = insert x (above (Some x))"
            using xxs_above by(auto simp add: proper_interval_Some2 intro: above_upclosed)
          from x_Min have xs_above: "set xs \<subseteq> above (Some x)" by auto
          from \<open>x < y\<close> y_Min have ys_above: "set (y # ys) \<subseteq> above (Some x)" by auto

          have eq_xs: "- set xs \<inter> above (Some x) = - set (x # xs) \<inter> above ao"
            using above_eq by auto
          have eq_ys: "set (y # ys) \<inter> above (Some x) = set (y # ys) \<inter> above ao"
            using y_Min \<open>x < y\<close> xxs_above by(auto intro: above_upclosed)
          
          from \<open>x < y\<close> xs xs_above yys ys_above
          have "proper_interval_Compl_set_aux (Some x) xs (y # ys) \<longleftrightarrow>
               (\<exists>A. - set xs \<inter> above (Some x) \<sqsubset>' A \<inter> above (Some x) \<and>
                    A \<inter> above (Some x) \<sqsubset>' set (y # ys) \<inter> above (Some x))"
            by(rule "1.IH")
          also have "\<dots> \<longleftrightarrow> ?rhs" (is "?lhs \<longleftrightarrow> _")
          proof
            assume ?lhs
            then obtain A where "- set xs \<inter> above (Some x) \<sqsubset>' A \<inter> above (Some x)"
              and "A \<inter> above (Some x) \<sqsubset>' set (y # ys) \<inter> above (Some x)" by blast
            moreover have "A \<inter> above (Some x) = (A - {x}) \<inter> above ao"
              using above_eq by auto
            ultimately have "- set (x # xs) \<inter> above ao \<sqsubset>' (A - {x}) \<inter> above ao"
              and "(A - {x}) \<inter> above ao \<sqsubset>' set (y # ys) \<inter> above ao"
              using eq_xs eq_ys by simp_all
            thus ?rhs by blast
          next
            assume ?rhs
            then obtain A where "- set (x # xs) \<inter> above ao \<sqsubset>' A \<inter> above ao"
              and A_less: "A \<inter> above ao \<sqsubset>' set (y # ys) \<inter> above ao" by blast
            moreover have "x \<notin> A"
            proof
              assume "x \<in> A"
              hence "set (y # ys) \<inter> above ao \<sqsubset>' A \<inter> above ao"
                using y_Min \<open>x < y\<close> by(auto simp add: above_eq set_less_aux_def intro!: bexI[where x=x])
              with A_less show False by(auto dest: set_less_aux_antisym)
            qed
            hence "A \<inter> above ao = A \<inter> above (Some x)" using above_eq by auto
            ultimately show ?lhs using eq_xs eq_ys by auto
          qed
          finally show ?thesis using False by simp
        qed
        thus ?thesis using True by simp
      next
        case False
        show ?thesis
        proof(cases "y < x")
          case True
          show ?thesis (is "?lhs \<longleftrightarrow> ?rhs")
          proof(cases "proper_interval ao (Some y)")
            case True
            then obtain z where z: "z < y" "z \<in> above ao"
              by(auto simp add: proper_interval_Some2)
            hence nempty: "above ao \<noteq> {}" by auto
            with z have "Min (above ao) \<le> z" by auto
            hence "Min (above ao) < y" using \<open>z < y\<close> by(rule le_less_trans)
            hence "set (y # ys) \<inter> above ao \<sqsubset>' - set (x # xs) \<inter> above ao"
              using y_Min x_Min z \<open>y < x\<close>
              by(fastforce simp add: set_less_aux_def nempty intro!: Min_eqI bexI[where x="Min (above ao)"])
            thus ?thesis using True \<open>y < x\<close> by(auto dest: set_less_aux_trans set_less_aux_antisym)
          next
            case False
            hence above_eq: "above ao = insert y (above (Some y))"
              using yys_above by(auto simp add: proper_interval_Some2 intro: above_upclosed)
            from y_Min have ys_above: "set ys \<subseteq> above (Some y)" by auto
            from \<open>y < x\<close> x_Min have xs_above: "set (x # xs) \<subseteq> above (Some y)" by auto

            have "y \<in> - set (x # xs) \<inter> above ao" using \<open>y < x\<close> x_Min yys_above by auto
            hence nempty: "- set (x # xs) \<inter> above ao \<noteq> {}" by auto
            have Min_x: "Min (- set (x # xs) \<inter> above ao) = y"
              using above_eq \<open>y < x\<close> x_Min by(auto intro!: Min_eqI)
            have Min_y: "Min (set (y # ys) \<inter> above ao) = y"
              using y_Min above_eq by(auto intro!: Min_eqI)
            have eq_xs: "- set (x # xs) \<inter> above ao - {y} = - set (x # xs) \<inter> above (Some y)"
                by(auto simp add: above_eq)
            have eq_ys: "set ys \<inter> above ao - {y} = set ys \<inter> above (Some y)"
              using y_Min above_eq by auto

            from \<open>\<not> x < y\<close> \<open>y < x\<close> xxs xs_above ys ys_above
            have "proper_interval_Compl_set_aux (Some y) (x # xs) ys \<longleftrightarrow>
                 (\<exists>A. - set (x # xs) \<inter> above (Some y) \<sqsubset>' A \<inter> above (Some y) \<and>
                      A \<inter> above (Some y) \<sqsubset>' set ys \<inter> above (Some y))"
              by(rule "1.IH")
            also have "\<dots> \<longleftrightarrow> ?rhs" (is "?lhs' \<longleftrightarrow> _")
            proof
              assume ?lhs'
              then obtain A where less_A: "- set (x # xs) \<inter> above (Some y) \<sqsubset>' A \<inter> above (Some y)"
                and A_less: "A \<inter> above (Some y) \<sqsubset>' set ys \<inter> above (Some y)" by blast
              let ?A = "insert y A"

              have Min_A: "Min (?A \<inter> above ao) = y"
                using above_eq by(auto intro!: Min_eqI)
              moreover have A_eq: "A \<inter> above ao - {y} = A \<inter> above (Some y)"
                using above_eq by auto
              ultimately have less_A': "- set (x # xs) \<inter> above ao \<sqsubset>' ?A \<inter> above ao"
                using nempty yys_above less_A Min_x eq_xs by(subst set_less_aux_rec) simp_all

              have A'_less: "?A \<inter> above ao \<sqsubset>' set (y # ys) \<inter> above ao"
                using yys_above nempty Min_A A_eq A_less Min_y eq_ys
                by(subst set_less_aux_rec) simp_all
              
              with less_A' show ?rhs by blast
            next
              assume ?rhs
              then obtain A where less_A: "- set (x # xs) \<inter> above ao \<sqsubset>' A \<inter> above ao"
                and A_less: "A \<inter> above ao \<sqsubset>' set (y # ys) \<inter> above ao" by blast

              from less_A have nempty': "A \<inter> above ao \<noteq> {}" by auto
              moreover have A_eq: "A \<inter> above ao - {y} = A \<inter> above (Some y)"
                using above_eq by auto
              moreover have y_in_xxs: "y \<in> - set (x # xs) \<inter> above ao"
                using \<open>y < x\<close> x_Min yys_above by auto
              moreover have "y \<in> A"
              proof(rule ccontr)
                assume "y \<notin> A"
                hence "A \<inter> above ao \<sqsubset>' - set (x # xs) \<inter> above ao"
                  using \<open>y < x\<close> x_Min y_in_xxs
                  by(auto simp add: set_less_aux_def above_eq intro: bexI[where x=y])
                with less_A show False by(rule set_less_aux_antisym)
              qed
              hence Min_A: "Min (A \<inter> above ao) = y" using above_eq y_Min by(auto intro!: Min_eqI)
              ultimately have less_A': "- set (x # xs) \<inter> above (Some y) \<sqsubset>' A \<inter> above (Some y)"
                using nempty less_A Min_x eq_xs
                by(subst (asm) set_less_aux_rec)(auto dest: bspec[where x=y])
              
              have A'_less: "A \<inter> above (Some y) \<sqsubset>' set ys \<inter> above (Some y)"
                using A_less nempty' yys_above Min_A Min_y A_eq eq_ys
                by(subst (asm) set_less_aux_rec) simp_all
              with less_A' show ?lhs' by blast
            qed
            finally show ?thesis using \<open>\<not> x < y\<close> \<open>y < x\<close> False by simp
          qed
        next
          case False
          with \<open>\<not> x < y\<close> have "x = y" by auto
          thus ?thesis (is "?lhs \<longleftrightarrow> ?rhs")
          proof(cases "proper_interval ao (Some x)")
            case True
            then obtain z where z: "z < x" "z \<in> above ao"
              by(auto simp add: proper_interval_Some2)
            hence nempty: "above ao \<noteq> {}" by auto
            with z have "Min (above ao) \<le> z" by auto
            hence "Min (above ao) < x" using \<open>z < x\<close> by(rule le_less_trans)
            hence "set (y # ys) \<inter> above ao \<sqsubset>' - set (x # xs) \<inter> above ao"
              using y_Min x_Min z \<open>x = y\<close>
              by(fastforce simp add: set_less_aux_def nempty intro!: Min_eqI bexI[where x="Min (above ao)"])
            thus ?thesis using True \<open>x = y\<close> by(auto dest: set_less_aux_trans set_less_aux_antisym)
          next
            case False
            hence above_eq: "above ao = insert x (above (Some x))"
              using xxs_above by(auto simp add: proper_interval_Some2 intro: above_upclosed)

            have "(ys = [] \<longrightarrow> xs \<noteq> []) \<longleftrightarrow> ?rhs" (is "?lhs' \<longleftrightarrow> _")
            proof(intro iffI strip notI)
              assume ?lhs'
              show ?rhs
              proof(cases ys)
                case Nil
                with \<open>?lhs'\<close> obtain x' xs' where xs_eq: "xs = x' # xs'"
                  by(auto simp add: neq_Nil_conv)
                with xs have x'_Min: "\<forall>x'' \<in> set xs'. x' < x''"
                  by(auto simp add: less_le)
                let ?A = "- set (x # xs')"
                have "- set (x # xs) \<inter> above ao \<subseteq> ?A \<inter> above ao"
                  using xs_eq by auto
                moreover have "x' \<notin> - set (x # xs) \<inter> above ao" "x' \<in> ?A \<inter> above ao"
                  using xs_eq xxs_above x'_Min x_Min by auto
                ultimately have "- set (x # xs) \<inter> above ao \<subset> ?A \<inter> above ao"
                  by blast
                hence "- set (x # xs) \<inter> above ao \<sqsubset>' \<dots> "
                  by(fastforce intro: psubset_finite_imp_set_less_aux)
                moreover have "\<dots> \<sqsubset>' set (y # ys) \<inter> above ao" 
                  using Nil \<open>x = y\<close> by(auto simp add: set_less_aux_def above_eq)
                ultimately show ?thesis by blast
              next
                case (Cons y' ys')
                let ?A = "{y}"
                have "- set (x # xs) \<inter> above ao \<sqsubset>' ?A \<inter> above ao"
                  using \<open>x = y\<close> x_Min by(auto simp add: set_less_aux_def above_eq)
                moreover have "\<dots> \<subset> set (y # ys) \<inter> above ao"
                  using yys_above yys Cons by auto
                hence "?A \<inter> above ao \<sqsubset>' \<dots>" by(fastforce intro: psubset_finite_imp_set_less_aux)
                ultimately show ?thesis by blast
              qed
            next
              assume Nil: "ys = []" "xs = []" and ?rhs
              then obtain A where less_A: "- {x} \<inter> above ao \<sqsubset>' A \<inter> above ao" 
                and A_less: "A \<inter> above ao \<sqsubset>' {x}" using \<open>x = y\<close> above_eq by auto
              have "x \<notin> A" using A_less by(auto simp add: set_less_aux_def above_eq)
              hence "A \<inter> above ao \<subseteq> - {x} \<inter> above ao" by auto
              hence "A \<inter> above ao \<sqsubseteq>' \<dots>" by(auto intro: subset_finite_imp_set_less_eq_aux)
              with less_A have "\<dots> \<sqsubset>' \<dots>" by(rule set_less_trans_set_less_eq)
              thus False by simp
            qed
            with \<open>x = y\<close> False show ?thesis by simp
          qed
        qed
      qed
    qed }
  from this[of None] show ?thesis by simp
qed

end

subsection \<open>Proper intervals for HOL types\<close>

instantiation unit :: proper_interval begin
fun proper_interval_unit :: "unit proper_interval" where
  "proper_interval_unit None None = True"
| "proper_interval_unit _ _ = False"
instance by intro_classes auto
end

instantiation bool :: proper_interval begin
fun proper_interval_bool :: "bool proper_interval" where
  "proper_interval_bool (Some x) (Some y) \<longleftrightarrow> False"
| "proper_interval_bool (Some x) None \<longleftrightarrow> \<not> x"
| "proper_interval_bool None (Some y) \<longleftrightarrow> y"
| "proper_interval_bool None None = True"
instance by intro_classes auto
end

instantiation nat :: proper_interval begin
fun proper_interval_nat :: "nat proper_interval" where
  "proper_interval_nat no None = True"
| "proper_interval_nat None (Some x) \<longleftrightarrow> x > 0"
| "proper_interval_nat (Some x) (Some y) \<longleftrightarrow> y - x > 1"
instance by intro_classes auto
end

instantiation int :: proper_interval begin
fun proper_interval_int :: "int proper_interval" where
  "proper_interval_int (Some x) (Some y) \<longleftrightarrow> y - x > 1"
| "proper_interval_int _ _ = True"
instance by intro_classes (auto intro: less_add_one, metis less_add_one minus_less_iff)
end

instantiation integer :: proper_interval begin
context includes integer.lifting begin
lift_definition proper_interval_integer :: "integer proper_interval" is "proper_interval" .
instance by(intro_classes)(transfer, simp only: proper_interval_simps)+
end
end
lemma proper_interval_integer_simps [code]:
  includes integer.lifting fixes x y :: integer and xo yo :: "integer option" shows
  "proper_interval (Some x) (Some y) = (1 < y - x)"
  "proper_interval None yo = True"
  "proper_interval xo None = True"
by(transfer, simp)+

instantiation natural :: proper_interval begin
context includes natural.lifting begin
lift_definition proper_interval_natural :: "natural proper_interval" is "proper_interval" .
instance by(intro_classes)(transfer, simp only: proper_interval_simps)+
end
end
lemma proper_interval_natural_simps [code]:
  includes natural.lifting fixes x y :: natural and xo :: "natural option" shows
  "proper_interval xo None = True"
  "proper_interval None (Some y) \<longleftrightarrow> y > 0"
  "proper_interval (Some x) (Some y) \<longleftrightarrow> y - x > 1"
by(transfer, simp)+

lemma char_less_iff_nat_of_char: "x < y \<longleftrightarrow> of_char x < (of_char y :: nat)"
  by (fact less_char_def)

lemma nat_of_char_inject [simp]: "of_char x = (of_char y :: nat) \<longleftrightarrow> x = y"
  by (fact of_char_eq_iff)

lemma char_le_iff_nat_of_char: "x \<le> y \<longleftrightarrow> of_char x \<le> (of_char y :: nat)"
  by (fact less_eq_char_def)

instantiation char :: proper_interval
begin

fun proper_interval_char :: "char proper_interval" where
  "proper_interval_char None None \<longleftrightarrow> True"
| "proper_interval_char None (Some x) \<longleftrightarrow> x \<noteq> CHR 0x00"
| "proper_interval_char (Some x) None \<longleftrightarrow> x \<noteq> CHR 0xFF"
| "proper_interval_char (Some x) (Some y) \<longleftrightarrow> of_char y - of_char x > (1 :: nat)"

instance proof
  fix y :: char
  { assume "y \<noteq> CHR 0x00"
    have "CHR 0x00 < y" 
    proof (rule ccontr)
      assume "\<not> CHR 0x00 < y"
      then have "of_char y = (of_char CHR 0x00 :: nat)"
        by (simp add: not_less char_le_iff_nat_of_char)
      then have "y = CHR 0x00"
        using nat_of_char_inject [of y "CHR 0x00"] by simp
      with \<open>y \<noteq> CHR 0x00\<close> show False
        by simp
    qed }
  moreover
  { fix z :: char
    assume "z < CHR 0x00"
    hence False
      by (simp add: char_less_iff_nat_of_char of_char_eq_iff [symmetric]) }
  ultimately show "proper_interval None (Some y) = (\<exists>z. z < y)"
    by auto

  fix x :: char
  { assume "x \<noteq> CHR 0xFF"
    then have "x < CHR 0xFF"
      by (auto simp add: neq_iff char_less_iff_nat_of_char)
        (insert nat_of_char_less_256 [of x], simp)
    hence "\<exists>z. x < z" .. }
  moreover
  { fix z :: char
    assume "CHR 0xFF < z"
    hence "False"
      by (simp add: char_less_iff_nat_of_char)
        (insert nat_of_char_less_256 [of z], simp) }
  ultimately show "proper_interval (Some x) None = (\<exists>z. x < z)" by auto

  { assume gt: "of_char y - of_char x > (1 :: nat)"
    let ?z = "char_of (of_char x + (1 :: nat))"
    from gt nat_of_char_less_256 [of y]
    have 255: "of_char x < (255 :: nat)" by arith
    with gt have "x < ?z" "?z < y"
      by (simp_all add: char_less_iff_nat_of_char)
    hence "\<exists>z. x < z \<and> z < y" by blast }
  moreover
  { fix z
    assume "x < z" "z < y"
    hence "(1 :: nat) < of_char y - of_char x"
      by (simp add: char_less_iff_nat_of_char) }
  ultimately show "proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)"
    by auto
qed simp

end

instantiation Enum.finite_1 :: proper_interval begin
definition proper_interval_finite_1 :: "Enum.finite_1 proper_interval" 
where "proper_interval_finite_1 x y \<longleftrightarrow> x = None \<and> y = None"
instance by intro_classes (simp_all add: proper_interval_finite_1_def less_finite_1_def)
end

instantiation Enum.finite_2 :: proper_interval begin
fun proper_interval_finite_2 :: "Enum.finite_2 proper_interval" where 
  "proper_interval_finite_2 None None \<longleftrightarrow> True"
| "proper_interval_finite_2 None (Some x) \<longleftrightarrow> x = finite_2.a\<^sub>2"
| "proper_interval_finite_2 (Some x) None \<longleftrightarrow> x = finite_2.a\<^sub>1"
| "proper_interval_finite_2 (Some x) (Some y) \<longleftrightarrow> False"
instance by intro_classes (auto simp add: less_finite_2_def)
end

instantiation Enum.finite_3 :: proper_interval begin
fun proper_interval_finite_3 :: "Enum.finite_3 proper_interval" where
  "proper_interval_finite_3 None None \<longleftrightarrow> True"
| "proper_interval_finite_3 None (Some x) \<longleftrightarrow> x \<noteq> finite_3.a\<^sub>1"
| "proper_interval_finite_3 (Some x) None \<longleftrightarrow> x \<noteq> finite_3.a\<^sub>3"
| "proper_interval_finite_3 (Some x) (Some y) \<longleftrightarrow> x = finite_3.a\<^sub>1 \<and> y = finite_3.a\<^sub>3"
instance
proof
  fix x y :: Enum.finite_3
  show "proper_interval None (Some y) = (\<exists>z. z < y)"
    by(cases y)(auto simp add: less_finite_3_def split: finite_3.split)
  show "proper_interval (Some x) None = (\<exists>z. x < z)"
    by(cases x)(auto simp add: less_finite_3_def)
  show "proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)"
    by(auto simp add: less_finite_3_def split: finite_3.split_asm)
qed simp
end

subsection \<open>List fusion for the order and proper intervals on @{typ "'a set"}\<close>

definition length_last_fusion :: "('a, 's) generator \<Rightarrow> 's \<Rightarrow> nat \<times> 'a"
where "length_last_fusion g s = length_last (list.unfoldr g s)"

lemma length_last_fusion_code [code]:
  "length_last_fusion g s =
  (if list.has_next g s then
     let (x, s') = list.next g s
     in fold_fusion g (\<lambda>x (n, _). (n + 1, x)) s' (1, x)
   else (0, undefined))"
unfolding length_last_fusion_def
by(subst list.unfoldr.simps)(simp add: length_last_Nil length_last_Cons_code fold_fusion_def split_beta)

declare length_last_fusion_def [symmetric, code_unfold]

context proper_intrvl begin

definition set_less_eq_aux_Compl_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "set_less_eq_aux_Compl_fusion g1 g2 ao s1 s2 = 
   set_less_eq_aux_Compl ao (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition Compl_set_less_eq_aux_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "Compl_set_less_eq_aux_fusion g1 g2 ao s1 s2 = 
   Compl_set_less_eq_aux ao (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition set_less_aux_Compl_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "set_less_aux_Compl_fusion g1 g2 ao s1 s2 =
   set_less_aux_Compl ao (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition Compl_set_less_aux_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "Compl_set_less_aux_fusion g1 g2 ao s1 s2 =
   Compl_set_less_aux ao (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition exhaustive_above_fusion :: "('a, 's) generator \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
where "exhaustive_above_fusion g a s = exhaustive_above a (list.unfoldr g s)"

definition exhaustive_fusion :: "('a, 's) generator \<Rightarrow> 's \<Rightarrow> bool"
where "exhaustive_fusion g s = exhaustive (list.unfoldr g s)"

definition proper_interval_set_aux_fusion :: "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "proper_interval_set_aux_fusion g1 g2 s1 s2 =
   proper_interval_set_aux (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition proper_interval_set_Compl_aux_fusion :: 
  "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> nat \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "proper_interval_set_Compl_aux_fusion g1 g2 ao n s1 s2 =
   proper_interval_set_Compl_aux ao n (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

definition proper_interval_Compl_set_aux_fusion ::
  "('a, 's1) generator \<Rightarrow> ('a, 's2) generator \<Rightarrow> 'a option \<Rightarrow> 's1 \<Rightarrow> 's2 \<Rightarrow> bool"
where
  "proper_interval_Compl_set_aux_fusion g1 g2 ao s1 s2 =
   proper_interval_Compl_set_aux ao (list.unfoldr g1 s1) (list.unfoldr g2 s2)"

lemma set_less_eq_aux_Compl_fusion_code:
  "set_less_eq_aux_Compl_fusion g1 g2 ao s1 s2 \<longleftrightarrow>
   (list.has_next g1 s1 \<longrightarrow> list.has_next g2 s2 \<longrightarrow>
    (let (x, s1') = list.next g1 s1;
         (y, s2') = list.next g2 s2
     in if x < y then proper_interval ao (Some x) \<or> set_less_eq_aux_Compl_fusion g1 g2 (Some x) s1' s2
        else if y < x then proper_interval ao (Some y) \<or> set_less_eq_aux_Compl_fusion g1 g2 (Some y) s1 s2'
        else proper_interval ao (Some y)))"
unfolding set_less_eq_aux_Compl_fusion_def
by(subst (1 2 4 5) list.unfoldr.simps)(simp add: split_beta)

lemma Compl_set_less_eq_aux_fusion_code:
  "Compl_set_less_eq_aux_fusion g1 g2 ao s1 s2 \<longleftrightarrow>
  (if list.has_next g1 s1 then
     let (x, s1') = list.next g1 s1
     in if list.has_next g2 s2 then
          let (y, s2') = list.next g2 s2
          in if x < y then \<not> proper_interval ao (Some x) \<and> Compl_set_less_eq_aux_fusion g1 g2 (Some x) s1' s2
             else if y < x then \<not> proper_interval ao (Some y) \<and> Compl_set_less_eq_aux_fusion g1 g2 (Some y) s1 s2'
             else \<not> proper_interval ao (Some y)
        else \<not> proper_interval ao (Some x) \<and> Compl_set_less_eq_aux_fusion g1 g2 (Some x) s1' s2
   else if list.has_next g2 s2 then
     let (y, s2') = list.next g2 s2
     in \<not> proper_interval ao (Some y) \<and> Compl_set_less_eq_aux_fusion g1 g2 (Some y) s1 s2'
   else \<not> proper_interval ao None)"
unfolding Compl_set_less_eq_aux_fusion_def
by(subst (1 2 4 5 8 9) list.unfoldr.simps)(simp add: split_beta)

lemma set_less_aux_Compl_fusion_code:
  "set_less_aux_Compl_fusion g1 g2 ao s1 s2 \<longleftrightarrow>
  (if list.has_next g1 s1 then
     let (x, s1') = list.next g1 s1
     in if list.has_next g2 s2 then
          let (y, s2') = list.next g2 s2
          in if x < y then proper_interval ao (Some x) \<or> set_less_aux_Compl_fusion g1 g2 (Some x) s1' s2
             else if y < x then proper_interval ao (Some y) \<or> set_less_aux_Compl_fusion g1 g2 (Some y) s1 s2'
             else proper_interval ao (Some y)
        else proper_interval ao (Some x) \<or> set_less_aux_Compl_fusion g1 g2 (Some x) s1' s2
   else if list.has_next g2 s2 then
     let (y, s2') = list.next g2 s2
     in proper_interval ao (Some y) \<or> set_less_aux_Compl_fusion g1 g2 (Some y) s1 s2'
   else proper_interval ao None)"
unfolding set_less_aux_Compl_fusion_def
by(subst (1 2 4 5 8 9) list.unfoldr.simps)(simp add: split_beta)

lemma Compl_set_less_aux_fusion_code:
  "Compl_set_less_aux_fusion g1 g2 ao s1 s2 \<longleftrightarrow>
   list.has_next g1 s1 \<and> list.has_next g2 s2 \<and>
  (let (x, s1') = list.next g1 s1;
       (y, s2') = list.next g2 s2
   in if x < y then \<not> proper_interval ao (Some x) \<and> Compl_set_less_aux_fusion g1 g2 (Some x) s1' s2
      else if y < x then \<not> proper_interval ao (Some y) \<and> Compl_set_less_aux_fusion g1 g2 (Some y) s1 s2'
      else \<not> proper_interval ao (Some y))"
unfolding Compl_set_less_aux_fusion_def
by(subst (1 2 4 5) list.unfoldr.simps)(simp add: split_beta)

lemma exhaustive_above_fusion_code:
  "exhaustive_above_fusion g y s \<longleftrightarrow>
  (if list.has_next g s then
     let (x, s') = list.next g s
     in \<not> proper_interval (Some y) (Some x) \<and> exhaustive_above_fusion g x s'
   else \<not> proper_interval (Some y) None)"
unfolding exhaustive_above_fusion_def
by(subst list.unfoldr.simps)(simp add: split_beta)

lemma exhaustive_fusion_code:
  "exhaustive_fusion g s =
  (list.has_next g s \<and> 
   (let (x, s') = list.next g s
    in \<not> proper_interval None (Some x) \<and> exhaustive_above_fusion g x s'))"
unfolding exhaustive_fusion_def exhaustive_above_fusion_def
by(subst (1) list.unfoldr.simps)(simp add: split_beta)

lemma proper_interval_set_aux_fusion_code:
  "proper_interval_set_aux_fusion g1 g2 s1 s2 \<longleftrightarrow>
   list.has_next g2 s2 \<and>
  (let (y, s2') = list.next g2 s2
   in if list.has_next g1 s1 then
        let (x, s1') = list.next g1 s1
        in if x < y then False
           else if y < x then proper_interval (Some y) (Some x) \<or> list.has_next g2 s2' \<or> \<not> exhaustive_above_fusion g1 x s1'
           else proper_interval_set_aux_fusion g1 g2 s1' s2'
      else list.has_next g2 s2' \<or> proper_interval (Some y) None)"
unfolding proper_interval_set_aux_fusion_def exhaustive_above_fusion_def
by(subst (1 2) list.unfoldr.simps)(simp add: split_beta)

lemma proper_interval_set_Compl_aux_fusion_code:
  "proper_interval_set_Compl_aux_fusion g1 g2 ao n s1 s2 \<longleftrightarrow>
  (if list.has_next g1 s1 then
     let (x, s1') = list.next g1 s1
     in if list.has_next g2 s2 then
          let (y, s2') = list.next g2 s2
          in if x < y then 
               proper_interval ao (Some x) \<or> 
               proper_interval_set_Compl_aux_fusion g1 g2 (Some x) (n + 1) s1' s2
             else if y < x then 
               proper_interval ao (Some y) \<or> 
               proper_interval_set_Compl_aux_fusion g1 g2 (Some y) (n + 1) s1 s2'
             else
               proper_interval ao (Some x) \<and>
               (let m = CARD('a) - n 
                in m - length_fusion g2 s2' \<noteq> 2 \<or> m - length_fusion g1 s1' \<noteq> 2)
        else 
          let m = CARD('a) - n; (len_x, x') = length_last_fusion g1 s1
          in m \<noteq> len_x \<and> (m = len_x + 1 \<longrightarrow> \<not> proper_interval (Some x') None)

   else if list.has_next g2 s2 then
     let (y, s2') = list.next g2 s2;
         m = CARD('a) - n;
         (len_y, y') = length_last_fusion g2 s2
     in m \<noteq> len_y \<and> (m = len_y + 1 \<longrightarrow> \<not> proper_interval (Some y') None)
   else CARD('a) > n + 1)"
unfolding proper_interval_set_Compl_aux_fusion_def length_last_fusion_def length_fusion_def
by(subst (1 2 4 5 9 10) list.unfoldr.simps)(simp add: split_beta)

lemma proper_interval_Compl_set_aux_fusion_code:
  "proper_interval_Compl_set_aux_fusion g1 g2 ao s1 s2 \<longleftrightarrow>
   list.has_next g1 s1 \<and> list.has_next g2 s2 \<and>
   (let (x, s1') = list.next g1 s1;
        (y, s2') = list.next g2 s2
    in if x < y then
         \<not> proper_interval ao (Some x) \<and> proper_interval_Compl_set_aux_fusion g1 g2 (Some x) s1' s2
       else if y < x then
         \<not> proper_interval ao (Some y) \<and> proper_interval_Compl_set_aux_fusion g1 g2 (Some y) s1 s2'
       else \<not> proper_interval ao (Some x) \<and> (list.has_next g2 s2' \<or> list.has_next g1 s1'))"
unfolding proper_interval_Compl_set_aux_fusion_def
by(subst (1 2 4 5) list.unfoldr.simps)(auto simp add: split_beta)

end

lemmas [code] =
  set_less_eq_aux_Compl_fusion_code proper_intrvl.set_less_eq_aux_Compl_fusion_code
  Compl_set_less_eq_aux_fusion_code proper_intrvl.Compl_set_less_eq_aux_fusion_code
  set_less_aux_Compl_fusion_code proper_intrvl.set_less_aux_Compl_fusion_code
  Compl_set_less_aux_fusion_code proper_intrvl.Compl_set_less_aux_fusion_code
  exhaustive_above_fusion_code proper_intrvl.exhaustive_above_fusion_code
  exhaustive_fusion_code proper_intrvl.exhaustive_fusion_code
  proper_interval_set_aux_fusion_code proper_intrvl.proper_interval_set_aux_fusion_code
  proper_interval_set_Compl_aux_fusion_code proper_intrvl.proper_interval_set_Compl_aux_fusion_code
  proper_interval_Compl_set_aux_fusion_code proper_intrvl.proper_interval_Compl_set_aux_fusion_code

lemmas [symmetric, code_unfold] =
  set_less_eq_aux_Compl_fusion_def proper_intrvl.set_less_eq_aux_Compl_fusion_def
  Compl_set_less_eq_aux_fusion_def proper_intrvl.Compl_set_less_eq_aux_fusion_def
  set_less_aux_Compl_fusion_def proper_intrvl.set_less_aux_Compl_fusion_def
  Compl_set_less_aux_fusion_def proper_intrvl.Compl_set_less_aux_fusion_def
  exhaustive_above_fusion_def proper_intrvl.exhaustive_above_fusion_def
  exhaustive_fusion_def proper_intrvl.exhaustive_fusion_def
  proper_interval_set_aux_fusion_def proper_intrvl.proper_interval_set_aux_fusion_def
  proper_interval_set_Compl_aux_fusion_def proper_intrvl.proper_interval_set_Compl_aux_fusion_def
  proper_interval_Compl_set_aux_fusion_def proper_intrvl.proper_interval_Compl_set_aux_fusion_def

subsection \<open>Drop notation\<close>

context ord begin

no_notation set_less_aux (infix "\<sqsubset>''" 50)
  and set_less_eq_aux (infix "\<sqsubseteq>''" 50)
  and set_less_eq_aux' (infix "\<sqsubseteq>''''" 50)
  and set_less_eq_aux'' (infix "\<sqsubseteq>''''''" 50)
  and set_less_eq (infix "\<sqsubseteq>" 50)
  and set_less (infix "\<sqsubset>" 50)

end

end
