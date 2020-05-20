(* Author: Alexander Maletzky *)

section \<open>Auto-reducing Lists of Polynomials\<close>

theory Auto_Reduction
  imports Reduction More_MPoly_Type_Class
begin

subsection \<open>Reduction and Monic Sets\<close>

context ordered_term
begin

lemma is_red_monic: "is_red B (monic p) \<longleftrightarrow> is_red B p"
  unfolding is_red_adds_iff keys_monic ..

lemma red_image_monic [simp]: "red (monic ` B) = red B"
proof (rule, rule)
  fix p q
  show "red (monic ` B) p q \<longleftrightarrow> red B p q"
  proof
    assume "red (monic ` B) p q"
    then obtain f t where "f \<in> monic ` B" and *: "red_single p q f t" by (rule red_setE)
    from this(1) obtain g where "g \<in> B" and "f = monic g" ..
    from * have "f \<noteq> 0" by (simp add: red_single_def)
    hence "g \<noteq> 0" by (simp add: monic_0_iff \<open>f = monic g\<close>)
    hence "lc g \<noteq> 0" by (rule lc_not_0)
    have eq: "monom_mult (lc g) 0 f = g" by (simp add: \<open>f = monic g\<close> mult_lc_monic[OF \<open>g \<noteq> 0\<close>])
    from \<open>g \<in> B\<close> show "red B p q"
    proof (rule red_setI)
      from * \<open>lc g \<noteq> 0\<close> have "red_single p q (monom_mult (lc g) 0 f) t" by (rule red_single_mult_const)
      thus "red_single p q g t" by (simp only: eq)
    qed
  next
    assume "red B p q"
    then obtain f t where "f \<in> B" and *: "red_single p q f t" by (rule red_setE)
    from * have "f \<noteq> 0" by (simp add: red_single_def)
    hence "lc f \<noteq> 0" by (rule lc_not_0)
    hence "1 / lc f \<noteq> 0" by simp
    from \<open>f \<in> B\<close> have "monic f \<in> monic ` B" by (rule imageI)
    thus "red (monic ` B) p q"
    proof (rule red_setI)
      from * \<open>1 / lc f \<noteq> 0\<close> show "red_single p q (monic f) t" unfolding monic_def
        by (rule red_single_mult_const)
    qed
  qed
qed

lemma is_red_image_monic [simp]: "is_red (monic ` B) p \<longleftrightarrow> is_red B p"
  by (simp add: is_red_def)

subsection \<open>Minimal Bases and Auto-reduced Bases\<close>

definition is_auto_reduced :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool" where
  "is_auto_reduced B \<equiv> (\<forall>b\<in>B. \<not> is_red (B - {b}) b)"

definition is_minimal_basis :: "('t \<Rightarrow>\<^sub>0 'b::zero) set \<Rightarrow> bool" where
  "is_minimal_basis B \<longleftrightarrow> (0 \<notin> B \<and> (\<forall>p q. p \<in> B \<longrightarrow> q \<in> B \<longrightarrow> p \<noteq> q \<longrightarrow> \<not> lt p adds\<^sub>t lt q))"

lemma is_auto_reducedD:
  assumes "is_auto_reduced B" and "b \<in> B"
  shows "\<not> is_red (B - {b}) b"
  using assms unfolding is_auto_reduced_def by auto

text \<open>The converse of the following lemma is only true if @{term B} is minimal!\<close>
lemma image_monic_is_auto_reduced:
  assumes "is_auto_reduced B"
  shows "is_auto_reduced (monic ` B)"
  unfolding is_auto_reduced_def
proof
  fix b
  assume "b \<in> monic ` B"
  then obtain b' where b_def: "b = monic b'" and "b' \<in> B" ..
  from assms \<open>b' \<in> B\<close> have nred: "\<not> is_red (B - {b'}) b'" by (rule is_auto_reducedD)
  show "\<not> is_red ((monic ` B) - {b}) b"
  proof
    assume red: "is_red ((monic ` B) - {b}) b"
    have "(monic ` B) - {b} \<subseteq> monic ` (B - {b'})" unfolding b_def by auto
    with red have "is_red (monic ` (B - {b'})) b" by (rule is_red_subset)
    hence "is_red (B - {b'}) b'" unfolding b_def is_red_monic is_red_image_monic .
    with nred show False ..
  qed
qed
  
lemma is_minimal_basisI:
  assumes "\<And>p. p \<in> B \<Longrightarrow> p \<noteq> 0" and "\<And>p q. p \<in> B \<Longrightarrow> q \<in> B \<Longrightarrow> p \<noteq> q \<Longrightarrow> \<not> lt p adds\<^sub>t lt q"
  shows "is_minimal_basis B"
  unfolding is_minimal_basis_def using assms by auto
    
lemma is_minimal_basisD1:
  assumes "is_minimal_basis B" and "p \<in> B"
  shows "p \<noteq> 0"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basisD2:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lt p adds\<^sub>t lt q"
  using assms unfolding is_minimal_basis_def by auto
  
lemma is_minimal_basisD3:
  assumes "is_minimal_basis B" and "p \<in> B" and "q \<in> B" and "p \<noteq> q"
  shows "\<not> lt q adds\<^sub>t lt p"
  using assms unfolding is_minimal_basis_def by auto
    
lemma is_minimal_basis_subset:
  assumes "is_minimal_basis B" and "A \<subseteq> B"
  shows "is_minimal_basis A"
proof (intro is_minimal_basisI)
  fix p
  assume "p \<in> A"
  with \<open>A \<subseteq> B\<close> have "p \<in> B" ..
  with \<open>is_minimal_basis B\<close> show "p \<noteq> 0" by (rule is_minimal_basisD1)
next
  fix p q
  assume "p \<in> A" and "q \<in> A" and "p \<noteq> q"
  from \<open>p \<in> A\<close> and \<open>q \<in> A\<close> have "p \<in> B" and "q \<in> B" using \<open>A \<subseteq> B\<close> by auto
  from \<open>is_minimal_basis B\<close> this \<open>p \<noteq> q\<close> show " \<not> lt p adds\<^sub>t lt q" by (rule is_minimal_basisD2)
qed
  
lemma nadds_red:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and red: "red B p r"
  shows "r \<noteq> 0 \<and> lt r = lt p"
proof -
  from red obtain q t where "q \<in> B" and rs: "red_single p r q t" by (rule red_setE)
  from rs have "q \<noteq> 0" and "lookup p (t \<oplus> lt q) \<noteq> 0"
    and r_def: "r = p - monom_mult (lookup p (t \<oplus> lt q) / lc q) t q" unfolding red_single_def by simp_all
  have "t \<oplus> lt q \<preceq>\<^sub>t lt p" by (rule lt_max, fact)
  moreover have "t \<oplus> lt q \<noteq> lt p"
  proof
    assume "t \<oplus> lt q = lt p"
    hence "lt q adds\<^sub>t lt p" by (metis adds_term_triv) 
    with nadds[OF \<open>q \<in> B\<close>] show False ..
  qed
  ultimately have "t \<oplus> lt q \<prec>\<^sub>t lt p" by simp
  let ?m = "monom_mult (lookup p (t \<oplus> lt q) / lc q) t q"
  from \<open>lookup p (t \<oplus> lt q) \<noteq> 0\<close> lc_not_0[OF \<open>q \<noteq> 0\<close>] have c0: "lookup p (t \<oplus> lt q) / lc q \<noteq> 0" by simp
  from \<open>q \<noteq> 0\<close> c0 have "?m \<noteq> 0" by (simp add: monom_mult_eq_zero_iff)
  have "lt (-?m) = lt ?m" by (fact lt_uminus)
  also have lt1: "lt ?m = t \<oplus> lt q" by (rule lt_monom_mult, fact+)
  finally have lt2: "lt (-?m) = t \<oplus> lt q" .
  
  show ?thesis
  proof
    show "r \<noteq> 0"
    proof
      assume "r = 0"
      hence "p = ?m" unfolding r_def by simp
      with lt1 \<open>t \<oplus> lt q \<noteq> lt p\<close> show False by simp
    qed
  next
    have "lt (-?m + p) = lt p"
    proof (rule lt_plus_eqI)
      show "lt (-?m) \<prec>\<^sub>t lt p" unfolding lt2 by fact
    qed
    thus "lt r = lt p" unfolding r_def by simp
  qed
qed
    
lemma nadds_red_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "red B p r"
  shows "r \<noteq> 0"
  using nadds_red[OF assms] by simp
    
lemma nadds_red_lt:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "red B p r"
  shows "lt r = lt p"
  using nadds_red[OF assms] by simp
  
lemma nadds_red_rtrancl_lt:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "lt r = lt p"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case ..
next
  case (step y z)
  have "lt z = lt y"
  proof (rule nadds_red_lt)
    fix q
    assume "q \<in> B"
    thus "\<not> lt q adds\<^sub>t lt y" unfolding \<open>lt y = lt p\<close> by (rule nadds)
  qed fact
  with \<open>lt y = lt p\<close> show ?case by simp
qed
  
lemma nadds_red_rtrancl_nonzero:
  assumes nadds: "\<And>q. q \<in> B \<Longrightarrow> \<not> lt q adds\<^sub>t lt p" and "p \<noteq> 0" and rtrancl: "(red B)\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
  using rtrancl
proof (induct rule: rtranclp_induct)
  case base
  show ?case by fact
next
  case (step y z)
  from nadds \<open>(red B)\<^sup>*\<^sup>* p y\<close> have "lt y = lt p" by (rule nadds_red_rtrancl_lt)
  show "z \<noteq> 0"
  proof (rule nadds_red_nonzero)
    fix q
    assume "q \<in> B"
    thus "\<not> lt q adds\<^sub>t lt y" unfolding \<open>lt y = lt p\<close> by (rule nadds)
  qed fact
qed
  
lemma minimal_basis_red_rtrancl_nonzero:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "r \<noteq> 0"
proof (rule nadds_red_rtrancl_nonzero)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lt q adds\<^sub>t lt p" by (rule is_minimal_basisD2, fact+)
next
  show "p \<noteq> 0" by (rule is_minimal_basisD1, fact+)
qed fact

lemma minimal_basis_red_rtrancl_lt:
  assumes "is_minimal_basis B" and "p \<in> B" and "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "lt r = lt p"
proof (rule nadds_red_rtrancl_lt)
  fix q
  assume "q \<in> (B - {p})"
  hence "q \<in> B" and "q \<noteq> p" by auto
  show "\<not> lt q adds\<^sub>t lt p" by (rule is_minimal_basisD2, fact+)
qed fact
  
lemma is_minimal_basis_replace:
  assumes major: "is_minimal_basis B" and "p \<in> B" and red: "(red (B - {p}))\<^sup>*\<^sup>* p r"
  shows "is_minimal_basis (insert r (B - {p}))"
proof (rule is_minimal_basisI)
  fix q
  assume "q \<in> insert r (B - {p})"
  hence "q = r \<or> q \<in> B \<and> q \<noteq> p" by simp
  thus "q \<noteq> 0"
  proof
    assume "q = r"
    from assms show ?thesis unfolding \<open>q = r\<close> by (rule minimal_basis_red_rtrancl_nonzero)
  next
    assume "q \<in> B \<and> q \<noteq> p"
    hence "q \<in> B" ..
    with major show ?thesis by (rule is_minimal_basisD1)
  qed
next
  fix a b
  assume "a \<in> insert r (B - {p})" and "b \<in> insert r (B - {p})" and "a \<noteq> b"
  from assms have ltr: "lt r = lt p" by (rule minimal_basis_red_rtrancl_lt)
  from \<open>b \<in> insert r (B - {p})\<close> have b: "b = r \<or> b \<in> B \<and> b \<noteq> p" by simp
  from \<open>a \<in> insert r (B - {p})\<close> have "a = r \<or> a \<in> B \<and> a \<noteq> p" by simp
  thus "\<not> lt a adds\<^sub>t lt b"
  proof
    assume "a = r"
    hence lta: "lt a = lt p" using ltr by simp
    from b show ?thesis
    proof
      assume "b = r"
      with \<open>a \<noteq> b\<close> show ?thesis unfolding \<open>a = r\<close> by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" and "p \<noteq> b" by auto
      with major \<open>p \<in> B\<close> have "\<not> lt p adds\<^sub>t lt b" by (rule is_minimal_basisD2)
      thus ?thesis unfolding lta .
    qed
  next
    assume "a \<in> B \<and> a \<noteq> p"
    hence "a \<in> B" and "a \<noteq> p" by simp_all
    from b show ?thesis
    proof
      assume "b = r"
      from major \<open>a \<in> B\<close> \<open>p \<in> B\<close> \<open>a \<noteq> p\<close> have "\<not> lt a adds\<^sub>t lt p" by (rule is_minimal_basisD2)
      thus ?thesis unfolding \<open>b = r\<close> ltr by simp
    next
      assume "b \<in> B \<and> b \<noteq> p"
      hence "b \<in> B" ..
      from major \<open>a \<in> B\<close> \<open>b \<in> B\<close> \<open>a \<noteq> b\<close> show ?thesis by (rule is_minimal_basisD2)
    qed
  qed
qed

subsection \<open>Computing Minimal Bases\<close>

definition comp_min_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::zero) list" where
  "comp_min_basis xs = filter_min (\<lambda>x y. lt x adds\<^sub>t lt y) (filter (\<lambda>x. x \<noteq> 0) xs)"

lemma comp_min_basis_subset': "set (comp_min_basis xs) \<subseteq> {x \<in> set xs. x \<noteq> 0}"
proof -
  have "set (comp_min_basis xs) \<subseteq> set (filter (\<lambda>x. x \<noteq> 0) xs)"
    unfolding comp_min_basis_def by (rule filter_min_subset)
  also have "\<dots> = {x \<in> set xs. x \<noteq> 0}" by simp
  finally show ?thesis .
qed

lemma comp_min_basis_subset: "set (comp_min_basis xs) \<subseteq> set xs"
proof -
  have "set (comp_min_basis xs) \<subseteq> {x \<in> set xs. x \<noteq> 0}" by (rule comp_min_basis_subset')
  also have "... \<subseteq> set xs" by simp
  finally show ?thesis .
qed
    
lemma comp_min_basis_nonzero: "p \<in> set (comp_min_basis xs) \<Longrightarrow> p \<noteq> 0"
  using comp_min_basis_subset' by blast

lemma comp_min_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_min_basis xs)" and "lt q adds\<^sub>t lt p"
proof -
  let ?rel = "(\<lambda>x y. lt x adds\<^sub>t lt y)"
  have "transp ?rel" by (auto intro!: transpI dest: adds_term_trans)
  moreover have "reflp ?rel" by (simp add: reflp_def adds_term_refl)
  moreover from assms have "p \<in> set (filter (\<lambda>x. x \<noteq> 0) xs)" by simp
  ultimately obtain q where "q \<in> set (comp_min_basis xs)" and "lt q adds\<^sub>t lt p"
    unfolding comp_min_basis_def by (rule filter_min_relE)
  thus ?thesis ..
qed
  
lemma comp_min_basis_is_red:
  assumes "is_red (set xs) f"
  shows "is_red (set (comp_min_basis xs)) f"
proof -
  from assms obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_min_basis xs)" and "lt y adds\<^sub>t lt x"
    by (rule comp_min_basis_adds)
  show ?thesis
  proof (rule is_red_addsI)
    from \<open>lt y adds\<^sub>t lt x\<close> \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (rule adds_term_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_min_basis_nonzero)
  qed fact+
qed

lemma comp_min_basis_nadds:
  assumes "p \<in> set (comp_min_basis xs)" and "q \<in> set (comp_min_basis xs)" and "p \<noteq> q"
  shows "\<not> lt q adds\<^sub>t lt p"
proof
  have "transp (\<lambda>x y. lt x adds\<^sub>t lt y)" by (auto intro!: transpI dest: adds_term_trans)
  moreover note assms(2, 1)
  moreover assume "lt q adds\<^sub>t lt p"
  ultimately have "q = p" unfolding comp_min_basis_def by (rule filter_min_minimal)
  with assms(3) show False by simp
qed

lemma comp_min_basis_is_minimal_basis: "is_minimal_basis (set (comp_min_basis xs))"
  by (rule is_minimal_basisI, rule comp_min_basis_nonzero, assumption, rule comp_min_basis_nadds,
      assumption+, simp)

lemma comp_min_basis_distinct: "distinct (comp_min_basis xs)"
  unfolding comp_min_basis_def by (rule filter_min_distinct) (simp add: reflp_def adds_term_refl)

end (* ordered_term *)

subsection \<open>Auto-Reduction\<close>

context gd_term
begin

lemma is_minimal_basis_trd_is_minimal_basis:
  assumes "is_minimal_basis (set (x # xs))" and "x \<notin> set xs"
  shows "is_minimal_basis (set ((trd xs x) # xs))"
proof -
  from assms(1) have "is_minimal_basis (insert (trd xs x) (set (x # xs) - {x}))"
  proof (rule is_minimal_basis_replace, simp)
    from assms(2) have eq: "set (x # xs) - {x} = set xs" by simp
    show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
  qed
  also from assms(2) have "... = set ((trd xs x) # xs)" by auto
  finally show ?thesis .
qed

lemma is_minimal_basis_trd_distinct:
  assumes min: "is_minimal_basis (set (x # xs))" and dist: "distinct (x # xs)"
  shows "distinct ((trd xs x) # xs)"
proof -
  let ?y = "trd xs x"
  from min have lty: "lt ?y = lt x"
  proof (rule minimal_basis_red_rtrancl_lt, simp)
    from dist have "x \<notin> set xs" by simp
    hence eq: "set (x # xs) - {x} = set xs" by simp
    show "(red (set (x # xs) - {x}))\<^sup>*\<^sup>* x (trd xs x)" unfolding eq by (rule trd_red_rtrancl)
  qed
  have "?y \<notin> set xs"
  proof
    assume "?y \<in> set xs"
    hence "?y \<in> set (x # xs)" by simp
    with min have "\<not> lt ?y adds\<^sub>t lt x"
    proof (rule is_minimal_basisD2, simp)
      show "?y \<noteq> x"
      proof
        assume "?y = x"
        from dist have "x \<notin> set xs" by simp
        with \<open>?y \<in> set xs\<close> show False unfolding \<open>?y = x\<close> by simp
      qed
    qed
    thus False unfolding lty by (simp add: adds_term_refl)
  qed
  moreover from dist have "distinct xs" by simp
  ultimately show ?thesis by simp
qed

primrec comp_red_basis_aux :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list" where
  comp_red_basis_aux_base: "comp_red_basis_aux Nil ys = ys"|
  comp_red_basis_aux_rec: "comp_red_basis_aux (x # xs) ys = comp_red_basis_aux xs ((trd (xs @ ys) x) # ys)"
  
lemma subset_comp_red_basis_aux: "set ys \<subseteq> set (comp_red_basis_aux xs ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base ..
next
  case (Cons a xs)
  have "set ys \<subseteq> set ((trd (xs @ ys) a) # ys)" by auto
  also have "... \<subseteq> set (comp_red_basis_aux xs ((trd (xs @ ys) a) # ys))" by (rule Cons.hyps)
  finally show ?case unfolding comp_red_basis_aux_rec .
qed

lemma comp_red_basis_aux_nonzero:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)" and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "p \<noteq> 0"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case
  proof (rule is_minimal_basisD1)
    from Nil(1) show "is_minimal_basis (set ys)" by simp
  next
    from Nil(3) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  have "a \<in> set (a # xs @ ys)" by simp
  from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?ys = "trd (xs @ ys) a # ys"
  show ?case
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  next
    from Cons(4) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed
  
lemma comp_red_basis_aux_lt:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "lt ` set (xs @ ys) = lt ` set (comp_red_basis_aux xs ys)"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  from Cons(2) have "lt ?b = lt a" unfolding eq
  proof (rule minimal_basis_red_rtrancl_lt, simp)
    from a have eq2: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
    show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq2 by (rule trd_red_rtrancl)
  qed
  hence "lt ` set ((a # xs) @ ys) = lt ` set ((?b # xs) @ ys)" by simp
  also have "... = lt ` set (xs @ (?b # ys))" by simp
  finally have eq2: "lt ` set ((a # xs) @ ys) = lt ` set (xs @ (?b # ys))" .
  show ?case unfolding comp_red_basis_aux_rec eq2
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
qed
  
lemma comp_red_basis_aux_pmdl:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
  shows "pmdl (set (comp_red_basis_aux xs ys)) \<subseteq> pmdl (set (xs @ ys))"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  show ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a: "a \<notin> set (xs @ ys)" unfolding eq by simp
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have "pmdl (set (comp_red_basis_aux xs ?ys)) \<subseteq> pmdl (set (xs @ ?ys))"
  proof (rule Cons.hyps)
    from Cons(3) have "a \<notin> set (xs @ ys)" unfolding eq by simp
    with Cons(2) show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from Cons(2) Cons(3) show "distinct (xs @ ?ys)" unfolding distinct_reorder eq
      by (rule is_minimal_basis_trd_distinct)
  qed
  also have "... = pmdl (set (?b # xs @ ys))" by simp
  also from a have "... = pmdl (insert ?b (set (a # xs @ ys) - {a}))" by auto
  also have "... \<subseteq> pmdl (set (a # xs @ ys))"
  proof (rule pmdl.replace_span)
    have "a - (trd (xs @ ys) a) \<in> pmdl (set (xs @ ys))" by (rule trd_in_pmdl)
    have "a - (trd (xs @ ys) a) \<in> pmdl (set (a # xs @ ys))"
    proof
      show "pmdl (set (xs @ ys)) \<subseteq> pmdl (set (a # xs @ ys))" by (rule pmdl.span_mono) auto
    qed fact
    hence "- (a - (trd (xs @ ys) a)) \<in> pmdl (set (a # xs @ ys))" by (rule pmdl.span_neg)
    hence "(trd (xs @ ys) a) - a \<in> pmdl (set (a # xs @ ys))" by simp
    hence "((trd (xs @ ys) a) - a) + a \<in> pmdl (set (a # xs @ ys))"
    proof (rule pmdl.span_add)
      show "a \<in> pmdl (set (a # xs @ ys))"
      proof
        show "a \<in> set (a # xs @ ys)" by simp
      qed (rule pmdl.span_superset)
    qed
    thus "trd (xs @ ys) a \<in> pmdl (set (a # xs @ ys))" by simp
  qed
  also have "... = pmdl (set ((a # xs) @ ys))" by simp
  finally show ?case unfolding comp_red_basis_aux_rec .
qed
  
lemma comp_red_basis_aux_irred:
  assumes "is_minimal_basis (set (xs @ ys))" and "distinct (xs @ ys)"
    and "\<And>y. y \<in> set ys \<Longrightarrow> \<not> is_red (set (xs @ ys) - {y}) y"
    and "p \<in> set (comp_red_basis_aux xs ys)"
  shows "\<not> is_red (set (comp_red_basis_aux xs ys) - {p}) p"
  using assms
proof (induct xs arbitrary: ys)
  case Nil
  have "\<not> is_red (set ([] @ ys) - {p}) p"
  proof (rule Nil(3))
    from Nil(4) show "p \<in> set ys" unfolding comp_red_basis_aux_base .
  qed
  thus ?case unfolding comp_red_basis_aux_base by simp
next
  case (Cons a xs)
  have eq: "(a # xs) @ ys = a # (xs @ ys)" by simp
  from Cons(3) have a_notin: "a \<notin> set (xs @ ys)" unfolding eq by simp
  from Cons(2) have is_min: "is_minimal_basis (set (a # xs @ ys))" unfolding eq .
  let ?b = "trd (xs @ ys) a"
  let ?ys = "?b # ys"
  have dist: "distinct (?b # (xs @ ys))"
  proof (rule is_minimal_basis_trd_distinct, fact is_min)
    from Cons(3) show "distinct (a # xs @ ys)" unfolding eq .
  qed
  
  show ?case unfolding comp_red_basis_aux_rec
  proof (rule Cons.hyps)
    from Cons(2) a_notin show "is_minimal_basis (set (xs @ ?ys))" unfolding set_reorder eq
      by (rule is_minimal_basis_trd_is_minimal_basis)
  next
    from dist show "distinct (xs @ ?ys)" unfolding distinct_reorder .
  next
    fix y
    assume "y \<in> set ?ys"
    hence "y = ?b \<or> y \<in> set ys" by simp
    thus "\<not> is_red (set (xs @ ?ys) - {y}) y"
    proof
      assume "y = ?b"
      from dist have "?b \<notin> set (xs @ ys)" by simp
      hence eq3: "set (xs @ ?ys) - {?b} = set (xs @ ys)" unfolding set_reorder by simp
      have "\<not> is_red (set (xs @ ys)) ?b" by (rule trd_irred)
      thus ?thesis unfolding \<open>y = ?b\<close> eq3 .
    next
      assume "y \<in> set ys"
      hence irred: "\<not> is_red (set ((a # xs) @ ys) - {y}) y" by (rule Cons(4))
      from \<open>y \<in> set ys\<close> a_notin have "y \<noteq> a" by auto
      hence eq3: "set ((a # xs) @ ys) - {y} = {a} \<union> (set (xs @ ys) - {y})" by auto
      from irred have i1: "\<not> is_red {a} y" and i2: "\<not> is_red (set (xs @ ys) - {y}) y"
        unfolding eq3 is_red_union by simp_all
      show ?thesis unfolding set_reorder
      proof (cases "y = ?b")
        case True
        from i2 show "\<not> is_red (set (?b # xs @ ys) - {y}) y" by (simp add: True)
      next
        case False
        hence eq4: "set (?b # xs @ ys) - {y} = {?b} \<union> (set (xs @ ys) - {y})" by auto
        show "\<not> is_red (set (?b # xs @ ys) - {y}) y" unfolding eq4
        proof
          assume "is_red ({?b} \<union> (set (xs @ ys) - {y})) y"
          thus False unfolding is_red_union
          proof
            have ltb: "lt ?b = lt a"
            proof (rule minimal_basis_red_rtrancl_lt, fact is_min)
              show "a \<in> set (a # xs @ ys)" by simp
            next
              from a_notin have eq: "set (a # xs @ ys) - {a} = set (xs @ ys)" by simp
              show "(red (set (a # xs @ ys) - {a}))\<^sup>*\<^sup>* a ?b" unfolding eq by (rule trd_red_rtrancl)
            qed
            assume "is_red {?b} y"
            then obtain t where "t \<in> keys y" and "lt ?b adds\<^sub>t t" unfolding is_red_adds_iff by auto
            with ltb have "lt a adds\<^sub>t t" by simp
            have "is_red {a} y"
              by (rule is_red_addsI, rule, rule is_minimal_basisD1, fact is_min, simp, fact+)
            with i1 show False ..
          next
            assume "is_red (set (xs @ ys) - {y}) y"
            with i2 show False ..
          qed
        qed
      qed
    qed
  next
    from Cons(5) show "p \<in> set (comp_red_basis_aux xs ?ys)" unfolding comp_red_basis_aux_rec .
  qed
qed

lemma comp_red_basis_aux_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (comp_red_basis_aux xs ys)) (set xs \<union> set ys)"
proof (induct xs arbitrary: ys)
  case Nil
  show ?case by (simp, rule dgrad_p_set_le_subset, fact subset_refl)
next
  case (Cons x xs)
  let ?h = "trd (xs @ ys) x"
  have "dgrad_p_set_le d (set (comp_red_basis_aux xs (?h # ys))) (set xs \<union> set (?h # ys))"
    by (fact Cons)
  also have "... = insert ?h (set xs \<union> set ys)" by simp
  also have "dgrad_p_set_le d ... (insert x (set xs \<union> set ys))"
  proof (rule dgrad_p_set_leI_insert)
    show "dgrad_p_set_le d (set xs \<union> set ys) (insert x (set xs \<union> set ys))"
      by (rule dgrad_p_set_le_subset, blast)
  next
    have "(red (set (xs @ ys)))\<^sup>*\<^sup>* x ?h" by (rule trd_red_rtrancl)
    with assms have "dgrad_p_set_le d {?h} (insert x (set (xs @ ys)))"
      by (rule dgrad_p_set_le_red_rtrancl)
    thus "dgrad_p_set_le d {?h} (insert x (set xs \<union> set ys))" by simp
  qed
  finally show ?case by simp
qed

definition comp_red_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list"
  where "comp_red_basis xs = comp_red_basis_aux (comp_min_basis xs) []"
  
lemma comp_red_basis_nonzero:
  assumes "p \<in> set (comp_red_basis xs)"
  shows "p \<noteq> 0"
proof -
  have "is_minimal_basis (set ((comp_min_basis xs) @ []))" by (simp add: comp_min_basis_is_minimal_basis)
  moreover have "distinct ((comp_min_basis xs) @ [])" by (simp add: comp_min_basis_distinct)
  moreover from assms have "p \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  ultimately show ?thesis by (rule comp_red_basis_aux_nonzero)
qed

lemma pmdl_comp_red_basis_subset: "pmdl (set (comp_red_basis xs)) \<subseteq> pmdl (set xs)"
proof
  fix f
  assume fin: "f \<in> pmdl (set (comp_red_basis xs))"
  have "f \<in> pmdl (set (comp_min_basis xs))"
  proof
    from fin show  "f \<in> pmdl (set (comp_red_basis_aux (comp_min_basis xs) []))"
      unfolding comp_red_basis_def .
  next
    have "pmdl (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pmdl (set ((comp_min_basis xs) @ []))"
      by (rule comp_red_basis_aux_pmdl, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
    thus "pmdl (set (comp_red_basis_aux (comp_min_basis xs) [])) \<subseteq> pmdl (set (comp_min_basis xs))"
      by simp
  qed
  also from comp_min_basis_subset have "... \<subseteq> pmdl (set xs)" by (rule pmdl.span_mono)
  finally show "f \<in> pmdl (set xs)" .
qed

lemma comp_red_basis_adds:
  assumes "p \<in> set xs" and "p \<noteq> 0"
  obtains q where "q \<in> set (comp_red_basis xs)" and "lt q adds\<^sub>t lt p"
proof -
  from assms obtain q1 where "q1 \<in> set (comp_min_basis xs)" and "lt q1 adds\<^sub>t lt p"
    by (rule comp_min_basis_adds)
  from \<open>q1 \<in> set (comp_min_basis xs)\<close> have "lt q1 \<in> lt ` set (comp_min_basis xs)" by simp
  also have "... = lt ` set ((comp_min_basis xs) @ [])" by simp
  also have "... = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lt, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  finally obtain q where "q \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" and "lt q = lt q1"
    by auto
  show ?thesis
  proof
    show "q \<in> set (comp_red_basis xs)" unfolding comp_red_basis_def by fact
  next
    from \<open>lt q1 adds\<^sub>t lt p\<close> show "lt q adds\<^sub>t lt p" unfolding \<open>lt q = lt q1\<close> .
  qed
qed
  
lemma comp_red_basis_lt:
  assumes "p \<in> set (comp_red_basis xs)"
  obtains q where "q \<in> set xs" and "q \<noteq> 0" and "lt q = lt p"
proof -
  have eq: "lt ` set ((comp_min_basis xs) @ []) = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])"
    by (rule comp_red_basis_aux_lt, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
  from assms have "lt p \<in> lt ` set (comp_red_basis xs)" by simp
  also have "... = lt ` set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def ..
  also have "... = lt ` set (comp_min_basis xs)" unfolding eq[symmetric] by simp
  finally obtain q where "q \<in> set (comp_min_basis xs)" and "lt q = lt p" by auto
  show ?thesis
  proof
    show "q \<in> set xs" by (rule, fact, rule comp_min_basis_subset)
  next
    show "q \<noteq> 0" by (rule comp_min_basis_nonzero, fact)
  qed fact
qed

lemma comp_red_basis_is_red: "is_red (set (comp_red_basis xs)) f \<longleftrightarrow> is_red (set xs) f"
proof
  assume "is_red (set (comp_red_basis xs)) f"
  then obtain x t where "x \<in> set (comp_red_basis xs)" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set (comp_red_basis xs)\<close> obtain y where yin: "y \<in> set xs" and "y \<noteq> 0" and "lt y = lt x"
    by (rule comp_red_basis_lt)
  show "is_red (set xs) f"
  proof (rule is_red_addsI)
    from \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" unfolding \<open>lt y = lt x\<close> .
  qed fact+
next
  assume "is_red (set xs) f"
  then obtain x t where "x \<in> set xs" and "t \<in> keys f" and "x \<noteq> 0" and "lt x adds\<^sub>t t"
    by (rule is_red_addsE)
  from \<open>x \<in> set xs\<close> \<open>x \<noteq> 0\<close> obtain y where yin: "y \<in> set (comp_red_basis xs)" and "lt y adds\<^sub>t lt x"
    by (rule comp_red_basis_adds)
  show "is_red (set (comp_red_basis xs)) f"
  proof (rule is_red_addsI)
    from \<open>lt y adds\<^sub>t lt x\<close> \<open>lt x adds\<^sub>t t\<close> show "lt y adds\<^sub>t t" by (rule adds_term_trans)
  next
    from yin show "y \<noteq> 0" by (rule comp_red_basis_nonzero)
  qed fact+
qed
    
lemma comp_red_basis_is_auto_reduced: "is_auto_reduced (set (comp_red_basis xs))"
  unfolding is_auto_reduced_def remove_def
proof (intro ballI)
  fix x
  assume xin: "x \<in> set (comp_red_basis xs)"
  show "\<not> is_red (set (comp_red_basis xs) - {x}) x" unfolding comp_red_basis_def
  proof (rule comp_red_basis_aux_irred, simp_all, rule comp_min_basis_is_minimal_basis, rule comp_min_basis_distinct)
    from xin show "x \<in> set (comp_red_basis_aux (comp_min_basis xs) [])" unfolding comp_red_basis_def .
  qed
qed

lemma comp_red_basis_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (comp_red_basis xs)) (set xs)"
proof -
  have "dgrad_p_set_le d (set (comp_red_basis xs)) (set (comp_min_basis xs) \<union> set [])"
    unfolding comp_red_basis_def using assms by (rule comp_red_basis_aux_dgrad_p_set_le)
  also have "... = set (comp_min_basis xs)" by simp
  also from comp_min_basis_subset have "dgrad_p_set_le d ... (set xs)"
    by (rule dgrad_p_set_le_subset)
  finally show ?thesis .
qed

subsection \<open>Auto-Reduction and Monicity\<close>

definition comp_red_monic_basis :: "('t \<Rightarrow>\<^sub>0 'b) list \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) list" where
  "comp_red_monic_basis xs = map monic (comp_red_basis xs)"

lemma set_comp_red_monic_basis: "set (comp_red_monic_basis xs) = monic ` (set (comp_red_basis xs))"
  by (simp add: comp_red_monic_basis_def)

lemma comp_red_monic_basis_nonzero:
  assumes "p \<in> set (comp_red_monic_basis xs)"
  shows "p \<noteq> 0"
proof -
  from assms obtain p' where p_def: "p = monic p'" and p': "p' \<in> set (comp_red_basis xs)"
    unfolding set_comp_red_monic_basis ..
  from p' have "p' \<noteq> 0" by (rule comp_red_basis_nonzero)
  thus ?thesis unfolding p_def monic_0_iff .
qed

lemma comp_red_monic_basis_is_monic_set: "is_monic_set (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis by (rule image_monic_is_monic_set)

lemma pmdl_comp_red_monic_basis_subset: "pmdl (set (comp_red_monic_basis xs)) \<subseteq> pmdl (set xs)"
  unfolding set_comp_red_monic_basis pmdl_image_monic by (fact pmdl_comp_red_basis_subset)

lemma comp_red_monic_basis_is_auto_reduced: "is_auto_reduced (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis by (rule image_monic_is_auto_reduced, rule comp_red_basis_is_auto_reduced)

lemma comp_red_monic_basis_dgrad_p_set_le:
  assumes "dickson_grading d"
  shows "dgrad_p_set_le d (set (comp_red_monic_basis xs)) (set xs)"
proof -
  have "dgrad_p_set_le d (monic ` (set (comp_red_basis xs))) (set (comp_red_basis xs))"
    by (simp add: dgrad_p_set_le_def, fact dgrad_set_le_refl)
  also from assms have "dgrad_p_set_le d ... (set xs)" by (rule comp_red_basis_dgrad_p_set_le)
  finally show ?thesis by (simp add: set_comp_red_monic_basis)
qed

end (* gd_term *)

end (* theory *)
