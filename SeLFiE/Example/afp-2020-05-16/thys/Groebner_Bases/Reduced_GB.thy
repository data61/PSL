section \<open>Reduced Gr\"obner Bases\<close>

theory Reduced_GB
  imports Groebner_Bases Auto_Reduction
begin

lemma (in gd_term) GB_image_monic: "is_Groebner_basis (monic ` G) \<longleftrightarrow> is_Groebner_basis G"
  by (simp add: GB_alt_1)
  
subsection \<open>Definition and Uniqueness of Reduced Gr\"obner Bases\<close>

context ordered_term
begin
  
definition is_reduced_GB :: "('t \<Rightarrow>\<^sub>0 'b::field) set \<Rightarrow> bool" where
  "is_reduced_GB B \<equiv> is_Groebner_basis B \<and> is_auto_reduced B \<and> is_monic_set B \<and> 0 \<notin> B"
  
lemma reduced_GB_D1:
  assumes "is_reduced_GB G"
  shows "is_Groebner_basis G"
  using assms unfolding is_reduced_GB_def by simp

lemma reduced_GB_D2:
  assumes "is_reduced_GB G"
  shows "is_auto_reduced G"
  using assms unfolding is_reduced_GB_def by simp

 lemma reduced_GB_D3:
  assumes "is_reduced_GB G"
  shows "is_monic_set G"
  using assms unfolding is_reduced_GB_def by simp
     
lemma reduced_GB_D4:
  assumes "is_reduced_GB G" and "g \<in> G"
  shows "g \<noteq> 0"
  using assms unfolding is_reduced_GB_def by auto
    
lemma reduced_GB_lc:
  assumes major: "is_reduced_GB G" and "g \<in> G"
  shows "lc g = 1"
  by (rule is_monic_setD, rule reduced_GB_D3, fact major, fact \<open>g \<in> G\<close>, rule reduced_GB_D4, fact major, fact \<open>g \<in> G\<close>)

end (* ordered_term *)

context gd_term
begin

lemma is_reduced_GB_subsetI:
  assumes Ared: "is_reduced_GB A" and BGB: "is_Groebner_basis B" and Bmon: "is_monic_set B"
    and *: "\<And>a b. a \<in> A \<Longrightarrow> b \<in> B \<Longrightarrow> a \<noteq> 0 \<Longrightarrow> b \<noteq> 0 \<Longrightarrow> a - b \<noteq> 0 \<Longrightarrow> lt (a - b) \<in> keys b \<Longrightarrow> lt (a - b) \<prec>\<^sub>t lt b \<Longrightarrow> False"
    and id_eq: "pmdl A = pmdl B"
  shows "A \<subseteq> B"
proof
  fix a
  assume "a \<in> A"
    
  have "a \<noteq> 0" by (rule reduced_GB_D4, fact Ared, fact \<open>a \<in> A\<close>)
  have lca: "lc a = 1" by (rule reduced_GB_lc, fact Ared, fact \<open>a \<in> A\<close>)
  have AGB: "is_Groebner_basis A" by (rule reduced_GB_D1, fact Ared)
      
  from \<open>a \<in> A\<close> have "a \<in> pmdl A" by (rule pmdl.span_base)
  also have "... = pmdl B" using id_eq by simp
  finally have "a \<in> pmdl B" .

  from BGB this \<open>a \<noteq> 0\<close> obtain b where "b \<in> B" and "b \<noteq> 0" and baddsa: "lt b adds\<^sub>t lt a"
    by (rule GB_adds_lt)
  from Bmon this(1) this(2) have lcb: "lc b = 1" by (rule is_monic_setD)
  from \<open>b \<in> B\<close> have "b \<in> pmdl B" by (rule pmdl.span_base)
  also have "... = pmdl A" using id_eq by simp
  finally have "b \<in> pmdl A" .
      
  have lt_eq: "lt b = lt a"
  proof (rule ccontr)
    assume "lt b \<noteq> lt a"
    from AGB \<open>b \<in> pmdl A\<close> \<open>b \<noteq> 0\<close> obtain a'
      where "a' \<in> A" and "a' \<noteq> 0" and a'addsb: "lt a' adds\<^sub>t lt b" by (rule GB_adds_lt)
    have a'addsa: "lt a' adds\<^sub>t lt a" by (rule adds_term_trans, fact a'addsb, fact baddsa)
    have "lt a' \<noteq> lt a"
    proof
      assume "lt a' = lt a"
      hence aaddsa': "lt a adds\<^sub>t lt a'" by (simp add: adds_term_refl)
      have "lt a adds\<^sub>t lt b" by (rule adds_term_trans, fact aaddsa', fact a'addsb)
      have "lt a = lt b" by (rule adds_term_antisym, fact+)
      with \<open>lt b \<noteq> lt a\<close> show False by simp
    qed
    hence "a' \<noteq> a" by auto
    with \<open>a' \<in> A\<close> have "a' \<in> A - {a}" by blast
    have is_red: "is_red (A - {a}) a" by (intro is_red_addsI, fact, fact, rule lt_in_keys, fact+)
    have "\<not> is_red (A - {a}) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
    from this is_red show False ..
  qed
  
  have "a - b = 0"
  proof (rule ccontr)
    let ?c = "a - b"
    assume "?c \<noteq> 0"
    have "?c \<in> pmdl A" by (rule pmdl.span_diff, fact+)
    also have "... = pmdl B" using id_eq by simp
    finally have "?c \<in> pmdl B" .
        
    from \<open>b \<noteq> 0\<close> have "- b \<noteq> 0" by simp
    have "lt (-b) = lt a" unfolding lt_uminus by fact
    have "lc (-b) = - lc a" unfolding lc_uminus lca lcb ..
    from \<open>?c \<noteq> 0\<close> have "a + (-b) \<noteq> 0" by simp
    
    have "lt ?c \<in> keys ?c" by (rule lt_in_keys, fact)
    have "keys ?c \<subseteq> (keys a \<union> keys b)" by (fact keys_minus)
    with \<open>lt ?c \<in> keys ?c\<close> have "lt ?c \<in> keys a \<or> lt ?c \<in> keys b" by auto
    thus False
    proof
      assume "lt ?c \<in> keys a"
          
      from AGB \<open>?c \<in> pmdl A\<close> \<open>?c \<noteq> 0\<close> obtain a'
        where "a' \<in> A" and "a' \<noteq> 0" and a'addsc: "lt a' adds\<^sub>t lt ?c" by (rule GB_adds_lt)

      from a'addsc have "lt a' \<preceq>\<^sub>t lt ?c" by (rule ord_adds_term)
      also have "... = lt (a + (- b))" by simp
      also have "... \<prec>\<^sub>t lt a" by (rule lt_plus_lessI, fact+)
      finally have "lt a' \<prec>\<^sub>t lt a" .
      hence "lt a' \<noteq> lt a" by simp
      hence "a' \<noteq> a" by auto
      with \<open>a' \<in> A\<close> have "a' \<in> A - {a}" by blast
      
      have is_red: "is_red (A - {a}) a" by (intro is_red_addsI, fact, fact, fact+)
      have "\<not> is_red (A - {a}) a" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Ared, fact+)
      from this is_red show False ..
    next
      assume "lt ?c \<in> keys b"

      with \<open>a \<in> A\<close> \<open>b \<in> B\<close> \<open>a \<noteq> 0\<close> \<open>b \<noteq> 0\<close> \<open>?c \<noteq> 0\<close> show False
      proof (rule *)
        have "lt ?c = lt ((- b) + a)" by simp
        also have "... \<prec>\<^sub>t lt (-b)"
        proof (rule lt_plus_lessI)
          from \<open>?c \<noteq> 0\<close> show "-b + a \<noteq> 0" by simp
        next
          from \<open>lt (-b) = lt a\<close> show "lt a = lt (-b)" by simp
        next
          from \<open>lc (-b) = - lc a\<close> show "lc a = - lc (-b)" by simp
        qed
        finally show "lt ?c \<prec>\<^sub>t lt b" unfolding lt_uminus .
      qed
    qed
  qed
  
  hence "a = b" by simp
  with \<open>b \<in> B\<close> show "a \<in> B" by simp
qed

lemma is_reduced_GB_unique':
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pmdl A = pmdl B"
  shows "A \<subseteq> B"
proof -
  from Bred have BGB: "is_Groebner_basis B" by (rule reduced_GB_D1)
  with assms(1) show ?thesis
  proof (rule is_reduced_GB_subsetI)
    from Bred show "is_monic_set B" by (rule reduced_GB_D3)
  next
    fix a b :: "'t \<Rightarrow>\<^sub>0 'b"
    let ?c = "a - b"
    assume "a \<in> A" and "b \<in> B" and "a \<noteq> 0" and "b \<noteq> 0" and "?c \<noteq> 0" and "lt ?c \<in> keys b" and "lt ?c \<prec>\<^sub>t lt b"
  
    from \<open>a \<in> A\<close> have "a \<in> pmdl B" by (simp only: id_eq[symmetric], rule pmdl.span_base)
    moreover from \<open>b \<in> B\<close> have "b \<in> pmdl B" by (rule pmdl.span_base)
    ultimately have "?c \<in> pmdl B" by (rule pmdl.span_diff)
    from BGB this \<open>?c \<noteq> 0\<close> obtain b'
      where "b' \<in> B" and "b' \<noteq> 0" and b'addsc: "lt b' adds\<^sub>t lt ?c" by (rule GB_adds_lt)
  
    from b'addsc have "lt b' \<preceq>\<^sub>t lt ?c" by (rule ord_adds_term)
    also have "... \<prec>\<^sub>t lt b" by fact
    finally have "lt b' \<prec>\<^sub>t lt b" unfolding lt_uminus .
    hence "lt b' \<noteq> lt b" by simp
    hence "b' \<noteq> b" by auto
    with \<open>b' \<in> B\<close> have "b' \<in> B - {b}" by blast
        
    have is_red: "is_red (B - {b}) b" by (intro is_red_addsI, fact, fact, fact+)
    have "\<not> is_red (B - {b}) b" by (rule is_auto_reducedD, rule reduced_GB_D2, fact Bred, fact+)
    from this is_red show False ..
  qed fact
qed
  
theorem is_reduced_GB_unique:
  assumes Ared: "is_reduced_GB A" and Bred: "is_reduced_GB B" and id_eq: "pmdl A = pmdl B"
  shows "A = B"
proof
  from assms show "A \<subseteq> B" by (rule is_reduced_GB_unique')
next
  from Bred Ared id_eq[symmetric] show "B \<subseteq> A" by (rule is_reduced_GB_unique')
qed
  
subsection \<open>Computing Reduced Gr\"obner Bases by Auto-Reduction\<close>

subsubsection \<open>Minimal Bases\<close>

lemma minimal_basis_is_reduced_GB:
  assumes "is_minimal_basis B" and "is_monic_set B" and "is_reduced_GB G" and "G \<subseteq> B"
    and "pmdl B = pmdl G"
  shows "B = G"
  using _ assms(3) assms(5)
proof (rule is_reduced_GB_unique)
  from assms(3) have "is_Groebner_basis G" by (rule reduced_GB_D1)
  show "is_reduced_GB B" unfolding is_reduced_GB_def
  proof (intro conjI)
    show "0 \<notin> B"
    proof
      assume "0 \<in> B"
      with assms(1) have "0 \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b)" by (rule is_minimal_basisD1)
      thus False by simp
    qed
  next
    from \<open>is_Groebner_basis G\<close> assms(4) assms(5) show "is_Groebner_basis B" by (rule GB_subset)
  next
    show "is_auto_reduced B" unfolding is_auto_reduced_def
    proof (intro ballI notI)
      fix b
      assume "b \<in> B"
      with assms(1) have "b \<noteq> 0" by (rule is_minimal_basisD1)
      assume "is_red (B - {b}) b"
      then obtain f where "f \<in> B - {b}" and "is_red {f} b" by (rule is_red_singletonI)
      from this(1) have "f \<in> B" and "f \<noteq> b" by simp_all

      from assms(1) \<open>f \<in> B\<close> have "f \<noteq> 0" by (rule is_minimal_basisD1)
      from \<open>f \<in> B\<close> have "f \<in> pmdl B" by (rule pmdl.span_base)
      hence "f \<in> pmdl G" by (simp only: assms(5))
      from \<open>is_Groebner_basis G\<close> this \<open>f \<noteq> 0\<close> obtain g where "g \<in> G" and "g \<noteq> 0" and "lt g adds\<^sub>t lt f"
        by (rule GB_adds_lt)
      from \<open>g \<in> G\<close> \<open>G \<subseteq> B\<close> have "g \<in> B" ..
      have "g = f"
      proof (rule ccontr)
        assume "g \<noteq> f"
        with assms(1) \<open>g \<in> B\<close> \<open>f \<in> B\<close> have "\<not> lt g adds\<^sub>t lt f" by (rule is_minimal_basisD2)
        from this \<open>lt g adds\<^sub>t lt f\<close> show False ..
      qed
      with \<open>g \<in> G\<close> have "f \<in> G" by simp
      with \<open>f \<in> B - {b}\<close> \<open>is_red {f} b\<close> have red: "is_red (G - {b}) b"
        by (meson Diff_iff is_red_singletonD)

      from \<open>b \<in> B\<close> have "b \<in> pmdl B" by (rule pmdl.span_base)
      hence "b \<in> pmdl G" by (simp only: assms(5))
      from \<open>is_Groebner_basis G\<close> this \<open>b \<noteq> 0\<close> obtain g' where "g' \<in> G" and "g' \<noteq> 0" and "lt g' adds\<^sub>t lt b"
        by (rule GB_adds_lt)
      from \<open>g' \<in> G\<close> \<open>G \<subseteq> B\<close> have "g' \<in> B" ..
      have "g' = b"
      proof (rule ccontr)
        assume "g' \<noteq> b"
        with assms(1) \<open>g' \<in> B\<close> \<open>b \<in> B\<close> have "\<not> lt g' adds\<^sub>t lt b" by (rule is_minimal_basisD2)
        from this \<open>lt g' adds\<^sub>t lt b\<close> show False ..
      qed
      with \<open>g' \<in> G\<close> have "b \<in> G" by simp

      from assms(3) have "is_auto_reduced G" by (rule reduced_GB_D2)
      from this \<open>b \<in> G\<close> have "\<not> is_red (G - {b}) b" by (rule is_auto_reducedD)
      from this red show False ..
    qed
  qed fact
qed

subsubsection \<open>Computing Minimal Bases\<close>

lemma comp_min_basis_pmdl:
  assumes "is_Groebner_basis (set xs)"
  shows "pmdl (set (comp_min_basis xs)) = pmdl (set xs)" (is "pmdl (set ?ys) = _")
  using finite_set
proof (rule pmdl_eqI_adds_lt_finite)
  from comp_min_basis_subset show *: "pmdl (set ?ys) \<subseteq> pmdl (set xs)" by (rule pmdl.span_mono)
next
  fix f
  assume "f \<in> pmdl (set xs)" and "f \<noteq> 0"
  with assms obtain g where "g \<in> set xs" and "g \<noteq> 0" and 1: "lt g adds\<^sub>t lt f" by (rule GB_adds_lt)
  from this(1, 2) obtain g' where "g' \<in> set ?ys" and 2: "lt g' adds\<^sub>t lt g"
    by (rule comp_min_basis_adds)
  note this(1)
  moreover from this have "g' \<noteq> 0" by (rule comp_min_basis_nonzero)
  moreover from 2 1 have "lt g' adds\<^sub>t lt f" by (rule adds_term_trans)
  ultimately show "\<exists>g\<in>set ?ys. g \<noteq> 0 \<and> lt g adds\<^sub>t lt f" by blast
qed

lemma comp_min_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_min_basis xs))" (is "is_Groebner_basis (set ?ys)")
  unfolding GB_alt_2_finite[OF finite_set]
proof (intro ballI impI)
  fix f
  assume "f \<in> pmdl (set ?ys)"
  also from assms have "\<dots> = pmdl (set xs)" by (rule comp_min_basis_pmdl)
  finally have "f \<in> pmdl (set xs)" .
  moreover assume "f \<noteq> 0"
  ultimately have "is_red (set xs) f" using assms unfolding GB_alt_2_finite[OF finite_set] by blast
  thus "is_red (set ?ys) f" by (rule comp_min_basis_is_red)
qed

subsubsection \<open>Computing Reduced Bases\<close>

lemma comp_red_basis_pmdl:
  assumes "is_Groebner_basis (set xs)"
  shows "pmdl (set (comp_red_basis xs)) = pmdl (set xs)"
proof (rule, fact pmdl_comp_red_basis_subset, rule)
  fix f
  assume "f \<in> pmdl (set xs)"
  show "f \<in> pmdl (set (comp_red_basis xs))"
  proof (cases "f = 0")
    case True
    show ?thesis unfolding True by (rule pmdl.span_zero)
  next
    case False
    let ?xs = "comp_red_basis xs"
    have "(red (set ?xs))\<^sup>*\<^sup>* f 0"
    proof (rule is_red_implies_0_red_finite, fact finite_set, fact pmdl_comp_red_basis_subset)
      fix q
      assume "q \<noteq> 0" and "q \<in> pmdl (set xs)"
      with assms have "is_red (set xs) q" by (rule GB_imp_reducibility)
      thus "is_red (set (comp_red_basis xs)) q" unfolding comp_red_basis_is_red .
    qed fact
    thus ?thesis by (rule red_rtranclp_0_in_pmdl)
  qed
qed
  
lemma comp_red_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_basis xs))"
  unfolding GB_alt_2_finite[OF finite_set]
proof (intro ballI impI)
  fix f
  assume fin: "f \<in> pmdl (set (comp_red_basis xs))"
  hence "f \<in> pmdl (set xs)" unfolding comp_red_basis_pmdl[OF assms] .
  assume "f \<noteq> 0"
  from assms \<open>f \<noteq> 0\<close> \<open>f \<in> pmdl (set xs)\<close> show "is_red (set (comp_red_basis xs)) f"
    by (simp add: comp_red_basis_is_red GB_alt_2_finite)
qed

subsubsection \<open>Computing Reduced Gr\"obner Bases\<close>

lemma comp_red_monic_basis_pmdl:
  assumes "is_Groebner_basis (set xs)"
  shows "pmdl (set (comp_red_monic_basis xs)) = pmdl (set xs)"
  unfolding set_comp_red_monic_basis pmdl_image_monic comp_red_basis_pmdl[OF assms] ..
    
lemma comp_red_monic_basis_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_Groebner_basis (set (comp_red_monic_basis xs))"
  unfolding set_comp_red_monic_basis GB_image_monic using assms by (rule comp_red_basis_GB)
    
lemma comp_red_monic_basis_is_reduced_GB:
  assumes "is_Groebner_basis (set xs)"
  shows "is_reduced_GB (set (comp_red_monic_basis xs))"
  unfolding is_reduced_GB_def
proof (intro conjI, rule comp_red_monic_basis_GB, fact assms,
       rule comp_red_monic_basis_is_auto_reduced, rule comp_red_monic_basis_is_monic_set, intro notI)
  assume "0 \<in> set (comp_red_monic_basis xs)"
  hence "0 \<noteq> (0::'t \<Rightarrow>\<^sub>0 'b)" by (rule comp_red_monic_basis_nonzero)
  thus False by simp
qed

lemma ex_finite_reduced_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  obtains G where "G \<subseteq> dgrad_p_set d m" and "finite G" and "is_reduced_GB G" and "pmdl G = pmdl F"
proof -
  from assms obtain G0 where G0_sub: "G0 \<subseteq> dgrad_p_set d m" and fin: "finite G0"
    and gb: "is_Groebner_basis G0" and pid: "pmdl G0 = pmdl F"
    by (rule ex_finite_GB_dgrad_p_set)
  from fin obtain xs where set: "G0 = set xs" using finite_list by blast
  let ?G = "set (comp_red_monic_basis xs)"
  show ?thesis
  proof
    from assms(1) have "dgrad_p_set_le d (set (comp_red_monic_basis xs)) G0" unfolding set
      by (rule comp_red_monic_basis_dgrad_p_set_le)
    from this G0_sub show "set (comp_red_monic_basis xs) \<subseteq> dgrad_p_set d m"
      by (rule dgrad_p_set_le_dgrad_p_set)
  next
    from gb show rgb: "is_reduced_GB ?G" unfolding set
      by (rule comp_red_monic_basis_is_reduced_GB)
  next
    from gb show "pmdl ?G = pmdl F" unfolding set pid[symmetric]
      by (rule comp_red_monic_basis_pmdl)
  qed (fact finite_set)
qed

theorem ex_unique_reduced_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "\<exists>!G. G \<subseteq> dgrad_p_set d m \<and> finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F"
proof -
  from assms obtain G where "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "is_reduced_GB G" and G: "pmdl G = pmdl F" by (rule ex_finite_reduced_GB_dgrad_p_set)
  hence "G \<subseteq> dgrad_p_set d m \<and> finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F" by simp
  thus ?thesis
  proof (rule ex1I)
    fix G'
    assume "G' \<subseteq> dgrad_p_set d m \<and> finite G' \<and> is_reduced_GB G' \<and> pmdl G' = pmdl F"
    hence "is_reduced_GB G'" and G': "pmdl G' = pmdl F" by simp_all
    note this(1) \<open>is_reduced_GB G\<close>
    moreover have "pmdl G' = pmdl G" by (simp only: G G')
    ultimately show "G' = G" by (rule is_reduced_GB_unique)
  qed
qed

corollary ex_unique_reduced_GB_dgrad_p_set':
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "\<exists>!G. finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F"
proof -
  from assms obtain G where "G \<subseteq> dgrad_p_set d m" and "finite G"
    and "is_reduced_GB G" and G: "pmdl G = pmdl F" by (rule ex_finite_reduced_GB_dgrad_p_set)
  hence "finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F" by simp
  thus ?thesis
  proof (rule ex1I)
    fix G'
    assume "finite G' \<and> is_reduced_GB G' \<and> pmdl G' = pmdl F"
    hence "is_reduced_GB G'" and G': "pmdl G' = pmdl F" by simp_all
    note this(1) \<open>is_reduced_GB G\<close>
    moreover have "pmdl G' = pmdl G" by (simp only: G G')
    ultimately show "G' = G" by (rule is_reduced_GB_unique)
  qed
qed
  
definition reduced_GB :: "('t \<Rightarrow>\<^sub>0 'b) set \<Rightarrow> ('t \<Rightarrow>\<^sub>0 'b::field) set"
  where "reduced_GB B = (THE G. finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl B)"

text \<open>@{const reduced_GB} returns the unique reduced Gr\"obner basis of the given set, provided its
  Dickson grading is bounded. Combining @{const comp_red_monic_basis} with any function for computing
  Gr\"obner bases, e.\,g. \<open>gb\<close> from theory "Buchberger", makes @{const reduced_GB} computable.\<close>

lemma finite_reduced_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "finite (reduced_GB F)"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, fact, elim conjE)

lemma reduced_GB_is_reduced_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "is_reduced_GB (reduced_GB F)"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, fact, elim conjE)

lemma reduced_GB_is_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "is_Groebner_basis (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def ..
qed

lemma reduced_GB_is_auto_reduced_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "is_auto_reduced (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
    
lemma reduced_GB_is_monic_set_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "is_monic_set (reduced_GB F)"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed
  
lemma reduced_GB_nonzero_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "0 \<notin> reduced_GB F"
proof -
  from assms have "is_reduced_GB (reduced_GB F)" by (rule reduced_GB_is_reduced_GB_dgrad_p_set)
  thus ?thesis unfolding is_reduced_GB_def by simp
qed

lemma reduced_GB_pmdl_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "pmdl (reduced_GB F) = pmdl F"
  unfolding reduced_GB_def
  by (rule the1I2, rule ex_unique_reduced_GB_dgrad_p_set', fact, fact, fact, elim conjE)

lemma reduced_GB_unique_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
    and "is_reduced_GB G" and "pmdl G = pmdl F"
  shows "reduced_GB F = G"
  by (rule is_reduced_GB_unique, rule reduced_GB_is_reduced_GB_dgrad_p_set, fact+,
      simp only: reduced_GB_pmdl_dgrad_p_set[OF assms(1, 2, 3)] assms(5))

lemma reduced_GB_dgrad_p_set:
  assumes "dickson_grading d" and "finite (component_of_term ` Keys F)" and "F \<subseteq> dgrad_p_set d m"
  shows "reduced_GB F \<subseteq> dgrad_p_set d m"
proof -
  from assms obtain G where G: "G \<subseteq> dgrad_p_set d m" and "is_reduced_GB G" and "pmdl G = pmdl F"
    by (rule ex_finite_reduced_GB_dgrad_p_set)
  from assms this(2, 3) have "reduced_GB F = G" by (rule reduced_GB_unique_dgrad_p_set)
  with G show ?thesis by simp
qed

lemma reduced_GB_unique:
  assumes "finite G" and "is_reduced_GB G" and "pmdl G = pmdl F"
  shows "reduced_GB F = G"
proof -
  from assms have "finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F" by simp
  thus ?thesis unfolding reduced_GB_def
  proof (rule the_equality)
    fix G'
    assume "finite G' \<and> is_reduced_GB G' \<and> pmdl G' = pmdl F"
    hence "is_reduced_GB G'" and eq: "pmdl G' = pmdl F" by simp_all
    note this(1)
    moreover note assms(2)
    moreover have "pmdl G' = pmdl G" by (simp only: assms(3) eq)
    ultimately show "G' = G" by (rule is_reduced_GB_unique)
  qed
qed

lemma is_reduced_GB_empty: "is_reduced_GB {}"
  by (simp add: is_reduced_GB_def is_Groebner_basis_empty is_monic_set_def is_auto_reduced_def)

lemma is_reduced_GB_singleton: "is_reduced_GB {f} \<longleftrightarrow> lc f = 1"
proof
  assume "is_reduced_GB {f}"
  hence "is_monic_set {f}" and "f \<noteq> 0" by (rule reduced_GB_D3, rule reduced_GB_D4) simp
  from this(1) _ this(2) show "lc f = 1" by (rule is_monic_setD) simp
next
  assume "lc f = 1"
  moreover from this have "f \<noteq> 0" by auto
  ultimately show "is_reduced_GB {f}"
    by (simp add: is_reduced_GB_def is_Groebner_basis_singleton is_monic_set_def is_auto_reduced_def
        not_is_red_empty)
qed

lemma reduced_GB_empty: "reduced_GB {} = {}"
  using finite.emptyI is_reduced_GB_empty refl by (rule reduced_GB_unique)

lemma reduced_GB_singleton: "reduced_GB {f} = (if f = 0 then {} else {monic f})"
proof (cases "f = 0")
  case True
  from finite.emptyI is_reduced_GB_empty have "reduced_GB {f} = {}"
    by (rule reduced_GB_unique) (simp add: True flip: pmdl.span_Diff_zero[of "{0}"])
  with True show ?thesis by simp
next
  case False
  have "reduced_GB {f} = {monic f}"
  proof (rule reduced_GB_unique)
    from False have "lc f \<noteq> 0" by (rule lc_not_0)
    thus "is_reduced_GB {monic f}" by (simp add: is_reduced_GB_singleton monic_def)
  next
    have "pmdl {monic f} = pmdl (monic ` {f})" by simp
    also have "\<dots> = pmdl {f}" by (fact pmdl_image_monic)
    finally show "pmdl {monic f} = pmdl {f}" .
  qed simp
  with False show ?thesis by simp
qed

lemma ex_unique_reduced_GB_finite: "finite F \<Longrightarrow> (\<exists>!G. finite G \<and> is_reduced_GB G \<and> pmdl G = pmdl F)"
  by (rule ex_unique_reduced_GB_dgrad_p_set', rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma finite_reduced_GB_finite: "finite F \<Longrightarrow> finite (reduced_GB F)"
  by (rule finite_reduced_GB_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_is_reduced_GB_finite: "finite F \<Longrightarrow> is_reduced_GB (reduced_GB F)"
  by (rule reduced_GB_is_reduced_GB_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_is_GB_finite: "finite F \<Longrightarrow> is_Groebner_basis (reduced_GB F)"
  by (rule reduced_GB_is_GB_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_is_auto_reduced_finite: "finite F \<Longrightarrow> is_auto_reduced (reduced_GB F)"
  by (rule reduced_GB_is_auto_reduced_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_is_monic_set_finite: "finite F \<Longrightarrow> is_monic_set (reduced_GB F)"
  by (rule reduced_GB_is_monic_set_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_nonzero_finite: "finite F \<Longrightarrow> 0 \<notin> reduced_GB F"
  by (rule reduced_GB_nonzero_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_pmdl_finite: "finite F \<Longrightarrow> pmdl (reduced_GB F) = pmdl F"
  by (rule reduced_GB_pmdl_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

lemma reduced_GB_unique_finite: "finite F \<Longrightarrow> is_reduced_GB G \<Longrightarrow> pmdl G = pmdl F \<Longrightarrow> reduced_GB F = G"
  by (rule reduced_GB_unique_dgrad_p_set, rule dickson_grading_dgrad_dummy,
      erule finite_imp_finite_component_Keys, erule dgrad_p_set_exhaust_expl)

end (* gd_term *)

subsubsection \<open>Properties of the Reduced Gr\"obner Basis of an Ideal\<close>

context gd_powerprod
begin

lemma ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set:
  assumes "dickson_grading d" and "F \<subseteq> punit.dgrad_p_set d m"
  shows "ideal F = UNIV \<longleftrightarrow> punit.reduced_GB F = {1}"
proof -
  have fin: "finite (local.punit.component_of_term ` Keys F)" by simp
  show ?thesis
  proof
    assume "ideal F = UNIV"
    from assms(1) fin assms(2) show "punit.reduced_GB F = {1}"
    proof (rule punit.reduced_GB_unique_dgrad_p_set)
      show "punit.is_reduced_GB {1}" unfolding punit.is_reduced_GB_def
      proof (intro conjI, fact punit.is_Groebner_basis_singleton)
        show "punit.is_auto_reduced {1}" unfolding punit.is_auto_reduced_def
          by (rule ballI, simp add: remove_def punit.not_is_red_empty)
      next
        show "punit.is_monic_set {1}"
          by (rule punit.is_monic_setI, simp del: single_one add: single_one[symmetric])
      qed simp
    next
      have "punit.pmdl {1} = ideal {1}" by simp
      also have "... = ideal F"
      proof (simp only: \<open>ideal F = UNIV\<close> ideal_eq_UNIV_iff_contains_one)
        have "1 \<in> {1}" ..
        with module_times show "1 \<in> ideal {1}" by (rule module.span_base)
      qed
      also have "... = punit.pmdl F" by simp
      finally show "punit.pmdl {1} = punit.pmdl F" .
    qed
  next
    assume "punit.reduced_GB F = {1}"
    hence "1 \<in> punit.reduced_GB F" by simp
    hence "1 \<in> punit.pmdl (punit.reduced_GB F)" by (rule punit.pmdl.span_base)
    also from assms(1) fin assms(2) have "... = punit.pmdl F" by (rule punit.reduced_GB_pmdl_dgrad_p_set)
    finally show "ideal F = UNIV" by (simp add: ideal_eq_UNIV_iff_contains_one)
  qed
qed

lemmas ideal_eq_UNIV_iff_reduced_GB_eq_one_finite =
  ideal_eq_UNIV_iff_reduced_GB_eq_one_dgrad_p_set[OF dickson_grading_dgrad_dummy punit.dgrad_p_set_exhaust_expl]
                                                                          
end (* gd_powerprod *)

subsubsection \<open>Context @{locale od_term}\<close>

context od_term
begin

lemmas ex_unique_reduced_GB =
  ex_unique_reduced_GB_dgrad_p_set'[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas finite_reduced_GB =
  finite_reduced_GB_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_is_reduced_GB =
  reduced_GB_is_reduced_GB_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_is_GB =
  reduced_GB_is_GB_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_is_auto_reduced =
  reduced_GB_is_auto_reduced_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_is_monic_set =
  reduced_GB_is_monic_set_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_nonzero =
  reduced_GB_nonzero_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_pmdl =
  reduced_GB_pmdl_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]
lemmas reduced_GB_unique =
  reduced_GB_unique_dgrad_p_set[OF dickson_grading_zero _ subset_dgrad_p_set_zero]

end (* od_term *)

end (* theory *)
