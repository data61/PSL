chapter\<open>Basic Predicates\<close>

theory Predicates
imports SyntaxN
begin

section \<open>The Subset Relation\<close>

nominal_function Subset :: "tm \<Rightarrow> tm \<Rightarrow> fm"   (infixr "SUBS" 150)
  where "atom z \<sharp> (t, u) \<Longrightarrow> t SUBS u = All2 z t ((Var z) IN u)"
  by (auto simp: eqvt_def Subset_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

declare Subset.simps [simp del]

lemma Subset_fresh_iff [simp]: "a \<sharp> t SUBS u \<longleftrightarrow> a \<sharp> t \<and> a \<sharp> u"
apply (rule obtain_fresh [where x="(t, u)"])
apply (subst Subset.simps, auto)
done

lemma eval_fm_Subset [simp]: "eval_fm e (Subset t u) \<longleftrightarrow> (\<lbrakk>t\<rbrakk>e \<le> \<lbrakk>u\<rbrakk>e)"
apply (rule obtain_fresh [where x="(t, u)"])
apply (subst Subset.simps, auto)
done

lemma subst_fm_Subset [simp]: "(t SUBS u)(i::=x) = (subst i x t) SUBS (subst i x u)"
proof -
  obtain j::name where "atom j \<sharp> (i,x,t,u)"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp: Subset.simps [of j])
qed

lemma Subset_I:
  assumes "insert ((Var i) IN t) H \<turnstile> (Var i) IN u" "atom i \<sharp> (t,u)" "\<forall>B \<in> H. atom i \<sharp> B"
  shows "H \<turnstile> t SUBS u"
by (subst Subset.simps [of i]) (auto simp: assms)

lemma Subset_D:
  assumes major: "H \<turnstile> t SUBS u" and minor: "H \<turnstile> a IN t" shows "H \<turnstile> a IN u"
proof -
  obtain i::name where i: "atom i \<sharp> (t, u)"
    by (rule obtain_fresh)
  hence "H \<turnstile> (Var i IN t IMP Var i IN u) (i::=a)"
    by (metis Subset.simps major All_D)
  thus ?thesis
    using i  by simp (metis MP_same minor)
qed

lemma Subset_E: "H \<turnstile> t SUBS u \<Longrightarrow> H \<turnstile> a IN t \<Longrightarrow> insert (a IN u) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis Subset_D cut_same)

lemma Subset_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> u EQ u' \<Longrightarrow> H \<turnstile> t SUBS u IFF t' SUBS u'"
  by (rule P2_cong) auto

lemma Set_MP: "x SUBS y \<in> H \<Longrightarrow> z IN x \<in> H \<Longrightarrow> insert (z IN y) H \<turnstile> A \<Longrightarrow> H \<turnstile> A"
  by (metis Assume Subset_D cut_same insert_absorb)

lemma Zero_Subset_I [intro!]: "H \<turnstile> Zero SUBS t"
proof -
  have "{} \<turnstile> Zero SUBS t"
    by (rule obtain_fresh [where x="(Zero,t)"]) (auto intro: Subset_I)
  thus ?thesis
    by (auto intro: thin)
qed

lemma Zero_SubsetE: "H \<turnstile> A \<Longrightarrow> insert (Zero SUBS X) H \<turnstile> A"
  by (rule thin1)

lemma Subset_Zero_D:
   assumes "H \<turnstile> t SUBS Zero" shows "H \<turnstile> t EQ Zero"
proof -
  obtain i::name where i [iff]: "atom i \<sharp> t"
    by (rule obtain_fresh)
  have "{t SUBS Zero} \<turnstile> t EQ Zero"
  proof (rule Eq_Zero_I)
    fix A
    show "{Var i IN t, t SUBS Zero} \<turnstile> A"
      by (metis Hyp Subset_D insertI1 thin1 Mem_Zero_E cut1)
  qed auto
  thus ?thesis
    by (metis assms cut1)
qed

lemma Subset_refl: "H \<turnstile> t SUBS t"
proof -
  obtain i::name where "atom i \<sharp> t"
    by (rule obtain_fresh)
  thus ?thesis
    by (metis Assume Subset_I empty_iff fresh_Pair thin0)
qed

lemma Eats_Subset_Iff: "H \<turnstile> Eats x y SUBS z IFF (x SUBS z) AND (y IN z)"
proof -
  obtain i::name where i: "atom i \<sharp> (x,y,z)"
    by (rule obtain_fresh)
  have "{} \<turnstile> (Eats x y SUBS z) IFF (x SUBS z AND y IN z)"
  proof (rule Iff_I) 
    show "{Eats x y SUBS z} \<turnstile> x SUBS z AND y IN z"
    proof (rule Conj_I) 
      show "{Eats x y SUBS z} \<turnstile> x SUBS z"
        apply (rule Subset_I [where i=i]) using i
        apply (auto intro: Subset_D Mem_Eats_I1) 
        done
    next
      show "{Eats x y SUBS z} \<turnstile> y IN z"
        by (metis Subset_D Assume Mem_Eats_I2 Refl) 
    qed
  next
    show "{x SUBS z AND y IN z} \<turnstile> Eats x y SUBS z" using i
      by (auto intro!: Subset_I [where i=i] intro: Subset_D Mem_cong [THEN Iff_MP2_same])
  qed
  thus ?thesis
    by (rule thin0) 
qed

lemma Eats_Subset_I [intro!]: "H \<turnstile> x SUBS z \<Longrightarrow> H \<turnstile> y IN z \<Longrightarrow> H \<turnstile> Eats x y SUBS z"
  by (metis Conj_I Eats_Subset_Iff Iff_MP2_same)

lemma Eats_Subset_E [intro!]:
  "insert (x SUBS z) (insert (y IN z) H) \<turnstile> C \<Longrightarrow> insert (Eats x y SUBS z) H \<turnstile> C"
  by (metis Conj_E Eats_Subset_Iff Iff_MP_left')

text\<open>A surprising proof: a consequence of @{thm Eats_Subset_Iff} and reflexivity!\<close>
lemma Subset_Eats_I [intro!]: "H \<turnstile> x SUBS Eats x y"
  by (metis Conj_E1 Eats_Subset_Iff Iff_MP_same Subset_refl)

lemma SUCC_Subset_I [intro!]: "H \<turnstile> x SUBS z \<Longrightarrow> H \<turnstile> x IN z \<Longrightarrow> H \<turnstile> SUCC x SUBS z"
  by (metis Eats_Subset_I SUCC_def)

lemma SUCC_Subset_E [intro!]:
  "insert (x SUBS z) (insert (x IN z) H) \<turnstile> C \<Longrightarrow> insert (SUCC x SUBS z) H \<turnstile> C"
  by (metis Eats_Subset_E SUCC_def)

lemma Subset_trans0: "{ a SUBS b, b SUBS c } \<turnstile> a SUBS c"
proof -
  obtain i::name where [simp]: "atom i \<sharp> (a,b,c)"
    by (rule obtain_fresh)
  show ?thesis
    by (rule Subset_I [of i]) (auto intro: Subset_D)
qed

lemma Subset_trans: "H \<turnstile> a SUBS b \<Longrightarrow> H \<turnstile> b SUBS c \<Longrightarrow> H \<turnstile> a SUBS c"
  by (metis Subset_trans0 cut2)

lemma Subset_SUCC: "H \<turnstile> a SUBS (SUCC a)"
  by (metis SUCC_def Subset_Eats_I)

lemma All2_Subset_lemma: "atom l \<sharp> (k',k) \<Longrightarrow> {P} \<turnstile> P' \<Longrightarrow> {All2 l k P, k' SUBS k} \<turnstile> All2 l k' P'"
  apply auto
  apply (rule Ex_I [where x = "Var l"])
  apply (auto intro: ContraProve Set_MP cut1)
  done

lemma All2_Subset: "\<lbrakk>H \<turnstile> All2 l k P; H \<turnstile> k' SUBS k; {P} \<turnstile> P'; atom l \<sharp> (k', k)\<rbrakk> \<Longrightarrow> H \<turnstile> All2 l k' P'"
  by (rule cut2 [OF All2_Subset_lemma]) auto


section\<open>Extensionality\<close>

lemma Extensionality: "H \<turnstile> x EQ y IFF x SUBS y AND y SUBS x"
proof -
  obtain i::name and j::name and k::name
    where atoms: "atom i \<sharp> (x,y)"  "atom j \<sharp> (i,x,y)"  "atom k \<sharp> (i,j,y)"
    by (metis obtain_fresh) 
  have "{} \<turnstile> (Var i EQ y IFF Var i SUBS y AND y SUBS Var i)" (is "{} \<turnstile> ?scheme")
  proof (rule Ind [of j])
    show "atom j \<sharp> (i, ?scheme)" using atoms
      by simp 
  next
    show "{} \<turnstile> ?scheme(i::=Zero)" using atoms
    proof auto
      show "{Zero EQ y} \<turnstile> y SUBS Zero"
        by (rule Subset_cong [OF Assume Refl, THEN Iff_MP_same]) (rule Subset_refl)
    next
      show "{Zero SUBS y, y SUBS Zero} \<turnstile> Zero EQ y"
        by (metis AssumeH(2) Subset_Zero_D Sym)
    qed
  next
    show "{} \<turnstile> All i (All j (?scheme IMP ?scheme(i::=Var j) IMP ?scheme(i::=Eats (Var i) (Var j))))"
      using atoms
      apply auto
      apply (metis Subset_cong [OF Refl Assume, THEN Iff_MP_same] Subset_Eats_I)
      apply (metis Mem_cong [OF Refl Assume, THEN Iff_MP_same] Mem_Eats_I2 Refl)
      apply (metis Subset_cong [OF Assume Refl, THEN Iff_MP_same] Subset_refl)
      apply (rule Eq_Eats_I [of _ k, THEN Sym])
      apply (auto intro: Set_MP [where x=y] Subset_D [where t = "Var i"] Disj_I1 Disj_I2)
      apply (rule Var_Eq_subst_Iff [THEN Iff_MP_same], auto)
      done
  qed
  hence "{} \<turnstile> (Var i EQ y IFF Var i SUBS y AND y SUBS Var i)(i::=x)" 
    by (metis Subst emptyE)
  thus ?thesis using atoms
    by (simp add: thin0)
qed

lemma Equality_I: "H \<turnstile> y SUBS x \<Longrightarrow> H \<turnstile> x SUBS y \<Longrightarrow> H \<turnstile> x EQ y"
  by (metis Conj_I Extensionality Iff_MP2_same)

lemma EQ_imp_SUBS: "insert (t EQ u) H \<turnstile> (t SUBS u)"
proof -
  have "{t EQ u} \<turnstile> (t SUBS u)"
    by (metis Assume Conj_E Extensionality Iff_MP_left')
thus ?thesis
  by (metis Assume cut1)
qed

lemma EQ_imp_SUBS2: "insert (u EQ t) H \<turnstile> (t SUBS u)"
  by (metis EQ_imp_SUBS Sym_L)

lemma Equality_E: "insert (t SUBS u) (insert (u SUBS t) H) \<turnstile> A \<Longrightarrow> insert (t EQ u) H \<turnstile> A"
  by (metis Conj_E Extensionality Iff_MP_left')


section \<open>The Disjointness Relation\<close>

text\<open>The following predicate is defined in order to prove Lemma 2.3, Foundation\<close>

nominal_function Disjoint :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "atom z \<sharp> (t, u) \<Longrightarrow> Disjoint t u = All2 z t (Neg ((Var z) IN u))"
  by (auto simp: eqvt_def Disjoint_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

declare Disjoint.simps [simp del]

lemma Disjoint_fresh_iff [simp]: "a \<sharp> Disjoint t u \<longleftrightarrow> a \<sharp> t \<and> a \<sharp> u"
proof -
  obtain j::name where j: "atom j \<sharp> (a,t,u)"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp: Disjoint.simps [of j])
qed

lemma subst_fm_Disjoint [simp]:
  "(Disjoint t u)(i::=x) = Disjoint (subst i x t) (subst i x u)"
proof -
  obtain j::name where j: "atom j \<sharp> (i,x,t,u)"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp: Disjoint.simps [of j])
qed

lemma Disjoint_cong: "H \<turnstile> t EQ t' \<Longrightarrow> H \<turnstile> u EQ u' \<Longrightarrow> H \<turnstile> Disjoint t u IFF Disjoint t' u'"
  by (rule P2_cong) auto

lemma Disjoint_I:
  assumes "insert ((Var i) IN t) (insert ((Var i) IN u) H) \<turnstile> Fls"
          "atom i \<sharp> (t,u)" "\<forall>B \<in> H. atom i \<sharp> B"
  shows "H \<turnstile> Disjoint t u"
by (subst Disjoint.simps [of i]) (auto simp: assms insert_commute)

lemma Disjoint_E:
  assumes major: "H \<turnstile> Disjoint t u" and minor: "H \<turnstile> a IN t" "H \<turnstile> a IN u" shows "H \<turnstile> A"
proof -
  obtain i::name where i: "atom i \<sharp> (t, u)"
    by (rule obtain_fresh)
  hence "H \<turnstile> (Var i IN t IMP Neg (Var i IN u)) (i::=a)"
    by (metis Disjoint.simps major All_D)
  thus ?thesis using i
    by simp (metis MP_same Neg_D minor)
qed

lemma Disjoint_commute: "{ Disjoint t u } \<turnstile> Disjoint u t"
proof -
  obtain i::name where "atom i \<sharp> (t,u)"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp: fresh_Pair intro: Disjoint_I Disjoint_E) 
qed

lemma Disjoint_commute_I: "H \<turnstile> Disjoint t u \<Longrightarrow> H \<turnstile> Disjoint u t"
  by (metis Disjoint_commute cut1)

lemma Disjoint_commute_D: "insert (Disjoint t u) H \<turnstile> A \<Longrightarrow> insert (Disjoint u t) H \<turnstile> A" 
  by (metis Assume Disjoint_commute_I cut_same insert_commute thin1)

lemma Zero_Disjoint_I1 [iff]: "H \<turnstile> Disjoint Zero t"
proof -
  obtain i::name where i: "atom i \<sharp> t"
    by (rule obtain_fresh)
  hence "{} \<turnstile> Disjoint Zero t"
    by (auto intro: Disjoint_I [of i]) 
  thus ?thesis
    by (metis thin0)
qed

lemma Zero_Disjoint_I2 [iff]: "H \<turnstile> Disjoint t Zero"
  by (metis Disjoint_commute Zero_Disjoint_I1 cut1)

lemma Disjoint_Eats_D1: "{ Disjoint (Eats x y) z } \<turnstile> Disjoint x z"
proof -
  obtain i::name where i: "atom i \<sharp> (x,y,z)"
    by (rule obtain_fresh)
  show ?thesis
    apply (rule Disjoint_I [of i])  
    apply (blast intro: Disjoint_E Mem_Eats_I1)
    using i apply auto
    done
qed

lemma Disjoint_Eats_D2: "{ Disjoint (Eats x y) z } \<turnstile> Neg(y IN z)"
proof -
  obtain i::name where i: "atom i \<sharp> (x,y,z)"
    by (rule obtain_fresh)
  show ?thesis
    by (force intro: Disjoint_E [THEN rotate2] Mem_Eats_I2)
qed

lemma Disjoint_Eats_E: 
  "insert (Disjoint x z) (insert (Neg(y IN z)) H) \<turnstile> A \<Longrightarrow> insert (Disjoint (Eats x y) z) H \<turnstile> A"
  apply (rule cut_same [OF cut1 [OF Disjoint_Eats_D2, OF Assume]])
  apply (rule cut_same [OF cut1 [OF Disjoint_Eats_D1, OF Hyp]])
  apply (auto intro: thin)
  done  

lemma Disjoint_Eats_E2: 
  "insert (Disjoint z x) (insert (Neg(y IN z)) H) \<turnstile> A \<Longrightarrow> insert (Disjoint z (Eats x y)) H \<turnstile> A"
  by (metis Disjoint_Eats_E Disjoint_commute_D)
    
lemma Disjoint_Eats_Imp: "{ Disjoint x z, Neg(y IN z) } \<turnstile> Disjoint (Eats x y) z"
proof -
  obtain i::name where"atom i \<sharp> (x,y,z)"
    by (rule obtain_fresh)
  then show ?thesis 
    by (auto intro: Disjoint_I [of i]  Disjoint_E [THEN rotate3] 
                    Mem_cong [OF Assume Refl, THEN Iff_MP_same])
qed

lemma Disjoint_Eats_I [intro!]: "H \<turnstile> Disjoint x z \<Longrightarrow> insert (y IN z) H \<turnstile> Fls \<Longrightarrow> H \<turnstile> Disjoint (Eats x y) z"
  by (metis Neg_I cut2 [OF Disjoint_Eats_Imp])

lemma Disjoint_Eats_I2 [intro!]: "H \<turnstile> Disjoint z x \<Longrightarrow> insert (y IN z) H \<turnstile> Fls \<Longrightarrow> H \<turnstile> Disjoint z (Eats x y)"
  by (metis Disjoint_Eats_I Disjoint_commute cut1)


section \<open>The Foundation Theorem\<close>

lemma Foundation_lemma: 
  assumes i: "atom i \<sharp> z"
  shows "{ All2 i z (Neg (Disjoint (Var i) z)) } \<turnstile> Neg (Var i IN z) AND Disjoint (Var i) z"
proof -
  obtain j::name  where j: "atom j \<sharp> (z,i)"
    by (metis obtain_fresh) 
  show ?thesis
    apply (rule Ind [of j]) using i j
    apply auto
    apply (rule Ex_I [where x=Zero], auto)
    apply (rule Ex_I [where x="Eats (Var i) (Var j)"], auto)
    apply (metis ContraAssume insertI1 insert_commute)
    apply (metis ContraProve Disjoint_Eats_Imp rotate2 thin1)
    apply (metis Assume Disj_I1 anti_deduction rotate3)
    done
qed    

theorem Foundation: "atom i \<sharp> z \<Longrightarrow> {} \<turnstile> All2 i z (Neg (Disjoint (Var i) z)) IMP z EQ Zero"
  apply auto 
  apply (rule Eq_Zero_I)
  apply (rule cut_same [where A = "(Neg ((Var i) IN z) AND Disjoint (Var i) z)"])
  apply (rule Foundation_lemma [THEN cut1], auto)
  done

lemma Mem_Neg_refl: "{} \<turnstile> Neg (x IN x)"
proof -
  obtain i::name where i: "atom i \<sharp> x"
    by (metis obtain_fresh)
  have "{} \<turnstile> Disjoint x (Eats Zero x)" 
    apply (rule cut_same [OF Foundation [where z = "Eats Zero x"]]) using i
    apply auto
    apply (rule cut_same [where A = "Disjoint x (Eats Zero x)"])    
    apply (metis Assume thin1 Disjoint_cong [OF Assume Refl, THEN Iff_MP_same])
    apply (metis Assume AssumeH(4) Disjoint_E Mem_Eats_I2 Refl) 
    done
  thus ?thesis 
    by (metis Disjoint_Eats_D2 Disjoint_commute cut_same)
qed

lemma Mem_refl_E [intro!]: "insert (x IN x) H \<turnstile> A"
  by (metis Disj_I1 Mem_Neg_refl anti_deduction thin0)

lemma Mem_non_refl: assumes "H \<turnstile> x IN x" shows "H \<turnstile> A"
  by (metis Mem_refl_E assms cut_same)

lemma Mem_Neg_sym: "{ x IN y, y IN x } \<turnstile> Fls"
proof -
  obtain i::name where i: "atom i \<sharp> (x,y)"
    by (metis obtain_fresh)
  have "{} \<turnstile> Disjoint x (Eats Zero y) OR Disjoint y (Eats Zero x)" 
    apply (rule cut_same [OF Foundation [where i=i and z = "Eats (Eats Zero y) x"]]) using i
    apply (auto intro!: Disjoint_Eats_E2 [THEN rotate2])
    apply (rule Disj_I2, auto)
    apply (metis Assume EQ_imp_SUBS2 Subset_D insert_commute)
    apply (blast intro!: Disj_I1 Disjoint_cong [OF Hyp Refl, THEN Iff_MP_same])
    done
  thus ?thesis
    by (auto intro: cut0 Disjoint_Eats_E2)
qed

lemma Mem_not_sym: "insert (x IN y) (insert (y IN x) H) \<turnstile> A"
  by (rule cut_thin [OF Mem_Neg_sym]) auto

  
section \<open>The Ordinal Property\<close>

nominal_function OrdP :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom y \<sharp> (x, z); atom z \<sharp> x\<rbrakk> \<Longrightarrow>
    OrdP x = All2 y x ((Var y) SUBS x AND  All2 z (Var y) ((Var z) SUBS (Var y)))"
  by (auto simp: eqvt_def OrdP_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows OrdP_fresh_iff [simp]: "a \<sharp> OrdP x \<longleftrightarrow> a \<sharp> x"       (is ?thesis1)
   and eval_fm_OrdP [simp]:  "eval_fm e (OrdP x) \<longleftrightarrow> Ord \<lbrakk>x\<rbrakk>e"  (is ?thesis2)
proof -
  obtain z::name and y::name where "atom z \<sharp> x" "atom y \<sharp> (x, z)"
    by (metis obtain_fresh)
  thus ?thesis1 ?thesis2
    by (auto simp: OrdP.simps [of y _ z] Ord_def Transset_def)
qed

lemma subst_fm_OrdP [simp]: "(OrdP t)(i::=x) = OrdP (subst i x t)"
proof -
  obtain z::name and y::name where "atom z \<sharp> (t,i,x)" "atom y \<sharp> (t,i,x,z)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: OrdP.simps [of y _ z])
qed

lemma OrdP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> OrdP x IFF OrdP x'"
  by (rule P1_cong) auto

lemma OrdP_Mem_lemma:
  assumes z: "atom z \<sharp> (k,l)" and l: "insert (OrdP k) H \<turnstile> l IN k"
  shows "insert (OrdP k) H \<turnstile> l SUBS k AND All2 z l (Var z SUBS l)"
proof -
  obtain y::name where y: "atom y \<sharp> (k,l,z)"
    by (metis obtain_fresh)
  have "insert (OrdP k) H 
        \<turnstile> (Var y IN k IMP (Var y SUBS k AND All2 z (Var y) (Var z SUBS Var y)))(y::=l)"
    by (rule All_D) (simp add: OrdP.simps [of y _ z] y z Assume) 
  also have "... = l IN k IMP (l SUBS k AND All2 z l (Var z SUBS l))" 
    using y z  by simp
  finally show ?thesis
    by (metis MP_same l) 
qed

lemma OrdP_Mem_E:
  assumes "atom z \<sharp> (k,l)" 
          "insert (OrdP k) H \<turnstile> l IN k"
          "insert (l SUBS k) (insert (All2 z l (Var z SUBS l)) H) \<turnstile> A"
  shows "insert (OrdP k) H \<turnstile> A" 
  apply (rule OrdP_Mem_lemma [THEN cut_same])
  apply (auto simp: insert_commute)
  apply (blast intro: assms thin1)+
  done

lemma OrdP_Mem_imp_Subset:
  assumes k: "H \<turnstile> k IN l" and l: "H \<turnstile> OrdP l" shows "H \<turnstile> k SUBS l"
  apply (rule obtain_fresh [of "(l,k)"])
  apply (rule cut_same [OF l])
  using k  apply (auto intro: OrdP_Mem_E thin1)
  done

lemma SUCC_Subset_Ord_lemma: "{ k' IN k, OrdP k } \<turnstile> SUCC k' SUBS k"
  by auto (metis Assume thin1 OrdP_Mem_imp_Subset)

lemma SUCC_Subset_Ord: "H \<turnstile> k' IN k \<Longrightarrow> H \<turnstile> OrdP k \<Longrightarrow> H \<turnstile> SUCC k' SUBS k"
  by (blast intro!: cut2 [OF SUCC_Subset_Ord_lemma])

lemma OrdP_Trans_lemma: "{ OrdP k, i IN j, j IN k } \<turnstile> i IN k"
proof -
  obtain m::name where "atom m \<sharp> (i,j,k)"
    by (metis obtain_fresh) 
  thus ?thesis
    by (auto intro: OrdP_Mem_E [of m k j] Subset_D [THEN rotate3])
qed

lemma OrdP_Trans: "H \<turnstile>  OrdP k \<Longrightarrow> H \<turnstile> i IN j \<Longrightarrow> H \<turnstile> j IN k \<Longrightarrow> H  \<turnstile> i IN k"
  by (blast intro: cut3 [OF OrdP_Trans_lemma])

lemma Ord_IN_Ord0:
  assumes l: "H \<turnstile> l IN k"
  shows "insert (OrdP k) H \<turnstile> OrdP l"
proof -
  obtain z::name and y::name where z: "atom z \<sharp> (k,l)" and y: "atom y \<sharp> (k,l,z)"
    by (metis obtain_fresh)
  have "{Var y IN l, OrdP k, l IN k} \<turnstile> All2 z (Var y) (Var z SUBS Var y)"  using y z
    apply (simp add: insert_commute [of _ "OrdP k"]) 
    apply (auto intro: OrdP_Mem_E [of z k "Var y"] OrdP_Trans_lemma del: All_I Neg_I)
    done
  hence "{OrdP k, l IN k} \<turnstile> OrdP l" using z y
    apply (auto simp: OrdP.simps [of y l z])
    apply (simp add: insert_commute [of _ "OrdP k"]) 
    apply (rule OrdP_Mem_E [of y k l], simp_all)
    apply (metis Assume thin1)
    apply (rule All_E [where x= "Var y", THEN thin1], simp) 
    apply (metis Assume anti_deduction insert_commute) 
    done
  thus ?thesis
    by (metis (full_types) Assume l cut2 thin1) 
qed

lemma Ord_IN_Ord: "H \<turnstile> l IN k \<Longrightarrow> H \<turnstile> OrdP k \<Longrightarrow> H \<turnstile> OrdP l"
  by (metis Ord_IN_Ord0 cut_same)

lemma OrdP_I:
  assumes "insert (Var y IN x) H \<turnstile> (Var y) SUBS x"
      and "insert (Var z IN Var y) (insert (Var y IN x) H) \<turnstile> (Var z) SUBS (Var y)"
      and "atom y \<sharp> (x, z)" "\<forall>B \<in> H. atom y \<sharp> B"  "atom z \<sharp> x" "\<forall>B \<in> H. atom z \<sharp> B"
    shows "H \<turnstile> OrdP x"
  using assms by auto

lemma OrdP_Zero [simp]: "H \<turnstile> OrdP Zero"
proof -
  obtain y::name and z::name where "atom y \<sharp> z"
    by (rule obtain_fresh)
  hence "{} \<turnstile> OrdP Zero"
    by (auto intro: OrdP_I [of y _ _ z])
  thus ?thesis 
    by (metis thin0)
qed

lemma OrdP_SUCC_I0: "{ OrdP k } \<turnstile> OrdP (SUCC k)"
proof -
  obtain w::name and y::name and z::name where atoms: "atom w \<sharp> (k,y,z)" "atom y \<sharp> (k,z)" "atom z \<sharp> k"
    by (metis obtain_fresh)
  have 1: "{Var y IN SUCC k, OrdP k} \<turnstile> Var y SUBS SUCC k"
    apply (rule Mem_SUCC_E)
    apply (rule OrdP_Mem_E [of w _ "Var y", THEN rotate2]) using atoms
    apply auto
    apply (metis Assume Subset_SUCC Subset_trans)   
    apply (metis EQ_imp_SUBS Subset_SUCC Subset_trans)
    done
  have in_case: "{Var y IN k, Var z IN Var y, OrdP k} \<turnstile> Var z SUBS Var y"
    apply (rule OrdP_Mem_E [of w _ "Var y", THEN rotate3]) using atoms
    apply (auto intro:  All2_E [THEN thin1])
    done
  have "{Var y EQ k, Var z IN k, OrdP k} \<turnstile> Var z SUBS Var y"
    by (metis AssumeH(2) AssumeH(3) EQ_imp_SUBS2 OrdP_Mem_imp_Subset Subset_trans)
  hence eq_case: "{Var y EQ k, Var z IN Var y, OrdP k} \<turnstile> Var z SUBS Var y"
    by (rule cut3) (auto intro: EQ_imp_SUBS [THEN cut1] Subset_D)
  have 2: "{Var z IN Var y, Var y IN SUCC k, OrdP k} \<turnstile> Var z SUBS Var y"
    by (metis rotate2 Mem_SUCC_E in_case eq_case)   
  show ?thesis
    apply (rule OrdP_I [OF 1 2]) 
    using atoms apply auto 
    done
qed

lemma OrdP_SUCC_I: "H \<turnstile> OrdP k \<Longrightarrow> H \<turnstile> OrdP (SUCC k)"
  by (metis OrdP_SUCC_I0 cut1)

lemma Zero_In_OrdP: "{ OrdP x } \<turnstile> x EQ Zero OR Zero IN x"
proof -
  obtain i::name and j::name
    where i: "atom i \<sharp> x" and j: "atom j \<sharp> (x,i)"
    by (metis obtain_fresh)
  show ?thesis
    apply (rule cut_thin [where HB = "{OrdP x}", OF Foundation [where i=i and z = x]])
    using i j apply auto
    prefer 2 apply (metis Assume Disj_I1)
    apply (rule Disj_I2)
    apply (rule cut_same [where A = "Var i EQ Zero"])
    prefer 2 apply (blast intro: Iff_MP_same [OF Mem_cong [OF Assume Refl]])
    apply (auto intro!: Eq_Zero_I [where i=j] Ex_I [where x="Var i"])
    apply (blast intro: Disjoint_E Subset_D)
    done
qed

lemma OrdP_HPairE: "insert (OrdP (HPair x y)) H \<turnstile> A"
proof -
  have "{ OrdP (HPair x y) } \<turnstile> A"
    by (rule cut_same [OF Zero_In_OrdP]) (auto simp: HPair_def)
  thus ?thesis
    by (metis Assume cut1)
qed

lemmas OrdP_HPairEH = OrdP_HPairE OrdP_HPairE [THEN rotate2] OrdP_HPairE [THEN rotate3] OrdP_HPairE [THEN rotate4] OrdP_HPairE [THEN rotate5] 
                 OrdP_HPairE [THEN rotate6] OrdP_HPairE [THEN rotate7] OrdP_HPairE [THEN rotate8] OrdP_HPairE [THEN rotate9] OrdP_HPairE [THEN rotate10]
declare OrdP_HPairEH [intro!]

lemma Zero_Eq_HPairE: "insert (Zero EQ HPair x y) H \<turnstile> A"
  by (metis Eats_EQ_Zero_E2 HPair_def)

lemmas Zero_Eq_HPairEH = Zero_Eq_HPairE Zero_Eq_HPairE [THEN rotate2] Zero_Eq_HPairE [THEN rotate3] Zero_Eq_HPairE [THEN rotate4] Zero_Eq_HPairE [THEN rotate5] 
                 Zero_Eq_HPairE [THEN rotate6] Zero_Eq_HPairE [THEN rotate7] Zero_Eq_HPairE [THEN rotate8] Zero_Eq_HPairE [THEN rotate9] Zero_Eq_HPairE [THEN rotate10]
declare Zero_Eq_HPairEH [intro!]

lemma HPair_Eq_ZeroE: "insert (HPair x y EQ Zero) H \<turnstile> A"
  by (metis Sym_L Zero_Eq_HPairE)

lemmas HPair_Eq_ZeroEH = HPair_Eq_ZeroE HPair_Eq_ZeroE [THEN rotate2] HPair_Eq_ZeroE [THEN rotate3] HPair_Eq_ZeroE [THEN rotate4] HPair_Eq_ZeroE [THEN rotate5] 
                 HPair_Eq_ZeroE [THEN rotate6] HPair_Eq_ZeroE [THEN rotate7] HPair_Eq_ZeroE [THEN rotate8] HPair_Eq_ZeroE [THEN rotate9] HPair_Eq_ZeroE [THEN rotate10]
declare HPair_Eq_ZeroEH [intro!]

section \<open>Induction on Ordinals\<close>

lemma OrdInd_lemma:
  assumes j: "atom (j::name) \<sharp> (i,A)"
  shows "{ OrdP (Var i) } \<turnstile> (All i (OrdP (Var i) IMP ((All2 j (Var i) (A(i::= Var j))) IMP A))) IMP A"
proof -
  obtain l::name and k::name
      where l: "atom l \<sharp> (i,j,A)" and k: "atom k \<sharp> (i,j,l,A)" 
      by (metis obtain_fresh)  
  have "{ (All i (OrdP (Var i) IMP ((All2 j (Var i) (A(i::= Var j))) IMP A))) } 
        \<turnstile> (All2 l (Var i) (OrdP (Var l) IMP A(i::= Var l)))"
    apply (rule Ind [of k]) 
    using j k l apply auto
    apply (rule All_E [where x="Var l", THEN rotate5], auto)
    apply (metis Assume Disj_I1 anti_deduction thin1)
    apply (rule Ex_I [where x="Var l"], auto)
    apply (rule All_E [where x="Var j", THEN rotate6], auto)
    apply (blast intro: ContraProve Iff_MP_same [OF Mem_cong [OF Refl]])
    apply (metis Assume Ord_IN_Ord0 ContraProve insert_commute)
    apply (metis Assume Neg_D thin1)+
    done
  hence "{ (All i (OrdP (Var i) IMP ((All2 j (Var i) (A(i::= Var j))) IMP A))) } 
          \<turnstile> (All2 l (Var i) (OrdP (Var l) IMP A(i::= Var l)))(i::= Eats Zero (Var i))"
    by (rule Subst, auto) 
  hence indlem: "{ All i (OrdP (Var i) IMP ((All2 j (Var i) (A(i::= Var j))) IMP A)) } 
             \<turnstile> All2 l (Eats Zero (Var i)) (OrdP (Var l) IMP A(i::=Var l))" 
    using j l by simp 
  show ?thesis
    apply (rule Imp_I)
    apply (rule cut_thin [OF indlem, where HB = "{OrdP (Var i)}"])
    apply (rule All2_Eats_E) using j l
    apply auto 
    done
qed

lemma OrdInd:
  assumes j: "atom (j::name) \<sharp> (i,A)"
  and x: "H \<turnstile> OrdP (Var i)" and step: "H \<turnstile> All i (OrdP (Var i) IMP (All2 j (Var i) (A(i::= Var j)) IMP A))"
  shows "H \<turnstile> A"
  apply (rule cut_thin [OF x, where HB=H])
  apply (rule MP_thin [OF OrdInd_lemma step])
  apply (auto simp: j)
  done

lemma OrdIndH:
  assumes "atom (j::name) \<sharp> (i,A)"
      and "H \<turnstile> All i (OrdP (Var i) IMP (All2 j (Var i) (A(i::= Var j)) IMP A))"
    shows "insert (OrdP (Var i)) H \<turnstile> A"
  by (metis assms thin1 Assume OrdInd)

  
section \<open>Linearity of Ordinals\<close>

lemma OrdP_linear_lemma:
  assumes j: "atom j \<sharp> i"
  shows "{ OrdP (Var i) } \<turnstile> All j (OrdP (Var j) IMP (Var i IN Var j OR Var i EQ Var j OR Var j IN Var i))"
         (is "_ \<turnstile> ?scheme")
proof -
  obtain k::name and l::name and m::name
    where k: "atom k \<sharp> (i,j)" and l: "atom l \<sharp> (i,j,k)" and m: "atom m \<sharp> (i,j)"
    by (metis obtain_fresh) 
  show ?thesis
  proof (rule OrdIndH [where i=i and j=k])
    show "atom k \<sharp> (i, ?scheme)"
      using k  by (force simp add: fresh_Pair)  
  next
    show "{} \<turnstile> All i (OrdP (Var i) IMP (All2 k (Var i) (?scheme(i::= Var k)) IMP ?scheme))"
      using j k
      apply simp
      apply (rule All_I Imp_I)+
      defer 1
      apply auto [2]
      apply (rule OrdIndH [where i=j and j=l]) using l
      \<comment> \<open>nested induction\<close>
      apply (force simp add: fresh_Pair)
      apply simp
      apply (rule All_I Imp_I)+
      prefer 2  apply force
      apply (rule Disj_3I)
      apply (rule Equality_I)
      \<comment> \<open>Now the opposite inclusion, @{term"Var j SUBS Var i"}\<close>
      apply (rule Subset_I [where i=m])
      apply (rule All2_E [THEN rotate4]) using l m
      apply auto
      apply (blast intro: ContraProve [THEN rotate3] OrdP_Trans)
      apply (blast intro: ContraProve [THEN rotate3] Mem_cong [OF Hyp Refl, THEN Iff_MP2_same])
      \<comment> \<open>Now the opposite inclusion, @{term"Var i SUBS Var j"}\<close>
      apply (rule Subset_I [where i=m])
      apply (rule All2_E [THEN rotate6], auto) 
      apply (rule All_E [where x = "Var j"], auto) 
      apply (blast intro: ContraProve [THEN rotate4] Mem_cong [OF Hyp Refl, THEN Iff_MP_same])
      apply (blast intro: ContraProve [THEN rotate4] OrdP_Trans)
      done
  qed
qed

lemma OrdP_linear_imp: "{} \<turnstile> OrdP x IMP OrdP y IMP x IN y OR x EQ y OR y IN x"
proof -
  obtain i::name and j::name
    where atoms: "atom i \<sharp> (x,y)" "atom j \<sharp> (x,y,i)" 
    by (metis obtain_fresh) 
  have "{ OrdP (Var i) } \<turnstile> (OrdP (Var j) IMP (Var i IN Var j OR Var i EQ Var j OR Var j IN Var i))(j::=y)"
    using atoms  by (metis All_D OrdP_linear_lemma fresh_Pair)
  hence "{} \<turnstile> OrdP (Var i) IMP OrdP y IMP (Var i IN y OR Var i EQ y OR y IN Var i)"
    using atoms by auto
  hence "{} \<turnstile> (OrdP (Var i) IMP OrdP y IMP (Var i IN y OR Var i EQ y OR y IN Var i))(i::=x)"
    by (metis Subst empty_iff)
  thus ?thesis
    using atoms by auto
qed
  
lemma OrdP_linear:
  assumes "H \<turnstile> OrdP x" "H \<turnstile> OrdP y" 
          "insert (x IN y) H \<turnstile> A" "insert (x EQ y) H \<turnstile> A" "insert (y IN x) H \<turnstile> A" 
    shows "H \<turnstile> A"
proof -
  have "{ OrdP x, OrdP y } \<turnstile> x IN y OR x EQ y OR y IN x"
    by (metis OrdP_linear_imp Imp_Imp_commute anti_deduction)
  thus ?thesis    
    using assms  by (metis cut2 Disj_E cut_same)
qed

lemma Zero_In_SUCC: "{OrdP k} \<turnstile> Zero IN SUCC k"
  by (rule OrdP_linear [OF OrdP_Zero OrdP_SUCC_I]) (force simp: SUCC_def)+


section \<open>The predicate \<open>OrdNotEqP\<close>\<close>

nominal_function OrdNotEqP :: "tm \<Rightarrow> tm \<Rightarrow> fm"  (infixr "NEQ" 150)
  where "OrdNotEqP x y = OrdP x AND OrdP y AND (x IN y OR y IN x)"
  by (auto simp: eqvt_def OrdNotEqP_graph_aux_def)

nominal_termination (eqvt)
  by lexicographic_order

lemma OrdNotEqP_fresh_iff [simp]: "a \<sharp> OrdNotEqP x y \<longleftrightarrow> a \<sharp> x \<and> a \<sharp> y"
  by auto

lemma eval_fm_OrdNotEqP [simp]: "eval_fm e (OrdNotEqP x y) \<longleftrightarrow> Ord \<lbrakk>x\<rbrakk>e \<and> Ord \<lbrakk>y\<rbrakk>e \<and> \<lbrakk>x\<rbrakk>e \<noteq> \<lbrakk>y\<rbrakk>e"
  by (auto simp: hmem_not_refl) (metis Ord_linear)

lemma OrdNotEqP_subst [simp]: "(OrdNotEqP x y)(i::=t) = OrdNotEqP (subst i t x) (subst i t y)"
  by simp

lemma OrdNotEqP_cong: "H \<turnstile> x EQ x' \<Longrightarrow> H \<turnstile> y EQ y' \<Longrightarrow> H \<turnstile> OrdNotEqP x y IFF OrdNotEqP x' y'"
  by (rule P2_cong) auto

lemma OrdNotEqP_self_contra: "{x NEQ x} \<turnstile> Fls"
  by auto

lemma OrdNotEqP_OrdP_E: "insert (OrdP x) (insert (OrdP y) H) \<turnstile> A \<Longrightarrow> insert (x NEQ y) H \<turnstile> A"
  by (auto intro: thin1 rotate2)

lemma OrdNotEqP_I: "insert (x EQ y) H \<turnstile> Fls \<Longrightarrow> H \<turnstile> OrdP x \<Longrightarrow> H \<turnstile> OrdP y \<Longrightarrow> H \<turnstile> x NEQ y"
  by (rule OrdP_linear [of _ x y]) (auto intro: ExFalso thin1 Disj_I1 Disj_I2)

declare OrdNotEqP.simps [simp del]

lemma OrdNotEqP_imp_Neg_Eq: "{x NEQ y} \<turnstile> Neg (x EQ y)"
  by (blast intro: OrdNotEqP_cong [THEN Iff_MP2_same]  OrdNotEqP_self_contra [of x, THEN cut1])

lemma OrdNotEqP_E: "H \<turnstile> x EQ y \<Longrightarrow> insert (x NEQ y) H \<turnstile> A"
  by (metis ContraProve OrdNotEqP_imp_Neg_Eq rcut1)

  
section \<open>Predecessor of an Ordinal\<close>

lemma OrdP_set_max_lemma:
  assumes j: "atom (j::name) \<sharp> i" and k: "atom (k::name) \<sharp> (i,j)"
  shows "{} \<turnstile> (Neg (Var i EQ Zero) AND (All2 j (Var i) (OrdP (Var j)))) IMP 
              (Ex j (Var j IN Var i AND (All2 k (Var i) (Var k SUBS Var j))))"
proof -
  obtain l::name where l: "atom l \<sharp> (i,j,k)" 
    by (metis obtain_fresh) 
  show ?thesis
    apply (rule Ind [of l i]) using j k l 
      apply simp_all
     apply (metis Conj_E Refl Swap Imp_I)
    apply (rule All_I Imp_I)+  
      apply simp_all
    apply clarify
    apply (rule thin1)
    apply (rule thin1 [THEN rotate2])
    apply (rule Disj_EH)
     apply (rule Neg_Conj_E)
      apply (auto simp: All2_Eats_E1)   
     apply (rule Ex_I [where x="Var l"], auto intro: Mem_Eats_I2)
      apply (metis Assume Eq_Zero_D rotate3)
     apply (metis Assume EQ_imp_SUBS Neg_D thin1)
    apply (rule Cases [where A = "Var j IN Var l"])
    apply (rule Ex_I [where x="Var l"], auto intro: Mem_Eats_I2)
    apply (rule Ex_I [where x="Var l"], auto intro: Mem_Eats_I2 ContraProve)
    apply (rule Ex_I [where x="Var k"], auto)
    apply (metis Assume Subset_trans OrdP_Mem_imp_Subset thin1)
    apply (rule Ex_I [where x="Var l"], auto intro: Mem_Eats_I2 ContraProve)
    apply (metis ContraProve EQ_imp_SUBS rotate3)
    \<comment> \<open>final case\<close>
    apply (rule All2_Eats_E [THEN rotate4], simp_all)
    apply (rule Ex_I [where x="Var j"], auto intro: Mem_Eats_I1)
    apply (rule All2_E [where x = "Var k", THEN rotate3], auto)
    apply (rule Ex_I [where x="Var k"], simp)
    apply (metis Assume NegNeg_I Neg_Disj_I rotate3)
    apply (rule cut_same [where A = "OrdP (Var j)"])
    apply (rule All2_E [where x = "Var j", THEN rotate3], auto)
    apply (rule cut_same [where A = "Var l EQ Var j OR Var l IN Var j"])
    apply (rule OrdP_linear [of _ "Var l" "Var j"], auto intro: Disj_CI)
    apply (metis Assume ContraProve rotate7)
    apply (metis ContraProve [THEN rotate4] EQ_imp_SUBS Subset_trans rotate3)
    apply (blast intro: ContraProve [THEN rotate4] OrdP_Mem_imp_Subset Iff_MP2_same [OF Mem_cong])
    done
qed

lemma OrdP_max_imp:
  assumes j: "atom j \<sharp> (x)" and k: "atom k \<sharp> (x,j)"
  shows  "{ OrdP x, Neg (x EQ Zero) } \<turnstile> Ex j (Var j IN x AND (All2 k x (Var k SUBS Var j)))"
proof -
  obtain i::name where i: "atom i \<sharp> (x,j,k)" 
    by (metis obtain_fresh) 
  have "{} \<turnstile> ((Neg (Var i EQ Zero) AND (All2 j (Var i) (OrdP (Var j)))) IMP 
              (Ex j (Var j IN Var i AND (All2 k (Var i) (Var k SUBS Var j)))))(i::=x)"
    apply (rule Subst [OF OrdP_set_max_lemma])
    using i k apply auto
    done
  hence "{ Neg (x EQ Zero) AND (All2 j x (OrdP (Var j))) } 
         \<turnstile> Ex j (Var j IN x AND (All2 k x (Var k SUBS Var j)))"
   using i j k by simp (metis anti_deduction)
  hence "{ All2 j x (OrdP (Var j)), Neg (x EQ Zero) } 
             \<turnstile> Ex j (Var j IN x AND (All2 k x (Var k SUBS Var j)))"
    by (rule cut1) (metis Assume Conj_I thin1)
  moreover have "{ OrdP x } \<turnstile> All2 j x (OrdP (Var j))" using j
    by auto (metis Assume Ord_IN_Ord thin1)
  ultimately show ?thesis
   by (metis rcut1)
qed

declare OrdP.simps [simp del]


section \<open>Case Analysis and Zero/SUCC Induction\<close>

lemma OrdP_cases_lemma:
  assumes p: "atom p \<sharp> x" 
  shows  "{ OrdP x, Neg (x EQ Zero) } \<turnstile> Ex p (OrdP (Var p) AND x EQ SUCC (Var p))"
proof -
  obtain j::name and k::name where j: "atom j \<sharp> (x,p)" and k: "atom k \<sharp> (x,j,p)" 
    by (metis obtain_fresh) 
  show ?thesis
    apply (rule cut_same [OF OrdP_max_imp [of j x k]]) 
    using p j k apply auto
    apply (rule Ex_I [where x="Var j"], auto)
     apply (metis Assume Ord_IN_Ord thin1)
    apply (rule cut_same [where A = "OrdP (SUCC (Var j))"])
    apply (metis Assume Ord_IN_Ord0 OrdP_SUCC_I rotate2 thin1)
    apply (rule OrdP_linear [where x = x, OF _ Assume], auto intro!: Mem_SUCC_EH)
    apply (metis Mem_not_sym rotate3) 
    apply (rule Mem_non_refl, blast intro: Mem_cong [OF Assume Refl, THEN Iff_MP2_same])
    apply (force intro: thin1 All2_E [where x = "SUCC (Var j)", THEN rotate4])
    done
qed

lemma OrdP_cases_disj:
  assumes p: "atom p \<sharp> x" 
  shows  "insert (OrdP x) H \<turnstile> x EQ Zero OR Ex p (OrdP (Var p) AND x EQ SUCC (Var p))"
  by (metis Disj_CI Assume cut2 [OF OrdP_cases_lemma [OF p]] Swap thin1)

lemma OrdP_cases_E:
  "\<lbrakk>insert (x EQ Zero) H \<turnstile> A;
    insert (x EQ SUCC (Var k)) (insert (OrdP (Var k)) H) \<turnstile> A; 
    atom k \<sharp> (x,A);   \<forall>C \<in> H. atom k \<sharp> C\<rbrakk>
   \<Longrightarrow> insert (OrdP x) H \<turnstile> A"
  by (rule cut_same [OF OrdP_cases_disj [of k]]) (auto simp: insert_commute intro: thin1)

lemma OrdInd2_lemma:
  "{ OrdP (Var i), A(i::= Zero), (All i (OrdP (Var i) IMP A IMP (A(i::= SUCC (Var i))))) } \<turnstile> A"
proof -
  obtain j::name and k::name  where atoms: "atom j \<sharp> (i,A)" "atom k \<sharp> (i,j,A)" 
    by (metis obtain_fresh) 
  show ?thesis
  apply (rule OrdIndH [where i=i and j=j]) 
  using atoms  apply auto
  apply (rule OrdP_cases_E [where k=k, THEN rotate3])
  apply (rule ContraProve [THEN rotate2]) using Var_Eq_imp_subst_Iff
  apply (metis Assume AssumeH(3) Iff_MP_same) 
  apply (rule Ex_I [where x="Var k"], simp)
  apply (rule Neg_Imp_I, blast)
  apply (rule cut_same [where A = "A(i::=Var k)"])
  apply (rule All2_E [where x = "Var k", THEN rotate5])
  apply (auto intro: Mem_SUCC_I2 Mem_cong [OF Refl, THEN Iff_MP2_same])
  apply (rule ContraProve [THEN rotate5])
  by (metis Assume Iff_MP_left' Var_Eq_subst_Iff thin1)
qed

lemma OrdInd2:
  assumes "H \<turnstile> OrdP (Var i)"
      and "H \<turnstile> A(i::= Zero)"
      and "H \<turnstile> All i (OrdP (Var i) IMP A IMP (A(i::= SUCC (Var i))))"
    shows "H \<turnstile> A"
  by (metis cut3 [OF OrdInd2_lemma] assms)

lemma OrdInd2H:
  assumes "H \<turnstile> A(i::= Zero)"
      and "H \<turnstile> All i (OrdP (Var i) IMP A IMP (A(i::= SUCC (Var i))))"
    shows "insert (OrdP (Var i)) H \<turnstile> A"
  by (metis assms thin1 Assume OrdInd2)


section \<open>The predicate \<open>HFun_Sigma\<close>\<close>

text\<open>To characterise the concept of a function using only bounded universal quantifiers.\<close>

text\<open>See the note after the proof of Lemma 2.3.\<close>

definition hfun_sigma where
 "hfun_sigma r \<equiv> \<forall>z \<^bold>\<in> r. \<forall>z' \<^bold>\<in> r. \<exists>x y x' y'. z = \<langle>x,y\<rangle> \<and> z' = \<langle>x',y'\<rangle> \<and> (x=x' \<longrightarrow> y=y')"

definition hfun_sigma_ord where
 "hfun_sigma_ord r \<equiv> \<forall>z \<^bold>\<in> r. \<forall>z' \<^bold>\<in> r. \<exists>x y x' y'. z = \<langle>x,y\<rangle> \<and> z' = \<langle>x',y'\<rangle> \<and> Ord x \<and> Ord x' \<and> (x=x' \<longrightarrow> y=y')"

nominal_function HFun_Sigma :: "tm \<Rightarrow> fm"
  where "\<lbrakk>atom z \<sharp> (r,z',x,y,x',y'); atom z' \<sharp> (r,x,y,x',y'); 
          atom x \<sharp> (r,y,x',y'); atom y \<sharp> (r,x',y'); atom x' \<sharp> (r,y'); atom y' \<sharp> (r) \<rbrakk> \<Longrightarrow>
    HFun_Sigma r = 
         All2 z r (All2 z' r (Ex x (Ex y (Ex x' (Ex y'
             (Var z EQ HPair (Var x) (Var y) AND Var z' EQ HPair (Var x') (Var y')
              AND OrdP (Var x) AND OrdP (Var x') AND 
              ((Var x EQ Var x') IMP (Var y EQ Var y'))))))))"
by (auto simp: eqvt_def HFun_Sigma_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows HFun_Sigma_fresh_iff [simp]: "a \<sharp> HFun_Sigma r \<longleftrightarrow> a \<sharp> r" (is ?thesis1)
    and eval_fm_HFun_Sigma [simp]:
         "eval_fm e (HFun_Sigma r) \<longleftrightarrow> hfun_sigma_ord \<lbrakk>r\<rbrakk>e" (is ?thesis2)
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name
    where "atom z \<sharp> (r,z',x,y,x',y')"  "atom z' \<sharp> (r,x,y,x',y')"
          "atom x \<sharp> (r,y,x',y')"  "atom y \<sharp> (r,x',y')" 
          "atom x' \<sharp> (r,y')"  "atom y' \<sharp> (r)"
    by (metis obtain_fresh) 
  thus ?thesis1 ?thesis2
    by (auto simp: HBall_def hfun_sigma_ord_def, metis+)
qed

lemma HFun_Sigma_subst [simp]: "(HFun_Sigma r)(i::=t) = HFun_Sigma (subst i t r)"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name
    where "atom z \<sharp> (r,t,i,z',x,y,x',y')" "atom z' \<sharp> (r,t,i,x,y,x',y')"
          "atom x \<sharp> (r,t,i,y,x',y')" "atom y \<sharp> (r,t,i,x',y')" 
          "atom x' \<sharp> (r,t,i,y')" "atom y' \<sharp> (r,t,i)"
    by (metis obtain_fresh) 
  thus ?thesis 
    by (auto simp: HFun_Sigma.simps [of z _ z' x y x' y'])
qed

lemma HFun_Sigma_Zero: "H \<turnstile> HFun_Sigma Zero"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name and z''::name
    where "atom z'' \<sharp> (z,z',x,y,x',y')" "atom z \<sharp> (z',x,y,x',y')" "atom z' \<sharp> (x,y,x',y')"
      "atom x \<sharp> (y,x',y')" "atom y \<sharp> (x',y')" "atom x' \<sharp> y'" 
    by (metis obtain_fresh) 
  hence "{} \<turnstile> HFun_Sigma Zero"
    by (auto simp: HFun_Sigma.simps [of z _ z' x y x' y'])
  thus ?thesis
    by (metis thin0)
qed

lemma Subset_HFun_Sigma: "{HFun_Sigma s, s' SUBS s} \<turnstile> HFun_Sigma s'"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name and z''::name
    where "atom z'' \<sharp> (z,z',x,y,x',y',s,s')" 
      "atom z \<sharp> (z',x,y,x',y',s,s')" "atom z' \<sharp> (x,y,x',y',s,s')"
      "atom x \<sharp> (y,x',y',s,s')" "atom y \<sharp> (x',y',s,s')" 
      "atom x' \<sharp> (y',s,s')" "atom y' \<sharp> (s,s')" 
    by (metis obtain_fresh) 
  thus ?thesis
    apply (auto simp: HFun_Sigma.simps [of z _ z' x y x' y'])
    apply (rule Ex_I [where x="Var z"], auto)
    apply (blast intro: Subset_D ContraProve)
    apply (rule All_E [where x="Var z'"], auto intro: Subset_D ContraProve)
    done
qed

text\<open>Captures the property of being a relation, using fewer variables than the full definition\<close>
lemma HFun_Sigma_Mem_imp_HPair:
  assumes "H \<turnstile> HFun_Sigma r" "H \<turnstile> a IN r"
      and xy: "atom x \<sharp> (y,a,r)" "atom y \<sharp> (a,r)"
    shows "H \<turnstile> (Ex x (Ex y (a EQ HPair (Var x) (Var y))))"  (is "_ \<turnstile> ?concl")
proof -
  obtain x'::name and y'::name and z::name and z'::name
    where atoms: "atom z \<sharp> (z',x',y',x,y,a,r)" "atom z' \<sharp> (x',y',x,y,a,r)"
                 "atom x' \<sharp> (y',x,y,a,r)" "atom y' \<sharp> (x,y,a,r)" 
    by (metis obtain_fresh) 
  hence "{HFun_Sigma r, a IN r} \<turnstile> ?concl" using xy
    apply (auto simp: HFun_Sigma.simps [of z r z' x y x' y'])
    apply (rule All_E [where x=a], auto)
    apply (rule All_E [where x=a], simp)
    apply (rule Imp_E, blast)
    apply (rule Ex_EH Conj_EH)+
    apply simp_all
    apply (rule Ex_I [where x="Var x"], simp)
    apply (rule Ex_I [where x="Var y"], auto)
    done
  thus ?thesis
    by (rule cut2) (rule assms)+ 
qed

    
section \<open>The predicate \<open>HDomain_Incl\<close>\<close>

text \<open>This is an internal version of @{term "\<forall>x \<^bold>\<in> d. \<exists>y z. z \<^bold>\<in> r \<and> z = \<langle>x,y\<rangle>"}.\<close>

nominal_function HDomain_Incl :: "tm \<Rightarrow> tm \<Rightarrow> fm"
  where "\<lbrakk>atom x \<sharp> (r,d,y,z); atom y \<sharp> (r,d,z); atom z \<sharp> (r,d)\<rbrakk> \<Longrightarrow>
    HDomain_Incl r d = All2 x d (Ex y (Ex z (Var z IN r AND Var z EQ HPair (Var x) (Var y))))"
  by (auto simp: eqvt_def HDomain_Incl_graph_aux_def flip_fresh_fresh) (metis obtain_fresh)

nominal_termination (eqvt)
  by lexicographic_order

lemma
  shows HDomain_Incl_fresh_iff [simp]:
      "a \<sharp> HDomain_Incl r d \<longleftrightarrow> a \<sharp> r \<and> a \<sharp> d" (is ?thesis1)
  and   eval_fm_HDomain_Incl [simp]:
      "eval_fm e (HDomain_Incl r d) \<longleftrightarrow> \<lbrakk>d\<rbrakk>e \<le> hdomain \<lbrakk>r\<rbrakk>e" (is ?thesis2)
proof -
  obtain x::name and y::name and z::name 
    where "atom x \<sharp> (r,d,y,z)" "atom y \<sharp> (r,d,z)" "atom z \<sharp> (r,d)"
    by (metis obtain_fresh) 
  thus ?thesis1 ?thesis2
    by (auto simp: HDomain_Incl.simps [of x _ _ y z] hdomain_def)
qed

lemma HDomain_Incl_subst [simp]:
      "(HDomain_Incl r d)(i::=t) = HDomain_Incl (subst i t r) (subst i t d)"
proof -
  obtain x::name and y::name and z::name 
    where "atom x \<sharp> (r,d,y,z,t,i)"  "atom y \<sharp> (r,d,z,t,i)" "atom z \<sharp> (r,d,t,i)"
    by (metis obtain_fresh) 
  thus ?thesis
    by (auto simp: HDomain_Incl.simps [of x _ _ y z])
qed

lemma HDomain_Incl_Subset_lemma: "{ HDomain_Incl r k, k' SUBS k } \<turnstile> HDomain_Incl r k'"
proof -
  obtain x::name and y::name and z::name 
    where "atom x \<sharp> (r,k,k',y,z)" "atom y \<sharp> (r,k,k',z)" "atom z \<sharp> (r,k,k')"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (simp add: HDomain_Incl.simps [of x _ _ y z], auto)
    apply (rule Ex_I [where x = "Var x"], auto intro: ContraProve Subset_D)
    done
qed

lemma HDomain_Incl_Subset: "H \<turnstile> HDomain_Incl r k \<Longrightarrow> H \<turnstile> k' SUBS k \<Longrightarrow> H \<turnstile> HDomain_Incl r k'"
  by (metis HDomain_Incl_Subset_lemma cut2)

lemma HDomain_Incl_Mem_Ord: "H \<turnstile> HDomain_Incl r k \<Longrightarrow> H \<turnstile> k' IN k \<Longrightarrow> H \<turnstile> OrdP k \<Longrightarrow> H \<turnstile> HDomain_Incl r k'"
  by (metis HDomain_Incl_Subset OrdP_Mem_imp_Subset)

lemma HDomain_Incl_Zero [simp]: "H \<turnstile> HDomain_Incl r Zero"
proof -
  obtain x::name and y::name and z::name 
    where "atom x \<sharp> (r,y,z)" "atom y \<sharp> (r,z)" "atom z \<sharp> r"
    by (metis obtain_fresh) 
  hence "{} \<turnstile> HDomain_Incl r Zero"
    by (auto simp: HDomain_Incl.simps [of x _ _ y z])
  thus ?thesis
    by (metis thin0)
qed

lemma HDomain_Incl_Eats: "{ HDomain_Incl r d } \<turnstile> HDomain_Incl (Eats r (HPair d d')) (SUCC d)"
proof -
  obtain x::name and y::name and z::name 
    where x: "atom x \<sharp> (r,d,d',y,z)" and y: "atom y \<sharp> (r,d,d',z)" and z: "atom z \<sharp> (r,d,d')"
    by (metis obtain_fresh) 
  thus ?thesis
    apply (auto simp: HDomain_Incl.simps [of x _ _ y z] intro!: Mem_SUCC_EH)
    apply (rule Ex_I [where x = "Var x"], auto)
    apply (rule Ex_I [where x = "Var y"], auto)
    apply (rule Ex_I [where x = "Var z"], auto intro: Mem_Eats_I1)
    apply (rule rotate2 [OF Swap])
    apply (rule Ex_I [where x = d'], auto)
    apply (rule Ex_I [where x = "HPair d d'"], auto intro: Mem_Eats_I2 HPair_cong Sym)
    done
qed

lemma HDomain_Incl_Eats_I: "H \<turnstile> HDomain_Incl r d \<Longrightarrow> H \<turnstile> HDomain_Incl (Eats r (HPair d d')) (SUCC d)"
  by (metis HDomain_Incl_Eats cut1)


section \<open>@{term HPair} is Provably Injective\<close>

lemma Doubleton_E:
  assumes "insert (a EQ c) (insert (b EQ d) H) \<turnstile> A"
          "insert (a EQ d) (insert (b EQ c) H) \<turnstile> A"
    shows    "insert ((Eats (Eats Zero b) a) EQ (Eats (Eats Zero d) c)) H \<turnstile> A"
apply (rule Equality_E) using assms
apply (auto intro!: Zero_SubsetE rotate2 [of "a IN b"])
apply (rule_tac [!] rotate3) 
apply (auto intro!: Zero_SubsetE rotate2 [of "a IN b"])
apply (metis Sym_L insert_commute thin1)+
done
  
lemma HFST: "{HPair a b EQ HPair c d} \<turnstile> a EQ c"
  unfolding HPair_def  by (metis Assume Doubleton_E thin1)

lemma b_EQ_d_1: "{a EQ c, a EQ d, b EQ c} \<turnstile> b EQ d"
  by (metis Assume thin1 Sym Trans)

lemma HSND: "{HPair a b EQ HPair c d} \<turnstile> b EQ d"
  unfolding HPair_def
  by (metis  AssumeH(2) Doubleton_E b_EQ_d_1 rotate3 thin2) 

lemma HPair_E [intro!]:
  assumes "insert (a EQ c) (insert (b EQ d) H) \<turnstile> A"
    shows "insert (HPair a b EQ HPair c d) H \<turnstile> A"
  by (metis Conj_E [OF assms] Conj_I [OF HFST HSND] rcut1)

declare HPair_E [THEN rotate2, intro!]
declare HPair_E [THEN rotate3, intro!]
declare HPair_E [THEN rotate4, intro!]
declare HPair_E [THEN rotate5, intro!]
declare HPair_E [THEN rotate6, intro!]
declare HPair_E [THEN rotate7, intro!]
declare HPair_E [THEN rotate8, intro!]

lemma HFun_Sigma_E:
  assumes r: "H \<turnstile> HFun_Sigma r"
      and b: "H \<turnstile> HPair a b IN r"
      and b': "H \<turnstile> HPair a b' IN r"
    shows "H \<turnstile> b EQ b'"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name
    where atoms: "atom z \<sharp> (r,a,b,b',z',x,y,x',y')"  "atom z' \<sharp> (r,a,b,b',x,y,x',y')"
       "atom x \<sharp> (r,a,b,b',y,x',y')"  "atom y \<sharp> (r,a,b,b',x',y')" 
       "atom x' \<sharp> (r,a,b,b',y')"  "atom y' \<sharp> (r,a,b,b')"
    by (metis obtain_fresh) 
  hence d1: "H \<turnstile> All2 z r (All2 z' r (Ex x (Ex y (Ex x' (Ex y'
                  (Var z EQ HPair (Var x) (Var y) AND Var z' EQ HPair (Var x') (Var y')
                   AND OrdP (Var x) AND OrdP (Var x') AND ((Var x EQ Var x') IMP (Var y EQ Var y'))))))))" 
      using r HFun_Sigma.simps [of z r z' x y x' y']
    by simp 
  have d2: "H \<turnstile> All2 z' r (Ex x (Ex y (Ex x' (Ex y'
             (HPair a b EQ HPair (Var x) (Var y) AND Var z' EQ HPair (Var x') (Var y')
                   AND OrdP (Var x) AND OrdP (Var x') AND ((Var x EQ Var x') IMP (Var y EQ Var y')))))))" 
    using All_D [where x = "HPair a b", OF d1]  atoms
    by simp (metis MP_same b)              
  have d4: "H \<turnstile> Ex x (Ex y (Ex x' (Ex y'
             (HPair a b EQ HPair (Var x) (Var y) AND HPair a b' EQ HPair (Var x') (Var y')
               AND OrdP (Var x) AND OrdP (Var x') AND ((Var x EQ Var x') IMP (Var y EQ Var y'))))))"
    using All_D [where x = "HPair a b'", OF d2]  atoms
    by simp (metis MP_same b')              
  have d': "{ Ex x (Ex y (Ex x' (Ex y'
             (HPair a b EQ HPair (Var x) (Var y) AND HPair a b' EQ HPair (Var x') (Var y')
              AND OrdP (Var x) AND OrdP (Var x') AND ((Var x EQ Var x') IMP (Var y EQ Var y')))))) } \<turnstile> b EQ b'" 
     using atoms
     by (auto intro: ContraProve Trans Sym)
  thus ?thesis 
    by (rule cut_thin [OF d4], auto)
qed


section \<open>@{term SUCC} is Provably Injective\<close>

lemma SUCC_SUBS_lemma: "{SUCC x SUBS SUCC y} \<turnstile> x SUBS y"
  apply (rule obtain_fresh [where x="(x,y)"]) 
  apply (auto simp: SUCC_def)
  prefer 2  apply (metis Assume Conj_E1 Extensionality Iff_MP_same)
  apply (auto intro!: Subset_I)
  apply (blast intro: Set_MP cut_same [OF Mem_cong [OF Refl Assume, THEN Iff_MP2_same]] 
            Mem_not_sym thin2)
  done

lemma SUCC_SUBS: "insert (SUCC x SUBS SUCC y) H \<turnstile> x SUBS y"
  by (metis Assume SUCC_SUBS_lemma cut1)

lemma SUCC_inject: "insert (SUCC x EQ SUCC y) H \<turnstile> x EQ y"
  by (metis Equality_I EQ_imp_SUBS SUCC_SUBS Sym_L cut1)

lemma SUCC_inject_E [intro!]: "insert (x EQ y) H \<turnstile> A \<Longrightarrow> insert (SUCC x EQ SUCC y) H \<turnstile> A"
  by (metis SUCC_inject cut_same insert_commute thin1)

declare SUCC_inject_E [THEN rotate2, intro!]
declare SUCC_inject_E [THEN rotate3, intro!]
declare SUCC_inject_E [THEN rotate4, intro!]
declare SUCC_inject_E [THEN rotate5, intro!]
declare SUCC_inject_E [THEN rotate6, intro!]
declare SUCC_inject_E [THEN rotate7, intro!]
declare SUCC_inject_E [THEN rotate8, intro!]

lemma OrdP_IN_SUCC_lemma: "{OrdP x, y IN x} \<turnstile> SUCC y IN SUCC x"
  apply (rule OrdP_linear [of _ "SUCC x" "SUCC y"])
  apply (auto intro!: Mem_SUCC_EH  intro: OrdP_SUCC_I Ord_IN_Ord0)
  apply (metis Hyp Mem_SUCC_I1 Mem_not_sym cut_same insertCI)
  apply (metis Assume EQ_imp_SUBS Mem_SUCC_I1 Mem_non_refl Subset_D thin1) 
  apply (blast intro: cut_same [OF Mem_cong [THEN Iff_MP2_same]])
  done

lemma OrdP_IN_SUCC: "H \<turnstile> OrdP x \<Longrightarrow> H \<turnstile> y IN x \<Longrightarrow> H \<turnstile> SUCC y IN SUCC x"
  by (rule cut2 [OF OrdP_IN_SUCC_lemma])

lemma OrdP_IN_SUCC_D_lemma: "{OrdP x, SUCC y IN SUCC x} \<turnstile> y IN x"
  apply (rule OrdP_linear [of _ "x" "y"], auto)
  apply (metis Assume AssumeH(2) Mem_SUCC_Refl OrdP_SUCC_I Ord_IN_Ord)
  apply (rule Mem_SUCC_E [THEN rotate3])
  apply (blast intro: Mem_SUCC_Refl OrdP_Trans) 
  apply (metis AssumeH(2) EQ_imp_SUBS Mem_SUCC_I1 Mem_non_refl Subset_D)
  apply (metis EQ_imp_SUBS Mem_SUCC_I2 Mem_SUCC_EH(2) Mem_SUCC_I1 Refl SUCC_Subset_Ord_lemma Subset_D thin1)  
  done

lemma OrdP_IN_SUCC_D: "H \<turnstile> OrdP x \<Longrightarrow> H \<turnstile> SUCC y IN SUCC x \<Longrightarrow> H \<turnstile> y IN x"
  by (rule cut2 [OF OrdP_IN_SUCC_D_lemma])

lemma OrdP_IN_SUCC_Iff: "H \<turnstile> OrdP y \<Longrightarrow> H \<turnstile> SUCC x IN SUCC y IFF x IN y" 
  by (metis Assume Iff_I OrdP_IN_SUCC OrdP_IN_SUCC_D thin1)


section \<open>The predicate \<open>LstSeqP\<close>\<close>

lemma hfun_sigma_ord_iff: "hfun_sigma_ord s \<longleftrightarrow> OrdDom s \<and> hfun_sigma s"
  by (auto simp: hfun_sigma_ord_def OrdDom_def hfun_sigma_def HBall_def, metis+)

lemma hfun_sigma_iff: "hfun_sigma r \<longleftrightarrow> hfunction r \<and> hrelation r"
  by (auto simp add: HBall_def hfun_sigma_def hfunction_def hrelation_def is_hpair_def, metis+)

lemma Seq_iff: "Seq r d \<longleftrightarrow> d \<le> hdomain r \<and> hfun_sigma r"
  by (auto simp: Seq_def hfun_sigma_iff)

lemma LstSeq_iff: "LstSeq s k y \<longleftrightarrow> succ k \<le> hdomain s \<and> \<langle>k,y\<rangle> \<^bold>\<in> s \<and> hfun_sigma_ord s"
  by (auto simp: OrdDom_def LstSeq_def Seq_iff hfun_sigma_ord_iff)

nominal_function LstSeqP :: "tm \<Rightarrow> tm \<Rightarrow> tm \<Rightarrow> fm"
  where
    "LstSeqP s k y = OrdP k AND HDomain_Incl s (SUCC k) AND HFun_Sigma s AND HPair k y IN s"
  by (auto simp: eqvt_def LstSeqP_graph_aux_def)

nominal_termination (eqvt)
  by lexicographic_order

lemma
 shows LstSeqP_fresh_iff [simp]:
      "a \<sharp> LstSeqP s k y \<longleftrightarrow> a \<sharp> s \<and> a \<sharp> k \<and> a \<sharp> y"         (is ?thesis1)
   and eval_fm_LstSeqP [simp]: 
      "eval_fm e (LstSeqP s k y) \<longleftrightarrow> LstSeq \<lbrakk>s\<rbrakk>e \<lbrakk>k\<rbrakk>e \<lbrakk>y\<rbrakk>e"  (is ?thesis2)
proof -
  show ?thesis1 ?thesis2
    by (auto simp: LstSeq_iff OrdDom_def hfun_sigma_ord_iff)
qed

lemma LstSeqP_subst [simp]:
  "(LstSeqP s k y)(i::=t) = LstSeqP (subst i t s) (subst i t k) (subst i t y)" 
  by (auto simp: fresh_Pair fresh_at_base)

lemma LstSeqP_E: 
  assumes "insert (HDomain_Incl s (SUCC k)) 
            (insert (OrdP k) (insert (HFun_Sigma s)
              (insert (HPair k y IN s) H))) \<turnstile> B" 
    shows "insert (LstSeqP s k y) H \<turnstile> B" 
  using assms by (auto simp: insert_commute)

declare LstSeqP.simps [simp del]

lemma LstSeqP_cong:
  assumes "H \<turnstile> s EQ s'" "H \<turnstile> k EQ k'" "H \<turnstile> y EQ y'" 
  shows "H \<turnstile> LstSeqP s k y IFF LstSeqP s' k' y'"
  by (rule P3_cong [OF _ assms], auto)

lemma LstSeqP_OrdP: "H \<turnstile> LstSeqP r k y \<Longrightarrow> H \<turnstile> OrdP k"
  by (metis Conj_E1 LstSeqP.simps)

lemma LstSeqP_Mem_lemma: "{ LstSeqP r k y, HPair k' z IN r, k' IN k } \<turnstile> LstSeqP r k' z"
  by (auto simp: LstSeqP.simps intro: Ord_IN_Ord OrdP_SUCC_I OrdP_IN_SUCC HDomain_Incl_Mem_Ord)

lemma LstSeqP_Mem: "H \<turnstile> LstSeqP r k y \<Longrightarrow> H \<turnstile> HPair k' z IN r \<Longrightarrow> H \<turnstile> k' IN k \<Longrightarrow> H \<turnstile> LstSeqP r k' z"
  by (rule cut3 [OF LstSeqP_Mem_lemma])

lemma LstSeqP_imp_Mem: "H \<turnstile> LstSeqP s k y \<Longrightarrow> H \<turnstile> HPair k y IN s"
  by (auto simp: LstSeqP.simps) (metis Conj_E2)

lemma LstSeqP_SUCC: "H \<turnstile> LstSeqP r (SUCC d) y \<Longrightarrow> H \<turnstile> HPair d z IN r \<Longrightarrow> H \<turnstile> LstSeqP r d z"
  by (metis LstSeqP_Mem Mem_SUCC_I2 Refl)

lemma LstSeqP_EQ: "\<lbrakk>H \<turnstile> LstSeqP s k y; H \<turnstile> HPair k y' IN s\<rbrakk> \<Longrightarrow> H \<turnstile> y EQ y'" 
  by (metis AssumeH(2) HFun_Sigma_E LstSeqP_E cut1 insert_commute)

end
