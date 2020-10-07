chapter \<open>Sigma-Formulas and Theorem 2.5\<close>

theory Sigma
imports Predicates
begin

section\<open>Ground Terms and Formulas\<close>

definition ground_aux :: "tm \<Rightarrow> atom set \<Rightarrow> bool"
  where "ground_aux t S \<equiv> (supp t \<subseteq> S)"

abbreviation ground :: "tm \<Rightarrow> bool"
  where "ground t \<equiv> ground_aux t {}"

definition ground_fm_aux :: "fm \<Rightarrow> atom set \<Rightarrow> bool"
  where "ground_fm_aux A S \<equiv> (supp A \<subseteq> S)"

abbreviation ground_fm :: "fm \<Rightarrow> bool"
  where "ground_fm A \<equiv> ground_fm_aux A {}"

lemma ground_aux_simps[simp]:
  "ground_aux Zero S = True"
  "ground_aux (Var k) S = (if atom k \<in> S then True else False)"
  "ground_aux (Eats t u) S = (ground_aux t S \<and> ground_aux u S)"
unfolding ground_aux_def
by (simp_all add: supp_at_base)

lemma ground_fm_aux_simps[simp]:
  "ground_fm_aux Fls S = True"
  "ground_fm_aux (t IN u) S = (ground_aux t S \<and> ground_aux u S)"
  "ground_fm_aux (t EQ u) S = (ground_aux t S \<and> ground_aux u S)"
  "ground_fm_aux (A OR B) S = (ground_fm_aux A S \<and> ground_fm_aux B S)"
  "ground_fm_aux (A AND B) S = (ground_fm_aux A S \<and> ground_fm_aux B S)"
  "ground_fm_aux (A IFF B) S = (ground_fm_aux A S \<and> ground_fm_aux B S)"
  "ground_fm_aux (Neg A) S =  (ground_fm_aux A S)"
  "ground_fm_aux (Ex x A) S = (ground_fm_aux A (S \<union> {atom x}))" 
by (auto simp: ground_fm_aux_def ground_aux_def supp_conv_fresh)

lemma ground_fresh[simp]:
  "ground t \<Longrightarrow> atom i \<sharp> t"
  "ground_fm A \<Longrightarrow> atom i \<sharp> A"
unfolding ground_aux_def ground_fm_aux_def fresh_def
by simp_all


section\<open>Sigma Formulas\<close>

text\<open>Section 2 material\<close>

subsection \<open>Strict Sigma Formulas\<close>

text\<open>Definition 2.1\<close>
inductive ss_fm :: "fm \<Rightarrow> bool" where
    MemI:  "ss_fm (Var i IN Var j)"
  | DisjI: "ss_fm A \<Longrightarrow> ss_fm B \<Longrightarrow> ss_fm (A OR B)"
  | ConjI: "ss_fm A \<Longrightarrow> ss_fm B \<Longrightarrow> ss_fm (A AND B)"
  | ExI:   "ss_fm A \<Longrightarrow> ss_fm (Ex i A)"
  | All2I: "ss_fm A \<Longrightarrow> atom j \<sharp> (i,A) \<Longrightarrow> ss_fm (All2 i (Var j) A)"

equivariance ss_fm

nominal_inductive ss_fm
  avoids ExI: "i" | All2I: "i"
by (simp_all add: fresh_star_def)

declare ss_fm.intros [intro]


definition Sigma_fm :: "fm \<Rightarrow> bool"
  where "Sigma_fm A \<longleftrightarrow> (\<exists>B. ss_fm B \<and> supp B \<subseteq> supp A \<and> {} \<turnstile> A IFF B)"

lemma Sigma_fm_Iff: "\<lbrakk>{} \<turnstile> B IFF A; supp A \<subseteq> supp B; Sigma_fm A\<rbrakk> \<Longrightarrow> Sigma_fm B"
  by (metis Sigma_fm_def Iff_trans order_trans)

lemma ss_fm_imp_Sigma_fm [intro]: "ss_fm A \<Longrightarrow> Sigma_fm A"
  by (metis Iff_refl Sigma_fm_def order_refl)

lemma Sigma_fm_Fls [iff]: "Sigma_fm Fls"
  by (rule Sigma_fm_Iff [of _ "Ex i (Var i IN Var i)"]) auto

subsection\<open>Closure properties for Sigma-formulas\<close>

lemma
  assumes "Sigma_fm A" "Sigma_fm B"  
    shows Sigma_fm_AND [intro!]: "Sigma_fm (A AND B)" 
      and Sigma_fm_OR [intro!]:  "Sigma_fm (A OR B)"
      and Sigma_fm_Ex [intro!]:  "Sigma_fm (Ex i A)"
proof -
  obtain SA SB where "ss_fm SA" "{} \<turnstile> A IFF SA" "supp SA \<subseteq> supp A"
                 and "ss_fm SB" "{} \<turnstile> B IFF SB" "supp SB \<subseteq> supp B"
    using assms by (auto simp add: Sigma_fm_def)
  then show "Sigma_fm (A AND B)"  "Sigma_fm (A OR B)"  "Sigma_fm (Ex i A)" 
    apply (auto simp: Sigma_fm_def)
    apply (metis ss_fm.ConjI Conj_cong Un_mono supp_Conj)
    apply (metis ss_fm.DisjI Disj_cong Un_mono fm.supp(3))
    apply (rule exI [where x = "Ex i SA"])
    apply (auto intro!: Ex_cong)
    done
qed

lemma Sigma_fm_All2_Var:
  assumes H0: "Sigma_fm A" and ij: "atom j \<sharp> (i,A)"
  shows "Sigma_fm (All2 i (Var j) A)"
proof -
  obtain SA where SA: "ss_fm SA" "{} \<turnstile> A IFF SA" "supp SA \<subseteq> supp A"
    using H0 by (auto simp add: Sigma_fm_def)
  show "Sigma_fm (All2 i (Var j) A)"
    apply (rule Sigma_fm_Iff [of _ "All2 i (Var j) SA"])
    apply (metis All2_cong Refl SA(2) emptyE)
    using SA ij
    apply (auto simp: supp_conv_fresh subset_iff)
    apply (metis ss_fm.All2I fresh_Pair ss_fm_imp_Sigma_fm)
    done
qed

  
section\<open>Lemma 2.2: Atomic formulas are Sigma-formulas\<close>

lemma Eq_Eats_Iff:
   assumes [unfolded fresh_Pair, simp]: "atom i \<sharp> (z,x,y)"
   shows "{} \<turnstile> z EQ Eats x y IFF (All2 i z (Var i IN x OR Var i EQ y)) AND x SUBS z AND y IN z"
proof (rule Iff_I, auto)
  have "{Var i IN z, z EQ Eats x y} \<turnstile> Var i IN Eats x y"
    by (metis Assume Iff_MP_left Iff_sym Mem_cong Refl)
  then show "{Var i IN z, z EQ Eats x y} \<turnstile> Var i IN x OR Var i EQ y"
    by (metis Iff_MP_same Mem_Eats_Iff)
next
  show "{z EQ Eats x y} \<turnstile> x SUBS z"
    by (metis Iff_MP2_same Subset_cong [OF Refl Assume] Subset_Eats_I)
next
  show "{z EQ Eats x y} \<turnstile> y IN z"
    by (metis Iff_MP2_same Mem_cong Assume Refl Mem_Eats_I2)
next
  show "{x SUBS z, y IN z, All2 i z (Var i IN x OR Var i EQ y)} \<turnstile> z EQ Eats x y"
       (is "{_, _, ?allHyp} \<turnstile> _")
    apply (rule Eq_Eats_iff [OF assms, THEN Iff_MP2_same], auto)
    apply (rule Ex_I [where x="Var i"])
    apply (auto intro: Subset_D  Mem_cong [OF Assume Refl, THEN Iff_MP2_same])
    done
qed

lemma Subset_Zero_sf: "Sigma_fm (Var i SUBS Zero)"
proof -
  obtain j::name where j: "atom j \<sharp> i"
    by (rule obtain_fresh)
  hence Subset_Zero_Iff: "{} \<turnstile> Var i SUBS Zero IFF (All2 j (Var i) Fls)"
    by (auto intro!: Subset_I [of j] intro: Eq_Zero_D Subset_Zero_D All2_E [THEN rotate2])
  thus ?thesis using j
    by (auto simp: supp_conv_fresh 
             intro!: Sigma_fm_Iff [OF Subset_Zero_Iff] Sigma_fm_All2_Var)
qed

lemma Eq_Zero_sf: "Sigma_fm (Var i EQ Zero)"
proof -
  obtain j::name where "atom j \<sharp> i"
    by (rule obtain_fresh)
  thus ?thesis
    by (auto simp add: supp_conv_fresh
             intro!: Sigma_fm_Iff [OF _ _ Subset_Zero_sf] Subset_Zero_D EQ_imp_SUBS)
qed

lemma theorem_sf: assumes "{} \<turnstile> A" shows "Sigma_fm A"
proof -
  obtain i::name and j::name
    where ij: "atom i \<sharp> (j,A)" "atom j \<sharp> A"
    by (metis obtain_fresh)
  show ?thesis
    apply (rule Sigma_fm_Iff [where A = "Ex i (Ex j (Var i IN Var j))"])
    using ij
    apply (auto simp: )
    apply (rule Ex_I [where x=Zero], simp)
    apply (rule Ex_I [where x="Eats Zero Zero"])
    apply (auto intro: Mem_Eats_I2 assms thin0)
    done
qed

text \<open>The subset relation\<close>
lemma Var_Subset_sf: "Sigma_fm (Var i SUBS Var j)"
proof -
  obtain k::name where k: "atom (k::name) \<sharp> (i,j)"
    by (metis obtain_fresh)
  thus ?thesis
  proof (cases "i=j")
    case True thus ?thesis using k
      by (auto intro!: theorem_sf Subset_I [where i=k])
  next
    case False thus ?thesis using k
      by (auto simp: ss_fm_imp_Sigma_fm Subset.simps [of k] ss_fm.intros)
  qed
qed

lemma Zero_Mem_sf: "Sigma_fm (Zero IN Var i)"
proof -
  obtain j::name where "atom j \<sharp> i"
    by (rule obtain_fresh)
  hence Zero_Mem_Iff: "{} \<turnstile> Zero IN Var i IFF (Ex j (Var j  EQ Zero AND Var j  IN Var i))"
    by (auto intro: Ex_I [where x = Zero]  Mem_cong [OF Assume Refl, THEN Iff_MP_same])
  show ?thesis 
    by (auto intro!: Sigma_fm_Iff [OF Zero_Mem_Iff] Eq_Zero_sf)
qed

lemma ijk: "i + k < Suc (i + j + k)"
  by arith

lemma All2_term_Iff_fresh: "i\<noteq>j \<Longrightarrow> atom j' \<sharp> (i,j,A) \<Longrightarrow>
   {} \<turnstile> (All2 i (Var j) A) IFF Ex j' (Var j EQ Var j' AND All2 i (Var j') A)"
apply auto
apply (rule Ex_I [where x="Var j"], auto)
apply (rule Ex_I [where x="Var i"], auto intro: ContraProve Mem_cong [THEN Iff_MP_same])
done

lemma Sigma_fm_All2_fresh:
  assumes "Sigma_fm A" "i\<noteq>j"
    shows "Sigma_fm (All2 i (Var j) A)"
proof -
  obtain j'::name where j': "atom j' \<sharp> (i,j,A)"
    by (metis obtain_fresh)
  show "Sigma_fm (All2 i (Var j) A)"
    apply (rule Sigma_fm_Iff [OF All2_term_Iff_fresh [OF _ j']])
    using assms j'
    apply (auto simp: supp_conv_fresh Var_Subset_sf
                intro!: Sigma_fm_All2_Var Sigma_fm_Iff [OF Extensionality _ _])
    done
qed

lemma Subset_Eats_sf:
  assumes "\<And>j::name. Sigma_fm (Var j IN t)"
      and "\<And>k::name. Sigma_fm (Var k EQ u)"
  shows "Sigma_fm (Var i SUBS Eats t u)"
proof -
  obtain k::name where k: "atom k \<sharp> (t,u,Var i)"
    by (metis obtain_fresh)
  hence "{} \<turnstile> Var i SUBS Eats t u IFF All2 k (Var i) (Var k IN t OR Var k EQ u)"
    apply (auto simp: fresh_Pair intro: Set_MP Disj_I1 Disj_I2)
    apply (force intro!: Subset_I [where i=k] intro: All2_E' [OF Hyp] Mem_Eats_I1 Mem_Eats_I2)
    done
  thus ?thesis
    apply (rule Sigma_fm_Iff)
    using k
    apply (auto intro!: Sigma_fm_All2_fresh simp add: assms fresh_Pair supp_conv_fresh fresh_at_base)
    done
qed

lemma Eq_Eats_sf:
  assumes "\<And>j::name. Sigma_fm (Var j EQ t)"
      and "\<And>k::name. Sigma_fm (Var k EQ u)"
  shows "Sigma_fm (Var i EQ Eats t u)"
proof -
  obtain j::name and k::name and l::name
    where atoms: "atom j \<sharp> (t,u,i)" "atom k \<sharp> (t,u,i,j)" "atom l \<sharp> (t,u,i,j,k)"
    by (metis obtain_fresh)
  hence "{} \<turnstile> Var i EQ Eats t u IFF
              Ex j (Ex k (Var i EQ Eats (Var j) (Var k) AND Var j EQ t AND Var k EQ u))"
    apply auto
    apply (rule Ex_I [where x=t], simp)
    apply (rule Ex_I [where x=u], auto intro: Trans Eats_cong)
    done
  thus ?thesis
    apply (rule Sigma_fm_Iff)
    apply (auto simp: assms supp_at_base)
    apply (rule Sigma_fm_Iff [OF Eq_Eats_Iff [of l]])
    using atoms
    apply (auto simp: supp_conv_fresh fresh_at_base Var_Subset_sf 
                intro!: Sigma_fm_All2_Var Sigma_fm_Iff [OF Extensionality _ _])
    done
qed

lemma Eats_Mem_sf:
  assumes "\<And>j::name. Sigma_fm (Var j EQ t)"
      and "\<And>k::name. Sigma_fm (Var k EQ u)"
  shows "Sigma_fm (Eats t u IN Var i)"
proof -
  obtain j::name where j: "atom j \<sharp> (t,u,Var i)"
    by (metis obtain_fresh)
  hence "{} \<turnstile> Eats t u IN Var i IFF
              Ex j (Var j IN Var i AND Var j EQ Eats t u)"
    apply (auto simp: fresh_Pair intro: Ex_I [where x="Eats t u"])
    apply (metis Assume Mem_cong [OF _ Refl, THEN Iff_MP_same] rotate2)
    done
  thus ?thesis
    by (rule Sigma_fm_Iff) (auto simp: assms supp_conv_fresh Eq_Eats_sf)
qed

lemma Subset_Mem_sf_lemma:
  "size t + size u < n \<Longrightarrow> Sigma_fm (t SUBS u) \<and> Sigma_fm (t IN u)"
proof (induction n arbitrary: t u rule: less_induct)
  case (less n t u)
  show ?case
  proof
    show "Sigma_fm (t SUBS u)"
      proof (cases t rule: tm.exhaust)
        case Zero thus ?thesis
          by (auto intro: theorem_sf)
      next
        case (Var i) thus ?thesis using less.prems
          apply (cases u rule: tm.exhaust)
          apply (auto simp: Subset_Zero_sf Var_Subset_sf)
          apply (force simp: supp_conv_fresh less.IH 
                       intro: Subset_Eats_sf Sigma_fm_Iff [OF Extensionality])
          done
      next
        case (Eats t1 t2) thus ?thesis using less.IH [OF _ ijk] less.prems
          by (auto intro!: Sigma_fm_Iff [OF Eats_Subset_Iff]  simp: supp_conv_fresh)
             (metis add.commute)
      qed
  next
    show "Sigma_fm (t IN u)"
      proof (cases u rule: tm.exhaust)
        case Zero show ?thesis
          by (rule Sigma_fm_Iff [where A=Fls]) (auto simp: supp_conv_fresh Zero)
      next
        case (Var i) show ?thesis
        proof (cases t rule: tm.exhaust)
          case Zero thus ?thesis using \<open>u = Var i\<close>
            by (auto intro: Zero_Mem_sf)
        next
          case (Var j)
          thus ?thesis using \<open>u = Var i\<close>
            by auto
        next
          case (Eats t1 t2) thus ?thesis using \<open>u = Var i\<close> less.prems
            by (force intro: Eats_Mem_sf Sigma_fm_Iff [OF Extensionality _ _] 
                      simp: supp_conv_fresh less.IH [THEN conjunct1])
        qed
      next
        case (Eats t1 t2) thus ?thesis  using  less.prems
          by (force intro: Sigma_fm_Iff [OF Mem_Eats_Iff] Sigma_fm_Iff [OF Extensionality _ _] 
                    simp: supp_conv_fresh less.IH)
      qed
  qed
qed

lemma Subset_sf [iff]: "Sigma_fm (t SUBS u)"
  by (metis Subset_Mem_sf_lemma [OF lessI])

lemma Mem_sf [iff]: "Sigma_fm (t IN u)"
  by (metis Subset_Mem_sf_lemma [OF lessI])

text \<open>The equality relation is a Sigma-Formula\<close>
lemma Equality_sf [iff]: "Sigma_fm (t EQ u)"
  by (auto intro: Sigma_fm_Iff [OF Extensionality] simp: supp_conv_fresh)


section\<open>Universal Quantification Bounded by an Arbitrary Term\<close>

lemma All2_term_Iff: "atom i \<sharp> t \<Longrightarrow> atom j \<sharp> (i,t,A) \<Longrightarrow> 
                  {} \<turnstile> (All2 i t A) IFF Ex j (Var j EQ t AND All2 i (Var j) A)"
apply auto
apply (rule Ex_I [where x=t], auto)
apply (rule Ex_I [where x="Var i"])
apply (auto intro: ContraProve Mem_cong [THEN Iff_MP2_same])
done

lemma Sigma_fm_All2 [intro!]:
  assumes "Sigma_fm A" "atom i \<sharp> t"
    shows "Sigma_fm (All2 i t A)"
proof -
  obtain j::name where j: "atom j \<sharp> (i,t,A)"
    by (metis obtain_fresh)
  show "Sigma_fm (All2 i t A)"
    apply (rule Sigma_fm_Iff [OF All2_term_Iff [of i t j]])
    using assms j
    apply (auto simp: supp_conv_fresh Sigma_fm_All2_Var)
    done
qed


section \<open>Lemma 2.3: Sequence-related concepts are Sigma-formulas\<close>

lemma OrdP_sf [iff]: "Sigma_fm (OrdP t)"
proof -
  obtain z::name and y::name where "atom z \<sharp> t" "atom y \<sharp> (t, z)"
    by (metis obtain_fresh)
  thus ?thesis
    by (auto simp: OrdP.simps)
qed

lemma OrdNotEqP_sf [iff]: "Sigma_fm (OrdNotEqP t u)"
  by (auto simp: OrdNotEqP.simps)

lemma HDomain_Incl_sf [iff]: "Sigma_fm (HDomain_Incl t u)"
proof -
  obtain x::name and y::name and z::name
    where "atom x \<sharp> (t,u,y,z)" "atom y \<sharp> (t,u,z)" "atom z \<sharp> (t,u)"
    by (metis obtain_fresh)
  thus ?thesis
    by auto
qed

lemma HFun_Sigma_Iff:
  assumes "atom z \<sharp> (r,z',x,y,x',y')"  "atom z' \<sharp> (r,x,y,x',y')"
       "atom x \<sharp> (r,y,x',y')"  "atom y \<sharp> (r,x',y')"
       "atom x' \<sharp> (r,y')"  "atom y' \<sharp> (r)"
  shows
  "{} \<turnstile>HFun_Sigma r IFF
         All2 z r (All2 z' r (Ex x (Ex y (Ex x' (Ex y'
             (Var z EQ HPair (Var x) (Var y) AND Var z' EQ HPair (Var x') (Var y')
              AND OrdP (Var x) AND OrdP (Var x') AND
              ((Var x NEQ Var x') OR (Var y EQ Var y'))))))))"
  apply (simp add: HFun_Sigma.simps [OF assms])
  apply (rule Iff_refl All_cong Imp_cong Ex_cong)+
  apply (rule Conj_cong [OF Iff_refl])
  apply (rule Conj_cong [OF Iff_refl], auto)
  apply (blast intro: Disj_I1 Neg_D OrdNotEqP_I)
  apply (blast intro: Disj_I2)
  apply (blast intro: OrdNotEqP_E rotate2)
  done

lemma HFun_Sigma_sf [iff]: "Sigma_fm (HFun_Sigma t)"
proof -
  obtain x::name and y::name and z::name and x'::name and y'::name and z'::name
    where atoms: "atom z \<sharp> (t,z',x,y,x',y')"  "atom z' \<sharp> (t,x,y,x',y')"
       "atom x \<sharp> (t,y,x',y')"  "atom y \<sharp> (t,x',y')"
       "atom x' \<sharp> (t,y')"  "atom y' \<sharp> (t)"
    by (metis obtain_fresh)
  show ?thesis
    by (auto intro!: Sigma_fm_Iff [OF HFun_Sigma_Iff [OF atoms]] simp: supp_conv_fresh atoms)
qed

lemma LstSeqP_sf [iff]: "Sigma_fm (LstSeqP t u v)"
  by (auto simp: LstSeqP.simps)

  
section \<open>A Key Result: Theorem 2.5\<close>

subsection \<open>Sigma-Eats Formulas\<close>

inductive se_fm :: "fm \<Rightarrow> bool" where
    MemI:  "se_fm (t IN u)"
  | DisjI: "se_fm A \<Longrightarrow> se_fm B \<Longrightarrow> se_fm (A OR B)"
  | ConjI: "se_fm A \<Longrightarrow> se_fm B \<Longrightarrow> se_fm (A AND B)"
  | ExI:   "se_fm A \<Longrightarrow> se_fm (Ex i A)"
  | All2I: "se_fm A \<Longrightarrow> atom i \<sharp> t \<Longrightarrow> se_fm (All2 i t A)"

equivariance se_fm

nominal_inductive se_fm
  avoids ExI: "i" | All2I: "i"
by (simp_all add: fresh_star_def)

declare se_fm.intros [intro]

lemma subst_fm_in_se_fm: "se_fm A \<Longrightarrow> se_fm (A(k::=x))"
by (nominal_induct avoiding: k x rule: se_fm.strong_induct) (auto)

subsection\<open>Preparation\<close>
text\<open>To begin, we require some facts connecting quantification and ground terms.\<close>

lemma obtain_const_tm:  obtains t where "\<lbrakk>t\<rbrakk>e = x" "ground t"
proof (induct x rule: hf_induct)
  case 0 thus ?case
    by (metis ground_aux_simps(1) eval_tm.simps(1))
next
  case (hinsert y x) thus ?case
    by (metis ground_aux_simps(3) eval_tm.simps(3))
qed

lemma ex_eval_fm_iff_exists_tm:
  "eval_fm e (Ex k A) \<longleftrightarrow> (\<exists>t. eval_fm e (A(k::=t)) \<and> ground t)"
by (auto simp: eval_subst_fm) (metis obtain_const_tm)

text\<open>In a negative context, the formulation above is actually weaker than this one.\<close>
lemma ex_eval_fm_iff_exists_tm':
  "eval_fm e (Ex k A) \<longleftrightarrow> (\<exists>t. eval_fm e (A(k::=t)))"
by (auto simp: eval_subst_fm) (metis obtain_const_tm)

text\<open>A ground term defines a finite set of ground terms, its elements.\<close>
nominal_function elts :: "tm \<Rightarrow> tm set" where
   "elts Zero       = {}"
 | "elts (Var k)    = {}"
 | "elts (Eats t u) = insert u (elts t)"
by (auto simp: eqvt_def elts_graph_aux_def) (metis tm.exhaust)

nominal_termination (eqvt)
  by lexicographic_order

lemma eval_fm_All2_Eats:
  "atom i \<sharp> (t,u) \<Longrightarrow>
   eval_fm e (All2 i (Eats t u) A) \<longleftrightarrow> eval_fm e (A(i::=u)) \<and> eval_fm e (All2 i t A)"
  by (simp only: ex_eval_fm_iff_exists_tm' eval_fm.simps) (auto simp: eval_subst_fm)

text\<open>The term @{term t} must be ground, since @{term elts} doesn't handle variables.\<close>
lemma eval_fm_All2_Iff_elts:
  "ground t \<Longrightarrow> eval_fm e (All2 i t A) \<longleftrightarrow> (\<forall>u \<in> elts t. eval_fm e (A(i::=u)))"
apply (induct t rule: tm.induct)
apply auto [2]
apply (simp add: eval_fm_All2_Eats del: eval_fm.simps)
done

lemma prove_elts_imp_prove_All2:
   "ground t \<Longrightarrow> (\<And>u. u \<in> elts t \<Longrightarrow> {} \<turnstile> A(i::=u)) \<Longrightarrow> {} \<turnstile> All2 i t A"
proof (induct t rule: tm.induct)
  case Zero thus ?case
    by auto
next
  case (Var i) thus ?case  \<comment> \<open>again: vacuously!\<close>
    by simp
next
  case (Eats t u)
  hence pt: "{} \<turnstile> All2 i t A" and pu: "{} \<turnstile> A(i::=u)"
    by auto
  have "{} \<turnstile> ((Var i IN t) IMP A)(i ::= Var i)"
    by (rule All_D [OF pt])
  hence "{} \<turnstile> ((Var i IN t) IMP A)"
    by simp
  thus ?case using pu
    by (auto intro: anti_deduction) (metis Iff_MP_same Var_Eq_subst_Iff thin1)
qed

subsection\<open>The base cases: ground atomic formulas\<close>

lemma ground_prove:
   "\<lbrakk>size t + size u < n; ground t; ground u\<rbrakk>
    \<Longrightarrow> (\<lbrakk>t\<rbrakk>e \<le> \<lbrakk>u\<rbrakk>e \<longrightarrow> {} \<turnstile> t SUBS u) \<and> (\<lbrakk>t\<rbrakk>e \<^bold>\<in> \<lbrakk>u\<rbrakk>e \<longrightarrow> {} \<turnstile> t IN u)"
proof (induction n arbitrary: t u rule: less_induct)
  case (less n t u)
  show ?case
  proof
    show "\<lbrakk>t\<rbrakk>e \<le> \<lbrakk>u\<rbrakk>e \<longrightarrow> {} \<turnstile> t SUBS u" using less
      by (cases t rule: tm.exhaust) auto
  next
    { fix y t u
      have "\<lbrakk>y < n; size t + size u < y; ground t; ground u; \<lbrakk>t\<rbrakk>e = \<lbrakk>u\<rbrakk>e\<rbrakk>
           \<Longrightarrow> {} \<turnstile> t EQ u"
        by (metis Equality_I less.IH add.commute order_refl)
    }
    thus "\<lbrakk>t\<rbrakk>e \<^bold>\<in> \<lbrakk>u\<rbrakk>e \<longrightarrow> {} \<turnstile> t IN u" using less.prems
      by (cases u rule: tm.exhaust) (auto simp: Mem_Eats_I1 Mem_Eats_I2 less.IH)
  qed
qed

lemma 
  assumes "ground t" "ground u"
    shows ground_prove_SUBS: "\<lbrakk>t\<rbrakk>e \<le> \<lbrakk>u\<rbrakk>e \<Longrightarrow> {} \<turnstile> t SUBS u"
      and ground_prove_IN:   "\<lbrakk>t\<rbrakk>e \<^bold>\<in> \<lbrakk>u\<rbrakk>e \<Longrightarrow> {} \<turnstile> t IN u"
      and ground_prove_EQ:   "\<lbrakk>t\<rbrakk>e = \<lbrakk>u\<rbrakk>e \<Longrightarrow> {} \<turnstile> t EQ u"
  by (metis Equality_I assms ground_prove [OF lessI] order_refl)+

lemma ground_subst: 
  "ground_aux tm (insert (atom i) S) \<Longrightarrow> ground t \<Longrightarrow> ground_aux (subst i t tm) S"
  by (induct tm rule: tm.induct) (auto simp: ground_aux_def)

lemma ground_subst_fm: 
  "ground_fm_aux A (insert (atom i) S) \<Longrightarrow> ground t \<Longrightarrow> ground_fm_aux (A(i::=t)) S"
  apply (nominal_induct A avoiding: i arbitrary: S rule: fm.strong_induct)
  apply (auto simp: ground_subst Set.insert_commute)
  done

lemma elts_imp_ground: "u \<in> elts t \<Longrightarrow> ground_aux t S \<Longrightarrow> ground_aux u S"
  by (induct t rule: tm.induct) auto

lemma ground_se_fm_induction:
   "ground_fm \<alpha> \<Longrightarrow> size \<alpha> < n \<Longrightarrow> se_fm \<alpha> \<Longrightarrow> eval_fm e \<alpha> \<Longrightarrow> {} \<turnstile> \<alpha>"
proof (induction n arbitrary: \<alpha> rule: less_induct)
  case (less n \<alpha>)
  show ?case using \<open>se_fm \<alpha>\<close>
  proof (cases rule: se_fm.cases)
    case (MemI t u) thus "{} \<turnstile> \<alpha>" using less
      by (auto intro: ground_prove_IN)
  next
    case (DisjI A B) thus "{} \<turnstile> \<alpha>" using less
      by (auto intro: Disj_I1 Disj_I2)
  next
    case (ConjI A B) thus "{} \<turnstile> \<alpha>" using less
      by auto
  next
    case (ExI A i)
    thus "{} \<turnstile> \<alpha>" using less.prems
      apply (auto simp: ex_eval_fm_iff_exists_tm simp del: better_ex_eval_fm)
      apply (auto intro!: Ex_I less.IH subst_fm_in_se_fm ground_subst_fm)
      done
  next
    case (All2I A i t)
    hence t: "ground t" using less.prems
      by (auto simp: ground_aux_def fresh_def)
    hence "(\<forall>u\<in>elts t. eval_fm e (A(i::=u)))"
      by (metis All2I(1) t eval_fm_All2_Iff_elts less(5))
    thus "{} \<turnstile> \<alpha>" using less.prems All2I t
      apply (auto del: Neg_I intro!: prove_elts_imp_prove_All2 less.IH)
      apply (auto intro: subst_fm_in_se_fm ground_subst_fm elts_imp_ground)
      done
  qed
qed

lemma ss_imp_se_fm: "ss_fm A \<Longrightarrow> se_fm A"
  by (erule ss_fm.induct) auto

lemma se_fm_imp_thm: "\<lbrakk>se_fm A; ground_fm A; eval_fm e A\<rbrakk> \<Longrightarrow> {} \<turnstile> A"
  by (metis ground_se_fm_induction lessI)

text\<open>Theorem 2.5\<close>
theorem Sigma_fm_imp_thm: "\<lbrakk>Sigma_fm A; ground_fm A; eval_fm e0 A\<rbrakk> \<Longrightarrow> {} \<turnstile> A"
  by (metis Iff_MP2_same ss_imp_se_fm empty_iff Sigma_fm_def eval_fm_Iff ground_fm_aux_def 
            hfthm_sound se_fm_imp_thm subset_empty)

end

