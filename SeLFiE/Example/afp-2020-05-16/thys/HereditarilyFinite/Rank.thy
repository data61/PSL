chapter \<open>V-Sets, Epsilon Closure, Ranks\<close>

theory Rank imports Ordinal
begin

section \<open>V-sets\<close>

text \<open>Definition 4.1\<close>
definition Vset :: "hf \<Rightarrow> hf"
  where "Vset x = ord_rec 0 HPow (\<lambda>z. 0) x"

lemma Vset_0 [simp]: "Vset 0 = 0"
  by (simp add: Vset_def)

lemma Vset_succ [simp]: "Ord k \<Longrightarrow> Vset (succ k) = HPow (Vset k)"
  by (simp add: Vset_def)

lemma Vset_non [simp]: "\<not> Ord x \<Longrightarrow> Vset x = 0"
  by (simp add: Vset_def)

text \<open>Theorem 4.2(a)\<close>
lemma Vset_mono_strict:
  assumes "Ord m" "n \<^bold>\<in> m" shows "Vset n < Vset m"
proof -
  have n: "Ord n"
    by (metis Ord_in_Ord assms)
  hence "Ord m \<Longrightarrow> n \<^bold>\<in> m \<Longrightarrow> Vset n < Vset m"
  proof (induct n arbitrary: m rule: Ord_induct2)
    case 0 thus ?case
      by (metis HPow_iff Ord_cases Vset_0 Vset_succ hemptyE le_imp_less_or_eq zero_le)
  next
    case (succ n)
    then show ?case using \<open>Ord m\<close>
      by (metis Ord_cases hemptyE HPow_mono_strict_iff Vset_succ mem_succ_iff)
  qed
  thus ?thesis using assms .
qed

lemma Vset_mono: "\<lbrakk>Ord m; n \<le> m\<rbrakk> \<Longrightarrow> Vset n \<le> Vset m"
  by (metis Ord_linear2 Vset_mono_strict Vset_non order.order_iff_strict
            order_class.order.antisym zero_le)

text \<open>Theorem 4.2(b)\<close>
lemma Vset_Transset: "Ord m \<Longrightarrow> Transset (Vset m)"
  by (induct rule: Ord_induct2) (auto simp: Transset_def)

lemma Ord_sup [simp]: "Ord k \<Longrightarrow> Ord l \<Longrightarrow> Ord (k \<squnion> l)"
  by (metis Ord_linear_le le_iff_sup sup_absorb1)

lemma Ord_inf [simp]: "Ord k \<Longrightarrow> Ord l \<Longrightarrow> Ord (k \<sqinter> l)"
  by (metis Ord_linear_le inf_absorb2 le_iff_inf)


text \<open>Theorem 4.3\<close>
lemma Vset_universal: "\<exists>n. Ord n \<and> x \<^bold>\<in> Vset n"
proof (induct x rule: hf_induct)
  case 0 thus ?case
    by (metis HPow_iff Ord_0 Ord_succ Vset_succ zero_le)
next
  case (hinsert a b)
  then obtain na nb where nab: "Ord na" "a \<^bold>\<in> Vset na" "Ord nb" "b \<^bold>\<in> Vset nb"
    by blast
  hence "b \<le> Vset nb" using Vset_Transset [of nb]
    by (auto simp: Transset_def)
  also have "... \<le> Vset (na \<squnion> nb)" using nab
    by (metis Ord_sup Vset_mono sup_ge2)
  finally have "b \<triangleleft> a \<^bold>\<in> Vset (succ (na \<squnion> nb))" using nab
    by simp (metis Ord_sup Vset_mono sup_ge1 rev_hsubsetD)
  thus ?case using nab
    by (metis Ord_succ Ord_sup)
qed


section \<open>Least Ordinal Operator\<close>

text \<open>Definition 4.4. For every x, let rank(x) be the least ordinal n such that...\<close>

lemma Ord_minimal:
   "Ord k \<Longrightarrow> P k \<Longrightarrow> \<exists>n. Ord n \<and> P n \<and> (\<forall>m. Ord m \<and> P m \<longrightarrow> n \<le> m)"
  by (induct k rule: Ord_induct) (metis Ord_linear2)

lemma OrdLeastI: "Ord k \<Longrightarrow> P k \<Longrightarrow> P(LEAST n. Ord n \<and> P n)"
by (metis (lifting, no_types) Least_equality Ord_minimal)

lemma OrdLeast_le: "Ord k \<Longrightarrow> P k \<Longrightarrow> (LEAST n. Ord n \<and> P n) \<le> k"
by (metis (lifting, no_types) Least_equality Ord_minimal)

lemma OrdLeast_Ord:
  assumes "Ord k" "P k"shows "Ord(LEAST n. Ord n \<and> P n)"
proof -
  obtain n where "Ord n" "P n" "\<forall>m. Ord m \<and> P m \<longrightarrow> n \<le> m"
    by (metis Ord_minimal assms)
  thus ?thesis
    by (metis (lifting) Least_equality)
qed


section \<open>Rank Function\<close>

definition rank :: "hf \<Rightarrow> hf"
  where "rank x = (LEAST n. Ord n \<and> x \<^bold>\<in> Vset (succ n))"

lemma [simp]: "rank 0 = 0"
  by (simp add: rank_def) (metis (lifting) HPow_iff Least_equality Ord_0 Vset_succ zero_le)

lemma in_Vset_rank: "a \<^bold>\<in> Vset(succ(rank a))"
proof -
  from Vset_universal [of a]
  obtain na where na: "Ord na" "a \<^bold>\<in> Vset (succ na)"
    by (metis Ord_Union Ord_in_Ord Ord_pred Vset_0 hempty_iff)
  thus ?thesis
    by (unfold rank_def) (rule OrdLeastI)
qed

lemma Ord_rank [simp]: "Ord (rank a)"
  by (metis Ord_succ_iff Vset_non hemptyE in_Vset_rank)

lemma le_Vset_rank: "a \<le> Vset(rank a)"
  by (metis HPow_iff Ord_succ_iff Vset_non Vset_succ hemptyE in_Vset_rank)

lemma VsetI: "succ(rank a) \<le> k \<Longrightarrow> Ord k \<Longrightarrow> a \<^bold>\<in> Vset k"
  by (metis Vset_mono hsubsetCE in_Vset_rank)

lemma Vset_succ_rank_le: "Ord k \<Longrightarrow> a \<^bold>\<in> Vset (succ k) \<Longrightarrow> rank a \<le> k"
  by (unfold rank_def) (rule OrdLeast_le)

lemma Vset_rank_lt: assumes a: "a \<^bold>\<in> Vset k" shows "rank a < k"
proof -
  { assume k: "Ord k"
    hence ?thesis
    proof (cases k rule: Ord_cases)
      case 0 thus ?thesis using a
        by simp
    next
      case (succ l) thus ?thesis using a
        by (metis Ord_lt_succ_iff_le Ord_succ_iff Vset_non Vset_succ_rank_le hemptyE in_Vset_rank)
    qed
  }
  thus ?thesis using a
    by (metis Vset_non hemptyE)
qed

text \<open>Theorem 4.5\<close>
theorem rank_lt: "a \<^bold>\<in> b \<Longrightarrow> rank(a) < rank(b)"
  by (metis Vset_rank_lt hsubsetD le_Vset_rank)

lemma rank_mono: "x \<le> y \<Longrightarrow> rank x \<le> rank y"
  by (metis HPow_iff Ord_rank Vset_succ Vset_succ_rank_le dual_order.trans le_Vset_rank)

lemma rank_sup [simp]: "rank (a \<squnion> b) = rank a \<squnion> rank b"
proof (rule antisym)
  have o: "Ord (rank a \<squnion> rank b)"
    by simp
  thus "rank (a \<squnion> b) \<le> rank a \<squnion> rank b"
    apply (rule Vset_succ_rank_le, simp)
    apply (metis le_Vset_rank order_trans Vset_mono sup_ge1 sup_ge2 o)
    done
next
  show "rank a \<squnion> rank b \<le> rank (a \<squnion> b)"
    by (metis le_supI le_supI1 le_supI2 order_eq_refl rank_mono)
qed

lemma rank_singleton [simp]: "rank \<lbrace>a\<rbrace> = succ(rank a)"
proof -
  have oba: "Ord (succ (rank a))"
    by simp
  show ?thesis
    proof (rule antisym)
      show "rank \<lbrace>a\<rbrace> \<le> succ (rank a)"
        by (metis Vset_succ_rank_le HPow_iff Vset_succ in_Vset_rank less_eq_insert1_iff oba zero_le)
    next
      show "succ (rank a) \<le> rank\<lbrace>a\<rbrace>"
        by (metis Ord_linear_le Ord_lt_succ_iff_le rank_lt Ord_rank hmem_hinsert less_le_not_le oba)
    qed
qed

lemma rank_hinsert [simp]: "rank (b \<triangleleft> a) = rank b \<squnion> succ(rank a)"
  by (metis hinsert_eq_sup rank_singleton rank_sup)

text \<open>Definition 4.6. The transitive closure of @{term x} is
 the minimal transitive set @{term y} such that @{term"x\<le>y"}.\<close>


section \<open>Epsilon Closure\<close>

definition
  eclose    :: "hf \<Rightarrow> hf"  where
    "eclose X = \<Sqinter> \<lbrace>Y \<^bold>\<in> HPow(Vset (rank X)). Transset Y \<and> X\<le>Y\<rbrace>"

lemma eclose_facts:
  shows Transset_eclose: "Transset (eclose X)"
   and  le_eclose: "X \<le> eclose X"
proof -
  have nz: "\<lbrace>Y \<^bold>\<in> HPow(Vset (rank X)). Transset Y \<and> X\<le>Y\<rbrace> \<noteq> 0"
    by (simp add: eclose_def hempty_iff) (metis Ord_rank Vset_Transset le_Vset_rank order_refl)
  show "Transset (eclose X)" "X \<le> eclose X" using HInter_iff [OF nz]
    by (auto simp: eclose_def Transset_def)
qed

lemma eclose_minimal:
  assumes Y: "Transset Y" "X\<le>Y" shows "eclose X \<le> Y"
proof -
  have "\<lbrace>Y \<^bold>\<in> HPow(Vset (rank X)). Transset Y \<and> X\<le>Y\<rbrace> \<noteq> 0"
    by (simp add: eclose_def hempty_iff) (metis Ord_rank Vset_Transset le_Vset_rank order_refl)
  moreover have "Transset (Y \<sqinter> Vset (rank X))"
    by (metis Ord_rank Transset_inf Vset_Transset Y(1))
  moreover have "X \<le> Y \<sqinter> Vset (rank X)"
    by (metis Y(2) le_Vset_rank le_inf_iff)
  ultimately show "eclose X \<le> Y"
    apply (auto simp: eclose_def)
    apply (metis hinter_iff le_inf_iff order_refl)
    done
qed

lemma eclose_0 [simp]: "eclose 0 = 0"
  by (metis Ord_0 Vset_0 Vset_Transset eclose_minimal less_eq_hempty)

lemma eclose_sup [simp]: "eclose (a \<squnion> b) = eclose a \<squnion> eclose b"
proof (rule order_antisym)
  show "eclose (a \<squnion> b) \<le> eclose a \<squnion> eclose b"
    by (metis Transset_eclose Transset_sup eclose_minimal le_eclose sup_mono)
next
  show "eclose a \<squnion> eclose b \<le> eclose (a \<squnion> b)"
    by (metis Transset_eclose eclose_minimal le_eclose le_sup_iff)
qed

lemma eclose_singleton [simp]: "eclose \<lbrace>a\<rbrace> = (eclose a) \<triangleleft> a"
proof (rule order_antisym)
  show "eclose \<lbrace>a\<rbrace> \<le> eclose a \<triangleleft> a"
    by (metis eclose_minimal Transset_eclose Transset_hinsert
              le_eclose less_eq_insert1_iff order_refl zero_le)
next
  show "eclose a \<triangleleft> a \<le> eclose \<lbrace>a\<rbrace>"
    by (metis Transset_def Transset_eclose eclose_minimal le_eclose less_eq_insert1_iff)
qed

lemma eclose_hinsert [simp]: "eclose (b \<triangleleft> a) = eclose b \<squnion> (eclose a \<triangleleft> a)"
  by (metis eclose_singleton eclose_sup hinsert_eq_sup)

lemma eclose_succ [simp]: "eclose (succ a) = eclose a \<triangleleft> a"
  by (auto simp: succ_def)

lemma fst_in_eclose [simp]: "x \<^bold>\<in> eclose \<langle>x, y\<rangle>"
  by (metis eclose_hinsert hmem_hinsert hpair_def hunion_iff)

lemma snd_in_eclose [simp]: "y \<^bold>\<in> eclose \<langle>x, y\<rangle>"
  by (metis eclose_hinsert hmem_hinsert hpair_def hunion_iff)

text \<open>Theorem 4.7. rank(x) = rank(cl(x)).\<close>
lemma rank_eclose [simp]: "rank (eclose x) = rank x"
proof (induct x rule: hf_induct)
  case 0 thus ?case by simp
next
  case (hinsert a b) thus ?case
    by simp (metis hinsert_eq_sup succ_def sup.left_idem)
qed


section \<open>Epsilon-Recursion\<close>

text \<open>Theorem 4.9.  Definition of a function by recursion on rank.\<close>

lemma hmem_induct [case_names step]:
  assumes ih: "\<And>x. (\<And>y. y \<^bold>\<in> x \<Longrightarrow> P y) \<Longrightarrow> P x" shows "P x"
proof -
  have "\<And>y. y \<^bold>\<in> x \<Longrightarrow> P y"
  proof (induct x rule: hf_induct)
    case 0 thus ?case by simp
  next
    case (hinsert a b) thus ?case
      by (metis assms hmem_hinsert)
  qed
  thus ?thesis by (metis ih)
qed

definition
  hmem_rel :: "(hf * hf) set" where
  "hmem_rel = trancl {(x,y). x \<^bold>\<in> y}"

lemma wf_hmem_rel: "wf hmem_rel"
proof -
  have "wf {(x,y). x \<^bold>\<in> y}"
    by (metis (full_types) hmem_induct wfPUNIVI wfP_def)
  thus ?thesis
    by (metis hmem_rel_def wf_trancl)
qed

lemma hmem_eclose_le: "y \<^bold>\<in> x \<Longrightarrow> eclose y \<le> eclose x"
  by (metis Transset_def Transset_eclose eclose_minimal hsubsetD le_eclose)

lemma hmem_rel_iff_hmem_eclose: "(x,y) \<in> hmem_rel \<longleftrightarrow> x \<^bold>\<in> eclose y"
proof (unfold hmem_rel_def, rule iffI)
  assume "(x, y) \<in> trancl {(x, y). x \<^bold>\<in> y}"
  thus "x \<^bold>\<in> eclose y"
    proof (induct rule: trancl_induct)
      case (base y) thus ?case
        by (metis hsubsetCE le_eclose mem_Collect_eq split_conv)
    next
      case (step y z) thus ?case
        by (metis hmem_eclose_le hsubsetD mem_Collect_eq split_conv)
    qed
next
  have "Transset \<lbrace>x \<^bold>\<in> eclose y. (x, y) \<in> hmem_rel\<rbrace>" using Transset_eclose
    by (auto simp: Transset_def hmem_rel_def intro: trancl_trans)
  hence "eclose y \<le> \<lbrace>x \<^bold>\<in> eclose y. (x, y) \<in> hmem_rel\<rbrace>"
    by (rule eclose_minimal) (auto simp: le_HCollect_iff le_eclose hmem_rel_def)
  moreover assume "x \<^bold>\<in> eclose y"
  ultimately show "(x, y) \<in> trancl {(x, y). x \<^bold>\<in> y}"
    by (metis HCollect_iff hmem_rel_def hsubsetD)
qed

definition hmemrec :: "((hf \<Rightarrow> 'a) \<Rightarrow> hf \<Rightarrow> 'a) \<Rightarrow> hf \<Rightarrow> 'a" where
  "hmemrec G \<equiv> wfrec hmem_rel G"

definition ecut :: "(hf \<Rightarrow> 'a) \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> 'a" where
  "ecut f x \<equiv> (\<lambda>y. if y \<^bold>\<in> eclose x then f y else undefined)"

lemma hmemrec: "hmemrec G a = G (ecut (hmemrec G) a) a"
  by (simp add: cut_def ecut_def hmem_rel_iff_hmem_eclose def_wfrec [OF hmemrec_def wf_hmem_rel])

text \<open>This form avoids giant explosions in proofs.\<close>
lemma def_hmemrec: "f \<equiv> hmemrec G \<Longrightarrow> f a = G (ecut (hmemrec G) a) a"
  by (metis hmemrec)

lemma ecut_apply: "y \<^bold>\<in> eclose x \<Longrightarrow> ecut f x y = f y"
  by (metis ecut_def)

lemma RepFun_ecut: "y \<le> z \<Longrightarrow> RepFun y (ecut f z) = RepFun y f"
  apply (auto simp: hf_ext)
  apply (metis ecut_def hsubsetD le_eclose)
  apply (metis ecut_apply le_eclose hsubsetD)
  done

text \<open>Now, a stronger induction rule, for the transitive closure of membership\<close>
lemma hmem_rel_induct [case_names step]:
  assumes ih: "\<And>x. (\<And>y. (y,x) \<in> hmem_rel \<Longrightarrow> P y) \<Longrightarrow> P x" shows "P x"
proof -
  have "\<And>y. (y,x) \<in> hmem_rel \<Longrightarrow> P y"
  proof (induct x rule: hf_induct)
    case 0 thus ?case
      by (metis eclose_0 hmem_hempty hmem_rel_iff_hmem_eclose)
  next
    case (hinsert a b)
    thus ?case
      by (metis assms eclose_hinsert hmem_hinsert hmem_rel_iff_hmem_eclose hunion_iff)
  qed
  thus ?thesis  by (metis assms)
qed

lemma rank_HUnion_less:  "x \<noteq> 0 \<Longrightarrow> rank (\<Squnion>x) < rank x"
  apply (induct x rule: hf_induct, auto)
  apply (metis hmem_hinsert rank_hinsert rank_lt)
  apply (metis HUnion_hempty Ord_lt_succ_iff_le Ord_rank hunion_hempty_right
               less_supI1 less_supI2 rank_sup sup.cobounded2)
  done

corollary Sup_ne: "x \<noteq> 0 \<Longrightarrow> \<Squnion>x \<noteq> x"
  by (metis less_irrefl rank_HUnion_less)

end
