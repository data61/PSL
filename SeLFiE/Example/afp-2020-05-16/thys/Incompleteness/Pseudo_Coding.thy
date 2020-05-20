chapter\<open>Pseudo-Coding: Section 7 Material\<close>

theory Pseudo_Coding 
imports II_Prelims
begin

section\<open>General Lemmas\<close>

lemma Collect_disj_Un: "{f i |i. P i \<or> Q i} = {f i |i. P i} \<union> {f i |i. Q i}"
by auto 

abbreviation Q_Subset :: "tm \<Rightarrow> tm \<Rightarrow> tm"
  where "Q_Subset t u \<equiv> (Q_All (Q_Imp (Q_Mem (Q_Ind Zero) t) (Q_Mem (Q_Ind Zero) u)))"

lemma NEQ_quot_tm: "i\<noteq>j \<Longrightarrow> {} \<turnstile> \<guillemotleft>Var i\<guillemotright> NEQ \<guillemotleft>Var j\<guillemotright>"
  by (auto intro: Sigma_fm_imp_thm [OF OrdNotEqP_sf] 
           simp: ground_fm_aux_def supp_conv_fresh quot_tm_def)

lemma EQ_quot_tm_Fls: "i\<noteq>j \<Longrightarrow> insert (\<guillemotleft>Var i\<guillemotright> EQ \<guillemotleft>Var j\<guillemotright>) H \<turnstile> Fls"
  by (metis (full_types) NEQ_quot_tm Assume OrdNotEqP_E cut2 thin0)

lemma perm_commute: "a \<sharp> p \<Longrightarrow> a' \<sharp> p \<Longrightarrow> (a \<rightleftharpoons> a') + p = p + (a \<rightleftharpoons> a')"
  by (rule plus_perm_eq) (simp add: supp_swap fresh_def)

lemma perm_self_inverseI: "\<lbrakk>-p = q; a \<sharp> p; a' \<sharp> p\<rbrakk> \<Longrightarrow> - ((a \<rightleftharpoons> a') + p) = (a \<rightleftharpoons> a') + q"
  by (simp_all add: perm_commute fresh_plus_perm minus_add)

lemma fresh_image:
  fixes f :: "'a \<Rightarrow> 'b::fs"  shows "finite A \<Longrightarrow> i \<sharp> f ` A \<longleftrightarrow> (\<forall>x\<in>A. i \<sharp> f x)"
  by (induct rule: finite_induct) (auto simp: fresh_finite_insert)

lemma atom_in_atom_image [simp]: "atom j \<in> atom ` V \<longleftrightarrow> j \<in> V"
  by auto

lemma fresh_star_empty [simp]: "{} \<sharp>* bs"
  by (simp add: fresh_star_def)

declare fresh_star_insert [simp]

lemma fresh_star_finite_insert:
  fixes S :: "('a::fs) set"  shows "finite S \<Longrightarrow> a \<sharp>* insert x S \<longleftrightarrow> a \<sharp>* x \<and> a \<sharp>* S"
  by (auto simp: fresh_star_def fresh_finite_insert) 

lemma fresh_finite_Diff_single [simp]:
  fixes V :: "name set"   shows "finite V \<Longrightarrow> a \<sharp> (V - {j}) \<longleftrightarrow> (a \<sharp> j \<longrightarrow> a \<sharp> V)"
apply (auto simp: fresh_finite_insert)
apply (metis finite_Diff fresh_finite_insert insert_Diff_single)
apply (metis Diff_iff finite_Diff fresh_atom fresh_atom_at_base fresh_finite_set_at_base insertI1)
apply (metis Diff_idemp Diff_insert_absorb finite_Diff fresh_finite_insert insert_Diff_single insert_absorb)
done

lemma fresh_image_atom [simp]: "finite A \<Longrightarrow> i \<sharp> atom ` A \<longleftrightarrow> i \<sharp> A"
  by (induct rule: finite_induct) (auto simp: fresh_finite_insert)

lemma atom_fresh_star_atom_set_conv: "\<lbrakk>atom i \<sharp> bs; finite bs\<rbrakk> \<Longrightarrow> bs \<sharp>* i"
by (metis fresh_finite_atom_set fresh_ineq_at_base fresh_star_def)

lemma notin_V:
  assumes p: "atom i \<sharp> p" and V: "finite V" "atom ` (p \<bullet> V) \<sharp>* V" 
  shows "i \<notin> V" "i \<notin> p \<bullet> V"
  using V
  apply (auto simp: fresh_def fresh_star_def supp_finite_set_at_base)
  apply (metis p mem_permute_iff fresh_at_base_permI)+
  done

section\<open>Simultaneous Substitution\<close>

definition ssubst :: "tm \<Rightarrow> name set \<Rightarrow> (name \<Rightarrow> tm) \<Rightarrow> tm"
  where "ssubst t V F = Finite_Set.fold (\<lambda>i. subst i (F i)) t V"

definition make_F :: "name set \<Rightarrow> perm \<Rightarrow> name \<Rightarrow> tm"
  where "make_F Vs p \<equiv> \<lambda>i. if i \<in> Vs then Var (p \<bullet> i) else Var i"

lemma ssubst_empty [simp]: "ssubst t {} F = t"
  by (simp add: ssubst_def)

text\<open>Renaming a finite set of variables. Based on the theorem \<open>at_set_avoiding\<close>\<close>
locale quote_perm =
  fixes p :: perm and Vs :: "name set" and F :: "name \<Rightarrow> tm"
  assumes p: "atom ` (p \<bullet> Vs) \<sharp>* Vs" 
      and pinv: "-p = p"
      and Vs:  "finite Vs" 
  defines "F \<equiv> make_F Vs p"
begin

lemma F_unfold: "F i = (if i \<in> Vs then Var (p \<bullet> i) else Var i)"
  by (simp add: F_def make_F_def)

lemma finite_V [simp]: "V \<subseteq> Vs \<Longrightarrow> finite V"
  by (metis Vs finite_subset)

lemma perm_exits_Vs: "i \<in> Vs \<Longrightarrow> (p \<bullet> i) \<notin> Vs" 
  by (metis Vs fresh_finite_set_at_base imageI fresh_star_def mem_permute_iff p)

lemma atom_fresh_perm: "\<lbrakk>x \<in> Vs; y \<in> Vs\<rbrakk> \<Longrightarrow> atom x \<sharp> p \<bullet> y"
  by (metis imageI Vs p fresh_finite_set_at_base fresh_star_def mem_permute_iff fresh_at_base(2))

lemma fresh_pj: "\<lbrakk>a \<sharp> p; j \<in> Vs\<rbrakk> \<Longrightarrow> a \<sharp> p \<bullet> j"
  by (metis atom_fresh_perm fresh_at_base(2) fresh_perm fresh_permute_left pinv)

lemma fresh_Vs: "a \<sharp> p \<Longrightarrow> a \<sharp> Vs"
  by (metis Vs fresh_def fresh_perm fresh_permute_iff fresh_star_def p permute_finite supp_finite_set_at_base)

lemma fresh_pVs: "a \<sharp> p \<Longrightarrow> a \<sharp> p \<bullet> Vs"
  by (metis fresh_Vs fresh_perm fresh_permute_left pinv)

lemma assumes "V \<subseteq> Vs" "a \<sharp> p"
      shows fresh_pV [simp]: "a \<sharp> p \<bullet> V" and fresh_V [simp]: "a \<sharp> V"
  using fresh_pVs fresh_Vs assms 
  apply (auto simp: fresh_def)
  apply (metis (full_types) Vs finite_V permute_finite subsetD subset_Un_eq supp_of_finite_union union_eqvt)
  by (metis Vs finite_V subsetD subset_Un_eq supp_of_finite_union)

lemma qp_insert:
  fixes i::name and i'::name
  assumes "atom i \<sharp> p" "atom i' \<sharp> (i,p)"
    shows  "quote_perm ((atom i \<rightleftharpoons> atom i') + p) (insert i Vs)"
using p pinv Vs assms
  by (auto simp: quote_perm_def fresh_at_base_permI atom_fresh_star_atom_set_conv swap_fresh_fresh 
                 fresh_star_finite_insert fresh_finite_insert perm_self_inverseI)

lemma subst_F_left_commute: "subst x (F x) (subst y (F y) t) = subst y (F y) (subst x (F x) t)"
  by (metis subst_tm_commute2 F_unfold subst_tm_id F_unfold atom_fresh_perm tm.fresh(2)) 

lemma 
  assumes "finite V" "i \<notin> V" 
  shows ssubst_insert:  "ssubst t (insert i V) F = subst i (F i) (ssubst t V F)"  (is ?thesis1)
    and ssubst_insert2: "ssubst t (insert i V) F = ssubst (subst i (F i) t) V F"  (is ?thesis2)
proof -
  interpret comp_fun_commute "(\<lambda>i. subst i (F i))"
  proof qed (simp add: subst_F_left_commute fun_eq_iff)
  show ?thesis1 using assms Vs
    by (simp add: ssubst_def)
  show ?thesis2 using assms Vs
    by (simp add: ssubst_def fold_insert2 del: fold_insert)
qed

lemma ssubst_insert_if:
  "finite V \<Longrightarrow> 
     ssubst t (insert i V) F = (if i \<in> V then ssubst t V F 
                                         else subst i (F i) (ssubst t V F))"
  by (simp add: ssubst_insert insert_absorb)

lemma ssubst_single [simp]: "ssubst t {i} F = subst i (F i) t"
  by (simp add: ssubst_insert)

lemma ssubst_Var_if [simp]:
  assumes "finite V"  
    shows "ssubst (Var i) V F = (if i \<in> V then F i else Var i)"
using assms
  apply (induction V, auto)
  apply (metis ssubst_insert subst.simps(2))
  apply (metis ssubst_insert2 subst.simps(2))+
  done

lemma ssubst_Zero [simp]: "finite V \<Longrightarrow> ssubst Zero V F = Zero"
  by (induct V rule: finite_induct) (auto simp: ssubst_insert)

lemma ssubst_Eats [simp]: "finite V \<Longrightarrow> ssubst (Eats t u) V F = Eats (ssubst t V F) (ssubst u V F)"
  by (induct V rule: finite_induct) (auto simp: ssubst_insert)

lemma ssubst_SUCC [simp]: "finite V \<Longrightarrow> ssubst (SUCC t) V F = SUCC (ssubst t V F)"
  by (metis SUCC_def ssubst_Eats)

lemma ssubst_ORD_OF [simp]: "finite V \<Longrightarrow> ssubst (ORD_OF n) V F = ORD_OF n"
  by (induction n) auto

lemma ssubst_HPair [simp]: 
  "finite V \<Longrightarrow> ssubst (HPair t u) V F = HPair (ssubst t V F) (ssubst u V F)"
  by (simp add: HPair_def)

lemma ssubst_HTuple [simp]: "finite V \<Longrightarrow> ssubst (HTuple n) V F = (HTuple n)"
  by (induction n) (auto simp: HTuple.simps)

lemma ssubst_Subset:
  assumes "finite V" shows "ssubst \<lfloor>t SUBS u\<rfloor>V V F = Q_Subset (ssubst \<lfloor>t\<rfloor>V V F) (ssubst \<lfloor>u\<rfloor>V V F)"
proof -
  obtain i::name where "atom i \<sharp> (t,u)"
    by (rule obtain_fresh)
  thus ?thesis using assms
    by (auto simp: Subset.simps [of i] vquot_fm_def vquot_tm_def trans_tm_forget)
qed

lemma fresh_ssubst: 
  assumes "finite V" "a \<sharp> p \<bullet> V" "a \<sharp> t"
    shows "a \<sharp> ssubst t V F"
using assms
  by (induct V) 
     (auto simp: ssubst_insert_if fresh_finite_insert F_unfold intro: fresh_ineq_at_base)

lemma fresh_ssubst': 
  assumes "finite V" "atom i \<sharp> t" "atom (p \<bullet> i) \<sharp> t"
    shows "atom i \<sharp> ssubst t V F"
using assms 
  by (induct t rule: tm.induct) (auto simp: F_unfold fresh_permute_left pinv)

lemma ssubst_vquot_Ex:
  "\<lbrakk>finite V; atom i \<sharp> p \<bullet> V\<rbrakk> 
   \<Longrightarrow> ssubst \<lfloor>Ex i A\<rfloor>(insert i V) (insert i V) F = ssubst \<lfloor>Ex i A\<rfloor>V V F"
   by (simp add: ssubst_insert_if insert_absorb vquot_fm_insert fresh_ssubst)

lemma ground_ssubst_eq: "\<lbrakk>finite V; supp t = {}\<rbrakk> \<Longrightarrow> ssubst t V F = t"
  by (induct V rule: finite_induct) (auto simp: ssubst_insert fresh_def)

lemma ssubst_quot_tm [simp]:
  fixes t::tm shows "finite V \<Longrightarrow> ssubst \<guillemotleft>t\<guillemotright> V F = \<guillemotleft>t\<guillemotright>"
  by (simp add: ground_ssubst_eq supp_conv_fresh)

lemma ssubst_quot_fm [simp]:
  fixes A::fm shows "finite V \<Longrightarrow> ssubst \<guillemotleft>A\<guillemotright> V F = \<guillemotleft>A\<guillemotright>"
  by (simp add: ground_ssubst_eq supp_conv_fresh)

lemma atom_in_p_Vs: "\<lbrakk>i \<in> p \<bullet> V; V \<subseteq> Vs\<rbrakk> \<Longrightarrow> i \<in> p \<bullet> Vs"
  by (metis (full_types) True_eqvt subsetD subset_eqvt)


section\<open>The Main Theorems of Section 7\<close>

lemma SubstTermP_vquot_dbtm:
  assumes w: "w \<in> Vs - V" and V: "V \<subseteq> Vs" "V' = p \<bullet> V"
      and s: "supp dbtm \<subseteq> atom ` Vs"
  shows
  "insert (ConstP (F w)) {ConstP (F i) | i. i \<in> V}
   \<turnstile> SubstTermP \<guillemotleft>Var w\<guillemotright> (F w) 
                (ssubst (vquot_dbtm V dbtm) V F)
                (subst w (F w) (ssubst (vquot_dbtm (insert w V) dbtm) V F))"
using s
proof (induct dbtm rule: dbtm.induct)
  case DBZero thus ?case using V w
    by (auto intro: SubstTermP_Zero [THEN cut1] ConstP_imp_TermP [THEN cut1])
next
  case (DBInd n) thus ?case using V
    apply auto
    apply (rule thin [of "{ConstP (F w)}"])
    apply (rule SubstTermP_Ind [THEN cut3])
    apply (auto simp: IndP_Q_Ind OrdP_ORD_OF ConstP_imp_TermP)
    done
next
  case (DBVar i) show ?case
  proof (cases "i \<in> V'")
    case True hence "i \<notin> Vs" using assms 
      by (metis p Vs atom_in_atom_image atom_in_p_Vs fresh_finite_set_at_base fresh_star_def)
    thus ?thesis using DBVar True V
      by auto
  next
    case False thus ?thesis using DBVar V w
      apply (auto simp: quot_Var [symmetric])
        apply (blast intro: thin [of "{ConstP (F w)}"] ConstP_imp_TermP
                            SubstTermP_Var_same [THEN cut2])
       apply (subst forget_subst_tm, metis F_unfold atom_fresh_perm tm.fresh(2))
       apply (blast intro: Hyp thin [of "{ConstP (F w)}"] ConstP_imp_TermP
                           SubstTermP_Const [THEN cut2])
       apply (blast intro: Hyp thin [of "{ConstP (F w)}"] ConstP_imp_TermP EQ_quot_tm_Fls
                           SubstTermP_Var_diff [THEN cut4])
      done
  qed
next
  case (DBEats tm1 tm2) thus ?case using V
    by (auto simp: SubstTermP_Eats [THEN cut2])
qed

lemma SubstFormP_vquot_dbfm:
  assumes w: "w \<in> Vs - V" and V: "V \<subseteq> Vs" "V' = p \<bullet> V"
      and s: "supp dbfm \<subseteq> atom ` Vs"
  shows
  "insert (ConstP (F w)) {ConstP (F i) | i. i \<in> V}
   \<turnstile> SubstFormP \<guillemotleft>Var w\<guillemotright> (F w)
                (ssubst (vquot_dbfm V dbfm) V F) 
                (subst w (F w) (ssubst (vquot_dbfm (insert w V) dbfm) V F))"
using w s
proof (induct dbfm rule: dbfm.induct)
  case (DBMem t u) thus ?case using V
    by (auto intro: SubstTermP_vquot_dbtm SubstFormP_Mem [THEN cut2])
next
  case (DBEq t u) thus ?case using V
    by (auto intro: SubstTermP_vquot_dbtm SubstFormP_Eq [THEN cut2])
next
  case (DBDisj A B) thus ?case using V
    by (auto intro: SubstFormP_Disj [THEN cut2])
next
  case (DBNeg A) thus ?case using V
    by (auto intro: SubstFormP_Neg [THEN cut1])
next
  case (DBEx A) thus ?case using V
    by (auto intro: SubstFormP_Ex [THEN cut1])
qed

text\<open>Lemmas 7.5 and 7.6\<close>
lemma ssubst_SubstFormP:
  fixes A::fm
  assumes w: "w \<in> Vs - V" and V: "V \<subseteq> Vs" "V' = p \<bullet> V"
      and s: "supp A \<subseteq> atom ` Vs"
  shows
  "insert (ConstP (F w)) {ConstP (F i) | i. i \<in> V}
   \<turnstile> SubstFormP \<guillemotleft>Var w\<guillemotright> (F w) 
                (ssubst \<lfloor>A\<rfloor>V V F) 
                (ssubst \<lfloor>A\<rfloor>(insert w V) (insert w V) F)"
proof -
  have "w \<notin> V" using assms
    by auto
  thus ?thesis using assms
    by (simp add: vquot_fm_def supp_conv_fresh ssubst_insert_if SubstFormP_vquot_dbfm)
qed

text\<open>Theorem 7.3\<close>
theorem PfP_implies_PfP_ssubst:
  fixes \<beta>::fm
  assumes \<beta>: "{} \<turnstile> PfP \<guillemotleft>\<beta>\<guillemotright>"
      and V: "V \<subseteq> Vs"
      and s: "supp \<beta> \<subseteq> atom ` Vs"
    shows    "{ConstP (F i) | i. i \<in> V} \<turnstile> PfP (ssubst \<lfloor>\<beta>\<rfloor>V V F)"
proof -
  show ?thesis using finite_V [OF V] V 
  proof induction
    case empty thus ?case
      by (auto simp: \<beta>)
  next
    case (insert i V)
    thus ?case using assms
      by (auto simp: Collect_disj_Un fresh_finite_set_at_base 
               intro: PfP_implies_SubstForm_PfP thin1 ssubst_SubstFormP)
  qed
qed

end

end

