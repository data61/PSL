(**        Valuation1
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            h_coba@math.cst.nihon-u.ac.jp
                            June 24, 2005(revised)
                            July 20, 2007(revised)

   chapter 1. elementary properties of a valuation
    section 1. definition of a valuation
    section 2. the normal valuation of v
    section 3. valuation ring
    section 4. ideals in a valuation ring
    section 5. pow of vp and n_value -- convergence --
    section 6. equivalent valuations
    section 7. prime divisors
    section 8. approximation

   **)


theory Valuation1
imports  "Group-Ring-Module.Algebra9"
begin

declare ex_image_cong_iff [simp del]

chapter "Preliminaries"

section "Int and ant (augmented integers)"

lemma int_less_mono:"(a::nat) < b \<Longrightarrow> int a < int b"
apply simp
done

lemma zless_trans:"\<lbrakk>(i::int) < j; j < k\<rbrakk> \<Longrightarrow> i < k"
apply simp
done

lemma zmult_pos_bignumTr0:"\<exists>L. \<forall>m. L < m \<longrightarrow> z < x + int m"
by (subgoal_tac "\<forall>m. (nat((abs z) + (abs x))) < m \<longrightarrow> z < x + int m",
       blast, rule allI, rule impI, arith)

lemma zle_less_trans:"\<lbrakk>(i::int) \<le> j; j < k\<rbrakk> \<Longrightarrow> i < k"
apply (simp add:less_le)
done

lemma  zless_le_trans:"\<lbrakk>(i::int) < j; j \<le> k\<rbrakk> \<Longrightarrow> i < k"
apply (simp add:less_le)
done

lemma zmult_pos_bignumTr:"0 < (a::int) \<Longrightarrow>
                   \<exists>l. \<forall>m. l < m \<longrightarrow> z < x + (int m) * a"
apply (cut_tac zmult_pos_bignumTr0[of "z" "x"])
 apply (erule exE)
 apply (subgoal_tac "\<forall>m. L < m \<longrightarrow> z < x + int m * a", blast)
apply (rule allI, rule impI)
 apply (drule_tac a = m in forall_spec, assumption)
 apply (subgoal_tac "0 \<le> int m")
 apply (frule_tac a = "int m" and b = a in pos_zmult_pos, assumption)
 apply (cut_tac order_refl[of "x"])
 apply (frule_tac z' = "int m" and z = "int m * a" in
         zadd_zle_mono[of "x" "x"], assumption+)
 apply (rule_tac y = "x + int m" and z = "x + (int m)* a" in
         less_le_trans[of "z"], assumption+)
 apply simp
done

lemma  ale_shift:"\<lbrakk>(x::ant)\<le> y; y = z\<rbrakk> \<Longrightarrow> x \<le> z"
by simp

lemma aneg_na_0[simp]:"a < 0 \<Longrightarrow> na a = 0"
by (simp add:na_def)

lemma amult_an_an:"an (m * n) = (an m) * (an n)"
apply (simp add:an_def)
apply (simp add: of_nat_mult a_z_z)
done

definition
  adiv :: "[ant, ant] \<Rightarrow> ant" (infixl "adiv" 200) where
  "x adiv y = ant ((tna x) div (tna y))"

definition
  amod :: "[ant, ant] \<Rightarrow> ant" (infixl "amod" 200) where
  "x amod y = ant ((tna x) mod (tna y))"

lemma apos_amod_conj:"0 < ant b \<Longrightarrow>
                  0 \<le> (ant a) amod (ant b) \<and> (ant a) amod (ant b) < (ant b)"
by (simp add:amod_def tna_ant, simp only:ant_0[THEN sym],
       simp add:aless_zless)

lemma  amod_adiv_equality:
       "(ant a) = (a div b) *\<^sub>a (ant b) + ant (a mod b)"
apply (simp add:adiv_def tna_ant a_z_z a_zpz  asprod_mult)
done

lemma asp_z_Z:"z *\<^sub>a ant x \<in> Z\<^sub>\<infinity>"
by (simp add:asprod_mult z_in_aug_inf)

lemma apos_in_aug_inf:"0 \<le> a \<Longrightarrow> a \<in> Z\<^sub>\<infinity>"
by (simp add:aug_inf_def, rule contrapos_pp, simp+,
    cut_tac minf_le_any[of "0"], frule ale_antisym[of "0" "-\<infinity>"],
    assumption+, simp)

lemma  amult_1_both:"\<lbrakk>0 < (w::ant); x * w = 1\<rbrakk> \<Longrightarrow> x = 1 \<and> w = 1"
apply (cut_tac mem_ant[of "x"], cut_tac mem_ant[of "w"],
      (erule disjE)+, simp,
      (frule sym, thin_tac "\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1))
apply (erule disjE, erule exE, simp,
       (frule sym, thin_tac "-\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1), simp)
apply (frule sym, thin_tac "-\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1)
apply ((erule disjE)+, erule exE, simp,
       frule_tac aless_imp_le[of "0" "-\<infinity>"],
       cut_tac minf_le_any[of "0"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+,
       simp only:ant_0[THEN sym], simp,
       frule sym, thin_tac "-\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1)
apply ((erule disjE)+, (erule exE)+, simp only:ant_1[THEN sym],
       simp del:ant_1 add:a_z_z,
       (cut_tac a = z and b = za in mult.commute, simp,
        cut_tac z = za and z' = z in  times_1_both, assumption+),
       simp)
apply (erule exE, simp,
       cut_tac x = z and y = 0 in less_linear, erule disjE, simp,
       frule sym, thin_tac "-\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1,
       erule disjE, simp add:ant_0, simp,
       frule sym, thin_tac "\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1,
       erule disjE, erule exE, simp,
       frule sym, thin_tac "\<infinity> = 1", simp only:ant_1[THEN sym],
       simp del:ant_1, simp)
done

lemma poss_int_neq_0:"0 < (z::int) \<Longrightarrow> z \<noteq> 0"
by simp

lemma aadd_neg_negg[simp]:"\<lbrakk>a \<le> (0::ant); b < 0\<rbrakk> \<Longrightarrow> a + b < 0"
apply (frule ale_minus[of "a" "0"], simp,
       frule aless_minus[of "b" "0"], simp)
apply (frule aadd_pos_poss[of "-a" "-b"], assumption+,
       simp add:aminus_add_distrib[THEN sym, of "a" "b"],
       frule aless_minus[of "0" "-(a + b)"], simp add:a_minus_minus)
done

lemma aadd_two_negg[simp]:"\<lbrakk>a < (0::ant); b < 0\<rbrakk> \<Longrightarrow> a + b < 0"
by auto

lemma amin_aminTr:"(z::ant) \<le> z' \<Longrightarrow> amin z w \<le> amin z' w"
by (simp add:amin_def, simp add:aneg_le,
      (rule impI)+, frule aless_le_trans[of "w" "z" "z'"],
      assumption+, simp)

lemma amin_le1:"(z::ant) \<le> z' \<Longrightarrow> (amin z w) \<le> z'"
by (simp add:amin_def, simp add:aneg_le,
       rule impI, frule aless_le_trans[of "w" "z" "z'"],
       assumption+, simp add:aless_imp_le)

lemma amin_le2:"(z::ant) \<le> z' \<Longrightarrow> (amin w z) \<le> z'"
by (simp add:amin_def, rule impI,
       frule ale_trans[of "w" "z" "z'"], assumption+)

lemma  Amin_geTr:"(\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>j \<le> n. z \<le> (f j)) \<longrightarrow>
                                 z \<le> (Amin n f)"
apply (induct_tac n)
 apply (rule impI, erule conjE, simp)
apply (rule impI, (erule conjE)+,
       cut_tac Nsetn_sub_mem1[of n], simp,
       drule_tac x = "Suc n" in spec, simp,
       rule_tac z = z and x = "Amin n f" and y = "f(Suc n)" in amin_ge1,
       simp+)
done

lemma Amin_ge:"\<lbrakk>\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>; \<forall>j \<le> n. z \<le> (f j)\<rbrakk> \<Longrightarrow>
                             z \<le> (Amin n f)"
by (simp add:Amin_geTr)

definition
  Abs :: "ant \<Rightarrow> ant" where
  "Abs z = (if z < 0 then -z else z)"

lemma Abs_pos:"0 \<le> Abs z"
by (simp add:Abs_def, rule conjI, rule impI,
       cut_tac aless_minus[of "z" "0"], simp,
       assumption,
       rule impI, simp add:aneg_less[of "z" "0"])

lemma Abs_x_plus_x_pos:"0 \<le> (Abs x) + x"
apply (case_tac "x < 0",
       simp add:Abs_def, simp add:aadd_minus_inv)

apply (simp add:aneg_less,
       simp add:Abs_def, simp add:aneg_less[THEN sym, of "0" "x"],
       simp add:aneg_less[of "x" "0"], simp add:aadd_two_pos)
done

lemma  Abs_ge_self:"x \<le> Abs x"
apply (simp add:Abs_def, rule impI,
       cut_tac ale_minus[of "x" "0"],
       simp add:aminus_0, simp add:aless_imp_le)
done

lemma  na_1:"na 1 = Suc 0"
apply (simp only:ant_1[THEN sym], simp only:na_def,
       simp only:ant_0[THEN sym], simp only:aless_zless[of "1" "0"],
       simp, subgoal_tac "\<infinity> \<noteq> 1", simp)
apply (simp only:ant_1[THEN sym], simp only:tna_ant,
       rule not_sym, simp only:ant_1[THEN sym], simp del:ant_1)
done

lemma ant_int:"ant (int n) = an n"
by (simp add:an_def)

lemma int_nat:"0 < z \<Longrightarrow> int (nat z) = z"
by arith

lemma int_ex_nat:"0 < z \<Longrightarrow> \<exists>n. int n = z"
by (cut_tac int_nat[of z], blast, assumption)

lemma eq_nat_pos_ints:
  "\<lbrakk>nat (z::int) = nat (z'::int); 0 \<le> z; 0 \<le> z'\<rbrakk> \<Longrightarrow> z = z'"
by simp

lemma a_p1_gt[simp]:"\<lbrakk>a \<noteq> \<infinity>; a \<noteq> -\<infinity>\<rbrakk>  \<Longrightarrow> a < a + 1"
apply (cut_tac aadd_poss_less[of a 1],
       simp add:aadd_commute, assumption+)
apply (cut_tac zposs_aposss[of 1], simp)
done

lemma  gt_na_poss:"(na a) < m \<Longrightarrow> 0 < m"
apply (simp add:na_def)
done

lemma azmult_less:"\<lbrakk>a \<noteq> \<infinity>; na a < m; 0 < x\<rbrakk>
                         \<Longrightarrow> a < int m *\<^sub>a x"
apply (cut_tac mem_ant[of "a"])
 apply (erule disjE)
 apply (case_tac "x = \<infinity>") apply simp
 apply (subst less_le[of "-\<infinity>" "\<infinity>"]) apply simp
 apply (frule aless_imp_le[of "0" "x"], frule apos_neq_minf[of "x"])
 apply (cut_tac mem_ant[of "x"], simp, erule exE, simp)
 apply (simp add:asprod_amult a_z_z)
apply (simp, erule exE, simp)

apply (frule_tac a = "ant z" in gt_na_poss[of _ "m"])
 apply (case_tac "x = \<infinity>", simp)
 apply (frule aless_imp_le[of "0" "x"])
 apply (frule apos_neq_minf[of "x"])
 apply (cut_tac mem_ant[of "x"], simp, erule exE,
        simp add:asprod_amult a_z_z)
 apply (subst aless_zless)
 apply (cut_tac a = "ant z" in gt_na_poss[of _ "m"], assumption)
 apply (smt a0_less_int_conv aposs_na_poss int_less_mono int_nat na_def of_nat_0_le_iff pos_zmult_pos tna_ant z_neq_inf)
 done

lemma  zmult_gt_one:"\<lbrakk>2 \<le> m; 0 < xa\<rbrakk> \<Longrightarrow> 1 < int m * xa"
by (metis ge2_zmult_pos mult.commute)

lemma zmult_pos:"\<lbrakk> 0 < m; 0 < (a::int)\<rbrakk> \<Longrightarrow> 0 < (int m) * a"
by (frule zmult_zless_mono2[of "0" "a" "int m"], simp, simp)

lemma  ant_int_na:"\<lbrakk>0 \<le> a; a \<noteq> \<infinity> \<rbrakk> \<Longrightarrow> ant (int (na a)) = a"
by (frule an_na[of "a"], assumption, simp add:an_def)

lemma zpos_nat:"0 \<le> (z::int) \<Longrightarrow> \<exists>n. z = int n"
apply (subgoal_tac "z = int (nat z)")
apply blast apply simp
done

section "nsets"

lemma nsetTr1:"\<lbrakk>j \<in> nset a b; j \<noteq> a\<rbrakk> \<Longrightarrow> j \<in> nset (Suc a) b"
apply (simp add:nset_def)
done

lemma nsetTr2:"j \<in> nset (Suc a) (Suc b) \<Longrightarrow> j - Suc 0 \<in> nset a b"
apply (simp add:nset_def, erule conjE,
       simp add:skip_im_Tr4[of "j" "b"])
done

lemma  nsetTr3:"\<lbrakk>j \<noteq> Suc (Suc 0); j - Suc 0 \<in> nset (Suc 0) (Suc n)\<rbrakk>
       \<Longrightarrow>  Suc 0 < j - Suc 0"
apply (simp add:nset_def, erule conjE, subgoal_tac "j \<noteq> 0",
       rule contrapos_pp, simp+)
done

lemma Suc_leD1:"Suc m \<le> n \<Longrightarrow> m < n"
apply (insert lessI[of "m"],
       rule less_le_trans[of "m" "Suc m" "n"], assumption+)
done

lemma leI1:"n < m \<Longrightarrow> \<not> ((m::nat) \<le> n)"
apply (rule contrapos_pp, simp+)
done

lemma neg_zle:"\<not> (z::int) \<le> z' \<Longrightarrow> z' < z"
apply (simp add: not_le)
done

lemma nset_m_m:"nset m m = {m}"
by (simp add:nset_def,
       rule equalityI, rule subsetI, simp,
       rule subsetI, simp)

lemma nset_Tr51:"\<lbrakk>j \<in> nset (Suc 0) (Suc (Suc n)); j \<noteq> Suc 0\<rbrakk>
       \<Longrightarrow> j - Suc 0 \<in> nset (Suc 0) (Suc n)"
apply (simp add:nset_def, (erule conjE)+,
       frule_tac m = j and n = "Suc (Suc n)" and l = "Suc 0" in diff_le_mono,
       simp)
done

lemma nset_Tr52:"\<lbrakk>j \<noteq> Suc (Suc 0); Suc 0 \<le> j - Suc 0\<rbrakk>
       \<Longrightarrow> \<not> j - Suc 0 \<le> Suc 0"
by auto

lemma nset_Suc:"nset (Suc 0) (Suc (Suc n)) =
                  nset (Suc 0) (Suc n) \<union> {Suc (Suc n)}"
by (auto simp add:nset_def)

lemma AinequalityTr0:"x \<noteq> -\<infinity> \<Longrightarrow> \<exists>L. (\<forall>N. L < N \<longrightarrow>
                          (an m) < (x + an N))"
apply (case_tac "x = \<infinity>", simp add:an_def)
apply (cut_tac mem_ant[of "x"], simp, erule exE, simp add:an_def a_zpz,
       simp add:aless_zless,
       cut_tac x = z in zmult_pos_bignumTr0[of "int m"], simp)
done

lemma AinequalityTr:"\<lbrakk>0 < b \<and> b \<noteq> \<infinity>; x \<noteq> -\<infinity>\<rbrakk> \<Longrightarrow> \<exists>L. (\<forall>N. L < N \<longrightarrow>
                          (an m) < (x + (int N) *\<^sub>a b))"
apply (frule_tac AinequalityTr0[of "x" "m"],
       erule exE,
       subgoal_tac "\<forall>N. L < N \<longrightarrow> an m < x + (int N) *\<^sub>a b",
       blast, rule allI, rule impI)
apply (drule_tac a = N in forall_spec, assumption,
       erule conjE,
       cut_tac N = N in asprod_ge[of "b"], assumption,
       thin_tac "x \<noteq> - \<infinity>", thin_tac "b \<noteq> \<infinity>", thin_tac "an m < x + an N",
        simp)
 apply (frule_tac x = "an N" and y = "int N *\<^sub>a b" and z = x in aadd_le_mono,
        simp only:aadd_commute[of _ "x"])
done

lemma two_inequalities:"\<lbrakk>\<forall>(n::nat). x < n \<longrightarrow> P n; \<forall>(n::nat). y < n \<longrightarrow> Q n\<rbrakk>
 \<Longrightarrow>  \<forall>n. (max x y) < n \<longrightarrow> (P n) \<and> (Q n)"
by auto

lemma multi_inequalityTr0:"(\<forall>j \<le> (n::nat). (x j) \<noteq> -\<infinity> ) \<longrightarrow>
      (\<exists>L. (\<forall>N. L < N \<longrightarrow>  (\<forall>l \<le> n. (an m) < (x l) + (an N))))"
apply (induct_tac n)
 apply (rule impI, simp)
 apply (rule AinequalityTr0[of "x 0" "m"], assumption)
(** n **)
apply (rule impI)
 apply (subgoal_tac "\<forall>l. l \<le> n \<longrightarrow> l \<le> (Suc n)", simp)
 apply (erule exE)
 apply (frule_tac a = "Suc n" in forall_spec, simp)

 apply (frule_tac x = "x (Suc n)" in AinequalityTr0[of _ "m"])
 apply (erule exE)
 apply (subgoal_tac "\<forall>N. (max L La) < N \<longrightarrow>
                 (\<forall>l \<le> (Suc n). an m < x l + an N)", blast)
 apply (rule allI, rule impI, rule allI, rule impI)
 apply (rotate_tac 1)
 apply (case_tac "l = Suc n", simp,
        drule_tac m = l and n = "Suc n" in noteq_le_less, assumption+,
        drule_tac x = l and n = "Suc n" in less_le_diff, simp,
        simp)
done

lemma multi_inequalityTr1:"\<lbrakk>\<forall>j \<le> (n::nat). (x j) \<noteq> - \<infinity>\<rbrakk> \<Longrightarrow>
       \<exists>L. (\<forall>N. L < N \<longrightarrow>  (\<forall>l \<le> n. (an m) < (x l) + (an N)))"
by (simp add:multi_inequalityTr0)

lemma gcoeff_multi_inequality:"\<lbrakk>\<forall>N. 0 < N \<longrightarrow> (\<forall>j \<le> (n::nat). (x j) \<noteq> -\<infinity> \<and>
     0 < (b N j) \<and> (b N j) \<noteq> \<infinity>)\<rbrakk> \<Longrightarrow>
\<exists>L. (\<forall>N. L < N \<longrightarrow>  (\<forall>l \<le> n.(an m) < (x l) + (int N) *\<^sub>a (b N l)))"
apply (subgoal_tac "\<forall>j \<le> n. x j \<noteq> - \<infinity>")
apply (frule  multi_inequalityTr1[of "n" "x" "m"])
apply (erule exE)
apply (subgoal_tac "\<forall>N. L < N \<longrightarrow>
                     (\<forall>l \<le> n. an m < x l + (int N) *\<^sub>a (b N l))")
apply blast

apply (rule allI, rule impI, rule allI, rule impI,
       drule_tac a = N in forall_spec, simp,
       drule_tac a = l in forall_spec, assumption,
       drule_tac a = N in forall_spec, assumption,
       drule_tac a = l in forall_spec, assumption,
       drule_tac a = l in forall_spec, assumption)
 apply (cut_tac b = "b N l" and N = N in asprod_ge, simp, simp,
        (erule conjE)+, simp, thin_tac "x l \<noteq> - \<infinity>", thin_tac "b N l \<noteq> \<infinity>")
apply (frule_tac x = "an N" and y = "int N *\<^sub>a b N l" and z = "x l" in
       aadd_le_mono, simp add:aadd_commute,
       rule allI, rule impI,
       cut_tac lessI[of "(0::nat)"],
       drule_tac a = "Suc 0" in forall_spec, assumption)
 apply simp
done

primrec m_max :: "[nat, nat \<Rightarrow> nat] \<Rightarrow> nat"
where
  m_max_0: "m_max 0 f = f 0"
| m_max_Suc: "m_max (Suc n) f  = max (m_max n f) (f (Suc n))"

   (** maximum value of f **)

lemma m_maxTr:"\<forall>l \<le> n. (f l) \<le> m_max n f"
apply (induct_tac n)
 apply simp

apply (rule allI, rule impI)
 apply simp
 apply (case_tac "l = Suc n", simp)
 apply (cut_tac m = l and n = "Suc n" in noteq_le_less, assumption+,
        thin_tac "l \<le> Suc n", thin_tac "l \<noteq> Suc n",
        frule_tac x = l and n = "Suc n" in less_le_diff,
        thin_tac "l < Suc n", simp)
 apply (drule_tac a = l in forall_spec, assumption)
 apply simp
done

lemma m_max_gt:"l \<le> n \<Longrightarrow> (f l) \<le> m_max n f"
apply (simp add:m_maxTr)
done

lemma ASum_zero:" (\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>l \<le> n. f l = 0) \<longrightarrow> ASum f n = 0"
apply (induct_tac n)
apply (rule impI, erule conjE, simp)
apply (rule impI)
apply (subgoal_tac "(\<forall>j\<le>n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>l\<le>n. f l = 0)", simp)
 apply (simp add:aadd_0_l, erule conjE,
        thin_tac "(\<forall>j\<le>n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>l\<le>n. f l = 0) \<longrightarrow> ASum f n = 0")
 apply (rule conjI)
 apply (rule allI, rule impI,
        drule_tac a = j in forall_spec, simp, assumption+)
 apply (thin_tac "\<forall>j\<le>Suc n. f j \<in> Z\<^sub>\<infinity>")
 apply (rule allI, rule impI,
        drule_tac a = l in forall_spec, simp+)
done

lemma eSum_singleTr:"(\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>) \<and> (j \<le> n \<and> (\<forall>l \<in>{h. h \<le> n} - {j}. f l = 0))  \<longrightarrow> ASum f n = f j"
apply (induct_tac n)
 apply (simp, rule impI, (erule conjE)+)
 apply (case_tac "j \<le> n")
 apply simp
 apply (simp add:aadd_0_r)
 apply simp
 apply (simp add:nat_not_le_less[of j])
 apply (frule_tac m = n and n = j in Suc_leI)
 apply (frule_tac m = j and n = "Suc n" in le_antisym, assumption+, simp)
 apply (cut_tac n = n in ASum_zero [of _ "f"])
 apply (subgoal_tac "(\<forall>j\<le>n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>l\<le>n. f l = 0)")
 apply (thin_tac "\<forall>j\<le>Suc n. f j \<in> Z\<^sub>\<infinity>",
        thin_tac "\<forall>l\<in>{h. h \<le> Suc n} - {Suc n}. f l = 0", simp only:mp)
 apply (simp add:aadd_0_l)

 apply (thin_tac "(\<forall>j\<le>n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>l\<le>n. f l = 0) \<longrightarrow> ASum f n = 0")
 apply (rule conjI,
        thin_tac "\<forall>l\<in>{h. h \<le> Suc n} - {Suc n}. f l = 0", simp)
 apply (thin_tac "\<forall>j\<le>Suc n. f j \<in> Z\<^sub>\<infinity>", simp)
done

lemma eSum_single:"\<lbrakk>\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity> ; j \<le> n; \<forall>l \<in> {h. h \<le> n} - {j}. f l = 0\<rbrakk>
 \<Longrightarrow> ASum  f n = f j"
apply (simp add:eSum_singleTr)
done

lemma ASum_eqTr:"(\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>) \<and> (\<forall>j \<le> n. g j \<in> Z\<^sub>\<infinity>) \<and>
                (\<forall>j \<le> n. f j = g j) \<longrightarrow> ASum f n = ASum g n"
apply (induct_tac n)
 apply (rule impI, simp)

apply (rule impI, (erule conjE)+)
apply simp
done

lemma ASum_eq:"\<lbrakk>\<forall>j \<le> n. f j \<in> Z\<^sub>\<infinity>; \<forall>j \<le> n. g j \<in> Z\<^sub>\<infinity>; \<forall>j \<le> n. f j = g j\<rbrakk> \<Longrightarrow>
               ASum f n = ASum g n"
by (cut_tac ASum_eqTr[of n f g], simp)


definition
  Kronecker_delta :: "[nat, nat] \<Rightarrow> ant"
    ("(\<delta>\<^bsub>_ _\<^esub>)" [70,71]70) where
  "\<delta>\<^bsub>i j\<^esub> = (if i = j then 1 else 0)"

definition
  K_gamma :: "[nat, nat] \<Rightarrow> int"
    ("(\<gamma>\<^bsub>_ _\<^esub>)" [70,71]70) where
  "\<gamma>\<^bsub>i j\<^esub> = (if i = j then 0 else 1)"

abbreviation
  TRANSPOS  ("(\<tau>\<^bsub>_ _\<^esub>)" [90,91]90) where
  "\<tau>\<^bsub>i j\<^esub> == transpos i j"

lemma Kdelta_in_Zinf:"\<lbrakk>j \<le> (Suc n); k \<le> (Suc n)\<rbrakk>  \<Longrightarrow>
                 z *\<^sub>a (\<delta>\<^bsub>j k\<^esub>) \<in> Z\<^sub>\<infinity>"
apply (simp add:Kronecker_delta_def)
apply (simp add:z_in_aug_inf Zero_in_aug_inf)
apply (simp add:asprod_n_0 Zero_in_aug_inf)
done

lemma Kdelta_in_Zinf1:"\<lbrakk>j \<le> n; k \<le> n\<rbrakk>  \<Longrightarrow> \<delta>\<^bsub>j k\<^esub> \<in> Z\<^sub>\<infinity>"
apply (simp add:Kronecker_delta_def)
apply (simp add:z_in_aug_inf Zero_in_aug_inf)
apply (rule impI)
apply (simp only:ant_1[THEN sym], simp del:ant_1 add:z_in_aug_inf)
done

primrec m_zmax :: "[nat, nat \<Rightarrow> int] \<Rightarrow> int"
where
  m_zmax_0: "m_zmax 0 f = f 0"
| m_zmax_Suc: "m_zmax (Suc n) f = zmax (m_zmax n f) (f (Suc n))"

lemma m_zmax_gt_eachTr:
      "(\<forall>j \<le> n. f j \<in> Zset) \<longrightarrow> (\<forall>j \<le> n. (f j) \<le> m_zmax n f)"
apply (induct_tac n)
apply (rule impI, rule allI, rule impI, simp)
 apply (rule impI)
 apply simp
 apply (rule allI, rule impI)
 apply (case_tac "j = Suc n", simp)
 apply (simp add:zmax_def)
 apply (drule_tac m = j and n = "Suc n" in noteq_le_less, assumption,
        drule_tac x = j and n = "Suc n" in less_le_diff, simp)
 apply (drule_tac a = j in forall_spec, assumption)
 apply (simp add:zmax_def)
done

lemma m_zmax_gt_each:"(\<forall>j \<le> n. f j \<in> Zset) \<Longrightarrow> (\<forall>j \<le> n. (f j) \<le> m_zmax n f)"
apply (simp add:m_zmax_gt_eachTr)
done

lemma n_notin_Nset_pred:" 0 < n \<Longrightarrow> \<not> n \<le> (n - Suc 0)"
apply simp
done

lemma Nset_preTr:"\<lbrakk>0 < n; j \<le> (n - Suc 0)\<rbrakk> \<Longrightarrow> j \<le> n"
apply simp
done

lemma Nset_preTr1:"\<lbrakk>0 < n; j \<le> (n - Suc 0)\<rbrakk> \<Longrightarrow> j \<noteq> n"
apply simp
done

lemma transpos_noteqTr:"\<lbrakk>0 < n; k \<le> (n - Suc 0); j \<le> n; j \<noteq> n\<rbrakk>
                    \<Longrightarrow> j \<noteq> (\<tau>\<^bsub>j n\<^esub>) k"
apply (rule contrapos_pp, simp+)
 apply (simp add:transpos_def)
 apply (case_tac "k = j", simp, simp)
 apply (case_tac "k = n", simp)
 apply (simp add:n_notin_Nset_pred)
done

chapter "Elementary properties of a valuation"


section "Definition of a valuation"

definition
  valuation :: "[('b, 'm) Ring_scheme, 'b \<Rightarrow> ant] \<Rightarrow> bool" where
  "valuation K v \<longleftrightarrow>
     v \<in> extensional (carrier K) \<and>
     v \<in> carrier K \<rightarrow> Z\<^sub>\<infinity>  \<and>
     v (\<zero>\<^bsub>K\<^esub>) = \<infinity> \<and> (\<forall>x\<in>((carrier K) - {\<zero>\<^bsub>K\<^esub>}). v x \<noteq> \<infinity>) \<and>
    (\<forall>x\<in>(carrier K). \<forall>y\<in>(carrier K). v (x \<cdot>\<^sub>r\<^bsub>K\<^esub> y) = (v x) + (v y)) \<and>
    (\<forall>x\<in>(carrier K). 0 \<le> (v x) \<longrightarrow> 0 \<le> (v (1\<^sub>r\<^bsub>K\<^esub> \<plusminus>\<^bsub>K\<^esub> x))) \<and>
    (\<exists>x. x \<in> carrier K \<and> (v x) \<noteq> \<infinity> \<and> (v x) \<noteq> 0)"

lemma (in Corps) invf_closed:"x \<in> carrier K - {\<zero>} \<Longrightarrow> x\<^bsup>\<hyphen> K\<^esup> \<in> carrier K"
by (cut_tac invf_closed1[of x], simp, assumption)

lemma (in Corps) valuation_map:"valuation K v \<Longrightarrow> v \<in> carrier K \<rightarrow> Z\<^sub>\<infinity>"
by (simp add:valuation_def)

lemma (in Corps) value_in_aug_inf:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
       v x \<in> Z\<^sub>\<infinity>"
by (simp add:valuation_def, (erule conjE)+, simp add:funcset_mem)

lemma (in Corps) value_of_zero:"valuation K v  \<Longrightarrow> v (\<zero>) = \<infinity>"
by (simp add:valuation_def)

lemma (in Corps) val_nonzero_noninf:"\<lbrakk>valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk>
     \<Longrightarrow> (v x) \<noteq> \<infinity>"
by (simp add:valuation_def)

lemma (in Corps) value_inf_zero:"\<lbrakk>valuation K v; x \<in> carrier K; v x = \<infinity>\<rbrakk>
     \<Longrightarrow> x = \<zero>"
by (rule contrapos_pp, simp+,
    frule val_nonzero_noninf[of v x], assumption+, simp)

lemma (in Corps) val_nonzero_z:"\<lbrakk>valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                      \<exists>z. (v x) = ant z"
by (frule value_in_aug_inf[of v x], assumption+,
    frule val_nonzero_noninf[of v x], assumption+,
    cut_tac mem_ant[of "v x"],  simp add:aug_inf_def)

lemma (in Corps) val_nonzero_z_unique:"\<lbrakk>valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk>
       \<Longrightarrow> \<exists>!z. (v x) = ant z"
by (rule ex_ex1I, simp add:val_nonzero_z, simp)

lemma (in Corps) value_noninf_nonzero:"\<lbrakk>valuation K v; x \<in> carrier K; v x \<noteq> \<infinity>\<rbrakk>
         \<Longrightarrow> x \<noteq> \<zero>"
by (rule contrapos_pp, simp+, simp add:value_of_zero)

lemma (in Corps) val1_neq_0:"\<lbrakk>valuation K v; x \<in> carrier K; v x = 1\<rbrakk> \<Longrightarrow>
                                         x \<noteq> \<zero>"
apply (rule contrapos_pp, simp+, simp add:value_of_zero)
apply (simp only:ant_1[THEN sym], cut_tac z_neq_inf[THEN not_sym, of 1], simp)
done

lemma (in Corps) val_Zmin_sym:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K\<rbrakk>
                 \<Longrightarrow>  amin (v x) (v y) = amin (v y ) (v x)"
by (simp add:amin_commute)

lemma (in Corps) val_t2p:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K\<rbrakk>
                         \<Longrightarrow> v (x \<cdot>\<^sub>r y ) = v x + v y"
by (simp add:valuation_def)

lemma (in Corps) val_axiom4:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> v x\<rbrakk> \<Longrightarrow>
                      0 \<le> v (1\<^sub>r \<plusminus> x)"
by (simp add:valuation_def)

lemma (in Corps) val_axiom5:"valuation K v \<Longrightarrow>
                  \<exists>x. x \<in> carrier K \<and> v x \<noteq> \<infinity> \<and> v x \<noteq> 0"
by (simp add:valuation_def)

lemma (in Corps) val_field_nonzero:"valuation K v \<Longrightarrow> carrier K \<noteq> {\<zero>}"
by (rule contrapos_pp, simp+,
       frule val_axiom5[of v],
       erule exE, (erule conjE)+, simp add:value_of_zero)

lemma (in Corps) val_field_1_neq_0:"valuation K v \<Longrightarrow> 1\<^sub>r \<noteq> \<zero>"
apply (rule contrapos_pp, simp+)
apply (frule val_axiom5[of v])
apply (erule exE, (erule conjE)+)
apply (cut_tac field_is_ring,
       frule_tac t = x in  Ring.ring_l_one[THEN sym, of "K"], assumption+,
       simp add:Ring.ring_times_0_x, simp add:value_of_zero)
done

lemma (in Corps) value_of_one:"valuation K v \<Longrightarrow> v (1\<^sub>r) = 0"
apply (cut_tac field_is_ring, frule Ring.ring_one[of "K"])
apply (frule val_t2p[of v "1\<^sub>r" "1\<^sub>r"], assumption+,
       simp add:Ring.ring_l_one, frule val_field_1_neq_0[of v],
       frule val_nonzero_z[of v "1\<^sub>r"], assumption+,
       erule exE, simp add:a_zpz)
done

lemma (in Corps) has_val_one_neq_zero:"valuation K v \<Longrightarrow> 1\<^sub>r \<noteq> \<zero>"
by (frule value_of_one[of "v"],
       rule contrapos_pp, simp+, simp add:value_of_zero)

lemma (in Corps) val_minus_one:"valuation K v \<Longrightarrow> v (-\<^sub>a 1\<^sub>r) = 0"
apply (cut_tac field_is_ring, frule Ring.ring_one[of "K"],
       frule Ring.ring_is_ag[of "K"],
       frule val_field_1_neq_0[of v],
       frule aGroup.ag_inv_inj[of "K" "1\<^sub>r" "\<zero>"], assumption+,
       simp add:Ring.ring_zero, assumption)
 apply (frule val_nonzero_z[of v "-\<^sub>a 1\<^sub>r"],
        rule aGroup.ag_mOp_closed, assumption+, simp add:aGroup.ag_inv_zero,
        erule exE, frule val_t2p [THEN sym, of v "-\<^sub>a 1\<^sub>r" "-\<^sub>a 1\<^sub>r"])
apply (simp add:aGroup.ag_mOp_closed[of "K" "1\<^sub>r"],
       simp add:aGroup.ag_mOp_closed[of "K" "1\<^sub>r"],
       frule Ring.ring_inv1_3[THEN sym, of "K" "1\<^sub>r" "1\<^sub>r"], assumption+,
       simp add:Ring.ring_l_one, simp add:value_of_one a_zpz)
done

lemma (in Corps) val_minus_eq:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                            v (-\<^sub>a x) = v x"
apply (cut_tac field_is_ring,
     simp add:Ring.ring_times_minusl[of K x],
     subst val_t2p[of v], assumption+,
     frule Ring.ring_is_ag[of "K"], rule aGroup.ag_mOp_closed, assumption+,
     simp add:Ring.ring_one, assumption, simp add:val_minus_one,
     simp add:aadd_0_l)
done

lemma (in Corps) value_of_inv:"\<lbrakk>valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                        v (x\<^bsup>\<hyphen>K\<^esup>) = - (v x)"
apply (cut_tac invf_inv[of x], erule conjE,
       frule val_t2p[of v "x\<^bsup>\<hyphen>K\<^esup>" x], assumption+,
       simp+, simp add:value_of_one, simp add:a_inv)
apply simp
done

lemma (in Corps) val_exp_ring:"\<lbrakk> valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk>
           \<Longrightarrow> (int n) *\<^sub>a (v x) = v (x^\<^bsup>K n\<^esup>)"
apply (cut_tac field_is_ring,
       induct_tac n, simp add:Ring.ring_r_one, simp add:value_of_one)
apply (drule sym, simp)
apply (subst val_t2p[of v _ x], assumption+,
       rule Ring.npClose, assumption+,
       frule val_nonzero_z[of v x], assumption+,
              erule exE, simp add:asprod_mult a_zpz,
       simp add: distrib_right)
done

text\<open>exponent in a field\<close>
lemma (in Corps) val_exp:"\<lbrakk> valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                        z *\<^sub>a (v x) = v (x\<^bsub>K\<^esub>\<^bsup>z\<^esup>)"
apply (simp add:npowf_def)
apply (case_tac "0 \<le> z",
       simp, frule val_exp_ring [of v x "nat z"], assumption+,
       simp, simp)
 apply (simp add:zle,
       cut_tac invf_closed1[of x], simp,
       cut_tac  val_exp_ring [THEN sym, of v "x\<^bsup>\<hyphen> K\<^esup>" "nat (- z)"], simp,
       thin_tac "v (x\<^bsup>\<hyphen> K\<^esup>^\<^bsup>K (nat (- z))\<^esup>) = (- z) *\<^sub>a v (x\<^bsup>\<hyphen> K\<^esup>)", erule conjE)
 apply (subst value_of_inv[of v x], assumption+)
 apply (frule val_nonzero_z[of v x], assumption+, erule exE, simp,
       simp add:asprod_mult aminus, simp+)
done

lemma (in Corps) value_zero_nonzero:"\<lbrakk>valuation K v; x \<in> carrier K; v x = 0\<rbrakk>
                   \<Longrightarrow> x \<noteq> \<zero>"
by (frule value_noninf_nonzero[of v x], assumption+, simp,
        assumption)

lemma (in Corps) v_ale_diff:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K;
        x \<noteq> \<zero>; v x \<le> v y \<rbrakk> \<Longrightarrow> 0 \<le> v(y \<cdot>\<^sub>r x\<^bsup>\<hyphen> K\<^esup>)"
apply (frule value_in_aug_inf[of v x], simp+,
       frule value_in_aug_inf[of v y], simp+,
       frule val_nonzero_z[of v x], assumption+,
       erule exE)
apply (cut_tac invf_closed[of x], simp+,
       simp add:val_t2p,
       simp add:value_of_inv[of v "x"],
       frule_tac x = "ant z" in ale_diff_pos[of _ "v y"],
       simp add:diff_ant_def)
apply simp
done

lemma (in Corps) amin_le_plusTr:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K;
       v x \<noteq> \<infinity>; v y \<noteq> \<infinity>; v x \<le> v y\<rbrakk> \<Longrightarrow> amin (v x) (v y) \<le> v ( x \<plusminus> y)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag,
       frule value_noninf_nonzero[of v x], assumption+,
       frule v_ale_diff[of v x y], assumption+,
       cut_tac invf_closed1[of x],
       frule Ring.ring_tOp_closed[of K y "x\<^bsup>\<hyphen> K\<^esup>"], assumption+, simp,
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "y \<cdot>\<^sub>r x\<^bsup>\<hyphen> K\<^esup>"], assumption+,
       frule val_axiom4[of v "y \<cdot>\<^sub>r ( x\<^bsup>\<hyphen> K\<^esup>)"], assumption+)
apply (frule aadd_le_mono[of "0" "v (1\<^sub>r \<plusminus> y \<cdot>\<^sub>r x\<^bsup>\<hyphen> K\<^esup>)" "v x"],
       simp add:aadd_0_l, simp add:aadd_commute[of _ "v x"],
       simp add:val_t2p[THEN sym, of v x],
       simp add:Ring.ring_distrib1 Ring.ring_r_one,
       simp add:Ring.ring_tOp_commute[of "K" "x"],
       simp add:Ring.ring_tOp_assoc, simp add:linvf,
       simp add:Ring.ring_r_one,
       cut_tac amin_le_l[of "v x" "v y"],
       rule ale_trans[of "amin (v x) (v y)" "v x" "v (x \<plusminus> y)"], assumption+)
apply simp
done

lemma (in Corps) amin_le_plus:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K\<rbrakk>
                   \<Longrightarrow> (amin (v x) (v y)) \<le> (v (x \<plusminus> y))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag)
apply (case_tac "v x = \<infinity> \<or> v y = \<infinity>")
apply (erule disjE, simp,
       frule value_inf_zero[of v x], assumption+,
       simp add:aGroup.ag_l_zero amin_def,
       frule value_inf_zero[of v y], assumption+,
       simp add:aGroup.ag_r_zero amin_def, simp, erule conjE)
apply (cut_tac z = "v x" and w = "v y" in ale_linear,
       erule disjE, simp add:amin_le_plusTr,
       frule_tac amin_le_plusTr[of v y x], assumption+,
       simp add:aGroup.ag_pOp_commute amin_commute)
done

lemma (in Corps) value_less_eq:"\<lbrakk> valuation K v; x \<in> carrier K; y \<in> carrier K;
                       (v x) < (v y)\<rbrakk> \<Longrightarrow> (v x) = (v (x \<plusminus> y))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule amin_le_plus[of v x y], assumption+,
       frule aless_imp_le[of "v x" "v y"],
       simp add: amin_def)
apply (frule amin_le_plus[of v "x \<plusminus> y" "-\<^sub>a y"],
       rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       simp add:val_minus_eq,
       frule aGroup.ag_mOp_closed[of "K" "y"], assumption+,
       simp add:aGroup.ag_pOp_assoc[of "K" "x" "y"],
       simp add:aGroup.ag_r_inv1, simp add:aGroup.ag_r_zero,
       simp add:amin_def)
 apply (case_tac "\<not> (v (x \<plusminus>\<^bsub>K\<^esub> y) \<le> (v y))", simp+)
done

lemma (in Corps) value_less_eq1:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K;
      (v x) < (v y)\<rbrakk> \<Longrightarrow> v x =  v (y \<plusminus> x)"
apply (cut_tac field_is_ring,
       frule Ring.ring_is_ag[of "K"],
       frule value_less_eq[of v x y], assumption+)
apply (subst aGroup.ag_pOp_commute, assumption+)
done

lemma (in Corps) val_1px:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> (v (1\<^sub>r \<plusminus> x))\<rbrakk>
         \<Longrightarrow> 0 \<le> (v x)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"])
apply (rule contrapos_pp, simp+,
       case_tac "x = \<zero>\<^bsub>K\<^esub>",
        simp add:aGroup.ag_r_zero, simp add:value_of_zero,
        simp add: aneg_le[of "0" "v x"],
        frule value_less_eq[of v x "1\<^sub>r"], assumption+,
        simp add:value_of_one)
apply (drule sym,
       simp add:aGroup.ag_pOp_commute[of "K" "x"])
done

lemma (in Corps) val_1mx:"\<lbrakk>valuation K v; x \<in> carrier K;
                  0 \<le> (v (1\<^sub>r \<plusminus> (-\<^sub>a x)))\<rbrakk> \<Longrightarrow> 0 \<le> (v x)"
by (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule val_1px[of v "-\<^sub>a x"],
       simp add:aGroup.ag_mOp_closed, assumption, simp add:val_minus_eq)

section "The normal valuation of v"

definition
  Lv :: "[('r, 'm) Ring_scheme , 'r \<Rightarrow> ant] \<Rightarrow> ant" (* Least nonnegative value *) where
  "Lv K v = AMin {x. x \<in> v ` carrier K \<and> 0 < x}"

definition
  n_val :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant] \<Rightarrow> ('r \<Rightarrow> ant)" where
  "n_val K v = (\<lambda>x\<in> carrier K.  (THE l. (l * (Lv K v)) = v x))"
                     (* normal valuation *)

definition
  Pg :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant] \<Rightarrow> 'r" (* Positive generator *) where
  "Pg K v = (SOME x. x \<in> carrier K - {\<zero>\<^bsub>K\<^esub>} \<and> v x = Lv K v)"

lemma (in Corps) vals_pos_nonempty:"valuation K v \<Longrightarrow>
                       {x. x \<in> v ` carrier K \<and> 0 < x} \<noteq> {}"
  using val_axiom5[of v] value_noninf_nonzero[of v] value_of_inv[THEN sym, of v]
  by (auto simp: ex_image_cong_iff) (metis Ring.ring_is_ag aGroup.ag_mOp_closed aGroup.ag_pOp_closed aGroup.ag_r_inv1 f_is_ring zero_lt_inf)

lemma (in Corps) vals_pos_LBset:"valuation K v \<Longrightarrow>
            {x. x \<in> v ` carrier K \<and> 0 < x} \<subseteq> LBset 1"
by (rule subsetI, simp add:LBset_def, erule conjE,
       rule_tac x = x in gt_a0_ge_1, assumption)

lemma (in Corps) Lv_pos:"valuation K v \<Longrightarrow> 0 < Lv K v"
apply (simp add:Lv_def,
       frule vals_pos_nonempty[of v],
       frule vals_pos_LBset[of v],
       simp only:ant_1[THEN sym],
       frule AMin[of "{x. x \<in> v ` carrier K \<and> 0 < x}" "1"], assumption+,
       erule conjE)
apply simp
done

lemma (in Corps) AMin_z:"valuation K v \<Longrightarrow>
         \<exists>a. AMin {x. x \<in> v ` carrier K \<and> 0 < x} = ant a"
apply (frule vals_pos_nonempty[of v],
       frule vals_pos_LBset[of v],
       simp only:ant_1[THEN sym],
       frule AMin[of "{x. x \<in> v ` carrier K \<and> 0 < x}" "1"], assumption+,
       erule conjE)
apply (frule val_axiom5[of v],
       erule exE, (erule conjE)+,
       cut_tac x = "v x" in aless_linear[of _ "0"], simp,
       erule disjE,
       frule_tac x = x in value_noninf_nonzero[of v], assumption+,
       frule_tac x1 = x in value_of_inv[THEN sym, of v], assumption+)
apply (frule_tac x = "v x" in aless_minus[of _ "0"], simp,
       cut_tac x = x in invf_closed1, simp, erule conjE,
       frule valuation_map[of v],
       frule_tac a = "x\<^bsup>\<hyphen> K\<^esup>" in mem_in_image[of "v" "carrier K" "Z\<^sub>\<infinity>"], simp)
apply (drule_tac a = "v (x\<^bsup>\<hyphen> K\<^esup>)" in forall_spec, simp,
       frule_tac x = "x\<^bsup>\<hyphen> K\<^esup>" in val_nonzero_noninf[of v],
       thin_tac "v (x\<^bsup>\<hyphen> K\<^esup>) \<in> v ` carrier K",
       thin_tac "{x \<in> v ` carrier K. 0 < x} \<subseteq> LBset 1",
       thin_tac "AMin {x \<in> v ` carrier K. 0 < x} \<in> v ` carrier K",
       thin_tac "0 < AMin {x \<in> v ` carrier K. 0 < x}", simp,
       thin_tac "v (x\<^bsup>\<hyphen> K\<^esup>) \<in> v ` carrier K",
       thin_tac "{x \<in> v ` carrier K. 0 < x} \<subseteq> LBset 1",
       thin_tac "AMin {x \<in> v ` carrier K. 0 < x} \<in> v ` carrier K",
       thin_tac "0 < AMin {x \<in> v ` carrier K. 0 < x}", simp)
apply (rule noninf_mem_Z[of "AMin {x \<in> v ` carrier K. 0 < x}"],
       frule image_sub[of v "carrier K" "Z\<^sub>\<infinity>" "carrier K"],
       rule subset_refl)
apply (rule subsetD[of "v ` carrier K" "Z\<^sub>\<infinity>"
                    "AMin {x \<in> v ` carrier K. 0 < x}"], assumption+)
  apply auto
  by (metis (no_types, lifting) aneg_le aug_inf_noninf_is_z image_eqI value_in_aug_inf z_less_i)

lemma (in Corps) Lv_z:"valuation K v \<Longrightarrow> \<exists>z. Lv K v = ant z"
by (simp add:Lv_def, rule AMin_z, assumption+)

lemma (in Corps) AMin_k:"valuation K v \<Longrightarrow>
         \<exists>k\<in> carrier K - {\<zero>}. AMin {x. x \<in> v ` carrier K \<and> 0 < x} = v k"

apply (frule vals_pos_nonempty[of v],
       frule vals_pos_LBset[of v],
       simp only:ant_1[THEN sym],
       frule AMin[of "{x. x \<in> v ` carrier K \<and> 0 < x}" "1"], assumption+,
       erule conjE)
apply (thin_tac "\<forall>x\<in>{x. x \<in> v ` carrier K \<and> 0 < x}.
                   AMin {x. x \<in> v ` carrier K \<and> 0 < x} \<le> x")
apply (simp add:image_def, erule conjE, erule bexE,
       thin_tac "{x. (\<exists>xa\<in>carrier K. x = v xa) \<and> 0 < x} \<subseteq> LBset 1",
       thin_tac "\<exists>x. (\<exists>xa\<in>carrier K. x = v xa) \<and> 0 < x",
       subgoal_tac "x \<in> carrier K - {\<zero>}", blast,
       frule AMin_z[of v],  erule exE, simp)
apply (simp add:image_def,
       thin_tac "AMin {x. (\<exists>xa\<in>carrier K. x = v xa) \<and> 0 < x} = ant a",
       rule contrapos_pp, simp+, frule sym, thin_tac "v (\<zero>) = ant a",
       simp add:value_of_zero)
done

lemma (in Corps) val_Pg:" valuation K v \<Longrightarrow>
                  Pg K v \<in> carrier K - {\<zero>} \<and> v (Pg K v) = Lv K v"
apply (frule AMin_k[of v], unfold Lv_def, unfold Pg_def)
apply (rule someI2_ex)
 apply (erule bexE, drule sym, unfold Lv_def, blast)
 apply simp
done

lemma (in Corps) amin_generateTr:"valuation K v \<Longrightarrow>
  \<forall>w\<in>carrier K - {\<zero>}. \<exists>z. v w = z *\<^sub>a AMin {x. x \<in> v ` carrier K \<and> 0 < x}"
apply (frule vals_pos_nonempty[of v],
       frule vals_pos_LBset[of v],
       simp only:ant_1[THEN sym],
       frule AMin[of "{x. x \<in> v ` carrier K \<and> 0 < x}" "1"], assumption+,
       frule AMin_z[of v], erule exE, simp,
       thin_tac "\<exists>x. x \<in> v ` carrier K \<and> 0 < x",
       (erule conjE)+, rule ballI, simp, erule conjE,
       frule_tac x = w in val_nonzero_noninf[of v], assumption+,
       frule_tac x = w in value_in_aug_inf[of v], assumption+,
       simp add:aug_inf_def,
       cut_tac a = "v w" in mem_ant, simp, erule exE,
       cut_tac a = z and b = a in amod_adiv_equality)
apply (case_tac "z mod a = 0", simp add:ant_0 aadd_0_r, blast,
       thin_tac "{x. x \<in> v ` carrier K \<and> 0 < x} \<subseteq> LBset 1",
       thin_tac "v w \<noteq> \<infinity>", thin_tac "v w \<noteq> - \<infinity>")

apply (frule AMin_k[of v], erule bexE,
       drule sym,
       drule sym,
       drule sym,
       rotate_tac -1, drule sym)

apply (cut_tac z = z in z_in_aug_inf,
       cut_tac z = "(z div a)" and x = a in asp_z_Z,
       cut_tac z = "z mod a" in z_in_aug_inf,
       frule_tac a = "ant z" and b = "(z div a) *\<^sub>a ant a" and
       c = "ant (z mod a)" in ant_sol, assumption+,
       subst asprod_mult, simp, assumption, simp,
       frule_tac x = k and z = "z div a" in val_exp[of v],
        (erule conjE)+, assumption, simp, simp,
       thin_tac "(z div a) *\<^sub>a v k = v (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)",
       erule conjE)
apply (frule_tac x = k and n = "z div a" in field_potent_nonzero1,
         assumption+,
      frule_tac a = k and n = "z div a" in npowf_mem, assumption,
      frule_tac x1 = "k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>" in value_of_inv[THEN sym, of v], assumption+,
      simp add:diff_ant_def,
       thin_tac "- v (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>) = v ((k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>)",
       cut_tac x = "k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>" in invf_closed1, simp,
       simp, erule conjE,
       frule_tac x1 = w and y1 = "(k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>"  in
        val_t2p[THEN sym, of  v], assumption+, simp,
       cut_tac field_is_ring,
       thin_tac "v w + v ((k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>) = ant (z mod a)",
       thin_tac "v (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>) + ant (z mod a) = v w",
       frule_tac x = w and y = "(k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>" in
                 Ring.ring_tOp_closed[of "K"], assumption+)
apply (frule valuation_map[of v],
       frule_tac a = "w \<cdot>\<^sub>r (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>" in mem_in_image[of "v"
        "carrier K" "Z\<^sub>\<infinity>"], assumption+, simp)
apply (thin_tac "AMin {x. x \<in> v ` carrier K \<and> 0 < x} = v k",
       thin_tac "v \<in> carrier K \<rightarrow> Z\<^sub>\<infinity>",
       subgoal_tac "0 < v (w \<cdot>\<^sub>r (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup> )",
       drule_tac a = "v (w \<cdot>\<^sub>r (k\<^bsub>K\<^esub>\<^bsup>(z div a)\<^esup>)\<^bsup>\<hyphen> K\<^esup>)" in forall_spec,
       simp add:image_def)
apply (drule sym, simp)
apply (frule_tac b = a and a = z in pos_mod_conj, erule conjE,
       simp, simp,
       frule_tac b = a and a = z in pos_mod_conj, erule conjE, simp)
done

lemma (in Corps) val_principalTr1:"\<lbrakk> valuation K v\<rbrakk>  \<Longrightarrow>
            Lv K v \<in> v ` (carrier K - {\<zero>}) \<and>
             (\<forall>w\<in>v ` carrier K. \<exists>a. w = a * Lv K v) \<and> 0 < Lv K v"
 apply (rule conjI,
        frule val_Pg[of v], erule conjE,
        simp add:image_def, frule sym, thin_tac "v (Pg K v) = Lv K v",
        erule conjE, blast)
 apply (rule conjI,
       rule ballI, simp add:image_def, erule bexE)

 apply  (
        frule_tac x = x in value_in_aug_inf[of v], assumption,
        frule sym, thin_tac "w = v x", simp add:aug_inf_def,
        cut_tac a = w in mem_ant, simp, erule disjE, erule exE,
        frule_tac x = x in value_noninf_nonzero[of v], assumption+,
        simp, frule amin_generateTr[of v])
 apply (drule_tac x = x in bspec, simp,
        erule exE,
        frule AMin_z[of v], erule exE, simp add:Lv_def,
        simp add:asprod_mult, frule sym, thin_tac "za * a = z",
        simp, subst a_z_z[THEN sym], blast)

 apply (simp add:Lv_def,
        frule AMin_z[of v], erule exE, simp,
        frule Lv_pos[of v], simp add:Lv_def,
        frule_tac m1 = a in a_i_pos[THEN sym], blast,
        simp add:Lv_pos)
done

lemma (in Corps) val_principalTr2:"\<lbrakk>valuation K v;
  c \<in> v ` (carrier K - {\<zero>}) \<and> (\<forall>w\<in>v ` carrier K. \<exists>a. w = a * c) \<and> 0 < c;
  d \<in> v ` (carrier K - {\<zero>}) \<and> (\<forall>w\<in>v ` carrier K. \<exists>a. w = a * d) \<and> 0 < d\<rbrakk>
       \<Longrightarrow> c = d"
apply ((erule conjE)+,
       drule_tac x = d in bspec,
       simp add:image_def, erule bexE, blast,
       drule_tac x = c in bspec,
       simp add:image_def, erule bexE, blast)

apply ((erule exE)+,
       drule sym, simp,
       simp add:image_def, (erule bexE)+, simp,
       (erule conjE)+,
       frule_tac x = x in val_nonzero_z[of v], assumption+, erule exE,
       frule_tac x = xa in val_nonzero_z[of v], assumption+, erule exE,
       simp) apply (
       subgoal_tac "a \<noteq> \<infinity> \<and> a \<noteq> -\<infinity>", subgoal_tac "aa \<noteq> \<infinity> \<and> aa \<noteq> -\<infinity>",
       cut_tac a = a in mem_ant, cut_tac a = aa in mem_ant, simp,
       (erule exE)+, simp add:a_z_z,
       thin_tac "c = ant z", frule sym, thin_tac "zb * z = za", simp)
apply (subgoal_tac "0 < zb",
       cut_tac a = zc and b = zb in mult.commute, simp,
       simp add:pos_zmult_eq_1_iff,
       rule contrapos_pp, simp+,
       cut_tac x = 0 and y = zb in less_linear, simp,
       thin_tac "\<not> 0 < zb",
       erule disjE, simp,
       frule_tac i = 0 and j = z and k = zb in zmult_zless_mono_neg,
             assumption+, simp add:mult.commute)
apply (rule contrapos_pp, simp+, thin_tac "a \<noteq> \<infinity> \<and> a \<noteq> - \<infinity>",
       erule disjE, simp, rotate_tac 5, drule sym,
       simp, simp, rotate_tac 5, drule sym, simp)
apply (rule contrapos_pp, simp+,
       erule disjE, simp, rotate_tac 4,
       drule sym, simp, simp,
       rotate_tac 4, drule sym,
       simp)
done

lemma (in Corps) val_principal:"valuation K v \<Longrightarrow>
  \<exists>!x0. x0 \<in> v ` (carrier K - {\<zero>}) \<and>
     (\<forall>w \<in> v ` (carrier K). \<exists>(a::ant). w = a * x0) \<and> 0 < x0"
by (rule ex_ex1I,
    frule val_principalTr1[of v], blast,
    rule_tac c = x0 and d = y in val_principalTr2[of v],
                 assumption+)

lemma (in Corps) n_val_defTr:"\<lbrakk>valuation K v; w \<in> carrier K\<rbrakk> \<Longrightarrow>
                           \<exists>!a. a * Lv K v = v w"
apply (rule ex_ex1I,
      frule AMin_k[of v],
      frule Lv_pos[of v], simp add:Lv_def,
      erule bexE,
      frule_tac x = k in val_nonzero_z[of v], simp, simp,
      erule exE, simp, (erule conjE)+)
apply (case_tac "w = \<zero>\<^bsub>K\<^esub>", simp add:value_of_zero,
       frule_tac m = z in a_i_pos, blast)
apply (frule amin_generateTr[of v],
       drule_tac x = w in bspec, simp, simp)
apply (
       erule exE, simp add:asprod_mult,
       subst a_z_z[THEN sym], blast)
apply (frule AMin_k[of v]) apply (erule bexE,
      frule Lv_pos[of v], simp add:Lv_def) apply (
      erule conjE,
      frule_tac x = k in val_nonzero_z[of v], assumption+,
      erule exE, simp) apply (
      case_tac "w = \<zero>\<^bsub>K\<^esub>", simp del:a_i_pos add:value_of_zero,
      subgoal_tac "y = \<infinity>", simp, rule contrapos_pp, simp+,
      cut_tac a = a in mem_ant, simp,
      erule disjE, simp, erule exE, simp add:a_z_z)
apply (rule contrapos_pp, simp+,
      cut_tac a = y in mem_ant, simp, erule disjE, simp,
      erule exE, simp add:a_z_z,
      frule_tac x = w in val_nonzero_z[of v], assumption+,
      erule exE, simp, cut_tac a = a in mem_ant,
      erule disjE, simp, frule sym, thin_tac "- \<infinity> = ant za", simp,
      erule disjE, erule exE, simp add:a_z_z)
apply (cut_tac a = y in mem_ant,
      erule disjE, simp, rotate_tac 3, drule sym,
      simp, erule disjE, erule exE, simp add:a_z_z, frule sym,
      thin_tac "zb * z = za", simp, simp,
      rotate_tac 3, drule sym,
      simp, simp, frule sym, thin_tac "\<infinity> = ant za", simp)
done

lemma (in Corps) n_valTr:"\<lbrakk> valuation K v; x \<in> carrier K\<rbrakk>  \<Longrightarrow>
             (THE l. (l * (Lv K v)) = v x)*(Lv K v) = v x"
by (rule theI', rule n_val_defTr, assumption+)

lemma (in Corps) n_val:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk>  \<Longrightarrow>
                           (n_val K v x)*(Lv K v) = v x"
by (frule n_valTr[of v x], assumption+, simp add:n_val_def)

lemma (in Corps) val_pos_n_val_pos:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk>  \<Longrightarrow>
           (0 \<le> v x) = (0 \<le> n_val K v x)"
apply (frule n_val[of v x], assumption+,
       drule sym,
       frule Lv_pos[of v],
       frule Lv_z[of v], erule exE, simp)
apply (frule_tac w = z and x = 0 and y = "n_val K v x" in amult_pos_mono_r,
       simp add:amult_0_l)
done

lemma (in Corps) n_val_in_aug_inf:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                           n_val K v x \<in> Z\<^sub>\<infinity>"
apply (cut_tac field_is_ring, frule Ring.ring_zero[of "K"],
       frule Lv_pos[of v],
       frule Lv_z[of v], erule exE,
       simp add:aug_inf_def)
apply (rule contrapos_pp, simp+)
apply (case_tac "x = \<zero>\<^bsub>K\<^esub>", simp,
       frule n_val[of v "\<zero>"],
       simp add:value_of_zero, simp add:value_of_zero)

apply (frule n_val[of v x], simp,
       frule val_nonzero_z[of v x], assumption+,
       erule exE, simp, rotate_tac -2, drule sym,
       simp)
done

lemma (in Corps) n_val_0:"\<lbrakk>valuation K v; x \<in> carrier K; v x = 0\<rbrakk>
       \<Longrightarrow>  n_val K v x = 0"
by (frule Lv_z[of v], erule exE,
       frule Lv_pos[of v],
       frule n_val[of v x], simp, simp,
       rule_tac z = z and a = "n_val K v x" in a_a_z_0, assumption+)

lemma (in Corps) value_n0_n_val_n0:"\<lbrakk>valuation K v; x \<in> carrier K; v x \<noteq> 0\<rbrakk> \<Longrightarrow>
                             n_val K v x \<noteq> 0"
apply (frule n_val[of v x],
       rule contrapos_pp, simp+, frule Lv_z[of v],
       erule exE, simp, simp only:ant_0[THEN sym])
apply (rule contrapos_pp, simp+,
       simp add:a_z_z)
done

lemma (in Corps) val_0_n_val_0:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                         (v x = 0) = (n_val K v x = 0)"
apply (rule iffI,
       simp add:n_val_0)
apply (rule contrapos_pp, simp+,
       frule value_n0_n_val_n0[of v x], assumption+)
apply simp
done

lemma (in Corps) val_noninf_n_val_noninf:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
      (v x \<noteq> \<infinity>) = (n_val K v x \<noteq> \<infinity>)"
by (frule Lv_z[of v], erule exE,
       frule Lv_pos[of v], simp,
       frule n_val[THEN sym, of v x],simp, simp,
       thin_tac "v x = n_val K v x * ant z",
       rule iffI, rule contrapos_pp, simp+,
       cut_tac mem_ant[of "n_val K v x"], erule disjE, simp,
       erule disjE, erule exE, simp add:a_z_z, simp, simp)

lemma (in Corps) val_inf_n_val_inf:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
      (v x = \<infinity>) = (n_val K v x = \<infinity>)"
by (cut_tac val_noninf_n_val_noninf[of v x], simp, assumption+)

lemma (in Corps) val_eq_n_val_eq:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K\<rbrakk>
  \<Longrightarrow>  (v x = v y) = (n_val K v x = n_val K v y)"
apply (subst n_val[THEN sym, of v x], assumption+,
       subst n_val[THEN sym, of v y], assumption+,
       frule Lv_pos[of v], frule Lv_z[of v], erule exE, simp,
       frule_tac s = z in zless_neq[THEN not_sym, of "0"])
apply (rule iffI)
apply (rule_tac z = z in amult_eq_eq_r[of _ "n_val K v x" "n_val K v y"],
         assumption+)
apply simp
done

lemma (in Corps) val_poss_n_val_poss:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk>  \<Longrightarrow>
           (0 < v x) = (0 < n_val K v x)"
apply (simp add:less_le,
       frule val_pos_n_val_pos[of v x], assumption+,
       rule iffI, erule conjE, simp,
       simp add:value_n0_n_val_n0[of v x])
apply (drule sym,
       erule conjE, simp,
       frule_tac val_0_n_val_0[THEN sym, of v x], assumption+,
       simp)
done

lemma (in Corps) n_val_Pg:"valuation K v \<Longrightarrow> n_val K v (Pg K v) = 1"
apply (frule val_Pg[of v], simp, (erule conjE)+,
       frule n_val[of v "Pg K v"], simp, frule Lv_z[of v], erule exE, simp,
       frule Lv_pos[of v], simp, frule_tac i = 0 and j = z in zless_neq)
apply (rotate_tac -1, frule not_sym, thin_tac "0 \<noteq> z",
       subgoal_tac "n_val K v (Pg K v) * ant z = 1 * ant z",
       rule_tac z = z in adiv_eq[of _ "n_val K v (Pg K v)" "1"], assumption+,
       simp add:amult_one_l)
done

lemma (in Corps) n_val_valuationTr1:"valuation K v \<Longrightarrow>
                           \<forall>x\<in>carrier K. n_val K v x \<in> Z\<^sub>\<infinity>"
by (rule ballI,
      frule n_val[of v], assumption,
      frule_tac x = x in value_in_aug_inf[of v], assumption,
      frule Lv_pos[of v], simp add:aug_inf_def,
      frule Lv_z[of v], erule exE, simp,
      rule contrapos_pp, simp+)

lemma (in Corps) n_val_t2p:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K\<rbrakk> \<Longrightarrow>
                   n_val K v (x \<cdot>\<^sub>r y) = n_val K v x + (n_val K v y)"
apply (cut_tac field_is_ring,
       frule Ring.ring_tOp_closed[of K x y], assumption+,
       frule n_val[of v "x \<cdot>\<^sub>r y"], assumption+,
       frule Lv_pos[of "v"],
       simp add:val_t2p,
       frule n_val[THEN sym, of v x], assumption+,
       frule n_val[THEN sym, of v y], assumption+, simp,
       frule Lv_z[of v], erule exE, simp)
apply (subgoal_tac "ant z \<noteq> 0")
apply (frule_tac z1 = z in amult_distrib1[THEN sym, of _ "n_val K v x"
       "n_val K v y"], simp,
       thin_tac "n_val K v x * ant z + n_val K v y * ant z =
           (n_val K v x + n_val K v y) * ant z",
       rule_tac z = z and a = "n_val K v (x \<cdot>\<^sub>r y)" and
        b = "n_val K v x + n_val K v y" in adiv_eq, simp, assumption+, simp)
done

lemma (in Corps) n_val_valuationTr2:"\<lbrakk> valuation K v; x \<in> carrier K;
      y \<in> carrier K\<rbrakk>  \<Longrightarrow>
       amin (n_val K v x) (n_val K v y) \<le> (n_val K v ( x \<plusminus> y))"
apply (frule n_val[THEN sym, of v x], assumption+,
       frule n_val[THEN sym, of v y], assumption+,
       frule n_val[THEN sym, of v "x \<plusminus> y"],
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       rule aGroup.ag_pOp_closed, assumption+)
apply (frule amin_le_plus[of v x y], assumption+, simp,
       simp add:amult_commute[of _ "Lv K v"],
       frule Lv_z[of v], erule exE, simp,
       frule Lv_pos[of v], simp,
       simp add:amin_amult_pos, simp add:amult_pos_mono_l)
done

lemma (in Corps) n_val_valuation:"valuation K v \<Longrightarrow>
                                      valuation K (n_val K v)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag)
apply (frule Lv_z[of v], erule exE, frule Lv_pos[of v], simp,
       subst valuation_def)
apply (rule conjI, simp add:n_val_def restrict_def extensional_def)
apply (rule conjI, simp add:n_val_valuationTr1)
apply (rule conjI, frule n_val[of v \<zero>],
       simp add:Ring.ring_zero,
       frule Lv_z[of v], erule exE, frule Lv_pos[of v],
       cut_tac mem_ant[of "n_val K v (\<zero>)"], erule disjE,
       simp add:value_of_zero,
       erule disjE, erule exE, simp add:a_z_z value_of_zero, assumption+)
apply (rule conjI, rule ballI,
       frule_tac x = x in val_nonzero_noninf[of v], simp+,
       simp add:val_noninf_n_val_noninf)
apply (rule conjI, (rule ballI)+, simp add:n_val_t2p,
       rule conjI, rule ballI, rule impI,
       frule Lv_z[of v], erule exE,
            frule Lv_pos[of v], simp,
       frule_tac x = x in n_val[of v], simp,
       frule_tac w1 = z and x1 = 0 and y1 = "n_val K v x" in
            amult_pos_mono_r[THEN sym], simp add:amult_0_l,
       frule_tac x = x in val_axiom4[of v], assumption+,
       frule_tac x1 = "1\<^sub>r \<plusminus> x" in n_val[THEN sym, of v],
       frule Ring.ring_is_ag[of "K"],
           rule aGroup.ag_pOp_closed, assumption+, simp add:Ring.ring_one,
           assumption,
       frule_tac w = z and x = 0 and y = "n_val K v (1\<^sub>r \<plusminus> x)"
           in amult_pos_mono_r,
       simp add:amult_0_l)

apply (frule val_axiom5[of v], erule exE,
       (erule conjE)+,
       frule_tac x = x in value_n0_n_val_n0[of v], assumption+,
       frule_tac x = x in val_noninf_n_val_noninf, simp,
       blast)
done

lemma (in Corps) n_val_le_val:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> (v x)\<rbrakk>  \<Longrightarrow>
                 (n_val K v x) \<le>(v x)"
by (subst n_val[THEN sym, of v x], assumption+,
       frule Lv_pos[of v],
       simp add:val_pos_n_val_pos[of v x],
       frule Lv_z[of v], erule exE,
       cut_tac b = z and x = "n_val K v x" in amult_pos, simp+,
       simp add:asprod_amult, simp add:amult_commute)

lemma (in Corps) n_val_surj:"valuation K v \<Longrightarrow>
                                   \<exists>x\<in> carrier K. n_val K v x = 1"
apply (frule Lv_z[of v], erule exE,
       frule Lv_pos[of v],
       frule AMin_k[of v], erule bexE, frule_tac x = k in n_val[of v], simp,
       simp add:Lv_def)
apply (subgoal_tac "n_val K v k * ant z = 1 * ant z",
       subgoal_tac "z \<noteq> 0",
       frule_tac z = z and a = "n_val K v k" and b = 1 in amult_eq_eq_r,
         assumption, blast, simp, simp add:amult_one_l)
done

lemma (in Corps) n_value_in_aug_inf:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                             n_val K v x \<in> Z\<^sub>\<infinity>"
by (frule n_val[of v x], assumption,
    simp add:aug_inf_def, rule contrapos_pp, simp+,
    frule Lv_pos[of v], frule Lv_z[of v], erule exE, simp,
    frule value_in_aug_inf[of v x], assumption+, simp add:aug_inf_def)

lemma (in Corps) val_surj_n_valTr:"\<lbrakk>valuation K v; \<exists>x \<in> carrier K. v x = 1\<rbrakk>
      \<Longrightarrow>  Lv K v = 1"
apply (erule bexE,
       frule_tac x = x in n_val[of v],
       simp, frule Lv_pos[of v])
apply (frule_tac w = "Lv K v" and x = "n_val K v x" in amult_1_both)
apply simp+
done

lemma (in Corps) val_surj_n_val:"\<lbrakk>valuation K v; \<exists>x \<in> carrier K. v x = 1\<rbrakk> \<Longrightarrow>
                       (n_val K v) = v"
apply (rule funcset_eq[of _ "carrier K"],
      simp add:n_val_def restrict_def extensional_def,
      simp add:valuation_def)
apply (rule ballI,
       frule val_surj_n_valTr[of v], assumption+,
       frule_tac x = x in n_val[of v], assumption+,
       simp add:amult_one_r)
done

lemma (in Corps) n_val_n_val:"valuation K v \<Longrightarrow>
        n_val K (n_val K v)  = n_val K v"
by (frule n_val_valuation[of v],
       frule n_val_surj[of v],
       simp add:val_surj_n_val)

lemma nnonzero_annonzero:"0 < N \<Longrightarrow> an N \<noteq> 0"
apply (simp only:an_0[THEN sym])
apply (subst aneq_natneq, simp)
done


section "Valuation ring"

definition
  Vr :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant] \<Rightarrow> ('r, 'm) Ring_scheme" where
  "Vr K v = Sr K ({x. x \<in> carrier K \<and> 0 \<le> (v x)})"

definition
  vp :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant] \<Rightarrow> 'r set" where
  "vp K v = {x. x \<in> carrier (Vr K v) \<and> 0 < (v x)}"

definition
  r_apow :: "[('r, 'm) Ring_scheme, 'r set, ant] \<Rightarrow> 'r set" where
  "r_apow R I a = (if a = \<infinity> then {\<zero>\<^bsub>R\<^esub>} else
                   (if a = 0 then carrier R else I\<^bsup>\<diamondsuit>R (na a)\<^esup>))"
                                          (** 0 \<le> a and a \<noteq> -\<infinity> **)

abbreviation
  RAPOW  ("(3_\<^bsup> _ _\<^esup>)" [62,62,63]62) where
  "I\<^bsup>R a\<^esup> == r_apow R I a"

lemma (in Ring) ring_pow_apow:"ideal R I \<Longrightarrow>
                  I\<^bsup>\<diamondsuit>R n\<^esup> =  I\<^bsup>R (an n)\<^esup>"
apply (simp add:r_apow_def)
apply (case_tac "n = 0", simp)
apply (simp add:nnonzero_annonzero)
apply (simp add:an_neq_inf na_an)
done

lemma (in Ring) r_apow_Suc:"ideal R I \<Longrightarrow> I\<^bsup>R (an (Suc 0))\<^esup> = I"
apply (cut_tac an_1, simp add:r_apow_def)
apply (simp add:a0_neq_1[THEN not_sym])
  apply (simp only:ant_1[THEN sym])
  apply (simp del:ant_1 add:z_neq_inf[of 1, THEN not_sym])
  apply (simp add:na_1)
  apply (simp add:idealprod_whole_r)
done

lemma (in Ring) apow_ring_pow:"ideal R I \<Longrightarrow>
                  I\<^bsup>\<diamondsuit>R n\<^esup> =  I\<^bsup>R (an n)\<^esup>"
apply (simp add:r_apow_def)
apply (case_tac "n = 0", simp add:an_0)
apply (simp add: aless_nat_less[THEN sym],
       cut_tac an_neq_inf[of n],
       simp add: less_le[of 0 "an n"] na_an)
done

lemma (in Corps) Vr_ring:"valuation K v \<Longrightarrow> Ring (Vr K v)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:Vr_def, rule Ring.Sr_ring, assumption+)
  apply (simp add:sr_def)
  apply (intro conjI subsetI)
apply (simp_all add: value_of_one Ring.ring_one[of "K"])
apply ((rule allI, rule impI)+,
       (erule conjE)+, rule conjI, rule aGroup.ag_pOp_closed, assumption+,
       rule aGroup.ag_mOp_closed, assumption+)
apply (frule_tac x = x and y = "-\<^sub>a y" in amin_le_plus[of v], assumption+,
       rule aGroup.ag_mOp_closed, assumption+,
       simp add:val_minus_eq[of v]) apply (
       frule_tac z = 0 and x = "v x" and y = "v y" in amin_ge1, assumption+,
       frule_tac i = 0 and j = "amin (v x) (v y)" and k = "v (x \<plusminus> -\<^sub>a y)" in
       ale_trans, assumption+, simp)
  by (simp add: Ring.ring_tOp_closed aadd_two_pos val_t2p)

lemma (in Corps) val_pos_mem_Vr:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                             (0 \<le> (v x)) = (x \<in> carrier (Vr K v))"
by (rule iffI, (simp add:Vr_def Sr_def)+)

lemma (in Corps) val_poss_mem_Vr:"\<lbrakk>valuation K v; x \<in> carrier K; 0 < (v x)\<rbrakk>
                        \<Longrightarrow>  x \<in> carrier (Vr K v)"
by (frule aless_imp_le[of "0" "v x"], simp add:val_pos_mem_Vr)

lemma (in Corps) Vr_one:"valuation K v \<Longrightarrow> 1\<^sub>r\<^bsub>K\<^esub> \<in> carrier (Vr K v)"
by (cut_tac field_is_ring, frule Ring.ring_one[of "K"],
       frule val_pos_mem_Vr[of v "1\<^sub>r"], assumption+,
       simp add:value_of_one)

lemma (in Corps) Vr_mem_f_mem:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk>
     \<Longrightarrow>  x \<in> carrier K"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_0_f_0:"valuation K v \<Longrightarrow> \<zero>\<^bsub>Vr K v\<^esub> = \<zero>"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_1_f_1:"valuation K v \<Longrightarrow> 1\<^sub>r\<^bsub>(Vr K v)\<^esub> = 1\<^sub>r"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_pOp_f_pOp:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
       y \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>  x \<plusminus>\<^bsub>Vr K v\<^esub> y = x \<plusminus> y"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_mOp_f_mOp:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk>
                     \<Longrightarrow> -\<^sub>a\<^bsub>(Vr K v)\<^esub> x = -\<^sub>a x"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_tOp_f_tOp:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
                     y \<in> carrier(Vr K  v)\<rbrakk> \<Longrightarrow>  x \<cdot>\<^sub>r\<^bsub>(Vr K v)\<^esub> y = x \<cdot>\<^sub>r y"
by (simp add:Vr_def Sr_def)

lemma (in Corps) Vr_pOp_le:"\<lbrakk>valuation K v; x \<in> carrier K;
       y \<in> carrier (Vr K v)\<rbrakk>  \<Longrightarrow> v x \<le> (v x + (v y))"
apply (frule val_pos_mem_Vr[THEN sym, of v y],
       simp add:Vr_mem_f_mem, simp, frule aadd_pos_le[of "v y" "v x"],
       simp add:aadd_commute)
done

lemma (in Corps) Vr_integral:"valuation K v \<Longrightarrow> Idomain (Vr K v)"
apply (simp add:Idomain_def,
       simp add:Vr_ring, simp add:Idomain_axioms_def,
       rule allI, rule impI, rule allI, (rule impI)+,
       simp add:Vr_tOp_f_tOp, simp add:Vr_0_f_0)
apply (rule contrapos_pp, simp+, erule conjE,
       cut_tac field_is_idom,
       frule_tac x = a in Vr_mem_f_mem[of v], assumption,
       frule_tac x = b in Vr_mem_f_mem[of v], assumption,
       frule_tac x = a and y = b in Idomain.idom_tOp_nonzeros[of "K"],
       assumption+, simp)
done

lemma (in Corps) Vr_exp_mem:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk>
      \<Longrightarrow>  x^\<^bsup>K n\<^esup> \<in> carrier (Vr K v)"
by (frule Vr_ring[of v],
       induct_tac n, simp add:Vr_one,
       simp add:Vr_tOp_f_tOp[THEN sym, of v],
       simp add:Ring.ring_tOp_closed)

lemma (in Corps) Vr_exp_f_exp:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>
                                    x^\<^bsup>(Vr K v) n\<^esup> =  x^\<^bsup>K n\<^esup>"
apply (induct_tac n,
      simp, simp add:Vr_1_f_1, simp,
      thin_tac "x^\<^bsup>(Vr K v) n\<^esup> = x^\<^bsup>K n\<^esup>")
apply (rule Vr_tOp_f_tOp, assumption+,
      simp add:Vr_exp_mem, assumption)
done

lemma (in Corps) Vr_potent_nonzero:"\<lbrakk>valuation K v;
      x \<in> carrier (Vr K v) - {\<zero>\<^bsub>Vr K v\<^esub>}\<rbrakk>  \<Longrightarrow> x^\<^bsup>K n\<^esup> \<noteq> \<zero>\<^bsub>Vr K v\<^esub>"
apply (frule Vr_mem_f_mem[of v x], simp,
       simp add:Vr_0_f_0, erule conjE)
apply (frule Vr_mem_f_mem[of v x], assumption+,
        simp add:field_potent_nonzero)
done

lemma (in Corps) elem_0_val_if:"\<lbrakk>valuation K v; x \<in> carrier K; v x = 0\<rbrakk>
              \<Longrightarrow> x \<in> carrier (Vr K v) \<and> x\<^bsup>\<hyphen> K\<^esup> \<in> carrier (Vr K v)"
apply (frule val_pos_mem_Vr[of v x], assumption, simp)
apply (frule value_zero_nonzero[of "v" "x"], simp add:Vr_mem_f_mem, simp)
apply (frule value_of_inv[of v x], assumption+,
       simp, subst val_pos_mem_Vr[THEN sym, of v "x\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       cut_tac invf_closed[of x], simp+)
done

lemma (in Corps) elem0val:"\<lbrakk>valuation K v; x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
      (v x = 0) = ( x \<in> carrier (Vr K v) \<and> x\<^bsup>\<hyphen> K\<^esup> \<in> carrier (Vr K v))"
apply (rule iffI, rule elem_0_val_if[of v], assumption+,
       erule conjE)
apply (simp add:val_pos_mem_Vr[THEN sym, of v x],
      frule Vr_mem_f_mem[of v "x\<^bsup>\<hyphen>K\<^esup>"], assumption+,
      simp add:val_pos_mem_Vr[THEN sym, of v "x\<^bsup>\<hyphen>K\<^esup>"],
      simp add:value_of_inv, frule ale_minus[of "0" "- v x"],
      simp add:a_minus_minus)
done

lemma (in Corps) ideal_inc_elem0val_whole:"\<lbrakk> valuation K v; x \<in> carrier K;
 v x = 0; ideal (Vr K v) I; x \<in> I\<rbrakk> \<Longrightarrow>  I = carrier (Vr K v)"
apply (frule elem_0_val_if[of v x], assumption+, erule conjE,
       frule value_zero_nonzero[of v x], assumption+,
       frule Vr_ring[of v],
       frule_tac I = I and x = x and r = "x\<^bsup>\<hyphen>K\<^esup>" in
       Ring.ideal_ring_multiple[of "Vr K v"], assumption+,
       cut_tac invf_closed1[of x], simp+, (erule conjE)+)
apply (simp add:Vr_tOp_f_tOp, cut_tac invf_inv[of x], simp+,
       simp add: Vr_1_f_1[THEN sym, of v],
       simp add:Ring.ideal_inc_one, simp+)
done

lemma (in Corps) vp_mem_Vr_mem:"\<lbrakk>valuation K v; x \<in> (vp K v)\<rbrakk> \<Longrightarrow>
                                                x \<in> carrier (Vr K v)"
by (rule val_poss_mem_Vr[of v x], assumption+, (simp add:vp_def
       Vr_def Sr_def)+)

lemma (in Corps) vp_mem_val_poss:"\<lbrakk> valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
                                   (x \<in> vp K v) = (0 < (v x))"
by (simp add:vp_def, simp add:Vr_def Sr_def less_ant_def)

lemma (in Corps) Pg_in_Vr:"valuation K v \<Longrightarrow>  Pg K v \<in> carrier (Vr K v)"
by (frule val_Pg[of v], erule conjE,
    frule Lv_pos[of v], drule sym,
    simp, erule conjE,
    simp add:val_poss_mem_Vr)

lemma (in Corps) vp_ideal:"valuation K v \<Longrightarrow>  ideal (Vr K v) (vp K v)"
apply (cut_tac field_is_ring,
       frule Vr_ring[of v],
       rule Ring.ideal_condition1, assumption+,
       rule subsetI, simp add:vp_mem_Vr_mem,
       simp add:vp_def)
apply (frule val_Pg[of v],
       frule Lv_pos[of v], simp, (erule conjE)+,
       drule sym, simp,
       frule val_poss_mem_Vr[of v "Pg K v"], assumption+, blast)

apply ((rule ballI)+,
       frule_tac x = x in vp_mem_Vr_mem[of v], assumption) apply (
       frule_tac x = y in vp_mem_Vr_mem[of v], assumption,
       simp add:vp_def,
       frule Ring.ring_is_ag[of "Vr K v"],
       frule_tac x = x and y = y in aGroup.ag_pOp_closed, assumption+, simp)
 apply (simp add:Vr_pOp_f_pOp,
        cut_tac x = "v x" and y = "v y" in amin_le_l,
        frule_tac x = x and y = y in amin_le_plus,
        (simp add:Vr_mem_f_mem)+,
       (frule_tac z = 0 and x = "v x" and y = "v y" in amin_gt, assumption+),
       rule_tac x = 0 and y = "amin (v x) (v y)" and z = "v (x \<plusminus> y)" in
       less_le_trans, assumption+)
apply ((rule ballI)+,
       frule_tac x1 = r in val_pos_mem_Vr[THEN sym, of v],
       simp add:Vr_mem_f_mem, simp,
       frule_tac x = x in vp_mem_Vr_mem[of v], simp add:Vr_pOp_f_pOp,
       simp add:vp_def, simp add:Ring.ring_tOp_closed,
       simp add:Vr_tOp_f_tOp)
apply (frule_tac x = r in Vr_mem_f_mem[of v], assumption+,
       frule_tac x = x in Vr_mem_f_mem[of v], assumption+,
       simp add:val_t2p, simp add:aadd_pos_poss)
done

lemma (in Corps) vp_not_whole:"valuation K v \<Longrightarrow>
                       (vp K v) \<noteq> carrier (Vr K v)"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Vr_ring[of v])
apply (rule contrapos_pp, simp+,
       drule sym,
       frule Ring.ring_one[of "Vr K v"], simp,
       simp add:Vr_1_f_1,
       frule Ring.ring_one[of "K"])
apply (simp only:vp_mem_val_poss[of v "1\<^sub>r"],
        simp add:value_of_one)
done

lemma (in Ring) elem_out_ideal_nonzero:"\<lbrakk>ideal R I; x \<in> carrier R;
        x \<notin> I\<rbrakk> \<Longrightarrow> x \<noteq> \<zero>\<^bsub>R\<^esub>"
by (rule contrapos_pp, simp+, frule ideal_zero[of I],
       simp)

lemma (in Corps) vp_prime:"valuation K v \<Longrightarrow> prime_ideal (Vr K v) (vp K v)"
apply (simp add:prime_ideal_def, simp add:vp_ideal)
apply (rule conjI)
(** if the unit is contained in (vp K v), then (vp K v) is
    the whole ideal, this contradicts vp_not_whole **)
apply (rule contrapos_pp, simp+,
       frule Vr_ring[of v],
       frule vp_ideal[of v],
       frule Ring.ideal_inc_one[of "Vr K v" "vp K v"], assumption+,
       simp add:vp_not_whole[of v]) (* done*)

(** if x \<cdot>\<^bsub>(Vr K v)\<^esub> y is in (vp K v), then 0 < v (x \<cdot>\<^sub>K y). We have
    0 \<le> (v x) and 0 \<le> (v y), because x and y are elements of Vr K v.
    Since v (x \<cdot>\<^sub>K y) = (v x) + (v y), we have 0 < (v x) or 0 < (v y).
   To obtain the final conclusion, we suppose \<not> (x \<in> vp K v \<or> y \<in> vp K v)
   then, we have (v x) = 0 and (v y) = 0. Frome this, we have v (x \<cdot>\<^sub>K y) =
   0. Contradiction.  *)
apply ((rule ballI)+, rule impI, rule contrapos_pp, simp+, (erule conjE)+,
       frule Vr_ring[of v]) apply (
       frule_tac x = x in Vr_mem_f_mem[of v], assumption) apply (
       frule_tac x = y in Vr_mem_f_mem[of v], assumption) apply (
       frule vp_ideal[of v],
       frule_tac x = x in Ring.elem_out_ideal_nonzero[of "Vr K v" "vp K v"],
       assumption+) apply (
       frule_tac x = y in Ring.elem_out_ideal_nonzero[of "Vr K v" "vp K v"],
       assumption+, simp add:Vr_0_f_0,
       simp add:Vr_tOp_f_tOp) apply (
       frule_tac x = "x \<cdot>\<^sub>r y" in vp_mem_val_poss[of v],
       cut_tac field_is_ring, simp add:Ring.ring_tOp_closed, simp)
apply (cut_tac field_is_ring,
       frule_tac x = x and y = y in Ring.ring_tOp_closed, assumption+,
       simp add:Ring.ring_tOp_closed[of "Vr K v"],
       simp add:vp_def, simp add:aneg_less,
       frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of v], assumption+,
       frule_tac x1 = y in val_pos_mem_Vr[THEN sym, of v], assumption+,
       frule_tac P = "x \<in> carrier (Vr K v)" and Q = "0 \<le> v x" in eq_prop,
          assumption,
       frule_tac P = "y \<in> carrier (Vr K v)" and Q = "0 \<le> v y" in eq_prop,
          assumption,
       frule_tac x = "v x" and y = 0 in ale_antisym, assumption+,
       frule_tac x = "v y" and y = 0 in ale_antisym, assumption+,
       simp add:val_t2p aadd_0_l)
done

lemma (in Corps) vp_pow_ideal:"valuation K v \<Longrightarrow>
                      ideal (Vr K v) ((vp K v)\<^bsup>\<diamondsuit>(Vr K v) n\<^esup>)"
by (frule Vr_ring[of v], frule vp_ideal[of v],
       simp add:Ring.ideal_pow_ideal)

lemma (in Corps) vp_apow_ideal:"\<lbrakk>valuation K v; 0 \<le> n\<rbrakk> \<Longrightarrow>
                      ideal (Vr K v) ((vp K v)\<^bsup>(Vr K v) n\<^esup>)"
apply (frule Vr_ring[of v])
apply (case_tac "n = 0",
        simp add:r_apow_def, simp add:Ring.whole_ideal[of "Vr K v"])
apply (case_tac "n = \<infinity>",
        simp add:r_apow_def, simp add:Ring.zero_ideal)
apply (simp add:r_apow_def, simp add:vp_pow_ideal)
done

lemma (in Corps) mem_vp_apow_mem_Vr:"\<lbrakk>valuation K v;
       0 \<le> N; x \<in> vp K v \<^bsup>(Vr K v) N\<^esup>\<rbrakk>  \<Longrightarrow> x \<in> carrier (Vr K v)"
by (frule Vr_ring[of v], frule vp_apow_ideal[of v N], assumption,
    simp add:Ring.ideal_subset)

lemma (in Corps) elem_out_vp_unit:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
      x \<notin> vp K v\<rbrakk>  \<Longrightarrow> v x = 0"
by (metis Vr_mem_f_mem ale_antisym aneg_le val_pos_mem_Vr vp_mem_val_poss)

lemma (in Corps) vp_maximal:"valuation K v \<Longrightarrow>
                          maximal_ideal (Vr K v) (vp K v)"
apply (frule Vr_ring[of v],
       simp add:maximal_ideal_def, simp add:vp_ideal)
(** we know that vp is not a whole ideal, and so vp does not include 1 **)
apply (frule vp_not_whole[of v],
       rule conjI, rule contrapos_pp, simp+, frule vp_ideal[of v],
       frule Ring.ideal_inc_one[of "Vr K v" "vp K v"], assumption+)
 apply simp
(** onemore condition of maximal ideal **)
apply (rule equalityI,
       rule subsetI, simp, erule conjE,
       case_tac "x = vp K v", simp, simp, rename_tac X)
(** show exists a unit contained in X **)
apply (frule_tac A = X in sets_not_eq[of _ "vp K v"], assumption+,
       erule bexE,
       frule_tac I = X and h = a in Ring.ideal_subset[of "Vr K v"],
       assumption+,
       frule_tac x = a in elem_out_vp_unit[of v], assumption+)
(** since v a = 0, we see a is a unit **)
 apply (frule_tac x = a and I = X in ideal_inc_elem0val_whole [of v],
        simp add:Vr_mem_f_mem, assumption+)

 apply (rule subsetI, simp, erule disjE,
       simp add:prime_ideal_def, simp add:vp_ideal,
       simp add:Ring.whole_ideal, rule subsetI, simp add:vp_mem_Vr_mem)
done

lemma (in Corps) ideal_sub_vp:"\<lbrakk> valuation K v; ideal (Vr K v) I;
 I \<noteq> carrier (Vr K v)\<rbrakk> \<Longrightarrow> I \<subseteq> (vp K v)"
apply (frule Vr_ring[of v], rule contrapos_pp, simp+)
 apply (simp add:subset_eq,
        erule bexE)
 apply (frule_tac h = x in Ring.ideal_subset[of "Vr K v" I], assumption+,
        frule_tac x = x in elem_out_vp_unit[of v], assumption+,
        frule_tac x = x in ideal_inc_elem0val_whole[of v _ I],
        simp add:Vr_mem_f_mem, assumption+, simp)
done

lemma (in Corps) Vr_local:"\<lbrakk>valuation K v; maximal_ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                   (vp K v) = I"
apply (frule Vr_ring[of v],
       frule ideal_sub_vp[of v I], simp add:Ring.maximal_ideal_ideal)
apply (simp add:maximal_ideal_def,
       frule conjunct2, fold maximal_ideal_def, frule conjunct1,
       rule Ring.proper_ideal, assumption+,simp add:maximal_ideal_def, assumption)
apply (rule equalityI) prefer 2 apply assumption
 apply (rule contrapos_pp, simp+,
        frule sets_not_eq[of "vp K v" I], assumption+, erule bexE)
apply (frule_tac x = a in vp_mem_Vr_mem[of v],
 frule Ring.maximal_ideal_ideal[of "Vr K v" "I"], assumption,
 frule_tac x = a in Ring.elem_out_ideal_nonzero[of "Vr K v" "I"],
           assumption+,
 frule vp_ideal[of v], rule Ring.ideal_subset[of "Vr K v" "vp K v"],
 assumption+)

apply (frule_tac a = a in Ring.principal_ideal[of "Vr K v"], assumption+,
       frule Ring.maximal_ideal_ideal[of "Vr K v" I], assumption+,
       frule_tac ?I2.0 = "Vr K v \<diamondsuit>\<^sub>p a"in Ring.sum_ideals[of "Vr K v" "I"],
        simp add:Ring.maximal_ideal_ideal, assumption,
   frule_tac ?I2.0 = "Vr K v \<diamondsuit>\<^sub>p a"in Ring.sum_ideals_la1[of "Vr K v" "I"],
      assumption+,
   frule_tac ?I2.0 = "Vr K v \<diamondsuit>\<^sub>p a"in Ring.sum_ideals_la2[of "Vr K v" "I"],
      assumption+,
   frule_tac a = a in Ring.a_in_principal[of "Vr K v"], assumption+,
   frule_tac A = "Vr K v \<diamondsuit>\<^sub>p a" and B = "I \<minusplus>\<^bsub>(Vr K v)\<^esub> (Vr K v \<diamondsuit>\<^sub>p a)"
       and c = a in subsetD, assumption+)
   thm Ring.sum_ideals_cont[of "Vr K v" "vp K v" I ]
apply (frule_tac B = "Vr K v \<diamondsuit>\<^sub>p a" in Ring.sum_ideals_cont[of "Vr K v"
       "vp K v" I], simp add:vp_ideal, assumption)
 apply (frule_tac a = a in Ring.ideal_cont_Rxa[of "Vr K v" "vp K v"],
        simp add:vp_ideal, assumption+)
 apply (simp add:maximal_ideal_def, (erule conjE)+,
      subgoal_tac "I \<minusplus>\<^bsub>(Vr K v)\<^esub> (Vr K v \<diamondsuit>\<^sub>p a) \<in> {J. ideal (Vr K v) J \<and> I \<subseteq> J}",
      simp, thin_tac "{J. ideal (Vr K v) J \<and> I \<subseteq> J} = {I, carrier (Vr K v)}")
 apply (erule disjE, simp)
 apply (cut_tac A = "carrier (Vr K v)" and B = "I \<minusplus>\<^bsub>Vr K v\<^esub> Vr K v \<diamondsuit>\<^sub>p a" and
        C = "vp K v" in subset_trans, simp, assumption,
        frule Ring.ideal_subset1[of "Vr K v" "vp K v"], simp add:vp_ideal,
        frule equalityI[of "vp K v" "carrier (Vr K v)"], assumption+,
        frule vp_not_whole[of v], simp)
 apply blast
done

lemma (in Corps) v_residue_field:"valuation K v \<Longrightarrow>
                                Corps ((Vr K v)  /\<^sub>r (vp K v))"
by (frule Vr_ring[of v],
       rule Ring.residue_field_cd [of "Vr K v" "vp K v"], assumption+,
       simp add:vp_maximal)

lemma (in Corps) Vr_n_val_Vr:"valuation K v \<Longrightarrow>
     carrier (Vr K v) = carrier (Vr K (n_val K v))"
by (simp add:Vr_def Sr_def,
       rule equalityI,
      (rule subsetI, simp, erule conjE, simp add:val_pos_n_val_pos),
      (rule subsetI, simp, erule conjE, simp add:val_pos_n_val_pos[THEN sym]))


section "Ideals in a valuation ring"

lemma (in Corps) Vr_has_poss_elem:"valuation K v \<Longrightarrow>
                 \<exists>x\<in>carrier (Vr K v) - {\<zero>\<^bsub>Vr K v\<^esub>}. 0 < v x"
apply (frule val_Pg[of v], erule conjE,
       frule Lv_pos[of v], drule sym,
       subst Vr_0_f_0, assumption+)
apply (frule aeq_ale[of "Lv K v" "v (Pg K v)"],
       frule aless_le_trans[of "0" "Lv K v" "v (Pg K v)"], assumption+,
       frule val_poss_mem_Vr[of v "Pg K v"],
       simp, assumption, blast)
done

lemma (in Corps) vp_nonzero:"valuation K v \<Longrightarrow>  vp K v \<noteq>  {\<zero>\<^bsub>Vr K v\<^esub>}"
apply (frule Vr_has_poss_elem[of v], erule bexE,
       simp, erule conjE,
       frule_tac x1 = x in vp_mem_val_poss[THEN sym, of v],
       simp add:Vr_mem_f_mem, simp, rule contrapos_pp, simp+)
done

lemma (in Corps) field_frac_mul:"\<lbrakk>x \<in> carrier K; y \<in> carrier K; y \<noteq> \<zero>\<rbrakk>
        \<Longrightarrow>   x = (x \<cdot>\<^sub>r  (y\<^bsup>\<hyphen>K\<^esup>)) \<cdot>\<^sub>r y"
apply (cut_tac invf_closed[of y],
       cut_tac field_is_ring,
       simp add:Ring.ring_tOp_assoc,
       subst linvf[of y], simp, simp add:Ring.ring_r_one[of K], simp)
done

lemma (in Corps) elems_le_val:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K;
       x \<noteq> \<zero>; v x \<le> (v y)\<rbrakk>  \<Longrightarrow> \<exists>r\<in>carrier (Vr K v). y = r \<cdot>\<^sub>r x"
apply (frule ale_diff_pos[of "v x" "v y"], simp add:diff_ant_def,
       simp add:value_of_inv[THEN sym, of v x],
       cut_tac invf_closed[of "x"],
       simp only:val_t2p[THEN sym, of v y "x\<^bsup>\<hyphen>K\<^esup>"])
apply (cut_tac field_is_ring,
       frule_tac x = y and y = "x\<^bsup>\<hyphen>K\<^esup>" in Ring.ring_tOp_closed[of "K"],
       assumption+,
       simp add:val_pos_mem_Vr[of v "y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)"],
       frule field_frac_mul[of y x], assumption+, blast)
apply simp
done

lemma (in Corps) val_Rxa_gt_a:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v) - {\<zero>};
 y \<in> carrier (Vr K v);  y \<in> Rxa (Vr K v) x\<rbrakk> \<Longrightarrow> v x \<le> (v y)"
apply (simp add:Rxa_def,
       erule bexE,
       simp add:Vr_tOp_f_tOp, (erule conjE)+,
        frule_tac x = r in Vr_mem_f_mem[of v], assumption+,
        frule_tac x = x in Vr_mem_f_mem[of v], assumption+)
apply (subst val_t2p, assumption+,
       simp add:val_pos_mem_Vr[THEN sym, of v],
       frule_tac y = "v r" in aadd_le_mono[of "0" _ "v x"],
       simp add:aadd_0_l)
done

lemma (in Corps) val_Rxa_gt_a_1:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
y \<in> carrier (Vr K v); x \<noteq> \<zero>; v x \<le> (v y)\<rbrakk> \<Longrightarrow> y \<in> Rxa (Vr K v) x"
apply (frule_tac x = x in Vr_mem_f_mem[of v], assumption+,
       frule_tac x = y in Vr_mem_f_mem[of v], assumption+,
       frule v_ale_diff[of v x y], assumption+,
       cut_tac invf_closed[of x],
       cut_tac field_is_ring, frule Ring.ring_tOp_closed[of K y "x\<^bsup>\<hyphen>K\<^esup>"],
        assumption+)
apply (simp add:val_pos_mem_Vr[of "v" "y \<cdot>\<^sub>r (x\<^bsup>\<hyphen>K\<^esup>)"],
       frule field_frac_mul[of "y" "x"], assumption+,
       simp add:Rxa_def, simp add:Vr_tOp_f_tOp, blast, simp)
done

lemma (in Corps) eqval_inv:"\<lbrakk>valuation K v; x \<in> carrier K; y \<in> carrier K;
       y \<noteq> \<zero>; v x = v y\<rbrakk> \<Longrightarrow>  0 = v (x \<cdot>\<^sub>r (y\<^bsup>\<hyphen>K\<^esup>))"
by (cut_tac invf_closed[of y],
       simp add:val_t2p value_of_inv, simp add:aadd_minus_r,
       simp)

lemma (in Corps) eq_val_eq_idealTr:"\<lbrakk>valuation K v;
      x \<in> carrier (Vr K v) - {\<zero>}; y \<in> carrier  (Vr K v); v x \<le> (v y)\<rbrakk> \<Longrightarrow>
                       Rxa (Vr K v) y \<subseteq>  Rxa (Vr K v) x"
apply (frule val_Rxa_gt_a_1[of v x y], simp+,
       erule conjE)
apply (frule_tac x = x in Vr_mem_f_mem[of v], assumption+,
       frule Vr_ring[of v],
       frule Ring.principal_ideal[of "Vr K v" "x"], assumption,
       frule Ring.ideal_cont_Rxa[of "Vr K v" "(Vr K v) \<diamondsuit>\<^sub>p x" "y"],
  assumption+)
done

lemma (in Corps) eq_val_eq_ideal:"\<lbrakk>valuation K v;
      x \<in> carrier (Vr K v); y \<in> carrier  (Vr K v); v x = v y\<rbrakk>
       \<Longrightarrow> Rxa (Vr K v) x = Rxa (Vr K v) y"
apply (case_tac "x = \<zero>\<^bsub>K\<^esub>",
       simp add:value_of_zero,
       frule value_inf_zero[of v y],
       simp add:Vr_mem_f_mem, rule sym, assumption, simp)
apply (rule equalityI,
       rule eq_val_eq_idealTr[of v y x], assumption+,
       drule sym, simp,
       rule contrapos_pp, simp+, simp add:value_of_zero,
       frule Vr_mem_f_mem[of v x], assumption+,
       frule value_inf_zero[of v x], assumption+,
       rule sym, assumption, simp, simp, simp)
apply (rule eq_val_eq_idealTr[of v x y], assumption+, simp,
       assumption, rule aeq_ale, assumption+)
done

lemma (in Corps) eq_ideal_eq_val:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
y \<in> carrier (Vr K v); Rxa (Vr K v) x = Rxa (Vr K v) y\<rbrakk>  \<Longrightarrow> v x = v y"
apply (case_tac "x = \<zero>\<^bsub>K\<^esub>", simp,
       drule sym,
       frule Vr_ring[of v],
       frule Ring.a_in_principal[of "Vr K v" y], assumption+, simp,
       thin_tac "Vr K v \<diamondsuit>\<^sub>p y = Vr K v \<diamondsuit>\<^sub>p (\<zero>)", simp add:Rxa_def,
       erule bexE, simp add:Vr_0_f_0[of v, THEN sym])
apply (simp add:Vr_tOp_f_tOp, simp add:Vr_0_f_0,
       frule_tac x = r in Vr_mem_f_mem[of v], assumption+,
       cut_tac field_is_ring, simp add:Ring.ring_times_x_0)
apply (frule Vr_ring[of v],
       frule val_Rxa_gt_a[of v x y], simp,
       simp)
apply (drule sym,
       frule Ring.a_in_principal[of "Vr K v" "y"], simp, simp)
apply (frule val_Rxa_gt_a[of v y x],
       simp, rule contrapos_pp, simp+,
       frule Ring.a_in_principal[of "Vr K v" "x"], assumption+,
       simp add:Rxa_def,
       erule bexE, simp add:Vr_tOp_f_tOp, cut_tac field_is_ring,
       frule_tac x = r in Vr_mem_f_mem[of v], assumption+,
       simp add:Ring.ring_times_x_0, simp,
       frule Ring.a_in_principal[of "Vr K v" "x"], assumption+, simp,
       rule ale_antisym, assumption+)
done

lemma (in Corps) zero_val_gen_whole:
 "\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>
             (v x = 0) = (Rxa (Vr K v) x = carrier (Vr K v))"
apply (frule Vr_mem_f_mem[of v x], assumption,
       frule Vr_ring[of v])
apply (rule iffI,
       frule Ring.principal_ideal[of "Vr K v" "x"], assumption+,
       frule Ring.a_in_principal[of "Vr K v" "x"], assumption+,
       rule ideal_inc_elem0val_whole[of v x "Vr K v \<diamondsuit>\<^sub>p x"], assumption+,
       frule Ring.ring_one[of "Vr K v"],
       frule eq_set_inc[of "1\<^sub>r\<^bsub>(Vr K v)\<^esub>"
              "carrier (Vr K v)" "Vr K v \<diamondsuit>\<^sub>p x"], drule sym, assumption,
       thin_tac "1\<^sub>r\<^bsub>(Vr K v)\<^esub> \<in> carrier (Vr K v)",
       thin_tac "Vr K v \<diamondsuit>\<^sub>p x = carrier (Vr K v)")
apply (simp add:Rxa_def, erule bexE,
       simp add:Vr_1_f_1, simp add:Vr_tOp_f_tOp,
       frule value_of_one[of v], simp,
       frule_tac x = r in Vr_mem_f_mem[of v], assumption+,
       cut_tac field_is_ring, simp add:val_t2p,
       simp add:val_pos_mem_Vr[THEN sym, of v],
       rule contrapos_pp, simp+,
       cut_tac less_le[THEN sym, of "0" "v x"], drule not_sym, simp,
       frule_tac x = "v r" and y = "v x" in aadd_pos_poss, assumption+,
       simp)
done

lemma (in Corps) elem_nonzeroval_gen_proper:"\<lbrakk> valuation K v;
      x \<in> carrier (Vr K v); v x \<noteq> 0\<rbrakk> \<Longrightarrow> Rxa (Vr K v) x \<noteq> carrier (Vr K v)"
apply (rule contrapos_pp, simp+)
apply (simp add: zero_val_gen_whole[THEN sym])
done

text\<open>We prove that Vr K v is a principal ideal ring\<close>

definition
  LI :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant, 'r set] \<Rightarrow> ant" where
         (** The least nonzero value of I **)
 "LI K v I = AMin (v ` I)"

definition
  Ig :: "[('r, 'm) Ring_scheme, 'r \<Rightarrow> ant, 'r set] \<Rightarrow> 'r" where
                                          (** Generator of I **)
  "Ig K v I = (SOME x. x \<in> I \<and> v x = LI K v I)"

lemma (in Corps) val_in_image:"\<lbrakk>valuation K v; ideal (Vr K v) I; x \<in> I\<rbrakk> \<Longrightarrow>
                            v x \<in> v ` I"
by (simp add:image_def, blast)

lemma (in Corps) I_vals_nonempty:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                           v ` I \<noteq> {}"
by (frule Vr_ring[of v],
    frule Ring.ideal_zero[of "Vr K v" "I"],
    assumption+, rule contrapos_pp, simp+)

lemma (in Corps) I_vals_LBset:"\<lbrakk> valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                                          v ` I  \<subseteq> LBset 0"
apply (frule Vr_ring[of v],
       rule subsetI, simp add:LBset_def, simp add:image_def)
apply (erule bexE,
       frule_tac h = xa in Ring.ideal_subset[of "Vr K v" "I"], assumption+)
apply (frule_tac x1 = xa in val_pos_mem_Vr[THEN sym, of v],
       simp add:Vr_mem_f_mem, simp)
done

lemma (in Corps) LI_pos:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow> 0 \<le> LI K v I"
apply (simp add:LI_def,
       frule I_vals_LBset[of v],
       simp add:ant_0[THEN sym],
       frule I_vals_nonempty[of v], simp only:ant_0)

apply (simp only:ant_0[THEN sym], frule AMin[of "v ` I" "0"], assumption,
       erule conjE, frule subsetD[of "v ` I" "LBset (ant 0)" "AMin (v ` I)"],
       assumption+, simp add:LBset_def)
done

lemma (in Corps) LI_poss:"\<lbrakk>valuation K v; ideal (Vr K v) I;
                 I \<noteq> carrier (Vr K v)\<rbrakk> \<Longrightarrow> 0 < LI K v I"
apply (subst less_le)
apply (simp add:LI_pos)
apply (rule contrapos_pp, simp+)

apply (simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp add:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+, simp only:ant_0)

apply (simp only:ant_0[THEN sym], frule AMin[of "v ` I" "0"], assumption,
       erule conjE, frule subsetD[of "v ` I" "LBset (ant 0)" "AMin (v ` I)"],
       assumption+, simp add:LBset_def)

apply (thin_tac "\<forall>x\<in>I. ant 0 \<le> v x",
       thin_tac "v ` I \<subseteq> {x. ant 0 \<le> x}", simp add:image_def,
       erule bexE, simp add:ant_0)
apply (frule Vr_ring[of v],
       frule_tac h = x in Ring.ideal_subset[of "Vr K v" "I"], assumption+,
       frule_tac x = x in zero_val_gen_whole[of v], assumption+,
       simp,
       frule_tac a = x in Ring.ideal_cont_Rxa[of "Vr K v" "I"], assumption+,
       simp, frule Ring.ideal_subset1[of "Vr K v" "I"], assumption+)
apply (frule equalityI[of "I" "carrier (Vr K v)"], assumption+, simp)
done

lemma (in Corps) LI_z:"\<lbrakk>valuation K v; ideal (Vr K v) I; I \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}\<rbrakk> \<Longrightarrow>
                 \<exists>z. LI K v I = ant z"
apply (frule Vr_ring[of v],
       frule Ring.ideal_zero[of "Vr K v" "I"], assumption+,
       cut_tac mem_ant[of "LI K v I"],
       frule LI_pos[of v I], assumption,
       erule disjE, simp,
       cut_tac minf_le_any[of "0"],
       frule ale_antisym[of "0" "-\<infinity>"], assumption+, simp)
apply (erule disjE, simp,
       frule singleton_sub[of "\<zero>\<^bsub>Vr K v\<^esub>" "I"],
       frule sets_not_eq[of "I" "{\<zero>\<^bsub>Vr K v\<^esub>}"], assumption+,
       erule bexE, simp)

apply (simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp only:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+,
       frule AMin[of "v ` I" "0"], assumption, erule conjE)
apply (frule_tac x = a in val_in_image[of v I], assumption+,
       drule_tac x = "v a" in bspec, simp,
       simp add:Vr_0_f_0,
       frule_tac x = a in val_nonzero_z[of v],
       simp add:Ring.ideal_subset Vr_mem_f_mem, assumption+,
       erule exE, simp,
       cut_tac x = "ant z" in inf_ge_any, frule_tac x = "ant z" in
       ale_antisym[of _ "\<infinity>"], assumption+, simp)
done

lemma (in Corps) LI_k:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                                \<exists>k\<in> I. LI K v I = v k"
by (simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp only:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+,
       frule AMin[of "v ` I" "0"], assumption, erule conjE,
       thin_tac "\<forall>x\<in>v ` I. AMin (v ` I) \<le> x", simp add:image_def)

lemma (in Corps) LI_infinity:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
             (LI K v I = \<infinity>)  = (I = {\<zero>\<^bsub>Vr K v\<^esub>})"
apply (frule Vr_ring[of v])
apply (rule iffI)
apply (rule contrapos_pp, simp+,
       frule Ring.ideal_zero[of "Vr K v" "I"], assumption+,
       frule singleton_sub[of "\<zero>\<^bsub>Vr K v\<^esub>" "I"],
       frule sets_not_eq[of "I" "{\<zero>\<^bsub>Vr K v\<^esub>}"], assumption+,
       erule bexE,
       frule_tac h = a in Ring.ideal_subset[of "Vr K v" "I"], assumption+,
       simp add:Vr_0_f_0,
       frule_tac x = a in Vr_mem_f_mem[of v], assumption+,
       frule_tac x = a in val_nonzero_z[of v], assumption+,
       erule exE,
       simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp only:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+,
       frule AMin[of "v ` I" "0"], assumption, erule conjE)
apply (frule_tac h = a in Ring.ideal_subset[of "Vr K v" "I"], assumption+,
       frule_tac x = a in val_in_image[of v I], assumption+,
       drule_tac x = "v a" in bspec, simp)
 apply (frule_tac x = a in val_nonzero_z[of v], assumption+,
       erule exE, simp,
       cut_tac x = "ant z" in inf_ge_any, frule_tac x = "ant z" in
       ale_antisym[of _ "\<infinity>"], assumption+, simp)

apply (frule sym, thin_tac "I = {\<zero>\<^bsub>Vr K v\<^esub>}",
       simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp only:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+,
       frule AMin[of "v ` I" "0"], assumption, erule conjE,
       drule sym, simp,
       simp add:Vr_0_f_0 value_of_zero)
done

lemma (in Corps) val_Ig:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                           (Ig K v I) \<in> I \<and> v (Ig K v I) = LI K v I"
by (simp add:Ig_def, rule someI2_ex,
    frule LI_k[of v I], assumption+, erule bexE,
    drule sym, blast, assumption)

lemma (in Corps) Ig_nonzero:"\<lbrakk>valuation K v; ideal (Vr K v) I; I \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}\<rbrakk>
                  \<Longrightarrow> (Ig K v I) \<noteq> \<zero>"
by (rule contrapos_pp, simp+,
    frule LI_infinity[of v I], assumption+,
    frule val_Ig[of v I], assumption+, erule conjE,
    simp add:value_of_zero)

lemma (in Corps) Vr_ideal_npowf_closed:"\<lbrakk>valuation K v; ideal (Vr K v) I;
       x \<in> I; 0 < n\<rbrakk> \<Longrightarrow> x\<^bsub>K\<^esub>\<^bsup>n\<^esup> \<in> I"
by (simp add:npowf_def, frule Vr_ring[of v],
      frule Ring.ideal_npow_closed[of "Vr K v" "I" "x" "nat n"], assumption+,
      simp, frule Ring.ideal_subset[of "Vr K v" "I" "x"], assumption+,
      simp add:Vr_exp_f_exp)

lemma (in Corps) Ig_generate_I:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                        (Vr K v) \<diamondsuit>\<^sub>p (Ig K v I) = I"
apply (frule Vr_ring[of v])
apply (case_tac "I = carrier (Vr K v)",
   frule sym, thin_tac "I = carrier (Vr K v)",
   frule Ring.ring_one[of "Vr K v"],
   simp, simp add: Vr_1_f_1,
   frule val_Ig[of v I], assumption+, erule conjE,
   frule LI_pos[of v I], assumption+,

   simp add: LI_def cong del: image_cong_simp,
   frule I_vals_LBset[of v], assumption+,
   simp only: ant_0[THEN sym],
   frule I_vals_nonempty[of v], assumption+,
   frule AMin[of "v ` I" "0"], assumption, erule conjE,

   frule val_in_image[of v I "1\<^sub>r"], assumption+,
   drule_tac x = "v (1\<^sub>r)" in bspec, assumption+,
   simp add: value_of_one ant_0 cong del: image_cong_simp,
   simp add: zero_val_gen_whole[of v "Ig K v I"])

apply (frule val_Ig[of v I], assumption+, (erule conjE)+,
       frule Ring.ideal_cont_Rxa[of "Vr K v" "I" "Ig K v I"], assumption+,
       rule equalityI, assumption+)

apply (case_tac "LI K v I = \<infinity>",
       frule LI_infinity[of v I], simp,
       simp add:Rxa_def, simp add:Ring.ring_times_x_0,
       frule Ring.ring_zero, blast)

apply (rule subsetI,
       case_tac "v x = 0",
       frule_tac x = x in Vr_mem_f_mem[of v],
       simp add:Ring.ideal_subset,
       frule_tac x = x in zero_val_gen_whole[of v],
       simp add:Ring.ideal_subset, simp,
       frule_tac a = x in Ring.ideal_cont_Rxa[of "Vr K v" "I"], assumption+,
       simp, frule Ring.ideal_subset1[of "Vr K v" "I"], assumption,
       frule equalityI[of "I" "carrier (Vr K v)"], assumption+, simp)
apply (simp add:LI_def,
       frule I_vals_LBset[of v], assumption+,
       simp only:ant_0[THEN sym],
       frule I_vals_nonempty[of v], assumption+,
       frule AMin[of "v ` I" "0"], assumption, erule conjE,
       frule_tac x = "v x" in bspec,
       frule_tac x = x in val_in_image[of v I], assumption+,
       simp)
apply (drule_tac x =  x in bspec, assumption,
       frule_tac y = x in eq_val_eq_idealTr[of v "Ig K v I"],
           simp add:Ring.ideal_subset,
       rule contrapos_pp, simp+, simp add:value_of_zero,
       simp add:Ring.ideal_subset, simp)

apply (frule_tac a = x in Ring.a_in_principal[of "Vr K v"],
       simp add:Ring.ideal_subset, rule subsetD, assumption+)
done

lemma (in Corps) Pg_gen_vp:"valuation K v  \<Longrightarrow>
                          (Vr K v) \<diamondsuit>\<^sub>p (Pg K v) = vp K v"
apply (frule vp_ideal[of v],
       frule Ig_generate_I[of v "vp K v"], assumption+,
       frule vp_not_whole[of v],
       frule eq_val_eq_ideal[of v "Ig K v (vp K v)" "Pg K v"],
       frule val_Ig [of v "vp K v"], assumption+, erule conjE,
       simp add:vp_mem_Vr_mem)

apply (frule val_Pg[of v], erule conjE,
       frule Lv_pos[of v],
       rotate_tac -2, drule sym, simp,
       simp add:val_poss_mem_Vr)

apply (thin_tac "Vr K v \<diamondsuit>\<^sub>p Ig K v (vp K v) = vp K v",
       frule val_Pg[of v], erule conjE,
       simp, frule val_Ig[of v "vp K v"], assumption+, erule conjE,
       simp, thin_tac "v (Pg K v) = Lv K v",
       thin_tac "Ig K v (vp K v) \<in> vp K v \<and> v (Ig K v (vp K v)) =
        LI K v (vp K v)", simp add:LI_def Lv_def,
       subgoal_tac "v ` vp K v = {x. x \<in> v ` carrier K \<and> 0 < x}",
       simp)

apply (thin_tac "ideal (Vr K v) (vp K v)", thin_tac "Pg K v \<in> carrier K",
       thin_tac "Pg K v \<noteq> \<zero>",
       rule equalityI, rule subsetI,
       simp add:image_def vp_def, erule exE, erule conjE,
       (erule conjE)+,
       frule_tac x = xa in Vr_mem_f_mem[of v], assumption+, simp, blast)

apply (rule subsetI, simp add:image_def vp_def, erule conjE, erule bexE, simp,
       frule_tac x = xa in val_poss_mem_Vr[of v], assumption+,
       cut_tac y = "v xa" in less_le[of "0"], simp, blast, simp)
done

lemma (in Corps) vp_gen_t:"valuation K v  \<Longrightarrow>
                \<exists>t\<in>carrier (Vr K v). vp K v = (Vr K v) \<diamondsuit>\<^sub>p t"
by (frule Pg_gen_vp[of v], frule Pg_in_Vr[of v], blast)

lemma (in Corps) vp_gen_nonzero:"\<lbrakk>valuation K v; vp K v = (Vr K v) \<diamondsuit>\<^sub>p t\<rbrakk> \<Longrightarrow>
                 t \<noteq> \<zero>\<^bsub>Vr K v\<^esub>"
apply (rule contrapos_pp, simp+,
       cut_tac Ring.Rxa_zero[of "Vr K v"], drule sym, simp,
       simp add:vp_nonzero)
apply (simp add:Vr_ring)
done

lemma (in Corps) n_value_idealTr:"\<lbrakk>valuation K v; 0 \<le> n\<rbrakk> \<Longrightarrow>
        (vp K v) \<^bsup>\<diamondsuit>(Vr K v) n\<^esup> = Vr K v \<diamondsuit>\<^sub>p ((Pg K v)^\<^bsup>(Vr K v) n\<^esup>)"
apply (frule Vr_ring[of v],
       frule Pg_gen_vp[THEN sym, of v],
       simp add:vp_ideal,
       frule val_Pg[of v], simp, (erule conjE)+)
apply (subst Ring.principal_ideal_n_pow[of "Vr K v" "Pg K v"
       "Vr K v \<diamondsuit>\<^sub>p Pg K v"], assumption+,
       frule Lv_pos[of v], rotate_tac -2, frule sym,
       thin_tac "v (Pg K v) = Lv K v", simp, simp add:val_poss_mem_Vr,
       simp+)
done

lemma (in Corps) ideal_pow_vp:"\<lbrakk>valuation K v; ideal (Vr K v) I;
                     I \<noteq> carrier (Vr K v); I \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}\<rbrakk>  \<Longrightarrow>
                     I = (vp K v)\<^bsup>\<diamondsuit> (Vr K v) (na (n_val K v (Ig K v I)))\<^esup>"
apply (frule Vr_ring[of v],
       frule Ig_generate_I[of v I], assumption+)

apply (frule n_val[of v "Ig K v I"],
       frule val_Ig[of v I], assumption+, erule conjE,
       simp add:Ring.ideal_subset[of "Vr K v" "I" "Ig K v I"] Vr_mem_f_mem)

apply (frule val_Pg[of v], erule conjE,
       rotate_tac -1, drule sym, simp,
       frule Ig_nonzero[of v I], assumption+,
       frule LI_pos[of v I], assumption+,
       frule Lv_pos[of v],
       frule val_Ig[of v I], assumption+, (erule conjE)+,
       rotate_tac -1, drule sym, simp,
       frule val_pos_n_val_pos[of v "Ig K v I"],
       simp add:Ring.ideal_subset Vr_mem_f_mem,
       simp)
apply (frule zero_val_gen_whole[THEN sym, of v "Ig K v I"],
       simp add:Ring.ideal_subset,
       simp, rotate_tac -1, drule not_sym,
       cut_tac less_le[THEN sym, of "0" "v (Ig K v I)"], simp,
              thin_tac "0 \<le> v (Ig K v I)",
       frule Ring.ideal_subset[of "Vr K v" I "Ig K v I"], assumption+,
       frule Vr_mem_f_mem[of v "Ig K v I"], assumption+,
       frule val_poss_n_val_poss[of v "Ig K v I"], assumption+, simp)
apply (frule Ig_nonzero[of v I],
       frule val_nonzero_noninf[of v "Ig K v I"], assumption+,
       simp add:val_noninf_n_val_noninf[of v "Ig K v I"],
       frule val_poss_mem_Vr[of v "Pg K v"], assumption+,
       subst n_value_idealTr[of v "na (n_val K v (Ig K v I))"],
          assumption+, simp add:na_def)

apply (frule eq_val_eq_ideal[of v "Ig K v I"
               "(Pg K v)^\<^bsup>(Vr K v) (na (n_val K v (Ig K v I)))\<^esup>"], assumption+,
       rule Ring.npClose, assumption+,
       simp add:Vr_exp_f_exp[of v "Pg K v"],
       subst val_exp_ring[THEN sym, of v "Pg K v"
                          "na (n_val K v (Ig K v I))"], assumption+)
apply (frule Lv_z[of v], erule exE, simp,
      rotate_tac 6, drule sym, simp,
      subst asprod_amult,
      simp add:val_poss_n_val_poss[of v "Ig K v I"],
      frule val_nonzero_noninf[of v "Ig K v I"], assumption+,
      frule val_noninf_n_val_noninf[of v "Ig K v I"], assumption+, simp,
      rule aposs_na_poss[of "n_val K v (Ig K v I)"], assumption+)
apply (fold an_def)
apply (subst an_na[THEN sym, of "n_val K v (Ig K v I)"],
      frule val_nonzero_noninf[of v "Ig K v I"], assumption+,
      frule val_noninf_n_val_noninf[of v "Ig K v I"], assumption+, simp,
      simp add:aless_imp_le, simp)
apply simp
done

lemma (in Corps) ideal_apow_vp:"\<lbrakk>valuation K v; ideal (Vr K v) I\<rbrakk> \<Longrightarrow>
                     I = (vp K v)\<^bsup> (Vr K v) (n_val K v (Ig K v I))\<^esup>"
apply (frule Vr_ring[of v])
apply (case_tac "v (Ig K v I) = \<infinity>",
       frule val_Ig[of v I], assumption,
       frule val_inf_n_val_inf[of v "Ig K v I"],
       simp add:Ring.ideal_subset Vr_mem_f_mem, simp, simp add:r_apow_def,
       simp add:LI_infinity[of v I])

apply (case_tac "v (Ig K v I) = 0",
       frule val_0_n_val_0[of v "Ig K v I"],
       frule val_Ig[of v I], assumption+, erule conjE,
       simp add:Ring.ideal_subset Vr_mem_f_mem, simp,

       frule val_Ig[of v I], assumption,
       frule zero_val_gen_whole[of v "Ig K v I"],
       simp add:Ring.ideal_subset, (erule conjE)+, simp,
       frule Ring.ideal_cont_Rxa[of "Vr K v" "I" "Ig K v I"], assumption+)
apply (simp,
       frule Ring.ideal_subset1[of "Vr K v" "I"], assumption+,
       frule equalityI[of "I" "carrier (Vr K v)"], assumption+,
       simp add:r_apow_def)
apply (frule val_noninf_n_val_noninf[of v "Ig K v I"],
       frule val_Ig[of v I], assumption,
       simp add:Ring.ideal_subset Vr_mem_f_mem, simp,
       frule value_n0_n_val_n0[of v "Ig K v I"],
       frule val_Ig[of v I], assumption,
       simp add:Ring.ideal_subset Vr_mem_f_mem, assumption)

apply (simp add:r_apow_def,
       rule ideal_pow_vp, assumption+,
       frule elem_nonzeroval_gen_proper[of v "Ig K v I"],
       frule val_Ig[of v I], assumption+, erule conjE,
       simp add:Ring.ideal_subset, assumption, simp add:Ig_generate_I)

apply (frule val_Ig[of v I], assumption+, erule conjE, simp,
       simp add:LI_infinity[of v I])
done

(* A note to the above lemma (in Corps).
  Let K be a field and v be a valuation. Let R be the valuaiton ring of v,
and let P be the maximal ideal of R. If I is an ideal of R such that I \<noteq> 0
and I \<noteq> R, then I = P^n. Here n = nat znt n_valuation K G a i v (I_gen
K v I)) which is nat of the integer part of the normal value of
(I_gen K v I).  Let b be a generator of I, then n = v (b) / v (p), where
p is a generator of P in R:
                           I = P \<^bsup>\<diamondsuit>R n\<^esup>

Here
          P = vp K v,
          R = Vr K v,
          b = Ig K v I,,
          n = nat n_val K v (Ig K v I).
It is easy to see that n = v\<^sup>* b. Here v\<^sup>* is the normal valuation derived from
v. *)

lemma (in Corps) ideal_apow_n_val:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>
                        (Vr K v) \<diamondsuit>\<^sub>p x = (vp K v)\<^bsup>(Vr K v) (n_val K v x)\<^esup>"
apply (frule Vr_ring[of v],
       frule Ring.principal_ideal[of "Vr K v" "x"], assumption+,
       frule ideal_apow_vp[of v "Vr K v \<diamondsuit>\<^sub>p x"], assumption+)
apply (frule val_Ig[of v "Vr K v \<diamondsuit>\<^sub>p x"], assumption+, erule conjE,
       frule Ring.ideal_subset[of "Vr K v" "Vr K v \<diamondsuit>\<^sub>p x"
             "Ig K v (Vr K v \<diamondsuit>\<^sub>p x)"], assumption+,
       frule Ig_generate_I[of v "Vr K v \<diamondsuit>\<^sub>p x"], assumption+)
apply (frule eq_ideal_eq_val[of v "Ig K v (Vr K v \<diamondsuit>\<^sub>p x)" x],
       assumption+,
       thin_tac "Vr K v \<diamondsuit>\<^sub>p Ig K v (Vr K v \<diamondsuit>\<^sub>p x) = Vr K v \<diamondsuit>\<^sub>p x",
       thin_tac "v (Ig K v (Vr K v \<diamondsuit>\<^sub>p x)) = LI K v (Vr K v \<diamondsuit>\<^sub>p x)",
       frule n_val[THEN sym, of v x],
       simp add:Vr_mem_f_mem, simp,
       thin_tac "v x = n_val K v x * Lv K v",
       frule n_val[THEN sym, of v "Ig K v (Vr K v \<diamondsuit>\<^sub>p x)"],
       simp add:Vr_mem_f_mem, simp,
       thin_tac "v (Ig K v (Vr K v \<diamondsuit>\<^sub>p x)) = n_val K v x * Lv K v")
apply (frule Lv_pos[of v],
       frule Lv_z[of v], erule exE, simp,
       frule_tac s = z in zless_neq[THEN not_sym, of "0"],
       frule_tac z = z in adiv_eq[of _ "n_val K v (Ig K v (Vr K v \<diamondsuit>\<^sub>p x))"
        "n_val K v x"], assumption+, simp)
done

lemma (in Corps) t_gen_vp:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1\<rbrakk> \<Longrightarrow>
                        (Vr K v) \<diamondsuit>\<^sub>p t = vp K v"
(*
apply (frule val_surj_n_val[of v], blast)
apply (frule ideal_apow_n_val[of v t])
apply (cut_tac a0_less_1)
apply (rule val_poss_mem_Vr[of v t], assumption+, simp)
apply (simp add:r_apow_def)
apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
apply (simp only:aeq_zeq, simp)
apply (cut_tac z_neq_inf[THEN not_sym, of "1"], simp)
apply (simp only:an_1[THEN sym]) apply (simp add:na_an)
apply (rule Ring.idealprod_whole_r[of "Vr K v" "vp K v"])
apply (simp add:Vr_ring)
apply (simp add:vp_ideal)
done *)

proof -
assume  a1:"valuation K v" and
        a2:"t \<in> carrier K" and
        a3:"v t = 1"
 from a1 and a2 and a3 have h1:"t \<in> carrier (Vr K v)"
          apply (cut_tac a0_less_1)
          apply (rule val_poss_mem_Vr[of v t], assumption+, simp) done
 from a1 and a2 and a3 have h2:"n_val K v = v"
          apply (subst val_surj_n_val[of v]) apply assumption
          apply blast  apply simp done
 from a1 and h1 have h3:"Vr K v \<diamondsuit>\<^sub>p t = vp K v\<^bsup> (Vr K v) (n_val K v t)\<^esup>"
          apply (simp add:ideal_apow_n_val[of v t]) done
 from a1 and a3 and h2 and h3 show ?thesis
        apply (simp add:r_apow_def)
        apply (simp only:ant_1[THEN sym], simp only:ant_0[THEN sym])
        apply (simp only:aeq_zeq, simp)
        apply (cut_tac z_neq_inf[THEN not_sym, of "1"], simp)
        apply (simp only:an_1[THEN sym]) apply (simp add:na_an)
        apply (rule Ring.idealprod_whole_r[of "Vr K v" "vp K v"])
        apply (simp add:Vr_ring)
        apply (simp add:vp_ideal) done
qed

lemma (in Corps) t_vp_apow:"\<lbrakk>valuation K v; t \<in> carrier K; v t = 1\<rbrakk> \<Longrightarrow>
                        (Vr K v) \<diamondsuit>\<^sub>p (t^\<^bsup>(Vr K v) n\<^esup>) = (vp K v)\<^bsup>(Vr K v) (an n)\<^esup>"
(*
apply (frule Vr_ring[of v],
       subst Ring.principal_ideal_n_pow[THEN sym, of "Vr K v" t "vp K v" n],
       assumption+)
apply (cut_tac a0_less_1, rule val_poss_mem_Vr[of v], assumption+)
apply (simp, simp add:t_gen_vp,
       simp add:r_apow_def)
 apply (rule conjI, rule impI,
        simp only:an_0[THEN sym], frule an_inj[of n 0], simp)
apply (rule impI)
 apply (rule conjI, rule impI)
 apply (simp add:an_def)
apply (rule impI, cut_tac an_nat_pos[of n], simp add:na_an)
done *)

proof -
assume  a1:"valuation K v" and
        a2:"t \<in> carrier K" and
        a3:"v t = 1"
from a1 have h1:"Ring (Vr K v)"  by (simp add:Vr_ring[of v])
from a1 and a2 and a3 have h2:"t \<in> carrier (Vr K v)"
        apply (cut_tac a0_less_1)
        apply (rule val_poss_mem_Vr) apply assumption+ apply simp done
from a1 and a2 and a3 and h1 and h2 show ?thesis
 apply (subst Ring.principal_ideal_n_pow[THEN sym, of "Vr K v" t "vp K v" n])
 apply assumption+
 apply (simp add:t_gen_vp)
 apply (simp add:r_apow_def)
 apply (rule conjI, rule impI,
        simp only:an_0[THEN sym], frule an_inj[of n 0], simp)
 apply (rule impI)
 apply (rule conjI, rule impI)
 apply (simp add:an_def)
 apply (rule impI, cut_tac an_nat_pos[of n], simp add:na_an)
done
qed

lemma (in Corps) nonzeroelem_gen_nonzero:"\<lbrakk>valuation K v; x \<noteq> \<zero>;
                 x \<in> carrier (Vr K v)\<rbrakk> \<Longrightarrow>  Vr K v \<diamondsuit>\<^sub>p x \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}"
by (frule Vr_ring[of v],
    frule_tac a = x in Ring.a_in_principal[of "Vr K v"], assumption+,
    rule contrapos_pp, simp+, simp add:Vr_0_f_0)

subsection "Amin lemma (in Corps)s "

lemma (in Corps)  Amin_le_addTr:"valuation K v \<Longrightarrow>
(\<forall>j \<le> n. f j \<in> carrier K) \<longrightarrow> Amin n (v \<circ> f) \<le> (v (nsum K f n))"
apply (induct_tac n)
 apply (rule impI, simp)

apply (rule impI,
       simp,
       frule_tac x = "\<Sigma>\<^sub>e K f n" and y = "f (Suc n)" in amin_le_plus[of v],
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       cut_tac n = n in aGroup.nsum_mem[of K _ f], assumption,
       rule allI, simp add:funcset_mem, assumption, simp)
 apply (frule_tac z = "Amin n (\<lambda>u. v (f u))" and z' = "v (\<Sigma>\<^sub>e K f n)" and
        w = "v (f (Suc n))" in amin_aminTr,
        rule_tac i = "amin (Amin n (\<lambda>u. v (f u))) (v (f (Suc n)))" and
        j = "amin (v (\<Sigma>\<^sub>e K f n)) (v (f (Suc n)))" and
        k = "v (\<Sigma>\<^sub>e K f n \<plusminus> (f (Suc n)))" in ale_trans, assumption+)
done

lemma (in Corps) Amin_le_add:"\<lbrakk>valuation K v; \<forall>j \<le> n. f j \<in> carrier K\<rbrakk> \<Longrightarrow>
                      Amin n (v \<circ> f) \<le> (v (nsum K f n))"
by (frule Amin_le_addTr[of v n f], simp)

lemma (in Corps) value_ge_add:"\<lbrakk>valuation K v; \<forall>j \<le> n. f j \<in> carrier K;
                     \<forall>j \<le> n. z \<le> ((v \<circ> f) j)\<rbrakk>  \<Longrightarrow> z \<le> (v (\<Sigma>\<^sub>e K f n))"
apply (frule Amin_le_add[of v n f], assumption+,
       cut_tac Amin_ge[of n "v \<circ> f" z],
       rule ale_trans, assumption+)
apply (rule allI, rule impI,
       simp add:comp_def Zset_def,
       rule value_in_aug_inf[of v], assumption+, simp+)
done

lemma (in Corps) Vr_ideal_powTr1:"\<lbrakk>valuation K v; ideal (Vr K v) I;
 I \<noteq> carrier (Vr K v); b \<in> I\<rbrakk>  \<Longrightarrow> b \<in> (vp K v)"
by (frule ideal_sub_vp[of v I], assumption+, simp add:subsetD)

section \<open>pow of vp and \<open>n_value\<close> -- convergence --\<close>

lemma (in Corps) n_value_x_1:"\<lbrakk>valuation K v; 0 \<le> n;
                    x \<in> (vp K v) \<^bsup>(Vr K v) n\<^esup>\<rbrakk> \<Longrightarrow>  n \<le> (n_val K v x)"
(* 1. prove that x \<in> carrier (Vr K v) and that x \<in> carrier K *)
apply ((case_tac "n = \<infinity>", simp add:r_apow_def,
        simp add:Vr_0_f_0, cut_tac field_is_ring,
        frule Ring.ring_zero[of "K"], frule val_inf_n_val_inf[of v \<zero>],
        assumption+, simp add:value_of_zero),
       (case_tac "n = 0", simp add:r_apow_def,
        subst val_pos_n_val_pos[THEN sym, of v x], assumption+,
        simp add:Vr_mem_f_mem,
        subst val_pos_mem_Vr[of v x], assumption+,
        simp add:Vr_mem_f_mem, assumption,
        simp add:r_apow_def, frule Vr_ring[of v],
        frule vp_pow_ideal[of v "na n"],
        frule Ring.ideal_subset[of "Vr K v" "(vp K v) \<^bsup>\<diamondsuit>(Vr K v) (na n)\<^esup>" x],
        assumption+, frule Vr_mem_f_mem[of v x], assumption+))
(* 1. done *)

(** 2. Show that
  v (I_gen K v (vpr K  v)^\<^sup>Vr K v\<^sup> \<^sup>nat n) \<le> v x.  the key lemma (in Corps)  is
 "val_Rxa_gt_a"                  **)

apply (case_tac "x = \<zero>\<^bsub>K\<^esub>", simp,
      frule value_of_zero[of v],
      simp add:val_inf_n_val_inf,
      simp add:n_value_idealTr[of v "na n"],

      frule val_Pg[of v], erule conjE, simp, erule conjE,
      frule Lv_pos[of v],
      rotate_tac -4, frule sym, thin_tac "v (Pg K v) = Lv K v", simp,
      frule val_poss_mem_Vr[of v "Pg K v"], assumption+,
      frule val_Rxa_gt_a[of v "Pg K v^\<^bsup>(Vr K v) (na n)\<^esup>" x],

      frule Vr_integral[of v],
      simp only:Vr_0_f_0[of v, THEN sym],
      frule Idomain.idom_potent_nonzero[of "Vr K v" "Pg K v" "na n"],
      assumption+, simp, simp add:Ring.npClose, assumption+)

apply (thin_tac "x \<in> Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>(Vr K v) (na n)\<^esup>)",
       thin_tac "ideal (Vr K v) (Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>(Vr K v) (na n)\<^esup>))")

apply (simp add:Vr_exp_f_exp[of v "Pg K v"],
       simp add:val_exp_ring[THEN sym, of v "Pg K v"],
       simp add:n_val[THEN sym, of v x],
       frule val_nonzero_z[of v "Pg K v"], assumption+,
         erule exE, simp,
       frule aposs_na_poss[of "n"], simp add: less_le,
       simp add:asprod_amult,

       frule_tac w = z in amult_pos_mono_r[of _ "ant (int (na n))"
                   "n_val K v x"], simp,
       cut_tac an_na[of "n"], simp add:an_def, assumption+)
done

lemma (in Corps) n_value_x_1_nat:"\<lbrakk>valuation K v; x \<in> (vp K v)\<^bsup>\<diamondsuit>(Vr K v) n\<^esup> \<rbrakk> \<Longrightarrow>
             (an n) \<le> (n_val K v x)"
apply (cut_tac an_nat_pos[of "n"])
apply( frule n_value_x_1[of  "v" "an n" "x"], assumption+)
apply (simp add:r_apow_def)
apply (case_tac "n = 0", simp, simp)
apply (cut_tac aless_nat_less[THEN sym, of "0" "n"])
apply simp
unfolding less_le
apply simp
apply (cut_tac an_neq_inf [of "n"])
apply simp
apply (simp add: na_an)
apply assumption
done

lemma (in Corps) n_value_x_2:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
        n \<le> (n_val K v x);  0 \<le> n\<rbrakk> \<Longrightarrow>  x \<in> (vp K v) \<^bsup>(Vr K v) n\<^esup>"
apply (frule Vr_ring[of v],
       frule val_Pg[of v], erule conjE,
       simp, erule conjE, drule sym,
       frule Lv_pos[of v], simp,
       frule val_poss_mem_Vr[of v "Pg K v"], assumption+)

apply (case_tac "n = \<infinity>",
       simp add:r_apow_def, cut_tac inf_ge_any[of "n_val K v x"],
       frule ale_antisym[of "n_val K v x" "\<infinity>"], assumption+,
       frule val_inf_n_val_inf[THEN sym, of v "x"],
       simp add:Vr_mem_f_mem, simp,
       frule value_inf_zero[of v x],
       simp add:Vr_mem_f_mem, simp+, simp add:Vr_0_f_0)

apply (case_tac "n = 0",
       simp add:r_apow_def,
       simp add:r_apow_def,
       subst n_value_idealTr[of v "na n"], assumption+,
       simp add:apos_na_pos)
apply (rule val_Rxa_gt_a_1[of v "Pg K v^\<^bsup>(Vr K v) (na n)\<^esup>" x],
            assumption+,
       rule Ring.npClose, assumption+,
       simp add:Vr_0_f_0[THEN sym, of v],
       frule Vr_integral[of v],
       frule val_poss_mem_Vr[of v "Pg K v"], assumption+,
       simp add:Idomain.idom_potent_nonzero)

apply (simp add:Vr_exp_f_exp,
      simp add:val_exp_ring[THEN sym, of v],
      rotate_tac -5, drule sym,
      frule Lv_z[of v], erule exE, simp,
      frule aposs_na_poss[of "n"], simp add: less_le,
      simp add:asprod_amult, subst n_val[THEN sym, of v x],
      assumption+,
      simp add:Vr_mem_f_mem, simp,
      subst amult_pos_mono_r[of _ "ant (int (na n))" "n_val K v x"],
         assumption,
      cut_tac an_na[of "n"], simp add:an_def, assumption+)
done



lemma (in Corps) n_value_x_2_nat:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
      (an n) \<le> ((n_val K v) x)\<rbrakk> \<Longrightarrow>  x \<in> (vp K v)\<^bsup>\<diamondsuit>(Vr K  v)  n\<^esup>"
by (frule n_value_x_2[of v x "an n"], assumption+,
       simp, simp add:r_apow_def,
       case_tac "an n = \<infinity>", simp add:an_def, simp,
       case_tac "n = 0", simp,
       subgoal_tac "an n \<noteq> 0", simp, simp add:na_an,
       rule contrapos_pp, simp+, simp add:an_def)

lemma (in Corps) n_val_n_pow:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v); 0 \<le> n\<rbrakk> \<Longrightarrow>
         (n \<le> (n_val K v x)) = (x \<in> (vp K v) \<^bsup>(Vr K v)  n\<^esup>)"
by (rule iffI, simp add:n_value_x_2, simp add:n_value_x_1)

lemma (in Corps) eqval_in_vpr_apow:"\<lbrakk>valuation K v; x \<in> carrier K; 0 \<le> n;
      y \<in> carrier K; n_val K v x = n_val K v y; x \<in> (vp K v)\<^bsup>(Vr K v) n\<^esup>\<rbrakk> \<Longrightarrow>
      y \<in> (vp K v) \<^bsup>(Vr K v) n\<^esup>"
apply (frule n_value_x_1[of v n x], assumption+, simp,
       rule n_value_x_2[of v y n], assumption+,
       frule mem_vp_apow_mem_Vr[of v n x], assumption+)
apply (frule val_pos_mem_Vr[THEN sym, of v x], assumption+, simp,
       simp add:val_pos_n_val_pos[of v x],
       simp add:val_pos_n_val_pos[THEN sym, of v y],
       simp add:val_pos_mem_Vr, assumption+)
done

lemma (in Corps) convergenceTr:"\<lbrakk>valuation K v; x \<in> carrier K; b \<in> carrier K;
  b \<in> (vp K v)\<^bsup>(Vr K v) n\<^esup>; (Abs (n_val K v x)) \<le> n\<rbrakk> \<Longrightarrow>
                x \<cdot>\<^sub>r b \<in> (vp K v)\<^bsup>(Vr K v) (n + (n_val K v x))\<^esup>"
(** Valuation ring is a ring **)
apply (cut_tac Abs_pos[of "n_val K v x"],
       frule ale_trans[of "0" "Abs (n_val K v x)" "n"], assumption+,
       thin_tac "0 \<le> Abs (n_val K v x)")
apply (frule Vr_ring[of v],
       frule_tac aadd_le_mono[of "Abs (n_val K v x)" "n" "n_val K v x"],
       cut_tac Abs_x_plus_x_pos[of "n_val K v x"],
       frule ale_trans[of "0" "Abs (n_val K v x) + n_val K v x"
        "n + n_val K v x"], assumption+,
       thin_tac "0 \<le> Abs (n_val K v x) + n_val K v x",
       thin_tac "Abs (n_val K v x) + n_val K v x \<le> n + n_val K v x",
       rule n_value_x_2[of v "x \<cdot>\<^sub>r b" "n + n_val K v x"], assumption+)
apply (frule n_value_x_1[of v n b], assumption+)
 apply (frule aadd_le_mono[of "n" "n_val K v b" "n_val K v x"],
       frule ale_trans[of "0" "n + n_val K v x" "n_val K v b + n_val K v x"],
       assumption)
 apply (thin_tac "0 \<le> n + n_val K v x",
        thin_tac "n \<le> n_val K v b",
        thin_tac "n + n_val K v x \<le> n_val K v b + n_val K v x",
       simp add:aadd_commute[of "n_val K v b" "n_val K v x"])
apply (frule n_val_valuation[of v],
       simp add:val_t2p[THEN sym, of "n_val K v" x b],
       cut_tac field_is_ring,
       frule Ring.ring_tOp_closed[of "K" "x" "b"], assumption+,
       simp add:val_pos_n_val_pos[THEN sym, of v "x \<cdot>\<^sub>r b"],
       simp add:val_pos_mem_Vr,
       frule n_val_valuation[of v],
       subst val_t2p[of "n_val K v"], assumption+,
       frule n_value_x_1[of v n b], assumption+,
       simp add:aadd_commute[of "n_val K v x" "n_val K v b"],
       rule aadd_le_mono[of n "n_val K v b" "n_val K v x"], assumption+)
done

lemma (in Corps) convergenceTr1:"\<lbrakk>valuation K v; x \<in> carrier K;
      b \<in> (vp K v)\<^bsup>(Vr K v) (n + Abs (n_val K v x))\<^esup>; 0 \<le> n\<rbrakk> \<Longrightarrow>
                                 x \<cdot>\<^sub>r b \<in> (vp K v) \<^bsup>(Vr K v) n\<^esup>"
apply (cut_tac field_is_ring,
       frule Vr_ring[of v],
       frule vp_apow_ideal[of v "n + Abs (n_val K v x)"],
       cut_tac Abs_pos[of "n_val K v x"],
       rule aadd_two_pos[of "n" "Abs (n_val K v x)"], assumption+)

apply (frule Ring.ideal_subset[of "Vr K v" "vp K v\<^bsup> (Vr K v) (n + Abs (n_val K v x))\<^esup>"
        "b"], assumption+,
       frule Vr_mem_f_mem[of v b], assumption,
       frule convergenceTr[of v x b "n +  Abs (n_val K v x)"], assumption+,
       rule aadd_pos_le[of "n" "Abs (n_val K v x)"], assumption)

apply (frule  apos_in_aug_inf[of "n"],
       cut_tac Abs_pos[of "n_val K v x"],
       frule apos_in_aug_inf[of "Abs (n_val K v x)"],
       frule n_value_in_aug_inf[of v x], assumption+,
       frule aadd_assoc_i[of "n" "Abs (n_val K v x)" "n_val K v x"],
              assumption+,
       cut_tac Abs_x_plus_x_pos[of "n_val K v x"])

apply (frule_tac Ring.ring_tOp_closed[of K x b], assumption+,
       rule n_value_x_2[of v "x \<cdot>\<^sub>r b" n], assumption+)

apply (subst val_pos_mem_Vr[THEN sym, of v "x \<cdot>\<^sub>r b"], assumption+,
       subst val_pos_n_val_pos[of v "x \<cdot>\<^sub>r b"], assumption+)

apply (frule n_value_x_1[of "v" "n + Abs(n_val K v x) + n_val K v x" "x \<cdot>\<^sub>r b"],
       subst aadd_assoc_i, assumption+,
       rule aadd_two_pos[of "n"], assumption+,
       rule ale_trans[of "0" "n + Abs (n_val K v x) + n_val K v x"
                "n_val K v (x \<cdot>\<^sub>r b)"],
       simp, simp add:aadd_two_pos, assumption,
       frule n_value_x_1[of "v" "n + Abs (n_val K v x)" " b"],
       cut_tac Abs_pos[of "n_val K v x"],
       rule aadd_two_pos[of "n" "Abs (n_val K v x)"], assumption+)

apply (frule n_val_valuation[of v],
        subst val_t2p[of  "n_val K v"], assumption+)
apply (frule aadd_le_mono[of "n + Abs (n_val K v x)" "n_val K v b"
                              "n_val K v x"],
        simp add:aadd_commute[of "n_val K v b" "n_val K v x"],
        rule ale_trans[of "n" "n + (Abs (n_val K v x) + n_val K v x)"
           "n_val K v x + n_val K v b"],
        frule aadd_pos_le[of "Abs (n_val K v x) + n_val K v x" "n"],
        simp add:aadd_commute[of "n"], assumption+)
done

lemma (in Corps) vp_potent_zero:"\<lbrakk>valuation K v; 0 \<le> n\<rbrakk> \<Longrightarrow>
             (n = \<infinity>) = (vp K v \<^bsup>(Vr K v) n\<^esup> = {\<zero>\<^bsub>Vr K v\<^esub>})"
apply (rule iffI)
apply (simp add:r_apow_def, rule contrapos_pp, simp+,
       frule apos_neq_minf[of "n"],
       cut_tac mem_ant[of "n"], simp, erule exE, simp,
       simp add:ant_0[THEN sym], thin_tac "n = ant z")

apply (case_tac "z = 0", simp add:ant_0, simp add:r_apow_def,
       frule Vr_ring[of v],
       frule Ring.ring_one[of "Vr K v"], simp,
       simp add:Vr_0_f_0, simp add:Vr_1_f_1,
       frule value_of_one[of v], simp, simp add:value_of_zero,
       cut_tac n = z in zneq_aneq[of _ "0"], simp only:ant_0)
apply (simp add:r_apow_def,
       frule_tac n = "na (ant z)" in n_value_idealTr[of v],
       simp add:na_def,
       simp, thin_tac "vp K v \<^bsup>\<diamondsuit>(Vr K v) (na (ant z))\<^esup> = {\<zero>\<^bsub>Vr K v\<^esub>}",
       frule Vr_ring[of v],
       frule  Pg_in_Vr[of v],
       frule_tac n = "na (ant z)" in Ring.npClose[of "Vr K v" "Pg K v"],
       assumption)
apply (frule_tac a = "(Pg K v)^\<^bsup>(Vr K v) (na (ant z))\<^esup>" in
                   Ring.a_in_principal[of "Vr K v"], assumption,
       simp, frule Vr_integral[of "v"],
       frule val_Pg[of v], simp, (erule conjE)+,
       frule_tac n = "na (ant z)" in Idomain.idom_potent_nonzero[of "Vr K v"
        "Pg K v"], assumption+,
       simp add:Vr_0_f_0, simp)
done

lemma (in Corps) Vr_potent_eqTr1:"\<lbrakk>valuation K v; 0 \<le> n; 0 \<le> m;
        (vp K v) \<^bsup>(Vr K v) n\<^esup> = (vp K v) \<^bsup>(Vr K v) m\<^esup>; m = 0\<rbrakk>  \<Longrightarrow>  n = m"
(*** compare the value of the generator of each ideal ***)
(** express each ideal as a principal ideal **)
apply (frule Vr_ring[of v],
       simp add:r_apow_def,
       case_tac "n = 0", simp,
       case_tac "n = \<infinity>", simp,
       frule val_Pg[of v], erule conjE, simp,
       erule conjE,
       rotate_tac -3, drule sym,
       frule Lv_pos[of v], simp,
       frule val_poss_mem_Vr[of v "Pg K v"], assumption+,
       drule sym, simp, simp add:Vr_0_f_0)

apply (simp,
       drule sym,
       frule Ring.ring_one[of "Vr K v"], simp,

       frule n_value_x_1_nat[of v "1\<^sub>r\<^bsub>(Vr K v)\<^esub>" "na n"], assumption,
       simp add:an_na, simp add:Vr_1_f_1,
       frule n_val_valuation[of v],
       simp add:value_of_one[of "n_val K v"])
done

lemma (in Corps) Vr_potent_eqTr2:"\<lbrakk>valuation K v;
        (vp K v) \<^bsup>\<diamondsuit>(Vr K v) n\<^esup> = (vp K v) \<^bsup>\<diamondsuit>(Vr K v) m\<^esup>\<rbrakk>  \<Longrightarrow>   n = m"

(** 1. express each ideal as a principal ideal **)
apply (frule Vr_ring[of v],
       frule val_Pg[of v], simp, (erule conjE)+,
       rotate_tac -1, frule sym, thin_tac "v (Pg K v) = Lv K v",
       frule Lv_pos[of v], simp)

apply (subgoal_tac "0 \<le> int n", subgoal_tac "0 \<le> int m",
       frule n_value_idealTr[of "v" "m"]) apply simp apply simp
 apply(
       thin_tac "vp K v \<^bsup>\<diamondsuit>(Vr K v) m\<^esup> = Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>(Vr K v) m\<^esup>)",
       frule n_value_idealTr[of "v" "n"], simp, simp,
       thin_tac "vp K v \<^bsup>\<diamondsuit>(Vr K v) n\<^esup> = Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>(Vr K v) m\<^esup>)",
       frule val_poss_mem_Vr[of  "v" "Pg K v"], assumption+)

(** 2. the value of generators should coincide **)
 apply (frule Lv_z[of v], erule exE,
        rotate_tac -4, drule sym, simp,
        frule eq_ideal_eq_val[of "v" "Pg K v^\<^bsup>(Vr K v) n\<^esup>" "Pg K v^\<^bsup>(Vr K v) m\<^esup>"])
 apply (rule Ring.npClose, assumption+, rule Ring.npClose, assumption+)
 apply (simp only:Vr_exp_f_exp,
        simp add:val_exp_ring[THEN sym, of v "Pg K v"],
        thin_tac "Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>K n\<^esup>) = Vr K v \<diamondsuit>\<^sub>p (Pg K v^\<^bsup>K m\<^esup>)")

apply (case_tac "n = 0", simp, case_tac "m = 0", simp,
       simp only:of_nat_0_less_iff[THEN sym, of "m"],
       simp only:asprod_amult a_z_z,
       simp only:ant_0[THEN sym], simp only:aeq_zeq, simp)
apply (auto simp add: asprod_mult)
done

lemma (in Corps) Vr_potent_eq:"\<lbrakk>valuation K v; 0 \<le> n; 0 \<le> m;
              (vp K v) \<^bsup>(Vr K v) n\<^esup> = (vp K v) \<^bsup>(Vr K v) m\<^esup>\<rbrakk> \<Longrightarrow>  n = m"
apply (frule n_val_valuation[of v],
       case_tac "m = 0",
       simp add:Vr_potent_eqTr1)
apply (case_tac "n = 0",
       frule sym, thin_tac "vp K v\<^bsup> (Vr K v) n\<^esup> = vp K v\<^bsup> (Vr K v) m\<^esup>",
       frule Vr_potent_eqTr1[of v m n], assumption+,
       rule sym, assumption,
       frule vp_potent_zero[of  "v" "n"], assumption+)
apply (case_tac "n = \<infinity>", simp,
       thin_tac "vp K v\<^bsup> (Vr K v) \<infinity>\<^esup> = {\<zero>\<^bsub>Vr K v\<^esub>}",
       frule vp_potent_zero[THEN sym, of v m], assumption+, simp,
       simp,
       frule vp_potent_zero[THEN sym, of v "m"], assumption+, simp,
       thin_tac "vp K v\<^bsup> (Vr K v) m\<^esup> \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}")

apply (frule aposs_na_poss[of "n"], subst less_le, simp,
       frule aposs_na_poss[of "m"], subst less_le, simp,
       simp add:r_apow_def,
       frule Vr_potent_eqTr2[of  "v" "na n" "na m"], assumption+,
       thin_tac "vp K v \<^bsup>\<diamondsuit>(Vr K v) (na n)\<^esup> = vp K v \<^bsup>\<diamondsuit>(Vr K v) (na m)\<^esup>",
       simp add:aeq_nat_eq[THEN sym])
done

text\<open>the following two lemma (in Corps) s are used in completion of K\<close>

lemma (in Corps) Vr_prime_maximalTr1:"\<lbrakk>valuation K v; x \<in> carrier (Vr K v);
       Suc 0 < n\<rbrakk>  \<Longrightarrow> x \<cdot>\<^sub>r\<^bsub>(Vr K v)\<^esub> (x^\<^bsup>K (n - Suc 0)\<^esup>) \<in> (Vr K v) \<diamondsuit>\<^sub>p (x^\<^bsup>K n\<^esup>)"
apply (frule Vr_ring[of v],
       subgoal_tac "x^\<^bsup>K n\<^esup> = x^\<^bsup>K (Suc (n - Suc 0))\<^esup>",
       simp del:Suc_pred,
       rotate_tac -1, drule sym)
apply (subst Vr_tOp_f_tOp, assumption+,
       subst Vr_exp_f_exp[of v, THEN sym], assumption+,
       simp only:Ring.npClose, simp del:Suc_pred)
 apply (cut_tac field_is_ring,
       frule Ring.npClose[of K x "n - Suc 0"],
       frule Vr_mem_f_mem[of v x], assumption+,
       frule Vr_mem_f_mem[of v x], assumption+)
       apply (simp add:Ring.ring_tOp_commute[of K x "x^\<^bsup>K (n - Suc 0)\<^esup>"])
 apply (rule Ring.a_in_principal, assumption)
 apply (frule Ring.npClose[of "Vr K v" x n], assumption,
        simp add:Vr_exp_f_exp)
 apply (simp only:Suc_pred)
done

lemma (in Corps) Vr_prime_maximalTr2:"\<lbrakk> valuation K v; x \<in> vp K v; x \<noteq> \<zero>;
  Suc 0 < n\<rbrakk> \<Longrightarrow> x \<notin> Vr K v \<diamondsuit>\<^sub>p (x^\<^bsup>K n\<^esup>) \<and> x^\<^bsup>K (n - Suc 0)\<^esup> \<notin> (Vr K v) \<diamondsuit>\<^sub>p (x^\<^bsup>K n\<^esup>)"
apply (frule Vr_ring[of v])
apply (frule vp_mem_Vr_mem[of v x], assumption,
       frule Ring.npClose[of "Vr K v" x n],
       simp only:Vr_exp_f_exp)
apply (cut_tac field_is_ring,
       cut_tac field_is_idom,
       frule Vr_mem_f_mem[of v x], assumption+,
       frule Idomain.idom_potent_nonzero[of K x n], assumption+)
apply (rule conjI)
 apply (rule contrapos_pp, simp+)
 apply (frule val_Rxa_gt_a[of v "x^\<^bsup>K n\<^esup>" x],
        simp, simp add:Vr_exp_f_exp, assumption+)
 apply (simp add:val_exp_ring[THEN sym, of v x n])
 apply (frule val_nonzero_z[of v x], assumption+, erule exE,
        simp add:asprod_amult a_z_z)
 apply (simp add:vp_mem_val_poss[of v x])
apply (rule contrapos_pp, simp+)
apply (frule val_Rxa_gt_a[of v "x^\<^bsup>K n\<^esup>" "x^\<^bsup>K (n - Suc 0)\<^esup>"])
   apply (simp, frule Ring.npClose[of "Vr K v" "x" "n - Suc 0"], assumption+)
   apply (simp add:Vr_exp_f_exp)
  apply (frule Ring.npClose[of "Vr K v" "x" "n - Suc 0"], assumption+,
        simp add:Vr_exp_f_exp, assumption)
apply (simp add:val_exp_ring[THEN sym, of v x])
apply (simp add:vp_mem_val_poss[of "v" "x"])
apply (frule val_nonzero_z[of  "v" "x"], assumption+, erule exE,
        simp add:asprod_amult a_z_z)
done

lemma (in Corps) Vring_prime_maximal:"\<lbrakk>valuation K v; prime_ideal (Vr K v) I;
      I \<noteq> {\<zero>\<^bsub>Vr K v\<^esub>}\<rbrakk> \<Longrightarrow> maximal_ideal (Vr K v) I"
apply (frule Vr_ring[of v],
       frule Ring.prime_ideal_proper[of "Vr K v" "I"], assumption+,
       frule Ring.prime_ideal_ideal[of "Vr K v" "I"], assumption+,
       frule ideal_pow_vp[of v I],
       frule n_value_idealTr[of "v" "na (n_val K v (Ig K v I))"],
                  simp, simp, assumption+)

apply (case_tac "na (n_val K v (Ig K v I)) = 0",
       simp, frule Ring.Rxa_one[of "Vr K v"], simp,
       frule Suc_leI[of "0" "na (n_val K v (Ig K v I))"],
       thin_tac "0 < na (n_val K v (Ig K v I))")
apply (case_tac "na (n_val K v (Ig K v I)) = Suc 0", simp,
       frule Pg_in_Vr[of v])
apply (frule vp_maximal[of v],
       frule Ring.maximal_ideal_ideal[of "Vr K v" "vp K v"], assumption+,
       subst Ring.idealprod_whole_r[of "Vr K v" "vp K v"], assumption+)

apply (rotate_tac -1, drule not_sym,
       frule le_neq_implies_less[of "Suc 0" "na (n_val K v (Ig K v I))"],
       assumption+,
       thin_tac "Suc 0 \<le> na (n_val K v (Ig K v I))",
       thin_tac "Suc 0 \<noteq> na (n_val K v (Ig K v I))",
       thin_tac "Vr K v \<diamondsuit>\<^sub>p 1\<^sub>r\<^bsub>Vr K v\<^esub> = carrier (Vr K v)")
apply (frule val_Pg[of v], simp, (erule conjE)+,
       frule Lv_pos[of v], rotate_tac -2, drule sym)
 apply (frule val_poss_mem_Vr[of "v" "Pg K v"],
        frule vp_mem_val_poss[THEN sym, of "v" "Pg K v"], assumption+, simp)

apply (frule Vr_prime_maximalTr2[of v "Pg K v"
                            "na (n_val K v (Ig K v I))"],
       simp add:vp_mem_val_poss[of v "Pg K v"], assumption+, erule conjE)
apply (frule Ring.npMulDistr[of "Vr K v" "Pg K v" "na 1" "na (n_val K v (Ig K v I)) - Suc 0"], assumption+, simp add:na_1)

apply (rotate_tac 8, drule sym)
apply (frule Ring.a_in_principal[of "Vr K v"
         "Pg K v^\<^bsup>(Vr K v) (na (n_val K v (Ig K v I)))\<^esup>"], simp add:Ring.npClose)

apply (simp add:Vr_exp_f_exp[of "v"])
    apply (simp add:Ring.ring_l_one[of "Vr K v"])
    apply (frule n_value_idealTr[THEN sym,
                       of v "na (n_val K v (Ig K v I))"], simp)
    apply (simp add:Vr_exp_f_exp)
    apply (rotate_tac 6, drule sym, simp)
apply (thin_tac "I \<noteq> carrier (Vr K v)",
   thin_tac "I = vp K v \<^bsup>\<diamondsuit>(Vr K v) (na (n_val K v (Ig K v I)))\<^esup>",
   thin_tac "v (Pg K v) = Lv K v",
 thin_tac "(Vr K v) \<diamondsuit>\<^sub>p ((Pg K v) \<cdot>\<^sub>r\<^bsub>(Vr K v)\<^esub>
                   ((Pg K v)^\<^bsup>K (na ((n_val K v) (Ig K v I)) - (Suc 0))\<^esup>)) =
    I",
   thin_tac "Pg K v \<in> carrier K",
   thin_tac "Pg K v \<noteq> \<zero>",
   thin_tac "Pg K v^\<^bsup>K (na ((n_val K v) (Ig K v I)))\<^esup> =
     Pg K v \<cdot>\<^sub>r\<^bsub>Vr K v\<^esub> Pg K v^\<^bsup>K ((na ((n_val K v) (Ig K v I))) - Suc 0)\<^esup>")


apply (simp add:prime_ideal_def, erule conjE,
      drule_tac x = "Pg K v" in bspec, assumption,
      drule_tac x = "Pg K v^\<^bsup>K (na (n_val K v (Ig K v I)) - Suc 0)\<^esup> " in bspec)
      apply (simp add:Vr_exp_f_exp[THEN sym, of v])
apply (rule Ring.npClose[of "Vr K v" "Pg K v"], assumption+)
apply simp
done

text\<open>From the above lemma (in Corps) , we see that a valuation ring is of dimension one.\<close>

lemma (in Corps) field_frac1:"\<lbrakk>1\<^sub>r \<noteq> \<zero>; x \<in> carrier K\<rbrakk> \<Longrightarrow> x = x \<cdot>\<^sub>r ((1\<^sub>r)\<^bsup>\<hyphen>K\<^esup>)"
by (simp add:invf_one,
       cut_tac field_is_ring,
       simp add:Ring.ring_r_one[THEN sym])

lemma (in Corps) field_frac2:"\<lbrakk>x \<in> carrier K; x \<noteq> \<zero>\<rbrakk> \<Longrightarrow> x = (1\<^sub>r) \<cdot>\<^sub>r ((x\<^bsup>\<hyphen>K\<^esup>)\<^bsup>\<hyphen>K\<^esup>)"
by (cut_tac field_is_ring, simp add:field_inv_inv,
       simp add:Ring.ring_l_one[THEN sym])

lemma (in Corps) val_nonpos_inv_pos:"\<lbrakk>valuation K v; x \<in> carrier K;
        \<not> 0 \<le> (v x)\<rbrakk>  \<Longrightarrow> 0 < (v (x\<^bsup>\<hyphen>K\<^esup>))"
by (case_tac "x = \<zero>\<^bsub>K\<^esub>", simp add:value_of_zero,
       frule Vr_ring[of v],
       simp add:aneg_le[of "0" "v x"],
       frule value_of_inv[THEN sym, of v x], assumption+,
       frule aless_minus[of "v x" "0"], simp)

lemma (in Corps) frac_Vr_is_K:"\<lbrakk>valuation K v; x \<in> carrier K\<rbrakk> \<Longrightarrow>
 \<exists>s\<in>carrier (Vr K v). \<exists>t\<in>carrier (Vr K v) - {\<zero>}. x = s \<cdot>\<^sub>r (t\<^bsup>\<hyphen>K\<^esup>)"
apply (frule Vr_ring[of v],
       frule has_val_one_neq_zero[of v])
apply (case_tac "x = \<zero>\<^bsub>K\<^esub>",
       frule Ring.ring_one[of "Vr K v"],
       frule field_frac1[of x],
       simp only:Vr_1_f_1, frule Ring.ring_zero[of "Vr K v"],
       simp add:Vr_0_f_0 Vr_1_f_1, blast)
apply (case_tac "0 \<le> (v x)",
       frule val_pos_mem_Vr[THEN sym, of v x], assumption+, simp,
       frule field_frac1[of x], assumption+,
       frule has_val_one_neq_zero[of v],
       frule Ring.ring_one[of "Vr K v"], simp only:Vr_1_f_1, blast)
apply (frule val_nonpos_inv_pos[of v x], assumption+,
       cut_tac invf_inv[of x], erule conjE,
       frule val_poss_mem_Vr[of v "x\<^bsup>\<hyphen>K\<^esup>"], assumption+)
apply (frule Ring.ring_one[of "Vr K v"], simp only:Vr_1_f_1,
       frule field_frac2[of x], assumption+)
apply (cut_tac invf_closed1[of x], blast, simp+)
done

lemma (in Corps) valuations_eqTr1:"\<lbrakk>valuation K v; valuation K v';
 Vr K v = Vr K v'; \<forall>x\<in>carrier (Vr K v). v x = v' x\<rbrakk> \<Longrightarrow> v = v'"
apply (rule funcset_eq [of _  "carrier K"],
       simp add:valuation_def, simp add:valuation_def,
       rule ballI,
       frule_tac x = x in frac_Vr_is_K[of v], assumption+,
        (erule bexE)+, simp, erule conjE)
apply (frule_tac x = t in Vr_mem_f_mem[of v'], assumption,
       cut_tac x = t in invf_closed1, simp, simp, erule conjE)
 apply (frule_tac x = s in Vr_mem_f_mem[of "v'"], assumption+,
       simp add:val_t2p, simp add:value_of_inv)
done

lemma (in Corps) ridmap_rhom:"\<lbrakk> valuation K v; valuation K v';
 carrier (Vr K v) \<subseteq> carrier (Vr K v')\<rbrakk> \<Longrightarrow>
      ridmap (Vr K v) \<in> rHom (Vr K v) (Vr K v')"
apply (frule Vr_ring[of "v"], frule Vr_ring[of "v'"],
       subst rHom_def, simp, rule conjI)
apply (simp add:aHom_def, rule conjI,
       rule Pi_I, simp add:ridmap_def subsetD,
       simp add:ridmap_def restrict_def extensional_def,
       (rule ballI)+,
       frule Ring.ring_is_ag[of "Vr K v"], simp add:aGroup.ag_pOp_closed,
        simp add:Vr_pOp_f_pOp subsetD)
apply (rule conjI, (rule ballI)+, simp add:ridmap_def,
       simp add:Ring.ring_tOp_closed, simp add:Vr_tOp_f_tOp subsetD,
      frule Ring.ring_one[of "Vr K v"], frule Ring.ring_one[of "Vr K v'"],
      simp add:Vr_1_f_1, simp add:ridmap_def )
done

lemma (in Corps) contract_ideal:"\<lbrakk>valuation K v; valuation K v';
                 carrier (Vr K v) \<subseteq> carrier (Vr K v')\<rbrakk> \<Longrightarrow>
                       ideal (Vr K v) (carrier (Vr K v) \<inter> vp K v')"
apply (frule_tac ridmap_rhom[of "v" "v'"], assumption+,
      frule Vr_ring[of "v"], frule Vr_ring[of "v'"])
apply (cut_tac TwoRings.i_contract_ideal[of "Vr K v" "Vr K v'"
        "ridmap (Vr K v)" "vp K v'"],
       subgoal_tac "(i_contract (ridmap (Vr K v)) (Vr K v) (Vr K v')
                      (vp K v')) = (carrier (Vr K v) \<inter> vp K v')")
       apply simp
apply(thin_tac "ideal (Vr K v) (i_contract (ridmap (Vr K v))
            (Vr K v) (Vr K v') (vp K v'))",
       simp add:i_contract_def invim_def ridmap_def, blast)
apply (simp add:TwoRings_def TwoRings_axioms_def, simp)
 apply (simp add:vp_ideal)
done

lemma (in Corps) contract_prime:"\<lbrakk>valuation K v; valuation K v';
      carrier (Vr K v) \<subseteq> carrier (Vr K v')\<rbrakk>  \<Longrightarrow>
      prime_ideal (Vr K v) (carrier (Vr K v) \<inter> vp K v')"
apply (frule_tac ridmap_rhom[of "v" "v'"], assumption+,
     frule Vr_ring[of "v"],
     frule Vr_ring[of "v'"],
     cut_tac TwoRings.i_contract_prime[of "Vr K v" "Vr K v'" "ridmap (Vr K v)"
        "vp K v'"])
apply (subgoal_tac "(i_contract (ridmap (Vr K v)) (Vr K v) (Vr K v')
          (vp K v')) = (carrier (Vr K v) \<inter> vp K v')",
      simp,
      thin_tac "prime_ideal (Vr K v) (i_contract
       (ridmap (Vr K v))  (Vr K  v) (Vr K v') (vp K v'))",
      simp add:i_contract_def invim_def ridmap_def, blast)
apply (simp add:TwoRings_def TwoRings_axioms_def, simp)
apply (simp add:vp_prime)
done

(* \<forall>x\<in>carrier K. 0 \<le> (v x) \<longrightarrow> 0 \<le> (v' x) *)
lemma (in Corps) valuation_equivTr:"\<lbrakk>valuation K v; valuation K v';
      x \<in> carrier K;  0 < (v' x); carrier (Vr K v) \<subseteq> carrier (Vr K v')\<rbrakk>
      \<Longrightarrow> 0 \<le> (v x)"
apply (rule contrapos_pp, simp+,
       frule val_nonpos_inv_pos[of "v" "x"], assumption+,
       case_tac "x = \<zero>\<^bsub>K\<^esub>", simp add:value_of_zero[of "v"]) apply (
       cut_tac invf_closed1[of  "x"], simp, erule conjE,
       frule aless_imp_le[of "0" "v (x\<^bsup>\<hyphen>K\<^esup>)"])
apply (simp add:val_pos_mem_Vr[of v "x\<^bsup>\<hyphen>K\<^esup>"],
      frule subsetD[of "carrier (Vr K v)" "carrier (Vr K v')" "x\<^bsup>\<hyphen>K\<^esup>"],
      assumption+,
      frule val_pos_mem_Vr[THEN sym, of "v'" "x\<^bsup>\<hyphen>K\<^esup>"], assumption+)
apply (simp, simp add:value_of_inv[of "v'" "x"],
       cut_tac ale_minus[of "0" "- v' x"], thin_tac "0 \<le> - v' x",
       simp only:a_minus_minus,
       cut_tac aneg_less[THEN sym, of "v' x" "- 0"], simp,
       assumption, simp)
done

lemma (in Corps) contract_maximal:"\<lbrakk>valuation K v; valuation K v';
  carrier (Vr K v) \<subseteq> carrier (Vr K v')\<rbrakk> \<Longrightarrow>
  maximal_ideal (Vr K v) (carrier (Vr K v) \<inter> vp K v')"
apply (frule Vr_ring[of "v"],
       frule Vr_ring[of "v'"],
       rule Vring_prime_maximal, assumption+,
       simp add:contract_prime)
apply (frule vp_nonzero[of  "v'"],
       frule vp_ideal[of  "v'"],
       frule Ring.ideal_zero[of "Vr K v'" "vp K v'"], assumption+,
       frule sets_not_eq[of "vp K v'" "{\<zero>\<^bsub>(Vr K v')\<^esub>}"],
       simp add: singleton_sub[of "\<zero>\<^bsub>(Vr K v')\<^esub>" "carrier (Vr K v')"],
       erule bexE, simp add:Vr_0_f_0)

apply (case_tac "a \<in> carrier (Vr K v)", blast,
       frule_tac x = a in vp_mem_Vr_mem[of "v'"], assumption+,
       frule_tac x = a in Vr_mem_f_mem[of  "v'"], assumption+,
       subgoal_tac "a \<in> carrier (Vr K v)", blast,
       frule_tac x1 = a in val_pos_mem_Vr[THEN sym, of "v"], assumption+,
       simp, frule val_nonpos_inv_pos[of  "v"], assumption+)

apply (frule_tac y = "v (a\<^bsup>\<hyphen>K\<^esup>)" in aless_imp_le[of "0"],
       cut_tac x = a in invf_closed1, simp,
       frule_tac x = "a\<^bsup>\<hyphen>K\<^esup>" in val_poss_mem_Vr[of v], simp, assumption+)
apply (frule_tac c = "a\<^bsup>\<hyphen>K\<^esup>" in subsetD[of "carrier (Vr K v)"
        "carrier (Vr K v')"], assumption+) apply (
        frule_tac x = "a\<^bsup>\<hyphen>K\<^esup>" in val_pos_mem_Vr[of "v'"],
        simp, simp only:value_of_inv[of "v'"], simp,
        simp add:value_of_inv[of  "v'"])
apply (frule_tac y = "- v' a" in ale_minus[of "0"], simp add:a_minus_minus,
       frule_tac x = a in vp_mem_val_poss[of "v'"], assumption+,
       simp)
done

section "Equivalent valuations"

definition
  v_equiv :: "[_ , 'r \<Rightarrow> ant, 'r \<Rightarrow> ant] \<Rightarrow> bool" where
  "v_equiv K v1 v2 \<longleftrightarrow> n_val K v1 = n_val K v2"


lemma (in Corps) valuation_equivTr1:"\<lbrakk>valuation K v; valuation K v';
 \<forall>x\<in>carrier K. 0 \<le> (v x) \<longrightarrow> 0 \<le> (v' x)\<rbrakk> \<Longrightarrow>
                carrier (Vr K v) \<subseteq> carrier (Vr K v')"
apply (frule Vr_ring[of  "v"],
       frule Vr_ring[of  "v'"])
apply (rule subsetI,
       case_tac "x = \<zero>\<^bsub>K\<^esub>", simp, simp add:Vr_def Sr_def,
       frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of "v"],
       frule_tac x = x in Vr_mem_f_mem[of "v"],
       simp, frule_tac x = x in Vr_mem_f_mem[of "v"], assumption+)
apply (drule_tac x = x in bspec, simp add:Vr_mem_f_mem)
apply simp
apply (subst val_pos_mem_Vr[THEN sym, of v'], assumption+,
       simp add:Vr_mem_f_mem, assumption+)
done

lemma (in Corps) valuation_equivTr2:"\<lbrakk>valuation K v; valuation K v';
 carrier (Vr K v) \<subseteq> carrier (Vr K v'); vp K v = carrier (Vr K v) \<inter> vp K v'\<rbrakk>
  \<Longrightarrow>  carrier (Vr K v') \<subseteq> carrier (Vr K v)"
apply (frule Vr_ring[of "v"], frule Vr_ring[of "v'"])
apply (rule subsetI)
apply (case_tac "x = \<zero>\<^bsub>(Vr K v')\<^esub>", simp,
       subst Vr_0_f_0[of "v'"], assumption+,
       subst Vr_0_f_0[of "v", THEN sym], assumption,
       simp add:Ring.ring_zero)
apply (rule contrapos_pp, simp+)
apply (frule_tac x = x in Vr_mem_f_mem[of "v'"], assumption+)
apply (simp add:val_pos_mem_Vr[THEN sym, of "v"])
apply (cut_tac y = "v x" in aneg_le[of "0"], simp)
apply (simp add:Vr_0_f_0[of "v'"])
apply (frule_tac x = "v x" in aless_minus[of _ "0"], simp,
       thin_tac "v x < 0", thin_tac "\<not> 0 \<le> v x")
apply (simp add:value_of_inv[THEN sym, of "v"])
apply (cut_tac x = x in invf_closed1, simp, simp, erule conjE)
apply (frule_tac x1 = "x\<^bsup>\<hyphen>K\<^esup>" in vp_mem_val_poss[THEN sym, of "v"],
       assumption, simp, erule conjE)
apply (frule vp_ideal [of "v'"])
apply (frule_tac x = "x\<^bsup>\<hyphen>K\<^esup>" and r = x in Ring.ideal_ring_multiple[of "Vr K v'"
       "vp K v'"], assumption+)
apply (frule_tac x = "x\<^bsup>\<hyphen>K\<^esup>" in vp_mem_Vr_mem[of "v'"], assumption+)
apply (frule_tac x = x and y = "x\<^bsup>\<hyphen>K\<^esup>" in Ring.ring_tOp_commute[of "Vr K v'"],
        assumption+, simp,
        thin_tac "x \<cdot>\<^sub>r\<^bsub>Vr K v'\<^esub> x\<^bsup>\<hyphen> K\<^esup> = x\<^bsup>\<hyphen> K\<^esup> \<cdot>\<^sub>r\<^bsub>Vr K v'\<^esub> x")
apply (simp add:Vr_tOp_f_tOp)
 apply (cut_tac x = x in  linvf, simp, simp)
 apply (cut_tac field_is_ring, frule Ring.ring_one[of "K"])
 apply (frule ideal_inc_elem0val_whole[of "v'" "1\<^sub>r" "vp K v'"],
        assumption+, simp add:value_of_one, assumption+)
 apply (frule vp_not_whole[of "v'"], simp)
done

lemma (in Corps) eq_carr_eq_Vring:" \<lbrakk>valuation K v; valuation K v';
     carrier (Vr K v) = carrier (Vr K v')\<rbrakk> \<Longrightarrow> Vr K v = Vr K v'"
apply (simp add:Vr_def Sr_def)
done

lemma (in Corps) valuations_equiv:"\<lbrakk>valuation K v; valuation K v';
    \<forall>x\<in>carrier K. 0 \<le> (v x) \<longrightarrow> 0 \<le> (v' x)\<rbrakk>  \<Longrightarrow> v_equiv K v v'"
(** step0. preliminaries. **)
apply (frule Vr_ring[of "v"], frule Vr_ring[of "v'"])

(** step1.  show carrier (Vr K v) \<subseteq> carrier (Vr K v') **)
apply (frule valuation_equivTr1[of "v" "v'"], assumption+)

(** step2.  maximal_ideal (Vr K v) (carrier (Vr K v) \<inter> (vp K v')).
    contract of the maximal ideal is prime, and a prime is maximal **)
apply (frule contract_maximal [of "v" "v'"], assumption+)

(** step3. Vring is a local ring, we have (vp K v) =
    (carrier (Vr K v) \<inter> (vp  K v')) **)
apply (frule Vr_local[of "v" "(carrier (Vr K v) \<inter> vp K v')"],
        assumption+)

(** step4. show  carrier (Vr K v') \<subseteq> carrier (Vr K v) **)
 apply (frule valuation_equivTr2[of "v" "v'"], assumption+,
        frule equalityI[of "carrier (Vr K v)" "carrier (Vr K v')"],
                                          assumption+,
        thin_tac "carrier (Vr K v) \<subseteq> carrier (Vr K v')",
        thin_tac "carrier (Vr K v') \<subseteq> carrier (Vr K v)")
(** step5. vp K v' = vp K v **)
 apply (frule vp_ideal[of "v'"],
        frule Ring.ideal_subset1[of "Vr K v'" "vp K v'"], assumption,
        simp add:Int_absorb1,
        thin_tac "\<forall>x\<in>carrier K. 0 \<le> v x \<longrightarrow> 0 \<le> v' x",
        thin_tac "vp K v' \<subseteq> carrier (Vr K v')",
        thin_tac "ideal (Vr K v') (vp K v')",
        thin_tac "maximal_ideal (Vr K v) (vp K v')")
(** step6. to show v_equiv K v v', we check whether the normal valuations
    derived from the valuations have the same value or not. if (Vr K
(n_valuation K v)) = (Vr K (n_valuation K v')), then we have only to
check the values of the elements in this valuation ring.
We see (Vr K v) = (Vr K  (n_valuation K G a i v)). **)
apply (simp add:v_equiv_def,
       rule valuations_eqTr1[of  "n_val K v" "n_val K v'"],
       (simp add:n_val_valuation)+,
       rule eq_carr_eq_Vring[of  "n_val K v" "n_val K v'"],
       (simp add:n_val_valuation)+,
       subst Vr_n_val_Vr[THEN sym, of "v"], assumption+,
       subst Vr_n_val_Vr[THEN sym, of "v'"], assumption+)
apply (rule ballI,
       frule n_val_valuation[of "v"],
       frule n_val_valuation[of "v'"],
       frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of "n_val K v"],
       simp add:Vr_mem_f_mem, simp,
       frule Vr_n_val_Vr[THEN sym, of "v"], simp,
       thin_tac "carrier (Vr K (n_val K v)) = carrier (Vr K v')",
       frule_tac x1 = x in val_pos_mem_Vr[THEN sym, of "v'"],
                            simp add:Vr_mem_f_mem,
       simp,
       frule_tac x = x in val_pos_n_val_pos[of "v'"],
       simp add:Vr_mem_f_mem, simp,
       frule_tac x = x in ideal_apow_n_val[of "v"],
       simp add:Vr_n_val_Vr[THEN sym, of "v"], simp)
apply (frule eq_carr_eq_Vring[of "v" "v'"], assumption+,
       frule_tac x = x in ideal_apow_n_val[of "v'"], assumption,
       simp add:Vr_n_val_Vr[THEN sym, of "v"],
       thin_tac "Vr K v' \<diamondsuit>\<^sub>p x = vp K v'\<^bsup> (Vr K v') (n_val K v x)\<^esup>",
       frule_tac n = "n_val K v' x" and m = "n_val K v x" in
                        Vr_potent_eq[of  "v'"], assumption+,
       frule sym, assumption+)
done

lemma (in Corps) val_equiv_axiom1:"valuation K v \<Longrightarrow> v_equiv K v v"
apply (simp add:v_equiv_def)
done

lemma (in Corps) val_equiv_axiom2:"\<lbrakk> valuation K v; valuation K v';
      v_equiv K v v'\<rbrakk> \<Longrightarrow> v_equiv K v' v"
apply (simp add:v_equiv_def)
done

lemma (in Corps) val_equiv_axiom3:"\<lbrakk> valuation K v; valuation K v';
 valuation K v'; v_equiv K v v'; v_equiv K v' v''\<rbrakk> \<Longrightarrow>  v_equiv K v v''"
apply (simp add:v_equiv_def)
done

lemma (in Corps) n_val_equiv_val:"\<lbrakk> valuation K v\<rbrakk> \<Longrightarrow>
                               v_equiv K v (n_val K v)"
apply (frule valuations_equiv[of "v" "n_val K v"], simp add:n_val_valuation)
apply (rule ballI, rule impI, simp add:val_pos_n_val_pos,
       assumption)
done

section "Prime divisors"

definition
  prime_divisor :: "[_, 'b \<Rightarrow> ant] \<Rightarrow>
        ('b \<Rightarrow> ant) set"  ("(2P\<^bsub> _ _\<^esub>)" [96,97]96) where
 "P\<^bsub>K v\<^esub> = {v'. valuation K v' \<and> v_equiv K v v'}"

definition
  prime_divisors :: "_ \<Rightarrow> ('b \<Rightarrow> ant) set set" ("Pds\<index>" 96) where
  "Pds\<^bsub>K\<^esub> = {P. \<exists>v. valuation K v \<and> P = P\<^bsub> K v\<^esub> }"

definition
  normal_valuation_belonging_to_prime_divisor ::
    "[_ ,  ('b \<Rightarrow> ant) set] \<Rightarrow> ('b \<Rightarrow> ant)"  ("(\<nu>\<^bsub>_ _\<^esub>)" [96,97]96) where
  "\<nu>\<^bsub>K P\<^esub> = n_val K (SOME v. v \<in> P)"

lemma (in Corps) val_in_P_valuation:"\<lbrakk>valuation K v; v' \<in> P\<^bsub>K v\<^esub>\<rbrakk> \<Longrightarrow>
       valuation K v'"
apply (simp add:prime_divisor_def)
done

lemma (in Corps) vals_in_P_equiv:"\<lbrakk> valuation K v; v' \<in> P\<^bsub>K v\<^esub>\<rbrakk> \<Longrightarrow>
       v_equiv K v v'"
apply (simp add:prime_divisor_def)
done

lemma (in Corps) v_in_prime_v:"valuation K v \<Longrightarrow> v \<in> P\<^bsub>K v\<^esub>"
apply (simp add:prime_divisor_def,
       frule val_equiv_axiom1[of "v"], assumption+)
done

lemma (in Corps) some_in_prime_divisor:"valuation K v \<Longrightarrow>
             (SOME w. w \<in> P\<^bsub>K v\<^esub>) \<in>  P\<^bsub>K v\<^esub>"
apply (subgoal_tac "P\<^bsub> K v\<^esub> \<noteq> {}",
       rule nonempty_some[of "P\<^bsub> K v\<^esub>"], assumption+,
       frule v_in_prime_v[of "v"])
apply blast
done

lemma (in Corps) valuation_some_in_prime_divisor:"valuation K v
          \<Longrightarrow>  valuation K (SOME w. w \<in> P\<^bsub>K v\<^esub>)"
apply (frule some_in_prime_divisor[of "v"],
       simp add:prime_divisor_def)
done

lemma (in Corps) valuation_some_in_prime_divisor1:"P \<in> Pds  \<Longrightarrow>
                  valuation K (SOME w. w \<in> P)"
apply (simp add:prime_divisors_def, erule exE)
 apply (simp add:valuation_some_in_prime_divisor)
done

lemma (in Corps) representative_of_pd_valuation:
           "P \<in> Pds \<Longrightarrow> valuation K (\<nu>\<^bsub>K P\<^esub>)"
apply (simp add:prime_divisors_def,
       erule exE, erule conjE,
       simp add:normal_valuation_belonging_to_prime_divisor_def,
       frule_tac v = v in valuation_some_in_prime_divisor)

apply (rule n_val_valuation, assumption+)
done

lemma (in Corps) some_in_P_equiv:"valuation K v \<Longrightarrow>
                  v_equiv K v (SOME w. w \<in> P\<^bsub>K v\<^esub>)"
apply (frule some_in_prime_divisor[of v])
apply (rule vals_in_P_equiv, assumption+)
done

lemma (in Corps) n_val_n_val1:"P \<in> Pds  \<Longrightarrow> n_val K (\<nu>\<^bsub>K P\<^esub>) = (\<nu>\<^bsub>K P\<^esub>)"
apply (simp add: normal_valuation_belonging_to_prime_divisor_def,
       frule valuation_some_in_prime_divisor1[of P])
apply (rule n_val_n_val[of "SOME v. v \<in> P"], assumption+)
done

lemma (in Corps) P_eq_val_equiv:"\<lbrakk>valuation K v; valuation K v'\<rbrakk> \<Longrightarrow>
        (v_equiv K v v') = (P\<^bsub>K v\<^esub> =  P\<^bsub>K v'\<^esub>)"
apply (rule iffI,
       rule equalityI,
       rule subsetI, simp add:prime_divisor_def, erule conjE,
       frule val_equiv_axiom2[of "v" "v'"], assumption+,
       rule val_equiv_axiom3[of "v'" "v"], assumption+,
       rule subsetI, simp add:prime_divisor_def, erule conjE)
apply (rule val_equiv_axiom3[of "v" "v'"], assumption+,
       frule v_in_prime_v[of  "v"], simp,
       thin_tac "P\<^bsub>K v\<^esub> = P\<^bsub>K v'\<^esub>",
       simp add:prime_divisor_def,
       rule val_equiv_axiom2[of "v'" "v"], assumption+)
done

lemma (in Corps) unique_n_valuation:"\<lbrakk> P \<in> Pds\<^bsub>K\<^esub>; P' \<in> Pds\<rbrakk> \<Longrightarrow>
                (P = P') =  (\<nu>\<^bsub>K P\<^esub> = \<nu>\<^bsub>K P'\<^esub>)"
apply (rule iffI, simp)
apply (simp add:prime_divisors_def,
       (erule exE)+, (erule conjE)+)
apply (simp add:normal_valuation_belonging_to_prime_divisor_def,
       frule_tac v = v in some_in_P_equiv,
       frule_tac v = va in some_in_P_equiv,
       subgoal_tac "v_equiv K (SOME w. w \<in> P\<^bsub>K v\<^esub>) (SOME w. w \<in> P\<^bsub>K va\<^esub>)")
apply (frule_tac v = v in some_in_prime_divisor,
       frule_tac v = va in some_in_prime_divisor,
       frule_tac v = v and v' = "SOME w. w \<in> P\<^bsub>K v\<^esub>" and v'' =
       "SOME w. w \<in> P\<^bsub>K va\<^esub>" in val_equiv_axiom3)
apply (simp add:prime_divisor_def,
       simp add:prime_divisor_def, assumption+,
       frule_tac v = va and v' = "SOME w. w \<in> P\<^bsub>K va\<^esub>" in
                      val_equiv_axiom2,
       simp add:prime_divisor_def, assumption+)
apply (frule_tac v = v and v' = "SOME w. w \<in> P\<^bsub>K va\<^esub>" and v'' = va in
       val_equiv_axiom3,
      simp add:prime_divisor_def,
      simp add:prime_divisor_def, assumption+,
      frule_tac v = v and v' = va in P_eq_val_equiv, assumption+)
apply simp
apply (simp add:v_equiv_def)
done

lemma (in Corps) n_val_representative:"P \<in> Pds \<Longrightarrow>  (\<nu>\<^bsub>K P\<^esub>) \<in> P"
apply (simp add:prime_divisors_def,
       erule exE, erule conjE,
       simp add:normal_valuation_belonging_to_prime_divisor_def,
       frule_tac v = v in valuation_some_in_prime_divisor,
       frule_tac v = "SOME w. w \<in> P\<^bsub>K v\<^esub>" in
           n_val_equiv_val,
       frule_tac v = v in some_in_P_equiv,
       frule_tac v = v and v' = "SOME w. w \<in> P\<^bsub> K v\<^esub>" and v'' =
        "n_val K (SOME w. w \<in> P\<^bsub>K v\<^esub>)" in val_equiv_axiom3,
       assumption+,
       frule_tac v = v in n_val_valuation,
       simp add:prime_divisor_def, simp add:n_val_valuation)
done

lemma (in Corps) val_equiv_eq_pdiv:"\<lbrakk> P \<in> Pds\<^bsub>K\<^esub>; P'\<in> Pds\<^bsub>K\<^esub>; valuation K v;
         valuation K v'; v_equiv K v v'; v \<in> P; v' \<in> P' \<rbrakk> \<Longrightarrow>  P = P'"
apply (simp add:prime_divisors_def,
       (erule exE)+, (erule conjE)+)
apply (rename_tac w w',
       frule_tac v = w in vals_in_P_equiv[of _ "v"], simp,
       frule_tac v = w' in vals_in_P_equiv[of _ "v'"], simp,
       frule_tac v = w and v' = v and  v'' = v' in val_equiv_axiom3,
       assumption+,
       frule_tac v = w' in val_equiv_axiom2[of _ "v'"], assumption+,
       frule_tac v = w and v' = v' and  v'' = w' in val_equiv_axiom3,
          assumption+) apply simp+
apply (simp add:P_eq_val_equiv)
done

lemma (in Corps) distinct_p_divisors:"\<lbrakk> P \<in> Pds\<^bsub>K\<^esub>; P' \<in> Pds\<^bsub>K\<^esub>\<rbrakk> \<Longrightarrow>
          (\<not> P = P') =  (\<not> v_equiv K (\<nu>\<^bsub>K P\<^esub>) (\<nu>\<^bsub>K P'\<^esub>))"
apply (rule iffI,
       rule contrapos_pp, simp+,
       frule val_equiv_eq_pdiv[of "P" "P'" "\<nu>\<^bsub>K P\<^esub>" "\<nu>\<^bsub>K P'\<^esub>"], assumption+,
       simp add: representative_of_pd_valuation,
       simp add: representative_of_pd_valuation, assumption)
apply (rule n_val_representative[of "P"], assumption,
       rule n_val_representative[of "P'"], assumption,
       simp,
       rule contrapos_pp, simp+, frule sym, thin_tac "P = P'",
       simp,
       frule representative_of_pd_valuation[of P],
       frule val_equiv_axiom1[of "\<nu>\<^bsub>K P\<^esub>"], simp)
done

section "Approximation"

definition
  valuations :: "[_ , nat, nat \<Rightarrow> ('r \<Rightarrow> ant)] \<Rightarrow> bool" where
  "valuations K n vv \<longleftrightarrow> (\<forall>j \<le> n. valuation K (vv j))"

definition
  vals_nonequiv :: "[_, nat, nat \<Rightarrow> ('r \<Rightarrow> ant)] \<Rightarrow> bool" where
  "vals_nonequiv K n vv \<longleftrightarrow> valuations K n vv \<and>
  (\<forall>j\<le>n. \<forall>l \<le> n. j \<noteq> l \<longrightarrow> \<not> (v_equiv K (vv j) (vv l)))"

definition
  Ostrowski_elem :: "[_, nat, nat \<Rightarrow> ('b \<Rightarrow> ant), 'b] \<Rightarrow> bool" where
  "Ostrowski_elem K n vv x \<longleftrightarrow>
       (0 < (vv 0 (1\<^sub>r\<^bsub>K\<^esub> \<plusminus>\<^bsub>K\<^esub> (-\<^sub>a\<^bsub>K\<^esub> x)))) \<and>  (\<forall>j\<in>nset (Suc 0) n. 0 < (vv j x))"

 (** vv 0, vv 1, vv 2,\<dots>, vv n are valuations **)

lemma (in Corps) Ostrowski_elem_0:"\<lbrakk>vals_nonequiv K n vv; x \<in> carrier K;
 Ostrowski_elem K n vv x\<rbrakk> \<Longrightarrow> 0 < (vv 0 (1\<^sub>r \<plusminus> (-\<^sub>a x)))"
apply (simp add:Ostrowski_elem_def)
done

lemma (in Corps) Ostrowski_elem_Suc:"\<lbrakk>vals_nonequiv K n vv; x \<in> carrier K;
  Ostrowski_elem K n vv x; j \<in> nset (Suc 0) n\<rbrakk> \<Longrightarrow> 0 < (vv j x)"
apply (simp add:Ostrowski_elem_def)
done

lemma (in Corps) vals_nonequiv_valuation:"\<lbrakk>vals_nonequiv K n vv; m \<le> n\<rbrakk> \<Longrightarrow>
       valuation K (vv m)"
apply (simp add:vals_nonequiv_def, erule conjE)
 apply (thin_tac "\<forall>j\<le>n. \<forall>l\<le> n. j \<noteq> l \<longrightarrow> \<not> v_equiv K (vv j) (vv l)")
 apply (simp add:valuations_def)
done

lemma (in Corps) vals_nonequiv:"\<lbrakk> vals_nonequiv K (Suc (Suc n)) vv;
 i \<le> (Suc (Suc n)); j \<le> (Suc (Suc n)); i \<noteq> j\<rbrakk> \<Longrightarrow>
                                   \<not> (v_equiv K (vv i) (vv j))"
apply (simp add:vals_nonequiv_def)
done

lemma (in Corps) skip_vals_nonequiv:"vals_nonequiv K (Suc (Suc n)) vv \<Longrightarrow>
  vals_nonequiv K (Suc n) (compose {l. l \<le> (Suc n)} vv (skip j))"
apply (subst vals_nonequiv_def)
apply (rule conjI)
apply (subst valuations_def, rule allI, rule impI,
       simp add:compose_def)
apply (cut_tac l = ja and n = "Suc n" in skip_mem[of _ _ "j"], simp,
       frule_tac m = "skip j ja" in vals_nonequiv_valuation[of
         "Suc (Suc n)" "vv"], simp, assumption)
apply ((rule allI, rule impI)+, rule impI,
       cut_tac l = ja and n = "Suc n" in skip_mem[of _ _ "j"], simp,
       cut_tac l = l and n = "Suc n" in skip_mem[of _ _ "j"], simp+)
apply (cut_tac i = ja and j = l in skip_inj[of _ "Suc n" _ "j"], simp+,
       simp add:compose_def,
       rule_tac i = "skip j ja" and j = "skip j l" in
       vals_nonequiv[of "n"], assumption+)
done

lemma (in Corps) not_v_equiv_reflex:"\<lbrakk>valuation K v; valuation K v';
 \<not> v_equiv K v v'\<rbrakk> \<Longrightarrow> \<not> v_equiv K v' v "
apply (simp add:v_equiv_def)
done

lemma (in Corps) nonequiv_ex_Ostrowski_elem:"\<lbrakk>valuation K v; valuation K v';
 \<not> v_equiv K v v'\<rbrakk> \<Longrightarrow> \<exists>x\<in>carrier K. 0 \<le> (v x) \<and> (v' x) < 0"
 apply (subgoal_tac "\<not> (\<forall>x\<in>carrier K. 0 \<le> (v x) \<longrightarrow> 0 \<le> (v' x))")
 prefer 2
 apply (rule contrapos_pp, simp+,
        frule valuations_equiv[of "v" "v'"], assumption+,
        simp add:val_equiv_axiom2[of v v'])
apply (simp, erule bexE, erule conjE, simp add:aneg_le)
 apply blast
done

lemma (in Corps) field_op_minus:"\<lbrakk>a \<in> carrier K; b \<in> carrier K; b \<noteq> \<zero>\<rbrakk> \<Longrightarrow>
                              -\<^sub>a (a \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>)) = (-\<^sub>a a) \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>)"
apply (cut_tac invf_closed1[of "b"], simp,
       erule conjE, cut_tac field_is_ring,
        simp add:Ring.ring_inv1[of "K" "a" "b\<^bsup>\<hyphen>K\<^esup>"], simp)
done

lemma (in Corps) field_one_plus_frac1:"\<lbrakk>a \<in> carrier K; b \<in> carrier K; b \<noteq> \<zero>\<rbrakk>
 \<Longrightarrow> 1\<^sub>r \<plusminus> (a \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>)) = (b \<plusminus> a) \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>)"
apply (cut_tac field_is_ring,
       cut_tac invf_closed1[of b], simp+, erule conjE,
       cut_tac field_is_idom)
 apply (rule Idomain.idom_mult_cancel_r[of K "1\<^sub>r \<plusminus> (a \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>))"
        "(b \<plusminus> a) \<cdot>\<^sub>r (b\<^bsup>\<hyphen>K\<^esup>)" "b"],  assumption+,
       frule Idomain.idom_is_ring[of "K"], frule Ring.ring_is_ag[of "K"],
       rule aGroup.ag_pOp_closed [of "K"], assumption+,
       simp add:Ring.ring_one,rule Ring.ring_tOp_closed, assumption+,
       rule Ring.ring_tOp_closed, assumption+,
       frule Ring.ring_is_ag[of "K"],
       rule aGroup.ag_pOp_closed, assumption+,
       subst Ring.ring_distrib2[of "K" "b"], assumption+,
       simp add:Ring.ring_one, simp add:Ring.ring_tOp_closed,
       simp add:Ring.ring_l_one) thm Ring.ring_distrib2[of K "b\<^bsup>\<hyphen>K\<^esup>"]
 apply (subst Ring.ring_distrib2[of K "b\<^bsup>\<hyphen>K\<^esup>"], assumption+,
       simp add:Ring.ring_tOp_commute[of "K" "b" "b\<^bsup>\<hyphen>K\<^esup>"],
       subst linvf[of "b"], simp,
       subst  Ring.ring_distrib2[of "K" "b"], assumption+,
       simp add:Ring.ring_one, simp add:Ring.ring_tOp_closed,
       simp add:Ring.ring_l_one, simp)
done

lemma (in Corps) field_one_plus_frac2:"\<lbrakk>a \<in> carrier K; b \<in> carrier K;
 a \<plusminus> b \<noteq> \<zero>\<rbrakk>  \<Longrightarrow> 1\<^sub>r \<plusminus> (-\<^sub>a (a \<cdot>\<^sub>r (a \<plusminus> b)\<^bsup>\<hyphen>K\<^esup>)) = b \<cdot>\<^sub>r ((a \<plusminus> b)\<^bsup>\<hyphen>K\<^esup>)"
apply (frule field_op_minus[of "a" "a \<plusminus> b"],
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:aGroup.ag_pOp_closed, assumption, simp,
       thin_tac "-\<^sub>a (a \<cdot>\<^sub>r (a \<plusminus> b)\<^bsup>\<hyphen> K\<^esup>) = (-\<^sub>a a) \<cdot>\<^sub>r (a \<plusminus> b)\<^bsup>\<hyphen> K\<^esup>")
 apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
        frule aGroup.ag_mOp_closed[of "K" "a"], assumption,
        frule field_one_plus_frac1[of "-\<^sub>a a" "a \<plusminus> b"],
        simp add:aGroup.ag_pOp_closed, simp, simp,
        thin_tac "1\<^sub>r \<plusminus> (-\<^sub>a a) \<cdot>\<^sub>r (a \<plusminus> b)\<^bsup>\<hyphen> K\<^esup> = (a \<plusminus> b \<plusminus> -\<^sub>a a) \<cdot>\<^sub>r (a \<plusminus> b)\<^bsup>\<hyphen> K\<^esup>",
        simp add:aGroup.ag_pOp_assoc[of "K" "a" "b" "-\<^sub>a a"],
        simp add:aGroup.ag_pOp_commute[of "K" "b" "-\<^sub>a a"],
        simp add:aGroup.ag_pOp_assoc[THEN sym],
        simp add:aGroup.ag_r_inv1,
        simp add:aGroup.ag_l_zero)
done

lemma (in Corps) field_one_plus_frac3:"\<lbrakk>x \<in> carrier K; x \<noteq> 1\<^sub>r;
      1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x) \<noteq> \<zero> \<rbrakk> \<Longrightarrow>
      1\<^sub>r \<plusminus> -\<^sub>a x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen> K\<^esup> =
                    (1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup>) \<cdot>\<^sub>r (1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen> K\<^esup>"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag, frule Ring.ring_one,
       cut_tac invf_closed1[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], simp, erule conjE)
apply (subst Ring.ring_inv1_1, assumption+,
        subst field_one_plus_frac1[of "-\<^sub>a x" "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"])
 apply (rule aGroup.ag_mOp_closed, assumption+,
        rule aGroup.ag_pOp_closed, assumption+,
        rule Ring.ring_tOp_closed, assumption+)
 apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed,
        assumption+,
        subst Ring.ring_distrib1, assumption+,
        rule aGroup.ag_mOp_closed, assumption+)
 apply (simp add:Ring.ring_r_one)
 apply (simp add:Ring.ring_inv1_2[THEN sym, of K x x])
 apply (subgoal_tac "1\<^sub>r \<plusminus> (x \<plusminus> -\<^sub>a x \<cdot>\<^sub>r x) \<plusminus> -\<^sub>a x = 1\<^sub>r \<plusminus> -\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup>",
        simp,
        frule Ring.ring_tOp_closed[of K x x], assumption+)

 apply (frule Ring.ring_tOp_closed[of K x x], assumption+,
        frule aGroup.ag_mOp_closed[of K "x \<cdot>\<^sub>r x"], assumption+,
        frule aGroup.ag_mOp_closed[of K x], assumption+)
 apply (subst aGroup.ag_pOp_assoc, assumption+,
        rule aGroup.ag_pOp_closed, assumption+)
  apply (rule aGroup.ag_pOp_add_l[of K "x \<plusminus> -\<^sub>a x \<cdot>\<^sub>r x \<plusminus> -\<^sub>a x"
         "-\<^sub>a x^\<^bsup>K (Suc (Suc 0))\<^esup>" "1\<^sub>r"], assumption+,
         (rule aGroup.ag_pOp_closed, assumption+)+,
         rule aGroup.ag_mOp_closed, assumption+, rule Ring.npClose,
         assumption+,
         subst aGroup.ag_pOp_commute, assumption+,
         simp add:aGroup.ag_pOp_assoc aGroup.ag_r_inv1 aGroup.ag_r_zero)
   apply (simp add:Ring.ring_l_one)
apply simp
 apply (rule aGroup.ag_pOp_closed, assumption+,
        rule Ring.ring_tOp_closed, assumption+,
        rule aGroup.ag_pOp_closed, assumption+,
        rule aGroup.ag_mOp_closed[of K x], assumption+)
done

lemma (in Corps) OstrowskiTr1:"\<lbrakk> valuation K v; s \<in> carrier K; t \<in> carrier K;
      0 \<le> (v s); v t < 0\<rbrakk>  \<Longrightarrow> s \<plusminus> t \<noteq> \<zero>"
apply (rule contrapos_pp, simp+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp only:aGroup.ag_plus_zero[THEN sym, of "K" "s" "t"])
apply (simp add:val_minus_eq[of "v" "t"])
done

lemma (in Corps) OstrowskiTr2:"\<lbrakk>valuation K v; s \<in> carrier K; t \<in> carrier K;
  0 \<le> (v s); v t < 0\<rbrakk>  \<Longrightarrow> 0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a ((t \<cdot>\<^sub>r ((s \<plusminus> t)\<^bsup>\<hyphen>K\<^esup>))))))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule OstrowskiTr1[of "v" "s" "t"], assumption+,
       frule field_one_plus_frac2[of "t" "s"], assumption+,
       simp add:aGroup.ag_pOp_commute)
apply (subst aGroup.ag_pOp_commute[of "K" "s" "t"], assumption+, simp,
       simp add:aGroup.ag_pOp_commute[of "K" "t" "s"],
       thin_tac "1\<^sub>r \<plusminus> -\<^sub>a (t \<cdot>\<^sub>r (s \<plusminus> t)\<^bsup>\<hyphen> K\<^esup>) = s \<cdot>\<^sub>r (s \<plusminus> t)\<^bsup>\<hyphen> K\<^esup>",
       frule aGroup.ag_pOp_closed[of "K" "s" "t"], assumption+,
       cut_tac invf_closed1[of "s \<plusminus> t"], simp, erule conjE)
apply (simp add:val_t2p,
       simp add:value_of_inv,
       frule aless_le_trans[of "v t" "0" "v s"], assumption+,
       frule value_less_eq[THEN sym, of v t s], assumption+,
       simp add:aGroup.ag_pOp_commute,
       frule aless_diff_poss[of "v t" "v s"], simp add:diff_ant_def, simp)
done

lemma (in Corps) OstrowskiTr3:"\<lbrakk>valuation K v; s \<in> carrier K; t \<in> carrier K;
      0 \<le> (v t); v s < 0\<rbrakk>  \<Longrightarrow> 0 < (v (t \<cdot>\<^sub>r (( s \<plusminus> t)\<^bsup>\<hyphen>K\<^esup>)))"
apply (frule aless_le_trans[of "v s" "0" "v t"], assumption+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "s" "t"], assumption+,
       frule OstrowskiTr1[of v t s], assumption+,
       frule value_less_eq[THEN sym, of v s t], assumption+)
apply (simp add:aGroup.ag_pOp_commute[of K t s],
       cut_tac invf_closed1[of "s \<plusminus> t"], simp) apply (
       erule conjE, simp add:val_t2p[of v], simp add:value_of_inv)
       apply (cut_tac aless_diff_poss[of "v s" "v t"],
              simp add:diff_ant_def, simp+)
done

lemma (in Corps) restrict_Ostrowski_elem:"\<lbrakk> x \<in> carrier K;
  Ostrowski_elem K (Suc (Suc n)) vv x\<rbrakk> \<Longrightarrow> Ostrowski_elem K (Suc n) vv x"
apply (simp add:Ostrowski_elem_def,
       erule conjE, rule ballI, simp add:nset_def,
       insert lessI [of "Suc n"])
done

lemma (in Corps) restrict_vals_nonequiv:"vals_nonequiv K (Suc (Suc n)) vv \<Longrightarrow>
                  vals_nonequiv K (Suc n) vv"
apply (simp add:vals_nonequiv_def,
       erule conjE, simp add:valuations_def)
done

lemma (in Corps) restrict_vals_nonequiv1:"vals_nonequiv K (Suc (Suc n)) vv \<Longrightarrow>
       vals_nonequiv K (Suc n) (compose {h. h \<le> (Suc n)} vv (skip 1))"
apply (simp add:vals_nonequiv_def, (erule conjE)+,
       rule conjI,
       thin_tac "\<forall>j\<le>Suc (Suc n). \<forall>l\<le>Suc (Suc n). j \<noteq> l \<longrightarrow>
                                       \<not> v_equiv K (vv j) (vv l)",
      simp add:valuations_def, rule allI, rule impI,
      simp add:compose_def skip_def nset_def)
 apply ((rule allI, rule impI)+, rule impI)
 apply (simp add:compose_def skip_def nset_def)
done

lemma (in Corps) restrict_vals_nonequiv2:"\<lbrakk>vals_nonequiv K (Suc (Suc n)) vv\<rbrakk>
      \<Longrightarrow> vals_nonequiv K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 2))"
apply (simp add:vals_nonequiv_def, (erule conjE)+,
      rule conjI,
      thin_tac "\<forall>j\<le>Suc (Suc n). \<forall>l\<le>Suc (Suc n). j \<noteq> l \<longrightarrow>
                                              \<not> v_equiv K (vv j) (vv l)",
      simp add:valuations_def,
      rule allI, rule impI)
 apply (simp add:compose_def skip_def nset_def,
       (rule allI, rule impI)+, rule impI,
       simp add:compose_def skip_def nset_def)
done

lemma (in Corps)  OstrowskiTr31:"\<lbrakk>valuation K v; s \<in> carrier K;
        0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a s)))\<rbrakk> \<Longrightarrow> s \<noteq> \<zero>"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"])
apply (rule contrapos_pp, simp+)
 apply (simp add:aGroup.ag_inv_zero,
        frule Ring.ring_one[of "K"], simp add:aGroup.ag_r_zero)
 apply (simp add:value_of_one)
done

lemma (in Corps) OstrowskiTr32:"\<lbrakk>valuation K v; s \<in> carrier K;
           0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a s)))\<rbrakk> \<Longrightarrow> 0 \<le> (v s)"
apply (rule contrapos_pp, simp+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:aneg_le,
       frule has_val_one_neq_zero[of "v"])
apply (frule OstrowskiTr31[of v s], assumption+,
       frule not_sym,
       frule Ring.ring_one[of "K"])
apply (frule value_less_eq[THEN sym, of v "-\<^sub>a s" "1\<^sub>r"],
       simp add:aGroup.ag_mOp_closed, assumption+,
       simp add:val_minus_eq)
apply (simp add:value_of_one,
       frule aGroup.ag_mOp_closed[of "K" "s"], assumption+,
       simp add:aGroup.ag_pOp_commute[of "K" "-\<^sub>a s" "1\<^sub>r"],
       simp add:val_minus_eq)
done

lemma (in Corps) OstrowskiTr4:"\<lbrakk>valuation K v; s \<in> carrier K; t \<in> carrier K;
      0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a s))); 0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a t)))\<rbrakk>  \<Longrightarrow>
                              0 < (v (1\<^sub>r \<plusminus> (-\<^sub>a (s \<cdot>\<^sub>r t))))"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"])
apply (subgoal_tac "1\<^sub>r \<plusminus> (-\<^sub>a (s \<cdot>\<^sub>r t)) =
                    1\<^sub>r \<plusminus> (-\<^sub>a s) \<plusminus> (s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> (-\<^sub>a t)))", simp,
       thin_tac "1\<^sub>r \<plusminus> -\<^sub>a (s \<cdot>\<^sub>r t) = 1\<^sub>r \<plusminus> -\<^sub>a s \<plusminus> s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a t)")
apply (frule aGroup.ag_mOp_closed[of K s], assumption+,
       frule aGroup.ag_pOp_closed[of K "1\<^sub>r" "-\<^sub>a s"], assumption+,
       frule aGroup.ag_mOp_closed[of "K" "t"], assumption+,
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a t"], assumption+,
       frule Ring.ring_tOp_closed[of "K" "s" "1\<^sub>r \<plusminus> (-\<^sub>a t)"], assumption+,
       frule amin_le_plus[of v "1\<^sub>r \<plusminus> (-\<^sub>a s)" "s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> (-\<^sub>a t))"], assumption+)
apply (frule amin_gt[of "0" "v (1\<^sub>r \<plusminus> -\<^sub>a s)" "v (s \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a t))"])
apply (simp add:val_t2p,
       frule OstrowskiTr32[of v s], assumption+,
       rule aadd_pos_poss[of "v s" "v (1\<^sub>r \<plusminus> -\<^sub>a t)"], assumption+,
       simp add:Ring.ring_distrib1)
apply (frule aGroup.ag_mOp_closed[of K t], assumption,
       simp add:Ring.ring_distrib1 Ring.ring_r_one,
       frule aGroup.ag_mOp_closed[of K s], assumption+,
       subst aGroup.pOp_assocTr43, assumption+,
       simp add:Ring.ring_tOp_closed,
       simp add:aGroup.ag_l_inv1 aGroup.ag_r_zero,
       simp add:Ring.ring_inv1_2)
done

lemma (in Corps) OstrowskiTr5:"\<lbrakk> vals_nonequiv K (Suc (Suc n)) vv;
  s \<in> carrier K; t \<in> carrier K;
  0 \<le> (vv (Suc 0)) s \<and> 0 \<le> (vv (Suc (Suc 0))) t;
  Ostrowski_elem K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 1)) s;
  Ostrowski_elem K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 2)) t\<rbrakk> \<Longrightarrow>
  Ostrowski_elem K (Suc (Suc n)) vv (s \<cdot>\<^sub>r t)"
apply (erule conjE,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule_tac x = s and y = t in Ring.ring_tOp_closed[of "K"], assumption+,
       frule skip_vals_nonequiv[of n "vv" "1"],
       frule skip_vals_nonequiv[of n "vv" "2"],
       subst Ostrowski_elem_def, rule conjI)

apply (rule  OstrowskiTr4,
       simp add:vals_nonequiv_valuation[of "Suc (Suc n)" "vv" "0"],
       assumption+,
       frule Ostrowski_elem_0[of  "Suc n"
         "compose {j. j \<le> (Suc n)} vv (skip 1)" "s"], assumption+,
       simp add:skip_def compose_def,
       frule Ostrowski_elem_0[of "Suc n"
         "compose {j. j \<le> (Suc n)} vv (skip 2)" "t"], assumption+,
       simp add:skip_def compose_def)

apply (rule ballI,
      case_tac "j = Suc 0",
      frule_tac j = " Suc 0" in Ostrowski_elem_Suc[of "Suc n"
        "compose {j. j \<le> (Suc n)} vv (skip 2)" "t"], assumption+,
        simp add:nset_def) apply (
 thin_tac "Ostrowski_elem K (Suc n) (compose {j. j \<le> Suc n} vv (skip 1)) s",
 thin_tac "Ostrowski_elem K (Suc n) (compose {j. j \<le> Suc n} vv (skip 2)) t",
 thin_tac "vals_nonequiv K (Suc n) (compose {l. l \<le> Suc n} vv (skip 1))",
      frule vals_nonequiv_valuation[of  "Suc n"
       "compose {j. j \<le> (Suc n)} vv (skip 2)" "Suc 0"])
 apply simp+
 apply (simp add:skip_def compose_def,
        simp add:val_t2p, simp add:aadd_pos_poss)

 (** Ostrowski_elem_Suc case j = Suc (Suc 0) **)
apply (case_tac "j = Suc (Suc 0)",
       frule vals_nonequiv_valuation[of "Suc n"
        "compose {j. j \<le> Suc n} vv (skip 1)" "Suc 0"],
        simp,
       frule_tac j = " Suc 0" in Ostrowski_elem_Suc[of "Suc n"
        "compose {j. j \<le> (Suc n)} vv (skip 1)" "s"],
         assumption+, simp add:nset_def,
         simp add:skip_def compose_def,
       simp add:val_t2p, rule aadd_poss_pos, assumption+)
apply (frule_tac j = j in nsetTr1[of _ "Suc 0" "Suc (Suc n)"], assumption,
       frule_tac j = j in nsetTr2[of _ "Suc 0" "Suc n"],
       thin_tac "j \<in> nset (Suc (Suc 0)) (Suc (Suc n))",
       frule_tac j = "j - Suc 0" in Ostrowski_elem_Suc[of "Suc n"
                "compose {j. j \<le> (Suc n)} vv (skip 1)" "s"], assumption+)

apply (frule_tac j = "j - Suc 0" in Ostrowski_elem_Suc[of "Suc n"
                 "compose {j. j \<le> (Suc n)} vv (skip 2)" "t"], assumption+,
 thin_tac "Ostrowski_elem K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 1)) s",
 thin_tac "Ostrowski_elem K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 2)) t",
 thin_tac "vals_nonequiv K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 1))",
 thin_tac "vals_nonequiv K (Suc n) (compose {j. j \<le> (Suc n)} vv (skip 2))")

apply (simp add:compose_def skip_def nset_def,
      (erule conjE)+, simp, subgoal_tac "\<not> (j - Suc 0 \<le> Suc 0)", simp)
apply (frule_tac m = j in vals_nonequiv_valuation[of "Suc (Suc n)"],
       assumption+,
      simp add:val_t2p,
      rule_tac x = "vv j s" and y = "vv j t" in aadd_pos_poss,
      simp add:aless_imp_le, assumption)
apply simp
done

lemma (in Corps) one_plus_x_nonzero:"\<lbrakk>valuation K v; x \<in> carrier K; v x < 0\<rbrakk>
      \<Longrightarrow> 1\<^sub>r \<plusminus> x \<in> carrier K \<and> v (1\<^sub>r \<plusminus> x) < 0"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "x"], assumption+,
       simp)
apply (frule value_less_eq[of "v" "x" "1\<^sub>r"], assumption+,
       simp add:value_of_one, simp add:aGroup.ag_pOp_commute)
done

lemma (in Corps)  val_neg_nonzero:"\<lbrakk>valuation K v; x \<in> carrier K; v x < 0\<rbrakk> \<Longrightarrow>
                                     x \<noteq> \<zero>"
apply (rule contrapos_pp, simp+, simp add:value_of_zero)
apply (frule aless_imp_le[of "\<infinity>" "0"],
        cut_tac inf_ge_any[of "0"],
        frule ale_antisym[of "0" "\<infinity>"], assumption+, simp)
done

lemma (in Corps) OstrowskiTr6:"\<lbrakk>valuation K v; x \<in> carrier K; \<not> 0 \<le> (v x)\<rbrakk> \<Longrightarrow>
       (1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)) \<in> carrier K - {\<zero>}"
apply (simp add:aneg_le,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule one_plus_x_nonzero[of "v" "-\<^sub>a x"], assumption+,
        simp add:val_minus_eq, erule conjE)

apply (rule conjI,
       rule aGroup.ag_pOp_closed[of "K"], assumption+,
       simp add:Ring.ring_one, rule Ring.ring_tOp_closed[of "K"], assumption+)

apply (frule val_t2p[of v x "1\<^sub>r \<plusminus> (-\<^sub>a x)"], assumption+,
       frule val_neg_nonzero[of v x], assumption+,
       frule val_nonzero_z[of v x], assumption+, erule exE,
       frule_tac z = z in aadd_less_mono_z[of "v (1\<^sub>r \<plusminus> (-\<^sub>a x))" "0"],
       simp add:aadd_0_l,
       simp only:aadd_commute[of "v (1\<^sub>r \<plusminus> -\<^sub>a x)"],
       frule_tac x = "ant z + v (1\<^sub>r \<plusminus> -\<^sub>a x)" and y ="ant z" in
         aless_trans[of _ _ "0"], assumption,
       drule sym, simp)

apply (frule_tac x = x and y = "1\<^sub>r \<plusminus> -\<^sub>a x" in Ring.ring_tOp_closed[of "K"],
             assumption+,
       frule one_plus_x_nonzero[of v "x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> (-\<^sub>a x))"],
                      assumption+, erule conjE,
       rule val_neg_nonzero[of v], assumption+)
done

lemma (in Corps) OstrowskiTr7:"\<lbrakk>valuation K v; x \<in> carrier K; \<not> 0 \<le> (v x)\<rbrakk> \<Longrightarrow>
  1\<^sub>r \<plusminus> -\<^sub>a (x \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>)) =
     (1\<^sub>r \<plusminus> -\<^sub>a x \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)) \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>)"
apply (cut_tac field_is_ring,
       frule OstrowskiTr6[of v x], assumption+, simp, erule conjE,
       cut_tac field_is_idom,
       cut_tac invf_closed1[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], simp,
       frule Ring.ring_is_ag[of "K"],
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       frule Ring.ring_one[of "K"],
       frule aGroup.ag_pOp_closed[of "K" "1\<^sub>r" "-\<^sub>a x"], assumption+,
       rule Idomain.idom_mult_cancel_r[of K "1\<^sub>r \<plusminus> -\<^sub>a (x \<cdot>\<^sub>r ((1\<^sub>r \<plusminus> x \<cdot>\<^sub>r
       (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>))" "(1\<^sub>r \<plusminus> -\<^sub>a x \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)) \<cdot>\<^sub>r
       ((1\<^sub>r \<plusminus>  x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen>K\<^esup>)" "(1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))"],
       assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+, rule aGroup.ag_mOp_closed,
       assumption+,
       rule Ring.ring_tOp_closed, assumption+, simp, rule Ring.ring_tOp_closed,
       assumption+,
       (rule aGroup.ag_pOp_closed, assumption+)+,
       rule  Ring.ring_tOp_closed, assumption+, simp, assumption+,
       subst Ring.ring_tOp_assoc, assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       simp add:Ring.ring_tOp_closed, simp, simp)
apply (subst linvf[of "1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x)"], simp,
       (subst Ring.ring_distrib2, assumption+)+, erule conjE)
apply (rule aGroup.ag_mOp_closed, assumption,
       rule Ring.ring_tOp_closed, assumption+,
       subst Ring.ring_r_one, assumption+)
apply (rule aGroup.ag_pOp_closed, assumption+,
       rule Ring.ring_tOp_closed, assumption+,
       erule conjE,
       simp add:Ring.ring_inv1_1,
       simp add:Ring.ring_tOp_assoc[of K "-\<^sub>a x" "(1\<^sub>r \<plusminus> x \<cdot>\<^sub>r (1\<^sub>r \<plusminus> -\<^sub>a x))\<^bsup>\<hyphen> K\<^esup>"],
       simp add:linvf, simp add:Ring.ring_r_one Ring.ring_l_one,
       frule Ring.ring_tOp_closed[of K x "1\<^sub>r \<plusminus> -\<^sub>a x"], assumption+,
       simp add:aGroup.ag_pOp_assoc, simp add:aGroup.ag_pOp_commute)
apply simp
done

lemma (in Corps) Ostrowski_elem_nonzero:"\<lbrakk>vals_nonequiv K (Suc n) vv;
 x \<in> carrier K; Ostrowski_elem K (Suc n) vv x\<rbrakk> \<Longrightarrow> x \<noteq> \<zero>"
apply (simp add:Ostrowski_elem_def,
       frule conjunct1, fold Ostrowski_elem_def,
       frule vals_nonequiv_valuation[of "Suc n" "vv" "0"], simp)
apply (rule contrapos_pp, simp+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       simp add:aGroup.ag_inv_zero, frule Ring.ring_one[of "K"],
       simp add:aGroup.ag_r_zero, simp add:value_of_one)
done

lemma (in Corps) Ostrowski_elem_not_one:"\<lbrakk>vals_nonequiv K (Suc n) vv;
      x \<in> carrier K; Ostrowski_elem K (Suc n) vv x\<rbrakk>  \<Longrightarrow>  1\<^sub>r \<plusminus> -\<^sub>a x \<noteq> \<zero>"
apply (frule vals_nonequiv_valuation [of "Suc n" "vv" "Suc 0"],
       simp,
       simp add:Ostrowski_elem_def, frule conjunct2,
       fold Ostrowski_elem_def)
apply (subgoal_tac "0 < (vv (Suc 0) x)",
       rule contrapos_pp, simp+,
       cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"],
       simp only:aGroup.ag_eq_diffzero[THEN sym, of "K" "1\<^sub>r" "x"],
       drule sym, simp, simp add:value_of_one,
       subgoal_tac "Suc 0 \<in> nset (Suc 0) (Suc n)", simp,
       simp add:nset_def)
done

lemma (in Corps) val_unit_cond:"\<lbrakk> valuation K v; x \<in> carrier K;
      0 < (v (1\<^sub>r \<plusminus> -\<^sub>a x))\<rbrakk>  \<Longrightarrow> v x = 0"
apply (cut_tac field_is_ring, frule Ring.ring_is_ag[of "K"],
       frule Ring.ring_one[of "K"])

apply (frule aGroup.ag_mOp_closed[of "K" "1\<^sub>r"], assumption+,
       frule has_val_one_neq_zero[of v])

apply (frule aGroup.ag_pOp_assoc[of "K" "-\<^sub>a 1\<^sub>r" "1\<^sub>r" "-\<^sub>a x"], assumption+,
       simp add:aGroup.ag_mOp_closed, simp add:aGroup.ag_l_inv1,
       frule aGroup.ag_mOp_closed[of "K" "x"], assumption+,
       simp add:aGroup.ag_l_zero)
apply (subgoal_tac "v (-\<^sub>a x) = v ( -\<^sub>a 1\<^sub>r \<plusminus> (1\<^sub>r \<plusminus> -\<^sub>a x))") prefer 2
  apply simp
apply (thin_tac "-\<^sub>a x =  -\<^sub>a 1\<^sub>r \<plusminus> (1\<^sub>r \<plusminus> -\<^sub>a x)",
       frule value_less_eq[of "v" "-\<^sub>a 1\<^sub>r" "1\<^sub>r \<plusminus> -\<^sub>a x"],
                                  assumption+,
       rule aGroup.ag_pOp_closed, assumption+,
       simp add:val_minus_eq value_of_one, simp add:val_minus_eq)
apply (simp add: value_of_one)
done

end
