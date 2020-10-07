(**        Algebra8  
                            author Hidetsune Kobayashi
                            Group You Santo
                            Department of Mathematics
                            Nihon University
                            hikoba@math.cst.nihon-u.ac.jp
                            May 3, 2004.
                            April 6, 2007 (revised)
  
   chapter 5. Modules
    section 4. nsum and Generators(continued)
    section 5. existence of homomorphism
    section 6. Nakayama's lemma
    section 7. direct sum and direct products of modules
    
   **)

theory Algebra8 imports Algebra7 begin


section "nsum and Generators (continued)" 

lemma (in Module) unique_expression_last:" \<lbrakk>free_generator R M H; 
        f \<in> {j. j \<le> Suc n} \<rightarrow> H; s \<in> {j. j \<le> Suc n} \<rightarrow> carrier R;
        g \<in> {j. j \<le> Suc n} \<rightarrow> H; t \<in> {j. j \<le> Suc n} \<rightarrow> carrier R;
        l_comb R M (Suc n) s f = l_comb R M (Suc n) t g; 
        inj_on f {j. j \<le> Suc n}; inj_on g {j. j \<le> Suc n}; 
        f (Suc n) = g (Suc n)\<rbrakk>  \<Longrightarrow> s (Suc n) = t (Suc n)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal, frule free_generator_sub)
apply (frule l_comb_mem[of "carrier R" H s "Suc n" f], assumption+,
       frule l_comb_mem[of "carrier R" H t "Suc n" g], assumption+)
apply (frule ag_r_inv1[of "l_comb R M (Suc n) t g"],
       simp only:linear_span_iOp_closedTr2,
             thin_tac "l_comb R M (Suc n) t g \<in> carrier M",
       frule sym, 
             thin_tac "l_comb R M (Suc n) s f = l_comb R M (Suc n) t g",
             simp,
             thin_tac "l_comb R M (Suc n) t g = l_comb R M (Suc n) s f",
       subgoal_tac "(\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)) \<in> 
                                      {j. j \<le> Suc n} \<rightarrow> carrier R",
            simp add:l_comb_Suc,
       frule funcset_mem[of s "{j. j \<le> Suc n}" "carrier R" "Suc n"], 
                  simp,
       frule funcset_mem[of t "{j. j \<le> Suc n}" "carrier R" "Suc n"], 
                  simp,
       frule funcset_mem[of g "{j. j \<le> Suc n}" H "Suc n"], 
                  simp,
       frule subsetD[of H "carrier M" "g (Suc n)"], assumption+,
       frule func_pre[of s], frule func_pre[of t], frule func_pre[of f],
            frule func_pre[of g], 
            frule func_pre[of "\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)"],
       frule l_comb_mem[of "carrier R" H s n f], assumption+,
       frule l_comb_mem[of "carrier R" H "\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)" 
               n g], assumption+,
       frule sc_mem[of "s (Suc n)" "g (Suc n)"], assumption+,
         cut_tac sc_mem[of "-\<^sub>a\<^bsub>R\<^esub> (t (Suc n))" "g (Suc n)"],
       simp add:pOp_assocTr43[of "l_comb R M n s f" "s (Suc n) \<cdot>\<^sub>s g (Suc n)"],
         simp add:ag_pOp_commute[of "s (Suc n) \<cdot>\<^sub>s g (Suc n)"],
         simp add:pOp_assocTr43[THEN sym, of "l_comb R M n s f"])
  apply (frule Ring.ring_is_ag[of R],
         frule aGroup.ag_mOp_closed[of R "t (Suc n)"], assumption+,
         simp add:sc_l_distr[THEN sym],
         simp add:l_comb_add[THEN sym, of "carrier R" H s n f 
                  "\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)" n g])
  apply (frule jointfun_hom[of f n H g n H], assumption+,
         frule jointfun_hom[of s n "carrier R" "\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)"
          n "carrier R"], assumption+, simp)
  apply (subgoal_tac "(s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))) \<cdot>\<^sub>s g (Suc n) = 
            l_comb R M 0 (\<lambda>x\<in>{0::nat}. (s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))))
               (\<lambda>x\<in>{0::nat}. (g (Suc n)))",
         simp,
         thin_tac "(s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))) \<cdot>\<^sub>s g (Suc n) =
     l_comb R M 0 (\<lambda>x\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n)))
      (\<lambda>x\<in>{0}. g (Suc n))") 
   apply (subgoal_tac "(\<lambda>x\<in>{0::nat}. (s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n)))) \<in> 
           {j. j \<le> (0::nat)} \<rightarrow> carrier R",
          subgoal_tac "(\<lambda>x\<in>{0::nat}. g (Suc n)) \<in>  {j. j \<le> (0::nat)} \<rightarrow> H") 
   apply (simp add:l_comb_add[THEN sym] del: Pi_split_insert_domain)
apply (cut_tac unique_expression3_1[of H "jointfun (Suc (n + n)) 
         (jointfun n f n g) 0 (\<lambda>x\<in>{0}. g (Suc n))" "Suc (n + n)" 
      "jointfun (Suc (n + n))
        (jointfun n s n (\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x))) 0
        (\<lambda>x\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n)))"], simp del: Pi_split_insert_domain,
   thin_tac "l_comb R M (Suc (Suc (n + n)))
   (jointfun (Suc (n + n)) (jointfun n s n (\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x))) 0
   (\<lambda>x\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))))
      (jointfun (Suc (n + n)) (jointfun n f n g) 0 (\<lambda>x\<in>{0}. g (Suc n))) =
     \<zero>",
     thin_tac "(\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)) \<in> {j. j \<le> Suc n} \<rightarrow> carrier R",
     thin_tac "l_comb R M n s f \<in> carrier M",
     thin_tac "jointfun n f n g \<in> {j. j \<le> Suc (n + n)} \<rightarrow> H",
     thin_tac "jointfun n s n (\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x))
                     \<in> {j. j \<le> Suc (n + n)} \<rightarrow> carrier R",
     thin_tac "(\<lambda>x\<in>{0}. s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))) \<in> {0} \<rightarrow> carrier R")
apply (thin_tac " (-\<^sub>a\<^bsub>R\<^esub> (t (Suc n))) \<cdot>\<^sub>s g (Suc n) \<in> carrier M",
        thin_tac "-\<^sub>a\<^bsub>R\<^esub> (t (Suc n)) \<in> carrier R",
        thin_tac "l_comb R M n (\<lambda>x\<in>{j. j \<le> Suc n}. -\<^sub>a\<^bsub>R\<^esub> (t x)) g \<in> carrier M")
 apply ((erule exE)+, (erule conjE)+, erule exE, (erule conjE)+)
   apply (frule_tac s = ta and n = m and m = ga in unique_expression1[of H],
          assumption+, simp)
   apply (drule_tac x = m in bspec, simp)
    apply (simp add:jointfun_def[of "Suc (n + n)"] sliden_def,
          thin_tac "\<zero> = l_comb R M m ta ga",
          thin_tac "ta m = s (Suc n) \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t (Suc n))",
          frule Ring.ring_is_ag[of R],
          rotate_tac -2, frule sym,
       subst aGroup.ag_eq_diffzero[of R "s (Suc n)" "t (Suc n)"], assumption+)
       apply (rule sym, assumption) apply assumption
   apply (rule Pi_I,
          case_tac "x \<le> Suc (n + n)", simp add:jointfun_def del: Pi_split_insert_domain, 
          simp add:Pi_def del: Pi_split_insert_domain,
          rule impI, simp add:sliden_def del: Pi_split_insert_domain,
          simp add:Pi_def, simp add:jointfun_def sliden_def del: Pi_split_insert_domain)
     apply (rule Pi_I,
          case_tac "x \<le> Suc (n + n)",
          simp add:jointfun_def[of "Suc (n+n)"] del: Pi_split_insert_domain,
          simp add:Pi_def,
          simp add:jointfun_def[of "Suc (n + n)"] sliden_def del: Pi_split_insert_domain,
          rule aGroup.ag_pOp_closed, assumption+,
          simp add: Nset_pre1 del: Pi_split_insert_domain,
          simp add:im_jointfunTr1[of "Suc (n+n)" "jointfun n f n g" 0 
              "\<lambda>x\<in>{0}. g (Suc n)"] del: Pi_split_insert_domain,
          simp add:im_jointfun[of f n H g n H] del: Pi_split_insert_domain,
          (subst jointfun_def[of "Suc (n+n)"])+, simp add:sliden_def del: Pi_split_insert_domain)
  apply (rule conjI, frule sym, thin_tac "f (Suc n) = g (Suc n)",
         simp add:inj_on_def[of f],
         rule contrapos_pp, simp+, simp add:image_def, erule exE, 
         erule conjE,
         drule_tac a = "Suc n" in forall_spec, simp,
         drule_tac a = x in forall_spec, simp, simp)
   apply (simp add:inj_on_def[of g],
         rule contrapos_pp, simp+, simp add:image_def, erule exE, 
         erule conjE,
         drule_tac a = "Suc n" in forall_spec, simp,
         drule_tac a = x in forall_spec, simp, simp)
        
    apply (simp)
    apply (rule Pi_I, simp,
           rule aGroup.ag_pOp_closed, assumption+)
    apply (subst l_comb_def, simp,
           rule aGroup.ag_mOp_closed, simp add:Ring.ring_is_ag,
           simp add:Pi_def, simp add:Pi_def)
    apply (rule Pi_I, simp,
           frule Ring.ring_is_ag[of R],
           rule aGroup.ag_mOp_closed[of R], assumption+,
           simp add:Pi_def)
done

lemma (in Module) unique_exprTr7p1:"  \<lbrakk>free_generator R M H;
  \<forall>f s g t m.
   f \<in> {j. j \<le> n} \<rightarrow> H \<and> inj_on f {j. j \<le> n} \<and> s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and>
   g \<in> {j. j \<le> m} \<rightarrow> H \<and> inj_on g {j. j \<le> m} \<and> t \<in> {j. j \<le> m} \<rightarrow> carrier R \<and>
   l_comb R M n s f = l_comb R M m t g \<and> 
         (\<forall>j\<le>n. s j \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> (\<forall>k\<le>m. t k \<noteq> \<zero>\<^bsub>R\<^esub>) \<longrightarrow>
           n = m \<and>
   (\<exists>h. h \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n} \<and>
                (\<forall>l\<le>n. cmp f h l = g l \<and> cmp s h l = t l));
   f \<in> {j. j \<le> Suc n} \<rightarrow> H; s \<in> {j. j \<le> Suc n} \<rightarrow> carrier R;
   g \<in> {j. j \<le> Suc n} \<rightarrow> H; t \<in> {j. j \<le> Suc n} \<rightarrow> carrier R;
   l_comb R M (Suc n) s f = l_comb R M (Suc n) t g; \<forall>j\<le>Suc n. s j \<noteq> \<zero>\<^bsub>R\<^esub>;
   \<forall>k\<le>Suc n. t k \<noteq> \<zero>\<^bsub>R\<^esub>; inj_on f {j. j \<le> Suc n}; inj_on g {j. j \<le> Suc n}; 
   f (Suc n) = g (Suc n)\<rbrakk> \<Longrightarrow> \<exists>h. h \<in> {j. j \<le> Suc n} \<rightarrow> {j. j \<le> Suc n} \<and>
              (\<forall>l\<le>Suc n. cmp f h l = g l \<and> cmp s h l = t l)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal,
       frule Ring.ring_is_ag,
       frule free_generator_sub)
  apply (frule_tac f = f and n = n and s = s and g = g and t = t in 
         unique_expression_last[of H], assumption+)
  apply (simp add:l_comb_Suc)
  apply (frule_tac f = f in func_pre, frule_tac f = s in func_pre,
         frule_tac f = g in func_pre, frule_tac f = t in func_pre,
         cut_tac n = n in Nsetn_sub,
         frule_tac f = f and A = "{j. j \<le> Suc n}" and ?A1.0 = "{j. j \<le> n}" in 
         restrict_inj, assumption+,
         frule_tac f = g and A = "{j. j \<le> Suc n}" and ?A1.0 = "{j. j \<le> n}" in 
         restrict_inj, assumption+)
  apply (frule_tac s = s and m = f and n = n in l_comb_mem[of "carrier R" H], 
         assumption+,
         frule_tac s = t and m = g and n = n in l_comb_mem[of "carrier R" H], 
         assumption+,
         frule_tac f = t and A = "{j. j \<le> Suc n}" and B = "carrier R" and 
         x = "Suc n" in funcset_mem, simp,
         frule_tac f = g and A = "{j. j \<le> Suc n}" and B = H and x = "Suc n" 
         in funcset_mem, simp,
         frule_tac c = "g (Suc n)" in subsetD[of H "carrier M"], assumption+,
         frule_tac a = "t (Suc n)" and m = "g (Suc n)" in sc_mem, assumption+)
  apply (frule_tac x = "l_comb R M n s f" and y = "t (Suc n) \<cdot>\<^sub>s g (Suc n)" and
         z = "-\<^sub>a (t (Suc n) \<cdot>\<^sub>s g (Suc n))" in ag_pOp_assoc, assumption+,
         rule ag_mOp_closed, assumption, simp add:ag_r_inv1 ag_r_zero,
         frule_tac x = "t (Suc n) \<cdot>\<^sub>s g (Suc n)" in ag_mOp_closed,
         simp add:ag_pOp_assoc, simp add:ag_r_inv1 ag_r_zero,
         rotate_tac -2, frule sym,
                thin_tac "l_comb R M n t g = l_comb R M n s f")
  apply (drule_tac x = f in spec,
  rotate_tac -1,
  drule_tac x = s in spec,
  rotate_tac -1,
  drule_tac x = g in spec,
  rotate_tac -1, drule_tac x = t in spec,
  rotate_tac -1, drule_tac x = n in spec)
  apply (cut_tac n = n in Nsetn_sub_mem1, simp)
  apply (erule exE, erule conjE)
  apply (subgoal_tac "(jointfun n h 0 (\<lambda>j. (Suc n))) \<in> 
                       {j. j \<le> Suc n} \<rightarrow> {j. j \<le> Suc n}",
        subgoal_tac "\<forall>l\<le>Suc n. cmp f (jointfun n h 0 (\<lambda>j. (Suc n))) l = 
          g l \<and> cmp s (jointfun n h 0 (\<lambda>j. (Suc n))) l = t l",
   thin_tac "\<forall>k\<le>Suc n. t k \<noteq> \<zero>\<^bsub>R\<^esub>", thin_tac "inj_on f {j. j \<le> Suc n}",
   thin_tac "inj_on g {j. j \<le> Suc n}", thin_tac "f (Suc n) = g (Suc n)",
   thin_tac "s (Suc n) = t (Suc n)",
   thin_tac "f \<in> {j. j \<le> n} \<rightarrow> H", thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
   thin_tac "g \<in> {j. j \<le> n} \<rightarrow> H", thin_tac "t \<in> {j. j \<le> n} \<rightarrow> carrier R",
   thin_tac "{j. j \<le> n} \<subseteq> {j. j \<le> Suc n}",
   thin_tac "\<forall>l\<le>n. cmp f h l = g l \<and> cmp s h l = t l",
   thin_tac "l_comb R M n t g \<in> carrier M", blast)
  apply (rule allI, rule impI, case_tac "l \<le> n", 
                                simp add:cmp_def jointfun_def,
         simp add:cmp_def, simp add:jointfun_def sliden_def,
         frule_tac y = l and x = n in not_le_imp_less, thin_tac "\<not> l \<le> n",
         frule_tac m = n and n = l in Suc_leI,
         frule_tac m = l and n = "Suc n" in Nat.le_antisym, assumption,
         simp)
  apply (rule Pi_I,
         case_tac "xa \<le> n", simp add:jointfun_def, rule impI,
         frule_tac x = x and f = h and A = "{j. j \<le> n}" and 
         B = "{j. j \<le> n}" in funcset_mem, simp, simp,
         simp add:jointfun_def, rule impI,frule_tac x = x and f = h and 
         A = "{j. j \<le> n}" and B = "{j. j \<le> n}" in funcset_mem, simp, simp)
done

lemma (in Module) unique_expression7:"free_generator R M H \<Longrightarrow>
 \<forall>f s g t m. f \<in> {j. j \<le> (n::nat)} \<rightarrow> H \<and> inj_on f {j. j \<le> n} \<and>
    s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and>
    g \<in> {j. j \<le> (m::nat)} \<rightarrow> H \<and> inj_on g {j. j \<le> m} \<and>
    t \<in> {j. j \<le> m} \<rightarrow> carrier R \<and> l_comb R M n s f = l_comb R M m t g \<and>
    (\<forall>j \<in> {j. j \<le> n}. s j \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> (\<forall>k \<in> {j. j \<le> m}. t k \<noteq> \<zero>\<^bsub>R\<^esub> ) \<longrightarrow> n = m \<and> 
    (\<exists>h. h \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n} \<and> (\<forall>l \<in> {j. j \<le> n}. (cmp f h) l = g l
      \<and> (cmp s h) l = t l))"
apply (cut_tac sc_Ring,
        frule Ring.ring_is_ag[of R],
        frule free_generator_sub[of H])
apply (induct_tac n)
 apply (rule allI)+
 apply (rule impI, (erule conjE)+)
 apply (frule_tac H = H and f = f and n = 0 and s = s and g = g and m = m 
        and t = t in unique_expression7_1, assumption+, simp del: Pi_split_insert_domain)
 apply (frule_tac H = H and f = f and n = 0 and s = s and g = g and m = m 
        and t = t in  unique_expression6, (simp del: Pi_split_insert_domain) +)
 apply (simp add:l_comb_def del: Pi_split_insert_domain)
 apply (frule_tac f = s in funcset_mem[of _ "{0}" "carrier R" 0], simp del: Pi_split_insert_domain,
        frule_tac f = t in funcset_mem[of _ "{0}" "carrier R" 0], simp del: Pi_split_insert_domain,
        frule_tac f = g in funcset_mem[of _ "{0}" H 0], simp del: Pi_split_insert_domain,
        frule_tac c = "g 0" in subsetD[of "H" "carrier M"], assumption+)
 apply (frule_tac a = "s 0" and m = "g 0" in sc_mem, assumption+, 
        frule_tac a = "t 0" and m = "g 0" in sc_mem, assumption+,
        frule_tac a = "s 0 \<cdot>\<^sub>s g 0" and b = "t 0 \<cdot>\<^sub>s g 0" in ag_eq_diffzero)
  apply assumption
 apply (simp only:sc_minus_am1, 
        thin_tac "(s 0 \<cdot>\<^sub>s g 0 = t 0 \<cdot>\<^sub>s g 0) = (\<zero> = \<zero>)")
 apply (frule_tac x = "t 0" in aGroup.ag_mOp_closed[of R], assumption+)
 apply (simp add:sc_l_distr[THEN sym],
        frule_tac h = "g 0" and a = "s 0 \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (t 0)" in 
        free_gen_coeff_zero[of H],
        assumption+,
        rule aGroup.ag_pOp_closed[of R], assumption+) 
apply (simp add:aGroup.ag_eq_diffzero[THEN sym, of R],
        simp add:cmp_def,
        cut_tac Pi_I[of "{0::nat}" "id" "%_. {0::nat}"],
        subgoal_tac "f (id 0) = g 0 \<and> s (id 0) = t 0", blast,
        simp add:id_def, simp add:id_def)
(** n = 0 done **)
apply ((rule allI)+, rule impI)
 apply (erule conjE)+
  apply (frule_tac H = H and f = f and n = "Suc n" and s = s and g = g and 
       m = m and t = t in unique_expression6, assumption+)
  apply (cut_tac k = "Suc n" in finite_Collect_le_nat,
         frule_tac A = "{j. j \<le> Suc n}" and f = f in inj_on_iff_eq_card,
         simp)
  apply (cut_tac k = m in finite_Collect_le_nat,
         frule_tac A = "{j. j \<le> m}" and f = g in inj_on_iff_eq_card,
         simp,
         thin_tac "card (g ` {j. j \<le> m}) = Suc m")
  apply (frule sym, thin_tac "Suc n = m", simp)  
  apply (cut_tac a = "Suc n" and A = "{j. j \<le> Suc n}" and f = g in 
         mem_in_image2) apply simp apply (
         rotate_tac -6) apply ( frule sym,
         thin_tac "f ` {j. j \<le> Suc n} = g ` {j. j \<le> Suc n}", simp,
         simp add:image_def) apply ( erule exE, erule conjE)
  apply (case_tac "x = Suc n", simp, thin_tac "x = Suc n",
         rotate_tac -1, frule sym, thin_tac "g (Suc n) = f (Suc n)") 
  apply (rule_tac n = n and f = f and s = s and g = g and t = t in 
          unique_exprTr7p1[of H], assumption+)

 apply (rotate_tac -2, frule sym, thin_tac "g (Suc n) = f x")
 apply (frule Ring.whole_ideal)
  apply (frule_tac s = s and n = n and f = f and j = x in 
         l_comb_transpos1[of "carrier R" H], assumption+,
         rule noteq_le_less, assumption+, simp) apply (
         thin_tac "l_comb R M (Suc n) s f = l_comb R M (Suc n) t g")
  apply (frule_tac f = "cmp f (transpos x (Suc n))" and n = n and 
         s = "cmp s (transpos x (Suc n))" and g = g and t = t in 
         unique_exprTr7p1[of H], assumption+)
  apply (rule Pi_I,
         simp add:cmp_def, rule_tac f = f and A = "{j. j \<le> Suc n}" and B = H 
         and x = "transpos x (Suc n) xa" in funcset_mem, simp,
         simp add:transpos_mem)
  apply (rule Pi_I,
         simp add:cmp_def, rule_tac f = s and A = "{j. j \<le> Suc n}" and 
         B = "carrier R" and x = "transpos x (Suc n) xa" in funcset_mem, simp,
         simp add:transpos_mem)
   apply assumption+
   apply (rule allI, rule impI, simp add:cmp_def)
   apply (cut_tac i = x and n = "Suc n" and j = "Suc n" and l = j in 
              transpos_mem, simp+)
   apply (cut_tac i = x and n = "Suc n" and j = "Suc n" in transpos_inj,
          simp+)
   apply (cut_tac  i = x and n = "Suc n" and j = "Suc n" in 
              transpos_hom, simp+)    
   apply (rule_tac f = "transpos x (Suc n)" and A = "{j. j \<le> Suc n}" and 
          B = "{j. j \<le> Suc n}" and g = f and C = H in cmp_inj,
          assumption+)
   apply (simp add:cmp_def transpos_ij_2)
 apply (erule exE, erule conjE)  
   apply (cut_tac  i = x and n = "Suc n" and j = "Suc n" in 
              transpos_hom, simp+)
   apply (simp add:cmp_assoc[THEN sym]) 
   apply (frule_tac f = h and A = "{j. j \<le> Suc n}" and B = "{j. j \<le> Suc n}" 
          and g = "transpos x (Suc n)" and C = "{j. j \<le> Suc n}" in 
          cmp_fun, assumption+)
   apply (thin_tac "\<forall>f s g t m. f \<in> {j. j \<le> n} \<rightarrow> H \<and> inj_on f {j. j \<le> n} \<and>
   s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and> g \<in> {j. j \<le> m} \<rightarrow> H \<and> inj_on g {j. j \<le> m} \<and>
   t \<in> {j. j \<le> m} \<rightarrow> carrier R \<and> l_comb R M n s f = l_comb R M m t g \<and>
   (\<forall>j\<le>n. s j \<noteq> \<zero>\<^bsub>R\<^esub>) \<and> (\<forall>k\<le>m. t k \<noteq> \<zero>\<^bsub>R\<^esub>) \<longrightarrow>  n = m \<and>
   (\<exists>h. h \<in> {j. j \<le> n} \<rightarrow> {j. j \<le> n} \<and> 
               (\<forall>l\<le>n. cmp f h l = g l \<and> cmp s h l = t l))",
    thin_tac "\<forall>j\<le>Suc n. s j \<noteq> \<zero>\<^bsub>R\<^esub>", thin_tac "\<forall>k\<le>Suc n. t k \<noteq> \<zero>\<^bsub>R\<^esub>",
    thin_tac "{y. \<exists>x\<le>Suc n. y = g x} = {y. \<exists>x\<le>Suc n. y = f x}")
  apply blast
done

lemma (in Module) gen_mHom_eq:"\<lbrakk>R module N; generator R M H; f \<in> mHom R M N;
       g \<in> mHom R M N; \<forall>h\<in>H. f h = g h \<rbrakk> \<Longrightarrow> f = g"
apply (rule mHom_eq[of N], assumption+)
 apply (rule ballI)
 apply (unfold generator_def, frule conjunct2, fold generator_def)
 apply (frule sym, thin_tac "linear_span R M (carrier R) H = carrier M",
        simp,
        thin_tac "carrier M = linear_span R M (carrier R) H")
 apply (simp add:linear_span_def)
 apply (case_tac "H = {}", simp, simp add:mHom_0, simp)
 apply (erule exE, (erule bexE)+)
 apply (unfold generator_def, frule conjunct1, fold generator_def)
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
 apply simp
  apply (simp add: linmap_im_lincomb [of "carrier R" N])
 apply (frule_tac s = s and n = n and f = "cmp f fa" and g = "cmp g fa" in 
         Module.linear_comb_eq[of N R "f ` H"])
  apply (simp add: mHom_def aHom_def cong del: image_cong)
       apply (erule conjE)+
       apply (simp add: image_sub [of f "carrier M" "carrier N" H] cong del: image_cong)
      apply assumption
    apply (rule Pi_I, simp add:cmp_def,
         simp add:image_def, 
         frule_tac f = fa and A = "{j. j \<le> n}" and B = H and x = x in 
         funcset_mem, simp, blast)
  apply (rule Pi_I, simp add:cmp_def,
         simp add:image_def, 
         frule_tac f = fa and A = "{j. j \<le> n}" and B = H and x = x in 
         funcset_mem, simp, blast)
  apply (rule ballI, simp add:cmp_def,
         frule_tac f = fa and A = "{j. j \<le> n}" and B = H and x = j in 
         funcset_mem, simp)
   apply blast
 apply assumption
done

section "Existence of homomorphism"

definition
  fgs :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 'a set]  \<Rightarrow>
       'a set" where
  (* free generator span, A is a subset of free generator *)
  "fgs R M A = linear_span R M (carrier R) A"
 
definition
  fsp :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 
  ('b, 'r, 'm2) Module_scheme, 'a \<Rightarrow> 'b, 'a set, 'a set, 'a \<Rightarrow> 'b] \<Rightarrow> bool" where
  "fsp R M N f H A g \<longleftrightarrow> g \<in> mHom R (mdl M (fgs R M A)) N \<and> (\<forall>z\<in>A. f z = g z) \<and> A \<subseteq> H" 
 (* f \<in> H \<rightarrow> N (not a module hom), free span pair condition *)

definition
  fsps :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 
   ('b, 'r, 'm2) Module_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 
                                      (('a set) * ('a \<Rightarrow> 'b)) set" where
  "fsps R M N f H = {Z. \<exists>A g. Z = (A, g) \<and> fsp R M N f H A g}"
         (* free span pairs *)

definition
  od_fm_fun :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 
 ('b, 'r, 'm2) Module_scheme, 'a \<Rightarrow> 'b, 'a set] \<Rightarrow> 
                          (('a set) * ('a \<Rightarrow> 'b)) Order" where
  "od_fm_fun R M N f H = \<lparr>carrier = fsps R M N f H, 
     rel = {Y. Y \<in> (fsps R M N f H) \<times> (fsps R M N f H) \<and> 
                              (fst (fst Y)) \<subseteq> (fst (snd Y))} \<rparr>" 
 (* ordered set free module with function f *)

lemma (in Module) od_fm_fun_carrier:"carrier (od_fm_fun R M N f H) = 
                    fsps R M N f H"
by (simp add:od_fm_fun_def)

lemma (in Module) fgs_submodule:"a \<subseteq> carrier M \<Longrightarrow> 
              submodule R M (fgs R M a)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
apply (subst fgs_def) 
apply (rule linear_span_subModule, assumption, assumption)
done

lemma (in Module) fgs_sub_carrier:"a \<subseteq> carrier M \<Longrightarrow> (fgs R M a) \<subseteq> carrier M" 
by (frule fgs_submodule[of a], 
       rule submodule_subset, assumption+)

lemma (in Module) elem_fgs:"\<lbrakk>a \<subseteq> carrier M; x \<in> a\<rbrakk> \<Longrightarrow> x \<in> fgs R M a"
apply (simp add:fgs_def)
apply (frule l_span_cont_H[of a])
apply (simp add:subsetD)
done

lemma (in Module) fst_chain_subset:"\<lbrakk>R module N; free_generator R M H;
 f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; (a, b) \<in> C\<rbrakk>  \<Longrightarrow> a \<subseteq> carrier M"
apply (subgoal_tac "a \<subseteq> H", frule free_generator_sub)
 apply (rule subset_trans, assumption+)
 apply (frule_tac A = C and B = "fsps R M N f H" and c = "(a, b)" in subsetD, 
        assumption+) 
 apply (simp add:fsps_def fsp_def)
done 

lemma (in Module) empty_fsp:"\<lbrakk>R module N; free_generator R M H; 
     f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> ({}, (\<lambda>x\<in>{\<zero>\<^bsub>M\<^esub>}. \<zero>\<^bsub>N\<^esub>)) \<in> fsps R M N f H"
apply (simp add:fsps_def fsp_def,
       simp add:fgs_def linear_span_def,
       cut_tac submodule_0,
       frule mdl_is_module[of "{\<zero>}"])
apply (rule Module.mHom_test, assumption+)
apply (rule conjI)
 apply (rule Pi_I, simp add:mdl_carrier,
        rule Module.module_inc_zero[of N R], assumption+)
 apply (simp add:mdl_carrier)
 apply (simp add:mdl_def, fold mdl_def)
 apply (cut_tac ag_inc_zero, simp add:ag_l_zero,
        frule Module.module_is_ag[of N R],
        frule aGroup.ag_inc_zero[of N], simp add:aGroup.ag_l_zero[of N])
 apply (rule ballI, frule_tac a = a in sc_a_0, simp)
 apply (simp add:Module.sc_a_0)
done
  
lemma (in Module) mem_fgs_l_comb:"\<lbrakk>K \<noteq> {}; K \<subseteq> carrier M; x \<in> fgs R M K\<rbrakk> \<Longrightarrow> 
        \<exists>(n::nat).  
        \<exists>f \<in> {j. j \<le> (n::nat)} \<rightarrow> K. \<exists>s \<in> {j. j \<le> n} \<rightarrow> carrier R.
                    x = l_comb R M n s f" 
apply (simp add:fgs_def linear_span_def)
done

lemma PairE_lemma: "\<exists>x y. p = (x, y)" by auto

lemma (in Module) fsps_chain_boundTr1:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; 
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; \<forall>a b. (a, b) \<in> C \<longrightarrow> 
              (a, b) \<in> fsps R M N f H; \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}\<rbrakk> \<Longrightarrow> 
      fa \<in> {j. j \<le> (n::nat)} \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C} 
                       \<longrightarrow> (\<exists>(c, d) \<in> C. fa ` {j. j \<le> n} \<subseteq> c)"  
apply (induct_tac n)
 apply (rule impI, simp del: Pi_split_insert_domain)
 apply ((erule exE)+, erule conjE, erule exE)
 apply (frule_tac f = fa and A = "{0}" and B = "\<Union>{a. \<exists>b. (a, b) \<in> C}" and 
                      ?A1.0 = "{0}" in image_sub, simp, simp) 
 apply blast

apply (rule impI)
 apply (frule func_pre, simp) 
 apply (frule_tac f = fa and A = "{j. j \<le> (Suc n)}" and 
        B = "\<Union>{a. \<exists>b. (a, b) \<in> C}" and x = "Suc n" in funcset_mem, simp) 
 apply simp

 apply ((erule exE)+, erule conjE, erule exE, erule conjE, erule exE)
 apply (erule bexE)
 apply (drule_tac x = "(xa, ba)" in bspec, assumption, 
        drule_tac x = xb in bspec, assumption+)
 apply (erule disjE, simp)
 apply (subgoal_tac "(\<lambda>(c, d). fa ` {j. j \<le> Suc n} \<subseteq> c) xb")
 apply auto[1]
 apply (subgoal_tac "(\<lambda>(c, d). fa ` {j. j \<le> Suc n} \<subseteq> c) xb")
 apply (blast,
        cut_tac p = xb in PairE_lemma,
        (erule exE)+, simp, rule subsetI, simp add:image_def,
           erule exE, erule conjE,
        case_tac "xe = Suc n", simp, simp add:subsetD,
        frule_tac m = xe and n = "Suc n" in noteq_le_less, assumption,
        frule_tac x = xe and n = n in Suc_less_le,
        thin_tac "xe \<le> Suc n", thin_tac "xe < Suc n",
        cut_tac c = xd and A = "{y. \<exists>x\<le>n. y = fa x}" and B = xc in
           subsetD, simp, simp, blast, assumption)
 apply (subgoal_tac "(\<lambda>(c, d). fa ` {j. j \<le> Suc n} \<subseteq> c) (xa, ba)")
 apply auto[1]
   apply (simp, rule subsetI, simp add:image_def, erule exE, erule conjE,
         case_tac "xd = Suc n", simp,
         frule_tac m = xd and n = "Suc n" in noteq_le_less, assumption,
           frule_tac x = xd and n = n in Suc_less_le,
           thin_tac "xd \<le> Suc n", thin_tac "xd < Suc n",
         cut_tac p = xb in PairE_lemma, (erule exE)+, simp,
         cut_tac c = "fa xd" and A = "{y. \<exists>x\<le>n. y = fa x}" and B = xe in 
          subsetD, assumption, simp, blast)
   apply (rule_tac c = "fa xd" and A = xe and B = xa in subsetD, assumption+)
done

lemma (in Module) fsps_chain_boundTr1_1:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; 
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; 
       \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}; 
       fa \<in> {j. j \<le> (n::nat)} \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}\<rbrakk> \<Longrightarrow> 
        \<exists>(c, d) \<in> C. fa ` {j. j \<le> n} \<subseteq> c" 
apply (subgoal_tac "\<forall>a b. (a, b) \<in> C \<longrightarrow> (a, b) \<in> fsps R M N f H")
apply (simp add:fsps_chain_boundTr1)
apply ((rule allI)+, rule impI, simp add:subsetD)
done

lemma (in Module) fsps_chain_boundTr1_2:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; 
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; 
       \<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}; 
       fa \<in> {j. j \<le> (n::nat)} \<rightarrow> \<Union>{a. \<exists>b. (a, b) \<in> C}\<rbrakk> \<Longrightarrow> 
       \<exists>P \<in> C. fa ` {j. j \<le> n} \<subseteq> fst P"  
apply (frule_tac N = N and f = f and C = C and fa = fa and n = n in 
         fsps_chain_boundTr1_1, assumption+) 
apply (erule bexE)
apply (cut_tac p = x in PairE_lemma, (erule exE)+)
apply (subgoal_tac "fa ` {j. j \<le> n} \<subseteq> fst x")
apply blast
apply simp
done

lemma (in Module) eSum_in_SubmoduleTr:"\<lbrakk>H \<subseteq> carrier M; K \<subseteq> H\<rbrakk> \<Longrightarrow>
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> K \<and> s \<in> {j. j \<le> n} \<rightarrow> carrier R  \<longrightarrow>
      l_comb R (mdl M (fgs R M K)) n s f = l_comb R M n s f"
apply (induct_tac n)    
 apply (rule impI, (erule conjE)+)
 apply (simp add:l_comb_def del: Pi_split_insert_domain, simp add:mdl_def del: Pi_split_insert_domain, rule impI) 
 apply (simp add:fgs_def del: Pi_split_insert_domain, frule subset_trans[of K H "carrier M"], assumption+) 
 apply (frule funcset_mem[of f "{0}" K 0], simp del: Pi_split_insert_domain,
        frule l_span_cont_H[of K], simp add:subsetD)

apply (rule impI, erule conjE)
 apply (frule func_pre[of  _ _ K], frule func_pre[of  _ _ "carrier R"],
        simp)
 apply (simp add:l_comb_def, simp add:mdl_def)
 apply (rule impI, simp add:fgs_def,frule subset_trans[of K H "carrier M"], 
        assumption+)  
  apply (frule_tac x = "Suc n" and A = "{j. j \<le> Suc n}" in
         funcset_mem[of f _ K], simp,
        frule l_span_cont_H[of K], simp add:subsetD)
done

lemma (in Module) eSum_in_Submodule:"\<lbrakk>H \<subseteq> carrier M; K \<subseteq> H; 
      f \<in> {j. j \<le> (n::nat)} \<rightarrow> K; s \<in> {j. j \<le> n} \<rightarrow> carrier R\<rbrakk> \<Longrightarrow> 
      l_comb R (mdl M (fgs R M K)) n s f = l_comb R M n s f"  
apply (simp add:eSum_in_SubmoduleTr)
done

lemma (in Module) fgs_generator:"H \<subseteq> carrier M \<Longrightarrow>
       generator R (mdl M (fgs R M H)) H" 
apply (simp add:generator_def, simp add:mdl_def, fold mdl_def) 
apply (rule conjI)
 apply (simp add:fgs_def)
 apply (simp add:l_span_cont_H)
apply (rule equalityI)
 apply (rule subsetI, simp add:linear_span_def) 
 apply (case_tac "H = {}", simp add:mdl_def)
 apply (simp add:fgs_def linear_span_def)
 apply simp apply (erule exE, (erule bexE)+)
 apply (cut_tac f = f and n = n and s = s in eSum_in_Submodule[of H H],
        assumption+, simp, assumption+)
 apply simp
 apply (simp add:fgs_def)
 apply (cut_tac sc_Ring, frule Ring.whole_ideal)        
 apply (simp add:l_comb_mem_linear_span)
apply (rule subsetI)
 apply (case_tac "H = {}", simp)
 apply (simp add:fgs_def linear_span_def mdl_def)
 apply (frule_tac x = x in mem_fgs_l_comb[of H], assumption+)
 apply (erule exE, erule bexE, erule bexE)
 apply (simp add:eSum_in_Submodule[THEN sym, of H H])
 apply (frule fgs_submodule[of H],
        frule mdl_is_module[of "fgs R M H"])
 apply (rule Module.l_comb_mem_linear_span[of "mdl M (fgs R M H)" R "carrier R" H], assumption+)
 apply (cut_tac sc_Ring, rule Ring.whole_ideal, assumption)
 apply (simp add:mdl_carrier, simp add:fgs_def l_span_cont_H,
      assumption+)
done 

lemma (in Module) fgs_mono:"\<lbrakk>free_generator R M H; J \<subseteq> K; K \<subseteq> H\<rbrakk>
       \<Longrightarrow> fgs R M J \<subseteq> fgs R M K"   (* H1 \<subseteq> H2 , J \<subseteq> K *)
apply (cut_tac sc_Ring)    
apply (case_tac "J = {}")
 apply (simp add:fgs_def linear_span_def)
 apply (case_tac "K = {}") apply simp apply simp
 apply (frule nonempty_ex [of K])
 apply (erule exE)
 apply (subgoal_tac "(\<lambda>j. x) \<in> {j. j \<le> (0::nat)} \<rightarrow> K",
        subgoal_tac "(\<lambda>j. \<zero>\<^bsub>R\<^esub>) \<in> {j. j \<le> (0::nat)} \<rightarrow> carrier R",
        subgoal_tac "\<zero>\<^bsub>M\<^esub> = l_comb R M 0 (\<lambda>j. \<zero>\<^bsub>R\<^esub>) (\<lambda>j. x)")
 apply blast
 apply (simp add:l_comb_def)
 apply (frule free_generator_sub[of H],
        frule subset_trans[of K H "carrier M"], assumption+,
        frule_tac c = x in subsetD[of K "carrier M"], assumption+,
        simp add:sc_0_m)
 apply (rule Pi_I,
        frule Ring.ring_is_ag [of "R"],
        simp add:aGroup.ag_inc_zero[of R])
 apply (rule Pi_I, assumption)
apply (subgoal_tac "K \<noteq> {}") prefer 2 apply (rule contrapos_pp, simp+)
 apply (rule subsetI)
 apply (simp add:fgs_def, simp add:linear_span_def)
 apply (erule exE, (erule bexE)+)
 apply (frule_tac f = f and A = "{j. j \<le> n}" and B = J and ?B1.0 = K in 
        extend_fun, assumption+)
 apply blast
done

lemma (in Module) empty_fgs:"fgs R M {} = {\<zero>}"
by(simp add:fgs_def linear_span_def)

lemma (in Module) mem_fsps_snd_mHom:"\<lbrakk>R module N; free_generator R M H;
     f \<in> H \<rightarrow> carrier N; (a, b) \<in> fsps R M N f H\<rbrakk>  \<Longrightarrow> 
                    b \<in> mHom R (mdl M (fgs R M a)) N"
by (simp add:fsps_def fsp_def)
(*
lemma (in Module) mem_fsps_snd_mHom1:"\<lbrakk>R module N; free_generator R M H;
     f \<in> H \<rightarrow> carrier N; (a, b) \<in> fsps R M N f H\<rbrakk>  \<Longrightarrow> 
                    b \<in> mHom R (mdl M (fgs R M a)) N"
by (simp add:fsps_def fsp_def) *)

lemma (in Module) mem_fsps_fst_sub:"\<lbrakk>R module N; free_generator R M H;
     f \<in> H \<rightarrow> carrier N; (a, b) \<in> fsps R M N f H\<rbrakk>  \<Longrightarrow>  a \<subseteq> H"
by (simp add:fsps_def fsp_def)

lemma (in Module) mem_fsps_fst_sub1:"\<lbrakk>R module N; free_generator R M H;
     f \<in> H \<rightarrow> carrier N; (a, b) \<in> fsps R M N f H\<rbrakk>  \<Longrightarrow>  a \<subseteq> carrier M"
apply (simp add:fsps_def fsp_def)
apply (frule free_generator_sub[of H],
       rule subset_trans[of a H "carrier M"], simp+)
done

lemma (in Module) Order_od_fm_fun:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> Order (od_fm_fun R M N f H)"
apply (rule Order.intro)
 apply (simp add:od_fm_fun_carrier)
 apply (rule subsetI, simp add:od_fm_fun_def)
 apply (simp add:od_fm_fun_def)
 apply (simp add:od_fm_fun_def)
 apply (cut_tac p = a in PairE_lemma, (erule exE)+,
        cut_tac p = b in PairE_lemma, (erule exE)+, simp)
 apply (frule_tac a = x and b = y in mem_fsps_snd_mHom[of N H f], assumption+,
       frule_tac a = x and b = ya in mem_fsps_snd_mHom[of N H f], assumption+)
 apply (frule_tac a = x and b = y in mem_fsps_fst_sub[of N H f], assumption+,
        frule free_generator_sub,
        frule_tac A = x and B = H and C = "carrier M" in subset_trans,
        assumption+)  
apply (frule_tac a = x in fgs_submodule,
       frule_tac H = "fgs R M x" in mdl_is_module)
 apply (thin_tac "a = (x, y)", thin_tac "b = (x, ya)")
 apply (simp add:mdl_carrier)
 apply (frule_tac H = x in fgs_generator)
 apply (frule_tac R = R and M = "mdl M (fgs R M x)" and N = N and H = x 
       and f = y and g = ya in Module.gen_mHom_eq, assumption+,
       simp add:fsps_def fsp_def, assumption)
apply (simp add:od_fm_fun_def)
done

lemma (in Module) fsps_chain_boundTr2_1:"\<lbrakk>R module N; 
      free_generator R M H; f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; 
      (a, b) \<in> C; (aa, ba) \<in> C; x \<in> fgs R M a; x \<in> fgs R M aa; a \<subseteq> aa\<rbrakk>
      \<Longrightarrow> b x = ba x"
apply (cut_tac sc_Ring, frule Ring.whole_ideal, frule free_generator_sub)
 apply (frule mem_fsps_snd_mHom[of N H f a b], assumption+, simp add:subsetD,
        frule mem_fsps_snd_mHom[of N H f aa ba], assumption+, simp add:subsetD)
 apply (case_tac "a = {}", simp add:empty_fgs)
 apply (cut_tac submodule_0, frule mdl_is_module[of "{\<zero>}"],
        frule subsetD[of C "fsps R M N f H" "(aa, ba)"], assumption+) 
   apply (cut_tac fgs_submodule[of aa],
          frule mdl_is_module[of "fgs R M aa"])
   apply (frule Module.mHom_0[of "mdl M {\<zero>}" R N b], assumption+,
        frule Module.mHom_0[of "mdl M (fgs R M aa)" R N ba], assumption+,
        simp add:mdl_def) 
   apply (frule mem_fsps_fst_sub[of N H f aa ba], assumption+,
          rule subset_trans[of aa H "carrier M"], assumption+)
 apply (frule nonempty_ex[of a], erule exE,
        frule_tac c = xa in subsetD[of a aa], assumption,
        frule_tac x = xa in nonempty[of _ aa],
        thin_tac "xa \<in> a", thin_tac "xa \<in> aa")
 apply (frule mem_fsps_fst_sub[of N H f aa ba], assumption+,
        simp add:subsetD)
 apply (frule mem_fgs_l_comb[of a x],
        frule subset_trans[of a aa H], assumption+,
        rule subset_trans[of a H "carrier M"], assumption+)
 apply (erule exE, (erule bexE)+)
 apply (frule_tac f = fa and A = "{j. j \<le> n}" and B = a and ?B1.0 = aa in 
                  extend_fun, assumption+)
 apply (frule subsetD[of C "fsps R M N f H" "(a, b)"], assumption+,
        frule subsetD[of C "fsps R M N f H" "(aa, ba)"], assumption+,
        thin_tac "C \<subseteq> fsps R M N f H")
 apply (cut_tac fgs_submodule[of a],
        frule mdl_is_module[of "fgs R M a"],
        cut_tac fgs_submodule[of  aa], 
        frule mdl_is_module[of "fgs R M aa"]) (* 
 apply (simp add:fsps_def fsp_def, (erule conjE)+) *)
 apply (frule subset_trans[of a aa H], assumption+)
 apply (frule_tac f1 = fa and n1 = n and s1 = s in eSum_in_Submodule[THEN sym,
        of H a], assumption+,
        frule_tac s = s and n = n and g = fa in Module.linmap_im_lincomb[of 
        "mdl M (fgs R M a)" R "carrier R" N _ a], assumption+,
        simp add:mdl_carrier,
        subst fgs_def, rule_tac l_span_cont_H,
        frule subset_trans[of a H "carrier M"], assumption+, simp,
        thin_tac "b (l_comb R (mdl M (fgs R M a)) n s fa) = 
                                                  l_comb R N n s (cmp b fa)",
        rotate_tac -1, frule sym, 
        thin_tac "l_comb R M n s fa = l_comb R (mdl M (fgs R M a)) n s fa",
        simp,
        thin_tac "l_comb R (mdl M (fgs R M a)) n s fa = l_comb R M n s fa")
 apply (frule_tac f1 = fa and n1 = n and s1 = s in eSum_in_Submodule[THEN sym,
        of H aa], assumption+,
        frule_tac s = s and n = n and g = fa in Module.linmap_im_lincomb[of 
        "mdl M (fgs R M aa)" R "carrier R" N _ aa], assumption+,
        simp add:mdl_carrier,
        subst fgs_def, rule_tac l_span_cont_H,
        frule subset_trans[of a H "carrier M"], assumption+, simp+,
        thin_tac "l_comb R M n s fa = l_comb R (mdl M (fgs R M aa)) n s fa",
        thin_tac "ba (l_comb R (mdl M (fgs R M aa)) n s fa) =
        l_comb R N n s (cmp ba fa)")
 apply (simp add:fsps_def fsp_def)
 apply (rule_tac s = s and n = n and f = "cmp b fa" and g = "cmp ba fa" in
        Module.linear_comb_eq[of N R "f ` H"], assumption+,
        simp add:image_sub0, assumption)
 apply (rule Pi_I, simp add:cmp_def,
       frule_tac x = xa and f = fa and A = "{j. j \<le> n}" and B = a in 
       funcset_mem, simp,
       frule_tac m = "fa xa" in Module.mHom_mem[of "mdl M (fgs R M a)" R N b],
         assumption+,
       simp add:mdl_carrier fgs_def, rule_tac c = "fa xa" in 
         subsetD[of a "linear_span R M (carrier R) a"],
        rule l_span_cont_H,
        frule subset_trans[of a aa H], assumption+,
        rule subset_trans[of a H "carrier M"], assumption+,
        drule_tac x = "fa xa" in bspec, assumption,
        frule_tac c = "fa xa" in subsetD[of a H], assumption+,
        rotate_tac -2, frule sym, thin_tac "f (fa xa) = b (fa xa)", simp)
  apply (rule Pi_I, simp add:cmp_def,
        frule_tac x = xa and f = fa and A = "{j. j \<le> n}" and B = aa in 
        funcset_mem, simp,
        frule_tac c = "fa xa" in subsetD[of aa H], assumption+,
        drule_tac x = "fa xa" in bspec, assumption,
        rotate_tac -1, frule sym, thin_tac "f (fa xa) = ba (fa xa)",
        simp)
  apply (rule ballI, simp add:cmp_def,
        frule_tac x = j and f = fa and A = "{j. j \<le> n}" and B = a in 
        funcset_mem, simp)
  apply (frule_tac x = "fa j" in bspec, assumption,
               thin_tac "\<forall>z\<in>a. f z = b z",
               frule_tac c = "fa j" in subsetD[of a aa], assumption+,
               frule_tac x = "fa j" in bspec, assumption,
               thin_tac "\<forall>z\<in>aa. f z = ba z")
  apply (rotate_tac -3, frule sym, 
               thin_tac "f (fa j) = b (fa j)", frule sym,
               thin_tac "f (fa j) = ba (fa j)", simp)
  apply (simp add:subset_trans[of aa H "carrier M"])
  apply (frule subset_trans[of a aa H], assumption+,
         simp add:subset_trans[of a H "carrier M"])
done

lemma (in Module) fsps_chain_boundTr2_2:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; 
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; C \<noteq> {}; (a, b) \<in> C; 
       x \<in> fgs R M a; (a1, b1) \<in> C; x \<in> fgs R M a1\<rbrakk> \<Longrightarrow> b x = b1 x"
 apply (frule_tac x = "(a, b)" in bspec, assumption,
        thin_tac "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a",
        frule_tac x = "(a1, b1)" in bspec, assumption,
        thin_tac "\<forall>ba\<in>C. fst (a, b) \<subseteq> fst ba \<or> fst ba \<subseteq> fst (a, b)", simp)
 apply (erule disjE)
 apply (rule fsps_chain_boundTr2_1[of N H f C a b a1 b1], assumption+)  
 apply (frule fsps_chain_boundTr2_1[of N H f C a1 b1 a b], assumption+)  
 apply (rule sym, assumption)
done

lemma (in Module) fsps_chain_boundTr2:"\<And>x. \<lbrakk>R module N; free_generator R M H;
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H;  
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; 
       x \<in> (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})); C \<noteq> {}\<rbrakk>  \<Longrightarrow> 
    (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) \<in> 
    (carrier N) \<and> 
    (\<exists>a1 b1. (a1, b1) \<in> C \<and> x \<in> fgs R M a1 \<and> 
    (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) = 
              b1 x)"
apply (cut_tac sc_Ring, frule Ring.whole_ideal[of R])
apply (case_tac "\<Union>{a. \<exists>b. (a, b) \<in> C} = {}", simp add: empty_fgs,
       frule nonempty_ex[of C], erule exE,
       cut_tac p = xa in PairE_lemma, (erule exE)+,
       frule_tac c = xa in subsetD[of C "fsps R M N f H"], assumption+, simp)
apply (frule_tac a = xb and b = y in mem_fsps_snd_mHom[of N H f], 
       assumption+, simp add:subsetD)
apply (rename_tac a b a1 b1) 
 apply (subgoal_tac "\<exists>!y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
                                          \<zero> \<in> (fgs R M a) \<and> y = b \<zero>)",
        subgoal_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
         \<zero> \<in> fgs R M a \<and> y = b \<zero>)) \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
          \<zero> \<in> fgs R M a \<and> 
     (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> \<zero> \<in> fgs R M a \<and> y = b \<zero>)) =
      b \<zero>)")  
 prefer 2
    apply (rule theI', simp, simp)
 apply (rule ex_ex1I)
   apply (cut_tac a = a1 in fgs_submodule)
   apply (frule_tac a = a1 and b = b1 in mem_fsps_fst_sub[of N H f],
          assumption+, simp add:subsetD, frule free_generator_sub[of H],
          rule subset_trans[of _ H "carrier M"], assumption+,
        frule_tac H = "fgs R M a1" in mdl_is_module,
        frule_tac M = "mdl M (fgs R M a1)" and f = b1 in 
                                   Module.mHom_0[of _ R N], assumption+,
        frule_tac H = "fgs R M a1" in submodule_inc_0,
        frule Module.module_inc_zero[of N],
        thin_tac "b1 \<in> mHom R (mdl M (fgs R M a1)) N",
        thin_tac "R module mdl M (fgs R M a1)",
        simp add:mdl_def) 
   apply (rotate_tac -3, frule sym, thin_tac "b1 \<zero> = \<zero>\<^bsub>N\<^esub>", blast)
   apply ((erule conjE)+, (erule exE)+, (erule conjE)+)
   apply (cut_tac a = aa in fgs_submodule,
          frule_tac a = aa and b = ba in mem_fsps_fst_sub[of N H f],
          assumption+, simp add:subsetD,
          frule free_generator_sub, rule subset_trans, assumption+,
          simp add:subsetD,
          frule_tac H = "fgs R M aa" in mdl_is_module,
          frule_tac M = "mdl M (fgs R M aa)" and f = ba in 
                                   Module.mHom_0[of _ R N], assumption+,
          frule_tac H = "fgs R M aa" in submodule_inc_0,
          frule_tac c = "(aa, ba)" in subsetD[of C "fsps R M N f H"], 
          assumption+, simp,
          frule_tac a = aa and b = ba in mem_fsps_snd_mHom[of N H f],
          assumption+, simp add:mdl_def)  
   apply (cut_tac a = ab in fgs_submodule,
          frule_tac a = ab and b = bb in mem_fsps_fst_sub[of N H f],
          assumption+, simp add:subsetD,
          frule free_generator_sub, rule subset_trans[of _ H "carrier M"],
          assumption+,
          frule_tac H = "fgs R M ab" in mdl_is_module,
          frule_tac M = "mdl M (fgs R M ab)" and f = bb in 
                                   Module.mHom_0[of _ R N], assumption+) 
  apply (fold mdl_def,
         frule_tac c = "(ab, bb)" in subsetD[of C "fsps R M N f H"], 
         assumption+,
          frule_tac a = ab and b = bb in mem_fsps_snd_mHom[of N H f], 
          assumption+, simp add:mdl_def)
 (*********** case \<Union>{a. \<exists>b. (a, b) \<in> C} = {} done **********)
 apply (subgoal_tac "\<exists>!y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
                                          x \<in> (fgs R M a) \<and> y = b x)",
        subgoal_tac "(THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
         x \<in> fgs R M a \<and> y = b x)) \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> 
          x \<in> fgs R M a \<and> 
     (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) =
      b x)")  
 prefer 2
   apply (rule theI', simp, simp)
   apply (rule ex_ex1I)
   apply (frule_tac K = "\<Union>{a. \<exists>b. (a, b) \<in> C}" and x = x in mem_fgs_l_comb)
   apply (rule subsetI, simp,
          thin_tac "\<exists>x. (\<exists>b. (x, b) \<in> C) \<and> x \<noteq> {}",
          erule exE, erule conjE, erule exE,
          frule_tac a = xb and b = b in mem_fsps_fst_sub[of N H f],
                assumption+, simp add:subsetD,
          frule free_generator_sub[of H], simp add:subsetD, assumption)
   apply (erule exE, (erule bexE)+)
   apply (frule_tac fa = fa and n = n in fsps_chain_boundTr1_1[of N H f C],
          assumption+)
   apply (frule_tac A = "\<Union>{a. \<exists>b. (a, b) \<in> C}" in nonempty_ex, 
          erule exE, simp, assumption+, erule bexE,
          cut_tac p = xa in PairE_lemma, (erule exE)+, simp)
   apply (frule_tac a = xb and b = y in mem_fsps_fst_sub[of N H f], 
               assumption+, simp add:subsetD,
          frule free_generator_sub[of H], 
          frule_tac A = xb in subset_trans[of _ H "carrier M"], assumption+)
   apply (frule_tac H = xb and s = s and n = n and f = fa in 
          l_comb_mem_linear_span[of "carrier R"], assumption+,
          rule Pi_I,
          frule_tac a = xc and A = "{j. j \<le> n}" and f = fa in 
          mem_in_image2, simp add:image_def, erule exE, blast,
          fold fgs_def) 
   apply (frule_tac a = xb and b = y in mem_fsps_snd_mHom[of N H f],
          assumption+, simp add:subsetD,
          frule_tac a = xb in fgs_submodule,
          frule_tac H = "fgs R M xb" in mdl_is_module,
          frule_tac R = R and M = "mdl M (fgs R M xb)" and N = N and
                f = y and m = x in Module.mHom_mem, assumption+,
          simp add:mdl_carrier, simp, blast)
 apply ((erule conjE)+, (erule exE)+, (erule conjE)+) 
  apply (frule_tac x = "(a, b)" in bspec, assumption,
         rotate_tac -1,
         frule_tac x = "(aa, ba)" in bspec, assumption,
         thin_tac "\<forall>ba\<in>C. fst (a, b) \<subseteq> fst ba \<or> fst ba \<subseteq> fst (a, b)",
         simp)
 apply (rule_tac a = a and b = b and ?a1.0 = aa and ?b1.0 = ba and x = x in 
        fsps_chain_boundTr2_2[of N H f C], assumption+)
done

lemma (in Module) Un_C_submodule:"\<lbrakk>R module N; free_generator R M H; 
     f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; C \<noteq> {};
     \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a\<rbrakk> \<Longrightarrow> 
       submodule R M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))"
 apply (cut_tac sc_Ring, frule free_generator_sub[of H],
        frule Ring.whole_ideal)
 apply (subst fgs_def)
 apply (rule linear_span_subModule, assumption+) 
 apply (rule subsetI, simp) 
 apply (erule exE, erule conjE, erule exE,
        frule_tac c = "(xa, b)" in subsetD[of C "fsps R M N f H"], assumption+,
        frule_tac a = xa and b = b in mem_fsps_fst_sub[of N H f], assumption+,
        frule free_generator_sub, frule_tac A = xa in 
               subset_trans[of _ H "carrier M"], assumption+,
        simp add:subsetD)   
done

lemma (in Module) Un_C_fgs_sub:"\<lbrakk>R module N; free_generator R M H; 
     f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; C \<noteq> {};
     \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a\<rbrakk> \<Longrightarrow>
     \<Union>{a. \<exists>b. (a, b) \<in> C} \<subseteq> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})"
apply (simp add:fgs_def)
apply (rule l_span_cont_H)
apply (frule Un_C_submodule[of N H f C], assumption+)
apply (rule subsetI, simp, erule exE, erule conjE, erule exE)
apply (frule_tac a = xa and b = b in mem_fsps_fst_sub[of N H f], assumption+,
       simp add:subsetD,
       frule free_generator_sub[of H],
       frule_tac A = xa and B = H and C = "carrier M" in subset_trans, 
       assumption+, simp add:subsetD)
done

lemma (in Module) Chain_3_supset:"\<lbrakk>R module N; free_generator R M H; 
    f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; C \<noteq> {};
   \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; (a1, b1) \<in> C; (a2, b2) \<in> C;
   (a3, b3) \<in> C\<rbrakk> \<Longrightarrow> \<exists>(g, h)\<in>C. a1 \<subseteq> g \<and> a2 \<subseteq> g \<and> a3 \<subseteq> g"
proof -
  assume "(a1, b1) \<in> C"
    "(a2, b2) \<in> C"
    "(a3, b3) \<in> C"
  then have A: "a1 \<in> fst ` C"
    "a2 \<in> fst ` C"
    "a3 \<in> fst ` C"
    by (simp_all add: image_iff) force+
  assume "\<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a"
  with A have "a1 \<subseteq> a2 \<or> a2 \<subseteq> a1"
    "a1 \<subseteq> a3 \<or> a3 \<subseteq> a1"
    "a2 \<subseteq> a3 \<or> a3 \<subseteq> a2"
    by auto
  with A have "\<exists>a\<in>fst ` C. a1 \<subseteq> a \<and> a2 \<subseteq> a \<and> a3 \<subseteq> a"
    by auto
  then obtain a where "a \<in> fst ` C" and C: "a1 \<subseteq> a" "a2 \<subseteq> a" "a3 \<subseteq> a" by blast
  then obtain b where "(a, b) \<in> C" by auto
  with C show "\<exists>(a, b)\<in>C. a1 \<subseteq> a \<and> a2 \<subseteq> a \<and> a3 \<subseteq> a"
    by auto
qed

lemma (in Module) fsps_chain_bound1:"\<lbrakk>R module N; free_generator R M H;  
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H;  
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a; C \<noteq> {}\<rbrakk>  \<Longrightarrow> 
      (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). (THE y. y \<in> carrier N \<and> 
                    (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))) \<in> 
       mHom R (mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))) N"
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
apply (frule Un_C_submodule[of N H f C], assumption+)
apply (frule mdl_is_module[of "fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})"])
apply (rule Module.mHom_test[of "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))" R N 
      "\<lambda>x\<in>fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}). THE y. y \<in> carrier N \<and> 
        (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)"], assumption+)
apply (rule conjI)
 apply (rule Pi_I,
        frule submodule_subset[of "fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})"],
        simp add:mdl_carrier, simp add:fsps_chain_boundTr2) 
apply (rule conjI)
 apply (simp add:mdl_carrier)
apply (rule conjI)
 apply (rule ballI)+
 apply (frule Module.module_is_ag[of "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))"
         R])
 apply (frule_tac x = m and y = n in aGroup.ag_pOp_closed[of 
          "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))"], assumption+)
 apply (frule_tac x = m in fsps_chain_boundTr2[of N H f C], assumption+,
        simp add:mdl_carrier, assumption, erule conjE, (erule exE)+, 
        (erule conjE)+,
        frule_tac x = n in fsps_chain_boundTr2[of N H f C], assumption+,
        simp add:mdl_carrier, assumption, erule conjE, (erule exE)+, 
        (erule conjE)+,
        frule_tac x = "m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n" in 
        fsps_chain_boundTr2[of N H f C], assumption+,
        simp add:mdl_carrier, assumption, erule conjE, (erule exE)+, 
        (erule conjE)+) apply (simp add:mdl_carrier)
 apply (thin_tac "(THE y.
            y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) =
        b1 m") apply (
        thin_tac "(THE y.
            y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> n \<in> fgs R M a \<and> y = b n)) =
        b1a n") apply (
        thin_tac "(THE y.
            y \<in> carrier N \<and>
            (\<exists>a b. (a, b) \<in> C \<and>
                   m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n \<in> fgs R M a \<and>
                   y = b (m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n))) =
        b1b (m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n)")
 apply (thin_tac "m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n
        \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})",
        thin_tac "b1b (m \<plusminus>\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> n) \<in> carrier N",
        simp add:mdl_def, fold mdl_def) 
 apply (cut_tac ?a1.0 = a1 and ?b1.0 = b1 and ?a2.0 = a1a and ?b2.0 = b1a and 
        ?a3.0 = a1b and ?b3.0 = b1b in Chain_3_supset[of N H f C], assumption+)
 apply (erule bexE)
 apply (cut_tac p = x in PairE_lemma, (erule exE)+, simp, (erule conjE)+)
 apply (frule_tac J = a1b and K = xa in fgs_mono[of H], assumption+,
        rule_tac a = xa and b = y in mem_fsps_fst_sub[of N H f], assumption+, 
        simp add:subsetD,
        frule_tac J = a1 and K = xa in fgs_mono[of H], assumption+,
        rule_tac a = xa and b = y in mem_fsps_fst_sub[of N H f], assumption+,
        simp add:subsetD, 
        frule_tac J = a1a and K = xa in fgs_mono[of H], assumption+,
        rule_tac a = xa and b = y in mem_fsps_fst_sub[of N H f], assumption+, 
        simp add:subsetD)
  apply (frule_tac c = m and A = "fgs R M a1" and B = "fgs R M xa" in subsetD,
          assumption+,
         frule_tac c = n and A = "fgs R M a1a" and B = "fgs R M xa" in subsetD,
          assumption+,
         frule_tac c = "m \<plusminus> n" and A = "fgs R M a1b" and B = "fgs R M xa" in 
          subsetD, assumption+)
  apply (frule_tac a = a1 and b = b1 and aa = xa and ba = y in 
          fsps_chain_boundTr2_1[of N H f C], assumption+, simp,
         frule_tac a = a1a and b = b1a and aa = xa and ba = y in 
          fsps_chain_boundTr2_1[of N H f C], assumption+, simp,
         frule_tac a = a1b and b = b1b and aa = xa and ba = y in 
          fsps_chain_boundTr2_1[of N H f C], assumption+, simp)  
  apply (thin_tac "submodule R M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))",
         thin_tac "R module mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))",
         thin_tac "m \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})",
         thin_tac "n \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})",
         thin_tac "aGroup (mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})))",
         thin_tac "y m \<in> carrier N",  thin_tac "(a1, b1) \<in> C",
         thin_tac "m \<in> fgs R M a1",   thin_tac "y n \<in> carrier N",
         thin_tac "(a1a, b1a) \<in> C",   thin_tac "n \<in> fgs R M a1a",
         thin_tac "(a1b, b1b) \<in> C",   thin_tac "m \<plusminus> n \<in> fgs R M a1b",
         thin_tac "a1 \<subseteq> xa",          thin_tac "a1a \<subseteq> xa",
         thin_tac "a1b \<subseteq> xa",         thin_tac "fgs R M a1 \<subseteq> fgs R M xa",
         thin_tac "fgs R M a1a \<subseteq> fgs R M xa",
         thin_tac "b1b (m \<plusminus> n) = y (m \<plusminus> n)",
         thin_tac "b1 m = y m", thin_tac "b1a n = y n")
  apply (cut_tac a = xa in fgs_submodule, 
         frule_tac c = "(xa, y)" in subsetD[of C "fsps R M N f H"], 
         assumption+,
         simp add:mem_fsps_fst_sub1)
  apply (frule_tac H = "fgs R M xa" in mdl_is_module)
  apply (frule_tac a = xa and b = y in mem_fsps_snd_mHom[of N H f],
         assumption+, simp add:subsetD)
  apply (frule_tac R = R and M = "mdl M (fgs R M xa)" and N = N and f = y and 
         m = m and n = n in Module.mHom_add, assumption+,
         simp add:mdl_carrier, simp add:mdl_carrier, simp add:mdl_def)
(************** mHom_add ***********************)

apply (rule ballI)+
 apply (frule_tac a = a and m = m in Module.sc_mem[of 
          "mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))" R], assumption+)
 apply (frule_tac x = m in fsps_chain_boundTr2[of N H f C], assumption+,
        simp add:mdl_carrier, assumption, erule conjE, (erule exE)+, 
        (erule conjE)+,
        frule_tac x = "a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m" in 
        fsps_chain_boundTr2[of N H f C], assumption+,
        simp add:mdl_carrier, assumption, erule conjE, (erule exE)+, 
        (erule conjE)+) 
 apply (simp add:mdl_carrier)
 apply (thin_tac "(THE y.
            y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> m \<in> fgs R M a \<and> y = b m)) =
        b1 m",
        thin_tac "b1a (a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m) \<in> carrier N",
        thin_tac "(THE y.
            y \<in> carrier N \<and>
            (\<exists>aa b.
                (aa, b) \<in> C \<and>
                a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m \<in> fgs R M aa \<and>
                y = b (a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m))) =
        b1a (a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m)",
        thin_tac "a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))\<^esub> m
        \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})",
        thin_tac "submodule R M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))",
        thin_tac "R module mdl M (fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}))")
  apply (simp add:mdl_def,
        thin_tac "m \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})",
        thin_tac "b1 m \<in> carrier N")
  apply (frule_tac x = "(a1, b1)" in bspec, assumption,
         rotate_tac -1,
         drule_tac x = "(a1a, b1a)" in bspec, assumption,
         simp)
  apply (erule disjE,
        frule_tac J = a1 and K = a1a in fgs_mono[of H], assumption+,
        rule_tac a = a1a and b = b1a in mem_fsps_fst_sub[of N H f], 
        assumption+, simp add:subsetD,
        frule_tac c = m and A = "fgs R M a1" and B = "fgs R M a1a" in subsetD,
        assumption+)
  apply (cut_tac a = a1a in fgs_submodule,
         frule_tac c = "(a1a, b1a)" in subsetD[of C "fsps R M N f H"],
                               assumption+, simp add:mem_fsps_fst_sub1,
         frule_tac H = "fgs R M a1a" in mdl_is_module,
         frule_tac a = a1a and b = b1a in mem_fsps_snd_mHom[of N H f],
          assumption+, simp add:subsetD)
  apply (frule_tac R = R and M = "mdl M (fgs R M a1a)" and N = N and m = m 
         and f = b1a and a = a in Module.mHom_lin, assumption+,
         simp add:mdl_carrier, assumption+, simp add:mdl_def,
                fold mdl_def)
  apply (frule_tac a = a1 and b = b1 and ?a1.0 = a1a and ?b1.0 = b1a and x = m
         in fsps_chain_boundTr2_2[of N H f C], assumption+, simp)

  apply (frule_tac J = a1a and K = a1 in fgs_mono[of H], assumption+,
        rule_tac a = a1 and b = b1 in mem_fsps_fst_sub[of N H f], 
        assumption+, simp add:subsetD,
        frule_tac c = "a \<cdot>\<^sub>s m" and A = "fgs R M a1a" and B = "fgs R M a1" in 
        subsetD, assumption+)
  apply (frule_tac a = a1a and b = b1a and ?a1.0 = a1 and ?b1.0 = b1 and 
         x = "a \<cdot>\<^sub>s m" in fsps_chain_boundTr2_2[of N H f C], assumption+, simp)
  apply (cut_tac a = a1 in fgs_submodule,
         frule_tac c = "(a1, b1)" in subsetD[of C "fsps R M N f H"],
           assumption+, simp add:mem_fsps_fst_sub1,
         frule_tac H = "fgs R M a1" in mdl_is_module,
         frule_tac a = a1 and b = b1 in mem_fsps_snd_mHom[of N H f],
          assumption+, simp add:subsetD)
  apply (frule_tac R = R and M = "mdl M (fgs R M a1)" and N = N and m = m 
         and f = b1 and a = a in Module.mHom_lin, assumption+,
         simp add:mdl_carrier, assumption+, simp add:mdl_def) 
done

lemma (in Module) fsps_chain_bound2:"\<lbrakk>R module N; free_generator R M H;  
       f \<in> H \<rightarrow> carrier N; C \<subseteq> fsps R M N f H; C \<noteq> {}; 
       \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a\<rbrakk>  \<Longrightarrow> 
   \<forall>y\<in>(\<Union>{a. \<exists>b. (a, b) \<in> C}). (\<lambda>x\<in>(fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})). 
   (THE y. y \<in> carrier N \<and> (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))) y =
    f y"
apply (rule ballI)
 apply (subgoal_tac "y \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})")
 prefer 2 
 apply simp
 apply (erule exE, erule conjE, erule exE)
 apply (frule  Un_C_fgs_sub[of N H f C], assumption+)
 apply (rule_tac c = y in subsetD[of "\<Union>{a. \<exists>b. (a, b) \<in> C}"
                   "fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})"], assumption+)
 apply (simp, blast)

 apply simp
 apply (frule_tac x = y in fsps_chain_boundTr2[of N H f C], assumption+)
 apply (erule conjE, (erule exE)+, erule conjE, erule exE, (erule conjE)+)
 apply (simp,
       thin_tac "(THE ya. ya \<in> carrier N \<and>
            (\<exists>a b. (a, b) \<in> C \<and> y \<in> fgs R M a \<and> ya = b y)) = b1 y")
 apply (frule_tac c = "(x, b)" in subsetD[of C "fsps R M N f H"],
        assumption+,
        simp add:fsps_def fsp_def, (erule conjE)+,
        thin_tac "\<forall>z\<in>x. f z = b z")
 apply (frule_tac x = y and a = x and b = b and ?a1.0 = a1 and ?b1.0 = b1 in
        fsps_chain_boundTr2_2[of N H f C], assumption+,
        simp add:fsps_def fsp_def, assumption+, subst fgs_def,
        rule_tac c = y and A = x and B = "linear_span R M (carrier R) x"
        in subsetD,
        rule l_span_cont_H,
        frule free_generator_sub[of H], rule subset_trans[of _ H "carrier M"],
         assumption+, simp)
done

lemma (in Module) od_fm_fun_Chain:"\<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N; Algebra2.Chain (od_fm_fun R M N f H) C; C \<noteq> {}\<rbrakk> \<Longrightarrow> 
      \<forall>a\<in>C. \<forall>b\<in>C. fst a \<subseteq> fst b \<or> fst b \<subseteq> fst a"
apply (frule Order_od_fm_fun[of N H f], assumption+)
 apply (rule ballI)+
 apply (simp add:Algebra2.Chain_def, erule conjE, simp add:Torder_def, erule conjE,
        simp add:Torder_axioms_def)
 apply (simp add:Order.Iod_carrier)
  apply (auto simp add: Iod_def od_fm_fun_def ole_def)
  apply blast
done

lemma (in Module) od_fm_fun_inPr0:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; Algebra2.Chain (od_fm_fun R M N f H) C; C \<noteq> {};
       \<exists>b. (y, b) \<in> C; z \<in> y\<rbrakk>  \<Longrightarrow> z \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})"
apply (frule Un_C_fgs_sub[of N H f C], assumption+)
 apply (simp add:Algebra2.Chain_def od_fm_fun_def, assumption) 
 apply (simp add:od_fm_fun_Chain)
 apply (rule_tac subsetD[of "\<Union>{a. \<exists>b. (a, b) \<in> C}" 
                     "fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C})" z], assumption+)
 apply (simp, blast)
done

lemma (in Module) od_fm_fun_indPr1:" \<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N; Algebra2.Chain (od_fm_fun R M N f H) C; C \<noteq> {}\<rbrakk> \<Longrightarrow>
      (\<Union>{a. \<exists>b. (a, b) \<in> C}, 
         \<lambda>x \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}). THE y. y \<in> carrier N \<and>
         (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x)) \<in> fsps R M N f H"
apply (simp add:fsps_def fsp_def, rule conjI)
 apply (rule fsps_chain_bound1[of N H f C], assumption+)
 apply (simp add:od_fm_fun_def Algebra2.Chain_def)
 apply (simp add:od_fm_fun_Chain, assumption)
apply (rule conjI)
 apply (rule allI, rule impI)
 apply (rule ballI)
 apply (simp add:od_fm_fun_inPr0[of N H f C])
 apply (frule fsps_chain_bound2[of N H f C], assumption+,
        simp add:Algebra2.Chain_def od_fm_fun_def, assumption)
 apply (simp add:od_fm_fun_Chain)
 apply (drule_tac x = z in bspec)
  apply (simp, blast) 
 apply (simp add:od_fm_fun_inPr0)
apply (rule subsetI, simp, erule exE, erule conjE, erule exE)
 apply (frule Order_od_fm_fun[of N H f], assumption+,
        frule Order.Chain_sub[of "od_fm_fun R M N f H" C], assumption,
        thin_tac "Algebra2.Chain (od_fm_fun R M N f H) C",
        thin_tac "Order (od_fm_fun R M N f H)")
 apply (simp add:od_fm_fun_def)
 apply (frule_tac a = xa and b = b in mem_fsps_fst_sub[of N H f], assumption+,
        simp add:subsetD, simp add:subsetD)
done

lemma (in Module) od_fm_fun_indPr2:" \<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N; Algebra2.Chain (od_fm_fun R M N f H) C; C \<noteq> {}\<rbrakk> \<Longrightarrow>
     ub\<^bsub>od_fm_fun R M N f H\<^esub> C (\<Union>{a. \<exists>b. (a, b) \<in> C}, 
         \<lambda>x \<in> fgs R M (\<Union>{a. \<exists>b. (a, b) \<in> C}). THE y. y \<in> carrier N \<and>
                          (\<exists>a b. (a, b) \<in> C \<and> x \<in> fgs R M a \<and> y = b x))"
apply (frule Order_od_fm_fun[of N H f], assumption+,
       simp add:upper_bound_def)

 apply (simp add:od_fm_fun_def, fold od_fm_fun_def,
        frule od_fm_fun_indPr1[of N H f C], assumption+, simp)

 apply (rule ballI,
        subst od_fm_fun_def, subst ole_def, simp)
 apply (rule conjI)
 apply (frule Order.Chain_sub[of "od_fm_fun R M N f H" C], assumption,
        simp add:od_fm_fun_carrier, simp add:subsetD)
 apply (unfold split_paired_all,
        rule subsetI, simp, blast)
done
  
lemma (in Module) od_fm_fun_inductive:"\<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> inductive_set (od_fm_fun R M N f H)"
apply (frule Order_od_fm_fun[of N H f], assumption+)
apply (simp add:inductive_set_def)
apply (rule allI, rule impI)
apply (case_tac "C \<noteq> {}")
 apply (frule_tac C = C in od_fm_fun_indPr2[of N H f], assumption+)
 apply blast
apply simp
 apply (simp add:upper_bound_def)
 apply (subst od_fm_fun_def, simp)
 apply (frule empty_fsp[of N H f], assumption+, blast)
done

lemma (in Module) sSum_eq:"\<lbrakk>R module N; free_generator R M H; H1 \<subseteq> H; 
      h \<in> H - H1\<rbrakk> \<Longrightarrow>  (fgs R M H1) \<minusplus> (fgs R M {h}) = fgs R M (H1 \<union> {h})"
apply (cut_tac sc_Ring, frule Ring.whole_ideal)
apply (frule free_generator_sub)
 apply (frule subset_trans[of H1 H "carrier M"], assumption+,
        frule fgs_sub_carrier[of H1])
 apply (cut_tac subset_trans[of "{h}" "H - H1" "carrier M"],
         frule fgs_sub_carrier[of "{h}"])
 apply (simp add:set_sum[of "fgs R M H1" "fgs R M {h}"])
 apply (rule equalityI)
  apply (rule subsetI, simp, (erule bexE)+)
  apply (case_tac "H1 = {}", simp add:empty_fgs) 
  apply (frule_tac c = k in subsetD[of "fgs R M {h}" "carrier M"], assumption+)
  apply (simp add:ag_l_zero)
  apply (cut_tac fgs_mono[of H H1 "insert h H1"],
         frule_tac c = ha in subsetD[of "fgs R M H1" "fgs R M (insert h H1)"],
          assumption+,
         cut_tac fgs_mono[of H "{h}" "insert h H1"],
         frule_tac c = k in subsetD[of "fgs R M {h}" "fgs R M (insert h H1)"],
          assumption+)
  apply (simp add:fgs_def,
         cut_tac sc_Ring, frule Ring.whole_ideal,
         rule linear_span_pOp_closed, assumption+,
         rule subsetI, simp, erule disjE, simp, simp add:subsetD, assumption+,
         rule subsetI, simp, rule subsetI, simp, erule disjE, simp, 
         simp add:subsetD, assumption+, rule subsetI, simp,
         rule subsetI, simp, erule disjE, simp, simp add:subsetD)
 apply (rule subsetI)

 apply (cut_tac x = x in mem_fgs_l_comb[of "insert h H1"],
        simp,
        rule subsetI, simp, erule disjE, simp, simp add:subsetD, assumption+)
 apply (erule exE, (erule bexE)+)
 apply (case_tac "f ` {j. j \<le> n} \<subseteq> H1")
 apply (frule_tac s = s and n = n and f = f in 
           l_comb_mem_linear_span[of "carrier R" H1], assumption+)
  apply (rule Pi_I)
  apply (frule_tac f = f and A = "{j. j \<le> n}" and B = "insert h H1" and 
         a = xa in mem_in_image, assumption+, simp add:subsetD)
  apply (fold fgs_def)
  apply (frule fgs_sub_carrier[of H1]) 
  apply (frule_tac c = "l_comb R M n s f" in subsetD[of "fgs R M H1" 
             "carrier M"], assumption+)
  apply (frule_tac t = "l_comb R M n s f" in ag_r_zero[THEN sym], simp)
  apply (cut_tac fgs_submodule[of "{h}"],
        frule submodule_inc_0[of "fgs R M {h}"], blast,
        rule subsetI, simp)
 
  apply (frule_tac f = f and A = "{j. j \<le> n}" and B = "insert h H1" in
          image_sub0)
  apply (frule_tac Y = "f ` {j. j \<le> n}" and a = h and X = H1 in sub_inserted1,
         assumption+, erule conjE,
         thin_tac "\<not> f ` {j. j \<le> n} \<subseteq> H1", 
         thin_tac "f ` {j. j \<le> n} \<subseteq> insert h H1", erule conjE) 
  apply (cut_tac H = "insert h H1" and f = f and n = n and s = s in   
         unique_expression2)
         apply (rule subsetI, simp, erule disjE, simp, simp add:subsetD)
         apply assumption+
  apply ((erule exE)+, (erule conjE)+, simp)
  apply (simp add:bij_to_def, erule conjE,
         simp add:surj_to_def)
  apply (rotate_tac -2, frule sym, thin_tac "g ` {j. j \<le> m} = f ` {j. j \<le> n}",
         simp, thin_tac "f ` {j. j \<le> n} = g ` {j. j \<le> m}", simp add:image_def,
         erule exE,
         thin_tac "f \<in> {j. j \<le> n} \<rightarrow> insert h H1",
         thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
         thin_tac "l_comb R M n s f = l_comb R M m t g", erule conjE)

  apply (case_tac "m = 0", simp,
         frule_tac a = H1 in fgs_submodule,
         frule submodule_inc_0[of "fgs R M H1"],
         cut_tac a = "insert (g 0) H1" in fgs_submodule,
         rule subsetI, simp, erule disjE, simp, simp add:subsetD,
         frule_tac H = "fgs R M (insert (g 0) H1)" in submodule_subset,
         frule_tac c = "l_comb R M 0 t g" and A = "fgs R M (insert (g 0) H1)" 
                 and B = "carrier M" in subsetD, assumption+,
         frule_tac t = "l_comb R M 0 t g" in ag_l_zero[THEN sym],
         subgoal_tac "l_comb R M 0 t g \<in> fgs R M {g 0}", blast)
     apply (subst fgs_def,
         cut_tac s = t and n = m and f = g in 
                l_comb_mem_linear_span[of "carrier R" "{h}"], assumption+,
         rule subsetI, simp, simp, simp, 
         simp, simp)
   (** case n \<noteq> 0 **)
  apply (cut_tac f = g and n = "m - Suc 0" and s = t and l = xa in
          unique_expression3[of "insert h H1"],
         rule subsetI, simp, erule disjE, simp, simp add:subsetD)
         apply simp+ 
         apply (rule contrapos_pp, simp+, simp add:image_def)
         apply (erule bexE, simp add:inj_on_def)
         apply (drule_tac a = xa in forall_spec, simp)  
         apply (drule_tac a = xb in forall_spec,
                erule conjE, assumption, simp)
   apply ((erule exE)+, (erule conjE)+, simp)
         apply (thin_tac "g \<in> {j. j \<le> m} \<rightarrow> insert (g xa) H1",
                thin_tac "t \<in> {j. j \<le> m} \<rightarrow> carrier R",
                thin_tac "l_comb R M m t g = l_comb R M ma ta ga",
                thin_tac "inj_on g {j. j \<le> m}",
                thin_tac "g xa \<in> carrier M",
                thin_tac "fgs R M {g xa} \<subseteq> carrier M") 
         apply (rotate_tac 13, frule sym, thin_tac "h = g xa", simp) 
         apply (thin_tac "g xa = h", thin_tac "0 < m", thin_tac "xa \<le> m",
                thin_tac "ta ma = t xa", simp)
         apply (rename_tac x g m t)
   apply (case_tac "m = 0", simp,
         frule_tac a = H1 in fgs_submodule,
         frule submodule_inc_0[of "fgs R M H1"],
         cut_tac a = "insert h H1" in fgs_submodule,
         rule subsetI, simp, erule disjE, simp, simp add:subsetD,
         frule subset_trans[of H1 H "carrier M"], assumption+, 
         simp add:subsetD,
         frule_tac H = "fgs R M (insert h H1)" in submodule_subset,
         frule_tac c = "l_comb R M 0 t g" and A = "fgs R M (insert h H1)" 
                 and B = "carrier M" in subsetD, assumption+,
         frule_tac t = "l_comb R M 0 t g" in ag_l_zero[THEN sym],
         subgoal_tac "l_comb R M 0 t g \<in> fgs R M {h}", blast)
     apply (subst fgs_def,
         cut_tac s = t and n = 0 and f = g in 
                l_comb_mem_linear_span[of "carrier R" "{h}"],
         assumption, rule subsetI, simp, simp add:subsetD,
         simp, simp, assumption)
  apply (subgoal_tac "l_comb R M m t g = l_comb R M (Suc (m - Suc 0)) t g",
         simp del:Suc_pred,
         frule insert_sub[of H1 H h], assumption+,
         frule subset_trans[of "insert h H1" H "carrier M"], assumption+,
         subst l_comb_Suc[of "insert h H1" "carrier R"], assumption+,
         (subst Suc_pred, assumption,
          thin_tac "l_comb R M m t g = l_comb R M (Suc (m - Suc 0)) t g",
                simp)+)
  apply (subgoal_tac "l_comb R M (m - Suc 0) t g \<in> fgs R M H1",
         subgoal_tac "t m \<cdot>\<^sub>s h \<in> fgs R M {h}", blast,
         subst fgs_def,
         rule_tac h = h and a = "t m" in 
                 sc_linear_span[of "carrier R" "{h}"], assumption+,
         rule subsetI, simp, simp add:Pi_def, simp,
         cut_tac a = "{h}" in fgs_submodule, rule subsetI, simp,
         cut_tac s = t and n = "m - Suc 0" and f = g in 
                   l_comb_mem_linear_span[of "carrier R" H1], assumption,
         simp add:subset_trans[of H1 H "carrier M"],
         rule func_pre, simp,
         rule Pi_I, simp,
         frule_tac f = g and A = "{k. k \<le> m}" and B = "insert h H1"
                and x = xa in funcset_mem, simp, simp, simp add:inj_on_def) 
  apply (erule disjE)
  apply (drule_tac a = m in forall_spec, simp,
         drule_tac a = xa in forall_spec, simp, simp, simp)
  apply (cut_tac n1 = xa and m1 = "xa - Suc 0" in Suc_le_mono[THEN sym],
              simp, simp add:fgs_def, simp)
  apply (rule subsetI, simp)
  apply (rule subsetI, simp add:subsetD)
done

definition
  monofun :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, 
            ('b, 'r, 'm2) Module_scheme, 'a \<Rightarrow> 'b, 'a set, 'a] \<Rightarrow> ('a \<Rightarrow> 'b)" where
  "monofun R M N f H h = (\<lambda>x\<in>fgs R M {h}. 
          (THE y. (\<exists>r\<in>carrier R. x = r \<cdot>\<^sub>s\<^bsub>M\<^esub> h \<and>  y = r \<cdot>\<^sub>s\<^bsub>N\<^esub> (f h))))"  

lemma (in Module) fgs_single_span:"\<lbrakk>h \<in> carrier M; x \<in> (fgs R M {h})\<rbrakk> \<Longrightarrow> 
              \<exists>a\<in>carrier R. x = a \<cdot>\<^sub>s h" 
apply (simp add:fgs_def linear_span_def)
apply (erule exE, (erule bexE)+)
 apply (cut_tac sc_Ring, frule Ring.whole_ideal)
 apply (frule_tac A = "carrier R" and z = h and h = f and n = n and t = s in 
        single_span, assumption+)
 apply (erule bexE, simp add:l_comb_def del: Pi_split_insert_domain)
apply (frule_tac f = sa and A = "{0}" and B = "carrier R" and 
                 x = 0 in funcset_mem,  simp, blast)
done

lemma (in Module) monofun_mHomTr:"\<lbrakk>h \<in> H; free_generator R M H; 
      a \<in> carrier R; r \<in> carrier R; a \<cdot>\<^sub>s h = r \<cdot>\<^sub>s h\<rbrakk> \<Longrightarrow> a = r"
apply (cut_tac sc_Ring, frule free_generator_sub,
       frule subsetD[of H "carrier M" h], assumption+)
apply (frule_tac a = a and m = h in sc_mem, assumption+,
       frule_tac a = r and m = h in sc_mem, assumption+)
apply (frule ag_eq_diffzero[of "a \<cdot>\<^sub>s h" "r \<cdot>\<^sub>s h"], assumption+,
       simp only:sc_minus_am1, thin_tac "(a \<cdot>\<^sub>s h = r \<cdot>\<^sub>s h) = (\<zero> = \<zero>)")
apply (frule Ring.ring_is_ag[of R],
       frule aGroup.ag_mOp_closed[of R r], assumption+)
       apply (simp add:sc_l_distr[THEN sym])
       apply (frule free_gen_coeff_zero[of H h "a \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> r"], assumption+)
       apply (rule aGroup.ag_pOp_closed, assumption+)
apply (simp add:aGroup.ag_eq_diffzero)
done

lemma (in Module) monofun_mhomTr1:"\<lbrakk>R module N; h \<in> H; free_generator R M H;
        f \<in> H \<rightarrow> carrier N; a \<in> carrier R\<rbrakk>  \<Longrightarrow> 
                monofun R M N f H h (a \<cdot>\<^sub>s h) = a \<cdot>\<^sub>s\<^bsub>N\<^esub> (f h)"
apply (frule free_generator_sub)
apply (simp add:monofun_def) 
 apply (cut_tac a = "{h}" and x = h in elem_fgs, rule subsetI, 
        simp add:subsetD, simp,
        cut_tac fgs_submodule[of "{h}"])
 apply (frule submodule_sc_closed[of "fgs R M {h}" a h], assumption+,
        simp)
 apply (subgoal_tac "\<exists>!y. \<exists>r\<in>carrier R. a \<cdot>\<^sub>s h = r \<cdot>\<^sub>s h \<and> y = r \<cdot>\<^sub>s\<^bsub>N\<^esub> f h",
        subgoal_tac "\<exists>r\<in>carrier R. a \<cdot>\<^sub>s h =  r \<cdot>\<^sub>s h \<and>
         (THE y. \<exists>s\<in>carrier R.  a \<cdot>\<^sub>s h =  s \<cdot>\<^sub>s h \<and> y =  s \<cdot>\<^sub>s\<^bsub>N\<^esub> (f h)) = 
            r \<cdot>\<^sub>s\<^bsub>N\<^esub> (f h)")
 prefer 2 apply (rule theI', simp) 
 apply (thin_tac "\<exists>!y. \<exists>r\<in>carrier R. a \<cdot>\<^sub>s h = r \<cdot>\<^sub>s h \<and> y = r \<cdot>\<^sub>s\<^bsub>N\<^esub> f h")
 apply (erule bexE, erule conjE, simp, 
        thin_tac "(THE y. \<exists>s\<in>carrier R. r \<cdot>\<^sub>s h = s \<cdot>\<^sub>s h \<and> y = s \<cdot>\<^sub>s\<^bsub>N\<^esub> f h) = r \<cdot>\<^sub>s\<^bsub>N\<^esub> f h")
 apply (frule_tac r = r in monofun_mHomTr[of h H a], assumption+, simp)
 
 apply (rule ex_ex1I)
 apply blast
 apply ((erule bexE)+, (erule conjE)+)
 apply (frule_tac r = r in monofun_mHomTr[of h H a], assumption+,
        frule_tac r = ra in monofun_mHomTr[of h H a], assumption+)
 apply (thin_tac "a \<cdot>\<^sub>s h = r \<cdot>\<^sub>s h", thin_tac "a \<cdot>\<^sub>s h = ra \<cdot>\<^sub>s h",
        rotate_tac -2, frule sym, thin_tac "a = r", frule sym, 
        thin_tac "a = ra", simp)

 apply (rule subsetI, simp add:subsetD)
done

lemma (in Module) monofun_mem:"\<lbrakk>R module N; h \<in> H; free_generator R M H; 
       x \<in> fgs R M {h}; f \<in> H \<rightarrow> carrier N\<rbrakk>  \<Longrightarrow>  
       monofun R M N f H h x \<in> carrier N"
apply (frule free_generator_sub,
       frule subsetD[of H "carrier M" h], assumption+,
       frule fgs_single_span[of h x], assumption+)
apply (erule bexE, simp add:monofun_mhomTr1,
       frule funcset_mem[of f H "carrier N" h], assumption)
apply (simp add:Module.sc_mem[of N R _ "f h"])
done

lemma (in Module) monofun_eq_f:"\<lbrakk>R module N; h \<in> H; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N\<rbrakk>  \<Longrightarrow>  monofun R M N f H h h = f h"
apply (cut_tac sc_Ring)
apply (frule_tac N = N and h = h and f = f and a = "1\<^sub>r\<^bsub>R\<^esub>" in  monofun_mhomTr1,
        assumption+)
 apply (simp add:Ring.ring_one)
 apply (frule free_generator_sub, frule subsetD[of H "carrier M" h],
                           assumption+,
        frule funcset_mem[of f H "carrier N" h], assumption)
 apply (simp add:sprod_one, simp add:Module.sprod_one)
done

lemma (in Module) sSum_unique:"\<lbrakk>R module N; free_generator R M H; H1 \<subseteq> H; 
       h \<in> H - H1; x1 \<in>(fgs R M H1); x2 \<in> (fgs R M H1); 
       y1 \<in> (fgs R M {h}); y2 \<in> (fgs R M {h}); x1 \<plusminus> y1 = x2 \<plusminus> y2\<rbrakk> \<Longrightarrow>
       x1 = x2 \<and> y1 = y2"
apply (cut_tac sc_Ring, frule Ring.whole_ideal [of "R"],
       frule free_generator_sub)
 apply (frule_tac subset_trans[of H1 H "carrier M"], assumption+)
 apply (frule subsetD[of H "carrier M" h], simp)
 apply (frule_tac fgs_single_span[of h y1], assumption+,
        frule_tac fgs_single_span[of h y2], assumption+)
 apply (erule bexE, erule bexE)
 apply (frule_tac  a = a and m = h in sc_mem, assumption+,
        frule_tac  a = aa and m = h in sc_mem, assumption+)
 apply (frule subset_trans[of H1 H "carrier M"], assumption+)
 apply (frule_tac A = "carrier R" and H = H1 in lin_span_sub_carrier, 
                      assumption+) 
 apply (fold fgs_def)
 apply (frule subsetD[of "fgs R M H1" "carrier M" x1], assumption+,
        frule subsetD[of "fgs R M H1" "carrier M" x2], assumption+)
 apply simp
 apply (frule ag_mOp_closed[of x2])
 apply (frule_tac z = "a \<cdot>\<^sub>s h" in ag_pOp_assoc[of "-\<^sub>a x2" "x1"], assumption+,
        simp only:ag_pOp_assoc[THEN sym], simp add:ag_l_inv1,
        simp add:ag_l_zero,
        frule ag_pOp_closed[of "-\<^sub>a x2" x1], assumption+,
        frule_tac x = "a \<cdot>\<^sub>s h" in ag_mOp_closed)
 apply (frule_tac y = "a \<cdot>\<^sub>s h" and z = "-\<^sub>a (a \<cdot>\<^sub>s h)" in 
                    ag_pOp_assoc[of "-\<^sub>a x2 \<plusminus> x1"], assumption+,
        simp add:ag_r_inv1 ag_r_zero, thin_tac "-\<^sub>a x2 \<plusminus> x1 \<plusminus> a \<cdot>\<^sub>s h = aa \<cdot>\<^sub>s h")
 apply (frule fgs_submodule[of H1])
 apply (frule submodule_mOp_closed[of "fgs R M H1" x2], assumption,
        frule submodule_pOp_closed[of "fgs R M H1" "-\<^sub>a x2" "x1"], assumption+)
 apply (case_tac "H1 = {}", simp add:empty_fgs)
 apply (simp add:ag_eq_diffzero[THEN sym])
 apply (frule mem_fgs_l_comb[of H1 "-\<^sub>a x2 \<plusminus> x1"], assumption+,
        erule exE, (erule bexE)+)
 apply (case_tac "-\<^sub>a\<^bsub>M\<^esub> x2 \<plusminus>\<^bsub>M\<^esub> x1 = \<zero>\<^bsub>M\<^esub>", simp, rotate_tac -2, frule sym,
        thin_tac "\<zero> = l_comb R M n s f", simp,
        simp add:ag_pOp_commute[of "-\<^sub>a x2" " x1"])
 apply (simp add:ag_eq_diffzero[of x1 x2])
 apply (simp add:ag_eq_diffzero[THEN sym])
 apply simp
 apply (frule_tac f = f and n = n and s = s in unique_expression2[of H1],
        assumption+, (erule exE)+, (erule conjE)+, simp,
        simp add:bij_to_def, erule conjE,
        thin_tac "f \<in> {j. j \<le> n} \<rightarrow> H1",
        thin_tac "s \<in> {j. j \<le> n} \<rightarrow> carrier R",
        thin_tac "surj_to g {j. j \<le> m} (f ` {j. j \<le> n})",
        thin_tac "l_comb R M n s f = l_comb R M m t g", simp)
 apply (frule_tac f = g and A = "{j. j \<le> m}" and B = H1 and ?B1.0 = H in
                  extend_fun, assumption+)
 apply (frule_tac f = g and n = m and s = t in unique_expression4[of H],
        simp, (erule exE)+, (erule conjE)+, erule exE, (erule conjE)+)
 apply (frule_tac f = g and A = "{j. j \<le> m}" and B = H1 in image_sub0,
        frule_tac A = "ga ` {k. k \<le> ma}" and B = "g ` {j. j \<le> m}" and 
        C = H1 in subset_trans, assumption+, simp,
        thin_tac "g \<in> {j. j \<le> m} \<rightarrow> H1",
        thin_tac "t \<in> {j. j \<le> m} \<rightarrow> carrier R",
        thin_tac "ga ` {k. k \<le> ma} \<subseteq> g ` {k. k \<le> m}",
        thin_tac "l_comb R M m t g = l_comb R M ma ta ga",
        thin_tac "g ` {j. j \<le> m} \<subseteq> H1",
        thin_tac "inj_on g {j. j \<le> m}",
        thin_tac "g \<in> {j. j \<le> m} \<rightarrow> H", simp) 
  apply (rename_tac a aa m g t)
  apply (simp add:sc_minus_am1,
         cut_tac sc_Ring, frule Ring.ring_is_ag,
         frule_tac x = a in aGroup.ag_mOp_closed[of R], assumption)
  apply (simp add:sc_l_distr[THEN sym]) 
  apply (case_tac "aa \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> a = \<zero>\<^bsub>R\<^esub>", simp add:sc_0_m,
         frule_tac x = aa and y = "-\<^sub>a\<^bsub>R\<^esub> a" in aGroup.ag_pOp_closed, assumption+)
  apply (subgoal_tac "(\<lambda>x\<in>{0::nat}. (aa \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> a)) \<in>
                               {j. j \<le> (0::nat)} \<rightarrow> carrier R",
         subgoal_tac "(\<lambda>x\<in>{0::nat}. h) \<in>
                               {j. j \<le> (0::nat)} \<rightarrow> H")
  apply (frule_tac f = "\<lambda>x\<in>{0::nat}. h" and n = 0 and 
         s = "\<lambda>x\<in>{0::nat}. (aa \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> a)" and g = g and m = m and t = t in 
         unique_expression5[of H])
  apply (simp)
  apply (simp add:inj_on_def)
  apply (simp, assumption+)
  apply (simp add:l_comb_def[of _ _ 0], rule ballI, simp)
  apply simp
  apply (frule_tac A = "(\<lambda>x\<in>{0}. h) ` {j. j \<le> 0}" and B = "g ` {j. j \<le> m}" 
         and C = H1 in subset_trans, assumption+,
         thin_tac "(\<lambda>x\<in>{0}. h) \<in> {j. j \<le> 0} \<rightarrow> H",
         thin_tac "(\<lambda>x\<in>{0}. aa \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> a) \<in> {j. j \<le> 0} \<rightarrow> carrier R",
         thin_tac "(\<lambda>x\<in>{0}. h) ` {j. j \<le> 0} \<subseteq> g ` {j. j \<le> m}",
         thin_tac "g ` {k. k \<le> m} \<subseteq> H1")
  apply (simp, simp, simp)
done

lemma (in Module) ex_extensionTr:"\<lbrakk>R module N; free_generator R M H;  
       f \<in> H \<rightarrow> carrier N; H1 \<subseteq> H; h \<in> H; h \<notin> H1; 
       g \<in> mHom R (mdl M (fgs R M H1)) N; 
       x \<in> fgs R M H1 \<minusplus> (fgs R M {h})\<rbrakk> \<Longrightarrow> 
     \<exists>k1\<in> fgs R M H1. \<exists>k2\<in>fgs R M {h}. x = k1 \<plusminus> k2 \<and> 
 (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> 
         (monofun R M N f H h h2)) = g k1  \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h k2)"
apply (frule free_generator_sub)
apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp,
       simp)
apply (subgoal_tac "\<exists>!y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 \<plusminus> h2 \<and> 
                          y = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)",
       subgoal_tac "\<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x = h1 \<plusminus> h2 \<and> 
  (THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}. x =  h1 \<plusminus> h2 \<and> 
    y = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)) = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)")
prefer 2 apply (rule theI') apply simp
 apply (thin_tac " \<exists>!y. \<exists>h1\<in>fgs R M H1.
        \<exists>h2\<in>fgs R M {h}. x = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2")
 apply blast
apply (rule ex_ex1I)
 apply (thin_tac "fgs R M (insert h H1) = fgs R M H1 \<minusplus> (fgs R M {h})")
 apply (cut_tac fgs_sub_carrier[of H1], cut_tac fgs_sub_carrier[of "{h}"])
 apply (simp add:set_sum)
 apply (erule bexE)+
 apply (frule subsetD[of H "carrier M" h], assumption+) 
 apply (frule_tac x = k in monofun_mem[of N h H _ f], assumption+)
apply blast
 apply (rule subsetI, simp, simp add:subsetD,
        rule subset_trans[of H1 H "carrier M"], assumption+)
 apply ((erule bexE)+, (erule conjE)+, simp)
 apply (frule_tac ?x1.0 = h1a and ?x2.0 = h1 and ?y1.0 = h2a and ?y2.0 = h2 
        in sSum_unique[of N H H1 h], assumption+, simp, assumption+)
 apply ((erule conjE)+, simp)
done

lemma (in Module) monofun_add:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; h \<in> H; x \<in> fgs R M {h}; y \<in> fgs R M {h}\<rbrakk> \<Longrightarrow> 
       monofun R M N f H h (x \<plusminus> y) = 
                   monofun R M N f H h x \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h y)"
apply (frule free_generator_sub,
       cut_tac sc_Ring, frule Ring.ring_is_ag,
       frule subsetD[of H "carrier M" h], assumption+,
       frule fgs_single_span[of h x], assumption+,
       frule fgs_single_span[of h y], assumption+, (erule bexE)+, simp,
       simp add:sc_l_distr[THEN sym])
apply (frule_tac x = a and y = aa in aGroup.ag_pOp_closed[of R], assumption+)
apply (simp add:monofun_mhomTr1,
       frule funcset_mem[of f H "carrier N" h], assumption+)
apply (simp add:Module.sc_l_distr)
done

lemma (in Module) monofun_sprod:"\<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N; h \<in> H; x \<in> fgs R M {h}; a \<in> carrier R\<rbrakk> \<Longrightarrow> 
      monofun R M N f H h ( a \<cdot>\<^sub>s x) = a \<cdot>\<^sub>s\<^bsub>N\<^esub> (monofun R M N f H h x)"
apply (frule free_generator_sub,
       cut_tac sc_Ring,
       frule subsetD[of H "carrier M" h], assumption+,
       frule fgs_single_span[of h x], assumption+,
       erule bexE, simp add:sc_assoc[THEN sym])
apply (frule_tac x = a and y = aa in Ring.ring_tOp_closed, assumption+)
apply (simp add:monofun_mhomTr1,
       frule funcset_mem[of f H "carrier N" h], assumption+)
apply (simp add:Module.sc_assoc)
done

lemma (in Module) monofun_0:"\<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N; h \<in> H\<rbrakk> \<Longrightarrow>  monofun R M N f H h  \<zero>  = \<zero>\<^bsub>N\<^esub>"
apply (cut_tac fgs_submodule[of "{h}"],
       frule submodule_inc_0[of "fgs R M {h}"])
apply (cut_tac sc_Ring, frule Ring.ring_zero,
       frule monofun_sprod[of N H f h \<zero> "\<zero>\<^bsub>R\<^esub>"], assumption+,
       cut_tac ag_inc_zero)
apply (simp add:sc_0_m,
       frule monofun_mem[of N h H \<zero> f], assumption+,
       simp add:Module.sc_0_m)
apply (frule free_generator_sub, rule subsetI, simp add:subsetD)
done

lemma (in Module) ex_extension:"\<lbrakk>R module N; free_generator R M H; 
       f \<in> H \<rightarrow> carrier N; H1 \<subseteq> H; h \<in> H - H1; (H1, g) \<in> fsps R M N f H\<rbrakk> \<Longrightarrow>
       \<exists>k. ((H1 \<union> {h}), k) \<in> fsps R M N f H"
apply (frule free_generator_sub,
       cut_tac sc_Ring,
       frule subset_trans[of H1 H "carrier M"], assumption+,
       frule subsetD[of H "carrier M" h], simp+,
       frule singleton_sub[of h "carrier M"])
apply (frule fgs_submodule[of "{h}"],
       frule fgs_submodule[of H1],
       frule submodule_subset[of "fgs R M {h}"],
       frule submodule_subset[of "fgs R M H1"],
       frule insert_sub[of H1 "carrier M" h], assumption,
       frule fgs_submodule[of "insert h H1"])
apply (simp add:fsps_def fsp_def)
 apply (erule conjE)+
 apply (subgoal_tac "(\<lambda>x \<in> (fgs R M (H1 \<union> {h})). 
        (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 \<plusminus> h2 \<and> 
                 y = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)))) \<in> 
        mHom R (mdl M (fgs R M (insert h H1))) N \<and> 
  f h = (\<lambda>x \<in> (fgs R M (H1 \<union> {h})). 
        (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 \<plusminus> h2 \<and> 
            y = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)))) h \<and> 
        (\<forall>z\<in>H1. g z = (\<lambda>x \<in> (fgs R M (H1 \<union> {h})). 
        (THE y. (\<exists>h1\<in>(fgs R M H1). \<exists>h2\<in>(fgs R M {h}). x = h1 \<plusminus> h2 \<and> 
                  y = g h1 \<plusminus>\<^bsub>N\<^esub> (monofun R M N f H h h2)))) z)")
 apply blast
apply (rule conjI)
 apply (rule Module.mHom_test)
 apply (rule mdl_is_module, assumption+)
 apply (rule conjI,
        rule Pi_I, simp add:mdl_carrier)
 apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp, simp)
 apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and x = x and N = N
        in ex_extensionTr, assumption+,
        (erule bexE)+, erule conjE, rotate_tac -1,
         frule sym,
        thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  x = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
                  g k1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2")
 apply (frule mdl_is_module[of "fgs R M H1"],
        frule_tac f = g and m = k1 in Module.mHom_mem[of "mdl M (fgs R M H1)" 
                   R N], assumption+, simp add:mdl_carrier)
 apply (frule_tac x = k2 in monofun_mem[of N h H _ f], assumption+)
 apply (frule Module.module_is_ag[of N],
        frule_tac x = "g k1" and y = "monofun R M N f H h k2 " in 
        aGroup.ag_pOp_closed[of N], assumption+, simp)
 apply (simp add:mdl_carrier)
 apply (rule conjI, (rule ballI)+) 
 apply (frule mdl_is_module[of "fgs R M (insert h H1)"],
        frule Module.module_is_ag[of "mdl M (fgs R M (insert h H1))"],
        frule_tac x = m and y = n in aGroup.ag_pOp_closed[of
         "mdl M (fgs R M (insert h H1))"],
        (simp add:mdl_carrier)+)
 apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp, simp)
 apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
       x = "m \<plusminus>\<^bsub>mdl M (fgs R M H1 \<minusplus> fgs R M {h})\<^esub> n" in ex_extensionTr, assumption+,
       (erule bexE)+, (erule conjE)+, simp,
       thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  k1 \<plusminus> k2 = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
        g k1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2")
  apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
       x = m in ex_extensionTr, assumption+, (erule bexE)+, (erule conjE)+, 
       simp,
       thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  k1a \<plusminus> k2a = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
        g k1a \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2a")
  apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
       x = n in ex_extensionTr, assumption+, (erule bexE)+, (erule conjE)+, 
       simp,
       thin_tac "(THE y. \<exists>h1\<in>fgs R M H1.  \<exists>h2\<in>fgs R M {h}.
                  k1b \<plusminus> k2b = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
        g k1b \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2b")
  apply (simp add:mdl_def[of M "fgs R M H1 \<minusplus> fgs R M {h}"],
         fold mdl_def)
  apply (frule_tac c = k1a in subsetD[of "fgs R M H1" "carrier M"], 
         assumption+,
         frule_tac c = k1b in subsetD[of "fgs R M H1" "carrier M"], 
         assumption+) apply (
         frule_tac c = k2a in subsetD[of "fgs R M {h}" "carrier M"], 
         assumption+,
         frule_tac c = k2b in subsetD[of "fgs R M {h}" "carrier M"], 
         assumption+)  
  apply (simp add:pOp_assocTr41[THEN sym], simp add:pOp_assocTr42,
        frule_tac x = k2a and y = k1b in ag_pOp_commute, assumption+, simp,
        thin_tac "k2a \<plusminus> k1b = k1b \<plusminus> k2a", simp add:pOp_assocTr42[THEN sym],
        simp add:pOp_assocTr41)
  apply(frule_tac h = k1a and k = k1b in submodule_pOp_closed[of "fgs R M H1"],
        assumption+)
  apply(frule_tac h = k2a and k = k2b in 
          submodule_pOp_closed[of "fgs R M {h}"], assumption+)      
  apply (frule_tac ?x1.0 = "k1a \<plusminus> k1b" and ?x2.0 = k1 and ?y1.0 = "k2a \<plusminus> k2b" 
         and ?y2.0 = k2 in sSum_unique[of N H H1 h], assumption+, simp,
         assumption+, erule conjE, rotate_tac -2, frule sym,
         thin_tac "k1a \<plusminus> k1b = k1", frule sym, thin_tac "k2a \<plusminus> k2b = k2",
         thin_tac "k1a \<plusminus> k1b \<plusminus> (k2a \<plusminus> k2b) = k1 \<plusminus> k2", simp,
         frule mdl_is_module[of "fgs R M H1"])
  apply (frule_tac m = k1a and n = k1b in Module.mHom_add[of 
                           "mdl M (fgs R M H1)" R N g], assumption+,
         simp add:mdl_carrier, simp add:mdl_carrier, 
         simp add:mdl_def, fold mdl_def)
  apply (simp add: monofun_add)
  apply (frule_tac m = k1a in Module.mHom_mem[of "mdl M (fgs R M H1)" R N g],
         assumption+, simp add:mdl_carrier,
         frule_tac m = k1b in Module.mHom_mem[of "mdl M (fgs R M H1)" R N g],
         assumption+, simp add:mdl_carrier,
         frule_tac x = k2a in monofun_mem[of N h H _ f], assumption+,
         frule_tac x = k2b in monofun_mem[of N h H _ f], assumption+)
  apply (frule Module.module_is_ag[of N],
         simp add:aGroup.pOp_assocTr41[of N, THEN sym], 
         simp add:aGroup.pOp_assocTr42[of N],
         simp add:aGroup.ag_pOp_commute[of N])
apply (rule ballI)+
apply (frule mdl_is_module[of "fgs R M (insert h H1)"])
 apply (frule_tac a = a and m = m in Module.sc_mem[of 
             "mdl M (fgs R M (insert h H1))" R], assumption+,
        simp add:mdl_carrier, simp add:mdl_carrier)
 apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp) 
 apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
       x = "a \<cdot>\<^sub>s\<^bsub>mdl M (fgs R M (insert h H1))\<^esub> m" in ex_extensionTr, assumption+,
       simp)
 apply ((erule bexE)+, erule conjE, simp,
       thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  k1 \<plusminus> k2 = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
                  g k1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2")
       apply (simp add:mdl_def, fold mdl_def)
 apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
       x = m in ex_extensionTr, assumption+,
       (erule bexE)+, erule conjE, simp,
       thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  k1a \<plusminus> k2a = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
                  g k1a \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2a",
       frule_tac c = k1a in subsetD[of "fgs R M H1" "carrier M"], assumption+,
       frule_tac c = k1 in subsetD[of "fgs R M H1" "carrier M"], assumption+,
       frule_tac c = k2a in subsetD[of "fgs R M {h}" "carrier M"], assumption+,
       frule_tac c = k2 in subsetD[of "fgs R M {h}" "carrier M"], assumption+)        apply (simp add:sc_r_distr,
              frule_tac a = a and h = k1a in 
                    submodule_sc_closed[of "fgs R M H1"], assumption+,
              frule_tac a = a and h = k2a in 
                    submodule_sc_closed[of "fgs R M {h}"], assumption+)
  apply (frule_tac ?x1.0 = k1 and ?x2.0 = "a \<cdot>\<^sub>s k1a" and ?y1.0 = k2 and
          ?y2.0 = "a \<cdot>\<^sub>s k2a" in sSum_unique[of N H H1 h], assumption+,
          simp, assumption+, rule sym, assumption,
          thin_tac "a \<cdot>\<^sub>s k1a \<plusminus> a \<cdot>\<^sub>s k2a = k1 \<plusminus> k2", simp)
  apply (frule subset_trans[of H1 H "carrier M"], assumption+,
          frule mdl_is_module[of "fgs R M H1"])
  apply (frule_tac a = a and m = k1a in Module.mHom_lin[of "mdl M (fgs R M H1)"
          R N _ g], assumption+, simp add:mdl_carrier, assumption+)
  apply (simp add:mdl_def, fold mdl_def)
  apply (simp add:monofun_sprod)
  apply (frule_tac m = k1a in Module.mHom_mem[of "mdl M (fgs R M H1)" R N g],
          assumption+, simp add:mdl_carrier,
         frule_tac x = k2a in monofun_mem[of N h H _ f], assumption+,
         simp add:Module.sc_r_distr[of N])
apply (rule conjI) apply simp
  apply (cut_tac insert_sub[of H1 "carrier M" h], 
         frule elem_fgs[of "insert h H1" h], simp, simp)
  apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
         x = h in ex_extensionTr, assumption+)
   apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp, simp) 
   apply ((erule bexE)+, (erule conjE), simp,
         thin_tac "(THE y.
            \<exists>h1\<in>fgs R M H1.
               \<exists>h2\<in>fgs R M {k1 \<plusminus> k2}.
                  k1 \<plusminus> k2 = h1 \<plusminus> h2 \<and>
                  y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H (k1 \<plusminus> k2) h2) =
        g k1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H (k1 \<plusminus> k2) k2")
   apply (rotate_tac -1, frule sym, thin_tac "h = k1 \<plusminus> k2", simp)
   apply (cut_tac elem_fgs[of "{h}" h], 
          frule ag_l_zero[THEN sym, of h])
   apply (frule submodule_inc_0[of "fgs R M H1"])
   apply (frule_tac ?x1.0 = k1 and ?x2.0 = \<zero> and ?y1.0 = k2 and ?y2.0 = h in 
          sSum_unique[of N H H1 h], assumption+, simp, assumption+,
          simp, simp, simp add: monofun_eq_f)
   apply (cut_tac Module.mHom_0[of "mdl M (fgs R M H1)" R N g],
          simp add:mdl_def, fold mdl_def)
   apply (frule funcset_mem[of f H "carrier N" h], assumption+,
          frule Module.module_is_ag[of N], simp add:aGroup.l_zero,
          rule mdl_is_module, assumption+,
          rule subsetI, simp, simp, assumption+)
apply (rule ballI, simp,
       cut_tac x = z in elem_fgs[of "insert h H1"],
       rule subsetI, simp, erule disjE, simp, simp add:subsetD, 
       rule_tac c = z in subsetD[of "H1" "insert h H1"],
       rule subsetI, simp, assumption, simp) 

apply (frule_tac h = h and H = H and ?H1.0 = H1 and g = g and N = N and
         x = z in ex_extensionTr, assumption+) 
   apply (frule sSum_eq[THEN sym, of N H H1 h], assumption+, simp, simp) 
   apply ((erule bexE)+, (erule conjE), simp)
   apply (thin_tac "(THE y. \<exists>h1\<in>fgs R M H1. \<exists>h2\<in>fgs R M {h}.
                  k1 \<plusminus> k2 = h1 \<plusminus> h2 \<and> y = g h1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h h2) =
        g k1 \<plusminus>\<^bsub>N\<^esub> monofun R M N f H h k2")
   apply (rotate_tac -1, frule sym, thin_tac "z = k1 \<plusminus> k2", simp)
 apply (frule_tac x = z in elem_fgs[of H1], assumption,
       frule_tac c = z in subsetD[of H1 "carrier M"], assumption+,
       frule_tac t = z in ag_r_zero[THEN sym]) 
 apply (frule_tac ?x1.0 = k1 and ?x2.0 = z and ?y1.0 = k2 and ?y2.0 = \<zero>  in 
        sSum_unique[of N H H1 h], assumption+, simp, assumption+,
        simp add:submodule_inc_0, simp, simp)
 apply (simp add: monofun_0)
 apply (frule mdl_is_module[of "fgs R M H1"],
        frule_tac m = z in Module.mHom_mem[of "mdl M (fgs R M H1)" R N g],
        assumption+, simp add:mdl_carrier)
 apply (frule Module.module_is_ag[of N],
        simp add:aGroup.ag_r_zero)
done

lemma (in Module) mHom_mHom:"\<lbrakk>R module N; g \<in> mHom R (mdl M (carrier M)) N\<rbrakk>
       \<Longrightarrow> g \<in> mHom R M N"
apply (rule mHom_test, assumption)
apply (rule conjI)
 apply (simp add:mHom_def aHom_def mdl_def)
 apply (simp add:mHom_def aHom_def mdl_def)
done


lemma (in Module) exist_extension_mhom:"\<lbrakk>R module N; free_generator R M H; 
      f \<in> H \<rightarrow> carrier N\<rbrakk> \<Longrightarrow> \<exists>g\<in>mHom R M N. \<forall>x\<in>H. g x = f x"
apply (frule Order_od_fm_fun[of N H f], assumption+) 
apply (frule_tac  N = N and H = H and f = f in od_fm_fun_inductive, 
             assumption+)
apply (frule_tac D = "od_fm_fun R M N f H" in Order.g_Zorn_lemma3,
        assumption+)
apply (erule bexE)
apply (rule contrapos_pp, simp+)
 apply (simp add:maximal_element_def)
 apply (simp add:od_fm_fun_carrier)
 apply (cut_tac p = m in PairE_lemma, (erule exE)+, simp)
 apply (frule_tac a = x and b = y in mem_fsps_fst_sub[of N H f], assumption+)
 apply (case_tac "x \<noteq> H", frule not_sym)
 apply (frule_tac A = H and B = x in diff_nonempty, assumption,
        frule_tac A = "H - x" in nonempty_ex, erule exE,
        rename_tac m H1 g h)
 apply (frule_tac ?H1.0 = H1 and h = h and g = g in ex_extension[of N H f],
        assumption+, erule exE)
 apply (drule_tac x = "(H1 \<union> {h}, k)" in bspec, assumption)
 apply (simp add:od_fm_fun_def ole_def, fold od_fm_fun_def,
        simp add:insert_inc1, (erule conjE)+,
        cut_tac a = h and A = H1 in insert_inc2,
        rotate_tac -3, frule sym, thin_tac "H1 = insert h H1", simp)
 apply simp 
 apply (frule_tac a = H and b = y in mem_fsps_snd_mHom[of N H f], assumption+)
 apply (simp add:fgs_def free_generator_def generator_def)
 apply (frule_tac g = y in mHom_mHom[of N], assumption+,
        (erule conjE)+, thin_tac "\<forall>n s. s \<in> {j. j \<le> n} \<rightarrow> carrier R \<and>
               (\<exists>f. f \<in> {j. j \<le> n} \<rightarrow> H \<and>
                    inj_on f {j. j \<le> n} \<and> l_comb R M n s f = \<zero>) \<longrightarrow>
               s \<in> {j. j \<le> n} \<rightarrow> {\<zero>\<^bsub>R\<^esub>}")
 apply (drule_tac x = y in bspec, assumption+,
        simp add:fsps_def fsp_def)
done

section "Nakayama lemma" 

definition
  Lcg :: "[('r, 'm) Ring_scheme, ('a, 'r, 'm1) Module_scheme, nat] \<Rightarrow> bool" where
  "Lcg R M j \<longleftrightarrow> (\<exists>H. finite_generator R M H \<and> j = card H)" 
 (* Least cardinality of generator *)

lemma (in Module) NAKTr1:"M fgover R \<Longrightarrow> 
      \<exists>H. finite_generator R M H \<and> (LEAST j. 
        \<exists>L. finite_generator R M L \<and> j = card L) = card H"
apply (simp add:fGOver_def)
 apply (erule exE)
 apply (rule LeastI)
apply (rule_tac x = H in exI) apply simp
done

lemma (in Module) NAKTr2:"\<lbrakk>Lcg R M j; k < (LEAST j. Lcg R M j)\<rbrakk> \<Longrightarrow>
                            \<not> Lcg R M k"
apply (rule not_less_Least, assumption+) 
done

lemma (in Module) NAKTr3:"\<lbrakk>M fgover R; H \<subseteq> carrier M; finite H;
       card H < (LEAST j. \<exists>L. finite_generator R M L \<and> j = card L)\<rbrakk> \<Longrightarrow>
              \<not> finite_generator R M H"
apply (frule NAKTr1, erule exE, erule conjE) 
 apply (cut_tac j = "card Ha" and k = "card H" in NAKTr2)
 apply (simp add:Lcg_def, blast)
 apply (simp add:Lcg_def)
 apply (simp add:Lcg_def)
apply (rule contrapos_pp, simp+)
 apply (drule_tac a = H in forall_spec, assumption)
 apply simp
done

lemma (in Module) finite_gen_over_ideal:"\<lbrakk>ideal R A; h \<in> {j. j \<le> (n::nat)} \<rightarrow>
 carrier M; generator R M (h ` {j. j \<le> n}); A \<odot>\<^bsub>R\<^esub> M = carrier M; 
 m \<in> carrier M \<rbrakk>  \<Longrightarrow>  \<exists>s\<in>{j. j \<le> n} \<rightarrow> A. m = l_comb R M n s h"
apply (frule l_span_closed3[of "A" "h ` {j. j \<le> n}"], assumption+)
apply (rotate_tac -1, frule sym, 
        thin_tac "linear_span R M A (h ` {j. j \<le> n}) = carrier M")
 apply (frule eq_set_inc[of m "carrier M" 
                  "linear_span R M A (h ` {j. j \<le> n})"], assumption+)
 apply (thin_tac "carrier M = linear_span R M A (h ` {j. j \<le> n})")
 apply (simp add:linear_span_def) 
 apply (cut_tac Nset_nonempty[of n], simp)
 apply (case_tac "\<forall>x. \<not> x \<le> n", simp, simp) (** simp no good **)
 apply (erule exE, (erule bexE)+)
apply (simp add:finite_lin_span)
done

lemma (in Module) NAKTr4:"\<lbrakk>ideal R A; h \<in> {j. j \<le> (k::nat)} \<rightarrow> carrier M; 
 0 < k;  h ` {j. j \<le> k} \<subseteq> carrier M; s \<in> {j. j \<le> k} \<rightarrow> A; 
 h k = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (h j)) (k - Suc 0) \<plusminus> (s k \<cdot>\<^sub>s (h k))\<rbrakk> \<Longrightarrow> 
  (1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (s k))) \<cdot>\<^sub>s (h k) = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s (h j)) (k - Suc 0)"
apply (cut_tac sc_Ring)
apply (frule funcset_mem[of h "{j. j \<le> k}" "carrier M" k], simp)
apply (frule_tac funcset_mem[of s "{j. j \<le> k}" A k], simp,
       frule_tac h = "s k" in Ring.ideal_subset[of R A], assumption+)
apply (cut_tac n = "k - Suc 0" and f = "\<lambda>j. s j \<cdot>\<^sub>s h j" in nsum_mem)
apply (rule allI, rule impI, rule sc_mem,
       frule_tac x = j in funcset_mem[of s "{j. j \<le> k}" A ],
       simp)
 apply (simp add:Ring.ideal_subset)
 apply (cut_tac i = j and j = "k - Suc 0" and k = k in 
        le_trans, assumption+, simp,
        rule_tac x = j in funcset_mem[of h "{j. j \<le> k}" "carrier M"],
        assumption, simp)

 apply (frule sc_mem[of "s k" "h k"], assumption+,
        frule ag_mOp_closed[of "s k \<cdot>\<^sub>s h k"])
 apply (frule_tac ag_pOp_add_r[of "h k"
        "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0) \<plusminus> s k \<cdot>\<^sub>s h k" "-\<^sub>a (s k \<cdot>\<^sub>s h k)"],
         rule ag_pOp_closed, assumption+,
        thin_tac "h k = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0) \<plusminus> s k \<cdot>\<^sub>s h k",
        simp add:ag_pOp_assoc ag_r_inv1 ag_r_zero,
        simp add:sc_minus_am1)
 apply (frule Ring.ring_is_ag, 
        frule aGroup.ag_mOp_closed[of R "s k"], assumption+)
       (** I don't know how to change s k to 1\<^sub>r\<^bsub>R\<^esub> \<cdot>\<^sub>s s k **) 
 apply (subgoal_tac "(1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (s k))) \<cdot>\<^sub>s h k = h k \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s h k",
        simp,
        thin_tac "h k \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s h k = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0)")
 apply (cut_tac Ring.ring_one[of R],
        simp add:sc_l_distr sprod_one, assumption)
done
 
lemma (in Module) NAKTr5:"\<lbrakk>\<not> zeroring R; ideal R A; A \<subseteq> J_rad R; 
       A \<odot>\<^bsub>R\<^esub> M = carrier M; finite_generator R M H; card H = Suc k; 0 < k\<rbrakk> \<Longrightarrow>
     \<exists>h \<in> {j. j \<le> k} \<rightarrow> carrier M. H = h ` {j. j \<le> k} \<and>  
             h k \<in> linear_span R M A (h ` {j. j \<le> (k - Suc 0)})"
apply (cut_tac sc_Ring)
 apply (insert Nset2_finiteTr [of "k"]) 
 apply (subgoal_tac "\<exists>h. h \<in> {j. j \<le> k} \<rightarrow> H \<and> surj_to h {j. j \<le> k} H")
 prefer 2 
 apply (subgoal_tac "finite H")
 apply blast apply (simp add:finite_generator_def) 
 apply (thin_tac " \<forall>A. finite A \<and> card A = Suc k \<longrightarrow>
           (\<exists>f. f \<in> {j. j \<le> k} \<rightarrow> A \<and> surj_to f {j. j \<le> k} A)")
 apply (erule exE)
 apply (simp add:surj_to_def, erule conjE) apply (rotate_tac -1) 
 apply (drule sym)
apply (frule_tac f = h and A = "{j. j \<le> k}" and B = "H" and x = k in 
       funcset_mem)
 apply simp
 apply (simp add:finite_generator_def,
        simp add:generator_def, erule conjE)
 apply (cut_tac A = "h ` {j. j \<le> k}" and B = "carrier M" and c = "h k" in
   subsetD, assumption, simp)
 apply (frule_tac h = h and n = k and m = "h k" in finite_gen_over_ideal [of 
       "A"])
 apply (fastforce simp add:Pi_def image_def)
 apply (simp add:generator_def)
 apply assumption+
 apply (erule bexE)
 apply (frule_tac f = s and A = "{j. j \<le> k}" and B = A and x = k in 
           funcset_mem, simp, simp add:subsetD)
 apply (subgoal_tac "l_comb R M k s h = l_comb R M (Suc (k - Suc 0)) s h",
        simp del:Suc_pred,
        thin_tac "l_comb R M k s h = l_comb R M (Suc (k - Suc 0)) s h")
apply (cut_tac s = s and n = "k - Suc 0" and f = h and H = "h ` {j. j \<le> k}" 
       in l_comb_Suc[of _ A], assumption+,
       frule Ring.ideal_subset1[of R A], assumption,
       simp add:extend_fun, simp)
apply (rotate_tac -3, frule sym, 
       thin_tac "h k = l_comb R M (Suc (k - Suc 0)) s h", simp)
apply (frule_tac h = h and k = k and s = s in NAKTr4[of A])
 apply (fastforce simp add:Pi_def image_def)
 apply(assumption+, rule sym, simp add:l_comb_def)
apply (cut_tac H = "h ` {j. j \<le> (k - Suc 0)}" and s = s and n = "k - Suc 0" 
       and f = h in l_comb_mem_linear_span[of A], assumption+)
   apply (rule_tac A = "h ` {j. j \<le> k - Suc 0}" and 
           B = "h ` {j. j \<le> k}" and C = "carrier M" in  subset_trans)
   apply (rule subsetI, simp add:image_def, erule exE, erule conjE,
          cut_tac i = xa and j = "k - Suc 0" and k = k in le_trans,
           assumption, subst Suc_le_mono[THEN sym], simp, blast, assumption)
   apply (rule Pi_I, simp)
   apply (frule_tac x = x in le_pre_le[of _ k], simp add:Pi_def)
   apply (rule Pi_I, simp) 
   apply (unfold l_comb_def)
   apply (rotate_tac -2, frule sym,
    thin_tac "(1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s h k = \<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0)",
    thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0) \<plusminus> s k \<cdot>\<^sub>s h k = h k",
    simp,
    thin_tac "\<Sigma>\<^sub>e M (\<lambda>j. s j \<cdot>\<^sub>s h j) (k - Suc 0) = (1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>s h k")
    apply (frule_tac x = "s k" in Ring.J_rad_unit [of R], assumption,
           frule_tac f = s and A = "{j. j \<le> k}" and B = A and x = k in 
           funcset_mem, simp, simp add:subsetD)
    apply (frule Ring.ring_one[of R],
           frule_tac a = "1\<^sub>r\<^bsub>R\<^esub>" in forall_spec, assumption)
    apply (frule_tac h = "s k" in Ring.ideal_subset[of R A], assumption+,
           frule Ring.ring_is_ag[of R],
           frule_tac x = "s k" in aGroup.ag_mOp_closed[of R], assumption,
           thin_tac "\<forall>y. y \<in> carrier R \<longrightarrow> Unit R (1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (s k)) \<cdot>\<^sub>r\<^bsub>R\<^esub> y)",
           simp add:Ring.ring_r_one)
    apply (simp add:Unit_def, erule conjE, erule bexE)
    apply (simp add:Ring.ring_tOp_commute)
    apply (frule_tac H = "h ` {j. j \<le> k - Suc 0}" and r = b and 
          x = "(1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> (-\<^sub>a\<^bsub>R\<^esub> (s k))) \<cdot>\<^sub>s h k" in linear_span_sc_closed[of A])
    apply (rule_tac A = "h ` {j. j \<le> k - Suc 0}" and B = "h ` {j. j \<le> k}"
           and C = "carrier M" in subset_trans,
           rule subsetI, simp add:image_def, erule exE, erule conjE)
    apply (frule_tac x = xa and n = k in le_pre_le, blast, assumption+)
    apply (simp add:sc_assoc[THEN sym] sprod_one)
    apply(simp add:Pi_def)
    apply blast
 apply simp
done

lemma (in Module) NAK:"\<lbrakk>\<not> zeroring R; M fgover R; ideal R A; A \<subseteq> J_rad R;  
       A \<odot>\<^bsub>R\<^esub> M = carrier M \<rbrakk> \<Longrightarrow> carrier M = {\<zero>}"
apply (cut_tac sc_Ring)
apply (frule NAKTr1, erule exE, erule conjE)
apply (simp add:finite_generator_def, frule conjunct1, frule conjunct2,
       fold finite_generator_def)
apply (case_tac "H = {}", simp add:generator_def linear_span_def,
       frule_tac A = H in nonempty_card_pos1, assumption+)
apply (case_tac "card H = Suc 0", simp,
       frule_tac A = H in nonempty_ex, erule exE, rename_tac H h,
       frule_tac t = H and a1 = h in card1_tr0[THEN sym], assumption+, simp) 
apply (frule_tac H = "{h}" in generator_sub_carrier,
       frule sym, thin_tac "A \<odot>\<^bsub>R\<^esub> M = carrier M", simp,
       thin_tac "carrier M = A \<odot>\<^bsub>R\<^esub> M", simp add:smodule_ideal_coeff_def,
       simp add:generator_def) 
 apply (erule conjE, rotate_tac -1, frule sym, 
        thin_tac "linear_span R M (carrier R) {h} = carrier M", simp)
 apply (rotate_tac -1, frule sym,
        frule_tac a = h and A = "linear_span R M (carrier R) {h}" and
                  B = "carrier M" in eq_set_inc, assumption+,
        frule_tac a = h and A = "carrier M" in singleton_sub)
 apply (frule_tac H = "{h}" in l_spanA_l_span[of A], assumption+,
        thin_tac "carrier M = linear_span R M (carrier R) {h}",
        thin_tac "linear_span R M (carrier R) {h} = carrier M", simp,
        thin_tac "h \<in> linear_span R M (carrier R) {h}",
        thin_tac "linear_span R M A (linear_span R M (carrier R) {h}) =
           linear_span R M A {h}",
        thin_tac "(LEAST j. \<exists>L. finite L \<and>
                   L \<subseteq> linear_span R M (carrier R) {h} \<and>
                   linear_span R M (carrier R) L =
                   linear_span R M (carrier R) {h} \<and>
                   j = card L) = Suc 0")
apply (frule_tac h = h and x = h in mem_single_l_span1[of A],
        assumption+, erule bexE,
       frule_tac h = a in Ring.ideal_subset[of R A], assumption+,
       frule_tac a = a and m = h in sc_mem, assumption+,
       frule_tac x = "a \<cdot>\<^sub>s h" in ag_mOp_closed)
apply (frule_tac a = h and b = "a \<cdot>\<^sub>s h" and c = "-\<^sub>a (a \<cdot>\<^sub>s h)" in
       ag_pOp_add_r, assumption+,
       thin_tac "h = a \<cdot>\<^sub>s h", simp add:ag_r_inv1,
       simp add:sc_minus_am1,
       frule Ring.ring_is_ag[of R],
       frule_tac x = a in aGroup.ag_mOp_closed, assumption)
apply (subgoal_tac "h \<plusminus> (-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s h = 1\<^sub>r\<^bsub>R\<^esub> \<cdot>\<^sub>s h \<plusminus>  (-\<^sub>a\<^bsub>R\<^esub> a) \<cdot>\<^sub>s h", simp)
apply (frule Ring.ring_one[of R],
       simp add:sc_l_distr[THEN sym],
       frule_tac x = a in Ring.J_rad_unit [of R], assumption, 
       simp add:subsetD,
       drule_tac a = "1\<^sub>r\<^bsub>R\<^esub>" in forall_spec, assumption,
       simp add:Ring.ring_r_one,
       simp add:Unit_def, erule conjE, erule bexE,
       simp add:Ring.ring_tOp_commute,
       frule_tac a = b and b = "1\<^sub>r\<^bsub>R\<^esub> \<plusminus>\<^bsub>R\<^esub> -\<^sub>a\<^bsub>R\<^esub> a" and m = h in sc_assoc,
       rule aGroup.ag_pOp_closed, assumption+, simp add:sprod_one sc_a_0,
       simp add:l_span_zero, simp add:sprod_one)
 
 apply (rotate_tac -1, frule not_sym,
        frule_tac m = "Suc 0" and n = "card H" in noteq_le_less, assumption,
        thin_tac "Suc 0 \<le> card H", thin_tac "card H \<noteq> Suc 0")
 apply (frule_tac a = "Suc 0" and b = "card H" and c = "Suc 0" in
                  diff_less_mono, simp,
        thin_tac "Suc 0 < card H")
 apply (frule_tac H = H and k = "card H - Suc 0" in NAKTr5[of A],
         assumption+, simp, simp)
 apply (erule bexE)
 apply (frule_tac H = H and ?H1.0 = "h ` {j. j \<le> card H - Suc 0 - Suc 0}" in
        generator_generator,
       frule_tac f = h and A = "{j. j \<le> card H - Suc 0}" and B = "carrier M"
       and ?A1.0 = "{j. j \<le> card H - Suc 0 - Suc 0}" in image_sub,
       rule subsetI, simp+)
 apply (erule conjE)
   apply (cut_tac f = h and n = "card H - Suc (Suc 0)" in image_Nset_Suc)
   apply (frule_tac m = "Suc 0" and n = "card H" in Suc_leI)
   apply (simp add:Suc_Suc_Tr)
   apply (frule_tac f = h and A = "{j. j \<le> card H - Suc 0}" and 
          B = "carrier M" and ?A1.0 = "{j. j \<le> card H - Suc 0 - Suc 0}" in 
         image_sub,
         rule subsetI, simp)
   apply (frule_tac H = "h ` {j. j \<le> card H - Suc 0 - Suc 0}" in 
          lin_span_coeff_mono[of A], simp, simp)
   apply (frule_tac c = "h (card H - Suc 0)" and A = 
          "linear_span R M A (h ` {j. j \<le> card H - Suc (Suc 0)})" and 
           B = "linear_span R M (carrier R)
              (h ` {j. j \<le> card H - Suc (Suc 0)})" in subsetD, assumption)
  apply (rule_tac A = H and B = "insert (h (card H - Suc 0)) 
                        (h ` {j. j \<le> card H - Suc (Suc 0)})" and 
          C = "linear_span R M (carrier R)
                  (h ` {j. j \<le> card H - Suc (Suc 0)})" in subset_trans) 
  apply simp
  apply (rule_tac A = "h ` {j. j \<le> card H - Suc (Suc 0)}" and 
         B = "linear_span R M (carrier R)
           (h ` {j. j \<le> card H - Suc (Suc 0)})" and a = "h (card H - Suc 0)" 
        in insert_sub)
  apply (rule subsetI)
  apply (rule_tac H = "h ` {j. j \<le> card H - Suc (Suc 0)}" and h = x in
         h_in_linear_span, assumption+)
  apply (frule_tac H = "h ` {j. j \<le> card H - Suc 0 - Suc 0}" in NAKTr3)
  apply (simp add:generator_sub_carrier)
  apply (rule finite_imageI, simp) 
  apply (thin_tac "H = h ` {j. j \<le> card H - Suc 0} \<and>
           h (card H - Suc 0)
           \<in> linear_span R M A (h ` {j. j \<le> card H - Suc 0 - Suc 0})")
  apply (cut_tac k = "card H - Suc 0 - Suc 0" in finite_Collect_le_nat,
         frule_tac A = "{j. j \<le> card H - Suc 0 - Suc 0}" and f = h in 
                   card_image_le,
         simp)
  apply (frule_tac m = "Suc 0" and n = "card H" in  Suc_leI,
         simp add:Suc_Suc_Tr, simp add:finite_generator_def) (*
  apply (rule_tac i = "card (h ` {j. j \<le> card H - Suc (Suc 0)})" and 
         j = "card H - Suc 0" and k = "card H" in Nat.le_less_trans, assumption+)  
  apply simp*)
  apply (cut_tac k = "card H - Suc 0 - Suc 0" in finite_Collect_le_nat,
         frule_tac F = "{j. j \<le> card H - Suc 0 - Suc 0}" and h = h in 
         finite_imageI, simp add:finite_generator_def)
done
 
lemma (in Module) fg_qmodule:"\<lbrakk> M fgover R; submodule R M N\<rbrakk> \<Longrightarrow>
                          (M /\<^sub>m N) fgover R" 
apply (frule mpj_mHom[of N])
apply (frule mpj_surjec [of N])
apply (rule surjec_finitely_gen [of "M /\<^sub>m N" "mpj M N"])
apply (simp add:qmodule_module)
apply assumption+
done   

lemma (in Module) NAK1:"\<lbrakk>\<not> zeroring R; M fgover R; submodule R M N; 
      ideal R A; A \<subseteq> J_rad R;  carrier M = A \<odot>\<^bsub>R\<^esub> M \<minusplus> N \<rbrakk> \<Longrightarrow> carrier M = N"
apply (subgoal_tac "A \<odot>\<^bsub>R\<^esub> (M /\<^sub>m N) = carrier (M /\<^sub>m N)")
apply (frule fg_qmodule [of N], assumption+)
apply (frule qmodule_module [of N])
apply (frule Module.NAK [of "M /\<^sub>m N" R "A"], assumption+,
       thin_tac "R module M /\<^sub>m N", thin_tac "M /\<^sub>m N fgover R",
       thin_tac "A \<odot>\<^bsub>R\<^esub> M /\<^sub>m N = carrier (M /\<^sub>m N)",
       thin_tac "carrier M = A \<odot>\<^bsub>R\<^esub> M \<minusplus> N")
 apply (simp add:qmodule_def)
apply (rule equalityI) 
 apply (rule subsetI)
 apply (frule_tac m = x in set_mr_cos_mem[of N], assumption)
 apply simp
 apply (frule_tac m = x in m_in_mr_coset[of N], assumption, simp)
 apply (simp add:submodule_subset)
apply (subst smodule_ideal_coeff_def)
apply (frule qmodule_module [of N]) 
 apply (frule Module.lin_span_sub_carrier[of "M /\<^sub>m N" R A "carrier (M /\<^sub>m N)"],
        assumption, simp)
 apply (rule equalityI, assumption+)
 apply (thin_tac "linear_span R (M /\<^sub>m N) A (carrier (M /\<^sub>m N)) \<subseteq> 
                                                      carrier (M /\<^sub>m N)")
 apply (rule subsetI) 
 apply (simp add:qmodule_carr)
 apply (frule_tac x = x in mem_set_mr_cos[of N], assumption, erule bexE)
 apply (frule smodule_ideal_coeff_is_Submodule[of A],
        frule submodule_subset,
        frule submodule_subset[of "A \<odot>\<^bsub>R\<^esub> M"])
 apply (frule_tac x = m in mem_set_sum[of "A \<odot>\<^bsub>R\<^esub> M" "N"], assumption+,
        simp, (erule bexE)+)
 apply simp
  apply (frule submodule_asubg[of N])
  apply (frule sym, thin_tac "carrier M = A \<odot>\<^bsub>R\<^esub> M \<minusplus> N", simp)
  apply (frule_tac c = h in subsetD[of "A \<odot>\<^bsub>R\<^esub> M" "carrier M"], assumption+,
         frule_tac c = k in subsetD[of N "carrier M"], assumption+,
         frule_tac x = h and y = k in ag_pOp_commute, assumption+, simp)
  apply (simp add:arcos_fixed[THEN sym, of N], thin_tac "h \<plusminus> k = k \<plusminus> h",
         thin_tac "m = k \<plusminus> h",
         thin_tac "submodule R M (A \<odot>\<^bsub>R\<^esub> M)",
         thin_tac "A \<odot>\<^bsub>R\<^esub> M \<subseteq> carrier M",
         thin_tac "A \<odot>\<^bsub>R\<^esub> M \<minusplus> N = carrier M")
  apply (simp add:smodule_ideal_coeff_def)
  apply (frule_tac h = h in linmap_im_linspan1 [of A "M /\<^sub>m N" "mpj M N" 
         "carrier M"], assumption+,
         rule mpj_mHom[of N], assumption, simp, assumption)
  apply (frule_tac m = h in elem_mpj[of _ N], assumption,
         frule_tac mpj_surjec[of N], 
         simp add:surjec_def surj_to_def qmodule_carr)
done

section "Direct sum and direct products of modules"

definition
  prodM_sprod :: "[('r, 'm) Ring_scheme, 'i set, 
      'i \<Rightarrow> ('a, 'r, 'm1) Module_scheme] \<Rightarrow>  'r \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow>  ('i \<Rightarrow> 'a)" where
  "prodM_sprod R I A = (\<lambda>a\<in>carrier R. \<lambda>g\<in>carr_prodag I A. 
                                         (\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>(A j)\<^esub> (g j)))"

definition
  prodM :: "[('r, 'm) Ring_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'm1) Module_scheme] \<Rightarrow>
     \<lparr> carrier:: ('i \<Rightarrow> 'a) set, 
       pop::['i \<Rightarrow> 'a, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a),
       mop:: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a), zero::('i \<Rightarrow> 'a), 
       sprod :: ['r, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a) \<rparr>" where
  "prodM R I A = \<lparr>carrier = carr_prodag I A, 
    pop = prod_pOp I A, mop = prod_mOp I A,
    zero = prod_zero I A, sprod = prodM_sprod R I A \<rparr>"  

definition
  mProject :: "[('r, 'm) Ring_scheme, 'i set,
             'i \<Rightarrow> ('a, 'r, 'more) Module_scheme, 'i] \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "mProject R I A j = (\<lambda>f\<in>carr_prodag I A. f j)"

abbreviation
  PRODMODULES  ("(3m\<Pi>\<^bsub>_ _\<^esub> _)" [72,72,73]72) where
  "m\<Pi>\<^bsub>R I\<^esub> A == prodM R I A"

lemma (in Ring) prodM_carr:"\<lbrakk>\<forall>i\<in>I. (R module (M i))\<rbrakk> \<Longrightarrow> 
                                carrier (prodM R I M) = carr_prodag I M"
apply (simp add:prodM_def)
done

lemma (in Ring) prodM_mem_eq:"\<lbrakk>\<forall>i\<in>I. (R module (M i)); 
      m1 \<in> carrier (prodM R I M); m2 \<in> carrier (prodM R I M); 
      \<forall>i\<in>I. m1 i = m2 i \<rbrakk> \<Longrightarrow> m1 = m2" 
apply (simp add:prodM_carr [of I M])
apply (rule carr_prodag_mem_eq [of I M])
apply (rule ballI, drule_tac x = k in bspec, assumption,
       simp add:Module.module_is_ag)
apply assumption+
done

lemma (in Ring) prodM_sprod_mem:"\<lbrakk>\<forall>i\<in>I. (R module (M i)); a \<in> carrier R;
       m \<in> carr_prodag I M\<rbrakk> \<Longrightarrow> prodM_sprod R I M a m \<in> carr_prodag I M" 
apply (simp add:prodM_sprod_def carr_prodag_def)
apply (erule conjE)+
apply (rule conjI)
 apply (rule Pi_I)
 apply (simp add:Un_carrier_def)
 apply (drule_tac x = x in bspec, assumption,
        drule_tac x = x in bspec, assumption+)

 apply (frule_tac R = R and M = "M x" and a = a and m = "m x" in
        Module.sc_mem, assumption+, blast)
 apply (rule ballI, 
        drule_tac x = i in bspec, assumption,
        drule_tac x = i in bspec, assumption+)
       
 apply (frule_tac M = "M i" and a = a and m = "m i" in 
            Module.sc_mem [of _ "R"], assumption+)
done

lemma (in Ring) prodM_sprod_val:"\<lbrakk>\<forall>i\<in>I. (R module (M i)); a \<in> carrier R;
 m \<in> carr_prodag I M; j \<in> I\<rbrakk> \<Longrightarrow> (prodM_sprod R I M a m) j = a \<cdot>\<^sub>s\<^bsub>(M j)\<^esub> (m j)" 
apply (simp add:prodM_sprod_def)
done

lemma (in Ring) prodM_Module:"\<forall>i\<in>I. (R module (M i)) \<Longrightarrow> 
                                      R module (prodM R I M)"
apply (rule Module.intro)
 apply (cut_tac prodag_aGroup[of I M])
apply (simp add:prodM_def prodag_def aGroup_def)
apply (erule conjE)+
 apply (rule allI, rule impI)
 apply (rotate_tac -2,
        frule_tac a = a in forall_spec, assumption)
 apply (thin_tac "\<forall>a. a \<in> carr_prodag I M \<longrightarrow> 
                                      prod_pOp I M (prod_zero I M) a = a",
        thin_tac "\<forall>i\<in>I. R module M i",
        thin_tac "\<forall>a. a \<in> carr_prodag I M \<longrightarrow> (\<forall>b. b \<in> carr_prodag I M \<longrightarrow>
             (\<forall>c. c \<in> carr_prodag I M \<longrightarrow> prod_pOp I M (prod_pOp I M a b) c =
                       prod_pOp I M a (prod_pOp I M b c)))",
        thin_tac "\<forall>a. a \<in> carr_prodag I M \<longrightarrow>
             prod_pOp I M (prod_mOp I M a) a = prod_zero I M",
        frule_tac a = "prod_zero I M" in forall_spec, assumption,
        thin_tac "\<forall>a. a \<in> carr_prodag I M \<longrightarrow> (\<forall>b. b \<in> carr_prodag I M \<longrightarrow>
                  prod_pOp I M a b = prod_pOp I M b a)",
        frule_tac a = a in forall_spec, assumption,
        thin_tac "\<forall>b. b \<in> carr_prodag I M \<longrightarrow> prod_pOp I M (prod_zero I M) b =
             prod_pOp I M b (prod_zero I M)", simp)
 apply (rule ballI, drule_tac x = k in bspec, assumption,
        simp add:Module.module_is_ag)
 apply (rule Module_axioms.intro)
 apply (cut_tac Ring, assumption)
 apply (simp add:prodM_carr, simp add:prodM_def prodM_sprod_mem)
 apply (simp add:prodM_carr, simp add:prodM_def)
 apply (frule_tac a = a and m = m in prodM_sprod_mem[of I M], assumption+,
        frule_tac a = b and m = m in prodM_sprod_mem[of I M], assumption+,
       (cut_tac ring_is_ag,
        frule_tac x = a and y = b in aGroup.ag_pOp_closed[of R], assumption+),
        frule_tac a = "a \<plusminus> b" and m = m in prodM_sprod_mem[of I M], 
        assumption+)
 apply (rule prodM_mem_eq[of I M], assumption, simp add:prodM_carr)
 apply (simp add:prodM_carr,
        rule_tac X = "prodM_sprod R I M a m" and Y = "prodM_sprod R I M b m" 
        in prod_pOp_mem[of I M],
        (rule ballI, drule_tac x = k in bspec, assumption,
        simp add:Module.module_is_ag),
        assumption+)      
 apply (rule ballI,
        simp add:prodM_sprod_def prod_pOp_def,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i",
        thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
        thin_tac "(\<lambda>j\<in>I. b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
        thin_tac "(\<lambda>j\<in>I. (a \<plusminus> b) \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
        simp add:carr_prodag_def, (erule conjE)+,
        drule_tac x = i in bspec, assumption+)

apply (cut_tac Ring, simp add:Module.sc_l_distr)
  apply (simp add:prodM_carr)
  apply (simp add:prodM_def)
  apply (cut_tac X = m and Y = n in prod_pOp_mem[of I M],
         (rule ballI, frule_tac x = k in bspec, assumption,
          thin_tac "\<forall>i\<in>I. R module M i", simp add:Module.module_is_ag),
          assumption+)
  apply (frule_tac a = a and m = "prod_pOp I M m n" in prodM_sprod_mem[of I M],
         assumption+)
 
  apply (rule prodM_mem_eq[of I M], assumption, simp add:prodM_carr)      
  apply (simp add:prodM_carr,
         frule_tac a = a and m = m in prodM_sprod_mem[of I M], assumption+,
         frule_tac a = a and m = n in prodM_sprod_mem[of I M], assumption+,
         rule_tac X = "prodM_sprod R I M a m" and Y = "prodM_sprod R I M a n" 
        in prod_pOp_mem[of I M],
        (rule ballI, drule_tac x = k in bspec, assumption,
        simp add:Module.module_is_ag),
        assumption+)
  apply (rule ballI)
  apply (frule_tac a = a and m = m in prodM_sprod_mem[of I M], assumption+,
         frule_tac a = a and m = n in prodM_sprod_mem[of I M], assumption+,
         simp add:prod_pOp_def prodM_sprod_def,
         drule_tac x = i in bspec, assumption,
         thin_tac "(\<lambda>x\<in>I. m x \<plusminus>\<^bsub>M x\<^esub> n x) \<in> carr_prodag I M",
         thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> (if j \<in> I then m j \<plusminus>\<^bsub>M j\<^esub> n j else undefined))
        \<in> carr_prodag I M",
         thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
         thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> n j) \<in> carr_prodag I M")
   apply (simp add:carr_prodag_def, (erule conjE)+,
          drule_tac x = i in bspec, assumption,
          drule_tac x = i in bspec, assumption)
    
   apply (simp add:Module.sc_r_distr)

  apply (simp add:prodM_carr,
         frule_tac a = b and m = m in prodM_sprod_mem[of I M], assumption+,
         frule_tac a = a and m = "prodM_sprod R I M b m" in prodM_sprod_mem[of
          I M], assumption+)
  apply (frule_tac x = a and y = b in ring_tOp_closed, assumption+,
         frule_tac a = "a \<cdot>\<^sub>r b" and m = m in prodM_sprod_mem[of I M], 
         assumption+)
  apply (simp add:prodM_def,
         rule prodM_mem_eq, assumption+, simp add:prodM_carr,
         simp add:prodM_carr)
  apply (rule ballI, simp add:prodM_sprod_def,
         drule_tac x = i in bspec, assumption,
         thin_tac "(\<lambda>j\<in>I. b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
         thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> (if j \<in> I then b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j else undefined))
        \<in> carr_prodag I M",
         thin_tac "(\<lambda>j\<in>I. (a \<cdot>\<^sub>r b) \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
         simp add:carr_prodag_def, (erule conjE)+,
         drule_tac x = i in bspec, assumption)
     
   apply (simp add:Module.sc_assoc)

  apply (simp add:prodM_carr, cut_tac ring_one,
         frule_tac a = "1\<^sub>r"  and m = m in prodM_sprod_mem[of I M], assumption+,
         rule prodM_mem_eq, assumption+, simp add:prodM_carr,
         simp add:prodM_def, simp add:prodM_def)
  apply (rule ballI, simp add:prodM_def,
         thin_tac "prodM_sprod R I M 1\<^sub>r m \<in> carr_prodag I M",
         simp add:prodM_sprod_def,
         drule_tac x = i in bspec, assumption,
         simp add:carr_prodag_def, (erule conjE)+,
         drule_tac x = i in bspec, assumption,
         simp add:Module.sprod_one)
done
         
definition
  dsumM :: "[('r, 'm) Ring_scheme, 'i set, 'i \<Rightarrow> ('a, 'r, 'more) Module_scheme]
  \<Rightarrow>  \<lparr> carrier:: ('i \<Rightarrow> 'a) set, 
        pop::['i \<Rightarrow> 'a, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a),
        mop:: ('i \<Rightarrow> 'a) \<Rightarrow> ('i \<Rightarrow> 'a), 
        zero::('i \<Rightarrow> 'a), 
        sprod :: ['r, 'i \<Rightarrow> 'a] \<Rightarrow> ('i \<Rightarrow> 'a) \<rparr>" where
 
  "dsumM R I A = \<lparr> carrier = carr_dsumag I A, 
     pop = prod_pOp I A, mop = prod_mOp I A,
     zero = prod_zero I A, sprod = prodM_sprod R I A\<rparr>"  

abbreviation
  DSUMMOD  ("(3\<^bsub>_\<^esub>\<Sigma>\<^sub>d\<^bsub>_\<^esub> _)" [72,72,73]72) where
  "\<^bsub>R\<^esub>\<Sigma>\<^sub>d\<^bsub>I\<^esub> A == dsumM R I A"

lemma (in Ring) dsumM_carr:"carrier (dsumM R I M) = carr_dsumag I M"
by (simp add:dsumM_def)

lemma (in Ring) dsum_sprod_mem:"\<lbrakk>\<forall>i\<in>I. R module M i; a \<in> carrier R;
       b \<in> carr_dsumag I M\<rbrakk>  \<Longrightarrow> prodM_sprod R I M a b \<in> carr_dsumag I M"
apply (simp add:carr_dsumag_def)
 apply (simp add:finiteHom_def, erule conjE, erule exE, (erule conjE)+,
        frule_tac a = a and m = b in prodM_sprod_mem[of I M], assumption+)
 apply (subgoal_tac "\<forall>j\<in>I - H. prodM_sprod R I M a b j = \<zero>\<^bsub>M j\<^esub>", blast)
 apply (rule ballI, 
        drule_tac x = j in bspec, assumption,
        drule_tac x = j in bspec, simp)
      
 apply (subst prodM_sprod_def, simp)
 apply (simp add:Module.sc_a_0)
done

lemma (in Ring) carr_dsum_prod:"carr_dsumag I M \<subseteq> carr_prodag I M"
apply (rule subsetI) apply (simp add:carr_dsumag_def finiteHom_def) 
done

lemma (in Ring) carr_dsum_prod1:"
                 \<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M"
apply (rule allI) apply (rule impI)
apply (cut_tac carr_dsum_prod [of I M])
apply (simp add:subsetD)
done

lemma (in Ring) carr_dsumM_mem_eq:"\<lbrakk>\<forall>i\<in>I. R module M i; x \<in> carr_dsumag I M;
      y \<in> carr_dsumag I M; \<forall>j\<in>I. x j = y j\<rbrakk> \<Longrightarrow> x = y" 
apply (cut_tac carr_dsum_prod [of I M])
apply (frule subsetD [of "carr_dsumag I M" "carr_prodag I M" "x"], assumption+,
       frule subsetD [of "carr_dsumag I M" "carr_prodag I M" "y"], assumption+)
apply (subgoal_tac "\<forall>i\<in>I. aGroup (M i)")
apply (rule carr_prodag_mem_eq [of "I" "M"], assumption+)
apply (rule ballI) 
apply (drule_tac x = i in bspec, assumption,
       simp add:Module.module_is_ag)
done

lemma (in Ring) dsumM_Module:"\<forall>i\<in>I. R module (M i) \<Longrightarrow> R module (\<^bsub>R\<^esub>\<Sigma>\<^sub>d\<^bsub>I\<^esub> M)"
apply (rule Module.intro)
 apply (cut_tac prodag_aGroup[of I M])
 apply (cut_tac carr_dsum_prod1[of I M])
apply (simp add:dsumM_def prodag_def aGroup_def,
       cut_tac dsum_pOp_func[of I M], simp,
       cut_tac dsum_iOp_func[of I M], simp,
       cut_tac dsum_zero_func[of I M], simp)
 apply (erule conjE)+
 apply (rule allI, rule impI,
        thin_tac "\<forall>a. a \<in> carr_prodag I M \<longrightarrow>
             (\<forall>b. b \<in> carr_prodag I M \<longrightarrow>
                  (\<forall>c. c \<in> carr_prodag I M \<longrightarrow>
                       prod_pOp I M (prod_pOp I M a b) c =
                       prod_pOp I M a (prod_pOp I M b c)))",
        thin_tac "\<forall>i\<in>I. R module M i")
  apply (frule_tac a = a in forall_spec, assumption,
         drule_tac a = "prod_zero I M" in forall_spec, assumption)
  apply (drule_tac a = a in forall_spec, assumption,
         rotate_tac -1,
         drule_tac a = "prod_zero I M" in forall_spec, assumption, simp)

  apply (rule ballI, drule_tac x = k in bspec, assumption,
         simp add:Module.module_is_ag) 
  apply (rule ballI, drule_tac x = k in bspec, assumption,
         (simp add:Module.module_is_ag)+)
  apply (rule ballI, drule_tac x = k in bspec, assumption+,
         simp add:Module.module_is_ag)+

apply (rule Module_axioms.intro)
 apply (cut_tac Ring, simp del: Pi_split_insert_domain,
        simp add:dsumM_carr dsumM_def del: Pi_split_insert_domain,
        simp add:dsum_sprod_mem del: Pi_split_insert_domain)

(* sc_l_distr *)
 apply (cut_tac ring_is_ag,
        frule_tac x = a and y = b in aGroup.ag_pOp_closed, assumption+,
        simp add:dsumM_carr del: Pi_split_insert_domain,
        frule_tac a = a and b = m in dsum_sprod_mem[of I M], assumption+,
        frule_tac a = b and b = m in dsum_sprod_mem[of I M], assumption+,
        frule_tac a = "a \<plusminus> b" and b = m in dsum_sprod_mem[of I M], assumption+,
        simp add:dsumM_def del: Pi_split_insert_domain,
        cut_tac X = "prodM_sprod R I M a m" and Y = "prodM_sprod R I M b m" in
        prod_pOp_mem[of I M],
        (rule ballI, frule_tac x = k in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i", simp add:Module.module_is_ag del: Pi_split_insert_domain),
        (cut_tac carr_dsum_prod[of I M], simp add:subsetD del: Pi_split_insert_domain)+)
   apply(cut_tac carr_dsum_prod1[of I M])
apply(rule prodM_mem_eq)
apply(assumption+)
apply((simp add:prodM_carr del: Pi_split_insert_domain)+)
apply(rule ballI)
apply(simp add:prodM_sprod_def prod_pOp_def del: Pi_split_insert_domain PiE_restrict)
apply(thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
        thin_tac "(\<lambda>j\<in>I. b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
        thin_tac "(\<lambda>j\<in>I. (a \<plusminus> b) \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
        thin_tac "(\<lambda>x\<in>I. (if x \<in> I then a \<cdot>\<^sub>s\<^bsub>M x\<^esub> m x else undefined) \<plusminus>\<^bsub>M x\<^esub>
               (if x \<in> I then b \<cdot>\<^sub>s\<^bsub>M x\<^esub> m x else undefined))
        \<in> carr_prodag I M")
   apply (frule_tac a = m in forall_spec, assumption,
               thin_tac "\<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M",
               frule_tac x = i in bspec, assumption,
               thin_tac "\<forall>i\<in>I. R module M i",
               thin_tac "m \<in> carr_dsumag I M",
               simp add:carr_prodag_def, (erule conjE)+,
               frule_tac x = i in bspec, assumption,
               thin_tac "\<forall>i\<in>I. m i \<in> carrier (M i)")
    apply (simp add:Module.sc_l_distr)

 (** sc_r_distr **)
 apply (simp add:dsumM_carr,
        frule_tac a = a and b = m in dsum_sprod_mem[of I M], assumption+,
        frule_tac a = a and b = n in dsum_sprod_mem[of I M], assumption+)
 apply (simp add:dsumM_def, cut_tac carr_dsum_prod1[of I M],
        cut_tac X = m and Y = n in prod_pOp_mem[of I M],
        (rule ballI, frule_tac x = k in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i", simp add:Module.module_is_ag), simp+,
        frule_tac a = a and m = "prod_pOp I M m n" in prodM_sprod_mem[of I M],
        assumption, simp)
 apply (cut_tac X = "prodM_sprod R I M a m" and Y = "prodM_sprod R I M a n" in
        prod_pOp_mem[of I M],
        (rule ballI, frule_tac x = k in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i", simp add:Module.module_is_ag), simp+,
        rule_tac ?m1.0 = "prodM_sprod R I M a (prod_pOp I M m n)" and 
        ?m2.0 = "prod_pOp I M (prodM_sprod R I M a m) (prodM_sprod R I M a n)"
        in prodM_mem_eq[of I M], assumption, (simp add:prodM_carr)+)
 apply (rule ballI,
        frule_tac x = i in bspec, assumption,
        thin_tac "prodM_sprod R I M a m \<in> carr_dsumag I M",
        thin_tac "prodM_sprod R I M a n \<in> carr_dsumag I M")
 apply (rotate_tac 1,
        frule_tac a = m in forall_spec, assumption,
        frule_tac a = n in forall_spec, assumption,
        thin_tac "\<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M",
        thin_tac "m \<in> carr_dsumag I M",
        thin_tac "n \<in> carr_dsumag I M")
 apply (frule_tac a = a and m = m in prodM_sprod_mem[of I M], assumption+, 
        frule_tac a = a and m = n in prodM_sprod_mem[of I M], assumption+)
 apply (simp add:prodM_sprod_def prod_pOp_def del: PiE_restrict,
        thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> (if j \<in> I then m j \<plusminus>\<^bsub>M j\<^esub> n j else undefined))
        \<in> carr_prodag I M",
        thin_tac "(\<lambda>x\<in>I. (if x \<in> I then a \<cdot>\<^sub>s\<^bsub>M x\<^esub> m x else undefined) \<plusminus>\<^bsub>M x\<^esub>
               (if x \<in> I then a \<cdot>\<^sub>s\<^bsub>M x\<^esub> n x else undefined))
        \<in> carr_prodag I M",
        thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M",
        thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> n j) \<in> carr_prodag I M",
        thin_tac "(\<lambda>x\<in>I. m x \<plusminus>\<^bsub>M x\<^esub> n x) \<in> carr_prodag I M")
  apply (simp add:carr_prodag_def, (erule conjE)+,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i",
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. m i \<in> carrier (M i)",
        frule_tac x = i in bspec, assumption,
        simp add:Module.sc_r_distr)

  apply (frule_tac x = a and y = b in ring_tOp_closed, assumption+,
        simp add:dsumM_carr,
     frule_tac a = b and b = m in dsum_sprod_mem[of I M], assumption+,
     frule_tac a = a and b = "prodM_sprod R I M b m" in dsum_sprod_mem[of I M],
     assumption+,
     frule_tac a = "a \<cdot>\<^sub>r b" and b = m in dsum_sprod_mem[of I M], assumption+)
 apply (cut_tac carr_dsum_prod1[of I M])
 apply (simp add:dsumM_def,
        rule_tac ?m1.0 = "prodM_sprod R I M (a \<cdot>\<^sub>r b) m" and 
        ?m2.0 = "prodM_sprod R I M a (prodM_sprod R I M b m)"
        in prodM_mem_eq[of I M], assumption, (simp add:prodM_carr)+)
 apply (rule ballI, simp add:prodM_sprod_def,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i",
        thin_tac "(\<lambda>j\<in>I. b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
        thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> (if j \<in> I then b \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j else undefined))
        \<in> carr_dsumag I M",
        thin_tac "(\<lambda>j\<in>I. (a \<cdot>\<^sub>r b) \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
        frule_tac a = m in forall_spec, assumption,
        thin_tac "\<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M",
        thin_tac "m \<in> carr_dsumag I M",
        simp add:carr_prodag_def, (erule conjE)+,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. m i \<in> carrier (M i)",
        simp add:Module.sc_assoc)

  apply (simp add:dsumM_carr)      
  apply (simp add:dsumM_def)
  apply (cut_tac ring_one,
         cut_tac carr_dsum_prod1[of I M],
         frule_tac a = "1\<^sub>r" and b = m in dsum_sprod_mem[of I M], assumption+,
         rule_tac ?m1.0 = "prodM_sprod R I M 1\<^sub>r m" and
         ?m2.0 = m in prodM_mem_eq[of I M], assumption, (simp add:prodM_carr)+,
         frule_tac a = m in forall_spec, assumption,
         frule_tac a = "prodM_sprod R I M 1\<^sub>r m" in forall_spec, assumption,
         thin_tac "\<forall>x. x \<in> carr_dsumag I M \<longrightarrow> x \<in> carr_prodag I M")
  apply (rule ballI,
        frule_tac x = i in bspec, assumption,
        thin_tac "\<forall>i\<in>I. R module M i")
 apply (simp add:prodM_sprod_def)
  apply (thin_tac "(\<lambda>j\<in>I. 1\<^sub>r \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
         thin_tac "(\<lambda>j\<in>I. 1\<^sub>r \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_prodag I M")
  apply (simp add:carr_prodag_def, (erule conjE)+,
         frule_tac x = i in bspec, assumption,
         simp add:Module.sprod_one)
done
  
definition
  ringModule :: "('r, 'b) Ring_scheme \<Rightarrow> ('r, 'r) Module"
                ("(M\<^bsub>_\<^esub>)" [998]999) where
  "M\<^bsub>R\<^esub> = \<lparr>carrier = carrier R, pop = pop R, mop = mop R,
        zero = zero R, sprod = tp R\<rparr>" 

lemma (in Ring) ringModule_Module:"R module M\<^bsub>R\<^esub>"
apply (rule Module.intro)
 apply (simp add:aGroup_def,  simp add:ringModule_def,
        simp add:pop_closed,  simp add:pop_aassoc,
        simp add:pop_commute, simp add:mop_closed,
        simp add:l_m,         simp add:ex_zero,
        simp add:l_zero)

apply (rule Module_axioms.intro)
 apply (cut_tac Ring, assumption,
        simp add:ringModule_def, simp add:ring_tOp_closed,
        simp add:ringModule_def, simp add:ring_distrib2,
        simp add:ringModule_def, simp add:ring_distrib1,
        simp add:ringModule_def, simp add:ring_tOp_assoc,
        simp add:ringModule_def, simp add:rg_l_unit)
done

definition
  dsumMhom :: "['i set, 'i \<Rightarrow> ('a, 'r, 'm) Module_scheme, 
    'i \<Rightarrow> ('b, 'r, 'm1) Module_scheme, 'i \<Rightarrow> ('a \<Rightarrow> 'b)] \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> 
    ('i \<Rightarrow> 'b)" where

  "dsumMhom I A B S = (\<lambda>f\<in>carr_dsumag I A. (\<lambda>k\<in>I. (S k) (f k)))" 

(**     I \<longrightarrow> A
          \   |
           \  | S
              B        **)
 

lemma (in Ring) dsumMhom_mem:"\<lbrakk>\<forall>i\<in>I. R module M i; \<forall>i\<in>I. R module N i;
                \<forall>i\<in>I. S i \<in> mHom R (M i) (N i); x \<in> carr_dsumag I M\<rbrakk>
                 \<Longrightarrow> dsumMhom I M N S x \<in> carr_dsumag I N"
apply (subst carr_dsumag_def, simp, simp add:finiteHom_def)
apply (rule conjI)
 apply (simp add:dsumMhom_def)
 apply (cut_tac carr_dsum_prod1[of I M],
        drule_tac a = x in forall_spec, assumption) apply (
         subst carr_prodag_def, simp)
   apply (rule conjI,
          rule Pi_I,
          thin_tac "x \<in> carr_dsumag I M", simp,
          simp add:Un_carrier_def,
          drule_tac x = xa in bspec, assumption,
          drule_tac x = xa in bspec, assumption,
          drule_tac x = xa in bspec, assumption,
          simp add:carr_prodag_def, (erule conjE)+,
          drule_tac x = xa in bspec, assumption)

   apply (frule_tac R = R and M = "M xa" and N = "N xa" and f = "S xa" and 
          m = "x xa" in Module.mHom_mem, assumption+, blast)

  apply (rule ballI,
         drule_tac x = i in bspec, assumption,
         drule_tac x = i in bspec, assumption,
         drule_tac x = i in bspec, assumption,
         simp add:carr_prodag_def, (erule conjE)+,
         drule_tac x = i in bspec, assumption)
  apply (simp add:Module.mHom_mem)
   apply (cut_tac carr_dsum_prod1[of I M],
         drule_tac a = x in forall_spec, assumption)

  apply (simp add:dsumMhom_def)
  apply (simp add:carr_prodag_def, (erule conjE)+)
  apply (simp add:carr_dsumag_def, simp add:finiteHom_def)
  apply (erule conjE, erule exE)
  apply (subgoal_tac "\<forall>j\<in>I - H. S j (x j) = \<zero>\<^bsub>N j\<^esub>", blast)
  apply (rule ballI,
         drule_tac x = j in bspec, simp,
         drule_tac x = j in bspec, simp,
         drule_tac x = j in bspec, simp,
         simp add:carr_prodag_def, (erule conjE)+,
         drule_tac x = j in bspec, simp)
  apply (simp add:Module.mHom_0)
done

lemma (in Ring) dsumMhom_mHom:"\<lbrakk>\<forall>i\<in>I. (R module (M i)); 
      \<forall>i\<in>I. (R module (N i)); \<forall>i\<in>I. ((S i) \<in> mHom R (M i) (N i))\<rbrakk> \<Longrightarrow> 
                dsumMhom I M N S \<in> mHom R (dsumM R I M) (dsumM R I N)"
apply (subst mHom_def, simp) 
apply (rule conjI)
 apply (simp add:aHom_def,
        rule conjI,
        simp add:dsumM_def dsumMhom_mem)
apply (rule conjI,
        simp add:dsumMhom_def extensional_def dsumM_def)
apply (rule ballI)+
 apply (simp add:dsumM_def)
 apply (subgoal_tac "\<forall>i\<in>I. aGroup (M i)",
        frule_tac X = a and Y = b in dsum_pOp_mem [of I M], assumption+,
        frule_tac x = "prod_pOp I M a b" in dsumMhom_mem [of I M N S], 
        assumption+,
        frule_tac x = a in dsumMhom_mem [of I M N S], assumption+,
        frule_tac x = b in dsumMhom_mem [of I M N S], assumption+)
 apply (subgoal_tac "\<forall>i\<in>I. aGroup (N i)")
 apply (frule_tac X = "dsumMhom I M N S a" and Y = "dsumMhom I M N S b" in 
                                      dsum_pOp_mem [of I N], assumption+)
 apply (rule carr_dsumM_mem_eq [of I N], assumption+, rule ballI) 
 apply (cut_tac carr_dsum_prod1 [of  I M], cut_tac carr_dsum_prod1 [of I N])
 apply (simp add:prod_pOp_def)
 apply (simp add:dsumMhom_def)
 apply (rule_tac R = R and M = "M j" and N = "N j" and m = "a j" and n = "b j"
        in  Module.mHom_add)
  apply simp+
  apply (simp add:carr_dsumag_def carr_prodag_def finiteHom_def,
         simp add:carr_dsumag_def carr_prodag_def finiteHom_def,
         rule ballI, rotate_tac 1,
         drule_tac x = i in bspec, assumption,
         simp add:Module.module_is_ag,
         rule ballI, drule_tac x = i in bspec, assumption, 
         simp add:Module.module_is_ag)
apply (rule ballI)+
 apply (simp add:dsumM_def)
 apply (frule_tac a = a and b = m in dsum_sprod_mem [of I M], assumption+)
 apply (frule_tac x = "prodM_sprod R I M a m" in 
                  dsumMhom_mem [of I M N S], assumption+)
 apply (frule_tac x = m in dsumMhom_mem [of I M N S], assumption+)
 apply (frule_tac a = a and b = "dsumMhom I M N S m" in 
                    dsum_sprod_mem [of I N], assumption+)
 apply (rule carr_dsumM_mem_eq [of I N], assumption+)
 apply (rule ballI)
 apply (cut_tac carr_dsum_prod1 [of I])
 apply (drule_tac a = m in forall_spec, assumption)
        
  apply (cut_tac carr_dsum_prod1 [of I N],
         frule_tac a = "dsumMhom I M N S m" in forall_spec,
         assumption)
 apply (simp add:dsumMhom_def prodM_sprod_def)
  apply (thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>M j\<^esub> m j) \<in> carr_dsumag I M",
         thin_tac "(\<lambda>k\<in>I. S k (if k \<in> I then a \<cdot>\<^sub>s\<^bsub>M k\<^esub> m k else undefined))
        \<in> carr_dsumag I N",
         thin_tac "(\<lambda>k\<in>I. S k (m k)) \<in> carr_dsumag I N",
         thin_tac "(\<lambda>j\<in>I. a \<cdot>\<^sub>s\<^bsub>N j\<^esub> (if j \<in> I then S j (m j) else undefined))
        \<in> carr_dsumag I N",
         thin_tac "\<forall>x. x \<in> carr_dsumag I N \<longrightarrow> x \<in> carr_prodag I N")
  apply (drule_tac x = j in bspec, assumption,
         drule_tac x = j in bspec, assumption,
         drule_tac x = j in bspec, assumption,
         simp add:carr_prodag_def, (erule conjE)+,
         drule_tac x = j in bspec, assumption)
  apply (simp add:Module.mHom_lin)
done

end
