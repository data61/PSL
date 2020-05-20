theory GeneralizedZippingLemma
imports CompositionBase
begin

context Compositionality
begin

(* The proof of the generalized zipping lemma is split into parts
  generalized_zipping_lemma1 .. generalized_zipping_lemma4
  corresponding to the four cases of well behaved composition.
    
Afterwards the actual lemma is proved based on these four parts. *)
 
(* Generalized zipping lemma for case one of lemma 6.4.4 *)
lemma generalized_zipping_lemma1: "\<lbrakk> N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}; N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<rbrakk> \<Longrightarrow> 
  \<forall> \<tau> lambda t1 t2. ( ( set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> set lambda \<subseteq> V\<^bsub>\<V>\<^esub> \<and> set t1 \<subseteq> E\<^bsub>ES1\<^esub> \<and> set t2 \<subseteq> E\<^bsub>ES2\<^esub>
  \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub> \<and> (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)
  \<and> (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [] \<and> (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []) 
  \<longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = [])) )"
proof -
  assume Nv1_inter_E2_empty: "N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}"
    and Nv2_inter_E1_empty: "N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"

  {
    fix \<tau> lambda t1 t2
    assume \<tau>_in_Estar: "set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      and lambda_in_Vvstar: "set lambda \<subseteq> V\<^bsub>\<V>\<^esub>"
      and t1_in_E1star: "set t1 \<subseteq> E\<^bsub>ES1\<^esub>"
      and t2_in_E2star: "set t2 \<subseteq> E\<^bsub>ES2\<^esub>"
      and \<tau>_E1_t1_in_Tr1: "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<tau>_E2_t2_in_Tr2: "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>"
      and lambda_E1_is_t1_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and lambda_E2_is_t2_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and t1_no_Cv1: "(t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = []"
      and t2_no_Cv2: "(t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []"
   
     have "\<lbrakk> set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>;
      set lambda \<subseteq> V\<^bsub>\<V>\<^esub>; 
      set t1 \<subseteq> E\<^bsub>ES1\<^esub>;
      set t2 \<subseteq> E\<^bsub>ES2\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>;
      (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [];
      (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = [] \<rbrakk>  
      \<Longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []))"
      proof (induct lambda arbitrary: \<tau> t1 t2)
        case (Nil \<tau> t1 t2)
        
        have "(\<tau> @ []) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          proof -
            have "\<tau> \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              proof -
                from Nil(5) validES1 have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def 
                    prefixclosed_def prefix_def)
                moreover
                from Nil(6) validES2 have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def
                    prefixclosed_def prefix_def)
                moreover 
                note Nil(1)
                ultimately show ?thesis
                  by (simp add: composeES_def)
              qed
            thus ?thesis
              by auto
          qed
        moreover
        have "([] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        moreover
        have "([] \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        ultimately show ?case
          by blast
      next
        case (Cons \<V>' lambda' \<tau> t1 t2) 
        thus ?case
          proof -
            from Cons(3) have v'_in_Vv: "\<V>' \<in> V\<^bsub>\<V>\<^esub>"
              by auto

            have "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> 
              \<or> \<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>
              \<or> \<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"  
              using Vv_is_Vv1_union_Vv2 v'_in_Vv  propSepViews
              unfolding properSeparationOfViews_def 
              by fastforce
            moreover {
              assume v'_in_Vv1_inter_Vv2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>" and v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>" 
                by auto
              with v'_in_Vv propSepViews 
              have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>" and v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def by auto
          
              (* split t1, t2 w. r. t. \<V>' *)
              from Cons(2,4,8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              from Cons(3,5,9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto

              (* properties of r1, s1 *)
              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>" 
                and s1_in_E1star: "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              from Cons(6) t1_is_r1_v'_s1 
              have \<tau>E1_r1_v'_s1_in_Tr1: "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ [\<V>'] @ s1 \<in> Tr\<^bsub>ES1\<^esub>"
                by simp

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof -
                  note r1_in_E1star
                  moreover
                  from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Diff_eq Int_commute 
                      Int_empty_right disjoint_eq_subset_Compl 
                      list_subset_iff_projection_neutral projection_on_union)
                  moreover
                  from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Diff_eq  Int_commute 
                      Int_empty_right disjoint_eq_subset_Compl 
                      list_subset_iff_projection_neutral projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              with Nv1_inter_E2_empty have r1E2_empty: "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                by (metis Int_commute empty_subsetI projection_on_subset2 r1_Vv_empty)                

              (* properties of r2, s2 *)
              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>" 
                and s2_in_E2star: "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              from Cons(7) t2_is_r2_v'_s2 
              have \<tau>E2_r2_v'_s2_in_Tr2: "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ [\<V>'] @ s2 \<in> Tr\<^bsub>ES2\<^esub>"
                by simp

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
                proof -
                  note r2_in_E2star
                  moreover
                  from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV2
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              with Nv2_inter_E1_empty have r2E1_empty: "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                by (metis Int_commute empty_subsetI projection_on_subset2 r2_Vv_empty)          
                            
              (* apply inductive hypothesis to lambda' s1 s2 *)
              let ?tau = "\<tau> @ r1 @ r2 @ [\<V>']"

              from Cons(2) r1_in_E1star r2_in_E2star v'_in_E2 
              have "set ?tau \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
                by (simp add: composeES_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              note s1_in_E1star s2_in_E2star
              moreover
              from Cons(6) r1_in_E1star r2E1_empty v'_in_E1 t1_is_r1_v'_s1 
              have "((?tau \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ s1) \<in> Tr\<^bsub>ES1\<^esub>"
                by (simp only: projection_concatenation_commute 
                  list_subset_iff_projection_neutral projection_def, auto)
              moreover
              from Cons(7) r2_in_E2star r1E2_empty v'_in_E2 t2_is_r2_v'_s2 
              have "((?tau \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ s2) \<in> Tr\<^bsub>ES2\<^esub>"
                by (simp only: projection_concatenation_commute 
                  list_subset_iff_projection_neutral projection_def, auto)
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                proof -
                  from Cons(2,4,8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                    by (simp add: projection_def)
                  moreover
                  from t1_is_r1_v'_s1 r1_Vv_empty v'_in_Vv1 Vv_is_Vv1_union_Vv2 
                  have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                    by (simp only: t1_is_r1_v'_s1 projection_concatenation_commute 
                      projection_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                proof -
                  from Cons(3,5,9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                    by (simp add: projection_def)
                  moreover
                  from t2_is_r2_v'_s2 r2_Vv_empty v'_in_Vv2 Vv_is_Vv1_union_Vv2 
                  have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                    by (simp only: t2_is_r2_v'_s2 projection_concatenation_commute 
                      projection_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              moreover
              note s1_Cv1_empty s2_Cv2_empty Cons.hyps(1)[of ?tau s1 s2]
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r1 @ r2 @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)              
              note tau_t'_in_Tr
              moreover
              from r1_Vv_empty r2_Vv_empty t'Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                hence "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"                 
                    by (metis  projection_on_subset2  r1_Cv1_empty r1_in_E1star)
                  moreover
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                hence "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                    by (metis  projection_on_subset2 r2_Cv2_empty r2_in_E2star)
                  moreover
                  note v'_in_Vv VIsViewOnE t'Cv_empty 
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def VC_disjoint_def projection_def, auto)
                qed
              ultimately have ?thesis 
                by auto
            }
            moreover {
              assume v'_in_Vv1_minus_E2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>"
                by auto
              with v'_in_Vv propSepViews have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>"
                unfolding properSeparationOfViews_def
                by auto

              from v'_in_Vv1_minus_E2 have v'_notin_E2: "\<V>' \<notin> E\<^bsub>ES2\<^esub>"
                by (auto)
              with validV2 have v'_notin_Vv2: "\<V>' \<notin> V\<^bsub>\<V>2\<^esub>"
                by (simp add: isViewOn_def V_valid_def, auto)

               (* split t1 w.r.t. \<V>' *)
              from Cons(3) Cons(4) Cons(8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto
              
              (* properties of r1 s1 *)
              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
              proof -
                note r1_in_E1star
                moreover
                from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq  Int_commute 
                    Int_empty_right disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq  Int_commute 
                    Int_empty_right disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                note validV1
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
              qed
              with Nv1_inter_E2_empty have r1E2_empty: "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"               
                by (metis Int_commute empty_subsetI 
                  projection_on_subset2 r1_Vv1_empty)
             
              (* apply inductive hypothesis to lambda' r1 t2 *)
              let ?tau = "\<tau> @ r1 @ [\<V>']"
              
              from v'_in_E1 Cons(2) r1_in_Nv1star validV1 
              have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: isViewOn_def composeES_def V_valid_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from Cons(4) t1_is_r1_v'_s1 have "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto
              moreover
              note Cons(5)
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1 \<in> Tr\<^bsub>ES1\<^esub>"
                by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(3) Cons.prems(5) 
                  projection_concatenation_commute t1_is_r1_v'_s1)
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ t2 \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  from v'_notin_E2 have "[\<V>'] \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                    by (simp add: projection_def)
                  with Cons(7) Cons(4) t1_is_r1_v'_s1 v'_notin_E2 
                    r1_in_Nv1star Nv1_inter_E2_empty r1E2_empty
                    show ?thesis
                      by (simp only: t1_is_r1_v'_s1 list_subset_iff_projection_neutral 
                        projection_concatenation_commute, auto)
                qed
              moreover
              from Cons(8) t1_is_r1_v'_s1 r1_Vv_empty v'_in_E1 v'_in_Vv have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(9) v'_notin_E2 have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
                by (simp add: projection_def)
              moreover
              note s1_Cv1_empty Cons(11)
              moreover
              note Cons.hyps(1)[of ?tau s1 t2]
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r1 @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)      
              note tau_t'_in_Tr
              moreover
              from r1_Vv_empty t'_Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                hence"r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"                 
                  by (metis projection_on_subset2 r1_Cv1_empty r1_in_E1star)
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            moreover {
              assume v'_in_Vv2_minus_E1: "\<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
              hence v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>"
                by auto
              with v'_in_Vv propSepViews 
              have v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def by auto

              from v'_in_Vv2_minus_E1 
              have v'_notin_E1: "\<V>' \<notin> E\<^bsub>ES1\<^esub>"
                by (auto)
              with validV1 
              have v'_notin_Vv1: "\<V>' \<notin> V\<^bsub>\<V>1\<^esub>"
                by (simp add:isViewOn_def V_valid_def, auto)

               (* split t2 w.r.t. \<V>' *)
              from Cons(4) Cons(5) Cons(9) v'_in_E2 
              have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto
              
              (* properties of r2 s2 *)
              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
              proof -
                note r2_in_E2star
                moreover
                from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                note validV2
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
              qed
              with Nv2_inter_E1_empty have r2E1_empty: "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"               
                by (metis Int_commute empty_subsetI 
                  projection_on_subset2 r2_Vv2_empty)
             
              (* apply inductive hypothesis to lambda' t1 r2 *)
              let ?tau = "\<tau> @ r2 @ [\<V>']"
              
              from v'_in_E2 Cons(2) r2_in_Nv2star validV2 
              have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              note Cons(4)
              moreover
              from Cons(5) t2_is_r2_v'_s2 have "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ t1 \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  from v'_notin_E1 have "[\<V>'] \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                    by (simp add: projection_def)
                  with Cons(6) Cons(3) t2_is_r2_v'_s2 v'_notin_E1 r2_in_Nv2star 
                    Nv2_inter_E1_empty r2E1_empty
                    show ?thesis
                      by (simp only: t2_is_r2_v'_s2 list_subset_iff_projection_neutral 
                        projection_concatenation_commute, auto)
                qed
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2 \<in> Tr\<^bsub>ES2\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(4) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(4) Cons.prems(6) 
                  projection_concatenation_commute t2_is_r2_v'_s2)
              moreover
              from Cons(8) v'_notin_E1 have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
                by (simp add: projection_def)
              moreover
              from Cons(9) t2_is_r2_v'_s2 r2_Vv_empty v'_in_E2 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              note Cons(10) s2_Cv2_empty
              moreover
              note Cons.hyps(1)[of ?tau t1 s2]
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r2 @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)      
              note tau_t'_in_Tr
              moreover
              from r2_Vv_empty t'_Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                hence "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"                 
                  by (metis projection_on_subset2 r2_Cv2_empty r2_in_E2star)
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            ultimately show ?thesis
              by blast
          qed
        qed
  }
  thus ?thesis 
    by auto
qed

 (* Generalized zipping lemma for case two of lemma 6.4.4 *)
lemma generalized_zipping_lemma2: "\<lbrakk> N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}; total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>); BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<rbrakk> \<Longrightarrow> 
  \<forall> \<tau> lambda t1 t2. ( ( set \<tau> \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<and> set lambda \<subseteq> V\<^bsub>\<V>\<^esub> \<and> set t1 \<subseteq> E\<^bsub>ES1\<^esub> \<and> set t2 \<subseteq> E\<^bsub>ES2\<^esub>
  \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>
  \<and> (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)
  \<and> (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [] \<and> (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []) 
  \<longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = [])) )"
proof -
  assume Nv1_inter_E2_empty: "N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}"
  assume total_ES1_Cv1_inter_Nv2: "total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
  assume BSIA: "BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"

  {
    fix \<tau> lambda t1 t2
    assume \<tau>_in_Estar: "set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      and lambda_in_Vvstar: "set lambda \<subseteq> V\<^bsub>\<V>\<^esub>"
      and t1_in_E1star: "set t1 \<subseteq> E\<^bsub>ES1\<^esub>"
      and t2_in_E2star: "set t2 \<subseteq> E\<^bsub>ES2\<^esub>"
      and \<tau>_E1_t1_in_Tr1: "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<tau>_E2_t2_in_Tr2: "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>"
      and lambda_E1_is_t1_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and lambda_E2_is_t2_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and t1_no_Cv1: "(t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = []"
      and t2_no_Cv2: "(t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []"

      have "\<lbrakk> set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>; set lambda \<subseteq> V\<^bsub>\<V>\<^esub>; 
        set t1 \<subseteq> E\<^bsub>ES1\<^esub>; set t2 \<subseteq> E\<^bsub>ES2\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>; ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>;
      (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>); (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = []; (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = [] \<rbrakk>  
      \<Longrightarrow> (\<exists>t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []))"
      proof (induct lambda arbitrary: \<tau> t1 t2)
        case (Nil \<tau> t1 t2)
        
        have "(\<tau> @ []) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          proof -
            have "\<tau> \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              proof -
                from Nil(5) validES1 have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def 
                    prefixclosed_def prefix_def)
                moreover
                from Nil(6) validES2 have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def
                    prefixclosed_def prefix_def)
                moreover 
                note Nil(1)
                ultimately show ?thesis
                  by (simp add: composeES_def)
              qed
            thus ?thesis
              by auto
          qed
        moreover
        have "([] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        moreover
        have "([] \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        ultimately show ?case
          by blast
      next
        case (Cons \<V>' lambda' \<tau> t1 t2) 
        thus ?case
          proof -
            from Cons(3) have v'_in_Vv: "\<V>' \<in> V\<^bsub>\<V>\<^esub>"
              by auto

            have "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<or> \<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub> \<or> \<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>" 
              using propSepViews unfolding properSeparationOfViews_def 
              using Vv_is_Vv1_union_Vv2 v'_in_Vv by fastforce
            moreover {
              assume v'_in_Vv1_inter_Vv2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>" and v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>" 
                by auto
              with v'_in_Vv propSepViews
              have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>" and v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def by auto

              (* split t2 w.r.t. \<V>' *)
              from Cons(3,5,9) v'_in_E2 
              have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto

              (* properties of r2 s2 *)
              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>" 
                and s2_in_E2star: "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              from Cons(7) t2_is_r2_v'_s2 
              have \<tau>E2_r2_v'_s2_in_Tr2: "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ [\<V>'] @ s2 \<in> Tr\<^bsub>ES2\<^esub>"
                by simp

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
                proof -
                  note r2_in_E2star
                  moreover
                  from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV2
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              
              have r2E1_in_Nv2_inter_C1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                proof -
                  have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) = set r2 \<inter> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  with r2_in_Nv2star have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
                    by auto
                  moreover 
                  from validV1 propSepViews 
                  have "E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>"
                    unfolding properSeparationOfViews_def isViewOn_def V_valid_def 
                    using disjoint_Nv2_Vv1 by blast
                  ultimately show ?thesis
                    by auto
                qed
 
              note outerCons_prems = Cons.prems

              (* repair t1 by inserting r2 \<upharpoonleft> E\<^bsub>ES1\<^esub> *)
              have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>) \<Longrightarrow> 
                \<exists> t1'. ( set t1' \<subseteq> E\<^bsub>ES1\<^esub> 
                \<and> ((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub> 
                \<and> t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> 
                \<and> t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [] )"
              proof (induct "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>" arbitrary: r2 rule: rev_induct)
                case Nil thus ?case     
                  by (metis append_self_conv outerCons_prems(9) 
                    outerCons_prems(3) outerCons_prems(5) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE1: "xs = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES1\<^esub>"
                      by (simp add: projection_def, auto)
                    hence "set xs \<subseteq> E\<^bsub>ES1\<^esub>"
                      by auto
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                  proof -
                    have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"                      
                      by (metis Int_commute snoc.prems)
                    with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by simp
                    hence "set xs \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by auto
                    with xs_is_xsE1 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t1''
                  where t1''_in_E1star: "set t1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                  and \<tau>_xs_E1_t1''_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1'' \<in> Tr\<^bsub>ES1\<^esub>"
                  and t1''Vv1_is_t1Vv1: "t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and t1''Cv1_empty: "t1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by auto
                              
                have x_in_Cv1_inter_Nv2: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by simp
                    thus ?thesis
                      by auto
                  qed
                hence x_in_Cv1: "x \<in> C\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E1_t1''_in_Tr1 t1''Cv1_empty
                moreover
                have Adm: "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) x)"
                  proof -
                    from \<tau>_xs_E1_t1''_in_Tr1 validES1 
                    have \<tau>_xsE1_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def 
                        prefixclosed_def prefix_def)
                    with x_in_Cv1_inter_Nv2 total_ES1_Cv1_inter_Nv2 
                    have \<tau>_xsE1_x_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1)" ..
                    ultimately show ?thesis
                      by (simp add: Adm_def, auto)
                  qed
                moreover note BSIA
                ultimately obtain t1'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  and res2: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and res3: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t1' \<subseteq> E\<^bsub>ES1\<^esub>"
                  proof -
                    from res1 validES1 
                    have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1') \<subseteq> E\<^bsub>ES1\<^esub>"
                      by (simp add: ES_valid_def traces_contain_events_def, auto)
                    thus ?thesis
                      by auto
                  qed
                moreover 
                have "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  proof -
                    from res1 xs_is_xsE1 have "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (xs @ [x])) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp only: projection_concatenation_commute, auto)
                    thus  ?thesis
                      by (simp only: snoc(2) projection_concatenation_commute)
                  qed
                moreover
                from t1''Vv1_is_t1Vv1 res2 have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r2E1_in_Nv2_inter_C1_star] obtain t1'
                where t1'_in_E1star: "set t1' \<subseteq> E\<^bsub>ES1\<^esub>" 
                and \<tau>r2E1_t1'_in_Tr1: "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                and t1'_Vv1_is_t1_Vv1: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                and t1'_Cv1_empty: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by auto

              (* split t1' w.r.t. \<V>' *)
              have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                proof -
                  from projection_intersection_neutral[OF Cons(4), of "V\<^bsub>\<V>\<^esub>"] 
                  propSepViews
                  have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" 
                    unfolding properSeparationOfViews_def
                    by (simp only: Int_commute)
                  with Cons(8) t1'_Vv1_is_t1_Vv1 v'_in_E1 show ?thesis
                    by (simp add: projection_def)
                qed
              from projection_split_first[OF this] obtain r1' s1'
                where t1'_is_r1'_v'_s1': "t1' = r1' @ [\<V>'] @ s1'"
                and r1'_Vv1_empty: "r1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto
              
              (* properties of r1' s1' *)
              from t1'_is_r1'_v'_s1' t1'_Cv1_empty 
              have r1'_Cv1_empty: "r1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)
              
              from t1'_is_r1'_v'_s1' t1'_Cv1_empty 
              have s1'_Cv1_empty: "s1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)
              
              from t1'_in_E1star t1'_is_r1'_v'_s1' 
              have r1'_in_E1star: "set r1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto
              with propSepViews r1'_Vv1_empty 
              have r1'_Vv_empty: "r1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                unfolding properSeparationOfViews_def
                by (metis projection_on_subset2 subset_iff_psubset_eq)

              have r1'_in_Nv1star: "set r1' \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof - 
                  note r1'_in_E1star
                  moreover
                  from r1'_Vv1_empty have "set r1' \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r1'_Cv1_empty have "set r1' \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              with Nv1_inter_E2_empty have r1'E2_empty: "r1' \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"               
                by (metis Int_commute empty_subsetI 
                  projection_on_subset2 r1'_Vv1_empty)
              
              (* apply inductive hypothesis to lambda' s1' s2 *)
              let ?tau = "\<tau> @ r2 @ r1' @ [\<V>']"
           
              from Cons(2) r2_in_E2star r1'_in_E1star v'_in_E2 
              have "set ?tau \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
                by (simp add: composeES_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from t1'_in_E1star t1'_is_r1'_v'_s1' 
              have "set s1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by simp
              moreover
              note s2_in_E2star
              moreover
              from \<tau>r2E1_t1'_in_Tr1 t1'_is_r1'_v'_s1' v'_in_E1 
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  from v'_in_E1 r1'_in_E1star 
                  have  "(\<tau> @ r2 @ r1' @ [\<V>']) \<upharpoonleft> E\<^bsub>ES1\<^esub> =  (\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1' @ [\<V>']"
                    by (simp only: projection_concatenation_commute 
                      list_subset_iff_projection_neutral projection_def, auto)
                  with \<tau>r2E1_t1'_in_Tr1 t1'_is_r1'_v'_s1' v'_in_E1 show ?thesis
                    by simp
                qed
              moreover
              from r2_in_E2star v'_in_E2 r1'E2_empty \<tau>E2_r2_v'_s2_in_Tr2 
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2 \<in> Tr\<^bsub>ES2\<^esub>"
                by (simp only: list_subset_iff_projection_neutral
                  projection_concatenation_commute projection_def, auto)
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(2,4,8)  v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_def)
                moreover            
                from t1'_is_r1'_v'_s1' r1'_Vv1_empty r1'_in_E1star v'_in_Vv1 propSepViews
                have "t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                proof -
                  have "r1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> =[]" 
                    using propSepViews unfolding properSeparationOfViews_def
                    by (metis  projection_on_subset2 
                      r1'_Vv1_empty r1'_in_E1star subset_iff_psubset_eq)
                  with t1'_is_r1'_v'_s1' v'_in_Vv1 Vv_is_Vv1_union_Vv2 show ?thesis                    
                    by (simp only: t1'_is_r1'_v'_s1' projection_concatenation_commute 
                      projection_def, auto)
                qed
                moreover
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>" 
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute  outerCons_prems(3) 
                    projection_intersection_neutral 
                    t1'_Vv1_is_t1_Vv1 t1'_in_E1star)
                ultimately show ?thesis
                  by auto
              qed
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(3,5,9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from t2_is_r2_v'_s2 r2_Vv_empty v'_in_Vv2 Vv_is_Vv1_union_Vv2 
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  by (simp only: t2_is_r2_v'_s2 projection_concatenation_commute projection_def, auto)
                ultimately show ?thesis
                  by auto
              qed
              moreover
              note s1'_Cv1_empty s2_Cv2_empty Cons.hyps[of ?tau s1' s2]
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto
              
              let ?t = "r2 @ r1' @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)
              note tau_t'_in_Tr
              moreover
              from r2_Vv_empty r1'_Vv_empty t'Vv_is_lambda' v'_in_Vv have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by(simp only: projection_concatenation_commute projection_def, auto)
              moreover
              from VIsViewOnE r2_Cv2_empty t'Cv_empty r1'_Cv1_empty v'_in_Vv 
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from VIsViewOnE v'_in_Vv have "[\<V>'] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def projection_def, auto)
                moreover
                from r2_in_E2star r2_Cv2_empty propSepViews 
                have "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
                  unfolding properSeparationOfViews_def  
                  using projection_on_subset2 by auto
                moreover
                from r1'_in_E1star r1'_Cv1_empty propSepViews
                have "r1' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
                  unfolding properSeparationOfViews_def 
                  using projection_on_subset2 by auto
                moreover
                note t'Cv_empty
                ultimately show ?thesis
                  by (simp only: projection_concatenation_commute, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            moreover {
              assume v'_in_Vv1_minus_E2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>"
                by auto
              with v'_in_Vv propSepViews have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>"
                unfolding properSeparationOfViews_def by auto

              from v'_in_Vv1_minus_E2 have v'_notin_E2: "\<V>' \<notin> E\<^bsub>ES2\<^esub>"
                by (auto)
              with validV2 have v'_notin_Vv2: "\<V>' \<notin> V\<^bsub>\<V>2\<^esub>"
                by (simp add: isViewOn_def V_valid_def, auto)

              (* split t1 w.r.t. v' *)
              from Cons(3) Cons(4) Cons(8) v'_in_E1 
              have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              (* properties of r1 s1 *)
              from t1_is_r1_v'_s1 Cons(10) 
              have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) 
              have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 
              have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
              proof -
                note r1_in_E1star
                moreover
                from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq  
                    Int_commute Int_empty_right disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq 
                    Int_commute Int_empty_right disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                note validV1
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def VN_disjoint_def NC_disjoint_def, auto)
              qed
              with Nv1_inter_E2_empty have r1E2_empty: "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"               
                by (metis Int_commute empty_subsetI projection_on_subset2 r1_Vv1_empty)
             
             
              (* apply inductive hypothesis to lambda' s1 t2 *)
              let ?tau = "\<tau> @ r1 @ [\<V>']"
              
              from v'_in_E1 Cons(2) r1_in_Nv1star validV1 
              have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from Cons(4) t1_is_r1_v'_s1 have "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto
              moreover
              note Cons(5)
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1 \<in> Tr\<^bsub>ES1\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(3) Cons.prems(5) 
                  projection_concatenation_commute t1_is_r1_v'_s1)
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ t2 \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  from v'_notin_E2 have "[\<V>'] \<upharpoonleft> E\<^bsub>ES2\<^esub> = []"
                    by (simp add: projection_def)
                  with Cons(7) Cons(4) t1_is_r1_v'_s1 v'_notin_E2 r1_in_Nv1star 
                    Nv1_inter_E2_empty r1E2_empty
                    show ?thesis
                      by (simp only: t1_is_r1_v'_s1 list_subset_iff_projection_neutral 
                        projection_concatenation_commute, auto)
                qed
              moreover
              from Cons(8) t1_is_r1_v'_s1 r1_Vv_empty v'_in_E1 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(9) v'_notin_E2 have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
                by (simp add: projection_def)
              moreover
              note s1_Cv1_empty Cons(11)
              moreover
              note Cons.hyps(1)[of ?tau s1 t2]
              ultimately obtain t'
                where \<tau>r1v't'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r1 @ [\<V>'] @ t'"
              
              (* conclude that ?t is a suitable choice *)
              note \<tau>r1v't'_in_Tr
              moreover
              from r1_Vv_empty t'_Vv_is_lambda' v'_in_Vv have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  using propSepViews unfolding properSeparationOfViews_def                
                  by (metis  projection_on_subset2 r1_Cv1_empty r1_in_E1star)
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            moreover {              
              assume v'_in_Vv2_minus_E1: "\<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
              hence v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>"
                by auto
              with v'_in_Vv propSepViews 
              have v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def by auto

              from v'_in_Vv2_minus_E1 
              have v'_notin_E1: "\<V>' \<notin> E\<^bsub>ES1\<^esub>"
                by (auto)
              with validV1 
              have v'_notin_Vv1: "\<V>' \<notin> V\<^bsub>\<V>1\<^esub>"
                by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              (* split t2 w.r.t. \<V>' *)
              from Cons(3) Cons(5) Cons(9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto

              (* properties of r2 s2 *)
              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
              proof -
                note r2_in_E2star
                moreover
                from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral projection_on_union)
                moreover
                from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral projection_on_union)
                moreover
                note validV2
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def  
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              qed
              
              have r2E1_in_Nv2_inter_C1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
              proof -
                have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) = set r2 \<inter> E\<^bsub>ES1\<^esub>"
                  by (simp add: projection_def, auto)
                with r2_in_Nv2star have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
                  by auto
                moreover 
                from validV1 propSepViews disjoint_Nv2_Vv1 have "E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def
                  by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def, auto)
                ultimately show ?thesis
                  by auto
              qed

              note outerCons_prems = Cons.prems

              (* repair t1 by inserting r2 \<upharpoonleft> E\<^bsub>ES1\<^esub> *)
              have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>) \<Longrightarrow> 
                \<exists> t1'. ( set t1' \<subseteq> E\<^bsub>ES1\<^esub> 
                \<and> ((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub> 
                \<and> t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> 
                \<and> t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [] )"
              proof (induct "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>" arbitrary: r2 rule: rev_induct)
                case Nil thus ?case 
                  by (metis append_self_conv outerCons_prems(9) outerCons_prems(3) 
                    outerCons_prems(5) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE1: "xs = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                proof -
                  from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  hence "set xs \<subseteq> E\<^bsub>ES1\<^esub>"
                    by auto
                  thus ?thesis
                    by (simp add: list_subset_iff_projection_neutral)
                qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                proof -
                  have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"                      
                    by (metis Int_commute snoc.prems)
                  with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by simp
                  hence "set xs \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by auto
                  with xs_is_xsE1 show ?thesis
                    by auto
                qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t1''
                  where t1''_in_E1star: "set t1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                  and \<tau>_xs_E1_t1''_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1'' \<in> Tr\<^bsub>ES1\<^esub>"
                  and t1''Vv1_is_t1Vv1: "t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and t1''Cv1_empty: "t1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by auto
                
                have x_in_Cv1_inter_Nv2: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                proof -
                  from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by simp
                  thus ?thesis
                    by auto
                qed
                hence x_in_Cv1: "x \<in> C\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E1_t1''_in_Tr1 t1''Cv1_empty
                moreover
                have Adm: "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) x)"
                proof -
                  from \<tau>_xs_E1_t1''_in_Tr1 validES1 
                  have \<tau>_xsE1_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_prefixclosed_def 
                      prefixclosed_def prefix_def)
                  with x_in_Cv1_inter_Nv2 total_ES1_Cv1_inter_Nv2 
                  have \<tau>_xsE1_x_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp only: total_def)
                  moreover
                  have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1)" ..
                  ultimately show ?thesis
                    by (simp add: Adm_def, auto)
                qed
                moreover note BSIA
                ultimately obtain t1'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  and res2: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and res3: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t1' \<subseteq> E\<^bsub>ES1\<^esub>"
                proof -
                  from res1 validES1 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1') \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  thus ?thesis
                    by auto
                qed
                moreover 
                have "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  from res1 xs_is_xsE1 have "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (xs @ [x])) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp only: projection_concatenation_commute, auto)
                  thus  ?thesis
                    by (simp only: snoc(2) projection_concatenation_commute)
                qed
                moreover
                from t1''Vv1_is_t1Vv1 res2 have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r2E1_in_Nv2_inter_C1_star] obtain t1'
                where t1'_in_E1star: "set t1' \<subseteq> E\<^bsub>ES1\<^esub>" 
                and \<tau>r2E1_t1'_in_Tr1: "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                and t1'_Vv1_is_t1_Vv1: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                and t1'_Cv1_empty: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by auto
              
              (* apply inductive hypothesis on lambda' t1' s2 *)
              let ?tau = "\<tau> @ r2 @ [\<V>']"
              
              from v'_in_E2 Cons(2) r2_in_Nv2star validV2 have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def  
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from Cons(5) t2_is_r2_v'_s2 have "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              moreover
              note t1'_in_E1star
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2 \<in> Tr\<^bsub>ES2\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(4) Cons.prems(6) 
                  projection_concatenation_commute t2_is_r2_v'_s2)
              moreover
              from \<tau>r2E1_t1'_in_Tr1 v'_notin_E1 have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(9) t2_is_r2_v'_s2 r2_Vv_empty v'_in_E2 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(10) v'_notin_E1 t1'_Vv1_is_t1_Vv1 have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
              proof -
                have "t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: projection_def, metis Int_commute 
                     projection_def projection_intersection_neutral 
                    t1'_in_E1star)
                moreover
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def         
                  by (simp add: projection_def, metis Int_commute 
                     projection_def 
                    projection_intersection_neutral Cons(4))
                moreover
                note Cons(8) v'_notin_E1 t1'_Vv1_is_t1_Vv1
                ultimately show ?thesis
                  by (simp add: projection_def)
              qed
              moreover
              note s2_Cv2_empty t1'_Cv1_empty
              moreover
              note Cons.hyps(1)[of ?tau t1' s2]
              ultimately obtain t'
                where \<tau>r2v't'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r2 @ [\<V>'] @ t'"
              
              (* conclude that ?t is a suitable choice *)
              note \<tau>r2v't'_in_Tr
              moreover
              from r2_Vv_empty t'_Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                proof -
                  from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>"
                    unfolding properSeparationOfViews_def by auto
                  from projection_on_subset[OF \<open>C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>\<close> r2_Cv2_empty] 
                  have "r2 \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = []"
                    by (simp only: Int_commute)
                  with projection_intersection_neutral[OF r2_in_E2star, of "C\<^bsub>\<V>\<^esub>"] show ?thesis
                    by simp
                qed
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            ultimately show ?thesis
              by blast
          qed 
        qed 
    }
    thus ?thesis
      by auto
qed

 (* Generalized zipping lemma for case three of lemma 6.4.4 *)
lemma generalized_zipping_lemma3: "\<lbrakk> N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}; total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>); BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub> \<rbrakk> \<Longrightarrow> 
  \<forall> \<tau> lambda t1 t2. ( ( set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> set lambda \<subseteq> V\<^bsub>\<V>\<^esub> \<and> set t1 \<subseteq> E\<^bsub>ES1\<^esub> \<and> set t2 \<subseteq> E\<^bsub>ES2\<^esub>
  \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>
  \<and> (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)
  \<and> (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [] \<and> (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []) 
  \<longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = [])) )"
proof -
  assume Nv2_inter_E1_empty: "N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"
  assume total_ES2_Cv2_inter_Nv1: "total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
  assume BSIA: "BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"

  {
    fix \<tau> lambda t1 t2
    assume \<tau>_in_Estar: "set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
      and lambda_in_Vvstar: "set lambda \<subseteq> V\<^bsub>\<V>\<^esub>"
      and t1_in_E1star: "set t1 \<subseteq> E\<^bsub>ES1\<^esub>"
      and t2_in_E2star: "set t2 \<subseteq> E\<^bsub>ES2\<^esub>"
      and \<tau>_E1_t1_in_Tr1: "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>"
      and \<tau>_E2_t2_in_Tr2: "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>"
      and lambda_E1_is_t1_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and lambda_E2_is_t2_Vv: "(lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
      and t1_no_Cv1: "(t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = []"
      and t2_no_Cv2: "(t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []"

    have "\<lbrakk> set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>;
      set lambda \<subseteq> V\<^bsub>\<V>\<^esub>; 
      set t1 \<subseteq> E\<^bsub>ES1\<^esub>;
      set t2 \<subseteq> E\<^bsub>ES2\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>;
      (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [];
      (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = [] \<rbrakk>  
      \<Longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []))"
      proof (induct lambda arbitrary: \<tau> t1 t2)
        case (Nil \<tau> t1 t2)
        
        have "(\<tau> @ []) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          proof -
            have "\<tau> \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              proof -
                from Nil(5) validES1 have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def 
                    prefixclosed_def prefix_def)
                moreover
                from Nil(6) validES2 have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def 
                    prefixclosed_def prefix_def)
                moreover 
                note Nil(1)
                ultimately show ?thesis
                  by (simp add: composeES_def)
              qed
            thus ?thesis
              by auto
          qed
        moreover
        have "([] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        moreover
        have "([] \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        ultimately show ?case
          by blast
      next
        case (Cons \<V>' lambda' \<tau> t1 t2) 
        thus ?case
          proof -
            from Cons(3) have v'_in_Vv: "\<V>' \<in> V\<^bsub>\<V>\<^esub>"
              by auto

            have "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> 
              \<or> \<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>
              \<or> \<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>" 
              using propSepViews unfolding properSeparationOfViews_def             
              by (metis Diff_iff Int_commute Int_iff Un_iff  
                 Vv_is_Vv1_union_Vv2 v'_in_Vv)
            moreover {
              assume v'_in_Vv1_inter_Vv2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub>"
              hence v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>" and v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>" 
                by auto
              with v'_in_Vv  
              have v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>" and v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>"
               using propSepViews unfolding properSeparationOfViews_def  by auto

              (* split t1 w.r.t. \<V>' *)
              from Cons(2,4,8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              (* properties of r1 s1 *)
              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 
              have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>" and s1_in_E1star: "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              from Cons(6) t1_is_r1_v'_s1 
              have \<tau>E1_r1_v'_s1_in_Tr1: "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ [\<V>'] @ s1 \<in> Tr\<^bsub>ES1\<^esub>"
                by simp

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof -
                  note r1_in_E1star
                  moreover
                  from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                      VN_disjoint_def NC_disjoint_def, auto)
                qed
              
              have r1E2_in_Nv1_inter_C2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                proof -
                  have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) = set r1 \<inter> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  with r1_in_Nv1star have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
                    by auto
                  moreover 
                  from validV2  disjoint_Nv1_Vv2 
                  have "E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> = N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp add:isViewOn_def  V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
 
              note outerCons_prems = Cons.prems

              (* repair t2 by inserting r1 \<upharpoonleft> E\<^bsub>ES2\<^esub> *)
              have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>) \<Longrightarrow> 
                \<exists> t2'. ( set t2' \<subseteq> E\<^bsub>ES2\<^esub> 
                \<and> ((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub> 
                \<and> t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
                \<and> t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [] )"
              proof (induct "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>" arbitrary: r1 rule: rev_induct)
                case Nil thus ?case     
                  by (metis append_self_conv outerCons_prems(10) outerCons_prems(4) 
                    outerCons_prems(6) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE2: "xs = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: projection_def, auto)
                    hence "set xs \<subseteq> E\<^bsub>ES2\<^esub>"
                      by auto
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                  proof -
                    have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"                      
                      by (metis Int_commute snoc.prems)
                    with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    hence "set xs \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by auto
                    with xs_is_xsE2 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t2''
                  where t2''_in_E2star: "set t2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                  and \<tau>_xs_E2_t2''_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2'' \<in> Tr\<^bsub>ES2\<^esub>"
                  and t2''Vv2_is_t2Vv2: "t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and t2''Cv2_empty: "t2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by auto
                              
                have x_in_Cv2_inter_Nv1: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    thus ?thesis
                      by auto
                  qed
                hence x_in_Cv2: "x \<in> C\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E2_t2''_in_Tr2 t2''Cv2_empty
                moreover
                have Adm: "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) x)"
                  proof -
                    from \<tau>_xs_E2_t2''_in_Tr2 validES2
                    have \<tau>_xsE2_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)
                    with x_in_Cv2_inter_Nv1 total_ES2_Cv2_inter_Nv1 
                    have \<tau>_xsE2_x_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2)" ..
                    ultimately show ?thesis
                      by (simp add: Adm_def, auto)
                  qed
                moreover note BSIA
                ultimately obtain t2'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  and res2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and res3: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t2' \<subseteq> E\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 validES2
                    have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2') \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_contain_events_def, auto)
                    thus ?thesis
                      by auto
                  qed
                moreover 
                have "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 xs_is_xsE2 have "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (xs @ [x])) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: projection_concatenation_commute, auto)
                    thus  ?thesis
                      by (simp only: snoc(2) projection_concatenation_commute)
                  qed
                moreover
                from t2''Vv2_is_t2Vv2 res2 have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r1E2_in_Nv1_inter_C2_star] obtain t2'
                where t2'_in_E2star: "set t2' \<subseteq> E\<^bsub>ES2\<^esub>" 
                and \<tau>r1E2_t2'_in_Tr2: "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                and t2'_Vv2_is_t2_Vv2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                and t2'_Cv2_empty: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by auto

              (* split t2' w.r.t. \<V>' *)
              have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                proof -
                  from projection_intersection_neutral[OF Cons(5), of "V\<^bsub>\<V>\<^esub>"] 
                  have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp only: Int_commute)
                  with Cons(9) t2'_Vv2_is_t2_Vv2 v'_in_E2 show ?thesis
                    by (simp add: projection_def)
                qed
              from projection_split_first[OF this] obtain r2' s2'
                where t2'_is_r2'_v'_s2': "t2' = r2' @ [\<V>'] @ s2'"
                and r2'_Vv2_empty: "r2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto
              
              (* properties of r2' s2' *)
              from t2'_is_r2'_v'_s2' t2'_Cv2_empty 
              have r2'_Cv2_empty: "r2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)
              
              from t2'_is_r2'_v'_s2' t2'_Cv2_empty 
              have s2'_Cv2_empty: "s2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)
              
              from t2'_in_E2star t2'_is_r2'_v'_s2' 
              have r2'_in_E2star: "set r2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              with  r2'_Vv2_empty 
              have r2'_Vv_empty: "r2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                using propSepViews unfolding properSeparationOfViews_def
                by (metis projection_on_subset2 subset_iff_psubset_eq)

              have r2'_in_Nv2star: "set r2' \<subseteq> N\<^bsub>\<V>2\<^esub>"
                proof - 
                  note r2'_in_E2star
                  moreover
                  from r2'_Vv2_empty have "set r2' \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r2'_Cv2_empty have "set r2' \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV2
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                      VN_disjoint_def NC_disjoint_def, auto)
                qed
              with Nv2_inter_E1_empty have r2'E1_empty: "r2' \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"               
                by (metis Int_commute empty_subsetI projection_on_subset2 r2'_Vv2_empty)
              
              (* apply inductive hypothesis to lambda' s1 s2' *)
              let ?tau = "\<tau> @ r1 @ r2' @ [\<V>']"
           
              from Cons(2) r1_in_E1star r2'_in_E2star v'_in_E1 
              have "set ?tau \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
                by (simp add: composeES_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              note s1_in_E1star
              moreover
              from t2'_in_E2star t2'_is_r2'_v'_s2' have "set s2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by simp
              moreover
              from r1_in_E1star v'_in_E1 r2'E1_empty \<tau>E1_r1_v'_s1_in_Tr1 
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1 \<in> Tr\<^bsub>ES1\<^esub>"
                by (simp only: list_subset_iff_projection_neutral 
                  projection_concatenation_commute projection_def, auto)
              moreover
              from \<tau>r1E2_t2'_in_Tr2 t2'_is_r2'_v'_s2' v'_in_E2 
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  from v'_in_E2 r2'_in_E2star 
                  have  "(\<tau> @ r1 @ r2' @ [\<V>']) \<upharpoonleft> E\<^bsub>ES2\<^esub> =  (\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2' @ [\<V>']"
                    by (simp only: projection_concatenation_commute 
                      list_subset_iff_projection_neutral projection_def, auto)
                  with \<tau>r1E2_t2'_in_Tr2 t2'_is_r2'_v'_s2' v'_in_E2 show ?thesis
                    by simp
                qed
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(3,4,8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from t1_is_r1_v'_s1 r1_Vv_empty v'_in_Vv1 Vv_is_Vv1_union_Vv2
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  by (simp only: t1_is_r1_v'_s1 projection_concatenation_commute projection_def, auto)
                ultimately show ?thesis
                  by auto
              qed
              moreover
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(4,5,9)  v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                moreover            
                from t2'_is_r2'_v'_s2' r2'_Vv2_empty r2'_in_E2star v'_in_Vv2 propSepViews
                have "t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                proof -
                  have "r2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> =[]"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (metis projection_on_subset2 
                      r2'_Vv2_empty r2'_in_E2star subset_iff_psubset_eq)
                  with t2'_is_r2'_v'_s2' v'_in_Vv2 Vv_is_Vv1_union_Vv2 show ?thesis                    
                    by (simp only: t2'_is_r2'_v'_s2' projection_concatenation_commute 
                      projection_def, auto)
                qed
                moreover
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute  outerCons_prems(4) 
                    projection_intersection_neutral 
                    t2'_Vv2_is_t2_Vv2 t2'_in_E2star)
                ultimately show ?thesis
                  by auto
              qed
              moreover
              note s1_Cv1_empty s2'_Cv2_empty Cons.hyps[of ?tau s1 s2']
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto
              
              let ?t = "r1 @ r2' @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)
              note tau_t'_in_Tr
              moreover
              from r1_Vv_empty r2'_Vv_empty t'Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by(simp only: projection_concatenation_commute projection_def, auto)
              moreover
              from VIsViewOnE r1_Cv1_empty t'Cv_empty r2'_Cv2_empty v'_in_Vv 
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from VIsViewOnE v'_in_Vv have "[\<V>'] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add:isViewOn_def V_valid_def VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def projection_def, auto)
                moreover
                from r1_in_E1star r1_Cv1_empty  
                have "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  using propSepViews projection_on_subset2 unfolding properSeparationOfViews_def     
                  by auto
                moreover
                from r2'_in_E2star r2'_Cv2_empty 
                have "r2' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  using propSepViews projection_on_subset2 unfolding properSeparationOfViews_def     
                  by auto
                moreover
                note t'Cv_empty
                ultimately show ?thesis
                  by (simp only: projection_concatenation_commute, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            moreover {
              assume v'_in_Vv1_minus_E2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>"
                by auto
              with v'_in_Vv  have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>"
                using propSepViews unfolding properSeparationOfViews_def
                by auto

              from v'_in_Vv1_minus_E2 have v'_notin_E2: "\<V>' \<notin> E\<^bsub>ES2\<^esub>"
                by (auto)
              with validV2 have v'_notin_Vv2: "\<V>' \<notin> V\<^bsub>\<V>2\<^esub>"
                by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                  VN_disjoint_def NC_disjoint_def, auto)

              (* split t1 w.r.t. \<V>' *)
              from Cons(3) Cons(4) Cons(8) v'_in_E1 
              have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              (* properties of r1 s1 *)
              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
              proof -
                note r1_in_E1star
                moreover
                from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq 
                    Int_commute Int_empty_right disjoint_eq_subset_Compl 
                    list_subset_iff_projection_neutral projection_on_union)
                moreover
                from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Diff_eq Int_commute Int_empty_right 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                    projection_on_union)
                moreover
                note validV1
                ultimately show ?thesis
                  by (simp add:isViewOn_def V_valid_def VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def, auto)
              qed
              
              have r1E2_in_Nv1_inter_C2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
              proof -
                have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) = set r1 \<inter> E\<^bsub>ES2\<^esub>"
                  by (simp add: projection_def, auto)
                with r1_in_Nv1star have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
                  by auto
                moreover 
                from validV2  disjoint_Nv1_Vv2 
                have "E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> = N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def, auto)
                ultimately show ?thesis
                  by auto
              qed

              note outerCons_prems = Cons.prems
              
              (* repair t2 by inserting r1\<upharpoonleft> E\<^bsub>ES2\<^esub> *)
              have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>) \<Longrightarrow> 
                \<exists> t2'. ( set t2' \<subseteq> E\<^bsub>ES2\<^esub> 
                \<and> ((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub> 
                \<and> t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
                \<and> t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [] )"
              proof (induct "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>" arbitrary: r1 rule: rev_induct)
                case Nil thus ?case 
                  by (metis append_self_conv outerCons_prems(10) outerCons_prems(4) 
                    outerCons_prems(6) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE2: "xs = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                proof -
                  from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  hence "set xs \<subseteq> E\<^bsub>ES2\<^esub>"
                    by auto
                  thus ?thesis
                    by (simp add: list_subset_iff_projection_neutral)
                qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                proof -
                  have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"                      
                    by (metis Int_commute snoc.prems)
                  with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                    by simp
                  hence "set xs \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                    by auto
                  with xs_is_xsE2 show ?thesis
                    by auto
                qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t2''
                  where t2''_in_E2star: "set t2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                  and \<tau>_xs_E2_t2''_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2'' \<in> Tr\<^bsub>ES2\<^esub>"
                  and t2''Vv2_is_t2Vv2: "t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and t2''Cv2_empty: "t2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by auto
                
                have x_in_Cv2_inter_Nv1: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                proof -
                  from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                    by simp
                  thus ?thesis
                    by auto
                qed
                hence x_in_Cv2: "x \<in> C\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E2_t2''_in_Tr2 t2''Cv2_empty
                moreover
                have Adm: "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) x)"
                proof -
                  from \<tau>_xs_E2_t2''_in_Tr2 validES2 
                  have \<tau>_xsE2_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_prefixclosed_def
                      prefixclosed_def prefix_def)
                  with x_in_Cv2_inter_Nv1 total_ES2_Cv2_inter_Nv1 
                  have \<tau>_xsE2_x_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp only: total_def)
                  moreover
                  have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2)" ..
                  ultimately show ?thesis
                    by (simp add: Adm_def, auto)
                qed
                moreover note BSIA
                ultimately obtain t2'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  and res2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and res3: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t2' \<subseteq> E\<^bsub>ES2\<^esub>"
                proof -
                  from res1 validES2 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2') \<subseteq> E\<^bsub>ES2\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  thus ?thesis
                    by auto
                qed
                moreover 
                have "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                proof -
                  from res1 xs_is_xsE2 have "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (xs @ [x])) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                    by (simp only: projection_concatenation_commute, auto)
                  thus  ?thesis
                    by (simp only: snoc(2) projection_concatenation_commute)
                qed
                moreover
                from t2''Vv2_is_t2Vv2 res2 have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r1E2_in_Nv1_inter_C2_star] obtain t2'
                where t2'_in_E2star: "set t2' \<subseteq> E\<^bsub>ES2\<^esub>" 
                and \<tau>r1E2_t2'_in_Tr2: "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                and t2'_Vv2_is_t2_Vv2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                and t2'_Cv2_empty: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by auto
              
              (* apply inductive hypothesis to lambda' s1 t2 *)
              let ?tau = "\<tau> @ r1 @ [\<V>']"
              
              from v'_in_E1 Cons(2) r1_in_Nv1star validV1 have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from Cons(4) t1_is_r1_v'_s1 have "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto
              moreover
              note t2'_in_E2star
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1 \<in> Tr\<^bsub>ES1\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(3) Cons.prems(5) 
                  projection_concatenation_commute t1_is_r1_v'_s1)
              moreover
              from \<tau>r1E2_t2'_in_Tr2 v'_notin_E2 
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(8) t1_is_r1_v'_s1 r1_Vv_empty v'_in_E1 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(11) v'_notin_E2 t2'_Vv2_is_t2_Vv2 
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
              proof -
                have "t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"  
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: projection_def, metis Int_commute 
                     projection_def projection_intersection_neutral 
                    t2'_in_E2star)
                moreover
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"          
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: projection_def, metis Int_commute 
                     projection_def 
                    projection_intersection_neutral Cons(5))
                moreover
                note Cons(9) v'_notin_E2 t2'_Vv2_is_t2_Vv2
                ultimately show ?thesis
                  by (simp add: projection_def)
              qed
              moreover
              note s1_Cv1_empty t2'_Cv2_empty
              moreover
              note Cons.hyps(1)[of ?tau s1 t2']
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r1 @ [\<V>'] @ t'"
              
              (* conclude that ?t is a suitable choice *)
              note tau_t'_in_Tr
              moreover
              from r1_Vv_empty t'_Vv_is_lambda' v'_in_Vv 
              have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                proof -
                  from propSepViews have "E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>"
                    unfolding properSeparationOfViews_def by auto
                  from projection_on_subset[OF \<open>E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>\<close> r1_Cv1_empty] 
                  have "r1 \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = []"
                    by (simp only: Int_commute)
                  with projection_intersection_neutral[OF r1_in_E1star, of "C\<^bsub>\<V>\<^esub>"] show ?thesis
                    by simp
                qed
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add:isViewOn_def V_valid_def  VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            moreover {              
              assume v'_in_Vv2_minus_E1: "\<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
              hence v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>"
                by auto
              with v'_in_Vv  have v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                using propSepViews unfolding properSeparationOfViews_def            
                by auto

              from v'_in_Vv2_minus_E1 have v'_notin_E1: "\<V>' \<notin> E\<^bsub>ES1\<^esub>"
                by (auto)
              with validV1 have v'_notin_Vv1: "\<V>' \<notin> V\<^bsub>\<V>1\<^esub>"
                by (simp add: isViewOn_def V_valid_def 
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

               (* split t2 w.r.t. \<V>' *)
              from Cons(4) Cons(5) Cons(9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto
              
              (* properties of r2 s2 *)
              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
              proof -
                note r2_in_E2star
                moreover
                from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                    projection_on_union)
                moreover
                from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                    projection_on_union)
                moreover
                note validV2
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def, auto)
              qed
              with Nv2_inter_E1_empty have r2E1_empty: "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"               
                by (metis Int_commute empty_subsetI projection_on_subset2 r2_Vv2_empty)
             
              (* apply inductive hypothesis to lambda' t1 r2 *)
              let ?tau = "\<tau> @ r2 @ [\<V>']"
              
              from v'_in_E2 Cons(2) r2_in_Nv2star validV2 have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              note Cons(4)
              moreover
              from Cons(5) t2_is_r2_v'_s2 have "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ t1 \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  from v'_notin_E1 have "[\<V>'] \<upharpoonleft> E\<^bsub>ES1\<^esub> = []"
                    by (simp add: projection_def)
                  with Cons(6) Cons(3) t2_is_r2_v'_s2 v'_notin_E1 
                    r2_in_Nv2star Nv2_inter_E1_empty r2E1_empty
                    show ?thesis
                      by (simp only: t2_is_r2_v'_s2 list_subset_iff_projection_neutral 
                        projection_concatenation_commute, auto)
                qed
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2 \<in> Tr\<^bsub>ES2\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(4) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(4) Cons.prems(6) 
                  projection_concatenation_commute t2_is_r2_v'_s2)
              moreover
              from Cons(8) v'_notin_E1 have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
                by (simp add: projection_def)
              moreover
              from Cons(9) t2_is_r2_v'_s2 r2_Vv_empty v'_in_E2 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              note Cons(10) s2_Cv2_empty
              moreover
              note Cons.hyps(1)[of ?tau t1 s2]
              ultimately obtain t'
                where tau_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r2 @ [\<V>'] @ t'"

              (* conclude that ?t is a suitable choice *)      
              note tau_t'_in_Tr
              moreover
              from r2_Vv_empty t'_Vv_is_lambda' v'_in_Vv 
                have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"  
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis  projection_on_subset2 
                    r2_Cv2_empty r2_in_E2star)
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            ultimately show ?thesis
              by blast
          qed 
        qed 
  }
  thus ?thesis
    by auto
qed

(* Generalized zipping lemma for case four of lemma 6.4.4 *)
lemma generalized_zipping_lemma4: 
"\<lbrakk>  \<nabla>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>; \<Delta>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>; \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>; \<nabla>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>; \<Delta>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>; \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>;
  BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>; BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>; total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>); total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>);
  FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>; FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>; V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub> \<union> \<nabla>\<^bsub>\<Gamma>2\<^esub>;
  C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>; C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>;
  N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}; N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<rbrakk> \<Longrightarrow>
  \<forall> \<tau> lambda t1 t2. ( ( set \<tau> \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<and> set lambda \<subseteq> V\<^bsub>\<V>\<^esub>  \<and> set t1 \<subseteq> E\<^bsub>ES1\<^esub>
  \<and> set t2 \<subseteq> E\<^bsub>ES2\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>
  \<and> (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)
  \<and> (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [] \<and> (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []) 
  \<longrightarrow> (\<exists>t. ((\<tau> @ t) \<in> (Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>) \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = [])) )"
proof -
  assume Nabla1_subsetof_E1: "\<nabla>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>" 
  and Delta1_subsetof_E1: "\<Delta>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>" 
  and Upsilon1_subsetof_E1: "\<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>"
  and Nabla2_subsetof_E2: "\<nabla>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>" 
  and Delta2_subsetof_E2: "\<Delta>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>" 
  and Upsilon2_subsetof_E2: "\<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>"
  and BSIA1: "BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>" 
  and BSIA2: "BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
  and ES1_total_Cv1_inter_Nv2: "total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)" 
  and ES2_total_Cv2_inter_Nv1: "total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
  and FCIA1: "FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub>" 
  and FCIA2: "FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
  and Vv1_inter_Vv2_subsetof_Nabla1_union_Nabla2: "V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub> \<union> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
  and Cv1_inter_Nv2_subsetof_Upsilon1: "C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>" 
  and Cv2_inter_Nv1_subsetof_Upsilon2: "C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
  and disjoint_Nv1_inter_Delta1_inter_E2: "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}" 
  and disjoint_Nv2_inter_Delta2_inter_E1: "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"
  
  {
    fix \<tau> lambda t1 t2

    have "\<lbrakk> set \<tau> \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>);
      set lambda \<subseteq> V\<^bsub>\<V>\<^esub>; 
      set t1 \<subseteq> E\<^bsub>ES1\<^esub>;
      set t2 \<subseteq> E\<^bsub>ES2\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub>;
      ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>;
      (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>);
      (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [];
      (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = [] \<rbrakk>  
      \<Longrightarrow> (\<exists> t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []))"
      proof (induct lambda arbitrary: \<tau> t1 t2)
        case (Nil \<tau> t1 t2)
        
        have "(\<tau> @ []) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
          proof -
            have "\<tau> \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              proof -
                from Nil(5) validES1 have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> \<in> Tr\<^bsub>ES1\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def
                    prefixclosed_def prefix_def)
                moreover
                from Nil(6) validES2 have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> \<in> Tr\<^bsub>ES2\<^esub>"
                  by (simp add: ES_valid_def traces_prefixclosed_def
                    prefixclosed_def prefix_def)
                moreover 
                note Nil(1)
                ultimately show ?thesis
                  by (simp add: composeES_def)
              qed
            thus ?thesis
              by auto
          qed
        moreover
        have "([] \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        moreover
        have "([] \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = []"
          by (simp add: projection_def)
        ultimately show ?case
          by blast
      next
        case (Cons \<V>' lambda' \<tau> t1 t2) 
        thus ?case
          proof -

            from Cons(3) have v'_in_Vv: "\<V>' \<in> V\<^bsub>\<V>\<^esub>"
              by auto

            have "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>1\<^esub> 
              \<or> \<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>2\<^esub>
              \<or> \<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>
              \<or> \<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
              proof -
                let ?S = "V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<union> ( V\<^bsub>\<V>1\<^esub> - V\<^bsub>\<V>2\<^esub> ) \<union> ( V\<^bsub>\<V>2\<^esub> - V\<^bsub>\<V>1\<^esub>  )"
                have "V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub> = ?S"
                  by auto
                moreover
                have "V\<^bsub>\<V>1\<^esub> - V\<^bsub>\<V>2\<^esub> = V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>" 
                  and "V\<^bsub>\<V>2\<^esub> - V\<^bsub>\<V>1\<^esub> = V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def by auto
                moreover 
                note Vv1_inter_Vv2_subsetof_Nabla1_union_Nabla2 
                  Vv_is_Vv1_union_Vv2 v'_in_Vv
                ultimately show ?thesis
                  by auto
              qed
            moreover
            { 
              assume v'_in_Vv1_inter_Vv2_inter_Nabla1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>" and v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>" 
                and v'_in_Nabla2: "\<V>' \<in> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
                by auto
              with v'_in_Vv 
              have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>" and v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                using propSepViews unfolding properSeparationOfViews_def by auto

              from Cons(3-4) Cons(8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 
              have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>" and s1_in_E1star: "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof -
                  note r1_in_E1star
                  moreover
                  from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              
              have r1E2_in_Nv1_inter_C2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                proof -
                  have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) = set r1 \<inter> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  with r1_in_Nv1star have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
                    by auto
                  moreover 
                  from validV2  disjoint_Nv1_Vv2 
                  have "E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> = N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp add: isViewOn_def V_valid_def
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              with Cv2_inter_Nv1_subsetof_Upsilon2 
              have r1E2_in_Nv1_inter_C2_Upsilon2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                by auto
 
              note outerCons_prems = Cons.prems

              have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>) \<Longrightarrow> 
                \<exists> t2'. ( set t2' \<subseteq> E\<^bsub>ES2\<^esub> 
                \<and> ((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub> 
                \<and> t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
                \<and> t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [] )"
              proof (induct "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>" arbitrary: r1 rule: rev_induct)
                case Nil thus ?case          
                  by (metis append_self_conv outerCons_prems(10) 
                    outerCons_prems(4) outerCons_prems(6) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE2: "xs = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: projection_def, auto)
                    hence "set xs \<subseteq> E\<^bsub>ES2\<^esub>"
                      by auto
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                  proof -
                    have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"                      
                      by (metis Int_commute snoc.prems)
                    with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    hence "set xs \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by auto
                    with xs_is_xsE2 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t2''
                  where t2''_in_E2star: "set t2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                  and \<tau>_xs_E2_t2''_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2'' \<in> Tr\<^bsub>ES2\<^esub>"
                  and t2''Vv2_is_t2Vv2: "t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and t2''Cv2_empty: "t2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by auto
                              
                have x_in_Cv2_inter_Nv1: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    thus ?thesis
                      by auto
                  qed
                hence x_in_Cv2: "x \<in> C\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E2_t2''_in_Tr2 t2''Cv2_empty
                moreover
                have Adm: "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) x)"
                  proof -
                    from \<tau>_xs_E2_t2''_in_Tr2 validES2 
                    have \<tau>_xsE2_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)
                    with x_in_Cv2_inter_Nv1 ES2_total_Cv2_inter_Nv1 
                    have \<tau>_xsE2_x_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2)" ..
                    ultimately show ?thesis
                      by (simp add: Adm_def, auto)
                  qed
                moreover note BSIA2
                ultimately obtain t2'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  and res2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and res3: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t2' \<subseteq> E\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 validES2 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2') \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_contain_events_def, auto)
                    thus ?thesis
                      by auto
                  qed
                moreover 
                have "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 xs_is_xsE2 have "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (xs @ [x])) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: projection_concatenation_commute, auto)
                    thus  ?thesis
                      by (simp only: snoc(2) projection_concatenation_commute)
                  qed
                moreover
                from t2''Vv2_is_t2Vv2 res2 have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r1E2_in_Nv1_inter_C2_star] obtain t2'
                where t2'_in_E2star: "set t2' \<subseteq> E\<^bsub>ES2\<^esub>" 
                and \<tau>r1E2_t2'_in_Tr2: "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                and t2'_Vv2_is_t2_Vv2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                and t2'_Cv2_empty: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by auto

              have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                proof -
                  from projection_intersection_neutral[OF Cons(5), of "V\<^bsub>\<V>\<^esub>"]  
                  have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp only: Int_commute)
                  with Cons(9) t2'_Vv2_is_t2_Vv2 v'_in_E2 show ?thesis
                    by (simp add: projection_def)
                qed
              from projection_split_first[OF this] obtain r2' s2'
                where t2'_is_r2'_v'_s2': "t2' = r2' @ [\<V>'] @ s2'"
                and r2'_Vv2_empty: "r2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto
              
              from t2'_is_r2'_v'_s2' t2'_Cv2_empty have r2'_Cv2_empty: "r2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)
              
              from t2'_is_r2'_v'_s2' t2'_Cv2_empty have s2'_Cv2_empty: "s2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)
              
              from t2'_in_E2star t2'_is_r2'_v'_s2' have r2'_in_E2star: "set r2' \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              
              have r2'_in_Nv2star: "set r2' \<subseteq> N\<^bsub>\<V>2\<^esub>"
                proof -
                  note r2'_in_E2star
                  moreover
                  from r2'_Vv2_empty have "set r2' \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r2'_Cv2_empty have "set r2' \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral
                      projection_on_union)
                  moreover
                  note validV2
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                qed
            
              have r2'E1_in_Nv2_inter_C1_star: "set (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                proof -
                  have "set (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) = set r2' \<inter> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  with r2'_in_Nv2star have "set (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
                    by auto
                  moreover 
                  from validV1  disjoint_Nv2_Vv1 
                  have "E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp add: isViewOn_def V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              with Cv1_inter_Nv2_subsetof_Upsilon1 
              have r2'E1_in_Nv2_inter_Cv1_Upsilon1_star: 
                "set (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                by auto
            

              have "set (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<Longrightarrow>
                \<exists> s1' q1'. (
                set s1' \<subseteq> E\<^bsub>ES1\<^esub> \<and> set q1' \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> 
                \<and> (\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ r1 @ q1' @ [\<V>'] @ s1' \<in> Tr\<^bsub>ES1\<^esub>
                \<and> q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>
                \<and> s1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>
                \<and> s1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [])"              
              proof (induct "r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>" arbitrary: r2' rule: rev_induct)
                case Nil

                note s1_in_E1star
                moreover
                have "set [] \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                  by auto
                moreover
                from outerCons_prems(5) t1_is_r1_v'_s1 
                have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ [] @ [\<V>'] @ s1 \<in> Tr\<^bsub>ES1\<^esub>"
                  by auto
                moreover
                from Nil have "[] \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp add: projection_def)
                moreover
                have "s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"..
                moreover
                note s1_Cv1_empty
                ultimately show ?case
                  by blast
                
              next
                case (snoc x xs)

                have xs_is_xsE1: "xs = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES1\<^esub>"
                      by (simp add: projection_def, auto)
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>"
                      by simp
                    with xs_is_xsE1 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain s1'' q1'' 
                  where s1''_in_E1star: "set s1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                  and q1''_in_C1_inter_Upsilon1_inter_Delta1: "set q1'' \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                  and \<tau>E1_r1_q1''_v'_s1''_in_Tr1: "(\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') @ [\<V>'] @ s1'' \<in> Tr\<^bsub>ES1\<^esub>"
                  and q1''C1_Upsilon1_is_xsE1: "q1'' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  and s1''V1_is_s1V1: "s1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" 
                  and s1''C1_empty: "s1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by auto
                
                have x_in_Cv1_inter_Upsilon1: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>" 
                  and x_in_Cv1_inter_Nv2: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                      by simp
                    thus "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>" 
                      and  "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                      by auto
                  qed
                with validV1 have x_in_E1: "x \<in> E\<^bsub>ES1\<^esub>"
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

                note x_in_Cv1_inter_Upsilon1
                moreover
                from v'_in_Vv1_inter_Vv2_inter_Nabla1 have "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>1\<^esub>"
                  by auto
                moreover
                note \<tau>E1_r1_q1''_v'_s1''_in_Tr1 s1''C1_empty
                moreover
                have Adm: "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> (\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') x)"
                  proof -
                    from \<tau>E1_r1_q1''_v'_s1''_in_Tr1 validES1 
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)                   
                    with x_in_Cv1_inter_Nv2 ES1_total_Cv1_inter_Nv2 
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') @ [x] \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') \<upharpoonleft> (\<rho>1 \<V>1) = (\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') \<upharpoonleft> (\<rho>1 \<V>1)" ..
                    ultimately show ?thesis
                      by (simp only: Adm_def, blast)
                  qed
                moreover 
                note FCIA1  
                ultimately
                obtain s1' \<gamma>'
                  where res1: "(set \<gamma>') \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                  and res2: "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ q1'') @ [x] @ \<gamma>' @ [\<V>'] @ s1') \<in> Tr\<^bsub>ES1\<^esub>"
                  and res3: "(s1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>) = (s1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>)"
                  and res4: "s1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  unfolding FCIA_def
                  by blast
                 
                let ?q1' = "q1'' @ [x] @ \<gamma>'"

                from res2 validES1 have "set s1' \<subseteq> E\<^bsub>ES1\<^esub>"
                  by (simp add: ES_valid_def traces_contain_events_def, auto)
                moreover
                from res1 x_in_Cv1_inter_Upsilon1 q1''_in_C1_inter_Upsilon1_inter_Delta1 
                have "set ?q1' \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>"
                  by auto
                moreover
                from res2 have "\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub> @ r1 @ ?q1' @ [\<V>'] @ s1' \<in> Tr\<^bsub>ES1\<^esub>"
                  by auto
                moreover
                have "?q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  proof -
                    from validV1 res1 have "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = []"
                      proof -
                        from res1 have "\<gamma>' = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                          by (simp only: list_subset_iff_projection_neutral)
                        hence "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                          by simp
                        hence "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                          by (simp only: projection_def, auto)
                        moreover
                        from validV1 have "N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> = {}"
                          by (simp add: isViewOn_def V_valid_def 
                            VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                        ultimately show ?thesis
                          by (simp add: projection_def)
                      qed
                    hence "?q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = (q1'' @ [x]) \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                      by (simp only: projection_concatenation_commute, auto)
                    with q1''C1_Upsilon1_is_xsE1 x_in_Cv1_inter_Upsilon1 
                    have "?q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x]"
                      by (simp only: projection_concatenation_commute projection_def, auto)
                    with xs_is_xsE1 snoc(2) show ?thesis
                      by simp
                  qed
                moreover
                from res3 s1''V1_is_s1V1 have "s1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  by simp
                moreover
                note res4
                ultimately show ?case 
                  by blast
              qed
            from this[OF r2'E1_in_Nv2_inter_Cv1_Upsilon1_star] obtain s1' q1' 
              where s1'_in_E1star: "set s1' \<subseteq> E\<^bsub>ES1\<^esub>"
              and q1'_in_Cv1_inter_Upsilon1_union_Nv1_inter_Delta1: 
              "set q1' \<subseteq> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>" 
              and \<tau>E1_r1_q1'_v'_s1'_in_Tr1: "(\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ r1 @ q1' @ [\<V>'] @ s1' \<in> Tr\<^bsub>ES1\<^esub>"
              and q1'Cv1_inter_Upsilon1_is_r2'E1: "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
              and s1'Vv1_is_s1_Vv1: "s1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
              and s1'Cv1_empty: "s1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
              by auto

            from q1'_in_Cv1_inter_Upsilon1_union_Nv1_inter_Delta1 validV1 
            have q1'_in_E1star: "set q1' \<subseteq> E\<^bsub>ES1\<^esub>"
              by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                VN_disjoint_def NC_disjoint_def, auto)
          
            have r2'Cv_empty: "r2' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              using propSepViews unfolding properSeparationOfViews_def
              by (metis  projection_on_subset2 
                r2'_Cv2_empty r2'_in_E2star)  

            (* application of merge_property' *)
            from validES1 \<tau>E1_r1_q1'_v'_s1'_in_Tr1 
            have q1'_in_E1star: "set q1' \<subseteq> E\<^bsub>ES1\<^esub>"
              by (simp add: ES_valid_def traces_contain_events_def, auto)
            moreover
            note r2'_in_E2star
            moreover
            have q1'E2_is_r2'E1: "q1' \<upharpoonleft> E\<^bsub>ES2\<^esub> = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
              proof -
                from q1'_in_Cv1_inter_Upsilon1_union_Nv1_inter_Delta1 
                have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) = q1'"
                  by (simp add: list_subset_iff_projection_neutral)
                hence "(q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)) \<upharpoonleft> E\<^bsub>ES2\<^esub> = q1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by simp
                hence "q1' \<upharpoonleft> ((C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<inter> E\<^bsub>ES2\<^esub>) = q1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp add: projection_def)
                hence "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = q1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp only: Int_Un_distrib2 disjoint_Nv1_inter_Delta1_inter_E2, auto)
                moreover
                from q1'Cv1_inter_Upsilon1_is_r2'E1 
                have "(q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)) \<upharpoonleft> E\<^bsub>ES2\<^esub> = (r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by simp
                hence "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = (r2' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp add: projection_def conj_commute)
                with r2'_in_E2star have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub>) = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp only: list_subset_iff_projection_neutral)
                ultimately show ?thesis
                  by auto
              qed  
            moreover
            have "q1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []" 
              proof -
                from q1'_in_Cv1_inter_Upsilon1_union_Nv1_inter_Delta1 
                have "q1' = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"
                  by (simp add: list_subset_iff_projection_neutral)
                moreover
                from q1'_in_E1star have "q1' = q1' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp add: list_subset_iff_projection_neutral)
                ultimately have "q1' = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by simp
                hence "q1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  by simp
                hence "q1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                  by (simp add: Int_commute projection_def)
                hence "q1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> ((C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<inter> V\<^bsub>\<V>1\<^esub>)"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: projection_def)
                hence "q1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> (V\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> V\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>)"              
                  by (simp add: Int_Un_distrib2, metis Int_assoc Int_commute Int_left_commute Un_commute)
                with validV1 show ?thesis
                  by (simp add: isViewOn_def V_valid_def  VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def, auto, simp add: projection_def)
              qed
            moreover
            have "r2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []" 
              using propSepViews unfolding properSeparationOfViews_def
              by (metis Int_commute  projection_intersection_neutral 
                r2'_Vv2_empty r2'_in_E2star)
            moreover
            have q1'Cv_empty: "q1' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from q1'_in_E1star have foo: "q1' = q1' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp add: list_subset_iff_projection_neutral)
                hence "q1' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                  by (metis Int_commute list_subset_iff_projection_neutral projection_intersection_neutral)
                moreover
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>\<subseteq>C\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                from projection_subset_elim[OF \<open>C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>\<subseteq>C\<^bsub>\<V>1\<^esub>\<close>, of q1'] 
                have "q1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES1\<^esub> = q1' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (simp add: projection_def)
                hence "q1' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> C\<^bsub>\<V>1\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = q1' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_commute)
                with foo have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = q1' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from q1'_in_Cv1_inter_Upsilon1_union_Nv1_inter_Delta1 
                have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>)"
                  by (simp add: list_subset_iff_projection_neutral)
                moreover
                have "(C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<inter> (C\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) 
                    = (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<inter> C\<^bsub>\<V>\<^esub>"
                  by fast
                hence "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) 
                     = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by (simp add: projection_sequence)
                moreover
                from validV1 
                have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<union> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>
                  = q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by (simp add: isViewOn_def V_valid_def  
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def Int_commute)
                moreover
                from q1'Cv1_inter_Upsilon1_is_r2'E1 
                have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = r2' \<upharpoonleft> E\<^bsub>ES1\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by simp
                with projection_on_intersection[OF r2'Cv_empty] 
                have "q1' \<upharpoonleft> (C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add: Int_commute projection_def)
                ultimately show ?thesis
                  by auto           
              qed
            moreover
            note r2'Cv_empty merge_property'[of q1' r2']
            ultimately obtain q'
              where q'E1_is_q1': "q' \<upharpoonleft> E\<^bsub>ES1\<^esub> = q1'"
              and q'E2_is_r2': "q' \<upharpoonleft> E\<^bsub>ES2\<^esub> = r2'"
              and q'V_empty: "q' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
              and q'C_empty: "q' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              and q'_in_E1_union_E2_star: "set q' \<subseteq> (E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>)"
              unfolding Let_def
              by auto
            
            let ?tau = "\<tau> @ r1 @ q' @ [\<V>']"
           
            from Cons(2) r1_in_E1star q'_in_E1_union_E2_star v'_in_E1 
            have "set ?tau \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
              by (simp add: composeES_def, auto)
            moreover
            from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
              by auto
            moreover
            note s1'_in_E1star
            moreover
            from t2'_in_E2star t2'_is_r2'_v'_s2' have "set s2' \<subseteq> E\<^bsub>ES2\<^esub>"
              by simp
            moreover
            from q'E1_is_q1' r1_in_E1star v'_in_E1 q1'_in_E1star \<tau>E1_r1_q1'_v'_s1'_in_Tr1 
            have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1' \<in> Tr\<^bsub>ES1\<^esub>"
              by (simp only: list_subset_iff_projection_neutral 
                projection_concatenation_commute projection_def, auto)
            moreover
            from \<tau>r1E2_t2'_in_Tr2 t2'_is_r2'_v'_s2' v'_in_E2 q'E2_is_r2' 
            have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2' \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp only: projection_concatenation_commute projection_def, auto)
            moreover
            have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(3-4) Cons(8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from t1_is_r1_v'_s1 r1_Vv_empty v'_in_Vv1 Vv_is_Vv1_union_Vv2 
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  by (simp only: t1_is_r1_v'_s1 projection_concatenation_commute 
                    projection_def, auto)
                moreover
                have "s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute  projection_intersection_neutral 
                    s1'Vv1_is_s1_Vv1 s1'_in_E1star s1_in_E1star)    
                ultimately show ?thesis
                  by auto
              qed
            moreover
            have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(3,5,9)  v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                moreover            
                from t2'_is_r2'_v'_s2' r2'_Vv2_empty r2'_in_E2star v'_in_Vv2 propSepViews
                have "t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  proof -
                    have "r2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> =[]"   
                      using propSepViews unfolding properSeparationOfViews_def
                      by (metis  projection_on_subset2 r2'_Vv2_empty 
                        r2'_in_E2star subset_iff_psubset_eq)
                    with t2'_is_r2'_v'_s2' v'_in_Vv2 Vv_is_Vv1_union_Vv2 show ?thesis                    
                      by (simp only: t2'_is_r2'_v'_s2' 
                        projection_concatenation_commute projection_def, auto)
                  qed
                moreover
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute  outerCons_prems(4) 
                    projection_intersection_neutral t2'_Vv2_is_t2_Vv2 t2'_in_E2star)
                ultimately show ?thesis
                  by auto
              qed
            moreover
            note s1'Cv1_empty s2'_Cv2_empty Cons.hyps[of ?tau s1' s2']
            ultimately obtain t'
              where \<tau>_r1_q'_v'_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              and t'Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
              and t'Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              by auto
            
            let ?t = "r1 @ q' @ [\<V>'] @ t'"

            note \<tau>_r1_q'_v'_t'_in_Tr
            moreover
            from r1_Vv_empty q'V_empty t'Vv_is_lambda' v'_in_Vv 
            have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
              by(simp only: projection_concatenation_commute projection_def, auto)
            moreover
            from VIsViewOnE r1_Cv1_empty t'Cv_empty q'C_empty v'_in_Vv 
            have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from VIsViewOnE v'_in_Vv have "[\<V>'] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                    VN_disjoint_def NC_disjoint_def projection_def, auto)
                moreover
                from r1_in_E1star r1_Cv1_empty  
                have "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"     
                  using propSepViews projection_on_subset2 
                  unfolding properSeparationOfViews_def by auto
                moreover
                note t'Cv_empty q'C_empty
                ultimately show ?thesis
                  by (simp only: projection_concatenation_commute, auto)
              qed
            ultimately have ?thesis
              by auto
          }
            moreover
            {         
              assume v'_in_Vv1_inter_Vv2_inter_Nabla2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>" and v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>" 
                and v'_in_Nabla2: "\<V>' \<in> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
                by auto
              with v'_in_Vv  propSepViews
              have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>" and v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def by auto

              from Cons(3,5,9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto

              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>" 
                and s2_in_E2star: "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
                proof -
                  note r2_in_E2star
                  moreover
                  from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV2
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def  
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              
              have r2E1_in_Nv2_inter_C1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                proof -
                  have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) = set r2 \<inter> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  with r2_in_Nv2star have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
                    by auto
                  moreover 
                  from validV1  disjoint_Nv2_Vv1 propSepViews
                  have "E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>"
                    unfolding properSeparationOfViews_def
                    by (simp add: isViewOn_def V_valid_def
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              with Cv1_inter_Nv2_subsetof_Upsilon1 
              have r2E1_in_Nv2_inter_C1_Upsilon1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                by auto
 
              note outerCons_prems = Cons.prems

              have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>) \<Longrightarrow> 
                \<exists> t1'. ( set t1' \<subseteq> E\<^bsub>ES1\<^esub> 
                \<and> ((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub> 
                \<and> t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> 
                \<and> t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [] )"
              proof (induct "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>" arbitrary: r2 rule: rev_induct)
                case Nil thus ?case     
                  by (metis append_self_conv outerCons_prems(9) outerCons_prems(3) 
                    outerCons_prems(5) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE1: "xs = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES1\<^esub>"
                      by (simp add: projection_def, auto)
                    hence "set xs \<subseteq> E\<^bsub>ES1\<^esub>"
                      by auto
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                  proof -
                    have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"                      
                      by (metis Int_commute snoc.prems)
                    with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by simp
                    hence "set xs \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by auto
                    with xs_is_xsE1 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t1''
                  where t1''_in_E1star: "set t1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                  and \<tau>_xs_E1_t1''_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1'' \<in> Tr\<^bsub>ES1\<^esub>"
                  and t1''Vv1_is_t1Vv1: "t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and t1''Cv1_empty: "t1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by auto
                              
                have x_in_Cv1_inter_Nv2: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                      by simp
                    thus ?thesis
                      by auto
                  qed
                hence x_in_Cv1: "x \<in> C\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E1_t1''_in_Tr1 t1''Cv1_empty
                moreover
                have Adm: "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) x)"
                  proof -
                    from \<tau>_xs_E1_t1''_in_Tr1 validES1
                    have \<tau>_xsE1_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)
                    with x_in_Cv1_inter_Nv2 ES1_total_Cv1_inter_Nv2 
                    have \<tau>_xsE1_x_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1)" ..
                    ultimately show ?thesis
                      by (simp add: Adm_def, auto)
                  qed
                moreover note BSIA1
                ultimately obtain t1'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  and res2: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and res3: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t1' \<subseteq> E\<^bsub>ES1\<^esub>"
                  proof -
                    from res1 validES1 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1') \<subseteq> E\<^bsub>ES1\<^esub>"
                      by (simp add: ES_valid_def traces_contain_events_def, auto)
                    thus ?thesis
                      by auto
                  qed
                moreover 
                have "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  proof -
                    from res1 xs_is_xsE1 have "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (xs @ [x])) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                      by (simp only: projection_concatenation_commute, auto)
                    thus  ?thesis
                      by (simp only: snoc(2) projection_concatenation_commute)
                  qed
                moreover
                from t1''Vv1_is_t1Vv1 res2 have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r2E1_in_Nv2_inter_C1_star] obtain t1'
                where t1'_in_E1star: "set t1' \<subseteq> E\<^bsub>ES1\<^esub>" 
                and \<tau>r2E1_t1'_in_Tr1: "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                and t1'_Vv1_is_t1_Vv1: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                and t1'_Cv1_empty: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by auto

              have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                proof -
                  from projection_intersection_neutral[OF Cons(4), of "V\<^bsub>\<V>\<^esub>"] propSepViews 
                  have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                    unfolding properSeparationOfViews_def
                    by (simp only: Int_commute)
                  with Cons(8) t1'_Vv1_is_t1_Vv1 v'_in_E1 show ?thesis
                    by (simp add: projection_def)
                qed
              from projection_split_first[OF this] obtain r1' s1'
                where t1'_is_r1'_v'_s1': "t1' = r1' @ [\<V>'] @ s1'"
                and r1'_Vv1_empty: "r1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto
              
              from t1'_is_r1'_v'_s1' t1'_Cv1_empty have r1'_Cv1_empty: "r1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)
              
              from t1'_is_r1'_v'_s1' t1'_Cv1_empty have s1'_Cv1_empty: "s1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)
              
              from t1'_in_E1star t1'_is_r1'_v'_s1' have r1'_in_E1star: "set r1' \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto
              
              have r1'_in_Nv1star: "set r1' \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof - 
                  note r1'_in_E1star
                  moreover
                  from r1'_Vv1_empty have "set r1' \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  from r1'_Cv1_empty have "set r1' \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                qed
            
              have r1'E2_in_Nv1_inter_C2_star: "set (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                proof -
                  have "set (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) = set r1' \<inter> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  with r1'_in_Nv1star have "set (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
                    by auto
                  moreover 
                  from validV2 propSepViews disjoint_Nv1_Vv2 
                  have "E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> = N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>"
                    unfolding properSeparationOfViews_def
                    by (simp add: isViewOn_def V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              with Cv2_inter_Nv1_subsetof_Upsilon2 
              have r1'E2_in_Nv1_inter_Cv2_Upsilon2_star: 
                "set (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                by auto            

              have "set (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<Longrightarrow>
                \<exists> s2' q2'. (
                set s2' \<subseteq> E\<^bsub>ES2\<^esub> \<and> set q2' \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> 
                \<and> (\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ r2 @ q2' @ [\<V>'] @ s2' \<in> Tr\<^bsub>ES2\<^esub>
                \<and> q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>
                \<and> s2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>
                \<and> s2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [])"              
              proof (induct "r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>" arbitrary: r1' rule: rev_induct)
                case Nil

                note s2_in_E2star
                moreover
                have "set [] \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                  by auto
                moreover
                from outerCons_prems(6) t2_is_r2_v'_s2 
                have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ [] @ [\<V>'] @ s2 \<in> Tr\<^bsub>ES2\<^esub>"
                  by auto
                moreover
                from Nil have "[] \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp add: projection_def)
                moreover
                have "s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"..
                moreover
                note s2_Cv2_empty
                ultimately show ?case
                  by blast
                
              next
                case (snoc x xs)

                have xs_is_xsE2: "xs = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: projection_def, auto)
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>"
                      by simp
                    with xs_is_xsE2 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain s2'' q2'' 
                  where s2''_in_E2star: "set s2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                  and q2''_in_C2_inter_Upsilon2_inter_Delta2: "set q2'' \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                  and \<tau>E2_r2_q2''_v'_s2''_in_Tr2: "(\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') @ [\<V>'] @ s2'' \<in> Tr\<^bsub>ES2\<^esub>"
                  and q2''C2_Upsilon2_is_xsE2: "q2'' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  and s2''V2_is_s2V2: "s2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" 
                  and s2''C2_empty: "s2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by auto
                
                have x_in_Cv2_inter_Upsilon2: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>" 
                  and x_in_Cv2_inter_Nv1: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                      by simp
                    thus "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>" 
                      and  "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                      by auto
                  qed
                with validV2 have x_in_E2: "x \<in> E\<^bsub>ES2\<^esub>"
                  by (simp add:isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

                note x_in_Cv2_inter_Upsilon2
                moreover
                from v'_in_Vv1_inter_Vv2_inter_Nabla2 have "\<V>' \<in> V\<^bsub>\<V>2\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>2\<^esub>"
                  by auto
                moreover
                note \<tau>E2_r2_q2''_v'_s2''_in_Tr2 s2''C2_empty
                moreover
                have Adm: "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> (\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') x)"
                  proof -
                    from \<tau>E2_r2_q2''_v'_s2''_in_Tr2 validES2
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)                   
                    with x_in_Cv2_inter_Nv1 ES2_total_Cv2_inter_Nv1 
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') @ [x] \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "(\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') \<upharpoonleft> (\<rho>2 \<V>2) = (\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') \<upharpoonleft> (\<rho>2 \<V>2)" ..
                    ultimately show ?thesis
                      by (simp only: Adm_def, blast)
                  qed
                moreover 
                note FCIA2  
                ultimately
                obtain s2' \<gamma>'
                  where res1: "(set \<gamma>') \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                  and res2: "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ q2'') @ [x] @ \<gamma>' @ [\<V>'] @ s2') \<in> Tr\<^bsub>ES2\<^esub>"
                  and res3: "(s2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>) = (s2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>)"
                  and res4: "s2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  unfolding FCIA_def
                  by blast
                 
                let ?q2' = "q2'' @ [x] @ \<gamma>'"

                from res2 validES2 have "set s2' \<subseteq> E\<^bsub>ES2\<^esub>"
                  by (simp add: ES_valid_def traces_contain_events_def, auto)
                moreover
                from res1 x_in_Cv2_inter_Upsilon2 q2''_in_C2_inter_Upsilon2_inter_Delta2 
                have "set ?q2' \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>"
                  by auto
                moreover
                from res2 have "\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub> @ r2 @ ?q2' @ [\<V>'] @ s2' \<in> Tr\<^bsub>ES2\<^esub>"
                  by auto
                moreover
                have "?q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  proof -
                    from validV2 res1 have "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = []"
                      proof -
                        from res1 have "\<gamma>' = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                          by (simp only: list_subset_iff_projection_neutral)
                        hence "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                          by simp
                        hence "\<gamma>' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = \<gamma>' \<upharpoonleft> (N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                          by (simp only: projection_def, auto)
                        moreover
                        from validV2 have "N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> = {}"
                          by (simp add:isViewOn_def V_valid_def 
                            VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                        ultimately show ?thesis
                          by (simp add: projection_def)
                      qed
                    hence "?q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = (q2'' @ [x]) \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                      by (simp only: projection_concatenation_commute, auto)
                    with q2''C2_Upsilon2_is_xsE2 x_in_Cv2_inter_Upsilon2 
                    have "?q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x]"
                      by (simp only: projection_concatenation_commute projection_def, auto)
                    with xs_is_xsE2 snoc(2) show ?thesis
                      by simp
                  qed
                moreover
                from res3 s2''V2_is_s2V2 have "s2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  by simp
                moreover
                note res4
                ultimately show ?case 
                  by blast
              qed
            from this[OF r1'E2_in_Nv1_inter_Cv2_Upsilon2_star] obtain s2' q2' 
              where s2'_in_E2star: "set s2' \<subseteq> E\<^bsub>ES2\<^esub>"
              and q2'_in_Cv2_inter_Upsilon2_union_Nv2_inter_Delta2: 
              "set q2' \<subseteq> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>" 
              and \<tau>E2_r2_q2'_v'_s2'_in_Tr2: "(\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ r2 @ q2' @ [\<V>'] @ s2' \<in> Tr\<^bsub>ES2\<^esub>"
              and q2'Cv2_inter_Upsilon2_is_r1'E2: "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
              and s2'Vv2_is_s2_Vv2: "s2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
              and s2'Cv2_empty: "s2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
              by auto

            from q2'_in_Cv2_inter_Upsilon2_union_Nv2_inter_Delta2 validV2 
            have q2'_in_E2star: "set q2' \<subseteq> E\<^bsub>ES2\<^esub>"
              by (simp add: isViewOn_def V_valid_def VC_disjoint_def 
                VN_disjoint_def NC_disjoint_def, auto)
          
            have r1'Cv_empty: "r1' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              using propSepViews unfolding properSeparationOfViews_def
              by (metis  projection_on_subset2 
                r1'_Cv1_empty r1'_in_E1star)  

            (* application of merge_property' *)
            from validES2 \<tau>E2_r2_q2'_v'_s2'_in_Tr2 
            have q2'_in_E2star: "set q2' \<subseteq> E\<^bsub>ES2\<^esub>"
              by (simp add: ES_valid_def traces_contain_events_def, auto)
            moreover
            note r1'_in_E1star
            moreover
            have q2'E1_is_r1'E2: "q2' \<upharpoonleft> E\<^bsub>ES1\<^esub> = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
              proof -
                from q2'_in_Cv2_inter_Upsilon2_union_Nv2_inter_Delta2 
                have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) = q2'"
                  by (simp add: list_subset_iff_projection_neutral)
                hence "(q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)) \<upharpoonleft> E\<^bsub>ES1\<^esub> = q2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by simp
                hence "q2' \<upharpoonleft> ((C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<inter> E\<^bsub>ES1\<^esub>) = q2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp add: projection_def)
                hence "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = q2' \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by (simp only: Int_Un_distrib2 disjoint_Nv2_inter_Delta2_inter_E1, auto)
                moreover
                from q2'Cv2_inter_Upsilon2_is_r1'E2 
                have "(q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)) \<upharpoonleft> E\<^bsub>ES1\<^esub> = (r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                  by simp
                hence "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = (r1' \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp add: projection_def conj_commute)
                with r1'_in_E1star have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub>) = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp only: list_subset_iff_projection_neutral)
                ultimately show ?thesis
                  by auto
              qed  
            moreover
            have "q2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
              proof -
                from q2'_in_Cv2_inter_Upsilon2_union_Nv2_inter_Delta2 
                have "q2' = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"
                  by (simp add: list_subset_iff_projection_neutral)
                moreover
                from q2'_in_E2star have "q2' = q2' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp add: list_subset_iff_projection_neutral)
                ultimately have "q2' = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by simp
                hence "q2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  by simp
                hence "q2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                  by (simp add: Int_commute projection_def)
                with propSepViews
                have "q2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> ((C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<inter> V\<^bsub>\<V>2\<^esub>)"
                  unfolding properSeparationOfViews_def
                  by (simp add: projection_def)
                hence "q2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> (V\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> V\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>)"              
                  by (simp add: Int_Un_distrib2, metis Int_assoc 
                    Int_commute Int_left_commute Un_commute)
                with validV2 show ?thesis
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto, simp add: projection_def)
              qed
            moreover
            have "r1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
              using propSepViews unfolding properSeparationOfViews_def
              by (metis Int_commute  projection_intersection_neutral 
                r1'_Vv1_empty r1'_in_E1star)
            moreover
            have q2'Cv_empty: "q2' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof - 
                from q2'_in_E2star have foo: "q2' = q2' \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  by (simp add: list_subset_iff_projection_neutral)
                hence "q2' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                  by (metis Int_commute list_subset_iff_projection_neutral 
                    projection_intersection_neutral)
                moreover
                from propSepViews have "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>"
                  unfolding properSeparationOfViews_def by auto
                from projection_subset_elim[OF \<open>C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>\<close>, of q2'] 
                have "q2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub> \<upharpoonleft> E\<^bsub>ES2\<^esub> = q2' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                hence "q2' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> C\<^bsub>\<V>2\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = q2' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_commute)
                with foo have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = q2' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from q2'_in_Cv2_inter_Upsilon2_union_Nv2_inter_Delta2 
                have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>)"
                  by (simp add: list_subset_iff_projection_neutral)
                moreover
                have "(C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<inter> (C\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) 
                    = (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<inter> C\<^bsub>\<V>\<^esub>"
                  by fast
                hence "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) 
                  = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by (simp add: projection_sequence)
                moreover
                from validV2 
                have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<union> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>
                  = q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def Int_commute)
                moreover
                from q2'Cv2_inter_Upsilon2_is_r1'E2 
                have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = r1' \<upharpoonleft> E\<^bsub>ES2\<^esub> \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
                  by simp
                with projection_on_intersection[OF r1'Cv_empty] have "q2' \<upharpoonleft> (C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add: Int_commute projection_def)
                ultimately show ?thesis
                  by auto           
              qed
            moreover
            note r1'Cv_empty merge_property'[of r1' q2']
            ultimately obtain q'
              where q'E2_is_q2': "q' \<upharpoonleft> E\<^bsub>ES2\<^esub> = q2'"
              and q'E1_is_r1': "q' \<upharpoonleft> E\<^bsub>ES1\<^esub> = r1'"
              and q'V_empty: "q' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
              and q'C_empty: "q' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              and q'_in_E1_union_E2_star: "set q' \<subseteq> (E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>)"
              unfolding Let_def
              by auto
            
            let ?tau = "\<tau> @ r2 @ q' @ [\<V>']"
           
            from Cons(2) r2_in_E2star q'_in_E1_union_E2_star v'_in_E2 
            have "set ?tau \<subseteq> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
              by (simp add: composeES_def, auto)
            moreover
            from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
              by auto
            moreover
            from t1'_in_E1star t1'_is_r1'_v'_s1' have "set s1' \<subseteq> E\<^bsub>ES1\<^esub>"
              by simp
            moreover
            note s2'_in_E2star
            moreover
            from \<tau>r2E1_t1'_in_Tr1 t1'_is_r1'_v'_s1' v'_in_E1 q'E1_is_r1' 
            have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1' \<in> Tr\<^bsub>ES1\<^esub>"
              by (simp only: projection_concatenation_commute projection_def, auto)
            moreover
            from q'E2_is_q2' r2_in_E2star v'_in_E2 q2'_in_E2star \<tau>E2_r2_q2'_v'_s2'_in_Tr2 
            have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2' \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp only: list_subset_iff_projection_neutral 
                projection_concatenation_commute projection_def, auto)
            moreover
            have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(2,4,8)  v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                  by (simp add: projection_def)
                moreover            
                from t1'_is_r1'_v'_s1' r1'_Vv1_empty r1'_in_E1star 
                  v'_in_Vv1 propSepViews
                have "t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  proof -
                    have "r1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> =[]"
                      using propSepViews unfolding properSeparationOfViews_def
                      by (metis  projection_on_subset2 r1'_Vv1_empty 
                        r1'_in_E1star subset_iff_psubset_eq)
                    with t1'_is_r1'_v'_s1' v'_in_Vv1 Vv_is_Vv1_union_Vv2 show ?thesis                    
                      by (simp only: t1'_is_r1'_v'_s1' projection_concatenation_commute 
                        projection_def, auto)
                  qed
                moreover
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute outerCons_prems(3) 
                    projection_intersection_neutral t1'_Vv1_is_t1_Vv1 t1'_in_E1star)
                ultimately show ?thesis
                  by auto
              qed
            moreover
            have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              proof -
                from Cons(3,5,9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                  by (simp add: projection_def)
                moreover
                from t2_is_r2_v'_s2 r2_Vv_empty v'_in_Vv2 Vv_is_Vv1_union_Vv2 
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [\<V>'] @ (s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)"
                  by (simp only: t2_is_r2_v'_s2 projection_concatenation_commute 
                    projection_def, auto)
                moreover
                have "s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = s2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>" 
                  using propSepViews unfolding properSeparationOfViews_def
                  by (metis Int_commute  projection_intersection_neutral 
                    s2'Vv2_is_s2_Vv2 s2'_in_E2star s2_in_E2star)    
                ultimately show ?thesis
                  by auto
              qed
            moreover
            note s1'_Cv1_empty s2'Cv2_empty Cons.hyps[of ?tau s1' s2']
            ultimately obtain t'
              where \<tau>_r2_q'_v'_t'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              and t'Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
              and t'Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              by auto
            
            let ?t = "r2 @ q' @ [\<V>'] @ t'"

            note \<tau>_r2_q'_v'_t'_in_Tr
            moreover
            from r2_Vv_empty q'V_empty t'Vv_is_lambda' v'_in_Vv 
            have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
              by(simp only: projection_concatenation_commute projection_def, auto)
            moreover
            from VIsViewOnE r2_Cv2_empty t'Cv_empty q'C_empty v'_in_Vv 
            have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                from VIsViewOnE v'_in_Vv have "[\<V>'] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def projection_def, auto)
                moreover
                from r2_in_E2star r2_Cv2_empty 
                have "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"     
                  using propSepViews projection_on_subset2 unfolding properSeparationOfViews_def 
                  by auto
                moreover
                note t'Cv_empty q'C_empty
                ultimately show ?thesis
                  by (simp only: projection_concatenation_commute, auto)
              qed
            ultimately have ?thesis
              by auto
            }
            moreover
            {
              assume v'_in_Vv1_minus_E2: "\<V>' \<in> V\<^bsub>\<V>1\<^esub> - E\<^bsub>ES2\<^esub>"
              hence v'_in_Vv1: "\<V>' \<in> V\<^bsub>\<V>1\<^esub>"
                by auto
              with v'_in_Vv  have v'_in_E1: "\<V>' \<in> E\<^bsub>ES1\<^esub>" 
                using propSepViews unfolding properSeparationOfViews_def
                by auto

              from v'_in_Vv1_minus_E2 have v'_notin_E2: "\<V>' \<notin> E\<^bsub>ES2\<^esub>"
                by auto
              with validV2 have v'_notin_Vv2: "\<V>' \<notin> V\<^bsub>\<V>2\<^esub>"
                by (simp add: isViewOn_def V_valid_def 
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

              from Cons(3-4) Cons(8) v'_in_E1 have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r1 s1 
                where t1_is_r1_v'_s1: "t1 = r1 @ [\<V>'] @ s1"
                and r1_Vv_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>1\<^esub>" "V\<^bsub>\<V>\<^esub>" "r1"]
              have r1_Vv1_empty: "r1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = []"
                by auto

              from t1_is_r1_v'_s1 Cons(10) have r1_Cv1_empty: "r1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t1_is_r1_v'_s1 Cons(10) have s1_Cv1_empty: "s1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(4) t1_is_r1_v'_s1 have r1_in_E1star: "set r1 \<subseteq> E\<^bsub>ES1\<^esub>"
                by auto

              have r1_in_Nv1star: "set r1 \<subseteq> N\<^bsub>\<V>1\<^esub>"
                proof -
                  note r1_in_E1star
                  moreover
                  from r1_Vv1_empty have "set r1 \<inter> V\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral
                      projection_on_union)
                  moreover
                  from r1_Cv1_empty have "set r1 \<inter> C\<^bsub>\<V>1\<^esub> = {}"
                    by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                      disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                      projection_on_union)
                  moreover
                  note validV1
                  ultimately show ?thesis
                    by (simp add: isViewOn_def V_valid_def
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                qed
              
              have r1E2_in_Nv1_inter_C2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                proof -
                  have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) = set r1 \<inter> E\<^bsub>ES2\<^esub>"
                    by (simp add: projection_def, auto)
                  with r1_in_Nv1star have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)"
                    by auto
                  moreover 
                  from validV2  disjoint_Nv1_Vv2 
                  have "E\<^bsub>ES2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> = N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>"
                    using propSepViews unfolding properSeparationOfViews_def
                    by (simp add: isViewOn_def V_valid_def 
                      VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                  ultimately show ?thesis
                    by auto
                qed
              with Cv2_inter_Nv1_subsetof_Upsilon2 
              have r1E2_in_Nv1_inter_C2_Upsilon2_star: "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>)"
                by auto

              note outerCons_prems = Cons.prems

              have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>) \<Longrightarrow> 
                \<exists> t2'. ( set t2' \<subseteq> E\<^bsub>ES2\<^esub> 
                \<and> ((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub> 
                \<and> t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> 
                \<and> t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = [] )"
              proof (induct "r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>" arbitrary: r1 rule: rev_induct)
                case Nil thus ?case          
                  by (metis append_self_conv outerCons_prems(10) outerCons_prems(4) 
                    outerCons_prems(6) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE2: "xs = xs \<upharpoonleft> E\<^bsub>ES2\<^esub>"
                  proof -
                    from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: projection_def, auto)
                    hence "set xs \<subseteq> (E\<^bsub>ES2\<^esub>)"
                      by auto
                    thus ?thesis
                      by (simp add: list_subset_iff_projection_neutral)
                  qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                  proof -
                    have "set (r1 \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"                      
                      by (metis Int_commute snoc.prems)
                    with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    hence "set xs \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by auto
                    with xs_is_xsE2 show ?thesis
                      by auto
                  qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t2''
                  where t2''_in_E2star: "set t2'' \<subseteq> E\<^bsub>ES2\<^esub>"
                  and \<tau>_xs_E2_t2''_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2'' \<in> Tr\<^bsub>ES2\<^esub>"
                  and t2''Vv2_is_t2Vv2: "t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and t2''Cv2_empty: "t2'' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by auto
                              
                have x_in_Cv2_inter_Nv1: "x \<in> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>"
                  proof -
                    from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>1\<^esub> \<inter> C\<^bsub>\<V>2\<^esub>)"
                      by simp
                    thus ?thesis
                      by auto
                  qed
                hence x_in_Cv2: "x \<in> C\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E2_t2''_in_Tr2 t2''Cv2_empty
                moreover
                have Adm: "(Adm \<V>2 \<rho>2 Tr\<^bsub>ES2\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) x)"
                  proof -
                    from \<tau>_xs_E2_t2''_in_Tr2 validES2
                    have \<tau>_xsE2_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_prefixclosed_def
                        prefixclosed_def prefix_def)
                    with x_in_Cv2_inter_Nv1 ES2_total_Cv2_inter_Nv1 
                    have \<tau>_xsE2_x_in_Tr2: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: total_def)
                    moreover
                    have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) \<upharpoonleft> (\<rho>2 \<V>2)" ..
                    ultimately show ?thesis
                      by (simp add: Adm_def, auto)
                  qed
                moreover note BSIA2
                ultimately obtain t2'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  and res2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2'' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  and res3: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t2' \<subseteq> E\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 validES2 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ [x] @ t2') \<subseteq> E\<^bsub>ES2\<^esub>"
                      by (simp add: ES_valid_def traces_contain_events_def, auto)
                    thus ?thesis
                      by auto
                  qed
                moreover 
                have "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                  proof -
                    from res1 xs_is_xsE2 have "((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ (xs @ [x])) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                      by (simp only: projection_concatenation_commute, auto)
                    thus  ?thesis
                      by (simp only: snoc(2) projection_concatenation_commute)
                  qed
                moreover
                from t2''Vv2_is_t2Vv2 res2 have "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
            from this[OF r1E2_in_Nv1_inter_C2_star] obtain t2'
              where t2'_in_E2star: "set t2' \<subseteq> E\<^bsub>ES2\<^esub>" 
                and \<tau>r1E2_t2'_in_Tr2: "((\<tau> @ r1) \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
                and t2'_Vv2_is_t2_Vv2: "t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"
                and t2'_Cv2_empty: "t2' \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
              by auto
            
            let ?tau = "\<tau> @ r1 @ [\<V>']"
            
            from v'_in_E1 Cons(2) r1_in_Nv1star validV1 have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              by (simp only: isViewOn_def composeES_def V_valid_def
                VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
            moreover
            from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
              by auto
            moreover
            from Cons(4) t1_is_r1_v'_s1 have "set s1 \<subseteq> E\<^bsub>ES1\<^esub>"
              by auto
            moreover
            note t2'_in_E2star
            moreover
            have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ s1 \<in> Tr\<^bsub>ES1\<^esub>"              
              by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                list_subset_iff_projection_neutral Cons.prems(3) Cons.prems(5) 
                projection_concatenation_commute t1_is_r1_v'_s1)
            moreover
            from \<tau>r1E2_t2'_in_Tr2 v'_notin_E2 have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ t2' \<in> Tr\<^bsub>ES2\<^esub>"
              by (simp add: projection_def)
            moreover
            from Cons(8) t1_is_r1_v'_s1 r1_Vv_empty v'_in_E1 v'_in_Vv have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = s1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
              by (simp add: projection_def)
            moreover
            from Cons(9) v'_notin_E2 t2'_Vv2_is_t2_Vv2 have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
              proof -
                have "t2' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2' \<upharpoonleft> V\<^bsub>\<V>2\<^esub>" 
                  using propSepViews unfolding properSeparationOfViews_def                 
                  by (simp add: projection_def, metis Int_commute  
                    projection_def projection_intersection_neutral t2'_in_E2star)
                moreover
                have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub>"    
                  using propSepViews unfolding properSeparationOfViews_def     
                  by (simp add: projection_def, metis Int_commute 
                    projection_def projection_intersection_neutral Cons(5))
                moreover
                note Cons(9) v'_notin_E2 t2'_Vv2_is_t2_Vv2
                ultimately show ?thesis
                  by (simp add: projection_def)
              qed
            moreover
            note s1_Cv1_empty t2'_Cv2_empty
            moreover
            note Cons.hyps(1)[of ?tau s1 t2']
            ultimately obtain t'
              where \<tau>r1v't'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
              and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
              and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              by auto

            let ?t = "r1 @ [\<V>'] @ t'"

            note \<tau>r1v't'_in_Tr
            moreover
            from r1_Vv_empty t'_Vv_is_lambda' v'_in_Vv have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
              by (simp add: projection_def)
            moreover
            have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                proof -
                  from propSepViews have "E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>" 
                    unfolding properSeparationOfViews_def by auto
                    from projection_on_subset[OF \<open>E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>\<close> r1_Cv1_empty] 
                    have "r1 \<upharpoonleft> (E\<^bsub>ES1\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = []"
                      by (simp only: Int_commute)
                    with projection_intersection_neutral[OF r1_in_E1star, of "C\<^bsub>\<V>\<^esub>"] show ?thesis
                      by simp
                  qed
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def projection_def, auto)
              qed
            ultimately have ?thesis
              by auto
            }
            moreover
            {
              assume v'_in_Vv2_minus_E1: "\<V>' \<in> V\<^bsub>\<V>2\<^esub> - E\<^bsub>ES1\<^esub>"
              hence v'_in_Vv2: "\<V>' \<in> V\<^bsub>\<V>2\<^esub>"
                by auto
              with v'_in_Vv propSepViews have v'_in_E2: "\<V>' \<in> E\<^bsub>ES2\<^esub>"
                unfolding properSeparationOfViews_def
                by auto

              from v'_in_Vv2_minus_E1 have v'_notin_E1: "\<V>' \<notin> E\<^bsub>ES1\<^esub>"
                by auto
              with validV1 have v'_notin_Vv1: "\<V>' \<notin> V\<^bsub>\<V>1\<^esub>"
                by (simp add: isViewOn_def V_valid_def
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)

              from Cons(3) Cons(5) Cons(9) v'_in_E2 have "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # (lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub>)"
                by (simp add: projection_def)
              from projection_split_first[OF this] obtain r2 s2 
                where t2_is_r2_v'_s2: "t2 = r2 @ [\<V>'] @ s2"
                and r2_Vv_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
                by auto
              with Vv_is_Vv1_union_Vv2 projection_on_subset[of "V\<^bsub>\<V>2\<^esub>" "V\<^bsub>\<V>\<^esub>" "r2"]
              have r2_Vv2_empty: "r2 \<upharpoonleft> V\<^bsub>\<V>2\<^esub> = []"
                by auto

              from t2_is_r2_v'_s2 Cons(11) have r2_Cv2_empty: "r2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp add: projection_concatenation_commute)

              from t2_is_r2_v'_s2 Cons(11) have s2_Cv2_empty: "s2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub> = []"
                by (simp only: projection_concatenation_commute, auto)

              from Cons(5) t2_is_r2_v'_s2 have r2_in_E2star: "set r2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto

              have r2_in_Nv2star: "set r2 \<subseteq> N\<^bsub>\<V>2\<^esub>"
              proof -
                note r2_in_E2star
                moreover
                from r2_Vv2_empty have "set r2 \<inter> V\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                    projection_on_union)
                moreover
                from r2_Cv2_empty have "set r2 \<inter> C\<^bsub>\<V>2\<^esub> = {}"
                  by (metis Compl_Diff_eq Diff_cancel Un_upper2 
                    disjoint_eq_subset_Compl list_subset_iff_projection_neutral 
                    projection_on_union)
                moreover
                note validV2
                ultimately show ?thesis
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              qed
              
              have r2E1_in_Nv2_inter_C1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
              proof -
                have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) = set r2 \<inter> E\<^bsub>ES1\<^esub>"
                  by (simp add: projection_def, auto)
                with r2_in_Nv2star have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>)"
                  by auto
                moreover 
                from validV1 propSepViews disjoint_Nv2_Vv1 
                have "E\<^bsub>ES1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>"
                  unfolding properSeparationOfViews_def
                  by (simp add: isViewOn_def V_valid_def 
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
                ultimately show ?thesis
                  by auto
              qed
              with Cv1_inter_Nv2_subsetof_Upsilon1 
              have r2E1_in_Nv2_inter_C1_Upsilon1_star: "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>1\<^esub>)"
                by auto

              note outerCons_prems = Cons.prems

              have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>) \<Longrightarrow> 
                \<exists> t1'. ( set t1' \<subseteq> E\<^bsub>ES1\<^esub> 
                \<and> ((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub> 
                \<and> t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub> 
                \<and> t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = [] )"
              proof (induct "r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>" arbitrary: r2 rule: rev_induct)
                case Nil thus ?case 
                  by (metis append_self_conv outerCons_prems(9) outerCons_prems(3) 
                    outerCons_prems(5) projection_concatenation_commute)
              next
                case (snoc x xs)

                have xs_is_xsE1: "xs = xs \<upharpoonleft> E\<^bsub>ES1\<^esub>"
                proof -
                  from snoc(2) have "set (xs @ [x]) \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: projection_def, auto)
                  hence "set xs \<subseteq> E\<^bsub>ES1\<^esub>"
                    by auto
                  thus ?thesis
                    by (simp add: list_subset_iff_projection_neutral)
                qed
                moreover
                have "set (xs \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                proof -
                  have "set (r2 \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"                      
                    by (metis Int_commute snoc.prems)
                  with snoc(2) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by simp
                  hence "set xs \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by auto
                  with xs_is_xsE1 show ?thesis
                    by auto
                qed
                moreover
                note snoc.hyps(1)[of xs]
                ultimately obtain t1''
                  where t1''_in_E1star: "set t1'' \<subseteq> E\<^bsub>ES1\<^esub>"
                  and \<tau>_xs_E1_t1''_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1'' \<in> Tr\<^bsub>ES1\<^esub>"
                  and t1''Vv1_is_t1Vv1: "t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and t1''Cv1_empty: "t1'' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by auto
                
                have x_in_Cv1_inter_Nv2: "x \<in> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>"
                proof -
                  from snoc(2-3) have "set (xs @ [x]) \<subseteq> (N\<^bsub>\<V>2\<^esub> \<inter> C\<^bsub>\<V>1\<^esub>)"
                    by simp
                  thus ?thesis
                    by auto
                qed
                hence x_in_Cv1: "x \<in> C\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note \<tau>_xs_E1_t1''_in_Tr1 t1''Cv1_empty
                moreover
                have Adm: "(Adm \<V>1 \<rho>1 Tr\<^bsub>ES1\<^esub> ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) x)"
                proof -
                  from \<tau>_xs_E1_t1''_in_Tr1 validES1
                  have \<tau>_xsE1_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_prefixclosed_def
                      prefixclosed_def prefix_def)
                  with x_in_Cv1_inter_Nv2 ES1_total_Cv1_inter_Nv2 
                  have \<tau>_xsE1_x_in_Tr1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp only: total_def)
                  moreover
                  have "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1) = ((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) \<upharpoonleft> (\<rho>1 \<V>1)" ..
                  ultimately show ?thesis
                    by (simp add: Adm_def, auto)
                qed
                moreover note BSIA1
                ultimately obtain t1'
                  where res1: "((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                  and res2: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1'' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  and res3: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                  by (simp only: BSIA_def, blast)

                have "set t1' \<subseteq> E\<^bsub>ES1\<^esub>"
                proof -
                  from res1 validES1 have "set (((\<tau> @ xs) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ [x] @ t1') \<subseteq> E\<^bsub>ES1\<^esub>"
                    by (simp add: ES_valid_def traces_contain_events_def, auto)
                  thus ?thesis
                    by auto
                qed
                moreover 
                have "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                proof -
                  from res1 xs_is_xsE1 have "((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ (xs @ [x])) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                    by (simp only: projection_concatenation_commute, auto)
                  thus  ?thesis
                    by (simp only: snoc(2) projection_concatenation_commute)
                qed
                moreover
                from t1''Vv1_is_t1Vv1 res2 have "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                  by auto
                moreover
                note res3
                ultimately show ?case
                  by auto
              qed
              from this[OF r2E1_in_Nv2_inter_C1_star] obtain t1'
                where t1'_in_E1star: "set t1' \<subseteq> E\<^bsub>ES1\<^esub>" 
                and \<tau>r2E1_t1'_in_Tr1: "((\<tau> @ r2) \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                and t1'_Vv1_is_t1_Vv1: "t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>"
                and t1'_Cv1_empty: "t1' \<upharpoonleft> C\<^bsub>\<V>1\<^esub> = []"
                by auto
              
              let ?tau = "\<tau> @ r2 @ [\<V>']"
              
              from v'_in_E2 Cons(2) r2_in_Nv2star validV2 have "set ?tau \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                by (simp only: composeES_def isViewOn_def V_valid_def 
                  VC_disjoint_def VN_disjoint_def NC_disjoint_def, auto)
              moreover
              from Cons(3) have "set lambda' \<subseteq> V\<^bsub>\<V>\<^esub>"
                by auto
              moreover
              from Cons(5) t2_is_r2_v'_s2 have "set s2 \<subseteq> E\<^bsub>ES2\<^esub>"
                by auto
              moreover
              note t1'_in_E1star
              moreover
              have "?tau \<upharpoonleft> E\<^bsub>ES2\<^esub> @ s2 \<in> Tr\<^bsub>ES2\<^esub>"              
                by (metis Cons_eq_appendI append_eq_appendI calculation(3) eq_Nil_appendI 
                  list_subset_iff_projection_neutral Cons.prems(4) Cons.prems(6) 
                  projection_concatenation_commute t2_is_r2_v'_s2)
              moreover
              from \<tau>r2E1_t1'_in_Tr1 v'_notin_E1 have "?tau \<upharpoonleft> E\<^bsub>ES1\<^esub> @ t1' \<in> Tr\<^bsub>ES1\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(9) t2_is_r2_v'_s2 r2_Vv_empty v'_in_E2 v'_in_Vv 
              have "lambda' \<upharpoonleft> E\<^bsub>ES2\<^esub> = s2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
                by (simp add: projection_def)
              moreover
              from Cons(10) v'_notin_E1 t1'_Vv1_is_t1_Vv1 
              have "lambda' \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub>"         
              proof -
                have "t1' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1' \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" 
                  using propSepViews unfolding properSeparationOfViews_def  
                  by (simp add: projection_def, metis Int_commute 
                    projection_def projection_intersection_neutral t1'_in_E1star)
                moreover
                have "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = t1 \<upharpoonleft> V\<^bsub>\<V>1\<^esub>" 
                  using propSepViews unfolding properSeparationOfViews_def           
                  by (simp add: projection_def, metis Int_commute  
                    projection_def projection_intersection_neutral Cons(4))
                moreover
                note Cons(8) v'_notin_E1 t1'_Vv1_is_t1_Vv1
                ultimately show ?thesis
                  by (simp add: projection_def)
              qed
              moreover
              note s2_Cv2_empty t1'_Cv1_empty
              moreover
              note Cons.hyps(1)[of ?tau t1' s2]
              ultimately obtain t'
                where \<tau>r2v't'_in_Tr: "?tau @ t' \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub>"
                and t'_Vv_is_lambda': "t' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = lambda'"
                and t'_Cv_empty: "t' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                by auto

              let ?t = "r2 @ [\<V>'] @ t'"

              note \<tau>r2v't'_in_Tr
              moreover
              from r2_Vv_empty t'_Vv_is_lambda' v'_in_Vv have "?t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<V>' # lambda'"
                by (simp add: projection_def)
              moreover
              have "?t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
              proof -
                have "r2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
                proof -
                  from propSepViews have "E\<^bsub>ES2\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>" 
                    unfolding properSeparationOfViews_def by auto
                  from projection_on_subset[OF \<open>E\<^bsub>ES2\<^esub> \<inter> C\<^bsub>\<V>\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>\<close> r2_Cv2_empty] 
                  have "r2 \<upharpoonleft> (E\<^bsub>ES2\<^esub> \<inter> C\<^bsub>\<V>\<^esub>) = []"
                    by (simp only: Int_commute)
                  with projection_intersection_neutral[OF r2_in_E2star, of "C\<^bsub>\<V>\<^esub>"] show ?thesis
                    by simp
                qed
                with v'_in_Vv VIsViewOnE t'_Cv_empty show ?thesis
                  by (simp add: isViewOn_def V_valid_def
                    VC_disjoint_def VN_disjoint_def NC_disjoint_def projection_def, auto)
              qed
              ultimately have ?thesis
                by auto
            }
            ultimately show ?thesis
              by blast
        qed
        
      qed 
  }
  thus ?thesis
    by auto
qed

(* The generalized zipping lemma (Lemma 6.4.4) *)
lemma generalized_zipping_lemma: 
 "\<forall> \<tau> lambda t1 t2. ( ( set \<tau> \<subseteq> E\<^bsub>(ES1 \<parallel> ES2)\<^esub>
  \<and> set lambda \<subseteq> V\<^bsub>\<V>\<^esub> \<and> set t1 \<subseteq> E\<^bsub>ES1\<^esub> \<and> set t2 \<subseteq> E\<^bsub>ES2\<^esub>
  \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES1\<^esub>) @ t1) \<in> Tr\<^bsub>ES1\<^esub> \<and> ((\<tau> \<upharpoonleft> E\<^bsub>ES2\<^esub>) @ t2) \<in> Tr\<^bsub>ES2\<^esub>
  \<and> (lambda \<upharpoonleft> E\<^bsub>ES1\<^esub>) = (t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub>) \<and> (lambda \<upharpoonleft> E\<^bsub>ES2\<^esub>) = (t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub>)
  \<and> (t1 \<upharpoonleft> C\<^bsub>\<V>1\<^esub>) = [] \<and> (t2 \<upharpoonleft> C\<^bsub>\<V>2\<^esub>) = []) 
  \<longrightarrow> (\<exists>t. ((\<tau> @ t) \<in> Tr\<^bsub>(ES1 \<parallel> ES2)\<^esub> \<and> (t \<upharpoonleft> V\<^bsub>\<V>\<^esub>) = lambda \<and> (t \<upharpoonleft> C\<^bsub>\<V>\<^esub>) = [])) )"
proof -
  note well_behaved_composition
  moreover {
    assume "N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"
    with generalized_zipping_lemma1 have ?thesis
      by auto
  }
  moreover {
    assume "\<exists> \<rho>1. N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
    then obtain \<rho>1 where "N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub>"
        by auto
    with generalized_zipping_lemma2[of \<rho>1] have ?thesis
      by auto
  }
  moreover {
    assume "\<exists> \<rho>2. N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>) \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
    then obtain \<rho>2 where "N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>) \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>"
      by auto
    with generalized_zipping_lemma3[of \<rho>2] have ?thesis
      by auto
  }
  moreover {
    assume "\<exists> \<rho>1 \<rho>2 \<Gamma>1 \<Gamma>2. ( \<nabla>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>
      \<and> \<nabla>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>
      \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)
      \<and> FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub> \<union> \<nabla>\<^bsub>\<Gamma>2\<^esub>
      \<and> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<and> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>
      \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} )"
    then obtain \<rho>1 \<rho>2 \<Gamma>1 \<Gamma>2 where "\<nabla>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>
      \<and> \<nabla>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>
      \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)
      \<and> FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub> \<union> \<nabla>\<^bsub>\<Gamma>2\<^esub>
      \<and> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<and> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>
      \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}"
      by auto
    with generalized_zipping_lemma4[of \<Gamma>1 \<Gamma>2 \<rho>1 \<rho>2]  have ?thesis
      by auto
  }
  ultimately show ?thesis unfolding wellBehavedComposition_def
    by blast
qed

end

end
