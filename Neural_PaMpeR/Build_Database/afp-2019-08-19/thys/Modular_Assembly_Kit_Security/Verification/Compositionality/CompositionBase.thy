theory CompositionBase
imports "../Basics/BSPTaxonomy"
begin

definition 
properSeparationOfViews :: 
"'e ES_rec \<Rightarrow> 'e ES_rec \<Rightarrow> 'e V_rec \<Rightarrow> 'e V_rec \<Rightarrow> 'e V_rec \<Rightarrow> bool"
where
"properSeparationOfViews ES1 ES2 \<V> \<V>1 \<V>2 \<equiv>
   V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> = V\<^bsub>\<V>1\<^esub>
   \<and> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>\<V>2\<^esub>
   \<and> C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<subseteq> C\<^bsub>\<V>1\<^esub>
   \<and> C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<subseteq> C\<^bsub>\<V>2\<^esub>
   \<and> N\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> = {}"

definition
wellBehavedComposition :: 
"'e ES_rec \<Rightarrow> 'e ES_rec \<Rightarrow> 'e V_rec \<Rightarrow> 'e V_rec \<Rightarrow> 'e V_rec \<Rightarrow> bool"
where
"wellBehavedComposition ES1 ES2 \<V> \<V>1 \<V>2 \<equiv>
( N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} )
  \<or> (\<exists>\<rho>1. ( N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) 
            \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub> ))
  \<or> (\<exists>\<rho>2. ( N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>) 
            \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub> ))
  \<or> (\<exists>\<rho>1 \<rho>2 \<Gamma>1 \<Gamma>2. ( 
      \<nabla>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>
      \<and> \<nabla>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub> \<and> \<Upsilon>\<^bsub>\<Gamma>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>
      \<and> BSIA \<rho>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> BSIA \<rho>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> total ES1 (C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub>) \<and> total ES2 (C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub>)
      \<and> FCIA \<rho>1 \<Gamma>1 \<V>1 Tr\<^bsub>ES1\<^esub> \<and> FCIA \<rho>2 \<Gamma>2 \<V>2 Tr\<^bsub>ES2\<^esub>
      \<and> V\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> \<subseteq> \<nabla>\<^bsub>\<Gamma>1\<^esub> \<union> \<nabla>\<^bsub>\<Gamma>2\<^esub>
      \<and> C\<^bsub>\<V>1\<^esub> \<inter> N\<^bsub>\<V>2\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>1\<^esub> \<and> C\<^bsub>\<V>2\<^esub> \<inter> N\<^bsub>\<V>1\<^esub> \<subseteq> \<Upsilon>\<^bsub>\<Gamma>2\<^esub>
      \<and> N\<^bsub>\<V>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>1\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {} \<and> N\<^bsub>\<V>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>2\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {} ))"

locale Compositionality =
fixes ES1 :: "'e ES_rec"
and ES2 :: "'e ES_rec"
and \<V> :: "'e V_rec" (* view of the composed system *)
and \<V>1 :: "'e V_rec" (* view for component ES1 *)
and \<V>2 :: "'e V_rec" (* view for component ES2 *)

(* assumptions about the event systems *)
assumes validES1: "ES_valid ES1"
and validES2: "ES_valid ES2"
and composableES1ES2: "composable ES1 ES2"

(* basic assumptions about the views *)
and validVC: "isViewOn \<V> (E\<^bsub>(ES1 \<parallel> ES2)\<^esub>)"
and validV1: "isViewOn \<V>1 E\<^bsub>ES1\<^esub>"
and validV2: "isViewOn \<V>2 E\<^bsub>ES2\<^esub>"


(* the following assumptions constitute proper separation of views 
  (Def. 6.3.2 in Heiko Mantel's dissertation) *)
and propSepViews: "properSeparationOfViews ES1 ES2 \<V> \<V>1 \<V>2" 

(* the following assumptions constitute well behaved composition (Def. 6.3.6 in Mantel's dissertation) *)
and well_behaved_composition: "wellBehavedComposition ES1 ES2 \<V> \<V>1 \<V>2"



(* sublocale relations for Compositionality *)
sublocale Compositionality \<subseteq> BSPTaxonomyDifferentCorrections "ES1 \<parallel> ES2" "\<V>"
  by (unfold_locales, rule composeES_yields_ES, rule validES1,
    rule validES2, rule validVC)


(* body of Compositionality *)
context Compositionality
begin


(* proper separation of views implies the following equality *)
lemma Vv_is_Vv1_union_Vv2: "V\<^bsub>\<V>\<^esub> = V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>"
proof -
  from propSepViews have "V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<union> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> = V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>"
    unfolding properSeparationOfViews_def by auto
  hence "V\<^bsub>\<V>\<^esub> \<inter> (E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>) = V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>"
    by auto
  hence "V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>(ES1 \<parallel> ES2)\<^esub> = V\<^bsub>\<V>1\<^esub> \<union> V\<^bsub>\<V>2\<^esub>"
    by (simp add: composeES_def)
  with validVC show ?thesis
    by (simp add: isViewOn_def, auto)
qed

lemma disjoint_Nv1_Vv2: "N\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> = {}"
proof -
  from validV1 have "N\<^bsub>\<V>1\<^esub> \<subseteq> E\<^bsub>ES1\<^esub>"
    by (simp add: isViewOn_def, auto)
  with propSepViews have "N\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> = (N\<^bsub>\<V>1\<^esub> \<inter> E\<^bsub>ES1\<^esub> \<inter> V\<^bsub>\<V>\<^esub>) \<inter> E\<^bsub>ES2\<^esub>"
    unfolding properSeparationOfViews_def by auto
  hence "N\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>2\<^esub> = (N\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub>) \<inter> E\<^bsub>ES2\<^esub>"
    by auto
  moreover
  from validV1 have "N\<^bsub>\<V>1\<^esub> \<inter> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES1\<^esub> = {}" 
    using propSepViews unfolding properSeparationOfViews_def
    by (metis VN_disjoint_def V_valid_def inf_assoc inf_commute isViewOn_def)
  ultimately show ?thesis
    by auto      
qed

lemma disjoint_Nv2_Vv1: "N\<^bsub>\<V>2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> = {}"
proof -
  from validV2 have "N\<^bsub>\<V>2\<^esub> \<subseteq> E\<^bsub>ES2\<^esub>"
    by (simp add:isViewOn_def, auto)
  with propSepViews have "N\<^bsub>\<V>2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> = (N\<^bsub>\<V>2\<^esub> \<inter> E\<^bsub>ES2\<^esub> \<inter> V\<^bsub>\<V>\<^esub>) \<inter> E\<^bsub>ES1\<^esub>"
    unfolding properSeparationOfViews_def by auto
  hence "N\<^bsub>\<V>2\<^esub> \<inter> V\<^bsub>\<V>1\<^esub> = (N\<^bsub>\<V>2\<^esub> \<inter> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub>) \<inter> E\<^bsub>ES1\<^esub>"
    by auto
  moreover
  from validV2 have "N\<^bsub>\<V>2\<^esub> \<inter> V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ES2\<^esub> = {}"
    using propSepViews unfolding properSeparationOfViews_def 
    by (metis VN_disjoint_def V_valid_def inf_assoc inf_commute isViewOn_def)
  ultimately show ?thesis
    by auto      
qed

(* An extended variant of the merge_property.
 Useful for the proof of the generalized zipping lemma. *)
lemma merge_property': " \<lbrakk> set t1 \<subseteq> E\<^bsub>ES1\<^esub>; set t2 \<subseteq> E\<^bsub>ES2\<^esub>; 
  t1 \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2 \<upharpoonleft> E\<^bsub>ES1\<^esub>; t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []; t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []; 
  t1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []; t2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<rbrakk> 
\<Longrightarrow> \<exists> t. (t \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1 \<and> t \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2 \<and> t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = [] \<and> t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> set t \<subseteq> (E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>))"
proof -
  assume t1_in_E1star: "set t1 \<subseteq> E\<^bsub>ES1\<^esub>"
  and t2_in_E2star: "set t2 \<subseteq> E\<^bsub>ES2\<^esub>"
  and t1_t2_synchronized: "t1 \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2 \<upharpoonleft> E\<^bsub>ES1\<^esub>"
  and t1Vv_empty: "t1 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
  and t2Vv_empty: "t2 \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []"
  and t1Cv_empty: "t1 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
  and t2Cv_empty: "t2 \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"

  from merge_property[OF t1_in_E1star t2_in_E2star t1_t2_synchronized] obtain t
    where t_is_interleaving: "t \<upharpoonleft> E\<^bsub>ES1\<^esub> = t1 \<and> t \<upharpoonleft> E\<^bsub>ES2\<^esub> = t2"
    and t_contains_only_events_from_t1_t2: "set t \<subseteq> set t1 \<union> set t2"
    unfolding Let_def
    by auto
  moreover
  from t1Vv_empty t2Vv_empty t_contains_only_events_from_t1_t2
  have "t \<upharpoonleft> V\<^bsub>\<V>\<^esub> = []" 
    using propSepViews unfolding properSeparationOfViews_def
    by (metis Int_commute Vv_is_Vv1_union_Vv2 projection_on_union projection_sequence t_is_interleaving)
  moreover
  have "t \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    proof -
      from t1Cv_empty have "\<forall>c \<in> C\<^bsub>\<V>\<^esub>. c \<notin> set t1"
        by (simp add: projection_def filter_empty_conv, fast)
      moreover
      from t2Cv_empty have "\<forall>c \<in> C\<^bsub>\<V>\<^esub>. c \<notin> set t2"
        by (simp add: projection_def filter_empty_conv, fast)
      ultimately have
      "\<forall>c \<in> C\<^bsub>\<V>\<^esub>. c \<notin> (set t1 \<union> set t2)"
        by auto
      with t_contains_only_events_from_t1_t2 have "\<forall>c \<in> C\<^bsub>\<V>\<^esub>. c \<notin> set t"
        by auto
      thus ?thesis
        by (simp add: projection_def, metis filter_empty_conv)
    qed
  moreover
  from t1_in_E1star t2_in_E2star t_contains_only_events_from_t1_t2 
  have "set t \<subseteq> (E\<^bsub>ES1\<^esub> \<union> E\<^bsub>ES2\<^esub>)"
    by auto
  ultimately show ?thesis
    by blast
qed

lemma Nv1_union_Nv2_subsetof_Nv: "N\<^bsub>\<V>1\<^esub> \<union> N\<^bsub>\<V>2\<^esub> \<subseteq> N\<^bsub>\<V>\<^esub>"
proof -
  {
    fix e
    assume e_in_N1: "e \<in> N\<^bsub>\<V>1\<^esub>"
    with validV1 have 
      e_in_E1: "e \<in> E\<^bsub>ES1\<^esub>"
      and e_notin_V1: "e \<notin> V\<^bsub>\<V>1\<^esub>"
      and e_notin_C1: "e \<notin> C\<^bsub>\<V>1\<^esub>"
      by (simp only: isViewOn_def V_valid_def VC_disjoint_def NC_disjoint_def
        VN_disjoint_def, auto)+
    
    from e_in_E1 e_notin_V1 propSepViews have "e \<notin> V\<^bsub>\<V>\<^esub>"
     unfolding properSeparationOfViews_def by auto
    moreover
    from e_in_E1 e_notin_C1 propSepViews have "e \<notin> C\<^bsub>\<V>\<^esub>"
     unfolding properSeparationOfViews_def by auto
    moreover
    note e_in_E1 validVC
    ultimately have "e \<in> N\<^bsub>\<V>\<^esub>"
      by (simp add: isViewOn_def V_valid_def VC_disjoint_def NC_disjoint_def VN_disjoint_def
         composeES_def, auto)
  }
  moreover {
    fix e
    assume e_in_N2: "e \<in> N\<^bsub>\<V>2\<^esub>"
    with validV2 have 
      e_in_E2: "e \<in> E_ES ES2"
      and e_notin_V2: "e \<notin> V\<^bsub>\<V>2\<^esub>"
      and e_notin_C2: "e \<notin> C\<^bsub>\<V>2\<^esub>"
      by (simp only: isViewOn_def V_valid_def VC_disjoint_def NC_disjoint_def VN_disjoint_def
        , auto)+
    
    from e_in_E2 e_notin_V2 propSepViews have "e \<notin> V\<^bsub>\<V>\<^esub>"
     unfolding properSeparationOfViews_def by auto
    moreover
    from e_in_E2 e_notin_C2 propSepViews have "e \<notin> C\<^bsub>\<V>\<^esub>"
     unfolding properSeparationOfViews_def by auto
    moreover
    note e_in_E2 validVC
    ultimately have "e \<in> N\<^bsub>\<V>\<^esub>"
      by (simp add: isViewOn_def V_valid_def VC_disjoint_def VN_disjoint_def NC_disjoint_def
         composeES_def, auto)
  }
  ultimately show ?thesis
    by auto
qed

end

end
