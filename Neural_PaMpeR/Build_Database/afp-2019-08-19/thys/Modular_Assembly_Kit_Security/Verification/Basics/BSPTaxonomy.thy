theory BSPTaxonomy
imports "../../SystemSpecification/EventSystems"
  "../../SecuritySpecification/BasicSecurityPredicates"
begin

locale BSPTaxonomyDifferentCorrections =
fixes ES :: "'e ES_rec"
and \<V> :: "'e V_rec"

assumes validES: "ES_valid ES"
and VIsViewOnE: "isViewOn \<V> E\<^bsub>ES\<^esub>"

locale BSPTaxonomyDifferentViews =
fixes ES :: "'e ES_rec"
and \<V>\<^sub>1 :: "'e V_rec"
and \<V>\<^sub>2 :: "'e V_rec"

assumes validES: "ES_valid ES"
and \<V>\<^sub>1IsViewOnE: "isViewOn \<V>\<^sub>1 E\<^bsub>ES\<^esub>" 
and \<V>\<^sub>2IsViewOnE: "isViewOn \<V>\<^sub>2 E\<^bsub>ES\<^esub>"

locale BSPTaxonomyDifferentViewsFirstDim= BSPTaxonomyDifferentViews +
assumes V2_subset_V1: "V\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> V\<^bsub>\<V>\<^sub>1\<^esub>"  
and     N2_supset_N1: "N\<^bsub>\<V>\<^sub>2\<^esub> \<supseteq> N\<^bsub>\<V>\<^sub>1\<^esub>"
and     C2_subset_C1: "C\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> C\<^bsub>\<V>\<^sub>1\<^esub>"

sublocale  BSPTaxonomyDifferentViewsFirstDim \<subseteq> BSPTaxonomyDifferentViews
by (unfold_locales)

locale BSPTaxonomyDifferentViewsSecondDim= BSPTaxonomyDifferentViews +
assumes V2_subset_V1: "V\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> V\<^bsub>\<V>\<^sub>1\<^esub>"  
and     N2_supset_N1: "N\<^bsub>\<V>\<^sub>2\<^esub> \<supseteq> N\<^bsub>\<V>\<^sub>1\<^esub>"
and     C2_equals_C1: "C\<^bsub>\<V>\<^sub>2\<^esub> = C\<^bsub>\<V>\<^sub>1\<^esub>"

sublocale  BSPTaxonomyDifferentViewsSecondDim \<subseteq> BSPTaxonomyDifferentViews
by (unfold_locales)

(* body of BSPTaxonomy *)
context BSPTaxonomyDifferentCorrections
begin

(*lemma taken from lemma 3.5.1 from Heiko Mantel's dissertation*)
lemma SR_implies_R: 
"SR \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> R \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume SR: "SR \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<tau>
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    with SR  have "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>" 
      unfolding SR_def by auto 
    hence "\<exists> \<tau>'. \<tau>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    proof -
      assume tau_V_N_is_trace: "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>"
      show "\<exists> \<tau>'. \<tau>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      proof
        let  ?\<tau>'= "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
        have "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>" 
          by (simp add: projection_subset_elim) 
        moreover
        from  VIsViewOnE have "VC_disjoint \<V> \<and> NC_disjoint \<V>" 
          unfolding isViewOn_def V_valid_def
          by auto
        then have "(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<inter> C\<^bsub>\<V>\<^esub> = {}" 
          by (simp add: NC_disjoint_def VC_disjoint_def inf_sup_distrib2) 
        then have "?\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
          by (simp add: disjoint_projection)
        ultimately
        show "?\<tau>' \<in> Tr\<^bsub>ES\<^esub> \<and> ?\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> ?\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
          using  tau_V_N_is_trace  by auto 
      qed  
    qed
  }
  thus ?thesis
    unfolding SR_def R_def by auto
qed

(* lemma taken from lemma 3.5.1 from Heiko Mantel's dissertation *)
lemma SD_implies_BSD :
"(SD \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> BSD \<V> Tr\<^bsub>ES\<^esub> "
proof -
  assume SD:  "SD \<V> Tr\<^bsub>ES\<^esub>"
  { 
    fix \<alpha> \<beta> c 
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and  "\<beta> @ c # \<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      and  alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
    with SD have "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      unfolding SD_def by auto
    hence "\<exists>\<alpha>'. \<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      using alpha_C_empty  
      by auto
   }
   thus ?thesis
     unfolding SD_def BSD_def by auto
qed

(* lemma taken from lemma 3.5.1 from Heiko Mantel's dissertation *)
lemma BSD_implies_D: 
"BSD \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> D \<V> Tr\<^bsub>ES\<^esub>"
proof - 
  assume BSD: "BSD \<V> Tr\<^bsub>ES\<^esub>"
  
  {
    fix \<alpha> \<beta> c
    assume "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and "c \<in> C\<^bsub>\<V>\<^esub>"
      and "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
    with BSD obtain \<alpha>' 
      where "\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V \<V>"
      and  "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      by (simp add: BSD_def, auto)
    hence "(\<exists>\<alpha>' \<beta>'.
      (\<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []) \<and>
      \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>))"
      by auto
  }
  thus ?thesis
    unfolding BSD_def D_def
    by auto
qed

(* lemma taken from lemma 3.5.1 from Heiko Mantel's dissertation *)
lemma SD_implies_SR: 
"SD \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> SR \<V> Tr\<^bsub>ES\<^esub>"
unfolding SR_def
proof
  fix \<tau> 

  assume SD: "SD \<V> Tr\<^bsub>ES\<^esub>"
  assume \<tau>_trace: "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
  
  {
    fix  n 

      (* show via induction over length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>) that SR holds *)
    have SR_via_length: " \<lbrakk> \<tau> \<in> Tr\<^bsub>ES\<^esub>; n = length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>) \<rbrakk> 
      \<Longrightarrow> \<exists>\<tau>' \<in> Tr\<^bsub>ES\<^esub>. \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    proof (induct n arbitrary: \<tau>)
      case 0 
      note \<tau>_in_Tr = \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close>
        and \<open>0 = length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>)\<close>
      hence "\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        by simp
      with \<tau>_in_Tr show ?case 
        by auto
    next
      case (Suc n)
      from projection_split_last[OF Suc(3)] obtain \<beta> c \<alpha>
        where c_in_C: "c \<in> C\<^bsub>\<V>\<^esub>"
        and \<tau>_is_\<beta>c\<alpha>: "\<tau> = \<beta> @ [c] @ \<alpha>"
        and \<alpha>_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        and \<beta>\<alpha>_contains_n_cs: "n = length ((\<beta> @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>)"
      by auto
      with Suc(2) have \<beta>c\<alpha>_in_Tr: "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
        by auto
      
      with SD c_in_C \<beta>c\<alpha>_in_Tr \<alpha>_no_c obtain \<beta>' \<alpha>' 
        where \<beta>'\<alpha>'_in_Tr: "(\<beta>' @ \<alpha>') \<in> Tr\<^bsub>ES\<^esub>" 
        and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
        and \<alpha>'_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        and \<beta>'_VC_is_\<beta>_VC: "\<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)"
        unfolding SD_def
        by blast
       
      have "(\<beta>' @ \<alpha>') \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
      proof - 
        from \<beta>'_VC_is_\<beta>_VC have  "\<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
          by (rule projection_subset_eq_from_superset_eq)
        with \<alpha>'_V_is_\<alpha>_V have "(\<beta>' @ \<alpha>') \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = (\<beta> @ \<alpha>) \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
          by (simp add: projection_def)
        moreover
        with  VIsViewOnE c_in_C have "c \<notin> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
          by (simp add: isViewOn_def V_valid_def VC_disjoint_def NC_disjoint_def, auto)
        hence "(\<beta> @ \<alpha>) \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = (\<beta> @ [c] @ \<alpha>) \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
          by (simp add: projection_def)
        moreover note \<tau>_is_\<beta>c\<alpha>
        ultimately show ?thesis
          by auto
      qed
      moreover 
      have "n = length ((\<beta>' @ \<alpha>') \<upharpoonleft> C\<^bsub>\<V>\<^esub>)"
      proof -
        have  "\<beta>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = \<beta> \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
        proof -
          have "V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub> = C\<^bsub>\<V>\<^esub> \<union> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
            by auto
          with \<beta>'_VC_is_\<beta>_VC have "\<beta>' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<union> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)) = \<beta> \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<union> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>))"
            by auto
          thus ?thesis
            by (rule projection_subset_eq_from_superset_eq)
        qed
        with \<alpha>'_no_c \<alpha>_no_c have "(\<beta>' @ \<alpha>') \<upharpoonleft> C\<^bsub>\<V>\<^esub> = (\<beta> @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<beta>\<alpha>_contains_n_cs show ?thesis
          by auto
      qed
      with Suc.hyps \<beta>'\<alpha>'_in_Tr obtain \<tau>' 
        where  "\<tau>' \<in> Tr\<^bsub>ES\<^esub>" 
        and "\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        and "\<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = (\<beta>' @ \<alpha>') \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
        by auto
      ultimately show ?case
        by auto
    qed 
  }
  
  hence "\<tau> \<in> Tr\<^bsub>ES\<^esub> \<Longrightarrow> \<exists>\<tau>'. \<tau>'\<in>Tr\<^bsub>ES\<^esub> \<and> \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    by auto

  from this \<tau>_trace obtain \<tau>' where
        \<tau>'_trace : "\<tau>'\<in>Tr\<^bsub>ES\<^esub>"
    and \<tau>'_no_C  : "\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    and \<tau>'_\<tau>_rel : "\<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
  by auto

  from \<tau>'_no_C have "\<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    by (auto simp add: projection_on_union)

  with  VIsViewOnE have \<tau>'_E_eq_VN: "\<tau>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    by (auto simp add: isViewOn_def)

  from validES \<tau>'_trace have "(set \<tau>') \<subseteq> E\<^bsub>ES\<^esub>" 
    by (auto simp add: ES_valid_def traces_contain_events_def)
  hence "\<tau>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<tau>'" by (simp add: list_subset_iff_projection_neutral)
  with \<tau>'_E_eq_VN have "\<tau>' = \<tau>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" by auto
  with \<tau>'_\<tau>_rel have "\<tau>' = \<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" by auto
  with \<tau>'_trace show "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>" by auto
qed

(* lemma taken from lemma 3.5.1 from Heiko Mantel's dissertation *)
lemma D_implies_R: 
"D \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> R \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume D: "D \<V> Tr\<^bsub>ES\<^esub>"  
  {
    fix \<tau> n 

      (* show via induction over length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>) that R holds *)
    have R_via_length: " \<lbrakk> \<tau> \<in> Tr\<^bsub>ES\<^esub>; n = length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>) \<rbrakk>
                          \<Longrightarrow> \<exists>\<tau>' \<in> Tr\<^bsub>ES\<^esub>. \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
    proof (induct n arbitrary: \<tau>)
      case 0 
      note \<tau>_in_Tr = \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close>
        and \<open>0 = length (\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub>)\<close>
      hence "\<tau> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        by simp
      with \<tau>_in_Tr show ?case 
        by auto
    next
      case (Suc n)
      from projection_split_last[OF Suc(3)] obtain \<beta> c \<alpha>
        where c_in_C: "c \<in> C\<^bsub>\<V>\<^esub>"
        and \<tau>_is_\<beta>c\<alpha>: "\<tau> = \<beta> @ [c] @ \<alpha>"
        and \<alpha>_no_c: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
        and \<beta>\<alpha>_contains_n_cs: "n = length ((\<beta> @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>)"
      by auto
      with Suc(2) have \<beta>c\<alpha>_in_Tr: "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
        by auto
      
      with D c_in_C \<beta>c\<alpha>_in_Tr \<alpha>_no_c obtain \<beta>' \<alpha>' 
        where \<beta>'\<alpha>'_in_Tr: "(\<beta>' @ \<alpha>') \<in> Tr\<^bsub>ES\<^esub>" 
        and \<alpha>'_V_is_\<alpha>_V: "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        and \<alpha>'_no_c: "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        and \<beta>'_VC_is_\<beta>_VC: "\<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)"
        unfolding D_def 
        by blast

      have "(\<beta>' @ \<alpha>') \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      proof - 
        from \<beta>'_VC_is_\<beta>_VC have  "\<beta>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<beta> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (rule projection_subset_eq_from_superset_eq)
        with \<alpha>'_V_is_\<alpha>_V have "(\<beta>' @ \<alpha>') \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (\<beta> @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        moreover
        with  VIsViewOnE c_in_C have "c \<notin> V\<^bsub>\<V>\<^esub>"
          by (simp add: isViewOn_def V_valid_def VC_disjoint_def, auto)
        hence "(\<beta> @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (\<beta> @ [c] @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        moreover note \<tau>_is_\<beta>c\<alpha>
        ultimately show ?thesis
          by auto
      qed
      moreover 
      have "n = length ((\<beta>' @ \<alpha>') \<upharpoonleft> C\<^bsub>\<V>\<^esub>)"
      proof -
        have  "\<beta>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = \<beta> \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
        proof -
          have "V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub> = C\<^bsub>\<V>\<^esub> \<union> V\<^bsub>\<V>\<^esub>"
            by auto
          with \<beta>'_VC_is_\<beta>_VC have "\<beta>' \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<union> V\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<union> V\<^bsub>\<V>\<^esub>)"
            by auto
          thus ?thesis
            by (rule projection_subset_eq_from_superset_eq)
        qed
        with \<alpha>'_no_c \<alpha>_no_c have "(\<beta>' @ \<alpha>') \<upharpoonleft> C\<^bsub>\<V>\<^esub> = (\<beta> @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub>"
          by (simp add: projection_def)
        with \<beta>\<alpha>_contains_n_cs show ?thesis
          by auto
      qed
      with Suc.hyps \<beta>'\<alpha>'_in_Tr obtain \<tau>' 
        where  "\<tau>' \<in> Tr\<^bsub>ES\<^esub>" 
        and "\<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
        and "\<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = (\<beta>' @ \<alpha>') \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
        by auto
      ultimately show ?case
        by auto
    qed 
  }
  thus ?thesis
    by (simp add: R_def)
qed

(* Theorem 3.5.6.1 from Heiko Mantel's dissertation *)
lemma SR_implies_R_for_modified_view :
"\<lbrakk>SR \<V> Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> R \<V>' Tr\<^bsub>ES\<^esub>" 
proof -
  assume "SR \<V> Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>"
   {
     from \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> VIsViewOnE 
     have V'IsViewOnE: "isViewOn \<V>' E\<^bsub>ES\<^esub> " 
       unfolding isViewOn_def V_valid_def VC_disjoint_def NC_disjoint_def VN_disjoint_def by auto
    fix \<tau>
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    with \<open>SR \<V> Tr\<^bsub>ES\<^esub>\<close> have "\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>"
      unfolding SR_def by auto
    
    let ?\<tau>'="\<tau> \<upharpoonleft>V\<^bsub>\<V>'\<^esub>"
    
    from \<open>\<tau> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>\<close> have "?\<tau>' \<in> Tr\<^bsub>ES\<^esub>" 
      using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> by simp
    moreover   
    from V'IsViewOnE have "?\<tau>'\<upharpoonleft>C\<^bsub>\<V>'\<^esub>=[]"
      using disjoint_projection  
      unfolding isViewOn_def V_valid_def VC_disjoint_def by auto
    moreover  
    have "?\<tau>'\<upharpoonleft>V\<^bsub>\<V>'\<^esub> = \<tau>\<upharpoonleft>V\<^bsub>\<V>'\<^esub>"
      by (simp add: projection_subset_elim)
    ultimately
    have "\<exists>\<tau>'\<in>Tr\<^bsub>ES\<^esub>. \<tau>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>"
      by auto
   }
  with \<open>SR \<V> Tr\<^bsub>ES\<^esub>\<close> show ?thesis 
    unfolding R_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> by auto 
qed   

lemma R_implies_SR_for_modified_view : 
"\<lbrakk>R \<V>' Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> SR \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume "R \<V>' Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>"
  {
    fix \<tau>
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    from \<open>R \<V>' Tr\<^bsub>ES\<^esub>\<close> \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close>  obtain \<tau>' where "\<tau>' \<in> Tr\<^bsub>ES\<^esub>"
                                        and "\<tau>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []" 
                                        and "\<tau>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>"
                                        unfolding R_def by auto
    from VIsViewOnE \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>  have "isViewOn  \<V>' E\<^bsub>ES\<^esub>" 
      unfolding isViewOn_def V_valid_def  VN_disjoint_def VC_disjoint_def NC_disjoint_def                                   
      by auto

    from \<open>\<tau>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>\<close>  \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<tau>' \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>)" 
      by simp
    
    from \<open>\<tau>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []\<close> have "\<tau>' =\<tau>' \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>)"
      using validES \<open>\<tau>' \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>isViewOn \<V>' E\<^bsub>ES\<^esub>\<close> 
      unfolding projection_def ES_valid_def isViewOn_def traces_contain_events_def
      by (metis UnE filter_True filter_empty_conv)
    hence  "\<tau>' =\<tau> \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>)" 
      using \<open>\<tau>' \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>) = \<tau> \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>)\<close>
      by simp                 
    with \<open>\<tau>' \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<tau> \<upharpoonleft> (V\<^bsub>\<V>'\<^esub> \<union> N\<^bsub>\<V>'\<^esub>) \<in> Tr\<^bsub>ES\<^esub>" 
      by auto
  } 
  thus ?thesis 
    unfolding SR_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    by simp
qed

(* Theorem 3.5.6.2 from Heiko Mantel's dissertation *)
lemma SD_implies_BSD_for_modified_view :
"\<lbrakk>SD \<V> Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> BSD \<V>' Tr\<^bsub>ES\<^esub>" 
proof -
  assume "SD \<V> Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>"
   {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>'\<^esub>"
       and "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []"
    
    from \<open>c \<in> C\<^bsub>\<V>'\<^esub>\<close>  \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    have "c \<in> C\<^bsub>\<V>\<^esub>" 
      by auto     
    from \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []" 
      by auto

    from \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close> \<open>\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> 
    have "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>" using \<open>SD \<V> Tr\<^bsub>ES\<^esub>\<close>
      unfolding SD_def by auto
    hence  "\<exists>\<alpha>'. \<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and>  \<alpha>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>  \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = [] " 
      using \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []\<close> by blast
   }
  with \<open>SD \<V> Tr\<^bsub>ES\<^esub>\<close> show ?thesis 
    unfolding BSD_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> by auto 
qed   

lemma BSD_implies_SD_for_modified_view : 
"\<lbrakk>BSD \<V>' Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> SD \<V> Tr\<^bsub>ES\<^esub>"
  unfolding SD_def
  proof(clarsimp)
  fix \<alpha> \<beta> c
  assume BSD_view' : "BSD \<lparr>V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub>\<rparr> Tr\<^bsub>ES\<^esub>"
  assume alpha_no_C_view : "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
  assume c_C_view : "c \<in> C\<^bsub>\<V>\<^esub>"
  assume beta_c_alpha_is_trace : "\<beta> @ c # \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
  
  from BSD_view' alpha_no_C_view c_C_view beta_c_alpha_is_trace 
  obtain \<alpha>' 
    where beta_alpha'_is_trace: "\<beta> @ \<alpha>'\<in>(Tr\<^bsub>ES\<^esub>)" 
      and alpha_alpha': "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
      and alpha'_no_C_view : "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    by (auto simp add: BSD_def)

  from beta_c_alpha_is_trace validES
  have alpha_consists_of_events: "set \<alpha> \<subseteq> E\<^bsub>ES\<^esub>" 
      by (auto simp add: ES_valid_def traces_contain_events_def)

  from alpha_no_C_view have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    by (rule projection_on_union)
  with VIsViewOnE  have alpha_on_ES : "\<alpha> \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    unfolding isViewOn_def by simp

  from alpha_consists_of_events VIsViewOnE have "\<alpha> \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>"
    by (simp add: list_subset_iff_projection_neutral)
  
  with alpha_on_ES have \<alpha>_eq: "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha>" by auto

  from beta_alpha'_is_trace validES
  have alpha'_consists_of_events: "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" 
    by (auto simp add: ES_valid_def traces_contain_events_def)

  from alpha'_no_C_view have "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    by (rule projection_on_union)
  with VIsViewOnE have alpha'_on_ES : "\<alpha>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    unfolding isViewOn_def by (simp)

  from alpha'_consists_of_events VIsViewOnE have "\<alpha>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>'"
    by (simp add: list_subset_iff_projection_neutral)
  
  with alpha'_on_ES have \<alpha>'_eq: "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha>'" by auto


  from alpha_alpha' \<alpha>_eq \<alpha>'_eq have "\<alpha> = \<alpha>'" by auto
    
  with beta_alpha'_is_trace show "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>" by auto
qed


(* lemma taken from lemma 3.5.4 from Heiko Mantel's dissertation*)
lemma SD_implies_FCD: 
"(SD \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
proof -    
   assume SD: "SD \<V> Tr\<^bsub>ES\<^esub>"
    { 
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub>  \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
      and  "v \<in> V\<^bsub>\<V>\<^esub>  \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
      and alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and  "\<beta> @ [c, v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
    moreover
    with VIsViewOnE  have "(v # \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    ultimately
    have "\<beta> @ (v # \<alpha>) \<in> Tr\<^bsub>ES\<^esub>" 
      using SD unfolding SD_def by auto
    with alpha_C_empty  
    have "\<exists>\<alpha>'. \<exists>\<delta>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ \<delta>' @ [v] @ \<alpha>') \<in>  Tr\<^bsub>ES\<^esub>  
            \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
      by (metis append.simps(1) append.simps(2) bot_least list.set(1))
  }    
  thus ?thesis 
    unfolding SD_def FCD_def by auto
qed



(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma SI_implies_BSI :
"(SI \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> BSI \<V> Tr\<^bsub>ES\<^esub> "
proof -
  assume SI: "SI \<V> Tr\<^bsub>ES\<^esub>"
  { 
    fix \<alpha> \<beta> c 
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and  "\<beta> @  \<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      and alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
    with SI have "\<beta> @ c # \<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      unfolding SI_def by auto
    hence  "\<exists>\<alpha>'. \<beta> @ c # \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      using alpha_C_empty  by auto
  }
  thus ?thesis 
    unfolding SI_def BSI_def by auto
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma BSI_implies_I: 
"(BSI \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> (I \<V> Tr\<^bsub>ES\<^esub>)"
proof -
  assume BSI: "BSI \<V> Tr\<^bsub>ES\<^esub>"

  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    with BSI obtain \<alpha>' 
      where "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and  "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      unfolding BSI_def
      by blast
    hence 
      "(\<exists>\<alpha>' \<beta>'. (\<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []) \<and>
                  \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>))"
      by auto
  }
  thus ?thesis unfolding BSI_def I_def
    by auto
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma SIA_implies_BSIA: 
"(SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> (BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>)"
proof -
  assume SIA: "SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and "(Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c)"
    with SIA obtain "\<beta> @ c # \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      unfolding SIA_def by auto
    hence "\<exists> \<alpha>'. \<beta> @ c # \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"  
      using  alpha_C_empty  by auto
  }
  thus ?thesis
    unfolding SIA_def BSIA_def by auto
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma BSIA_implies_IA: 
"(BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> (IA \<rho> \<V> Tr\<^bsub>ES\<^esub>)"
proof -
  assume BSIA: "BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"

  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and "(Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c)"
    with BSIA obtain \<alpha>' 
      where "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>"
      and  "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      unfolding BSIA_def
      by blast
    hence "(\<exists>\<alpha>' \<beta>'.
      (\<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []) \<and>
      \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>))"
      by auto
  }
  thus ?thesis 
    unfolding BSIA_def IA_def by auto
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma SI_implies_SIA: 
"SI \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume SI: "SI \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and  "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    with SI have "\<beta> @ (c # \<alpha>) \<in> Tr\<^bsub>ES\<^esub>"
      unfolding SI_def by auto  
  }
  thus ?thesis unfolding SI_def SIA_def by auto  
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma BSI_implies_BSIA: 
"BSI \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume BSI: "BSI \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and  "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    with BSI have "\<exists> \<alpha>'. \<beta> @ (c # \<alpha>') \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>  \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      unfolding BSI_def by auto  
  }
  thus ?thesis
    unfolding BSI_def BSIA_def by auto  
qed

(* lemma taken from lemma 3.5.9 from Heiko Mantel's dissertation *)
lemma I_implies_IA: 
"I \<V> Tr\<^bsub>ES\<^esub> \<Longrightarrow> IA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume I: "I \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and  "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    with I have "\<exists> \<alpha>' \<beta>'. \<beta>' @ (c # \<alpha>') \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub>  
                            \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []  \<and> \<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) " 
      unfolding I_def by auto  
  }
  thus ?thesis
    unfolding I_def IA_def by auto  
qed

(* Theorem 3.5.15.1 from Heiko Mantel's dissertation *)
lemma SI_implies_BSI_for_modified_view :
"\<lbrakk>SI \<V> Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> BSI \<V>' Tr\<^bsub>ES\<^esub>" 
proof -
  assume "SI \<V> Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>"
   {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>'\<^esub>"
       and "\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []"
    
    from \<open>c \<in> C\<^bsub>\<V>'\<^esub>\<close>  \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    have "c \<in> C\<^bsub>\<V>\<^esub>"
      by auto     
    from \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      by auto

    from \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close> \<open>\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> 
    have "\<beta> @ [c] @  \<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      using \<open>SI \<V> Tr\<^bsub>ES\<^esub>\<close>  unfolding SI_def by auto
    hence  "\<exists>\<alpha>'. \<beta> @ [c] @  \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and>  \<alpha>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>  \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = [] " 
      using \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []\<close> 
      by blast
   }
  with \<open>SI \<V> Tr\<^bsub>ES\<^esub>\<close> show ?thesis 
    unfolding BSI_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> by auto 
qed 

lemma BSI_implies_SI_for_modified_view : 
"\<lbrakk>BSI \<V>' Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<rbrakk> \<Longrightarrow> SI \<V> Tr\<^bsub>ES\<^esub>"
  unfolding SI_def
  proof (clarsimp)
  fix \<alpha> \<beta> c
  assume BSI_view' : "BSI \<lparr>V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>, N = {}, C = C\<^bsub>\<V>\<^esub>\<rparr> Tr\<^bsub>ES\<^esub>"
  assume alpha_no_C_view : "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
  assume c_C_view : "c \<in> C\<^bsub>\<V>\<^esub>"
  assume beta_alpha_is_trace : "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"

  from BSI_view' have "\<forall>c\<in>C\<^bsub>\<V>\<^esub>. \<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [] 
    \<longrightarrow> (\<exists>\<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
    by (auto simp add: BSI_def)

  with beta_alpha_is_trace alpha_no_C_view have "\<forall>c\<in>C\<^bsub>\<V>\<^esub>.
        (\<exists>\<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
    by auto

  with this BSI_view' c_C_view obtain \<alpha>'
    where beta_c_alpha'_is_trace: "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>" 
      and alpha_alpha': "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
      and alpha'_no_C_view : "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    by auto

  from beta_alpha_is_trace validES
  have alpha_consists_of_events: "set \<alpha> \<subseteq> E\<^bsub>ES\<^esub>" 
    by (auto simp add: ES_valid_def traces_contain_events_def)

  from alpha_no_C_view have "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    by (rule projection_on_union)
  with VIsViewOnE have alpha_on_ES : "\<alpha> \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    unfolding isViewOn_def by (simp)

  from alpha_consists_of_events VIsViewOnE have "\<alpha> \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>"
    by (simp add: list_subset_iff_projection_neutral)
  
  with alpha_on_ES have \<alpha>_eq: "\<alpha> \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha>" by auto
  
  from beta_c_alpha'_is_trace validES 
  have alpha'_consists_of_events: "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" 
    by (auto simp add: ES_valid_def traces_contain_events_def)

  from alpha'_no_C_view have "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
    by (rule projection_on_union)
  with VIsViewOnE have alpha'_on_ES : "\<alpha>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" 
    unfolding isViewOn_def by (simp)

  from alpha'_consists_of_events VIsViewOnE have "\<alpha>' \<upharpoonleft> E\<^bsub>ES\<^esub> = \<alpha>'"
    by (simp add: list_subset_iff_projection_neutral)
  
  with alpha'_on_ES have \<alpha>'_eq: "\<alpha>' \<upharpoonleft> (V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) = \<alpha>'" by auto

  from alpha_alpha' \<alpha>_eq \<alpha>'_eq have "\<alpha> = \<alpha>'" by auto
    
  with beta_c_alpha'_is_trace show "\<beta> @ c # \<alpha> \<in> Tr\<^bsub>ES\<^esub>" by auto
qed


(* lemma taken from Theorem 3.5.15.2 from Heiko Mantel's dissertation *)
lemma SIA_implies_BSIA_for_modified_view :
"\<lbrakk>SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr> ; \<rho> \<V> = \<rho>' \<V>'\<rbrakk> \<Longrightarrow> BSIA \<rho>' \<V>' Tr\<^bsub>ES\<^esub>" 
proof -
  assume "SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>"
     and "\<rho> \<V> = \<rho>' \<V>'"
   {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>'\<^esub>"
       and "\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []"
       and "Adm \<V>' \<rho>' Tr\<^bsub>ES\<^esub> \<beta> c"
    
    from \<open>c \<in> C\<^bsub>\<V>'\<^esub>\<close>  \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    have "c \<in> C\<^bsub>\<V>\<^esub>"
      by auto     
    from \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      by auto
    from  \<open>Adm \<V>' \<rho>' Tr\<^bsub>ES\<^esub> \<beta> c\<close> \<open>\<rho> \<V> = \<rho>' \<V>'\<close> 
    have "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
      by (simp add: Adm_def)

    from \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close> \<open>\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c\<close>
    have "\<beta> @ [c] @  \<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      using \<open>SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>\<close>  unfolding SIA_def by auto
    hence  "\<exists>\<alpha>'. \<beta> @ [c] @  \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and>  \<alpha>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>  \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = [] " 
      using \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []\<close> by blast
   }
  with \<open>SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>\<close> show ?thesis 
    unfolding BSIA_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    by auto 
qed 

lemma BSIA_implies_SIA_for_modified_view : 
  "\<lbrakk>BSIA \<rho>' \<V>' Tr\<^bsub>ES\<^esub>; \<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub> \<rparr>; \<rho> \<V> = \<rho>' \<V>'\<rbrakk> \<Longrightarrow> SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "BSIA \<rho>' \<V>' Tr\<^bsub>ES\<^esub>"
     and "\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub> \<rparr>" 
     and "\<rho> \<V> = \<rho>' \<V>'"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^esub>"
       and "\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
       and "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    
    from \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    have "c \<in> C\<^bsub>\<V>'\<^esub>"
      by auto     
    from \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []"
      by auto
    from  \<open>Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c\<close> \<open>\<rho> \<V> = \<rho>' \<V>'\<close> 
    have "Adm \<V>' \<rho>' Tr\<^bsub>ES\<^esub> \<beta> c"
      by (simp add: Adm_def)

    from \<open>c \<in> C\<^bsub>\<V>'\<^esub>\<close> \<open>\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>'\<^esub> = []\<close> \<open>Adm \<V>' \<rho>' Tr\<^bsub>ES\<^esub> \<beta> c\<close>
    obtain \<alpha>' where "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                and " \<alpha>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>"
                and " \<alpha>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []"
      using \<open>BSIA \<rho>' \<V>' Tr\<^bsub>ES\<^esub>\<close>  unfolding BSIA_def by blast

    (*Show that \<alpha>'=\<alpha>*)    
    from \<open>\<beta>  @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> validES
    have alpha_consists_of_events: "set \<alpha> \<subseteq> E\<^bsub>ES\<^esub>" 
      by (auto simp add: ES_valid_def traces_contain_events_def)

    from \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> validES
    have alpha'_consists_of_events: "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" 
      by (auto simp add: ES_valid_def traces_contain_events_def)  

    from \<open>\<alpha>' \<upharpoonleft> V\<^bsub>\<V>'\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>'\<^esub>\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> 
    have "\<alpha>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)=\<alpha>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)" by auto
    with \<open>\<alpha>' \<upharpoonleft> C\<^bsub>\<V>'\<^esub> = []\<close>  \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N = {} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close>
    have "\<alpha>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)=\<alpha>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)" 
      by (simp add: projection_on_union)
    with VIsViewOnE alpha_consists_of_events alpha'_consists_of_events
    have "\<alpha>'=\<alpha>" unfolding isViewOn_def 
      by (simp add: list_subset_iff_projection_neutral)

    hence  "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub> "
      using \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by blast
   }
  with \<open>BSIA \<rho>' \<V>' Tr\<^bsub>ES\<^esub>\<close> show ?thesis 
    unfolding SIA_def using \<open>\<V>' = \<lparr> V = V\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> , N ={} , C = C\<^bsub>\<V>\<^esub> \<rparr>\<close> by auto   
qed    
end

(* lemma taken from lemma 3.5.11 in Heiko Mantel's dissertation *)
lemma Adm_implies_Adm_for_modified_rho: 
"\<lbrakk> Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr \<alpha> e;\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)\<rbrakk> \<Longrightarrow> Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr \<alpha> e " 
proof -
  assume "Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr \<alpha> e"
    and  "\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)"
  then obtain \<gamma>
    where "\<gamma> @ [e] \<in> Tr"
      and "\<gamma> \<upharpoonleft> \<rho>\<^sub>2 \<V>\<^sub>2 = \<alpha> \<upharpoonleft> \<rho>\<^sub>2 \<V>\<^sub>2"
    unfolding Adm_def by auto
  thus "Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr \<alpha> e"
    unfolding Adm_def 
    using \<open>\<rho>\<^sub>1 \<V>\<^sub>1 \<subseteq> \<rho>\<^sub>2 \<V>\<^sub>2\<close> non_empty_projection_on_subset 
    by blast
qed

context BSPTaxonomyDifferentCorrections
begin

(* lemma taken from lemma 3.5.13 from Heiko Mantel's dissertation*)
lemma SI_implies_FCI: 
"(SI \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
proof -    
   assume SI: "SI \<V> Tr\<^bsub>ES\<^esub>"
    { 
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub>  \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
      and  "v \<in> V\<^bsub>\<V>\<^esub>  \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
      and  "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    moreover
    with VIsViewOnE  have "(v # \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    ultimately
    have "\<beta> @ [c , v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>" using SI unfolding SI_def by auto
    with alpha_C_empty  
    have "\<exists>\<alpha>'. \<exists>\<delta>'. 
              (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in>  Tr\<^bsub>ES\<^esub> 
                \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
      by (metis append.simps(1) append.simps(2) bot_least list.set(1))
  }    
  thus ?thesis 
    unfolding SI_def FCI_def by auto
qed

(* lemma taken from lemma 3.5.13 from Heiko Mantel's dissertation*)
lemma SIA_implies_FCIA: 
"(SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
proof -    
   assume SIA: "SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"
    { 
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub>  \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
      and  "v \<in> V\<^bsub>\<V>\<^esub>  \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
      and  "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and alpha_C_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
      and "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    moreover
    with VIsViewOnE  have "(v # \<alpha>) \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    ultimately
    have "\<beta> @ [c , v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>" using SIA unfolding SIA_def by auto
    with alpha_C_empty  
    have "\<exists>\<alpha>'. \<exists>\<delta>'. 
              (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ((\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>') \<in>  Tr\<^bsub>ES\<^esub>  
                \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [])" 
      by (metis append.simps(1) append.simps(2) bot_least list.set(1))
  }    
  thus ?thesis
    unfolding SIA_def FCIA_def by auto
qed

(* lemma taken from lemma 3.5.13 from Heiko Mantel's dissertation*)
lemma FCI_implies_FCIA: 
"(FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>) \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof-
  assume FCI: "FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub>  \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
      and  "v \<in> V\<^bsub>\<V>\<^esub>  \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
      and  "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []"
    with FCI have   "\<exists>\<alpha>' \<delta>'. set \<delta>' \<subseteq> N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub> \<and>
                         \<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
                            unfolding FCI_def by auto   
  }
  thus ?thesis
    unfolding FCI_def FCIA_def by auto  
qed


(* Mantel's PhD thesis, Theorem 3.5.7 Trivially fulfilled BSPs*)
lemma Trivially_fulfilled_SR_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> SR \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "C\<^bsub>\<V>\<^esub>={}"
  {
    fix \<tau> 
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    hence "\<tau>=\<tau>\<upharpoonleft>E\<^bsub>ES\<^esub>" using  validES 
      unfolding  ES_valid_def traces_contain_events_def projection_def by auto
    with \<open>C\<^bsub>\<V>\<^esub>={}\<close> have "\<tau>=\<tau>\<upharpoonleft>(V\<^bsub>\<V>\<^esub>\<union>N\<^bsub>\<V>\<^esub>)"
      using VIsViewOnE unfolding isViewOn_def by auto    
    with \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<tau>\<upharpoonleft>(V\<^bsub>\<V>\<^esub>\<union>N\<^bsub>\<V>\<^esub>) \<in> Tr\<^bsub>ES\<^esub>"
      by auto
  }
  thus ?thesis
    unfolding SR_def by auto
qed

lemma Trivially_fulfilled_R_C_empty: 
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> R \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "C\<^bsub>\<V>\<^esub>={}"
  {
    fix \<tau> 
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    hence "\<tau>=\<tau>\<upharpoonleft>E\<^bsub>ES\<^esub>" using  validES 
      unfolding  ES_valid_def traces_contain_events_def projection_def by auto
    with \<open>C\<^bsub>\<V>\<^esub>={}\<close> have "\<tau>=\<tau>\<upharpoonleft>(V\<^bsub>\<V>\<^esub>\<union>N\<^bsub>\<V>\<^esub>)"
      using VIsViewOnE unfolding isViewOn_def by auto    
    with \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>C\<^bsub>\<V>\<^esub>={}\<close> have "\<exists>\<tau>' \<in> Tr\<^bsub>ES\<^esub>. \<tau>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[] \<and> \<tau>' \<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<tau>\<upharpoonleft>V\<^bsub>\<V>\<^esub>" 
      unfolding projection_def by auto
  }
  thus ?thesis
    unfolding R_def by auto
qed

lemma Trivially_fulfilled_SD_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> SD \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: SD_def)

lemma Trivially_fulfilled_BSD_C_empty: 
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> BSD \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: BSD_def)

lemma Trivially_fulfilled_D_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> D \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: D_def)

lemma Trivially_fulfilled_FCD_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: FCD_def)

lemma Trivially_fullfilled_R_V_empty: 
"V\<^bsub>\<V>\<^esub>={} \<Longrightarrow> R \<V> Tr\<^bsub>ES\<^esub>"
proof - 
  assume "V\<^bsub>\<V>\<^esub>={}"
  {
    fix \<tau>
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>"
    let ?\<tau>'="[]"
    from \<open>\<tau> \<in> Tr\<^bsub>ES\<^esub>\<close>have "?\<tau>' \<in> Tr\<^bsub>ES\<^esub>" 
      using validES 
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
    with \<open>V\<^bsub>\<V>\<^esub>={}\<close>
    have "\<exists>\<tau>' \<in> Tr\<^bsub>ES\<^esub>. \<tau>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[] \<and> \<tau>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<tau>\<upharpoonleft>V\<^bsub>\<V>\<^esub>"  
      by (metis projection_on_empty_trace projection_to_emptyset_is_empty_trace)
  }
  thus ?thesis
    unfolding R_def by auto  
qed

lemma Trivially_fulfilled_BSD_V_empty: 
"V\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> BSD \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume "V\<^bsub>\<V>\<^esub>={}"
  {
    fix \<alpha> \<beta> c
    assume "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>= []"  

    from \<open>\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>"
      using validES 
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
 
    let ?\<alpha>'="[]"
    from \<open>\<beta> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>V\<^bsub>\<V>\<^esub>={}\<close> 
    have "\<beta>@ ?\<alpha>'\<in>Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      by (simp add: projection_on_empty_trace projection_to_emptyset_is_empty_trace)
    hence
    "\<exists>\<alpha>'. 
      \<beta> @ \<alpha>'\<in>Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []" by blast
  }
  thus ?thesis
    unfolding BSD_def by auto
qed

lemma Trivially_fulfilled_D_V_empty: 
"V\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> D \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume "V\<^bsub>\<V>\<^esub>={}"
  {
    fix \<alpha> \<beta> c
    assume "\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>= []"  
    
    from \<open>\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>"
      using validES 
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
    
    let ?\<beta>'=\<beta> and  ?\<alpha>'="[]"
    from \<open>\<beta> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>V\<^bsub>\<V>\<^esub>={}\<close> 
    have "?\<beta>'@ ?\<alpha>'\<in>Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> ?\<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)"
      by (simp add: projection_on_empty_trace projection_to_emptyset_is_empty_trace)
    hence
    "\<exists>\<alpha>' \<beta>'. 
      \<beta>'@ \<alpha>'\<in>Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)"
      by blast
  }
  thus ?thesis
    unfolding D_def by auto
qed

lemma Trivially_fulfilled_FCD_V_empty: 
"V\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: FCD_def)

(* Mantel's PhD thesis, Theorem 3.5.8 Trivially fulfilled BSPs*)
lemma Trivially_fulfilled_FCD_Nabla_\<Upsilon>_empty: 
"\<lbrakk>\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}\<rbrakk>\<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}"
  thus ?thesis
  proof(rule disjE)
    assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCD_def)
  next
    assume " \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCD_def)
  qed
qed

lemma Trivially_fulfilled_FCD_N_subseteq_\<Delta>_and_BSD: 
"\<lbrakk>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>; BSD \<V> Tr\<^bsub>ES\<^esub>\<rbrakk> \<Longrightarrow> FCD \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
proof -
  assume "N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
     and "BSD \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
       and "\<beta> @ [c,v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
    from \<open>c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>\<close> have "c \<in> C\<^bsub>\<V>\<^esub>"
      by auto
    from \<open>v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>\<close> have "v \<in> V\<^bsub>\<V>\<^esub>"
      by auto
    
    let ?\<alpha>="[v] @ \<alpha>"
    from \<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> have "?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      using VIsViewOnE 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    from \<open>\<beta> @ [c,v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> @ [c] @ ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      by auto
    
    from \<open>BSD \<V> Tr\<^bsub>ES\<^esub>\<close> 
    obtain \<alpha>' 
      where "\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
        and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
        and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      using \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  \<open>\<beta> @ [c] @ ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> 
      unfolding BSD_def by auto 

    from\<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = [v] @ \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>" 
      by (simp add: projection_def)
    then obtain \<delta> \<alpha>''
      where "\<alpha>'=\<delta> @ [v] @ \<alpha>''"
        and "\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []"
        and "\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
       using projection_split_first_with_suffix by fastforce 

    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]" 
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    
    from \<open>\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> have "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" using validES 
      unfolding ES_valid_def traces_contain_events_def by auto
    with  \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "set \<delta> \<subseteq> E\<^bsub>ES\<^esub>"
      by auto
    with  \<open>\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close> \<open>\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []\<close> \<open>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>\<close>
    have "(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)" 
      using VIsViewOnE projection_empty_implies_absence_of_events  
      unfolding isViewOn_def projection_def by blast
    
    let ?\<beta>=\<beta> and ?\<delta>'=\<delta> and ?\<alpha>'=\<alpha>''
    from \<open>(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)\<close> \<open>\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> 
            \<open>\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close>
    have "(set ?\<delta>')\<subseteq>(N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ?\<beta> @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by auto
    hence "\<exists>\<alpha>''' \<delta>''. (set \<delta>'') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> (\<beta> @ \<delta>'' @ [v] @ \<alpha>''') \<in> Tr\<^bsub>ES\<^esub> 
              \<and> \<alpha>''' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>''' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      by auto 
  }
  thus ?thesis
    unfolding FCD_def by auto  
qed

(* Mantel's PhD thesis, Theorem 3.5.16 Trivially fulfilled BSPs*)
lemma Trivially_fulfilled_SI_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> SI \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: SI_def)

lemma Trivially_fulfilled_BSI_C_empty: 
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> BSI \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: BSI_def)

lemma Trivially_fulfilled_I_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> I \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: I_def)

lemma Trivially_fulfilled_FCI_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: FCI_def)

lemma Trivially_fulfilled_SIA_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> SIA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: SIA_def)

lemma Trivially_fulfilled_BSIA_C_empty: 
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: BSIA_def)

lemma Trivially_fulfilled_IA_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> IA \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: IA_def)

lemma Trivially_fulfilled_FCIA_C_empty:  
"C\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCIA \<Gamma> \<rho> \<V> Tr\<^bsub>ES\<^esub>" 
  by (simp add: FCIA_def)

lemma Trivially_fulfilled_FCI_V_empty: 
"V\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: FCI_def)

lemma Trivially_fulfilled_FCIA_V_empty: 
"V\<^bsub>\<V>\<^esub> = {} \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>ES\<^esub>"
  by (simp add: FCIA_def)

lemma Trivially_fulfilled_BSIA_V_empty_rho_subseteq_C_N: 
"\<lbrakk>V\<^bsub>\<V>\<^esub> = {}; \<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<rbrakk> \<Longrightarrow> BSIA \<rho>  \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "V\<^bsub>\<V>\<^esub>={}"
     and "\<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
  {
    fix \<alpha> \<beta> c 
    assume "c \<in> C\<^bsub>\<V>\<^esub>" 
       and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
       and "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    from \<open>Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c\<close> 
    obtain \<gamma> 
      where "\<gamma> @ [c] \<in> Tr\<^bsub>ES\<^esub>"
        and "\<gamma>\<upharpoonleft>(\<rho> \<V>) = \<beta>\<upharpoonleft>(\<rho> \<V>)"
      unfolding Adm_def by auto
    from this(1) have "\<gamma> \<in> Tr\<^bsub>ES\<^esub>" 
      using validES 
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto 
    moreover
    from \<open>\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>"
      using validES
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
    ultimately
    have "\<beta>\<upharpoonleft>E\<^bsub>ES\<^esub>=\<gamma>\<upharpoonleft>E\<^bsub>ES\<^esub>" 
      using validES VIsViewOnE \<open>V\<^bsub>\<V>\<^esub>={}\<close> \<open>\<gamma>\<upharpoonleft>(\<rho> \<V>) = \<beta>\<upharpoonleft>(\<rho> \<V>)\<close> \<open>\<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)\<close> 
        non_empty_projection_on_subset
      unfolding ES_valid_def isViewOn_def traces_contain_events_def 
      by (metis  empty_subsetI sup_absorb2 sup_commute)
    hence "\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>" using validES \<open>\<gamma> @ [c] \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<beta> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<gamma> \<in> Tr\<^bsub>ES\<^esub>\<close>
      unfolding ES_valid_def traces_contain_events_def 
      by (metis  list_subset_iff_projection_neutral subsetI)
    
    let ?\<alpha>'="[]"
    from \<open>\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>V\<^bsub>\<V>\<^esub> = {}\<close> 
    have "\<beta> @ [c] @ ?\<alpha>' \<in>Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []" 
      by (simp add: projection_on_empty_trace projection_to_emptyset_is_empty_trace)
    hence "\<exists> \<alpha>'. \<beta> @ [c] @ \<alpha>' \<in>Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []" 
      by auto  
  }
  thus ?thesis
    unfolding BSIA_def by auto
qed

lemma Trivially_fulfilled_IA_V_empty_rho_subseteq_C_N: 
"\<lbrakk>V\<^bsub>\<V>\<^esub> = {}; \<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>) \<rbrakk> \<Longrightarrow> IA \<rho>  \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "V\<^bsub>\<V>\<^esub>={}"
     and "\<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)"
  {
    fix \<alpha> \<beta> c 
    assume "c \<in> C\<^bsub>\<V>\<^esub>" 
       and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
       and "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    from \<open>Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c\<close>
    obtain \<gamma> 
      where "\<gamma> @ [c] \<in> Tr\<^bsub>ES\<^esub>"
        and "\<gamma>\<upharpoonleft>(\<rho> \<V>) = \<beta>\<upharpoonleft>(\<rho> \<V>)"
        unfolding Adm_def by auto
    from this(1) have "\<gamma> \<in> Tr\<^bsub>ES\<^esub>"
      using validES 
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto 
    moreover
    from \<open>\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>" using validES
      unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
    ultimately
    have "\<beta>\<upharpoonleft>E\<^bsub>ES\<^esub>=\<gamma>\<upharpoonleft>E\<^bsub>ES\<^esub>" 
      using validES VIsViewOnE \<open>V\<^bsub>\<V>\<^esub>={}\<close> \<open>\<gamma>\<upharpoonleft>(\<rho> \<V>) = \<beta>\<upharpoonleft>(\<rho> \<V>)\<close> \<open>\<rho> \<V> \<supseteq> (C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub>)\<close> 
        non_empty_projection_on_subset
      unfolding ES_valid_def isViewOn_def traces_contain_events_def 
      by (metis  empty_subsetI sup_absorb2 sup_commute)
    hence "\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>" using validES \<open>\<gamma> @ [c] \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<beta> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<gamma> \<in> Tr\<^bsub>ES\<^esub>\<close>
      unfolding ES_valid_def traces_contain_events_def 
      by (metis  list_subset_iff_projection_neutral subsetI)
    
    let ?\<beta>'=\<beta> and ?\<alpha>'="[]"
    from \<open>\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>V\<^bsub>\<V>\<^esub> = {}\<close> 
    have "?\<beta>' @ [c] @ ?\<alpha>' \<in>Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] 
              \<and> ?\<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)" 
      by (simp add: projection_on_empty_trace projection_to_emptyset_is_empty_trace)
    hence "\<exists> \<alpha>' \<beta>'. 
              \<beta>' @ [c] @ \<alpha>' \<in>Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = [] 
                \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)"
      by auto  
  }
  thus ?thesis
    unfolding IA_def by auto
qed

lemma Trivially_fulfilled_BSI_V_empty_total_ES_C: 
"\<lbrakk>V\<^bsub>\<V>\<^esub> = {}; total ES C\<^bsub>\<V>\<^esub> \<rbrakk> \<Longrightarrow> BSI \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "V\<^bsub>\<V>\<^esub> = {}"
     and "total ES C\<^bsub>\<V>\<^esub>"  
  {
   fix \<alpha> \<beta> c
   assume "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      and "c \<in> C\<^bsub>\<V>\<^esub>"
   from \<open>\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>" 
    using validES
    unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
   with \<open>total ES C\<^bsub>\<V>\<^esub>\<close> have "\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>" 
    using \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  unfolding total_def by auto
   moreover
   from \<open>V\<^bsub>\<V>\<^esub> = {}\<close> have "\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>=[]"
     unfolding projection_def by auto
   ultimately 
   have "\<exists>\<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]" 
    using \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close>  by (metis append_Nil2 projection_idempotent)     
  }
  thus ?thesis
    unfolding BSI_def by auto
qed

lemma Trivially_fulfilled_I_V_empty_total_ES_C: 
"\<lbrakk>V\<^bsub>\<V>\<^esub> = {}; total ES C\<^bsub>\<V>\<^esub> \<rbrakk> \<Longrightarrow> I \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "V\<^bsub>\<V>\<^esub> = {}"
     and "total ES C\<^bsub>\<V>\<^esub>"  
  {
   fix \<alpha> \<beta> c
   assume "c \<in> C\<^bsub>\<V>\<^esub>"
      and "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
   from \<open>\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> \<in> Tr\<^bsub>ES\<^esub>" 
     using validES
     unfolding ES_valid_def traces_prefixclosed_def prefixclosed_def prefix_def by auto
   with \<open>total ES C\<^bsub>\<V>\<^esub>\<close> have "\<beta> @ [c] \<in> Tr\<^bsub>ES\<^esub>"
     using \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  unfolding total_def by auto
   moreover
   from \<open>V\<^bsub>\<V>\<^esub> = {}\<close> have "\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>=[]"
     unfolding projection_def by auto
   ultimately 
   have "\<exists>\<beta>' \<alpha>'. 
          \<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[] \<and> \<beta>'\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>) = \<beta>\<upharpoonleft>(V\<^bsub>\<V>\<^esub> \<union> C\<^bsub>\<V>\<^esub>)" 
    using \<open>\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []\<close> by (metis append_Nil2 projection_idempotent)     
  }
  thus ?thesis
    unfolding I_def by blast
qed

(* Mantel's PhD thesis, Theorem 3.5.17 Trivially fulfilled BSPs*)
lemma Trivially_fulfilled_FCI_Nabla_\<Upsilon>_empty: 
"\<lbrakk>\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}\<rbrakk>\<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}"
  thus ?thesis
  proof(rule disjE)
    assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCI_def)
  next
    assume " \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCI_def)
  qed
qed

lemma Trivially_fulfilled_FCIA_Nabla_\<Upsilon>_empty: 
"\<lbrakk>\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}\<rbrakk>\<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={} \<or> \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}"
  thus ?thesis
  proof(rule disjE)
    assume "\<nabla>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCIA_def)
  next
    assume " \<Upsilon>\<^bsub>\<Gamma>\<^esub>={}" thus ?thesis
      by (simp add: FCIA_def)
  qed
qed

lemma Trivially_fulfilled_FCI_N_subseteq_\<Delta>_and_BSI: 
"\<lbrakk>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>; BSI \<V> Tr\<^bsub>ES\<^esub>\<rbrakk> \<Longrightarrow> FCI \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
     and "BSI \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
       and "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
    from \<open>c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>\<close> have "c \<in> C\<^bsub>\<V>\<^esub>"
      by auto
    from \<open>v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>\<close> have "v \<in> V\<^bsub>\<V>\<^esub>"
      by auto
    
    let ?\<alpha>="[v] @ \<alpha>"
    from \<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> have "?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      using VIsViewOnE 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    from \<open>\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> @  ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      by auto
    
    from \<open>BSI \<V> Tr\<^bsub>ES\<^esub>\<close> 
    obtain \<alpha>' 
      where "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
        and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
        and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      using \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  \<open>\<beta> @ ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> 
      unfolding BSI_def by blast 

    from\<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = [v] @ \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>" 
      by (simp add: projection_def)
    then 
    obtain \<delta> \<alpha>''
      where "\<alpha>'=\<delta> @ [v] @ \<alpha>''"
        and "\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []"
        and "\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
       using projection_split_first_with_suffix by fastforce 

    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]" 
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    
    from \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> have "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" 
      using validES 
      unfolding ES_valid_def traces_contain_events_def by auto
    with  \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "set \<delta> \<subseteq> E\<^bsub>ES\<^esub>" 
      by auto
    with  \<open>\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close> \<open>\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []\<close> \<open>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>\<close>
    have "(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)"
      using VIsViewOnE projection_empty_implies_absence_of_events  
      unfolding isViewOn_def projection_def by blast
    
    let ?\<beta>=\<beta> and ?\<delta>'=\<delta> and ?\<alpha>'=\<alpha>''
    from \<open>(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)\<close> \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> 
            \<open>\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close>
    have "(set ?\<delta>')\<subseteq>(N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ?\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by auto
    hence "\<exists>\<alpha>''' \<delta>''. (set \<delta>'') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> (\<beta> @ [c] @ \<delta>'' @ [v] @ \<alpha>''') \<in> Tr\<^bsub>ES\<^esub> 
              \<and> \<alpha>''' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>''' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      by auto 
  }
  thus ?thesis
    unfolding FCI_def by auto  
qed

lemma Trivially_fulfilled_FCIA_N_subseteq_\<Delta>_and_BSIA: 
"\<lbrakk>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>; BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>\<rbrakk> \<Longrightarrow> FCIA \<rho> \<Gamma> \<V> Tr\<^bsub>ES\<^esub>" 
proof -
  assume "N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>"
     and "BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c v
    assume "c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>"
       and "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
       and "Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c"
    from \<open>c \<in> C\<^bsub>\<V>\<^esub> \<inter> \<Upsilon>\<^bsub>\<Gamma>\<^esub>\<close> have "c \<in> C\<^bsub>\<V>\<^esub>" 
      by auto
    from \<open>v \<in> V\<^bsub>\<V>\<^esub> \<inter> \<nabla>\<^bsub>\<Gamma>\<^esub>\<close> have "v \<in> V\<^bsub>\<V>\<^esub>" 
      by auto
    
    let ?\<alpha>="[v] @ \<alpha>"
    from \<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> have "?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      using VIsViewOnE 
      unfolding isViewOn_def V_valid_def VC_disjoint_def projection_def by auto
    from \<open>\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> have "\<beta> @  ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>" 
      by auto
    
    from \<open>BSIA \<rho> \<V> Tr\<^bsub>ES\<^esub>\<close> 
    obtain \<alpha>' 
      where "\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
        and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
        and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []"
      using \<open>c \<in> C\<^bsub>\<V>\<^esub>\<close>  \<open>\<beta> @ ?\<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>?\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>Adm \<V> \<rho> Tr\<^bsub>ES\<^esub> \<beta> c\<close> 
      unfolding BSIA_def by blast 

    from\<open>v \<in> V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = ([v] @ \<alpha>)\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub> = [v] @ \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>" 
      by (simp add: projection_def)
    then 
    obtain \<delta> \<alpha>''
      where "\<alpha>'=\<delta> @ [v] @ \<alpha>''"
        and "\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []"
        and "\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>"
       using projection_split_first_with_suffix by fastforce 

    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    from \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub> = []\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]" 
      by (metis append_is_Nil_conv projection_concatenation_commute) 
    
    from \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> have "set \<alpha>' \<subseteq> E\<^bsub>ES\<^esub>" 
      using validES 
      unfolding ES_valid_def traces_contain_events_def by auto
    with  \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> have "set \<delta> \<subseteq> E\<^bsub>ES\<^esub>" 
      by auto
    with  \<open>\<delta>\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close> \<open>\<delta>\<upharpoonleft>V\<^bsub>\<V>\<^esub> = []\<close> \<open>N\<^bsub>\<V>\<^esub> \<subseteq> \<Delta>\<^bsub>\<Gamma>\<^esub>\<close>
    have "(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)" using VIsViewOnE projection_empty_implies_absence_of_events  
      unfolding isViewOn_def projection_def by blast
    
    let ?\<beta>=\<beta> and ?\<delta>'=\<delta> and ?\<alpha>'=\<alpha>''
    from \<open>(set \<delta>) \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>)\<close> \<open>\<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>\<alpha>'=\<delta> @ [v] @ \<alpha>''\<close> 
            \<open>\<alpha>''\<upharpoonleft>V\<^bsub>\<V>\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub>\<close> \<open>\<alpha>''\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]\<close>
    have "(set ?\<delta>')\<subseteq>(N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> ?\<beta> @ [c] @ ?\<delta>' @ [v] @ ?\<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> ?\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^esub>=\<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^esub> \<and> ?\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^esub>=[]"
      by auto
    hence "\<exists>\<alpha>''' \<delta>''. (set \<delta>'') \<subseteq> (N\<^bsub>\<V>\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^esub>) \<and> (\<beta> @ [c] @ \<delta>'' @ [v] @ \<alpha>''') \<in> Tr\<^bsub>ES\<^esub> 
              \<and> \<alpha>''' \<upharpoonleft> V\<^bsub>\<V>\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^esub> \<and> \<alpha>''' \<upharpoonleft> C\<^bsub>\<V>\<^esub> = []" 
      by auto 
  }
  thus ?thesis
    unfolding FCIA_def by auto  
qed

end

context BSPTaxonomyDifferentViewsFirstDim
begin
(* lemma taken from lemma 3.5.2 in Heiko Mantel's dissertation *)
lemma R_implies_R_for_modified_view: 
"R \<V>\<^sub>1 Tr\<^bsub>ES\<^esub> \<Longrightarrow> R \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume R_\<V>\<^sub>1: "R \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
  {
    fix \<tau>
    assume "\<tau> \<in> Tr\<^bsub>ES\<^esub>" 
    with R_\<V>\<^sub>1 have "\<exists> \<tau>' \<in> Tr\<^bsub>ES\<^esub>.  \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>"
      unfolding R_def by auto 
    hence "\<exists> \<tau>' \<in> Tr\<^bsub>ES\<^esub>.  \<tau>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = [] \<and> \<tau>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<tau> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>" 
      using  V2_subset_V1  C2_subset_C1  non_empty_projection_on_subset projection_on_subset by blast
  }
  thus ?thesis
    unfolding R_def by auto
qed

lemma BSD_implies_BSD_for_modified_view: 
"BSD \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>\<Longrightarrow> BSD \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof- 
  assume BSD_\<V>\<^sub>1: "BSD \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
  { 
    fix \<alpha> \<beta> c n 
    assume  c_in_C\<^sub>2: "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>" 
    from C2_subset_C1  c_in_C\<^sub>2  have c_in_C\<^sub>1: "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto 
    have "\<lbrakk>\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>; \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub>=[]; n= length(\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)\<rbrakk>
            \<Longrightarrow> \<exists> \<alpha>'. \<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>  \<and> \<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    proof(induct n arbitrary: \<alpha>  )        
      case 0
        from "0.prems"(3) have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []" by auto
        with c_in_C\<^sub>1 "0.prems"(1) 
          have "\<exists> \<alpha>'. \<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]"
          using BSD_\<V>\<^sub>1 unfolding BSD_def by auto
        then 
        obtain \<alpha>' where "\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                    and "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>"
                    and "\<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]"
          by auto
        from V2_subset_V1  \<open>\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>\<close>  have  "\<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>" 
          using non_empty_projection_on_subset by blast
        moreover
        from \<open>\<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]\<close>  C2_subset_C1 have "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
          using projection_on_subset by auto
        ultimately
        show ?case 
          using \<open>\<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by auto
      next
      case (Suc n)
        from "Suc.prems"(3) projection_split_last[OF "Suc.prems"(3)]  
        obtain \<gamma>\<^sub>1 \<gamma>\<^sub>2 c\<^sub>1 where c\<^sub>1_in_C\<^sub>1: "c\<^sub>1 \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
                         and "\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2" 
                         and "\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []" 
                         and "n = length((\<gamma>\<^sub>1 @ \<gamma>\<^sub>2)\<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)"
          by auto
        from  "Suc.prems"(2) \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> have "\<gamma>\<^sub>1 \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
          by (simp add: projection_concatenation_commute)
        from  "Suc.prems"(1) \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> 
        obtain \<beta>' where "\<beta>'=\<beta> @ [c] @ \<gamma>\<^sub>1"
                    and "\<beta>' @ [c\<^sub>1] @ \<gamma>\<^sub>2 \<in> Tr\<^bsub>ES\<^esub>"
          by auto
        from \<open>\<beta>' @ [c\<^sub>1] @ \<gamma>\<^sub>2 \<in> Tr\<^bsub>ES\<^esub>\<close>  \<open>\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> \<open>c\<^sub>1 \<in> C\<^bsub>\<V>\<^sub>1\<^esub>\<close> 
        obtain \<gamma>\<^sub>2' where " \<beta>' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>"
                    and "\<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>"
                    and "\<gamma>\<^sub>2' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]"
          using BSD_\<V>\<^sub>1  unfolding BSD_def by auto
        from \<open>\<beta>'=\<beta> @ [c] @ \<gamma>\<^sub>1\<close> \<open>\<beta>' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>\<close>  have "\<beta> @ [c] @ \<gamma>\<^sub>1 @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>"
          by auto 
        moreover
        from  \<open>\<gamma>\<^sub>1 \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub>=[]\<close>  \<open>\<gamma>\<^sub>2' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]\<close> C2_subset_C1 have "(\<gamma>\<^sub>1 @ \<gamma>\<^sub>2') \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> =[]" 
          by (metis append_Nil projection_concatenation_commute projection_on_subset)
        moreover
        from \<open>n = length((\<gamma>\<^sub>1 @ \<gamma>\<^sub>2)\<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> \<open>\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> \<open>\<gamma>\<^sub>2' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]\<close> 
        have "n = length((\<gamma>\<^sub>1 @ \<gamma>\<^sub>2')\<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)"
          by (simp add: projection_concatenation_commute)
        ultimately 
        have witness: "\<exists> \<alpha>'. \<beta> @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2') \<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>  \<and> \<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
          using  Suc.hyps by auto
        
        from  \<V>\<^sub>1IsViewOnE \<V>\<^sub>2IsViewOnE V2_subset_V1 C2_subset_C1  c\<^sub>1_in_C\<^sub>1 have "c\<^sub>1 \<notin> V\<^bsub>\<V>\<^sub>2\<^esub>"  
          unfolding isViewOn_def V_valid_def  VC_disjoint_def by auto
        with \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2) \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>" 
          unfolding projection_def by auto
        hence "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<gamma>\<^sub>1 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> @ \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> " 
          using projection_concatenation_commute by auto
        with V2_subset_V1 \<open>\<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>\<close>
        have "\<gamma>\<^sub>1 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> @ \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<gamma>\<^sub>1\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> @ \<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>" 
          using non_empty_projection_on_subset by metis
        with \<open>\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<gamma>\<^sub>1 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> @ \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>\<close> have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2') \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>"
          by (simp add: projection_concatenation_commute)
       
       from witness  \<open>\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2') \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>\<close> 
       show ?case 
         by auto
     qed          
 }  
  thus ?thesis 
    unfolding BSD_def by auto
qed

lemma D_implies_D_for_modified_view: 
"D \<V>\<^sub>1 Tr\<^bsub>ES\<^esub> \<Longrightarrow> D \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof- 
  assume D_\<V>\<^sub>1: "D \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
   from V2_subset_V1 C2_subset_C1
    have V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1: "V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>" by auto
  { 
    fix \<alpha> \<beta> c n 
    assume  c_in_C\<^sub>2: "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>" 
    from C2_subset_C1  c_in_C\<^sub>2  have c_in_C\<^sub>1: "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>" 
      by auto 
    have "\<lbrakk>\<beta> @ [c] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>; \<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub>=[]; n= length(\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)\<rbrakk>
            \<Longrightarrow> \<exists> \<alpha>' \<beta>'. 
                  \<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>  \<and> \<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>  \<and> \<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = [] 
                     \<and> \<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) "
    proof(induct n arbitrary: \<alpha> \<beta> )        
      case 0
        from "0.prems"(3) have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []" by auto
        with c_in_C\<^sub>1 "0.prems"(1) 
        have "\<exists> \<alpha>' \<beta>'. 
                \<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>  \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[] 
                  \<and> \<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)"
          using D_\<V>\<^sub>1 unfolding D_def by fastforce
        then 
        obtain \<beta>' \<alpha>' where "\<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                      and "\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>"
                      and "\<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]"
                      and "\<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          by auto
        from V2_subset_V1  \<open>\<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>\<close>  have  "\<alpha>'\<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>" 
          using non_empty_projection_on_subset by blast
        moreover
        from \<open>\<alpha>' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]\<close>  C2_subset_C1 have "\<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
          using projection_on_subset by auto
        moreover
        from \<open>\<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close>  V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1 
        have "\<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)"
          using non_empty_projection_on_subset by blast
        ultimately
        show ?case 
          using \<open>\<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by auto
      next
      case (Suc n)
        from "Suc.prems"(3) projection_split_last[OF "Suc.prems"(3)]  
        obtain \<gamma>\<^sub>1 \<gamma>\<^sub>2 c\<^sub>1 where c\<^sub>1_in_C\<^sub>1: "c\<^sub>1 \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
                         and "\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2" 
                         and "\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []" 
                         and "n = length((\<gamma>\<^sub>1 @ \<gamma>\<^sub>2)\<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          by auto
        from  "Suc.prems"(2) \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> have "\<gamma>\<^sub>1 \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
          by (simp add: projection_concatenation_commute)
        from  "Suc.prems"(1) \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> 
        obtain \<beta>' where "\<beta>'=\<beta> @ [c] @ \<gamma>\<^sub>1"
                    and "\<beta>' @ [c\<^sub>1] @ \<gamma>\<^sub>2 \<in> Tr\<^bsub>ES\<^esub>"
          by auto
        from \<open>\<beta>' @ [c\<^sub>1] @ \<gamma>\<^sub>2 \<in> Tr\<^bsub>ES\<^esub>\<close>  \<open>\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> \<open>c\<^sub>1 \<in> C\<^bsub>\<V>\<^sub>1\<^esub>\<close> 
        obtain \<gamma>\<^sub>2'  \<beta>'' where " \<beta>'' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>"
                         and "\<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>"
                         and "\<gamma>\<^sub>2' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]"
                         and "\<beta>'' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          using D_\<V>\<^sub>1  unfolding D_def by force
        
        from  c_in_C\<^sub>1 have "c \<in> V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>"
          by auto  
        moreover
        from  \<open>\<beta>'' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta>' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> \<open>\<beta>'=\<beta> @ [c] @ \<gamma>\<^sub>1\<close>  
        have "\<beta>'' \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = (\<beta> @ [c] @ \<gamma>\<^sub>1) \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)"
          by auto 
        ultimately   
        have "\<exists> \<beta>''' \<gamma>\<^sub>1'. \<beta>''=\<beta>'''@ [c] @ \<gamma>\<^sub>1' 
                           \<and> \<beta>'''  \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) 
                           \<and> \<gamma>\<^sub>1'\<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<gamma>\<^sub>1 \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          using projection_split_arbitrary_element by fast
        then  
        obtain \<beta>''' \<gamma>\<^sub>1' where "\<beta>''= \<beta>''' @ [c] @ \<gamma>\<^sub>1'" 
                         and  "\<beta>'''  \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)"
                         and  "\<gamma>\<^sub>1'\<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<gamma>\<^sub>1 \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          using projection_split_arbitrary_element  by auto 
        
        from \<open>\<beta>'' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>\<close> this(1)
        have "\<beta>''' @ [c] @ \<gamma>\<^sub>1' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>"
          by simp    

        from \<open>\<gamma>\<^sub>2' \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> =[]\<close> have "\<gamma>\<^sub>2' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub>=[]"
          using C2_subset_C1 projection_on_subset by auto
        moreover
        from \<open>\<gamma>\<^sub>1 \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []\<close> \<open>\<gamma>\<^sub>1'\<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<gamma>\<^sub>1 \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> 
        have "\<gamma>\<^sub>1'\<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []" using C2_subset_C1 V2_subset_V1 
          by (metis non_empty_projection_on_subset projection_subset_eq_from_superset_eq sup_commute)               
        ultimately
        have "(\<gamma>\<^sub>1' @ \<gamma>\<^sub>2')\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
          by (simp add: projection_concatenation_commute)
          
        from \<open>\<gamma>\<^sub>1'\<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<gamma>\<^sub>1 \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> have "\<gamma>\<^sub>1'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = \<gamma>\<^sub>1\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>" 
          using projection_subset_eq_from_superset_eq sup_commute by metis
        hence "length(\<gamma>\<^sub>1'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>) = length(\<gamma>\<^sub>1\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>)" by simp
        moreover
        from \<open>\<gamma>\<^sub>2 \<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> \<open>\<gamma>\<^sub>2'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>=[]\<close> have "length(\<gamma>\<^sub>2'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>) = length(\<gamma>\<^sub>2\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>)"
          by simp
        ultimately
        have "n=length((\<gamma>\<^sub>1' @ \<gamma>\<^sub>2')\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>)" 
          by (simp add: \<open>n = length ((\<gamma>\<^sub>1 @ \<gamma>\<^sub>2) \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> projection_concatenation_commute)

          
      
        from \<open>\<beta>''' @ [c] @ \<gamma>\<^sub>1' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>(\<gamma>\<^sub>1' @ \<gamma>\<^sub>2')\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []\<close> \<open>n=length((\<gamma>\<^sub>1' @ \<gamma>\<^sub>2')\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> 
        have witness: 
        " \<exists>\<alpha>' \<beta>'. \<beta>' @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = ( \<gamma>\<^sub>1' @ \<gamma>\<^sub>2')  \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> 
                    \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = [] \<and> \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta>''' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)" 
          using Suc.hyps[OF \<open>\<beta>''' @ [c] @ \<gamma>\<^sub>1' @ \<gamma>\<^sub>2' \<in> Tr\<^bsub>ES\<^esub>\<close>] by simp
        
        from V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1  \<open>\<beta>'''  \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> 
        have "\<beta>'''  \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)"
          using non_empty_projection_on_subset by blast
          
        from  \<V>\<^sub>1IsViewOnE \<V>\<^sub>2IsViewOnE V2_subset_V1 C2_subset_C1  c\<^sub>1_in_C\<^sub>1 have "c\<^sub>1 \<notin> V\<^bsub>\<V>\<^sub>2\<^esub>"  
          unfolding isViewOn_def V_valid_def  VC_disjoint_def by auto
        with \<open>\<alpha> = \<gamma>\<^sub>1 @ [c\<^sub>1] @ \<gamma>\<^sub>2\<close> have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2) \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>"
          unfolding projection_def by auto
        moreover
        from V2_subset_V1 \<open>\<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub>\<close> have "\<gamma>\<^sub>2' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<gamma>\<^sub>2 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>"
           using V2_subset_V1 by (metis projection_subset_eq_from_superset_eq subset_Un_eq)
        moreover
        from \<open>\<gamma>\<^sub>1'\<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<gamma>\<^sub>1 \<upharpoonleft>(V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)\<close> have "\<gamma>\<^sub>1' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<gamma>\<^sub>1 \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>" 
          using V2_subset_V1 by (metis projection_subset_eq_from_superset_eq subset_Un_eq)
        ultimately  
        have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1' @ \<gamma>\<^sub>2') \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>" using \<open>\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1 @ \<gamma>\<^sub>2) \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>\<close>
          by (simp add: projection_concatenation_commute)

        from \<open>\<beta>'''  \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft>(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)\<close> \<open>\<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = (\<gamma>\<^sub>1' @ \<gamma>\<^sub>2') \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub>\<close>
        show ?case
          using witness by simp
     qed          
 }  
  thus ?thesis
    unfolding D_def by auto 
qed
end 

context BSPTaxonomyDifferentViewsSecondDim
begin
(* lemma taken from lemma 3.5.5 from Heiko Mantel's dissertation*)
lemma FCD_implies_FCD_for_modified_view_gamma: 
"\<lbrakk>FCD \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>; 
     V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub> \<rbrakk>
     \<Longrightarrow> FCD \<Gamma>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>" 
proof -
  assume "FCD \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
     and "V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
     and "N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>" 
     and "C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
  {
    fix \<alpha> \<beta> v c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "\<beta> @ [c,v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    
    from \<open>c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "c \<in>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from \<open>v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "v \<in>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from C2_equals_C1 \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []\<close> have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    ultimately
    obtain \<alpha>' \<delta>' where "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)"
                  and "\<beta> @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                  and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>"
                  and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      using \<open>\<beta> @ [c,v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>FCD \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>\<close> unfolding FCD_def by blast  
    
    from \<open>(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)\<close> \<open>N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> 
    have "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>)"
      by auto
    moreover
    from \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>\<close> V2_subset_V1 have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>" 
    using non_empty_projection_on_subset by blast
    moreover
    from C2_equals_C1 \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> have "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      by auto
    ultimately
    have "\<exists> \<delta>' \<alpha>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>) 
                         \<and> \<beta> @ \<delta>'@ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      using \<open>\<beta> @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by auto                
  }
  thus ?thesis
    unfolding FCD_def by blast
qed  

(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma SI_implies_SI_for_modified_view : 
"SI \<V>\<^sub>1 Tr\<^bsub>ES\<^esub> \<Longrightarrow> SI \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  SI: "SI \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    moreover
    with  C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    ultimately
    have "\<beta> @ (c # \<alpha>) \<in> Tr\<^bsub>ES\<^esub>"
      using SI  unfolding SI_def by auto
  }
  thus ?thesis
    unfolding SI_def by auto  
qed  


(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma BSI_implies_BSI_for_modified_view : 
"BSI \<V>\<^sub>1 Tr\<^bsub>ES\<^esub> \<Longrightarrow> BSI \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  BSI: "BSI \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    moreover
    with  C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    ultimately
    have "\<exists> \<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []" 
      using BSI  unfolding BSI_def by auto
    with V2_subset_V1  C2_equals_C1
    have "\<exists> \<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
      using non_empty_projection_on_subset by metis
  }
  thus ?thesis
    unfolding BSI_def by auto  
qed  

(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma I_implies_I_for_modified_view : 
"I \<V>\<^sub>1 Tr\<^bsub>ES\<^esub> \<Longrightarrow> I \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  I: "I \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
  from V2_subset_V1 C2_equals_C1 have V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1: "V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>"
    by auto
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    moreover
    with C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []" 
      by auto
    ultimately
    have "\<exists> \<alpha>' \<beta>'. 
            \<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = [] 
              \<and> \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
      using I  unfolding I_def by auto
    with  V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1 V2_subset_V1  C2_equals_C1
    have "\<exists> \<alpha>' \<beta>'. 
              \<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []  
                \<and> \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)" 
      using non_empty_projection_on_subset by metis
  }
  thus ?thesis
    unfolding I_def by auto  
qed  

(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma SIA_implies_SIA_for_modified_view : 
"\<lbrakk>SIA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>; \<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1) \<rbrakk> \<Longrightarrow> SIA \<rho>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  SIA: "SIA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
    and   \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1: "\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)" 
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      and admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2:"Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr\<^bsub>ES\<^esub> \<beta> c"
    moreover
    with  C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    moreover
    from \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1  admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2 have "Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr\<^bsub>ES\<^esub> \<beta> c" 
      by (simp add: Adm_implies_Adm_for_modified_rho)
    ultimately
    have "\<beta> @ (c # \<alpha>) \<in> Tr\<^bsub>ES\<^esub>"
      using SIA  unfolding SIA_def by auto
  }
  thus ?thesis
    unfolding SIA_def by auto  
qed  


(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma BSIA_implies_BSIA_for_modified_view : 
"\<lbrakk>BSIA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>; \<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1) \<rbrakk> \<Longrightarrow> BSIA \<rho>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  BSIA: "BSIA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
    and   \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1: "\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)" 
  from V2_subset_V1 C2_equals_C1
  have V\<^sub>2_union_C\<^sub>2_subset_V\<^sub>1_union_C\<^sub>1: "V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub> \<subseteq> V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>"
    by auto
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      and admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2:"Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr\<^bsub>ES\<^esub> \<beta> c"
    moreover
    with  C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    moreover
    from \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1  admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2 have "Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr\<^bsub>ES\<^esub> \<beta> c"
      by (simp add: Adm_implies_Adm_for_modified_rho)
    ultimately
    have "\<exists> \<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []" 
      using BSIA  unfolding BSIA_def by auto
    with V2_subset_V1  C2_equals_C1 
    have "\<exists> \<alpha>'. \<beta> @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []" 
      using non_empty_projection_on_subset by metis
  }
  thus ?thesis
    unfolding BSIA_def by auto  
qed  

(* lemma taken from lemma 3.5.10 in Heiko Mantel's dissertation*)
lemma IA_implies_IA_for_modified_view : 
"\<lbrakk>IA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>; \<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1) \<rbrakk> \<Longrightarrow> IA \<rho>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>"
proof -
  assume  IA: "IA \<rho>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
    and   \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1: "\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)" 
  {
    fix \<alpha> \<beta> c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>"
      and  "\<beta> @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
      and  alpha_C\<^sub>2_empty: "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      and admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2:"Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr\<^bsub>ES\<^esub> \<beta> c"
    moreover
    with C2_equals_C1 have "c \<in> C\<^bsub>\<V>\<^sub>1\<^esub>"
      by auto  
    moreover
    from   alpha_C\<^sub>2_empty C2_equals_C1 have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    moreover
    from \<rho>\<^sub>2_supseteq_\<rho>\<^sub>1  admissible_c_\<rho>\<^sub>2_\<V>\<^sub>2 have "Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr\<^bsub>ES\<^esub> \<beta> c"
      by (simp add: Adm_implies_Adm_for_modified_rho)
    ultimately
    have "\<exists> \<alpha>' \<beta>'. \<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>1\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>1\<^esub> = [] \<and> \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)" 
      using IA  unfolding IA_def by auto
    moreover
    from   V2_subset_V1 C2_equals_C1 have "(V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) \<subseteq>  (V\<^bsub>\<V>\<^sub>1\<^esub> \<union> C\<^bsub>\<V>\<^sub>1\<^esub>)"
      by auto 
    ultimately
    have "\<exists> \<alpha>' \<beta>'. \<beta>' @ [c] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>' \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>' \<upharpoonleft> C\<^bsub>\<V>\<^sub>2\<^esub> = []  \<and> \<beta>' \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>) = \<beta> \<upharpoonleft> (V\<^bsub>\<V>\<^sub>2\<^esub> \<union> C\<^bsub>\<V>\<^sub>2\<^esub>)" 
      using V2_subset_V1  C2_equals_C1   non_empty_projection_on_subset by metis
  }
  thus ?thesis
    unfolding IA_def by auto  
qed

(* lemma taken from lemma 3.5.14 from Heiko Mantel's dissertation*)
lemma FCI_implies_FCI_for_modified_view_gamma: 
"\<lbrakk>FCI \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>;
     V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub> \<rbrakk>
     \<Longrightarrow> FCI \<Gamma>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>" 
proof -
  assume "FCI \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
     and "V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
     and "N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>" 
     and "C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
  {
    fix \<alpha> \<beta> v c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
    
    from \<open>c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "c \<in>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from \<open>v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "v \<in>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from C2_equals_C1 \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []\<close> have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    ultimately 
    obtain \<alpha>' \<delta>' where "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)"
                  and "\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                  and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>"
                  and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      using \<open>\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>FCI \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>\<close> unfolding FCI_def by blast  
    
    from \<open>(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)\<close> \<open>N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> 
    have "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>)"
      by auto
    moreover
    from \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>\<close> V2_subset_V1 have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>" 
      using non_empty_projection_on_subset by blast
    moreover
    from \<open>C\<^bsub>\<V>\<^sub>2\<^esub> = C\<^bsub>\<V>\<^sub>1\<^esub>\<close> \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> have "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      by auto
    ultimately have "\<exists> \<delta>' \<alpha>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>) 
                         \<and> \<beta> @ [c] @  \<delta>'@ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
               using \<open>\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by auto                
  }
  thus ?thesis
    unfolding FCI_def by blast
qed  


(* lemma taken from lemma 3.5.14 from Heiko Mantel's dissertation*)
lemma FCIA_implies_FCIA_for_modified_view_rho_gamma: 
"\<lbrakk>FCIA \<rho>\<^sub>1 \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>; \<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1);
     V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>;  C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub> \<rbrakk>
     \<Longrightarrow> FCIA \<rho>\<^sub>2 \<Gamma>\<^sub>2 \<V>\<^sub>2 Tr\<^bsub>ES\<^esub>" 
proof -
  assume "FCIA \<rho>\<^sub>1 \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>"
     and "\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)"
     and "V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
     and "N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>" 
     and "C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
  {
    fix \<alpha> \<beta> v c
    assume "c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>"
       and "\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>"
       and "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
       and "Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr\<^bsub>ES\<^esub> \<beta> c"
    
    from \<open>c \<in> C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>C\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "c \<in>  C\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Upsilon>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from \<open>v \<in> V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub>\<close> \<open>V\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<subseteq>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> have "v \<in>  V\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<nabla>\<^bsub>\<Gamma>\<^sub>1\<^esub>"
      by auto
    moreover
    from C2_equals_C1 \<open>\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []\<close> have "\<alpha>\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      by auto
    moreover
    from \<open>Adm \<V>\<^sub>2 \<rho>\<^sub>2 Tr\<^bsub>ES\<^esub> \<beta> c\<close> \<open>\<rho>\<^sub>2(\<V>\<^sub>2) \<supseteq> \<rho>\<^sub>1(\<V>\<^sub>1)\<close> have "Adm \<V>\<^sub>1 \<rho>\<^sub>1 Tr\<^bsub>ES\<^esub> \<beta> c" 
       by (simp add: Adm_implies_Adm_for_modified_rho)
    ultimately
    obtain \<alpha>' \<delta>' where "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)"
                  and "\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>"
                  and "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>"
                  and "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []"
      using \<open>\<beta> @ [v] @ \<alpha> \<in> Tr\<^bsub>ES\<^esub>\<close> \<open>FCIA \<rho>\<^sub>1 \<Gamma>\<^sub>1 \<V>\<^sub>1 Tr\<^bsub>ES\<^esub>\<close> unfolding FCIA_def by blast  
    
    from \<open>(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>1\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>)\<close> \<open>N\<^bsub>\<V>\<^sub>2\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub> \<supseteq>  N\<^bsub>\<V>\<^sub>1\<^esub>\<inter>\<Delta>\<^bsub>\<Gamma>\<^sub>1\<^esub>\<close> 
    have "(set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>)"
      by auto
    moreover
    from \<open>\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>1\<^esub>\<close> V2_subset_V1 have "\<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub>" 
      using non_empty_projection_on_subset by blast
    moreover
    from \<open>C\<^bsub>\<V>\<^sub>2\<^esub> = C\<^bsub>\<V>\<^sub>1\<^esub>\<close> \<open>\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>1\<^esub> = []\<close> have "\<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      by auto
    ultimately
    have "\<exists> \<delta>' \<alpha>'. (set \<delta>') \<subseteq> (N\<^bsub>\<V>\<^sub>2\<^esub> \<inter> \<Delta>\<^bsub>\<Gamma>\<^sub>2\<^esub>) 
                         \<and> \<beta> @ [c] @  \<delta>'@ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub> \<and> \<alpha>'\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> = \<alpha>\<upharpoonleft>V\<^bsub>\<V>\<^sub>2\<^esub> \<and> \<alpha>'\<upharpoonleft>C\<^bsub>\<V>\<^sub>2\<^esub> = []"
      using \<open>\<beta> @ [c] @ \<delta>' @ [v] @ \<alpha>' \<in> Tr\<^bsub>ES\<^esub>\<close> by auto                
  }
  thus ?thesis
    unfolding FCIA_def by blast
qed   
end

end
