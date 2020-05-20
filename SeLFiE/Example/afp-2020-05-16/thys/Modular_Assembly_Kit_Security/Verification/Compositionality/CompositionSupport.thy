theory CompositionSupport
imports CompositionBase
begin

locale CompositionSupport =
fixes ESi :: "'e ES_rec"
and \<V> :: "'e V_rec"
and \<V>i :: "'e V_rec"

(* assumption about the component event system *)
assumes validESi: "ES_valid ESi"

(* assumption about the views (part of proper separation) *)
and validVi: "isViewOn \<V>i E\<^bsub>ESi\<^esub>"
and Vv_inter_Ei_is_Vvi: "V\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ESi\<^esub> = V\<^bsub>\<V>i\<^esub>"
and Cv_inter_Ei_subsetof_Cvi: "C\<^bsub>\<V>\<^esub> \<inter> E\<^bsub>ESi\<^esub> \<subseteq> C\<^bsub>\<V>i\<^esub>"

(* sublocale relations for CompositionSupport *)

(* body of CompositionSupport *)
context CompositionSupport
begin

(* This lemma is used in the compositionality proof for BSD.
  Assuming that BSD holds for a subsystem ESi and given a trace \<beta> @ [c] @ \<alpha> of the composed system,
  we can obtain a trace (\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ \<alpha>_i' of ESi where \<alpha>_i' contains no 
  events that are confidential in ESi and (\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) holds.
  
 \<V> and \<V>i denote views on the composition and subsystem respectively.
  We assume that \<V> and \<V>i are properly separated. *)
lemma BSD_in_subsystem:
"\<lbrakk> c \<in> C\<^bsub>\<V>\<^esub>; ((\<beta> @ [c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ESi\<^esub>) \<in> Tr\<^bsub>ESi\<^esub> ; BSD \<V>i Tr\<^bsub>ESi\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists>\<alpha>_i'. ( ((\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ \<alpha>_i') \<in> Tr\<^bsub>ESi\<^esub> 
  \<and> (\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) \<and> \<alpha>_i' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = [] )"
proof (induct "length (([c] @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)" arbitrary: \<beta> c \<alpha>)
  case 0
  (* show that ([c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ESi\<^esub> is a suitable choice for \<alpha>_i' *)
  let ?L = "([c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ESi\<^esub>"
  
  from 0(3) have \<beta>_E1_c\<alpha>_E1_in_Tr1: "((\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ (([c] @ \<alpha>) \<upharpoonleft> E\<^bsub>ESi\<^esub>)) \<in> Tr\<^bsub>ESi\<^esub>"
    by (simp only: projection_concatenation_commute)
  moreover
  have "(?L \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>)"
  proof -
    have "(?L \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = ([c] @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      from validVi have "E\<^bsub>ESi\<^esub> \<inter> V\<^bsub>\<V>i\<^esub> = V\<^bsub>\<V>i\<^esub>"
        by (simp add: isViewOn_def V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def 
          , auto)
      moreover
      have "(?L \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = ([c] @ \<alpha>) \<upharpoonleft> (E\<^bsub>ESi\<^esub> \<inter> V\<^bsub>\<V>i\<^esub>)"
        by (simp add: projection_def)
      ultimately show ?thesis
        by auto
    qed
    moreover
    have "([c] @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      have "([c] @ \<alpha>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = ([c] \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) @ (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>)"
        by (rule projection_concatenation_commute)
      moreover
      have "([c] \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = []"
      proof -
        from 0(2) have "[c] \<upharpoonleft> C\<^bsub>\<V>\<^esub> = [c]"
          by (simp add: projection_def)
        moreover
        have "[c] \<upharpoonleft> C\<^bsub>\<V>\<^esub> \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = []"
        proof -
          from validVi Cv_inter_Ei_subsetof_Cvi have "C\<^bsub>\<V>\<^esub> \<inter> V\<^bsub>\<V>i\<^esub> \<subseteq> C\<^bsub>\<V>i\<^esub>"
            by (simp add: isViewOn_def  V_valid_def VC_disjoint_def, auto)
          moreover
          from 0(1) have "[c] \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
            by (simp only: projection_concatenation_commute, auto)
          ultimately have "[c] \<upharpoonleft> (C\<^bsub>\<V>\<^esub> \<inter> V\<^bsub>\<V>i\<^esub>) = []"
            by (rule projection_on_subset)
          thus ?thesis
            by (simp only: projection_def, auto)
        qed
        ultimately show ?thesis
          by auto
      qed
      ultimately show ?thesis
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
  moreover
  have "?L \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
  proof -
    from 0(1) have "([c] @ \<alpha>) \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
      by auto
    hence "([c] @ \<alpha>) \<upharpoonleft> (C\<^bsub>\<V>i\<^esub> \<inter> E\<^bsub>ESi\<^esub>) = []"
      by (rule projection_on_intersection)
    hence "([c] @ \<alpha>) \<upharpoonleft> (E\<^bsub>ESi\<^esub> \<inter> C\<^bsub>\<V>i\<^esub>) = []"
      by (simp only: Int_commute)
    thus ?thesis
      by (simp only: projection_def, auto)                
  qed
  ultimately show ?case
    by auto
  
next
  case (Suc n)
  
  from projection_split_last[OF Suc(2)] obtain \<gamma> c_i \<delta>
    where c_i_in_C\<V>i: "c_i \<in> C\<^bsub>\<V>i\<^esub>"
    and   c\<alpha>_is_\<gamma>c_i\<delta>: "[c] @ \<alpha> = \<gamma> @ [c_i] @ \<delta>"
    and   \<delta>_no_C\<V>i:  "\<delta> \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
    and   n_is_len_\<gamma>\<delta>_C\<V>i: "n = length ((\<gamma> @ \<delta>) \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)"
    by auto
  
  let ?L1 = "((\<beta> @ \<gamma>) \<upharpoonleft> E\<^bsub>ESi\<^esub>)"
  let ?L2 = "(\<delta> \<upharpoonleft> E\<^bsub>ESi\<^esub>)"

  note c_i_in_C\<V>i
  moreover
  have list_with_c_i_in_Tr1: "(?L1 @ [c_i] @ ?L2) \<in> Tr\<^bsub>ESi\<^esub>"
  proof -
    from c_i_in_C\<V>i validVi have "[c_i] \<upharpoonleft> E\<^bsub>ESi\<^esub> = [c_i]"
      by (simp only: isViewOn_def V_valid_def VC_disjoint_def
        VN_disjoint_def NC_disjoint_def projection_def, auto)
    moreover
    from Suc(4) c\<alpha>_is_\<gamma>c_i\<delta> have "((\<beta> @ \<gamma> @ [c_i] @ \<delta>) \<upharpoonleft> E\<^bsub>ESi\<^esub>) \<in> Tr\<^bsub>ESi\<^esub>"
      by auto
    hence "(?L1 @ ([c_i] \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ ?L2) \<in> Tr\<^bsub>ESi\<^esub>"
      by (simp only: projection_def, auto)
    ultimately show ?thesis
      by auto
  qed
  moreover 
  have "?L2 \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
  proof -
    from validVi have "\<And>x. (x \<in> E\<^bsub>ESi\<^esub> \<and> x \<in> C\<^bsub>\<V>i\<^esub>) = (x \<in> C\<^bsub>\<V>i\<^esub>)"
      by (simp add: isViewOn_def V_valid_def VC_disjoint_def
        VN_disjoint_def NC_disjoint_def, auto)
    with \<delta>_no_C\<V>i show ?thesis
      by (simp add: projection_def)
  qed            
  moreover note Suc(5)
  ultimately obtain \<delta>'
    where \<delta>'_1: "(?L1 @ \<delta>') \<in> Tr\<^bsub>ESi\<^esub>"
    and \<delta>'_2: "\<delta>' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = ?L2 \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    and \<delta>'_3: "\<delta>' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
    unfolding BSD_def
    by blast
  hence \<delta>'_2': "\<delta>' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
  proof -
    have "?L2 \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      from validVi have "\<And>x. (x \<in> E\<^bsub>ESi\<^esub> \<and> x \<in> V\<^bsub>\<V>i\<^esub>) = (x \<in> V\<^bsub>\<V>i\<^esub>)"
        by (simp add: isViewOn_def V_valid_def VC_disjoint_def
        VN_disjoint_def NC_disjoint_def, auto)
      thus ?thesis
        by (simp add: projection_def)
    qed
    with \<delta>'_2 show ?thesis
      by auto
  qed
  
  show ?case
  proof (cases \<gamma>) (* need to distinguish between these cases as the inductive 
      hypothesis can only be applied to one case. *)
    case Nil
    with c\<alpha>_is_\<gamma>c_i\<delta> have "[c] @ \<alpha> = [c_i] @ \<delta>"
      by auto
    hence \<delta>_is_\<alpha>: "\<delta> = \<alpha>"
      by auto
    
    from \<delta>'_1 have \<delta>'_1': "((\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ \<delta>') \<in> Tr\<^bsub>ESi\<^esub>"
      by (simp only: Nil, auto)
    moreover
    note \<delta>'_2'
    moreover note \<delta>'_3
    ultimately show ?thesis
      by (simp only: \<delta>_is_\<alpha>, auto)
  next
    case (Cons x \<gamma>')
    with c\<alpha>_is_\<gamma>c_i\<delta> have \<gamma>_is_c\<gamma>': "\<gamma> = [c] @ \<gamma>'"
      by simp
    with n_is_len_\<gamma>\<delta>_C\<V>i have "n = length (([c] @ \<gamma>' @ \<delta>) \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)"
      by auto
    with \<delta>_no_C\<V>i \<delta>'_3 have "n = length (([c] @ \<gamma>' @ \<delta>') \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)"
      by (simp only: projection_concatenation_commute)
    moreover
    note Suc(3)
    moreover
    have "((\<beta> @ [c] @ (\<gamma>' @ \<delta>')) \<upharpoonleft> E\<^bsub>ESi\<^esub>) \<in> Tr\<^bsub>ESi\<^esub>"
    proof -
      from \<delta>'_1 validESi have "\<delta>' = \<delta>' \<upharpoonleft> E\<^bsub>ESi\<^esub>"
      proof -
        let ?L = "(\<beta> @ \<gamma>) \<upharpoonleft> E\<^bsub>ESi\<^esub> @ \<delta>'"
        
        from \<delta>'_1 validESi have "\<forall>e \<in> set ?L. e \<in> E\<^bsub>ESi\<^esub>"
          by (simp add: ES_valid_def traces_contain_events_def)
        hence "set \<delta>' \<subseteq> E\<^bsub>ESi\<^esub>"
          by auto
        thus ?thesis
          by (simp add: list_subset_iff_projection_neutral)
      qed
      with \<delta>'_1  have "?L1 @ \<delta>' = (\<beta> @ \<gamma> @ \<delta>') \<upharpoonleft> E\<^bsub>ESi\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      with \<gamma>_is_c\<gamma>' \<delta>'_1  show ?thesis
        by auto
    qed
    moreover
    note Suc(5)
    moreover note Suc(1)[of c "\<gamma>' @ \<delta>'" \<beta>]
    ultimately obtain \<alpha>_i'
      where \<alpha>_i'_1: "\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub> @ \<alpha>_i' \<in> Tr\<^bsub>ESi\<^esub>"
      and \<alpha>_i'_2: "\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma>' @ \<delta>') \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
      and \<alpha>_i'_3: "\<alpha>_i' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
      by auto
    moreover
    have "\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma>' @ \<delta>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
      proof -
        from c\<alpha>_is_\<gamma>c_i\<delta> \<gamma>_is_c\<gamma>' have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma>' @ [c_i] @ \<delta>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
          by simp
        with validVi c_i_in_C\<V>i show ?thesis
          by (simp only: isViewOn_def V_valid_def  VC_disjoint_def
            VN_disjoint_def NC_disjoint_def projection_concatenation_commute 
            projection_def, auto)
      qed
      moreover
      from \<alpha>_i'_2 \<delta>'_2' have "\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma>' @ \<delta>) \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
        by (simp only: projection_concatenation_commute)
      ultimately show ?thesis
        by auto
    qed
    ultimately show ?thesis
      by auto
  qed
qed

(*
    Variant of the previous lemma with different propositions (note the lack of a confidential event c).
*)
lemma BSD_in_subsystem2:
"\<lbrakk> ((\<beta> @ \<alpha>) \<upharpoonleft> E\<^bsub>ESi\<^esub>) \<in> Tr\<^bsub>ESi\<^esub> ; BSD \<V>i Tr\<^bsub>ESi\<^esub> \<rbrakk> 
  \<Longrightarrow> \<exists> \<alpha>_i'. ( ((\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ \<alpha>_i') \<in> Tr\<^bsub>ESi\<^esub> \<and> (\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) \<and> \<alpha>_i' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = [] )"
proof (induct "length (\<alpha> \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)" arbitrary: \<beta> \<alpha>)
  case 0
  (* show that \<alpha> \<upharpoonleft> E\<^bsub>ESi\<^esub>  is a suitable choice for \<alpha>_i' *)
  let ?L = "\<alpha> \<upharpoonleft> E\<^bsub>ESi\<^esub>"
  
  from 0(2) have \<beta>_E1_\<alpha>_E1_in_Tr1: "((\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ ?L) \<in> Tr\<^bsub>ESi\<^esub>"
    by (simp only: projection_concatenation_commute)
  moreover
  have "(?L \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = (\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>)"
    proof -
      from validVi have "E\<^bsub>ESi\<^esub> \<inter> V\<^bsub>\<V>i\<^esub> = V\<^bsub>\<V>i\<^esub>"
        by (simp add: isViewOn_def V_valid_def  VC_disjoint_def
        VN_disjoint_def NC_disjoint_def, auto)
      moreover
      have "(?L \<upharpoonleft> V\<^bsub>\<V>i\<^esub>) = \<alpha> \<upharpoonleft> (E\<^bsub>ESi\<^esub> \<inter> V\<^bsub>\<V>i\<^esub>)"
        by (simp add: projection_def)
      ultimately show ?thesis
        by auto
    qed
  moreover
  have "?L \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
  proof -
    from 0(1) have "\<alpha> \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
      by auto
    hence "\<alpha> \<upharpoonleft> (C\<^bsub>\<V>i\<^esub> \<inter> E\<^bsub>ESi\<^esub>) = []"
      by (rule projection_on_intersection)
    hence "\<alpha> \<upharpoonleft> (E\<^bsub>ESi\<^esub> \<inter> C\<^bsub>\<V>i\<^esub>) = []"
      by (simp only: Int_commute)
    thus ?thesis
      by (simp only: projection_def, auto)                
  qed
  ultimately show ?case
    by auto
  
next
  case (Suc n)
  
  from projection_split_last[OF Suc(2)] obtain \<gamma> c_i \<delta>
    where c_i_in_C\<V>i: "c_i \<in> C\<^bsub>\<V>i\<^esub>"
    and   \<alpha>_is_\<gamma>c_i\<delta>: "\<alpha> = \<gamma> @ [c_i] @ \<delta>"
    and   \<delta>_no_C\<V>i:  "\<delta> \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
    and   n_is_len_\<gamma>\<delta>_C\<V>i: "n = length ((\<gamma> @ \<delta>) \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)"
    by auto
  
  let ?L1 = "((\<beta> @ \<gamma>) \<upharpoonleft> E\<^bsub>ESi\<^esub>)"
  let ?L2 = "(\<delta> \<upharpoonleft> E\<^bsub>ESi\<^esub>)"


  (* first apply BSD to get rid of c_i in \<alpha> *)
  note c_i_in_C\<V>i
  moreover
  have list_with_c_i_in_Tr1: "(?L1 @ [c_i] @ ?L2) \<in> Tr\<^bsub>ESi\<^esub>"
  proof -
    from c_i_in_C\<V>i validVi have "[c_i] \<upharpoonleft> E\<^bsub>ESi\<^esub> = [c_i]"
      by (simp only: isViewOn_def V_valid_def  VC_disjoint_def
        VN_disjoint_def NC_disjoint_def projection_def, auto)
    moreover
    from Suc(3) \<alpha>_is_\<gamma>c_i\<delta> have "((\<beta> @ \<gamma> @ [c_i] @ \<delta>) \<upharpoonleft> E\<^bsub>ESi\<^esub>) \<in> Tr\<^bsub>ESi\<^esub>"
      by auto
    hence "(?L1 @ ([c_i] \<upharpoonleft> E\<^bsub>ESi\<^esub>) @ ?L2) \<in> Tr\<^bsub>ESi\<^esub>"
      by (simp only: projection_def, auto)
    ultimately show ?thesis
      by auto
  qed
  moreover 
  have "?L2 \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
  proof -
    from validVi have "\<And>x. (x \<in> E\<^bsub>ESi\<^esub> \<and> x \<in> C\<^bsub>\<V>i\<^esub>) = (x \<in> C\<^bsub>\<V>i\<^esub>)"
      by (simp add: isViewOn_def V_valid_def  VC_disjoint_def
        VN_disjoint_def NC_disjoint_def, auto)
    with \<delta>_no_C\<V>i show ?thesis
      by (simp add: projection_def)
  qed            
  moreover note Suc(4)
  ultimately obtain \<delta>'
    where \<delta>'_1: "(?L1 @ \<delta>') \<in> Tr\<^bsub>ESi\<^esub>"
    and \<delta>'_2: "\<delta>' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = ?L2 \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    and \<delta>'_3: "\<delta>' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
    unfolding BSD_def
    by blast
  hence \<delta>'_2': "\<delta>' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
  proof -
    have "?L2 \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<delta> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      from validVi have "\<And>x. (x \<in> E\<^bsub>ESi\<^esub> \<and> x \<in> V\<^bsub>\<V>i\<^esub>) = (x \<in> V\<^bsub>\<V>i\<^esub>)"
        by (simp add: isViewOn_def V_valid_def  VC_disjoint_def
        VN_disjoint_def NC_disjoint_def, auto)
      thus ?thesis
        by (simp add: projection_def)
    qed
    with \<delta>'_2 show ?thesis
      by auto
  qed

  (* now that we eliminated c_i, we can apply the inductive hypothesis for ?\<beta> = \<beta> and ?\<alpha> = \<gamma> @ \<delta>' *)
  from n_is_len_\<gamma>\<delta>_C\<V>i \<delta>_no_C\<V>i \<delta>'_3 have "n = length ((\<gamma> @ \<delta>') \<upharpoonleft> C\<^bsub>\<V>i\<^esub>)"
    by (simp add: projection_concatenation_commute)
  moreover
  have "(\<beta> @ (\<gamma> @ \<delta>')) \<upharpoonleft> E\<^bsub>ESi\<^esub> \<in> Tr\<^bsub>ESi\<^esub>"
    proof -
      have "\<delta>' = \<delta>' \<upharpoonleft> E\<^bsub>ESi\<^esub>"
        proof -
          let ?L = "(\<beta> @ \<gamma>) \<upharpoonleft> E\<^bsub>ESi\<^esub> @ \<delta>'"
        
          from \<delta>'_1 validESi have "\<forall>e \<in> set ?L. e \<in> E\<^bsub>ESi\<^esub>"
            by (simp add: ES_valid_def traces_contain_events_def)
          hence "set \<delta>' \<subseteq> E\<^bsub>ESi\<^esub>"
            by auto
          thus ?thesis
            by (simp add: list_subset_iff_projection_neutral)
        qed
      with \<delta>'_1  have "?L1 @ \<delta>' = (\<beta> @ \<gamma> @ \<delta>') \<upharpoonleft> E\<^bsub>ESi\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      with \<delta>'_1  show ?thesis
        by auto
    qed
  moreover
  note Suc(4) Suc(1)[of "\<gamma> @ \<delta>'" \<beta>] 
  ultimately obtain \<alpha>_i' 
    where res1: "\<beta> \<upharpoonleft> E\<^bsub>ESi\<^esub> @ \<alpha>_i' \<in> Tr\<^bsub>ESi\<^esub>" 
    and res2: "\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma> @ \<delta>') \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    and res3: "\<alpha>_i' \<upharpoonleft> C\<^bsub>\<V>i\<^esub> = []"
    by auto

  (* Show that the resulting \<alpha>_i' is suitable *)
  have "\<alpha>_i' \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = \<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
    proof -
      from c_i_in_C\<V>i validVi have "[c_i] \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = []"
        by (simp add: isViewOn_def V_valid_def  VC_disjoint_def
        VN_disjoint_def NC_disjoint_def projection_def, auto)
      with \<alpha>_is_\<gamma>c_i\<delta> \<delta>'_2' have "\<alpha> \<upharpoonleft> V\<^bsub>\<V>i\<^esub> = (\<gamma> @ \<delta>') \<upharpoonleft> V\<^bsub>\<V>i\<^esub>"
        by (simp only: projection_concatenation_commute, auto)
      with res2 show ?thesis
        by auto
    qed
  with res1 res3 show ?case
    by auto
qed

end

end
