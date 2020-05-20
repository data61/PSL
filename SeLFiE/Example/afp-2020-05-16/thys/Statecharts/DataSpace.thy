(*  Title:      statecharts/DataSpace/DataSpace.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Partitoned Data Spaces for Statecharts\<close>
theory DataSpace
imports Contrib
begin

subsection \<open>Definitions\<close>

definition
  DataSpace :: "('d set) list
                => bool" where
  "DataSpace L = ((distinct L) \<and> 
                  (\<forall> D1\<in>(set L). \<forall> D2\<in>(set L).
                             D1 \<noteq> D2 \<longrightarrow> ((D1 \<inter> D2) = {})) \<and>
                  ((\<Union> (set L)) = UNIV))"

lemma DataSpace_EmptySet:
 "[UNIV] \<in> { L | L. DataSpace L }"
by (unfold DataSpace_def, auto)

definition "dataspace = { L | (L::('d set) list). DataSpace L}"

typedef 'd dataspace = "dataspace :: 'd set list set"
  unfolding dataspace_def
  apply (rule exI)
  apply (rule DataSpace_EmptySet)
  done

definition
 PartNum :: "('d)dataspace => nat" where
 "PartNum = length o Rep_dataspace"

definition
 PartDom :: "['d dataspace, nat] => ('d set)" (infixl "!D!" 101) where
 "PartDom d n = (Rep_dataspace d) ! n" 

subsection \<open>Lemmas\<close>

subsubsection \<open>\<open>DataSpace\<close>\<close>

lemma DataSpace_UNIV [simp]:
 "DataSpace [UNIV]"
by (unfold DataSpace_def, auto)

lemma DataSpace_select: 
 "DataSpace (Rep_dataspace L)"
apply (cut_tac x=L in  Rep_dataspace) 
apply (unfold dataspace_def)
apply auto
done

lemma UNIV_dataspace [simp]: 
  "[UNIV] \<in> dataspace"
by (unfold dataspace_def, auto)

lemma Inl_Inr_DataSpace [simp]:
  "DataSpace [Part UNIV Inl, Part UNIV Inr]"
apply (unfold DataSpace_def)
apply auto
apply (rename_tac d)
apply (rule_tac b="(inv Inl) d" in Part_eqI)
apply auto
apply (rule sym)
apply (case_tac d)
apply auto
done

lemma Inl_Inr_dataspace [simp]:
  "[Part UNIV Inl, Part UNIV Inr] \<in> dataspace"
by (unfold dataspace_def, auto)

lemma InlInr_InlInl_Inr_DataSpace [simp]:
  "DataSpace [Part UNIV (Inl o Inr), Part UNIV (Inl o Inl), Part UNIV Inr]"
apply (unfold DataSpace_def)
apply auto
apply (unfold Part_def)
apply auto
apply (rename_tac x)
apply (case_tac x)
apply auto
apply (rename_tac a)
apply (case_tac a)
apply auto
done

lemma InlInr_InlInl_Inr_dataspace [simp]:
  "[Part UNIV (Inl o Inr), Part UNIV (Inl o Inl), Part UNIV Inr] : dataspace"
by (unfold dataspace_def, auto)

subsubsection \<open>\<open>PartNum\<close>\<close>

lemma PartDom_PartNum_distinct: 
      "\<lbrakk> i < PartNum d; j < PartNum d;        
         i \<noteq> j; p \<in>  (d !D! i) \<rbrakk> \<Longrightarrow>
         p \<notin> (d !D! j)"
apply auto
apply (cut_tac L=d in DataSpace_select)
apply (unfold DataSpace_def) 
apply auto
apply (erule_tac x="Rep_dataspace d ! i" in ballE)
apply (erule_tac x="Rep_dataspace d ! j" in ballE)
apply auto
apply (simp add:distinct_conv_nth PartNum_def)
apply (unfold PartDom_def PartNum_def)
apply auto
done

lemma PartDom_PartNum_distinct2: 
      "\<lbrakk> i < PartNum d; j < PartNum d;       
         i \<noteq> j; p \<in>  (d !D! j) \<rbrakk> \<Longrightarrow>
        p \<notin> (d !D! i)"
apply auto
apply (cut_tac L=d in DataSpace_select)
apply (unfold DataSpace_def) 
apply auto
apply (erule_tac x="Rep_dataspace d ! i" in ballE)
apply (erule_tac x="Rep_dataspace d ! j" in ballE)
apply auto
apply (simp add:distinct_conv_nth PartNum_def)
apply (unfold PartDom_def PartNum_def)
apply auto
done

lemma PartNum_length [simp]: 
  "(DataSpace L) \<Longrightarrow> (PartNum (Abs_dataspace L) = (length L))"
apply (unfold PartNum_def)
apply auto
apply (subst Abs_dataspace_inverse)
apply (unfold dataspace_def)
apply auto
done

end
