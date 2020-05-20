(*  Title:      statecharts/DataSpace/Update.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Update-Functions on Data Spaces\<close>
theory Update
imports Data
begin

subsection \<open>Total update-functions\<close>

definition
  Update :: "(('d data) => ('d data)) => bool" where 
  "Update U = (\<forall> d. Data.DataSpace d = DataSpace (U d))"

lemma Update_EmptySet: 
 "(% d. d) \<in> { L | L. Update L}" 
by (unfold Update_def, auto)

definition
  "update = { L | (L::(('d data) => ('d data))). Update L}"

typedef 'd update = "update :: ('d data => 'd data) set"
  unfolding update_def
  apply (rule exI)
  apply (rule Update_EmptySet)
  done
 
definition
 UpdateApply :: "['d update, 'd data] => 'd data" ("(_ !!!/ _)" [10,11]10) where
 "UpdateApply U D == Rep_update U D" 

definition
  DefaultUpdate :: "('d update)" where
 "DefaultUpdate ==  Abs_update (\<lambda> D. D)"

subsubsection \<open>Basic lemmas\<close>

lemma Update_select:
   "Update (Rep_update U)"
apply (cut_tac x=U in Rep_update)
apply (unfold update_def)
apply auto
done

lemma DataSpace_DataSpace_Update [simp]:
   "Data.DataSpace (Rep_update U DP) = Data.DataSpace DP"
apply (cut_tac U=U in Update_select)
apply (unfold Update_def)
apply auto
done

subsubsection \<open>\<open>DefaultUpdate\<close>\<close>

lemma Update_DefaultUpdate [simp]:
   "Update (\<lambda> D. D)"
by (unfold Update_def, auto)

lemma update_DefaultUpdate [simp]:
   "(\<lambda> D. D) \<in> update"
by (unfold update_def, auto)

lemma DataSpace_UpdateApply [simp]:
   "Data.DataSpace (U !!! D) = Data.DataSpace D"
by (unfold UpdateApply_def, auto)

subsection \<open>Partial update-functions\<close>

definition
  PUpdate :: "(('d data) => ('d pdata)) => bool" where
  "PUpdate U = (\<forall> d. Data.DataSpace d = PDataSpace (U d))"

lemma PUpdate_EmptySet:
 "(% d. Data2PData d) \<in> { L | L. PUpdate L}" 
by (unfold PUpdate_def, auto)

definition "pupdate = { L | (L::(('d data) => ('d pdata))). PUpdate L}"

typedef 'd pupdate = "pupdate :: ('d data => 'd pdata) set" 
  unfolding pupdate_def
  apply (rule exI)
  apply (rule PUpdate_EmptySet)
  done
 
definition
 PUpdateApply :: "['d pupdate, 'd data] => 'd pdata" ("(_ !!/ _)" [10,11]10) where
 "PUpdateApply U D = Rep_pupdate U D" 

definition
  DefaultPUpdate :: "('d pupdate)" where
 "DefaultPUpdate = Abs_pupdate (\<lambda> D. DefaultPData (Data.DataSpace D))"
                      
subsubsection \<open>Basic lemmas\<close>

lemma PUpdate_select:
   "PUpdate (Rep_pupdate U)"
apply (cut_tac x=U in Rep_pupdate)
apply (unfold pupdate_def)
apply auto
done

lemma DataSpace_PDataSpace_PUpdate [simp]:
   "PDataSpace (Rep_pupdate U DP) = Data.DataSpace DP"
apply (cut_tac U=U in PUpdate_select)
apply (unfold PUpdate_def)
apply auto
done

subsubsection \<open>\<open>Data2PData\<close>\<close>

lemma  PUpdate_Data2PData [simp]: 
   "PUpdate Data2PData"
by (unfold PUpdate_def, auto)

lemma pupdate_Data2PData  [simp]:
   "Data2PData \<in> pupdate"
by (unfold pupdate_def, auto)

subsubsection \<open>\<open>PUpdate\<close>\<close>

lemma PUpdate_DefaultPUpdate [simp]:
   "PUpdate (\<lambda> D. DefaultPData (Data.DataSpace D))"
apply (unfold PUpdate_def)
apply auto
done

lemma pupdate_DefaultPUpdate [simp]:
   "(\<lambda> D. DefaultPData (Data.DataSpace D)) \<in> pupdate"
apply (unfold pupdate_def)
apply auto
done

lemma DefaultPUpdate_None [simp]:
    "(DefaultPUpdate !! D) = DefaultPData (DataSpace D)"
apply (unfold DefaultPUpdate_def PUpdateApply_def)
apply (subst Abs_pupdate_inverse)
apply auto
done

subsubsection \<open>\<open>SequentialRacing\<close>\<close>

definition
 UpdateOverride :: "['d pupdate, 'd update] => 
                     'd update" ("(_ [U+]/ _)" [10,11]10) where
 "UpdateOverride U P = Abs_update (\<lambda> DA . (U !! DA) [D+] (P !!! DA))"
 

(* -------------------------------------------------------------- *)
(* We use our own FoldSet operator simular to the definition      *)
(* of Isabelle 2002. Note, it is different to the definition      *)
(* in Isabelle 2009. Basically we express "f (g x)" by "h x"      *)
(* -------------------------------------------------------------- *)

inductive
  FoldSet :: "('b => 'a => 'a) => 'a => 'b set => 'a => bool"
  for h ::  "'b => 'a => 'a"
  and z :: 'a
where
  emptyI [intro]: "FoldSet h z {} z"
| insertI [intro]:
     "\<lbrakk> x \<notin> A; FoldSet h z A y \<rbrakk>
      \<Longrightarrow> FoldSet h z (insert x A) (h x y)"

definition
SequentialRacing :: "('d pupdate set) => ('d update set)" where
 "SequentialRacing U = 
     {u. FoldSet UpdateOverride DefaultUpdate U u}"

lemma FoldSet_imp_finite:
  "FoldSet h z A x \<Longrightarrow> finite A"
by (induct set: FoldSet) auto

lemma finite_imp_FoldSet:
  "finite A \<Longrightarrow> \<exists> x. FoldSet h z A x"
by (induct set: finite) auto

lemma finite_SequentialRacing:
   "finite US \<Longrightarrow> (SOME u. u \<in> SequentialRacing US) \<in> SequentialRacing US"
apply (unfold SequentialRacing_def)
apply auto
apply (drule_tac h=UpdateOverride and z=DefaultUpdate in finite_imp_FoldSet)
apply auto
apply (rule someI)
apply auto
done


end
