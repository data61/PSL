(*  Title:      statecharts/DataSpace/Data.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Data Space Assignments\<close>
theory Data
imports DataSpace
begin

subsection \<open>Total data space assignments\<close>

definition
  Data :: "['d list, 'd dataspace]
                => bool" where
  "Data L D = (((length L) = (PartNum D)) \<and>
               (\<forall> i \<in> {n. n < (PartNum D)}. (L!i) \<in> (PartDom D i)))"

lemma Data_EmptySet: 
    "([@ t. True], Abs_dataspace [UNIV])\<in> { (L,D) | L D. Data L D }"
apply (unfold Data_def PartDom_def)
apply auto
apply (subst Abs_dataspace_inverse)
apply auto
done

definition
  "data =
    { (L,D) |
             (L::('d list))
             (D::('d dataspace)).
              Data L D }"

typedef 'd data = "data :: ('d list * 'd dataspace) set"
  unfolding data_def
  apply (rule exI)
  apply (rule Data_EmptySet)
  done

definition
 DataValue :: "('d data) => ('d list)" where
 "DataValue = fst o Rep_data"

definition
 DataSpace :: "('d data) => ('d dataspace)" where
 "DataSpace = snd o Rep_data"

definition
 DataPart :: "['d data, nat] => 'd" ("(_ !P!/ _)" [10,11]10) where
 "DataPart d n = (DataValue d) ! n"

lemma Rep_data_tuple:
  "Rep_data D = (DataValue D, DataSpace D)"
by (unfold DataValue_def DataSpace_def, simp)

lemma Rep_data_select: 
  "(DataValue D, DataSpace D) \<in> data"
apply (subst Rep_data_tuple [THEN sym])
apply (rule Rep_data)
done

lemma Data_select:
  "Data (DataValue D) (DataSpace D)"
apply (cut_tac D=D in Rep_data_select)
apply (unfold data_def)
apply auto
done

lemma length_DataValue_PartNum [simp]: 
  "length (DataValue D) = PartNum (Data.DataSpace D)"
apply (cut_tac D=D in Data_select)
apply (unfold Data_def)
apply auto
done

lemma DataValue_PartDom [simp]:
  "i < PartNum (Data.DataSpace D) \<Longrightarrow>
   DataValue D ! i \<in> PartDom (Data.DataSpace D) i"
apply (cut_tac D=D in Data_select)
apply (unfold Data_def)
apply auto
done 

lemma DataPart_PartDom [simp]:
  "i < PartNum (Data.DataSpace d) \<longrightarrow> (d !P! i) \<in> ((Data.DataSpace d) !D! i)"
apply (unfold DataPart_def)
apply auto
done

subsection \<open>Partial data space assignments\<close>

definition
  PData :: "['d option list, 'd dataspace] => bool" where
  "PData L D == ((length L) = (PartNum D)) \<and> 
                (\<forall> i \<in> {n. n < (PartNum D)}.
                    (L!i) \<noteq> None \<longrightarrow> the (L!i) \<in> (PartDom D i))"

lemma PData_EmptySet:
    "([Some (@ t. True)], Abs_dataspace [UNIV]) \<in> { (L,D) | L D. PData L D }"
apply (unfold PData_def PartDom_def)
apply auto
apply (subst Abs_dataspace_inverse)
apply auto
done

definition
  "pdata =
    { (L,D) |
             (L::('d option list))
             (D::('d dataspace)).
              PData L D }"

typedef 'd pdata = "pdata :: ('d option list * 'd dataspace) set"
  unfolding pdata_def
  apply (rule exI)
  apply (rule PData_EmptySet)
  done

definition
  PDataValue :: "('d pdata) => ('d option list)" where
 "PDataValue = fst o Rep_pdata"

definition
  PDataSpace :: "('d pdata) => ('d dataspace)" where
 "PDataSpace = snd o Rep_pdata"

definition
  Data2PData :: "('d data) => ('d pdata)" where
 "Data2PData D = (let
                      (L,DP) = Rep_data D;
                      OL     = map Some L
                  in
                      Abs_pdata (OL,DP))"

definition
  PData2Data :: "('d pdata) => ('d data)" where
 "PData2Data D = (let
                      (OL,DP) = Rep_pdata D;
                       L      = map the OL
                  in
                      Abs_data (L,DP))"

definition
  DefaultPData :: "('d dataspace) => ('d pdata)" where
 "DefaultPData D = Abs_pdata (replicate (PartNum D) None, D)"

definition
  OptionOverride :: "('d option * 'd) => 'd" where
 "OptionOverride P = (if (fst P) = None then (snd P) else (the (fst P)))"

definition
  DataOverride :: "['d pdata, 'd data] => 'd data" ("(_ [D+]/ _)" [10,11]10) where
 "DataOverride D1 D2 =
                (let
                    (L1,DP1) = Rep_pdata D1;
                    (L2,DP2) = Rep_data D2;
                    L        = map OptionOverride (zip L1 L2)
                 in
                    Abs_data (L,DP2))"

lemma Rep_pdata_tuple:
  "Rep_pdata D = (PDataValue D, PDataSpace D)"
apply (unfold PDataValue_def PDataSpace_def)
apply (simp)
done

lemma Rep_pdata_select:
  "(PDataValue D, PDataSpace D) \<in> pdata"
apply (subst Rep_pdata_tuple [THEN sym])
apply (rule Rep_pdata)
done

lemma PData_select: 
  "PData (PDataValue D) (PDataSpace D)"
apply (cut_tac D=D in Rep_pdata_select)
apply (unfold pdata_def)
apply auto
done

subsubsection \<open>\<open>DefaultPData\<close>\<close>

lemma PData_DefaultPData [simp]:
   "PData (replicate (PartNum D) None) D"
apply (unfold PData_def)
apply auto
done

lemma pdata_DefaultPData [simp]:
   "(replicate (PartNum D) None, D) \<in> pdata "
apply (unfold pdata_def)
apply auto
done

lemma PDataSpace_DefaultPData [simp]:
   "PDataSpace (DefaultPData D) = D"
apply (unfold DataSpace_def PDataSpace_def DefaultPData_def)
apply auto
apply (subst Abs_pdata_inverse)
apply auto
done

lemma length_PartNum_PData [simp]:
  "length (PDataValue P) = PartNum (PDataSpace P)"
apply (cut_tac D=P in Rep_pdata_select)
apply (unfold pdata_def PData_def)
apply auto
done

subsubsection \<open>\<open>Data2PData\<close>\<close>

lemma PData_Data2PData [simp]:
  "PData (map Some (DataValue D)) (Data.DataSpace D)"
apply (unfold PData_def)
apply auto
done

lemma pdata_Data2PData [simp]:
  "(map Some (DataValue D), Data.DataSpace D) \<in> pdata"
apply (unfold pdata_def)
apply auto
done

lemma DataSpace_Data2PData [simp]:
  "(PDataSpace (Data2PData D)) = (Data.DataSpace D)"
apply (unfold DataSpace_def PDataSpace_def Data2PData_def Let_def)
apply auto
apply (cut_tac D=D in Rep_data_tuple)
apply auto
apply (subst Abs_pdata_inverse)
apply auto
done

lemma PDataValue_Data2PData_DataValue [simp]:
     "(map the (PDataValue (Data2PData D))) = DataValue D"
apply (unfold DataValue_def PDataValue_def Data2PData_def Let_def)
apply auto
apply (cut_tac D=D in Rep_data_tuple)
apply auto
apply (subst Abs_pdata_inverse)
apply simp
apply (simp del: map_map)
done

lemma DataSpace_PData2Data:  
   "Data (map the (PDataValue D)) (PDataSpace D) \<Longrightarrow>
   (Data.DataSpace (PData2Data D) = (PDataSpace D))"
apply (unfold DataSpace_def PDataSpace_def PData2Data_def Let_def)
apply auto
apply (cut_tac D=D in Rep_pdata_tuple)
apply auto
apply (subst Abs_data_inverse)
apply (unfold data_def)
apply auto
done

lemma PartNum_PDataValue_PartDom [simp]:
   "\<lbrakk> i < PartNum (PDataSpace Q);
      PDataValue Q ! i = Some y \<rbrakk> \<Longrightarrow>
      y \<in> PartDom (PDataSpace Q) i"
apply (cut_tac D=Q in Rep_pdata_select)
apply (unfold pdata_def PData_def)
apply auto
done

subsubsection \<open>\<open>DataOverride\<close>\<close>

lemma Data_DataOverride:
 "((PDataSpace P) = (Data.DataSpace Q)) \<Longrightarrow>
  Data (map OptionOverride (zip (PDataValue P) (Data.DataValue Q))) (Data.DataSpace Q)"
apply (unfold Data_def)
apply auto
apply (unfold OptionOverride_def)
apply auto
apply (rename_tac i D)
apply (case_tac "PDataValue P ! i = None")
apply auto
apply (drule sym)
apply auto
done

lemma data_DataOverride:
 "((PDataSpace P) = (Data.DataSpace Q)) \<Longrightarrow>
   (map OptionOverride (zip (PDataValue P) (Data.DataValue Q)), Data.DataSpace Q) \<in> data"
apply (unfold data_def)
apply auto
apply (rule Data_DataOverride)
apply fast
done

lemma DataSpace_DataOverride [simp]:
 "((Data.DataSpace D) = (PDataSpace E)) \<Longrightarrow>
   Data.DataSpace (E [D+] D) = (Data.DataSpace D)"
apply (unfold DataSpace_def DataOverride_def Let_def)
apply auto
apply (cut_tac D=D in Rep_data_tuple)
apply (cut_tac D=E in Rep_pdata_tuple)
apply auto
apply (subst Abs_data_inverse)
apply auto
apply (drule sym)
apply simp
apply (rule data_DataOverride)
apply auto
done

lemma DataValue_DataOverride [simp]:
 "((PDataSpace P) = (Data.DataSpace Q)) \<Longrightarrow>
  (DataValue (P [D+] Q)) = (map OptionOverride (zip (PDataValue P) (Data.DataValue Q)))"
apply (unfold DataValue_def DataOverride_def Let_def)
apply auto
apply (cut_tac D=P in Rep_pdata_tuple)
apply (cut_tac D=Q in Rep_data_tuple)
apply auto
apply (subst Abs_data_inverse)
apply auto
apply (rule data_DataOverride)
apply auto
done

subsubsection \<open>\<open>OptionOverride\<close>\<close>

lemma DataValue_OptionOverride_nth:
 "\<lbrakk> ((PDataSpace P) = (DataSpace Q));
    i < PartNum (DataSpace Q) \<rbrakk> \<Longrightarrow>
    (DataValue (P [D+] Q) ! i) = 
    OptionOverride (PDataValue P ! i, DataValue Q ! i)"
apply auto
done

lemma None_OptionOverride [simp]:
   "(fst P) = None \<Longrightarrow> OptionOverride P = (snd P)"
apply (unfold OptionOverride_def)
apply auto
done

lemma Some_OptionOverride [simp]:
   "(fst P) \<noteq> None \<Longrightarrow> OptionOverride P = the (fst P)"
apply (unfold OptionOverride_def)
apply auto
done

end
