theory PropertyLibrary
imports InformationFlowProperties "../SystemSpecification/EventSystems" "../Verification/Basics/BSPTaxonomy"
begin

(* The following properties assume a partition of the
event set into a set of low events (L) and a set of high
events (H), where low events are visible *)
definition 
HighInputsConfidential :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e V_rec"
where 
"HighInputsConfidential L H IE \<equiv> \<lparr> V=L, N=H-IE, C=H \<inter> IE \<rparr>"

definition HighConfidential :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e V_rec"
where 
"HighConfidential L H \<equiv> \<lparr> V=L, N={}, C=H \<rparr>"

fun interleaving :: "'e list \<Rightarrow> 'e list \<Rightarrow> ('e list) set"
where
"interleaving t1 [] = {t1}" |
"interleaving [] t2 = {t2}" | 
"interleaving (e1 # t1) (e2 # t2) = 
  {t. (\<exists>t'. t=(e1 # t') \<and> t' \<in> interleaving t1 (e2 #t2))}
  \<union> {t. (\<exists>t'. t=(e2 # t') \<and> t' \<in> interleaving (e1 # t1) t2)}"


(* Generalized Noninterference [McC87] *)
(* MAKS representation *)
definition GNI :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"GNI L H IE \<equiv> ( {HighInputsConfidential L H IE}, {BSD, BSI})"

lemma GNI_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (GNI L H IE)"
  unfolding IFP_valid_def GNI_def HighInputsConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_BSD BasicSecurityPredicates.BSP_valid_BSI 
  by auto
    
(* Literature representation *)
definition litGNI :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litGNI L H IE Tr \<equiv> 
  \<forall> t1 t2 t3. 
    t1 @ t2 \<in> Tr \<and> t3 \<upharpoonleft> (L \<union> (H - IE)) = t2 \<upharpoonleft> (L \<union> (H - IE))
     \<longrightarrow> (\<exists> t4. t1 @ t4 \<in> Tr \<and> t4\<upharpoonleft>(L \<union> (H \<inter> IE)) = t3\<upharpoonleft>(L \<union> (H \<inter> IE)))"  

(* Interleaving-based Generalized Noninterference [ZL97] *)
(* MAKS representation *) 
definition IBGNI :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where "IBGNI L H IE \<equiv> ( {HighInputsConfidential L H IE}, {D, I})"

lemma IBGNI_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (IBGNI L H IE)"
  unfolding IFP_valid_def IBGNI_def HighInputsConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_D BasicSecurityPredicates.BSP_valid_I 
  by auto    

(* Literature representation *) 
definition 
litIBGNI :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"  
where 
"litIBGNI L H IE Tr \<equiv> 
  \<forall> \<tau>_l \<in> Tr. \<forall> t_hi t. 
    (set t_hi) \<subseteq> (H \<inter> IE)  \<and> t \<in> interleaving t_hi (\<tau>_l \<upharpoonleft> L) 
      \<longrightarrow> (\<exists> \<tau>' \<in> Tr. \<tau>' \<upharpoonleft> (L \<union> (H \<inter> IE)) = t)"  

(* Forward Correctability [JT88] *)
(* MAKS representation *)  
definition FC :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"FC L H IE \<equiv> 
  ( {HighInputsConfidential L H IE}, 
  {BSD, BSI, (FCD \<lparr> Nabla=IE, Delta={}, Upsilon=IE \<rparr>), 
             (FCI \<lparr> Nabla=IE, Delta={}, Upsilon=IE \<rparr> )})"

lemma FC_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (FC L H IE)"
  unfolding IFP_valid_def FC_def HighInputsConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_BSD BasicSecurityPredicates.BSP_valid_BSI
    BasicSecurityPredicates.BSP_valid_FCD BasicSecurityPredicates.BSP_valid_FCI
  by auto  

(* Literature representation *)
definition litFC :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litFC L H IE Tr \<equiv> 
  \<forall>t_1 t_2. \<forall> hi \<in> (H \<inter> IE). 
  (
    (\<forall> li \<in> (L \<inter> IE). 
      t_1 @ [li] @ t_2 \<in> Tr \<and> t_2 \<upharpoonleft> (H \<inter> IE) = [] 
      \<longrightarrow> (\<exists> t_3. t_1 @ [hi] @ [li] @ t_3 \<in> Tr 
                   \<and> t_3 \<upharpoonleft> L = t_2 \<upharpoonleft> L \<and> t_3 \<upharpoonleft> (H \<inter> IE) = [] ))
      \<and> (t_1 @ t_2 \<in> Tr \<and> t_2 \<upharpoonleft> (H \<inter> IE) = [] 
         \<longrightarrow> (\<exists> t_3. t_1 @ [hi]  @ t_3 \<in> Tr 
                      \<and> t_3 \<upharpoonleft> L = t_2 \<upharpoonleft> L \<and> t_3 \<upharpoonleft> (H \<inter> IE) = [] ))
     \<and> (\<forall> li \<in> (L \<inter> IE). 
          t_1 @ [hi] @ [li] @ t_2 \<in> Tr \<and> t_2 \<upharpoonleft> (H \<inter> IE) = [] 
           \<longrightarrow> (\<exists> t_3. t_1 @ [li] @ t_3 \<in> Tr 
                        \<and> t_3 \<upharpoonleft> L = t_2 \<upharpoonleft> L \<and> t_3 \<upharpoonleft> (H \<inter> IE) = [] )) 
          \<and> (t_1 @ [hi]  @ t_2 \<in> Tr \<and> t_2 \<upharpoonleft> (H \<inter> IE) = [] 
             \<longrightarrow> (\<exists> t_3. t_1  @ t_3 \<in> Tr 
                          \<and> t_3 \<upharpoonleft> L = t_2 \<upharpoonleft> L \<and> t_3 \<upharpoonleft> (H \<inter> IE) = [] ))
  )"  

(* Nondeducibility for outputs [GN88] *)
(* MAKS representation *)
definition NDO :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"NDO UI L H \<equiv> 
  ( {HighConfidential L H}, {BSD, (BSIA (\<lambda> \<V>. C\<^bsub>\<V>\<^esub> \<union> (V\<^bsub>\<V>\<^esub> \<inter> UI)))})"

lemma NDO_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (NDO UI L H)"
  unfolding IFP_valid_def NDO_def HighConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_BSD
        BasicSecurityPredicates.BSP_valid_BSIA[of "(\<lambda> \<V>. C\<^bsub>\<V>\<^esub> \<union> (V\<^bsub>\<V>\<^esub> \<inter> UI))"]
  by auto 
  
(* Literature representation *)
definition litNDO :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litNDO UI L H Tr \<equiv> 
  \<forall>\<tau>_l \<in> Tr. \<forall> \<tau>_hlui \<in> Tr.  \<forall> t. 
    t\<upharpoonleft>L = \<tau>_l\<upharpoonleft>L \<and> t\<upharpoonleft>(H \<union> (L \<inter> UI)) = \<tau>_hlui\<upharpoonleft>(H \<union> (L \<inter> UI)) \<longrightarrow> t \<in> Tr"  
  
(* Noninference [ZL97] *)
(* MAKS representation *)  
definition NF :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"NF L H \<equiv> ( {HighConfidential L H}, {R})"

lemma NF_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (NF L H)"
  unfolding IFP_valid_def NF_def HighConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_R
  by auto     

(* Literature representation *)  
definition litNF :: "'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litNF L H Tr \<equiv> \<forall>\<tau> \<in> Tr. \<tau> \<upharpoonleft> L \<in> Tr"


(* Generalized Noninference [ZL97] *)
(* MAKS representation *)
definition GNF :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"GNF L H IE \<equiv> ( {HighInputsConfidential L H IE}, {R})"

lemma GNF_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (GNF L H IE)"
  unfolding IFP_valid_def GNF_def HighInputsConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_R
  by auto       

(* Literature representation *)
definition litGNF :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litGNF L H IE Tr \<equiv> 
  \<forall>\<tau> \<in> Tr. \<exists>\<tau>' \<in> Tr. \<tau>'\<upharpoonleft> (H \<inter> IE) = [] \<and> \<tau>'\<upharpoonleft> L = \<tau> \<upharpoonleft> L"  
  
(* Separability [ZL97] *)
(* MAKS representation *)  
definition SEP :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"SEP L H \<equiv> ( {HighConfidential L H}, {BSD, (BSIA (\<lambda> \<V>. C\<^bsub>\<V>\<^esub>))})"

lemma SEP_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (SEP L H)"
  unfolding IFP_valid_def SEP_def HighConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_BSD
        BasicSecurityPredicates.BSP_valid_BSIA[of "\<lambda> \<V>. C\<^bsub>\<V>\<^esub>"]
  by auto     
    
(* Literature representation *)
definition litSEP :: "'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litSEP L H Tr \<equiv> 
  \<forall>\<tau>_l \<in> Tr. \<forall> \<tau>_h \<in> Tr. 
    interleaving (\<tau>_l \<upharpoonleft> L) (\<tau>_h \<upharpoonleft> H) \<subseteq> {\<tau> \<in> Tr . \<tau> \<upharpoonleft> L = \<tau>_l \<upharpoonleft> L} "  

(* Perfect Security Property [ZL97] *)
(* MAKS representation *)
definition PSP :: "'e set \<Rightarrow> 'e set \<Rightarrow> 'e IFP_type"
where 
"PSP L H \<equiv> 
  ( {HighConfidential L H}, {BSD, (BSIA (\<lambda> \<V>. C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> V\<^bsub>\<V>\<^esub>))})"

lemma PSP_valid: "L \<inter> H = {} \<Longrightarrow> IFP_valid (L \<union> H) (PSP L H)"
  unfolding IFP_valid_def PSP_def HighConfidential_def isViewOn_def 
    V_valid_def VN_disjoint_def VC_disjoint_def NC_disjoint_def
  using BasicSecurityPredicates.BSP_valid_BSD
        BasicSecurityPredicates.BSP_valid_BSIA[of "\<lambda> \<V>. C\<^bsub>\<V>\<^esub> \<union> N\<^bsub>\<V>\<^esub> \<union> V\<^bsub>\<V>\<^esub>"]
  by auto         

(* Literature representation *)
definition litPSP :: "'e set \<Rightarrow> 'e set \<Rightarrow> ('e list) set \<Rightarrow> bool"
where 
"litPSP L H Tr \<equiv> 
  (\<forall>\<tau> \<in> Tr. \<tau> \<upharpoonleft> L \<in> Tr) 
    \<and> (\<forall> \<alpha> \<beta>. (\<beta> @ \<alpha>) \<in> Tr \<and> (\<alpha> \<upharpoonleft> H) = [] 
                \<longrightarrow> (\<forall> h \<in> H. \<beta> @ [h] \<in> Tr \<longrightarrow> \<beta> @ [h] @ \<alpha> \<in> Tr))"  

end
