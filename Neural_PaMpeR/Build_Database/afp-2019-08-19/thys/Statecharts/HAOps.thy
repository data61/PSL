(*  Title:      statecharts/HA/HAOps.thy
    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Constructing Hierarchical Automata\<close>
theory HAOps
imports HA
begin

subsection "Constructing a Composition Function for a PseudoHA"

definition
  EmptyMap :: "'s set => ('s \<rightharpoonup> (('s,'e,'d)seqauto) set)" where
  "EmptyMap S = (\<lambda> a . if a \<in> S then Some {} else None)"

lemma EmptyMap_dom [simp]:
  "dom (EmptyMap S) = S"
by (unfold dom_def EmptyMap_def,auto)

lemma EmptyMap_ran [simp]:
   "S \<noteq> {} \<Longrightarrow> ran (EmptyMap S) = {{}}"
by (unfold ran_def EmptyMap_def, auto)

lemma EmptyMap_the [simp]:
   "x \<in> S \<Longrightarrow> the ((EmptyMap S) x) = {}"
by (unfold ran_def EmptyMap_def, auto)

lemma EmptyMap_ran_override:
  "\<lbrakk> S \<noteq> {}; (S \<inter> (dom G)) = {} \<rbrakk> \<Longrightarrow>  
  ran (G ++ EmptyMap S) = insert {} (ran G)"
apply (subst ran_override)
apply (simp add: Int_commute)
apply simp
done

lemma EmptyMap_Union_ran_override:
 "\<lbrakk> S \<noteq> {};  
    S \<inter> dom G = {} \<rbrakk> \<Longrightarrow>  
  (Union (ran (G ++ (EmptyMap S)))) = (Union (ran G))"
apply (subst EmptyMap_ran_override)
apply auto
done

lemma EmptyMap_Union_ran_override2:
 "\<lbrakk> S \<noteq> {}; S \<inter> dom G1 = {}; 
    dom G1 \<inter> dom G2 = {} \<rbrakk> \<Longrightarrow> 
   \<Union> (ran (G1 ++ EmptyMap S ++ G2)) = (\<Union> (ran G1 \<union> ran G2))"
apply (unfold Union_eq UNION_eq EmptyMap_def Int_def ran_def)
apply (simp add: map_add_Some_iff)
apply (unfold dom_def)
apply simp
apply (rule equalityI)
apply (rule subsetI)
apply simp
apply fast
apply (rule subsetI)
apply (rename_tac t)
apply simp
apply (erule bexE)
apply (rename_tac U)
apply simp
apply (erule disjE)
apply (erule exE)
apply (rename_tac v)
apply (rule_tac x=U in exI)
apply simp
apply (rule_tac x=v in exI)
apply auto
done

lemma EmptyMap_Root [simp]:
 "Root {SA} (EmptyMap (States SA)) = SA"
by (unfold Root_def, auto)

lemma EmptyMap_RootEx [simp]:
  "RootEx {SA} (EmptyMap (States SA))"
by (unfold RootEx_def, auto)

lemma EmptyMap_OneAncestor [simp]:
 "OneAncestor {SA} (EmptyMap (States SA))"
by (unfold OneAncestor_def, auto)

lemma EmptyMap_NoCycles [simp]:
  "NoCycles {SA} (EmptyMap (States SA))"
by (unfold NoCycles_def EmptyMap_def , auto)

lemma EmptyMap_IsCompFun [simp]:
 "IsCompFun {SA} (EmptyMap (States SA))"
by (unfold IsCompFun_def, auto)

lemma EmptyMap_hierauto [simp]:
 "(D,{SA}, SAEvents SA, EmptyMap (States SA)) \<in> hierauto"
by (unfold hierauto_def HierAuto_def, auto)

subsection "Extending a Composition Function by a SA"

definition
  FAddSA :: "[('s \<rightharpoonup> (('s,'e,'d)seqauto) set), 's * ('s,'e,'d)seqauto]
             => ('s \<rightharpoonup> (('s,'e,'d)seqauto) set)"
           ("(_ [f+]/ _)" [10,11]10) where
  "FAddSA G SSA = (let  (S,SA) = SSA
                   in
                     (if ((S \<in> dom G) \<and> (S \<notin> States SA)) then
                        (G ++ (Map.empty(S \<mapsto> (insert SA (the (G S)))))
                         ++ EmptyMap (States SA))
                      else G))"

lemma FAddSA_dom [simp]:
 "(S \<notin> (dom (A::('a => ('a,'c,'d)seqauto set option)))) \<Longrightarrow>
   ((A [f+] (S,(SA::('a,'c,'d)seqauto))) = A)"
by (unfold FAddSA_def Let_def, auto)

lemma FAddSA_States [simp]:
 "(S \<in> (States (SA::('a,'c,'d)seqauto))) \<Longrightarrow>
   (((A::('a => ('a,'c,'d)seqauto set option)) [f+] (S,SA)) = A)"
by (unfold FAddSA_def Let_def, auto)

lemma FAddSA_dom_insert [simp]:
 "\<lbrakk> S \<in> (dom A); S \<notin>  States SA \<rbrakk> \<Longrightarrow> 
   (((A [f+] (S,SA)) S) = Some (insert SA (the (A S))))"
by (unfold FAddSA_def Let_def restrict_def, auto)

lemma FAddSA_States_neq [simp]:
 "\<lbrakk> S' \<notin> States (SA::('a,'c,'d)seqauto); S \<noteq>  S' \<rbrakk> \<Longrightarrow> 
  ((((A::('a => ('a,'c,'d)seqauto set option)) [f+] (S,SA)) S') = (A S'))"
apply (case_tac "S \<in> dom A")
apply (case_tac "S \<in> States SA")
apply auto
apply (case_tac "S' \<in> dom A")
apply (unfold FAddSA_def Let_def)
apply auto
apply (simp add: dom_None)
done

lemma FAddSA_dom_emptyset [simp]:
 "\<lbrakk> S \<in> (dom A); S \<notin> States SA; S' \<in> States (SA::('a,'c,'d)seqauto) \<rbrakk> \<Longrightarrow>  
    ((((A::('a => ('a,'c,'d)seqauto set option))) [f+] (S,SA)) S') = (Some {})"
apply (unfold FAddSA_def Let_def)
apply auto
apply (unfold EmptyMap_def)
apply auto
done

lemma FAddSA_dom_dom_States [simp]:
  "\<lbrakk> S \<in> (dom F); S \<notin> States SA \<rbrakk> \<Longrightarrow> 
    (dom ((F::('a \<rightharpoonup> (('a,'b,'d)seqauto) set)) [f+] (S, SA))) = 
    ((dom F) \<union> (States (SA::('a,'b,'d)seqauto)))"
by (unfold FAddSA_def Let_def, auto)

lemma FAddSA_dom_dom [simp]:
  "S \<notin> (dom F) \<Longrightarrow>   
   (dom ((F::('a \<rightharpoonup> (('a,'b,'d)seqauto) set)) [f+] 
       (S,(SA::('a,'b,'d)seqauto)))) = (dom F)"
by (unfold FAddSA_def Let_def, auto)

lemma FAddSA_States_dom [simp]:
  "S \<in> (States SA) \<Longrightarrow>  
   (dom ((F::('a \<rightharpoonup> (('a,'b,'d)seqauto) set)) [f+] 
        (S,(SA::('a,'b,'d)seqauto)))) = (dom F)"
by (unfold FAddSA_def Let_def, auto)

lemma FAddSA_dom_insert_dom_disjunct [simp]:
   "\<lbrakk> S \<in> dom G; States SA \<inter> dom G = {} \<rbrakk> \<Longrightarrow> ((G [f+] (S,SA)) S) = Some (insert SA (the (G S)))"
apply (rule  FAddSA_dom_insert)
apply auto
done

lemma FAddSA_Union_ran:
 "\<lbrakk> S \<in> dom G; (States SA) \<inter> (dom G) = {} \<rbrakk> \<Longrightarrow> 
   (\<Union> (ran (G [f+] (S,SA)))) = (insert SA (\<Union> (ran G)))"
apply (unfold FAddSA_def Let_def)
apply simp
apply (rule conjI)
prefer 2
apply (rule impI)
apply (unfold Int_def)
apply simp
apply (fold Int_def)
apply (rule impI)
apply (subst EmptyMap_Union_ran_override)
apply auto
done

lemma FAddSA_Union_ran2:
 "\<lbrakk> S \<in> dom G1; (States SA) \<inter> (dom G1) = {}; (dom G1 \<inter> dom G2) = {} \<rbrakk> \<Longrightarrow>
   (\<Union> (ran ((G1 [f+] (S,SA)) ++ G2))) = (insert SA (\<Union> ((ran G1) \<union> (ran G2))))"
apply (unfold FAddSA_def Let_def)
apply (simp (no_asm_simp))
apply (rule conjI)
apply (rule impI)
apply (subst EmptyMap_Union_ran_override2)
apply simp
apply simp
apply simp
apply fast
apply (subst Union_Un_distrib)
apply (subst Union_ran_override2)
apply auto
done

lemma FAddSA_ran:
  "\<lbrakk> \<forall> T \<in> dom G . T \<noteq> S \<longrightarrow> (the (G T) \<inter> the (G S)) = {};  
     S \<in> dom G; (States SA) \<inter>  (dom G) = {} \<rbrakk> \<Longrightarrow>  
    ran (G [f+] (S,SA)) = insert {} (insert (insert SA (the (G S))) (ran G - {the (G S)}))"
apply (unfold FAddSA_def Let_def)
apply simp
apply (rule conjI)
apply (rule impI)+
prefer 2
apply fast
apply (simp add: EmptyMap_ran_override)
apply (unfold ran_def)
apply auto
apply (rename_tac Y X a xa xb)
apply (erule_tac x=a in allE)
apply simp
apply (erule_tac x=a in allE)
apply simp
done

lemma FAddSA_RootEx_def: 
  "\<lbrakk> S \<in> dom G; (States SA) \<inter> (dom G) = {} \<rbrakk> \<Longrightarrow> 
    RootEx F (G [f+] (S,SA)) = (\<exists>! A . A \<in> F \<and> A \<notin> insert SA (\<Union> (ran G)))"
apply (unfold RootEx_def)
apply (simp only: FAddSA_Union_ran Int_commute)
done

lemma FAddSA_RootEx:
  "\<lbrakk> \<Union> (ran G) = F - {Root F G}; 
     dom G = \<Union>(States ` F); 
     (dom G \<inter> States SA) = {}; S \<in> dom G; 
     RootEx F G \<rbrakk> \<Longrightarrow> RootEx (insert SA F) (G [f+] (S,SA))"
apply (simp add: FAddSA_RootEx_def Int_commute cong: rev_conj_cong)
apply (auto cong: conj_cong) 
done

lemma FAddSA_Root_def:
  "\<lbrakk> S \<in> dom G; (States SA) \<inter> (dom G) = {} \<rbrakk>  \<Longrightarrow> 
   (Root F (G [f+] (S,SA)) = (@ A . A \<in> F \<and> A \<notin> insert SA (\<Union> (ran G))))" 
apply (unfold Root_def)
apply (simp only: FAddSA_Union_ran Int_commute)
done

lemma FAddSA_RootEx_Root: 
  "\<lbrakk> Union (ran G) = F - {Root F G};  
     \<Union>(States ` F) = dom G; 
     (dom G \<inter> States SA) = {}; S \<in> dom G;
     RootEx F G \<rbrakk> \<Longrightarrow> (Root (insert SA F) (G [f+] (S,SA))) = (Root F G)"
apply (simp add: FAddSA_Root_def Int_commute cong: rev_conj_cong)
apply (simp cong:conj_cong)
done

lemma FAddSA_OneAncestor:
  "\<lbrakk> \<Union> (ran G) = F - {Root F G}; 
     (dom G \<inter> States SA) = {}; S \<in> dom G; 
     \<Union>(States ` F) = dom G; RootEx F G;
     OneAncestor F G \<rbrakk> \<Longrightarrow> OneAncestor (insert SA F) (G [f+] (S,SA))"
apply (subst OneAncestor_def)
apply simp
apply (rule ballI)
apply (rename_tac SAA)
apply (case_tac "SA = SAA")
apply (rule_tac a=S in ex1I)
apply (rule conjI)
apply simp
apply fast
apply (subst FAddSA_dom_insert)
apply simp
apply (simp add:Int_def)
apply simp
apply (rename_tac T)
apply (erule conjE bexE exE disjE)+
apply (rename_tac SAAA)
apply simp
apply (erule conjE)
apply (subst not_not [THEN sym])
apply (rule notI)
apply (case_tac "T \<in> States SAA")
apply blast
apply (drule_tac A=G and S=S and SA=SAA in FAddSA_States_neq)
apply fast
apply simp
apply (case_tac "SAA \<notin> Union (ran G)")
apply (frule ran_dom_the)
prefer 2
apply fast
apply blast
apply simp
apply (erule conjE)
apply (simp add: States_Int_not_mem)
apply (unfold OneAncestor_def)
apply (drule_tac G=G and S=S and SA=SA in FAddSA_RootEx_Root)
apply simp
apply simp
apply simp
apply simp
apply (erule_tac x=SAA in ballE)
prefer 2
apply simp
apply simp
apply (erule conjE bexE ex1E exE disjE)+
apply (rename_tac T SAAA)
apply (rule_tac a=T in ex1I)
apply (rule conjI)
apply fast
apply (case_tac "T = S")
apply simp
apply (case_tac "S \<notin> States SA")
apply simp
apply simp
apply (subst FAddSA_States_neq)
apply blast
apply (rule not_sym)
apply simp
apply simp
apply (rename_tac U)
apply simp
apply (erule conjE bexE)+
apply (rename_tac SAAAA)
apply simp
apply (erule conjE disjE)+
apply (frule FAddSA_dom_emptyset)
prefer 2
apply fast
back
back
apply simp
apply blast
apply simp
apply (erule_tac x=U in allE)
apply (erule impE)
prefer 2
apply simp
apply (rule conjI)
apply fast
apply (case_tac "S \<noteq> U")
apply (subgoal_tac "U \<notin> States SA")
apply (drule_tac A=G in FAddSA_States_neq)
apply fast
apply simp
apply blast
apply (drule_tac A=G and SA=SA in FAddSA_dom_insert)
apply simp
apply blast
apply auto
done

lemma FAddSA_NoCycles:
  "\<lbrakk> (States SA \<inter> dom G) = {}; S \<in> dom G;
     dom G = \<Union>(States ` F); NoCycles F G \<rbrakk> \<Longrightarrow> 
     NoCycles  (insert SA F) (G [f+] (S,SA))"
apply (unfold NoCycles_def)
apply (rule ballI impI)+
apply (rename_tac SAA)
apply (case_tac "\<exists> s \<in> SAA. s \<in> States SA")
apply simp
apply (erule bexE)+
apply (rename_tac SAAA T)
apply (rule_tac x=T in bexI)
apply simp
apply (subst FAddSA_dom_emptyset)
apply simp
apply fast
apply blast
apply simp
apply simp
apply simp
apply simp
apply (erule_tac x=SAA in ballE)
prefer 2
apply simp
apply auto[1]
apply (unfold UNION_eq Pow_def)
apply simp
apply (case_tac "SAA = {}")
apply fast
apply simp
apply (erule bexE)+
apply (rename_tac SAAA T)
apply (rule_tac x=T in bexI)
prefer 2
apply simp
apply (case_tac "T=S")
apply simp
apply (subst FAddSA_dom_insert)
apply auto
done

lemma FAddSA_IsCompFun:
 "\<lbrakk> (States SA \<inter> (\<Union>(States ` F))) = {};
     S \<in> (\<Union>(States ` F)); 
     IsCompFun F G \<rbrakk> \<Longrightarrow>  IsCompFun (insert SA F) (G [f+] (S,SA))"
apply (unfold IsCompFun_def)
apply (erule conjE)+
apply (simp add: Int_commute FAddSA_RootEx_Root FAddSA_RootEx FAddSA_OneAncestor FAddSA_NoCycles)
apply (rule conjI)
apply (subst FAddSA_dom_dom_States)
apply simp
apply blast
apply (simp add: Un_commute)
apply (simp add: FAddSA_Union_ran)
apply (case_tac "SA = Root F G")
prefer 2
apply blast
apply (subgoal_tac "States (Root F G) \<subseteq>  \<Union>(States ` F)")
apply simp
apply (frule subset_lemma)
apply auto
done

lemma FAddSA_HierAuto:
  "\<lbrakk> (States SA \<inter> (\<Union>(States ` F))) = {};
      S \<in> (\<Union>(States ` F)); 
      HierAuto D F E G \<rbrakk> \<Longrightarrow> HierAuto D (insert SA F) (E \<union> SAEvents SA) (G [f+] (S,SA))"
apply (unfold HierAuto_def)
apply auto
apply (simp add: MutuallyDistinct_Insert)
apply (rule FAddSA_IsCompFun)
apply auto
done

lemma FAddSA_HierAuto_insert [simp]:
  "\<lbrakk> (States SA \<inter> HAStates HA) = {};
      S \<in> HAStates HA \<rbrakk> \<Longrightarrow> 
    HierAuto (HAInitValue HA)                  
             (insert SA (SAs HA))              
             (HAEvents HA \<union> SAEvents SA)      
             (CompFun HA [f+] (S,SA))"
apply (unfold HAStates_def)
apply (rule FAddSA_HierAuto)
apply auto
done

subsection "Constructing a PseudoHA" 

definition
  PseudoHA :: "[('s,'e,'d)seqauto,'d data] => ('s,'e,'d)hierauto" where
  "PseudoHA SA D = Abs_hierauto(D,{SA}, SAEvents SA ,EmptyMap (States SA))"

lemma PseudoHA_SAs [simp]:
  "SAs (PseudoHA SA D) = {SA}"
by (unfold PseudoHA_def SAs_def, simp add: Abs_hierauto_inverse)

lemma PseudoHA_Events [simp]:
  "HAEvents (PseudoHA SA D) = SAEvents SA"
by (unfold PseudoHA_def HAEvents_def, simp add: Abs_hierauto_inverse)
 
lemma PseudoHA_CompFun [simp]:
  "CompFun (PseudoHA SA D) = EmptyMap (States SA)"
by (unfold PseudoHA_def CompFun_def, simp add: Abs_hierauto_inverse)

lemma PseudoHA_HAStates [simp]:
  "HAStates (PseudoHA SA D) = (States SA)"
by (unfold HAStates_def, auto)

lemma PseudoHA_HAInitValue [simp]:
  "(HAInitValue (PseudoHA SA D)) = D"
by (unfold PseudoHA_def Let_def HAInitValue_def, simp add: Abs_hierauto_inverse)
 
lemma PseudoHA_CompFun_the [simp]: 
 "S \<in> States A \<Longrightarrow> (the (CompFun (PseudoHA A D) S)) = {}"
by simp

lemma PseudoHA_CompFun_ran [simp]:
 "(ran (CompFun (PseudoHA SA D))) = {{}}"
by auto

lemma PseudoHA_HARoot [simp]:
 "(HARoot (PseudoHA SA D)) = SA"
by (unfold HARoot_def, auto)

lemma PseudoHA_HAInitState [simp]:
  "HAInitState (PseudoHA A D) = InitState A"
apply (unfold HAInitState_def)
apply simp
done

lemma PseudoHA_HAInitStates [simp]:
  "HAInitStates (PseudoHA A D) = {InitState A}" 
apply (unfold HAInitStates_def)
apply simp
done

lemma PseudoHA_Chi [simp]:
  "S \<in> States A \<Longrightarrow> Chi (PseudoHA A D) S = {}"
apply (unfold Chi_def restrict_def)
apply auto
done

lemma PseudoHA_ChiRel [simp]:
  "ChiRel (PseudoHA A D) = {}"
apply (unfold ChiRel_def)
apply simp
done

lemma PseudoHA_InitConf [simp]:
 "InitConf (PseudoHA A D) = {InitState A}"
apply (unfold InitConf_def)
apply simp
done

subsection \<open>Extending a HA by a SA (\<open>AddSA\<close>)\<close>

definition
  AddSA :: "[('s,'e,'d)hierauto, 's * ('s,'e,'d)seqauto]
             => ('s,'e,'d)hierauto"
           ("(_ [++]/ _)" [10,11]10) where
  "AddSA HA SSA = (let (S,SA) = SSA;
                        DNew = HAInitValue HA;
                        FNew = insert SA (SAs HA);
                        ENew  = HAEvents HA \<union> SAEvents SA;
                        GNew  = CompFun HA [f+] (S,SA)
                   in
                       Abs_hierauto(DNew,FNew,ENew,GNew))"

definition
  AddHA :: "[('s,'e,'d)hierauto, 's * ('s,'e,'d)hierauto]
             => ('s,'e,'d)hierauto"
           ("(_ [**]/ _)" [10,11]10) where
  "AddHA HA1 SHA =
            (let (S,HA2)     = SHA;
                 (D1,F1,E1,G1) = Rep_hierauto (HA1 [++] (S,HARoot HA2));
                 (D2,F2,E2,G2) = Rep_hierauto HA2;
                 FNew       = F1 \<union> F2;
                 ENew       = E1 \<union> E2;
                 GNew       = G1 ++ G2
             in
                 Abs_hierauto(D1,FNew,ENew,GNew))"

lemma AddSA_SAs:
  "\<lbrakk> (States SA \<inter>  HAStates HA) = {}; 
      S \<in> HAStates HA \<rbrakk> \<Longrightarrow> (SAs (HA [++] (S,SA))) = insert SA (SAs HA)"
apply (unfold Let_def AddSA_def)
apply (subst SAs_def)
apply (simp add: hierauto_def Abs_hierauto_inverse)
done

lemma AddSA_Events:
  "\<lbrakk> (States SA \<inter> HAStates HA) = {}; 
      S \<in> HAStates HA \<rbrakk> \<Longrightarrow>
     HAEvents (HA [++] (S,SA)) = (HAEvents HA) \<union> (SAEvents SA)"
apply (unfold Let_def AddSA_def)
apply (subst HAEvents_def)
apply (simp add: hierauto_def Abs_hierauto_inverse)
done

lemma AddSA_CompFun:
   "\<lbrakk> (States SA \<inter>  HAStates HA) = {}; 
      S \<in> HAStates HA \<rbrakk> \<Longrightarrow>  
     CompFun (HA [++] (S,SA)) = (CompFun HA [f+] (S,SA))"
apply (unfold Let_def AddSA_def)
apply (subst CompFun_def)
apply (simp add: hierauto_def Abs_hierauto_inverse)
done

lemma AddSA_HAStates:
   "\<lbrakk> (States SA \<inter> HAStates HA) = {}; 
       S \<in> HAStates HA \<rbrakk> \<Longrightarrow>
      HAStates (HA [++] (S,SA)) = (HAStates HA) \<union> (States SA)"
apply (unfold HAStates_def)
apply (subst AddSA_SAs)
apply (unfold HAStates_def)
apply auto
done

lemma AddSA_HAInitValue:
   "\<lbrakk> (States SA \<inter> HAStates HA) = {};
       S \<in> HAStates HA \<rbrakk> \<Longrightarrow>
      (HAInitValue (HA [++] (S,SA))) = (HAInitValue HA)"
apply (unfold Let_def AddSA_def)
apply (subst HAInitValue_def)
apply (simp add: hierauto_def Abs_hierauto_inverse)
done

lemma AddSA_HARoot:
   "\<lbrakk> (States SA \<inter> HAStates HA) = {};
      S \<in> HAStates HA \<rbrakk> \<Longrightarrow> 
      (HARoot (HA [++] (S,SA))) = (HARoot HA)"
apply (unfold HARoot_def)
apply (simp add: AddSA_CompFun AddSA_SAs)
apply (subst FAddSA_RootEx_Root)
apply auto
apply (simp only: HAStates_SA_mem)
apply (unfold HAStates_def)
apply fast
done

lemma AddSA_CompFun_the: 
 "\<lbrakk> (States SA \<inter> HAStates A) = {}; 
    S \<in> HAStates A \<rbrakk> \<Longrightarrow> 
  (the ((CompFun (A [++] (S,SA))) S)) = insert SA (the ((CompFun A) S))"
by (simp add: AddSA_CompFun)

lemma AddSA_CompFun_the2:
 "\<lbrakk> S' \<in> States (SA::('a,'c,'d)seqauto); 
    (States SA \<inter> HAStates A) = {};
    S \<in> HAStates A \<rbrakk> \<Longrightarrow>
    the ((CompFun (A [++] (S,SA))) S') = {}"
apply (simp add: AddSA_CompFun)
apply (subst FAddSA_dom_emptyset)
apply auto
done

lemma AddSA_CompFun_the3:
 "\<lbrakk> S' \<notin> States (SA::('a,'c,'d)seqauto); 
    S \<noteq> S'; 
    (States SA \<inter> HAStates A) = {}; 
    S \<in> HAStates A \<rbrakk> \<Longrightarrow> 
   (the ((CompFun (A [++] (S,SA))) S')) = (the ((CompFun A) S'))"
by (simp add: AddSA_CompFun)

lemma AddSA_CompFun_ran:
 "\<lbrakk> (States SA \<inter> HAStates A) = {};
     S \<in> HAStates A \<rbrakk> \<Longrightarrow> 
   ran (CompFun (A [++] (S,SA))) = 
       insert {} (insert (insert SA (the ((CompFun A) S))) (ran (CompFun A) - {the ((CompFun A) S)}))"
apply (simp add: AddSA_CompFun)
apply (subst FAddSA_ran)
apply auto
apply (fast dest: CompFun_Int_disjoint) 
done

lemma AddSA_CompFun_ran2:
 "\<lbrakk> (States SA1 \<inter> HAStates A) = {};
    (States SA2 \<inter> (HAStates A \<union> States SA1)) = {};
     S \<in> HAStates A;
     T \<in> States SA1 \<rbrakk> \<Longrightarrow>
   ran (CompFun ((A [++] (S,SA1)) [++] (T,SA2))) = 
       insert {} (insert {SA2} (ran (CompFun (A  [++] (S,SA1)))))"
apply (simp add: AddSA_HAStates AddSA_CompFun)
apply (subst FAddSA_ran)
apply (rule ballI)
apply (rule impI)
apply (subst AddSA_CompFun [THEN sym])
apply simp
apply simp
apply (subst AddSA_CompFun [THEN sym])
apply simp
apply simp
apply (rule CompFun_Int_disjoint)
apply simp
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
apply (case_tac "S \<in> States SA1")
apply simp
apply (simp only: dom_CompFun [THEN sym])
apply (frule FAddSA_dom_dom_States)
apply fast
apply simp
apply (case_tac "S \<in> States SA1")
apply simp
apply fast
apply (subst FAddSA_dom_dom_States)
apply simp
apply simp
apply simp
apply (case_tac "S \<in>  States SA1")
apply simp
apply fast
apply (subst FAddSA_dom_dom_States)
apply simp
apply simp
apply simp
apply (case_tac "S \<in>  States SA1")
apply simp
apply fast
apply simp
apply fast
done

lemma AddSA_CompFun_ran_not_mem:
 "\<lbrakk> States SA2 \<inter> (HAStates A \<union> States SA1) = {};
    States SA1 \<inter> HAStates A = {};
    S \<in> HAStates A \<rbrakk> \<Longrightarrow> 
   {SA2} \<notin> ran (CompFun A [f+] (S, SA1))"
apply (cut_tac HA="A [++] (S,SA1)" and Sas="{SA2}" in ran_CompFun_is_not_SA)
apply (simp add: AddSA_HAStates AddSA_CompFun)
apply (simp add: AddSA_HAStates AddSA_SAs)
apply auto
apply (simp add: Int_def)
apply (cut_tac SA=SA2 in EX_State_SA)
apply (erule exE)
apply (frule HAStates_SA_mem)
apply fast
apply (simp only: HAStates_def)
apply fast
apply (simp add: AddSA_HAStates AddSA_CompFun)
done

lemma AddSA_CompFun_ran3:
 "\<lbrakk> (States SA1 \<inter> HAStates A) = {};
    (States SA2 \<inter> (HAStates A \<union> States SA1)) = {};
    (States SA3 \<inter> (HAStates A \<union> States SA1 \<union> States SA2)) = {};
     S \<in> HAStates A; 
     T \<in> States SA1 \<rbrakk> \<Longrightarrow> 
    ran (CompFun ((A [++] (S,SA1)) [++] (T,SA2) [++] (T,SA3))) = 
       insert {} (insert {SA3,SA2} (ran (CompFun (A  [++] (S,SA1)))))"
apply (simp add: AddSA_HAStates AddSA_CompFun)
apply (subst FAddSA_ran)
apply (rule ballI)
apply (rule impI)
apply (subst AddSA_CompFun [THEN sym])
apply simp
apply simp
apply (subst AddSA_CompFun [THEN sym])
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
apply (subst AddSA_CompFun [THEN sym])
apply simp
apply simp
apply (subst AddSA_CompFun [THEN sym])
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
apply (rule CompFun_Int_disjoint)
apply simp
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
apply (simp only: dom_CompFun [THEN sym])
apply (cut_tac F="CompFun A [f+] (S, SA1)" and S=T and SA="SA2" in FAddSA_dom_dom_States)
apply (cut_tac F="CompFun A" and S=S and SA="SA1" in FAddSA_dom_dom_States)
apply fast
apply fast
apply simp
apply fast
apply simp
apply (cut_tac F="CompFun A" and S=S and SA="SA1" in FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply (subst FAddSA_dom_dom_States)
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply fast
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply (subst FAddSA_dom_dom_States)
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply fast
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply (subst AddSA_CompFun [THEN sym])
back
apply simp
apply simp
apply (subst AddSA_CompFun [THEN sym])
back
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
apply (subst AddSA_CompFun_ran2)
apply fast
apply fast
apply fast
apply fast
apply (simp add: AddSA_CompFun)
apply (subst  FAddSA_dom_insert)
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply fast
apply (subst FAddSA_dom_emptyset)
apply simp
apply fast
apply simp
apply simp
apply (subst  FAddSA_dom_insert)
apply (subst FAddSA_dom_dom_States)
apply simp
apply fast
apply simp
apply fast
apply (subst FAddSA_dom_emptyset)
apply simp
apply fast
apply simp
apply simp
apply (case_tac "{SA2} \<notin> ran (CompFun A [f+] (S,SA1))")
apply fast
apply (simp add:AddSA_CompFun_ran_not_mem) 
done

lemma AddSA_CompFun_PseudoHA_ran:
  "\<lbrakk> S \<in> States RootSA;
     States RootSA \<inter> States SA = {} \<rbrakk> \<Longrightarrow> 
     (ran (CompFun ((PseudoHA RootSA D) [++] (S,SA)))) = (insert {} {{SA}})"
apply (subst AddSA_CompFun_ran)
apply auto
done

lemma AddSA_CompFun_PseudoHA_ran2:
  "\<lbrakk> States SA1 \<inter> States RootSA = {};
     States SA2 \<inter> (States RootSA \<union> States SA1) = {}; 
     S \<in> States RootSA \<rbrakk> \<Longrightarrow>  
     (ran (CompFun ((PseudoHA RootSA D) [++] (S,SA1) [++] (S,SA2)))) = (insert {} {{SA2,SA1}})"
apply (subst AddSA_CompFun_ran) 
prefer 3
apply (subst AddSA_CompFun_the)
apply simp
apply simp
apply (subst AddSA_CompFun_PseudoHA_ran)
apply fast
apply fast
apply (subst AddSA_CompFun_the)
apply simp
apply simp
apply simp
apply fast
apply (simp add: AddSA_HAStates)
apply (simp add: AddSA_HAStates)
done

lemma AddSA_HAInitStates [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> HAStates A \<rbrakk> \<Longrightarrow>
   HAInitStates (A [++] (S,SA)) = insert (InitState SA) (HAInitStates A)"
apply (unfold HAInitStates_def)
apply (simp add: AddSA_SAs)
done

lemma AddSA_HAInitState [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> HAStates A \<rbrakk> \<Longrightarrow>
  HAInitState (A [++] (S,SA)) = (HAInitState A)"
apply (unfold HAInitState_def)
apply (simp add: AddSA_HARoot)
done

lemma AddSA_Chi [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
   S \<in> HAStates A \<rbrakk> \<Longrightarrow>  
  Chi (A [++] (S,SA)) S = (States SA) \<union> (Chi A S)"
apply (unfold Chi_def restrict_def)
apply (simp add: AddSA_SAs AddSA_HAStates AddSA_CompFun_the)
apply auto
done

lemma AddSA_Chi2 [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> HAStates A;  
    T \<in> States SA \<rbrakk> \<Longrightarrow>
    Chi (A [++] (S,SA)) T = {}"
apply (unfold Chi_def restrict_def)
apply (simp add: AddSA_SAs AddSA_HAStates AddSA_CompFun_the2)
done

lemma AddSA_Chi3 [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> HAStates A; 
    T \<notin> States SA; T \<noteq> S \<rbrakk> \<Longrightarrow>
    Chi (A [++] (S,SA)) T = Chi A T"
apply (unfold Chi_def restrict_def)
apply (simp add: AddSA_SAs AddSA_HAStates AddSA_CompFun_the3)
apply auto
done

lemma AddSA_ChiRel [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> HAStates A \<rbrakk> \<Longrightarrow> 
   ChiRel (A [++] (S,SA)) = { (T,T') . T = S \<and> T' \<in> States SA } \<union> (ChiRel A)" 
apply (unfold ChiRel_def)
apply (simp add: AddSA_HAStates)
apply safe
apply (rename_tac T U)
apply (case_tac "T \<in> States SA")
apply simp
apply simp
apply (rename_tac T U)
apply (case_tac "T \<noteq> S")
apply (case_tac "T \<in>  States SA")
apply simp
apply simp
apply simp
apply (rename_tac T U)
apply (case_tac "T \<in>  States SA")
apply simp
apply simp
apply (cut_tac A=A and T=T in Chi_HAStates)
apply fast
apply (case_tac "T \<in> States SA")
apply simp
apply simp
apply (cut_tac A=A and T=T in Chi_HAStates)
apply fast
apply fast
apply (rename_tac T U)
apply (case_tac "T \<noteq> S")
apply (case_tac "T \<in> States SA")
apply simp
apply simp
apply simp
apply (rename_tac T U)
apply (case_tac "T \<in>  States SA")
apply auto
apply (metis AddSA_Chi AddSA_Chi3 Int_iff Un_iff empty_iff)
done

lemma help_InitConf:
  "\<lbrakk>States SA \<inter> HAStates A = {} \<rbrakk> \<Longrightarrow> {p. fst p \<noteq> InitState SA \<and> snd p \<noteq> InitState SA \<and> 
       p \<in>  insert (InitState SA) (HAInitStates A) \<times> insert (InitState SA) (HAInitStates A) \<and>  
       (p \<in>  {S} \<times> States SA \<or>  p \<in>  ChiRel A)} = 
   (HAInitStates A \<times> HAInitStates A \<inter>  ChiRel A)"    
apply auto
apply (cut_tac A=SA in InitState_States)
apply (cut_tac A=A in HAInitStates_HAStates, fast)
apply (cut_tac A=SA in InitState_States)
apply (cut_tac A=A in HAInitStates_HAStates, fast)
done
 
lemma AddSA_InitConf [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<in> InitConf A \<rbrakk> \<Longrightarrow> 
    InitConf (A [++] (S,SA)) = insert (InitState SA) (InitConf A)"
apply (frule InitConf_HAStates2)
apply (unfold InitConf_def)
apply (simp del: insert_Times_insert)
apply auto
apply (rename_tac T)
apply (case_tac "T=S")
apply auto
prefer 3
apply (rule_tac R="(HAInitStates A) \<times> (HAInitStates A) \<inter> ChiRel A" in trancl_subseteq)
apply auto
apply (rotate_tac 3)
apply (frule trancl_collect)
prefer 2
apply fast
apply auto
apply (cut_tac A=SA in InitState_States)
apply (frule ChiRel_HAStates)
apply fast
apply (frule ChiRel_HAStates)
apply (cut_tac A=SA in InitState_States)
apply fast
apply (frule ChiRel_HAStates)
apply (cut_tac A=SA in InitState_States)
apply fast
apply (subst help_InitConf [THEN sym])
apply fast
apply auto
apply (rule_tac b=S in rtrancl_into_rtrancl)
apply auto
prefer 2
apply (erule rtranclE)
apply auto
prefer 2
apply (erule rtranclE)
apply auto
apply (rule_tac R="(HAInitStates A) \<times> (HAInitStates A) \<inter> ChiRel A" in trancl_subseteq)
apply auto
done

lemma AddSA_InitConf2 [simp]:
 "\<lbrakk> States SA \<inter> HAStates A = {};
    S \<notin> InitConf A;
  S \<in> HAStates A \<rbrakk> \<Longrightarrow>
  InitConf (A [++] (S,SA)) = InitConf A"
apply (unfold InitConf_def)
apply simp
apply auto
apply (rename_tac T)
prefer 2
apply (rule_tac R="(HAInitStates A) \<times> (HAInitStates A) \<inter> ChiRel A" in trancl_subseteq)
apply auto
apply (case_tac "T=InitState SA")
apply auto
prefer 2
apply (rotate_tac 3)
apply (frule trancl_collect)
prefer 2
apply fast
apply auto
apply (cut_tac A=SA in InitState_States)
apply (frule ChiRel_HAStates)
apply fast
apply (cut_tac A=SA in InitState_States)
apply (frule ChiRel_HAStates)
apply fast
apply (cut_tac A=SA in InitState_States)
apply (cut_tac A=A in HAInitStates_HAStates)
apply fast
apply (subst help_InitConf [THEN sym])
apply fast
apply auto
apply (rule_tac b="InitState SA" in rtrancl_induct)
apply auto
apply (frule ChiRel_HAStates2)
apply (cut_tac A=SA in InitState_States)
apply fast
prefer 2
apply (frule ChiRel_HAStates)
apply (cut_tac A=SA in InitState_States)
apply fast
apply (rule rtrancl_into_rtrancl)
apply auto
apply (rule rtrancl_into_rtrancl)
apply auto
done

subsection "Theorems for Calculating Wellformedness of HA"

lemma PseudoHA_HAStates_IFF:
 "(States SA) = X  \<Longrightarrow> (HAStates (PseudoHA SA D)) = X"
apply simp
done

lemma AddSA_SAs_IFF:
 "\<lbrakk> States SA \<inter> HAStates HA = {};
    S \<in> HAStates HA;
    (SAs HA) = X \<rbrakk> \<Longrightarrow> (SAs (HA [++] (S, SA))) = (insert SA X)"
apply (subst AddSA_SAs)
apply auto
done

lemma AddSA_Events_IFF:
 "\<lbrakk> States SA \<inter> HAStates HA = {}; 
    S \<in> HAStates HA; 
    (HAEvents HA) = HAE;
    (SAEvents SA) = SAE;  
    (HAE \<union> SAE) = X \<rbrakk> \<Longrightarrow> (HAEvents (HA [++] (S, SA))) = X"
apply (subst AddSA_Events)
apply auto
done

lemma AddSA_CompFun_IFF:
 "\<lbrakk> States SA \<inter>  HAStates HA = {};
    S \<in> HAStates HA;
    (CompFun HA) = HAG;
    (HAG [f+] (S, SA)) = X \<rbrakk> \<Longrightarrow> (CompFun (HA [++] (S, SA))) = X"
apply (subst AddSA_CompFun)
apply auto
done

lemma AddSA_HAStates_IFF: 
 "\<lbrakk> States SA \<inter> HAStates HA = {};
    S \<in> HAStates HA;
    (HAStates HA) = HAS;
    (States SA) = SAS;
    (HAS \<union> SAS) = X \<rbrakk> \<Longrightarrow> (HAStates (HA [++] (S, SA))) = X"
apply (subst AddSA_HAStates)
apply auto
done

lemma AddSA_HAInitValue_IFF:
 "\<lbrakk> States SA \<inter> HAStates HA = {};
    S \<in> HAStates HA;
    (HAInitValue HA) = X \<rbrakk> \<Longrightarrow> (HAInitValue (HA [++] (S, SA))) = X"
apply (subst AddSA_HAInitValue)
apply auto
done

lemma AddSA_HARoot_IFF:
 "\<lbrakk> States SA \<inter> HAStates HA = {};
    S \<in> HAStates HA;
    (HARoot HA) = X \<rbrakk> \<Longrightarrow> (HARoot (HA [++] (S, SA))) = X"
apply (subst AddSA_HARoot)
apply auto
done

lemma AddSA_InitConf_IFF:
 "\<lbrakk> InitConf A = Y;
    States SA \<inter> HAStates A = {};
    S \<in> HAStates A; 
    (if S \<in> Y then insert (InitState SA) Y else Y) = X \<rbrakk> \<Longrightarrow> 
    InitConf (A [++] (S,SA)) = X" 
apply (case_tac "S \<in> Y")
apply auto
done

lemma AddSA_CompFun_ran_IFF:
  "\<lbrakk> (States SA \<inter> HAStates A) = {}; 
     S \<in> HAStates A;
     (insert {} (insert (insert SA (the ((CompFun A) S))) (ran (CompFun A) - {the ((CompFun A) S)}))) = X \<rbrakk> \<Longrightarrow>
     ran (CompFun (A [++] (S,SA))) = X"
apply (subst  AddSA_CompFun_ran)
apply auto
done

lemma AddSA_CompFun_ran2_IFF:
 "\<lbrakk> (States SA1 \<inter> HAStates A) = {}; 
    (States SA2 \<inter> (HAStates A \<union> States SA1)) = {};
    S \<in> HAStates A;
    T \<in> States SA1;
    insert {} (insert {SA2} (ran (CompFun (A  [++] (S,SA1))))) = X \<rbrakk> \<Longrightarrow>
    ran (CompFun ((A [++] (S,SA1)) [++] (T,SA2))) = X"
apply (subst AddSA_CompFun_ran2)
apply auto
done
   
lemma AddSA_CompFun_ran3_IFF:
 "\<lbrakk> (States SA1 \<inter> HAStates A) = {};
    (States SA2 \<inter> (HAStates A \<union> States SA1)) = {};
    (States SA3 \<inter> (HAStates A \<union> States SA1 \<union> States SA2)) = {};
     S \<in> HAStates A;
     T \<in> States SA1;
     insert {} (insert {SA3,SA2} (ran (CompFun (A  [++] (S,SA1))))) = X \<rbrakk> \<Longrightarrow>
     ran (CompFun ((A [++] (S,SA1)) [++] (T,SA2) [++] (T,SA3))) = X" 
apply (subst AddSA_CompFun_ran3)
apply auto
done

lemma AddSA_CompFun_PseudoHA_ran_IFF:
  "\<lbrakk> S \<in> States RootSA; 
     States RootSA \<inter> States SA = {};
   (insert {} {{SA}}) = X \<rbrakk> \<Longrightarrow> 
   (ran (CompFun ((PseudoHA RootSA D) [++] (S,SA)))) = X"
apply (subst AddSA_CompFun_PseudoHA_ran)
apply auto
done

lemma AddSA_CompFun_PseudoHA_ran2_IFF:
  "\<lbrakk> States SA1 \<inter> States RootSA = {};
     States SA2 \<inter> (States RootSA \<union> States SA1) = {};
     S \<in> States RootSA;
     (insert {} {{SA2,SA1}}) = X \<rbrakk> \<Longrightarrow> 
     (ran (CompFun ((PseudoHA RootSA D) [++] (S,SA1) [++] (S,SA2)))) = X" 
apply (subst AddSA_CompFun_PseudoHA_ran2)
apply auto
done


ML \<open>

val AddSA_SAs_IFF = @{thm AddSA_SAs_IFF};
val AddSA_Events_IFF = @{thm AddSA_Events_IFF};
val AddSA_CompFun_IFF = @{thm AddSA_CompFun_IFF};
val AddSA_HAStates_IFF = @{thm AddSA_HAStates_IFF};
val PseudoHA_HAStates_IFF = @{thm PseudoHA_HAStates_IFF};
val AddSA_HAInitValue_IFF = @{thm AddSA_HAInitValue_IFF};
val AddSA_CompFun_ran_IFF = @{thm AddSA_CompFun_ran_IFF};
val AddSA_HARoot_IFF = @{thm AddSA_HARoot_IFF};
val insert_inter = @{thm insert_inter};
val insert_notmem = @{thm insert_notmem};
val PseudoHA_CompFun = @{thm PseudoHA_CompFun};
val PseudoHA_Events = @{thm PseudoHA_Events};
val PseudoHA_SAs = @{thm PseudoHA_SAs};
val PseudoHA_HARoot = @{thm PseudoHA_HARoot};
val PseudoHA_HAInitValue = @{thm PseudoHA_HAInitValue};
val PseudoHA_CompFun_ran = @{thm PseudoHA_CompFun_ran};
val Un_empty_right = @{thm Un_empty_right};
val insert_union = @{thm insert_union};


fun wellformed_tac ctxt L i =
  FIRST[resolve_tac ctxt [AddSA_SAs_IFF] i,
        resolve_tac ctxt [AddSA_Events_IFF] i,
        resolve_tac ctxt [AddSA_CompFun_IFF] i,
        resolve_tac ctxt [AddSA_HAStates_IFF] i,
        resolve_tac ctxt [PseudoHA_HAStates_IFF] i,
        resolve_tac ctxt [AddSA_HAInitValue_IFF] i,
        resolve_tac ctxt [AddSA_HARoot_IFF] i,
        resolve_tac ctxt [AddSA_CompFun_ran_IFF] i,
        resolve_tac ctxt [insert_inter] i,
        resolve_tac ctxt [insert_notmem] i,
        CHANGED (simp_tac (put_simpset HOL_basic_ss ctxt addsimps
           [PseudoHA_HARoot, PseudoHA_CompFun, PseudoHA_CompFun_ran,PseudoHA_Events,PseudoHA_SAs,insert_union,
            PseudoHA_HAInitValue,Un_empty_right]@ L) i),
        fast_tac ctxt i,
        CHANGED (simp_tac ctxt i)];
\<close>

method_setup wellformed  = \<open>Attrib.thms >> (fn thms => fn ctxt => (METHOD (fn facts => 
                                       (HEADGOAL (wellformed_tac ctxt (facts @ thms))))))\<close>

end
