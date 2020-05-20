(*  Title:      statecharts/HA/HA.thy

    Author:     Steffen Helke, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Syntax of Hierarchical Automata\<close>
theory HA
imports SA
begin

subsection \<open>Definitions\<close>

(* unique root automaton *)

definition
  RootEx :: "[(('s,'e,'d)seqauto) set,
              's \<rightharpoonup>  ('s,'e,'d) seqauto set] => bool" where
  "RootEx F G = (\<exists>! A. A \<in> F \<and> A \<notin> \<Union> (ran G))"

definition
  Root :: "[(('s,'e,'d)seqauto) set,
            's \<rightharpoonup> ('s,'e,'d) seqauto set]
           => ('s,'e,'d) seqauto" where
  "Root F G = (@ A. A \<in> F \<and>  A \<notin> \<Union> (ran G))"

(* mutually distinct state spaces *)

definition
  MutuallyDistinct :: "(('s,'e,'d)seqauto) set => bool" where
  "MutuallyDistinct F =
        (\<forall> a \<in> F. \<forall> b \<in> F. a \<noteq> b \<longrightarrow> (States a) \<inter> (States b) = {})"

(* exactly one ancestor for every non root automaton *)

definition
 OneAncestor :: "[(('s,'e,'d)seqauto) set,
                   's \<rightharpoonup> ('s,'e,'d) seqauto set] => bool" where
 "OneAncestor F G =
                (\<forall> A \<in> F - {Root F G} .
                    \<exists>! s. s \<in> (\<Union> A' \<in> F - {A} . States A') \<and> 
                         A \<in> the (G s))"

(* composition function contains no cycles *)

definition
  NoCycles :: "[(('s,'e,'d)seqauto) set,
                   's \<rightharpoonup> ('s,'e,'d) seqauto set] => bool" where
  "NoCycles F G =
       (\<forall> S \<in> Pow (\<Union> A \<in> F. States A).
           S \<noteq> {} \<longrightarrow>  (\<exists> s \<in> S. S \<inter> (\<Union> A \<in> the (G s). States A) = {}))"
 
(* properties of composition functions *)

definition
  IsCompFun :: "[(('s,'e,'d)seqauto) set,
                    's \<rightharpoonup> ('s,'e,'d) seqauto set] => bool" where
  "IsCompFun F G = ((dom G = (\<Union> A \<in> F. States A)) \<and> 
                    (\<Union> (ran G) = (F - {Root F G})) \<and> 
                    (RootEx F G) \<and> 
                    (OneAncestor F G) \<and> 
                    (NoCycles F G))"

subsubsection \<open>Well-formedness for the syntax of HA\<close>

definition
  HierAuto :: "['d data,
                 (('s,'e,'d)seqauto) set,
                'e set,
                's \<rightharpoonup> (('s,'e,'d)seqauto) set]
                => bool" where
  "HierAuto D F E G = ((\<Union> A \<in> F. SAEvents A) \<subseteq> E \<and> 
                       MutuallyDistinct F \<and> 
                       finite F \<and> 
                       IsCompFun F G)"

lemma HierAuto_EmptySet:
 "((@x. True),{Abs_seqauto ({@x. True}, (@x. True), {}, {})}, {}, 
  Map.empty ( @x. True \<mapsto> {})) \<in> {(D,F,E,G) | D F E G. HierAuto D F E G}"
apply (unfold HierAuto_def IsCompFun_def Root_def RootEx_def MutuallyDistinct_def
           OneAncestor_def NoCycles_def)
apply auto
done

definition
  "hierauto =
    {(D,F,E,G) |
        (D::'d data)
        (F::(('s,'e,'d) seqauto) set)
        (E::('e set))
        (G::('s \<rightharpoonup> (('s,'e,'d) seqauto) set)).
                                HierAuto D F E G}"

typedef ('s,'e,'d) hierauto =
    "hierauto :: ('d data * ('s,'e,'d) seqauto set * 'e set * ('s \<rightharpoonup> ('s,'e,'d) seqauto set)) set"
  unfolding hierauto_def
  apply (rule exI)
  apply (rule HierAuto_EmptySet)
  done

definition
  SAs :: "(('s,'e,'d) hierauto)  => (('s,'e,'d) seqauto) set" where
  "SAs = fst o snd o Rep_hierauto"

definition
  HAEvents :: "(('s,'e,'d) hierauto) => ('e set)" where
  "HAEvents = fst o snd o snd o Rep_hierauto"

definition
  CompFun :: "(('s,'e,'d) hierauto) => ('s \<rightharpoonup> ('s,'e,'d) seqauto set)" where
  "CompFun = (snd o snd o snd o Rep_hierauto)"

definition
  HAStates :: "(('s,'e,'d) hierauto) => ('s set)" where
  "HAStates HA = (\<Union>  A \<in> (SAs HA). States A)"

definition
  HADelta :: "(('s,'e,'d) hierauto) => (('s,'e,'d)trans)set" where
  "HADelta HA = (\<Union> F \<in> (SAs HA). Delta F)"

definition
  HAInitValue :: "(('s,'e,'d) hierauto) => 'd data" where
  "HAInitValue == fst o Rep_hierauto"

definition
  HAInitStates :: "(('s,'e,'d) hierauto) => 's set" where
  "HAInitStates HA == \<Union> A \<in> (SAs HA). { InitState A }"

definition
  HARoot :: "(('s,'e,'d) hierauto) => ('s,'e,'d)seqauto" where
  "HARoot HA == Root (SAs HA) (CompFun HA)"

definition
  HAInitState :: "(('s,'e,'d) hierauto) => 's" where
  "HAInitState HA == InitState (HARoot HA)"

subsubsection \<open>State successor function\<close>

(* state successor function Chi *)
  
definition
  Chi   :: "('s,'e,'d)hierauto => 's => 's set" where
  "Chi A ==  (\<lambda>  S \<in>  (HAStates A) .
                 {S'. \<exists> SA \<in> (SAs A) . SA \<in> the ((CompFun A) S) \<and> S' \<in> States SA })"

(* direct state successor relation ChiRel *)

definition
  ChiRel :: "('s,'e,'d)hierauto => ('s *'s) set" where
  "ChiRel A == { (S,S'). S \<in> HAStates A \<and> S' \<in> HAStates A \<and> S' \<in> (Chi A) S }"

(* indirect state successor relation ChiPlus *)

definition
  ChiPlus :: "('s,'e,'d)hierauto => ('s *'s) set" where
  "ChiPlus A == (ChiRel A) ^+"

definition
  ChiStar :: "('s,'e,'d)hierauto => ('s *'s) set" where
  "ChiStar A == (ChiRel A) ^*"

(* priority on transitions that are successors *)

definition
  HigherPriority :: "[('s,'e,'d)hierauto,
                      ('s,'e,'d)trans * ('s,'e,'d)trans] => bool" where
  "HigherPriority A ==
             \<lambda> (t,t') \<in> (HADelta A) \<times> (HADelta A).
                          (source t',source t) \<in>  ChiPlus A"

subsubsection \<open>Configurations\<close>

(* initial configuration *)

definition
  InitConf :: "('s,'e,'d)hierauto => 's set" where
  "InitConf A == (((((HAInitStates A) \<times> (HAInitStates A)) \<inter> (ChiRel A))^* )
                     `` {HAInitState A})"

(*  -------------------------------------------------------------- *)
(*  First, the original definition calculating a step on           *)
(*  configurations given by                                        *)
(*                                                                 *)
(*  E. Mikk, Y. Lakhnech, and M. Siegel. Hierarchical automata as  *)
(*  model for statecharts. In Asian Computing Science Conference   *)
(*  (ASIAN~97), Springer LNCS, 1345, 1997.                         *)
(*                                                                
    "StepConf A C TS ==                                           
       (C - ((ChiStar A) `` (Source TS))) \<union>                       
        (Target TS) \<union> (((ChiPlus A) `` (Target TS)) 
                    \<inter> (HAInitStates A))"           
                                                                   *)
(*                                                                 *)
(* Note, that this semantic definition not preserves the           *)
(* well-formedness of a Statecharts. Hence we use our definition.  *)
(*  -------------------------------------------------------------- *)

(* step on configurations *)

definition
  StepConf  :: "[('s,'e,'d)hierauto, 's set,
                 ('s,'e,'d)trans set] => 's set" where

  "StepConf A C TS ==
               (C - ((ChiStar A) `` (Source TS))) \<union> 
               (Target TS) \<union>
               ((ChiRel A) `` (Target TS)) \<inter> (HAInitStates A) \<union>
               ((((ChiRel A) \<inter> ((HAInitStates A) \<times> (HAInitStates A)))\<^sup>+) 
                   `` (((ChiRel A)`` (Target TS)) \<inter> (HAInitStates A)))"

subsection \<open>Lemmas\<close>

lemma Rep_hierauto_tuple:
"Rep_hierauto HA = (HAInitValue HA, SAs HA, HAEvents HA, CompFun HA)"
by (unfold SAs_def HAEvents_def CompFun_def HAInitValue_def, simp)

lemma Rep_hierauto_select: 
  "(HAInitValue HA, SAs HA, HAEvents HA, CompFun HA): hierauto"
by (rule Rep_hierauto_tuple [THEN subst], rule Rep_hierauto)

lemma HierAuto_select [simp]: 
  "HierAuto (HAInitValue HA) (SAs HA) (HAEvents HA) (CompFun HA)"
by (cut_tac Rep_hierauto_select, unfold hierauto_def, simp)

subsubsection \<open>\<open>HAStates\<close>\<close>

lemma finite_HAStates [simp]:
  "finite (HAStates HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply auto
apply (simp add: HAStates_def)
apply (rule finite_UN_I)
apply fast
apply (rule finite_States)
done

lemma HAStates_SA_mem:
 "\<lbrakk> SA \<in> SAs A; S \<in> States SA \<rbrakk> \<Longrightarrow> S \<in> HAStates A"
by (unfold HAStates_def, auto)

lemma ChiRel_HAStates [simp]:
 "(a,b) \<in> ChiRel A \<Longrightarrow> a \<in> HAStates A"
apply (unfold ChiRel_def)
apply auto
done

lemma ChiRel_HAStates2 [simp]:
 "(a,b) \<in>  ChiRel A \<Longrightarrow> b \<in> HAStates A"
apply (unfold ChiRel_def)
apply auto
done

subsubsection \<open>\<open>HAEvents\<close>\<close>

lemma HAEvents_SAEvents_SAs:
  "\<Union>(SAEvents ` (SAs HA)) \<subseteq> HAEvents HA"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply fast
done

subsubsection \<open>\<open>NoCycles\<close>\<close>

lemma NoCycles_EmptySet [simp]:
  "NoCycles {} S"
by (unfold NoCycles_def, auto)

lemma NoCycles_HA [simp]: 
  "NoCycles (SAs HA) (CompFun HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def IsCompFun_def)
apply auto
done

subsubsection \<open>\<open>OneAncestor\<close>\<close>

lemma OneAncestor_HA [simp]:
  "OneAncestor (SAs HA) (CompFun HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def IsCompFun_def)
apply auto
done

subsubsection \<open>\<open>MutuallyDistinct\<close>\<close>

lemma MutuallyDistinct_Single [simp]:
  "MutuallyDistinct {SA}"
by (unfold MutuallyDistinct_def, auto)

lemma MutuallyDistinct_EmptySet [simp]:
  "MutuallyDistinct {}"
by (unfold MutuallyDistinct_def, auto)

lemma MutuallyDistinct_Insert:
  "\<lbrakk> MutuallyDistinct S; (States A) \<inter>  (\<Union> B \<in> S. States B) = {} \<rbrakk>
  \<Longrightarrow> MutuallyDistinct (insert A S)"
by (unfold MutuallyDistinct_def, safe, fast+)

lemma MutuallyDistinct_Union:
  "\<lbrakk> MutuallyDistinct A; MutuallyDistinct B;
  (\<Union> C \<in> A. States C) \<inter> (\<Union> C \<in> B. States C) = {} \<rbrakk>
  \<Longrightarrow> MutuallyDistinct (A \<union> B)"
by (unfold MutuallyDistinct_def, safe, blast+)

lemma MutuallyDistinct_HA [simp]:
  "MutuallyDistinct (SAs HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def IsCompFun_def)
apply auto
done

subsubsection \<open>\<open>RootEx\<close>\<close>

lemma RootEx_Root [simp]:
  "RootEx F G \<Longrightarrow> Root F G \<in> F"
apply (unfold RootEx_def Root_def)
apply (erule ex1E)
apply (erule conjE)
apply (rule someI2)
apply blast+
done

lemma RootEx_Root_ran [simp]:
  "RootEx F G \<Longrightarrow> Root F G \<notin> \<Union> (ran G)"
apply (unfold RootEx_def Root_def)
apply (erule ex1E)
apply (erule conjE)
apply (rule someI2)
apply blast+
done

lemma RootEx_States_Subset [simp]:
  "(RootEx F G) \<Longrightarrow> States (Root F G) \<subseteq> (\<Union> x \<in> F . States x)"
apply (unfold RootEx_def Root_def)
apply (erule ex1E)
apply (erule conjE)
apply (rule someI2)
apply fast
apply (unfold UNION_eq)
apply (simp add: subset_eq)
apply auto
done

lemma RootEx_States_notdisjunct [simp]:
  "RootEx F G \<Longrightarrow> States (Root F G) \<inter> (\<Union> x \<in> F . States x) \<noteq> {}"
apply (frule RootEx_States_Subset)
apply (case_tac "States (Root F G)={}")
prefer 2
apply fast
apply simp
done

lemma Root_neq_SA [simp]:
  "\<lbrakk> RootEx F G; (\<Union> x \<in> F . States x) \<inter> States SA = {} \<rbrakk> \<Longrightarrow> Root F G \<noteq> SA"
apply (rule  SA_States_disjunct)
apply (frule RootEx_States_Subset)
apply fast
done

lemma RootEx_HA [simp]:
  "RootEx (SAs HA) (CompFun HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def IsCompFun_def)
apply fast
done

subsubsection \<open>\<open>HARoot\<close>\<close>

lemma HARoot_SAs [simp]:  
  "(HARoot HA) \<in> SAs HA"
apply (unfold HARoot_def)
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply auto
done

lemma States_HARoot_HAStates:
  "States (HARoot HA) \<subseteq>  HAStates HA"
apply (unfold HAStates_def)
apply auto
apply (rule_tac x="HARoot HA" in bexI)
apply auto
done

lemma SAEvents_HARoot_HAEvents:
  "SAEvents (HARoot HA) \<subseteq> HAEvents HA"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply auto
apply (rename_tac S)
apply (unfold UNION_eq)
apply (simp add: subset_eq)
apply (erule_tac x=S in allE)
apply auto
done

lemma HARoot_ran_CompFun:
  "HARoot HA \<notin> Union (ran (CompFun HA))"
apply (unfold HARoot_def)
apply (cut_tac Rep_hierauto_select)
apply (unfold IsCompFun_def hierauto_def HierAuto_def)
apply fast
done

lemma HARoot_ran_CompFun2:
  "S \<in> ran (CompFun HA) \<longrightarrow> HARoot HA \<notin> S"
apply (unfold HARoot_def)
apply (cut_tac Rep_hierauto_select)
apply (unfold IsCompFun_def hierauto_def HierAuto_def)
apply fast
done

subsubsection \<open>\<open>CompFun\<close>\<close>

lemma IsCompFun_HA [simp]:
  "IsCompFun (SAs HA) (CompFun HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply auto
done

lemma dom_CompFun [simp]:
  "dom (CompFun HA) = HAStates HA"
apply (cut_tac HA=HA in IsCompFun_HA)
apply (unfold IsCompFun_def HAStates_def)
apply auto
done

lemma ran_CompFun [simp]:
  "Union (ran (CompFun HA)) = ((SAs HA) - {Root  (SAs HA)(CompFun HA)})"
apply (cut_tac HA=HA in IsCompFun_HA)
apply (unfold IsCompFun_def)
apply fast
done

lemma ran_CompFun_subseteq:
  "Union (ran (CompFun HA)) \<subseteq> (SAs HA)"
apply (cut_tac HA=HA in IsCompFun_HA)
apply (unfold IsCompFun_def)
apply fast
done

lemma ran_CompFun_is_not_SA:
  "\<not> Sas \<subseteq> (SAs HA) \<Longrightarrow> Sas \<notin> (ran (CompFun HA))"
apply (cut_tac HA=HA in IsCompFun_HA)
apply (unfold IsCompFun_def)
apply fast
done

lemma HAStates_HARoot_CompFun [simp]:
  "S \<in> HAStates HA \<Longrightarrow> HARoot HA \<notin> the (CompFun HA S)"
apply (rule ran_dom_the)
back
apply (simp add: HARoot_ran_CompFun2 HARoot_def HAStates_def)+
done

lemma HAStates_CompFun_SAs:
 "S \<in> HAStates A \<Longrightarrow> the (CompFun A S) \<subseteq> SAs A"
apply auto
apply (rename_tac T)
apply (cut_tac HA=A in ran_CompFun)
apply (erule equalityE)
apply (erule_tac c=T in subsetCE)
apply (drule ran_dom_the)
apply auto
done

lemma HAStates_CompFun_notmem [simp]:
  "\<lbrakk> S \<in> HAStates A; SA \<in> the (CompFun A S) \<rbrakk> \<Longrightarrow> S \<notin> States SA"
apply (unfold HAStates_def)
apply auto
apply (rename_tac T)
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (erule_tac x=T in ballE)
apply auto
prefer 2
apply (cut_tac A=A and S=S in  HAStates_CompFun_SAs)
apply (unfold HAStates_def)
apply simp
apply fast
apply fast
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="{S}" in ballE)
apply auto
done

lemma CompFun_Int_disjoint: 
  "\<lbrakk> S \<noteq> T; S \<in>  HAStates A; T \<in>  HAStates A \<rbrakk> \<Longrightarrow> the (CompFun A T) \<inter> the (CompFun A S) = {}" 
apply auto
apply (rename_tac U)
apply (cut_tac HA=A in OneAncestor_HA)
apply (unfold OneAncestor_def)
apply (erule_tac x=U in ballE)
prefer 2
apply simp
apply (fold HARoot_def)
apply (frule HAStates_HARoot_CompFun)
apply simp
apply (frule HAStates_CompFun_SAs)
apply auto
apply (erule_tac x=S in allE)
apply (erule_tac x=T in allE)
apply auto
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (simp only: HAStates_def)
apply safe
apply (erule_tac x="{S}" in ballE)
apply simp
apply fast
apply simp
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (simp only: HAStates_def)
apply safe
apply (erule_tac x="{T}" in ballE)
apply simp
apply fast
apply simp
done

subsubsection \<open>\<open>SAs\<close>\<close>

lemma finite_SAs [simp]:
  "finite (SAs HA)"
apply (cut_tac Rep_hierauto_select)
apply (unfold hierauto_def HierAuto_def)
apply fast
done

lemma HAStates_SAs_disjunct:
  "HAStates HA1 \<inter> HAStates HA2 = {} \<Longrightarrow> SAs HA1 \<inter> SAs HA2 = {}"
apply (unfold UNION_eq HAStates_def Int_def)
apply auto
apply (rename_tac SA)
apply (cut_tac SA=SA in EX_State_SA)
apply (erule exE)
apply auto
done

lemma HAStates_CompFun_SAs_mem [simp]:
 "\<lbrakk> S \<in> HAStates A; T \<in> the (CompFun A S) \<rbrakk> \<Longrightarrow> T \<in> SAs A" 
apply (cut_tac A=A and S=S in HAStates_CompFun_SAs)
apply auto
done 

lemma SAs_States_HAStates:
 "SA \<in> SAs A \<Longrightarrow> States SA \<subseteq> HAStates A"
by (unfold HAStates_def, auto)

subsubsection \<open>\<open>HAInitState\<close>\<close>

lemma HAInitState_HARoot [simp]:
  "HAInitState A \<in> States (HARoot A)"
by (unfold HAInitState_def, auto)

lemma HAInitState_HARoot2 [simp]:
  "HAInitState A \<in> States (Root (SAs A) (CompFun A))"
by (fold HARoot_def, simp)

lemma HAInitStates_HAStates [simp]:
  "HAInitStates A \<subseteq> HAStates A"
apply (unfold HAInitStates_def HAStates_def)
apply auto
done

lemma HAInitStates_HAStates2 [simp]:
  "S \<in> HAInitStates A \<Longrightarrow> S \<in> HAStates A"
apply (cut_tac A=A in HAInitStates_HAStates)
apply fast
done

lemma HAInitState_HAStates [simp]:
  "HAInitState A \<in> HAStates A"
apply (unfold HAStates_def)
apply auto
apply (rule_tac x="HARoot A" in bexI)
apply auto
done

lemma HAInitState_HAInitStates [simp]:
  "HAInitState A \<in> HAInitStates A"
by (unfold HAInitStates_def HAInitState_def, auto)


lemma CompFun_HAInitStates_HAStates [simp]:
 "\<lbrakk> S \<in> HAStates A; SA \<in> the (CompFun A S) \<rbrakk> \<Longrightarrow> (InitState SA) \<in> HAInitStates A"
apply (unfold HAInitStates_def)
apply auto
done

lemma CompFun_HAInitState_HAInitStates [simp]:
 "\<lbrakk> SA \<in> the (CompFun A (HAInitState A)) \<rbrakk> \<Longrightarrow> (InitState SA) \<in> HAInitStates A"
apply (unfold HAInitStates_def)
apply auto
apply (rule_tac x=SA in bexI)
apply auto
apply (cut_tac A=A and S="HAInitState A" in HAStates_CompFun_SAs)
apply auto
done

lemma HAInitState_notmem_States [simp]: 
  "\<lbrakk> S \<in> HAStates A; SA \<in> the (CompFun A S) \<rbrakk> \<Longrightarrow> HAInitState A \<notin> States SA"
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (erule_tac x="HARoot A" in ballE)
apply auto
done

lemma InitState_notmem_States [simp]: 
  "\<lbrakk> S \<in> HAStates A; SA \<in> the (CompFun A S); 
     T \<in> HAInitStates A; T \<noteq> InitState SA \<rbrakk> 
    \<Longrightarrow>  T \<notin> States SA"
apply (unfold HAInitStates_def)
apply auto
apply (rename_tac SAA)
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (erule_tac x=SAA in ballE)
apply auto
done

lemma InitState_States_notmem [simp]:
    "\<lbrakk> B \<in> SAs A; C \<in> SAs A; B \<noteq> C \<rbrakk> \<Longrightarrow> InitState B \<notin> States C"
apply auto
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply force
done

lemma OneHAInitState_SAStates:
   "\<lbrakk> S \<in> HAInitStates A; T \<in> HAInitStates A;
      S \<in> States SA; T \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> 
      S = T" 
apply (unfold HAInitStates_def)
apply auto
apply (rename_tac AA AAA)
apply (case_tac "AA = SA")
apply auto
apply (case_tac "AAA = SA")
apply auto
done

subsubsection \<open>\<open>Chi\<close>\<close>

lemma HARootStates_notmem_Chi [simp]:
  "\<lbrakk> S \<in> HAStates A;  T \<in> States (HARoot A) \<rbrakk> \<Longrightarrow> T \<notin>  Chi A S"
apply (unfold Chi_def restrict_def, auto)
apply (rename_tac SA)
apply (cut_tac HA="A" in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x="HARoot A" in ballE) 
apply (erule_tac x="SA" in ballE)
apply auto
done

lemma SAStates_notmem_Chi [simp]:
  "\<lbrakk> S \<in> States SA; T \<in> States SA;
     SA \<in> SAs A \<rbrakk> \<Longrightarrow> T \<notin> Chi A S"
apply (unfold Chi_def restrict_def, auto)
apply (rename_tac SAA)
apply (cut_tac HA="A" in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x="SAA" in ballE) 
apply (erule_tac x="SA" in ballE)
apply auto
apply (unfold HAStates_def)
apply auto
done

lemma HAInitState_notmem_Chi [simp]:
  "S \<in> HAStates A \<Longrightarrow> HAInitState A \<notin> Chi A S"
by (unfold Chi_def restrict_def, auto)

lemma Chi_HAStates [simp]:
  "T \<in> HAStates A \<Longrightarrow> (Chi A T) \<subseteq> HAStates A"
apply (unfold Chi_def restrict_def)
apply (auto)
apply (cut_tac A=A and S=T in HAStates_CompFun_SAs)
apply (unfold HAStates_def)
apply auto
done

lemma Chi_HAStates_Self [simp]:
  "s \<in>  HAStates a \<Longrightarrow> s \<notin> (Chi a s)"
by (unfold Chi_def restrict_def, auto)

lemma ChiRel_HAStates_Self [simp]:
  "(s,s) \<notin> (ChiRel a)"
by( unfold ChiRel_def, auto)

lemma HAStates_Chi_NoCycles:
  "\<lbrakk> s \<in> HAStates a; t \<in> HAStates a; s \<in> Chi a t \<rbrakk> \<Longrightarrow> t \<notin> Chi a s"
apply (unfold Chi_def restrict_def)
apply auto
apply (cut_tac HA=a in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="{s,t}" in ballE)
apply auto
done

lemma HAStates_Chi_NoCycles_trans:
 "\<lbrakk> s \<in> HAStates a; t \<in> HAStates a; u \<in> HAStates a;
    t \<in> Chi a s; u \<in> Chi a t \<rbrakk> \<Longrightarrow> s \<notin> Chi a u"
apply (unfold Chi_def restrict_def)
apply auto
apply (cut_tac HA=a in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="{s,t,u}" in ballE)
prefer 2
apply simp
apply (unfold HAStates_def)
apply auto
done

lemma Chi_range_disjoint:
  "\<lbrakk> S \<noteq> T; T \<in> HAStates A; S \<in> HAStates A; U \<in> Chi A S \<rbrakk> \<Longrightarrow> U \<notin> Chi A T"  
apply (frule CompFun_Int_disjoint)
apply auto
apply (unfold Chi_def restrict_def)
apply auto
apply (rename_tac SA SAA)
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (erule_tac x=SAA in ballE)
apply auto
done

lemma SAStates_Chi_trans [rule_format]:
  "\<lbrakk> U \<in> Chi A T; S \<in> Chi A U; T \<in> States SA; 
     SA \<in> SAs A; U \<in> HAStates A \<rbrakk> \<Longrightarrow> S \<notin> States SA"
apply (frule HAStates_SA_mem)
apply auto
apply (unfold Chi_def restrict_def)
apply auto
apply (rename_tac SAA SAAA)
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="{U,T}" in ballE)
prefer 2
apply (simp only: HAStates_def) 
apply auto
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (rotate_tac -1)
apply (erule_tac x=SA in ballE)
apply (rotate_tac -1)
apply (erule_tac x=SAAA in ballE)
apply auto
done

subsubsection \<open>\<open>ChiRel\<close>\<close>

lemma finite_ChiRel [simp]:
  "finite (ChiRel A)"
apply (rule_tac B="HAStates A \<times> HAStates A" in finite_subset)
apply auto
done

lemma ChiRel_HAStates_subseteq [simp]:
  "(ChiRel A) \<subseteq> (HAStates A \<times> HAStates A)"  
apply (unfold ChiRel_def Chi_def restrict_def)
apply auto
done

lemma ChiRel_CompFun:
  "s \<in> HAStates a \<Longrightarrow> ChiRel a `` {s} = (\<Union> x \<in> the (CompFun a s). States x)"
apply (unfold ChiRel_def Chi_def restrict_def Image_def)
apply simp
apply auto
apply (frule HAStates_CompFun_SAs_mem)
apply fast
apply (unfold HAStates_def)
apply fast
done

lemma ChiRel_HARoot:
 "\<lbrakk> (x,y) \<in> ChiRel A \<rbrakk> \<Longrightarrow> y \<notin> States (HARoot A)"
apply (unfold ChiRel_def Chi_def)
apply auto 
apply (unfold restrict_def)
apply auto
apply (rename_tac SA)
apply (frule HAStates_HARoot_CompFun)
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply auto
apply (erule_tac x=SA in ballE)
apply (erule_tac x="HARoot A" in ballE)
apply auto
done

lemma HAStates_CompFun_States_ChiRel:
 "S \<in> HAStates A \<Longrightarrow> \<Union> (States ` the (CompFun A S)) = ChiRel A `` {S}"
apply (unfold ChiRel_def Chi_def restrict_def)
apply auto
apply (drule HAStates_CompFun_SAs)
apply (subst HAStates_def)
apply fast
done

lemma HAInitState_notmem_Range_ChiRel [simp]: 
  "HAInitState A \<notin> Range (ChiRel A)"
by (unfold ChiRel_def, auto)

lemma HAInitState_notmem_Range_ChiRel2 [simp]: 
  "(S,HAInitState A) \<notin>  (ChiRel A)"
by (unfold ChiRel_def, auto)

lemma ChiRel_OneAncestor_notmem:
  "\<lbrakk> S \<noteq> T; (S,U) \<in> ChiRel A\<rbrakk> \<Longrightarrow> (T,U) \<notin> ChiRel A"
apply (unfold ChiRel_def)
apply auto
apply (simp only: Chi_range_disjoint)
done

lemma ChiRel_OneAncestor:
  "\<lbrakk> (S1,U) \<in> ChiRel A; (S2,U) \<in> ChiRel A \<rbrakk> \<Longrightarrow> S1 = S2"
apply (rule notnotD, rule notI)
apply (simp add: ChiRel_OneAncestor_notmem)
done

lemma CompFun_ChiRel:
  "\<lbrakk> S1 \<in> HAStates A; SA \<in> the (CompFun A S1); 
     S2 \<in> States SA \<rbrakk> \<Longrightarrow> (S1,S2) \<in> ChiRel A"
apply (unfold ChiRel_def Chi_def restrict_def)
apply auto
apply (cut_tac A=A and S=S1 in HAStates_CompFun_SAs)
apply (unfold HAStates_def)
apply auto
done

lemma CompFun_ChiRel2:
 "\<lbrakk> (S,T) \<in> ChiRel A; T \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> SA \<in> the (CompFun A S)"
apply (unfold ChiRel_def Chi_def restrict_def)
apply auto
apply (rename_tac SAA)
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (rotate_tac -1)
apply (erule_tac x=SAA in ballE) 
apply auto
done

lemma ChiRel_HAStates_NoCycles:
  "(s,t) \<in> (ChiRel a) \<Longrightarrow> (t,s) \<notin> (ChiRel a)"
apply (unfold ChiRel_def)
apply auto
apply (frule HAStates_Chi_NoCycles)
apply auto
done

lemma HAStates_ChiRel_NoCycles_trans:
  "\<lbrakk> (s,t) \<in> (ChiRel a); (t,u) \<in> (ChiRel a) \<rbrakk> \<Longrightarrow> (u,s) \<notin> (ChiRel a)"
apply (unfold ChiRel_def)
apply auto
apply (frule HAStates_Chi_NoCycles_trans)
apply fast
back
back
prefer 3
apply fast
apply auto
done

lemma SAStates_ChiRel:
  "\<lbrakk> S \<in> States SA; T \<in> States SA;
     SA \<in> SAs A \<rbrakk> \<Longrightarrow> (S,T) \<notin> (ChiRel A)"
by (unfold ChiRel_def, auto)

lemma ChiRel_SA_OneAncestor: 
   "\<lbrakk> (S,T) \<in> ChiRel A; T \<in> States SA; 
      U \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> 
      (S,U) \<in> ChiRel A"
apply (frule CompFun_ChiRel2)
apply auto
apply (rule CompFun_ChiRel)
apply auto
done

lemma ChiRel_OneAncestor2: 
  "\<lbrakk> S \<in> HAStates A; S \<notin> States (HARoot A) \<rbrakk> \<Longrightarrow> 
     \<exists>! T. (T,S) \<in> ChiRel A"
apply (unfold ChiRel_def)
apply auto
prefer 2
apply (rename_tac T U)
prefer 2
apply (unfold Chi_def restrict_def)
apply auto
prefer 2
apply (rename_tac SA SAA)
prefer 2
apply (cut_tac HA=A in OneAncestor_HA)
apply (unfold OneAncestor_def)
apply (fold HARoot_def)
apply auto
apply (simp cong: rev_conj_cong)
apply (unfold HAStates_def)
apply auto
apply (rename_tac SA)
apply (erule_tac x=SA in ballE)
apply auto
apply (case_tac "T = U")
apply auto
apply (frule CompFun_Int_disjoint)
apply (unfold HAStates_def)
apply auto
apply (case_tac "SA=SAA")
apply auto
apply (cut_tac HA=A in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SAA in ballE)
apply (erule_tac x=SA in ballE)
apply auto
apply (cut_tac S=T and A=A in HAStates_CompFun_SAs)
apply (unfold HAStates_def)
apply fast
apply fast
apply (cut_tac S=U and A=A in HAStates_CompFun_SAs)
apply (unfold HAStates_def)
apply fast
apply fast
done

lemma HARootStates_notmem_Range_ChiRel [simp]:
  "S \<in> States (HARoot A) \<Longrightarrow> S \<notin> Range (ChiRel A)"
by (unfold ChiRel_def, auto)

lemma ChiRel_int_disjoint:
  "S \<noteq> T \<Longrightarrow> (ChiRel A `` {S}) \<inter> (ChiRel A `` {T}) = {}"  
apply (unfold ChiRel_def)
apply auto
apply (simp only: Chi_range_disjoint)
done

lemma SAStates_ChiRel_trans [rule_format]:
  "\<lbrakk> (S,U) \<in> (ChiRel A); (U,T) \<in> ChiRel A; 
     S \<in> States SA; SA \<in> SAs A  \<rbrakk> \<Longrightarrow> T \<notin> States SA"
apply auto
apply (unfold ChiRel_def)
apply auto
apply (frule SAStates_Chi_trans)
back
apply fast+
done

lemma HAInitStates_InitState_trancl: 
  " \<lbrakk> S \<in> HAInitStates (HA ST); A \<in> the (CompFun (HA ST) S) \<rbrakk> \<Longrightarrow> 
       (S, InitState A) \<in> (ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST))\<^sup>+"
apply (case_tac "S \<in> HAStates (HA ST)") 
apply (frule CompFun_ChiRel)
apply fast+
apply (rule InitState_States)
apply auto
apply (rule r_into_trancl')
apply auto
apply (rule CompFun_HAInitStates_HAStates)
apply auto
done

lemma HAInitStates_InitState_trancl2:
 "\<lbrakk> S \<in> HAStates (HA ST); A \<in> the (CompFun (HA ST) S); 
   (x, S) \<in> (ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST))\<^sup>+ \<rbrakk>
  \<Longrightarrow> (x, InitState A) \<in> (ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST))\<^sup>+"
apply (rule_tac a="x" and b="S" and r="ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST)" in converse_trancl_induct)
apply auto
prefer 2
apply (rename_tac T U)
prefer 2
apply (case_tac "S \<in> HAStates (HA ST)") 
apply (frule CompFun_ChiRel)
apply fast
apply (rule InitState_States)
apply simp
apply (rule trancl_trans [of _ S])
apply (rule r_into_trancl')
apply auto
apply (rule r_into_trancl')
apply auto
apply (rule CompFun_HAInitStates_HAStates)
prefer 2
apply fast
apply (cut_tac A="HA ST" in HAInitStates_HAStates, fast)
apply (rule_tac y = U in trancl_trans)
apply (rule r_into_trancl')
apply auto
done

subsubsection \<open>\<open>ChiPlus\<close>\<close>

lemma ChiPlus_ChiRel [simp]:
  "(S,T) \<in> ChiRel A \<Longrightarrow> (S,T) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply (frule r_into_trancl)
apply auto
done

lemma ChiPlus_HAStates [simp]:
  "(ChiPlus A) \<subseteq> (HAStates A \<times> HAStates A)"  
apply (unfold ChiPlus_def)
apply (rule trancl_subset_Sigma)
apply auto
done

lemma ChiPlus_subset_States:
  "ChiPlus a `` {t} \<subseteq>  \<Union>(States ` (SAs a))"
apply (cut_tac A=a in ChiPlus_HAStates) 
apply (unfold HAStates_def)
apply auto
done

lemma finite_ChiPlus [simp]: 
  "finite (ChiPlus A)"
apply (rule_tac B="HAStates A \<times> HAStates A" in finite_subset)
apply auto
done

lemma ChiPlus_OneAncestor: 
  "\<lbrakk> S \<in> HAStates A; S \<notin> States (HARoot A) \<rbrakk> \<Longrightarrow> 
     \<exists> T. (T,S) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply (frule ChiRel_OneAncestor2)
apply auto
done

lemma ChiPlus_HAStates_Left:
 "(S,T) \<in> ChiPlus A \<Longrightarrow> S \<in> HAStates A"
apply (cut_tac A=A in ChiPlus_HAStates) 
apply (unfold HAStates_def)
apply auto
done

lemma ChiPlus_HAStates_Right:
 "(S,T) \<in> ChiPlus A \<Longrightarrow> T \<in>  HAStates A"
apply (cut_tac A=A in ChiPlus_HAStates) 
apply (unfold HAStates_def)
apply auto
done

lemma ChiPlus_ChiRel_int [rule_format]:
  "\<lbrakk> (T,S) \<in> (ChiPlus A)\<rbrakk> \<Longrightarrow> (ChiPlus A `` {T}) \<inter> (ChiRel A `` {S}) = (ChiRel A `` {S})"  
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in converse_trancl_induct)
apply auto
done

lemma ChiPlus_ChiPlus_int [rule_format]:
  "\<lbrakk> (T,S) \<in> (ChiPlus A)\<rbrakk> \<Longrightarrow> (ChiPlus A `` {T}) \<inter> (ChiPlus A `` {S}) = (ChiPlus A `` {S})"  
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in converse_trancl_induct)
apply auto
done

lemma ChiPlus_ChiRel_NoCycle_1 [rule_format]:
 "\<lbrakk> (T,S) \<in> ChiPlus A\<rbrakk> \<Longrightarrow>    
   (insert S (insert T ({U. (T,U) \<in> ChiPlus A \<and> (U,S) \<in> ChiPlus A})))  \<inter> (ChiRel A `` {T}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in converse_trancl_induct)
apply (unfold Image_def Int_def)
apply auto
done

lemma ChiPlus_ChiRel_NoCycle_2 [rule_format]:
 "\<lbrakk> (T,S) \<in> ChiPlus A\<rbrakk> \<Longrightarrow>  (S,T) \<in> (ChiRel A) \<longrightarrow> 
   (insert S (insert T ({U. (T,U) \<in> ChiPlus A \<and> (U,S) \<in> ChiPlus A})))  \<inter> (ChiRel A `` {S}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in converse_trancl_induct)
apply (unfold Image_def Int_def)
apply auto
done

lemma ChiPlus_ChiRel_NoCycle_3 [rule_format]:
 "\<lbrakk> (T,S) \<in> ChiPlus A\<rbrakk> \<Longrightarrow>  (S,T) \<in> (ChiRel A) \<longrightarrow> (T,U) \<in>  ChiPlus A \<longrightarrow> (U, S) \<in> ChiPlus A \<longrightarrow> 
   (insert S (insert T ({U. (T,U) \<in> ChiPlus A \<and> (U,S) \<in> ChiPlus A})))  \<inter> (ChiRel A `` {U}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in trancl_induct)
apply (unfold Image_def Int_def, simp)
apply (rename_tac V)
prefer 2
apply (rename_tac V W)
prefer 2
apply (simp, safe)
apply (simp only: ChiRel_HAStates_NoCycles)
apply simp
apply (case_tac "(U,W) \<in> (ChiRel A)", fast, rotate_tac 5, frule tranclD3, fast, blast intro: trancl_into_trancl)+
done

lemma ChiPlus_ChiRel_NoCycle_4 [rule_format]:
 "\<lbrakk> (T,S) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> (S,T) \<in>  (ChiRel A) \<longrightarrow> ((ChiPlus A ``{T}) \<inter> (ChiRel A `` {S})) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel A)" in trancl_induct)
apply (unfold Image_def Int_def)
apply auto
apply (simp only: ChiRel_HAStates_NoCycles)
apply (rule_tac x=T in exI)
apply simp
apply (rule_tac x=T in exI)
apply simp
done

lemma ChiRel_ChiPlus_NoCycles:
 "(S,T) \<in> (ChiRel A) \<Longrightarrow> (T,S) \<notin> (ChiPlus A)"
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="insert S (insert T ({U. (T,U) \<in> ChiPlus A \<and> (U,S) \<in> ChiPlus A}))" in ballE)
prefer 2
apply (simp add: ChiPlus_subset_States)
apply (cut_tac A=A in ChiPlus_HAStates) 
apply (unfold HAStates_def)
apply auto
apply (frule ChiPlus_ChiRel_NoCycle_2)
apply fast
apply (simp add:ChiRel_CompFun)
apply (frule ChiPlus_ChiRel_NoCycle_1)
apply (simp add:ChiRel_CompFun)
apply (frule ChiPlus_ChiRel_NoCycle_3)
apply fast
apply fast
back
apply fast
apply (rename_tac V)
apply (case_tac "V \<in> HAStates A") 
apply (simp add: ChiRel_CompFun)
apply (simp only: ChiPlus_HAStates_Right)
apply fast
done

lemma ChiPlus_ChiPlus_NoCycles:
 "(S,T) \<in> (ChiPlus A) \<Longrightarrow> (T,S) \<notin> (ChiPlus A)"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="T" and r="(ChiRel A)" in trancl_induct)
apply fast
apply (frule ChiRel_ChiPlus_NoCycles)
apply (auto intro: trancl_into_trancl2 simp add:ChiPlus_def)
done

lemma ChiPlus_NoCycles [rule_format]:
 "(S,T) \<in> (ChiPlus A) \<Longrightarrow> S \<noteq> T"
apply (frule ChiPlus_ChiPlus_NoCycles)
apply auto
done

lemma ChiPlus_NoCycles_2 [simp]:
 "(S,S) \<notin> (ChiPlus A)"
apply (rule notI)
apply (frule ChiPlus_NoCycles)
apply fast
done

lemma ChiPlus_ChiPlus_NoCycles_2:
  "\<lbrakk> (S,U) \<in> ChiPlus A; (U,T) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> (T,S) \<notin>  ChiPlus A"
apply (rule ChiPlus_ChiPlus_NoCycles)
apply (auto intro: trancl_trans simp add: ChiPlus_def)
done

lemma ChiRel_ChiPlus_trans:
   "\<lbrakk> (U,S) \<in> ChiPlus A; (S,T) \<in> ChiRel A\<rbrakk> \<Longrightarrow> (U,T) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply auto
done

lemma ChiRel_ChiPlus_trans2:
   "\<lbrakk> (U,S) \<in> ChiRel A; (S,T) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> (U,T) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply auto
done

lemma ChiPlus_ChiRel_Ex [rule_format]:
  "\<lbrakk> (S,T) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> (S,T) \<notin> ChiRel A \<longrightarrow> 
    (\<exists> U. (S,U) \<in> ChiPlus A \<and> (U,T) \<in> ChiRel A)"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="T" and r="(ChiRel A)" in converse_trancl_induct)
apply auto
apply (rename_tac U)
apply (rule_tac x=U in exI)
apply auto
done

lemma ChiPlus_ChiRel_Ex2 [rule_format]:
  "\<lbrakk> (S,T) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> (S,T) \<notin> ChiRel A \<longrightarrow> 
    (\<exists> U. (S,U) \<in> ChiRel A \<and> (U,T) \<in> ChiPlus A)"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="T" and r="(ChiRel A)" in converse_trancl_induct)
apply auto
done

lemma HARootStates_Range_ChiPlus [simp]:
  "\<lbrakk> S \<in> States (HARoot A) \<rbrakk> \<Longrightarrow> S \<notin> Range (ChiPlus A)" 
by (unfold ChiPlus_def, auto)

lemma HARootStates_Range_ChiPlus2 [simp]:
  "\<lbrakk> S \<in> States (HARoot A) \<rbrakk> \<Longrightarrow> (x,S) \<notin> (ChiPlus A)" 
by (frule HARootStates_Range_ChiPlus, unfold Domain_converse [symmetric], fast)

lemma SAStates_ChiPlus_ChiRel_NoCycle_1 [rule_format]:
 "\<lbrakk> (S,U) \<in> ChiPlus A; SA \<in> SAs A \<rbrakk> \<Longrightarrow> (U,T) \<in> (ChiRel A) \<longrightarrow> S \<in> States SA \<longrightarrow> T \<in> States SA \<longrightarrow> 
   (insert S (insert U ({V. (S,V) \<in> ChiPlus A \<and> (V,U) \<in> ChiPlus A}))) \<inter> (ChiRel A `` {U}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="U" and r="(ChiRel A)" in converse_trancl_induct)
apply (simp, safe) 
apply (simp only: SAStates_ChiRel_trans)
apply (simp add:ChiRel_CompFun)
apply safe
apply (erule_tac x=SA in ballE)
apply (simp add: CompFun_ChiRel2)+
apply (simp add:Int_def, fast)
apply auto
apply (fold ChiPlus_def)
apply (rename_tac W)
apply (frule_tac U=U and T=U and S=W in ChiRel_ChiPlus_trans2)
apply auto
done

lemma SAStates_ChiPlus_ChiRel_NoCycle_2 [rule_format]:
 "\<lbrakk> (S,U) \<in>  ChiPlus A \<rbrakk> \<Longrightarrow>  (U,T) \<in> (ChiRel A) \<longrightarrow> 
   (insert S (insert U ({V. (S,V) \<in> ChiPlus A \<and> (V,U) \<in> ChiPlus A})))  \<inter> (ChiRel A `` {S}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="U" and r="(ChiRel A)" in converse_trancl_induct)
apply (unfold Image_def Int_def)
apply auto
done

(* TO DO *)

lemma SAStates_ChiPlus_ChiRel_NoCycle_3 [rule_format]:
 "\<lbrakk> (S,U) \<in>  ChiPlus A \<rbrakk> \<Longrightarrow>  (U,T) \<in> (ChiRel A) \<longrightarrow> (S,s) \<in> ChiPlus A \<longrightarrow> (s,U) \<in> ChiPlus A \<longrightarrow>
   (insert S (insert U ({V. (S,V) \<in> ChiPlus A \<and> (V,U) \<in> ChiPlus A})))  \<inter> (ChiRel A `` {s}) \<noteq> {}"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="U" and r="(ChiRel A)" in trancl_induct)
apply fast
apply (rename_tac W)
prefer 2
apply (rename_tac W X)
prefer 2
apply (unfold Image_def Int_def)
apply (simp, safe)
apply (fold ChiPlus_def)
apply (case_tac "(s,W) \<in> ChiRel A")
apply fast
apply (frule_tac S=s and T=W in ChiPlus_ChiRel_Ex2)
apply simp
apply safe
apply (rename_tac X)
apply (rule_tac x=X in exI)
apply (fast intro: ChiRel_ChiPlus_trans)
apply simp
apply (case_tac "(s,X) \<in> ChiRel A")
apply force
apply (frule_tac S=s and T=X in ChiPlus_ChiRel_Ex2)
apply simp
apply safe
apply (rename_tac Y)
apply (erule_tac x=Y in allE)
apply simp
apply (fast intro: ChiRel_ChiPlus_trans)
apply simp
apply (case_tac "(s,X) \<in> ChiRel A")
apply force
apply (frule_tac S=s and T=X in ChiPlus_ChiRel_Ex2)
apply simp
apply safe
apply (rename_tac Y)
apply (erule_tac x=Y in allE)
apply simp
apply (fast intro: ChiRel_ChiPlus_trans)
apply fastforce
apply simp
apply (erule_tac x=W in allE)
apply simp
apply simp
apply (rename_tac Y)
apply (erule_tac x=Y in allE)
apply simp
apply (fast intro: ChiRel_ChiPlus_trans)
done

lemma SAStates_ChiPlus_ChiRel_trans [rule_format]:
  "\<lbrakk> (S,U) \<in> (ChiPlus A); (U,T) \<in> (ChiRel A); S \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> T \<notin> States SA"
apply (cut_tac HA=A in NoCycles_HA)
apply (unfold NoCycles_def)
apply (erule_tac x="insert S (insert U ({V. (S,V) \<in> ChiPlus A \<and> (V,U) \<in> ChiPlus A}))" in ballE)
prefer 2
apply (simp add: ChiPlus_subset_States)
apply (cut_tac A=A in ChiPlus_HAStates) 
apply (unfold HAStates_def)
apply auto[1]
apply safe
apply fast
apply (frule SAStates_ChiPlus_ChiRel_NoCycle_2)
apply fast
apply (frule HAStates_SA_mem)
apply fast
apply (simp only:ChiRel_CompFun)
apply (frule SAStates_ChiPlus_ChiRel_NoCycle_1)
apply auto[3]
apply fast
apply (simp add:ChiRel_CompFun)
apply (frule SAStates_ChiPlus_ChiRel_NoCycle_3)
apply fast
apply fast
back
apply fast
apply (simp only:ChiPlus_HAStates_Left ChiRel_CompFun)
done

lemma SAStates_ChiPlus2 [rule_format]:
  "\<lbrakk> (S,T) \<in> ChiPlus A; SA \<in> SAs A  \<rbrakk> \<Longrightarrow> S \<in> States SA \<longrightarrow> T \<notin> States SA"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="T" and r="(ChiRel A)" in trancl_induct)
apply auto
apply (rename_tac U)
apply (frule_tac S=S and T=U in SAStates_ChiRel) 
apply auto
apply (fold ChiPlus_def)
apply (simp only: SAStates_ChiPlus_ChiRel_trans)
done

lemma SAStates_ChiPlus [rule_format]:
 "\<lbrakk> S \<in> States SA; T \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> (S,T) \<notin> ChiPlus A"
apply auto
apply (simp only: SAStates_ChiPlus2)
done

lemma SAStates_ChiPlus_ChiRel_OneAncestor [rule_format]:
  "\<lbrakk> T \<in> States SA; SA \<in> SAs A; (S,U) \<in> ChiPlus A\<rbrakk> \<Longrightarrow>  S \<noteq> T \<longrightarrow> S \<in> States SA \<longrightarrow> (T,U) \<notin> ChiRel A"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="U" and r="(ChiRel A)" in trancl_induct)
apply auto
apply (simp add: ChiRel_OneAncestor_notmem)
apply (rename_tac V W)
apply (fold ChiPlus_def)
apply (case_tac "V=T")
apply (simp add: ChiRel_OneAncestor_notmem SAStates_ChiPlus)+
done

lemma SAStates_ChiPlus_OneAncestor [rule_format]:
  "\<lbrakk> T \<in> States SA; SA \<in> SAs A; (S,U) \<in> ChiPlus A \<rbrakk> \<Longrightarrow>  S \<noteq> T \<longrightarrow>  
     S \<in> States SA \<longrightarrow> (T,U) \<notin> ChiPlus A"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="U" and r="(ChiRel A)" in trancl_induct)
apply auto
apply (fold ChiPlus_def)
apply (rename_tac V)
apply (frule_tac T=S and S=T and U=V in SAStates_ChiPlus_ChiRel_OneAncestor)
apply auto
apply (rename_tac V W)
apply (frule_tac S=T and T=W in ChiPlus_ChiRel_Ex)
apply auto
apply (frule_tac T=T and S=S and U=W in SAStates_ChiPlus_ChiRel_OneAncestor)
apply auto
apply (rule ChiRel_ChiPlus_trans)
apply auto
apply (rename_tac X)
apply (case_tac "V=X")
apply simp
apply (simp add: ChiRel_OneAncestor_notmem)
done

lemma ChiRel_ChiPlus_OneAncestor [rule_format]:
  "\<lbrakk> (T,U) \<in> ChiPlus A \<rbrakk> \<Longrightarrow> T \<noteq> S \<longrightarrow> (S,U) \<in> ChiRel A \<longrightarrow> (T,S) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="U" and r="(ChiRel A)" in trancl_induct)
apply auto
apply (fast intro:ChiRel_OneAncestor)
apply (rename_tac V W)
apply (case_tac "S=V")
apply auto
apply (fast intro:ChiRel_OneAncestor)
done

lemma ChiPlus_SA_OneAncestor [rule_format]: 
   "\<lbrakk> (S,T) \<in> ChiPlus A; 
      U \<in> States SA; SA \<in> SAs A \<rbrakk> \<Longrightarrow> T \<in> States SA \<longrightarrow>
      (S,U) \<in> ChiPlus A"
apply (unfold ChiPlus_def)
apply (rule_tac a="S" and b="T" and r="(ChiRel A)" in converse_trancl_induct)
apply auto
apply (frule ChiRel_SA_OneAncestor)
apply fast+
done

subsubsection \<open>\<open>ChiStar\<close>\<close>

lemma ChiPlus_ChiStar [simp]:
  "\<lbrakk> (S,T) \<in> ChiPlus A  \<rbrakk> \<Longrightarrow> (S,T) \<in> ChiStar A"
by (unfold ChiPlus_def ChiStar_def, auto)

lemma HARootState_Range_ChiStar [simp]:
  "\<lbrakk> x \<noteq> S; S \<in> States (HARoot A) \<rbrakk> \<Longrightarrow> (x,S) \<notin> (ChiStar A)" 
apply (unfold ChiStar_def)
apply (subst rtrancl_eq_or_trancl)
apply (fold ChiPlus_def)
apply auto
done

lemma ChiStar_Self [simp]:
 "(S,S) \<in> ChiStar A"
apply (unfold ChiStar_def)
apply simp
done

lemma ChiStar_Image [simp]:  
  "S \<in> M \<Longrightarrow> S \<in> (ChiStar A `` M)"
apply (unfold Image_def)
apply (auto intro: ChiStar_Self)
done

lemma ChiStar_ChiPlus_noteq: 
  "\<lbrakk> S \<noteq> T; (S,T) \<in> ChiStar A \<rbrakk> \<Longrightarrow> (S,T) \<in> ChiPlus A"
apply (unfold ChiPlus_def ChiStar_def)
apply (simp add: rtrancl_eq_or_trancl)
done

lemma ChiRel_ChiStar_trans:
  "\<lbrakk> (S,U) \<in> ChiStar A; (U,T) \<in> ChiRel A \<rbrakk> \<Longrightarrow> (S,T) \<in> ChiStar A"
apply (unfold ChiStar_def)
apply auto
done

subsubsection \<open>\<open>InitConf\<close>\<close>

lemma InitConf_HAStates [simp]:
  "InitConf A \<subseteq> HAStates A"
apply (unfold InitConf_def HAStates_def)
apply auto
apply (rule rtrancl_induct)
back
apply auto
apply (rule_tac x="HARoot A" in bexI)
apply auto
apply (unfold HAStates_def ChiRel_def)
apply auto
done

lemma InitConf_HAStates2 [simp]:
 "S \<in> InitConf A \<Longrightarrow> S \<in> HAStates A"
apply (cut_tac A=A in InitConf_HAStates)
apply fast
done

lemma HAInitState_InitConf [simp]:
  "HAInitState A \<in> InitConf A"
by (unfold HAInitState_def InitConf_def, auto)

lemma InitConf_HAInitState_HARoot:
 "[| S \<in> InitConf A; S \<noteq> HAInitState A |] ==> S \<notin> States (HARoot A)"
apply (unfold InitConf_def)
apply auto
apply (rule mp)
prefer 2 
apply fast
back
apply (rule mp)
prefer 2
apply fast
back
back
apply (rule_tac b=S in rtrancl_induct)
apply auto
apply (simp add: ChiRel_HARoot)+
done

lemma InitConf_HARoot_HAInitState [simp]:
 "\<lbrakk> S \<in> InitConf A; S \<in> States (HARoot A) \<rbrakk> \<Longrightarrow> S = HAInitState A"
apply (subst not_not [THEN sym])
apply (rule notI)
apply (simp add:InitConf_HAInitState_HARoot)
done

lemma HAInitState_CompFun_InitConf [simp]:
 "[|SA \<in> the (CompFun A  (HAInitState A)) |] ==> (InitState SA) \<in> InitConf A"
apply (unfold InitConf_def HAStates_def)
apply auto
apply (rule rtrancl_Int)
apply auto
apply (cut_tac A=A and S="HAInitState A" in HAStates_CompFun_States_ChiRel)
apply auto
apply (rule Image_singleton_iff [THEN subst])
apply (rotate_tac -1)
apply (drule sym)
apply simp
apply (rule_tac x=SA in bexI)
apply auto
done

lemma InitState_CompFun_InitConf:
 "[| S \<in> HAStates A; SA \<in> the (CompFun A S); S \<in> InitConf A |] ==> (InitState SA) \<in> InitConf A"
apply (unfold InitConf_def)
apply auto
apply (rule_tac b=S in rtrancl_into_rtrancl)
apply fast
apply (frule rtrancl_Int1)
apply auto
apply (case_tac "S = HAInitState A")
apply simp
apply (rule rtrancl_mem_Sigma)
apply auto
apply (cut_tac A=A and S=S in HAStates_CompFun_States_ChiRel)
apply auto
apply (rule Image_singleton_iff [THEN subst])
apply (rotate_tac -1)
apply (drule sym)
apply simp 
apply (rule_tac x=SA in bexI)
apply auto
done

lemma InitConf_HAInitStates:
  "InitConf A \<subseteq> HAInitStates A"
apply (unfold InitConf_def)
apply (rule subsetI)
apply auto
apply (frule rtrancl_Int1)
apply (case_tac "x = HAInitState A")
apply simp
apply (rule rtrancl_mem_Sigma)
apply auto
done

lemma InitState_notmem_InitConf:
 "[| SA \<in> the (CompFun A S); S \<in> InitConf A; T \<in> States SA;
     T \<noteq> InitState SA |] ==>  T \<notin> InitConf A"
apply (frule InitConf_HAStates2)
apply (unfold InitConf_def)
apply auto
apply (rule mp)
prefer 2
apply fast
apply (rule mp)
prefer 2
apply fast
back
apply (rule mp)
prefer 2
apply fast
back
back
apply (rule mp)
prefer 2
apply fast
back
back 
back
apply (rule mp)
prefer 2
apply fast
back
back 
back
back
apply (rule mp)
prefer 2
apply fast
back
back 
back
back
back
apply (rule_tac b=T in rtrancl_induct)
apply auto
done

lemma InitConf_CompFun_InitState [simp]:
 "\<lbrakk> SA \<in> the (CompFun A S); S \<in> InitConf A; T \<in> States SA;
    T \<in> InitConf A \<rbrakk> \<Longrightarrow> T = InitState SA"
apply (subst not_not [THEN sym])
apply (rule notI)
apply (frule InitState_notmem_InitConf)
apply auto
done

lemma InitConf_ChiRel_Ancestor:
  "\<lbrakk> T \<in> InitConf A; (S,T) \<in> ChiRel A \<rbrakk> \<Longrightarrow> S \<in> InitConf A"
apply (unfold InitConf_def)
apply auto
apply (erule rtranclE)
apply auto
apply (rename_tac U)
apply (cut_tac A=A  in HAInitState_notmem_Range_ChiRel)
apply auto
apply (case_tac "U = S")
apply (auto simp add: ChiRel_OneAncestor)
done

lemma InitConf_CompFun_Ancestor:
  "\<lbrakk> S \<in> HAStates A; SA \<in> the (CompFun A S); T \<in> InitConf A; T \<in> States SA \<rbrakk>
    \<Longrightarrow>  S \<in> InitConf A"
apply (rule InitConf_ChiRel_Ancestor)
apply auto
apply (rule CompFun_ChiRel)
apply auto
done

subsubsection \<open>\<open>StepConf\<close>\<close>

lemma StepConf_EmptySet [simp]:
  "StepConf A C {} = C"
by (unfold StepConf_def, auto)

end

