(*  Title:      statecharts/HA/HASem.thy

    Author:     Steffen Helke and Florian Kammüller, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Semantics of Hierarchical Automata\<close>
theory HASem
imports HA
begin

subsection \<open>Definitions\<close>

definition
  RootExSem :: "[(('s,'e,'d)seqauto) set, 's \<rightharpoonup> ('s,'e,'d)seqauto set,
                 's set] => bool" where
  "RootExSem F G C == (\<exists>! S. S \<in> States (Root F G) \<and> S \<in> C)"

definition
  UniqueSucStates ::  "[(('s,'e,'d)seqauto) set, 's \<rightharpoonup> ('s,'e,'d)seqauto set,
                        's set] \<Rightarrow> bool" where
  "UniqueSucStates F G C  == \<forall> S \<in> (\<Union>(States ` F)).
                                   \<forall> A \<in> the (G S).
                                      if (S \<in> C) then
                                       \<exists>! S' . S' \<in>  States A \<and> S' \<in> C
                                     else
                                       \<forall> S \<in> States A. S \<notin> C"

definition
  IsConfSet :: "[(('s,'e,'d)seqauto) set, 's \<rightharpoonup> ('s,'e,'d)seqauto set,
                 's set] => bool" where
  "IsConfSet F G C ==
                C \<subseteq> (\<Union>(States ` F)) &
                RootExSem F G C &
                UniqueSucStates F G C" 

definition
  Status :: "[('s,'e,'d)hierauto,
              's set,
              'e set,
              'd data] => bool" where
  "Status HA C E D == E \<subseteq> HAEvents HA \<and> 
                      IsConfSet (SAs HA) (CompFun HA) C \<and> 
                      Data.DataSpace (HAInitValue HA) = Data.DataSpace D"

subsubsection \<open>\<open>Status\<close>\<close>

lemma Status_EmptySet:
 "(Abs_hierauto ((@ x . True),
    {Abs_seqauto ({ @ x . True}, (@ x . True), {}, {})}, {}, Map.empty(@ x . True \<mapsto> {})), 
  {@x. True},{}, @x. True) \<in> 
  {(HA,C,E,D) | HA C E D. Status HA C E D}"
apply (unfold Status_def CompFun_def SAs_def)
apply auto
apply (subst Abs_hierauto_inverse)
apply (subst hierauto_def)
apply (rule HierAuto_EmptySet)
apply (subst Abs_hierauto_inverse)
apply (subst hierauto_def)
apply (rule HierAuto_EmptySet)
apply auto
apply (unfold IsConfSet_def UniqueSucStates_def RootExSem_def)
apply auto
apply (unfold States_def)
apply auto
apply (unfold Root_def)
apply (rule someI2)
apply (rule conjI)
apply fast
apply (simp add: ran_def) 
apply simp
apply (subst Abs_seqauto_inverse)
apply (subst seqauto_def)
apply (rule SeqAuto_EmptySet)
apply simp
apply (unfold HAInitValue_def)
apply auto
apply (subst Abs_hierauto_inverse)
apply (subst hierauto_def)
apply (rule HierAuto_EmptySet)
apply simp
done

definition
  "status =
    {(HA,C,E,D) |
        (HA::('s,'e,'d)hierauto)
        (C::('s set))
        (E::('e set))
        (D::'d data). Status HA C E D}"

typedef ('s,'e,'d) status =
    "status :: (('s,'e,'d)hierauto * 's set * 'e set * 'd data) set"
  unfolding status_def
  apply (rule exI)
  apply (rule Status_EmptySet)
  done


definition
  HA :: "('s,'e,'d) status  => ('s,'e,'d) hierauto" where
  "HA == fst o Rep_status"

definition
  Conf :: "('s,'e,'d) status  => 's set" where
  "Conf == fst o snd o Rep_status"

definition
  Events :: "('s,'e,'d) status  => 'e set" where
  "Events == fst o snd o snd o Rep_status"

definition
  Value :: "('s,'e,'d) status  => 'd data" where
  "Value == snd o snd o snd o Rep_status"

definition
  RootState :: "('s,'e,'d) status  => 's" where
  "RootState ST == @ S. S \<in> Conf ST \<and> S \<in> States (HARoot (HA ST))"

(* -------------------------------------------------------------- *)
(* enabled transitions                                            *)
(* -------------------------------------------------------------- *)

definition
  EnabledTrans :: "(('s,'e,'d)status * ('s,'e,'d)seqauto *
                    ('s,'e,'d)trans) set" where
  "EnabledTrans == {(ST,SA,T) .
                       SA \<in> SAs (HA ST) \<and> 
                       T \<in> Delta SA \<and> 
                       source T \<in> Conf ST \<and> 
                       (Conf ST, Events ST, Value ST) |= (label T) }"

definition
  ET :: "('s,'e,'d) status => (('s,'e,'d) trans) set" where
  "ET ST == \<Union> SA \<in> SAs (HA ST). (EnabledTrans `` {ST}) `` {SA}"

(* -------------------------------------------------------------- *)
(* maximal non conflicting set of transitions                     *)
(* -------------------------------------------------------------- *)

definition
  MaxNonConflict :: "[('s,'e,'d)status,
                      ('s,'e,'d)trans set] => bool" where
  "MaxNonConflict ST T ==
        (T \<subseteq> ET ST) \<and> 
        (\<forall> A \<in> SAs (HA ST). card (T Int Delta A) \<le> 1)  \<and> 
        (\<forall> t \<in> (ET ST). (t \<in> T) =  (\<not> (\<exists> t' \<in> ET ST. HigherPriority (HA ST) (t',t))))"

(* -------------------------------------------------------------- *)
(* resolving the occurrence of racing with interleaving semantic  *)
(* for one set of transitions                                     *)
(* -------------------------------------------------------------- *)

definition
 ResolveRacing :: "('s,'e,'d)trans set
                   => ('d update set)" where
 "ResolveRacing TS ==
            let
                U = PUpdate (Label TS)
            in
                SequentialRacing U"

(* -------------------------------------------------------------- *)
(* HPT is a set, there can be more than one! If there are         *)
(* nondeterministic transitions t1, t2 in one SA : SAs A, then    *)
(* they are not in conflict wt higher priority. We have to chose  *)
(* one and get different sets.                                    *)
(* -------------------------------------------------------------- *)

definition
 HPT :: "('s,'e,'d)status => (('s,'e,'d)trans set) set" where
 "HPT ST == { T. MaxNonConflict ST T}"

(* -------------------------------------------------------------- *)
(* The initials status can be defined now for a given automaton.  *)
(* -------------------------------------------------------------- *)

definition
 InitStatus :: "('s,'e,'d)hierauto => ('s,'e,'d)status" where
 "InitStatus A ==
    Abs_status (A,InitConf A,{}, HAInitValue A)"

(* -------------------------------------------------------------- *)
(* The next status for a given status can be defined now by a     *)
(* step.                                                          *)
(* -------------------------------------------------------------- *)

definition
  StepActEvent :: "('s,'e,'d)trans set => 'e set" where
  "StepActEvent TS == Union (Actevent (Label TS))"

definition
  StepStatus :: "[('s,'e,'d)status, ('s,'e,'d)trans set, 'd update]
                 => ('s,'e,'d)status" where
  "StepStatus ST TS U =
                (let
                   (A,C,E,D) = Rep_status ST;
                   C'        = StepConf A C TS;
                   E'        = StepActEvent TS;
                   D'        = U !!! D
                 in
                   Abs_status (A,C',E',D'))"

(* --------------------------------------------------------------- *)
(* The Relation StepRel defines semantic transitions on statuses   *)
(* for given hierarchical automaton.                               *)
(* --------------------------------------------------------------- *)

definition
  StepRelSem :: "('s,'e,'d)hierauto
              => (('s,'e,'d)status * ('s,'e,'d)status) set" where
  "StepRelSem A == {(ST,ST'). (HA ST) = A \<and>
                    ((HPT ST \<noteq> {}) \<longrightarrow>
                       (\<exists>TS \<in> HPT ST.
                           \<exists>U \<in> ResolveRacing TS.
                                  ST' = StepStatus ST TS U)) &
                    ((HPT ST = {}) \<longrightarrow>
                       (ST' = StepStatus ST {} DefaultUpdate))}"

(* --------------------------------------------------------------- *)
(* The Relation StepRel defines semantic transitions on statuses   *)
(* The set of all reachable stati can now be defined inductively   *)
(* as the set of statuses derived through applications of          *)
(* transitions starting from the initial status TInitStatus 0.     *)
(* --------------------------------------------------------------- *)

inductive_set
  ReachStati  :: "('s,'e,'d)hierauto => ('s,'e,'d) status set"
  for A ::  "('s,'e,'d)hierauto"
where
  Status0 : "InitStatus A \<in> ReachStati A"
| StatusStep :
     "\<lbrakk> ST \<in> ReachStati A;  TS \<in> HPT ST; U \<in> ResolveRacing TS \<rbrakk>
      \<Longrightarrow> StepStatus ST TS U \<in> ReachStati A"

subsection \<open>Lemmas\<close>

lemma Rep_status_tuple: 
 "Rep_status ST = (HA ST, Conf ST, Events ST, Value ST)"
by (unfold HA_def Conf_def Events_def Value_def, simp) 

lemma Rep_status_select:
 "(HA ST, Conf ST, Events ST, Value ST) \<in> status"
by (rule Rep_status_tuple [THEN subst], rule Rep_status)

lemma Status_select [simp]:
  "Status (HA ST) (Conf ST) (Events ST) (Value ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def)
apply simp
done

subsubsection \<open>\<open>IsConfSet\<close>\<close>

lemma IsConfSet_Status [simp]: 
 "IsConfSet (SAs (HA ST)) (CompFun (HA ST)) (Conf ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def)
apply auto
done

subsubsection \<open>\<open>InitStatus\<close>\<close>

lemma IsConfSet_InitConf [simp]:
  "IsConfSet (SAs A) (CompFun A) (InitConf A)"
apply (unfold IsConfSet_def RootExSem_def UniqueSucStates_def, fold HARoot_def)
apply (rule conjI)
apply (fold HAStates_def, simp)
apply (rule conjI)
apply (rule_tac a="HAInitState A" in ex1I)
apply auto
apply (rename_tac S SA)
apply (case_tac "S \<in> InitConf A")
apply auto
apply (rule_tac x="InitState SA" in exI)
apply auto
apply (rule InitState_CompFun_InitConf)
apply auto
apply (rename_tac S SA T U)
apply (case_tac "U = InitState SA")
apply auto
apply (simp only:InitConf_CompFun_Ancestor HAStates_SA_mem, simp)+
done

lemma InitConf_status [simp]:
  "(A, InitConf A, {}, HAInitValue A) \<in>  status"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def)
apply auto
done

lemma Conf_InitStatus_InitConf [simp]:
 "Conf (InitStatus A) = InitConf A"
apply (unfold Conf_def InitStatus_def)
apply simp
apply (subst Abs_status_inverse)
apply auto
done

lemma HAInitValue_Value_DataSpace_Status [simp]:
  "Data.DataSpace (HAInitValue (HA ST)) = Data.DataSpace (Value ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def)
apply fast
done

lemma Value_InitStatus_HAInitValue [simp]:
 "Value (InitStatus A) = HAInitValue A"
apply (unfold Value_def InitStatus_def)
apply simp
apply (subst Abs_status_inverse)
apply auto
done

lemma HA_InitStatus [simp]:
 "HA (InitStatus A) = A"
apply (unfold InitStatus_def HA_def)
apply auto
apply (subst Abs_status_inverse)
apply auto
done

subsubsection \<open>\<open>Events\<close>\<close>

lemma Events_HAEvents_Status: 
  "(Events ST) \<subseteq> HAEvents (HA ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def)
apply fast
done

lemma TS_EventSet:
    "TS \<subseteq>  ET ST \<Longrightarrow> \<Union> (Actevent (Label TS)) \<subseteq> HAEvents (HA ST)"
apply (unfold Actevent_def actevent_def ET_def EnabledTrans_def Action_def Label_def)
apply (cut_tac HA="HA ST" in HAEvents_SAEvents_SAs)
apply auto
apply (rename_tac Event Source Trigger Guard Action Update Target)
apply (unfold SAEvents_def)
apply (erule subsetCE)
apply auto
apply (rename_tac SA)
apply (erule subsetCE)
apply auto
apply (erule_tac x=SA in ballE)
apply auto
apply (erule_tac x="(Trigger, Guard, Action, Update)" in ballE)
apply auto
apply (cut_tac SA=SA in Label_Delta_subset)
apply (erule subsetCE)
apply (unfold Label_def image_def)
apply auto
done

subsubsection \<open>\<open>StepStatus\<close>\<close>

lemma StepStatus_empty:
   "Abs_status (HA ST, Conf ST, {}, U !!! (Value ST)) = StepStatus ST {} U"
apply (unfold StepStatus_def Let_def)
apply auto
apply (subst Rep_status_tuple)
apply auto
apply (unfold StepActEvent_def)
apply auto
done

lemma status_empty_eventset [simp]:
      "(HA ST, Conf ST, {}, U !!! (Value ST)) \<in> status"
apply (unfold status_def Status_def)
apply auto
done

lemma HA_StepStatus_emptyTS [simp]:
  "HA (StepStatus ST {} U) = HA ST"
apply (subst StepStatus_empty [THEN sym])
apply (unfold HA_def)
apply auto
apply (subst Abs_status_inverse)
apply auto
apply (subst Rep_status_tuple)
apply auto
done

subsubsection \<open>Enabled Transitions \<open>ET\<close>\<close>

lemma HPT_ETI: 
    "TS \<in> HPT ST \<Longrightarrow> TS \<subseteq> ET ST"
by (unfold HPT_def MaxNonConflict_def, auto)

lemma finite_ET [simp]:
 "finite (ET ST)"
by (unfold ET_def Image_def EnabledTrans_def, auto)

subsubsection \<open>Finite Transition Set\<close>

lemma finite_MaxNonConflict [simp]:
 "MaxNonConflict ST TS \<Longrightarrow> finite TS"
apply (unfold MaxNonConflict_def)
apply auto
apply (subst finite_subset)
apply auto
done

lemma finite_HPT [simp]:
  "TS \<in> HPT ST \<Longrightarrow> finite TS"
by (unfold HPT_def, auto)

subsubsection \<open>\<open>PUpdate\<close>\<close>

lemma finite_Update:
 "finite TS \<Longrightarrow> finite ((\<lambda> F. (Rep_pupdate F) (Value ST)) ` (PUpdate (Label TS)))"
by (rule finite_imageI, auto)

lemma finite_PUpdate:
 "TS \<in> HPT S \<Longrightarrow> finite (Expr.PUpdate (Label TS))"
apply auto
done

lemma HPT_ResolveRacing_Some [simp]:
  "TS \<in> HPT S \<Longrightarrow> (SOME u. u \<in> ResolveRacing TS) \<in> ResolveRacing TS"
apply (unfold ResolveRacing_def Let_def)
apply (rule finite_SequentialRacing)
apply auto
done

subsubsection \<open>Higher Priority Transitions \<open>HPT\<close>\<close>

lemma finite_HPT2 [simp]:
  "finite (HPT ST)"
apply (cut_tac ST=ST in finite_ET)
apply (unfold HPT_def MaxNonConflict_def)
apply (subst Collect_subset)
apply (frule finite_Collect_subsets)
apply auto
done

lemma HPT_target_StepConf [simp]: 
  "\<lbrakk> TS \<in> HPT ST; T \<in> TS \<rbrakk> \<Longrightarrow> target T \<in> StepConf (HA ST) (Conf ST) TS"
apply (unfold StepConf_def)
apply auto
done

lemma HPT_target_StepConf2 [simp]: 
  "\<lbrakk> TS \<in> HPT ST; (S,L,T) \<in> TS \<rbrakk> \<Longrightarrow> T \<in> StepConf (HA ST) (Conf ST) TS"
apply (unfold StepConf_def Target_def Source_def source_def target_def image_def)
apply auto
apply auto
done

subsubsection \<open>Delta Transition Set\<close>

lemma ET_Delta: 
  "\<lbrakk> TS \<subseteq> ET ST; t \<in> TS; source t \<in> States A; A \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow> t \<in> Delta A"
apply (unfold ET_def EnabledTrans_def)
apply simp
apply (erule subsetCE)
apply auto
apply (rename_tac SA)
apply (case_tac "A = SA")
apply auto
apply (cut_tac HA="HA ST" in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply force
done

lemma ET_Delta_target: 
  "\<lbrakk> TS \<subseteq> ET ST; t \<in> TS; target t \<in> States A; A \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> t \<in> Delta A"
apply (unfold ET_def EnabledTrans_def)
apply simp
apply (erule subsetCE)
apply auto
apply (rename_tac SA)
apply (case_tac "A = SA")
apply auto
apply (cut_tac HA="HA ST" in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply force
done

lemma ET_HADelta:
   " \<lbrakk> TS \<subseteq> ET ST; t \<in> TS \<rbrakk> \<Longrightarrow> t \<in> HADelta (HA ST)"
apply (unfold HADelta_def) 
apply auto
apply (unfold ET_def EnabledTrans_def Image_def)
apply auto
done

lemma HPT_HADelta:
   " \<lbrakk> TS \<in> HPT ST; t \<in> TS \<rbrakk> \<Longrightarrow> t \<in> HADelta (HA ST)"
apply (rule ET_HADelta)
apply (unfold HPT_def MaxNonConflict_def)
apply auto
done

lemma HPT_Delta: 
  "\<lbrakk> TS \<in> HPT ST; t \<in> TS; source t \<in> States A; A \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow> t \<in> Delta A"
apply (rule ET_Delta)
apply auto
apply (unfold HPT_def MaxNonConflict_def)
apply fast
done

lemma HPT_Delta_target: 
  "\<lbrakk> TS \<in> HPT ST; t \<in> TS; target t \<in> States A; A \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow> t \<in> Delta A"
apply (rule ET_Delta_target)
apply auto
apply (unfold HPT_def MaxNonConflict_def)
apply fast
done

lemma OneTrans_HPT_SA:
  "\<lbrakk> TS \<in> HPT ST; T \<in> TS; source T \<in> States SA;
     U \<in> TS; source U \<in> States SA; SA \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> T = U"
apply (unfold HPT_def MaxNonConflict_def Source_def)
apply auto
apply (erule_tac x=SA in ballE)
apply (case_tac "finite (TS \<inter> Delta SA)") 
apply (frule_tac t=T in OneElement_Card)
apply fast
apply (frule_tac t=T and A=SA in ET_Delta)
apply assumption+
apply fast
apply (frule_tac t=U in OneElement_Card)
apply fast
apply (frule_tac t=U and A=SA in ET_Delta)
apply auto
done

lemma OneTrans_HPT_SA2:
  "\<lbrakk> TS \<in> HPT ST; T \<in> TS; target T \<in> States SA;
     U \<in> TS; target U \<in> States SA; SA \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> T = U"
apply (unfold HPT_def MaxNonConflict_def Target_def)
apply auto
apply (erule_tac x=SA in ballE)
apply (case_tac "finite (TS \<inter> Delta SA)") 
apply (frule_tac t=T in OneElement_Card)
apply fast
apply (frule_tac t=T and A=SA in ET_Delta_target)
apply assumption+
apply fast
apply (frule_tac t=U in OneElement_Card)
apply fast
apply (frule_tac t=U and A=SA in ET_Delta_target)
apply auto
done

subsubsection \<open>Target Transition Set\<close>

lemma ET_Target_HAStates:
    "TS \<subseteq> ET ST \<Longrightarrow> Target TS \<subseteq> HAStates (HA ST)"
apply (unfold HAStates_def Target_def target_def ET_def EnabledTrans_def Action_def Label_def) 
apply (cut_tac HA="HA ST" in Target_SAs_Delta_States)
apply auto
apply (rename_tac Source Trigger Guard Action Update Target)
apply (unfold Target_def)
apply (erule subsetCE)
apply auto
apply (rename_tac SA)
apply (erule subsetCE)
apply auto
apply (unfold image_def)
apply auto
apply (metis target_select)
done

lemma HPT_Target_HAStates:
 "TS \<in> HPT ST \<Longrightarrow> Target TS \<subseteq> HAStates (HA ST)"
apply (rule HPT_ETI [THEN ET_Target_HAStates])
apply assumption
done

lemma HPT_Target_HAStates2 [simp]:
  "\<lbrakk>TS \<in> HPT ST; S \<in> Target TS\<rbrakk> \<Longrightarrow> S \<in> HAStates (HA ST)"
apply (cut_tac HPT_Target_HAStates)
apply fast+
done

lemma OneState_HPT_Target:
  "\<lbrakk> TS \<in> HPT ST; S \<in> Target TS; 
     T \<in> Target TS; S \<in> States SA;
     T \<in> States SA; SA \<in> SAs (HA ST) \<rbrakk>
   \<Longrightarrow> S = T"
apply (unfold Target_def)
apply (auto dest: OneTrans_HPT_SA2[rotated -1])
done

subsubsection \<open>Source Transition Set\<close>

lemma ET_Source_Conf:
  "TS \<subseteq> ET ST \<Longrightarrow> (Source TS) \<subseteq> Conf ST"
apply (unfold Source_def ET_def EnabledTrans_def)
apply auto
done

lemma HPT_Source_Conf [simp]:
  "TS \<in> HPT ST \<Longrightarrow> (Source TS) \<subseteq> Conf ST"
apply (unfold HPT_def MaxNonConflict_def)
apply (rule ET_Source_Conf)
apply auto
done

lemma ET_Source_Target [simp]:
  "\<lbrakk> SA \<in> SAs (HA ST); TS \<subseteq> ET ST; States SA \<inter> Source TS = {} \<rbrakk> \<Longrightarrow> States SA \<inter> Target TS = {}"
apply (unfold ET_def EnabledTrans_def Source_def Target_def)
apply auto
apply (rename_tac Source Trigger Guard Action Update Target)
apply (erule subsetCE)
apply auto
apply (rename_tac SAA)
apply (unfold image_def source_def Int_def)
apply auto
apply (erule_tac x=Source in allE)
apply auto
apply (frule Delta_source_States)
apply (unfold source_def)
apply auto
apply (case_tac "SA=SAA")
apply auto
apply (cut_tac HA="HA ST" in MutuallyDistinct_HA)
apply (unfold MutuallyDistinct_def)
apply (erule_tac x=SA in ballE)
apply (erule_tac x=SAA in ballE)
apply auto
apply (frule Delta_target_States)
apply (unfold target_def)
apply force
done

lemma HPT_Source_Target [simp]:
  "\<lbrakk> TS \<in> HPT ST; States SA \<inter> Source TS = {}; SA \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> States SA \<inter> Target TS = {}"
apply (unfold HPT_def MaxNonConflict_def)
apply auto
done

lemma ET_target_source:
  "\<lbrakk> TS \<subseteq> ET ST; t \<in> TS; target t \<in> States A; A \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> source t \<in> States A"
apply (frule ET_Delta_target)
apply auto
done

lemma ET_source_target:
  "\<lbrakk> TS \<subseteq> ET ST; t \<in> TS; source t \<in> States A; A \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> target t \<in> States A"
apply (frule ET_Delta)
apply auto
done

lemma HPT_target_source:
  "\<lbrakk> TS \<in> HPT ST; t \<in> TS; target t \<in> States A; A \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow> source t \<in> States A"
apply (rule ET_target_source)
apply auto
apply (unfold HPT_def MaxNonConflict_def)
apply fast
done

lemma HPT_source_target:
  "\<lbrakk> TS \<in> HPT ST; t \<in> TS; source t \<in> States A; A \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> target t \<in> States A"
apply (rule ET_source_target)
apply auto
apply (unfold HPT_def MaxNonConflict_def)
apply fast
done

lemma HPT_source_target2 [simp]:
  "\<lbrakk> TS \<in>HPT ST; (s,l,t) \<in> TS; s \<in> States A; A \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow>  t \<in>States A" 
apply (cut_tac ST=ST and TS=TS and t="(s,l,t)" in HPT_source_target)
apply auto
done

lemma ChiRel_ChiStar_Source_notmem:
   "\<lbrakk> TS \<in> HPT ST; (S, T) \<in> ChiRel (HA ST); S \<in> Conf ST; 
      T \<notin> ChiStar (HA ST) `` Source TS \<rbrakk> \<Longrightarrow> 
      S \<notin> ChiStar (HA ST) `` Source TS"
apply auto
apply (rename_tac U)
apply (simp only: Image_def)
apply auto
apply (erule_tac x=U in ballE)
apply (fast intro: ChiRel_ChiStar_trans)+
done

lemma ChiRel_ChiStar_notmem:
  "\<lbrakk> TS \<in> HPT ST; (S,T) \<in> ChiRel (HA ST); 
     S \<in> ChiStar (HA ST) `` Source TS \<rbrakk> \<Longrightarrow> T \<notin> Source TS"
using [[hypsubst_thin = true]]
apply (unfold HPT_def MaxNonConflict_def HigherPriority_def restrict_def)
apply auto
apply (rename_tac U)
apply (unfold Source_def image_def)
apply auto
apply (rename_tac SSource STrigger SGuard SAction SUpdate STarget 
                  TSource TTrigger TGuard TAction TUpdate TTarget)
apply (erule_tac x="(SSource, (STrigger, SGuard, SAction, SUpdate), STarget)" in ballE)
apply auto
apply (erule_tac x="(TSource, (TTrigger, TGuard, TAction, TUpdate), TTarget)" in ballE)
apply auto
apply (simp add: ET_HADelta)
apply (case_tac "SSource=S") 
apply auto
apply (frule ChiStar_ChiPlus_noteq)
apply fast
apply (fast intro: ChiRel_ChiPlus_trans)
done

subsubsection \<open>\<open>StepActEvents\<close>\<close>

lemma StepActEvent_empty [simp]:
  "StepActEvent {} = {}"
by (unfold StepActEvent_def, auto)

lemma StepActEvent_HAEvents:
 "TS \<in> HPT ST \<Longrightarrow> StepActEvent TS \<subseteq> HAEvents (HA ST)"
apply (unfold StepActEvent_def image_def)
apply (rule HPT_ETI [THEN TS_EventSet])
apply assumption
done

subsubsection \<open>\<open>UniqueSucStates\<close>\<close>

lemma UniqueSucStates_Status [simp]:
  "UniqueSucStates (SAs (HA ST)) (CompFun (HA ST)) (Conf ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def IsConfSet_def)
apply auto
done

subsubsection \<open>\<open>RootState\<close>\<close>

lemma RootExSem_Status [simp]:
  "RootExSem (SAs (HA ST)) (CompFun (HA ST)) (Conf ST)"
apply (cut_tac Rep_status_select)
apply (unfold status_def Status_def IsConfSet_def)
apply auto
done

lemma RootState_HARootState [simp]:
  "(RootState ST) \<in> States (HARoot (HA ST))"
apply (unfold RootState_def)
apply (cut_tac ST=ST in RootExSem_Status)
apply (unfold RootExSem_def HARoot_def HAStates_def)
apply auto
apply (subst some1_equality)
apply auto
done

lemma RootState_Conf [simp]:
  "(RootState ST) \<in> (Conf ST)"
apply (unfold RootState_def)
apply (cut_tac ST=ST in RootExSem_Status)
apply (unfold RootExSem_def HARoot_def HAStates_def)
apply auto
apply (subst some1_equality)
apply auto
done

lemma RootState_notmem_Chi [simp]:
  "S \<in> HAStates (HA ST) \<Longrightarrow> (RootState ST) \<notin> Chi (HA ST) S"
by auto

lemma RootState_notmem_Range_ChiRel [simp]:
  "RootState ST \<notin> Range (ChiRel (HA ST))"
by auto

lemma RootState_Range_ChiPlus [simp]:
  "RootState ST \<notin> Range (ChiPlus (HA ST))" 
by auto

lemma RootState_Range_ChiStar [simp]:
  "\<lbrakk> x \<noteq> RootState ST \<rbrakk> \<Longrightarrow> (x,RootState ST) \<notin> (ChiStar (HA ST))" 
by auto

lemma RootState_notmem_ChiRel [simp]:
  "(x,RootState ST) \<notin> (ChiRel (HA ST))" 
by (unfold ChiRel_def, auto)

lemma RootState_notmem_ChiRel2 [simp]:
  "\<lbrakk> S \<in> States (HARoot (HA ST))  \<rbrakk> \<Longrightarrow> (x,S) \<notin> (ChiRel (HA ST))" 
by (unfold ChiRel_def, auto)

lemma RootState_Conf_StepConf [simp]:
  "\<lbrakk> RootState ST \<notin> Source TS \<rbrakk> \<Longrightarrow> RootState ST \<in> StepConf (HA ST) (Conf ST) TS"
apply (unfold StepConf_def)
apply auto
apply (rename_tac S)
apply (case_tac "S=RootState ST")
apply fast
apply auto
apply (rename_tac S)
apply (case_tac "S=RootState ST")
apply fast
apply auto
done

lemma OneRootState_Conf [simp]:
  "\<lbrakk> S \<in> States (HARoot (HA ST)); S \<in> Conf ST \<rbrakk> \<Longrightarrow> S = RootState ST"
apply (cut_tac ST=ST in IsConfSet_Status)
apply (unfold IsConfSet_def RootExSem_def)
apply (fold HARoot_def)
apply auto
done

lemma OneRootState_Source:
  "\<lbrakk> TS \<in> HPT ST; S \<in> Source TS; S \<in> States (HARoot (HA ST)) \<rbrakk> \<Longrightarrow> S = RootState ST"
apply (cut_tac ST=ST and TS=TS in HPT_Source_Conf, assumption)
apply (cut_tac ST=ST in OneRootState_Conf)
apply fast+
done

lemma OneState_HPT_Target_Source:
  "\<lbrakk> TS \<in> HPT ST; S \<in> States SA; SA \<in> SAs (HA ST);
     States SA \<inter> Source TS = {} \<rbrakk> 
   \<Longrightarrow> S \<notin> Target TS"
apply (unfold Target_def)
apply auto
apply (unfold Source_def Image_def Int_def)
apply auto
apply (frule HPT_target_source)
apply auto
done

lemma RootState_notmem_Target [simp]:
  "\<lbrakk> TS \<in> HPT ST; S \<in> States (HARoot (HA ST)); RootState ST \<notin> Source TS \<rbrakk> \<Longrightarrow> S \<notin> Target TS" 
apply auto
apply (frule OneState_HPT_Target_Source)
prefer 4
apply fast+
apply simp
apply (unfold Int_def)
apply auto
apply (frule OneRootState_Source)
apply fast+
done

subsubsection \<open>Configuration \<open>Conf\<close>\<close>

lemma Conf_HAStates:
 "Conf ST \<subseteq> HAStates (HA ST)"
apply (cut_tac Rep_status_select)
apply (unfold IsConfSet_def status_def Status_def HAStates_def)
apply fast
done

lemma Conf_HAStates2 [simp]:
  "S \<in> Conf ST \<Longrightarrow> S \<in> HAStates (HA ST)"
apply (cut_tac ST="ST" in Conf_HAStates)
apply fast
done

lemma OneState_Conf [intro]:
  "\<lbrakk> S \<in> Conf ST; T \<in> Conf ST; S \<in> States SA; T \<in> States SA;
     SA \<in> SAs (HA ST)\<rbrakk> \<Longrightarrow> T = S"
apply (cut_tac ST=ST in IsConfSet_Status)
apply (unfold IsConfSet_def UniqueSucStates_def)
apply (case_tac "SA = HARoot (HA ST)")
apply (cut_tac ST=ST and S=S in OneRootState_Conf)
apply fast+
apply (simp only:OneRootState_Conf)
apply (erule conjE)+
apply (cut_tac HA="HA ST" in OneAncestor_HA)
apply (unfold OneAncestor_def)
apply (fold HARoot_def)
apply (erule_tac x=SA in ballE)
apply (drule ex1_implies_ex)
apply (erule exE)
apply (rename_tac U)
apply (erule_tac x=U in ballE)
apply (erule_tac x=SA in ballE)
apply (case_tac "U \<in> Conf ST")
apply simp
apply safe
apply fast+
apply simp
apply fast
done

lemma OneState_HPT_SA:
  "\<lbrakk> TS \<in> HPT ST; S \<in> Source TS; T \<in> Source TS;
     S \<in> States SA; T \<in> States SA; 
     SA \<in> SAs (HA ST) \<rbrakk> \<Longrightarrow> S = T"
apply (rule OneState_Conf)
apply auto
apply (frule HPT_Source_Conf, fast)+
done

lemma HPT_SAStates_Target_Source:
   "\<lbrakk>TS \<in> HPT ST; A \<in> SAs (HA ST); S \<in> States A; T \<in> States A; S \<in> Conf ST;
     T \<in> Target TS \<rbrakk> \<Longrightarrow> S \<in> Source TS"
apply (case_tac "States A \<inter> Source TS ={}")
apply (frule OneState_HPT_Target_Source)
apply fast
back
apply simp+
apply auto
apply (rename_tac U)
apply (cut_tac ST=ST in HPT_Source_Conf)
apply fast
apply (frule_tac S=S and T=U in OneState_Conf)
apply fast+
done

lemma HPT_Conf_Target_Source:
   "\<lbrakk>TS \<in> HPT ST; S \<in> Conf ST;
     S \<in> Target TS \<rbrakk> \<Longrightarrow> S \<in> Source TS"
apply (frule Conf_HAStates2)
apply (unfold HAStates_def)
apply auto
apply (simp only:HPT_SAStates_Target_Source)
done

lemma Conf_SA:
  "S \<in> Conf ST \<Longrightarrow> \<exists> A \<in> SAs (HA ST). S \<in> States A"
apply (cut_tac ST=ST in IsConfSet_Status)
apply (unfold IsConfSet_def)
apply fast
done

lemma HPT_Source_HAStates [simp]:
   "\<lbrakk> TS \<in> HPT ST; S \<in> Source TS \<rbrakk> \<Longrightarrow> S \<in> HAStates (HA ST)"
apply (frule HPT_Source_Conf)
apply (rule Conf_HAStates2)
apply fast
done

lemma Conf_Ancestor: 
  "\<lbrakk> S \<in> Conf ST;  A \<in> the (CompFun (HA ST) S) \<rbrakk> \<Longrightarrow> \<exists>! T \<in> States A. T \<in> Conf ST"
apply (cut_tac ST=ST in IsConfSet_Status)
apply (unfold IsConfSet_def UniqueSucStates_def)
apply safe
apply (erule_tac x=S in ballE)
prefer 2
apply blast
apply (erule_tac x=A in ballE)
prefer 2
apply fast
apply simp
apply (fast intro: HAStates_CompFun_SAs_mem Conf_HAStates2)+
done


lemma Conf_ChiRel: 
   "\<lbrakk> (S,T) \<in> ChiRel (HA ST); T \<in> Conf ST \<rbrakk> \<Longrightarrow> S \<in> Conf ST"
apply (unfold ChiRel_def Chi_def restrict_def)
apply simp
apply safe
apply simp
apply safe
apply (rename_tac SA)
apply (unfold HAStates_def)
apply simp
apply safe
apply (rename_tac U)
apply (cut_tac ST=ST in UniqueSucStates_Status) 
apply (unfold UniqueSucStates_def)
apply (erule_tac x=S in ballE)
apply (erule_tac x=SA in ballE)
apply auto
apply (case_tac "S \<in> Conf ST")
apply simp+
done

lemma Conf_ChiPlus:
   "\<lbrakk> (T,S) \<in> ChiPlus (HA ST) \<rbrakk> \<Longrightarrow>  S \<in> Conf ST \<longrightarrow> T \<in> Conf ST"
apply (unfold ChiPlus_def)
apply (rule_tac a="T" and b="S" and r="(ChiRel (HA ST))" in trancl_induct)
apply (fast intro: Conf_ChiRel)+
done

lemma HPT_Conf_Target_Source_ChiPlus:
  "\<lbrakk> TS \<in> HPT ST; S \<in> Conf ST; S \<in> ChiPlus (HA ST) `` Target TS \<rbrakk>
     \<Longrightarrow> S \<in> ChiStar (HA ST) `` Source TS"
apply auto
apply (rename_tac T)
apply (simp add: Image_def)
apply (frule HPT_Target_HAStates2) 
apply fast
apply (unfold HAStates_def)
apply auto
apply (rename_tac SA)
apply (case_tac "States SA \<inter> Source TS = {}")
apply (simp only:OneState_HPT_Target_Source)
apply auto
apply (rename_tac U)
apply (erule_tac x=U in ballE)
apply auto
apply (case_tac "U=T")
apply auto
apply (frule Conf_ChiPlus)
apply simp
apply (frule HPT_Conf_Target_Source)
apply fast
back
apply fast
apply (simp add:OneState_HPT_SA)
done

lemma OneState_HPT_Target_ChiRel:
   "\<lbrakk> TS \<in> HPT ST; (U,T) \<in> ChiRel (HA ST);
      U \<in> Target TS; A \<in> SAs (HA ST); T \<in> States A;
      S \<in> States A \<rbrakk> \<Longrightarrow> S \<notin> Target TS"
using [[hypsubst_thin = true]]
apply auto
apply (unfold HigherPriority_def restrict_def HPT_def MaxNonConflict_def Target_def)
apply auto
apply (rename_tac SSource STrigger SGuard SAction SUpdate STarget 
                  TSource TTrigger TGuard TAction TUpdate TTarget)
apply (cut_tac t="(TSource, (TTrigger, TGuard, TAction, TUpdate), TTarget)" and TS=TS and ST=ST and A=A in ET_target_source)
apply assumption+
apply simp
apply assumption
apply (frule ChiRel_HAStates)
apply (unfold HAStates_def)
apply safe
apply (cut_tac t="(SSource, (STrigger, SGuard, SAction, SUpdate), STarget)" and A=x and ST=ST and TS=TS in ET_target_source)
apply assumption+ 
apply simp
apply assumption
apply simp
apply (erule_tac x="(SSource, (STrigger, SGuard, SAction, SUpdate), STarget)" in ballE)
apply simp
apply (erule_tac x="(TSource, (TTrigger, TGuard, TAction, TUpdate), TTarget)" in ballE)
apply (simp add: ET_HADelta)
apply (cut_tac A="HA ST" and S=STarget and T=T and U=TSource in ChiRel_SA_OneAncestor)
apply fast+
apply (frule ET_Source_Conf)
apply (unfold Source_def image_def)
apply (case_tac "SSource \<in>Conf ST") 
prefer 2
apply (erule subsetCE)
back
apply fast
back
apply simp
apply (case_tac "TSource \<in>Conf ST") 
prefer 2
apply (erule subsetCE)
back
apply fast
apply simp
apply (case_tac "STarget=SSource") 
apply simp
apply (fast intro:Conf_ChiRel)+ 
done

lemma OneState_HPT_Target_ChiPlus [rule_format]:
   "\<lbrakk> TS \<in> HPT ST; (U,T) \<in> ChiPlus (HA ST);
      S \<in> Target TS; A \<in> SAs (HA ST); 
      S \<in> States A \<rbrakk> \<Longrightarrow> T \<in> States A \<longrightarrow> U \<notin> Target TS"
using [[hypsubst_thin = true]]
apply (unfold ChiPlus_def)
apply (rule_tac a="U" and b="T" and r="(ChiRel (HA ST))" in converse_trancl_induct)
apply auto
apply (simp only:OneState_HPT_Target_ChiRel)
apply (rename_tac V W)
apply (fold ChiPlus_def)
apply (unfold HPT_def MaxNonConflict_def Target_def HigherPriority_def restrict_def)
apply auto
apply (rename_tac SSource STrigger SGuard SAction SUpdate STarget 
                  TSource TTrigger TGuard TAction TUpdate TTarget)
apply (cut_tac t="(SSource, (STrigger, SGuard, SAction, SUpdate), STarget)" and ST=ST and TS=TS and A=A in ET_target_source)
apply assumption+ 
apply simp
apply assumption
apply simp
apply (frule ChiRel_HAStates)
apply (unfold HAStates_def)
apply safe
apply (cut_tac t="(TSource, (TTrigger, TGuard, TAction, TUpdate), TTarget)" and A=x and TS=TS and ST=ST in ET_target_source)
apply assumption+ 
apply simp
apply assumption
apply simp
apply (erule_tac x="(TSource, (TTrigger, TGuard, TAction, TUpdate), TTarget)" in ballE)
apply simp
apply (erule_tac x="(SSource, (STrigger, SGuard, SAction, SUpdate), STarget)" in ballE)
apply (simp add: ET_HADelta)
apply (cut_tac A="HA ST" and S=TTarget and T=T and U=SSource in ChiPlus_SA_OneAncestor)
apply (fast intro: ChiRel_ChiPlus_trans2)
apply fast+
apply (frule ET_Source_Conf)
apply (unfold Source_def image_def)
apply (case_tac "SSource \<in>Conf ST") 
prefer 2
apply (erule subsetCE)
back
apply fast
apply simp
apply (case_tac "TSource \<in>Conf ST") 
prefer 2
apply (erule subsetCE)
back
apply fast
back
apply simp
apply (case_tac "TTarget=SSource") 
apply simp
apply (frule_tac T=TTarget and S=SSource in Conf_ChiPlus)
apply simp
apply (frule_tac T=TSource and S=TTarget in OneState_Conf)
apply fast+
done

subsubsection \<open>\<open>RootExSem\<close>\<close>

lemma RootExSem_StepConf: 
   "\<lbrakk> TS \<in> HPT ST \<rbrakk> \<Longrightarrow> 
      RootExSem (SAs (HA ST)) (CompFun (HA ST)) (StepConf (HA ST) (Conf ST) TS)"
apply (unfold RootExSem_def)
apply (fold HARoot_def)
apply auto
apply (case_tac "RootState ST \<notin> Source TS") 
apply (rule_tac x="RootState ST" in exI)
apply simp
apply simp
apply (unfold Source_def image_def)
apply simp
apply (erule bexE)
apply (rename_tac T)
apply (rule_tac x="target T" in exI)
apply simp
apply (rule HPT_source_target)
apply auto
apply (rename_tac S T)
apply (case_tac "S \<in> Conf ST") 
apply (case_tac "T \<in> Conf ST")
apply (frule OneRootState_Conf) 
apply auto
apply (frule OneRootState_Conf) 
apply auto
apply (frule OneRootState_Conf) 
apply auto
apply (case_tac "RootState ST \<in> Source TS")
apply (case_tac "T \<in> Source TS")
apply (frule HPT_Source_Conf)
apply fast
apply (unfold StepConf_def)
apply auto
apply (frule OneState_HPT_Target)
apply (frule_tac SA="HARoot (HA ST)" and TS=TS and S=T and T="RootState ST" in OneState_HPT_Target)
apply fast+
apply simp+
apply (frule trancl_Int_mem, fold ChiPlus_def, force)+
prefer 2
apply (frule OneState_HPT_Target)
apply fast+
back
apply simp+
apply (case_tac "RootState ST \<in> Source TS") 
apply (case_tac "T = RootState ST")
apply auto
apply (frule trancl_Int_mem, fold ChiPlus_def, force)+
done

subsubsection \<open>\<open>StepConf\<close>\<close>

lemma Target_StepConf:
   "S \<in> Target TS \<Longrightarrow> S \<in> StepConf (HA ST) (Conf ST) TS"
apply (unfold StepConf_def)
apply auto
done

lemma Target_ChiRel_HAInit_StepConf:
   "\<lbrakk> S \<in> Target TS; (S,T) \<in> ChiRel A; 
      T \<in> HAInitStates A \<rbrakk> \<Longrightarrow> T \<in> StepConf A C TS" 
apply (unfold StepConf_def)
apply auto
done

lemma StepConf_HAStates: 
 "TS \<in> HPT ST \<Longrightarrow> StepConf (HA ST) (Conf ST) TS \<subseteq> HAStates (HA ST)"
apply (unfold StepConf_def)
apply auto
apply (frule tranclD2)
apply auto
done

lemma RootState_Conf_StepConf2 [simp]:
  "\<lbrakk> source T = RootState ST; T \<in> TS \<rbrakk> \<Longrightarrow> target T \<in> StepConf (HA ST) (Conf ST) TS"
apply (unfold StepConf_def)
apply auto
done

lemma HPT_StepConf_HAStates [simp]: 
   "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS \<rbrakk> \<Longrightarrow> S \<in> HAStates (HA ST)"
apply (unfold StepConf_def)
apply auto
apply (frule tranclD2)
apply auto
done

lemma StepConf_Target_HAInitStates: 
  "\<lbrakk> S \<in> StepConf (HA ST) (Conf ST) TS; S \<notin> Target TS; S \<notin> Conf ST\<rbrakk> \<Longrightarrow> S \<in> HAInitStates (HA ST)"
apply (unfold StepConf_def)
apply auto
apply (frule tranclD2)
apply auto
done

lemma InitSucState_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<notin> Target TS; A \<in> the (CompFun (HA ST) S);
      S \<notin> Conf ST; S \<in> StepConf (HA ST) (Conf ST) TS \<rbrakk> \<Longrightarrow>
      InitState A \<in> StepConf (HA ST) (Conf ST) TS"
apply (frule StepConf_HAStates [THEN subsetD, THEN CompFun_HAInitStates_HAStates])
apply fast+
apply (subst (asm) StepConf_def)
apply safe
apply (unfold StepConf_def)
apply (fast intro: HAInitStates_InitState_trancl)
apply (frule trancl_Int_mem, fold ChiPlus_def)
apply (fast intro:ChiPlus_HAStates_Right [THEN HAInitStates_InitState_trancl2]) 
done

lemma InitSucState_Target_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<in> Target TS; A \<in> the (CompFun (HA ST) S)\<rbrakk> \<Longrightarrow>
      InitState A \<in> StepConf (HA ST) (Conf ST) TS"
apply (frule HPT_Target_HAStates2 [THEN CompFun_HAInitStates_HAStates])
apply fast+
apply (frule HPT_Target_HAStates2 [THEN CompFun_ChiRel])
apply (fast intro:InitState_States)+
apply (unfold StepConf_def)
apply auto
done

lemma InitSucState_Conf_StepConf:
  "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; 
     S \<notin> Target TS; A \<in> the (CompFun (HA ST) S);
     S \<in> Conf ST; S \<in> ChiStar (HA ST) `` (Source TS) \<rbrakk> \<Longrightarrow> 
     InitState A \<in> StepConf (HA ST) (Conf ST) TS"
apply (frule Conf_HAStates2 [THEN CompFun_HAInitStates_HAStates])
apply fast
apply (subst (asm) StepConf_def)
apply safe
apply fast
apply (unfold StepConf_def)
apply (fast intro:HAInitStates_InitState_trancl)
apply (rename_tac T U V)
apply (frule trancl_Int_mem, fold ChiPlus_def, safe)
apply (subst (asm) Image_def, safe)
apply (rule_tac x=U in bexI)
apply (simp only: ChiPlus_HAStates_Right [THEN HAInitStates_InitState_trancl2])
apply fast
apply (subst (asm) Image_def, safe)
apply (rule_tac x=U in bexI)
apply (simp only: ChiPlus_HAStates_Right [THEN HAInitStates_InitState_trancl2])
apply fast
done

lemma SucState_Conf_StepConf:
  "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS;
     S \<notin> Target TS; A \<in> the (CompFun (HA ST) S);
     S \<in> Conf ST; States A \<inter> ChiStar (HA ST) `` (Source TS) = {} \<rbrakk> \<Longrightarrow> 
     \<exists> x. x \<in> States A \<and> x \<in> StepConf (HA ST) (Conf ST) TS" 
apply (unfold StepConf_def)
apply (cut_tac ST=ST in UniqueSucStates_Status)
apply (unfold UniqueSucStates_def)
apply (cut_tac ST=ST in Conf_HAStates2)
apply fast
apply (fold HAStates_def)
apply (erule_tac x=S in ballE)
apply (erule_tac x=A in ballE)
apply simp
apply fast+ 
done

lemma SucState_Conf_Source_StepConf:
  "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; 
     S \<notin> Target TS; A \<in> the (CompFun (HA ST) S);
     S \<in> Conf ST; States A \<inter> ChiStar (HA ST) `` (Source TS) \<noteq> {}; 
     S \<notin> ChiStar (HA ST) `` (Source TS)\<rbrakk> \<Longrightarrow> 
     \<exists> x. x \<in> States A \<and> x \<in> StepConf (HA ST) (Conf ST) TS"
apply safe
apply (rename_tac T U)
apply (frule Conf_HAStates2 [THEN CompFun_ChiRel])
apply fast+
apply simp
apply (case_tac "U=T")
apply simp
apply (rotate_tac -5)
apply (simp only:Source_def Target_def image_def)
apply safe
apply (rename_tac Source Trigger Guard Action Update Target)
apply (erule_tac x=Target in allE)
apply simp
apply (frule HPT_source_target2)
apply fast+
apply (rule HAStates_CompFun_SAs_mem)
apply (rule Conf_HAStates2)
apply fast+
apply (frule ChiStar_ChiPlus_noteq)
apply fast
apply (case_tac "U=S")
apply (fast intro:ChiStar_Self ChiRel_ChiPlus_OneAncestor ChiPlus_ChiStar)+
done

lemma SucState_StepConf:
  "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; 
     A \<in> the (CompFun (HA ST) S) \<rbrakk> \<Longrightarrow> 
     \<exists> x. x \<in> States A \<and> x \<in> StepConf (HA ST) (Conf ST) TS" 
apply (case_tac "S \<in> Target TS")
apply (fast intro: InitSucState_Target_StepConf InitState_States)
apply (case_tac "S \<in> Conf ST")
prefer 2
apply (fast intro: InitSucState_StepConf InitState_States)
apply (case_tac "S \<in> ChiStar (HA ST) `` (Source TS)")
apply (fast intro: InitSucState_Conf_StepConf InitState_States)
apply (case_tac "States A \<inter> ChiStar (HA ST) `` (Source TS) = {}")
apply (fast intro: SucState_Conf_StepConf SucState_Conf_Source_StepConf)+
done

subsubsection \<open>\<open>StepStatus\<close>\<close>

lemma StepStatus_expand:
   "Abs_status (HA ST, StepConf (HA ST) (Conf ST) TS, 
                StepActEvent TS, U !!! (Value ST)) 
    = (StepStatus ST TS U)"
apply (unfold StepStatus_def Let_def)
apply (subst Rep_status_tuple)
apply auto
done

lemma UniqueSucState_Conf_Source_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; A \<in> SAs (HA ST);
      A \<in> the (CompFun (HA ST) S); T \<in> States A; U \<in> States A;
      T \<in> StepConf (HA ST) (Conf ST) TS; T \<noteq> U; U \<in> Conf ST \<rbrakk> \<Longrightarrow> 
      U \<in> ChiStar (HA ST) `` Source TS"
apply (frule_tac ?S2.0=T in StepConf_HAStates [THEN subsetD, THEN CompFun_ChiRel])
apply fast+
apply (frule_tac ?S2.0=U in StepConf_HAStates [THEN subsetD, THEN CompFun_ChiRel])
apply fast+
apply (frule_tac S=S and T=U in Conf_ChiRel, fast)
apply (case_tac "S \<in> ChiStar (HA ST) `` Source TS")
apply (fast intro: ChiRel_ChiStar_trans)
apply (case_tac "U \<in> Source TS")
apply force
apply (unfold StepConf_def)
apply simp
apply safe
apply (fast intro: HPT_SAStates_Target_Source)+
apply (rename_tac V)
apply (case_tac "V=S")
apply (frule_tac S=S in HPT_Conf_Target_Source, fast+)
apply (fast intro: ChiStar_Image ChiRel_OneAncestor)+
apply (rename_tac V W) 
apply (frule trancl_Int_mem, fold ChiPlus_def, safe)
apply (cut_tac ST=ST and S=S in HPT_Conf_Target_Source_ChiPlus)
apply fast+
apply (simp only:Image_def, safe)
apply (case_tac "(V, T) \<notin> ChiRel (HA ST)")
apply (frule_tac S=V and T=T in ChiPlus_ChiRel_Ex)
apply (fast, safe)
apply (rename_tac X)
apply (case_tac "X=S")
apply (rule_tac x=W in bexI)
prefer 4
apply (case_tac "V=S")
prefer 2
apply simp
apply (fast intro: ChiPlus_ChiRel ChiRel_ChiPlus_trans2 ChiRel_OneAncestor)+
done

lemma UniqueSucState_Target_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; A \<in> SAs (HA ST);
      A \<in> the (CompFun (HA ST) S); T \<in> States A; U \<in> States A;
      T \<in> StepConf (HA ST) (Conf ST) TS; T \<noteq> U \<rbrakk> \<Longrightarrow> 
      U \<notin> Target TS"
apply auto
apply (frule_tac ST=ST in Target_StepConf)
apply (subst (asm) (2) StepConf_def)
apply simp
apply safe
apply (cut_tac TS=TS and ST=ST and S=S and T=U in UniqueSucState_Conf_Source_StepConf)
apply fast+
apply (simp add: OneState_HPT_Target)
apply (simp only:OneState_HPT_Target_ChiRel)
apply (rename_tac V W)
apply (frule_tac U=W and S=V and T=T in ChiRel_ChiPlus_trans2)
apply (frule trancl_Int_mem, fold ChiPlus_def, force)
apply (simp only:OneState_HPT_Target_ChiPlus)
done

lemma UniqueSucState_Target_ChiRel_StepConf: 
   "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; A \<in> SAs (HA ST);
      A \<in> the (CompFun (HA ST) S); T \<in> States A; U \<in> States A;
      T \<in> StepConf (HA ST) (Conf ST) TS; T \<noteq> U; (V,U) \<in> ChiRel (HA ST); 
      U \<in> HAInitStates (HA ST) \<rbrakk>
    \<Longrightarrow> V \<notin> Target TS" 
apply auto
apply (frule_tac A="HA ST" and C="Conf ST" in Target_ChiRel_HAInit_StepConf)
apply fast+
apply (subst (asm) (2) StepConf_def, safe)
apply (fast intro:UniqueSucState_Conf_Source_StepConf) 
apply (simp only:OneState_HPT_Target_ChiRel) 
apply (fast intro:OneHAInitState_SAStates)
apply (frule trancl_Int_mem, fold ChiPlus_def)
apply (fast intro:OneHAInitState_SAStates) 
done

lemma UniqueSucState_Target_ChiPlus_StepConf [rule_format]:
  "\<lbrakk> TS \<in> HPT ST; (S,T) \<in> ChiRel (HA ST); (S,U) \<in> ChiRel (HA ST); 
     V \<in> Target TS; (V,W) \<in> ChiRel (HA ST); T \<notin> ChiStar (HA ST) `` Source TS;
     (W,U) \<in> (ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST))\<^sup>+;
     T \<in> Conf ST \<rbrakk> \<Longrightarrow> (S,U) \<in> ChiRel (HA ST) \<longrightarrow> T=U"    
apply (frule_tac S=S and T=T in Conf_ChiRel)
apply fast
apply (rule_tac a="W" and b="U" and r="ChiRel (HA ST) \<inter> HAInitStates (HA ST) \<times> HAInitStates (HA ST)" in trancl_induct)
apply safe
apply (rename_tac X)
apply (case_tac "W=S")
apply simp
prefer 2
apply (simp add: ChiRel_OneAncestor)
prefer 2
apply (rename_tac X Y)
apply (case_tac "X=S")
apply simp
prefer 2
apply (simp add: ChiRel_OneAncestor)
prefer 2
apply (frule_tac a=V in ChiRel_HAStates)
apply (unfold HAStates_def)
apply (simp,safe)
apply (rename_tac Y)
apply (case_tac "States Y \<inter> Source TS = {}")
apply (simp add:OneState_HPT_Target_Source)
apply (subst (asm) Int_def, safe)
apply (rename_tac Z)
apply (frule_tac S=V and T=S in Conf_ChiRel)
apply fast
apply (frule HPT_Conf_Target_Source)
prefer 2
apply fast
apply fast
apply (frule_tac S=Z and T=V in  OneState_HPT_SA)
apply fast+
apply simp
apply (fast intro: ChiPlus_ChiRel ChiRel_ChiPlus_trans ChiPlus_ChiStar)
apply (simp add: Image_def)
apply (frule trancl_Int_mem, fold ChiPlus_def, simp, safe)
back
apply (frule_tac T=W and S=S in Conf_ChiPlus)
apply simp
apply (frule_tac S=V and T=W in Conf_ChiRel)
apply fast
apply (frule_tac a=V in ChiRel_HAStates)
apply (unfold HAStates_def)
apply (simp, safe)
apply (rename_tac Z)
apply (case_tac "States Z \<inter> Source TS = {}")
apply (simp add:OneState_HPT_Target_Source)
apply (subst (asm) Int_def, safe)
apply (frule_tac S=V in HPT_Conf_Target_Source)
apply fast+
apply (rename_tac P)
apply (frule_tac S=P and T=V in  OneState_HPT_SA)
apply fast+
apply (frule_tac U=V and S=W and T=S in ChiRel_ChiPlus_trans2)
apply fast+
apply (fast intro: ChiPlus_ChiRel ChiRel_ChiPlus_trans ChiPlus_ChiStar)
apply (case_tac "T=S")
apply (simp add: ChiRel_OneAncestor)+
done

lemma UniqueSucStates_SAStates_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<in> StepConf (HA ST) (Conf ST) TS; A \<in> SAs (HA ST);
      A \<in> the (CompFun (HA ST) S); T \<in> States A; U \<in> States A;
      T \<in> StepConf (HA ST) (Conf ST) TS; T \<noteq> U \<rbrakk> \<Longrightarrow> 
      U \<notin> StepConf (HA ST) (Conf ST) TS"
apply (subst StepConf_def)
apply (simp, safe)
apply (rule UniqueSucState_Conf_Source_StepConf)
apply fast+
apply (frule_tac U=U in UniqueSucState_Target_StepConf)
apply fast+
apply (frule_tac U=U in UniqueSucState_Target_ChiRel_StepConf)
apply fast+
apply (rename_tac V W)
apply (frule trancl_Int_mem, fold ChiPlus_def)
apply (simp, safe)
apply (frule_tac ?S2.0=T in StepConf_HAStates [THEN subsetD, THEN CompFun_ChiRel])
apply fast+
apply (frule_tac ?S2.0=U in StepConf_HAStates [THEN subsetD, THEN CompFun_ChiRel])
apply fast+
apply (subst (asm) (2) StepConf_def)
apply (simp, safe)
apply (fast intro: UniqueSucState_Target_ChiPlus_StepConf)
apply (frule_tac U=W and T=U and S=T in OneState_HPT_Target_ChiPlus)
apply (fast intro: ChiPlus_ChiRel ChiRel_ChiPlus_trans2 OneHAInitState_SAStates)+
apply (frule trancl_Int_mem, fold ChiPlus_def, simp, safe)
apply (fast intro:OneHAInitState_SAStates)
done

lemma UniqueSucStates_Ancestor_StepConf:
   "\<lbrakk> TS \<in> HPT ST; S \<in> HAStates (HA ST); SA \<in> the (CompFun (HA ST) S); 
      T \<in> States SA; T \<in> StepConf (HA ST) (Conf ST) TS \<rbrakk>
    \<Longrightarrow> S \<in> StepConf (HA ST) (Conf ST) TS"
apply (rule notnotD, rule notI)
apply (subst (asm) StepConf_def)
apply (simp, safe)
apply (frule  CompFun_ChiRel, fast+)
apply (frule Conf_ChiRel, fast) 
apply (frule ChiRel_ChiStar_Source_notmem, fast+)
apply (subst (asm) StepConf_def)
apply force
apply (case_tac "States SA \<inter> Source TS = {}")
apply (simp add:OneState_HPT_Target_Source)
apply (subst (asm) Int_def)
apply (simp, safe)
apply (rename_tac U)
apply (frule_tac ?S2.0=U in CompFun_ChiRel, fast+)
apply (frule Conf_ChiRel) 
apply (frule HPT_Source_Conf, fast)
apply (case_tac "S \<in> ChiStar (HA ST) `` Source TS")
apply (subst (asm) StepConf_def)
apply simp
apply (frule ChiRel_ChiStar_notmem)
apply fast+
apply (case_tac "U=S")
apply (subst (asm) StepConf_def)
apply force
apply (subst (asm) StepConf_def)
apply force
apply (rename_tac U)
apply (case_tac "U=S")
apply (subst (asm) StepConf_def)
apply force
apply (frule  CompFun_ChiRel, fast+)
apply (simp add: ChiRel_OneAncestor)
apply (rename_tac U V)
apply (frule trancl_Int_mem, fold ChiPlus_def, simp, safe)
apply (frule tranclD2)
apply safe
apply (rename_tac W)
apply (case_tac "W=S")
apply simp
prefer 2
apply (frule CompFun_ChiRel, fast+)
apply (simp only: ChiRel_OneAncestor)
apply (subst (asm) StepConf_def)
apply safe
apply (simp add: Image_def)
apply (erule_tac x=U in ballE)
apply (case_tac "U=S")
apply fast
apply (simp add: rtrancl_eq_or_trancl)
apply fast
apply (simp add: Image_def)
apply (rename_tac W)
apply (erule_tac x=U in ballE)
apply (simp add: rtrancl_eq_or_trancl)
apply fast+
done

lemma UniqueSucStates_StepConf:
   "\<lbrakk> TS \<in> HPT ST \<rbrakk> \<Longrightarrow> 
      UniqueSucStates (SAs (HA ST)) (CompFun (HA ST)) (StepConf (HA ST) (Conf ST) TS)"
apply (unfold UniqueSucStates_def)
apply auto
apply (simp only: SucState_StepConf)
apply (rule notnotD, rule notI)
apply (frule UniqueSucStates_SAStates_StepConf)
apply fast
prefer 2
apply fast
apply (rule HAStates_CompFun_SAs_mem)
prefer 2
apply fast
apply (simp only: HAStates_def, fast)
apply fast+
back
apply (frule UniqueSucStates_Ancestor_StepConf)
prefer 2
apply fast
apply (simp only:HAStates_def, fast)
apply fast+
done

lemma Status_Step:
  "\<lbrakk> TS \<in> HPT ST; U \<in> ResolveRacing TS \<rbrakk> \<Longrightarrow>  
    (HA ST, StepConf (HA ST) (Conf ST) TS, StepActEvent TS, U !!! (Value ST)) \<in> status"
apply (unfold status_def Status_def)
apply auto
apply (frule StepActEvent_HAEvents)
apply blast
apply (unfold IsConfSet_def)
apply (rule conjI, frule StepConf_HAStates, unfold HAStates_def,assumption)
apply (rule conjI, rule RootExSem_StepConf, assumption)
apply (rule UniqueSucStates_StepConf, assumption) 
done

subsection \<open>Meta Theorem: Preservation for Statecharts\<close>

(* We prove, that the well-formedness of a Statecharts is preserved by the semantics
   (theorem "IsConfSet_StepConf") *)

lemma IsConfSet_StepConf:
       "TS \<in> HPT ST \<Longrightarrow> IsConfSet (SAs (HA ST)) (CompFun (HA ST))
                                  (StepConf (HA ST) (Conf ST) TS)"
apply (unfold IsConfSet_def)
apply auto
apply (frule StepConf_HAStates)
apply (unfold HAStates_def, fast)
apply (rule RootExSem_StepConf, assumption)
apply (rule UniqueSucStates_StepConf, assumption)
done

lemma HA_StepStatus_HPT_ResolveRacing [simp]:
  "\<lbrakk> TS \<in> HPT ST; U \<in> ResolveRacing TS \<rbrakk> \<Longrightarrow> 
    HA (StepStatus ST TS U) = HA ST"
apply (subst StepStatus_expand [THEN sym])
apply (subst HA_def)
apply auto
apply (subst Abs_status_inverse)
apply auto
apply (rule Status_Step)
apply auto
done

end
