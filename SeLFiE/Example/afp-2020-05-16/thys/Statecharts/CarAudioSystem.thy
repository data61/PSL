(*  Title:      statecharts/Examples/CarAudioSystem.thy

    Author:     Steffen Helke and Florian Kammüller, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Example Specification for a Car Audio System\<close>

theory CarAudioSystem
imports HAKripke HAOps
begin

subsection \<open>Definitions\<close>

subsubsection \<open>Data space for two Integer-Variables\<close>                  

datatype d = V0 int
             | V1 int

primrec
 Sel0 :: "d => int" where
  "Sel0 (V0 i) = i"

primrec
 Sel1 :: "d => int" where
  "Sel1 (V1 i) = i"


(* Selectors for the two Integer-Variables *)
definition
  Select0 :: "[d data] => int" where
  "Select0 d = Sel0 (DataPart d 0)"

definition 
  Select1 :: "[d data] => int" where 
  "Select1 d = Sel1 (DataPart d 1)"

(* Data Space for tthe two Integer-Variables *)
definition
  DSpace :: "d dataspace" where
  "DSpace = Abs_dataspace ([range V0, range V1])"

(* Lift in InitData *)
definition
  LiftInitData :: "(d list) => d data" where
  "LiftInitData L = Abs_data (L,DSpace)"

(* Lift in PUpdate-Function *)
definition
  LiftPUpdate :: "(d data => ((d option) list)) => d pupdate" where
  "LiftPUpdate L = Abs_pupdate
                        (\<lambda> d. if ((DataSpace d) = DSpace) then
                                   Abs_pdata (L d, DSpace)
                              else (Data2PData d))"

subsubsection \<open>Sequential Automaton  \<open>Root_CTRL\<close>\<close>                  

definition
 Root_CTRL_States :: "string set" where
 "Root_CTRL_States = {''CarAudioSystem''}"

definition
 Root_CTRL_Init :: "string" where
 "Root_CTRL_Init = ''CarAudioSystem''"

definition
 Root_CTRL_Labels :: "(string,string,d)label set" where
 "Root_CTRL_Labels = {}"

definition
 Root_CTRL_Delta :: "(string,string,d)trans set" where
 "Root_CTRL_Delta = {}"

definition
 Root_CTRL :: "(string,string,d)seqauto" where
 "Root_CTRL = Abs_seqauto (Root_CTRL_States, Root_CTRL_Init,
                            Root_CTRL_Labels, Root_CTRL_Delta)"

subsubsection \<open>Sequential Automaton  \<open>CDPlayer_CTRL\<close>\<close>                  

definition
 CDPlayer_CTRL_States :: "string set" where
 "CDPlayer_CTRL_States = {''ReadTracks'',''CDFull'',''CDEmpty''}"

definition
 CDPlayer_CTRL_Init :: "string" where
 "CDPlayer_CTRL_Init = ''CDEmpty''"

definition
 CDPlayer_CTRL_Update1 :: "d pupdate" where
 "CDPlayer_CTRL_Update1 = LiftPUpdate (% d. [None, Some (V1 ((Select0 d) + 1))])"

definition
 CDPlayer_CTRL_Action1 :: "(string,d)action" where
 "CDPlayer_CTRL_Action1 = ({},CDPlayer_CTRL_Update1)"

definition
 CDPlayer_CTRL_Update2 :: "d pupdate" where
 "CDPlayer_CTRL_Update2 = LiftPUpdate (% d. [Some (V0 ((Select0 d) + 1)), None])"

definition
 CDPlayer_CTRL_Action2 :: "(string,d)action" where
 "CDPlayer_CTRL_Action2 = ({},CDPlayer_CTRL_Update2)"

definition
 CDPlayer_CTRL_Update3 :: "d pupdate" where
 "CDPlayer_CTRL_Update3 = LiftPUpdate (% d. [Some (V0 0), None])"

definition
 CDPlayer_CTRL_Action3 :: "(string,d)action" where
 "CDPlayer_CTRL_Action3 = ({},CDPlayer_CTRL_Update3)"

definition
 CDPlayer_CTRL_Labels :: "(string,string,d)label set" where
 "CDPlayer_CTRL_Labels = {(En ''LastTrack'', defaultguard, CDPlayer_CTRL_Action1),
                          (En ''NewTrack'', defaultguard, CDPlayer_CTRL_Action2),
                          (And (En ''CDEject'') (In ''On''), defaultguard, CDPlayer_CTRL_Action3),
                          (En ''CDIn'', defaultguard, defaultaction)}"

definition
 CDPlayer_CTRL_Delta :: "(string,string,d)trans set" where
 "CDPlayer_CTRL_Delta = {(''ReadTracks'',(En ''LastTrack'', defaultguard, CDPlayer_CTRL_Action1),
                          ''CDFull''),
                         (''CDFull'',(And (En ''CDEject'') (In ''On''), defaultguard, CDPlayer_CTRL_Action3), 
                          ''CDEmpty''),
                         (''ReadTracks'',(En ''NewTrack'', defaultguard, CDPlayer_CTRL_Action2),
                          ''ReadTracks''),
                         (''CDEmpty'',(En ''CDIn'', defaultguard, defaultaction),
                          ''ReadTracks'')}"

definition
 CDPlayer_CTRL :: "(string,string,d)seqauto" where
 "CDPlayer_CTRL  = Abs_seqauto (CDPlayer_CTRL_States, CDPlayer_CTRL_Init,
                                CDPlayer_CTRL_Labels, CDPlayer_CTRL_Delta)"

subsubsection \<open>Sequential Automaton  \<open>AudioPlayer_CTRL\<close>\<close>                  

definition
 AudioPlayer_CTRL_States :: "string set" where
 "AudioPlayer_CTRL_States = {''Off'',''On''}"

definition
 AudioPlayer_CTRL_Init :: "string" where
 "AudioPlayer_CTRL_Init = ''Off''"

definition
 AudioPlayer_CTRL_Labels :: "(string,string,d)label set" where
 "AudioPlayer_CTRL_Labels = {(En ''O'', defaultguard, defaultaction)}"

definition
 AudioPlayer_CTRL_Delta :: "(string,string,d)trans set" where
 "AudioPlayer_CTRL_Delta = {(''Off'', (En ''O'', defaultguard, defaultaction), ''On''),
                            (''On'', (En ''O'', defaultguard, defaultaction), ''Off'')}"

definition
 AudioPlayer_CTRL :: "(string,string,d)seqauto" where
 "AudioPlayer_CTRL = Abs_seqauto (AudioPlayer_CTRL_States, AudioPlayer_CTRL_Init,
                                  AudioPlayer_CTRL_Labels, AudioPlayer_CTRL_Delta)"

subsubsection \<open>Sequential Automaton  \<open>On_CTRL\<close>\<close>                  

definition
 On_CTRL_States :: "string set" where
 "On_CTRL_States = {''TunerMode'',''CDMode''}"

definition
 On_CTRL_Init :: "string" where
 "On_CTRL_Init = ''TunerMode''"

definition
 On_CTRL_Labels :: "(string,string,d)label set" where
 "On_CTRL_Labels = {(And (En ''Src'') (In ''CDFull''), defaultguard, defaultaction),
                    (En ''Src'', defaultguard, defaultaction),
                    (En ''CDEject'', defaultguard, defaultaction),
                    (En ''EndOfTitle'', (\<lambda> d. (DataPart d 0) =  (DataPart d 1)), defaultaction)}"

definition
 On_CTRL_Delta :: "(string,string,d)trans set" where
 "On_CTRL_Delta = {(''TunerMode'',(And (En ''Src'') (In ''CDFull''), defaultguard, defaultaction),''CDMode''),
                   (''CDMode'', (En ''Src'', defaultguard, defaultaction), ''TunerMode''),
                   (''CDMode'', (En ''CDEject'', defaultguard, defaultaction), ''TunerMode''), 
                   (''CDMode'', (En ''EndOfTitle'', (\<lambda> d. (DataPart d 0) =  (DataPart d 1)), defaultaction),
                    ''TunerMode'')}"

definition
 On_CTRL :: "(string,string,d)seqauto" where
 "On_CTRL = Abs_seqauto (On_CTRL_States, On_CTRL_Init,
                         On_CTRL_Labels, On_CTRL_Delta)"

subsubsection \<open>Sequential Automaton  \<open>TunerMode_CTRL\<close>\<close>                  

definition
 TunerMode_CTRL_States :: "string set" where
 "TunerMode_CTRL_States = {''1'',''2'',''3'',''4''}"

definition
 TunerMode_CTRL_Init :: "string" where
 "TunerMode_CTRL_Init = ''1''"

definition
 TunerMode_CTRL_Labels :: "(string,string,d)label set" where
 "TunerMode_CTRL_Labels = {(En ''Next'', defaultguard, defaultaction),
                       (En ''Back'', defaultguard, defaultaction)}"

definition
 TunerMode_CTRL_Delta :: "(string,string,d)trans set" where
 "TunerMode_CTRL_Delta = {(''1'', (En ''Next'', defaultguard, defaultaction), ''2''),
                      (''2'', (En ''Next'', defaultguard, defaultaction), ''3''),
                      (''3'', (En ''Next'', defaultguard, defaultaction), ''4''),
                      (''4'', (En ''Next'', defaultguard, defaultaction), ''1''),
                      (''1'', (En ''Back'', defaultguard, defaultaction), ''4''),
                      (''4'', (En ''Back'', defaultguard, defaultaction), ''3''),
                      (''3'', (En ''Back'', defaultguard, defaultaction), ''2''),
                      (''2'', (En ''Back'', defaultguard, defaultaction), ''1'')}"

definition
 TunerMode_CTRL :: "(string,string,d)seqauto" where
 "TunerMode_CTRL  = Abs_seqauto (TunerMode_CTRL_States, TunerMode_CTRL_Init,
                                  TunerMode_CTRL_Labels, TunerMode_CTRL_Delta)"

subsubsection \<open>Sequential Automaton  \<open>CDMode_CTRL\<close>\<close>                  

definition
 CDMode_CTRL_States :: "string set" where
 "CDMode_CTRL_States = {''Playing'',''SelectingNextTrack'',
                        ''SelectingPreviousTrack''}"

definition
 CDMode_CTRL_Init :: "string" where
 "CDMode_CTRL_Init = ''Playing''"

definition
 CDMode_CTRL_Update1 :: "d pupdate" where
 "CDMode_CTRL_Update1 = LiftPUpdate (% d. [ Some (V0 ((Select0 d) + 1)), None ])"

definition
 CDMode_CTRL_Action1 :: "(string,d)action" where
 "CDMode_CTRL_Action1 = ({},CDMode_CTRL_Update1)"

definition
 CDMode_CTRL_Update2 :: "d pupdate" where
 "CDMode_CTRL_Update2 = LiftPUpdate (% d. [ Some (V0 ((Select0 d) - 1)), None ])"

definition
 CDMode_CTRL_Action2 :: "(string,d)action" where
 "CDMode_CTRL_Action2 = ({},CDMode_CTRL_Update2)"

definition
 CDMode_CTRL_Labels :: "(string,string,d)label set" where
 "CDMode_CTRL_Labels = {(En ''Next'', defaultguard, defaultaction),
                        (En ''Back'', defaultguard, defaultaction),
                        (En ''Ready'', defaultguard, CDMode_CTRL_Action1),
                        (En ''Ready'', defaultguard, CDMode_CTRL_Action2),
                        (En ''EndOfTitle'',(\<lambda> (d:: d data). (Select0 d) < (Select1 d)), defaultaction)}"

definition
 CDMode_CTRL_Delta :: "(string,string,d)trans set" where
 "CDMode_CTRL_Delta = {(''Playing'', (En ''Next'', defaultguard, defaultaction) , ''SelectingNextTrack''),
                       (''SelectingNextTrack'', (En ''Ready'', defaultguard, CDMode_CTRL_Action1) ,''Playing''),
                       (''Playing'', (En ''Back'', defaultguard, defaultaction) ,''SelectingPreviousTrack''),
                       (''SelectingPreviousTrack'', (En ''Ready'', defaultguard, CDMode_CTRL_Action2), 
                        ''Playing''),
                       (''Playing'', (En ''EndOfTitle'', (\<lambda> (d:: d data). (Select0 d) < (Select1 d)), defaultaction),
                        ''SelectingNextTrack'')}"

definition
 CDMode_CTRL :: "(string,string,d)seqauto" where
 "CDMode_CTRL  = Abs_seqauto (CDMode_CTRL_States, CDMode_CTRL_Init,
                               CDMode_CTRL_Labels, CDMode_CTRL_Delta)"

subsubsection \<open>Hierarchical Automaton  \<open>CarAudioSystem\<close>\<close>                  

definition
     CarAudioSystem :: "(string,string,d)hierauto" where
     "CarAudioSystem = ((PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0]))
                  [++] (''CarAudioSystem'',CDPlayer_CTRL)
                  [++] (''CarAudioSystem'',AudioPlayer_CTRL)
                  [++] (''On'', TunerMode_CTRL)
                  [++] (''On'', CDMode_CTRL))"


subsection \<open>Lemmas\<close>

subsubsection \<open>Sequential Automaton \<open>CDMode_CTRL\<close>\<close>

lemma check_Root_CTRL:
  "(Root_CTRL_States,Root_CTRL_Init,Root_CTRL_Labels,Root_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def Root_CTRL_States_def Root_CTRL_Init_def Root_CTRL_Labels_def Root_CTRL_Delta_def)
apply simp
done

lemma States_Root_CTRL:
  "States Root_CTRL = Root_CTRL_States"
apply (simp add: Root_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_Root_CTRL) 
done

lemma Init_State_Root_CTRL:
  "InitState Root_CTRL = Root_CTRL_Init"
apply (simp add: Root_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_Root_CTRL) 
done

lemma Labels_Root_CTRL:
  "Labels Root_CTRL = Root_CTRL_Labels"
apply (simp add: Root_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_Root_CTRL)
done

lemma Delta_Root_CTRL:
  "Delta Root_CTRL = Root_CTRL_Delta"
apply (simp add: Root_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_Root_CTRL)
done

schematic_goal Events_Root_CTRL:
  "SAEvents Root_CTRL = ?X"
apply (unfold SAEvents_def expr_def)
apply (rule trans)
apply (simp add: expr_def Delta_Root_CTRL Root_CTRL_Delta_def)
apply (rule refl)
done

subsubsection \<open>Sequential Automaton \<open>CDPlayer_CTRL\<close>\<close>

lemma check_CDPlayer_CTRL:
  "(CDPlayer_CTRL_States,CDPlayer_CTRL_Init,CDPlayer_CTRL_Labels,CDPlayer_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def CDPlayer_CTRL_States_def CDPlayer_CTRL_Init_def CDPlayer_CTRL_Labels_def CDPlayer_CTRL_Delta_def)
apply simp
done

lemma States_CDPlayer_CTRL:
  "States CDPlayer_CTRL = CDPlayer_CTRL_States"
apply (simp add: CDPlayer_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_CDPlayer_CTRL) 
done

lemma Init_State_CDPlayer_CTRL:
  "InitState CDPlayer_CTRL = CDPlayer_CTRL_Init"
apply (simp add: CDPlayer_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_CDPlayer_CTRL) 
done

lemma Labels_CDPlayer_CTRL:
  "Labels CDPlayer_CTRL = CDPlayer_CTRL_Labels"
apply (simp add: CDPlayer_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_CDPlayer_CTRL)
done

lemma Delta_CDPlayer_CTRL:
  "Delta CDPlayer_CTRL = CDPlayer_CTRL_Delta"
apply (simp add: CDPlayer_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_CDPlayer_CTRL)
done

schematic_goal Events_CDPlayer_CTRL:
  "SAEvents CDPlayer_CTRL = ?X"
apply (unfold SAEvents_def)
apply (rule trans)
apply (simp add: expr_def Delta_CDPlayer_CTRL CDPlayer_CTRL_Delta_def CDPlayer_CTRL_Action1_def CDPlayer_CTRL_Action2_def CDPlayer_CTRL_Action3_def Label_def)
apply (rule refl)
done

subsubsection \<open>Sequential Automaton \<open>AudioPlayer_CTRL\<close>\<close>

lemma check_AudioPlayer_CTRL:
  "(AudioPlayer_CTRL_States,AudioPlayer_CTRL_Init,AudioPlayer_CTRL_Labels,AudioPlayer_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def AudioPlayer_CTRL_States_def AudioPlayer_CTRL_Init_def AudioPlayer_CTRL_Labels_def AudioPlayer_CTRL_Delta_def)
apply simp
done

lemma States_AudioPlayer_CTRL:
  "States AudioPlayer_CTRL = AudioPlayer_CTRL_States"
apply (simp add: AudioPlayer_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_AudioPlayer_CTRL) 
done

lemma Init_State_AudioPlayer_CTRL:
  "InitState AudioPlayer_CTRL = AudioPlayer_CTRL_Init"
apply (simp add: AudioPlayer_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_AudioPlayer_CTRL) 
done

lemma Labels_AudioPlayer_CTRL:
  "Labels AudioPlayer_CTRL = AudioPlayer_CTRL_Labels"
apply (simp add: AudioPlayer_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_AudioPlayer_CTRL)
done

lemma Delta_AudioPlayer_CTRL:
  "Delta AudioPlayer_CTRL = AudioPlayer_CTRL_Delta"
apply (simp add: AudioPlayer_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_AudioPlayer_CTRL)
done

schematic_goal Events_AudioPlayer_CTRL:
  "SAEvents AudioPlayer_CTRL = ?X"
apply (unfold SAEvents_def)
apply (rule trans)
apply (simp add: expr_def Delta_AudioPlayer_CTRL AudioPlayer_CTRL_Delta_def Label_def)
apply (rule refl)
done

subsubsection \<open>Sequential Automaton \<open>On_CTRL\<close>\<close>

lemma check_On_CTRL:
  "(On_CTRL_States,On_CTRL_Init,On_CTRL_Labels,On_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def On_CTRL_States_def On_CTRL_Init_def On_CTRL_Labels_def On_CTRL_Delta_def)
apply simp
done

lemma States_On_CTRL:
  "States On_CTRL = On_CTRL_States"
apply (simp add: On_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_On_CTRL) 
done

lemma Init_State_On_CTRL:
  "InitState On_CTRL = On_CTRL_Init"
apply (simp add: On_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_On_CTRL) 
done

lemma Labels_On_CTRL:
  "Labels On_CTRL = On_CTRL_Labels"
apply (simp add: On_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_On_CTRL)
done

lemma Delta_On_CTRL:
  "Delta On_CTRL = On_CTRL_Delta"
apply (simp add: On_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_On_CTRL)
done

schematic_goal Events_On_CTRL:
  "SAEvents On_CTRL = ?X"
apply (unfold SAEvents_def)
apply (rule trans)
apply (simp add: expr_def Delta_On_CTRL On_CTRL_Delta_def Label_def)
apply (rule refl)
done

subsubsection \<open>Sequential Automaton \<open>TunerMode_CTRL\<close>\<close>

lemma check_TunerMode_CTRL:
  "(TunerMode_CTRL_States,TunerMode_CTRL_Init,TunerMode_CTRL_Labels,TunerMode_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def TunerMode_CTRL_States_def TunerMode_CTRL_Init_def TunerMode_CTRL_Labels_def TunerMode_CTRL_Delta_def)
apply simp
done

lemma States_TunerMode_CTRL:
  "States TunerMode_CTRL = TunerMode_CTRL_States"
apply (simp add: TunerMode_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_TunerMode_CTRL) 
done

lemma Init_State_TunerMode_CTRL:
  "InitState TunerMode_CTRL = TunerMode_CTRL_Init"
apply (simp add: TunerMode_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_TunerMode_CTRL) 
done

lemma Labels_TunerMode_CTRL:
  "Labels TunerMode_CTRL = TunerMode_CTRL_Labels"
apply (simp add: TunerMode_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_TunerMode_CTRL)
done

lemma Delta_TunerMode_CTRL:
  "Delta TunerMode_CTRL = TunerMode_CTRL_Delta"
apply (simp add: TunerMode_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_TunerMode_CTRL)
done

schematic_goal Events_TunerMode_CTRL:
  "SAEvents TunerMode_CTRL = ?X"
apply (unfold SAEvents_def)
apply (rule trans)
apply (simp add: expr_def Delta_TunerMode_CTRL TunerMode_CTRL_Delta_def Label_def)
apply (rule refl)
done

subsubsection \<open>Sequential Automaton \<open>CDMode_CTRL\<close>\<close>

lemma check_CDMode_CTRL:
  "(CDMode_CTRL_States,CDMode_CTRL_Init,CDMode_CTRL_Labels,CDMode_CTRL_Delta) : seqauto"
apply (unfold seqauto_def SeqAuto_def CDMode_CTRL_States_def CDMode_CTRL_Init_def CDMode_CTRL_Labels_def CDMode_CTRL_Delta_def)
apply simp
done

lemma States_CDMode_CTRL:
  "States CDMode_CTRL = CDMode_CTRL_States"
apply (simp add: CDMode_CTRL_def)
apply (unfold States_def)
apply (simp add: Abs_seqauto_inverse check_CDMode_CTRL) 
done

lemma Init_State_CDMode_CTRL:
  "InitState CDMode_CTRL = CDMode_CTRL_Init"
apply (simp add: CDMode_CTRL_def)
apply (unfold InitState_def)
apply (simp add: Abs_seqauto_inverse check_CDMode_CTRL) 
done

lemma Labels_CDMode_CTRL:
  "Labels CDMode_CTRL = CDMode_CTRL_Labels"
apply (simp add: CDMode_CTRL_def)
apply (unfold Labels_def)
apply (simp add: Abs_seqauto_inverse check_CDMode_CTRL)
done

lemma Delta_CDMode_CTRL:
  "Delta CDMode_CTRL = CDMode_CTRL_Delta"
apply (simp add: CDMode_CTRL_def)
apply (unfold Delta_def)
apply (simp add: Abs_seqauto_inverse check_CDMode_CTRL)
done

schematic_goal Events_CDMode_CTRL:
  "SAEvents CDMode_CTRL = ?X"
apply (unfold SAEvents_def)
apply (rule trans)
apply (simp add: expr_def Label_def Delta_CDMode_CTRL CDMode_CTRL_Delta_def CDMode_CTRL_Action1_def CDMode_CTRL_Action2_def)
apply (rule refl)
done

subsubsection \<open>Hierarchical Automaton \<open>CarAudioSystem\<close>\<close>

lemmas CarAudioSystemStates = States_Root_CTRL States_CDPlayer_CTRL States_AudioPlayer_CTRL States_On_CTRL 
                              States_TunerMode_CTRL States_CDMode_CTRL
                              Root_CTRL_States_def CDPlayer_CTRL_States_def AudioPlayer_CTRL_States_def 
                              On_CTRL_States_def TunerMode_CTRL_States_def CDMode_CTRL_States_def

lemmas CarAudioSystemInitState = Init_State_Root_CTRL Init_State_CDPlayer_CTRL Init_State_AudioPlayer_CTRL 
                                 Init_State_On_CTRL Init_State_TunerMode_CTRL Init_State_CDMode_CTRL
                                 Root_CTRL_Init_def CDPlayer_CTRL_Init_def AudioPlayer_CTRL_Init_def
                                 On_CTRL_Init_def TunerMode_CTRL_Init_def CDMode_CTRL_Init_def  

lemmas CarAudioSystemEvents = Events_Root_CTRL Events_CDPlayer_CTRL Events_AudioPlayer_CTRL Events_On_CTRL 
                              Events_TunerMode_CTRL Events_CDMode_CTRL 

lemmas CarAudioSystemthms = CarAudioSystemStates CarAudioSystemEvents CarAudioSystemInitState

(* -------------------------------------------------------------- *)
(*                  States of \<guillemotright> CarAudioSystem \<guillemotleft>                  *)
(* -------------------------------------------------------------- *)

schematic_goal CarAudioSystem_StatesRoot:
  "HAStates (PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0])) = ?X"
apply (wellformed CarAudioSystemthms)+
done

lemmas CarAudioSystemthms_1 = CarAudioSystemthms CarAudioSystem_StatesRoot


schematic_goal CarAudioSystem_StatesCDPlayer:
  "HAStates (PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0]) [++] 
            (''CarAudioSystem'',CDPlayer_CTRL)) = ?X"
apply (wellformed CarAudioSystemthms_1)+
done

lemmas CarAudioSystemthms_2 = CarAudioSystemthms_1 CarAudioSystem_StatesCDPlayer

schematic_goal CarAudioSystem_StatesAudioPlayer:
  "HAStates (PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0])
                  [++] (''CarAudioSystem'',CDPlayer_CTRL)
                  [++] (''CarAudioSystem'',AudioPlayer_CTRL)) = ?X"
apply (wellformed CarAudioSystemthms_2)+
done

lemmas CarAudioSystemthms_3 = CarAudioSystemthms_2 CarAudioSystem_StatesAudioPlayer

schematic_goal CarAudioSystem_StatesTunerMode:
  "HAStates (PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0])
                  [++] (''CarAudioSystem'',CDPlayer_CTRL)
                  [++] (''CarAudioSystem'',AudioPlayer_CTRL)
                  [++] (''On'', TunerMode_CTRL )) = ?X"
apply (wellformed CarAudioSystemthms_3)+
done

lemmas CarAudioSystemthms_4 = CarAudioSystemthms_3 CarAudioSystem_StatesTunerMode

schematic_goal CarAudioSystem_StatesCDMode:
  "HAStates (PseudoHA Root_CTRL (LiftInitData [V0 0, V1 0])
                  [++] (''CarAudioSystem'',CDPlayer_CTRL)
                  [++] (''CarAudioSystem'',AudioPlayer_CTRL)
                  [++] (''On'', TunerMode_CTRL )
                  [++] (''On'', CDMode_CTRL)) = ?X"
apply (wellformed CarAudioSystemthms_4)+
done

lemmas CarAudioSystemthms_5 = CarAudioSystemthms_4 CarAudioSystem_StatesCDMode

schematic_goal SAsCarAudioSystem:
  "SAs CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal EventsCarAudioSystem:
 "HAEvents CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal CompFunCarAudioSystem:
  "CompFun CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal StatesCarAudioSystem:
  "HAStates CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal ValueCarAudioSystem:
  "HAInitValue CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal HAInitStatesCarAudioSystem:
  "HAInitStates CarAudioSystem = ?X"
by (simp add: HAInitStates_def SAsCarAudioSystem CarAudioSystemInitState)

schematic_goal HARootCarAudioSystem:
  "HARoot CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal HAInitStateCarAudioSystem:
  "HAInitState CarAudioSystem = ?X"
by (simp add: HARootCarAudioSystem HAInitState_def CarAudioSystemInitState)


(* -------------------------------------------------------------- *)
(*      Components of the initial data space assignement          *)
(* -------------------------------------------------------------- *)

lemma check_DataSpace [simp]:
  "[range V0, range V1] \<in> dataspace"
apply (unfold dataspace_def DataSpace.DataSpace_def)
apply auto
apply (rename_tac D)
apply (case_tac "D")
apply auto
done

lemma PartNum_DataSpace [simp]:
  "PartNum (DSpace) = 2"
apply (unfold PartNum_def DSpace_def)
apply (simp add: Abs_dataspace_inverse) 
done

lemma PartDom_DataSpace_V0 [simp]:
  "(PartDom DSpace 0) = range V0"
apply (unfold PartDom_def DSpace_def)
apply (simp add: Abs_dataspace_inverse) 
done

lemma PartDom_DataSpace_V1 [simp]:
  "(PartDom DSpace (Suc 0)) = range V1"
apply (unfold PartDom_def DSpace_def)
apply (simp add: Abs_dataspace_inverse) 
done

lemma check_InitialData [simp]:
  "([V0 0, V1 0],DSpace) \<in> data"
apply (unfold data_def Data.Data_def)
apply auto
apply (rename_tac d)
apply (case_tac "d=0 \<or> d = 1")
apply auto
done

lemma Select0_InitData [simp]:
  "Select0 (LiftInitData [V0 0, V1 0]) = 0"
apply (unfold LiftInitData_def Select0_def DataPart_def DataValue_def)
apply (simp add: Abs_data_inverse) 
done

lemma Select1_InitData [simp]:
  "Select1 (LiftInitData [V0 0, V1 0]) = 0"
apply (unfold LiftInitData_def Select1_def DataPart_def DataValue_def)
apply (simp add: Abs_data_inverse) 
done

lemma HAInitValue1_CarAudioSystem:
  "CarAudioSystem |=H= Atom (VAL (\<lambda> d. (Select0 d) = 0))"
apply (simp add: ValueCarAudioSystem)
done

lemma HAInitValue2_CarAudioSystem:
  "CarAudioSystem |=H= Atom (VAL (\<lambda> d. (Select1 d) = 0))"
apply (simp add: ValueCarAudioSystem)
done

lemma HAInitValue_DSpace_CarAudioSystem [simp]:
  "Data.DataSpace (LiftInitData [V0 0, V1 0]) = DSpace"
apply (unfold LiftInitData_def Data.DataSpace_def)
apply (simp add: Abs_data_inverse) 
done

lemma check_InitStatus [simp]:
  "(CarAudioSystem, InitConf CarAudioSystem, {},LiftInitData [V0 0, V1 0]) \<in> status"
apply (unfold status_def Status_def)
apply (simp add: ValueCarAudioSystem) 
done

lemma InitData_InitStatus [simp]:
  "Value (InitStatus CarAudioSystem) = LiftInitData [V0 0, V1 0]" 
apply (simp add: ValueCarAudioSystem)
done

lemma Events_InitStatus [simp]:
  "Events (InitStatus CarAudioSystem) = {}" 
apply (unfold InitStatus_def Events_def)
apply (simp add: Abs_status_inverse) 
done

lemma Conf_InitStatus [simp]:
  "Conf (InitStatus CarAudioSystem) = InitConf CarAudioSystem" 
apply (unfold InitStatus_def Conf_def)
apply (simp add: Abs_status_inverse) 
done

lemma CompFunCarAudioSystem_the:
  "the (CompFun CarAudioSystem ''On'') =  {CDMode_CTRL,TunerMode_CTRL}"
apply (unfold CarAudioSystem_def)
apply (subst AddSA_CompFun_the)
prefer 3
apply (subst AddSA_CompFun_the)
prefer 3
apply (subst AddSA_CompFun_the2)
apply (wellformed CarAudioSystemthms_5)+
done

lemma CompFunCarAudioSystem_the2:
  "the (CompFun CarAudioSystem ''CarAudioSystem'') =  {AudioPlayer_CTRL, CDPlayer_CTRL}"
apply (unfold CarAudioSystem_def)
apply (subst AddSA_CompFun_the3)
prefer 5
apply (subst AddSA_CompFun_the3)
prefer 5
apply (subst AddSA_CompFun_the)
prefer 3
apply (subst AddSA_CompFun_the)
prefer 3
apply (subst PseudoHA_CompFun_the)
apply (wellformed CarAudioSystemthms_5)+
done

lemma CompFunCarAudioSystem_the3:
  "the (CompFun CarAudioSystem ''Off'') =  {}"
apply (unfold CarAudioSystem_def)
apply (subst AddSA_CompFun_the3)
prefer 5
apply (subst AddSA_CompFun_the3)
prefer 5
apply (subst AddSA_CompFun_the2)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal CompFunCarAudioSystem_ran:
  "ran (CompFun CarAudioSystem) = ?X"
apply (unfold CarAudioSystem_def)
apply (rule AddSA_CompFun_ran3_IFF)
prefer 6
apply (subst AddSA_CompFun_PseudoHA_ran2)
prefer 4
apply (simp add: insert_commute)
apply (wellformed CarAudioSystemthms_5)+
done

lemma Root_CTRL_CDPlayer_CTRL_noteq [simp]:
  "Root_CTRL \<noteq> CDPlayer_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma Root_CTRL_AudioPlayer_CTRL_noteq [simp]:
  "Root_CTRL \<noteq> AudioPlayer_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma Root_CTRL_TunerMode_CTRL_noteq [simp]:
  "Root_CTRL \<noteq> TunerMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma Root_CTRL_CDMode_CTRL_noteq [simp]:
  "Root_CTRL \<noteq> CDMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma CDPlayer_CTRL_AudioPlayer_CTRL_noteq [simp]:
  "CDPlayer_CTRL \<noteq> AudioPlayer_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma CDPlayer_CTRL_TunerMode_CTRL_noteq [simp]:
  "CDPlayer_CTRL \<noteq> TunerMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma CDPlayer_CTRL_CDMode_CTRL_noteq [simp]:
  "CDPlayer_CTRL \<noteq> CDMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma AudioPlayer_CTRL_TunerMode_CTRL_noteq [simp]:
  "AudioPlayer_CTRL \<noteq>  TunerMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma AudioPlayer_CTRL_CDMode_CTRL_noteq [simp]:
  "AudioPlayer_CTRL \<noteq> CDMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

lemma TunerMode_CTRL_CDMode_CTRL_noteq [simp]:
  "TunerMode_CTRL \<noteq>  CDMode_CTRL"
apply (rule SA_States_disjunct)
apply (wellformed CarAudioSystemthms_5)+
done

schematic_goal Chi_CarAudioSystem:
  "Chi CarAudioSystem ''CarAudioSystem'' = ?X"
apply (unfold Chi_def)
apply (rule trans)
apply (simp add: SAsCarAudioSystem StatesCarAudioSystem restrict_def CompFunCarAudioSystem_the2)
apply (rule trans)
apply (simp add: not_sym)
apply (simp add: CarAudioSystemStates insert_or)
done

schematic_goal Chi_CarAudioSystem_On:
  "Chi CarAudioSystem ''On'' = ?X"
apply (unfold Chi_def)
apply (rule trans)
apply (simp add: SAsCarAudioSystem StatesCarAudioSystem restrict_def CompFunCarAudioSystem_the)
apply (rule trans)
apply (simp add: not_sym)
apply (simp add: CarAudioSystemStates insert_or)
done

schematic_goal Chi_CarAudioSystem_Off:
  "Chi CarAudioSystem ''Off'' = ?X"
apply (unfold Chi_def)
apply (simp add: SAsCarAudioSystem StatesCarAudioSystem restrict_def CompFunCarAudioSystem_the3)
done

schematic_goal InitConf_CarAudioSystem:
  "InitConf CarAudioSystem = ?X"
apply (unfold CarAudioSystem_def)
apply (rule AddSA_InitConf_IFF)+
apply simp
apply (wellformed CarAudioSystemthms_5)
apply fast
apply (wellformed CarAudioSystemthms_5)
apply simp
apply (simp add: CarAudioSystemthms_5)
apply (wellformed CarAudioSystemthms_5)
apply fast
apply (wellformed CarAudioSystemthms_5)
apply fast
apply simp
apply (wellformed CarAudioSystemthms_5)
apply fast
apply (wellformed CarAudioSystemthms_5)
apply fast
apply simp
apply (wellformed CarAudioSystemthms_5)
apply force
apply (wellformed CarAudioSystemthms_5)
apply fast
apply (simp add: CarAudioSystemthms_5)
done

lemma Initial_State_CarAudioSystem:
  "CarAudioSystem |=H= Atom (IN ''Off'')"
apply (simp add: InitConf_CarAudioSystem )
done


end

