(*<*)
(*
   Title: FR.thy  (FlexRay: Verification)
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
section \<open>FlexRay: Verification\<close>

theory  FR_proof
imports FR
begin


subsection \<open>Properties of the function Send\<close>

lemma Send_L1:
assumes "Send return send get activation"
       and "send t  \<noteq> []"
shows  "(activation t) \<noteq> []"
using assms by (simp add: Send_def, auto)

lemma Send_L2:
assumes "Send return send get activation"
       and "(activation t)  \<noteq> []"
       and "return t \<noteq> []"
shows  "(send t) \<noteq> []"
using assms  by (simp add: Send_def) 


subsection \<open>Properties of the component Scheduler\<close>

lemma Scheduler_L1:
assumes h1:"Scheduler C activation"
        and h2:"(activation t) \<noteq> []"
shows "(t mod (cycleLength C)) mem (schedule C)"
using assms
proof - 
   { assume  a1:"\<not> t mod cycleLength C mem schedule C"
      from h1 have 
      "if t mod cycleLength C mem schedule C 
       then activation t = [t mod cycleLength C]
       else activation t = []"
         by (simp add: Scheduler_def Let_def)
     from a1 and this have "activation t = []" by simp
     from this and h2 have sg3:"False" by simp
   } from this have  sg4:"(t mod (cycleLength C)) mem (schedule C)" by blast
  from this show ?thesis by simp
qed

lemma Scheduler_L2:
assumes "Scheduler C activation"
       and "\<not> (t mod cycleLength C) mem (schedule C)"
shows "activation t = []"
using assms by (simp add: Scheduler_def Let_def)  

lemma Scheduler_L3:
assumes "Scheduler C activation"
       and "(t mod cycleLength C) mem (schedule C)"
shows "activation t \<noteq> []"
using assms by (simp add: Scheduler_def Let_def)

lemma Scheduler_L4:
assumes "Scheduler C activation"
       and "(t mod cycleLength C) mem (schedule C)"
shows "activation t = [t mod cycleLength C]"
using assms by (simp add: Scheduler_def Let_def)
 
lemma correct_DisjointSchedules1:
assumes h1:"DisjointSchedules n nC"
       and h2:"IdenticCycleLength n nC"
       and h3:"(t mod cycleLength (nC i)) mem schedule (nC i)" 
       and h4:"i < n"
       and h5:"j < n"
       and h6:"i \<noteq> j"
shows "\<not> (t mod cycleLength (nC j) mem schedule (nC j))"
proof -
  from h1 and h4 and h5 and h6 have sg1:"disjoint (schedule (nC i)) (schedule (nC j))"
    by (simp add: DisjointSchedules_def) 
  from h2 and h4 and h5 have sg2:"cycleLength (nC i) = cycleLength (nC j)"
    by (metis IdenticCycleLength_def)
  from sg1 and h3 have sg3:"\<not> (t mod (cycleLength (nC i))) mem (schedule (nC j))" 
    by (simp add: mem_notdisjoint2)
  from sg2 and sg3 show ?thesis by simp
qed


subsection \<open>Disjoint Frames\<close>

lemma disjointFrame_L1:
assumes h1:"DisjointSchedules n nC"  
       and h2:"IdenticCycleLength n nC"
       and h3:"\<forall> i < n. FlexRayController (nReturn i) rcv 
                      (nC i) (nStore i) (nSend i) (nGet i)"
       and h4:"nSend i t \<noteq> []"
       and h5:"i < n"
       and h6:"j < n"
       and h7:"i \<noteq> j"
shows "nSend j t = []"
proof - 
  from h3 and h5 have sg1:
   "FlexRayController (nReturn i) rcv (nC i) (nStore i) (nSend i) (nGet i)"
    by auto
  from h3 and h6 have sg2:
   "FlexRayController (nReturn j) rcv (nC j) (nStore j) (nSend j) (nGet j)"
    by auto
  from sg1 obtain activation1 where
     a1:"Scheduler (nC i) activation1" and 
     a2:"BusInterface activation1 (nReturn i) rcv (nStore i) (nSend i) (nGet i)"
     by (simp add: FlexRayController_def, auto)
  from sg2 obtain activation2 where
     a3:"Scheduler (nC j) activation2" and 
     a4:"BusInterface activation2 (nReturn j) rcv (nStore j) (nSend j) (nGet j)"
     by (simp add: FlexRayController_def, auto)
  from h1 and h5 and h6 and h7 have sg3:"disjoint (schedule (nC i)) (schedule (nC j))"
    by (simp add: DisjointSchedules_def) 
  from a2 have  sg4a:"Send (nReturn i) (nSend i) (nGet i) activation1" 
     by (simp add:  BusInterface_def)
  from sg4a and h4 have sg5:"activation1 t  \<noteq> []" by (simp add: Send_L1)
  from a1 and sg5 have sg6:"(t mod (cycleLength (nC i))) mem (schedule (nC i))" 
     by (simp add: Scheduler_L1)
  from h2 and h5 and h6 have sg7:"cycleLength (nC i) = cycleLength (nC j)"
    by (metis IdenticCycleLength_def)  
  from sg3 and sg6 have sg8:"\<not> (t mod (cycleLength (nC i))) mem (schedule (nC j))" 
    by (simp add: mem_notdisjoint2)
  from sg8 and sg7 have sg9:"\<not> (t mod (cycleLength (nC j))) mem (schedule (nC j))" 
    by simp
  from sg9 and a3 have sg10:"activation2 t = []" by (simp add: Scheduler_L2) 
  from a4 have sg11:"Send (nReturn j) (nSend j) (nGet j) activation2" 
     by (simp add:  BusInterface_def)
  from sg11 and sg10 show ?thesis by (simp add: Send_def)
qed

lemma disjointFrame_L2:
assumes "DisjointSchedules n nC"  
       and "IdenticCycleLength n nC"
       and "\<forall> i < n. FlexRayController (nReturn i) rcv 
                      (nC i) (nStore i) (nSend i) (nGet i)"
shows "inf_disj n nSend"
using assms
  apply (simp add: inf_disj_def, clarify)
  by (rule disjointFrame_L1, auto)


lemma disjointFrame_L3:
assumes h1:"DisjointSchedules n nC"  
     and h2:"IdenticCycleLength n nC"
     and h3:"\<forall> i < n. FlexRayController (nReturn i) rcv 
                      (nC i) (nStore i) (nSend i) (nGet i)"
    and h4:"t mod cycleLength (nC i) mem schedule (nC i)"
    and h5:"i < n"
    and h6:"j < n"
    and h7:"i \<noteq> j"
shows "nSend j t = []"
proof - 
  from h2 and h5 and h6 have sg1:"cycleLength (nC i) = cycleLength (nC j)"
    by (metis IdenticCycleLength_def)  
  from h1 and h5 and h6 and h7 have sg2:"disjoint (schedule (nC i)) (schedule (nC j))"
    by (simp add: DisjointSchedules_def) 
  from sg2 and h4 have sg3:"\<not> (t mod (cycleLength (nC i))) mem (schedule (nC j))" 
    by (simp add: mem_notdisjoint2)
  from sg1 and sg3 have sg4:"\<not> (t mod (cycleLength (nC j))) mem (schedule (nC j))" 
    by simp
  from h3 and h6 have sg5:
   "FlexRayController (nReturn j) rcv (nC j) (nStore j) (nSend j) (nGet j)"
    by auto
  from sg5 obtain activation2 where
     a1:"Scheduler (nC j) activation2" and 
     a2:"BusInterface activation2 (nReturn j) rcv (nStore j) (nSend j) (nGet j)"
     by (simp add: FlexRayController_def, auto)
  from sg4 and a1 have sg6:"activation2 t = []" by (simp add: Scheduler_L2) 
  from a2 have sg7:"Send (nReturn j) (nSend j) (nGet j) activation2" 
     by (simp add:  BusInterface_def)
  from sg7 and sg6 show ?thesis by (simp add: Send_def)
qed


subsection \<open>Properties of the sheaf of channels nSend\<close>

lemma fr_Send1:
assumes frc:"FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
        and h1:"\<not> (t mod cycleLength (nC i) mem schedule (nC i))"
 shows      "(nSend i) t = []"
proof - 
  from frc obtain activation where 
    a1:"Scheduler (nC i) activation"  and
    a2:"BusInterface activation (nReturn i) recv (nStore i) (nSend i) (nGet i)"
    by (simp add: FlexRayController_def, auto)
  from a1 and h1 have sg1:"activation t = []" by (simp add: Scheduler_L2)
  from a2 have sg2:"Send (nReturn i) (nSend i) (nGet i) activation"
    by (simp add: BusInterface_def)
  from sg2 and sg1 show ?thesis by (simp add: Send_def)
qed

lemma fr_Send2:
 assumes h1:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
     and h2:"DisjointSchedules n nC"
     and h3:"IdenticCycleLength n nC"
     and h4:"t mod cycleLength (nC k) mem schedule (nC k)"
     and h5:"k < n"
 shows "nSend k t = nReturn k t"
proof - 
 from h1 and h5 have sg1:
   "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
    by auto
  from sg1 obtain activation where
     a1:"Scheduler (nC k) activation" and 
     a2:"BusInterface activation (nReturn k) recv (nStore k) (nSend k) (nGet k)"
     by (simp add: FlexRayController_def, auto)
  from a1 and h4 have sg3:"activation t \<noteq> []" by (simp add: Scheduler_L3)
  from a2 have  sg4:"Send (nReturn k) (nSend k) (nGet k) activation" 
     by (simp add:  BusInterface_def)
  from sg4 and sg3 show ?thesis by (simp add: Send_def)
qed

lemma fr_Send3:
 assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
     and "DisjointSchedules n nC"
     and "IdenticCycleLength n nC"
     and "t mod cycleLength (nC k) mem schedule (nC k)"
     and "k < n"
     and "nReturn k t \<noteq> []"
 shows "nSend k t \<noteq> []"
using assms by (simp add: fr_Send2)

lemma fr_Send4:
 assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
     and "DisjointSchedules n nC"
     and "IdenticCycleLength n nC"
     and "t mod cycleLength (nC k) mem schedule (nC k)"
     and "k < n"
     and "nReturn k t \<noteq> []"
 shows "\<exists>k. k < n \<longrightarrow> nSend k t \<noteq> []"
using assms
by (metis  fr_Send3)

lemma fr_Send5:
 assumes h1:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
     and h2:"DisjointSchedules n nC"
     and h3:"IdenticCycleLength n nC"
     and h4:"t mod cycleLength (nC k) mem schedule (nC k)"
     and h5:"k < n"
     and h6:"nReturn k t \<noteq> []"
     and h7:"\<forall>k<n. nSend k t = []"
 shows "False"
proof - 
  from h1 and h2 and h3 and h4 and h5 and h6 have sg1:"nSend k t \<noteq> []"
    by (simp add: fr_Send2)
  from h7 and h5 have sg2:"nSend k t = []" by blast 
  from sg1 and sg2 show ?thesis by simp    
qed

lemma fr_Send6:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC"
       and "t mod cycleLength (nC k) mem schedule (nC k)"
       and "k < n"
       and "nReturn k t \<noteq> []"
shows "\<exists>k<n. nSend k t \<noteq> []"
using assms
by (metis fr_Send3)

lemma fr_Send7:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC"
       and "t mod cycleLength (nC k) mem schedule (nC k)"
       and "k < n"
       and "j < n"
       and "nReturn k t = []"
shows "nSend j t = []"
using assms
by (metis (full_types) disjointFrame_L3 fr_Send2)

lemma fr_Send8:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC"
       and "t mod cycleLength (nC k) mem schedule (nC k)"
       and "k < n"
       and "nReturn k t = []"
shows "\<not> (\<exists>k<n. nSend k t \<noteq> [])"
using assms by (auto, simp add: fr_Send7)

lemma fr_nC_Send:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "k < n"
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC"
       and "t mod cycleLength (nC k) mem schedule (nC k)"
shows "\<forall>j. j < n \<and> j \<noteq> k \<longrightarrow> (nSend j) t = []"
using assms by (clarify, simp add: disjointFrame_L3)

lemma length_nSend:
assumes h1:"BusInterface activation (nReturn i) recv (nStore i) (nSend i) (nGet i)"
       and h2:"\<forall>t. length (nReturn i t) \<le> Suc 0"
shows   "length (nSend i t) \<le> Suc 0"
proof - 
  from h1 have sg1:"Send (nReturn i) (nSend i) (nGet i) activation"
    by (simp add: BusInterface_def)
  from sg1 have sg2:
   "if activation t = [] then nGet i t = [] \<and> nSend i t = []
    else nGet i t = activation t \<and> nSend i t = nReturn i t"
    by (simp add: Send_def)
  show ?thesis
  proof (cases "activation t = []")
    assume a1:"activation t = []"
    from sg2 and a1 show ?thesis by simp
  next
    assume a2:"activation t \<noteq> []"
    from h2 have sg3:"length (nReturn i t) \<le> Suc 0" by auto
    from sg2 and a2 and sg3 show ?thesis by simp
  qed
qed

lemma msg_nSend:
assumes "BusInterface activation (nReturn i) recv (nStore i) (nSend i) (nGet i)"
       and "msg (Suc 0) (nReturn i)"
shows "msg (Suc 0) (nSend i)"
using assms by (simp add: msg_def, clarify, simp add: length_nSend)

lemma Broadcast_nSend_empty1:
assumes h1:"Broadcast n nSend recv"
       and h2:"\<forall>k<n. nSend k t = []"
shows      "recv t = []"
using assms 
by (metis Broadcast_def)


subsection \<open>Properties of the sheaf of channels  nGet\<close>

lemma fr_nGet1a:
assumes h1:"FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)" 
       and h2:"t mod cycleLength (nC k) mem schedule (nC k)"
shows "nGet k t = [t mod cycleLength (nC k)]"
proof -
  from h1  obtain activation1 where
     a1:"Scheduler (nC k) activation1" and 
     a2:"BusInterface activation1 (nReturn k) recv (nStore k) (nSend k) (nGet k)"
     by (simp add: FlexRayController_def, auto)
   from a2 have sg1:"Send (nReturn k) (nSend k) (nGet k) activation1"
     by (simp add: BusInterface_def)
   from sg1 have sg2:
    "if activation1 t = [] then nGet k t = [] \<and> nSend k t = []
     else nGet k t = activation1 t \<and> nSend k t = nReturn k t" 
     by (simp add: Send_def)
  from a1 and h2 have sg3:"activation1 t = [t mod cycleLength (nC k)]"
     by (simp add: Scheduler_L4)
  from sg2 and sg3 show ?thesis  by simp
qed

lemma fr_nGet1:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
       and "t mod cycleLength (nC k) mem schedule (nC k)"
       and "k < n"
shows "nGet k t = [t mod cycleLength (nC k)]"
using assms
by (metis  fr_nGet1a)

lemma fr_nGet2a:
assumes h1:"FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)" 
       and h2:"\<not> (t mod cycleLength (nC k) mem schedule (nC k))"
shows "nGet k t = []" 
proof -
   from h1 obtain activation1 where
     a1:"Scheduler (nC k) activation1" and 
     a2:"BusInterface activation1 (nReturn k) recv (nStore k) (nSend k) (nGet k)"
     by (simp add: FlexRayController_def, auto)
   from a2 have sg2:"Send (nReturn k) (nSend k) (nGet k) activation1"
     by (simp add: BusInterface_def)
   from sg2 have sg3:
    "if activation1 t = [] then nGet k t = [] \<and> nSend k t = []
     else nGet k t = activation1 t \<and> nSend k t = nReturn k t" 
     by (simp add: Send_def)
  from a1 and h2 have sg4:"activation1 t = []"
     by (simp add: Scheduler_L2)
  from sg3 and sg4 show ?thesis  by simp
qed

lemma fr_nGet2:
assumes h1:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
     and h2:"\<not> (t mod cycleLength (nC k) mem schedule (nC k))"
     and h3:"k < n"
 shows "nGet k t = []"
proof -
  from h1 and h3 have sg1:
    "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
    by auto
  from sg1 and h2 show ?thesis by (rule fr_nGet2a)
qed

lemma length_nGet1:
 assumes "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
 shows    "length (nGet k t) \<le> Suc 0"
proof (cases "t mod cycleLength (nC k) mem schedule (nC k)")
  assume "t mod cycleLength (nC k) mem schedule (nC k)"
  from assms and this have "nGet k t = [t mod cycleLength (nC k)]" 
    by (rule fr_nGet1a)
  then show ?thesis by auto
next
  assume "\<not> (t mod cycleLength (nC k) mem schedule (nC k))"
  from assms and this have "nGet k t = []" by (rule fr_nGet2a)
  then show ?thesis by auto
qed

lemma msg_nGet1:
 assumes "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
 shows    "msg (Suc 0) (nGet k)"
using assms 
by (simp add: msg_def, auto, rule length_nGet1)

lemma msg_nGet2:
assumes "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "k < n"
shows "msg (Suc 0) (nGet k)"
using assms
by (metis msg_nGet1) 


subsection \<open>Properties of the sheaf of channels nStore\<close>

lemma fr_nStore_nReturn1:
 assumes h0:"Broadcast n nSend recv"
     and h1:"inf_disj n nSend"
     and h2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
     and h5:"t mod cycleLength (nC k) mem schedule (nC k)"
     and h6:"k < n"
     and h7:"j < n"
     and h8:"j \<noteq> k"
 shows  "nStore j t = nReturn k t"
proof - 
  from h2 and h6 have sg1:
    "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
    by auto
  from h2 and h7 have sg2:
    "FlexRayController (nReturn j) recv (nC j) (nStore j) (nSend j) (nGet j)"
    by auto
   from sg1 obtain activation1 where
     a1:"Scheduler (nC k) activation1" and 
     a2:"BusInterface activation1 (nReturn k) recv (nStore k) (nSend k) (nGet k)"
     by (simp add: FlexRayController_def, auto)
  from sg2 obtain activation2 where
     a3:"Scheduler (nC j) activation2" and 
     a4:"BusInterface activation2 (nReturn j) recv (nStore j) (nSend j) (nGet j)"
     by (simp add: FlexRayController_def, auto)
  from a4 have sg3:"Receive recv (nStore j) activation2"
     by (simp add: BusInterface_def)
  from this have sg4:
   "if activation2 t = [] then nStore j t = recv t else nStore j t = []"
    by (simp add: Receive_def)
  from a1 and h5 have sg5:"activation1 t \<noteq> []"
     by (simp add: Scheduler_L3)
 from h4 and h6 and h7 have sg6:"cycleLength (nC k) = cycleLength (nC j)"
    by (metis IdenticCycleLength_def)  
  from h3 and h6 and h7 and h8 have sg7:"disjoint (schedule (nC k)) (schedule (nC j))"
    by (simp add: DisjointSchedules_def) 
  from sg7 and h5 have sg8:"\<not> (t mod (cycleLength (nC k))) mem (schedule (nC j))" 
    by (simp add: mem_notdisjoint2)
  from sg6 and sg8 have sg9:"\<not> (t mod (cycleLength (nC j))) mem (schedule (nC j))" 
    by simp
  from sg9 and a3 have sg10:"activation2 t = []" by (simp add: Scheduler_L2) 
  from sg10 and sg4 have sg11:"nStore j t = recv t" by simp
  from h0 have sg15:
   "if \<exists>k<n. nSend k t \<noteq> [] 
    then recv t = nSend (SOME k. k < n \<and> nSend k t \<noteq> []) t
    else recv t = []"
    by (simp add: Broadcast_def)
  show ?thesis
  proof (cases "nReturn k t = []") 
    assume a5: "nReturn k t = []"
    from h2 and h3 and h4 and h5 and h6 and a5 have sg16:"\<not> (\<exists>k<n. nSend k t \<noteq> [])"
      by (simp add: fr_Send8)
    from sg16 and sg15 have sg17:"recv t = []" by simp
    from sg11 and sg17 have sg18:"nStore j t = []" by simp
    from this and a5 show ?thesis by simp
  next
    assume a6:"nReturn k t \<noteq> []"
    from h2 and h3 and h4 and h5 and h6 and a6 have sg19:"\<exists>k<n. nSend k t \<noteq> []"
      by (simp add: fr_Send6)
    from h2 and h3 and h4 and h5 and h6 and a6 have sg20:"nSend k t \<noteq> []"
      by (simp add: fr_Send3)
    from h1 and sg20 and h6 have sg21:"(SOME k. k < n \<and> nSend k t \<noteq> []) = k"
      by (simp add: inf_disj_index)
    from sg15 and sg19 have sg22:"recv t = nSend (SOME k. k < n \<and> nSend k t \<noteq> []) t" 
      by simp
    from sg22 and sg21 have sg23:"recv t = nSend k t" by simp
    from h2 and h3 and h4 and h5 and h6 have sg24:"nSend k t =  nReturn k t"
      by (simp add: fr_Send2)
    from sg11 and sg23 and sg24 show ?thesis by simp
  qed
qed


lemma fr_nStore_nReturn2:
 assumes h1:"Cable n nSend recv"
     and h2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
     and h5:"t mod cycleLength (nC k) mem schedule (nC k)"
     and h6:"k < n"
     and h7:"j < n"
     and h8:"j \<noteq> k"
 shows  "nStore j t = nReturn k t"
proof - 
  from h1 have sg1:"inf_disj n nSend \<longrightarrow> Broadcast n nSend recv"
    by (simp add: Cable_def) 
  from  h3 and h4 and h2 have sg2:"inf_disj n nSend" 
    by (simp add: disjointFrame_L2)
  from sg1 and sg2 have sg3:"Broadcast n nSend recv" by simp
  from sg3 and sg2 and assms show ?thesis  by (simp add: fr_nStore_nReturn1)
qed

lemma fr_nStore_empty1:
 assumes h1:"Cable n nSend recv"
     and h2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
     and h5:"(t mod cycleLength (nC k) mem schedule (nC k))"
     and h6:"k < n"
 shows  "nStore k t = []"
proof - 
  from h2 and h6 have sg1:
    "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
    by auto
   from sg1 obtain activation1 where
     a1:"Scheduler (nC k) activation1" and 
     a2:"BusInterface activation1 (nReturn k) recv (nStore k) (nSend k) (nGet k)"
     by (simp add: FlexRayController_def, auto)
  from a2 have sg2:"Receive recv (nStore k) activation1"
     by (simp add: BusInterface_def)
  from this have sg3:
   "if activation1 t = [] then nStore k t = recv t else nStore k t = []"
    by (simp add: Receive_def)
  from a1 and h5 have sg4:"activation1 t \<noteq> []"
     by (simp add: Scheduler_L3)
 from sg3 and sg4 show ?thesis by simp
qed

lemma fr_nStore_nReturn3:
 assumes "Cable n nSend recv"
     and "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
     and "DisjointSchedules n nC"
     and "IdenticCycleLength n nC"
     and "t mod cycleLength (nC k) mem schedule (nC k)"
     and "k < n"
 shows  "\<forall>j. j < n \<and> j \<noteq> k \<longrightarrow> nStore j t = nReturn k t"
using assms
by (clarify, simp add: fr_nStore_nReturn2)

lemma length_nStore:
 assumes h1:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
     and h2:"DisjointSchedules n nC"
     and h3:"IdenticCycleLength n nC"
     and h4:"inf_disj n nSend"
     and h5:"i < n"  
     and h6:"\<forall> i<n. msg (Suc 0) (nReturn i)"
     and h7:"Broadcast n nSend recv"
 shows "length (nStore i t) \<le> Suc 0"
proof -
  from h7 have sg1:
   "if \<exists>k<n. nSend k t \<noteq> [] 
    then recv t = nSend (SOME k. k < n \<and> nSend k t \<noteq> []) t 
    else recv t = []"
   by (simp add: Broadcast_def)
  show ?thesis 
  proof (cases "\<exists>k<n. nSend k t \<noteq> []")
    assume "\<exists>k<n. nSend k t \<noteq> []"
    from this obtain k where a2:"k<n" and a3:"nSend k t \<noteq> []"  by auto
    from h1 and a2 have 
      "FlexRayController (nReturn k) recv (nC k) (nStore k) (nSend k) (nGet k)"
      by auto
    then obtain activation1 where
      a4:"Scheduler (nC k) activation1" and 
      a5:"BusInterface activation1 (nReturn k) recv (nStore k) (nSend k) (nGet k)" 
      by (simp add: FlexRayController_def, auto)
    from a5 have sg5:"Send (nReturn k) (nSend k) (nGet k) activation1" 
      by (simp add:  BusInterface_def)
    from a5 have sg6:"Receive recv (nStore k) activation1"
      by (simp add: BusInterface_def)
    from sg5 and a3 have sg7:"(activation1 t) \<noteq> []" by (simp add: Send_L1)
    from sg6 have sg8:
     "if activation1 t = [] 
      then nStore k t = recv t else nStore k t = []"
      by (simp add: Receive_def)
    from sg8 and sg7 have sg9:"nStore k t = []" by simp
    from a4 and sg7 have sg10:"(t mod (cycleLength (nC k))) mem (schedule (nC k))"
      by (simp add: Scheduler_L1)
    show ?thesis 
    proof (cases "i = k")
      assume  "i = k"
      from sg9 and this show ?thesis by simp
    next
      assume "i \<noteq> k"
      from h7 and h4 and h1 and h2 and h3 and sg10 and a2 and h5 and this have sg11:
       "nStore i t = nReturn k t"
        by (simp add: fr_nStore_nReturn1)
      from h6 and a2 have sg12:"msg (Suc 0) (nReturn k)" by auto
      from a2 and h6 have sg13:"length (nReturn k t) \<le> Suc 0" 
        by (simp add: msg_def)  
      from sg11 and sg13  show ?thesis by simp
    qed
  next
    assume "\<not> (\<exists>k<n. nSend k t \<noteq> [])"
    from h7 and this have sg14:"recv t = []" by (simp add: Broadcast_nSend_empty1)  
    from h1 and h5 have 
      "FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
      by auto
   then obtain activation2 where
      a11:"Scheduler (nC i) activation2" and 
      a12:"BusInterface activation2 (nReturn i) recv (nStore i) (nSend i) (nGet i)" 
      by (simp add: FlexRayController_def, auto)
    from a12 have "Receive recv (nStore i) activation2"
      by (simp add: BusInterface_def)
    then have sg17:
     "if activation2 t = [] 
      then nStore i t = recv t else nStore i t = []"
      by (simp add: Receive_def)
    show ?thesis
    proof (cases "activation2 t = []")
      assume aa3:"activation2 t = []"
      from sg17 and aa3 and sg14 have "nStore i t = []" by simp
      then show ?thesis by simp
    next
      assume aa4:"activation2 t \<noteq> []"
      from sg17 and aa4 have "nStore i t = []" by simp
      then show ?thesis by simp
    qed
  qed
qed

lemma msg_nStore:
assumes " \<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC"
       and "inf_disj n nSend"
       and "i < n"  
       and "\<forall> i<n. msg (Suc 0) (nReturn i)"
       and "Cable n nSend recv"
shows "msg (Suc 0) (nStore i)"
using assms
  apply (simp (no_asm) add: msg_def, simp add: Cable_def, clarify)
  by (simp add: length_nStore)


subsection \<open>Refinement Properties\<close> 

lemma fr_refinement_FrameTransmission:
assumes "Cable n nSend recv"
       and "\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)" 
       and "DisjointSchedules n nC"
       and "IdenticCycleLength n nC" 
shows "FrameTransmission n nStore nReturn nGet nC"
using assms 
  apply (simp add: FrameTransmission_def Let_def, auto)
  apply (simp add: fr_nGet1)
  by (simp add: fr_nStore_nReturn3)

lemma FlexRayArch_CorrectSheaf:
 assumes "FlexRayArch n nReturn nC nStore nGet"
 shows    "CorrectSheaf n"
using assms by (simp add: FlexRayArch_def)

lemma FlexRayArch_FrameTransmission:
 assumes h1:"FlexRayArch n nReturn nC nStore nGet"
     and h2:"\<forall>i<n. msg (Suc 0) (nReturn i)"
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
 shows      "FrameTransmission n nStore nReturn nGet nC"
proof - 
  from assms obtain nSend recv where
    a1:"Cable n nSend recv" and 
    a2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
    by (simp add: FlexRayArch_def  FlexRayArchitecture_def, auto)
  from a1 and a2 and h3 and h4 show ?thesis 
    by (rule fr_refinement_FrameTransmission)
qed

lemma FlexRayArch_nGet:
 assumes h1:"FlexRayArch n nReturn nC nStore nGet"
     and h2:"\<forall>i<n. msg (Suc 0) (nReturn i)"
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
     and h5:"i < n"
 shows      "msg (Suc 0) (nGet i)"
proof - 
 from assms obtain nSend recv where
    a1:"Cable n nSend recv" and 
    a2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
    by (simp add: FlexRayArch_def  FlexRayArchitecture_def, auto)
  from a2 and h5 show ?thesis by (rule msg_nGet2)
qed

lemma FlexRayArch_nStore:
 assumes h1:"FlexRayArch n nReturn nC nStore nGet"
     and h2:"\<forall>i<n. msg (Suc 0) (nReturn i)"
     and h3:"DisjointSchedules n nC"
     and h4:"IdenticCycleLength n nC"
     and h5:"i < n"
 shows      "msg (Suc 0) (nStore i)"
proof - 
 from assms obtain nSend recv where
    a1:"Cable n nSend recv" and 
    a2:"\<forall>i<n. FlexRayController (nReturn i) recv (nC i) (nStore i) (nSend i) (nGet i)"
    by (simp add: FlexRayArch_def  FlexRayArchitecture_def, auto)
  from h3 and h4 and a2 have sg1:"inf_disj n nSend" by (simp add: disjointFrame_L2)
  from a2 and h3 and h4 and sg1 and h5 and h2 and a1  show ?thesis 
    by (rule msg_nStore)
qed

theorem main_fr_refinement:
 assumes "FlexRayArch n nReturn nC nStore nGet"
 shows     "FlexRay n nReturn nC nStore nGet"
using assms
  by (simp add: FlexRay_def
                FlexRayArch_CorrectSheaf 
                FlexRayArch_FrameTransmission 
                FlexRayArch_nGet 
                FlexRayArch_nStore)
     
end
