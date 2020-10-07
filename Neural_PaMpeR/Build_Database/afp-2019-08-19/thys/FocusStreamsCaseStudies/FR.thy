(*<*)
(*
   Title: FR.thy  (FlexRay: Specification)
   Author:    Maria Spichkova <maria.spichkova at rmit.edu.au>, 2013
*) 
(*>*)
section \<open>FlexRay: Specification\<close>

theory  FR 
imports FR_types
begin

subsection \<open>Auxiliary predicates\<close>

\<comment> \<open>The predicate DisjointSchedules is true  for sheaf of channels of type Config,\<close>
\<comment> \<open>if all bus configurations have disjoint scheduling tables.\<close>
definition
  DisjointSchedules :: "nat \<Rightarrow> nConfig \<Rightarrow> bool" 
where
 "DisjointSchedules n nC
  \<equiv>
  \<forall> i j. i < n \<and> j < n \<and> i \<noteq> j \<longrightarrow> 
  disjoint (schedule (nC i))  (schedule (nC j))" 

\<comment> \<open>The predicate IdenticCycleLength is true  for sheaf of channels of type Config,\<close> 
\<comment> \<open>if all bus configurations have the equal length of the communication round.\<close>
definition
   IdenticCycleLength :: "nat \<Rightarrow> nConfig \<Rightarrow> bool"
where
  "IdenticCycleLength n nC
   \<equiv>
   \<forall> i j. i < n \<and> j < n \<longrightarrow> 
   cycleLength (nC i) = cycleLength (nC j)"
   
\<comment> \<open>The predicate FrameTransmission defines the correct message transmission:\<close>
\<comment> \<open>if the time t is equal modulo the length of the cycle (Flexray communication round)\<close>
\<comment> \<open>to the element of the scheduler table of the node k, then this and only this node\<close>
\<comment> \<open>can send a data atn the $t$th time interval.\<close>
definition
   FrameTransmission :: 
     "nat \<Rightarrow> 'a nFrame \<Rightarrow> 'a nFrame \<Rightarrow> nNat \<Rightarrow> nConfig \<Rightarrow> bool"
where
  "FrameTransmission n nStore nReturn nGet nC
   \<equiv>
   \<forall> (t::nat) (k::nat). k < n \<longrightarrow>
   ( let s = t mod (cycleLength (nC k))
     in 
     ( s mem (schedule (nC k))
       \<longrightarrow>
       (nGet k t) = [s] \<and>  
       (\<forall> j. j < n \<and> j \<noteq> k \<longrightarrow> 
            ((nStore j) t) =  ((nReturn k) t)) ))" 

\<comment> \<open>The   predicate Broadcast describes properties of FlexRay broadcast.\<close>
definition
   Broadcast :: 
     "nat \<Rightarrow> 'a nFrame \<Rightarrow> 'a Frame istream \<Rightarrow> bool"
where
  "Broadcast n nSend recv
   \<equiv> 
   \<forall> (t::nat). 
    ( if \<exists> k. k < n \<and> ((nSend k) t) \<noteq> []
      then (recv t) = ((nSend (SOME k. k < n \<and> ((nSend k) t) \<noteq> [])) t)
      else (recv t) = [] )"  
      
\<comment> \<open>The predicate Receive defines the  relations on the streams  to represent\<close> 
\<comment> \<open>data receive by FlexRay controller.\<close>
definition
  Receive :: 
  "'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow> nat istream \<Rightarrow> bool"     
where
  "Receive recv store activation
   \<equiv>
   \<forall> (t::nat).
    ( if  (activation t) = []
      then (store t) = (recv t)
      else (store t) = [])"

\<comment> \<open>The predicate Send defines the  relations on the streams  to represent\<close>
\<comment> \<open>sending data  by FlexRay controller.\<close>
definition
  Send :: 
  "'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow> nat istream \<Rightarrow> nat istream \<Rightarrow> bool"
where
  "Send return send get activation
   \<equiv>
   \<forall> (t::nat). 
   ( if  (activation t) = []
     then (get t) = [] \<and> (send t) = []
     else (get t) = (activation t) \<and> (send t) = (return t)  )"   
    
 
subsection \<open>Specifications of the FlexRay components\<close>

definition
   FlexRay :: 
  "nat \<Rightarrow> 'a nFrame \<Rightarrow> nConfig \<Rightarrow> 'a nFrame \<Rightarrow> nNat \<Rightarrow> bool"
where
  "FlexRay n nReturn nC nStore nGet
   \<equiv> 
   (CorrectSheaf n)  \<and>  
   ((\<forall> (i::nat). i < n \<longrightarrow> (msg 1 (nReturn i))) \<and> 
    (DisjointSchedules n nC) \<and> (IdenticCycleLength n nC) 
   \<longrightarrow>
    (FrameTransmission n nStore nReturn nGet nC) \<and> 
    (\<forall> (i::nat). i < n \<longrightarrow> (msg 1 (nGet i)) \<and> (msg 1 (nStore i))) )"

definition 
   Cable :: "nat \<Rightarrow> 'a nFrame \<Rightarrow> 'a Frame istream \<Rightarrow> bool" 
where
  "Cable n nSend recv 
   \<equiv>
   (CorrectSheaf n) 
    \<and>  
   ((inf_disj n nSend) \<longrightarrow> (Broadcast n nSend recv))"

definition
   Scheduler :: "Config \<Rightarrow> nat istream \<Rightarrow> bool"
where
  "Scheduler c activation
   \<equiv> 
   \<forall> (t::nat).
   ( let s = (t mod (cycleLength c))
      in
       ( if  (s mem (schedule c))
         then (activation t) = [s]
         else (activation t) = []) )"
         
definition
  BusInterface :: 
    "nat istream \<Rightarrow> 'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow> 
     'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow> nat istream \<Rightarrow> bool"
where
  "BusInterface activation return recv  store send get
   \<equiv>
   (Receive recv store activation) \<and>
   (Send return send get activation)"


definition
   FlexRayController :: 
     "'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow>  Config \<Rightarrow>
      'a Frame istream \<Rightarrow> 'a Frame istream \<Rightarrow> nat istream \<Rightarrow> bool"
where
  "FlexRayController return recv c store send get
   \<equiv>
  (\<exists> activation. 
     (Scheduler c activation) \<and>
     (BusInterface activation return recv store send get))"
 

definition
  FlexRayArchitecture :: 
   "nat \<Rightarrow> 'a nFrame \<Rightarrow> nConfig \<Rightarrow> 'a nFrame \<Rightarrow> nNat \<Rightarrow> bool"   
where
  "FlexRayArchitecture n nReturn nC nStore nGet
   \<equiv>
   (CorrectSheaf n) \<and>
   (\<exists> nSend recv.
     (Cable n nSend recv) \<and> 
     (\<forall> (i::nat). i < n \<longrightarrow>  
         FlexRayController (nReturn i) recv (nC i) 
                           (nStore i) (nSend i) (nGet i)))"  
   
definition
  FlexRayArch :: 
   "nat \<Rightarrow> 'a nFrame \<Rightarrow> nConfig \<Rightarrow> 'a nFrame \<Rightarrow> nNat \<Rightarrow> bool"   
where
  "FlexRayArch n nReturn nC nStore nGet
   \<equiv>
   (CorrectSheaf n)  \<and> 
   ((\<forall> (i::nat). i < n \<longrightarrow> msg 1 (nReturn i)) \<and> 
    (DisjointSchedules n nC) \<and> (IdenticCycleLength n nC)    
    \<longrightarrow>
    (FlexRayArchitecture n nReturn nC nStore nGet))"    

end
