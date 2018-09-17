(* Author: Giuliano Losa *)

section {* The SLin Automata specification*}

theory SLin
imports IOA RDR
begin

datatype ('a,'b,'c,'d)SLin_action =
\<comment> \<open>The nat component is the instance number\<close>
  Invoke nat 'b 'c
| Response nat 'b 'd
| Switch nat 'b 'c 'a
| Recover nat
| Linearize nat

datatype SLin_status = Sleep | Pending | Ready | Aborted

record ('a,'b,'c)SLin_state = 
  pending :: "'b \<Rightarrow> 'b \<times> 'c"
  initVals :: "'a set"
  abortVals :: "'a set"
  status :: "'b \<Rightarrow> SLin_status"
  dstate :: 'a
  initialized :: bool

locale SLin = RDR + IOA
begin

definition
  asig :: "nat \<Rightarrow> nat \<Rightarrow> ('a,'b,'c,'d)SLin_action signature" 
  \<comment> \<open>The first instance has number 0\<close>
  where
  "asig i j \<equiv> \<lparr>
    inputs = {act . \<exists> p c iv i' .
      (i \<le> i' \<and> i' < j \<and> act = Invoke i' p c) \<or> (i > 0 \<and> act = Switch i p c iv)},
    outputs = {act . \<exists> p c av i' outp . 
      (i \<le> i' \<and> i' < j \<and> act = Response i' p outp) \<or> act = Switch j p c av},
    internals = {act. \<exists> i' . i \<le> i' \<and> i' < j 
      \<and> (act = Linearize i' \<or> act = Recover i')} \<rparr>"

definition pendingReqs :: "('a,'b,'c)SLin_state \<Rightarrow> ('b\<times>'c) set"
  where
  "pendingReqs s \<equiv> {r . \<exists> p . 
     r = pending s p
     \<and> status s p \<in> {Pending, Aborted}}"

definition Inv :: "'b \<Rightarrow> 'c 
  \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool"
where
  "Inv p c s s' \<equiv> 
    status s p = Ready
    \<and> s' = s\<lparr>pending := (pending s)(p := (p,c)),
        status := (status s)(p := Pending)\<rparr>"

definition pendingSeqs where
  "pendingSeqs s \<equiv> {rs . set rs \<subseteq> pendingReqs s}"
  
definition Lin :: "('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool" 
where
  "Lin s s' \<equiv> \<exists> rs \<in> pendingSeqs s .
      initialized s 
      \<and> (\<forall> av \<in> abortVals s . (dstate s) \<star> rs \<preceq> av) 
      \<and> s' = s\<lparr>dstate := (dstate s) \<star> rs\<rparr>"

definition initSets where
  "initSets s \<equiv> {ivs . ivs \<noteq> {} \<and> ivs \<subseteq> initVals s}"

definition safeInits where
  "safeInits s \<equiv> if initVals s = {} then {}
    else {d . \<exists> ivs \<in> initSets s . \<exists> rs \<in> pendingSeqs s .
      d = \<Sqinter>ivs \<star> rs \<and> (\<forall> av \<in> abortVals s . d \<preceq> av)}"
      
definition initAborts where
  "initAborts s \<equiv> { d .dstate s \<preceq> d
    \<and> ((\<exists> rs \<in> pendingSeqs s . d = dstate s \<star> rs)
      \<or> (\<exists> ivs \<in> initSets s . dstate s \<preceq> \<Sqinter>ivs 
        \<and> (\<exists> rs \<in> pendingSeqs s . d = \<Sqinter>ivs \<star> rs))) }"
definition uninitAborts where
  "uninitAborts s \<equiv> { d .
    \<exists> ivs \<in> initSets s . \<exists> rs \<in> pendingSeqs s . 
      d = \<Sqinter>ivs \<star> rs }"

definition safeAborts::"('a,'b,'c)SLin_state \<Rightarrow> 'a set" where
  "safeAborts s \<equiv> if initialized s then initAborts s
    else uninitAborts s"
  
definition Reco :: "('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool"
where
  "Reco s s' \<equiv>  
      (\<exists> p . status s p \<noteq> Sleep)
      \<and> \<not> initialized s
      \<and> (\<exists> d \<in> safeInits s . 
        s' = s\<lparr>dstate := d, initialized := True\<rparr>)"
      
definition Resp :: "'b \<Rightarrow> 'd \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool"
where
  "Resp p ou s s' \<equiv>  
      status s p = Pending 
      \<and> initialized s
      \<and> contains (dstate s) (pending s p)
      \<and> ou = \<gamma> (dstate s) (pending s p)
      \<and> s' = s \<lparr>status := (status s)(p := Ready)\<rparr>"

definition Init :: "'b \<Rightarrow> 'c \<Rightarrow> 'a 
  \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool"
where
  "Init p c iv s s' \<equiv>
    status s p = Sleep
    \<and> s' = s \<lparr>initVals := {iv} \<union> (initVals s), 
        status := (status s)(p := Pending), 
        pending := (pending s)(p := (p,c))\<rparr>"
      
definition Abort :: "'b \<Rightarrow> 'c \<Rightarrow> 'a 
  \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> ('a,'b,'c)SLin_state \<Rightarrow> bool"
where
  "Abort p c av s s' \<equiv>
     status s p = Pending \<and> pending s p = (p,c)
     \<and> av \<in> safeAborts s
     \<and> s' = s\<lparr>status := (status s)(p := Aborted), 
      abortVals := (abortVals s \<union> {av})\<rparr>"

definition trans where
"trans i j \<equiv> { (s,a,s') . case a of 
  Invoke i' p c \<Rightarrow> i \<le> i' \<and> i < j \<and> Inv p c s s'
| Response i' p ou \<Rightarrow> i \<le> i' \<and> i < j \<and> Resp p ou s s'
| Switch i' p c v \<Rightarrow> (i > 0 \<and> i' = i \<and> Init p c v s s') 
    \<or> (i' = j \<and> Abort p c v s s')
| Linearize i' \<Rightarrow> i' = i \<and> Lin s s'
| Recover i' \<Rightarrow> i > 0 \<and> i' = i \<and> Reco s s' }"

definition start where
  "start i \<equiv> { s . 
    \<forall> p . status s p = (if i > 0 then Sleep else Ready) 
    \<and> dstate s = \<bottom>
    \<and> (if i > 0 then \<not> initialized s else initialized s)
    \<and> initVals s = {}
    \<and> abortVals s = {}}"

definition ioa where
  "ioa i j \<equiv>
     \<lparr>ioa.asig = asig i j ,
      start = start i,
      trans = trans i j\<rparr>"

end

end
