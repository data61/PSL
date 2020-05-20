(*  Title:      JinjaThreads/JVM/JVMExceptions.thy
    Author:     Gerwin Klein, Martin Strecker, Andreas Lochbihler
*)

section \<open>Exception handling in the JVM\<close>

theory JVMExceptions
imports
  JVMInstructions
begin

abbreviation Any :: "cname option"
where "Any \<equiv> None"

definition matches_ex_entry :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool"
where
 "matches_ex_entry P C pc xcp \<equiv>
                 let (s, e, C', h, d) = xcp in
                 s \<le> pc \<and> pc < e \<and> (case C' of None \<Rightarrow> True | \<lfloor>C''\<rfloor> \<Rightarrow> P \<turnstile> C \<preceq>\<^sup>* C'')"


primrec
  match_ex_table :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> (pc \<times> nat) option"
where
  "match_ex_table P C pc []     = None"
| "match_ex_table P C pc (e#es) = (if matches_ex_entry P C pc e
                                   then Some (snd(snd(snd e)))
                                   else match_ex_table P C pc es)"

abbreviation ex_table_of :: "'addr jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table"
where "ex_table_of P C M == snd (snd (snd (the (snd (snd (snd(method P C M)))))))"

lemma match_ex_table_SomeD:
  "match_ex_table P C pc xt = Some (pc',d') \<Longrightarrow> 
  \<exists>(f,t,D,h,d) \<in> set xt. matches_ex_entry P C pc (f,t,D,h,d) \<and> h = pc' \<and> d=d'"
  by (induct xt) (auto split: if_split_asm)

end
