(*  Title:      HOL/MicroJava/JVM/JVMExceptions.thy
    Author:     Gerwin Klein, Martin Strecker
    Copyright   2001 Technische Universitaet Muenchen
*)

section \<open>Exception handling in the JVM\<close>

theory JVMExceptions imports JVMInstructions "../Common/Exceptions" begin

definition matches_ex_entry :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_entry \<Rightarrow> bool"
where
  "matches_ex_entry P C pc xcp \<equiv>
                 let (s, e, C', h, d) = xcp in
                 s \<le> pc \<and> pc < e \<and> P \<turnstile> C \<preceq>\<^sup>* C'"


primrec match_ex_table :: "'m prog \<Rightarrow> cname \<Rightarrow> pc \<Rightarrow> ex_table \<Rightarrow> (pc \<times> nat) option"
where
  "match_ex_table P C pc []     = None"
| "match_ex_table P C pc (e#es) = (if matches_ex_entry P C pc e
                                   then Some (snd(snd(snd e)))
                                   else match_ex_table P C pc es)"

abbreviation
  ex_table_of :: "jvm_prog \<Rightarrow> cname \<Rightarrow> mname \<Rightarrow> ex_table" where
  "ex_table_of P C M == snd (snd (snd (snd (snd (snd(method P C M))))))"


primrec find_handler :: "jvm_prog \<Rightarrow> addr \<Rightarrow> heap \<Rightarrow> frame list \<Rightarrow> jvm_state"
where
  "find_handler P a h [] = (Some a, h, [])"
| "find_handler P a h (fr#frs) = 
       (let (stk,loc,C,M,pc) = fr in
        case match_ex_table P (cname_of h a) pc (ex_table_of P C M) of
          None \<Rightarrow> find_handler P a h frs
        | Some pc_d \<Rightarrow> (None, h, (Addr a # drop (size stk - snd pc_d) stk, loc, C, M, fst pc_d)#frs))"

end
