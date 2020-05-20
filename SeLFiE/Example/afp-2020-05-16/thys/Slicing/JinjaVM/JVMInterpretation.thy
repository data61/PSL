theory JVMInterpretation imports JVMCFG "../Basic/CFGExit" begin

section \<open>Instatiation of the \<open>CFG\<close> locale\<close>

abbreviation sourcenode :: "j_edge \<Rightarrow> j_node"
  where "sourcenode e \<equiv> fst e"

abbreviation targetnode :: "j_edge \<Rightarrow> j_node"
  where "targetnode e \<equiv> snd(snd e)"

abbreviation kind :: "j_edge \<Rightarrow> state edge_kind"
  where "kind e \<equiv> fst(snd e)"

text \<open>
The following predicates define the aforementioned well-formedness requirements
for nodes. Later, \<open>valid_callstack\<close> will be implied by Jinja's state conformance.
\<close>

fun valid_callstack :: "jvmprog \<Rightarrow> callstack \<Rightarrow> bool"
where
  "valid_callstack prog [] = True"
| "valid_callstack (P, C0, Main) [(C, M, pc)] \<longleftrightarrow> 
    C = C0 \<and> M = Main \<and>
    (P\<^bsub>\<Phi>\<^esub>) C M ! pc \<noteq> None \<and>
    (\<exists>T Ts mxs mxl is xt. (P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T=(mxs, mxl, is, xt) in C \<and> pc < length is)"
| "valid_callstack (P, C0, Main) ((C, M, pc)#(C', M', pc')#cs) \<longleftrightarrow>
    instrs_of (P\<^bsub>wf\<^esub>) C' M' ! pc' =
      Invoke M (locLength P C M 0 - Suc (fst(snd(snd(snd(snd(method (P\<^bsub>wf\<^esub>) C M)))))) ) \<and>
    (P\<^bsub>\<Phi>\<^esub>) C M ! pc \<noteq> None \<and>
    (\<exists>T Ts mxs mxl is xt. (P\<^bsub>wf\<^esub>) \<turnstile> C sees M:Ts\<rightarrow>T=(mxs, mxl, is, xt) in C \<and> pc < length is) \<and>
    valid_callstack (P, C0, Main) ((C', M', pc')#cs)"

fun valid_node :: "jvmprog \<Rightarrow> j_node \<Rightarrow> bool"
where
  "valid_node prog (_Entry_) = True"
(* | "valid_node prog (_Exit_) = True" *)
| "valid_node prog (_ cs,None _) \<longleftrightarrow> valid_callstack prog cs"
| "valid_node prog (_ cs,\<lfloor>(cs', xf)\<rfloor> _) \<longleftrightarrow>
    valid_callstack prog cs \<and> valid_callstack prog cs' \<and>
    (\<exists>Q. prog \<turnstile> (_ cs,None _) -(Q)\<^sub>\<surd>\<rightarrow> (_ cs,\<lfloor>(cs', xf)\<rfloor> _)) \<and>
    (\<exists>f. prog \<turnstile> (_ cs,\<lfloor>(cs', xf)\<rfloor> _) -\<Up>f\<rightarrow> (_ cs',None _))"

fun valid_edge :: "jvmprog \<Rightarrow> j_edge \<Rightarrow> bool"
where
  "valid_edge prog a \<longleftrightarrow>
    (prog \<turnstile> (sourcenode a) -(kind a)\<rightarrow> (targetnode a))
    \<and> (valid_node prog (sourcenode a))
    \<and> (valid_node prog (targetnode a))"

interpretation JVM_CFG_Interpret:
  CFG "sourcenode" "targetnode" "kind" "valid_edge prog" "Entry"
  for prog
proof (unfold_locales)
  fix a
  assume ve: "valid_edge prog a"
    and trg: "targetnode a = (_Entry_)"
  obtain n et n'
    where "a = (n,et,n')"
    by (cases a) fastforce
  with ve trg 
    have "prog \<turnstile> n -et\<rightarrow> (_Entry_)" by simp
  thus False by fastforce
next
  fix a a'
  assume valid: "valid_edge prog a"
    and valid': "valid_edge prog a'"
    and sourceeq: "sourcenode a = sourcenode a'"
    and targeteq: "targetnode a = targetnode a'"
  obtain n1 et n2
    where a:"a = (n1, et, n2)"
    by (cases a) fastforce
  obtain n1' et' n2'
    where a':"a' = (n1', et', n2')"
    by (cases a') fastforce
  from a valid a' valid' sourceeq targeteq
  have "et = et'"
    by (fastforce elim: JVMCFG_edge_det)
  with a a' sourceeq targeteq
  show "a = a'"
    by simp
qed


interpretation JVM_CFGExit_Interpret:
  CFGExit "sourcenode" "targetnode" "kind" "valid_edge prog" "Entry" "(_Exit_)"
  for prog
proof(unfold_locales)
  fix a
  assume ve: "valid_edge prog a"
    and src: "sourcenode a = (_Exit_)"
  obtain n et n'
    where "a = (n,et,n')"
    by (cases a) fastforce
  with ve src
    have "prog \<turnstile> (_Exit_) -et\<rightarrow> n'" by simp
  thus False by fastforce
next
  have "prog \<turnstile> (_Entry_) -(\<lambda>s. False)\<^sub>\<surd>\<rightarrow> (_Exit_)" 
    by (rule JCFG_EntryExit)
  thus "\<exists>a. valid_edge prog a \<and> sourcenode a = (_Entry_) \<and>
            targetnode a = (_Exit_) \<and> kind a = (\<lambda>s. False)\<^sub>\<surd>"
    by fastforce
qed

end

