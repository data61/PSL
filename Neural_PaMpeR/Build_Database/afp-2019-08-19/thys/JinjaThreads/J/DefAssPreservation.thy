(*  Title:      JinjaThreads/J/DefAssPreservation.thy
    Author:     Andreas Lochbihler, Tobias Nipkow
*)

section \<open>Preservation of definite assignment\<close>

theory DefAssPreservation
imports
  DefAss
  JWellForm
  SmallStep
begin

text\<open>Preservation of definite assignment more complex and requires a
few lemmas first.\<close>

lemma D_extRetJ [intro!]: "\<D> e A \<Longrightarrow> \<D> (extRet2J e va) A"
by(cases va) simp_all

lemma blocks_defass [iff]: "\<And>A. \<lbrakk> length Vs = length Ts; length vs = length Ts\<rbrakk> \<Longrightarrow>
 \<D> (blocks Vs Ts vs e) A = \<D> e (A \<squnion> \<lfloor>set Vs\<rfloor>)"
(*<*)
apply(induct Vs Ts vs e rule:blocks.induct)
apply(simp_all add:hyperset_defs)
done
(*>*)

context J_heap_base begin

lemma red_lA_incr: "extTA,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> \<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A> e \<sqsubseteq>  \<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A> e'"
  and reds_lA_incr: "extTA,P,t \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> \<lfloor>dom (lcl s)\<rfloor> \<squnion> \<A>s es \<sqsubseteq>  \<lfloor>dom (lcl s')\<rfloor> \<squnion> \<A>s es'"
apply(induct rule:red_reds.inducts)
apply(simp_all del:fun_upd_apply add:hyperset_defs)
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply blast
apply(force split: if_split_asm)
apply blast
apply blast
apply blast
apply blast
apply blast
apply(blast dest: red_lcl_incr)
apply(blast dest: red_lcl_incr)
by blast+

end

text\<open>Now preservation of definite assignment.\<close>

declare hyperUn_comm [simp del]
declare hyperUn_leftComm [simp del]

context J_heap_base begin

lemma assumes wf: "wf_J_prog P"
  shows red_preserves_defass: "extTA,P,t \<turnstile> \<langle>e,s\<rangle> -ta\<rightarrow> \<langle>e',s'\<rangle> \<Longrightarrow> \<D> e \<lfloor>dom (lcl s)\<rfloor> \<Longrightarrow> \<D> e' \<lfloor>dom (lcl s')\<rfloor>"
  and reds_preserves_defass: "extTA,P,t \<turnstile> \<langle>es,s\<rangle> [-ta\<rightarrow>] \<langle>es',s'\<rangle> \<Longrightarrow> \<D>s es \<lfloor>dom (lcl s)\<rfloor> \<Longrightarrow> \<D>s es' \<lfloor>dom (lcl s')\<rfloor>"
proof (induction rule:red_reds.inducts)
  case BinOpRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case AAccRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case AAssRed1 thus ?case by(auto intro: red_lA_incr sqUn_lem D_mono)
next
  case AAssRed2 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case FAssRed1 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CASRed1 thus ?case by(auto intro: red_lA_incr sqUn_lem D_mono)
next
  case CASRed2 thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CallObj thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
next
  case CallParams thus ?case by(auto elim!: Ds_mono[OF red_lA_incr])
next
  case RedCall thus ?case by(auto dest!:sees_wf_mdecl[OF wf] simp:wf_mdecl_def elim!:D_mono')
next
  case BlockRed thus ?case
    by(auto simp:hyperset_defs elim!:D_mono' simp del:fun_upd_apply split: if_split_asm)
next
  case SynchronizedRed1 thus ?case by(auto elim!: D_mono[OF red_lA_incr])
next
  case SeqRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case CondRed thus ?case by (auto elim!: D_mono[OF red_lA_incr])
next
  case TryRed thus ?case
    by (fastforce dest:red_lcl_incr intro:D_mono' simp:hyperset_defs)
next
  case RedWhile thus ?case by(auto simp:hyperset_defs elim!:D_mono')
next
  case ListRed1 thus ?case by (auto elim!: Ds_mono[OF red_lA_incr])
qed (auto simp:hyperset_defs)

end

end
