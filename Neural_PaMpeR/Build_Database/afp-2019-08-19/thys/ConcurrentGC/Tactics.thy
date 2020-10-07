(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Tactics
imports
  Model
  "HOL-Library.Sublist"
begin

(*>*)
section\<open>Invariants and Proofs \label{sec:gc-invs}\<close>

subsection\<open>Constructors for sets of locations.\<close>

abbreviation prefixed :: "location \<Rightarrow> location set" where
  "prefixed p \<equiv> { l . prefix p l }"

abbreviation suffixed :: "location \<Rightarrow> location set" where
  "suffixed p \<equiv> { l . suffix p l }"

subsection\<open>Hoare triples\<close>

text\<open>

Specialise CIMP's pre/post validity to our system.

\<close>

definition
  valid_proc :: "('field, 'mut, 'ref) gc_pred \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>")
where
  "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace> \<equiv> \<forall>(c, afts) \<in> vcg_fragments (gc_pgms p). (gc_pgms, p, afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>)"

abbreviation
  valid_proc_inv_syn :: "('field, 'mut, 'ref) gc_pred \<Rightarrow> 'mut process_name \<Rightarrow> bool" ("\<lbrace>_\<rbrace> _" [100,0] 100)
where
  "\<lbrace>P\<rbrace> p \<equiv> \<lbrace>P\<rbrace> p \<lbrace>P\<rbrace>"
(*<*)

lemma valid_pre:
  assumes "\<lbrace>Q\<rbrace> p \<lbrace>R\<rbrace>"
  assumes "\<And>s. P s \<Longrightarrow> Q s"
  shows "\<lbrace>P\<rbrace> p \<lbrace>R\<rbrace>"
using assms
apply (clarsimp simp: valid_proc_def)
apply (drule (1) bspec)
apply (auto elim: vcg_pre)
done

lemma valid_conj_lift:
  assumes x: "\<lbrace>P\<rbrace> p \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> p \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<and> P'\<rbrace> p \<lbrace>Q \<^bold>\<and> Q'\<rbrace>"
apply (clarsimp simp: valid_proc_def)
apply (rule vcg_conj)
 apply (rule vcg_pre[OF spec[OF spec[OF x[unfolded Ball_def valid_proc_def split_paired_All]], simplified, rule_format]], simp, simp)
apply (rule vcg_pre[OF spec[OF spec[OF y[unfolded Ball_def valid_proc_def split_paired_All]], simplified, rule_format]], simp, simp)
done

lemma valid_all_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> p \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> p \<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace>"
using assms by (fastforce simp: valid_proc_def intro: vcg_all_lift)

(*>*)
text\<open>

As we elide formal proofs in this document, we also omit our
specialised proof tactics. These support essentially traditional local
correctness and non-interference proofs. Their most interesting aspect
is the use of Isabelle's parallelism to greatly reduce system latency.

\<close>
(*<*)

subsection\<open>Tactics\<close>

named_theorems nie "Non-interference elimination rules"

text\<open>

Collect the component definitions. Inline everything.

\<close>

lemmas gc_defs =
  (* gc.com_def *) gc.handshake_done_def gc.handshake_init_def gc.handshake_noop_def gc.handshake_get_roots_def gc.handshake_get_work_def
  mark_object_fn_def

lemmas mut_defs =
  (* mut.com_def *) mut_m.handshake_def mut_m.store_def
  mark_object_fn_def

lemmas sys_defs =
  (* sys.com_def *) sys.alloc_def sys.free_def sys.mem_TSO_def sys.handshake_def

lemmas gc_all_defs[com] =
  gc.com_def[simplified gc_defs append.simps if_True if_False]
  mut_m.com_def[simplified mut_defs append.simps if_True if_False]
  sys.com_def[simplified sys_defs append.simps if_True if_False]

(* FIXME not automation friendly. *)
lemma atS_dests:
  "\<lbrakk> atS p ls s; atS p ls' s \<rbrakk> \<Longrightarrow> atS p (ls \<union> ls') s"
  "\<lbrakk> \<not>atS p ls s; \<not>atS p ls' s \<rbrakk> \<Longrightarrow> \<not>atS p (ls \<union> ls') s"
  "\<lbrakk> \<not>atS p ls s; atS p ls' s \<rbrakk> \<Longrightarrow> atS p (ls' - ls) s"
  "\<lbrakk> \<not>atS p ls s; at p l s \<rbrakk> \<Longrightarrow> atS p ({l} - ls) s"
by (auto simp: atS_def)

(* FIXME these leave \<not>at ... assumptions when P is easy to contradict. *)
lemma thin_locs:
  "\<lbrakk> at p l' s \<longrightarrow> P; at p l s; l' \<noteq> l \<or> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk> atS p ls s \<longrightarrow> P; at p l s; l \<notin> ls \<or> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
(*  "\<lbrakk> at p l' s \<longrightarrow> P; atS p ls s; ... FIXME strategy: reduce atS to at and use the first of thin_locs. *)
(*  "\<lbrakk> atS p ls' s \<longrightarrow> P; atS p ls s; \<not>atS p (ls' \<inter> ls) s \<or> P \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q" *)
by (auto simp: atS_def)

text\<open>

The following is unfortunately overspecialised to the GC. One might
hope for general tactics that work on all CIMP programs.

The system responds to all requests. The schematic variable is
instantiated with the semantics of the responses. Thanks to Thomas
Sewell for the hackery.

\<close>

schematic_goal system_responds_actionE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_pgms p) \<langle>False\<rangle>; v \<in> action x s;
     \<lbrakk> p = sys; ?P \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
apply (cases p)
apply (simp_all add: gc_all_defs)
apply atomize

apply (drule_tac P="x \<or> y" and Q="v \<in> action p k" for x y p k in conjI, assumption)
apply (thin_tac "v \<in> action p k" for p k)
apply (simp only: conj_disj_distribR conj_assoc mem_Collect_eq cong: conj_cong)

apply (erule mp)
apply (thin_tac "p = sys")
apply (assumption)
done

lemma triv: "P \<Longrightarrow> P"
  by simp

schematic_goal system_responds_action_caseE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_pgms p) \<langle>False\<rangle>; v \<in> action (pname, req) s;
     \<lbrakk> p = sys; case_request_op ?P1 ?P2 ?P3 ?P4 ?P5 ?P6 ?P7 ?P8 ?P9 ?P10 ?P11 ?P12 ?P13 req \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (erule(1) system_responds_actionE)
  apply (cases req, simp_all only: request_op.simps prod.inject simp_thms fst_conv snd_conv)
  apply (drule meta_mp[OF _ TrueI], erule meta_mp, erule_tac P="A \<and> B" for A B in triv)+
  done

schematic_goal system_responds_action_specE:
  "\<lbrakk> (\<lbrace>l\<rbrace> Response action, afts) \<in> fragments (gc_pgms p) \<langle>False\<rangle>; v \<in> action x s;
     \<lbrakk> p = sys; case_request_op ?P1 ?P2 ?P3 ?P4 ?P5 ?P6 ?P7 ?P8 ?P9 ?P10 ?P11 ?P12 ?P13 (snd x) \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (erule system_responds_action_caseE[where pname="fst x" and req="snd x"])
   apply simp
  apply assumption
  done

(* Simplification rules for locations. *)
lemmas loc_simps =
  bex_simps
  append.simps list.simps rev.simps (* evaluate string equality *)
  char.inject cong_exp_iff_simps (* evaluate character equality *)
  prefix_code suffix_to_prefix
  mem_Collect_eq Un_iff UNION_eq Compl_iff insertI1 insertI2 singleton_iff Diff_iff UNIV_I
  if_True if_False
  fun_upd_same fun_upd_other process_name.simps
  refl simp_thms
  atS_simps

lemmas vcg_fragments'_simps =
  valid_proc_def gc_pgms.simps vcg_fragments'.simps atC.simps
  ball_Un bool_simps if_False if_True

(* equations for deriving useful things from eq_imp facts. *)
lemmas eq_imp_simps =
  eq_imp_def
  all_conj_distrib
  split_paired_All split_def fst_conv snd_conv prod_eq_iff
  conj_explode
  simp_thms

(* Tweak the default simpset:
  - "not in dom" as a premise negates the goal
  - we always want to execute suffix
  - we may as well simplify under our non-recursive datatypes.
*)
declare dom_def[simp]
declare suffix_to_prefix[simp]

declare gc_phase.case_cong[cong]
declare mem_write_action.case_cong[cong]
declare process_name.case_cong[cong]
declare handshake_phase.case_cong[cong]

ML \<open>

(* Thanks BNF people. *)
fun ss_only thms ctxt = clear_simpset (put_simpset HOL_basic_ss ctxt) addsimps thms;

(* Thanks BNF people. Actually use HOL_ss rather than HOL_basic_ss *)
fun HOL_ss_only thms ctxt = clear_simpset (put_simpset HOL_ss ctxt) addsimps thms;

fun vcg_clarsimp_tac ctxt =
        simp_tac (ss_only (@{thms vcg_fragments'_simps} @ Named_Theorems.get ctxt @{named_theorems com}) ctxt)
  THEN' SELECT_GOAL (safe_tac ctxt)

val _ =
  Theory.setup (Method.setup @{binding vcg_clarsimp}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_clarsimp_tac))
    "unfold com defs, execute vcg_fragments' and split goals")

fun vcg_sem_tac ctxt =
        Tactic.match_tac ctxt @{thms vcg.intros}
  THEN' (TRY o (Tactic.ematch_tac ctxt @{thms system_responds_action_specE} THEN' assume_tac ctxt))
  THEN' Rule_Insts.thin_tac ctxt "hist s = h" [(@{binding s}, NONE, NoSyn), (@{binding h}, NONE, NoSyn)] (* FIXME discard history: we don't use it here *)
  THEN' clarsimp_tac ctxt

val _ =
  Theory.setup (Method.setup @{binding vcg_sem}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_sem_tac))
    "turn VCG goal into semantics and clarsimp")

fun vcg_jackhammer_gen_tac terminal_tac ctxt =
  SELECT_GOAL (
    HEADGOAL (vcg_clarsimp_tac ctxt)
  THEN
    PARALLEL_ALLGOALS (
                 vcg_sem_tac ctxt
    THEN_ALL_NEW (full_simp_tac (Splitter.add_split @{thm lcond_split_asm} (ctxt addsimps Named_Theorems.get ctxt @{named_theorems inv})))
    THEN_ALL_NEW ( (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms conjE}))
             THEN' (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms thin_locs} THEN' REPEAT1 o assume_tac ctxt))
             THEN' asm_full_simp_tac (ss_only (@{thms loc_simps} @ Named_Theorems.get ctxt @{named_theorems loc}) ctxt)
             THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Rule_Insts.thin_tac ctxt "True" [])) (* FIXME weird, must be a standard way to do this. Leaving them in can cause simp to diverge ?? *)
             THEN_ALL_NEW clarsimp_tac (ctxt addsimps (Named_Theorems.get ctxt @{named_theorems loc} @ @{thms atS_simps})) (* FIXME smelly *)
             THEN_ALL_NEW Rule_Insts.thin_tac ctxt "AT _ = _" [] (* FIXME discard \<open>AT s = s'(funupd)\<close> fact *)
             THEN_ALL_NEW TRY o terminal_tac ctxt)))

val _ =
  Theory.setup (Method.setup @{binding vcg_jackhammer}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_jackhammer_gen_tac (fn _ => SELECT_GOAL all_tac)))
    "VCG supertactic, no terminal method")

val _ =
  Theory.setup (Method.setup @{binding vcg_jackhammer_ff}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_jackhammer_gen_tac fast_force_tac))
    "VCG supertactic, fastforce the survivors")

fun vcg_ni_tac ctxt =
  SELECT_GOAL (
    HEADGOAL (TRY o vcg_clarsimp_tac ctxt)
  THEN
    PARALLEL_ALLGOALS (
                   vcg_sem_tac ctxt
             THEN' (TRY o SELECT_GOAL (Local_Defs.unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems inv})))
             THEN' (TRY o REPEAT_ALL_NEW (Tactic.match_tac ctxt @{thms conjI})) (* expose the location predicates, do not split the consequents *)
      THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.match_tac ctxt @{thms impI}))
                       (* Preserve the label sets in atS but normalise the label in at; turn s' into s *)
      THEN_ALL_NEW asm_full_simp_tac ctxt (* FIXME diverges on some invariants *)
      THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms conjE}))
                       (* The effect of vcg_pre: should be cheap *)
      THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms thin_locs} THEN' REPEAT1 o assume_tac ctxt))
      THEN_ALL_NEW asm_full_simp_tac (ss_only (@{thms loc_simps} @ Named_Theorems.get ctxt @{named_theorems loc}) ctxt)
      THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Rule_Insts.thin_tac ctxt "True" [])) (* FIXME weird, must be a standard way to do this. Leaving them in can cause simp to diverge ?? *)
(*      THEN_ALL_NEW Rule_Insts.thin_tac ctxt "AT _ = _" [] (* FIXME discard \<open>AT s = s'(funupd)\<close> fact *) doesn't work when processes communicate! see gc_sweep_loop_invL *)
      THEN_ALL_NEW clarsimp_tac ctxt))

fun vcg_nihe_tac ctxt =
  SELECT_GOAL (
    HEADGOAL (vcg_clarsimp_tac ctxt)
  THEN
    PARALLEL_ALLGOALS (
                     (vcg_sem_tac ctxt
        THEN_ALL_NEW (Tactic.ematch_tac ctxt (Named_Theorems.get ctxt @{named_theorems nie})
        THEN_ALL_NEW clarsimp_tac ctxt
        THEN_ALL_NEW SELECT_GOAL no_tac))
      ORELSE' SELECT_GOAL all_tac)) (* FIXME perhaps replace with vcg_ni? but less diagnosable then *)

val _ =
  Theory.setup (Method.setup @{binding vcg_ni}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_ni_tac))
    "VCG non-interference supertactic, no terminal method")

val _ =
  Theory.setup (Method.setup @{binding vcg_nihe}
    (Method.sections clasimp_modifiers >> K (SIMPLE_METHOD' o vcg_nihe_tac))
    "cheap VCG non-interference tactic: apply non-interference Hoare and elimination rules, leaving remaining goals as Hoare triples")
\<close>

(*>*)
(*<*)

end
(*>*)
