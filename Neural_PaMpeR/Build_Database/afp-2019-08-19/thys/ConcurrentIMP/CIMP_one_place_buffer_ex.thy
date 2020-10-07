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

theory CIMP_one_place_buffer_ex
imports
  CIMP
begin

(*>*)
section\<open>One-place buffer example\<close>

text\<open>

\label{sec:one_place_buffer}

To demonstrate the CIMP reasoning infrastructure, we treat the trivial
one-place buffer example of @{cite [cite_macro=citet]
\<open>\S3.3\<close> "DBLP:journals/toplas/LamportS84"}. Note that the
semantics for our language is different to @{cite
[cite_macro=citeauthor] "DBLP:journals/toplas/LamportS84"}'s, who
treated a historical variant of CSP (i.e., not the one in @{cite
"Hoare:1985"}).

We introduce some syntax for fixed-topology (static channel-based)
scenarios.

\<close>

abbreviation
  Receive :: "'location \<Rightarrow> 'channel \<Rightarrow> ('val \<Rightarrow> 'state \<Rightarrow> 'state)
             \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleright>_")
where
  "\<lbrace>l\<rbrace> ch\<triangleright>f \<equiv> \<lbrace>l\<rbrace> Response (\<lambda>quest s. if fst quest = ch then {(f (snd quest) s, ())} else {})"

abbreviation
  Send :: "'location \<Rightarrow> 'channel \<Rightarrow> ('state \<Rightarrow> 'val)
          \<Rightarrow> (unit, 'location, 'channel \<times> 'val, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleleft>_")
where
  "\<lbrace>l\<rbrace> ch\<triangleleft>f \<equiv> \<lbrace>l\<rbrace> Request (\<lambda>s. (ch, f s)) (\<lambda>ans s. {s})"

text\<open>

We further specialise these for our particular example.

\<close>

abbreviation
  Receive' :: "'location \<Rightarrow> 'channel \<Rightarrow> (unit, 'location, 'channel \<times> 'state, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleright>")
where
  "\<lbrace>l\<rbrace> ch\<triangleright> \<equiv> \<lbrace>l\<rbrace> ch\<triangleright>(\<lambda>v _. v)"

abbreviation
  Send' :: "'location \<Rightarrow> 'channel \<Rightarrow> (unit, 'location, 'channel \<times> 'state, 'state) com" ("\<lbrace>_\<rbrace>/ _\<triangleleft>")
where
 "\<lbrace>l\<rbrace> ch\<triangleleft> \<equiv> \<lbrace>l\<rbrace> ch\<triangleleft>id"

text\<open>

These definitions largely follow @{cite [cite_macro=citet]
"DBLP:journals/toplas/LamportS84"}. We have three processes
communicating over two channels. We enumerate program locations.

\<close>

datatype ex_chname = \<xi>12 | \<xi>23
type_synonym ex_val = nat
type_synonym ex_ch = "ex_chname \<times> ex_val"
datatype ex_loc = r12 | r23 | s23 | s12
datatype ex_proc = p1 | p2 | p3

type_synonym ex_pgm = "(unit, ex_loc, ex_ch, ex_val) com"
type_synonym ex_pred = "(unit, ex_loc, ex_proc, ex_ch, ex_val) pred"
type_synonym ex_state = "(unit, ex_loc, ex_proc, ex_ch, ex_val) global_state"
type_synonym ex_system = "(unit, ex_loc, ex_proc, ex_ch, ex_val) system"
type_synonym ex_history = "(ex_ch \<times> unit) list"

primrec
  ex_pgms :: "ex_proc \<Rightarrow> ex_pgm"
where
  "ex_pgms p1 = \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>"
| "ex_pgms p2 = LOOP DO \<lbrace>r12\<rbrace> \<xi>12\<triangleright>;; \<lbrace>s23\<rbrace> \<xi>23\<triangleleft> OD"
| "ex_pgms p3 = \<lbrace>r23\<rbrace> \<xi>23\<triangleright>"

text\<open>

Each process starts with an arbitrary initial local state.

\<close>

abbreviation ex_init :: "(ex_proc \<Rightarrow> ex_val) \<Rightarrow> bool" where
  "ex_init \<equiv> \<langle>True\<rangle>"

abbreviation ex_system :: "ex_system" where
  "ex_system \<equiv> (ex_pgms, ex_init)"

text\<open>

The following adapts Kai Engelhardt's, from his notes titled
\emph{Proving an Asynchronous Message Passing Program Correct},
2011. The history variable tracks the causality of the system, which I
feel is missing in Lamport's treatment. We tack on Lamport's invariant
so we can establish \<open>Etern_pred\<close>.

\<close>

abbreviation
  filter_on_channel :: "ex_chname \<Rightarrow> ex_history \<Rightarrow> ex_val list"
where
  "filter_on_channel ch \<equiv> map (snd \<circ> fst) \<circ> filter ((=) ch \<circ> fst \<circ> fst)"

definition Ip1_0 :: ex_pred where
  "Ip1_0 \<equiv> at p1 s12 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>12 (hist s) = [])"
definition Ip1_1 :: ex_pred where
  "Ip1_1 \<equiv> terminated p1 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>12 (hist s) = [LST s p1])"

definition Ip2_0 :: ex_pred where
  "Ip2_0 \<equiv> at p2 r12 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>12 (hist s) = filter_on_channel \<xi>23 (hist s))"
definition Ip2_1 :: ex_pred where
  "Ip2_1 \<equiv> at p2 s23 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>12 (hist s) = filter_on_channel \<xi>23 (hist s) @ [LST s p2]
                           \<and> LST s p1 = LST s p2)"

definition Ip3_0 :: ex_pred where
  "Ip3_0 \<equiv> at p3 r23 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>23 (hist s) = [])"
definition Ip3_1 :: ex_pred where
  "Ip3_1 \<equiv> terminated p3 \<^bold>\<longrightarrow> (\<lambda>s. filter_on_channel \<xi>23 (hist s) = [LST s p2]
                                \<and> LST s p1 = LST s p3)"

definition I_pred :: ex_pred where
  "I_pred \<equiv> pred_conjoin [ Ip1_0, Ip1_1, Ip2_0, Ip2_1, Ip3_0, Ip3_1 ]"

lemmas I_defs = Ip1_0_def Ip1_1_def Ip2_0_def Ip2_1_def Ip3_0_def Ip3_1_def

text\<open>

If process three terminates, then it has process one's value. This is
stronger than @{cite [cite_macro=citeauthor]
"DBLP:journals/toplas/LamportS84"}'s as we don't ask that the first
process has also terminated.

\<close>

definition Etern_pred :: ex_pred where
  "Etern_pred \<equiv> terminated p3 \<^bold>\<longrightarrow> (\<lambda>s. LST s p1 = LST s p3)"

text\<open>

Proofs from here down.

\<close>

lemma correct_system:
  "I_pred sh \<Longrightarrow> Etern_pred sh"
apply (clarsimp simp: Etern_pred_def I_pred_def I_defs)
done

lemma p1: "ex_pgms, p1, lconst \<langle>False\<rangle> \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>\<lambda>s. s"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p')
  apply (auto simp: I_pred_def I_defs atS_def)
done

lemma p2_1: "ex_pgms, p2, lconst (\<lambda>l. l = r12) \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s23\<rbrace> \<xi>23\<triangleleft>\<lambda>s. s"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p')
  apply (auto simp: I_pred_def I_defs atS_def)
done

lemma "(s, h) \<in> reachable_states ex_system \<Longrightarrow> I_pred (mkP (s, h))"
apply (erule VCG)
 apply (clarsimp simp: I_pred_def I_defs atS_def)
apply simp
apply (rename_tac p)
apply (case_tac p)
  apply auto (* vcg_clarsimp_tac *)
  apply (auto simp: p1 p2_1)
done

text\<open>\<close>
(*<*)

end
(*>*)
