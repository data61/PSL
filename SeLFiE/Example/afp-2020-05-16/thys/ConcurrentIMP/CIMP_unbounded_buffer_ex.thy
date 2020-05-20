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

theory CIMP_unbounded_buffer_ex
imports
  CIMP
  "HOL-Library.Prefix_Order"
begin

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

lemma butlastE:
  "\<lbrakk> butlast xs = ys; xs \<noteq> []; \<And>z. xs = ys @ [z] \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (induct xs rule: rev_induct) auto

(*>*)
section\<open>Unbounded buffer example\<close>

text\<open>

\label{sec:unbounded_place_buffer}

This is more literally Kai's example from his notes titled
\emph{Proving an Asynchronous Message Passing Program Correct}, 2011.

\<close>

datatype ex_chname = \<xi>12 | \<xi>23
type_synonym ex_val = nat
type_synonym ex_ls = "ex_val list"
type_synonym ex_ch = "ex_chname \<times> ex_val"
datatype ex_loc = \<pi>4 | \<pi>5 | c1 | r12 | r23 | s23 | s12
datatype ex_proc = p1 | p2 | p3

type_synonym ex_pgm = "(unit, ex_loc, ex_ch, ex_ls) com"
type_synonym ex_pred = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) pred"
type_synonym ex_state = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) global_state"
type_synonym ex_system = "(unit, ex_loc, ex_proc, ex_ch, ex_ls) system"
type_synonym ex_history = "(ex_ch \<times> unit) list"

text\<open>

FIXME a bit fake: the local state for the producer process contains
all values produced.

\<close>

primrec ex_pgms :: "ex_proc \<Rightarrow> ex_pgm" where
  "ex_pgms p1 = LOOP DO \<lbrace>c1\<rbrace> LocalOp (\<lambda>xs. { xs @ [x] |x. True }) ;; \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>last OD"
| "ex_pgms p2 = LOOP DO \<lbrace>r12\<rbrace> \<xi>12\<triangleright>(\<lambda>x xs. xs @ [x])
                           \<squnion> \<lbrace>\<pi>4\<rbrace> IF (\<lambda>s. length s > 0) THEN \<lbrace>s23\<rbrace> Request (\<lambda>s. (\<xi>23, hd s)) (\<lambda>ans s. {tl s}) FI
                          OD"
| "ex_pgms p3 = LOOP DO \<lbrace>r23\<rbrace> \<xi>23\<triangleright>(\<lambda>x xs. xs @ [x]) OD"

abbreviation ex_init :: "(ex_proc \<Rightarrow> ex_ls) \<Rightarrow> bool" where
  "ex_init f \<equiv> \<forall>p. f p = []"

abbreviation ex_system :: "ex_system" where
  "ex_system \<equiv> (ex_pgms, ex_init)"

definition filter_on_channel :: "ex_chname \<Rightarrow> ex_history \<Rightarrow> ex_val list" where
  "filter_on_channel ch \<equiv> map (snd \<circ> fst) \<circ> filter ((=) ch \<circ> fst \<circ> fst)"

lemma filter_on_channel_simps [simp]:
  "filter_on_channel ch [] = []"
  "filter_on_channel ch (xs @ ys) = filter_on_channel ch xs @ filter_on_channel ch ys"
  "filter_on_channel ch (((ch', v), resp) # vals) = (if ch' = ch then [v] else []) @ filter_on_channel ch vals"
by (simp_all add: filter_on_channel_def)

definition Ip1_0 :: ex_pred where
  "Ip1_0 \<equiv> \<lambda>s. at p1 c1 s \<longrightarrow> filter_on_channel \<xi>12 (hist s) = s\<down> p1"
definition Ip1_1 :: ex_pred where
  "Ip1_1 \<equiv> \<lambda>s. at p1 s12 s \<longrightarrow> length (s\<down> p1) > 0 \<and> butlast (s\<down> p1) = filter_on_channel \<xi>12 (hist s)"
definition Ip1_2 :: ex_pred where
  "Ip1_2 \<equiv> \<lambda>s. filter_on_channel \<xi>12 (hist s) \<le> s\<down> p1"

definition Ip2_0 :: ex_pred where
  "Ip2_0 \<equiv> \<lambda>s. filter_on_channel \<xi>12 (hist s) = filter_on_channel \<xi>23 (hist s) @ s\<down> p2"
(* We would get this for free from a proper VCG. *)
definition Ip2_1 :: ex_pred where
  "Ip2_1 \<equiv> \<lambda>s. at p2 s23 s \<longrightarrow> length (s\<down> p2) > 0"

definition Ip3_0 :: ex_pred where
  "Ip3_0 \<equiv> \<lambda>s. s\<down> p3 = filter_on_channel \<xi>23 (hist s)"

definition I_pred :: ex_pred where
  "I_pred \<equiv> pred_conjoin [ Ip1_0, Ip1_1, Ip1_2, Ip2_0, Ip2_1, Ip3_0 ]"

lemmas I_defs = I_pred_def Ip1_0_def Ip1_1_def Ip1_2_def Ip2_0_def Ip2_1_def Ip3_0_def

text\<open>

The local state of @{const "p3"} is some prefix of the local state of
@{const "p1"}.

\<close>

definition Etern_pred :: ex_pred where
  "Etern_pred \<equiv> \<lambda>s. s\<down> p3 \<le> s\<down> p1"

lemma correct_system:
  "I_pred s \<Longrightarrow> Etern_pred s"
(*<*)
by (clarsimp simp: Etern_pred_def I_defs less_eq_list_def prefix_def)

lemma p1_c1[simplified, intro]:
  "ex_pgms, p1, lconst (\<lambda>l. l = s12) \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>c1\<rbrace> LocalOp (\<lambda>xs. { xs @ [x] |x. True })"
apply (rule vcg.intros)
apply (clarsimp simp: I_defs atS_def)
done

lemma p1_s12[intro]:
  "ex_pgms, p1, lconst (\<lambda>l. l = c1) \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s12\<rbrace> \<xi>12\<triangleleft>last"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p', simp_all)
apply (clarsimp simp: I_defs atS_def elim!: butlastE)
done

lemma p2_s23[intro]:
  "ex_pgms, p2, lconst (\<lambda>l. l = r12 \<or> l = \<pi>4) \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>s23\<rbrace> Request (\<lambda>s. (\<xi>23, hd s)) (\<lambda>ans s. {tl s})"
apply (rule vcg.intros)
apply (rename_tac p')
apply (case_tac p', simp_all)
apply (clarsimp simp: I_defs atS_def)
done

lemma p2_pi4[intro]:
  "ex_pgms, p2, lcond (\<lambda>l. l = s23) (\<lambda>l. l = r12 \<or> l = \<pi>4) \<Turnstile> \<lbrace>I_pred\<rbrace> \<lbrace>\<pi>4\<rbrace> IF \<lambda>s. s \<noteq> [] THEN c' FI"
apply (rule vcg.intros)
apply (clarsimp simp: I_defs atS_def split: lcond_splits)
done

(*>*)
text\<open>\<close>

lemma "s \<in> reachable_states ex_system \<Longrightarrow> I_pred (mkP s)"
(*<*)
apply (erule VCG)
 apply (clarsimp dest!: initial_statesD simp: I_defs atS_def)
apply simp
apply (rename_tac p)
apply (case_tac p)
 apply auto
done
(*>*)
(*<*)

end
(*>*)
