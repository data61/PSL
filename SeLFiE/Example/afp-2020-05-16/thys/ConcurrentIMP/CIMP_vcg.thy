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

theory CIMP_vcg
imports
  CIMP_lang
begin

(*>*)
subsection\<open>Simple-minded Hoare Logic/VCG for CIMP\<close>

text\<open>

\label{sec:cimp-vcg}

We do not develop a proper Hoare logic or full VCG for CIMP: this
machinery merely packages up the subgoals that arise from induction
over the reachable states (\S\ref{sec:cimp-invariants}). This is
somewhat in the spirit of @{cite [cite_macro=citet] "Ridge:2009"}.

Note that this approach is not compositional: it consults the original
system to find matching communicating pairs, and \<open>aft\<close>
tracks the labels of possible successor statements. More serious Hoare
logics are provided by @{cite [cite_macro=citet]
"DBLP:journals/acta/Lamport80" and "DBLP:journals/toplas/LamportS84"
and "CousotCousot89-IC"}.

Intuitively we need to discharge a proof obligation for either @{const
"Request"}s or @{const "Response"}s but not both. Here we choose to
focus on @{const "Request"}s as we expect to have more local
information available about these.

\<close>

inductive
  vcg :: "('answer, 'location, 'proc, 'question, 'state) programs
        \<Rightarrow> 'proc
        \<Rightarrow> ('answer, 'location, 'question, 'state) loc_comp
        \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred
        \<Rightarrow> ('answer, 'location, 'question, 'state) com
        \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred
        \<Rightarrow> bool" ("_, _, _ \<Turnstile>/ \<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")
where
  Request: "\<lbrakk> \<And>aft' action' s ps' p's' l' \<beta> s' p'.
                 \<lbrakk> pre s; (\<lbrace>l'\<rbrace> Response action', aft') \<in> fragments (pgms p') \<langle>False\<rangle>; p \<noteq> p';
                   ps' \<in> val \<beta> (LST s p); (p's', \<beta>) \<in> action' (action (LST s p)) (LST s p');
                   at p l s; at p' l' s;
                   AT s' = (AT s)(p := aft (\<lbrace>l\<rbrace> Request action val) (LST s p),
                                  p' := aft' (\<lbrace>l'\<rbrace> Response action') (LST s p'));
                   LST s' = (LST s)(p := ps', p' := p's');
                   hist s' = hist s @ [(action (LST s p), \<beta>)]
                 \<rbrakk> \<Longrightarrow> post s'
            \<rbrakk> \<Longrightarrow> pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Request action val \<lbrace>post\<rbrace>"
| LocalOp: "\<lbrakk> \<And>s ps' s'. \<lbrakk> pre s; ps' \<in> f (LST s p);
                           at p l s;
                           AT s' = (AT s)(p := aft (\<lbrace>l\<rbrace> LocalOp f) (LST s p));
                           LST s' = (LST s)(p := ps');
                           hist s' = hist s
                         \<rbrakk> \<Longrightarrow> post s'
            \<rbrakk> \<Longrightarrow> pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> LocalOp f \<lbrace>post\<rbrace>"
| Cond1: "\<lbrakk> \<And>s s'. \<lbrakk> pre s;
                     at p l s;
                     AT s' = (AT s)(p := aft (\<lbrace>l\<rbrace> IF b THEN t FI) (LST s p));
                     LST s' = LST s;
                     hist s' = hist s
                   \<rbrakk> \<Longrightarrow> post s'
       \<rbrakk> \<Longrightarrow> pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t FI \<lbrace>post\<rbrace>"
| Cond2: "\<lbrakk> \<And>s s'. \<lbrakk> pre s;
                     at p l s;
                     AT s' = (AT s)(p := aft (\<lbrace>l\<rbrace> IF b THEN t ELSE e FI) (LST s p));
                     LST s' = LST s;
                     hist s' = hist s
                   \<rbrakk> \<Longrightarrow> post s'
       \<rbrakk> \<Longrightarrow> pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t ELSE e FI \<lbrace>post\<rbrace>"
| While: "\<lbrakk> \<And>s s'. \<lbrakk> pre s;
                     at p l s;
                     AT s' = (AT s)(p := aft (\<lbrace>l\<rbrace> WHILE b DO c OD) (LST s p));
                     LST s' = LST s;
                     hist s' = hist s
                   \<rbrakk> \<Longrightarrow> post s'
          \<rbrakk> \<Longrightarrow> pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> WHILE b DO c OD \<lbrace>post\<rbrace>"
\<comment> \<open>There are no proof obligations for the following commands.\<close>
| Response: "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Response action \<lbrace>post\<rbrace>"
| Seq: "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> c1 ;; c2 \<lbrace>post\<rbrace>"
| Loop: "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> LOOP DO c OD \<lbrace>post\<rbrace>"
| Choose: "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> c1 \<squnion> c2 \<lbrace>post\<rbrace>"

text\<open>

We abbreviate invariance with one-sided validity syntax.

\<close>

abbreviation valid_inv ("_, _, _ \<Turnstile>/ \<lbrace>_\<rbrace>/ _") where
  "pgms, p, aft \<Turnstile> \<lbrace>I\<rbrace> c \<equiv> pgms, p, aft \<Turnstile> \<lbrace>I\<rbrace> c \<lbrace>I\<rbrace>"
(*<*)

inductive_cases vcg_inv:
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Request action val \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> LocalOp f \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t FI \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> IF b THEN t ELSE e FI \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> LOOP DO c OD \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> WHILE b DO c OD \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> \<lbrace>l\<rbrace> Response action \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> c1 ;; c2 \<lbrace>post\<rbrace>"
  "pgms, p, aft \<Turnstile> \<lbrace>pre\<rbrace> c1 \<squnion> c2 \<lbrace>post\<rbrace>"

lemma vcg_precond_cong:
  "P = P' \<Longrightarrow> (pgms, p, aft \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>) \<longleftrightarrow> (pgms, p, aft \<Turnstile> \<lbrace>P'\<rbrace> c \<lbrace>Q\<rbrace>)"
by simp

lemma vcg_postcond_cong:
  "Q = Q' \<Longrightarrow> (pgms, p, aft \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>) \<longleftrightarrow> (pgms, p, aft \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q'\<rbrace>)"
by simp

(*>*)
text\<open>

We tweak @{const "fragments"} by omitting @{const "Response"}s,
yielding fewer obligations.

\<close>

fun
  vcg_fragments' :: "('answer, 'location, 'question, 'state) com
               \<Rightarrow> ('location \<Rightarrow> bool)
               \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                 \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "vcg_fragments' (\<lbrace>l\<rbrace> Response action) ls = {}"
| "vcg_fragments' (\<lbrace>l\<rbrace> IF b THEN c FI) ls
       = vcg_fragments' c ls
       \<union> { (\<lbrace>l\<rbrace> IF b THEN c' FI, lcond (atC c) ls) |c'. True }"
| "vcg_fragments' (\<lbrace>l\<rbrace> IF b THEN c1 ELSE c2 FI) ls
       = vcg_fragments' c2 ls \<union> vcg_fragments' c1 ls
       \<union> { (\<lbrace>l\<rbrace> IF b THEN c1' ELSE c2' FI, lcond (atC c1) (atC c2)) |c1' c2'. True }"
| "vcg_fragments' (LOOP DO c OD) ls = vcg_fragments' c (atC c)"
| "vcg_fragments' (\<lbrace>l'\<rbrace> WHILE b DO c OD) ls
       = vcg_fragments' c (\<lambda>l. l = l') \<union> { (\<lbrace>l'\<rbrace> WHILE b DO c' OD, lcond (atC c) ls) |c'. True }"
| "vcg_fragments' (c1 ;; c2) ls = vcg_fragments' c2 ls \<union> vcg_fragments' c1 (atC c2)"
| "vcg_fragments' (c1 \<squnion> c2) ls = vcg_fragments' c1 ls \<union> vcg_fragments' c2 ls"
| "vcg_fragments' c ls = {(c, lconst ls)}"

abbreviation
  vcg_fragments :: "('answer, 'location, 'question, 'state) com
                  \<Rightarrow> ( ('answer, 'location, 'question, 'state) com
                    \<times> ('answer, 'location, 'question, 'state) loc_comp ) set"
where
  "vcg_fragments c \<equiv> vcg_fragments' c \<langle>False\<rangle>"
(*<*)

lemma vcg_fragments'_inc:
  "\<lbrakk> (c', lp) \<in> fragments c ls; \<And>l action. c' \<noteq> \<lbrace>l\<rbrace> Response action \<rbrakk> \<Longrightarrow> (c', lp) \<in> vcg_fragments' c ls"
by (induct c arbitrary: ls) (auto split: if_splits)

lemma VCG_step:
  assumes V: "\<And>p. \<forall>(c, afts) \<in> vcg_fragments (fst sys p). ((fst sys), p, afts \<Turnstile> \<lbrace>pre\<rbrace> c \<lbrace>post\<rbrace>)"
  assumes S: "(s, h) s\<Rightarrow> (s', h')"
  assumes R: "(s, h) \<in> reachable_states sys"
  assumes P: "pre (mkP (s, h))"
  shows "post (mkP (s', h'))"
using S
proof cases
  case (LocalStep p ps') with P show ?thesis
    apply -
    apply (erule decompose_small_step[OF _ R])
    apply (elim basic_com.cases, simp_all)
    apply (fastforce dest!: V[rule_format] vcg_fragments'_inc
                     elim!: small_step_inv vcg_inv
                      simp: fun_eq_iff LST_def AT_def mkP_def split_def)+
    done
next
  case (CommunicationStep p1 \<alpha> \<beta> ls1' p2 ls2) with P show ?thesis
    apply -
    apply (erule decompose_small_step[OF _ R])
    apply (erule decompose_small_step[OF _ R])
    apply (elim basic_com.cases, simp_all)
    apply (drule vcg_fragments'_inc, simp)
    apply (drule V[rule_format])
    apply clarsimp
    apply (erule vcg_inv)
    apply (elim small_step_inv)
    apply (fastforce simp add: fun_eq_iff LST_def AT_def mkP_def split_def)
    done
qed

(*>*)
text\<open>

The user sees the conclusion of \<open>V\<close> for each element of \<open>vcg_fragments\<close>.

\<close>

lemma VCG:
  assumes R: "s \<in> reachable_states sys"
  assumes I: "\<forall>s \<in> initial_states sys. I (mkP (s, []))"
  assumes V: "\<And>p. \<forall>(c, afts) \<in> vcg_fragments (fst sys p). ((fst sys), p, afts \<Turnstile> \<lbrace>I\<rbrace> c)"
  shows "I (mkP s)"
(*<*)
proof -
  have "I (mkP (s', h'))" if B: "s0 \<in> initial_states sys" and S: "(s0, []) s\<Rightarrow>\<^sup>* (s', h')" for s0 s' h'
  using S
  proof(induct rule: rtrancl_induct2)
    case refl with B show ?case by (rule I[rule_format])
  next
    case (step s' h' s'' h'') with B V show ?case
      by - (erule (1) VCG_step; auto simp: reachable_states_def)
  qed
  with I R show ?thesis by (cases s) (clarsimp simp: reachable_states_def)
qed
(*>*)

subsubsection\<open>VCG rules\<close>

text\<open>

We can develop some (but not all) of the familiar Hoare rules; see
@{cite [cite_macro=citet] "DBLP:journals/acta/Lamport80"} and the
seL4/l4.verified lemma buckets for inspiration. We avoid many of the
issues Lamport mentions as we only treat basic (atomic) commands.

\<close>

context
  fixes pgms :: "('answer, 'location, 'proc, 'question, 'state) programs"
  fixes p :: "'proc"
  fixes afts :: "('answer, 'location, 'question, 'state) loc_comp"
begin

abbreviation
  valid_syn :: "('answer, 'location, 'proc, 'question, 'state) pred
             \<Rightarrow> ('answer, 'location, 'question, 'state) com
             \<Rightarrow> ('answer, 'location, 'proc, 'question, 'state) pred \<Rightarrow> bool" where
  "valid_syn P c Q \<equiv> pgms, p, afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
notation valid_syn ("\<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")

abbreviation
  valid_inv_syn :: "('answer, 'location, 'proc, 'question, 'state) pred
                  \<Rightarrow> ('answer, 'location, 'question, 'state) com \<Rightarrow> bool" where
  "valid_inv_syn P c \<equiv> \<lbrace>P\<rbrace> c \<lbrace>P\<rbrace>"
notation valid_inv_syn ("\<lbrace>_\<rbrace>/ _")

lemma vcg_True:
  "\<lbrace>P\<rbrace> c \<lbrace>\<langle>True\<rangle>\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_conj:
  "\<lbrakk> \<lbrace>I\<rbrace> c \<lbrace>Q\<rbrace>; \<lbrace>I\<rbrace> c \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>I\<rbrace> c \<lbrace>Q \<^bold>\<and> R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_pre_imp:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s; \<lbrace>Q\<rbrace> c \<lbrace>R\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> c \<lbrace>R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemmas vcg_pre = vcg_pre_imp[rotated]

lemma vcg_post_imp:
  "\<lbrakk> \<And>s. Q s \<Longrightarrow> R s; \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<rbrakk> \<Longrightarrow> \<lbrace>P\<rbrace> c \<lbrace>R\<rbrace>"
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_prop[intro]:
  "\<lbrace>\<langle>P\<rangle>\<rbrace> c"
by (cases c) (fastforce intro: vcg.intros)+

lemma vcg_drop_imp:
  assumes "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> c \<lbrace>R \<^bold>\<longrightarrow> Q\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_conj_lift:
  assumes x: "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<and> P'\<rbrace> c \<lbrace>Q \<^bold>\<and> Q'\<rbrace>"
apply (rule vcg_conj)
 apply (rule vcg_pre[OF x], simp)
apply (rule vcg_pre[OF y], simp)
done

lemma vcg_disj_lift:
  assumes x: "\<lbrace>P\<rbrace>  c \<lbrace>Q\<rbrace>"
  assumes y: "\<lbrace>P'\<rbrace> c \<lbrace>Q'\<rbrace>"
  shows      "\<lbrace>P \<^bold>\<or> P'\<rbrace> c \<lbrace>Q \<^bold>\<or> Q'\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_imp_lift:
  assumes "\<lbrace>P'\<rbrace> c \<lbrace>\<^bold>\<not> P\<rbrace>"
  assumes "\<lbrace>Q'\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P' \<^bold>\<or> Q'\<rbrace> c \<lbrace>P \<^bold>\<longrightarrow> Q\<rbrace>"
by (simp only: imp_conv_disj vcg_disj_lift[OF assms])

lemma vcg_ex_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> c \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<exists>x. P x s\<rbrace> c \<lbrace>\<lambda>s. \<exists>x. Q x s\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_all_lift:
  assumes "\<And>x. \<lbrace>P x\<rbrace> c \<lbrace>Q x\<rbrace>"
  shows "\<lbrace>\<lambda>s. \<forall>x. P x s\<rbrace> c \<lbrace>\<lambda>s. \<forall>x. Q x s\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_name_pre_state:
  assumes "\<And>s. P s \<Longrightarrow> \<lbrace>(=) s\<rbrace> c \<lbrace>Q\<rbrace>"
  shows "\<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
using assms
by (cases c) (fastforce elim!: vcg_inv intro: vcg.intros)+

lemma vcg_lift_comp:
  assumes f: "\<And>P. \<lbrace>\<lambda>s. P (f s :: 'a :: type)\<rbrace> c"
  assumes P: "\<And>x. \<lbrace>Q x\<rbrace> c \<lbrace>P x\<rbrace>"
  shows "\<lbrace>\<lambda>s. Q (f s) s\<rbrace> c \<lbrace>\<lambda>s. P (f s) s\<rbrace>"
  apply (rule vcg_name_pre_state)
  apply (rename_tac s)
  apply (rule vcg_pre)
   apply (rule vcg_post_imp[rotated])
    apply (rule vcg_conj_lift)
     apply (rule_tac x="f s" in P)
    apply (rule_tac P="\<lambda>fs. fs = f s" in f)
   apply simp
  apply simp
  done

(* **************************************** *)

subsubsection\<open>Cheap non-interference rules\<close>

text\<open>

These rules magically construct VCG lifting rules from the easier to
prove \<open>eq_imp\<close> facts. We don't actually use these in the GC,
but we do derive @{const "fun_upd"} equations using the same
mechanism. Thanks to Thomas Sewell for the requisite syntax magic.

As these \<open>eq_imp\<close> facts do not usefully compose, we make the
definition asymmetric (i.e., \<open>g\<close> does not get a bundle of
parameters).

\<close>

definition eq_imp :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('b \<Rightarrow> 'e) \<Rightarrow> bool" where
  "eq_imp f g \<equiv> (\<forall>s s'. (\<forall>x. f x s = f x s') \<longrightarrow> (g s = g s'))"

lemma eq_impD:
  "\<lbrakk> eq_imp f g; \<forall>x. f x s = f x s' \<rbrakk> \<Longrightarrow> g s = g s'"
by (simp add: eq_imp_def)

lemma eq_imp_vcg:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x P. \<lbrace>P \<circ> (f x)\<rbrace> c"
  shows "\<lbrace>P \<circ> g\<rbrace> c"
  apply (rule vcg_name_pre_state)
  apply (rename_tac s)
  apply (rule vcg_pre)
   apply (rule vcg_post_imp[rotated])
    apply (rule vcg_all_lift[where 'a='a])
    apply (rule_tac x=x and P="\<lambda>fs. fs = f x s" in f[rule_format])
   apply simp
   apply (frule eq_impD[where f=f, OF g])
   apply simp
  apply simp
  done

lemma eq_imp_vcg_LST:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x P. \<lbrace>P \<circ> (f x) \<circ> LST\<rbrace> c"
  shows "\<lbrace>P \<circ> g \<circ> LST\<rbrace> c"
  apply (rule vcg_name_pre_state)
  apply (rename_tac s)
  apply (rule vcg_pre)
   apply (rule vcg_post_imp[rotated])
    apply (rule vcg_all_lift[where 'a='a])
    apply (rule_tac x=x and P="\<lambda>fs. fs = f x s\<down>" in f[rule_format])
   apply simp
   apply (frule eq_impD[where f=f, OF g])
   apply simp
  apply simp
  done

lemma eq_imp_fun_upd:
  assumes g: "eq_imp f g"
  assumes f: "\<forall>x. f x (s(fld := val)) = f x s"
  shows "g (s(fld := val)) = g s"
apply (rule eq_impD[OF g])
apply (rule f)
done

lemma curry_forall_eq:
  "(\<forall>f. P f) = (\<forall>f. P (case_prod f))"
  apply safe
   apply simp_all
  apply (rename_tac f)
  apply (drule_tac x="\<lambda>x y. f (x, y)" in spec)
  apply simp
  done

lemma pres_tuple_vcg:
  "(\<forall>P. \<lbrace>P \<circ> (\<lambda>s. (f s, g s))\<rbrace> c)
    \<longleftrightarrow> ((\<forall>P. \<lbrace>P \<circ> f\<rbrace> c) \<and> (\<forall>P. \<lbrace>P \<circ> g\<rbrace> c))"
  apply (simp add: curry_forall_eq o_def)
  apply safe
    apply fast
   apply fast
  apply (rename_tac P)
  apply (rule_tac f="f" and P="\<lambda>fs s. P fs (g s)" in vcg_lift_comp, simp, simp)
  done

lemma pres_tuple_vcg_LST:
  "(\<forall>P. \<lbrace>P \<circ> (\<lambda>s. (f s, g s)) \<circ> LST\<rbrace> c)
    \<longleftrightarrow> ((\<forall>P. \<lbrace>P \<circ> f \<circ> LST\<rbrace> c) \<and> (\<forall>P. \<lbrace>P \<circ> g \<circ> LST\<rbrace> c))"
  apply (simp add: curry_forall_eq o_def)
  apply safe
    apply fast
   apply fast
  apply (rename_tac P)
  apply (rule_tac f="\<lambda>s. f s\<down>" and P="\<lambda>fs s. P fs (g s)" for g in vcg_lift_comp, simp, simp)
  done

lemmas conj_explode = conj_imp_eq_imp_imp

end
(*<*)

end
(*>*)
