(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Refinement.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Refinement.thy 132859 2016-12-21 09:09:39Z eth.jlallemand $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Infrastructure for specifications, invariants, and refinements.

  Copyright (c) 2009-2016 Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Models, Invariants and Refinements\<close>

theory Refinement imports Infra 
begin

(******************************************************************************)
subsection \<open>Specifications, reachability, and behaviours.\<close>
(******************************************************************************)

text \<open>Transition systems are multi-pointed graphs.\<close>

record 's TS = 
  init :: "'s set"
  trans :: "('s \<times> 's) set"


text \<open>The inductive set of reachable states.\<close>

inductive_set 
  reach ::  "('s, 'a) TS_scheme \<Rightarrow> 's set" 
  for T :: "('s, 'a) TS_scheme"
where
  r_init [intro]:  "s \<in> init T \<Longrightarrow> s \<in> reach T"
| r_trans [intro]: "\<lbrakk> (s, t) \<in> trans T; s \<in> reach T \<rbrakk> \<Longrightarrow> t \<in> reach T"



subsubsection \<open>Finite behaviours\<close>
(******************************************************************************)

text \<open>Note that behaviours grow at the head of the list, i.e., the initial 
state is at the end.\<close>

inductive_set 
  beh :: "('s, 'a) TS_scheme \<Rightarrow> ('s list) set"
  for T :: "('s, 'a) TS_scheme" 
where
  b_empty [iff]: "[] \<in> beh T"
| b_init [intro]: "s \<in> init T \<Longrightarrow> [s] \<in> beh T"
| b_trans [intro]: "\<lbrakk> s # b \<in> beh T; (s, t) \<in> trans T \<rbrakk> \<Longrightarrow> t # s # b \<in> beh T"

inductive_cases beh_non_empty: "s # b \<in> beh T"


text \<open>Behaviours are prefix closed.\<close>

lemma beh_immediate_prefix_closed:
  "s # b \<in> beh T \<Longrightarrow> b \<in> beh T"
by (erule beh_non_empty, auto) 

lemma beh_prefix_closed:
  "c @ b \<in> beh T \<Longrightarrow> b \<in> beh T"
by (induct c, auto dest!: beh_immediate_prefix_closed)


text \<open>States in behaviours are exactly reachable.\<close>

lemma beh_in_reach [rule_format]:
  "b \<in> beh T \<Longrightarrow> (\<forall>s \<in> set b. s \<in> reach T)"
by (erule beh.induct) (auto)
  
lemma reach_in_beh:
  assumes "s \<in> reach T" shows "\<exists>b \<in> beh T. s \<in> set b" 
using assms
proof (induction s rule: reach.induct)
  case (r_init s) 
  hence "s \<in> set [s]" and "[s] \<in> beh T" by auto
  thus ?case by fastforce
next 
  case (r_trans s t)
  then obtain b where "b \<in> beh T" and "s \<in> set b" by blast
  from \<open>s \<in> set b\<close> obtain b1 b2 where "b = b2 @ s # b1" by (blast dest: split_list)
  with \<open>b \<in> beh T\<close> have "s # b1 \<in> beh T" by (blast intro: beh_prefix_closed)
  with \<open>(s, t) \<in> trans T\<close> have "t # s # b1 \<in> beh T" by blast
  thus ?case by force
qed

lemma reach_equiv_beh_states: "reach T = \<Union> (set`(beh T))"
by (auto intro!: reach_in_beh beh_in_reach)


subsubsection \<open>Specifications, observability, and implementation\<close> 
(******************************************************************************)

text \<open>Specifications add an observer function to transition systems.\<close>

record ('s, 'o) spec = "'s TS" +
  obs :: "'s \<Rightarrow> 'o" 

lemma beh_obs_upd [simp]: "beh (S(| obs := x |)) = beh S"
by (safe) (erule beh.induct, auto)+

lemma reach_obs_upd [simp]: "reach (S(| obs := x |)) = reach S"
by (safe) (erule reach.induct, auto)+

text \<open>Observable behaviour and reachability.\<close>

definition 
  obeh :: "('s, 'o) spec \<Rightarrow> ('o list) set" where
  "obeh S \<equiv> (map (obs S))`(beh S)"

definition 
  oreach :: "('s, 'o) spec \<Rightarrow> 'o set" where 
  "oreach S \<equiv> (obs S)`(reach S)"

lemma oreach_equiv_obeh_states:
  "oreach S = \<Union> (set`(obeh S))"
by (auto simp add: reach_equiv_beh_states oreach_def obeh_def)


lemma obeh_pi_translation:
  "(map pi)`(obeh S) = obeh (S(| obs := pi o (obs S) |))"
by (auto simp add: obeh_def image_comp)

lemma oreach_pi_translation:
  "pi`(oreach S) = oreach (S(| obs := pi o (obs S) |))"
by (auto simp add: oreach_def)


text \<open>A predicate $P$ on the states of a specification is \emph{observable} 
if it cannot distinguish between states yielding the same observation. 
Equivalently, $P$ is observable if it is the inverse image under the 
observation function of a predicate on observations.\<close>

definition 
  observable :: "['s \<Rightarrow> 'o, 's set] \<Rightarrow> bool"
where
  "observable ob P \<equiv> \<forall>s s'. ob s = ob s' \<longrightarrow> s' \<in> P \<longrightarrow> s \<in> P"

definition 
  observable2 :: "['s \<Rightarrow> 'o, 's set] \<Rightarrow> bool"
where
  "observable2 ob P \<equiv> \<exists>Q. P = ob-`Q"

definition 
  observable3 :: "['s \<Rightarrow> 'o, 's set] \<Rightarrow> bool"
where
  "observable3 ob P \<equiv> ob-`ob`P \<subseteq> P"    \<comment> \<open>other direction holds trivially\<close>

lemma observableE [elim]:
  "\<lbrakk>observable ob P; ob s = ob s'; s' \<in> P\<rbrakk> \<Longrightarrow> s \<in> P"
by (unfold observable_def) (fast)

lemma observable2_equiv_observable: "observable2 ob P = observable ob P"
by (unfold observable_def observable2_def) (auto)

lemma observable3_equiv_observable2: "observable3 ob P = observable2 ob P"
by (unfold observable3_def observable2_def) (auto)

lemma observable_id [simp]: "observable id P" 
by (simp add: observable_def)

text \<open>The set extension of a function @{term "ob"} is the left adjoint of 
a Galois connection on the powerset lattices over domain and range of @{term "ob"} 
where the right adjoint is the inverse image function.\<close>

lemma image_vimage_adjoints: "(ob`P \<subseteq> Q) = (P \<subseteq> ob-`Q)"
by auto

declare image_vimage_subset [simp, intro]
declare vimage_image_subset [simp, intro]

text \<open>Similar but "reversed" (wrt to adjointness) relationships only hold under
additional conditions.\<close>

lemma image_r_vimage_l: "\<lbrakk> Q \<subseteq> ob`P; observable ob P \<rbrakk> \<Longrightarrow> ob-`Q \<subseteq> P"
by (auto)

lemma vimage_l_image_r: "\<lbrakk> ob-`Q \<subseteq> P; Q \<subseteq> range ob \<rbrakk> \<Longrightarrow> Q \<subseteq> ob`P"
by (drule image_mono [where f=ob], auto)


text \<open>Internal and external invariants\<close>

lemma external_from_internal_invariant: 
  "\<lbrakk> reach S \<subseteq> P; (obs S)`P \<subseteq> Q \<rbrakk>  
  \<Longrightarrow> oreach S \<subseteq> Q"
by (auto simp add: oreach_def)

lemma external_from_internal_invariant_vimage: 
  "\<lbrakk> reach S \<subseteq> P; P \<subseteq> (obs S)-`Q \<rbrakk>
  \<Longrightarrow> oreach S \<subseteq> Q"
by (erule external_from_internal_invariant) (auto)


lemma external_to_internal_invariant_vimage: 
  "\<lbrakk> oreach S \<subseteq> Q; (obs S)-`Q \<subseteq> P \<rbrakk>
  \<Longrightarrow> reach S \<subseteq> P"
by (auto simp add: oreach_def)

lemma external_to_internal_invariant:
  "\<lbrakk> oreach S \<subseteq> Q; Q \<subseteq> (obs S)`P; observable (obs S) P \<rbrakk> 
  \<Longrightarrow> reach S \<subseteq> P"
by (erule external_to_internal_invariant_vimage) (auto)


lemma external_equiv_internal_invariant_vimage: 
  "\<lbrakk> P = (obs S)-`Q \<rbrakk> 
  \<Longrightarrow> (oreach S \<subseteq> Q) = (reach S \<subseteq> P)"
by (fast intro: external_from_internal_invariant_vimage
                external_to_internal_invariant_vimage 
         del: subsetI)

lemma external_equiv_internal_invariant: 
  "\<lbrakk> (obs S)`P = Q; observable (obs S) P \<rbrakk> 
  \<Longrightarrow> (oreach S \<subseteq> Q) = (reach S \<subseteq> P)"
by (rule external_equiv_internal_invariant_vimage) (auto)


text \<open>Our notion of implementation is inclusion of observable behaviours.\<close>

definition 
  implements :: "['p \<Rightarrow> 'o, ('s, 'o) spec, ('t, 'p) spec] \<Rightarrow> bool" where
  "implements pi Sa Sc \<equiv> (map pi)`(obeh Sc) \<subseteq> obeh Sa"


text \<open>Reflexivity and transitivity\<close>

lemma implements_refl: "implements id S S"
by (auto simp add: implements_def)

lemma implements_trans:
  "\<lbrakk> implements pi1 S1 S2; implements pi2 S2 S3 \<rbrakk> 
  \<Longrightarrow> implements (pi1 o pi2) S1 S3"
by (fastforce simp add: implements_def image_subset_iff)


text \<open>Preservation of external invariants\<close>

lemma implements_oreach:
  "implements pi Sa Sc \<Longrightarrow> pi`(oreach Sc) \<subseteq> oreach Sa"
by (auto simp add: implements_def oreach_equiv_obeh_states dest!: subsetD)

lemma external_invariant_preservation:
  "\<lbrakk> oreach Sa \<subseteq> Q; implements pi Sa Sc \<rbrakk>
  \<Longrightarrow> pi`(oreach Sc) \<subseteq> Q"
by (rule subset_trans [OF implements_oreach]) (auto)

lemma external_invariant_translation:
  "\<lbrakk> oreach Sa \<subseteq> Q; pi-`Q \<subseteq> P; implements pi Sa Sc \<rbrakk>
  \<Longrightarrow> oreach Sc \<subseteq> P"
apply (rule subset_trans [OF vimage_image_subset, of pi])
apply (rule subset_trans [where B="pi-`Q"])
apply (intro vimage_mono external_invariant_preservation, auto)
done


text \<open>Preservation of internal invariants\<close>

lemma internal_invariant_translation:
  "\<lbrakk> reach Sa \<subseteq> Pa; Pa \<subseteq> obs Sa -` Qa; pi -` Qa \<subseteq> Q; obs S -` Q \<subseteq> P;
     implements pi Sa S \<rbrakk>
  \<Longrightarrow> reach S \<subseteq> P"
by (rule external_from_internal_invariant_vimage [
      THEN external_invariant_translation, 
      THEN external_to_internal_invariant_vimage])


(******************************************************************************)
subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>First we define Hoare triples over transition relations and then
we derive proof rules to establish invariants.\<close>


subsubsection \<open>Hoare triples\<close>
(******************************************************************************)

definition 
  PO_hoare :: "['s set, ('s \<times> 's) set, 's set] \<Rightarrow> bool"
     ("(3{_} _ {> _})" [0, 0, 0] 90)
where
  "{pre} R {> post} \<equiv> R``pre \<subseteq> post"

lemmas PO_hoare_defs = PO_hoare_def Image_def

lemma "{P} R {> Q} = (\<forall>s t. s \<in> P \<longrightarrow> (s, t) \<in> R \<longrightarrow> t \<in> Q)"
by (auto simp add: PO_hoare_defs)


text \<open>Some essential facts about Hoare triples.\<close>

lemma hoare_conseq_left [intro]:
  "\<lbrakk> {P'} R {> Q}; P \<subseteq> P' \<rbrakk>
  \<Longrightarrow> {P} R {> Q}"
by (auto simp add: PO_hoare_defs)

lemma hoare_conseq_right:
  "\<lbrakk> {P} R {> Q'}; Q' \<subseteq> Q \<rbrakk>
  \<Longrightarrow> {P} R {> Q}"
by (auto simp add: PO_hoare_defs)

lemma hoare_false_left [simp]:
  "{{}} R {> Q}"
by (auto simp add: PO_hoare_defs)

lemma hoare_true_right [simp]:
  "{P} R {> UNIV}"
by (auto simp add: PO_hoare_defs)

lemma hoare_conj_right [intro!]:
  "\<lbrakk> {P} R {> Q1}; {P} R {> Q2} \<rbrakk>
  \<Longrightarrow> {P} R {> Q1 \<inter> Q2}"
by (auto simp add: PO_hoare_defs)


text \<open>Special transition relations.\<close>

lemma hoare_stop [simp, intro!]:
  "{P} {} {> Q}"
by (auto simp add: PO_hoare_defs)

lemma hoare_skip [simp, intro!]: 
  "P \<subseteq> Q \<Longrightarrow> {P} Id {> Q}"
by (auto simp add: PO_hoare_defs)

lemma hoare_trans_Un [iff]:
  "{P} R1 \<union> R2 {> Q} = ({P} R1 {> Q} \<and> {P} R2 {> Q})"
by (auto simp add: PO_hoare_defs)

lemma hoare_trans_UN [iff]:
  "{P} \<Union> x. R x {> Q} = (\<forall>x. {P} R x {> Q})"
by (auto simp add: PO_hoare_defs)

lemma hoare_apply:
  "{P} R {>Q} \<Longrightarrow> x \<in> P \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> y \<in> Q"
by (auto simp add: PO_hoare_defs)



subsubsection \<open>Characterization of reachability\<close>
(******************************************************************************)

lemma reach_init: "reach T \<subseteq> I \<Longrightarrow> init T \<subseteq> I"
by (auto dest: subsetD)

lemma reach_trans: "reach T \<subseteq> I \<Longrightarrow> {reach T} trans T {> I}"
by (auto simp add: PO_hoare_defs)


text \<open>Useful consequences.\<close>

corollary init_reach [iff]: "init T \<subseteq> reach T" 
by (rule reach_init, simp)

corollary trans_reach [iff]: "{reach T} trans T {> reach T}" 
by (rule reach_trans, simp)



subsubsection \<open>Invariant proof rules\<close>
(******************************************************************************)

text \<open>Basic proof rule for invariants.\<close>

lemma inv_rule_basic:
  "\<lbrakk> init T \<subseteq> P; {P} (trans T) {> P} \<rbrakk>
  \<Longrightarrow> reach T \<subseteq> P"
by (safe, erule reach.induct, auto simp add: PO_hoare_def)


text \<open>General invariant proof rule. This rule is complete (set 
@{term "I = reach T"}).\<close>

lemma inv_rule:
  "\<lbrakk> init T \<subseteq> I; I \<subseteq> P; {I} (trans T) {> I} \<rbrakk>
  \<Longrightarrow> reach T \<subseteq> P"
apply (rule subset_trans, auto)              \<comment> \<open>strengthen goal\<close>
apply (erule reach.induct, auto simp add: PO_hoare_def)
done

text \<open>The following rule is equivalent to the previous one.\<close>

lemma INV_rule:
  "\<lbrakk> init T \<subseteq> I; {I \<inter> reach T} (trans T) {> I} \<rbrakk>
  \<Longrightarrow> reach T \<subseteq> I"
by (safe, erule reach.induct, auto simp add: PO_hoare_defs)


text \<open>Proof of equivalence.\<close>

lemma inv_rule_from_INV_rule:
  "\<lbrakk> init T \<subseteq> I; I \<subseteq> P; {I} (trans T) {> I} \<rbrakk>
  \<Longrightarrow> reach T \<subseteq> P"
apply (rule subset_trans, auto del: subsetI)
apply (rule INV_rule, auto)
done

lemma INV_rule_from_inv_rule:
  "\<lbrakk> init T \<subseteq> I; {I \<inter> reach T} (trans T) {> I} \<rbrakk>
  \<Longrightarrow> reach T \<subseteq> I"
by (rule_tac I="I \<inter> reach T" in inv_rule, auto)


text \<open>Incremental proof rule for invariants using auxiliary invariant(s). 
This rule might have become obsolete by addition of $INV\_rule$.\<close>

lemma inv_rule_incr:
  "\<lbrakk> init T \<subseteq> I; {I \<inter> J} (trans T) {> I}; reach T \<subseteq> J \<rbrakk>    
  \<Longrightarrow> reach T \<subseteq> I"
by (rule INV_rule, auto)


(******************************************************************************)
subsection \<open>Refinement\<close>
(******************************************************************************)

text \<open>Our notion of refinement is simulation. We first define a general
notion of relational Hoare tuple, which we then use to define the refinement
proof obligation.  Finally, we show that observation-consistent refinement 
of specifications implies the implementation relation between them.\<close>


subsubsection \<open>Relational Hoare tuples\<close>
(******************************************************************************)

text \<open>Relational Hoare tuples formalize the following generalized simulation 
diagram:

\begin{verbatim}
                           o -- Ra --> o
                           |           |
                          pre         post
                           |           |
                           v           V
                           o -- Rc --> o
\end{verbatim}

Here, $Ra$ and $Rc$ are the abstract and concrete transition relations, 
and $pre$ and $post$ are the pre- and post-relations.
(In the definiton below, the operator @{term "(O)"} stands for relational 
composition, which is defined as follows: @{thm relcomp_def [no_vars]}.)\<close>

definition
  PO_rhoare :: 
    "[('s \<times> 't) set, ('s \<times> 's) set, ('t \<times> 't) set, ('s \<times> 't) set] \<Rightarrow> bool"
     ("(4{_} _, _ {> _})" [0, 0, 0] 90)
where
  "{pre} Ra, Rc {> post} \<equiv> pre O Rc \<subseteq> Ra O post"

lemmas PO_rhoare_defs = PO_rhoare_def relcomp_unfold


text \<open>Facts about relational Hoare tuples.\<close>

lemma relhoare_conseq_left [intro]:
  "\<lbrakk> {pre'} Ra, Rc {> post}; pre \<subseteq> pre' \<rbrakk> 
  \<Longrightarrow> {pre} Ra, Rc {> post}"
by (auto simp add: PO_rhoare_defs dest!: subsetD)

lemma relhoare_conseq_right:                    \<comment> \<open>do NOT declare [intro]\<close>
  "\<lbrakk> {pre} Ra, Rc {> post'}; post' \<subseteq> post \<rbrakk> 
  \<Longrightarrow> {pre} Ra, Rc {> post}"
by (auto simp add: PO_rhoare_defs)

lemma relhoare_false_left [simp]:               \<comment> \<open>do NOT declare [intro]\<close>
  "{ {} } Ra, Rc {> post}"
by (auto simp add: PO_rhoare_defs)

lemma relhoare_true_right [simp]:                \<comment> \<open>not true in general\<close>
  "{pre} Ra, Rc {> UNIV} = (Domain (pre O Rc) \<subseteq> Domain Ra)"
by (auto simp add: PO_rhoare_defs)

lemma Domain_rel_comp [intro]:
  "Domain pre \<subseteq> R \<Longrightarrow> Domain (pre O Rc) \<subseteq> R"
by (auto simp add: Domain_def)

lemma rel_hoare_skip [iff]: "{R} Id, Id {> R}"
by (auto simp add: PO_rhoare_def)


text \<open>Reflexivity and transitivity.\<close>

lemma relhoare_refl [simp]: "{Id} R, R {> Id}"
by (auto simp add: PO_rhoare_defs)

lemma rhoare_trans:
  "\<lbrakk> {R1} T1, T2 {> R1}; {R2} T2, T3 {> R2} \<rbrakk>
  \<Longrightarrow> {R1 O R2} T1, T3 {> R1 O R2}"
apply (auto simp add: PO_rhoare_def del: subsetI)
apply (drule subset_refl [THEN relcomp_mono, where r=R1])
apply (drule subset_refl [THEN [2] relcomp_mono, where s=R2])
apply (auto simp add: O_assoc del: subsetI)
done


text \<open>Conjunction in the post-relation cannot be split in general.  However, 
here are two useful special cases.  In the first case the abstract transtition 
relation is deterministic and in the second case one conjunct is a cartesian 
product of two state predicates.\<close>

lemma relhoare_conj_right_det:                 
  "\<lbrakk> {pre} Ra, Rc {> post1}; {pre} Ra, Rc {> post2};
     single_valued Ra \<rbrakk>                           \<comment> \<open>only for deterministic \<open>Ra\<close>!\<close>
  \<Longrightarrow> {pre} Ra, Rc {> post1 \<inter> post2}"
by (auto simp add: PO_rhoare_defs dest: single_valuedD dest!: subsetD)

lemma relhoare_conj_right_cartesian [intro]:
  "\<lbrakk> {Domain pre} Ra {> I}; {Range pre} Rc {> J};
     {pre} Ra, Rc {> post} \<rbrakk> 
  \<Longrightarrow> {pre} Ra, Rc {> post \<inter> I \<times> J}"
by (force simp add: PO_rhoare_defs PO_hoare_defs Domain_def Range_def)


text \<open>Separate rule for cartesian products.\<close>

corollary relhoare_cartesian:
  "\<lbrakk> {Domain pre} Ra {> I}; {Range pre} Rc {> J};
     {pre} Ra, Rc {> post} \<rbrakk>                      \<comment> \<open>any \<open>post\<close>, including \<open>UNIV\<close>!\<close>
  \<Longrightarrow> {pre} Ra, Rc {> I \<times> J}"
by (auto intro: relhoare_conseq_right)


text \<open>Unions of transition relations.\<close>

lemma relhoare_concrete_Un [simp]:
  "{pre} Ra, Rc1 \<union> Rc2 {> post} 
   = ({pre} Ra, Rc1 {> post} \<and> {pre} Ra, Rc2 {> post})"
apply (auto simp add: PO_rhoare_defs)
apply (auto dest!: subsetD)
done

lemma relhoare_concrete_UN [simp]:
  "{pre} Ra, \<Union>x. Rc x {> post} = (\<forall>x. {pre} Ra, Rc x {> post})"
apply (auto simp add: PO_rhoare_defs)
apply (auto dest!: subsetD)
done

lemma relhoare_abstract_Un_left [intro]:
  "\<lbrakk> {pre} Ra1, Rc {> post} \<rbrakk>
  \<Longrightarrow> {pre} Ra1 \<union> Ra2, Rc {> post}"
by (auto simp add: PO_rhoare_defs)

lemma relhoare_abstract_Un_right [intro]:
  "\<lbrakk> {pre} Ra2, Rc {> post} \<rbrakk>
  \<Longrightarrow> {pre} Ra1 \<union> Ra2, Rc {> post}"
by (auto simp add: PO_rhoare_defs)

lemma relhoare_abstract_UN [intro]:   \<comment> \<open>! might be too aggressive? INDEED.\<close>
  "\<lbrakk> {pre} Ra x, Rc {> post} \<rbrakk>
  \<Longrightarrow> {pre} \<Union>x. Ra x, Rc {> post}"
apply (auto simp add: PO_rhoare_defs)
apply (auto dest!: subsetD)
done

text \<open>Inclusion of abstract transition relations.\<close>

lemma relhoare_abstract_trans_weak [intro]:
  "\<lbrakk> {pre} Ra', Rc {> post}; Ra' \<subseteq> Ra \<rbrakk> 
 \<Longrightarrow> {pre} Ra, Rc {> post}"
by (auto simp add:PO_rhoare_defs)


subsubsection \<open>Refinement proof obligations\<close>
(******************************************************************************)

text \<open>A transition system refines another one if the initial states and the
transitions are refined. 
Initial state refinement means that for each concrete initial state there is 
a related abstract one. Transition refinement means that the simulation 
relation is preserved (as expressed by a relational Hoare tuple). 
\<close>

definition 
  PO_refines :: 
    "[('s \<times> 't) set, ('s, 'a) TS_scheme, ('t, 'b) TS_scheme] \<Rightarrow> bool" 
where
  "PO_refines R Ta Tc \<equiv> (
       init Tc \<subseteq> R``(init Ta)
     \<and> {R} (trans Ta), (trans Tc) {> R} 
  )"

lemma PO_refinesI:
  "\<lbrakk> init Tc \<subseteq> R``(init Ta); {R} (trans Ta), (trans Tc) {> R} \<rbrakk> \<Longrightarrow> PO_refines R Ta Tc"
by (simp add: PO_refines_def)

lemma PO_refinesE [elim]:
  "\<lbrakk> PO_refines R Ta Tc; \<lbrakk> init Tc \<subseteq> R``(init Ta); {R} (trans Ta), (trans Tc) {> R} \<rbrakk> \<Longrightarrow> P \<rbrakk> 
 \<Longrightarrow> P"
by (simp add: PO_refines_def)


text \<open>Basic refinement rule. This is just an introduction rule for the
definition.\<close>

lemma refine_basic:
  "\<lbrakk> init Tc \<subseteq> R``(init Ta); {R} (trans Ta), (trans Tc) {> R} \<rbrakk>
  \<Longrightarrow> PO_refines R Ta Tc"
by (simp add: PO_refines_def)


text \<open>The following proof rule uses individual invariants @{term "I"} 
and @{term "J"} of the concrete and abstract systems to strengthen the 
simulation relation $R$. 

The hypotheses state that these state predicates are indeed invariants.
Note that the pre-condition of the invariant preservation hypotheses for 
@{term "I"} and @{term "J"} are strengthened by adding the predicates 
@{term "Domain (R \<inter> UNIV \<times> J)"} and @{term "Range (R \<inter> I \<times> UNIV)"}, 
respectively.  In particular, the latter predicate may be essential, if a 
concrete invariant depends on the simulation relation and an abstract invariant, 
i.e. to "transport" abstract invariants to the concrete system.\<close>

lemma refine_init_using_invariants:
  "\<lbrakk> init Tc \<subseteq> R``(init Ta); init Ta \<subseteq> I; init Tc \<subseteq> J \<rbrakk>
  \<Longrightarrow> init Tc \<subseteq> (R \<inter> I \<times> J)``(init Ta)"
by (auto simp add: Image_def dest!: bspec subsetD)

lemma refine_trans_using_invariants:
  "\<lbrakk> {R \<inter> I \<times> J} (trans Ta), (trans Tc) {> R};
     {I \<inter> Domain (R \<inter> UNIV \<times> J)} (trans Ta) {> I}; 
     {J \<inter> Range (R \<inter> I \<times> UNIV)} (trans Tc) {> J} \<rbrakk>
  \<Longrightarrow> {R \<inter> I \<times> J} (trans Ta), (trans Tc) {> R  \<inter> I \<times> J}"
by (rule relhoare_conj_right_cartesian) (auto)


text \<open>This is our main rule for refinements.\<close>

lemma refine_using_invariants:
  "\<lbrakk> {R \<inter> I \<times> J} (trans Ta), (trans Tc) {> R};
     {I \<inter> Domain (R \<inter> UNIV \<times> J)} (trans Ta) {> I}; 
     {J \<inter> Range (R \<inter> I \<times> UNIV)} (trans Tc) {> J}; 
     init Tc \<subseteq> R``(init Ta); 
     init Ta \<subseteq> I; init Tc \<subseteq> J \<rbrakk>
  \<Longrightarrow> PO_refines (R \<inter> I \<times> J) Ta Tc"
by (unfold PO_refines_def)
   (intro refine_init_using_invariants refine_trans_using_invariants conjI)


subsubsection \<open>Deriving invariants from refinements\<close>
(******************************************************************************)

text \<open>Some invariants can only be proved after the simulation has been 
established, because they depend on the simulation relation and some abstract
invariants.  Here is a rule to derive invariant theorems from the refinement.\<close>

lemma PO_refines_implies_Range_init:
  "PO_refines R Ta Tc \<Longrightarrow> init Tc \<subseteq> Range R"
by (auto simp add: PO_refines_def)

lemma PO_refines_implies_Range_trans:
  "PO_refines R Ta Tc \<Longrightarrow> {Range R} trans Tc {> Range R}"
by (auto simp add: PO_refines_def PO_rhoare_def PO_hoare_def)

lemma PO_refines_implies_Range_invariant:
  "PO_refines R Ta Tc \<Longrightarrow> reach Tc \<subseteq> Range R"
by (rule INV_rule)
   (auto intro!: PO_refines_implies_Range_init 
                 PO_refines_implies_Range_trans)

text \<open>The following rules are more useful in proofs.\<close>

corollary INV_init_from_refinement: 
  "\<lbrakk> PO_refines R Ta Tc; Range R \<subseteq> I \<rbrakk>
  \<Longrightarrow> init Tc \<subseteq> I"
by (drule PO_refines_implies_Range_init, auto)

corollary INV_trans_from_refinement: 
  "\<lbrakk> PO_refines R Ta Tc; K \<subseteq> Range R; Range R \<subseteq> I \<rbrakk>
  \<Longrightarrow> {K} trans Tc {> I}"
apply (drule PO_refines_implies_Range_trans)
apply (auto intro: hoare_conseq_right)
done

corollary INV_from_refinement: 
  "\<lbrakk> PO_refines R Ta Tc; Range R \<subseteq> I \<rbrakk>
  \<Longrightarrow> reach Tc \<subseteq> I"
by (drule PO_refines_implies_Range_invariant, fast)


subsubsection \<open>Refinement of specifications\<close>
(******************************************************************************)

text \<open>Lift relation membership to finite sequences\<close>

inductive_set 
  seq_lift :: "('s \<times> 't) set \<Rightarrow> ('s list \<times> 't list) set" 
  for R :: "('s \<times> 't) set"
where
  sl_nil [iff]: "([], []) \<in> seq_lift R"
| sl_cons [intro]: 
    "\<lbrakk> (xs, ys) \<in> seq_lift R; (x, y) \<in> R \<rbrakk> \<Longrightarrow> (x#xs, y#ys) \<in> seq_lift R"

inductive_cases sl_cons_right_invert: "(ba', t # bc) \<in> seq_lift R" 


text \<open>For each concrete behaviour there is a related abstract one.\<close>

lemma behaviour_refinement:
  "\<lbrakk> PO_refines R Ta Tc; bc \<in> beh Tc\<rbrakk> 
  \<Longrightarrow> \<exists>ba \<in> beh Ta. (ba, bc) \<in> seq_lift R" 
apply (erule beh.induct, auto)
  \<comment> \<open>case: singleton\<close>
  apply (clarsimp simp add: PO_refines_def Image_def)
  apply (drule subsetD, auto)

  \<comment> \<open>case: cons; first construct related abstract state\<close>
  apply (erule sl_cons_right_invert, clarsimp)
  apply (rename_tac s bc s' ba t)
  \<comment> \<open>now construct abstract transition\<close>
  apply (auto simp add: PO_refines_def PO_rhoare_def)
  apply (thin_tac "X \<subseteq> Y" for X Y)
  apply (drule subsetD, auto)
done


text \<open>Observation consistency of a relation is defined using a mediator 
function @{term "pi"} to abstract the concrete observation.  This allows us 
to also refine the observables as we move down a refinement branch.
\<close>

definition 
  obs_consistent :: 
    "[('s \<times> 't) set, 'p \<Rightarrow> 'o, ('s, 'o) spec, ('t, 'p) spec] \<Rightarrow> bool"
where
  "obs_consistent R pi Sa Sc \<equiv> (\<forall>s t. (s, t) \<in> R \<longrightarrow> pi (obs Sc t) = obs Sa s)"

lemma obs_consistent_refl [iff]: "obs_consistent Id id S S"
by (simp add: obs_consistent_def)

lemma obs_consistent_trans [intro]: 
  "\<lbrakk> obs_consistent R1 pi1 S1 S2; obs_consistent R2 pi2 S2 S3 \<rbrakk>
  \<Longrightarrow> obs_consistent (R1 O R2) (pi1 o pi2) S1 S3"
by (auto simp add: obs_consistent_def)

lemma obs_consistent_empty: "obs_consistent {} pi Sa Sc"
by (auto simp add: obs_consistent_def)

lemma obs_consistent_conj1 [intro]: 
  "obs_consistent R pi Sa Sc \<Longrightarrow> obs_consistent (R \<inter> R') pi Sa Sc"
by (auto simp add: obs_consistent_def)

lemma obs_consistent_conj2 [intro]: 
  "obs_consistent R pi Sa Sc \<Longrightarrow> obs_consistent (R' \<inter> R) pi Sa Sc"
by (auto simp add: obs_consistent_def)

lemma obs_consistent_behaviours:
  "\<lbrakk> obs_consistent R pi Sa Sc; bc \<in> beh Sc; ba \<in> beh Sa; (ba, bc) \<in> seq_lift R\<rbrakk>
  \<Longrightarrow> map pi (map (obs Sc) bc) = map (obs Sa) ba"
by (erule seq_lift.induct) (auto simp add: obs_consistent_def) 


text \<open>Definition of refinement proof obligations.\<close>

definition 
  refines :: 
    "[('s \<times> 't) set, 'p \<Rightarrow> 'o, ('s, 'o) spec, ('t, 'p) spec] \<Rightarrow> bool" 
where
  "refines R pi Sa Sc \<equiv> obs_consistent R pi Sa Sc \<and> PO_refines R Sa Sc"

lemmas refines_defs = 
  refines_def PO_refines_def

lemma refinesI: 
  "\<lbrakk> PO_refines R Sa Sc; obs_consistent R pi Sa Sc \<rbrakk>
  \<Longrightarrow> refines R pi Sa Sc"
by (simp add: refines_def)

lemma refinesE [elim]: 
  "\<lbrakk> refines R pi Sa Sc; \<lbrakk> PO_refines R Sa Sc; obs_consistent R pi Sa Sc \<rbrakk> \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
by (simp add: refines_def)


text \<open>Reflexivity and transitivity of refinement.\<close>

lemma refinement_reflexive: "refines Id id S S"
by (auto simp add: refines_defs)

lemma refinement_transitive: 
  "\<lbrakk> refines R1 pi1 S1 S2; refines R2 pi2 S2 S3 \<rbrakk> 
  \<Longrightarrow> refines (R1 O R2) (pi1 o pi2) S1 S3"
apply (auto simp add: refines_defs del: subsetI
            intro: rhoare_trans)
apply (fastforce dest: Image_mono)
done


text \<open>Soundness of refinement for proving implementation\<close>

lemma observable_behaviour_refinement:
  "\<lbrakk> refines R pi Sa Sc; bc \<in> obeh Sc \<rbrakk> \<Longrightarrow> map pi bc \<in> obeh Sa"
by (auto simp add: refines_def obeh_def image_def
         dest!: behaviour_refinement obs_consistent_behaviours)

theorem refinement_soundness: 
  "refines R pi Sa Sc \<Longrightarrow> implements pi Sa Sc"
by (auto simp add: implements_def 
         elim!: observable_behaviour_refinement)


text \<open>Extended versions of refinement proof rules including observations\<close>

lemmas Refinement_basic = refine_basic [THEN refinesI]
lemmas Refinement_using_invariants = refine_using_invariants [THEN refinesI]

lemma refines_reachable_strengthening:
  "refines R pi Sa Sc \<Longrightarrow> refines (R \<inter> reach Sa \<times> reach Sc) pi Sa Sc"
by (auto intro!: Refinement_using_invariants)


text \<open>Inhertitance of internal invariants through refinements\<close>

lemma INV_init_from_Refinement:
  "\<lbrakk>refines R pi Sa Sc; Range R \<subseteq> I\<rbrakk> \<Longrightarrow> init Sc \<subseteq> I" 
by (blast intro: INV_init_from_refinement) 

lemma INV_trans_from_Refinement:
  " \<lbrakk>refines R pi Sa Sc; K \<subseteq> Range R; Range R \<subseteq> I\<rbrakk> \<Longrightarrow> {K} TS.trans Sc {> I}"
by (blast intro: INV_trans_from_refinement) 


lemma INV_from_Refinement_basic: 
  "\<lbrakk> refines R pi Sa Sc; Range R \<subseteq> I \<rbrakk> \<Longrightarrow> reach Sc \<subseteq> I"
by (rule INV_from_refinement) blast

lemma INV_from_Refinement_using_invariants: 
  assumes "refines R pi Sa Sc" "Range (R \<inter> I \<times> J) \<subseteq> K" 
          "reach Sa \<subseteq> I" "reach Sc \<subseteq> J" 
  shows "reach Sc \<subseteq> K" 
proof (rule INV_from_Refinement_basic)
  show "refines (R \<inter> reach Sa \<times> reach Sc) pi Sa Sc" using assms(1) 
    by (rule refines_reachable_strengthening)
next 
  show "Range (R \<inter> reach Sa \<times> reach Sc) \<subseteq> K" using assms(2-4) by blast
qed


end
