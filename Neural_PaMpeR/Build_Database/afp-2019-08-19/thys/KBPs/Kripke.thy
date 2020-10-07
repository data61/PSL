(*<*)
(*
 * Knowledge-based programs.
 * (C)opyright 2011, Peter Gammie, peteg42 at gmail.com.
 * License: BSD
 *)

theory Kripke
imports Main
begin
(*>*)

section \<open>A modal logic of knowledge\<close>

text\<open>

\label{sec:kbps-logic-of-knowledge}

We begin with the standard syntax and semantics of the propositional
logic of knowledge based on \emph{Kripke structures}. More extensive
treatments can be found in \citet{Lenzen:1978}, \citet{Chellas:1980},
\citet{Hintikka:1962} and \citet[Chapter~2]{FHMV:1995}.

The syntax includes one knowledge modality per agent, and one for
\emph{common knowledge} amongst a set of agents. It is parameterised
by the type @{typ "'a"} of agents and @{typ "'p"} of propositions.

\<close>

datatype ('a, 'p) Kform
  = Kprop "'p"
  | Knot "('a, 'p) Kform"
  | Kand "('a, 'p) Kform" "('a, 'p) Kform"
  | Kknows "'a" "('a, 'p) Kform"  ("\<^bold>K\<^sub>_ _")
  | Kcknows "'a list" "('a, 'p) Kform" ("\<^bold>C\<^bsub>_\<^esub> _")

text\<open>

A Kripke structure consists of a set of \emph{worlds} of type @{typ
"'w"}, one \emph{accessibility relation} between worlds for each agent
and a \emph{valuation function} that indicates the truth of a
proposition at a world. This is a very general story that we will
quickly specialise.

\<close>

type_synonym 'w Relation = "('w \<times> 'w) set"

record ('a, 'p, 'w) KripkeStructure =
  worlds :: "'w set"
  relations :: "'a \<Rightarrow> 'w Relation"
  valuation :: "'w \<Rightarrow> 'p \<Rightarrow> bool"

definition kripke :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> bool" where
  "kripke M \<equiv> \<forall>a. relations M a \<subseteq> worlds M \<times> worlds M"

definition
  mkKripke :: "'w set \<Rightarrow> ('a \<Rightarrow> 'w Relation) \<Rightarrow> ('w \<Rightarrow> 'p \<Rightarrow> bool)
            \<Rightarrow> ('a, 'p, 'w) KripkeStructure"
where
  "mkKripke ws rels val \<equiv>
     \<lparr> worlds = ws, relations = \<lambda>a. rels a \<inter> ws \<times> ws, valuation = val \<rparr>"
(*<*)

lemma kripkeI[intro]:
  assumes "\<And>a. relations M a \<subseteq> worlds M \<times> worlds M"
  shows "kripke M"
  using assms unfolding kripke_def by simp

lemma kripke_rels_worlds[dest]:
  assumes "(w, w') \<in> relations M a"
  assumes M: "kripke M"
  shows "w \<in> worlds M \<and> w' \<in> worlds M"
  using assms unfolding kripke_def by auto

lemma kripke_tc_rels_worlds[dest]:
  assumes R: "(w, w') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
  assumes M: "kripke M"
  shows "w \<in> worlds M \<and> w' \<in> worlds M"
  using assms by (induct rule: trancl_induct) auto

lemma kripke_rels_trc_worlds:
  assumes R: "(w, w') \<in> (\<Union>a. relations M a)\<^sup>*"
  assumes w: "w \<in> worlds M"
  assumes M: "kripke M"
  assumes W: "W = worlds M"
  shows "w' \<in> W"
  using assms by (induct rule: rtrancl_induct) auto

lemma mkKripke_kripke[intro, simp]:
  "kripke (mkKripke ws rels val)"
  unfolding kripke_def mkKripke_def by clarsimp

lemma mkKripke_simps[simp]:
  "worlds (mkKripke ws rels val) = ws"
  "relations (mkKripke ws rels val) = (\<lambda>a. rels a \<inter> ws \<times> ws)"
  "valuation (mkKripke ws rels val) = val"
  unfolding mkKripke_def by simp_all
(*>*)

text \<open>

The standard semantics for knowledge is given by taking the
accessibility relations to be equivalence relations, yielding the
S$5_n$ structures, so-called due to their axiomatisation.

\<close>

definition S5n :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> bool" where
  "S5n M \<equiv> \<forall>a. equiv (worlds M) (relations M a)"
(*<*)

lemma S5nI[intro]: "\<lbrakk> \<And>a. equiv (worlds M) (relations M a) \<rbrakk> \<Longrightarrow> S5n M"
  by (simp add: S5n_def)

lemma S5nD[dest]: "S5n M \<Longrightarrow> equiv (worlds M) (relations M a)"
  by (simp add: S5n_def)

lemma S5n_kripke[intro]: "S5n M \<Longrightarrow> kripke M"
  by (rule kripkeI, erule equivE[OF S5nD], auto simp add: refl_on_def)

lemma S5n_rels_closed:
  "S5n M \<Longrightarrow> relations M a `` (relations M a `` X) \<subseteq> relations M a `` X"
  apply (drule S5nD[where a=a])
  apply (erule equivE)
  apply (auto dest: refl_onD symD transD)
  done

(*>*)

text\<open>

Intuitively an agent considers two worlds to be equivalent if it
cannot distinguish between them.

\<close>

subsection\<open>Satisfaction\<close>

text\<open>

A formula $\phi$ is satisfied at a world $w$ in Kripke structure $M$
in the following way:\<close>

fun models :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> ('a, 'p) Kform
           \<Rightarrow> bool" ("(_, _ \<Turnstile> _)" [80,0,80] 80) where
  "M, w \<Turnstile> (Kprop p) = valuation M w p"
| "M, w \<Turnstile> (Knot \<phi>) = (\<not> M, w \<Turnstile> \<phi>)"
| "M, w \<Turnstile> (Kand \<phi> \<psi>) = (M, w \<Turnstile> \<phi> \<and> M, w \<Turnstile> \<psi>)"
| "M, w \<Turnstile> (\<^bold>K\<^sub>a \<phi>) = (\<forall>w' \<in> relations M a `` {w}. M, w' \<Turnstile> \<phi>)"
| "M, w \<Turnstile> (\<^bold>C\<^bsub>as\<^esub> \<phi>) = (\<forall>w' \<in> (\<Union>a \<in> set as. relations M a)\<^sup>+ `` {w}. M, w' \<Turnstile> \<phi>)"

text\<open>

The first three clauses are standard.

The clause for @{term "Kknows a \<phi>"} expresses the idea that an agent
knows @{term "\<phi>"} at world @{term "w"} in structure @{term "M"} iff
@{term "\<phi>"} is true at all worlds it considers possible.

The clause for @{term "Kcknows as \<phi>"} captures what it means for the
set of agents @{term "as"} to commonly know @{term "\<phi>"}; roughly,
everyone knows @{term "\<phi>"} and knows that everyone knows it, and so
forth. Note that the transitive closure and the reflexive-transitive
closure generate the same relation due to the reflexivity of the
agents' accessibility relations; we use the former as it has a more
pleasant induction principle.

\<close>
(*<*)

lemma S5n_rels_eq:
  assumes S5n: "S5n M"
      and ww': "(w, w') \<in> relations M a"
  shows "relations M a `` {w} = relations M a `` {w'}"
  using S5nD[OF S5n] ww' by - (rule equiv_class_eq, blast+)

text\<open>

A key property of the semantics for common knowledge is that it forms
an equivalence class itself.

\<close>

lemma tc_equiv:
  assumes E: "\<And>i. i \<in> is \<Longrightarrow> equiv A (f i)"
      and is_nempty: "is \<noteq> {}"
  shows "equiv A ((\<Union>i\<in>is. f i)\<^sup>+)"
proof(rule equivI)
  from E is_nempty show "refl_on A ((\<Union>i\<in>is. f i)\<^sup>+)"
    unfolding equiv_def
    apply -
    apply (rule refl_onI)
    apply (rule trancl_Int_subset)
    apply (auto dest: refl_onD refl_onD1 refl_onD2)
    done
  from E show "sym ((\<Union>i\<in>is. f i)\<^sup>+)"
    apply -
    apply (rule sym_trancl)
    unfolding equiv_def sym_def by blast
  show "trans  ((\<Union>i\<in>is. f i)\<^sup>+)" by (rule trans_trancl)
qed

lemma S5n_tc_rels_eq:
  assumes S5n: "S5n M"
      and ww': "(w, w') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
  shows "(\<Union>a \<in> as. relations M a)\<^sup>+ `` {w} = (\<Union>a \<in> as. relations M a)\<^sup>+ `` {w'}"
  apply (cases "as = {}")
   apply fastforce
  apply (rule equiv_class_eq[OF _ ww'])
  apply (erule tc_equiv[OF S5nD[OF S5n]])
  done

text\<open>We can show that the standard S5 properties hold of this semantics:\<close>

lemma S5n_knowledge_generalisation:
  "\<lbrakk> S5n M; \<forall>w \<in> worlds M. M, w \<Turnstile> \<phi> \<rbrakk> \<Longrightarrow> M, w \<Turnstile> Kknows a \<phi>"
  unfolding S5n_def equiv_def refl_on_def by auto

lemma S5n_knowledge:
  "\<lbrakk> S5n M; w \<in> worlds M; M, w \<Turnstile> Kknows a \<phi> \<rbrakk> \<Longrightarrow> M, w \<Turnstile> \<phi>"
  unfolding S5n_def equiv_def refl_on_def by auto

lemma S5n_positive_introspection:
  "\<lbrakk> S5n M; w \<in> worlds M; M, w \<Turnstile> Kknows a \<phi> \<rbrakk> \<Longrightarrow> M, w \<Turnstile> Kknows a (Kknows a \<phi>)"
  unfolding S5n_def equiv_def by simp (blast dest: transD)

lemma S5n_negative_introspection:
  "\<lbrakk> S5n M; w \<in> worlds M; M, w \<Turnstile> Knot (Kknows a \<phi>) \<rbrakk>
     \<Longrightarrow> M, w \<Turnstile> Kknows a (Knot (Kknows a \<phi>))"
  unfolding S5n_def equiv_def by simp (blast dest: symD transD)
(*>*)

text\<open>

The relation between knowledge and common knowledge can be understood
as follows, following \citet[\S2.4]{FHMV:1995}. Firstly, that $\phi$
is common knowledge to a set of agents $as$ can be seen as asserting
that everyone in $as$ knows $\phi$ and moreover knows that it is
common knowledge amongst $as$.

\<close>

lemma S5n_common_knowledge_fixed_point:
  assumes S5n: "S5n M"
  assumes w: "w \<in> worlds M"
  assumes a: "a \<in> set as"
  shows "M, w \<Turnstile> Kcknows as \<phi>
     \<longleftrightarrow> M, w \<Turnstile> Kand (Kknows a \<phi>) (Kknows a (Kcknows as \<phi>))"
(*<*)
proof
  assume CK: "M, w \<Turnstile> Kcknows as \<phi>"
  from S5n a w CK
  have "M, w \<Turnstile> Kknows a \<phi>"
   and "M, w \<Turnstile> Kknows a (Kcknows as \<phi>)"
    by (auto intro: trancl_into_trancl2)
  then show "M, w \<Turnstile> Kand (Kknows a \<phi>) (Kknows a (Kcknows as \<phi>))"
    by simp
next
  assume "M, w \<Turnstile> Kand (Kknows a \<phi>) (Kknows a (Kcknows as \<phi>))"
  hence "M, w \<Turnstile> (Kknows a (Kcknows as \<phi>))" by simp
  with S5n w show "M, w \<Turnstile> (Kcknows as \<phi>)" by (rule S5n_knowledge)
qed

(*>*)
text\<open>

Secondly we can provide an induction schema for the introduction of
common knowledge: from everyone in $as$ knows that $\phi$ implies
$\phi \land \psi$, and that $\phi$ is satisfied at world $w$, infer
that $\psi$ is common knowledge amongst $as$ at $w$.

\<close>

lemma S5n_common_knowledge_induct:
  assumes S5n: "S5n M"
  assumes w: "w \<in> worlds M"
  assumes E: "\<forall>a \<in> set as. \<forall>w \<in> worlds M.
                 M, w \<Turnstile> \<phi> \<longrightarrow> M, w \<Turnstile> \<^bold>K\<^sub>a (Kand \<phi> \<psi>)"
  assumes p: "M, w \<Turnstile> \<phi>"
  shows "M, w \<Turnstile> \<^bold>C\<^bsub>as\<^esub> \<psi>"
(*<*)
proof -
  { fix w' assume ww': "(w, w') \<in> (\<Union>x\<in>set as. relations M x)\<^sup>+"
    from ww' S5n E p w have "M, w' \<Turnstile> Kand \<phi> \<psi>"
      by ( induct rule: trancl_induct
         , simp_all, blast+) }
  thus ?thesis by simp
qed

(* We actually use a simpler variant. *)

lemma S5n_common_knowledge_fixed_point_simpler:
  assumes S5n: "S5n M"
      and w: "w \<in> worlds M"
      and a: "a \<in> set as"
  shows "M, w \<Turnstile> Kcknows as \<phi> \<longleftrightarrow> M, w \<Turnstile> Kknows a (Kcknows as \<phi>)"
proof
  assume CK: "M, w \<Turnstile> Kcknows as \<phi>"
  from S5n a w CK show "M, w \<Turnstile> Kknows a (Kcknows as \<phi>)"
    by (auto intro: trancl_into_trancl2)
next
  assume "M, w \<Turnstile> Kknows a (Kcknows as \<phi>)"
  with S5n w show "M, w \<Turnstile> (Kcknows as \<phi>)" by (rule S5n_knowledge)
qed

(*>*)

(* **************************************** *)

subsection \<open>Generated models\<close>

text\<open>

\label{sec:generated_models}

The rest of this section introduces the technical machinery we use to
relate Kripke structures.

Intuitively the truth of a formula at a world depends only on the
worlds that are reachable from it in zero or more steps, using any of
the accessibility relations at each step. Traditionally this result is
called the \emph{generated model property}
\citep[\S3.4]{Chellas:1980}.

Given the model generated by @{term "w"} in @{term "M"}:

\<close>

definition
  gen_model :: "('a, 'p, 'w) KripkeStructure \<Rightarrow> 'w \<Rightarrow> ('a, 'p, 'w) KripkeStructure"
where
  "gen_model M w \<equiv>
    let ws' = worlds M \<inter> (\<Union>a. relations M a)\<^sup>* `` {w}
     in \<lparr> worlds = ws',
          relations = \<lambda>a. relations M a \<inter> (ws' \<times> ws'),
          valuation = valuation M \<rparr>"
(*<*)

lemma gen_model_worldsD[dest]:
  "w' \<in> worlds (gen_model M w) \<Longrightarrow> w' \<in> worlds M"
  unfolding gen_model_def by simp

lemma gen_model_world_refl:
  "w \<in> worlds M \<Longrightarrow> w \<in> worlds (gen_model M w)"
  unfolding gen_model_def by simp

lemma gen_model_rels_worlds[dest]:
  assumes "(w', w'') \<in> relations (gen_model M w) a"
  shows "w' \<in> worlds (gen_model M w) \<and> w'' \<in> worlds (gen_model M w)"
  using assms unfolding gen_model_def by simp

lemma gen_model_rels_tc_worlds[dest]:
  assumes "(w', w'') \<in> (\<Union>a \<in> as. relations (gen_model M w) a)\<^sup>+"
  shows "w'' \<in> worlds (gen_model M w)"
  using assms by (induct rule: trancl_induct) auto

lemma gen_model_rels[dest]:
  assumes "(w', w'') \<in> relations (gen_model M w) a"
  shows "(w', w'') \<in> relations M a"
  using assms unfolding gen_model_def by simp

lemma gen_model_worlds:
  "worlds (gen_model M w) = worlds M \<inter> (\<Union>a. relations M a)\<^sup>* `` {w}"
  unfolding gen_model_def by simp

lemma gen_model_tc_rels[dest]:
  assumes M: "kripke M"
      and R: "(w', w'') \<in> (\<Union>a \<in> as. relations (gen_model M w) a)\<^sup>+"
  shows "(w', w'') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
using R
proof(induct rule: trancl_induct)
  case (base y) with M show ?case by auto
next
  case (step y z)
  with M have "y \<in> worlds (gen_model M w)"
          and "z \<in> worlds (gen_model M w)" by auto
  with M step show ?case by (auto intro: trancl_into_trancl)
qed

lemma gen_model_rels_rev[dest]:
  assumes M: "kripke M"
      and "w' \<in> worlds (gen_model M w)"
      and "(w', w'') \<in> relations M a"
  shows "(w', w'') \<in> relations (gen_model M w) a"
  using assms
  unfolding gen_model_def by (auto intro: rtrancl_into_rtrancl)

lemma gen_model_tc_rels_rev[dest]:
  assumes M: "kripke M"
      and R: "(w', w'') \<in> (\<Union>a \<in> as. relations M a)\<^sup>+"
      and W: "w' \<in> worlds (gen_model M w)"
  shows "(w', w'') \<in> (\<Union>a \<in> as. relations (gen_model M w) a)\<^sup>+"
using R W
proof(induct rule: trancl_induct)
  case (base y) with M show ?case by auto
next
  case (step y z)
  with M have "y \<in> worlds (gen_model M w)"
          and "z \<in> worlds (gen_model M w)" by auto
  with M step show ?case by (auto intro: trancl_into_trancl)
qed

lemma gen_model_kripke:
  shows "kripke (gen_model M w)"
  unfolding gen_model_def by auto

(*>*)

text\<open>

where we take the image of @{term "w"} under the reflexive transitive
closure of the agents' relations, we can show that the satisfaction of
a formula @{term "\<phi>"} at a world @{term "w'"} is preserved, provided
@{term "w'"} is relevant to the world @{term "w"} that the sub-model
is based upon:

\<close>

lemma gen_model_semantic_equivalence:
  assumes M: "kripke M"
  assumes w': "w' \<in> worlds (gen_model M w)"
  shows "M, w' \<Turnstile> \<phi> \<longleftrightarrow> (gen_model M w), w' \<Turnstile> \<phi>"
(*<*)
proof -
  { fix w w' assume "w' \<in> worlds (gen_model M w)"
    hence "M, w' \<Turnstile> \<phi> \<longleftrightarrow> (gen_model M w), w' \<Turnstile> \<phi>"
    proof(induct \<phi> arbitrary: w')
      case (Kknows a f w') show ?case
      proof
        assume lhs: "M, w' \<Turnstile> Kknows a f"
        with Kknows show "gen_model M w, w' \<Turnstile> Kknows a f" by auto
      next
        assume rhs: "gen_model M w, w' \<Turnstile> Kknows a f"
        with M Kknows show "M, w' \<Turnstile> Kknows a f"
          by (simp, blast)
      qed
    next
      case (Kcknows as f w') show ?case
      proof
        assume lhs: "M, w' \<Turnstile> Kcknows as f"
        with M Kcknows show "gen_model M w, w' \<Turnstile> Kcknows as f"
          by (simp, blast)
      next
        assume rhs: "gen_model M w, w' \<Turnstile> Kcknows as f"
        with M Kcknows show "M, w' \<Turnstile> Kcknows as f"
          by (simp, blast)
      qed
    qed (simp_all add: gen_model_def) }
  with w' show ?thesis by simp
qed
(*>*)

text\<open>

This is shown by a straightforward structural induction over the
formula @{term "\<phi>"}.

\<close>
(*<*)

lemma gen_model_S5n:
  assumes S5n: "S5n M"
  shows "S5n (gen_model M w)"
proof(intro S5nI equivI)
  show "\<And>n. refl_on (worlds (gen_model M w)) (relations (gen_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by - (rule refl_onI, auto simp add: refl_on_def gen_model_def)
  show "\<And>n. sym (relations (gen_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by (unfold gen_model_def sym_def, auto)
  show "\<And>n. trans (relations (gen_model M w) n)"
    apply (rule equivE[OF S5nD[OF S5n]])
    by - (rule transI, simp add: gen_model_def, unfold trans_def, blast)
qed

text\<open>

If two models generate the same sub-model for a world, they satisfy
the same formulas at that world.

\<close>

lemma gen_model_eq:
  assumes M: "kripke M"
      and M': "kripke M'"
      and "gen_model M w = gen_model M' w"
      and "w' \<in> worlds (gen_model M' w)"
  shows "M, w' \<Turnstile> \<phi> \<longleftrightarrow> M', w' \<Turnstile> \<phi>"
  using assms gen_model_semantic_equivalence[OF M, where w=w]
              gen_model_semantic_equivalence[OF M', where w=w]
  by auto

text \<open>

Our final lemma in this section is technical: it allows us to move
between two Kripke structures that have the same relevant worlds.

\<close>

lemma gen_model_subset_aux:
  assumes R: "\<And>a. relations M a \<inter> T \<times> T = relations M' a \<inter> T \<times> T"
      and T: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> T"
  shows "(\<Union>x. relations M x)\<^sup>* `` {t} \<subseteq> (\<Union>x. relations M' x)\<^sup>* `` {t}"
proof -
  { fix x assume "(t, x) \<in> (\<Union>x. relations M x)\<^sup>*"
    hence "(t, x) \<in> (\<Union>x. relations M' x)\<^sup>*"
    proof(induct rule: rtrancl_induct)
      case (step y z)
      with R T have "(y, z) \<in> (\<Union>a. relations M' a)"
        by auto (blast dest: rtrancl_trans)
      with step show ?case by (blast intro: rtrancl_trans)
    qed simp }
  thus ?thesis by blast
qed

lemma gen_model_subset:
  assumes M: "kripke M"
      and M': "kripke M'"
      and R: "\<And>a. relations M a \<inter> T \<times> T = relations M' a \<inter> T \<times> T"
      and tMT: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> T"
      and tM'T: "(\<Union>a. relations M' a)\<^sup>* `` {t} \<subseteq> T"
      and tM: "t \<in> worlds M"
      and tM': "t \<in> worlds M'"
      and V: "valuation M = valuation M'"
  shows "gen_model M t = gen_model M' t"
proof -
  from tMT tM'T gen_model_subset_aux[OF R] gen_model_subset_aux[OF R[symmetric]]
  have F: "(\<Union>a. relations M a)\<^sup>* `` {t} = (\<Union>a. relations M' a)\<^sup>* `` {t}"
    by - (rule, simp_all)

  from M tMT tM have G: "(\<Union>a. relations M a)\<^sup>* `` {t} \<subseteq> worlds M"
    by (auto dest: kripke_rels_trc_worlds)
  from M' tM'T tM' have H: "(\<Union>a. relations M' a)\<^sup>* `` {t} \<subseteq> worlds M'"
    by (auto dest: kripke_rels_trc_worlds)

  from F G H have WORLDS: "worlds (gen_model M t) = worlds (gen_model M' t)"
    unfolding gen_model_def by (auto iff: Int_absorb1)

  have RELATIONS: "\<And>a. relations (gen_model M t) a = relations (gen_model M' t) a"
  proof (simp add: Int_absorb1 G H gen_model_def)
    fix a
    { fix a x y
      assume XY: "(x, y) \<in> relations M a \<inter> (\<Union>x. relations M x)\<^sup>* `` {t} \<times> (\<Union>x. relations M x)\<^sup>* `` {t}"
      from XY tMT
      have "(x, y) \<in> relations M a \<inter> T \<times> T" by blast
      with R
      have "(x, y) \<in> relations M' a \<inter> T \<times> T" by blast
      with F XY tM'T
      have "(x, y) \<in> relations M' a \<inter> (\<Union>x. relations M' x)\<^sup>* `` {t} \<times> (\<Union>x. relations M' x)\<^sup>* `` {t}"
        by blast }
    moreover
    { fix a x y
      assume XY: "(x, y) \<in> relations M' a \<inter> (\<Union>x. relations M' x)\<^sup>* `` {t} \<times> (\<Union>x. relations M' x)\<^sup>* `` {t}"
      from XY tM'T
      have "(x, y) \<in> relations M' a \<inter> T \<times> T" by blast
      with R
      have "(x, y) \<in> relations M a \<inter> T \<times> T" by blast
      with F XY tMT
      have "(x, y) \<in> relations M a \<inter> (\<Union>x. relations M x)\<^sup>* `` {t} \<times> (\<Union>x. relations M x)\<^sup>* `` {t}"
        by blast }
    ultimately show "Restr (relations M a) ((\<Union>x. relations M x)\<^sup>* `` {t}) =
      Restr (relations M' a) ((\<Union>x. relations M' x)\<^sup>* `` {t})"
    apply -
    apply rule
     apply rule
     apply auto[1]
    apply rule
    apply (case_tac x)
    apply (simp (no_asm_use))
    apply (metis Image_singleton_iff mem_Sigma_iff)
    done
  qed
  from WORLDS RELATIONS V show ?thesis
    unfolding gen_model_def by simp
qed

(*>*)

subsection \<open>Simulations\<close>

text\<open>

\label{sec:kripke-theory-simulations}

A \emph{simulation}, or \emph{p-morphism}, is a mapping from the
worlds of one Kripke structure to another that preserves the truth of
all formulas at related worlds \citep[\S3.4, Ex. 3.60]{Chellas:1980}.
Such a function @{term "f"} must satisfy four properties. Firstly, the
image of the set of worlds of @{term "M"} under @{term "f"} should
equal the set of worlds of @{term "M'"}.

\<close>

definition
  sim_range :: "('a, 'p, 'w1) KripkeStructure
              \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_range M M' f \<equiv> worlds M' = f ` worlds M
                    \<and> (\<forall>a. relations M' a \<subseteq> worlds M' \<times> worlds M')"

text\<open>The value of a proposition should be the same at corresponding
worlds:\<close>

definition
  sim_val :: "('a, 'p, 'w1) KripkeStructure
           \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_val M M' f \<equiv> \<forall>u \<in> worlds M. valuation M u = valuation M' (f u)"

text\<open>

If two worlds are related in @{term "M"}, then the simulation
maps them to related worlds in @{term "M'"}; intuitively the
simulation relates enough worlds. We term this the \emph{forward}
property.

\<close>

definition
  sim_f :: "('a, 'p, 'w1) KripkeStructure
         \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_f M M' f \<equiv>
     \<forall>a u v. (u, v) \<in> relations M a \<longrightarrow> (f u, f v) \<in> relations M' a"

text\<open>

Conversely, if two worlds @{term "f u"} and @{term "v'"} are related
in @{term "M'"}, then there is a pair of related worlds @{term "u"}
and @{term "v"} in @{term "M"} where @{term "f v = v'"}. Intuitively
the simulation makes enough distinctions. We term this the
\emph{reverse} property.

\<close>

definition
  sim_r :: "('a, 'p, 'w1) KripkeStructure
         \<Rightarrow> ('a, 'p, 'w2) KripkeStructure \<Rightarrow> ('w1 \<Rightarrow> 'w2) \<Rightarrow> bool"
where
  "sim_r M M' f \<equiv> \<forall>a. \<forall>u \<in> worlds M. \<forall>v'.
              (f u, v') \<in> relations M' a
           \<longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v')"

definition "sim M M' f \<equiv> sim_range M M' f \<and> sim_val M M' f
                       \<and> sim_f M M' f \<and> sim_r M M' f"
(*<*)

lemma sim_rangeI[intro]:
  "\<lbrakk> worlds M' = f ` worlds M; (\<And>a. relations M' a \<subseteq> worlds M' \<times> worlds M') \<rbrakk>
     \<Longrightarrow> sim_range M M' f"
  unfolding sim_range_def by simp

lemma sim_valI[intro]:
  "(\<And>u. u \<in> worlds M \<Longrightarrow> valuation M u = valuation M' (f u))
   \<Longrightarrow> sim_val M M' f"
  unfolding sim_val_def by simp

lemma sim_fI[intro]:
  "(\<And>a u v. (u, v) \<in> relations M a \<Longrightarrow> (f u, f v) \<in> relations M' a)
   \<Longrightarrow> sim_f M M' f"
  unfolding sim_f_def by simp

lemma sim_fD:
  "\<lbrakk> (u, v) \<in> relations M a; sim M M' f \<rbrakk>
     \<Longrightarrow> (f u, f v) \<in> relations M' a"
  unfolding sim_def sim_f_def by blast

lemma sim_rI[intro]:
  "(\<And>a u v'.
    \<lbrakk>u \<in> worlds M; (f u, v') \<in> relations M' a\<rbrakk>
    \<Longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v'))
  \<Longrightarrow> sim_r M M' f"
  unfolding sim_r_def by simp

lemma sim_rD:
  "\<lbrakk> (f u, v') \<in> relations M' a; sim M M' f; u \<in> worlds M \<rbrakk>
     \<Longrightarrow> (\<exists>v. (u, v) \<in> relations M a \<and> f v = v')"
  unfolding sim_def sim_r_def by blast

lemma simI[intro]:
  "\<lbrakk> sim_range M M' f; sim_val M M' f; sim_f M M' f; sim_r M M' f \<rbrakk>
     \<Longrightarrow> sim M M' f"
  unfolding sim_def by simp

text\<open>The identity is a simulation:\<close>

lemma sim_id: "kripke M \<Longrightarrow> sim M M id"
(*<*)
  unfolding sim_def sim_r_def sim_f_def sim_range_def sim_val_def
  by auto
(*>*)

(*>*)

text\<open>

Due to the common knowledge modality, we need to show the simulation
properties lift through the transitive closure. In particular we can
show that forward simulation is preserved:

\<close>

lemma sim_f_tc:
  assumes s: "sim M M' f"
  assumes uv': "(u, v) \<in> (\<Union>a\<in>as. relations M a)\<^sup>+"
  shows "(f u, f v) \<in> (\<Union>a\<in>as. relations M' a)\<^sup>+"
(*<*)
  using assms
  by - ( induct rule: trancl_induct[OF uv']
       , auto dest: sim_fD intro: trancl_into_trancl )
(*>*)
text\<open>

Reverse simulation also:

\<close>

lemma sim_r_tc:
  assumes M: "kripke M"
  assumes s: "sim M M' f"
  assumes u: "u \<in> worlds M"
  assumes fuv': "(f u, v') \<in> (\<Union>a\<in>as. relations M' a)\<^sup>+"
  obtains v where "f v = v'" and "(u, v) \<in> (\<Union>a\<in>as. relations M a)\<^sup>+"
(*<*)
proof -
  assume E: "\<And>v. \<lbrakk>f v = v'; (u, v) \<in> (\<Union>a\<in>as. relations M a)\<^sup>+\<rbrakk> \<Longrightarrow> thesis"

  from fuv' have as_nempty: "as \<noteq> {}" by auto
  from fuv' have "\<exists>v. f v = v' \<and> (u, v) \<in> (\<Union>a\<in>as. relations M a)\<^sup>+"
  proof(induct rule: trancl_induct)
    case (base v') with u s as_nempty show ?case
      by (blast dest: sim_rD)
  next
    case (step v' w')
    hence fuv': "(f u, v') \<in> (\<Union>a\<in>as. relations M' a)\<^sup>+"
      and v'w': "(v', w') \<in> (\<Union>a\<in>as. relations M' a)" by fast+
    from step
    obtain v where vv': "f v = v'"
               and uv: "(u, v) \<in> (\<Union>a\<in>as. relations M a)\<^sup>+"
      by blast
    from s v'w' vv' kripke_tc_rels_worlds[OF uv M]
    obtain w where ww': "f w = w'"
               and vw: "(v, w) \<in> (\<Union>a\<in>as. relations M a)"
      by (blast dest: sim_rD)
    from uv vw ww' show ?case by (blast intro: trancl_trans)
  qed
  with E show thesis by blast
qed

lemma sim_f_trc:
  assumes uv': "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
      and s: "sim M M' f"
  shows "(f u, f v) \<in> (\<Union>a. relations M' a)\<^sup>*"
  using assms
  by - ( induct rule: rtrancl_induct[OF uv']
       , auto dest: sim_fD intro: rtrancl_into_rtrancl )

lemma sim_r_trc:
  assumes s: "sim M M' f"
      and fuv': "(f u, v') \<in> (\<Union>a. relations M' a)\<^sup>*"
      and M: "kripke M"
      and u: "u \<in> worlds M"
  obtains v
    where "f v = v'"
      and "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
proof -
  assume E: "\<And>v. \<lbrakk>f v = v'; (u, v) \<in> (\<Union>a. relations M a)\<^sup>*\<rbrakk> \<Longrightarrow> thesis"
  from fuv' have "\<exists>v. f v = v' \<and> (u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
  proof(induct rule: rtrancl_induct)
    case base show ?case by blast
  next
    case (step v' w')
    hence fuv': "(f u, v') \<in> (\<Union>a. relations M' a)\<^sup>*"
      and v'w': "(v', w') \<in> (\<Union>a. relations M' a)" by fast+
    from step
    obtain v where vv': "f v = v'"
               and uv: "(u, v) \<in> (\<Union>a. relations M a)\<^sup>*"
      by blast
    from s v'w' vv' kripke_rels_trc_worlds[OF uv u M]
    obtain w where ww': "f w = w'"
               and vw: "(v, w) \<in> (\<Union>a. relations M a)"
      by (blast dest: sim_rD)
    from uv vw ww' show ?case by (blast intro: rtrancl_trans)
  qed
  with E show thesis by blast
qed

lemma sim_trc_commute:
  assumes M: "kripke M"
      and s: "sim M M' f"
      and t: "t \<in> worlds M"
  shows "f ` ((\<Union>a. relations M a)\<^sup>* `` {t})
       = (\<Union>a. relations M' a)\<^sup>* `` {f t}" (is "?lhs = ?rhs")
proof
  from M s show "?lhs \<subseteq> ?rhs" by (auto intro: sim_f_trc)
next
  from M s t show "?rhs \<subseteq> ?lhs" by (auto elim: sim_r_trc)
qed

lemma sim_kripke: "\<lbrakk> sim M M' f; kripke M \<rbrakk> \<Longrightarrow> kripke M'"
  unfolding sim_def sim_range_def by (rule kripkeI, blast)

lemma sim_S5n:
  assumes S5n: "S5n M"
      and sim: "sim M M' f"
  shows "S5n M'"
proof(intro S5nI equivI)
  fix a from S5n sim show "refl_on (worlds M') (relations M' a)"
     using sim_kripke S5n_kripke
     unfolding S5n_def equiv_def sim_def sim_f_def sim_range_def
     by - (rule refl_onI, (simp, blast dest: refl_onD)+)
next
  fix a
  { fix u v assume uv: "(u, v) \<in> relations M' a"
    from sim uv
    obtain u' where uw: "u' \<in> worlds M"
                and fu: "u = f u'"
      unfolding sim_def sim_range_def by bestsimp
    from sim uv fu uw
    obtain v' where u'v': "(u', v') \<in> relations M a"
                and fv: "v = f v'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n u'v' have "(v', u') \<in> relations M a"
      unfolding S5n_def equiv_def by (blast dest: symD)
    with sim fu fv have "(v, u) \<in> relations M' a"
      unfolding sim_def sim_f_def by simp }
  thus "sym (relations M' a)" by (blast intro: symI)
next
  fix a
  { fix x y z
    assume xy: "(x, y) \<in> relations M' a"
       and yz: "(y, z) \<in> relations M' a"
    from sim xy
    obtain x' where xw: "x' \<in> worlds M"
                and fx: "x = f x'"
      unfolding sim_def sim_range_def by bestsimp
    from sim xy fx xw
    obtain y' where x'y': "(x', y') \<in> relations M a"
                and fy: "y = f y'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n sim yz fy x'y'
    obtain z' where y'z': "(y', z') \<in> relations M a"
                and fz: "z = f z'"
      unfolding sim_def sim_r_def sim_range_def by best
    from S5n x'y' y'z' have "(x', z') \<in> relations M a"
      unfolding S5n_def equiv_def by (blast dest: transD)
    with sim fx fy fz have "(x, z) \<in> relations M' a"
      unfolding sim_def sim_f_def by simp }
  thus "trans (relations M' a)" by (blast intro: transI)
qed

(*>*)
text\<open>

Finally we establish the key property of simulations, that they
preserve the satisfaction of all formulas in the following way:

\<close>

lemma sim_semantic_equivalence:
  assumes M: "kripke M"
  assumes s: "sim M M' f"
  assumes u: "u \<in> worlds M"
  shows "M, u \<Turnstile> \<phi> \<longleftrightarrow> M', f u \<Turnstile> \<phi>"
(*<*)
using u
proof(induct \<phi> arbitrary: u)
  case (Kknows a \<psi> u)
  hence u: "u \<in> worlds M" by fast
  show ?case
  proof
    assume lhs: "M, u \<Turnstile> Kknows a \<psi>"
    { fix v' assume "(f u, v') \<in> relations M' a"
      with s u obtain v where uv:  "(u, v) \<in> relations M a"
                          and vv': "f v = v'"
        by (blast dest: sim_rD)
      from lhs uv have "M, v \<Turnstile> \<psi>" by simp
      with kripke_rels_worlds[OF uv M] vv' Kknows
      have "M', v' \<Turnstile> \<psi>" by auto }
    thus "M', f u \<Turnstile> Kknows a \<psi>" by simp
  next
    assume rhs: "M', f u \<Turnstile> Kknows a \<psi>"
    { fix v assume uv: "(u, v) \<in> relations M a"
      with s have "(f u, f v) \<in> relations M' a"
        by (blast dest: sim_fD)
      with rhs have "M', f v \<Turnstile> \<psi>" by simp
      with kripke_rels_worlds[OF uv M] Kknows s
      have "M, v \<Turnstile> \<psi>" by auto }
    thus "M, u \<Turnstile> Kknows a \<psi>" by simp
  qed
next
  case (Kcknows as \<psi>)
  hence u: "u \<in> worlds M" by fast
  show ?case
  proof
    assume lhs: "M, u \<Turnstile> Kcknows as \<psi>"
    { fix v' assume "(f u, v') \<in> (\<Union>x\<in>set as. relations M' x)\<^sup>+"
      with M s u
      obtain v where uv:  "(u, v) \<in> (\<Union>x\<in>set as. relations M x)\<^sup>+"
                and vv': "f v = v'"
        by (blast intro: sim_r_tc)
      from uv lhs have "M, v \<Turnstile> \<psi>" by simp
      with kripke_tc_rels_worlds[OF uv M] vv' Kcknows
      have "M', v' \<Turnstile> \<psi>" by auto }
    thus "M', f u \<Turnstile> Kcknows as \<psi>" by simp
  next
    assume rhs: "M', f u \<Turnstile> Kcknows as \<psi>"
    { fix v assume uv: "(u, v) \<in> (\<Union>x\<in>set as. relations M x)\<^sup>+"
      with s have "(f u, f v) \<in> (\<Union>x\<in>set as. relations M' x)\<^sup>+"
        by (blast dest: sim_f_tc)
      with rhs have "M', f v \<Turnstile> \<psi>" by simp
      with kripke_tc_rels_worlds[OF uv M] Kcknows s
      have "M, v \<Turnstile> \<psi>" by auto }
    thus "M, u \<Turnstile> Kcknows as \<psi>" by simp
  qed
qed (insert s,
     auto simp add: sim_range_def sim_def sim_val_def)
(*>*)

text\<open>

The proof is by structural induction over the formula @{term "\<phi>"}. The
knowledge cases appeal to our two simulation preservation lemmas.

\citet{DBLP:journals/toplas/Sangiorgi09} surveys the history of
p-morphisms and the related concept of \emph{bisimulation}.

This is all we need to know about Kripke structures.

\<close>

(*<*)
end
(*>*)
