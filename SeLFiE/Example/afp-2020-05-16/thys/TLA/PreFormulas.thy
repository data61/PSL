(*  Title:       A Definitional Encoding of TLA in Isabelle/HOL
    Authors:     Gudmund Grov <ggrov at inf.ed.ac.uk>
                 Stephan Merz <Stephan.Merz at loria.fr>
    Year:        2011
    Maintainer:  Gudmund Grov <ggrov at inf.ed.ac.uk>
*)

section "Reasoning about PreFormulas"

theory PreFormulas  
imports Semantics
begin

text\<open>
  Semantic separation of formulas and pre-formulas requires a deep embedding.
  We introduce a syntactically distinct notion of validity, written \<open>|~ A\<close>,
  for pre-formulas. Although it is semantically identical to \<open>\<turnstile> A\<close>, it
  helps users distinguish pre-formulas from formulas in \tlastar{} proofs.
\<close>

definition PreValid :: "('w::world) form \<Rightarrow> bool"
where "PreValid A \<equiv> \<forall> w. w \<Turnstile> A"

syntax
  "_PreValid"      :: "lift \<Rightarrow> bool"     ("(|~ _)" 5)

translations
  "_PreValid"  \<rightleftharpoons> "CONST PreValid"

lemma prefD[dest]: "|~ A \<Longrightarrow> w \<Turnstile> A"
  by (simp add: PreValid_def)

lemma prefI[intro!]: "(\<And> w. w \<Turnstile> A) \<Longrightarrow> |~ A"
  by (simp add: PreValid_def)

method_setup pref_unlift = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD'
    (resolve_tac ctxt @{thms prefI} THEN' rewrite_goal_tac ctxt @{thms intensional_rews}))
\<close> "int_unlift for PreFormulas"

lemma prefeq_reflection: assumes P1: "|~ x=y" shows  "(x \<equiv> y)"
using P1 by (intro eq_reflection) force

lemma pref_True[simp]: "|~ #True"
  by auto

lemma pref_eq: "|~ X = Y \<Longrightarrow> X = Y"
  by (auto simp: prefeq_reflection)

lemma pref_iffI: 
  assumes "|~ F \<longrightarrow> G" and "|~ G \<longrightarrow> F"
  shows "|~ F = G"
  using assms by force

lemma pref_iffD1: assumes "|~ F = G" shows "|~ F \<longrightarrow> G"
  using assms by auto

lemma pref_iffD2: assumes "|~ F = G" shows "|~ G \<longrightarrow> F"
  using assms by auto

lemma unl_pref_imp: 
  assumes "|~ F \<longrightarrow> G" shows "\<And> w. w \<Turnstile> F \<Longrightarrow> w \<Turnstile> G"
  using assms by auto

lemma pref_imp_trans:
  assumes "|~ F \<longrightarrow> G" and "|~ G \<longrightarrow> H"
  shows "|~ F \<longrightarrow> H"
  using assms by force

subsection "Lemmas about \<open>Unchanged\<close>"

text \<open>
  Many of the \tlastar{} axioms only require a state function witness
  which leaves the state space unchanged. An obvious witness is the
  @{term id} function. The lemmas require that the given formula is
  invariant under stuttering.
\<close>

lemma pre_id_unch: assumes h: "stutinv F"
  shows "|~ F \<and> Unchanged id \<longrightarrow> \<circle>F"
proof (pref_unlift, clarify)
  fix s
  assume a1: "s \<Turnstile> F" and  a2: "s \<Turnstile> Unchanged id"
  from a2 have "(id (second s) = id (first s))" by (simp add: unch_defs)
  hence "s \<approx> (tail s)" by (simp add: addfirststut)
  with h a1 have "(tail s) \<Turnstile> F" by (simp add: stutinv_def)
  thus "s \<Turnstile> \<circle>F" by (unfold nexts_def)
qed

lemma pre_ex_unch: 
  assumes h: "stutinv F"
  shows "\<exists>(v::'a::world \<Rightarrow> 'a). ( |~ F \<and> Unchanged v \<longrightarrow> \<circle>F)"
using pre_id_unch[OF h] by blast

lemma unch_pair: "|~ Unchanged (x,y) = (Unchanged x \<and> Unchanged y)"
  by (auto simp: unch_def before_def after_def nexts_def)

lemmas unch_eq1 = unch_pair[THEN pref_eq]
lemmas unch_eq2 = unch_pair[THEN prefeq_reflection]

lemma angle_actrans_sem: "|~ \<langle>F\<rangle>_v = (F \<and> v$ \<noteq> $v)"
  by (auto simp: angle_actrans_def actrans_def unch_def)

lemmas angle_actrans_sem_eq = angle_actrans_sem[THEN pref_eq]

subsection "Lemmas about \<open>after\<close>"

lemma after_const: "|~ (#c)` = #c"
  by (auto simp: nexts_def before_def after_def)

lemma after_fun1: "|~ f<x>` = f<x`>"
  by (auto simp: nexts_def before_def after_def)

lemma after_fun2: "|~ f<x,y>` = f <x`,y`>"
  by (auto simp: nexts_def before_def after_def)

lemma after_fun3: "|~ f<x,y,z>` = f <x`,y`,z`>"
  by (auto simp: nexts_def before_def after_def)

lemma after_fun4: "|~ f<x,y,z,zz>` = f <x`,y`,z`,zz`>"
  by (auto simp: nexts_def before_def after_def)

lemma after_forall: "|~ (\<forall> x. P x)` = (\<forall> x. (P x)`)"
  by (auto simp: nexts_def before_def after_def)

lemma after_exists: "|~ (\<exists> x. P x)` = (\<exists> x. (P x)`)"
  by (auto simp: nexts_def before_def after_def)

lemma after_exists1: "|~ (\<exists>! x. P x)` = (\<exists>! x. (P x)`)"
  by (auto simp: nexts_def before_def after_def)

lemmas all_after = after_const after_fun1 after_fun2 after_fun3 after_fun4
  after_forall after_exists after_exists1 

lemmas all_after_unl = all_after[THEN prefD]
lemmas all_after_eq = all_after[THEN prefeq_reflection]

subsection "Lemmas about \<open>before\<close>"

lemma before_const: "\<turnstile> $(#c) = #c"
  by (auto simp: before_def)

lemma before_fun1: "\<turnstile> $(f<x>) = f <$x>"
  by (auto simp: before_def)

lemma before_fun2: "\<turnstile> $(f<x,y>) = f <$x,$y>"
  by (auto simp: before_def)

lemma before_fun3: "\<turnstile> $(f<x,y,z>) = f <$x,$y,$z>"
  by (auto simp: before_def)

lemma before_fun4: "\<turnstile> $(f<x,y,z,zz>) = f <$x,$y,$z,$zz>"
  by (auto simp: before_def)

lemma before_forall: "\<turnstile> $(\<forall> x. P x) = (\<forall> x. $(P x))"
  by (auto simp: before_def)

lemma before_exists: "\<turnstile> $(\<exists> x. P x) = (\<exists> x. $(P x))"
  by (auto simp: before_def)

lemma before_exists1: "\<turnstile> $(\<exists>! x. P x) = (\<exists>! x. $(P x))"
  by (auto simp: before_def)


lemmas all_before = before_const before_fun1 before_fun2 before_fun3 before_fun4
  before_forall before_exists before_exists1

lemmas all_before_unl = all_before[THEN intD]
lemmas all_before_eq = all_before[THEN inteq_reflection]

subsection "Some general properties"

lemma angle_actrans_conj: "|~ (\<langle>F \<and> G\<rangle>_v) = (\<langle>F\<rangle>_v \<and> \<langle>G\<rangle>_v)"
  by (auto simp: angle_actrans_def actrans_def unch_def)

lemma angle_actrans_disj: "|~ (\<langle>F \<or> G\<rangle>_v) = (\<langle>F\<rangle>_v \<or> \<langle>G\<rangle>_v)"
  by (auto simp: angle_actrans_def actrans_def unch_def)

lemma int_eq_true: "\<turnstile> P \<Longrightarrow> \<turnstile> P = #True"
  by auto

lemma pref_eq_true: "|~ P \<Longrightarrow> |~ P = #True"
  by auto

subsection "Unlifting attributes and methods"

text \<open>Attribute which unlifts an intensional formula or preformula\<close>
ML \<open>
fun unl_rewr ctxt thm = 
    let
       val unl = (thm RS @{thm intD}) handle THM _ => (thm RS @{thm prefD})
                                      handle THM _ => thm
       val rewr = rewrite_rule ctxt @{thms intensional_rews} 
     in
       unl |> rewr
     end;
\<close>
attribute_setup unlifted = \<open>
  Scan.succeed (Thm.rule_attribute [] (unl_rewr o Context.proof_of))
\<close> "unlift intensional formulas"

attribute_setup unlift_rule = \<open>
  Scan.succeed
    (Thm.rule_attribute []
      (Context.proof_of #> (fn ctxt => Object_Logic.rulify ctxt o unl_rewr ctxt)))
\<close> "unlift and rulify intensional formulas"


text \<open>
  Attribute which turns an intensional formula or preformula into a rewrite rule.
  Formulas \<open>F\<close> that are not equalities are turned into \<open>F \<equiv> #True\<close>.
\<close>
ML \<open>
fun int_rewr thm = 
   (thm RS @{thm inteq_reflection})
     handle THM _ => (thm RS @{thm prefeq_reflection})
     handle THM _ => ((thm RS @{thm int_eq_true}) RS @{thm inteq_reflection})
     handle THM _ => ((thm RS @{thm pref_eq_true}) RS @{thm prefeq_reflection});
\<close>

attribute_setup simp_unl = \<open>
    Attrib.add_del
      (Thm.declaration_attribute
        (fn th => Simplifier.map_ss (Simplifier.add_simp (int_rewr th))))
      (K (NONE, NONE))  (* note only adding -- removing is ignored *)
\<close> "add thm unlifted from rewrites from intensional formulas or preformulas"

attribute_setup int_rewrite = \<open>Scan.succeed (Thm.rule_attribute [] (fn _ => int_rewr))\<close>
  "produce rewrites from intensional formulas or preformulas"

end
