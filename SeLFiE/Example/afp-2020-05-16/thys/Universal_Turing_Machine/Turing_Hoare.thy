(* Title: thys/Turing_Hoare.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
*)

chapter \<open>Hoare Rules for TMs\<close>

theory Turing_Hoare
  imports Turing
begin


type_synonym assert = "tape \<Rightarrow> bool"

definition 
  assert_imp :: "assert \<Rightarrow> assert \<Rightarrow> bool" ("_ \<mapsto> _" [0, 0] 100)
  where
    "P \<mapsto> Q \<equiv> \<forall>l r. P (l, r) \<longrightarrow> Q (l, r)"

lemma refl_assert[intro, simp]:
  "P \<mapsto> P"
  unfolding assert_imp_def by simp

fun 
  holds_for :: "(tape \<Rightarrow> bool) \<Rightarrow> config \<Rightarrow> bool" ("_ holds'_for _" [100, 99] 100)
  where
    "P holds_for (s, l, r) = P (l, r)"  

lemma is_final_holds[simp]:
  assumes "is_final c"
  shows "Q holds_for (steps c p n) = Q holds_for c"
  using assms 
  by(induct n;cases c,auto)

(* Hoare Rules *)

(* halting case *)
definition
  Hoare_halt :: "assert \<Rightarrow> tprog0 \<Rightarrow> assert \<Rightarrow> bool" ("({(1_)}/ (_)/ {(1_)})" 50)
  where
    "{P} p {Q} \<equiv> (\<forall>tp. P tp \<longrightarrow> (\<exists>n. is_final (steps0 (1, tp) p n) \<and> Q holds_for (steps0 (1, tp) p n)))"

(* not halting case *)
definition
  Hoare_unhalt :: "assert \<Rightarrow> tprog0 \<Rightarrow> bool" ("({(1_)}/ (_)) \<up>" 50)
  where
    "{P} p \<up> \<equiv> \<forall>tp. P tp \<longrightarrow> (\<forall> n . \<not> (is_final (steps0 (1, tp) p n)))"


lemma Hoare_haltI:
  assumes "\<And>l r. P (l, r) \<Longrightarrow> \<exists>n. is_final (steps0 (1, (l, r)) p n) \<and> Q holds_for (steps0 (1, (l, r)) p n)"
  shows "{P} p {Q}"
  unfolding Hoare_halt_def 
  using assms by auto

lemma Hoare_unhaltI:
  assumes "\<And>l r n. P (l, r) \<Longrightarrow> \<not> is_final (steps0 (1, (l, r)) p n)"
  shows "{P} p \<up>"
  unfolding Hoare_unhalt_def 
  using assms by auto




text \<open>
  {P} A {Q}   {Q} B {S}  A well-formed
  -----------------------------------------
  {P} A |+| B {S}
\<close>


lemma Hoare_plus_halt [case_names A_halt B_halt A_wf]: 
  assumes A_halt : "{P} A {Q}"
    and B_halt : "{Q} B {S}"
    and A_wf : "tm_wf (A, 0)"
  shows "{P} A |+| B {S}"
proof(rule Hoare_haltI)
  fix l r
  assume h: "P (l, r)"
  then obtain n1 l' r' 
    where "is_final (steps0 (1, l, r) A n1)"  
      and a1: "Q holds_for (steps0 (1, l, r) A n1)"
      and a2: "steps0 (1, l, r) A n1 = (0, l', r')"
    using A_halt unfolding Hoare_halt_def
    by (metis is_final_eq surj_pair) 
  then obtain n2 
    where "steps0 (1, l, r) (A |+| B) n2 = (Suc (length A div 2), l', r')"
    using A_wf by (rule_tac tm_comp_next) 
  moreover
  from a1 a2 have "Q (l', r')" by (simp)
  then obtain n3 l'' r''
    where "is_final (steps0 (1, l', r') B n3)" 
      and b1: "S holds_for (steps0 (1, l', r') B n3)"
      and b2: "steps0 (1, l', r') B n3 = (0, l'', r'')"
    using B_halt unfolding Hoare_halt_def 
    by (metis is_final_eq surj_pair) 
  then have "steps0 (Suc (length A div 2), l', r')  (A |+| B) n3 = (0, l'', r'')"
    using A_wf by (rule_tac tm_comp_final) 
  ultimately show 
    "\<exists>n. is_final (steps0 (1, l, r) (A |+| B) n) \<and> S holds_for (steps0 (1, l, r) (A |+| B) n)"
    using b1 b2 by (rule_tac x = "n2 + n3" in exI) (simp)
qed

text \<open>
  {P} A {Q}   {Q} B loops   A well-formed
  ------------------------------------------
          {P} A |+| B  loops
\<close>

lemma Hoare_plus_unhalt [case_names A_halt B_unhalt A_wf]:
  assumes A_halt: "{P} A {Q}"
    and B_uhalt: "{Q} B \<up>"
    and A_wf : "tm_wf (A, 0)"
  shows "{P} (A |+| B) \<up>"
proof(rule_tac Hoare_unhaltI)
  fix n l r 
  assume h: "P (l, r)"
  then obtain n1 l' r'
    where a: "is_final (steps0 (1, l, r) A n1)" 
      and b: "Q holds_for (steps0 (1, l, r) A n1)"
      and c: "steps0 (1, l, r) A n1 = (0, l', r')"
    using A_halt unfolding Hoare_halt_def 
    by (metis is_final_eq surj_pair) 
  then obtain n2 where eq: "steps0 (1, l, r) (A |+| B) n2 = (Suc (length A div 2), l', r')"
    using A_wf by (rule_tac tm_comp_next)
  then show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)"
  proof(cases "n2 \<le> n")
    case True
    from b c have "Q (l', r')" by simp
    then have "\<forall> n. \<not> is_final (steps0 (1, l', r') B n)  "
      using B_uhalt unfolding Hoare_unhalt_def by simp
    then have "\<not> is_final (steps0 (1, l', r') B (n - n2))" by auto
    then obtain s'' l'' r'' 
      where "steps0 (1, l', r') B (n - n2) = (s'', l'', r'')" 
        and "\<not> is_final (s'', l'', r'')" by (metis surj_pair)
    then have "steps0 (Suc (length A div 2), l', r') (A |+| B) (n - n2) = (s''+ length A div 2, l'', r'')"
      using A_wf by (auto dest: tm_comp_second simp del: tm_wf.simps)
    then have "\<not> is_final (steps0 (1, l, r) (A |+| B) (n2 + (n  - n2)))"
      using A_wf by (simp only: steps_add eq) simp
    then show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)" 
      using \<open>n2 \<le> n\<close> by simp
  next 
    case False
    then obtain n3 where "n = n2 - n3"
      using diff_le_self le_imp_diff_is_add nat_le_linear
        add.commute by metis
    moreover
    with eq show "\<not> is_final (steps0 (1, l, r) (A |+| B) n)"
      by (simp add: not_is_final[where ?n1.0="n2"])
  qed
qed

lemma Hoare_consequence:
  assumes "P' \<mapsto> P" "{P} p {Q}" "Q \<mapsto> Q'"
  shows "{P'} p {Q'}"
  using assms
  unfolding Hoare_halt_def assert_imp_def
  by (metis holds_for.simps surj_pair)



end