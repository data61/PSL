subsection\<open>Resolution\<close>
theory Resolution
imports CNF "HOL-Library.While_Combinator"
begin

text\<open>Resolution is different from the other proof systems:
  its derivations do not represent proofs in the way the other systems do.
  Rather, they represent invariant additions (under satisfiability) to set of clauses.\<close>
inductive Resolution :: "'a literal set set \<Rightarrow> 'a literal set \<Rightarrow> bool" ("_ \<turnstile> _" [30] 28) where
Ass: "C \<in> S \<Longrightarrow> S \<turnstile> C" |
R: "S \<turnstile> C \<Longrightarrow> S \<turnstile> D \<Longrightarrow> k\<^sup>+ \<in> C \<Longrightarrow> k\<inverse> \<in> D \<Longrightarrow> S \<turnstile> (C - {k\<^sup>+}) \<union> (D - {k\<inverse>})"
text\<open>The problematic part of this formulation is that we can't talk about a "Resolution Refutation" in an inductive manner. 
  In the places where Gallier's proofs~\cite{gallier2015logic} do that, we have to work around that.\<close>

lemma Resolution_weaken: "S \<turnstile> D \<Longrightarrow> T \<union> S \<turnstile> D"
  by(induction rule: Resolution.induct; auto intro: Resolution.intros)

lemma Resolution_unnecessary:
  assumes sd: "\<forall>C \<in> T. S \<turnstile> C"
  shows "T \<union> S \<turnstile> D \<longleftrightarrow> S \<turnstile> D" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?l
  from \<open>?l\<close> sd show  ?r
  proof(induction "T \<union> S" D rule: Resolution.induct)
    case (Ass D)
    show ?case proof cases
      assume "D \<in> S" with Resolution.Ass show ?thesis .
    next
      assume "D \<notin> S"
      with Ass.hyps have "D \<in> T" by simp
      with Ass.prems show ?thesis by blast
    qed
  next
    case (R D H k) thus ?case by (simp add: Resolution.R)
  qed
next
  assume ?r with Resolution_weaken show ?l by blast
qed

lemma Resolution_taint_assumptions: "S \<union> T \<turnstile> C \<Longrightarrow> \<exists>R \<subseteq> D. ((\<union>) D ` S) \<union> T \<turnstile> R \<union> C"
(* No, we don't need to show this for an arbitrary clause D, but the proof doesn't get any more readable if you only allow a single atom. *)
proof(induction "S \<union> T" "C" rule: Resolution.induct)
 case (Ass C)
  show ?case proof(cases "C \<in> S")
    case True
    hence "D \<union> C \<in> (\<union>) D ` S \<union> T" by simp
    with Resolution.Ass have "((\<union>) D ` S) \<union> T \<turnstile> D \<union> C" .
    thus ?thesis by blast
  next
    case False
    with Ass have "C \<in> T" by simp
    hence "((\<union>) D ` S) \<union> T \<turnstile> C" by(simp add: Resolution.Ass)
    thus ?thesis by(intro exI[where x="{}"]) simp
  qed
next
  case (R C1 C2 k)
  let ?m = "((\<union>) D ` S) \<union> T"
  from R obtain R1 where IH1: "R1 \<subseteq> D" "?m \<turnstile> R1 \<union> C1" by blast
  from R obtain R2 where IH2: "R2 \<subseteq> D" "?m \<turnstile> R2 \<union> C2" by blast
  from R have "k\<^sup>+ \<in> R1 \<union> C1" "k\<inverse> \<in> R2 \<union> C2" by simp_all
  note Resolution.R[OF IH1(2) IH2(2) this]
  hence "?m \<turnstile> (R1 - {k\<^sup>+}) \<union> (R2 - {k\<inverse>}) \<union> (C1 - {k\<^sup>+} \<union> (C2 - {k\<inverse>}))"
    by (simp add: Un_Diff Un_left_commute sup.assoc)
  moreover have "(R1 - {k\<^sup>+}) \<union> (R2 - {k\<inverse>}) \<subseteq> D" (* hah\<triangleright> gotcha. This is the reason that I should be doing this on sets\<triangleright> not multisets. - neh, actually, there are others. how is the rule even supposed to look? *)
    using IH1(1) IH2(1) by blast
  ultimately show ?case by blast
qed

text\<open>Resolution is ``strange'':
Given a set of clauses that is presumed to be satisfiable,
it derives new clauses that can be added while preserving the satisfiability of the set of clauses.
However, not every clause that could be added while keeping satisfiability can actually be added by resolution.
Especially, the above lemma \<open>Resolution_taint_assumptions\<close> gives us the derivability of a clause
@{term "R \<union> C"}, where @{term "R \<subseteq> D"}. What we might actually want is the derivability of 
@{term "D \<union> C"}. Any model that satisfies @{term "R \<union> C"} obviously satisfies @{term "D \<union> C"} 
(since they are disjunctions), but Resolution only allows to derive the former.
\<close>
text\<open>Nevertheless, \<open>Resolution_taint_assumptions\<close>, can still be a quite useful lemma:
picking @{term D} to be a singleton set only leaves two possibilities for @{term R}.\<close>

lemma Resolution_useless_infinite:
assumes R: "S \<turnstile> R"
assumes "finite R"
shows "\<exists>S' \<subseteq> S. Ball S' finite \<and> finite S' \<and> (S' \<turnstile> R)"
using assms proof(induction rule: Resolution.induct)
  case (Ass C S) thus ?case using Resolution.Ass by(intro exI[where x="{C}"]) auto
next
  case (R S C D k)
  from R.prems have "finite C" "finite D" by simp_all
  with R.IH obtain SC SD where IH:
    "SC\<subseteq>S" "(\<forall>C\<in>SC. finite C)" "finite SC" "SC \<turnstile> C"
    "SD\<subseteq>S" "(\<forall>D\<in>SD. finite D)" "finite SD" "SD \<turnstile> D"
    by blast
  hence IHw: "SC \<union> SD \<turnstile> C" "SC \<union> SD \<turnstile> D" using Resolution_weaken 
    by(simp_all add: sup_commute Resolution_weaken (* yes, using and simp set. whatever. *))
  with IH(1-3,5-7) show ?case
    by(blast intro!: exI[where x="SC \<union> SD"] Resolution.R[OF _ _ \<open>k\<^sup>+ \<in> C\<close> \<open>k\<inverse> \<in> D\<close>])
qed
(* situation would be different if we allowed to resolve an infinite amount of literals in one step instead of just one.
   And I think that's exactly the reason why one doesn't do that.
 *)

text\<open>Now we define and verify a toy resolution prover.
Function \<open>res\<close> computes the set of resolvents of a clause set:\<close>
context begin

definition res :: "'a clause set \<Rightarrow> 'a clause set" where
"res S =
 (\<Union>C1 \<in> S. \<Union>C2 \<in> S. \<Union>L1 \<in> C1. \<Union>L2 \<in> C2.
 (case (L1,L2) of (Pos i,Neg j) \<Rightarrow> if i=j then {(C1 - {Pos i}) \<union> (C2 - {Neg j})} else {}
  | _ \<Rightarrow> {}))"

private definition "ex1 \<equiv> {{Neg (0::int)}, {Pos 0, Pos 1, Neg 2}, {Pos 0, Pos 1, Pos 2}, {Pos 0, Neg 1}}"
value "res ex1"
  
(* now we want to iterate res. We've got two options. Either use the while combinator,
   which is not so beautiful to present but easy to understand, or use partial_function magic,
  which looks beautiful, but\<dots> magic. The ML kind. *)

definition Rwhile ::" 'a clause set \<Rightarrow> 'a clause set option" where
"Rwhile = while_option (\<lambda>S. \<box> \<notin> S \<and> \<not> res S \<subseteq> S) (\<lambda>S. res S \<union> S)"

value [code] "Rwhile ex1"
lemma "\<box> \<in> the (Rwhile ex1)" by eval

lemma Rwhile_sound: assumes "Rwhile S = Some S'"
  shows "\<forall>C \<in> S'. Resolution S C"
apply(rule while_option_rule[OF _ assms[unfolded Rwhile_def]])
apply (auto simp: Ass R res_def split: if_splits literal.splits)
done

definition "all_clauses S = {s. s \<subseteq> {Pos k|k. k \<in> atoms_of_cnf S} \<union> {Neg k|k. k \<in> atoms_of_cnf S}}"
lemma s_sub_all_clauses: "S \<subseteq> all_clauses S"
  unfolding all_clauses_def
  apply(rule)
  apply(simp)
  apply(rule)
  apply(simp add: atoms_of_cnf_alt lit_atoms_cases[abs_def])
  by (metis imageI literal.exhaust literal.simps(5) literal.simps(6))
lemma atoms_res: "atoms_of_cnf (res S) \<subseteq>  atoms_of_cnf S"
  unfolding res_def atoms_of_cnf_alt
  apply (clarsimp simp: lit_atoms_cases [abs_def] split: literal.splits if_splits)
  apply (clarsimp simp add: image_iff)
  apply force
  done

lemma exlitE: "(\<And>x. xe = Pos x \<Longrightarrow> P x) \<Longrightarrow> (\<And>x. xe = Neg x \<Longrightarrow> False) \<Longrightarrow> \<exists>x. xe = Pos x \<and> P x"
  by(cases xe) auto
lemma res_in_all_clauses: "res S \<subseteq> all_clauses S"
  apply (clarsimp simp: res_def all_clauses_def atoms_of_cnf_alt lit_atoms_cases
    split: literal.splits if_splits)
  apply (clarsimp simp add: image_iff)
  apply (metis atoms_of_lit.simps(1) atoms_of_lit.simps(2) lit_atoms_cases literal.exhaust)
  done

lemma Res_in_all_clauses: "res S \<union> S \<subseteq> all_clauses S"
  by (simp add: res_in_all_clauses s_sub_all_clauses)  
lemma all_clauses_Res_inv: "all_clauses (res S \<union> S) = all_clauses S"
  unfolding all_clauses_def atoms_of_cnf_Un
  using atoms_res by fast
lemma all_clauses_finite: "finite S \<and> (\<forall>C \<in> S. finite C) \<Longrightarrow> finite (all_clauses S)"
  unfolding all_clauses_def atoms_of_cnf_def by simp
lemma finite_res: "\<forall>C \<in> S. finite C \<Longrightarrow> \<forall>C \<in> res S. finite C"
  unfolding res_def by(clarsimp split: literal.splits)

lemma "finite T \<Longrightarrow> S \<subseteq> T \<Longrightarrow> card S < Suc (card T)"
  by (simp add: card_mono le_imp_less_Suc)
    
lemma "finite S \<and> (\<forall>C \<in> S. finite C) \<Longrightarrow> \<exists>T. Rwhile S = Some T"
  apply(unfold Rwhile_def)
  apply(rule measure_while_option_Some[rotated, where f="\<lambda>T. Suc (card (all_clauses S)) - card T"
        and P="\<lambda>T. finite T \<and> (\<forall>C \<in> T. finite C) \<and> all_clauses T = all_clauses S"])
   apply(simp;fail)
  apply(intro conjI)
     subgoal by (meson all_clauses_finite finite_UnI finite_subset res_in_all_clauses)
    subgoal using finite_res by blast
   subgoal using all_clauses_Res_inv by blast
  subgoal 
    apply(rule diff_less_mono2)
     subgoal by (metis Res_in_all_clauses all_clauses_finite card_seteq finite_subset not_le sup_commute sup_ge2)
    subgoal apply(intro card_mono le_imp_less_Suc)
      subgoal using all_clauses_finite by blast
      subgoal using s_sub_all_clauses by blast
    done
  done
done

partial_function(option) Res where
"Res S = (let R = res S \<union> S in if R = S then Some S else Res R)"
declare Res.simps[code]

value [code] "Res ex1"
lemma "\<box> \<in> the (Res ex1)" by code_simp

lemma res: "C \<in> res S \<Longrightarrow> S \<turnstile> C"
  unfolding res_def by(auto split: literal.splits if_splits) (metis Resolution.simps literal.exhaust)    

lemma Res_sound: "Res S = Some S' \<Longrightarrow> (\<forall>C \<in> S'. S \<turnstile> C)"
proof (induction arbitrary: S S' rule: Res.fixp_induct)
  fix X S S'
  assume IH: "\<And>S S'. X S = Some S' \<Longrightarrow> (\<forall>C\<in>S'. S \<turnstile> C)"
  assume prem: "(let R = res S \<union> S in if R = S then Some S else X R) = Some S'"
  thus "(\<forall>C\<in>S'. S \<turnstile> C)"
  proof cases
    assume "res S \<union> S = S"
    with prem show ?thesis by (simp add: Resolution.Ass)
  next
    assume 1: "res S \<union> S \<noteq> S"
    with prem have "X (res S \<union> S) = Some S'" by simp
    with IH have "\<forall>C\<in>S'. res S \<union> S \<turnstile> C" by blast
    thus ?thesis using Resolution_unnecessary res by blast (* this needs the generalized Resolution_unnecessary lemma. And I don't get why the option-variant didn't. *)
  qed
qed (fast intro!: option_admissible)+

lemma Res_terminates: "finite S \<Longrightarrow> \<forall>C \<in> S. finite C \<Longrightarrow> \<exists>T. Res S = Some T"
proof(induction "card (all_clauses S) - card S" arbitrary: S rule: less_induct) (* can be done by induction on "card (all_clauses S - S)", but I found that to be more annoying. *)
  case less
  let ?r = "res S \<union> S"
  show ?case proof(cases "?r = S")
    case False
    have b: "finite (res S \<union> S)" by (meson less Res_in_all_clauses all_clauses_finite infinite_super)
    have c: "Ball (res S \<union> S) finite" using less.prems(2) finite_res by auto
    have "card S < card ?r" by (metis False b psubsetI psubset_card_mono sup_ge2)
    moreover have "card ?r \<le> (card (all_clauses S))"
      by (meson less Res_in_all_clauses all_clauses_finite card_mono le_imp_less_Suc)
    ultimately have a: "(card (all_clauses ?r)) - card ?r < (card (all_clauses S)) - card S" 
      using all_clauses_Res_inv[of S] by simp
    from less(1)[OF a b c] show ?thesis by (subst Res.simps) (simp add: Let_def)
  qed (simp add: Res.simps)
qed
  
(* just to demonstrate, this would not work: *)
code_pred (*(modes: i \<Rightarrow> i \<Rightarrow> bool)*) Resolution . (* can't infer any modes. *)
print_theorems (* doesn't generate any theorems either. *)

end
end
