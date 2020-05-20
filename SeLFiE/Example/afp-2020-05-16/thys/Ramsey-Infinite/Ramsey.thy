
section "Ramsey's Theorem"

theory Ramsey
imports Main "HOL-Library.Infinite_Set"
begin


declare [[simp_depth_limit = 5]]

subsection "Library lemmas"

lemma infinite_inj_infinite_image: "infinite Z \<Longrightarrow> inj_on f Z \<Longrightarrow> infinite (f ` Z)"
  apply(rule ccontr)
  apply(simp)
  apply(force dest: finite_imageD)
  done

lemma infinite_dom_finite_rng: "[| infinite A; finite (f ` A) |] ==> \<exists>b \<in> f ` A. infinite {a : A. f a = b}"
  apply(rule ccontr) apply(simp)
  apply(subgoal_tac "\<Union>((\<lambda>b. {a : A. f a = f b}) ` A) = A") prefer 2 apply(blast)
  apply(subgoal_tac "(UN c : f ` A. {a : A. f a = c})= (UN b:A. {a : A. f a = f b})") prefer 2 apply(blast)
  apply(subgoal_tac "finite (UN c:f ` A. {a : A. f a = c})") apply(force) 
  apply(rule finite_UN_I)
  apply(auto)
  done

lemma infinite_mem: "infinite X \<Longrightarrow> \<exists>x. x \<in> X"
  apply(rule ccontr)
  apply(force)
  done

lemma not_empty_least: "(Y::nat set) \<noteq> {} \<Longrightarrow> \<exists>m. m \<in> Y \<and> (\<forall>m'. m' \<in> Y \<longrightarrow> m \<le> m')"
  apply(rule_tac x="LEAST x. x : Y" in exI)
  apply(rule)
  apply(rule LeastI_ex) apply(force)
  apply(rule)
  apply(rule)
  apply(rule Least_le)
  apply(assumption)
  done


subsection "Dependent Choice Variant"

  \<comment> \<open>%%cut choice\<close>
primrec choice :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a" where
  "choice P R 0 = (SOME x. P x)"
| "choice P R (Suc n) = (let x = choice P R n in SOME y. P y \<and> R x y)"
  \<comment> \<open>%%tuc\<close>

lemma dc: "
  (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z)
  \<and> (\<exists>x0. P x0)
  \<and> (\<forall>x. P x \<longrightarrow> (\<exists>y. P y \<and> R x y))
  \<longrightarrow> (\<exists>f::nat\<Rightarrow>'b. (\<forall>n. P (f n)) \<and> (\<forall>n m. R (f n) (f (n+m+1))))
 "
  apply(intro allI impI, elim exE conjE)
  apply(rule_tac x="choice P R" in exI)
  apply(subgoal_tac "(\<forall>n. P (choice P R n))") prefer 2
  apply(rule, induct_tac n)
  apply(simp add: Let_def) apply(rule someI_ex) apply(blast)
  apply(simp add: Let_def) apply(subgoal_tac "P (SOME y. P y \<and> R (choice P R na) y) \<and> R (choice P R na) (SOME y. P y \<and> R (choice P R na) y)") apply(blast) apply(rule someI_ex) apply(blast)
  apply(rule) apply(assumption)
  
  apply(subgoal_tac "\<forall>n. R (choice P R n) (choice P R (Suc n))") prefer 2
  apply(rule)
  apply(simp add: Let_def)
  apply(subgoal_tac "P (SOME y. P y \<and> R (choice P R n) y) \<and>  R (choice P R n) (SOME y. P y \<and> R (choice P R n) y)") apply(blast)
  apply(rule someI_ex) apply(force)

  apply(rule) apply(rule)
  apply(induct_tac m) 
  apply(force)
  apply(drule_tac x="n+na+1" in spec) back
  apply(force simp del: choice.simps)
  done


subsection "Partitions"

(* expect Y infinite *)
definition
  part :: "nat \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> ('a set \<Rightarrow> nat) \<Rightarrow> bool" where
  "part r s Y f = (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = r \<longrightarrow> f X < s)"

lemma part: "[| infinite YY; part (Suc n) s YY f; yy : YY |] ==> part n s (YY - {yy}) (\<lambda>u. f (insert yy u))"
  apply(simp add: part_def)
  apply(intro allI impI, elim exE conjE)
  apply(drule_tac x="insert yy X" in spec)
  apply(force simp:card_Diff_singleton_if)
  done

lemma part_subset: "part (Suc n) s YY f \<Longrightarrow> Y \<subseteq> YY \<Longrightarrow> part (Suc n) s Y f" 
  apply(simp add: part_def)
  apply(blast)
  done

  

subsection "Ramsey's theorem"

(* state theorem so it doesn't require part definition *)

lemma ramsey: "
  \<forall>(s::nat) (r::nat) (YY::'a set) (f::'a set \<Rightarrow> nat).
  infinite YY 
  \<and> (\<forall>X. X \<subseteq> YY \<and> finite X \<and> card X = r \<longrightarrow> f X < s)
  \<longrightarrow> (\<exists>Y' t'.
  Y' \<subseteq> YY 
  \<and> infinite Y' 
  \<and> t' < s 
  \<and> (\<forall>X. X \<subseteq> Y' \<and> finite X \<and> card X = r \<longrightarrow> f X = t'))"
  apply(simp add: part_def[symmetric] del: ex_simps)
  apply(rule, rule, rule_tac nat.induct)

  apply(intro allI impI)
  apply(rule_tac x="YY" in exI)
  apply(rule_tac x="f {}" in exI)
  apply(force simp: part_def)

  apply(intro allI impI) apply(elim exE conjE)

  (* now get the infinite g *)
  apply(subgoal_tac "
    \<exists>g. 
    (\<forall>m::nat. let (y,Y,t) = (g m) in
    y \<in> YY \<and> y \<notin> Y
    \<and> Y \<subseteq> YY \<and> infinite Y
    \<and> t < s 
    \<and> (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = nat \<longrightarrow> (f \<circ> insert y) X = t))
    \<and> (\<forall>m m'.     
    let (y,Y,t) = (g m) in 
    let (y',Y',t') =(g (m+m'+1)) in 
    y' : Y
    \<and> Y' \<subseteq> Y
    )
    ")
   prefer 2
   apply(cut_tac

     P = "\<lambda>gn.
     let (y,Y,t) = (gn) in 
     y \<in> YY \<and> y \<notin> Y 
     \<and> Y \<subseteq> YY \<and> infinite Y
     \<and> t < s
     \<and> (\<forall>X. X \<subseteq> Y \<and> finite X \<and> card X = nat \<longrightarrow> (f \<circ> insert y) X = t)
     "
 
     and R = "\<lambda>gn gn'.
     let (y,Y,t) = (gn) in 
     let (y',Y',t') =(gn') in 
     y' : Y
     \<and> Y' \<subseteq> Y
     "
 
     in dc)
   apply(erule impE)
   (* 3 *)
    apply(intro conjI)
      apply(intro allI impI, elim conjE) apply(simp add: Let_def split_beta) apply(blast)
     apply(subgoal_tac "\<exists>yy. yy \<in> YY") prefer 2 apply(rule infinite_mem) apply(assumption)
     apply(elim exE conjE)
     apply(drule_tac x="YY - {yy}" in spec) apply(drule_tac x="f \<circ> insert yy" in spec) 
     apply(erule impE) apply(simp) apply(rule part) apply(assumption+)
     apply(elim exE conjE)
     apply(rule_tac x="(yy,Y',t')" in exI) apply(simp) apply(blast)
    apply(intro allI impI)
    apply(case_tac x) apply(rename_tac yx b Yx tx)
    apply(subgoal_tac "\<exists>yx'. yx' \<in> Yx") prefer 2 apply(rule infinite_mem) apply(force) 
    apply(elim exE conjE) 
    apply(drule_tac x="Yx - {yx'}" in spec) 
    apply(drule_tac x="f \<circ> insert yx'" in spec) 
    apply(erule impE) apply(simp) apply(elim exE conjE) apply(rule part) apply(assumption+)
    apply(rule part_subset) apply(assumption) apply(assumption) apply(assumption)
    apply(elim exE conjE)
    apply(rule_tac x="(yx',Y',t')" in exI) apply(simp) apply(blast)
   apply(assumption)
      
  apply(elim exE conjE)

  apply(subgoal_tac "\<exists>s'. s' < s \<and> infinite {n. (\<lambda>n. let (y,Y,t) = g n in t) n = s'}") prefer 2

  apply(subgoal_tac "\<exists>s' \<in> ((\<lambda>n. let (Y, y, t) = g n in t) ` UNIV). infinite {n : UNIV. (let (Y, y, t) = g n in t) = s'}") prefer 2
  apply(rule infinite_dom_finite_rng) apply(simp) 
  apply(simp (no_asm) add: finite_nat_iff_bounded)
  apply(rule_tac x=s in exI) 
  apply(rule)
  apply(simp add: image_iff) apply(elim exE conjE)
  apply(drule_tac x=xa in spec) apply(force simp add: Let_def split_beta)
  apply(elim bexE conjE) apply(rule_tac x=s' in exI) apply(simp)
  apply(simp add: image_iff) apply(elim exE conjE) apply(drule_tac x=x in spec) apply(force simp: Let_def split_beta)

  apply(elim exE conjE)
  apply(rule_tac x="(\<lambda>n. let (y,Y,t) = g n in y) ` {n. (\<lambda>n. let (y,Y,t) = g n in t) n = s'}" in exI)
  apply(rule_tac x=s' in exI)
  (* lift this because it is needed in later subgoals *)
  apply(subgoal_tac "inj (\<lambda>n. let (y, Y, t) = g n in y)") prefer 2 
  apply(simp add: inj_on_def)
  (* minor optimisation *)
  apply(subgoal_tac "\<forall>x y. x < y \<and> (let (y, Y, t) = g x in y) = (let (y, Y, t) = g y in y) \<longrightarrow> x = y")
  apply(intro allI impI)
  apply(subgoal_tac "x < y | x = y | y < x") prefer 2 apply(arith)
  apply(elim disjE)
  apply(drule_tac x=x in spec) back back apply(drule_tac x=y in spec) back back apply(force simp: Let_def) 
  apply(assumption)
  apply(drule_tac x=y in spec) back back apply(drule_tac x=x in spec) back back apply(force simp: Let_def)
  apply(intro allI impI)
  apply(drule_tac x=x in spec) apply(drule_tac x=x in spec) apply(drule_tac x="y-(Suc x)" in spec) apply(force simp: Let_def)

  apply(intro allI conjI)

  apply(drule_tac x=xa in spec) 
  apply(force simp add: Let_def split_beta)
  
  apply(rule infinite_inj_infinite_image) apply(assumption)
  apply(simp add: inj_on_def)

  apply(simp)
  
  (* difficult goal- need that the other members of X all occur in Ya *)
  apply(intro allI impI, elim exE conjE)
  apply(simp add: subset_image_iff) apply(elim exE conjE)
  apply(subgoal_tac "\<exists>a. a \<in> AA \<and> (\<forall>a'. a' \<in> AA \<longrightarrow> a \<le> a')") prefer 2 apply(rule not_empty_least) apply(force)
  apply(elim exE conjE)
  apply(case_tac "g a" rule: prod.exhaust)
  apply(rename_tac b) apply(case_tac b rule: prod.exhaust) apply(rename_tac ya b Ya ta)
  apply(subgoal_tac "ya : X") prefer 2 apply(force intro!: rev_image_eqI simp: Let_def) 
  apply(drule_tac s=X in sym)
  apply(subgoal_tac "f X = (f \<circ> insert ya) (X - {ya})") apply(simp)
  apply(drule_tac x=a in spec) 
  apply(simp add: Let_def) apply(elim exE conjE)
  apply(drule_tac x="X-{ya}" in spec) back apply(erule impE)
  apply(simp)
  apply(rule) 
  apply(rule)
  apply(drule_tac t=X in sym) apply(simp) 
  apply(simp add: image_iff) apply(elim bexE exE conjE) apply(rename_tac a')
  apply(subgoal_tac "a' \<noteq> a") prefer 2 apply(force)
  apply(drule_tac x=a in spec)
  apply(drule_tac x="a'-Suc a" in spec) back
  apply(simp add: Let_def split_beta) apply(case_tac "g a'" rule: prod.exhaust) apply(case_tac ba rule: prod.exhaust) apply(rename_tac ya' ba Ya' ta') apply(simp add: Let_def split_beta)
  apply(drule_tac x=a' in spec) apply(erule impE) apply(force)
  apply(force)
  apply(force simp add: card_Diff_singleton_if)
  apply(subgoal_tac "ta = s'") apply(simp) apply(force)
  apply(simp) apply(rule_tac f=f in arg_cong) apply(force)
  done
  
end
