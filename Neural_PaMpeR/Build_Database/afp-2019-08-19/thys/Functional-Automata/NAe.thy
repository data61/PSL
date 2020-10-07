(*  Author:     Tobias Nipkow
    Copyright   1998 TUM
*)

section "Nondeterministic automata with epsilon transitions"

theory NAe
imports NA
begin

type_synonym ('a,'s)nae = "('a option,'s)na"

abbreviation
  eps :: "('a,'s)nae \<Rightarrow> ('s * 's)set" where
  "eps A \<equiv> step A None"

primrec steps :: "('a,'s)nae \<Rightarrow> 'a list \<Rightarrow>   ('s * 's)set" where
"steps A [] = (eps A)\<^sup>*" |
"steps A (a#w) = (eps A)\<^sup>* O step A (Some a) O steps A w"

definition
 accepts :: "('a,'s)nae \<Rightarrow> 'a list \<Rightarrow> bool" where
"accepts A w = (\<exists>q. (start A,q) \<in> steps A w \<and> fin A q)"

(* not really used:
consts delta :: "('a,'s)nae \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> 's set"
primrec
"delta A [] s = (eps A)\<^sup>* `` {s}"
"delta A (a#w) s = lift(delta A w) (lift(next A (Some a)) ((eps A)\<^sup>* `` {s}))"
*)

lemma steps_epsclosure[simp]: "(eps A)\<^sup>* O steps A w = steps A w"
by (cases w) (simp_all add: O_assoc[symmetric])

lemma in_steps_epsclosure:
  "[| (p,q) : (eps A)\<^sup>*; (q,r) : steps A w |] ==> (p,r) : steps A w"
apply(rule steps_epsclosure[THEN equalityE])
apply blast
done

lemma epsclosure_steps: "steps A w O (eps A)\<^sup>* = steps A w"
apply(induct w)
 apply simp
apply(simp add:O_assoc)
done

lemma in_epsclosure_steps:
  "[| (p,q) : steps A w; (q,r) : (eps A)\<^sup>* |] ==> (p,r) : steps A w"
apply(rule epsclosure_steps[THEN equalityE])
apply blast
done

lemma steps_append[simp]:  "steps A (v@w) = steps A v  O  steps A w"
by(induct v)(simp_all add:O_assoc[symmetric])

lemma in_steps_append[iff]:
  "(p,r) : steps A (v@w) = ((p,r) : (steps A v O steps A w))"
apply(rule steps_append[THEN equalityE])
apply blast
done

(* Equivalence of steps and delta
* Use "(\<exists>x \<in> f ` A. P x) = (\<exists>a\<in>A. P(f x))" ?? *
Goal "\<forall>p. (p,q) : steps A w = (q : delta A w p)";
by (induct_tac "w" 1);
 by (Simp_tac 1);
by (asm_simp_tac (simpset() addsimps [comp_def,step_def]) 1);
by (Blast_tac 1);
qed_spec_mp "steps_equiv_delta";
*)

end
