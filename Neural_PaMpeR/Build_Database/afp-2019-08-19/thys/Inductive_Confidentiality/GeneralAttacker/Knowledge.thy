section\<open>Study on knowledge equivalence --- results to relate the knowledge of an agent to that of another's\<close>

theory Knowledge
imports NS_Public_Bad_GA
begin

(*Protocol independent study*)

(*Whatever A knows, which is neither static-private nor dynamic-private for
  her, then also B knows that*)
theorem knowledge_equiv:
 "\<lbrakk> X \<in> knows A evs; Notes A X \<notin> set evs;
   X \<notin> {Key (priEK A), Key (priSK A), Key (shrK A)} \<rbrakk>
 \<Longrightarrow> X \<in> knows B evs"
apply (erule rev_mp, erule rev_mp, erule rev_mp)
apply (induct_tac "A", induct_tac "B", induct_tac "evs")
apply (induct_tac [2] "a") apply auto
done

lemma knowledge_equiv_bis:
 "\<lbrakk> X \<in> knows A evs; Notes A X \<notin> set evs \<rbrakk>
 \<Longrightarrow> X \<in> {Key (priEK A), Key (priSK A), Key (shrK A)} \<union> knows B evs"
apply (blast dest: knowledge_equiv)
done

lemma knowledge_equiv_ter:
 "\<lbrakk> X \<in> knows A evs; X \<notin> {Key (priEK A), Key (priSK A), Key (shrK A)} \<rbrakk>
\<Longrightarrow> X \<in> knows B evs \<or> Notes A X \<in> set evs"
apply (blast dest: knowledge_equiv)
done

lemma knowledge_equiv_quater:
 " X \<in> knows A evs
\<Longrightarrow> X \<in> knows B evs \<or> Notes A X \<in> set evs \<or> 
   X \<in> {Key (priEK A), Key (priSK A), Key (shrK A)}"
apply (blast dest: knowledge_equiv)
done

lemma setdiff_diff_insert: "A-B-C=D-E-F \<Longrightarrow> insert m (A-B-C) = insert m (D-E-F)"
by simp
(*IMPORTANT NOTE TO PREVIOUS LEMMA: removing parentheses from rhs falsifies
the lemma because set insertion seems to have higher priority than set
difference, hence insert m A-B-C \<noteq> insert m (A-B-C)!
Seen such operand priority, it can be understood why the lemma wouldn't hold
without parentheses*)
lemma "A-B-C=D-E-F \<Longrightarrow> insert m A-B-C = insert m D-E-F"
oops

lemma knowledge_equiv_eq_setdiff:
 "knows A evs  -
   {Key (priEK A), Key (priSK A), Key (shrK A)} -
     {X. Notes A X \<in> set evs}
  =
  knows B evs -
   {Key (priEK B), Key (priSK B), Key (shrK B)} -
     {X. Notes B X \<in> set evs}"
apply (induct_tac "evs", induct_tac "A", induct_tac "B")
apply force
apply (induct_tac "a")

(*Gets case solves because this event doesn't touch any agent knowledge*)
apply simp_all

(*Says case fails because both agents extract the said message, plus
discussion on lemma setdiff_diff_insert*)

(*Notes case solves in case neither of the two agents is the agent of the
  current step, because no notes are extracted and inductive premise applies;
  it fails in the two subcases when either of them is the agent of the current
  step, because a note would be extracted i.e. inserted in his knowledge, and
  hence falsification by discussion on lemma setdiff_diff_insert*)

oops (*So we have clear counterexamples of why this theorem CANNOT be proved inductively. Alternative stretegy using symbolic evaluation introduces clear counterexamples such as when an agent says A's shared key: it would be in the rhs but not in the lhs!*)

(* Old proof*)
lemma knowledge_equiv_eq_old:
 "knows A evs  \<union>  
   {Key (priEK B), Key (priSK B), Key (shrK B)} \<union> 
     {X. Notes B X \<in> set evs} 
  = 
  knows B evs \<union> 
   {Key (priEK A), Key (priSK A), Key (shrK A)} \<union> 
     {X. Notes A X \<in> set evs}"
apply (induct_tac "evs", induct_tac "A", induct_tac "B")
apply force
apply (induct_tac "a")
txt\<open>Gets case solves because this event doesn't touch any agent knowledge\<close>
apply simp_all
apply safe txt\<open>speeds up subsequent blasting\<close>
apply blast+  txt\<open>very very slow\<close>
done

(* New proof*)

theorem knowledge_eval: "knows A evs = 
       {Key (priEK A), Key (priSK A), Key (shrK A)} \<union> 
       (Key ` range pubEK) \<union> (Key ` range pubSK) \<union>
       {X. \<exists> S R. Says S R X \<in> set evs} \<union>
       {X. Notes A X \<in> set evs}"
apply (induct_tac "A", induct_tac "evs")
apply (induct_tac [2] "a")
apply auto
done

lemma knowledge_eval_setdiff:
 "knows A evs  - 
   {Key (priEK A), Key (priSK A), Key (shrK A)} -
     {X. Notes A X \<in> set evs}
  = 
       (Key ` range pubEK) \<union> (Key ` range pubSK) \<union>
       {X. \<exists> S R. Says S R X \<in> set evs}"
apply (simp only: knowledge_eval) apply auto
oops(*here are clear counterexamples!*)

theorem knowledge_equiv_eq: "knows A evs  \<union>  
   {Key (priEK B), Key (priSK B), Key (shrK B)} \<union> 
     {X. Notes B X \<in> set evs} 
  = 
  knows B evs \<union> 
   {Key (priEK A), Key (priSK A), Key (shrK A)} \<union> 
     {X. Notes A X \<in> set evs}"
apply (force simp only: knowledge_eval)
done

lemma "knows A evs  \<union>  
   {Key (priEK B), Key (priSK B), Key (shrK B)} \<union> 
     {X. Notes B X \<in> set evs} -
(  {Key (priEK B), Key (priSK B), Key (shrK B)} \<union> 
     {X. Notes B X \<in> set evs} ) = knows A evs"
apply auto
oops
(*Here the prover tells you why this fails*)

theorem parts_knowledge_equiv_eq: "
parts(knows A evs)  \<union>  
   {Key (priEK B), Key (priSK B), Key (shrK B)} \<union> 
     parts({X. Notes B X \<in> set evs}) 
  = 
parts(knows B evs) \<union> 
   {Key (priEK A), Key (priSK A), Key (shrK A)} \<union> 
     parts({X. Notes A X \<in> set evs})"
apply (simp only: knowledge_eval parts_Un) apply force
done

lemmas parts_knowledge_equiv = parts_knowledge_equiv_eq [THEN equalityD1, THEN subsetD]
thm parts_knowledge_equiv
theorem noprishr_parts_knowledge_equiv: "
\<lbrakk> X \<notin> {Key (priEK A), Key (priSK A), Key (shrK A)};
  X \<in> parts(knows A evs) \<rbrakk>
\<Longrightarrow>  X \<in> parts(knows B evs) \<union> 
      parts({X. Notes A X \<in> set evs})"
apply (force dest: UnI1 [THEN UnI1, THEN parts_knowledge_equiv])
done



(*Protocol-dependent study*)


lemma knowledge_equiv_eq_NS: " 
  evs \<in> ns_public \<Longrightarrow>
  knows A evs  \<union> {Key (priEK B), Key (priSK B), Key (shrK B)}  = 
  knows B evs \<union> {Key (priEK A), Key (priSK A), Key (shrK A)}"
apply (force simp only: knowledge_eval NS_no_Notes)
done

lemma parts_knowledge_equiv_eq_NS: " 
  evs \<in> ns_public \<Longrightarrow>
  parts(knows A evs) \<union> {Key (priEK B), Key (priSK B), Key (shrK B)}  = 
  parts(knows B evs) \<union> {Key (priEK A), Key (priSK A), Key (shrK A)}"
apply (simp only: knowledge_eval NS_no_Notes parts_Un) apply force
done

theorem noprishr_parts_knowledge_equiv_NS: " 
\<lbrakk> X \<notin> {Key (priEK A), Key (priSK A), Key (shrK A)};
  X \<in> parts(knows A evs); evs \<in> ns_public \<rbrakk>
\<Longrightarrow>  X \<in> parts(knows B evs)"
apply (drule noprishr_parts_knowledge_equiv, simp)
apply (simp add: NS_no_Notes)
done

theorem Agent_not_analz_N:
"\<lbrakk> Nonce N \<notin> parts(knows A evs); evs \<in> ns_public \<rbrakk>
 \<Longrightarrow> Nonce N \<notin> analz(knows B evs)"
apply (force intro: noprishr_parts_knowledge_equiv_NS analz_into_parts)
done
(*Conclusion in terms of analz because we are more used to it. It would have been a stronger law in terms of parts, though*)

end
