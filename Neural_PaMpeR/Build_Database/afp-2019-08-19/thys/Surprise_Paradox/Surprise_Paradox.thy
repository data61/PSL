theory Surprise_Paradox
imports
  Incompleteness.Goedel_I
  Incompleteness.Pseudo_Coding
begin

text \<open>
The Surprise Paradox comes in a few variations, one being the following:

\begin{quote}
A judge sentences a felon to death by hanging, to be executed at noon the next week, Monday to
Friday. As an extra punishment, the judge does not disclose the day of the hanging and promises the
felon that it will come at a surprise.

The felon, probably a logician, then concludes that he cannot be hanged on Friday, as by then it would
not longer be a surprise. Using this fact and similar reasoning, he cannot be hanged on Thursday, and so
on. He reaches the conclusion that he cannot be hanged at all, and contently returns to his cell.

Wednesday, at noon, the hangman comes to the very surprised felon, and executes him.
\end{quote}

Obviously, something is wrong here: Does the felon reason wrongly? It looks about right.
Or is the judge lying? But his prediction became true!

It is an interesting exercise to try to phrase the Surprise Paradox in a rigorous manner, and
see this might clarify things.

In 1964, Frederic Fitch suggested a formulation that refines the notion of ``surprise'' as
``cannot be proven from the given assumptions'' @{cite Fitch}. To formulate that, we need propositions that
reference their own provability, so just as Fitch builds on Gödel's work, we build on Paulson's
formalisation of Gödel's incompleteness theorems in Isabelle @{cite Incompleteness}.
\<close>

section \<open>Excluded or\<close>

text \<open>Although the proof goes through with regular disjunction, Fitch phrases the judge's
proposition using exclusive or, so we add syntax for that.\<close>

abbreviation Xor :: "fm \<Rightarrow> fm \<Rightarrow> fm" (infix "XOR" 120)
 where "Xor A B \<equiv> (A OR B) AND ((Neg A) OR (Neg B))"

section \<open>Formulas with variables\<close>

text \<open>
In Paulson's formalisation of terms and formulas, only terms carry variables. This is sufficient for
his purposes, because the proposition that is being diagonalised needs itself as a parameter to
@{term_type PfP}, which does take a term (which happens to be a quoted formula).

In order to stay close to Fitch, we need the diagonalised proposition to occur deeper in a quotation
of a few logical conjunctions. Therefore, we build a small theory of formulas with variables (``holed''
formulas). These support substituting a formula for a variable, this substitution commutes with
quotation, and closed holed formulas can be converted to regular formulas.

In our application, we do not need holes under an quantifier, which greatly simplifies things here.
In particular, we can use @{command datatype} and @{command fun}.
\<close>

datatype hfm =
   HVar name
 | HFm fm
 | HDisj hfm hfm (infixr "HOR" 130)
 | HNeg  hfm

abbreviation HImp :: "hfm \<Rightarrow> hfm \<Rightarrow> hfm"  (infixr "HIMP" 125)
  where "HImp A B \<equiv> HDisj (HNeg A) B"

definition HConj :: "hfm \<Rightarrow> hfm \<Rightarrow> hfm"   (infixr "HAND" 135)
  where "HConj A B \<equiv> HNeg (HDisj (HNeg A) (HNeg B))"

abbreviation HXor :: "hfm \<Rightarrow> hfm \<Rightarrow> hfm" (infix "HXOR" 120)
 where "HXor A B \<equiv> (A HOR B) HAND (HNeg A HOR HNeg B)"

fun  subst_hfm :: "hfm \<Rightarrow> name \<Rightarrow> fm \<Rightarrow> hfm" ("_'(_:::=_')" [1000, 0, 0] 200)
  where
    "(HVar name)(i:::=x) = (if i = name then HFm x else HVar name)"
  | "(HDisj A B)(i:::=x) = HDisj (A(i:::=x)) (B(i:::=x))"
  | "(HNeg A)(i:::=x) = HNeg (A(i:::=x))"
  | "(HFm A)(i:::=x) = HFm A"

lemma subst_hfml_Conj[simp]:
  "(HConj A B)(i:::=x) = HConj (A(i:::=x)) (B(i:::=x))"
 unfolding HConj_def by simp

instantiation hfm :: quot
begin
fun quot_hfm :: "hfm \<Rightarrow> tm"
  where
   "quot_hfm (HVar name) = (Var name)"
 | "quot_hfm (HFm A) = \<lceil>A\<rceil>"
 | "quot_hfm (HDisj A B) = HPair (HTuple 3) (HPair (quot_hfm A) (quot_hfm B))"
 | "quot_hfm (HNeg A) = HPair (HTuple 4) (quot_hfm A)"

instance ..
end

lemma subst_quot_hfm[simp]: "subst i \<lceil>P\<rceil> \<lceil>A\<rceil> = \<lceil>A(i:::=P)\<rceil>"
  by (induction A) auto

fun hfm_to_fm :: "hfm \<Rightarrow> fm"
  where
   "hfm_to_fm (HVar name) = undefined"
 | "hfm_to_fm (HFm A) = A"
 | "hfm_to_fm (HDisj A B) = Disj (hfm_to_fm A) (hfm_to_fm B)"
 | "hfm_to_fm (HNeg A) = Neg (hfm_to_fm A)"

lemma hfm_to_fm_Conj[simp]:
  "hfm_to_fm (HConj A B) = Conj (hfm_to_fm A) (hfm_to_fm B)"
unfolding HConj_def Conj_def by simp

fun closed_hfm  :: "hfm \<Rightarrow> bool"
  where
   "closed_hfm (HVar name) \<longleftrightarrow> False"
 | "closed_hfm (HFm A) \<longleftrightarrow> True"
 | "closed_hfm (HDisj A B) \<longleftrightarrow> closed_hfm A \<and> closed_hfm B"
 | "closed_hfm (HNeg A) \<longleftrightarrow> closed_hfm A"

lemma closed_hfm_Conj[simp]:
  "closed_hfm (HConj A B) \<longleftrightarrow> closed_hfm A \<and> closed_hfm B"
unfolding HConj_def by simp

lemma quot_closed_hfm[simp]: "closed_hfm A \<Longrightarrow> \<lceil>A\<rceil> = \<lceil>hfm_to_fm A\<rceil>"
  by (induction A) (auto simp add: quot_fm_def)

declare quot_hfm.simps[simp del]

section \<open>Fitch's proof\<close>

text \<open>
For simplicity, Fitch (and we) restrict the week to two days. Propositions \<open>Q\<^sub>1\<close> and \<open>Q\<^sub>2\<close>
represent the propositions that the hanging occurs on the first resp.\@ the second day, but
these can obviously be any propositions.
\<close>

context
  fixes Q\<^sub>1 :: fm and Q\<^sub>2 :: fm
  assumes Q_closed: "supp Q\<^sub>1 = {}" "supp Q\<^sub>2 = {}"
begin

  text \<open>
  In order to define the judge's proposition, which is self-referential, we apply the usual trick
  of defining a proposition with a variable, and then using Gödel's diagonalisation lemma.
  \<close>

  definition H :: fm where
    "H = Q\<^sub>1 AND Neg (PfP \<lceil>HVar X0 HIMP HFm Q\<^sub>1\<rceil>) XOR 
     Q\<^sub>2 AND Neg (PfP \<lceil>HVar X0 HAND HNeg (HFm Q\<^sub>1) HIMP (HFm Q\<^sub>2)\<rceil>)"

  definition P where "P = (SOME P. {} \<turnstile> P IFF H(X0 ::= \<lceil>P\<rceil>))"

  lemma P': "{} \<turnstile> P IFF H(X0 ::= \<lceil>P\<rceil>)"
  proof-
    from diagonal[where \<alpha> = "H" and i = X0]
    obtain \<delta> where "{} \<turnstile> \<delta> IFF H(X0 ::= \<lceil>\<delta>\<rceil>)".
    thus ?thesis  unfolding P_def by (rule someI)
  qed

  text \<open>
  From now on, the lemmas are named after their number in Fitch's paper, and correspond to his
  statements pleasingly closely.
  \<close>

  lemma 7: "{} \<turnstile> P IFF
     (Q\<^sub>1 AND Neg (PfP \<lceil>P IMP Q\<^sub>1\<rceil>) XOR
      Q\<^sub>2 AND Neg (PfP \<lceil>P AND Neg Q\<^sub>1 IMP Q\<^sub>2\<rceil>))"
    using P' unfolding H_def
    by (simp add: Q_closed forget_subst_fm[unfolded fresh_def])
  lemmas "7_E" = 7[THEN thin0, THEN Iff_MP_left', OF Conj_E, OF thin2]

  lemmas propositional_calculus = 
    AssumeH Neg_I Imp_I Conj_E Disj_E ExFalso[OF Neg_E]
    ExFalso[OF rotate2, OF Neg_E] ExFalso[OF rotate3, OF Neg_E]  
    
  lemma 8: "{} \<turnstile> (P AND Neg Q\<^sub>1) IMP Q\<^sub>2"
    by (intro propositional_calculus "7_E")

  lemma 10: "{} \<turnstile> PfP \<lceil>(P AND Neg Q\<^sub>1) IMP Q\<^sub>2\<rceil>"
    using 8 by (rule proved_imp_proved_PfP)
  lemmas "10_I" = 10[THEN thin0]

  lemma 11: "{} \<turnstile> P IMP Q\<^sub>1"
    by (intro propositional_calculus "7_E" "10_I")
    
  lemma 12: "{} \<turnstile> PfP \<lceil>P IMP Q\<^sub>1\<rceil>"
    using 11 by (rule proved_imp_proved_PfP)
  lemmas "12_I" = 12[THEN thin0]

  lemma 13: "{} \<turnstile> Neg P"
    by (intro propositional_calculus "7_E" "10_I" "12_I")
end

section \<open>Substitution, quoting and V-quoting\<close>

text \<open>In the end, we did not need the lemma at the end of this section, but it may be useful to
others.\<close>

lemma trans_tm_forgets: "atom ` set is \<sharp>* t \<Longrightarrow> trans_tm is t = trans_tm [] t"
  by (induct t rule: tm.induct)
     (auto simp: lookup_notin fresh_star_def fresh_at_base)

lemma vquot_dbtm_fresh: "atom ` V \<sharp>* t \<Longrightarrow> vquot_dbtm V t = quot_dbtm t"
  by (nominal_induct t rule: dbtm.strong_induct)
     (auto simp add: fresh_star_def fresh_at_base)

lemma subst_vquot_dbtm_trans_tm[simp]:
  "atom i \<sharp> is \<Longrightarrow> atom ` set is \<sharp>* t \<Longrightarrow>
   subst i \<lceil>t\<rceil> (vquot_dbtm {i} (trans_tm is t')) =
   quot_dbtm (trans_tm is (subst i t t'))"
  by (nominal_induct t' avoiding: "is" i t rule: tm.strong_induct)
     (auto simp add:  quot_tm_def lookup_notin fresh_imp_notin_env
                      vquot_dbtm_fresh lookup_fresh
           intro: trans_tm_forgets[symmetric])

lemma subst_vquot_dbtm_trans_fm[simp]:
  "atom i \<sharp> is \<Longrightarrow> atom ` set is \<sharp>* t \<Longrightarrow>
   subst i \<lceil>t\<rceil> (vquot_dbfm {i} (trans_fm is A)) =
   quot_dbfm (trans_fm is (subst_fm A i t))"
  by (nominal_induct A avoiding: "is" i t rule: fm.strong_induct)
     (auto simp add: quot_fm_def fresh_Cons)

lemma subst_vquot[simp]:
  "subst i \<lceil>t\<rceil> \<lfloor>A\<rfloor>{i} = \<lceil>A(i ::= t)\<rceil>"
  by (nominal_induct A avoiding: i t rule: fm.strong_induct)
     (auto simp add: vquot_fm_def quot_fm_def fresh_Cons)

end
