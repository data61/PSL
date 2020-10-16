section \<open>Normalizing Derivative\<close>

theory NDerivative
imports
  Regular_Exp
begin

subsection \<open>Normalizing operations\<close>

text \<open>associativity, commutativity, idempotence, zero\<close>

fun nPlus :: "'a::order rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "nPlus Zero r = r"
| "nPlus r Zero = r"
| "nPlus (Plus r s) t = nPlus r (nPlus s t)"
| "nPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if le_rexp r s then Plus r (Plus s t)
     else Plus s (nPlus r t))"
| "nPlus r s =
     (if r = s then r
      else if le_rexp r s then Plus r s
      else Plus s r)"

lemma lang_nPlus[simp]: "lang (nPlus r s) = lang (Plus r s)"
by (induction r s rule: nPlus.induct) auto

text \<open>associativity, zero, one\<close>

fun nTimes :: "'a::order rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "nTimes Zero _ = Zero"
| "nTimes _ Zero = Zero"
| "nTimes One r = r"
| "nTimes r One = r"
| "nTimes (Times r s) t = Times r (nTimes s t)"
| "nTimes r s = Times r s"

lemma lang_nTimes[simp]: "lang (nTimes r s) = lang (Times r s)"
by (induction r s rule: nTimes.induct) (auto simp: conc_assoc)

primrec norm :: "'a::order rexp \<Rightarrow> 'a rexp"
where
  "norm Zero = Zero"
| "norm One = One"
| "norm (Atom a) = Atom a"
| "norm (Plus r s) = nPlus (norm r) (norm s)"
| "norm (Times r s) = nTimes (norm r) (norm s)"
| "norm (Star r) = Star (norm r)"

lemma lang_norm[simp]: "lang (norm r) = lang r"
by (induct r) auto

primrec nderiv :: "'a::order \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "nderiv _ Zero = Zero"
| "nderiv _ One = Zero"
| "nderiv a (Atom b) = (if a = b then One else Zero)"
| "nderiv a (Plus r s) = nPlus (nderiv a r) (nderiv a s)"
| "nderiv a (Times r s) =
    (let r's = nTimes (nderiv a r) s
     in if nullable r then nPlus r's (nderiv a s) else r's)"
| "nderiv a (Star r) = nTimes (nderiv a r) (Star r)"

lemma lang_nderiv: "lang (nderiv a r) = Deriv a (lang r)"
by (induction r) (auto simp: Let_def nullable_iff)

lemma deriv_no_occurrence: 
  "x \<notin> atoms r \<Longrightarrow> nderiv x r = Zero"
by (induction r) auto

lemma atoms_nPlus[simp]: "atoms (nPlus r s) = atoms r \<union> atoms s"
by (induction r s rule: nPlus.induct) auto

lemma atoms_nTimes: "atoms (nTimes r s) \<subseteq> atoms r \<union> atoms s"
by (induction r s rule: nTimes.induct) auto

lemma atoms_norm: "atoms (norm r) \<subseteq> atoms r"
by (induction r) (auto dest!:subsetD[OF atoms_nTimes])

lemma atoms_nderiv: "atoms (nderiv a r) \<subseteq> atoms r"
by (induction r) (auto simp: Let_def dest!:subsetD[OF atoms_nTimes])

end
