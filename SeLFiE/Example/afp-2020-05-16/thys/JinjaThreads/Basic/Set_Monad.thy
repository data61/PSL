theory Set_Monad
imports 
  Main
  "HOL-Library.Monad_Syntax"
begin

lemma member_SUP: (* FIXME delete candidate: should be subsumed by default simpset as soon as SUP_apply is included *)
  "x \<in> \<Union>(f ` A) = (SUP B\<in>A. (\<lambda>x. x \<in> f B)) x"
  by auto

abbreviation (input) "of_pred == Predicate.set_of_pred" (* FIXME delte alias *)
abbreviation (input) "of_seq == Predicate.set_of_seq" (* FIXME delte alias *)

lemmas bind_def = Set.bind_def (* FIXME delte alias *)
lemmas bind_bind = Set.bind_bind (* FIXME delte alias *)
lemmas empty_bind = Set.empty_bind (* FIXME delte alias *)
lemmas bind_const = Set.bind_const (* FIXME delte alias *)
lemmas member_of_pred = Predicate.member_set_of_pred (* FIXME delte alias *)
lemmas member_of_seq = Predicate.member_set_of_seq (* FIXME delte alias *)

definition single :: "'a \<Rightarrow> 'a set"
  where "single a = {a}"

definition undefined :: "'a set"
  where [simp]: "undefined = Collect HOL.undefined"

declare [[code abort: undefined]]

definition Undefined :: "unit \<Rightarrow> 'a set"
  where "Undefined _ = Collect HOL.undefined"

declare [[code abort: Undefined]]

lemma undefined_code [code_unfold]:
  "undefined = Undefined ()"
  by (simp add: Undefined_def)

lemma bind_single [simp, code_unfold]:
  "A \<bind> single = A"
  by (simp add: bind_def single_def)

lemma single_bind [simp, code_unfold]:
  "single a \<bind> B = B a"
  by (simp add: bind_def single_def)

declare Set.empty_bind [code_unfold]

lemma member_single [simp]:
  "x \<in> single a \<longleftrightarrow> x = a"
by (simp add: single_def)

lemma single_sup_simps [simp, code_unfold]:
  shows single_sup: "sup (single a) A = insert a A"
  and sup_single: "sup A (single a) = insert a A"
  by (unfold set_eq_iff) auto

lemma single_code [code]:
  "single a = set [a]"
  by (simp add: set_eq_iff)

end
