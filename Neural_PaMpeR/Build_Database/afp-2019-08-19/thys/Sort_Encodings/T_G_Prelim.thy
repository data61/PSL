(* Preliminaries on the tag and guard encodings  *)
theory T_G_Prelim
imports Mcalc
begin


(* Copy of ProblemIk, together with a partitioning of the types.
O stands for the original---this copy shall be used
as ``the original problem: *)

locale ProblemIkTpart =
Ik? : ProblemIk wtFsym wtPsym arOf resOf parOf \<Phi> infTp
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp +
fixes
    prot :: "'tp \<Rightarrow> bool" (* types aimed to be protected (with tags or guards) *)
and protFw :: "'tp \<Rightarrow> bool" (* types aimed to be protected in a featherweight fashion  *)
assumes
    tp_disj: "\<And> \<sigma>. \<not> prot \<sigma> \<or> \<not> protFw \<sigma>"
and tp_mcalc: "\<And> \<sigma>. prot \<sigma> \<or> protFw \<sigma> \<or> (\<forall> c \<in> \<Phi>. \<sigma> \<turnstile> c)"
begin

(* The notion of being a result type of some operation symbol: *)
definition isRes where "isRes \<sigma> \<equiv> \<exists> f. wtFsym f \<and> resOf f = \<sigma>"

(* Types meant to be left unprotected:
-- in the case of tags, terms of these type are not tagged;
-- in the case of guards, no guards are added for these types  *)
definition "unprot \<sigma> \<equiv> \<not> prot \<sigma> \<and> \<not> protFw \<sigma>"

lemma unprot_mcalc[simp]: "\<lbrakk>unprot \<sigma>; c \<in> \<Phi>\<rbrakk> \<Longrightarrow> \<sigma> \<turnstile> c "
using tp_mcalc unfolding unprot_def by auto

end (* context ProblemIkTpart *)


(* Problem with type partition and model: *)
locale ModelIkTpart =
Ik? : ProblemIkTpart wtFsym wtPsym arOf resOf parOf \<Phi> infTp prot protFw +
Ik? : Model wtFsym wtPsym arOf resOf parOf \<Phi> intT intF intP
for wtFsym :: "'fsym \<Rightarrow> bool"
and wtPsym :: "'psym \<Rightarrow> bool"
and arOf :: "'fsym \<Rightarrow> 'tp list"
and resOf and parOf and \<Phi> and infTp and prot and protFw
and intT and intF and intP

end
