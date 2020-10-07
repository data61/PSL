(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>LTL Translation Layer\<close>

theory LTL_Compat
  imports Main LTL.LTL "../LTL_FGXU"
begin

\<comment> \<open>The following infrastructure translates the generic @{datatype ltln} datatype to special structure used in this project\<close>

abbreviation LTLRelease :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ R _" [87,87] 86)
where
  "\<phi> R \<psi> \<equiv> (G \<psi>) or (\<psi> U (\<phi> and \<psi>))"

abbreviation LTLWeakUntil :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ W _" [87,87] 86)
where
  "\<phi> W \<psi> \<equiv> (\<phi> U \<psi>) or (G \<phi>)"

abbreviation LTLStrongRelease :: "'a ltl \<Rightarrow> 'a ltl \<Rightarrow> 'a ltl" ("_ M _" [87,87] 86)
where
  "\<phi> M \<psi> \<equiv> \<psi> U (\<phi> and \<psi>)"

fun ltln_to_ltl :: "'a ltln \<Rightarrow> 'a ltl"
where
  "ltln_to_ltl true\<^sub>n = true"
| "ltln_to_ltl false\<^sub>n = false"
| "ltln_to_ltl prop\<^sub>n(q) = p(q)"
| "ltln_to_ltl nprop\<^sub>n(q) = np(q)"
| "ltln_to_ltl (\<phi> and\<^sub>n \<psi>) = ltln_to_ltl \<phi> and ltln_to_ltl \<psi>"
| "ltln_to_ltl (\<phi> or\<^sub>n \<psi>) = ltln_to_ltl \<phi> or ltln_to_ltl \<psi>"
| "ltln_to_ltl (\<phi> U\<^sub>n \<psi>) = (if \<phi> = true\<^sub>n then F (ltln_to_ltl \<psi>) else (ltln_to_ltl \<phi>) U (ltln_to_ltl \<psi>))"
| "ltln_to_ltl (\<phi> R\<^sub>n \<psi>) = (if \<phi> = false\<^sub>n then G (ltln_to_ltl \<psi>) else (ltln_to_ltl \<phi>) R (ltln_to_ltl \<psi>))"
| "ltln_to_ltl (\<phi> W\<^sub>n \<psi>) = (if \<psi> = false\<^sub>n then G (ltln_to_ltl \<phi>) else (ltln_to_ltl \<phi>) W (ltln_to_ltl \<psi>))"
| "ltln_to_ltl (\<phi> M\<^sub>n \<psi>) = (if \<psi> = true\<^sub>n then F (ltln_to_ltl \<phi>) else (ltln_to_ltl \<phi>) M (ltln_to_ltl \<psi>))"
| "ltln_to_ltl (X\<^sub>n \<phi>) = X (ltln_to_ltl \<phi>)"

lemma ltln_to_ltl_semantics:
  "w \<Turnstile> ltln_to_ltl \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction \<phi> arbitrary: w)
     (simp_all del: semantics_ltln.simps(9-11), unfold ltln_Release_alterdef ltln_weak_strong(1) ltl_StrongRelease_Until_con, insert nat_less_le, auto)

lemma ltln_to_ltl_atoms:
  "vars (ltln_to_ltl \<phi>) = atoms_ltln \<phi>"
  by (induction \<phi>) auto

fun atoms_list :: "'a ltln \<Rightarrow>'a list"
where 
  "atoms_list (\<phi> and\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> or\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> U\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> R\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> W\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (\<phi> M\<^sub>n \<psi>) = List.union (atoms_list \<phi>) (atoms_list \<psi>)"
| "atoms_list (X\<^sub>n \<phi>) = atoms_list \<phi>"
| "atoms_list (prop\<^sub>n(a)) = [a]"
| "atoms_list (nprop\<^sub>n(a)) = [a]"
| "atoms_list _ = []"

lemma atoms_list_correct:
  "set (atoms_list \<phi>) = atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma atoms_list_distinct:
  "distinct (atoms_list \<phi>)"
  by (induction \<phi>) auto

end
