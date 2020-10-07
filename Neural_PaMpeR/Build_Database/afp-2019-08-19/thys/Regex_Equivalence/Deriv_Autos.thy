(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section "Framework Instantiations using (Partial) Derivatives"

(*<*)
theory Deriv_Autos
imports
  Automaton
  "Regular-Sets.NDerivative"
  Deriv_PDeriv
begin
(*>*)

subsection \<open>Brzozowski Derivatives Modulo ACI\<close>

lemma ACI_norm_derivs_alt: "\<guillemotleft>derivs w r\<guillemotright> = fold (\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>) w \<guillemotleft>r\<guillemotright>"
  by (induct w arbitrary: r) (auto simp: ACI_norm_deriv)

global_interpretation brzozowski: rexp_DFA "\<lambda>r. \<guillemotleft>r\<guillemotright>" "\<lambda>a r. \<guillemotleft>deriv a r\<guillemotright>" nullable lang
  defines brzozowski_closure = brzozowski.closure
    and check_eqv_brz = brzozowski.check_eqv
    and reachable_brz = brzozowski.reachable
    and automaton_brz = brzozowski.automaton
    and match_brz = brzozowski.match
proof (unfold_locales, goal_cases)
  case 1 show ?case by (rule lang_ACI_norm)
next
  case 2 show ?case by (rule trans[OF lang_ACI_norm lang_deriv])
next
  case 3 show ?case by (rule nullable_iff)
next
  case 4 show ?case by (simp only: ACI_norm_derivs_alt[symmetric] finite_derivs)
qed


subsection \<open>Brzozowski Derivatives Modulo ACI Operating on the Quotient Type\<close>

lemma derivs_alt: "derivs = fold deriv"
proof
  fix w :: "'a list" show "derivs w = fold deriv w" by (induct w) auto
qed

functor map_rexp by (simp_all only: o_def id_def map_map_rexp map_rexp_ident)

quotient_type 'a ACI_rexp = "'a rexp" / ACI
  morphisms rep_ACI_rexp ACI_class
  by (intro equivpI reflpI sympI transpI) (blast intro: ACI_refl ACI_sym ACI_trans)+

instantiation ACI_rexp :: ("{equal, linorder}") "{equal, linorder}"
begin
lift_definition less_eq_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. less_eq \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
lift_definition less_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. less \<guillemotleft>r\<guillemotright> \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
lift_definition equal_ACI_rexp :: "'a ACI_rexp \<Rightarrow> 'a ACI_rexp \<Rightarrow> bool" is "\<lambda>r s. \<guillemotleft>r\<guillemotright> = \<guillemotleft>s\<guillemotright>"
   by (simp add: ACI_decidable)
instance by intro_classes (transfer, force simp: ACI_decidable)+
end

lift_definition ACI_deriv :: "'a :: linorder \<Rightarrow> 'a ACI_rexp \<Rightarrow> 'a ACI_rexp" is deriv
  by (rule ACI_deriv)
lift_definition ACI_nullable :: "'a :: linorder ACI_rexp \<Rightarrow> bool" is nullable
  by (rule ACI_nullable)
lift_definition ACI_lang :: "'a :: linorder ACI_rexp \<Rightarrow> 'a lang" is lang
  by (rule ACI_lang)

lemma [transfer_rule]: "rel_fun (rel_set (pcr_ACI_rexp (=))) (=) (finite o image ACI_norm) finite"
  unfolding rel_fun_def rel_set_def cr_ACI_rexp_def ACI_rexp.pcr_cr_eq
  apply (auto simp: elim!: finite_surj[of _ _ ACI_class] finite_surj[of _ _ "ACI_norm o rep_ACI_rexp"])
  apply (metis (hide_lams, no_types) ACI_norm_idem ACI_rexp.abs_eq_iff ACI_decidable imageI)
  apply (rule image_eqI)
  apply (subst ACI_decidable[symmetric])
  apply (rule ACI_sym)
  apply (rule Quotient_rep_abs[OF Quotient_ACI_rexp, OF ACI_refl])
  apply blast
  done

global_interpretation brzozowski_quotient: rexp_DFA ACI_class ACI_deriv ACI_nullable ACI_lang
  defines brzozowski_quotient_closure = brzozowski_quotient.closure
    and check_eqv_brzq = brzozowski_quotient.check_eqv
    and reachable_brzq = brzozowski_quotient.reachable
    and automaton_brzq = brzozowski_quotient.automaton
    and match_brzq = brzozowski_quotient.match
proof (unfold_locales, goal_cases)
  case 1 show ?case by transfer (rule refl)
next
  case 2 show ?case by transfer (rule lang_deriv)
next
  case 3 show ?case by transfer (rule nullable_iff)
next
  case 4 show ?case by transfer
    (auto simp: ACI_decidable derivs_alt intro!: finite_subset[OF _ finite_derivs])
qed


subsection \<open>Brzozowski Derivatives Modulo ACI++ (Only Soundness)\<close>

global_interpretation nderiv: rexp_DA "\<lambda>x. norm x" nderiv nullable lang
  defines nderiv_closure = nderiv.closure
    and check_eqv_n = nderiv.check_eqv
    and reachable_n = nderiv.reachable
    and automaton_n = nderiv.automaton
    and match_n = nderiv.match
proof (unfold_locales, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by (rule lang_nderiv)
next
  case 3 show ?case by (rule nullable_iff)
qed


subsection \<open>Partial Derivatives\<close>

global_interpretation pderiv: rexp_DFA "\<lambda>r. {r}" pderiv_set "\<lambda>P. \<exists>p\<in>P. nullable p" "\<lambda>P. \<Union>(lang ` P)"
  defines pderiv_closure = pderiv.closure
    and check_eqv_p = pderiv.check_eqv
    and reachable_p = pderiv.reachable
    and automaton_p = pderiv.automaton
    and match_p = pderiv.match
proof (unfold_locales, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by (simp add: Deriv_pderiv)
next
  case 3 show ?case by (simp add: nullable_iff)
next
  case (4 s) note pderivs_lang_def[simp]
  { fix w :: "'a list"
    have "fold pderiv_set w = Union o image (pderivs_lang {w})" by (induct w) auto
  }
  hence "{fold pderiv_set w {s} |w. True} \<subseteq> Pow (pderivs_lang UNIV s)" by auto
  then show ?case by (rule finite_subset) (auto simp only: finite_pderivs_lang)
qed

global_interpretation pnderiv: rexp_DFA "\<lambda>r. r" pnderiv nullable lang
  defines pnderiv_closure = pnderiv.closure
    and check_eqv_pn = pnderiv.check_eqv
    and reachable_pn = pnderiv.reachable
    and automaton_pn = pnderiv.automaton
    and match_pn = pnderiv.match
proof (unfold_locales, goal_cases)
  case 1 show ?case by simp
next
  case 2 show ?case by (simp add: pnorm_def pset_deriv Deriv_pderiv pnderiv_alt)
next
  case 3 show ?case by (simp add: nullable_iff)
next
  case (4 s)
  then show ?case unfolding pnderiv_alt[abs_def]
    by (rule finite_surj[OF pderiv.fin, of _ "flatten PLUS" s]) (auto simp: fold_pnorm_deriv)
qed

subsection \<open>Languages as States\<close>

text \<open>Not executable but still instructive.\<close>

lemma Derivs_alt_def: "Derivs w L = fold Deriv w L"
  by (induct w arbitrary: L) simp_all

interpretation language: rexp_DFA lang Deriv "\<lambda>L. [] \<in> L" id
proof (unfold_locales, goal_cases)
  case (4 s)
  have "{fold Deriv w (lang s) |w. True} \<subseteq> (\<lambda>X. \<Union>(lang ` X)) ` Pow (pderivs_lang UNIV s)"
    by (auto simp: sym[OF Derivs_alt_def] Derivs_pderivs pderivs_lang_def)
  then show ?case by (rule finite_surj[OF iffD2[OF finite_Pow_iff finite_pderivs_lang_UNIV]])
qed simp_all

definition str_eq :: "'a lang => ('a list \<times> 'a list) set" ("\<approx>_" [100] 100)
where "\<approx>A \<equiv> {(x, y).  (\<forall>z. x @ z \<in> A \<longleftrightarrow> y @ z \<in> A)}"

lemma str_eq_alt: "\<approx>A = {(x, y). fold Deriv x A = fold Deriv y A}"
  unfolding str_eq_def set_eq_iff in_fold_Deriv by simp

lemma Myhill_Nerode2: "finite (UNIV // \<approx>lang r)"
  unfolding str_eq_alt quotient_def Image_def
  by (rule finite_surj[OF language.fin, of _ "\<lambda>X. {y. X = fold Deriv y (lang r)}" r]) auto

(*<*)
end
(*>*)
