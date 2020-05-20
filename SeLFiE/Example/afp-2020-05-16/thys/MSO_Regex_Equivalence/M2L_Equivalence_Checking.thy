(* Author: Dmitriy Traytel *)

section \<open>Deciding Equivalence of M2L Formulas\<close>

(*<*)
theory M2L_Equivalence_Checking
imports
  Pi_Equivalence_Checking
  PNormalization
  Init_Normalization
  M2L_Normalization
  Pi_Regular_Exp_Dual
begin
(*>*)

global_interpretation embed "set o \<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<epsilon> \<Sigma>"
  for \<Sigma> :: "'a :: linorder list"
  defines
      \<DD> = "embed.lderiv lookup (\<epsilon> \<Sigma>)"
  and Co\<DD> = "embed.lderiv_dual lookup (\<epsilon> \<Sigma>)"
  by unfold_locales (auto simp: \<sigma>_def \<pi>_def \<epsilon>_def set_n_lists)

lemma enum_not_empty[simp]: "Enum.enum \<noteq> []" (is "?enum \<noteq> []")
proof (rule notI)
  assume "?enum = []"
  hence "set ?enum = {}" by simp
  thus False unfolding UNIV_enum[symmetric] by simp
qed

global_interpretation \<Phi>: formula "Enum.enum :: 'a :: {enum, linorder} list"
  defines
      pre_wf_formula = \<Phi>.pre_wf_formula
  and wf_formula = \<Phi>.wf_formula
  and rexp_of = \<Phi>.rexp_of
  and rexp_of_alt = \<Phi>.rexp_of_alt
  and rexp_of_alt' = \<Phi>.rexp_of_alt'
  and rexp_of' = \<Phi>.rexp_of'
  and rexp_of'' = \<Phi>.rexp_of''
  and valid_ENC = \<Phi>.valid_ENC
  and ENC = \<Phi>.ENC
  and dec_interp = \<Phi>.dec_interp
  by unfold_locales (auto simp: \<sigma>_def \<pi>_def set_n_lists)

lemma lang_Plus_Zero: "lang \<Sigma> n (Plus r One) = lang \<Sigma> n (Plus s One) \<longleftrightarrow> lang \<Sigma> n r - {[]} = lang \<Sigma> n s - {[]}"
  by auto

lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of]
lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of']
lemmas lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm = trans[OF sym[OF \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_norm] \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L_rexp_of'']

setup \<open>Sign.map_naming (Name_Space.mandatory_path "slow")\<close>

global_interpretation D: rexp_DFA "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>"
  "\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>" final "alphabet.wf (wf_atom \<Sigma>) n" pnorm "lang \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  defines
      test = "rexp_DA.test (final :: 'a atom rexp \<Rightarrow> bool)"
  and step = "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n"
  and closure = "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n"
  and check_eqvRE = "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n"
  and test_invariant = "rexp_DA.test_invariant (final :: 'a atom rexp \<Rightarrow> bool) ::
    (('a \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> bool"
  and step_invariant = "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n"
  and closure_invariant = "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n"
  and counterexampleRE = "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) final pnorm n"
  and reachable = "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n"
  and automaton = "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. \<guillemotleft>pnorm (inorm x)\<guillemotright>) (\<lambda>a r. \<guillemotleft>\<DD> \<Sigma> a r\<guillemotright>) pnorm n"
  by unfold_locales (auto simp only: comp_apply
    ACI_norm_wf ACI_norm_lang wf_inorm lang_inorm wf_pnorm lang_pnorm wf_lderiv lang_lderiv
    lang_final finite_fold_lderiv dest!: lang_subset_lists)

definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   slow.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (slow.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "slow.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF slow.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: slow.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

lemma completeness:
  assumes "\<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>" "wf_formula n (FOr \<phi> \<psi>)"
  shows "slow.check_eqv n \<phi> \<psi>"
  using assms(2) unfolding slow.check_eqv_def
  by (intro conjI[OF assms(2) slow.D.check_eqv_complete[OF iffD2[OF lang_Plus_Zero]],
                OF box_equals[OF assms(1) lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]])
   (auto intro!: \<Phi>.wf_rexp_of'')

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

setup \<open>Sign.map_naming (Name_Space.mandatory_path "fast")\<close>

global_interpretation D: rexp_DA_no_post "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup "\<lambda>x. pnorm (inorm x)"
  "\<lambda>a r. pnorm (\<DD> \<Sigma> a r)" final "alphabet.wf (wf_atom \<Sigma>) n" "lang \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  defines
      test = "rexp_DA.test (final :: 'a atom rexp \<Rightarrow> bool)"
  and step = "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n"
  and closure = "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n"
  and check_eqvRE = "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n"
  and test_invariant = "rexp_DA.test_invariant (final :: 'a atom rexp \<Rightarrow> bool) ::
    (('a \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> bool"
  and step_invariant = "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n"
  and closure_invariant = "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n"
  and counterexampleRE = "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) final id n"
  and reachable = "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n"
  and automaton = "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm (inorm x)) (\<lambda>a r. pnorm (\<DD> \<Sigma> a r)) id n"
  by unfold_locales (auto simp only: comp_apply
    ACI_norm_wf ACI_norm_lang wf_inorm lang_inorm wf_pnorm lang_pnorm wf_lderiv lang_lderiv id_apply
    lang_final dest!: lang_subset_lists)

definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   fast.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (fast.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "fast.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF fast.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: fast.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

setup \<open>Sign.map_naming (Name_Space.mandatory_path "dual")\<close>

global_interpretation D: rexp_DA_no_post "\<sigma> \<Sigma>" "wf_atom \<Sigma>" \<pi> lookup
  "\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))" "\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)" final_dual
  "alphabet.wf_dual (wf_atom \<Sigma>) n" "lang_dual \<Sigma> n" n
  for \<Sigma> :: "'a :: linorder list" and n :: nat
  defines
      test = "rexp_DA.test (final_dual :: 'a atom rexp_dual \<Rightarrow> bool)"
  and step = "rexp_DA.step (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n"
  and closure = "rexp_DA.closure (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n"
  and check_eqvRE = "rexp_DA.check_eqv (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n"
  and test_invariant = "rexp_DA.test_invariant (final_dual :: 'a atom rexp_dual \<Rightarrow> bool) ::
    (('a \<times> bool list) list \<times> _) list \<times> _ \<Rightarrow> bool"
  and step_invariant = "rexp_DA.step_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n"
  and closure_invariant = "rexp_DA.closure_invariant (\<sigma> \<Sigma>) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n"
  and counterexampleRE = "rexp_DA.counterexample (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) final_dual id n"
  and reachable = "rexp_DA.reachable (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n"
  and automaton = "rexp_DA.automaton (\<sigma> \<Sigma>) (\<lambda>x. pnorm_dual (rexp_dual_of (inorm x))) (\<lambda>a r. pnorm_dual (Co\<DD> \<Sigma> a r)) id n"
  by unfold_locales (auto simp only: comp_apply id_apply
    wf_inorm lang_inorm
    wf_dual_pnorm_dual lang_dual_pnorm_dual
    wf_dual_rexp_dual_of lang_dual_rexp_dual_of
    wf_dual_lderiv_dual lang_dual_lderiv_dual
    lang_dual_final_dual dest!: lang_dual_subset_lists)

definition check_eqv where
"check_eqv n \<phi> \<psi> \<longleftrightarrow> wf_formula n (FOr \<phi> \<psi>) \<and>
   dual.check_eqvRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One)"

definition counterexample where
"counterexample n \<phi> \<psi> =
   map_option (\<lambda>w. dec_interp n (FOV (FOr \<phi> \<psi>)) w)
   (dual.counterexampleRE Enum.enum n (Plus (rexp_of'' n (norm \<phi>)) One) (Plus (rexp_of'' n (norm \<psi>)) One))"

lemma soundness: "dual.check_eqv n \<phi> \<psi> \<Longrightarrow> \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<phi> = \<Phi>.lang\<^sub>M\<^sub>2\<^sub>L n \<psi>"
  by (rule box_equals[OF iffD1[OF lang_Plus_Zero, OF dual.D.check_eqv_sound]
  sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]] sym[OF trans[OF lang\<^sub>M\<^sub>2\<^sub>L_rexp_of''_norm]]])
   (auto simp: dual.check_eqv_def intro!: \<Phi>.wf_rexp_of'')

setup \<open>Sign.map_naming Name_Space.parent_path\<close>

(*<*)
end
(*>*)
