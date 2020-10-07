(*<*)
theory Propositional_Logic
imports Abstract_Completeness
begin
(*>*)

section \<open>Toy instantiation: Propositional Logic\<close>

datatype fmla = Atom nat | Neg fmla | Conj fmla fmla

primrec max_depth where
  "max_depth (Atom _) = 0"
| "max_depth (Neg \<phi>) = Suc (max_depth \<phi>)"
| "max_depth (Conj \<phi> \<psi>) = Suc (max (max_depth \<phi>) (max_depth \<psi>))"

lemma max_depth_0: "max_depth \<phi> = 0 = (\<exists>n. \<phi> = Atom n)"
  by (cases \<phi>) auto

lemma max_depth_Suc: "max_depth \<phi> = Suc n = ((\<exists>\<psi>. \<phi> = Neg \<psi> \<and> max_depth \<psi> = n) \<or>
  (\<exists>\<psi>1 \<psi>2. \<phi> = Conj \<psi>1 \<psi>2 \<and> max (max_depth \<psi>1) (max_depth \<psi>2) = n))"
  by (cases \<phi>) auto

abbreviation "atoms \<equiv> smap Atom nats"
abbreviation "depth1 \<equiv>
  sinterleave (smap Neg atoms) (smap (case_prod Conj) (sproduct atoms atoms))"

abbreviation "sinterleaves \<equiv> fold sinterleave"

fun extendLevel where "extendLevel (belowN, N) =
  (let Next = sinterleaves
    (map (smap (case_prod Conj)) [sproduct belowN N, sproduct N belowN, sproduct N N])
    (smap Neg N)
  in (sinterleave belowN N, Next))"

lemma extendLevel_step:
  "\<lbrakk>sset belowN = {\<phi>. max_depth \<phi> < n};
    sset N = {\<phi>. max_depth \<phi> = n}; st = (belowN, N)\<rbrakk> \<Longrightarrow>
  \<exists>belowNext Next. extendLevel st = (belowNext, Next) \<and>
     sset belowNext = {\<phi>. max_depth \<phi> < Suc n} \<and> sset Next = {\<phi>. max_depth \<phi> = Suc n}"
  by (auto simp: sset_sinterleave sset_sproduct stream.set_map
    image_iff max_depth_Suc)

lemma sset_atoms: "sset atoms = {\<phi>. max_depth \<phi> < 1}"
  by (auto simp: stream.set_map max_depth_0)

lemma sset_depth1: "sset depth1 = {\<phi>. max_depth \<phi> = 1}"
  by (auto simp: sset_sinterleave sset_sproduct stream.set_map
    max_depth_Suc max_depth_0 max_def image_iff)

lemma extendLevel_Nsteps:
  "\<lbrakk>sset belowN = {\<phi>. max_depth \<phi> < n}; sset N = {\<phi>. max_depth \<phi> = n}\<rbrakk> \<Longrightarrow>
  \<exists>belowNext Next. (extendLevel ^^ m) (belowN, N) = (belowNext, Next) \<and>
     sset belowNext = {\<phi>. max_depth \<phi> < n + m} \<and> sset Next = {\<phi>. max_depth \<phi> = n + m}"
proof (induction m arbitrary: belowN N n)
  case (Suc m)
  then obtain belowNext Next where "(extendLevel ^^ m) (belowN, N) = (belowNext, Next)"
    "sset belowNext = {\<phi>. max_depth \<phi> < n + m}" "sset Next = {\<phi>. max_depth \<phi> = n + m}"
    by blast
  thus ?case unfolding funpow.simps o_apply add_Suc_right
    by (intro extendLevel_step[of belowNext _ Next])
qed simp

corollary extendLevel:
  "\<exists>belowNext Next. (extendLevel ^^ m) (atoms, depth1) = (belowNext, Next) \<and>
     sset belowNext = {\<phi>. max_depth \<phi> < 1 + m} \<and> sset Next = {\<phi>. max_depth \<phi> = 1 + m}"
  by (rule extendLevel_Nsteps) (auto simp: sset_atoms sset_depth1)


definition "fmlas = sinterleave atoms (smerge (smap snd (siterate extendLevel (atoms, depth1))))"

lemma fmlas_UNIV: "sset fmlas = (UNIV :: fmla set)"
proof (intro equalityI subsetI UNIV_I)
  fix \<phi>
  show "\<phi> \<in> sset fmlas"
  proof (cases "max_depth \<phi>")
    case 0 thus ?thesis unfolding fmlas_def sset_sinterleave stream.set_map
      by (intro UnI1) (auto simp: max_depth_0)
  next
    case (Suc m) thus ?thesis using extendLevel[of m]
    unfolding fmlas_def sset_smerge sset_siterate sset_sinterleave stream.set_map
      by (intro UnI2) (auto, metis (mono_tags) mem_Collect_eq)
  qed
qed

datatype rule = Idle | Ax nat | NegL fmla | NegR fmla | ConjL fmla fmla | ConjR fmla fmla

abbreviation "mkRules f \<equiv> smap f fmlas"
abbreviation "mkRulePairs f \<equiv> smap (case_prod f) (sproduct fmlas fmlas)"

definition rules where
  "rules = Idle ## 
     sinterleaves [mkRules NegL, mkRules NegR, mkRulePairs ConjL, mkRulePairs ConjR]
     (smap Ax nats)"

lemma rules_UNIV: "sset rules = (UNIV :: rule set)"
  unfolding rules_def by (auto simp: sset_sinterleave sset_sproduct stream.set_map
    fmlas_UNIV image_iff) (metis rule.exhaust)

type_synonym state = "fmla fset * fmla fset"

fun eff' :: "rule \<Rightarrow> state \<Rightarrow> state fset option" where
  "eff' Idle (\<Gamma>, \<Delta>) = Some {|(\<Gamma>, \<Delta>)|}"
| "eff' (Ax n) (\<Gamma>, \<Delta>) =
    (if Atom n |\<in>| \<Gamma> \<and> Atom n |\<in>| \<Delta> then Some {||} else None)"
| "eff' (NegL \<phi>) (\<Gamma>, \<Delta>) =
    (if Neg \<phi> |\<in>| \<Gamma> then Some {|(\<Gamma> |-| {| Neg \<phi> |}, finsert \<phi> \<Delta>)|} else None)"
| "eff' (NegR \<phi>) (\<Gamma>, \<Delta>) =
    (if Neg \<phi> |\<in>| \<Delta> then Some {|(finsert \<phi> \<Gamma>, \<Delta> |-| {| Neg \<phi> |})|} else None)"
| "eff' (ConjL \<phi> \<psi>) (\<Gamma>, \<Delta>) =
    (if Conj \<phi> \<psi> |\<in>| \<Gamma>
    then Some {|(finsert \<phi> (finsert \<psi> (\<Gamma> |-| {| Conj \<phi> \<psi> |})), \<Delta>)|}
    else None)"
| "eff' (ConjR \<phi> \<psi>) (\<Gamma>, \<Delta>) =
    (if Conj \<phi> \<psi> |\<in>| \<Delta>
    then Some {|(\<Gamma>, finsert \<phi> (\<Delta> |-| {| Conj \<phi> \<psi> |})), (\<Gamma>, finsert \<psi> (\<Delta> |-| {| Conj \<phi> \<psi> |}))|}
    else None)"


abbreviation "Disj \<phi> \<psi> \<equiv> Neg (Conj (Neg \<phi>) (Neg \<psi>))"
abbreviation "Imp \<phi> \<psi> \<equiv> Disj (Neg \<phi>) \<psi>"
abbreviation "Iff \<phi> \<psi> \<equiv> Conj (Imp \<phi> \<psi>) (Imp \<psi> \<phi>)"

definition "thm1 \<equiv> ({|Conj (Atom 0) (Neg (Atom 0))|}, {||})"

declare Stream.smember_code [code del]
lemma [code]: "Stream.smember x (y ## s) = (x = y \<or> Stream.smember x s)"
  unfolding Stream.smember_def by auto

interpretation RuleSystem "\<lambda>r s ss. eff' r s = Some ss" rules UNIV
  by unfold_locales (auto simp: rules_UNIV intro: exI[of _ Idle])

interpretation PersistentRuleSystem "\<lambda>r s ss. eff' r s = Some ss" rules UNIV
proof (unfold_locales, unfold enabled_def per_def rules_UNIV, clarsimp)
  fix r \<Gamma> \<Delta> ss r' \<Gamma>' \<Delta>' ss'
  assume "r' \<noteq> r" "eff' r (\<Gamma>, \<Delta>) = Some ss" "eff' r' (\<Gamma>, \<Delta>) = Some ss'" "(\<Gamma>', \<Delta>') |\<in>| ss'"
  then show "\<exists>sl. eff' r (\<Gamma>', \<Delta>') = Some sl"
    by (cases r r' rule: rule.exhaust[case_product rule.exhaust]) (auto split: if_splits)
qed

definition "rho \<equiv> i.fenum rules"
definition "propTree \<equiv> i.mkTree eff' rho"

export_code propTree thm1 in Haskell module_name PropInstance (* file "." *)

(*<*)
end
(*>*)
