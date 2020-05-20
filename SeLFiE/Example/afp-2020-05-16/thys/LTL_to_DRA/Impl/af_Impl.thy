(*  
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>af - Unfolding Functions - Optimized Code Equations\<close>

theory af_Impl
  imports Main "../af" LTL_Impl
begin

text \<open>Provide optimized code definitions for @{term "\<up>af"} and other functions, which use heuristics to reduce the formula size\<close>

subsection \<open>Helper Function\<close>

fun remove_and_or
where
  "remove_and_or (z or y) = (case z of 
      (((z' and x') or y') and x) \<Rightarrow> if x = x' \<and> y = y' then ((z' and x') or y') else remove_and_or z or remove_and_or y 
     | _ \<Rightarrow> remove_and_or z or remove_and_or y)"
| "remove_and_or (x and y) = remove_and_or x and remove_and_or y"
| "remove_and_or x = x"

lemma remove_and_or_correct: 
  "S \<Turnstile>\<^sub>P remove_and_or x \<longleftrightarrow> S \<Turnstile>\<^sub>P x"
proof (induction x)
  case (LTLOr x y)
    thus ?case 
    proof (induction x) 
      case (LTLAnd x' y')
        thus ?case
          proof (induction x')
            case (LTLOr x'' y'')
              thus ?case
                by (induction x'') auto
          qed auto
    qed auto
qed auto

subsection \<open>Optimized Equations\<close>

fun af_letter_simp
where
  "af_letter_simp true \<nu> = true"
| "af_letter_simp false \<nu> = false"
| "af_letter_simp p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_letter_simp (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_letter_simp (\<phi> and \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> af_letter_simp \<psi> \<nu>
    | false \<Rightarrow> false
    | p(a) \<Rightarrow> if a \<in> \<nu> then af_letter_simp \<psi> \<nu> else false
    | np(a) \<Rightarrow> if a \<notin> \<nu> then af_letter_simp \<psi> \<nu> else false
    | G \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = af_letter_simp \<phi>' \<nu>; 
        \<psi>'' = af_letter_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_and' (G \<phi>') \<phi>'' else mk_and id (mk_and' (G \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_and id (af_letter_simp \<phi> \<nu>) (af_letter_simp \<psi> \<nu>))"
| "af_letter_simp (\<phi> or \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> af_letter_simp \<psi> \<nu>
    | p(a) \<Rightarrow> if a \<in> \<nu> then true else af_letter_simp \<psi> \<nu>
    | np(a) \<Rightarrow> if a \<notin> \<nu> then true else af_letter_simp \<psi> \<nu>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = af_letter_simp \<phi>' \<nu>; 
        \<psi>'' = af_letter_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (af_letter_simp \<phi> \<nu>) (af_letter_simp \<psi> \<nu>))"
| "af_letter_simp (X \<phi>) \<nu> = \<phi>"
| "af_letter_simp (G \<phi>) \<nu> = mk_and' (G \<phi>) (af_letter_simp \<phi> \<nu>)"
| "af_letter_simp (F \<phi>) \<nu> = mk_or' (F \<phi>) (af_letter_simp \<phi> \<nu>)"
| "af_letter_simp (\<phi> U \<psi>) \<nu> = mk_or' (mk_and' (\<phi> U \<psi>) (af_letter_simp \<phi> \<nu>)) (af_letter_simp \<psi> \<nu>)"

lemma af_letter_simp_correct:
  "S \<Turnstile>\<^sub>P af_letter \<phi> \<nu> \<longleftrightarrow> S \<Turnstile>\<^sub>P af_letter_simp \<phi> \<nu>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct)
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct)

fun af_G_letter_simp
where
  "af_G_letter_simp true \<nu> = true"
| "af_G_letter_simp false \<nu> = false"
| "af_G_letter_simp p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_G_letter_simp (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_G_letter_simp (\<phi> and \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> af_G_letter_simp \<psi> \<nu>
    | false \<Rightarrow> false
    | p(a) \<Rightarrow> if a \<in> \<nu> then af_G_letter_simp \<psi> \<nu> else false
    | np(a) \<Rightarrow> if a \<notin> \<nu> then af_G_letter_simp \<psi> \<nu> else false
    | _ \<Rightarrow> mk_and id (af_G_letter_simp \<phi> \<nu>) (af_G_letter_simp \<psi> \<nu>))"
| "af_G_letter_simp (\<phi> or \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> af_G_letter_simp \<psi> \<nu>
    | p(a) \<Rightarrow> if a \<in> \<nu> then true else af_G_letter_simp \<psi> \<nu>
    | np(a) \<Rightarrow> if a \<notin> \<nu> then true else af_G_letter_simp \<psi> \<nu>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = af_G_letter_simp \<phi>' \<nu>; 
        \<psi>'' = af_G_letter_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (af_G_letter_simp \<phi> \<nu>) (af_G_letter_simp \<psi> \<nu>))"
| "af_G_letter_simp (X \<phi>) \<nu> = \<phi>"
| "af_G_letter_simp (G \<phi>) \<nu> = G \<phi>"
| "af_G_letter_simp (F \<phi>) \<nu> = mk_or' (F \<phi>) (af_G_letter_simp \<phi> \<nu>)"
| "af_G_letter_simp (\<phi> U \<psi>) \<nu> = mk_or' (mk_and' (\<phi> U \<psi>) (af_G_letter_simp \<phi> \<nu>)) (af_G_letter_simp \<psi> \<nu>)"

lemma af_G_letter_simp_correct:
  "S \<Turnstile>\<^sub>P af_G_letter \<phi> \<nu> \<longleftrightarrow> S \<Turnstile>\<^sub>P af_G_letter_simp \<phi> \<nu>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: mk_and_correct)
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct)

fun step_simp
where
  "step_simp p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "step_simp (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "step_simp (\<phi> and \<psi>) \<nu> = (mk_and id (step_simp \<phi> \<nu>) (step_simp \<psi> \<nu>))"
| "step_simp (\<phi> or \<psi>) \<nu> = (mk_or id (step_simp \<phi> \<nu>) (step_simp \<psi> \<nu>))"
| "step_simp (X \<phi>) \<nu> = remove_constants\<^sub>P \<phi>"
| "step_simp \<phi> \<nu> = \<phi>"

lemma step_simp_correct:
  "S \<Turnstile>\<^sub>P step \<phi> \<nu> \<longleftrightarrow> S \<Turnstile>\<^sub>P step_simp \<phi> \<nu>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct) 
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct remove_constants_correct[symmetric]) 

fun Unf_simp
where
  "Unf_simp (\<phi> and \<psi>) = (case \<phi> of
      true \<Rightarrow> Unf_simp \<psi>
    | false \<Rightarrow> false
    | G \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf_simp \<phi>'; \<psi>'' = Unf_simp \<psi>
       in
        (if \<phi>'' = \<psi>'' then mk_and' (G \<phi>') \<phi>'' else mk_and id (mk_and' (G \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_and id (Unf_simp \<phi>) (Unf_simp \<psi>))"
| "Unf_simp (\<phi> or \<psi>) = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> Unf_simp \<psi>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf_simp \<phi>'; \<psi>'' = Unf_simp \<psi>
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (Unf_simp \<phi>) (Unf_simp \<psi>))"
| "Unf_simp (G \<phi>) = mk_and' (G \<phi>) (Unf_simp \<phi>)"
| "Unf_simp (F \<phi>) = mk_or' (F \<phi>) (Unf_simp \<phi>)"
| "Unf_simp (\<phi> U \<psi>) = mk_or' (mk_and' (\<phi> U \<psi>) (Unf_simp \<phi>)) (Unf_simp \<psi>)"
| "Unf_simp \<phi> = \<phi>"

lemma Unf_simp_correct:
  "S \<Turnstile>\<^sub>P Unf \<phi> \<longleftrightarrow> S \<Turnstile>\<^sub>P Unf_simp \<phi>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct)
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct)

fun Unf\<^sub>G_simp
where
  "Unf\<^sub>G_simp (\<phi> and \<psi>) = mk_and id (Unf\<^sub>G_simp \<phi>) (Unf\<^sub>G_simp \<psi>)"
| "Unf\<^sub>G_simp (\<phi> or \<psi>) = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> Unf\<^sub>G_simp \<psi>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf\<^sub>G_simp \<phi>'; \<psi>'' = Unf\<^sub>G_simp \<psi>
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (Unf\<^sub>G_simp \<phi>) (Unf\<^sub>G_simp \<psi>))"
| "Unf\<^sub>G_simp (F \<phi>) = mk_or' (F \<phi>) (Unf\<^sub>G_simp \<phi>)"
| "Unf\<^sub>G_simp (\<phi> U \<psi>) = mk_or' (mk_and' (\<phi> U \<psi>) (Unf\<^sub>G_simp \<phi>)) (Unf\<^sub>G_simp \<psi>)"
| "Unf\<^sub>G_simp \<phi> = \<phi>"

lemma Unf\<^sub>G_simp_correct:
  "S \<Turnstile>\<^sub>P Unf\<^sub>G \<phi> \<longleftrightarrow> S \<Turnstile>\<^sub>P Unf\<^sub>G_simp \<phi>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct)
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct)

fun af_letter_opt_simp
where
  "af_letter_opt_simp true \<nu> = true"
| "af_letter_opt_simp false \<nu> = false"
| "af_letter_opt_simp p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_letter_opt_simp (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_letter_opt_simp (\<phi> and \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> af_letter_opt_simp \<psi> \<nu>
    | false \<Rightarrow> false
    | p(a) \<Rightarrow> if a \<in> \<nu> then af_letter_opt_simp \<psi> \<nu> else false
    | np(a) \<Rightarrow> if a \<notin> \<nu> then af_letter_opt_simp \<psi> \<nu> else false
    | G \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf_simp \<phi>'; 
        \<psi>'' = af_letter_opt_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_and' (G \<phi>') \<phi>'' else mk_and id (mk_and' (G \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_and id (af_letter_opt_simp \<phi> \<nu>) (af_letter_opt_simp \<psi> \<nu>))"
| "af_letter_opt_simp (\<phi> or \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> af_letter_opt_simp \<psi> \<nu>
    | p(a) \<Rightarrow> if a \<in> \<nu> then true else af_letter_opt_simp \<psi> \<nu>
    | np(a) \<Rightarrow> if a \<notin> \<nu> then true else af_letter_opt_simp \<psi> \<nu>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf_simp \<phi>'; 
        \<psi>'' = af_letter_opt_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (af_letter_opt_simp \<phi> \<nu>) (af_letter_opt_simp \<psi> \<nu>))"
| "af_letter_opt_simp (X \<phi>) \<nu> = Unf_simp \<phi>"
| "af_letter_opt_simp (G \<phi>) \<nu> = mk_and' (G \<phi>) (Unf_simp \<phi>)"
| "af_letter_opt_simp (F \<phi>) \<nu> = mk_or' (F \<phi>) (Unf_simp \<phi>)"
| "af_letter_opt_simp (\<phi> U \<psi>) \<nu> = mk_or' (mk_and' (\<phi> U \<psi>) (Unf_simp \<phi>)) (Unf_simp \<psi>)"

lemma af_letter_opt_simp_correct:
  "S \<Turnstile>\<^sub>P af_letter_opt \<phi> \<nu> \<longleftrightarrow> S \<Turnstile>\<^sub>P af_letter_opt_simp \<phi> \<nu>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct) 
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct Unf_simp_correct) 

fun af_G_letter_opt_simp
where
  "af_G_letter_opt_simp true \<nu> = true"
| "af_G_letter_opt_simp false \<nu> = false"
| "af_G_letter_opt_simp p(a) \<nu> = (if a \<in> \<nu> then true else false)"
| "af_G_letter_opt_simp (np(a)) \<nu>  = (if a \<notin> \<nu> then true else false)"
| "af_G_letter_opt_simp (\<phi> and \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> af_G_letter_opt_simp \<psi> \<nu>
    | false \<Rightarrow> false
    | p(a) \<Rightarrow> if a \<in> \<nu> then af_G_letter_opt_simp \<psi> \<nu> else false
    | np(a) \<Rightarrow> if a \<notin> \<nu> then af_G_letter_opt_simp \<psi> \<nu> else false
    | _ \<Rightarrow> mk_and id (af_G_letter_opt_simp \<phi> \<nu>) (af_G_letter_opt_simp \<psi> \<nu>))"
| "af_G_letter_opt_simp (\<phi> or \<psi>) \<nu> = (case \<phi> of
      true \<Rightarrow> true
    | false \<Rightarrow> af_G_letter_opt_simp \<psi> \<nu>
    | p(a) \<Rightarrow> if a \<in> \<nu> then true else af_G_letter_opt_simp \<psi> \<nu>
    | np(a) \<Rightarrow> if a \<notin> \<nu> then true else af_G_letter_opt_simp \<psi> \<nu>
    | F \<phi>' \<Rightarrow>  
      (let 
        \<phi>'' = Unf\<^sub>G_simp \<phi>'; 
        \<psi>'' = af_G_letter_opt_simp \<psi> \<nu> 
       in
        (if \<phi>'' = \<psi>'' then mk_or' (F \<phi>') \<phi>'' else mk_or id (mk_or' (F \<phi>') \<phi>'') \<psi>''))
    | _ \<Rightarrow> mk_or id (af_G_letter_opt_simp \<phi> \<nu>) (af_G_letter_opt_simp \<psi> \<nu>))"
| "af_G_letter_opt_simp (X \<phi>) \<nu> = Unf\<^sub>G_simp \<phi>"
| "af_G_letter_opt_simp (G \<phi>) \<nu> = G \<phi>"
| "af_G_letter_opt_simp (F \<phi>) \<nu> = mk_or' (F \<phi>) (Unf\<^sub>G_simp \<phi>)"
| "af_G_letter_opt_simp (\<phi> U \<psi>) \<nu> = mk_or' (mk_and' (\<phi> U \<psi>) (Unf\<^sub>G_simp \<phi>)) (Unf\<^sub>G_simp \<psi>)"

lemma af_G_letter_opt_simp_correct:
  "S \<Turnstile>\<^sub>P af_G_letter_opt \<phi> \<nu> \<longleftrightarrow> S \<Turnstile>\<^sub>P af_G_letter_opt_simp \<phi> \<nu>"
proof (induction \<phi>)
  case (LTLAnd \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_and_correct mk_and'_correct) 
next
  case (LTLOr \<phi> \<psi>)
    thus ?case
      by (cases \<phi>) (auto simp add: Let_def mk_or_correct mk_or'_correct)
qed (simp_all add: mk_and_correct mk_and'_correct mk_or_correct mk_or'_correct Unf\<^sub>G_simp_correct) 

subsection \<open>Register Code Equations\<close>
 
lemma [code]: 
  "\<up>af (Abs \<phi>) \<nu> = Abs (remove_and_or (af_letter_simp \<phi> \<nu>))"
  unfolding af_abs.f_abs.abs_eq af_letter_abs_def ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using af_letter_simp_correct remove_and_or_correct by blast

lemma [code]:
  "\<up>af\<^sub>G (Abs \<phi>) \<nu> = Abs (remove_and_or (af_G_letter_simp \<phi> \<nu>))"
  unfolding af_G_abs.f_abs.abs_eq af_G_letter_abs_def ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using af_G_letter_simp_correct remove_and_or_correct by blast

lemma [code]: 
  "\<up>step (Abs \<phi>) \<nu> = Abs (step_simp \<phi> \<nu>)"
  unfolding step_abs.abs_eq ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using step_simp_correct by blast

lemma [code]: 
  "\<up>Unf (Abs \<phi>) = Abs (remove_and_or (Unf_simp \<phi>))"
  unfolding Unf_abs.abs_eq ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using Unf_simp_correct remove_and_or_correct by blast

lemma [code]: 
  "\<up>Unf\<^sub>G (Abs \<phi>) = Abs (remove_and_or (Unf\<^sub>G_simp \<phi>))"
  unfolding Unf\<^sub>G_abs.abs_eq ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using Unf\<^sub>G_simp_correct remove_and_or_correct by blast

lemma [code]: 
  "\<up>af\<^sub>\<UU> (Abs \<phi>) \<nu> = Abs (remove_and_or (af_letter_opt_simp \<phi> \<nu>))"
  unfolding af_abs_opt.f_abs.abs_eq af_letter_abs_opt_def ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using af_letter_opt_simp_correct remove_and_or_correct by blast

lemma [code]:
  "\<up>af\<^sub>G\<^sub>\<UU> (Abs \<phi>) \<nu> = Abs (remove_and_or (af_G_letter_opt_simp \<phi> \<nu>))"
  unfolding af_G_abs_opt.f_abs.abs_eq af_G_letter_abs_opt_def ltl_prop_equiv_quotient.abs_eq_iff ltl_prop_equiv_def
  using af_G_letter_opt_simp_correct remove_and_or_correct by blast

end
