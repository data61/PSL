(* Author: Dmitriy Traytel *)

section "Some Useful Regular Operators"

(*<*)
theory Pi_Regular_Operators
imports Pi_Derivatives "HOL-Library.While_Combinator"
begin
(*>*)

primrec REV :: "'a rexp \<Rightarrow> 'a rexp" where
  "REV Zero = Zero"
| "REV Full = Full"
| "REV One = One"
| "REV (Atom a) = Atom a"
| "REV (Plus r s) = Plus (REV r) (REV s)"
| "REV (Times r s) = Times (REV s) (REV r)"
| "REV (Star r) = Star (REV r)"
| "REV (Not r) = Not (REV r)"
| "REV (Inter r s) = Inter (REV r) (REV s)"
| "REV (Pr r) = Pr (REV r)"

lemma REV_REV[simp]: "REV (REV r) = r"
  by (induct r) auto

lemma final_REV[simp]: "final (REV r) = final r"
  by (induct r) auto

lemma REV_PLUS: "REV (PLUS xs) = PLUS (map REV xs)"
  by (induct xs rule: list_singleton_induct) auto

lemma (in alphabet) wf_REV[simp]: "wf n r \<Longrightarrow> wf n (REV r)"
  by (induct r arbitrary: n) auto

lemma (in project) lang_REV[simp]: "lang n (REV r) = rev ` lang n r"
  by (induct r arbitrary: n) (auto simp: image_image rev_map image_set_diff)

context embed
begin

primrec rderiv :: "'a \<Rightarrow> 'b rexp \<Rightarrow> 'b rexp" where
  "rderiv _ Zero = Zero"
| "rderiv _ Full = Full"
| "rderiv _ One = Zero"
| "rderiv a (Atom b) = (if lookup b a then One else Zero)"
| "rderiv a (Plus r s) = Plus (rderiv a r) (rderiv a s)"
| "rderiv a (Times r s) =
    (let rs' = Times r (rderiv a s)
     in if final s then Plus rs' (rderiv a r) else rs')"
| "rderiv a (Star r) = Times (Star r) (rderiv a r)"
| "rderiv a (Not r) = Not (rderiv a r)"
| "rderiv a (Inter r s) = Inter (rderiv a r) (rderiv a s)"
| "rderiv a (Pr r) = Pr (PLUS (map (\<lambda>a'. rderiv a' r) (embed a)))"

primrec rderivs where
  "rderivs [] r = r"
| "rderivs (w#ws) r = rderivs ws (rderiv w r)"

lemma rderivs_snoc: "rderivs (ws @ [w]) r = rderiv w (rderivs ws r)"
  by (induct ws arbitrary: r) auto

lemma rderivs_append: "rderivs (ws @ ws') r = rderivs ws' (rderivs ws r)"
  by (induct ws arbitrary: r) auto

lemma rderiv_lderiv: "rderiv as r = REV (lderiv as (REV r))"
  by (induct r arbitrary: as) (auto simp: Let_def o_def REV_PLUS)

lemma rderivs_lderivs: "rderivs w r = REV (lderivs w (REV r))"
  by (induct w arbitrary: r) (auto simp: rderiv_lderiv)

lemma wf_rderiv[simp]: "wf n r \<Longrightarrow> wf n (rderiv w r)"
  unfolding rderiv_lderiv by (rule wf_REV[OF wf_lderiv[OF wf_REV]])

lemma wf_rderivs[simp]: "wf n r \<Longrightarrow> wf n (rderivs ws r)"
  unfolding rderivs_lderivs by (rule wf_REV[OF wf_lderivs[OF wf_REV]])

lemma lang_rderiv: "\<lbrakk>wf n r; as \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> lang n (rderiv as r) = rQuot as (lang n r)"
  unfolding rderiv_lderiv rQuot_rev_lQuot by (simp add: lang_lderiv)

lemma lang_rderivs: "\<lbrakk>wf n r; wf_word n w\<rbrakk> \<Longrightarrow> lang n (rderivs w r) = rQuots w (lang n r)"
  unfolding rderivs_lderivs rQuots_rev_lQuots by (simp add: lang_lderivs)

corollary rderivs_final:
assumes "wf n r" "wf_word n w"
shows "final (rderivs w r) \<longleftrightarrow> rev w \<in> lang n r"
  using lang_rderivs[OF assms] lang_final[of "rderivs w r" n] by auto

lemma toplevel_summands_REV[simp]: "toplevel_summands (REV r) = REV ` toplevel_summands r"
  by (induct r) auto

lemma ACI_norm_REV: "\<guillemotleft>REV \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>REV r\<guillemotright>"
proof (induct r)
  case (Plus r s)
  show ?case
    using [[unfold_abs_def = false]]
    unfolding REV.simps ACI_norm.simps Plus[symmetric] image_Un[symmetric]
      toplevel_summands.simps(1) toplevel_summands_ACI_norm toplevel_summands_REV
    unfolding toplevel_summands.simps(1)[symmetric] ACI_norm_flatten toplevel_summands_REV
    unfolding ACI_norm_flatten[symmetric] toplevel_summands_ACI_norm
    ..
qed auto

lemma ACI_norm_rderiv: "\<guillemotleft>rderiv as \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>rderiv as r\<guillemotright>"
  unfolding rderiv_lderiv by (metis ACI_norm_REV ACI_norm_lderiv)

lemma ACI_norm_rderivs: "\<guillemotleft>rderivs w \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>rderivs w r\<guillemotright>"
  unfolding rderivs_lderivs by (metis ACI_norm_REV ACI_norm_lderivs)

theorem finite_rderivs: "finite {\<guillemotleft>rderivs xs r\<guillemotright> | xs . True}"
  unfolding rderivs_lderivs
  by (subst ACI_norm_REV[symmetric]) (auto intro: finite_surj[OF finite_lderivs, of _ "\<lambda>r. \<guillemotleft>REV r\<guillemotright>"])

lemma lderiv_PLUS[simp]: "lderiv a (PLUS xs) = PLUS (map (lderiv a) xs)"
  by (induct xs rule: list_singleton_induct) auto

lemma rderiv_PLUS[simp]: "rderiv a (PLUS xs) = PLUS (map (rderiv a) xs)"
  by (induct xs rule: list_singleton_induct) auto

lemma lang_rderiv_lderiv: "lang n (rderiv a (lderiv b r)) = lang n (lderiv b (rderiv a r))"
  by (induct r arbitrary: n a b) (auto simp: Let_def conc_assoc)

lemma lang_lderiv_rderiv: "lang n (lderiv a (rderiv b r)) = lang n (rderiv b (lderiv a r))"
  by (induct r arbitrary: n a b) (auto simp: Let_def conc_assoc)

lemma lang_rderiv_lderivs[simp]: "\<lbrakk>wf n r; wf_word n w; a \<in> \<Sigma> n\<rbrakk> \<Longrightarrow>
  lang n (rderiv a (lderivs w r)) = lang n (lderivs w (rderiv a r))"
  by (induct w arbitrary: n r)
    (auto, auto simp: lang_lderivs lang_lderiv lang_rderiv lQuot_rQuot)

lemma lang_lderiv_rderivs[simp]: "\<lbrakk>wf n r; wf_word n w; a \<in> \<Sigma> n\<rbrakk> \<Longrightarrow>
  lang n (lderiv a (rderivs w r)) = lang n (rderivs w (lderiv a r))"
  by (induct w arbitrary: n r)
    (auto, auto simp: lang_rderivs lang_lderiv lang_rderiv lQuot_rQuot)
(*
primrec bideriv :: "'a \<Rightarrow> 'a \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "bideriv _ _ Zero = Zero"
| "bideriv _ _ One = Zero"
| "bideriv a b (Atom c) = Zero"
| "bideriv a b (Plus r s) = Plus (bideriv a b r) (bideriv a b s)"
| "bideriv a b (Times r s) =
    (let rs' = Times (lderiv a r) (rderiv b s)
     in if final r \<and> final s then Plus (Plus rs' (bideriv a b r)) (bideriv a b s)
        else if final r then Plus rs' (bideriv a b s)
        else if final s then Plus rs' (bideriv a b r)
        else rs')"
| "bideriv a b (Star r) = Plus (bideriv a b r) (TIMES [lderiv a r, Star r, rderiv b r])"
| "bideriv a b (Not r) = Not (bideriv a b r)"
| "bideriv a b (Inter r s) = Inter (bideriv a b r) (bideriv a b s)"
| "bideriv a b (Pr r) = Pr (PLUS (map (\<lambda>b. PLUS (map (\<lambda>a. bideriv a b r) (embed a))) (embed b)))"

lemma wf_bideriv[simp]: "wf n r \<Longrightarrow> wf n (bideriv a b r)"
  by (induct r arbitrary: n a b) (auto simp: maps_def Let_def)

lemma ACI_norm_bideriv_rderiv_lderiv: "\<guillemotleft>bideriv a b r\<guillemotright> = \<guillemotleft>rderiv b (lderiv a r)\<guillemotright>"
  by (induct r arbitrary: a b)
    (auto simp: Let_def maps_def o_def list_all2_map1 list_all2_map2 intro!: ACI_PLUS list_all2_refl)

lemma bideriv_rderiv_lderiv:
  "lang n (bideriv a b r) = lang n (rderiv b (lderiv a r))"
  by (induct r arbitrary: n a b) (auto simp: Let_def)

lemma lang_bideriv:
  "\<lbrakk>wf n r; a \<in> \<Sigma> n; b \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> lang n (bideriv a b r) = biQuot a b (lang n r)"
  by (auto simp: bideriv_rderiv_lderiv lang_lderiv lang_rderiv biQuot_rQuot_lQuot)

lemma ACI_norm_bideriv: "\<guillemotleft>bideriv a b \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>bideriv a b r\<guillemotright>"
  unfolding ACI_norm_bideriv_rderiv_lderiv by (metis ACI_norm_lderiv ACI_norm_rderiv)

fun biderivs where
  "biderivs [] [] r = r"
| "biderivs as [] r = lderivs as r"
| "biderivs [] bs r = rderivs bs r"
| "biderivs (a#as) (b#bs) r = biderivs as bs (bideriv a b r)"

lemma biderivs_rderivs_lderivs: "\<lbrakk>wf n r; wf_word n w1; wf_word n w2\<rbrakk> \<Longrightarrow>
  lang n (biderivs w1 w2 r) = lang n (rderivs w2 (lderivs w1 r))"
  by (induct arbitrary: r rule: biderivs.induct)
    (auto simp: lang_rderivs lang_lderivs bideriv_rderiv_lderiv)

lemma lang_biderivs:
  "\<lbrakk>wf n r; wf_word n w1; wf_word n w2\<rbrakk> \<Longrightarrow> lang n (biderivs w1 w2 r) = biQuots w1 w2 (lang n r)"
  by (auto simp: biderivs_rderivs_lderivs lang_lderivs lang_rderivs biQuots_rQuots_lQuots)

lemma wf_biderivs[simp]: "wf n r \<Longrightarrow> wf n (biderivs w1 w2 r)"
  by (induct arbitrary: r rule: biderivs.induct) auto
*)
definition "biderivs w1 w2 = rderivs w2 o lderivs w1"

lemma lang_biderivs: "\<lbrakk>wf n r; wf_word n w1; wf_word n w2\<rbrakk> \<Longrightarrow>
  lang n (biderivs w1 w2 r) = biQuots w1 w2 (lang n r)"
   unfolding biderivs_def by (auto simp: lang_rderivs lang_lderivs in_lists_conv_set)

lemma wf_biderivs[simp]: "wf n r \<Longrightarrow> wf n (biderivs w1 w2 r)"
  unfolding biderivs_def by simp

corollary biderivs_final:
assumes "wf n r" "wf_word n w1" "wf_word n w2"
shows "final (biderivs w1 w2 r) \<longleftrightarrow> w1 @ rev w2 \<in> lang n r"
  using lang_biderivs[OF assms] lang_final[of "biderivs w1 w2 r" n] by auto

lemma ACI_norm_biderivs: "\<guillemotleft>biderivs w1 w2 \<guillemotleft>r\<guillemotright>\<guillemotright> = \<guillemotleft>biderivs w1 w2 r\<guillemotright>"
  unfolding biderivs_def by (metis ACI_norm_lderivs ACI_norm_rderivs o_apply)

lemma "finite {\<guillemotleft>biderivs w1 w2 r\<guillemotright> | w1 w2 . True}"
proof -
  have "{\<guillemotleft>biderivs w1 w2 r\<guillemotright> | w1 w2 . True} =
    (\<Union>s \<in> {\<guillemotleft>lderivs as r\<guillemotright> | as . True}. {\<guillemotleft>rderivs bs s\<guillemotright> | bs . True})"
    unfolding biderivs_def by (fastforce simp: ACI_norm_rderivs)
  also have "finite \<dots>" by (rule iffD2[OF finite_UN[OF finite_lderivs] ballI[OF finite_rderivs]])
  finally show ?thesis .
qed

end


subsection \<open>Quotioning by the same letter\<close>

definition "fin_cut_same x xs = take (LEAST n. drop n xs = replicate (length xs - n) x) xs"

lemma fin_cut_same_Nil[simp]: "fin_cut_same x [] = []"
  unfolding fin_cut_same_def by simp

lemma Least_fin_cut_same: "(LEAST n. drop n xs = replicate (length xs - n) y) =
  length xs - length (takeWhile (\<lambda>x. x = y) (rev xs))"
  (is "Least ?P = ?min")
proof (rule Least_equality)
  show "?P ?min" by (induct xs rule: rev_induct) (auto simp:  Suc_diff_le replicate_append_same)
next
  fix m assume "?P m"
  have "length xs - m \<le> length (takeWhile (\<lambda>x. x = y) (rev xs))"
  proof (intro length_takeWhile_less_P_nth)
    fix i assume "i < length xs - m"
    hence "rev xs ! i \<in> set (drop m xs)"
      by (induct xs arbitrary: i rule: rev_induct) (auto simp: nth_Cons')
    with \<open>?P m\<close> show "rev xs ! i = y" by simp
  qed simp
  thus "?min \<le> m" by linarith
qed
    

lemma takeWhile_takes_all: "length xs = m \<Longrightarrow> m \<le> length (takeWhile P xs) \<longleftrightarrow> Ball (set xs) P"
  by hypsubst_thin (induct xs, auto)

lemma fin_cut_same_Cons[simp]: "fin_cut_same x (y # xs) =
  (if fin_cut_same x xs = [] then if x = y then [] else [y] else y # fin_cut_same x xs)"
  unfolding fin_cut_same_def Least_fin_cut_same
  apply auto
  apply (simp add: takeWhile_takes_all)
  apply (simp add: takeWhile_takes_all)
  apply auto
  apply (metis (full_types) Suc_diff_le length_rev length_takeWhile_le take_Suc_Cons)
  apply (simp add: takeWhile_takes_all)
  apply (subst takeWhile_append2)
  apply auto
  apply (simp add: takeWhile_takes_all)
  apply auto
  apply (metis (full_types) Suc_diff_le length_rev length_takeWhile_le take_Suc_Cons)
  done

lemma fin_cut_same_singleton[simp]: "fin_cut_same x (xs @ [x]) = fin_cut_same x xs"
  by (induct xs) auto

lemma fin_cut_same_replicate[simp]: "fin_cut_same x (xs @ replicate n x) = fin_cut_same x xs"
  by (induct n arbitrary: xs)
    (auto simp: replicate_append_same[symmetric] append_assoc[symmetric] simp del: append_assoc)

lemma fin_cut_sameE: "fin_cut_same x xs = ys \<Longrightarrow> \<exists>m. xs = ys @ replicate m x"
  by (induct xs arbitrary: ys) (auto, metis replicate_Suc)

definition "SAMEQUOT a A = {fin_cut_same a x @ replicate m a| x m. x \<in> A}"

lemma SAMEQUOT_mono: "A \<subseteq> B \<Longrightarrow> SAMEQUOT a A \<subseteq> SAMEQUOT a B"
  unfolding SAMEQUOT_def by auto

locale embed2 = embed \<Sigma> wf_atom project lookup embed
  for \<Sigma> :: "nat \<Rightarrow> 'a set"
  and wf_atom :: "nat \<Rightarrow> 'b :: linorder \<Rightarrow> bool"
  and project :: "'a \<Rightarrow> 'a"
  and lookup :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and embed :: "'a \<Rightarrow> 'a list" +
  fixes singleton :: "'a \<Rightarrow> 'b"
  assumes wf_singleton[simp]: "a \<in> \<Sigma> n \<Longrightarrow> wf_atom n (singleton a)"
  assumes lookup_singleton[simp]: "lookup (singleton a) a' = (a = a')"
begin

lemma finite_rderivs_same: "finite {\<guillemotleft>rderivs (replicate m a) r\<guillemotright> | m . True}"
  by (auto intro: finite_subset[OF _ finite_rderivs])

lemma wf_word_replicate[simp]: "a \<in> \<Sigma> n \<Longrightarrow> wf_word n (replicate m a)"
  by (induct m) auto

lemma star_singleton[simp]: "star {[x]} = {replicate m x | m . True}"
proof (intro equalityI subsetI)
  fix xs assume "xs \<in> star {[x]}"
  thus "xs \<in> {replicate m x | m . True}" by (induct xs) (auto, metis replicate_Suc)
qed (auto intro: Ball_starI)

definition "samequot a r = Times (flatten PLUS {\<guillemotleft>rderivs (replicate m a) r\<guillemotright> | m . True}) (Star (Atom (singleton a)))"

lemma wf_samequot: "\<lbrakk>wf n r; a \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> wf n (samequot a r)"
  unfolding samequot_def wf.simps wf_flatten_PLUS[OF finite_rderivs_same] by auto

lemma lang_samequot: "\<lbrakk>wf n r; a \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> 
   lang n (samequot a r) = SAMEQUOT a (lang n r)"
   unfolding SAMEQUOT_def samequot_def lang.simps lang_flatten_PLUS[OF finite_rderivs_same]
   apply (rule sym)
   apply (auto simp: lang_rderivs)
   apply (intro concI)
   apply auto
   apply (insert fin_cut_sameE[OF refl, of _ a])
   apply (drule meta_spec)
   apply (erule exE)
   apply (intro exI conjI)
   apply (rule refl)
   apply (auto simp: lang_rderivs)
   apply (erule subst)
   apply assumption
   apply (erule concE)
   apply (auto simp: lang_rderivs)
   apply (drule meta_spec)
   apply (erule exE)
   apply (intro exI conjI)
   defer
   apply assumption
   unfolding fin_cut_same_replicate
   apply (erule trans)
   unfolding fin_cut_same_replicate
   apply (rule refl)
   done

fun rderiv_and_add where
  "rderiv_and_add as (_ :: bool, rs) =
    (let
      r = \<guillemotleft>rderiv as (hd rs)\<guillemotright>
    in if r \<in> set rs then (False, rs) else (True, r # rs))"

definition "invar_rderiv_and_add as r brs \<equiv>
  (if fst brs then True else \<guillemotleft>rderiv as (hd (snd brs))\<guillemotright> \<in> set (snd brs)) \<and>
  snd brs \<noteq> [] \<and> distinct (snd brs) \<and>
  (\<forall>i < length (snd brs). snd brs ! i = \<guillemotleft>rderivs (replicate (length (snd brs) - 1 - i) as) r\<guillemotright>)"

lemma invar_rderiv_and_add_init: "invar_rderiv_and_add as r (True, [\<guillemotleft>r\<guillemotright>])"
  unfolding invar_rderiv_and_add_def by auto

lemma invar_rderiv_and_add_step: "invar_rderiv_and_add as r brs \<Longrightarrow> fst brs \<Longrightarrow>
  invar_rderiv_and_add as r (rderiv_and_add as brs)"
  unfolding invar_rderiv_and_add_def by (cases brs) (auto simp:
    Let_def nth_Cons' ACI_norm_rderiv rderivs_snoc[symmetric] neq_Nil_conv replicate_append_same)

lemma rderivs_replicate_mult: "\<lbrakk>\<guillemotleft>rderivs (replicate i as) r\<guillemotright> = \<guillemotleft>r\<guillemotright>; i > 0\<rbrakk> \<Longrightarrow>
  \<guillemotleft>rderivs (replicate (m * i) as) r\<guillemotright> = \<guillemotleft>r\<guillemotright>"
proof (induct m arbitrary: r)
  case (Suc m)
  hence "\<guillemotleft>rderivs (replicate (m * i) as) \<guillemotleft>rderivs (replicate i as) r\<guillemotright>\<guillemotright> = \<guillemotleft>r\<guillemotright>" 
    by (auto simp: ACI_norm_rderivs)
  thus ?case by (auto simp: ACI_norm_rderivs replicate_add rderivs_append)
qed simp

lemma rderivs_replicate_mult_rest: 
  assumes "\<guillemotleft>rderivs (replicate i as) r\<guillemotright> = \<guillemotleft>r\<guillemotright>" "k < i"
  shows "\<guillemotleft>rderivs (replicate (m * i + k) as) r\<guillemotright> = \<guillemotleft>rderivs (replicate k as) r\<guillemotright>" (is "?L = ?R")
proof -
  have "?L = \<guillemotleft>rderivs (replicate k as) \<guillemotleft>rderivs (replicate (m * i) as) r\<guillemotright>\<guillemotright>"
    by (simp add: ACI_norm_rderivs replicate_add rderivs_append)
  also have "\<guillemotleft>rderivs (replicate (m * i) as) r\<guillemotright> = \<guillemotleft>r\<guillemotright>" using assms
    by (simp add: rderivs_replicate_mult)
  finally show ?thesis by (simp add: ACI_norm_rderivs)
qed

lemma rderivs_replicate_mod: 
  assumes "\<guillemotleft>rderivs (replicate i as) r\<guillemotright> = \<guillemotleft>r\<guillemotright>" "i > 0"
  shows "\<guillemotleft>rderivs (replicate m as) r\<guillemotright> = \<guillemotleft>rderivs (replicate (m mod i) as) r\<guillemotright>" (is "?L = ?R")
  by (subst div_mult_mod_eq[symmetric, of m i])
    (intro rderivs_replicate_mult_rest[OF assms(1)] mod_less_divisor[OF assms(2)])

lemma rderivs_replicate_diff: "\<lbrakk>\<guillemotleft>rderivs (replicate i as) r\<guillemotright> = \<guillemotleft>rderivs (replicate j as) r\<guillemotright>; i > j\<rbrakk> \<Longrightarrow>
  \<guillemotleft>rderivs (replicate (i - j) as) (rderivs (replicate j as) r)\<guillemotright> = \<guillemotleft>rderivs (replicate j as) r\<guillemotright>"
  unfolding rderivs_append[symmetric] replicate_add[symmetric] by auto

lemma samequot_wf:
  assumes "wf n r" "while_option fst (rderiv_and_add as) (True, [\<guillemotleft>r\<guillemotright>]) = Some (b, rs)"
  shows "wf n (PLUS rs)"
proof -
  have "\<not> b" using while_option_stop[OF assms(2)] by simp
  from while_option_rule[where P="invar_rderiv_and_add as r",
    OF invar_rderiv_and_add_step assms(2) invar_rderiv_and_add_init]
    have *: "invar_rderiv_and_add as r (b, rs)" by simp
  thus "wf n (PLUS rs)" unfolding invar_rderiv_and_add_def wf_PLUS
    by (auto simp: in_set_conv_nth wf_rderivs[OF assms(1)])
qed

lemma samequot_soundness:
  assumes "while_option fst (rderiv_and_add as) (True, [\<guillemotleft>r\<guillemotright>]) = Some (b, rs)"
  shows "lang n (PLUS rs) = \<Union> (lang n ` {\<guillemotleft>rderivs (replicate m as) r\<guillemotright> | m. True})"
proof -
  have "\<not> b" using while_option_stop[OF assms] by simp
  moreover 
  from while_option_rule[where P="invar_rderiv_and_add as r",
    OF invar_rderiv_and_add_step assms invar_rderiv_and_add_init]
    have *: "invar_rderiv_and_add as r (b, rs)" by simp
  ultimately obtain i where i: "i < length rs" and "\<guillemotleft>rderivs (replicate (length rs - Suc i) as) r\<guillemotright> =
       \<guillemotleft>rderivs (replicate (Suc (length rs - Suc 0)) as) r\<guillemotright>" (is "\<guillemotleft>rderivs ?x r\<guillemotright> = _")
    unfolding invar_rderiv_and_add_def by (auto simp: in_set_conv_nth hd_conv_nth ACI_norm_rderiv
      rderivs_snoc[symmetric] replicate_append_same)
  with * have "\<guillemotleft>rderivs ?x r\<guillemotright> = \<guillemotleft>rderivs (replicate (length rs) as) r\<guillemotright>"
    by (auto simp: invar_rderiv_and_add_def)
  with i have cyc: "\<guillemotleft>rderivs (replicate (Suc i) as) (rderivs ?x r)\<guillemotright> = \<guillemotleft>rderivs ?x r\<guillemotright>"
    by (fastforce dest: rderivs_replicate_diff[OF sym])
  { fix m
    have "\<exists>i<length rs. rs ! i = \<guillemotleft>rderivs (replicate m as) r\<guillemotright>"
    proof (cases "m > length rs - Suc i")
      case True
      with i obtain m' where m: "m = m' + length rs - Suc i"
        by atomize_elim (auto intro: exI[of _ "m - (length rs - Suc i)"])
      with i have "\<guillemotleft>rderivs (replicate m as) r\<guillemotright> = \<guillemotleft>rderivs (replicate m' as) (rderivs ?x r)\<guillemotright>"
       unfolding replicate_add[symmetric] rderivs_append[symmetric] by (simp add: add.commute)
      also from cyc have "\<dots> = \<guillemotleft>rderivs (replicate (m' mod (Suc i)) as) (rderivs ?x r)\<guillemotright>" 
        by (elim rderivs_replicate_mod) simp
      also from i have "\<dots> = \<guillemotleft>rderivs (replicate (m' mod (Suc i) + length rs - Suc i) as) r\<guillemotright>" 
        unfolding rderivs_append[symmetric] replicate_add[symmetric] by (simp add: add.commute)
      also from m i have "\<dots> = \<guillemotleft>rderivs (replicate ((m - (length rs - Suc i)) mod (Suc i) + length rs - Suc i) as) r\<guillemotright>"
        by simp
      also have "\<dots> = \<guillemotleft>rderivs (replicate (length rs - Suc (i - (m - (length rs - Suc i)) mod (Suc i))) as) r\<guillemotright>"
        by (subst Suc_diff_le[symmetric])
          (metis less_Suc_eq_le mod_less_divisor zero_less_Suc, simp add: add.commute)
      finally have "\<exists>j < length rs. \<guillemotleft>rderivs (replicate m as) r\<guillemotright> = \<guillemotleft>rderivs (replicate (length rs - Suc j) as) r\<guillemotright>"
        using i by (metis less_imp_diff_less)
      with * show ?thesis unfolding invar_rderiv_and_add_def by auto
    next
      case False
      with i have "\<exists>j < length rs. m = length rs - Suc j"
        by (induct m)
          (metis diff_self_eq_0 gr_implies_not0 lessI nat.exhaust,
           metis (no_types) One_nat_def Suc_diff_Suc diff_Suc_1 gr0_conv_Suc less_imp_diff_less
             not_less_eq not_less_iff_gr_or_eq)
      with * show ?thesis unfolding invar_rderiv_and_add_def by auto
    qed
  }
  hence "\<Union> (lang n ` {\<guillemotleft>rderivs (replicate m as) r\<guillemotright> |m. True}) \<subseteq> lang n (PLUS rs)"
    by (fastforce simp: in_set_conv_nth intro!: bexI[rotated])
  moreover from * have "lang n (PLUS rs) \<subseteq> \<Union> (lang n ` {\<guillemotleft>rderivs (replicate m as) r\<guillemotright> |m. True})"
    unfolding invar_rderiv_and_add_def by (fastforce simp: in_set_conv_nth)
  ultimately show "lang n (PLUS rs) = \<Union> (lang n ` {\<guillemotleft>rderivs (replicate m as) r\<guillemotright> |m. True})" by blast
qed

lemma length_subset_card: "\<lbrakk>finite X; distinct (x # xs); set (x # xs) \<subseteq> X\<rbrakk> \<Longrightarrow> length xs < card X"
  by (metis card_mono distinct_card impossible_Cons not_le_imp_less order_trans)

lemma samequot_termination:
  assumes "while_option fst (rderiv_and_add as) (True, [\<guillemotleft>r\<guillemotright>]) = None" (is "?cl = None")
  shows "False"
proof -
  let ?D =  "{\<guillemotleft>rderivs (replicate m as) r\<guillemotright> | m . True}"
  let ?f = "\<lambda>(b, rs). card ?D + 1 - length rs + (if b then 1 else 0)"
  have "\<exists>st. ?cl = Some st"
    apply (rule measure_while_option_Some[of "invar_rderiv_and_add as r" _ _ ?f])
     apply (auto simp: invar_rderiv_and_add_init invar_rderiv_and_add_step)
    apply (auto simp: invar_rderiv_and_add_def Let_def neq_Nil_conv in_set_conv_nth
       intro!: diff_less_mono2 length_subset_card[OF finite_rderivs_same, simplified])
      apply auto []
     apply fastforce
    apply (metis Suc_less_eq nth_Cons_Suc)
    done
  with assms show False by auto
qed

definition "samequot_exec a r =
  Times (PLUS (snd (the (while_option fst (rderiv_and_add a) (True, [\<guillemotleft>r\<guillemotright>]))))) (Star (Atom (singleton a)))"

lemma wf_samequot_exec: "\<lbrakk>wf n r; as \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> wf n (samequot_exec as r)"
  unfolding samequot_exec_def
  by (cases "while_option fst (rderiv_and_add as) (True, [\<guillemotleft>r\<guillemotright>])")
    (auto dest: samequot_termination samequot_wf)

lemma samequot_exec_samequot: "lang n (samequot_exec as r) = lang n (samequot as r)"
  unfolding samequot_exec_def samequot_def lang.simps lang_flatten_PLUS[OF finite_rderivs_same]
  by (cases "while_option fst (rderiv_and_add as) (True, [\<guillemotleft>r\<guillemotright>])")
    (auto dest: samequot_termination dest!: samequot_soundness[of _ _ _ _ n] simp del: ACI_norm_lang)

lemma lang_samequot_exec:
  "\<lbrakk>wf n r; as \<in> \<Sigma> n\<rbrakk> \<Longrightarrow> lang n (samequot_exec as r) = SAMEQUOT as (lang n r)"
unfolding samequot_exec_samequot by (rule lang_samequot)

end

subsection \<open>Suffix and Prefix Languages\<close>

definition Suffix :: "'a lang \<Rightarrow> 'a lang" where
  "Suffix L = {w. \<exists>u. u @ w \<in> L}"

definition Prefix :: "'a lang \<Rightarrow> 'a lang" where
  "Prefix L = {w. \<exists>u. w @ u \<in> L}"

lemma Prefix_Suffix: "Prefix L = rev ` Suffix (rev ` L)"
  unfolding Prefix_def Suffix_def
  by (auto simp: rev_append_invert
  intro: image_eqI[of _ rev, OF rev_rev_ident[symmetric]]
         image_eqI[of _ rev, OF rev_append[symmetric]])

definition Root :: "'a lang \<Rightarrow> 'a lang" where
  "Root L = {x . \<exists>n > 0. x ^^ n \<in> L}"

definition Cycle :: "'a lang \<Rightarrow> 'a lang" where
  "Cycle L = {u @ w | u w. w @ u \<in> L}"

context embed
begin

context
fixes n :: nat
begin

definition SUFFIX :: "'b rexp \<Rightarrow> 'b rexp" where
  "SUFFIX r = flatten PLUS {\<guillemotleft>lderivs w r\<guillemotright>| w. wf_word n w}"

lemma finite_lderivs_wf: "finite {\<guillemotleft>lderivs w r\<guillemotright>| w. wf_word n w}"
  by (auto intro: finite_subset[OF _ finite_lderivs])

definition PREFIX :: "'b rexp \<Rightarrow> 'b rexp" where
  "PREFIX r = REV (SUFFIX (REV r))"

lemma wf_SUFFIX[simp]: "wf n r \<Longrightarrow> wf n (SUFFIX r)"
  unfolding SUFFIX_def by (intro iffD2[OF wf_flatten_PLUS[OF finite_lderivs_wf]]) auto
                                            
lemma lang_SUFFIX[simp]: "wf n r \<Longrightarrow> lang n (SUFFIX r) = Suffix (lang n r)"
  unfolding SUFFIX_def Suffix_def
  using lang_flatten_PLUS[OF finite_lderivs_wf] lang_lderivs wf_lang_wf_word
  by fastforce

lemma wf_PREFIX[simp]: "wf n r \<Longrightarrow> wf n (PREFIX r)"
  unfolding PREFIX_def by auto

lemma lang_PREFIX[simp]: "wf n r \<Longrightarrow> lang n (PREFIX r) = Prefix (lang n r)"
  unfolding PREFIX_def by (auto simp: Prefix_Suffix)         

end

lemma take_drop_CycleI[intro!]: "x \<in> L \<Longrightarrow> drop i x @ take i x \<in> Cycle L"
  unfolding Cycle_def by fastforce

lemma take_drop_CycleI'[intro!]: "drop i x @ take i x \<in> L \<Longrightarrow> x \<in> Cycle L"
  by (drule take_drop_CycleI[of _ _ "length x - i"]) auto

end

(*<*)
end
(*>*)
