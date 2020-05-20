(*  Title:       A Deterministic Ordered Resolution Prover for First-Order Clauses
    Author:      Jasmin Blanchette <j.c.blanchette at vu.nl>, 2017
    Author:      Anders Schlichtkrull <andschl at dtu.dk>, 2018
    Maintainer:  Anders Schlichtkrull <andschl at dtu.dk>
*)

section \<open>A Deterministic Ordered Resolution Prover for First-Order Clauses\<close>

text \<open>
The \<open>deterministic_RP\<close> prover introduced below is a deterministic program that works on finite
lists, committing to a strategy for assigning priorities to clauses. However, it is not fully
executable: It abstracts over operations on atoms and employs logical specifications instead of
executable functions for auxiliary notions.
\<close>

theory Deterministic_FO_Ordered_Resolution_Prover
  imports Polynomial_Factorization.Missing_List Weighted_FO_Ordered_Resolution_Prover
begin


subsection \<open>Library\<close>

lemma apfst_fst_snd: "apfst f x = (f (fst x), snd x)"
  by (rule apfst_conv[of _ "fst x" "snd x" for x, unfolded prod.collapse])

lemma apfst_comp_rpair_const: "apfst f \<circ> (\<lambda>x. (x, y)) = (\<lambda>x. (x, y)) \<circ> f"
  by (simp add: comp_def)

(* TODO: Move to Isabelle's "List.thy"? *)
lemma length_remove1_less[termination_simp]: "x \<in> set xs \<Longrightarrow> length (remove1 x xs) < length xs"
  by (induct xs) auto

(* TODO: Move to "Multiset_More.thy". *)
lemma subset_mset_imp_subset_add_mset: "A \<subseteq># B \<Longrightarrow> A \<subseteq># add_mset x B"
  by (metis add_mset_diff_bothsides diff_subset_eq_self multiset_inter_def subset_mset.inf.absorb2)

(* TODO: Move to "Multiset_More.thy"? *)
lemma subseq_mset_subseteq_mset: "subseq xs ys \<Longrightarrow> mset xs \<subseteq># mset ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs)
  note Outer_Cons = this
  then show ?case
  proof (induct ys)
    case (Cons y ys)
    have "subseq xs ys"
      by (metis Cons.prems(2) subseq_Cons' subseq_Cons2_iff)
    then show ?case
      using Cons by (metis mset.simps(2) mset_subset_eq_add_mset_cancel subseq_Cons2_iff
          subset_mset_imp_subset_add_mset)
  qed simp
qed simp

lemma map_filter_neq_eq_filter_map:
  "map f (filter (\<lambda>y. f x \<noteq> f y) xs) = filter (\<lambda>z. f x \<noteq> z) (map f xs)"
  by (induct xs) auto

lemma mset_map_remdups_gen:
  "mset (map f (remdups_gen f xs)) = mset (remdups_gen (\<lambda>x. x) (map f xs))"
  by (induct f xs rule: remdups_gen.induct) (auto simp: map_filter_neq_eq_filter_map)

lemma mset_remdups_gen_ident: "mset (remdups_gen (\<lambda>x. x) xs) = mset_set (set xs)"
proof -
  have "f = (\<lambda>x. x) \<Longrightarrow> mset (remdups_gen f xs) = mset_set (set xs)" for f
  proof (induct f xs rule: remdups_gen.induct)
    case (2 f x xs)
    note ih = this(1) and f = this(2)
    show ?case
      unfolding f remdups_gen.simps ih[OF f, unfolded f] mset.simps
      by (metis finite_set list.simps(15) mset_set.insert_remove removeAll_filter_not_eq
          remove_code(1) remove_def)
  qed simp
  then show ?thesis
    by simp
qed

(* FIXME: This is a clone of "Lambda_Free_RPOs". *)
lemma wf_app: "wf r \<Longrightarrow> wf {(x, y). (f x, f y) \<in> r}"
  unfolding wf_eq_minimal by (intro allI, drule spec[of _ "f ` Q" for Q]) fast

(* FIXME: This is a clone of "Lambda_Free_RPOs". *)
lemma wfP_app: "wfP p \<Longrightarrow> wfP (\<lambda>x y. p (f x) (f y))"
  unfolding wfP_def by (rule wf_app[of "{(x, y). p x y}" f, simplified])

(* TODO: Move to Isabelle? *)
lemma funpow_fixpoint: "f x = x \<Longrightarrow> (f ^^ n) x = x"
  by (induct n) auto

lemma rtranclp_imp_eq_image: "(\<forall>x y. R x y \<longrightarrow> f x = f y) \<Longrightarrow> R\<^sup>*\<^sup>* x y \<Longrightarrow> f x = f y"
  by (erule rtranclp.induct) auto

lemma tranclp_imp_eq_image: "(\<forall>x y. R x y \<longrightarrow> f x = f y) \<Longrightarrow> R\<^sup>+\<^sup>+ x y \<Longrightarrow> f x = f y"
  by (erule tranclp.induct) auto


subsection \<open>Prover\<close>

type_synonym 'a lclause = "'a literal list"
type_synonym 'a dclause = "'a lclause \<times> nat"
type_synonym 'a dstate = "'a dclause list \<times> 'a dclause list \<times> 'a dclause list \<times> nat"

locale deterministic_FO_resolution_prover =
  weighted_FO_resolution_prover_with_size_timestamp_factors S subst_atm id_subst comp_subst
    renamings_apart atm_of_atms mgu less_atm size_atm timestamp_factor size_factor
  for
    S :: "('a :: wellorder) clause \<Rightarrow> 'a clause" and
    subst_atm :: "'a \<Rightarrow> 's \<Rightarrow> 'a" and
    id_subst :: "'s" and
    comp_subst :: "'s \<Rightarrow> 's \<Rightarrow> 's" and
    renamings_apart :: "'a literal multiset list \<Rightarrow> 's list" and
    atm_of_atms :: "'a list \<Rightarrow> 'a" and
    mgu :: "'a set set \<Rightarrow> 's option" and
    less_atm :: "'a \<Rightarrow> 'a \<Rightarrow> bool" and
    size_atm :: "'a \<Rightarrow> nat" and
    timestamp_factor :: nat and
    size_factor :: nat +
  assumes
    S_empty: "S C = {#}"
begin

lemma less_atm_irrefl: "\<not> less_atm A A"
  using ex_ground_subst less_atm_ground less_atm_stable unfolding is_ground_subst_def by blast

fun wstate_of_dstate :: "'a dstate \<Rightarrow> 'a wstate" where
  "wstate_of_dstate (N, P, Q, n) =
   (mset (map (apfst mset) N), mset (map (apfst mset) P), mset (map (apfst mset) Q), n)"

fun state_of_dstate :: "'a dstate \<Rightarrow> 'a state" where
  "state_of_dstate (N, P, Q, _) =
   (set (map (mset \<circ> fst) N), set (map (mset \<circ> fst) P), set (map (mset \<circ> fst) Q))"

abbreviation clss_of_dstate :: "'a dstate \<Rightarrow> 'a clause set" where
  "clss_of_dstate St \<equiv> clss_of_state (state_of_dstate St)"

fun is_final_dstate :: "'a dstate \<Rightarrow> bool" where
  "is_final_dstate (N, P, Q, n) \<longleftrightarrow> N = [] \<and> P = []"

declare is_final_dstate.simps [simp del]

abbreviation rtrancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>*" 50) where
  "(\<leadsto>\<^sub>w\<^sup>*) \<equiv> (\<leadsto>\<^sub>w)\<^sup>*\<^sup>*"

abbreviation trancl_weighted_RP (infix "\<leadsto>\<^sub>w\<^sup>+" 50) where
  "(\<leadsto>\<^sub>w\<^sup>+) \<equiv> (\<leadsto>\<^sub>w)\<^sup>+\<^sup>+"

definition is_tautology :: "'a lclause \<Rightarrow> bool" where
  "is_tautology C \<longleftrightarrow> (\<exists>A \<in> set (map atm_of C). Pos A \<in> set C \<and> Neg A \<in> set C)"

definition subsume :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "subsume Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. subsumes (mset D) (mset C))"

definition strictly_subsume :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "strictly_subsume Ds C \<longleftrightarrow> (\<exists>D \<in> set Ds. strictly_subsumes (mset D) (mset C))"

definition is_reducible_on :: "'a literal \<Rightarrow> 'a lclause \<Rightarrow> 'a literal \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_reducible_on M D L C \<longleftrightarrow> subsumes (mset D + {#- M#}) (mset C + {#L#})"

definition is_reducible_lit :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a literal \<Rightarrow> bool" where
  "is_reducible_lit Ds C L \<longleftrightarrow>
   (\<exists>D \<in> set Ds. \<exists>L' \<in> set D. \<exists>\<sigma>. - L = L' \<cdot>l \<sigma> \<and> mset (remove1 L' D) \<cdot> \<sigma> \<subseteq># mset C)"

primrec reduce :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause" where
  "reduce _ _ [] = []"
| "reduce Ds C (L # C') =
   (if is_reducible_lit Ds (C @ C') L then reduce Ds C C' else L # reduce Ds (L # C) C')"

abbreviation is_irreducible :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_irreducible Ds C \<equiv> reduce Ds [] C = C"

abbreviation is_reducible :: "'a lclause list \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "is_reducible Ds C \<equiv> reduce Ds [] C \<noteq> C"

definition reduce_all :: "'a lclause \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause list" where
  "reduce_all D = map (apfst (reduce [D] []))"

fun reduce_all2 :: "'a lclause \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause list \<times> 'a dclause list" where
  "reduce_all2 _ [] = ([], [])"
| "reduce_all2 D (Ci # Cs) =
   (let
      (C, i) = Ci;
      C' = reduce [D] [] C
    in
      (if C' = C then apsnd else apfst) (Cons (C', i)) (reduce_all2 D Cs))"

fun remove_all :: "'b list \<Rightarrow> 'b list \<Rightarrow> 'b list" where
  "remove_all xs [] = xs"
| "remove_all xs (y # ys) = (if y \<in> set xs then remove_all (remove1 y xs) ys else remove_all xs ys)"

lemma remove_all_mset_minus: "mset ys \<subseteq># mset xs \<Longrightarrow> mset (remove_all xs ys) = mset xs - mset ys"
proof (induction ys arbitrary: xs)
  case (Cons y ys)
  show ?case
  proof (cases "y \<in> set xs")
    case y_in: True
    then have subs: "mset ys \<subseteq># mset (remove1 y xs)"
      using Cons(2) by (simp add: insert_subset_eq_iff)
    show ?thesis
      using y_in Cons subs by auto
  next
    case False
    then show ?thesis
      using Cons by auto
  qed
qed auto

definition resolvent :: "'a lclause \<Rightarrow> 'a \<Rightarrow>'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause" where
  "resolvent D A CA Ls =
   map (\<lambda>M. M \<cdot>l (the (mgu {insert A (atms_of (mset Ls))}))) (remove_all CA Ls @ D)"

definition resolvable :: "'a \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> bool" where
  "resolvable A D CA Ls \<longleftrightarrow>
   (let \<sigma> = (mgu {insert A (atms_of (mset Ls))}) in
        \<sigma> \<noteq> None
      \<and> Ls \<noteq> []
      \<and> maximal_wrt (A \<cdot>a the \<sigma>) ((add_mset (Neg A) (mset D)) \<cdot> the \<sigma>)
      \<and> strictly_maximal_wrt (A \<cdot>a the \<sigma>) ((mset CA - mset Ls) \<cdot> the \<sigma>)
      \<and> (\<forall>L \<in> set Ls. is_pos L))"

definition resolve_on :: "'a \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_on A D CA = map (resolvent D A CA) (filter (resolvable A D CA) (subseqs CA))"

definition resolve :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve C D =
   concat (map (\<lambda>L.
     (case L of
        Pos A \<Rightarrow> []
      | Neg A \<Rightarrow>
        if maximal_wrt A (mset D) then
          resolve_on A (remove1 L D) C
        else
          [])) D)"

definition resolve_rename :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename C D =
   (let \<sigma>s = renamings_apart [mset D, mset C] in
      resolve (map (\<lambda>L. L \<cdot>l last \<sigma>s) C) (map (\<lambda>L. L \<cdot>l hd \<sigma>s) D))"

definition resolve_rename_either_way :: "'a lclause \<Rightarrow> 'a lclause \<Rightarrow> 'a lclause list" where
  "resolve_rename_either_way C D = resolve_rename C D @ resolve_rename D C"

fun select_min_weight_clause :: "'a dclause \<Rightarrow> 'a dclause list \<Rightarrow> 'a dclause" where
  "select_min_weight_clause Ci [] = Ci"
| "select_min_weight_clause Ci (Dj # Djs) =
   select_min_weight_clause
     (if weight (apfst mset Dj) < weight (apfst mset Ci) then Dj else Ci) Djs"

lemma select_min_weight_clause_in: "select_min_weight_clause P0 P \<in> set (P0 # P)"
  by (induct P arbitrary: P0) auto

function remdups_clss :: "'a dclause list \<Rightarrow> 'a dclause list" where
  "remdups_clss [] = []"
| "remdups_clss (Ci # Cis) =
   (let
      Ci' = select_min_weight_clause Ci Cis
    in
      Ci' # remdups_clss (filter (\<lambda>(D, _). mset D \<noteq> mset (fst Ci')) (Ci # Cis)))"
  by pat_completeness auto
  termination
    apply (relation "measure length")
     apply (rule wf_measure)
    by (metis (mono_tags) in_measure length_filter_less prod.case_eq_if select_min_weight_clause_in)

declare remdups_clss.simps(2) [simp del]

fun deterministic_RP_step :: "'a dstate \<Rightarrow> 'a dstate" where
  "deterministic_RP_step (N, P, Q, n) =
   (if \<exists>Ci \<in> set (P @ Q). fst Ci = [] then
      ([], [], remdups_clss P @ Q, n + length (remdups_clss P))
    else
      (case N of
        [] \<Rightarrow>
        (case P of
           [] \<Rightarrow> (N, P, Q, n)
         | P0 # P' \<Rightarrow>
           let
             (C, i) = select_min_weight_clause P0 P';
             N = map (\<lambda>D. (D, n)) (remdups_gen mset (resolve_rename C C
               @ concat (map (resolve_rename_either_way C \<circ> fst) Q)));
             P = filter (\<lambda>(D, j). mset D \<noteq> mset C) P;
             Q = (C, i) # Q;
             n = Suc n
           in
             (N, P, Q, n))
      | (C, i) # N \<Rightarrow>
        let
          C = reduce (map fst (P @ Q)) [] C
        in
          if C = [] then
            ([], [], [([], i)], Suc n)
          else if is_tautology C \<or> subsume (map fst (P @ Q)) C then
            (N, P, Q, n)
          else
            let
              P = reduce_all C P;
              (back_to_P, Q) = reduce_all2 C Q;
              P = back_to_P @ P;
              Q = filter (Not \<circ> strictly_subsume [C] \<circ> fst) Q;
              P = filter (Not \<circ> strictly_subsume [C] \<circ> fst) P;
              P = (C, i) # P
            in
              (N, P, Q, n)))"

declare deterministic_RP_step.simps [simp del]

partial_function (option) deterministic_RP :: "'a dstate \<Rightarrow> 'a lclause list option" where
  "deterministic_RP St =
   (if is_final_dstate St then
      let (_, _, Q, _) = St in Some (map fst Q)
    else
      deterministic_RP (deterministic_RP_step St))"

lemma is_final_dstate_imp_not_weighted_RP: "is_final_dstate St \<Longrightarrow> \<not> wstate_of_dstate St \<leadsto>\<^sub>w St'"
  using wrp.final_weighted_RP
  by (cases St) (auto intro: wrp.final_weighted_RP simp: is_final_dstate.simps)

lemma is_final_dstate_funpow_imp_deterministic_RP_neq_None:
  "is_final_dstate ((deterministic_RP_step ^^ k) St) \<Longrightarrow> deterministic_RP St \<noteq> None"
proof (induct k arbitrary: St)
  case (Suc k)
  note ih = this(1) and final_Sk = this(2)[simplified, unfolded funpow_swap1]
  show ?case
    using ih[OF final_Sk] by (subst deterministic_RP.simps) (simp add: prod.case_eq_if)
qed (subst deterministic_RP.simps, simp add: prod.case_eq_if)

lemma is_reducible_lit_mono_cls:
  "mset C \<subseteq># mset C' \<Longrightarrow> is_reducible_lit Ds C L \<Longrightarrow> is_reducible_lit Ds C' L"
  unfolding is_reducible_lit_def by (blast intro: subset_mset.order.trans)

lemma is_reducible_lit_mset_iff:
  "mset C = mset C' \<Longrightarrow> is_reducible_lit Ds C' L \<longleftrightarrow> is_reducible_lit Ds C L"
  by (metis is_reducible_lit_mono_cls subset_mset.order_refl)

lemma is_reducible_lit_remove1_Cons_iff:
  assumes "L \<in> set C'"
  shows "is_reducible_lit Ds (C @ remove1 L (M # C')) L \<longleftrightarrow>
    is_reducible_lit Ds (M # C @ remove1 L C') L"
  using assms by (subst is_reducible_lit_mset_iff, auto)

lemma reduce_mset_eq: "mset C = mset C' \<Longrightarrow> reduce Ds C E = reduce Ds C' E"
proof (induct E arbitrary: C C')
  case (Cons L E)
  note ih = this(1) and mset_eq = this(2)
  have
    mset_lc_eq: "mset (L # C) = mset (L # C')" and
    mset_ce_eq: "mset (C @ E) = mset (C' @ E)"
    using mset_eq by simp+
  show ?case
    using ih[OF mset_eq] ih[OF mset_lc_eq] by (simp add: is_reducible_lit_mset_iff[OF mset_ce_eq])
qed simp

lemma reduce_rotate[simp]: "reduce Ds (C @ [L]) E = reduce Ds (L # C) E"
  by (rule reduce_mset_eq) simp

lemma mset_reduce_subset: "mset (reduce Ds C E) \<subseteq># mset E"
  by (induct E arbitrary: C) (auto intro: subset_mset_imp_subset_add_mset)

lemma reduce_idem: "reduce Ds C (reduce Ds C E) = reduce Ds C E"
  by (induct E arbitrary: C)
    (auto intro!: mset_reduce_subset
      dest!: is_reducible_lit_mono_cls[of "C @ reduce Ds (L # C) E" "C @ E" Ds L for L E C,
        rotated])

lemma is_reducible_lit_imp_is_reducible:
  "L \<in> set C' \<Longrightarrow> is_reducible_lit Ds (C @ remove1 L C') L \<Longrightarrow> reduce Ds C C' \<noteq> C'"
proof (induct C' arbitrary: C)
  case (Cons M C')
  note ih = this(1) and l_in = this(2) and l_red = this(3)

  show ?case
  proof (cases "is_reducible_lit Ds (C @ C') M")
    case True
    then show ?thesis
      by simp (metis mset.simps(2) mset_reduce_subset multi_self_add_other_not_self
          subset_mset.eq_iff subset_mset_imp_subset_add_mset)
  next
    case m_irred: False
    have
      "L \<in> set C'" and
      "is_reducible_lit Ds (M # C @ remove1 L C') L"
      using l_in l_red m_irred is_reducible_lit_remove1_Cons_iff by auto
    then show ?thesis
      by (simp add: ih[of "M # C"] m_irred)
  qed
qed simp

lemma is_reducible_imp_is_reducible_lit:
  "reduce Ds C C' \<noteq> C' \<Longrightarrow> \<exists>L \<in> set C'. is_reducible_lit Ds (C @ remove1 L C') L"
proof (induct C' arbitrary: C)
  case (Cons M C')
  note ih = this(1) and mc'_red = this(2)

  show ?case
  proof (cases "is_reducible_lit Ds (C @ C') M")
    case m_irred: False
    show ?thesis
      using ih[of "M # C"] mc'_red[simplified, simplified m_irred, simplified] m_irred
        is_reducible_lit_remove1_Cons_iff
      by auto
  qed simp
qed simp

lemma is_irreducible_iff_nexists_is_reducible_lit:
  "reduce Ds C C' = C' \<longleftrightarrow> \<not> (\<exists>L \<in> set C'. is_reducible_lit Ds (C @ remove1 L C') L)"
  using is_reducible_imp_is_reducible_lit is_reducible_lit_imp_is_reducible by blast

lemma is_irreducible_mset_iff: "mset E = mset E' \<Longrightarrow> reduce Ds C E = E \<longleftrightarrow> reduce Ds C E' = E'"
  unfolding is_irreducible_iff_nexists_is_reducible_lit
  by (metis (full_types) is_reducible_lit_mset_iff mset_remove1 set_mset_mset union_code)

lemma select_min_weight_clause_min_weight:
  assumes "Ci = select_min_weight_clause P0 P"
  shows "weight (apfst mset Ci) = Min ((weight \<circ> apfst mset) ` set (P0 # P))"
  using assms
proof (induct P arbitrary: P0 Ci)
  case (Cons P1 P)
  note ih = this(1) and ci = this(2)

  show ?case
  proof (cases "weight (apfst mset P1) < weight (apfst mset P0)")
    case True
    then have min: "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P1 # P))"
      by (simp add: min_def)
    show ?thesis
      unfolding min by (rule ih[of Ci P1]) (simp add: ih[of Ci P1] ci True)
  next
    case False
    have "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P1 # P0 # P))"
      by (rule arg_cong[of _ _ Min]) auto
    then have min: "Min ((weight \<circ> apfst mset) ` set (P0 # P1 # P)) =
      Min ((weight \<circ> apfst mset) ` set (P0 # P))"
      by (simp add: min_def) (use False eq_iff in fastforce)
    show ?thesis
      unfolding min by (rule ih[of Ci P0]) (simp add: ih[of Ci P1] ci False)
  qed
qed simp

lemma remdups_clss_Nil_iff: "remdups_clss Cs = [] \<longleftrightarrow> Cs = []"
  by (cases Cs, simp, hypsubst, subst remdups_clss.simps(2), simp add: Let_def)

lemma empty_N_if_Nil_in_P_or_Q:
  assumes nil_in: "[] \<in> fst ` set (P @ Q)"
  shows "wstate_of_dstate (N, P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], P, Q, n)"
proof (induct N)
  case ih: (Cons N0 N)
  have "wstate_of_dstate (N0 # N, P, Q, n) \<leadsto>\<^sub>w wstate_of_dstate (N, P, Q, n)"
    by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
          wrp.forward_subsumption[of "{#}" "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)"
            "mset (fst N0)" "mset (map (apfst mset) N)" "snd N0" n]])
      (use nil_in in \<open>force simp: image_def apfst_fst_snd\<close>)+
  then show ?case
    using ih by (rule converse_rtranclp_into_rtranclp)
qed simp

lemma remove_strictly_subsumed_clauses_in_P:
  assumes
    c_in: "C \<in> fst ` set N" and
    p_nsubs: "\<forall>D \<in> fst ` set P. \<not> strictly_subsume [C] D"
  shows "wstate_of_dstate (N, P @ P', Q, n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) P', Q, n)"
  using p_nsubs
proof (induct "length P'" arbitrary: P P' rule: less_induct)
  case less
  note ih = this(1) and p_nsubs = this(2)

  show ?case
  proof (cases "length P'")
    case Suc

    let ?Dj = "hd P'"
    let ?P'' = "tl P'"
    have p': "P' = hd P' # tl P'"
      using Suc by (metis length_Suc_conv list.distinct(1) list.exhaust_sel)

    show ?thesis
    proof (cases "strictly_subsume [C] (fst ?Dj)")
      case subs: True

      have p_filtered: "{#(E, k) \<in># image_mset (apfst mset) (mset P). E \<noteq> mset (fst ?Dj)#} =
        image_mset (apfst mset) (mset P)"
        by (rule filter_mset_cong[OF refl, of _ _ "\<lambda>_. True", simplified],
            use subs p_nsubs in \<open>auto simp: strictly_subsume_def\<close>)
      have "{#(E, k) \<in># image_mset (apfst mset) (mset P'). E \<noteq> mset (fst ?Dj)#} =
        {#(E, k) \<in># image_mset (apfst mset) (mset ?P''). E \<noteq> mset (fst ?Dj)#}"
        by (subst (2) p') (simp add: case_prod_beta)
      also have "\<dots> =
        image_mset (apfst mset) (mset (filter (\<lambda>(E, l). mset E \<noteq> mset (fst ?Dj)) ?P''))"
        by (auto simp: image_mset_filter_swap[symmetric] mset_filter case_prod_beta)
      finally have p'_filtered:
        "{#(E, k) \<in># image_mset (apfst mset) (mset P'). E \<noteq> mset (fst ?Dj)#} =
        image_mset (apfst mset) (mset (filter (\<lambda>(E, l). mset E \<noteq> mset (fst ?Dj)) ?P''))"
        .

      have "wstate_of_dstate (N, P @ P', Q, n)
        \<leadsto>\<^sub>w wstate_of_dstate (N, P @ filter (\<lambda>(E, l). mset E \<noteq> mset (fst ?Dj)) ?P'', Q, n)"
        by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
              wrp.backward_subsumption_P[of "mset C" "mset (map (apfst mset) N)" "mset (fst ?Dj)"
                "mset (map (apfst mset) (P @ P'))" "mset (map (apfst mset) Q)" n]],
          use c_in subs in \<open>auto simp add: p_filtered p'_filtered arg_cong[OF p', of set]
            strictly_subsume_def\<close>)
      also have "\<dots>
        \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) P', Q, n)"
        apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
              ih[of "filter (\<lambda>(E, l). mset E \<noteq> mset (fst ?Dj)) ?P''" P]])
           apply simp_all
          apply (subst (3) p')
        using subs
          apply (simp add: case_prod_beta)
          apply (rule arg_cong[of _ _ "\<lambda>x. image_mset (apfst mset) x"])
        apply (metis (no_types, hide_lams) strictly_subsume_def)
         apply (subst (3) p')
         apply (subst list.size)
         apply (metis (no_types, lifting) less_Suc0 less_add_same_cancel1 linorder_neqE_nat
            not_add_less1 sum_length_filter_compl trans_less_add1)
        using p_nsubs by fast
      ultimately show ?thesis
        by (rule converse_rtranclp_into_rtranclp)
    next
      case nsubs: False
      show ?thesis
        apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
              ih[of ?P'' "P @ [?Dj]"]])
        using nsubs p_nsubs
           apply (simp_all add: arg_cong[OF p', of mset] arg_cong[OF p', of "filter f" for f])
        apply (subst (1 2) p')
        by simp
    qed
  qed simp
qed

lemma remove_strictly_subsumed_clauses_in_Q:
  assumes c_in: "C \<in> fst ` set N"
  shows "wstate_of_dstate (N, P, Q @ Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P, Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) Q', n)"
proof (induct Q' arbitrary: Q)
  case ih: (Cons Dj Q')
  have "wstate_of_dstate (N, P, Q @ Dj # Q', n) \<leadsto>\<^sub>w\<^sup>*
    wstate_of_dstate (N, P, Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dj] @ Q', n)"
  proof (cases "strictly_subsume [C] (fst Dj)")
    case subs: True
    have "wstate_of_dstate (N, P, Q @ Dj # Q', n) \<leadsto>\<^sub>w wstate_of_dstate (N, P, Q @ Q', n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
            wrp.backward_subsumption_Q[of "mset C" "mset (map (apfst mset) N)" "mset (fst Dj)"
              "mset (map (apfst mset) P)" "mset (map (apfst mset) (Q @ Q'))" "snd Dj" n]])
        (use c_in subs in \<open>auto simp: apfst_fst_snd strictly_subsume_def\<close>)
    then show ?thesis
      by auto
  qed simp
  then show ?case
    using ih[of "Q @ filter (Not \<circ> strictly_subsume [C] \<circ> fst) [Dj]"] by force
qed simp

lemma reduce_clause_in_P:
  assumes
    c_in: "C \<in> fst ` set N" and
    p_irred: "\<forall>(E, k) \<in> set (P @ P'). k > j \<longrightarrow> is_irreducible [C] E"
  shows "wstate_of_dstate (N, P @ (D @ D', j) # P', Q, n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ (D @ reduce [C] D D', j) # P', Q, n)"
proof (induct D' arbitrary: D)
  case ih: (Cons L D')
  show ?case
  proof (cases "is_reducible_lit [C] (D @ D') L")
    case l_red: True
    then obtain L' :: "'a literal" and \<sigma> :: 's where
      l'_in: "L' \<in> set C" and
      not_l: "- L = L' \<cdot>l \<sigma>" and
      subs: "mset (remove1 L' C) \<cdot> \<sigma> \<subseteq># mset (D @ D')"
      unfolding is_reducible_lit_def by force

    have ldd'_red: "is_reducible [C] (L # D @ D')"
      apply (rule is_reducible_lit_imp_is_reducible)
      using l_red by auto

    have lt_imp_neq: "\<forall>(E, k) \<in> set (P @ P'). j < k \<longrightarrow> mset E \<noteq> mset (L # D @ D')"
      using p_irred ldd'_red is_irreducible_mset_iff by fast

    have "wstate_of_dstate (N, P @ (D @ L # D', j) # P', Q, n)
      \<leadsto>\<^sub>w wstate_of_dstate (N, P @ (D @ D', j) # P', Q, n)"
      apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
            wrp.backward_reduction_P[of "mset C - {#L'#}" L' "mset (map (apfst mset) N)" L \<sigma>
              "mset (D @ D')" "mset (map (apfst mset) (P @ P'))" j "mset (map (apfst mset) Q)" n]])
      using l'_in not_l subs c_in lt_imp_neq by (simp_all add: case_prod_beta) force+
    then show ?thesis
      using ih[of D] l_red by simp
  next
    case False
    then show ?thesis
      using ih[of "D @ [L]"] by simp
  qed
qed simp

lemma reduce_clause_in_Q:
  assumes
    c_in: "C \<in> fst ` set N" and
    p_irred: "\<forall>(E, k) \<in> set P. k > j \<longrightarrow> is_irreducible [C] E" and
    d'_red: "reduce [C] D D' \<noteq> D'"
  shows "wstate_of_dstate (N, P, Q @ (D @ D', j) # Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, (D @ reduce [C] D D', j) # P, Q @ Q', n)"
  using d'_red
proof (induct D' arbitrary: D)
  case (Cons L D')
  note ih = this(1) and ld'_red = this(2)
  then show ?case
  proof (cases "is_reducible_lit [C] (D @ D') L")
    case l_red: True
    then obtain L' :: "'a literal" and \<sigma> :: 's where
      l'_in: "L' \<in> set C" and
      not_l: "- L = L' \<cdot>l \<sigma>" and
      subs: "mset (remove1 L' C) \<cdot> \<sigma> \<subseteq># mset (D @ D')"
      unfolding is_reducible_lit_def by force

    have "wstate_of_dstate (N, P, Q @ (D @ L # D', j) # Q', n)
      \<leadsto>\<^sub>w wstate_of_dstate (N, (D @ D', j) # P, Q @ Q', n)"
      by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
            wrp.backward_reduction_Q[of "mset C - {#L'#}" L' "mset (map (apfst mset) N)" L \<sigma>
              "mset (D @ D')" "mset (map (apfst mset) P)" "mset (map (apfst mset) (Q @ Q'))" j n]],
          use l'_in not_l subs c_in in auto)
    then show ?thesis
      using l_red p_irred reduce_clause_in_P[OF c_in, of "[]" P j D D' "Q @ Q'" n] by simp
  next
    case l_nred: False
    then have d'_red: "reduce [C] (D @ [L]) D' \<noteq> D'"
      using ld'_red by simp
    show ?thesis
      using ih[OF d'_red] l_nred by simp
  qed
qed simp

lemma reduce_clauses_in_P:
  assumes
    c_in: "C \<in> fst ` set N" and
    p_irred: "\<forall>(E, k) \<in> set P. is_irreducible [C] E"
  shows "wstate_of_dstate (N, P @ P', Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ reduce_all C P', Q, n)"
  unfolding reduce_all_def
  using p_irred
proof (induct "length P'" arbitrary: P P')
  case (Suc l)
  note ih = this(1) and suc_l = this(2) and p_irred = this(3)

  have p'_nnil: "P' \<noteq> []"
    using suc_l by auto

  define j :: nat where
    "j = Max (snd ` set P')"

  obtain Dj :: "'a dclause" where
    dj_in: "Dj \<in> set P'" and
    snd_dj: "snd Dj = j"
    using Max_in[of "snd ` set P'", unfolded image_def, simplified]
    by (metis image_def j_def length_Suc_conv list.set_intros(1) suc_l)

  have "\<forall>k \<in> snd ` set P'. k \<le> j"
    unfolding j_def using p'_nnil by simp
  then have j_max: "\<forall>(E, k) \<in> set P'. j \<ge> k"
    unfolding image_def by fastforce

  obtain P1' P2' :: "'a dclause list"  where
    p': "P' = P1' @ Dj # P2'"
    using split_list[OF dj_in] by blast

  have "wstate_of_dstate (N, P @ P1' @ Dj # P2', Q, n)
     \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ P1' @ apfst (reduce [C] []) Dj # P2', Q, n)"
    unfolding append_assoc[symmetric]
    apply (subst (1 2) surjective_pairing[of Dj, unfolded snd_dj])
    apply (simp only: apfst_conv)
    apply (rule reduce_clause_in_P[of _ _ _ _ _ "[]", unfolded append_Nil, OF c_in])
    using p_irred j_max[unfolded p'] by (force simp: case_prod_beta)
  moreover have "wstate_of_dstate (N, P @ P1' @ apfst (reduce [C] []) Dj # P2', Q, n)
     \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, P @ map (apfst (reduce [C] [])) (P1' @ Dj # P2'), Q, n)"
    apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
          ih[of "P1' @ P2'" "apfst (reduce [C] []) Dj # P"]])
    using suc_l reduce_idem p_irred unfolding p' by (auto simp: case_prod_beta)
  ultimately show ?case
    unfolding p' by simp
qed simp

lemma reduce_clauses_in_Q:
  assumes
    c_in: "C \<in> fst ` set N" and
    p_irred: "\<forall>(E, k) \<in> set P. is_irreducible [C] E"
  shows "wstate_of_dstate (N, P, Q @ Q', n)
    \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, fst (reduce_all2 C Q') @ P, Q @ snd (reduce_all2 C Q'), n)"
  using p_irred
proof (induct Q' arbitrary: P Q)
  case (Cons Dj Q')
  note ih = this(1) and p_irred = this(2)
  show ?case
  proof (cases "is_irreducible [C] (fst Dj)")
    case True
    then show ?thesis
      using ih[of _ "Q @ [Dj]"] p_irred by (simp add: case_prod_beta)
  next
    case d_red: False
    have "wstate_of_dstate (N, P, Q @ Dj # Q', n)
      \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (N, (reduce [C] [] (fst Dj), snd Dj) # P, Q @ Q', n)"
      using p_irred reduce_clause_in_Q[of _ _ P "snd Dj" "[]" _ Q Q' n, OF c_in _ d_red]
      by (cases Dj) force
    then show ?thesis
      using ih[of "(reduce [C] [] (fst Dj), snd Dj) # P" Q] d_red p_irred reduce_idem
      by (force simp: case_prod_beta)
  qed
qed simp

lemma eligible_iff:
  "eligible S \<sigma> As DA \<longleftrightarrow> As = [] \<or> length As = 1 \<and> maximal_wrt (hd As \<cdot>a \<sigma>) (DA \<cdot> \<sigma>)"
  unfolding eligible.simps S_empty by (fastforce dest: hd_conv_nth)

lemma ord_resolve_one_side_prem:
  "ord_resolve S CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs = 1 \<and> length AAs = 1 \<and> length As = 1"
  by (force elim!: ord_resolve.cases simp: eligible_iff)

lemma ord_resolve_rename_one_side_prem:
  "ord_resolve_rename S CAs DA AAs As \<sigma> E \<Longrightarrow> length CAs = 1 \<and> length AAs = 1 \<and> length As = 1"
  by (force elim!: ord_resolve_rename.cases dest: ord_resolve_one_side_prem)

abbreviation Bin_ord_resolve :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause set" where
  "Bin_ord_resolve C D \<equiv> {E. \<exists>AA A \<sigma>. ord_resolve S [C] D [AA] [A] \<sigma> E}"

abbreviation Bin_ord_resolve_rename :: "'a clause \<Rightarrow> 'a clause \<Rightarrow> 'a clause set" where
  "Bin_ord_resolve_rename C D \<equiv> {E. \<exists>AA A \<sigma>. ord_resolve_rename S [C] D [AA] [A] \<sigma> E}"

lemma resolve_on_eq_UNION_Bin_ord_resolve:
  "mset ` set (resolve_on A D CA) =
   {E. \<exists>AA \<sigma>. ord_resolve S [mset CA] ({#Neg A#} + mset D) [AA] [A] \<sigma> E}"
proof
  {
    fix E :: "'a literal list"
    assume "E \<in> set (resolve_on A D CA)"
    then have "E \<in> resolvent D A CA ` {Ls. subseq Ls CA \<and> resolvable A D CA Ls}"
      unfolding resolve_on_def by simp
    then obtain Ls where Ls_p: "resolvent D A CA Ls = E" "subseq Ls CA \<and> resolvable A D CA Ls"
      by auto
    define \<sigma> where "\<sigma> = the (mgu {insert A (atms_of (mset Ls))})"
    then have \<sigma>_p:
      "mgu {insert A (atms_of (mset Ls))} = Some \<sigma>"
      "Ls \<noteq> []"
      "eligible S \<sigma> [A] (add_mset (Neg A) (mset D))"
      "strictly_maximal_wrt (A \<cdot>a \<sigma>) ((mset CA - mset Ls) \<cdot> \<sigma>)"
      "\<forall>L \<in> set Ls. is_pos L"
      using Ls_p unfolding resolvable_def unfolding Let_def eligible.simps using S_empty by auto
    from \<sigma>_p have \<sigma>_p2: "the (mgu {insert A (atms_of (mset Ls))}) = \<sigma>"
      by auto
    have Ls_sub_CA: "mset Ls \<subseteq># mset CA"
      using subseq_mset_subseteq_mset Ls_p by auto
    then have "mset (resolvent D A CA Ls) = sum_list [mset CA - mset Ls] \<cdot> \<sigma> + mset D \<cdot> \<sigma>"
      unfolding resolvent_def \<sigma>_p2 subst_cls_def using remove_all_mset_minus[of Ls CA] by auto
    moreover
    have "length [mset CA - mset Ls] = Suc 0"
      by auto
    moreover
    have "\<forall>L \<in> set Ls. is_pos L"
      using \<sigma>_p(5) list_all_iff[of is_pos] by auto
    then have "{#Pos (atm_of x). x \<in># mset Ls#} = mset Ls"
      by (induction Ls) auto
    then have "mset CA = [mset CA - mset Ls] ! 0 + {#Pos (atm_of x). x \<in># mset Ls#}"
      using Ls_sub_CA by auto
    moreover
    have "Ls \<noteq> []"
      using \<sigma>_p by -
    moreover
    have "Some \<sigma> = mgu {insert A (atm_of ` set Ls)}"
      using \<sigma>_p unfolding atms_of_def by auto
    moreover
    have "eligible S \<sigma> [A] (add_mset (Neg A) (mset D))"
      using \<sigma>_p by -
    moreover
    have "strictly_maximal_wrt (A \<cdot>a \<sigma>) ([mset CA - mset Ls] ! 0 \<cdot> \<sigma>)"
      using \<sigma>_p(4) by auto
    moreover have "S (mset CA) = {#}"
      by (simp add: S_empty)
    ultimately have "\<exists>Cs. mset (resolvent D A CA Ls) = sum_list Cs \<cdot> \<sigma> + mset D \<cdot> \<sigma>
        \<and> length Cs = Suc 0 \<and> mset CA = Cs ! 0 + {#Pos (atm_of x). x \<in># mset Ls#}
        \<and> Ls \<noteq> [] \<and> Some \<sigma> = mgu {insert A (atm_of ` set Ls)}
        \<and> eligible S \<sigma> [A] (add_mset (Neg A) (mset D)) \<and> strictly_maximal_wrt (A \<cdot>a \<sigma>) (Cs ! 0 \<cdot> \<sigma>)
        \<and> S (mset CA) = {#}"
      by blast
    then have "ord_resolve S [mset CA] (add_mset (Neg A) (mset D)) [image_mset atm_of (mset Ls)] [A]
      \<sigma> (mset (resolvent D A CA Ls))"
      unfolding ord_resolve.simps by auto
    then have "\<exists>AA \<sigma>. ord_resolve S [mset CA] (add_mset (Neg A) (mset D)) [AA] [A] \<sigma> (mset E)"
      using Ls_p by auto
  }
  then show "mset ` set (resolve_on A D CA)
    \<subseteq> {E. \<exists>AA \<sigma>. ord_resolve S [mset CA] ({#Neg A#} + mset D) [AA] [A] \<sigma> E}"
    by auto
next
  {
    fix E AA \<sigma>
    assume "ord_resolve S [mset CA] (add_mset (Neg A) (mset D)) [AA] [A] \<sigma> E"
    then obtain Cs where res': "E = sum_list Cs \<cdot> \<sigma> + mset D \<cdot> \<sigma>"
      "length Cs = Suc 0"
      "mset CA = Cs ! 0 + poss AA"
      "AA \<noteq> {#}"
      "Some \<sigma> = mgu {insert A (set_mset AA)}"
      "eligible S \<sigma> [A] (add_mset (Neg A) (mset D))"
      "strictly_maximal_wrt (A \<cdot>a \<sigma>) (Cs ! 0 \<cdot> \<sigma>)"
      "S (Cs ! 0 + poss AA) = {#}"
      unfolding ord_resolve.simps by auto
    moreover define C where "C = Cs ! 0"
    ultimately have res:
      "E = sum_list Cs \<cdot> \<sigma> + mset D \<cdot> \<sigma>"
      "mset CA = C + poss AA"
      "AA \<noteq> {#}"
      "Some \<sigma> = mgu {insert A (set_mset AA)}"
      "eligible S \<sigma> [A] (add_mset (Neg A) (mset D))"
      "strictly_maximal_wrt (A \<cdot>a \<sigma>) (C \<cdot> \<sigma>)"
      "S (C + poss AA) = {#}"
      unfolding ord_resolve.simps by auto
    from this(1) have
      "E = C \<cdot> \<sigma> + mset D \<cdot> \<sigma>"
      unfolding C_def using res'(2) by (cases Cs) auto
    note res' = this res(2-7)
    have "\<exists>Al. mset Al = AA \<and> subseq (map Pos Al) CA"
      using res(2)
    proof (induction CA arbitrary: AA C)
      case Nil
      then show ?case by auto
    next
      case (Cons L CA)
      then show ?case
      proof (cases "L \<in># poss AA ")
        case True
        then have pos_L: "is_pos L"
          by auto
        have rem: "\<And>A'. Pos A' \<in># poss AA \<Longrightarrow>
          remove1_mset (Pos A') (C + poss AA) = C + poss (remove1_mset A' AA)"
          by (induct AA) auto
        have "mset CA = C + (poss (AA - {#atm_of L#}))"
          using True Cons(2)
          by (metis add_mset_remove_trivial rem literal.collapse(1) mset.simps(2) pos_L)
        then have "\<exists>Al. mset Al = remove1_mset (atm_of L) AA \<and> subseq (map Pos Al) CA"
          using Cons(1)[of _ "((AA - {#atm_of L#}))"] by metis
        then obtain Al where
          "mset Al = remove1_mset (atm_of L) AA \<and> subseq (map Pos Al) CA"
          by auto
        then have
          "mset (atm_of L # Al) = AA" and
          "subseq (map Pos (atm_of L # Al)) (L # CA)"
          using True by (auto simp add: pos_L)
        then show ?thesis
          by blast
      next
        case False
        then have "mset CA = remove1_mset L C + poss AA"
          using Cons(2)
          by (metis Un_iff add_mset_remove_trivial mset.simps(2) set_mset_union single_subset_iff
              subset_mset.add_diff_assoc2 union_single_eq_member)
        then have "\<exists>Al. mset Al = AA \<and> subseq (map Pos Al) CA"
          using Cons(1)[of "C - {#L#}" AA] Cons(2) by auto
        then show ?thesis
          by auto
      qed
    qed
    then obtain Al where Al_p: "mset Al = AA" "subseq (map Pos Al) CA"
      by auto

    define Ls :: "'a lclause" where "Ls = map Pos Al"
    have diff: "mset CA - mset Ls = C"
      unfolding Ls_def using res(2) Al_p(1) by auto
    have ls_subq_ca: "subseq Ls CA"
      unfolding Ls_def using Al_p by -
    moreover
    {
      have "\<exists>y. mgu {insert A (atms_of (mset Ls))} = Some y"
        unfolding Ls_def using res(4) Al_p by (metis atms_of_poss mset_map)
      moreover have "Ls \<noteq> []"
        using Al_p(1) Ls_def res'(3) by auto
      moreover have \<sigma>_p: "the (mgu {insert A (set Al)}) = \<sigma>"
        using res'(4) Al_p(1) by (metis option.sel  set_mset_mset)
      then have "eligible S (the (mgu {insert A (atms_of (mset Ls))})) [A]
        (add_mset (Neg A) (mset D))"
        unfolding Ls_def using res  by auto
      moreover have "strictly_maximal_wrt (A \<cdot>a the (mgu {insert A (atms_of (mset Ls))}))
        ((mset CA - mset Ls) \<cdot> the (mgu {insert A (atms_of (mset Ls))}))"
        unfolding Ls_def using res \<sigma>_p Al_p by auto
      moreover have "\<forall>L \<in> set Ls. is_pos L"
        by (simp add: Ls_def)
      ultimately have "resolvable A D CA Ls"
        unfolding resolvable_def unfolding eligible.simps using S_empty by simp
    }
    moreover have ls_sub_ca: "mset Ls \<subseteq># mset CA"
      using ls_subq_ca subseq_mset_subseteq_mset[of Ls CA] by simp
    have "{#x \<cdot>l \<sigma>. x \<in># mset CA - mset Ls#} + {#M \<cdot>l \<sigma>. M \<in># mset D#} = C \<cdot> \<sigma> + mset D \<cdot> \<sigma>"
      using diff unfolding subst_cls_def by simp
    then have "{#x \<cdot>l \<sigma>. x \<in># mset CA - mset Ls#} + {#M \<cdot>l \<sigma>. M \<in># mset D#} = E"
      using res'(1) by auto
    then have "{#M \<cdot>l \<sigma>. M \<in># mset (remove_all CA Ls)#} + {#M \<cdot>l \<sigma> . M \<in># mset D#} = E"
      using remove_all_mset_minus[of Ls CA] ls_sub_ca by auto
    then have "mset (resolvent D A CA Ls) = E"
      unfolding resolvable_def Let_def resolvent_def using Al_p(1) Ls_def atms_of_poss res'(4)
      by (metis image_mset_union mset_append mset_map option.sel)
    ultimately have "E \<in> mset ` set (resolve_on A D CA)"
      unfolding resolve_on_def by auto
  }
  then show "{E. \<exists>AA \<sigma>. ord_resolve S [mset CA] ({#Neg A#} + mset D) [AA] [A] \<sigma> E}
    \<subseteq> mset ` set (resolve_on A D CA)"
    by auto
qed

lemma set_resolve_eq_UNION_set_resolve_on:
  "set (resolve C D) =
   (\<Union>L \<in> set D.
      (case L of
         Pos _ \<Rightarrow> {}
       | Neg A \<Rightarrow> if maximal_wrt A (mset D) then set (resolve_on A (remove1 L D) C) else {}))"
  unfolding resolve_def by (fastforce split: literal.splits if_splits)

lemma resolve_eq_Bin_ord_resolve: "mset ` set (resolve C D) = Bin_ord_resolve (mset C) (mset D)"
  unfolding set_resolve_eq_UNION_set_resolve_on
  apply (unfold image_UN literal.case_distrib if_distrib)
  apply (subst resolve_on_eq_UNION_Bin_ord_resolve)
  apply (rule order_antisym)
   apply (force split: literal.splits if_splits)
  apply (clarsimp split: literal.splits if_splits)
  apply (rule_tac x = "Neg A" in bexI)
   apply (rule conjI)
    apply blast
   apply clarify
   apply (rule conjI)
    apply clarify
    apply (rule_tac x = AA in exI)
    apply (rule_tac x = \<sigma> in exI)
    apply (frule ord_resolve.simps[THEN iffD1])
    apply force
   apply (drule ord_resolve.simps[THEN iffD1])
   apply (clarsimp simp: eligible_iff simp del: subst_cls_add_mset subst_cls_union)
   apply (drule maximal_wrt_subst)
   apply sat
  apply (drule ord_resolve.simps[THEN iffD1])
  using set_mset_mset by fastforce

lemma poss_in_map_clauseD:
  "poss AA \<subseteq># map_clause f C \<Longrightarrow> \<exists>AA0. poss AA0 \<subseteq># C \<and> AA = {#f A. A \<in># AA0#}"
proof (induct AA arbitrary: C)
  case (add A AA)
  note ih = this(1) and aaa_sub = this(2)

  have "Pos A \<in># map_clause f C"
    using aaa_sub by auto
  then obtain A0 where
    pa0_in: "Pos A0 \<in># C" and
    a: "A = f A0"
    by clarify (metis literal.distinct(1) literal.exhaust literal.inject(1) literal.simps(9,10))

  have "poss AA \<subseteq># map_clause f (C - {#Pos A0#})"
    using pa0_in aaa_sub[unfolded a] by (simp add: image_mset_remove1_mset_if insert_subset_eq_iff)
  then obtain AA0 where
    paa0_sub: "poss AA0 \<subseteq># C - {#Pos A0#}" and
    aa: "AA = image_mset f AA0"
    using ih by meson

  have "poss (add_mset A0 AA0) \<subseteq># C"
    using pa0_in paa0_sub by (simp add: insert_subset_eq_iff)
  moreover have "add_mset A AA = image_mset f (add_mset A0 AA0)"
    unfolding a aa by simp
  ultimately show ?case
    by blast
qed simp

lemma poss_subset_filterD:
  "poss AA \<subseteq># {#L \<cdot>l \<rho>. L \<in># mset C#} \<Longrightarrow> \<exists>AA0. poss AA0 \<subseteq># mset C \<and> AA = AA0 \<cdot>am \<rho>"
  unfolding subst_atm_mset_def subst_lit_def by (rule poss_in_map_clauseD)

lemma neg_in_map_literalD: "Neg A \<in> map_literal f ` D \<Longrightarrow> \<exists>A0. Neg A0 \<in> D \<and> A = f A0"
  unfolding image_def by (clarify, case_tac x, auto)

lemma neg_in_filterD: "Neg A \<in># {#L \<cdot>l \<rho>'. L \<in># mset D#} \<Longrightarrow> \<exists>A0. Neg A0 \<in># mset D \<and> A = A0 \<cdot>a \<rho>'"
  unfolding subst_lit_def image_def by (rule neg_in_map_literalD) simp

lemma resolve_rename_eq_Bin_ord_resolve_rename:
  "mset ` set (resolve_rename C D) = Bin_ord_resolve_rename (mset C) (mset D)"
proof (intro order_antisym subsetI)
  let ?\<rho>s = "renamings_apart [mset D, mset C]"
  define \<rho>' :: 's where
    "\<rho>' = hd ?\<rho>s"
  define \<rho> :: 's where
    "\<rho> = last ?\<rho>s"

  have tl_\<rho>s: "tl ?\<rho>s = [\<rho>]"
    unfolding \<rho>_def
    using renamings_apart_length Nitpick.size_list_simp(2) Suc_length_conv last.simps
    by (smt length_greater_0_conv list.sel(3))

  {
    fix E
    assume e_in: "E \<in> mset ` set (resolve_rename C D)"

    from e_in obtain AA :: "'a multiset" and A :: 'a and \<sigma> :: 's where
      aa_sub: "poss AA \<subseteq># mset C \<cdot> \<rho>" and
      a_in: "Neg A \<in># mset D \<cdot> \<rho>'" and
      res_e: "ord_resolve S [mset C \<cdot> \<rho>] {#L \<cdot>l \<rho>'. L \<in># mset D#} [AA] [A] \<sigma> E"
      unfolding \<rho>'_def \<rho>_def
      apply atomize_elim
      using e_in unfolding resolve_rename_def Let_def resolve_eq_Bin_ord_resolve
      apply clarsimp
      apply (frule ord_resolve_one_side_prem)
      apply (frule ord_resolve.simps[THEN iffD1])
      apply (rule_tac x = AA in exI)
      apply (clarsimp simp: subst_cls_def)
      apply (rule_tac x = A in exI)
      by (metis (full_types) Melem_subst_cls set_mset_mset subst_cls_def union_single_eq_member)

    obtain AA0 :: "'a multiset" where
      aa0_sub: "poss AA0 \<subseteq># mset C" and
      aa: "AA = AA0 \<cdot>am \<rho>"
      using aa_sub
      apply atomize_elim
      apply (rule ord_resolve.cases[OF res_e])
      by (rule poss_subset_filterD[OF aa_sub[unfolded subst_cls_def]])

    obtain A0 :: 'a where
      a0_in: "Neg A0 \<in> set D" and
      a: "A = A0 \<cdot>a \<rho>'"
      apply atomize_elim
      apply (rule ord_resolve.cases[OF res_e])
      using neg_in_filterD[OF a_in[unfolded subst_cls_def]] by simp

    show "E \<in> Bin_ord_resolve_rename (mset C) (mset D)"
      unfolding ord_resolve_rename.simps
      using res_e
      apply clarsimp
      apply (rule_tac x = AA0 in exI)
      apply (intro conjI)
       apply (rule aa0_sub)
      apply (rule_tac x = A0 in exI)
      apply (intro conjI)
       apply (rule a0_in)
      apply (rule_tac x = \<sigma> in exI)
      unfolding aa a \<rho>'_def[symmetric] \<rho>_def[symmetric] tl_\<rho>s by (simp add: subst_cls_def)
  }
  {
    fix E
    assume e_in: "E \<in> Bin_ord_resolve_rename (mset C) (mset D)"
    show "E \<in> mset ` set (resolve_rename C D)"
      using e_in
      unfolding resolve_rename_def Let_def resolve_eq_Bin_ord_resolve ord_resolve_rename.simps
      apply clarsimp
      apply (rule_tac x = "AA \<cdot>am \<rho>" in exI)
      apply (rule_tac x = "A \<cdot>a \<rho>'" in exI)
      apply (rule_tac x = \<sigma> in exI)
      unfolding tl_\<rho>s \<rho>'_def \<rho>_def by (simp add: subst_cls_def subst_cls_lists_def)
  }
qed

lemma bin_ord_FO_\<Gamma>_def:
  "ord_FO_\<Gamma> S = {Infer {#CA#} DA E | CA DA AA A \<sigma> E. ord_resolve_rename S [CA] DA [AA] [A] \<sigma> E}"
  unfolding ord_FO_\<Gamma>_def
  apply (rule order.antisym)
   apply clarify
   apply (frule ord_resolve_rename_one_side_prem)
   apply simp
   apply (metis Suc_length_conv length_0_conv)
  by blast

lemma ord_FO_\<Gamma>_side_prem: "\<gamma> \<in> ord_FO_\<Gamma> S \<Longrightarrow> side_prems_of \<gamma> = {#THE D. D \<in># side_prems_of \<gamma>#}"
  unfolding bin_ord_FO_\<Gamma>_def by clarsimp

lemma ord_FO_\<Gamma>_infer_from_Collect_eq:
  "{\<gamma> \<in> ord_FO_\<Gamma> S. infer_from (DD \<union> {C}) \<gamma> \<and> C \<in># prems_of \<gamma>} =
   {\<gamma> \<in> ord_FO_\<Gamma> S. \<exists>D \<in> DD \<union> {C}. prems_of \<gamma> = {#C, D#}}"
  unfolding infer_from_def
  apply (rule set_eq_subset[THEN iffD2])
  apply (rule conjI)
   apply clarify
   apply (subst (asm) (1 2) ord_FO_\<Gamma>_side_prem, assumption, assumption)
   apply (subst (1) ord_FO_\<Gamma>_side_prem, assumption)
   apply force
  apply clarify
  apply (subst (asm) (1) ord_FO_\<Gamma>_side_prem, assumption)
  apply (subst (1 2) ord_FO_\<Gamma>_side_prem, assumption)
  by force

lemma inferences_between_eq_UNION: "inference_system.inferences_between (ord_FO_\<Gamma> S) Q C =
  inference_system.inferences_between (ord_FO_\<Gamma> S) {C} C
  \<union> (\<Union>D \<in> Q. inference_system.inferences_between (ord_FO_\<Gamma> S) {D} C)"
  unfolding ord_FO_\<Gamma>_infer_from_Collect_eq inference_system.inferences_between_def by auto

lemma concls_of_inferences_between_singleton_eq_Bin_ord_resolve_rename:
  "concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) {D} C) =
   Bin_ord_resolve_rename C C \<union> Bin_ord_resolve_rename C D \<union> Bin_ord_resolve_rename D C"
proof (intro order_antisym subsetI)
  fix E
  assume e_in: "E \<in> concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) {D} C)"
  then show "E \<in> Bin_ord_resolve_rename C C \<union> Bin_ord_resolve_rename C D
    \<union> Bin_ord_resolve_rename D C"
    unfolding inference_system.inferences_between_def ord_FO_\<Gamma>_infer_from_Collect_eq
      bin_ord_FO_\<Gamma>_def infer_from_def by (fastforce simp: add_mset_eq_add_mset)
qed (force simp: inference_system.inferences_between_def infer_from_def ord_FO_\<Gamma>_def)

lemma concls_of_inferences_between_eq_Bin_ord_resolve_rename:
  "concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) Q C) =
   Bin_ord_resolve_rename C C \<union> (\<Union>D \<in> Q. Bin_ord_resolve_rename C D \<union> Bin_ord_resolve_rename D C)"
  by (subst inferences_between_eq_UNION)
    (auto simp: image_Un image_UN concls_of_inferences_between_singleton_eq_Bin_ord_resolve_rename)

lemma resolve_rename_either_way_eq_congls_of_inferences_between:
  "mset ` set (resolve_rename C C) \<union> (\<Union>D \<in> Q. mset ` set (resolve_rename_either_way C D)) =
   concls_of (inference_system.inferences_between (ord_FO_\<Gamma> S) (mset ` Q) (mset C))"
  by (simp add: resolve_rename_either_way_def image_Un resolve_rename_eq_Bin_ord_resolve_rename
      concls_of_inferences_between_eq_Bin_ord_resolve_rename UN_Un_distrib)

lemma compute_inferences:
  assumes
    ci_in: "(C, i) \<in> set P" and
    ci_min: "\<forall>(D, j) \<in># mset (map (apfst mset) P). weight (mset C, i) \<le> weight (D, j)"
  shows
    "wstate_of_dstate ([], P, Q, n) \<leadsto>\<^sub>w
     wstate_of_dstate (map (\<lambda>D. (D, n)) (remdups_gen mset (resolve_rename C C @
         concat (map (resolve_rename_either_way C \<circ> fst) Q))),
       filter (\<lambda>(D, j). mset D \<noteq> mset C) P, (C, i) # Q, Suc n)"
    (is "_ \<leadsto>\<^sub>w wstate_of_dstate (?N, _)")
proof -
  have ms_ci_in: "(mset C, i) \<in># image_mset (apfst mset) (mset P)"
    using ci_in by force

  show ?thesis
    apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
          wrp.inference_computation[of "mset (map (apfst mset) P) - {#(mset C, i)#}" "mset C" i
            "mset (map (apfst mset) ?N)" n "mset (map (apfst mset) Q)"]])
       apply (simp add: add_mset_remove_trivial_eq[THEN iffD2, OF ms_ci_in, symmetric])
    using ms_ci_in
      apply (simp add: ci_in image_mset_remove1_mset_if)
      apply (smt apfst_conv case_prodE case_prodI2 case_prod_conv filter_mset_cong
        image_mset_filter_swap mset_filter)
     apply (metis ci_min in_diffD)
    apply (simp only: list.map_comp apfst_comp_rpair_const)
    apply (simp only: list.map_comp[symmetric])
    apply (subst mset_map)
    apply (unfold mset_map_remdups_gen mset_remdups_gen_ident)
    apply (subst image_mset_mset_set)
     apply (simp add: inj_on_def)
    apply (subst mset_set_eq_iff)
      apply simp
     apply (simp add: finite_ord_FO_resolution_inferences_between)
    apply (rule arg_cong[of _ _ "\<lambda>N. (\<lambda>D. (D, n)) ` N"])
    apply (simp only: map_concat list.map_comp image_comp)
    using resolve_rename_either_way_eq_congls_of_inferences_between[of C "fst ` set Q", symmetric]
    by (simp add: image_comp comp_def image_UN)
qed

lemma nonfinal_deterministic_RP_step:
  assumes
    nonfinal: "\<not> is_final_dstate St" and
    step: "St' = deterministic_RP_step St"
  shows "wstate_of_dstate St \<leadsto>\<^sub>w\<^sup>+ wstate_of_dstate St'"
proof -
  obtain N P Q :: "'a dclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st deterministic_RP_step.simps, simplified]

  show ?thesis
  proof (cases "\<exists>Ci \<in> set P \<union> set Q. fst Ci = []")
    case nil_in: True
    note step = step[simplified nil_in, simplified]

    have nil_in': "[] \<in> fst ` set (P @ Q)"
      using nil_in by (force simp: image_def)

    have star: "[] \<in> fst ` set (P @ Q) \<Longrightarrow>
      wstate_of_dstate (N, P, Q, n)
      \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], remdups_clss P @ Q, n + length (remdups_clss P))"
    proof (induct "length (remdups_clss P)" arbitrary: N P Q n)
      case 0
      note len_p = this(1) and nil_in' = this(2)

      have p_nil: "P = []"
        using len_p remdups_clss_Nil_iff by simp
      have "wstate_of_dstate (N, [], Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], Q, n)"
        by (rule empty_N_if_Nil_in_P_or_Q[OF nil_in'[unfolded p_nil]])
      then show ?case
        unfolding p_nil by simp
    next
      case (Suc k)
      note ih = this(1) and suc_k = this(2) and nil_in' = this(3)

      have "P \<noteq> []"
        using suc_k remdups_clss_Nil_iff by force
      hence p_cons: "P = hd P # tl P"
        by simp

      obtain C :: "'a lclause" and i :: nat where
        ci: "(C, i) = select_min_weight_clause (hd P) (tl P)"
        by (metis prod.exhaust)

      have ci_in: "(C, i) \<in> set P"
        unfolding ci using p_cons select_min_weight_clause_in[of "hd P" "tl P"] by simp
      have ci_min: "\<forall>(D, j) \<in># mset (map (apfst mset) P). weight (mset C, i) \<le> weight (D, j)"
        by (subst p_cons) (simp add: select_min_weight_clause_min_weight[OF ci, simplified])

      let ?P' = "filter (\<lambda>(D, j). mset D \<noteq> mset C) P"

      have ms_p'_ci_q_eq: "mset (remdups_clss ?P' @ (C, i) # Q) = mset (remdups_clss P @ Q)"
        apply (subst (2) p_cons)
        apply (subst remdups_clss.simps(2))
        by (auto simp: Let_def case_prod_beta p_cons[symmetric] ci[symmetric])
      then have len_p: "length (remdups_clss P) = length (remdups_clss ?P') + 1"
        by (smt Suc_eq_plus1_left add.assoc add_right_cancel length_Cons length_append
            mset_eq_length)

      have "wstate_of_dstate (N, P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], P, Q, n)"
        by (rule empty_N_if_Nil_in_P_or_Q[OF nil_in'])
      also obtain N' :: "'a dclause list" where
        "\<dots> \<leadsto>\<^sub>w wstate_of_dstate (N', ?P', (C, i) # Q, Suc n)"
        by (atomize_elim, rule exI, rule compute_inferences[OF ci_in], use ci_min in fastforce)
      also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [], remdups_clss P @ Q, n + length (remdups_clss P))"
        apply (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
            ih[of ?P' "(C, i) # Q" N' "Suc n"], OF refl])
        using ms_p'_ci_q_eq suc_k nil_in' ci_in
          apply (simp_all add: len_p)
         apply (metis (no_types) apfst_conv image_mset_add_mset)
        by force
      finally show ?case
        .
    qed
    show ?thesis
      unfolding st step using star[OF nil_in'] nonfinal[unfolded st is_final_dstate.simps]
      by cases simp_all
  next
    case nil_ni: False
    note step = step[simplified nil_ni, simplified]
    show ?thesis
    proof (cases N)
      case n_nil: Nil
      note step = step[unfolded n_nil, simplified]
      show ?thesis
      proof (cases P)
        case Nil
        then have False
          using n_nil nonfinal[unfolded st] by (simp add: is_final_dstate.simps)
        then show ?thesis
          using step by simp
      next
        case p_cons: (Cons P0 P')
        note step = step[unfolded p_cons list.case, folded p_cons]

        obtain C :: "'a lclause" and i :: nat where
          ci: "(C, i) = select_min_weight_clause P0 P'"
          by (metis prod.exhaust)
        note step = step[unfolded select, simplified]

        have ci_in: "(C, i) \<in> set P"
          by (rule select_min_weight_clause_in[of P0 P', folded ci p_cons])

        show ?thesis
          unfolding st n_nil step p_cons[symmetric] ci[symmetric] prod.case
          by (rule tranclp.r_into_trancl, rule compute_inferences[OF ci_in])
            (simp add: select_min_weight_clause_min_weight[OF ci, simplified] p_cons)
      qed
    next
      case n_cons: (Cons Ci N')
      note step = step[unfolded n_cons, simplified]

      obtain C :: "'a lclause" and i :: nat where
        ci: "Ci = (C, i)"
        by (cases Ci) simp
      note step = step[unfolded ci, simplified]

      define C' :: "'a lclause" where
        "C' = reduce (map fst P @ map fst Q) [] C"
      note step = step[unfolded ci C'_def[symmetric], simplified]

      have "wstate_of_dstate ((E @ C, i) # N', P, Q, n)
           \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((E @ reduce (map fst P @ map fst Q) E C, i) # N', P, Q, n)" for E
        unfolding C'_def
      proof (induct C arbitrary: E)
        case (Cons L C)
        note ih = this(1)
        show ?case
        proof (cases "is_reducible_lit (map fst P @ map fst Q) (E @ C) L")
          case l_red: True
          then have red_lc:
            "reduce (map fst P @ map fst Q) E (L # C) = reduce (map fst P @ map fst Q) E C"
            by simp
          obtain D D' :: "'a literal list" and L' :: "'a literal" and \<sigma> :: 's where
            "D \<in> set (map fst P @ map fst Q)" and
            "D' = remove1 L' D" and
            "L' \<in> set D" and
            "- L = L' \<cdot>l \<sigma>" and
            "mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
            using l_red unfolding is_reducible_lit_def comp_def by blast
          then have \<sigma>:
            "mset D' + {#L'#} \<in> set (map (mset \<circ> fst) (P @ Q))"
            "- L = L' \<cdot>l \<sigma> \<and> mset D' \<cdot> \<sigma> \<subseteq># mset (E @ C)"
            unfolding is_reducible_lit_def by (auto simp: comp_def)
          have "wstate_of_dstate ((E @ L # C, i) # N', P, Q, n)
              \<leadsto>\<^sub>w wstate_of_dstate ((E @ C, i) # N', P, Q, n)"
            by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
                  wrp.forward_reduction[of "mset D'" L' "mset (map (apfst mset) P)"
                    "mset (map (apfst mset) Q)" L \<sigma> "mset (E @ C)" "mset (map (apfst mset) N')"
                    i n]])
              (use \<sigma> in \<open>auto simp: comp_def\<close>)
          then show ?thesis
            unfolding red_lc using ih[of E] by (rule converse_rtranclp_into_rtranclp)
        next
          case False
          then show ?thesis
            using ih[of "L # E"] by simp
        qed
      qed simp
      then have red_C:
        "wstate_of_dstate ((C, i) # N', P, Q, n) \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P, Q, n)"
        unfolding C'_def by (metis self_append_conv2)

      have proc_C: "wstate_of_dstate ((C', i) # N', P', Q', n')
          \<leadsto>\<^sub>w wstate_of_dstate (N', (C', i) # P', Q', n')" for P' Q' n'
        by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
              wrp.clause_processing[of "mset (map (apfst mset) N')" "mset C'" i
                "mset (map (apfst mset) P')" "mset (map (apfst mset) Q')" n']],
            simp+)

      show ?thesis
      proof (cases "C' = []")
        case True
        note c'_nil = this
        note step = step[simplified c'_nil, simplified]

        have
          filter_p: "filter (Not \<circ> strictly_subsume [[]] \<circ> fst) P = []" and
          filter_q: "filter (Not \<circ> strictly_subsume [[]] \<circ> fst) Q = []"
          using nil_ni unfolding strictly_subsume_def filter_empty_conv find_None_iff by force+

        note red_C[unfolded c'_nil]
        also have "wstate_of_dstate (([], i) # N', P, Q, n)
            \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], Q, n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
                remove_strictly_subsumed_clauses_in_P[of "[]" _ "[]", unfolded append_Nil],
                OF refl])
            (auto simp: filter_p)
        also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (([], i) # N', [], [], n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w\<^sup>*)", OF _ _
                remove_strictly_subsumed_clauses_in_Q[of "[]" _ _ "[]", unfolded append_Nil],
                OF refl])
            (auto simp: filter_q)
        also note proc_C[unfolded c'_nil, THEN tranclp.r_into_trancl[of "(\<leadsto>\<^sub>w)"]]
        also have "wstate_of_dstate (N', [([], i)], [], n)
            \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ([], [([], i)], [], n)"
          by (rule empty_N_if_Nil_in_P_or_Q) simp
        also have "\<dots> \<leadsto>\<^sub>w wstate_of_dstate ([], [], [([], i)], Suc n)"
          by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
                wrp.inference_computation[of "{#}" "{#}" i "{#}" n "{#}"]])
            (auto simp: ord_FO_resolution_inferences_between_empty_empty)
        finally show ?thesis
          unfolding step st n_cons ci .
      next
        case c'_nnil: False
        note step = step[simplified c'_nnil, simplified]
        show ?thesis
        proof (cases "is_tautology C' \<or> subsume (map fst P @ map fst Q) C'")
          case taut_or_subs: True
          note step = step[simplified taut_or_subs, simplified]

          have "wstate_of_dstate ((C', i) # N', P, Q, n) \<leadsto>\<^sub>w wstate_of_dstate (N', P, Q, n)"
          proof (cases "is_tautology C'")
            case True
            then obtain A :: 'a where
              neg_a: "Neg A \<in> set C'" and pos_a: "Pos A \<in> set C'"
              unfolding is_tautology_def by blast
            show ?thesis
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
                    wrp.tautology_deletion[of A "mset C'" "mset (map (apfst mset) N')" i
                      "mset (map (apfst mset) P)" "mset (map (apfst mset) Q)" n]])
                (use neg_a pos_a in simp_all)
          next
            case False
            then have "subsume (map fst P @ map fst Q) C'"
              using taut_or_subs by blast
            then obtain D :: "'a lclause" where
              d_in: "D \<in> set (map fst P @ map fst Q)" and
              subs: "subsumes (mset D) (mset C')"
              unfolding subsume_def by blast
            show ?thesis
              by (rule arg_cong2[THEN iffD1, of _ _ _ _ "(\<leadsto>\<^sub>w)", OF _ _
                    wrp.forward_subsumption[of "mset D" "mset (map (apfst mset) P)"
                      "mset (map (apfst mset) Q)" "mset C'" "mset (map (apfst mset) N')" i n]],
                  use d_in subs in \<open>auto simp: subsume_def\<close>)
          qed
          then show ?thesis
            unfolding step st n_cons ci using red_C by (rule rtranclp_into_tranclp1[rotated])
        next
          case not_taut_or_subs: False
          note step = step[simplified not_taut_or_subs, simplified]

          define P' :: "('a literal list \<times> nat) list" where
            "P' = reduce_all C' P"

          obtain back_to_P Q' :: "'a dclause list" where
            red_Q: "(back_to_P, Q') = reduce_all2 C' Q"
            by (metis prod.exhaust)
          note step = step[unfolded red_Q[symmetric], simplified]

          define Q'' :: "('a literal list \<times> nat) list" where
            "Q'' = filter (Not \<circ> strictly_subsume [C'] \<circ> fst) Q'"
          define P'' :: "('a literal list \<times> nat) list" where
            "P'' = filter (Not \<circ> strictly_subsume [C'] \<circ> fst) (back_to_P @ P')"
          note step = step[unfolded P'_def[symmetric] Q''_def[symmetric] P''_def[symmetric],
              simplified]

          note red_C
          also have "wstate_of_dstate ((C', i) # N', P, Q, n)
              \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P', Q, n)"
            unfolding P'_def by (rule reduce_clauses_in_P[of _ _ "[]", unfolded append_Nil]) simp+
          also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', back_to_P @ P', Q', n)"
            unfolding P'_def
            by (rule reduce_clauses_in_Q[of C' _ _ "[]" Q, folded red_Q,
                  unfolded append_Nil prod.sel])
              (auto intro: reduce_idem simp: reduce_all_def)
          also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', back_to_P @ P', Q'', n)"
            unfolding Q''_def
            by (rule remove_strictly_subsumed_clauses_in_Q[of _ _ _ "[]", unfolded append_Nil])
              simp
          also have "\<dots> \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate ((C', i) # N', P'', Q'', n)"
            unfolding P''_def
            by (rule remove_strictly_subsumed_clauses_in_P[of _ _ "[]", unfolded append_Nil]) auto
          also note proc_C[THEN tranclp.r_into_trancl[of "(\<leadsto>\<^sub>w)"]]
          finally show ?thesis
            unfolding step st n_cons ci P''_def by simp
        qed
      qed
    qed
  qed
qed

lemma final_deterministic_RP_step: "is_final_dstate St \<Longrightarrow> deterministic_RP_step St = St"
  by (cases St) (auto simp: deterministic_RP_step.simps is_final_dstate.simps)

lemma deterministic_RP_SomeD:
  assumes "deterministic_RP (N, P, Q, n) = Some R"
  shows "\<exists>N' P' Q' n'. (\<exists>k. (deterministic_RP_step ^^ k) (N, P, Q, n) = (N', P', Q', n'))
    \<and> is_final_dstate (N', P', Q', n') \<and> R = map fst Q'"
proof (induct rule: deterministic_RP.raw_induct[OF _ assms])
  case (1 self_call St R)
  note ih = this(1) and step = this(2)

  obtain N P Q :: "'a dclause list" and n :: nat where
    st: "St = (N, P, Q, n)"
    by (cases St) blast
  note step = step[unfolded st, simplified]

  show ?case
  proof (cases "is_final_dstate (N, P, Q, n)")
    case True
    then have "(deterministic_RP_step ^^ 0) (N, P, Q, n) = (N, P, Q, n)
      \<and> is_final_dstate (N, P, Q, n) \<and> R = map fst Q"
      using step by simp
    then show ?thesis
      unfolding st by blast
  next
    case nonfinal: False
    note step = step[simplified nonfinal, simplified]

    obtain N' P' Q' :: "'a dclause list" and n' k :: nat where
      "(deterministic_RP_step ^^ k) (deterministic_RP_step (N, P, Q, n)) = (N', P', Q', n')" and
      "is_final_dstate (N', P', Q', n')"
      "R = map fst Q'"
      using ih[OF step] by blast
    then show ?thesis
      unfolding st funpow_Suc_right[symmetric, THEN fun_cong, unfolded comp_apply] by blast
  qed
qed

context
  fixes
    N0 :: "'a dclause list" and
    n0 :: nat and
    R :: "'a lclause list"
begin

abbreviation St0 :: "'a dstate" where
  "St0 \<equiv> (N0, [], [], n0)"

abbreviation grounded_N0 where
  "grounded_N0 \<equiv> grounding_of_clss (set (map (mset \<circ> fst) N0))"

abbreviation grounded_R :: "'a clause set" where
  "grounded_R \<equiv> grounding_of_clss (set (map mset R))"

primcorec derivation_from :: "'a dstate \<Rightarrow> 'a dstate llist" where
  "derivation_from St =
   LCons St (if is_final_dstate St then LNil else derivation_from (deterministic_RP_step St))"

abbreviation Sts :: "'a dstate llist" where
  "Sts \<equiv> derivation_from St0"

abbreviation wSts :: "'a wstate llist" where
  "wSts \<equiv> lmap wstate_of_dstate Sts"

lemma full_deriv_wSts_trancl_weighted_RP: "full_chain (\<leadsto>\<^sub>w\<^sup>+) wSts"
proof -
  have "Sts' = derivation_from St0' \<Longrightarrow> full_chain (\<leadsto>\<^sub>w\<^sup>+) (lmap wstate_of_dstate Sts')"
    for St0' Sts'
  proof (coinduction arbitrary: St0' Sts' rule: full_chain.coinduct)
    case sts': full_chain
    show ?case
    proof (cases "is_final_dstate St0'")
      case True
      then have "ltl (lmap wstate_of_dstate Sts') = LNil"
        unfolding sts' by simp
      then have "lmap wstate_of_dstate Sts' = LCons (wstate_of_dstate St0') LNil"
        unfolding sts' by (subst derivation_from.code, subst (asm) derivation_from.code, auto)
      moreover have "\<And>St''. \<not> wstate_of_dstate St0' \<leadsto>\<^sub>w St''"
        using True by (rule is_final_dstate_imp_not_weighted_RP)
      ultimately show ?thesis
        by (meson tranclpD)
    next
      case nfinal: False
      have "lmap wstate_of_dstate Sts' =
        LCons (wstate_of_dstate St0') (lmap wstate_of_dstate (ltl Sts'))"
        unfolding sts' by (subst derivation_from.code) simp
      moreover have "ltl Sts' = derivation_from (deterministic_RP_step St0')"
        unfolding sts' using nfinal by (subst derivation_from.code) simp
      moreover have "wstate_of_dstate St0' \<leadsto>\<^sub>w\<^sup>+ wstate_of_dstate (lhd (ltl Sts'))"
        unfolding sts' using nonfinal_deterministic_RP_step[OF nfinal refl] nfinal
        by (subst derivation_from.code) simp
      ultimately show ?thesis
        by fastforce
    qed
  qed
  then show ?thesis
    by blast
qed

lemmas deriv_wSts_trancl_weighted_RP = full_chain_imp_chain[OF full_deriv_wSts_trancl_weighted_RP]

definition sswSts :: "'a wstate llist" where
  "sswSts = (SOME wSts'.
     full_chain (\<leadsto>\<^sub>w) wSts' \<and> emb wSts wSts' \<and> lhd wSts' = lhd wSts \<and> llast wSts' = llast wSts)"

lemma sswSts:
  "full_chain (\<leadsto>\<^sub>w) sswSts \<and> emb wSts sswSts \<and> lhd sswSts = lhd wSts \<and> llast sswSts = llast wSts"
  unfolding sswSts_def
  by (rule someI_ex[OF full_chain_tranclp_imp_exists_full_chain[OF
          full_deriv_wSts_trancl_weighted_RP]])

lemmas full_deriv_sswSts_weighted_RP = sswSts[THEN conjunct1]
lemmas emb_sswSts = sswSts[THEN conjunct2, THEN conjunct1]
lemmas lfinite_sswSts_iff = emb_lfinite[OF emb_sswSts]
lemmas lhd_sswSts = sswSts[THEN conjunct2, THEN conjunct2, THEN conjunct1]
lemmas llast_sswSts = sswSts[THEN conjunct2, THEN conjunct2, THEN conjunct2]

lemmas deriv_sswSts_weighted_RP = full_chain_imp_chain[OF full_deriv_sswSts_weighted_RP]

lemma not_lnull_sswSts: "\<not> lnull sswSts"
  using deriv_sswSts_weighted_RP by (cases rule: chain.cases) auto

lemma empty_ssgP0: "wrp.P_of_wstate (lhd sswSts) = {}"
  unfolding lhd_sswSts by (subst derivation_from.code) simp

lemma empty_ssgQ0: "wrp.Q_of_wstate (lhd sswSts) = {}"
  unfolding lhd_sswSts by (subst derivation_from.code) simp

lemmas sswSts_thms = full_deriv_sswSts_weighted_RP empty_ssgP0 empty_ssgQ0

abbreviation S_ssgQ :: "'a clause \<Rightarrow> 'a clause" where
  "S_ssgQ \<equiv> wrp.S_gQ sswSts"

abbreviation ord_\<Gamma> :: "'a inference set" where
  "ord_\<Gamma> \<equiv> ground_resolution_with_selection.ord_\<Gamma> S_ssgQ"

abbreviation Rf :: "'a clause set \<Rightarrow> 'a clause set" where
  "Rf \<equiv> standard_redundancy_criterion.Rf"

abbreviation Ri :: "'a clause set \<Rightarrow> 'a inference set" where
  "Ri \<equiv> standard_redundancy_criterion.Ri ord_\<Gamma>"

abbreviation saturated_upto :: "'a clause set \<Rightarrow> bool" where
  "saturated_upto \<equiv> redundancy_criterion.saturated_upto ord_\<Gamma> Rf Ri"

context
  assumes drp_some: "deterministic_RP St0 = Some R"
begin

lemma lfinite_Sts: "lfinite Sts"
proof (induct rule: deterministic_RP.raw_induct[OF _ drp_some])
  case (1 self_call St St')
  note ih = this(1) and step = this(2)
  show ?case
    using step by (subst derivation_from.code, auto intro: ih)
qed

lemma lfinite_wSts: "lfinite wSts"
  by (rule lfinite_lmap[THEN iffD2, OF lfinite_Sts])

lemmas lfinite_sswSts = lfinite_sswSts_iff[THEN iffD2, OF lfinite_wSts]

theorem
  deterministic_RP_saturated: "saturated_upto grounded_R" (is ?saturated) and
  deterministic_RP_model: "I \<Turnstile>s grounded_N0 \<longleftrightarrow> I \<Turnstile>s grounded_R" (is ?model)
proof -
  obtain N' P' Q' :: "'a dclause list" and n' k :: nat where
    k_steps: "(deterministic_RP_step ^^ k) St0 = (N', P', Q', n')" (is "_ = ?Stk") and
    final: "is_final_dstate (N', P', Q', n')" and
    r: "R = map fst Q'"
    using deterministic_RP_SomeD[OF drp_some] by blast

  have wrp: "wstate_of_dstate St0 \<leadsto>\<^sub>w\<^sup>* wstate_of_dstate (llast Sts)"
    using lfinite_chain_imp_rtranclp_lhd_llast
    by (metis (no_types) deriv_sswSts_weighted_RP derivation_from.disc_iff derivation_from.simps(2)
        lfinite_Sts lfinite_sswSts llast_lmap llist.map_sel(1) sswSts)

  have last_sts: "llast Sts = ?Stk"
  proof -
    have "(deterministic_RP_step ^^ k') St0' = ?Stk \<Longrightarrow> llast (derivation_from St0') = ?Stk"
      for St0' k'
    proof (induct k' arbitrary: St0')
      case 0
      then show ?case
        using final by (subst derivation_from.code) simp
    next
      case (Suc k')
      note ih = this(1) and suc_k'_steps = this(2)
      show ?case
      proof (cases "is_final_dstate St0'")
        case True
        then show ?thesis
          using ih[of "deterministic_RP_step St0'"] suc_k'_steps final_deterministic_RP_step
            funpow_fixpoint[of deterministic_RP_step]
          by auto
      next
        case False
        then show ?thesis
          using ih[of "deterministic_RP_step St0'"] suc_k'_steps
          by (subst derivation_from.code) (simp add: llast_LCons funpow_swap1[symmetric])
      qed
    qed
    then show ?thesis
      using k_steps by blast
  qed

  have fin_gr_fgsts: "lfinite (lmap wrp.grounding_of_wstate sswSts)"
    by (rule lfinite_lmap[THEN iffD2, OF lfinite_sswSts])

  have lim_last: "Liminf_llist (lmap wrp.grounding_of_wstate sswSts) =
    wrp.grounding_of_wstate (llast sswSts)"
    unfolding lfinite_Liminf_llist[OF fin_gr_fgsts] llast_lmap[OF lfinite_sswSts not_lnull_sswSts]
    using not_lnull_sswSts by simp

  have gr_st0: "wrp.grounding_of_wstate (wstate_of_dstate St0) = grounded_N0"
    by (simp add: clss_of_state_def comp_def)

  have "?saturated \<and> ?model"
  proof (cases "[] \<in> set R")
    case True
    then have emp_in: "{#} \<in> grounded_R"
      unfolding grounding_of_clss_def grounding_of_cls_def by (auto intro: ex_ground_subst)

    have "grounded_R \<subseteq> wrp.grounding_of_wstate (llast sswSts)"
      unfolding r llast_sswSts
      by (simp add: last_sts llast_lmap[OF lfinite_Sts] clss_of_state_def grounding_of_clss_def)
    then have gr_last_st: "grounded_R \<subseteq> wrp.grounding_of_wstate (wstate_of_dstate (llast Sts))"
      by (simp add: lfinite_Sts llast_lmap llast_sswSts)

    have gr_r_fls: "\<not> I \<Turnstile>s grounded_R"
      using emp_in unfolding true_clss_def by force
    then have gr_last_fls: "\<not> I \<Turnstile>s wrp.grounding_of_wstate (wstate_of_dstate (llast Sts))"
      using gr_last_st unfolding true_clss_def by auto

    have ?saturated
      unfolding wrp.ord_\<Gamma>_saturated_upto_def[OF sswSts_thms]
        wrp.ord_\<Gamma>_contradiction_Rf[OF sswSts_thms emp_in] inference_system.inferences_from_def
      by auto
    moreover have ?model
      unfolding gr_r_fls[THEN eq_False[THEN iffD2]]
      by (rule rtranclp_imp_eq_image[of "(\<leadsto>\<^sub>w)" "\<lambda>St. I \<Turnstile>s wrp.grounding_of_wstate St", OF _ wrp,
            unfolded gr_st0 gr_last_fls[THEN eq_False[THEN iffD2]]])
        (use wrp.weighted_RP_model[OF sswSts_thms] in blast)
    ultimately show ?thesis
      by blast
  next
    case False
    then have gr_last: "wrp.grounding_of_wstate (llast sswSts) = grounded_R"
      using final unfolding r llast_sswSts
      by (simp add: last_sts llast_lmap[OF lfinite_Sts] clss_of_state_def comp_def
          is_final_dstate.simps)
    then have gr_last_st: "wrp.grounding_of_wstate (wstate_of_dstate (llast Sts)) = grounded_R"
      by (simp add: lfinite_Sts llast_lmap llast_sswSts)

    have ?saturated
      using wrp.weighted_RP_saturated[OF sswSts_thms, unfolded gr_last lim_last] by auto
    moreover have ?model
      by (rule rtranclp_imp_eq_image[of "(\<leadsto>\<^sub>w)" "\<lambda>St. I \<Turnstile>s wrp.grounding_of_wstate St", OF _ wrp,
            unfolded gr_st0 gr_last_st])
        (use wrp.weighted_RP_model[OF sswSts_thms] in blast)
    ultimately show ?thesis
      by blast
  qed
  then show ?saturated and ?model
    by blast+
qed

corollary deterministic_RP_refutation:
  "\<not> satisfiable grounded_N0 \<longleftrightarrow> {#} \<in> grounded_R" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?rhs
  then have "\<not> satisfiable grounded_R"
    unfolding true_clss_def true_cls_def by force
  then show ?lhs
    using deterministic_RP_model[THEN iffD1] by blast
next
  assume ?lhs
  then have "\<not> satisfiable grounded_R"
    using deterministic_RP_model[THEN iffD2] by blast
  then show ?rhs
    unfolding wrp.ord_\<Gamma>_saturated_upto_complete[OF sswSts_thms deterministic_RP_saturated] .
qed

end

context
  assumes drp_none: "deterministic_RP St0 = None"
begin

theorem deterministic_RP_complete: "satisfiable grounded_N0"
proof (rule ccontr)
  assume unsat: "\<not> satisfiable grounded_N0"

  have unsat_wSts0: "\<not> satisfiable (wrp.grounding_of_wstate (lhd wSts))"
    using unsat by (subst derivation_from.code) (simp add: clss_of_state_def comp_def)

  have bot_in_ss: "{#} \<in> Q_of_state (wrp.Liminf_wstate sswSts)"
    by (rule wrp.weighted_RP_complete[OF sswSts_thms unsat_wSts0[folded lhd_sswSts]])
  have bot_in_lim: "{#} \<in> Q_of_state (wrp.Liminf_wstate wSts)"
  proof (cases "lfinite Sts")
    case fin: True
    have "wrp.Liminf_wstate sswSts = wrp.Liminf_wstate wSts"
      by (rule Liminf_state_fin, simp_all add: fin lfinite_sswSts_iff not_lnull_sswSts,
          subst (1 2) llast_lmap,
          simp_all add: lfinite_sswSts_iff fin not_lnull_sswSts llast_sswSts)
    then show ?thesis
      using bot_in_ss by simp
  next
    case False
    then show ?thesis
      using bot_in_ss Q_of_Liminf_state_inf[OF _ emb_lmap[OF emb_sswSts]] by auto
  qed
  then obtain k :: nat where
    k_lt: "enat k < llength Sts" and
    emp_in: "{#} \<in> wrp.Q_of_wstate (lnth wSts k)"
    unfolding Liminf_state_def Liminf_llist_def by auto
  have emp_in: "{#} \<in> Q_of_state (state_of_dstate ((deterministic_RP_step ^^ k) St0))"
  proof -
    have "enat k < llength Sts' \<Longrightarrow> Sts' = derivation_from St0' \<Longrightarrow>
      {#} \<in> wrp.Q_of_wstate (lnth (lmap wstate_of_dstate Sts') k) \<Longrightarrow>
      {#} \<in> Q_of_state (state_of_dstate ((deterministic_RP_step ^^ k) St0'))" for St0' Sts' k
    proof (induction k arbitrary: St0' Sts')
      case 0
      then show ?case
        by (subst (asm) derivation_from.code, cases St0', auto simp: comp_def)
    next
      case (Suc k)
      note ih = this(1) and sk_lt = this(2) and sts' = this(3) and emp_in_sk = this(4)

      have k_lt: "enat k < llength (ltl Sts')"
        using sk_lt by (cases Sts') (auto simp: Suc_ile_eq)
      moreover have "ltl Sts' = derivation_from (deterministic_RP_step St0')"
        using sts' k_lt by (cases Sts') auto
      moreover have "{#} \<in> wrp.Q_of_wstate (lnth (lmap wstate_of_dstate (ltl Sts')) k)"
        using emp_in_sk k_lt by (cases Sts') auto
      ultimately show ?case
        using ih[of "ltl Sts'" "deterministic_RP_step St0'"] by (simp add: funpow_swap1)
    qed
    then show ?thesis
      using k_lt emp_in by blast
  qed
  have "deterministic_RP St0 \<noteq> None"
    by (rule is_final_dstate_funpow_imp_deterministic_RP_neq_None[of "Suc k"],
        cases "(deterministic_RP_step ^^ k) St0",
        use emp_in in \<open>force simp: deterministic_RP_step.simps is_final_dstate.simps\<close>)
  then show False
    using drp_none ..
qed

end

end

end

end
