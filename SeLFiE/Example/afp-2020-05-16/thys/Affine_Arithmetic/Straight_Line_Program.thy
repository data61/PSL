section \<open>Straight Line Programs\<close>
theory Straight_Line_Program
  imports
    Floatarith_Expression
    Deriving.Derive
    "HOL-Library.Monad_Syntax"
    "HOL-Library.RBT_Mapping"
begin

unbundle floatarith_notation

derive (linorder) compare_order float

derive linorder floatarith

subsection \<open>Definition\<close>

type_synonym slp = "floatarith list"

primrec interpret_slp::"slp \<Rightarrow> real list \<Rightarrow> real list" where
  "interpret_slp [] = (\<lambda>xs. xs)"
| "interpret_slp (ea # eas) = (\<lambda>xs. interpret_slp eas (interpret_floatarith ea xs#xs))"

subsection \<open>Reification as straight line program (with common subexpression elimination)\<close>

definition "slp_index vs i = (length vs - Suc i)"

definition "slp_index_lookup vs M a = slp_index vs (the (Mapping.lookup M a))"

definition
  "slp_of_fa_bin Binop a b M slp M2 slp2 =
    (case Mapping.lookup M (Binop a b) of
        Some i \<Rightarrow> (Mapping.update (Binop a b) (length slp) M, slp@[Var (slp_index slp i)])
      | None \<Rightarrow> (Mapping.update (Binop a b) (length slp2) M2,
                slp2@[Binop (Var (slp_index_lookup slp2 M2 a)) (Var (slp_index_lookup slp2 M2 b))]))"

definition
  "slp_of_fa_un Unop a M slp M1 slp1 =
    (case Mapping.lookup M (Unop a) of
        Some i \<Rightarrow> (Mapping.update (Unop a) (length slp) M, slp@[Var (slp_index slp i)])
      | None \<Rightarrow> (Mapping.update (Unop a) (length slp1) M1,
                  slp1@[Unop (Var (slp_index_lookup slp1 M1 a))]))"

definition
  "slp_of_fa_cnst Const Const' M vs =
    (Mapping.update Const (length vs) M,
      vs @ [case Mapping.lookup M Const of Some i \<Rightarrow> Var (slp_index vs i) | None \<Rightarrow> Const'])"

fun slp_of_fa :: "floatarith \<Rightarrow> (floatarith, nat) mapping \<Rightarrow> floatarith list \<Rightarrow>
  ((floatarith, nat) mapping \<times> floatarith list)" where
"slp_of_fa (Add a b) M slp =
    (let (M1, slp1) = slp_of_fa a M slp; (M2, slp2) = slp_of_fa b M1 slp1 in
      slp_of_fa_bin Add a b M slp M2 slp2)"
| "slp_of_fa (Mult a b) M slp =
    (let (M1, slp1) = slp_of_fa a M slp; (M2, slp2) = slp_of_fa b M1 slp1 in
      slp_of_fa_bin Mult a b M slp M2 slp2)"
| "slp_of_fa (Min a b) M slp =
    (let (M1, slp1) = slp_of_fa a M slp; (M2, slp2) = slp_of_fa b M1 slp1 in
      slp_of_fa_bin Min a b M slp M2 slp2)"
| "slp_of_fa (Max a b) M slp =
    (let (M1, slp1) = slp_of_fa a M slp; (M2, slp2) = slp_of_fa b M1 slp1 in
      slp_of_fa_bin Max a b M slp M2 slp2)"
| "slp_of_fa (Powr a b) M slp =
    (let (M1, slp1) = slp_of_fa a M slp; (M2, slp2) = slp_of_fa b M1 slp1 in
      slp_of_fa_bin Powr a b M slp M2 slp2)"
| "slp_of_fa (Inverse a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Inverse a M slp M1 slp1)"
| "slp_of_fa (Cos a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Cos a M slp M1 slp1)"
| "slp_of_fa (Arctan a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Arctan a M slp M1 slp1)"
| "slp_of_fa (Abs a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Abs a M slp M1 slp1)"
| "slp_of_fa (Sqrt a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Sqrt a M slp M1 slp1)"
| "slp_of_fa (Exp a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Exp a M slp M1 slp1)"
| "slp_of_fa (Ln a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Ln a M slp M1 slp1)"
| "slp_of_fa (Minus a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Minus a M slp M1 slp1)"
| "slp_of_fa (Floor a) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un Floor a M slp M1 slp1)"
| "slp_of_fa (Power a n) M slp  =
   (let (M1, slp1) = slp_of_fa a M slp in slp_of_fa_un (\<lambda>a. Power a n) a M slp M1 slp1)"
| "slp_of_fa Pi M slp = slp_of_fa_cnst Pi Pi M slp"
| "slp_of_fa (Var v) M slp = slp_of_fa_cnst (Var v) (Var (v + length slp)) M slp"
| "slp_of_fa (Num n) M slp = slp_of_fa_cnst (Num n) (Num n) M slp"

lemma interpret_slp_snoc[simp]:
  "interpret_slp (slp @ [fa]) xs = interpret_floatarith fa (interpret_slp slp xs)#interpret_slp slp xs"
  by (induction slp arbitrary: fa xs) auto

lemma
  binop_slp_of_fa_induction_step:
  assumes
    Binop_IH1:
    "\<And>M slp M' slp'. slp_of_fa fa1 M slp = (M', slp') \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs) \<Longrightarrow>
    subterms fa1 \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp' \<and>
      interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
    and
    Binop_IH2:
    "\<And>M slp M' slp'. slp_of_fa fa2 M slp = (M', slp') \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs) \<Longrightarrow>
    subterms fa2 \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp' \<and>
      interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
    and Binop_prems:
    "(case slp_of_fa fa1 M slp of
      (M1, slp1) \<Rightarrow>
       case slp_of_fa fa2 M1 slp1 of (x, xa) \<Rightarrow> slp_of_fa_bin Binop fa1 fa2 M slp x xa) = (M', slp')"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs"
  assumes subterms_Binop[simp]:
    "\<And>a b. subterms (Binop a b) = insert (Binop a b) (subterms a \<union> subterms b)"
  assumes interpret_Binop[simp]:
    "\<And>a b xs. interpret_floatarith (Binop a b) xs = binop (interpret_floatarith a xs) (interpret_floatarith b xs)"
shows "insert (Binop fa1 fa2) (subterms fa1 \<union> subterms fa2) \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
       the (Mapping.lookup M' f) < length slp' \<and>
       interpret_slp slp' xs ! slp_index_lookup slp' M' f  = interpret_floatarith f xs)"
proof -
  from Binop_prems
  obtain M1 slp1 M2 slp2 where *:
    "slp_of_fa fa1 M slp = (M1, slp1)"
    "slp_of_fa fa2 M1 slp1 = (M2, slp2)"
    "slp_of_fa_bin Binop fa1 fa2 M slp M2 slp2 = (M', slp')"
    by (auto split: prod.splits)
  from Binop_IH1[OF *(1) Binop_prems(2) Binop_prems(3) Binop_prems(4), simplified]
  have IH1:
    "f \<in> subterms fa1 \<Longrightarrow> f \<in> Mapping.keys M1"
    "f \<in> Mapping.keys M \<Longrightarrow> f \<in> Mapping.keys M1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> subterms f \<subseteq> Mapping.keys M1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> the (Mapping.lookup M1 f) < length slp1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> interpret_slp slp1 xs ! slp_index_lookup slp1 M1 f  = interpret_floatarith f xs"
    for f
    by (auto simp: subset_iff)
  from Binop_IH2[OF *(2) IH1(3) IH1(4) IH1(5)]
  have IH2:
    "f \<in> subterms fa2 \<Longrightarrow> f \<in> Mapping.keys M2"
    "f \<in> Mapping.keys M1 \<Longrightarrow> f \<in> Mapping.keys M2"
    "f \<in> Mapping.keys M2 \<Longrightarrow> subterms f \<subseteq> Mapping.keys M2"
    "f \<in> Mapping.keys M2 \<Longrightarrow> the (Mapping.lookup M2 f) < length slp2"
    "f \<in> Mapping.keys M2 \<Longrightarrow> interpret_slp slp2 xs ! slp_index_lookup slp2 M2 f = interpret_floatarith f xs"
    for f
    by (auto simp: subset_iff)
  show ?thesis
  proof (cases "Mapping.lookup M (Binop fa1 fa2)")
    case None
    then have M': "M' = Mapping.update (Binop fa1 fa2) (length slp2) M2"
      and slp': "slp' = slp2 @ [Binop (Var (slp_index_lookup slp2 M2 fa1)) (Var (slp_index_lookup slp2 M2 fa2))]"
      using *
      by (auto simp: slp_of_fa_bin_def)
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      using IH1 IH2
      by (auto simp: M')
    have "Binop fa1 fa2 \<in> Mapping.keys M'"
      using M' by auto
    have M'_0: "Mapping.lookup M' (Binop fa1 fa2) = Some (length slp2)"
      by (auto simp: M' lookup_update)
    have fa1: "fa1 \<in> Mapping.keys M2" and fa2: "fa2 \<in> Mapping.keys M2"
      by (force intro: IH2 IH1)+
    have rew: "binop (interpret_slp slp2 xs ! slp_index_lookup slp2 M2 fa1) (interpret_slp slp2 xs ! slp_index_lookup slp2 M2 fa2) =
      binop (interpret_floatarith fa1 xs) (interpret_floatarith fa2 xs)"
      by (auto simp: IH2 fa1)
    show ?thesis
      apply (auto )
      subgoal by fact
      subgoal
        unfolding M'
        apply (simp add: )
        apply (rule disjI2)
        apply (rule IH2(2))
        apply (rule IH1) apply simp
        done
      subgoal
        unfolding M'
        apply (simp add: )
        apply (rule disjI2)
        apply (rule IH2)
        by simp
      subgoal
        unfolding M'
        apply simp
        apply (rule disjI2)
        apply (rule IH2(2))
        apply (rule IH1(2))
        by simp
      subgoal
        unfolding M'
        apply auto
        apply (simp add: IH1(1) IH2(2))
         apply (simp add: IH1(2) IH2(1))
        using IH2(3)
        by auto
      subgoal for f
        unfolding M' slp'
        apply simp
        apply (auto simp add: lookup_update' rew lookup_map_values slp_index_lookup_def slp_index_def)
        by (simp add: IH2(4) less_Suc_eq)
      subgoal for f
        unfolding M' slp'
        apply simp
        apply (subst rew)
        apply (auto simp add: fa1 lookup_update' rew lookup_map_values slp_index_lookup_def slp_index_def)
        apply (auto simp add: nth_Cons fa1 lookup_update' rew lookup_map_values slp_index_lookup_def slp_index_def
            split: nat.splits)
        using IH2(4) apply fastforce
        by (metis IH2(4) IH2(5) Suc_diff_Suc Suc_inject slp_index_def slp_index_lookup_def)
      done
  next
    case (Some C)
    then have M': "M' = Mapping.update (Binop fa1 fa2) (length slp) M"
      and slp': "slp' = slp @ [Var (slp_index slp C)]"
      and Binop_keys: "(Binop fa1 fa2) \<in> Mapping.keys M"
      using *
      by (auto simp: slp_of_fa_bin_def keys_dom_lookup)
    have "subterms (Binop fa1 fa2) \<subseteq> Mapping.keys M'"
      using Binop_keys assms(4)
      by (force simp: M')
    moreover
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      using Binop_keys
      by (auto simp add: M')
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> interpret_slp slp' xs ! slp_index_lookup slp' M' f =
      interpret_floatarith f xs" for f
      apply (auto simp add: M' lookup_map_values lookup_update' slp' Binop_prems slp_index_def
          slp_index_lookup_def)
      apply (metis Binop_keys Some assms(6) interpret_Binop option.sel slp_index_def slp_index_lookup_def)
      apply (metis Binop_keys Some assms(6) interpret_Binop option.sel slp_index_def slp_index_lookup_def)
      apply (metis assms(6) slp_index_def slp_index_lookup_def)
      done
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> subterms f \<subseteq> Mapping.keys M'" for f
      using Binop_keys Some assms(4,6)
      by (auto simp add: M' lookup_map_values)
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> the (Mapping.lookup M' f) < length slp'" for f
      using Binop_keys Some assms(5,7) IH1 IH2
      by (auto simp add: M' lookup_map_values lookup_update' Binop_prems slp' less_SucI)
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma
  unop_slp_of_fa_induction_step:
  assumes
    Unop_IH1:
    "\<And>M slp M' slp'. slp_of_fa fa1 M slp = (M', slp') \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp) \<Longrightarrow>
    (\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs) \<Longrightarrow>
    subterms fa1 \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp' \<and>
      interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
    and Unop_prems:
    "(case slp_of_fa fa1 M slp of (M1, slp1) \<Rightarrow> slp_of_fa_un Unop fa1 M slp M1 slp1) = (M', slp')"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs"
  assumes subterms_Unop[simp]:
    "\<And>a b. subterms (Unop a) = insert (Unop a) (subterms a)"
  assumes interpret_Unop[simp]:
    "\<And>a b xs. interpret_floatarith (Unop a) xs = unop (interpret_floatarith a xs)"
shows "insert (Unop fa1) (subterms fa1) \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp'  \<and>
      interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
proof -
  from Unop_prems
  obtain M1 slp1 where *:
    "slp_of_fa fa1 M slp = (M1, slp1)"
    "slp_of_fa_un Unop fa1 M slp M1 slp1 = (M', slp')"
    by (auto split: prod.splits)
  from Unop_IH1[OF *(1) Unop_prems(2) Unop_prems(3) Unop_prems(4), simplified]
  have IH1:
    "f \<in> subterms fa1 \<Longrightarrow> f \<in> Mapping.keys M1"
    "f \<in> Mapping.keys M \<Longrightarrow> f \<in> Mapping.keys M1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> subterms f \<subseteq> Mapping.keys M1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> the (Mapping.lookup M1 f) < length slp1"
    "f \<in> Mapping.keys M1 \<Longrightarrow> interpret_slp slp1 xs ! slp_index_lookup slp1 M1 f = interpret_floatarith f xs"
    for f
    by (auto simp: subset_iff)
  show ?thesis
  proof (cases "Mapping.lookup M (Unop fa1)")
    case None
    then have M': "M' = Mapping.update (Unop fa1) (length slp1) M1 "
      and slp': "slp' = slp1 @ [Unop (Var (slp_index_lookup slp1 M1 fa1))]"
      using *
      by (auto simp: slp_of_fa_un_def)
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      using IH1
      by (auto simp: M')
    have "Unop fa1 \<in> Mapping.keys M'"
      using M' by auto
    have fa1: "fa1 \<in> Mapping.keys M1"
      by (force intro: IH1)+
    have rew: "interpret_slp slp1 xs ! slp_index_lookup slp1 M1 fa1  = interpret_floatarith fa1 xs"
      by (auto simp: IH1 fa1)
    show ?thesis
      apply (auto )
      subgoal by fact
      subgoal
        unfolding M'
        apply (simp add: )
        apply (rule disjI2)
        apply (rule IH1) apply simp
        done
      subgoal
        unfolding M'
        apply (simp add: )
        apply (rule disjI2)
        by (rule IH1) simp
      subgoal
        using IH1(3) M' \<open>\<And>x. x \<in> subterms fa1 \<Longrightarrow> x \<in> Mapping.keys M'\<close> by fastforce
      subgoal for f
        unfolding M' slp'
        apply simp
        apply (auto simp add: lookup_update' rew lookup_map_values)
        by (simp add: IH1(4) less_SucI)
      subgoal for f
        unfolding M' slp'
        apply simp
        apply (subst rew)
        apply (auto simp add: fa1 lookup_update' rew lookup_map_values slp_index_lookup_def slp_index_def)
        apply (auto simp add: nth_Cons fa1 lookup_update' rew lookup_map_values slp_index_lookup_def slp_index_def
            split: nat.splits)
        using IH1(4) apply fastforce
        by (metis IH1(4) IH1(5) Suc_diff_Suc Suc_inject slp_index_def slp_index_lookup_def)
      done
  next
    case (Some C)
    then have M': "M' = Mapping.update (Unop fa1) (length slp) M"
      and slp': "slp' = slp @ [Var (slp_index slp C)]"
      and Unop_keys: "(Unop fa1) \<in> Mapping.keys M"
      using *
      by (auto simp: slp_of_fa_un_def keys_dom_lookup)
    have "subterms (Unop fa1) \<subseteq> Mapping.keys M'"
      using Unop_keys assms(3)
      by (force simp: M')
    moreover
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      using Unop_keys assms(5)
      by (force simp: M' IH1)
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> interpret_slp slp' xs ! slp_index_lookup slp' M' f  =
        interpret_floatarith f xs" for f
      apply (auto simp add: M' lookup_map_values lookup_update' slp' Unop_prems slp_index_def slp_index_lookup_def)
      apply (metis Unop_keys Some assms(5) interpret_Unop option.sel slp_index_def slp_index_lookup_def)
      apply (metis Unop_keys Some assms(5) interpret_Unop option.sel slp_index_def slp_index_lookup_def)
      apply (metis assms(5) slp_index_def slp_index_lookup_def)
      done
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> subterms f \<subseteq> Mapping.keys M'" for f
      using Unop_keys Some assms(3,5)
      by (auto simp add: M' lookup_map_values)
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> the (Mapping.lookup M' f) < length slp'" for f
      by (auto simp add: M' lookup_map_values lookup_update' slp' Unop_prems IH1 less_SucI)
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma
  cnst_slp_of_fa_induction_step:
  assumes *:
    "slp_of_fa_cnst Unop Unop' M slp = (M', slp')"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp"
    "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs"
  assumes subterms_Unop[simp]:
    "\<And>a b. subterms (Unop) = {Unop}"
  assumes interpret_Unop[simp]:
    "interpret_floatarith Unop xs = unop xs"
    "interpret_floatarith Unop' (interpret_slp slp xs) = unop xs"
  assumes ui: "unop (interpret_slp slp xs) = unop xs"
  shows "{Unop} \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp' \<and>
      interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
proof -
  show ?thesis
  proof (cases "Mapping.lookup M Unop")
    case None
    then have M': "M' = Mapping.update Unop (length slp) M"
      and slp': "slp' = slp @ [Unop']"
      using *
      by (auto simp: slp_of_fa_cnst_def)
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      by (auto simp: M')
    have "Unop \<in> Mapping.keys M'"
      using M' by auto
    show ?thesis
      apply (auto )
      subgoal by fact
      subgoal
        unfolding M'
        apply (simp add: )
        done
      subgoal
        unfolding M'
        apply (simp add: )
        using assms by auto
      subgoal
        unfolding M' slp'
        apply simp
        apply (auto simp add: lookup_update' ui lookup_map_values)
        using interpret_Unop apply auto[1]
        by (simp add: assms(3) less_Suc_eq)
      subgoal for f
        unfolding M' slp'
        apply simp
        apply (auto simp add: lookup_update' ui lookup_map_values slp_index_lookup_def slp_index_def)
        using interpret_Unop apply auto[1]
          apply (auto simp: nth_Cons split: nat.splits)
        using assms(3) leD apply blast
        by (metis Suc_diff_Suc Suc_inject assms(3) assms(4) slp_index_def slp_index_lookup_def)
      done
  next
    case (Some C)
    then have M': "M' = Mapping.update Unop (length slp) M"
      and slp': "slp' = slp @ [Var (slp_index slp C)]"
      and Unop_keys: "(Unop) \<in> Mapping.keys M"
      using *
      by (auto simp: slp_of_fa_cnst_def keys_dom_lookup)
    have "subterms (Unop) \<subseteq> Mapping.keys M'"
      using Unop_keys
      by (fastforce simp: M')
    moreover
    have "Mapping.keys M \<subseteq> Mapping.keys M'"
      using Unop_keys assms(5)
      by (force simp: M')
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> interpret_slp slp' xs ! slp_index_lookup slp' M' f  = interpret_floatarith f xs" for f
      apply (auto simp add: M' lookup_map_values lookup_update' slp' slp_index_lookup_def slp_index_def)
      apply (metis Some Unop_keys assms(4) interpret_Unop option.sel slp_index_def slp_index_lookup_def)
      apply (metis Some Unop_keys assms(4) interpret_Unop option.sel slp_index_def slp_index_lookup_def)
      by (metis Suc_diff_Suc assms(3) assms(4) nth_Cons_Suc slp_index_def slp_index_lookup_def)
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> subterms f \<subseteq> Mapping.keys M'" for f
      using assms by (auto simp add: M' lookup_map_values lookup_update' slp')
    moreover have "f\<in>Mapping.keys M' \<Longrightarrow> the (Mapping.lookup M' f) < length slp'" for f
      using assms
      by (auto simp add: M' lookup_map_values lookup_update' slp' less_SucI)
    ultimately
    show ?thesis
      by auto
  qed
qed

lemma interpret_slp_nth:
  "n \<ge> length slp \<Longrightarrow> interpret_slp slp xs ! n = xs ! (n - length slp)"
  by (induction slp arbitrary: xs n) auto

theorem
  interpret_slp_of_fa:
  assumes "slp_of_fa fa M slp = (M', slp')"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> (the (Mapping.lookup M f)) < length slp"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs"
  shows "subterms fa \<subseteq> Mapping.keys M' \<and> Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f \<in> Mapping.keys M'.
      subterms f \<subseteq> Mapping.keys M' \<and>
      the (Mapping.lookup M' f) < length slp' \<and>
      (interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs))"
  using assms
proof (induction fa arbitrary: M' slp' M slp)
  case *: (Add fa1 fa2)
  show ?case
    unfolding subterms.simps
    by (rule binop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Mult fa1 fa2)
  show ?case
    unfolding subterms.simps
    by (rule binop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Min fa1 fa2)
  show ?case
    unfolding subterms.simps
    by (rule binop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Max fa1 fa2)
  show ?case
    unfolding subterms.simps
    by (rule binop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Powr fa1 fa2)
  show ?case
    unfolding subterms.simps
    by (rule binop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Minus fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Inverse fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Arctan fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Floor fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Cos fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Ln fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Power fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Abs fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Sqrt fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Exp fa1)
  show ?case
    unfolding subterms.simps
    by (rule unop_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: Pi
  show ?case
    unfolding subterms.simps
    by (rule cnst_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: Num
  show ?case
    unfolding subterms.simps
    by (rule cnst_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]]) auto
next
  case *: (Var n)
  show ?case
    unfolding subterms.simps
    by (rule cnst_slp_of_fa_induction_step[OF
          *[unfolded subterms.simps slp_of_fa.simps Let_def]])
       (auto simp: interpret_slp_nth)
qed

primrec slp_of_fas' where
  "slp_of_fas' [] M slp = (M, slp)"
| "slp_of_fas' (fa#fas) M slp = (let (M, slp) = slp_of_fa fa M slp in slp_of_fas' fas M slp)"

theorem
  interpret_slp_of_fas':
  assumes "slp_of_fas' fas M slp = (M', slp')"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> subterms f \<subseteq> Mapping.keys M"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> the (Mapping.lookup M f) < length slp"
  assumes "\<And>f. f \<in> Mapping.keys M \<Longrightarrow> interpret_slp slp xs ! slp_index_lookup slp M f = interpret_floatarith f xs"
  shows "\<Union>(subterms ` set fas) \<subseteq> Mapping.keys M' \<and> Mapping.keys M \<subseteq> Mapping.keys M' \<and>
    (\<forall>f \<in> Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
      (the (Mapping.lookup M' f) < length slp') \<and>
      (interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs))"
  using assms
proof (induction fas arbitrary: M slp)
  case Nil then show ?case
    by auto
next
  case (Cons fa fas)
  from \<open>slp_of_fas' (fa # fas) M slp = (M', slp')\<close>
  obtain M1 slp1 where
    fa: "slp_of_fa fa M slp = (M1, slp1)"
    and fas: "slp_of_fas' fas M1 slp1 = (M', slp')"
    by (auto split: prod.splits)
  have "subterms fa \<subseteq> Mapping.keys M1 \<and>
    Mapping.keys M \<subseteq> Mapping.keys M1 \<and>
    (\<forall>f\<in>Mapping.keys M1. subterms f \<subseteq> Mapping.keys M1 \<and>
    the (Mapping.lookup M1 f) < length slp1 \<and>
    interpret_slp slp1 xs ! slp_index_lookup slp1 M1 f= interpret_floatarith f xs)"
    apply (rule interpret_slp_of_fa[OF fa, of xs])
    using Cons.prems
    by (auto split: prod.splits simp: trans_less_add2)
  moreover
  then have "(\<Union>a\<in>set fas. subterms a) \<subseteq> Mapping.keys M' \<and>
    Mapping.keys M1 \<subseteq> Mapping.keys M' \<and>
    (\<forall>f\<in>Mapping.keys M'. subterms f \<subseteq> Mapping.keys M' \<and>
    the (Mapping.lookup M' f) < length slp' \<and>
    interpret_slp slp' xs ! slp_index_lookup slp' M' f = interpret_floatarith f xs)"
    using Cons.prems
    by (intro Cons.IH[OF fas])
       (auto split: prod.splits simp: trans_less_add2)
  ultimately
  show ?case
    by auto
qed

definition "slp_of_fas fas =
  (let
    (M, slp) = slp_of_fas' fas Mapping.empty [];
    fasi = map (the o Mapping.lookup M) fas;
    fasi' = map (\<lambda>(a, b). Var (length slp + a - Suc b)) (zip [0..<length fasi] (rev fasi))
  in slp @ fasi')"

lemma length_interpret_slp[simp]:
  "length (interpret_slp slp xs) = length slp + length xs"
  by (induct slp arbitrary: xs) auto

lemma length_interpret_floatariths[simp]:
  "length (interpret_floatariths slp xs) = length slp"
  by (induct slp arbitrary: xs) auto

lemma interpret_slp_append[simp]:
  "interpret_slp (slp1 @ slp2) xs =
    interpret_slp slp2 (interpret_slp slp1 xs)"
  by (induction slp1 arbitrary: slp2 xs) auto

lemma "interpret_slp (map Var [a + 0, b + 1, c + 2, d + 3]) xs =
  (rev (map (\<lambda>(i, e). xs ! (e - i)) (zip [0..<4] [a + 0, b + 1, c + 2, d + 3])))@xs"
  by (auto simp: numeral_eq_Suc)

lemma aC_eq_aa: "xs @ y # zs = (xs @ [y]) @ zs"
  by simp

lemma
  interpret_slp_map_Var:
  assumes "\<And>i. i < length is \<Longrightarrow> is ! i \<ge> i"
  assumes "\<And>i. i < length is \<Longrightarrow> (is ! i - i) < length xs"
  shows "interpret_slp (map Var is) xs =
    (rev (map (\<lambda>(i, e). xs ! (e - i)) (zip [0..<length is] is)))
    @
    xs"
  using assms
proof (induction "is" arbitrary: xs)
  case Nil
  then show ?case by simp
next
  case (Cons a "is")
  show ?case
    unfolding interpret_slp.simps list.map
    apply (subst Cons.IH)
    subgoal using Cons.prems by force
    subgoal using Cons.prems by force
    subgoal
      apply (subst aC_eq_aa)
      apply (subst rev.simps(2)[symmetric])
      apply (rule arg_cong[where f="\<lambda>a. a @ xs"])
      apply (rule arg_cong[where f="rev"])
      unfolding interpret_floatarith.simps
      apply auto
      apply (rule nth_equalityI)
       apply force
      apply auto
      using Cons.prems
      apply (auto simp: nth_append nth_Cons split: nat.splits)
      subgoal
        by (metis Suc_leI le_imp_less_Suc not_le old.nat.simps(5))
      subgoal
        by (simp add: minus_nat.simps(2))
      subgoal
        by (metis Suc_lessI minus_nat.simps(2) old.nat.simps(5))
      done
    done
qed

theorem slp_of_fas:
  "take (length fas) (interpret_slp (slp_of_fas fas) xs) = interpret_floatariths fas xs"
proof -
  obtain M slp where Mslp:
    "slp_of_fas' fas Mapping.empty [] = (M, slp)"
    using old.prod.exhaust by blast
  have M: "\<Union>(subterms ` (set fas)) \<subseteq> Mapping.keys M \<and>
    Mapping.keys (Mapping.empty::(floatarith, nat) mapping) \<subseteq> Mapping.keys M \<and>
    (\<forall>f\<in>Mapping.keys M.
        subterms f \<subseteq> Mapping.keys M \<and>
        the (Mapping.lookup M f) < length slp \<and>
        interpret_slp slp xs ! slp_index_lookup slp M f =
        interpret_floatarith f xs)"
    by (rule interpret_slp_of_fas'[OF Mslp]) auto
  have map_eq:
    "map (\<lambda>(a, b). Var (length slp + a - Suc b)) (zip [0..<length fas] (rev (map ((\<lambda>x. the o (Mapping.lookup x)) M) fas)))
    = map Var (map (\<lambda>(a, b). (length slp + a - Suc b)) (zip [0..<length fas] (rev (map (the \<circ> Mapping.lookup M) fas))))"
    unfolding split_beta'
    by (simp add: split_beta')
  have "take (length fas)
     (interpret_slp
       (slp @
        map (\<lambda>(a, b). Var (length slp + a - Suc b)) (zip [0..<length fas] (rev (map (((\<lambda>x. the o (Mapping.lookup x))) M) fas))))
       xs) =
    interpret_floatariths fas xs"
    apply simp
    unfolding map_eq
    apply (subst interpret_slp_map_Var)
      apply (auto simp: rev_nth)
    subgoal premises prems for i
    proof -
      from prems have " (length fas - Suc i) < length fas" using prems by auto
      then have "fas ! (length fas - Suc i) \<in> set fas"
        by simp
      also have "\<dots> \<subseteq> Mapping.keys M"
        using M by force
      finally have "fas ! (length fas - Suc i) \<in> Mapping.keys M" .
      with M
      show ?thesis
        by auto
    qed
    subgoal premises prems for i
    proof -
      from prems have " (length fas - Suc i) < length fas" using prems by auto
      then have "fas ! (length fas - Suc i) \<in> set fas"
        by simp
      also have "\<dots> \<subseteq> Mapping.keys M"
        using M by force
      finally have "fas ! (length fas - Suc i) \<in> Mapping.keys M" .
      with M
      show ?thesis
        by auto
    qed
    subgoal
      apply (rule nth_equalityI, auto)
      subgoal premises prems for i
      proof -
        from prems have "fas ! i \<in> set fas"
          by simp
        also have "\<dots> \<subseteq> Mapping.keys M"
          using M by force
        finally have "fas ! i \<in> Mapping.keys M" .
        from M[THEN conjunct2, THEN conjunct2, rule_format, OF this]
        show ?thesis
          using prems
          by (auto simp: rev_nth interpret_floatariths_nth slp_index_lookup_def slp_index_def)
      qed
      done
    done
  then show ?thesis
    by (auto simp: slp_of_fas_def Let_def Mslp)
qed


subsection \<open>better code equations for construction of large programs\<close>

definition "slp_indexl slpl i = slpl - Suc i"
definition "slp_indexl_lookup vsl M a = slp_indexl vsl (the (Mapping.lookup M a))"

definition
  "slp_of_fa_rev_bin Binop a b M slp slpl M2 slp2 slpl2 =
    (case Mapping.lookup M (Binop a b) of
        Some i \<Rightarrow> (Mapping.update (Binop a b) (slpl) M, Var (slp_indexl slpl i)#slp, Suc slpl)
      | None \<Rightarrow> (Mapping.update (Binop a b) (slpl2) M2,
                Binop (Var (slp_indexl_lookup slpl2 M2 a)) (Var (slp_indexl_lookup slpl2 M2 b))#slp2,
                  Suc slpl2))"

definition
  "slp_of_fa_rev_un Unop a M slp slpl M1 slp1 slpl1 =
    (case Mapping.lookup M (Unop a) of
        Some i \<Rightarrow> (Mapping.update (Unop a) (slpl) M, Var (slp_indexl slpl i)#slp, Suc slpl)
      | None \<Rightarrow> (Mapping.update (Unop a) (slpl1) M1,
                  Unop (Var (slp_indexl_lookup slpl1 M1 a))#slp1, Suc slpl1))"

definition
  "slp_of_fa_rev_cnst Const Const' M vs vsl =
    (Mapping.update Const vsl M,
      (case Mapping.lookup M Const of Some i \<Rightarrow> Var (slp_indexl vsl i) | None \<Rightarrow> Const')#vs, Suc vsl)"

fun slp_of_fa_rev :: "floatarith \<Rightarrow> (floatarith, nat) mapping \<Rightarrow> floatarith list \<Rightarrow> nat \<Rightarrow>
  ((floatarith, nat) mapping \<times> floatarith list \<times> nat)" where
"slp_of_fa_rev (Add a b) M slp slpl =
    (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl; (M2, slp2, slpl2) = slp_of_fa_rev b M1 slp1 slpl1 in
      slp_of_fa_rev_bin Add a b M slp slpl M2 slp2 slpl2)"
| "slp_of_fa_rev (Mult a b) M slp slpl =
    (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl; (M2, slp2, slpl2) = slp_of_fa_rev b M1 slp1 slpl1 in
      slp_of_fa_rev_bin Mult a b M slp slpl M2 slp2 slpl2)"
| "slp_of_fa_rev (Min a b) M slp slpl =
    (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl; (M2, slp2, slpl2) = slp_of_fa_rev b M1 slp1 slpl1 in
      slp_of_fa_rev_bin Min a b M slp slpl M2 slp2 slpl2)"
| "slp_of_fa_rev (Max a b) M slp slpl =
    (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl; (M2, slp2, slpl2) = slp_of_fa_rev b M1 slp1 slpl1 in
      slp_of_fa_rev_bin Max a b M slp slpl M2 slp2 slpl2)"
| "slp_of_fa_rev (Powr a b) M slp slpl =
    (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl; (M2, slp2, slpl2) = slp_of_fa_rev b M1 slp1 slpl1 in
      slp_of_fa_rev_bin Powr a b M slp slpl M2 slp2 slpl2)"
| "slp_of_fa_rev (Inverse a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Inverse a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Cos a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Cos a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Arctan a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Arctan a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Abs a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Abs a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Sqrt a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Sqrt a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Exp a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Exp a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Ln a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Ln a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Minus a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Minus a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Floor a) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un Floor a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev (Power a n) M slp slpl =
   (let (M1, slp1, slpl1) = slp_of_fa_rev a M slp slpl in slp_of_fa_rev_un (\<lambda>a. Power a n) a M slp slpl M1 slp1 slpl1)"
| "slp_of_fa_rev Pi M slp slpl = slp_of_fa_rev_cnst Pi Pi M slp slpl"
| "slp_of_fa_rev (Var v) M slp slpl = slp_of_fa_rev_cnst (Var v) (Var (v + slpl)) M slp slpl"
| "slp_of_fa_rev (Num n) M slp slpl = slp_of_fa_rev_cnst (Num n) (Num n) M slp slpl"

lemma slp_indexl_length[simp]: "slp_indexl (length xs) i = slp_index xs i"
  by (auto simp: slp_index_def slp_indexl_def)

lemma slp_indexl_lookup_length[simp]: "slp_indexl_lookup (length xs) i = slp_index_lookup xs i"
  by (auto simp: slp_index_lookup_def slp_indexl_lookup_def)

lemma slp_index_rev[simp]: "slp_index (rev xs) i = slp_index xs i"
  by (auto simp: slp_index_def slp_indexl_def)

lemma slp_index_lookup_rev[simp]: "slp_index_lookup (rev xs) i = slp_index_lookup xs i"
  by (auto simp: slp_index_lookup_def slp_indexl_lookup_def)

lemma slp_of_fa_bin_slp_of_fa_rev_bin:
  "slp_of_fa_rev_bin Binop a b M slp (length slp) M2 slp2 (length slp2) =
   (let (M, slp') = slp_of_fa_bin Binop a b M (rev slp) M2 (rev slp2) in (M, rev slp', length slp'))"
  by (auto simp: slp_of_fa_rev_bin_def slp_of_fa_bin_def
      split: prod.splits option.splits)

lemma slp_of_fa_un_slp_of_fa_rev_un:
  "slp_of_fa_rev_un Binop a M slp (length slp) M2 slp2 (length slp2) =
   (let (M, slp') = slp_of_fa_un Binop a M (rev slp) M2 (rev slp2) in (M, rev slp', length slp'))"
  by (auto simp: slp_of_fa_rev_un_def slp_of_fa_un_def split: prod.splits option.splits)

lemma slp_of_fa_cnst_slp_of_fa_rev_cnst:
  "slp_of_fa_rev_cnst Cnst Cnst' M slp (length slp) =
   (let (M, slp') = slp_of_fa_cnst Cnst Cnst' M (rev slp) in (M, rev slp', length slp'))"
  by (auto simp: slp_of_fa_rev_cnst_def slp_of_fa_cnst_def
      split: prod.splits option.splits)

lemma slp_of_fa_rev:
  "slp_of_fa_rev fa M slp (length slp) = (let (M, slp') = slp_of_fa fa M (rev slp) in (M, rev slp', length slp'))"
proof (induction fa arbitrary: M slp)
  case (Add fa1 fa2)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
      (metis (no_types, lifting) Pair_inject length_rev prod.simps(2) rev_rev_ident slp_of_fa_bin_slp_of_fa_rev_bin)
next
  case (Minus fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Mult fa1 fa2)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
      (metis (no_types, lifting) Pair_inject length_rev prod.simps(2) rev_rev_ident slp_of_fa_bin_slp_of_fa_rev_bin)
next
  case (Inverse fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Cos fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Arctan fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Abs fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Max fa1 fa2)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
      (metis (no_types, lifting) Pair_inject length_rev prod.simps(2) rev_rev_ident slp_of_fa_bin_slp_of_fa_rev_bin)
next
  case (Min fa1 fa2)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
      (metis (no_types, lifting) Pair_inject length_rev prod.simps(2) rev_rev_ident slp_of_fa_bin_slp_of_fa_rev_bin)
next
  case Pi
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Sqrt fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Exp fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Powr fa1 fa2)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
      (metis (no_types, lifting) Pair_inject length_rev prod.simps(2) rev_rev_ident slp_of_fa_bin_slp_of_fa_rev_bin)
next
  case (Ln fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Power fa x2a)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Floor fa)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
    (metis (mono_tags, lifting) length_rev prod.simps(2) rev_swap slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Var x)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
next
  case (Num x)
  then show ?case
    by (auto split: prod.splits simp: Let_def
      slp_of_fa_cnst_slp_of_fa_rev_cnst slp_of_fa_bin_slp_of_fa_rev_bin slp_of_fa_un_slp_of_fa_rev_un)
qed

lemma slp_of_fa_code[code]:
  "slp_of_fa fa M slp = (let (M, slp', _) = slp_of_fa_rev fa M (rev slp) (length slp) in (M, rev slp'))"
  using slp_of_fa_rev[of fa M "rev slp"]
  by (auto split: prod.splits)

definition "norm2_slp n = slp_of_fas [floatarith.Inverse (norm2\<^sub>e n)]"

unbundle no_floatarith_notation

end
