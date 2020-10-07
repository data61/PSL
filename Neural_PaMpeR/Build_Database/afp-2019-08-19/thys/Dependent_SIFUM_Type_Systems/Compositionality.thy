(*
Title: Value-Dependent SIFUM-Type-Systems
Authors: Toby Murray, Robert Sison, Edward Pierzchalski, Christine Rizkallah
(Based on the SIFUM-Type-Systems AFP entry, whose authors
 are: Sylvia Grewe, Heiko Mantel, Daniel Schoepe)
*)
section \<open>Compositionality Proof for SIFUM-Security Property\<close>

theory Compositionality
imports Security
begin

context sifum_security_init
begin

(* Set of variables that differs between two memory states: *)
definition 
  differing_vars :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> 'Var set"
where
  "differing_vars mem\<^sub>1 mem\<^sub>2 \<equiv> {x. mem\<^sub>1 x \<noteq> mem\<^sub>2 x}"

definition 
  differing_vars_lists :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> 
                           ((_, _) Mem \<times> (_, _) Mem) list \<Rightarrow> nat \<Rightarrow> 'Var set"
where
  "differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<equiv>
     (differing_vars mem\<^sub>1 (fst (mems ! i)) \<union> differing_vars mem\<^sub>2 (snd (mems ! i)))"

lemma differing_finite: "finite (differing_vars mem\<^sub>1 mem\<^sub>2)"
  by (metis UNIV_def Un_UNIV_left finite_Un finite_memory)

lemma differing_lists_finite: "finite (differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)"
  by (simp add: differing_finite differing_vars_lists_def)


fun makes_compatible ::
  "('Com, 'Var, 'Val) GlobalConf \<Rightarrow>
   ('Com, 'Var, 'Val) GlobalConf \<Rightarrow>
   ((_, _) Mem \<times> (_, _) Mem) list \<Rightarrow>
  bool"
where
  "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems =
  (length cms\<^sub>1 = length cms\<^sub>2 \<and> length cms\<^sub>1 = length mems \<and>
   (\<forall> i. i < length cms\<^sub>1 \<longrightarrow>
       (\<forall> \<sigma>. dom \<sigma> = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<longrightarrow>
         (cms\<^sub>1 ! i, (fst (mems ! i)) [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! i, (snd (mems ! i)) [\<mapsto> \<sigma>])) \<and>
       (\<forall> x. (mem\<^sub>1 x = mem\<^sub>2 x \<or> dma mem\<^sub>1 x = High \<or> x \<in> \<C>) \<longrightarrow>
             x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)) \<and>
    ((length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or> (\<forall> x. \<exists> i. i < length cms\<^sub>1 \<and>
                                          x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)))"

(* This just restates the previous definition using meta-quantification. This allows
  more readable proof blocks that prove each part separately. *)
lemma makes_compatible_intro [intro]:
  "\<lbrakk> length cms\<^sub>1 = length cms\<^sub>2 \<and> length cms\<^sub>1 = length mems;
     (\<And> i \<sigma>. \<lbrakk> i < length cms\<^sub>1; dom \<sigma> = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow>
          (cms\<^sub>1 ! i, (fst (mems ! i)) [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! i, (snd (mems ! i)) [\<mapsto> \<sigma>]));
     (\<And> i x. \<lbrakk> i < length cms\<^sub>1; mem\<^sub>1 x = mem\<^sub>2 x \<or> dma mem\<^sub>1 x = High \<or> x \<in> \<C> \<rbrakk> \<Longrightarrow> 
          x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i);
     (length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or>
     (\<forall> x. \<exists> i. i < length cms\<^sub>1 \<and> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i) \<rbrakk> \<Longrightarrow>
  makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  by auto

(* First, some auxiliary lemmas about makes_compatible: *)
lemma compat_low:
  "\<lbrakk> makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems;
     i < length cms\<^sub>1;
     x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow> dma mem\<^sub>1 x = Low"
proof -
  assume "i < length cms\<^sub>1" and *: "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i" and
    "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  then have
    "(mem\<^sub>1 x = mem\<^sub>2 x \<or> dma mem\<^sub>1 x = High \<or> x \<in> \<C>) \<longrightarrow> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
    by (simp add: Let_def, blast)
  with * show "dma mem\<^sub>1 x = Low"
    by (cases "dma mem\<^sub>1 x", blast)
qed

lemma compat_different:
  "\<lbrakk> makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems;
     i < length cms\<^sub>1;
     x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow> mem\<^sub>1 x \<noteq> mem\<^sub>2 x \<and> dma mem\<^sub>1 x = Low \<and> x \<notin> \<C>"
  by (cases "dma mem\<^sub>1 x", auto)

lemma sound_modes_no_read :
  "\<lbrakk> sound_mode_use (cms, mem); x \<in> (map snd cms ! i) GuarNoReadOrWrite; i < length cms \<rbrakk> \<Longrightarrow>
  doesnt_read_or_modify (fst (cms ! i)) x"
proof -
  fix cms mem x i
  assume sound_modes: "sound_mode_use (cms, mem)" and "i < length cms"
  hence "locally_sound_mode_use (cms ! i, mem)"
    by (auto simp: sound_mode_use_def list_all_length)
  moreover
  assume "x \<in> (map snd cms ! i) GuarNoReadOrWrite"
  ultimately show "doesnt_read_or_modify (fst (cms !i)) x"
    apply (simp add: locally_sound_mode_use_def)
    using \<open>i < length cms\<close> \<open>locally_sound_mode_use (cms ! i, mem)\<close> locally_sound_respects_guarantees respects_own_guarantees_def by auto
qed

lemma differing_vars_neg: "x \<notin> differing_vars_lists mem1 mem2 mems i \<Longrightarrow>
  (fst (mems ! i) x = mem1 x \<and> snd (mems ! i) x = mem2 x)"
  by (simp add: differing_vars_lists_def differing_vars_def)

lemma differing_vars_neg_intro:
  "\<lbrakk> mem\<^sub>1 x = fst (mems ! i) x;
  mem\<^sub>2 x = snd (mems ! i) x \<rbrakk> \<Longrightarrow> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  by (auto simp: differing_vars_lists_def differing_vars_def)

lemma differing_vars_elim [elim]:
  "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<Longrightarrow>
  (fst (mems ! i) x \<noteq> mem\<^sub>1 x) \<or> (snd (mems ! i) x \<noteq> mem\<^sub>2 x)"
  by (auto simp: differing_vars_lists_def differing_vars_def)

lemma makes_compatible_dma_eq:
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes ile: "i < length cms\<^sub>1"
  assumes dom\<sigma>: "dom \<sigma> = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  shows "dma ((fst (mems ! i)) [\<mapsto> \<sigma>]) = dma mem\<^sub>1"
proof(rule dma_\<C>, clarify)
  fix x
  assume "x \<in> \<C>"
  with compat ile have notin_diff: "x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
    by simp
  hence "x \<notin> dom \<sigma>"
    by(metis dom\<sigma>)
  hence "(fst (mems ! i) [\<mapsto> \<sigma>]) x = (fst (mems ! i)) x"
    by(metis subst_not_in_dom)
  moreover have "(fst (mems ! i)) x = mem\<^sub>1 x"
    using notin_diff differing_vars_neg by metis
  ultimately show "(fst (mems ! i) [\<mapsto> \<sigma>]) x = mem\<^sub>1 x" by simp
qed

lemma compat_different_vars:
  "\<lbrakk> fst (mems ! i) x = snd (mems ! i) x;
     x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow>
    mem\<^sub>1 x = mem\<^sub>2 x"
proof -
  assume "x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  hence "fst (mems ! i) x = mem\<^sub>1 x \<and> snd (mems ! i) x = mem\<^sub>2 x"
    by (simp add: differing_vars_lists_def differing_vars_def)
  moreover assume "fst (mems ! i) x = snd (mems ! i) x"
  ultimately show "mem\<^sub>1 x = mem\<^sub>2 x" by auto
qed

lemma differing_vars_subst [rule_format]:
  assumes dom\<sigma>: "dom \<sigma> \<supseteq> differing_vars mem\<^sub>1 mem\<^sub>2"
  shows "mem\<^sub>1 [\<mapsto> \<sigma>] = mem\<^sub>2 [\<mapsto> \<sigma>]"
proof (rule ext)
  fix x
  from dom\<sigma> show "mem\<^sub>1 [\<mapsto> \<sigma>] x = mem\<^sub>2 [\<mapsto> \<sigma>] x"
    unfolding subst_def differing_vars_def
    by (cases "\<sigma> x", auto)
qed

lemma mm_equiv_low_eq:
  "\<lbrakk> \<langle> c\<^sub>1, mds, mem\<^sub>1 \<rangle> \<approx> \<langle> c\<^sub>2, mds, mem\<^sub>2 \<rangle> \<rbrakk> \<Longrightarrow> mem\<^sub>1 =\<^bsub>mds\<^esub>\<^sup>l mem\<^sub>2"
  unfolding mm_equiv.simps strong_low_bisim_mm_def
  by fast

lemma globally_sound_modes_compatible:
  "\<lbrakk> globally_sound_mode_use (cms, mem) \<rbrakk> \<Longrightarrow> compatible_modes (map snd cms)"
  apply (simp add: globally_sound_mode_use_def reachable_mode_states_def)
  using meval_sched.simps(1) by blast

(* map snd cms1 = map snd cms2 states that both global configurations use the same modes *)
lemma compatible_different_no_read :
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)"
                       "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes ile: "i < length cms\<^sub>1"
  assumes x: "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  shows "doesnt_read_or_modify (fst (cms\<^sub>1 ! i)) x \<and> doesnt_read_or_modify (fst (cms\<^sub>2 ! i)) x"
proof -
  from compat have len: "length cms\<^sub>1 = length cms\<^sub>2"
    by simp

  let ?X\<^sub>i = "differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"

  from compat ile x have a: "dma mem\<^sub>1 x = Low"
    by (metis compat_low)

  from compat ile x have b: "mem\<^sub>1 x \<noteq> mem\<^sub>2 x"
    by (metis compat_different)

  from compat ile x have not_in_\<C>: "x \<notin> \<C>"
    by (metis compat_different)

  with a and compat ile x obtain j where
    jprop: "j < length cms\<^sub>1 \<and> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems j"
    by fastforce

  let ?X\<^sub>j = "differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems j"
  obtain \<sigma> :: "'Var \<rightharpoonup> 'Val" where dom\<sigma>: "dom \<sigma> = ?X\<^sub>j"
  proof
    let ?\<sigma> = "\<lambda> x. if (x \<in> ?X\<^sub>j) then Some some_val else None"
    show "dom ?\<sigma> = ?X\<^sub>j" unfolding dom_def by auto
  qed
  let ?mdss = "map snd cms\<^sub>1" and
      ?mems\<^sub>1j = "fst (mems ! j)" and
      ?mems\<^sub>2j = "snd (mems ! j)"

  from jprop dom\<sigma> have subst_eq:
  "?mems\<^sub>1j [\<mapsto> \<sigma>] x = ?mems\<^sub>1j x \<and> ?mems\<^sub>2j [\<mapsto> \<sigma>] x = ?mems\<^sub>2j x"
  by (metis subst_not_in_dom)

  from compat jprop dom\<sigma>
  have "(cms\<^sub>1 ! j, ?mems\<^sub>1j [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! j, ?mems\<^sub>2j [\<mapsto> \<sigma>])"
    by (auto simp: Let_def)

  hence low_eq: "?mems\<^sub>1j [\<mapsto> \<sigma>] =\<^bsub>?mdss ! j\<^esub>\<^sup>l ?mems\<^sub>2j [\<mapsto> \<sigma>]" using modes_eq
    by (metis (no_types) jprop len mm_equiv_low_eq nth_map surjective_pairing)

  with jprop and b have "x \<in> (?mdss ! j) AsmNoReadOrWrite"
  proof -
    { assume "x \<notin> (?mdss ! j) AsmNoReadOrWrite"
      then have mems_eq: "?mems\<^sub>1j x = ?mems\<^sub>2j x"
        using \<open>dma mem\<^sub>1 x = Low\<close> low_eq subst_eq
        makes_compatible_dma_eq[OF compat jprop[THEN conjunct1] dom\<sigma>]
        low_mds_eq_def 
        by (metis (poly_guards_query))

      hence "mem\<^sub>1 x = mem\<^sub>2 x"
        by (metis compat_different_vars jprop)

      hence False by (metis b)
    }
    thus ?thesis by metis
  qed

  hence "x \<in> (?mdss ! i) GuarNoReadOrWrite"
    using sound_modes jprop
    by (metis compatible_modes_def globally_sound_modes_compatible
      length_map sound_mode_use.simps x ile)

  thus "doesnt_read_or_modify (fst (cms\<^sub>1 ! i)) x \<and> doesnt_read_or_modify (fst (cms\<^sub>2 ! i)) x" using sound_modes ile
    by (metis len modes_eq sound_modes_no_read)
qed

definition
  vars_and_\<C> :: "'Var set \<Rightarrow> 'Var set"
where
  "vars_and_\<C> X \<equiv> X \<union> vars_\<C> X"

(* Toby: most of the complexity drops out as doesnt_read_or_modify now implies doesnt_modify *)
fun change_respecting ::
  "('Com, 'Var, 'Val) LocalConf \<Rightarrow>
   ('Com, 'Var, 'Val) LocalConf \<Rightarrow>
   'Var set \<Rightarrow> bool"
  where "change_respecting (cms, mem) (cms', mem') X =
      ((cms, mem) \<leadsto> (cms', mem') \<and>
       (\<forall> \<sigma>. dom \<sigma> = vars_and_\<C> X \<longrightarrow> (cms, mem [\<mapsto> \<sigma>]) \<leadsto> (cms', mem' [\<mapsto> \<sigma>])))"

lemma subst_overrides: "dom \<sigma> = dom \<tau> \<Longrightarrow> mem [\<mapsto> \<tau>] [\<mapsto> \<sigma>] = mem [\<mapsto> \<sigma>]"
  unfolding subst_def
  by (metis domIff option.exhaust option.simps(4) option.simps(5))

definition to_partial :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where "to_partial f = (\<lambda> x. Some (f x))"

lemma dom_restrict_total: "dom (to_partial f |` X) = X"
  unfolding to_partial_def
  by (metis Int_UNIV_left dom_const dom_restrict)

lemma change_respecting_doesnt_modify':
  assumes eval: "(cms, mem) \<leadsto> (cms', mem')"
  assumes cr: "\<forall> f. dom f = Y \<longrightarrow> (cms, mem [\<mapsto> f]) \<leadsto> (cms', mem' [\<mapsto> f])"
  assumes x_in_dom: "x \<in> Y"
  shows "mem x = mem' x"
proof -
  let ?f' = "to_partial mem |` Y"
  have domf': "dom ?f' = Y"
    by (metis dom_restrict_total)

  from this cr have eval': "(cms, mem [\<mapsto> ?f']) \<leadsto> (cms', mem' [\<mapsto> ?f'])"
    by (metis)

  have mem_eq: "mem [\<mapsto> ?f'] = mem"
  proof
    fix x
    show "mem [\<mapsto> ?f'] x = mem x"
      unfolding subst_def
      apply (cases "x \<in> Y")
       apply (metis option.simps(5) restrict_in to_partial_def)
      by (metis domf' subst_def subst_not_in_dom)
  qed

  then have mem'_eq: "mem' [\<mapsto> ?f'] = mem'"
    using eval eval' deterministic
    by (metis Pair_inject)

  moreover
  have x_in_dom': "x \<in> dom ?f'"
    by (metis x_in_dom dom_restrict_total)
  hence "?f' x = Some (mem x)"
    by (metis restrict_in to_partial_def x_in_dom)
  hence "mem' [\<mapsto> ?f'] x = mem x"
    using subst_def x_in_dom'
    by (metis option.simps(5))
  thus "mem x = mem' x"
    by (metis mem'_eq)
qed

lemma change_respecting_subset':
  assumes step: "(cms, mem) \<leadsto> (cms', mem')"
  assumes noread: "(\<forall> \<sigma>. dom \<sigma> = X \<longrightarrow> (cms, mem [\<mapsto> \<sigma>]) \<leadsto> (cms', mem' [\<mapsto> \<sigma>]))"
  assumes dom_subset: "dom \<sigma> \<subseteq> X"
  shows "(cms, mem [\<mapsto> \<sigma>]) \<leadsto> (cms', mem' [\<mapsto> \<sigma>])"
proof -
  define \<sigma>\<^sub>X where "\<sigma>\<^sub>X x = (if x \<in> X then if x \<in> dom \<sigma> then \<sigma> x else Some (mem x) else None)" for x
  have "dom \<sigma>\<^sub>X = X" using dom_subset by(auto simp: \<sigma>\<^sub>X_def)

  have "mem [\<mapsto> \<sigma>] = mem [\<mapsto> \<sigma>\<^sub>X]"
    apply(rule ext)
    using dom_subset apply(auto simp: subst_def \<sigma>\<^sub>X_def split: option.splits)
    done

  moreover have "mem' [\<mapsto> \<sigma>] = mem' [\<mapsto> \<sigma>\<^sub>X]"
    apply(rule ext)
    using dom_subset apply(auto simp: subst_def \<sigma>\<^sub>X_def split: option.splits simp: change_respecting_doesnt_modify'[OF step noread])
    done

  moreover from noread \<open>dom \<sigma>\<^sub>X = X\<close> have "(cms, mem [\<mapsto> \<sigma>\<^sub>X]) \<leadsto> (cms', mem' [\<mapsto> \<sigma>\<^sub>X])" by metis
  ultimately show ?thesis by simp
qed
 
lemma change_respecting_subst:
  "change_respecting (cms, mem) (cms', mem') X \<Longrightarrow>
       (\<forall> \<sigma>. dom \<sigma> = X \<longrightarrow> (cms, mem [\<mapsto> \<sigma>]) \<leadsto> (cms', mem' [\<mapsto> \<sigma>]))"
  unfolding change_respecting.simps vars_and_\<C>_def
  using change_respecting_subset' by blast
 
lemma change_respecting_intro [iff]:
  "\<lbrakk> \<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>;
     \<And> f. dom f = vars_and_\<C> X \<Longrightarrow>
           (\<langle> c, mds, mem [\<mapsto> f] \<rangle> \<leadsto> \<langle> c', mds', mem' [\<mapsto> f] \<rangle>) \<rbrakk>
  \<Longrightarrow> change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X"
  unfolding change_respecting.simps
  by blast

lemma vars_\<C>_mono:
  "X \<subseteq> Y \<Longrightarrow> vars_\<C> X \<subseteq> vars_\<C> Y"
  by(auto simp: vars_\<C>_def)

lemma vars_\<C>_Un:
  "vars_\<C> (X \<union> Y) = (vars_\<C> X \<union> vars_\<C> Y)"
  by(simp add: vars_\<C>_def)

lemma vars_\<C>_insert:
  "vars_\<C> (insert x Y) = (vars_\<C> {x}) \<union> (vars_\<C> Y)"
  apply(subst insert_is_Un)
  apply(rule vars_\<C>_Un)
  done

lemma vars_\<C>_empty[simp]:
  "vars_\<C> {} = {}"
  by(simp add: vars_\<C>_def)

lemma \<C>_vars_of_\<C>_vars_empty:
  "x \<in> \<C>_vars y \<Longrightarrow> \<C>_vars x = {}"
  apply(drule subsetD[OF \<C>_vars_subset_\<C>])
  apply(erule \<C>_vars_\<C>)
  done

lemma vars_and_\<C>_mono:
  "X \<subseteq> X' \<Longrightarrow> vars_and_\<C> X \<subseteq> vars_and_\<C> X'"
  apply(unfold vars_and_\<C>_def)
  apply(metis Un_mono vars_\<C>_mono)
  done

lemma \<C>_vars_finite[simp]:
  "finite (\<C>_vars x)"
  apply(rule finite_subset[OF _ finite_memory])
  by blast

lemma finite_dom:
  "finite (dom (\<sigma>::'Var \<Rightarrow> 'Val option))"
  by(blast intro: finite_subset[OF _ finite_memory])

lemma doesnt_read_or_modify_subst: 
  assumes noread: "doesnt_read_or_modify c x"
  assumes step: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  assumes subset: "X \<subseteq> {x} \<union> \<C>_vars x"
  shows "\<And> \<sigma>. dom \<sigma> = X \<Longrightarrow> \<langle>c, mds, mem[\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem'[\<mapsto> \<sigma>]\<rangle>"  
proof -
  have "finite X"
    using subset apply(rule finite_subset)
    by simp
  show "\<And> \<sigma>. dom \<sigma> = X \<Longrightarrow> \<langle>c, mds, mem[\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem'[\<mapsto> \<sigma>]\<rangle>"
    using \<open>finite X\<close> subset 
  proof(induct "X" rule: finite_subset_induct[where A="{x} \<union> \<C>_vars x"])
    case empty
    thus "\<langle>c, mds, subst \<sigma> mem\<rangle> \<leadsto> \<langle>c', mds', subst \<sigma> mem'\<rangle>"
      using step by(simp add: subst_def)
  next
    case (insert a X)
    show "\<langle>c, mds, subst \<sigma> mem\<rangle> \<leadsto> \<langle>c', mds', subst \<sigma> mem'\<rangle>"
    proof -
      let ?\<sigma>\<^sub>X = "(\<sigma> |` X)"
      have IH\<^sub>X: "\<langle>c, mds, subst ?\<sigma>\<^sub>X mem\<rangle> \<leadsto> \<langle>c', mds', subst ?\<sigma>\<^sub>X mem'\<rangle>"
        apply(rule insert(4))
        using insert by (metis dom_restrict inf.absorb2 subset_insertI)
      from insert obtain v where \<sigma>a: "\<sigma> a = Some v" by auto
      have r: "\<And>mem. (subst ?\<sigma>\<^sub>X mem)(a := v) = subst \<sigma> mem"
        apply(rule ext, rename_tac y)
        apply(simp, safe)
         apply(simp add: subst_def \<sigma>a)
        using \<open>a \<notin> X\<close> insert apply(auto simp: subst_def split: option.splits simp: restrict_map_def)
        done
      have "\<langle>c, mds, (subst ?\<sigma>\<^sub>X mem)(a := v)\<rangle> \<leadsto> \<langle>c', mds', (subst ?\<sigma>\<^sub>X mem')(a := v)\<rangle>"
        using noread \<open>a \<in> {x} \<union> \<C>_vars x\<close> IH\<^sub>X
        unfolding doesnt_read_or_modify_def doesnt_read_or_modify_vars_def by metis
      thus ?thesis by(simp add: r)
    qed
  qed
qed

lemma subst_restrict_twice:
  "dom \<sigma> = A \<union> B \<Longrightarrow>
   mem [\<mapsto> (\<sigma> |` A)] [\<mapsto> (\<sigma> |` B)] = mem [\<mapsto> \<sigma>]"
  by(fastforce simp: subst_def split: option.splits intro!: ext simp: restrict_map_def)

(* Toby: this proof is now far simpler because change_respecting is *)
lemma noread_exists_change_respecting:
  assumes fin: "finite (X :: 'Var set)"
  assumes eval: "\<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>"
  assumes noread: "\<forall> x \<in> X. doesnt_read_or_modify c x"
  shows "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X"
proof -
  let ?lc = "\<langle>c, mds, mem\<rangle>" and ?lc' = "\<langle>c', mds', mem'\<rangle>"
  from fin eval noread show "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X"
  proof (induct "X" arbitrary: mem mem' rule: finite_induct)
    case empty
    have "mem [\<mapsto> Map.empty] = mem" "mem' [\<mapsto> Map.empty] = mem'"
      unfolding subst_def
      by auto
    hence "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> {}"
      using empty
      unfolding change_respecting.simps subst_def vars_\<C>_def vars_and_\<C>_def
      by auto
    thus ?case by blast
  next
    case (insert x X)
    then have IH: "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X"
      by (metis (poly_guards_query) insertCI insert_disjoint(1))
    show "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> (insert x X)"
    proof
      show "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>" using insert by auto
    next
      fix \<sigma> :: "'Var \<rightharpoonup> 'Val"
      let ?\<sigma>\<^sub>X = "\<sigma> |` vars_and_\<C> X"
      let ?\<sigma>\<^sub>x = "\<sigma> |` ({x} \<union> \<C>_vars x)"
      assume dom\<sigma>: "dom \<sigma> = vars_and_\<C> (insert x X)"
      hence "dom ?\<sigma>\<^sub>X = vars_and_\<C> X"
        by (metis dom_restrict inf_absorb2 subset_insertI vars_and_\<C>_mono)
      from dom\<sigma> have dom\<sigma>\<^sub>x: "dom ?\<sigma>\<^sub>x = {x} \<union> \<C>_vars x"
        by(simp add: dom\<sigma> vars_and_\<C>_def vars_\<C>_def, blast)
      have "dom \<sigma> = vars_and_\<C> X \<union> ({x} \<union> \<C>_vars x)"
        by(simp add: dom\<sigma> vars_and_\<C>_def vars_\<C>_def, blast)
      hence subst\<sigma>: "\<And> mem. mem [\<mapsto> ?\<sigma>\<^sub>X] [\<mapsto> ?\<sigma>\<^sub>x] = mem [\<mapsto> \<sigma>]"
        by(rule subst_restrict_twice)
      from insert have "doesnt_read_or_modify c x" by auto
      moreover from IH have eval\<^sub>X: "\<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> ?\<sigma>\<^sub>X]\<rangle>"
        using \<open>dom ?\<sigma>\<^sub>X = vars_and_\<C> X\<close>
        unfolding change_respecting.simps
        by auto
      ultimately have "\<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] [\<mapsto> ?\<sigma>\<^sub>x]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> ?\<sigma>\<^sub>X] [\<mapsto> ?\<sigma>\<^sub>x]\<rangle>"
        using subset_refl dom\<sigma>\<^sub>x doesnt_read_or_modify_subst by metis
      thus "\<langle>c, mds, mem [\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> \<sigma>]\<rangle>"
        using subst\<sigma> by metis 
    qed
  qed
qed


lemma update_nth_eq:
  "\<lbrakk> xs = ys; n < length xs \<rbrakk> \<Longrightarrow> xs = ys [n := xs ! n]"
  by (metis list_update_id)

text \<open>This property is obvious,
  so an unreadable apply-style proof is acceptable here:\<close>
lemma mm_equiv_step:
  assumes bisim: "(cms\<^sub>1, mem\<^sub>1) \<approx> (cms\<^sub>2, mem\<^sub>2)"
  assumes modes_eq: "snd cms\<^sub>1 = snd cms\<^sub>2"
  assumes step: "(cms\<^sub>1, mem\<^sub>1) \<leadsto> (cms\<^sub>1', mem\<^sub>1')"
  shows "\<exists> c\<^sub>2' mem\<^sub>2'. (cms\<^sub>2, mem\<^sub>2) \<leadsto> \<langle> c\<^sub>2', snd cms\<^sub>1', mem\<^sub>2' \<rangle> \<and>
  (cms\<^sub>1', mem\<^sub>1') \<approx> \<langle> c\<^sub>2', snd cms\<^sub>1', mem\<^sub>2' \<rangle>"
  using assms mm_equiv_strong_low_bisim
  unfolding strong_low_bisim_mm_def
  apply auto
  apply (erule_tac x = "fst cms\<^sub>1" in allE)
  apply (erule_tac x = "snd cms\<^sub>1" in allE)
  by (metis surjective_pairing)

lemma change_respecting_doesnt_modify:
  assumes cr: "change_respecting (cms, mem) (cms', mem') X"
  assumes eval: "(cms, mem) \<leadsto> (cms', mem')"
  assumes x_in_dom: "x \<in> X \<union> vars_\<C> X"
  shows "mem x = mem' x"
  using change_respecting_doesnt_modify'[where Y="X \<union> vars_\<C> X", OF eval] cr     
        change_respecting.simps vars_and_\<C>_def x_in_dom 
  by metis

lemma change_respecting_doesnt_modify_dma:
  assumes cr: "change_respecting (cms, mem) (cms', mem') X"
  assumes eval: "(cms, mem) \<leadsto> (cms', mem')"
  assumes x_in_dom: "x \<in> X"
  shows "dma mem x = dma mem' x"
proof - 
  have "\<And>y. y \<in> \<C>_vars x \<Longrightarrow> mem y = mem' y"
    proof -
    fix y
    assume "y \<in> \<C>_vars x"
    hence "y \<in> vars_\<C> X"
      using x_in_dom by(auto simp: vars_\<C>_def)
    thus "mem y = mem' y"
      using cr eval change_respecting_doesnt_modify by blast
    qed
  thus ?thesis by(metis dma_\<C>_vars)
qed

definition restrict_total :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<rightharpoonup> 'b" (*infix "|'" 60*)
  where "restrict_total f A = to_partial f |` A"

lemma differing_empty_eq:
  "\<lbrakk> differing_vars mem mem' = {} \<rbrakk> \<Longrightarrow> mem = mem'"
  unfolding differing_vars_def
  by auto

lemma adaptation_finite:
  "finite (dom (A::('Var,'Val) adaptation))"
  apply(rule finite_subset[OF _ finite_memory])
  by blast

definition 
  globally_consistent  :: "('Var, 'Val) adaptation \<Rightarrow> 'Var Mds \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> ('Var,'Val) Mem \<Rightarrow> bool"
where "globally_consistent A mds mem\<^sub>1 mem\<^sub>2 \<equiv> 
  (\<forall>x.  case A x of Some (v,v') \<Rightarrow> (mem\<^sub>1 x \<noteq> v \<or> mem\<^sub>2 x \<noteq> v') \<longrightarrow> \<not> var_asm_not_written mds x | _ \<Rightarrow> True) \<and>
        (\<forall>x. dma mem\<^sub>1 [\<parallel>\<^sub>1 A] x \<noteq> dma mem\<^sub>1 x \<longrightarrow> \<not> var_asm_not_written mds x) \<and>
          (\<forall>x. dma (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = Low \<and> (x \<notin> mds AsmNoReadOrWrite \<or> x \<in> \<C>) \<longrightarrow> (mem\<^sub>1 [\<parallel>\<^sub>1 A]) x = (mem\<^sub>2 [\<parallel>\<^sub>2 A]) x)"

lemma globally_consistent_adapt_bisim:
  assumes bisim: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  assumes globally_consistent: "globally_consistent A mds mem\<^sub>1 mem\<^sub>2"
  shows "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle>"
  apply(rule mm_equiv_glob_consistent[simplified closed_glob_consistent_def, rule_format])
   apply(rule bisim)
  apply(fold globally_consistent_def)
  by(rule globally_consistent)

lemma mm_equiv_\<C>_eq: 
  "(a,b) \<approx> (a',b') \<Longrightarrow> snd a = snd a' \<Longrightarrow>
    \<forall>x\<in>\<C>. b x = b' x"
  apply(case_tac a, case_tac a')
  using mm_equiv_strong_low_bisim[simplified strong_low_bisim_mm_def, rule_format]
  by(auto simp: low_mds_eq_def \<C>_Low)

lemma apply_adaptation_not_in_dom: 
  "x \<notin> dom A \<Longrightarrow> apply_adaptation b blah A x = blah x"
  apply(simp add: apply_adaptation_def domIff split: option.splits)
  done

(* This is the central lemma. Unfortunately, I didn't find
   a nice partitioning into several easier lemmas: *)
lemma makes_compatible_invariant:
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)"
                      "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes eval: "(cms\<^sub>1, mem\<^sub>1) \<leadsto>\<^bsub>k\<^esub> (cms\<^sub>1', mem\<^sub>1')"
  obtains cms\<^sub>2' mem\<^sub>2' mems' where
      "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
       (cms\<^sub>2, mem\<^sub>2) \<leadsto>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
       makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
proof -
  let ?X = "\<lambda> i. differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  from sound_modes compat modes_eq have
    a: "\<forall> i < length cms\<^sub>1. \<forall> x \<in> (?X i). doesnt_read_or_modify (fst (cms\<^sub>1 ! i)) x \<and>
                                          doesnt_read_or_modify (fst (cms\<^sub>2 ! i)) x"
    by (metis compatible_different_no_read)
  from eval have
    b: "k < length cms\<^sub>1 \<and> (cms\<^sub>1 ! k, mem\<^sub>1) \<leadsto> (cms\<^sub>1' ! k, mem\<^sub>1') \<and>
        cms\<^sub>1' = cms\<^sub>1 [k := cms\<^sub>1' ! k]"
    by (metis meval_elim nth_list_update_eq)

  from modes_eq have equal_size: "length cms\<^sub>1 = length cms\<^sub>2"
    by (metis length_map)

  let ?mds\<^sub>k = "snd (cms\<^sub>1 ! k)" and
      ?mds\<^sub>k' = "snd (cms\<^sub>1' ! k)" and
      ?mems\<^sub>1k = "fst (mems ! k)" and
      ?mems\<^sub>2k = "snd (mems ! k)" and
      ?n = "length cms\<^sub>1"

  have "finite (?X k)"
    by (metis differing_lists_finite)

  (* Obtaining cms' and mem\<^sub>2' is not in a proof block, since we
     need some of the following statements later: *)
  then have
    c: "change_respecting (cms\<^sub>1 ! k, mem\<^sub>1) (cms\<^sub>1' ! k, mem\<^sub>1') (?X k)"
    using noread_exists_change_respecting b a
    by (metis surjective_pairing)

  from compat have "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> ?mems\<^sub>1k [\<mapsto> \<sigma>] = mem\<^sub>1 [\<mapsto> \<sigma>]"
    using differing_vars_subst differing_vars_lists_def
    by (metis Un_upper1 Un_subset_iff)

  hence
    eval\<^sub>\<sigma>: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> (cms\<^sub>1 ! k, ?mems\<^sub>1k [\<mapsto> \<sigma>]) \<leadsto> (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> \<sigma>])"
      by(metis change_respecting_subst[rule_format, where X="?X k"] c)

  moreover
  with b and compat have
    bisim\<^sub>\<sigma>: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> (cms\<^sub>1 ! k, ?mems\<^sub>1k [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>])"
    by auto

  moreover have "snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)"
    by (metis b equal_size modes_eq nth_map)
    
  ultimately have d: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> \<exists> c\<^sub>f' mem\<^sub>f'.
    (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>f', ?mds\<^sub>k', mem\<^sub>f' \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> \<sigma>]) \<approx> \<langle> c\<^sub>f', ?mds\<^sub>k', mem\<^sub>f' \<rangle>"
    by (metis mm_equiv_step)

  obtain h :: "'Var \<rightharpoonup> 'Val" where domh: "dom h = ?X k"
    by (metis dom_restrict_total)

  then obtain c\<^sub>h mem\<^sub>h where h_prop:
    "(cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> h]) \<approx> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle>"
    using d
    by metis

  then have
    "change_respecting (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h]) \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle> (?X k)"
    using a b noread_exists_change_respecting
    by (metis differing_lists_finite surjective_pairing)

  \<comment> \<open>The following statements are universally quantified
      since they are reused later:\<close>
  with h_prop have
    "\<forall> \<sigma>. dom \<sigma> = ?X k \<longrightarrow>
      (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h] [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> \<sigma>] \<rangle>"
    by (metis change_respecting_subst)

  with domh have f:
    "\<forall> \<sigma>. dom \<sigma> = ?X k \<longrightarrow>
      (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> \<sigma>] \<rangle>"
    by (auto simp: subst_overrides)

  from d and f have g: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow>
    (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> \<sigma>] \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> \<sigma>]) \<approx> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> \<sigma>] \<rangle>"
    using h_prop
    by (metis deterministic)
  let ?\<sigma>_mem\<^sub>2 = "to_partial mem\<^sub>2 |` ?X k"
  define mem\<^sub>2' where "mem\<^sub>2' = mem\<^sub>h [\<mapsto> ?\<sigma>_mem\<^sub>2]"
  define c\<^sub>2' where "c\<^sub>2' = c\<^sub>h"

  have dom\<sigma>_mem\<^sub>2: "dom ?\<sigma>_mem\<^sub>2 = ?X k"
    by (metis dom_restrict_total)

  have "mem\<^sub>2 = ?mems\<^sub>2k [\<mapsto> ?\<sigma>_mem\<^sub>2]"
  proof (rule ext)
    fix x
    show "mem\<^sub>2 x = ?mems\<^sub>2k [\<mapsto> ?\<sigma>_mem\<^sub>2] x"
      using dom\<sigma>_mem\<^sub>2
      unfolding to_partial_def subst_def
      apply (cases "x \<in> ?X k")
      apply auto
      by (metis differing_vars_neg)
  qed

  with f dom\<sigma>_mem\<^sub>2 have i: "(cms\<^sub>2 ! k, mem\<^sub>2) \<leadsto> \<langle> c\<^sub>2', ?mds\<^sub>k', mem\<^sub>2' \<rangle>"
    unfolding mem\<^sub>2'_def c\<^sub>2'_def
    by metis

  define cms\<^sub>2' where "cms\<^sub>2' = cms\<^sub>2 [k := (c\<^sub>2', ?mds\<^sub>k')]"

  with i b equal_size have "(cms\<^sub>2, mem\<^sub>2) \<leadsto>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2')"
    by (metis meval_intro)

  moreover
  from equal_size have new_length: "length cms\<^sub>1' = length cms\<^sub>2'"
    unfolding cms\<^sub>2'_def
    by (metis eval length_list_update meval_elim)

  with modes_eq have "map snd cms\<^sub>1' = map snd cms\<^sub>2'"
    unfolding cms\<^sub>2'_def
    by (metis b map_update snd_conv)

  moreover

  \<comment> \<open>This is the complicated part of the proof.\<close>
  obtain mems' where "makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
  proof
    \<comment> \<open>This is used in two of the following cases, so we prove it beforehand:\<close>
    have x_unchanged: "\<And> x. \<lbrakk> x \<in> ?X k \<rbrakk> \<Longrightarrow>
      mem\<^sub>1 x = mem\<^sub>1' x \<and> mem\<^sub>2 x = mem\<^sub>2' x \<and> dma mem\<^sub>1 x = dma mem\<^sub>1' x"
    proof(intro conjI)
      fix x
      assume "x \<in> ?X k"
      thus "mem\<^sub>1 x = mem\<^sub>1' x"
        using a b c change_respecting_doesnt_modify domh 
        by (metis (erased, hide_lams) Un_upper1 contra_subsetD)
    next
      fix x
      assume "x \<in> ?X k"

      hence eq_mem\<^sub>2: "?\<sigma>_mem\<^sub>2 x = Some (mem\<^sub>2 x)"
        by (metis restrict_in to_partial_def)
      hence "?mems\<^sub>2k [\<mapsto> h] [\<mapsto> ?\<sigma>_mem\<^sub>2] x = mem\<^sub>2 x"
        by (auto simp: subst_def)

      moreover have "mem\<^sub>h [\<mapsto> ?\<sigma>_mem\<^sub>2] x = mem\<^sub>2 x"
        by (auto simp: subst_def \<open>x \<in> ?X k\<close> eq_mem\<^sub>2)

      ultimately have "?mems\<^sub>2k [\<mapsto> h] [\<mapsto> ?\<sigma>_mem\<^sub>2] x = mem\<^sub>h [\<mapsto> ?\<sigma>_mem\<^sub>2] x"
        by auto
      thus "mem\<^sub>2 x = mem\<^sub>2' x"
        by (metis \<open>mem\<^sub>2 = ?mems\<^sub>2k [\<mapsto> ?\<sigma>_mem\<^sub>2]\<close> dom\<sigma>_mem\<^sub>2 domh mem\<^sub>2'_def subst_overrides)
    next
      fix x
      assume "x \<in> ?X k"
      thus "dma mem\<^sub>1 x = dma mem\<^sub>1' x"
        using a b c change_respecting_doesnt_modify_dma domh 
        by (metis (erased, hide_lams))      
    qed

    define mems'_k where "mems'_k x =
      (if x \<notin> ?X k
       then (mem\<^sub>1' x, mem\<^sub>2' x)
       else (?mems\<^sub>1k x, ?mems\<^sub>2k x))" for x

    (* FIXME: see if we can reduce the number of cases *)
    define mems'_i where "mems'_i i x =
      (if ((mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x) \<and>
          (mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High))
         then (mem\<^sub>1' x, mem\<^sub>2' x)
         else if ((mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x) \<and>
                  (mem\<^sub>1' x \<noteq> mem\<^sub>2' x \<and> dma mem\<^sub>1' x = Low))
              then (some_val, some_val)
              else if dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low then (mem\<^sub>1 x, mem\<^sub>1 x)
              else if dma mem\<^sub>1' x = dma mem\<^sub>1 x then (fst (mems ! i) x, snd (mems ! i) x)
              else (mem\<^sub>1' x, mem\<^sub>2' x))" for i x

    define mems'
      where "mems' =
        map (\<lambda> i.
            if i = k
            then (fst \<circ> mems'_k, snd \<circ> mems'_k)
            else (fst \<circ> mems'_i i, snd \<circ> mems'_i i))
      [0..< length cms\<^sub>1]"
    from b have mems'_k_simp: "mems' ! k = (fst \<circ> mems'_k, snd \<circ> mems'_k)"
      unfolding mems'_def
      by auto

    have mems'_simp2: "\<And>i. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1 \<rbrakk> \<Longrightarrow>
      mems' ! i = (fst \<circ> mems'_i i, snd \<circ> mems'_i i)"
      unfolding mems'_def
      by auto
    (* Some auxiliary statements to allow reasoning about these definitions as if they were given
       by cases instead of nested if clauses. *)
    have mems'_k_1 [simp]: "\<And> x. \<lbrakk> x \<notin> ?X k \<rbrakk> \<Longrightarrow>
      fst (mems' ! k) x = mem\<^sub>1' x \<and> snd (mems' ! k) x = mem\<^sub>2' x"
      unfolding mems'_k_simp mems'_k_def
      by auto
    have mems'_k_2 [simp]: "\<And> x. \<lbrakk> x \<in> ?X k \<rbrakk> \<Longrightarrow>
      fst (mems' ! k) x = fst (mems ! k) x \<and> snd (mems' ! k) x = snd (mems ! k) x"
      unfolding mems'_k_simp mems'_k_def
      by auto

    
    have mems'_k_cases:
      "\<And> P x.
        \<lbrakk>
         \<lbrakk> x \<notin> ?X k;
           fst (mems' ! k) x = mem\<^sub>1' x;
           snd (mems' ! k) x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow> P x;
         \<lbrakk> x \<in> ?X k; 
           fst (mems' ! k) x = fst (mems ! k) x;
           snd (mems' ! k) x = snd (mems ! k) x \<rbrakk> \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P x"
      apply(case_tac "x \<notin> ?X k")
       apply simp
      apply simp
      done

    have mems'_i_simp:
      "\<And> i. \<lbrakk> i < length cms\<^sub>1; i \<noteq> k \<rbrakk> \<Longrightarrow> mems' ! i = (fst \<circ> mems'_i i, snd \<circ> mems'_i i)"
      unfolding mems'_def
      by auto

    have mems'_i_1 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
                 mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High \<rbrakk> \<Longrightarrow>
               fst (mems' ! i) x = mem\<^sub>1' x \<and> snd (mems' ! i) x = mem\<^sub>2' x"
      unfolding mems'_i_def mems'_i_simp
      by auto

    have mems'_i_2 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
                 mem\<^sub>1' x \<noteq> mem\<^sub>2' x; dma mem\<^sub>1' x = Low \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = some_val \<and> snd (mems' ! i) x = some_val"
      unfolding mems'_i_def mems'_i_simp
      by auto
    have mems'_i_3 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x;
                 dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = mem\<^sub>1 x \<and> snd (mems' ! i) x = mem\<^sub>1 x"
      unfolding mems'_i_def mems'_i_simp
      by auto

    have mems'_i_4 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x;
                 dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High;
                 dma mem\<^sub>1' x = dma mem\<^sub>1 x \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = fst (mems ! i) x \<and> snd (mems' ! i) x = snd (mems ! i) x"
      unfolding mems'_i_def mems'_i_simp
      by auto

    have mems'_i_5 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x;
                 dma mem\<^sub>1 x = Low \<and> dma mem\<^sub>1' x = High;
                 dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = mem\<^sub>1' x \<and> snd (mems' ! i) x = mem\<^sub>2' x"
      unfolding mems'_i_def mems'_i_simp
      by auto

    (* This may look complicated, but is actually a rather
       mechanical definition, as it merely spells out the cases
       of the definition: *)
    have mems'_i_cases:
      "\<And> P i x.
         \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
           \<lbrakk> mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
             mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High;
             fst (mems' ! i) x = mem\<^sub>1' x; snd (mems' ! i) x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
        mem\<^sub>1' x \<noteq>  mem\<^sub>2' x; dma mem\<^sub>1' x = Low;
        fst (mems' ! i) x = some_val; snd (mems' ! i) x = some_val \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x; dma mem\<^sub>1 x = High; 
        dma mem\<^sub>1' x = Low;
        fst (mems' ! i) x = mem\<^sub>1 x; snd (mems' ! i) x = mem\<^sub>1 x \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x; dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High;
        dma mem\<^sub>1' x = dma mem\<^sub>1 x;
        fst (mems' ! i) x = fst (mems ! i) x; snd (mems' ! i) x = snd (mems ! i) x \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x; dma mem\<^sub>1 x = Low; dma mem\<^sub>1' x = High;
        fst (mems' ! i) x = mem\<^sub>1' x; snd (mems' ! i) x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow> P x       \<rbrakk>
      \<Longrightarrow> P x"
      using mems'_i_1 mems'_i_2 mems'_i_3 mems'_i_4 mems'_i_5
      by (metis (full_types) Sec.exhaust)

    let ?X' = "\<lambda> i. differing_vars_lists mem\<^sub>1' mem\<^sub>2' mems' i"

    have len_unchanged: "length cms\<^sub>1' = length cms\<^sub>1"
      by (metis cms\<^sub>2'_def equal_size length_list_update new_length)

    have mm_equiv': "(cms\<^sub>1' ! k, subst (?\<sigma>_mem\<^sub>2) mem\<^sub>1') \<approx> \<langle>c\<^sub>h, snd (cms\<^sub>1' ! k), mem\<^sub>2'\<rangle>"
      apply(simp add: mem\<^sub>2'_def)
      apply(rule g[THEN conjunct2])
      apply(rule dom_restrict_total)
      done

   hence \<C>_subst_eq: "\<forall>x\<in>\<C>. (subst (?\<sigma>_mem\<^sub>2) mem\<^sub>1') x = mem\<^sub>2' x"
     apply(rule mm_equiv_\<C>_eq)
     by simp

   have low_mds_eq': "(subst (?\<sigma>_mem\<^sub>2) mem\<^sub>1') =\<^bsub>snd (cms\<^sub>1' ! k)\<^esub>\<^sup>l mem\<^sub>2'"
     apply(rule mm_equiv_low_eq[where c\<^sub>1="fst (cms\<^sub>1' ! k)"])
     apply(force intro: mm_equiv')
     done

   have \<C>_subst_eq_idemp: "\<And>x. x \<in> \<C> \<Longrightarrow> (subst (?\<sigma>_mem\<^sub>2) mem\<^sub>1') x = mem\<^sub>1' x"
     apply(rule subst_not_in_dom)
     apply(rule notI)
     apply(simp add: dom_restrict_total)
     using compat b by force

    from \<C>_subst_eq \<C>_subst_eq_idemp
    have \<C>_eq: "\<And>x. x \<in> \<C> \<Longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x"
     by simp

    have not_control: "\<And>x i. i < length cms\<^sub>1' \<Longrightarrow> x \<in> ?X' i \<Longrightarrow> x \<notin> \<C>"
    proof(rule ccontr, clarsimp)
      fix x i
      let ?mems\<^sub>1i = "fst (mems ! i)"
      let ?mems\<^sub>2i = "snd (mems ! i)"
      let ?mems\<^sub>1'i = "fst (mems' ! i)"
      let ?mems\<^sub>2'i = "snd (mems' ! i)"
      assume "i < length cms\<^sub>1'"
      have "i < length cms\<^sub>1" by (metis len_unchanged \<open>i < length cms\<^sub>1'\<close>)
      assume "x \<in> ?X' i"
      assume "x \<in> \<C>"
      have "x \<notin> ?X i"
        using compat \<open>i < length cms\<^sub>1'\<close> len_unchanged new_length
        by (metis \<open>x \<in> \<C>\<close> compat_different)
      from \<open>x \<in> \<C>\<close> have  "mem\<^sub>1' x = mem\<^sub>2' x" by(rule \<C>_eq)
      from \<open>x \<in> \<C>\<close> have "dma mem\<^sub>1' x = Low" by(simp add: \<C>_Low)
      show "False"
      proof(cases "i = k")
        assume eq[simp]: "i = k"
        show ?thesis
        using \<open>x \<notin> ?X i\<close> \<open>x \<in> ?X' i\<close>
        by(force simp: differing_vars_lists_def differing_vars_def)
      next
        assume neq: "i \<noteq> k"
        thus ?thesis
        using \<open>x \<in> ?X' i\<close> \<open>x \<notin> ?X i\<close> \<open>x \<in> \<C>\<close> \<C>_Low \<open>mem\<^sub>1' x = mem\<^sub>2' x\<close>
        by(force elim: mems'_i_cases[of "i" "x" "\<lambda>x. False", OF _ \<open>i < length cms\<^sub>1\<close>]
                 simp: differing_vars_lists_def differing_vars_def)
      qed
    qed

    show "makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
    proof
      have "length cms\<^sub>1' = length cms\<^sub>1"
        by (metis cms\<^sub>2'_def equal_size length_list_update new_length)
      then show "length cms\<^sub>1' = length cms\<^sub>2' \<and> length cms\<^sub>1' = length mems'"
        using compat new_length
        unfolding mems'_def
        by auto
    next
      fix i
      fix \<sigma> :: "'Var \<rightharpoonup> 'Val"
      let ?mems\<^sub>1'i = "fst (mems' ! i)"
      let ?mems\<^sub>2'i = "snd (mems' ! i)"
      assume i_le: "i < length cms\<^sub>1'"
      assume dom\<sigma>: "dom \<sigma> = ?X' i"
      show "(cms\<^sub>1' ! i, (fst (mems' ! i)) [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2' ! i, (snd (mems' ! i)) [\<mapsto> \<sigma>])"
      proof (cases "i = k")
        assume [simp]: "i = k"
        \<comment> \<open>We define another  function from this and reuse the universally quantified statements
          from the first part of the proof.\<close>
        define \<sigma>' where "\<sigma>' x =
           (if x \<in> ?X k
            then if x \<in> ?X' k
                 then \<sigma> x
                 else Some (mem\<^sub>1' x)
            else None)" for x
        have dom\<sigma>': "dom \<sigma>' = ?X k"
          using \<sigma>'_def [abs_def]
          apply (clarsimp, safe)
          by( metis domI domIff, metis \<open>i = k\<close> domD dom\<sigma> )
        have diff_vars_impl [simp]: "\<And>x. x \<in> ?X' k \<Longrightarrow> x \<in> ?X k"
        proof (rule ccontr)
          fix x
          assume "x \<notin> ?X k"
          hence "mem\<^sub>1 x = ?mems\<^sub>1k x \<and> mem\<^sub>2 x = ?mems\<^sub>2k x"
            by (metis differing_vars_neg)
          from \<open>x \<notin> ?X k\<close> have "?mems\<^sub>1'i x = mem\<^sub>1' x \<and> ?mems\<^sub>2'i x = mem\<^sub>2' x"
            by auto
          moreover
          assume "x \<in> ?X' k"
          hence "mem\<^sub>1' x \<noteq> ?mems\<^sub>1'i x \<or> mem\<^sub>2' x \<noteq> ?mems\<^sub>2'i x"
            by (metis \<open>i = k\<close> differing_vars_elim)
          ultimately show False
            by auto
        qed

        (* We now show that we can reuse the earlier statements
           by showing the following equality: *)
        have "?mems\<^sub>1'i [\<mapsto> \<sigma>] = mem\<^sub>1' [\<mapsto> \<sigma>']"
        proof (rule ext)
          fix x

          show "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = mem\<^sub>1' [\<mapsto> \<sigma>'] x"
          proof (cases "x \<in> ?X' k")
            assume x_in_X'k: "x \<in> ?X' k"

            then obtain v where "\<sigma> x = Some v"
              by (metis dom\<sigma> domD \<open>i = k\<close>)
            hence "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = v"
              using \<open>x \<in> ?X' k\<close> dom\<sigma>
              by (auto simp: subst_def)
            moreover
            from dom\<sigma>' and \<open>x \<in> ?X' k\<close> have "x \<in> dom \<sigma>'" by simp
             
            hence "mem\<^sub>1' [\<mapsto> \<sigma>'] x = v"
              using dom\<sigma>' 
              unfolding subst_def
              by (metis \<sigma>'_def \<open>\<sigma> x = Some v\<close> diff_vars_impl option.simps(5) x_in_X'k)

            ultimately show "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = mem\<^sub>1' [\<mapsto> \<sigma>'] x" ..
          next
            assume "x \<notin> ?X' k"

            hence "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = ?mems\<^sub>1'i x"
              using dom\<sigma>
              by (metis \<open>i = k\<close> subst_not_in_dom)
            show ?thesis
            proof(case_tac "x \<in> ?X k")
              assume "x \<in> ?X k"
              from \<open>x \<notin> ?X' k\<close> have "mem\<^sub>1' x = ?mems\<^sub>1'i x"
                by(metis differing_vars_neg \<open>i = k\<close>)
              then have "\<sigma>' x = Some (?mems\<^sub>1'i x)"
                unfolding \<sigma>'_def
                using dom\<sigma>' domh
                by(simp add: \<open>x \<in> ?X k\<close> \<open>x \<notin> ?X' k\<close>)
              hence "mem\<^sub>1' [\<mapsto> \<sigma>'] x = ?mems\<^sub>1'i x"
                unfolding subst_def
                by (metis option.simps(5))
              thus ?thesis
                by (metis \<open>?mems\<^sub>1'i [\<mapsto>\<sigma>] x = ?mems\<^sub>1'i x\<close>)
            next
              assume "x \<notin> ?X k"
              then have "mem\<^sub>1' [\<mapsto> \<sigma>'] x = mem\<^sub>1' x"
                by (metis dom\<sigma>' subst_not_in_dom)
              moreover
              have "?mems\<^sub>1'i x = mem\<^sub>1' x"
                by (metis \<open>i = k\<close> \<open>x \<notin> ?X' k\<close> differing_vars_neg)
              ultimately show ?thesis
                by (metis \<open>?mems\<^sub>1'i [\<mapsto>\<sigma>] x = ?mems\<^sub>1'i x\<close>)
            qed
          qed
        qed
        (* And the same for the second memories: *)
        moreover have "?mems\<^sub>2'i [\<mapsto> \<sigma>] = mem\<^sub>h [\<mapsto> \<sigma>']"
        proof (rule ext)
          fix x

          show "?mems\<^sub>2'i [\<mapsto> \<sigma>] x = mem\<^sub>h [\<mapsto> \<sigma>'] x"
          proof (cases "x \<in> ?X' k")
            assume "x \<in> ?X' k"

            then obtain v where "\<sigma> x = Some v"
              using dom\<sigma>
              by (metis domD \<open>i = k\<close>)
            hence "?mems\<^sub>2'i [\<mapsto> \<sigma>] x = v"
              using \<open>x \<in> ?X' k\<close> dom\<sigma>
              unfolding subst_def
              by (metis option.simps(5))
            moreover
            from \<open>x \<in> ?X' k\<close> have "x \<in> ?X k"
              by auto
            hence "x \<in> dom (\<sigma>')"
              by (metis dom\<sigma>'  \<open>x \<in> ?X' k\<close>)
            hence "mem\<^sub>2' [\<mapsto> \<sigma>'] x = v"
              using dom\<sigma>' c 
              unfolding subst_def
              by (metis \<sigma>'_def \<open>\<sigma> x = Some v\<close> diff_vars_impl option.simps(5) \<open>x \<in> ?X' k\<close>)

            ultimately show ?thesis
              by (metis dom\<sigma>' dom_restrict_total mem\<^sub>2'_def subst_overrides)
          next
            assume "x \<notin> ?X' k"

            hence "?mems\<^sub>2'i [\<mapsto> \<sigma>] x = ?mems\<^sub>2'i x"
              using dom\<sigma>
              by (metis \<open>i = k\<close> subst_not_in_dom) 
            show ?thesis
            
            proof(case_tac "x \<in> ?X k")
              assume "x \<in> ?X k"  
              (* This case can't happen so derive a contradiction *)
              hence "mem\<^sub>1 x = mem\<^sub>1' x \<and> mem\<^sub>2 x = mem\<^sub>2' x" by (metis x_unchanged)

              moreover from \<open>x \<notin> ?X' k\<close> \<open>i = k\<close> have "?mems\<^sub>1'i x = mem\<^sub>1' x \<and> ?mems\<^sub>2'i x = mem\<^sub>2' x"
                by(metis differing_vars_neg)
               
              moreover from \<open>x \<in> ?X k\<close> have "fst (mems ! i) x \<noteq> mem\<^sub>1 x \<or> snd (mems ! i) x \<noteq> mem\<^sub>2 x"
                by(metis differing_vars_elim \<open>i = k\<close>)

              moreover from \<open>x \<in> ?X k\<close> have "fst (mems' ! i) x = fst (mems ! i) x \<and>
                                             snd (mems' ! i) x = snd (mems ! i) x"
                by(metis mems'_k_2 \<open>i = k\<close>)
                
              ultimately have "False" by auto

              thus ?thesis by blast
            next
              assume "x \<notin> ?X k"
              hence "x \<notin> dom \<sigma>'" by (simp add: dom\<sigma>')
              then have "mem\<^sub>h [\<mapsto> \<sigma>'] x = mem\<^sub>h x"
                by (metis subst_not_in_dom)
              moreover
              have "?mems\<^sub>2'i x = mem\<^sub>2' x"
                by (metis \<open>i = k\<close>  mems'_k_1 \<open>x \<notin> ?X k\<close>)

              hence "?mems\<^sub>2'i x = mem\<^sub>h x"
                unfolding mem\<^sub>2'_def
                by (metis dom\<sigma>_mem\<^sub>2 subst_not_in_dom \<open>x \<notin> ?X k\<close>)
              ultimately show ?thesis
                by (metis \<open>?mems\<^sub>2'i [\<mapsto>\<sigma>] x = ?mems\<^sub>2'i x\<close>)
            qed
          qed
        qed

        ultimately show
          "(cms\<^sub>1' ! i, (fst (mems' ! i)) [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2' ! i, (snd (mems' ! i)) [\<mapsto> \<sigma>])"
          using dom\<sigma> dom\<sigma>' g b \<open>i = k\<close>
          by (metis c\<^sub>2'_def cms\<^sub>2'_def equal_size nth_list_update_eq)

      next
        assume "i \<noteq> k"
        define \<sigma>' where "\<sigma>' x =
            (if x \<in> ?X i
             then if x \<in> ?X' i
                  then \<sigma> x
                  else Some (mem\<^sub>1' x)
             else None)" for x
        let ?mems\<^sub>1i = "fst (mems ! i)" and
            ?mems\<^sub>2i = "snd (mems ! i)"
        have "dom \<sigma>' = ?X i"
          unfolding \<sigma>'_def
          apply auto
           apply (metis option.simps(2))
          by (metis domD dom\<sigma>)

        have o: "\<And> x.
                 ((?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                  ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x) \<and>
                 (dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and>
                 (dma mem\<^sub>1' x = dma mem\<^sub>1 x))
                 \<longrightarrow> (mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x)"
        proof -
          fix x
          {
            assume eq_mem: "mem\<^sub>1' x = mem\<^sub>1 x \<and> mem\<^sub>2' x = mem\<^sub>2 x"
               and clas: "dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High"
               and clas_eq: "dma mem\<^sub>1' x = dma mem\<^sub>1 x"
            hence mems'_simp: "?mems\<^sub>1'i x = ?mems\<^sub>1i x \<and> ?mems\<^sub>2'i x = ?mems\<^sub>2i x"
              using mems'_i_4
              by (metis \<open>i \<noteq> k\<close> b i_le length_list_update)
            have
              "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<and> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x = ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
            proof (cases "x \<in> ?X' i")
              assume "x \<in> ?X' i"
              hence "?mems\<^sub>1'i x \<noteq> mem\<^sub>1' x \<or> ?mems\<^sub>2'i x \<noteq> mem\<^sub>2' x"
                by (metis differing_vars_neg_intro)
              hence "x \<in> ?X i"
                using eq_mem mems'_simp
                by (metis differing_vars_neg)
              hence "\<sigma>' x = \<sigma> x"
                by (metis \<sigma>'_def \<open>x \<in> ?X' i\<close>)
              thus ?thesis
                by (clarsimp simp: subst_def mems'_simp split: option.splits)
            next
              assume "x \<notin> ?X' i"
              hence "?mems\<^sub>1'i x = mem\<^sub>1' x \<and> ?mems\<^sub>2'i x = mem\<^sub>2' x"
                by (metis differing_vars_neg)
              hence "x \<notin> ?X i"
                using eq_mem mems'_simp
                by (auto simp: differing_vars_neg_intro)
              thus ?thesis
                by (metis \<open>dom \<sigma>' = ?X i\<close> \<open>x \<notin> ?X' i\<close> dom\<sigma> mems'_simp subst_not_in_dom)
            qed
          }
          thus "?thesis x" by blast
        qed

        (* FIXME: clean this up once we optimise the definition of mems'_i *)
        (* Toby: try to establish something similar to o for the downgrading case *)
        have o_downgrade: "\<And>x. x \<notin> ?X' i \<and> (subst \<sigma> (fst (mems' ! i)) x \<noteq> subst \<sigma>' (fst (mems ! i)) x \<or>
                    subst \<sigma> (snd (mems' ! i)) x \<noteq> subst \<sigma>' (snd (mems ! i)) x) \<and>
                   (dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low) \<longrightarrow>
                    mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x"
          proof -
          fix x {
            assume mem_eq: "mem\<^sub>1' x = mem\<^sub>1 x \<and> mem\<^sub>2' x = mem\<^sub>2 x"
               and clas: "(dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low)"
               and notin: "x \<notin> ?X' i"
            hence mems'_simp [simp]: "?mems\<^sub>1'i x = mem\<^sub>1 x \<and> ?mems\<^sub>2'i x = mem\<^sub>1 x"
              using mems'_i_3
              by (metis \<open>i \<noteq> k\<close> b i_le length_list_update)
            have
              "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<and> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x = ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
            proof (cases "x \<in> ?X' i")
              assume "x \<in> ?X' i"
              thus ?thesis using notin by blast
            next
              assume "x \<notin> ?X' i"
              hence "?mems\<^sub>1'i x = mem\<^sub>1' x \<and> ?mems\<^sub>2'i x = mem\<^sub>2' x"
                by (metis differing_vars_neg)
              moreover have "x \<notin> ?X i"
                using clas compat i_le len_unchanged
                by (force)
              ultimately show ?thesis
                using dom\<sigma> \<open>dom \<sigma>' = ?X i\<close> \<open>x \<notin> ?X' i\<close> apply(simp add: subst_not_in_dom)
                apply(simp add: mem_eq)
                apply(force simp: differing_vars_def differing_vars_lists_def)
                done
            qed
            
          } thus "?thesis x" by blast
        qed

        have modifies_no_var_asm_not_written:
             "\<And>x. mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x \<or>
                   dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x \<or> dma mem\<^sub>2' x \<noteq> dma mem\<^sub>2 x \<Longrightarrow>
              \<not> var_asm_not_written (snd (cms\<^sub>1 ! i)) x"
        proof -
          fix x
          assume "mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x \<or> dma mem\<^sub>2' x \<noteq> dma mem\<^sub>2 x"
          hence modified: " \<not> (doesnt_modify (fst (cms\<^sub>1 ! k)) x) \<or> \<not> (doesnt_modify (fst (cms\<^sub>2 ! k)) x)"
            using b i
            unfolding doesnt_modify_def
            by (metis surjective_pairing)
          hence modified_r: " \<not> (doesnt_read_or_modify (fst (cms\<^sub>1 ! k)) x) \<or> \<not> (doesnt_read_or_modify (fst (cms\<^sub>2 ! k)) x)" using doesnt_read_or_modify_doesnt_modify by fastforce

          from sound_modes have loc_modes:
            "locally_sound_mode_use (cms\<^sub>1 ! k, mem\<^sub>1) \<and>
             locally_sound_mode_use (cms\<^sub>2 ! k, mem\<^sub>2)"
            unfolding sound_mode_use.simps
            by (metis b equal_size list_all_length)
          moreover
          have "snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)"
            by (metis b equal_size modes_eq nth_map)
          have "(cms\<^sub>1 ! k, mem\<^sub>1) \<in> loc_reach (cms\<^sub>1 ! k, mem\<^sub>1)"
            using loc_reach.refl by auto
          hence guars:
                "x \<in> snd (cms\<^sub>1 ! k) GuarNoWrite \<longrightarrow> doesnt_modify (fst (cms\<^sub>1 ! k)) x \<and>
                 x \<in> snd (cms\<^sub>2 ! k) GuarNoWrite \<longrightarrow> doesnt_modify (fst (cms\<^sub>1 ! k)) x \<and>
                 x \<in> snd (cms\<^sub>1 ! k) GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify (fst (cms\<^sub>1 ! k)) x \<and>
                 x \<in> snd (cms\<^sub>2 ! k) GuarNoReadOrWrite \<longrightarrow> doesnt_read_or_modify (fst (cms\<^sub>1 ! k)) x"
            using loc_modes
            unfolding locally_sound_mode_use_def \<open>snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)\<close>
            by (metis loc_reach.refl surjective_pairing)

          hence "x \<notin> snd (cms\<^sub>1 ! k) GuarNoWrite \<and> x \<notin> snd (cms\<^sub>1 ! k) GuarNoReadOrWrite"
            using modified modified_r loc_modes locally_sound_mode_use_def
            by (metis (no_types, lifting) \<open>(cms\<^sub>2, mem\<^sub>2) \<leadsto>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2')\<close> b locally_sound_respects_guarantees modes_eq nth_map meval_elim respects_own_guarantees_def sifum_security_init_axioms)
          moreover
          from sound_modes have "compatible_modes (map snd cms\<^sub>1)"
            by (metis globally_sound_modes_compatible sound_mode_use.simps)

          ultimately show "(?thesis x)"
            unfolding compatible_modes_def var_asm_not_written_def
            using \<open>i \<noteq> k\<close> i_le
            by (metis (no_types) b length_list_update length_map nth_map)
        qed

        
        from o o_downgrade have
          p: "\<And> x. \<lbrakk> ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                      ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x;
                     x \<notin> ?X' i \<or> ((dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and>
                                   (dma mem\<^sub>1' x = dma mem\<^sub>1 x)) \<rbrakk> \<Longrightarrow>
          \<not> var_asm_not_written  (snd (cms\<^sub>1 ! i)) x"
        proof -
          fix x
          assume mems_neq:
            "?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
             and nin:
            "x \<notin> ?X' i \<or> ((dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and>
                           (dma mem\<^sub>1' x = dma mem\<^sub>1 x))"
          hence "mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x"
            (* FIXME: clean this up *)
            apply -
            apply(erule disjE[where P="x \<notin> ?X' i"])
             apply(case_tac "(dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low)")
              apply(metis o_downgrade[rule_format])
             apply(case_tac "dma mem\<^sub>1' x = dma mem\<^sub>1 x")
              (* use o *)
              apply(metis (poly_guards_query) o Sec.exhaust)
             (* should follow trivially *)
             apply fastforce
            apply(metis (poly_guards_query) o Sec.exhaust)
            done
          thus "?thesis x"
            by(force simp: modifies_no_var_asm_not_written)
        qed

        have q':
          "\<And> x. \<lbrakk> dma mem\<^sub>1 x = Low; dma mem\<^sub>1' x = Low;
                   ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                   ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x;
                   x \<notin> ?X' i \<rbrakk> \<Longrightarrow>
                 mem\<^sub>1' x = mem\<^sub>2' x"
          by (metis \<open>i \<noteq> k\<close> b compat_different_vars i_le length_list_update mems'_i_2 o)
        have "i < length cms\<^sub>1"
          by (metis cms\<^sub>2'_def equal_size i_le length_list_update new_length)
        with compat and \<open>dom \<sigma>' = ?X i\<close> have
          bisim: "(cms\<^sub>1 ! i, ?mems\<^sub>1i [\<mapsto> \<sigma>']) \<approx> (cms\<^sub>2 ! i, ?mems\<^sub>2i [\<mapsto> \<sigma>'])"
          by auto

        define \<sigma>'\<^sub>k where "\<sigma>'\<^sub>k x = (if x \<in> ?X k then Some (undefined::'Val) else None)" for x
        have "dom \<sigma>'\<^sub>k = ?X k" unfolding \<sigma>'\<^sub>k_def by (simp add: dom_def)
        with compat and \<open>dom \<sigma>'\<^sub>k = ?X k\<close> and b have
          bisim\<^sub>k: "(cms\<^sub>1 ! k, ?mems\<^sub>1k [\<mapsto> \<sigma>'\<^sub>k]) \<approx> (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>'\<^sub>k])"
          by auto

        have q_downgrade:
          "\<And> x. \<lbrakk> dma mem\<^sub>1 x = High; dma mem\<^sub>1' x = Low;
                   ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                   ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x;
                   x \<notin> ?X' i \<rbrakk> \<Longrightarrow>
                 mem\<^sub>1' x = mem\<^sub>2' x"
        by (metis (erased, hide_lams) \<open>i \<noteq> k\<close> compat_different_vars i_le len_unchanged mems'_i_2 o_downgrade)

        have q: "\<And> x. \<lbrakk> dma mem\<^sub>1' x = Low;
                   ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                   ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x;
                   x \<notin> ?X' i \<rbrakk> \<Longrightarrow>
                 mem\<^sub>1' x = mem\<^sub>2' x"
          apply(case_tac "dma mem\<^sub>1 x")
           apply(blast intro: q_downgrade)
          by(blast intro: q')

        let ?\<Delta> = "differing_vars (?mems\<^sub>1i [\<mapsto> \<sigma>']) (?mems\<^sub>1'i [\<mapsto> \<sigma>]) \<union>
                  differing_vars (?mems\<^sub>2i [\<mapsto> \<sigma>']) (?mems\<^sub>2'i [\<mapsto> \<sigma>])"

        have \<Delta>_finite: "finite ?\<Delta>"
          by (metis (no_types) differing_finite finite_UnI)
        \<comment> \<open>We first define the adaptation, then prove that it does the right thing.\<close>
        define A where "A x =
             (if x \<in> ?\<Delta>
              then if dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = High
                   then Some (?mems\<^sub>1'i [\<mapsto> \<sigma>] x, ?mems\<^sub>2'i [\<mapsto> \<sigma>] x)
                   else if x \<in> ?X' i
                        then (case \<sigma> x of
                                Some v \<Rightarrow> Some (v, v)
                              | None \<Rightarrow> None)
                        else Some (mem\<^sub>1' x, mem\<^sub>1' x)
              else None)" for x
        have domA: "dom A = ?\<Delta>"
        proof
          show "dom A \<subseteq> ?\<Delta>"
            using A_def
            apply (auto simp: domD)
            by (metis option.simps(2))
        next
          show "?\<Delta> \<subseteq> dom A"
            unfolding A_def
            apply auto
             apply (metis (no_types) domIff dom\<sigma> option.exhaust option.simps(5))
            by (metis (no_types) domIff dom\<sigma> option.exhaust option.simps(5))
        qed

        (* FIXME: clean up *)
        have dma_eq: "dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) = dma mem\<^sub>1'"
          apply(rule dma_\<C>)
          apply(rule ballI)
          apply(case_tac "x \<in> ?X' i")
           apply(drule not_control[rotated])
            apply (metis i_le)
           apply blast
          apply(subst subst_not_in_dom)
           apply(simp add: dom\<sigma>)
          apply(simp add: differing_vars_lists_def differing_vars_def)
          done

        (* FIXME: clean up *)
        have dma_eq'': "dma (?mems\<^sub>1i [\<mapsto> \<sigma>']) = dma mem\<^sub>1"
          apply(rule dma_\<C>)
          apply(rule ballI)
          apply(case_tac "x \<in> ?X i")
           using compat compat i_le len_unchanged apply fastforce
          apply(subst subst_not_in_dom)
           apply(simp add: \<open>dom \<sigma>' = ?X i\<close>)
          apply(simp add: differing_vars_lists_def differing_vars_def)
          done

        have dma_eq': "dma (subst ((to_partial mem\<^sub>2 |` differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems k)) mem\<^sub>1') = dma mem\<^sub>1'"
          using compat b
          by(force intro!: dma_\<C> subst_not_in_dom)

        have A_correct:
              "\<And> x.
               ?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] x = ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<and>
               ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] x = ?mems\<^sub>2'i [\<mapsto> \<sigma>] x"
        proof -
          fix x
          show "?thesis x"
            (is "?Eq\<^sub>1 \<and> ?Eq\<^sub>2")
          proof (cases "x \<in> ?\<Delta>")
            assume "x \<in> ?\<Delta>"
            hence diff:
              "?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
              by (auto simp: differing_vars_def)
            show ?thesis
            proof (cases "dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x")
              assume "dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = High"
              from \<open>dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = High\<close> have A_simp [simp]:
                "A x = Some (?mems\<^sub>1'i [\<mapsto> \<sigma>] x, ?mems\<^sub>2'i [\<mapsto> \<sigma>] x)"
                unfolding A_def
                by (metis \<open>x \<in> ?\<Delta>\<close>)
              from A_simp have ?Eq\<^sub>1 ?Eq\<^sub>2
                unfolding A_def apply_adaptation_def
                by auto
              thus ?thesis
                by auto
            next
              assume "dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = Low"
              show ?thesis
              proof (cases "x \<in> ?X' i")
                assume "x \<in> ?X' i"
                then obtain v where "\<sigma> x = Some v"
                  by (metis domD dom\<sigma>)
                hence eq: "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = v \<and> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x = v"
                  unfolding subst_def
                  by auto
                moreover
                from \<open>x \<in> ?X' i\<close> and \<open>dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = Low\<close> have A_simp [simp]:
                  "A x = (case \<sigma> x of
                            Some v \<Rightarrow> Some (v, v)
                          | None \<Rightarrow> None)"
                  unfolding A_def
                  by (metis Sec.simps(1) \<open>x \<in> ?\<Delta>\<close>)
                ultimately show ?thesis
                  using domA \<open>x \<in> ?\<Delta>\<close> \<open>\<sigma> x = Some v\<close>
                  by (auto simp: apply_adaptation_def)

              next
                assume "x \<notin> ?X' i"

                hence A_simp [simp]: "A x = Some (mem\<^sub>1' x, mem\<^sub>1' x)"
                  unfolding A_def
                  using \<open>x \<in> ?\<Delta>\<close> \<open>x \<notin> ?X' i\<close> \<open>dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = Low\<close>
                  by auto

                from q have "mem\<^sub>1' x = mem\<^sub>2' x"
                  by (metis \<open>dma (?mems\<^sub>1'i [\<mapsto> \<sigma>]) x = Low\<close> diff \<open>x \<notin> ?X' i\<close> dma_eq dma_eq'')

                from \<open>x \<notin> ?X' i\<close> have
                  "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = ?mems\<^sub>1'i x \<and> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x = ?mems\<^sub>2'i x"
                  by (metis dom\<sigma> subst_not_in_dom)
                moreover
                from \<open>x \<notin> ?X' i\<close> have "?mems\<^sub>1'i x = mem\<^sub>1' x \<and> ?mems\<^sub>2'i x = mem\<^sub>2' x"
                  by (metis differing_vars_neg)
                ultimately show ?thesis
                  using \<open>mem\<^sub>1' x = mem\<^sub>2' x\<close>
                  by (auto simp: apply_adaptation_def)
              qed
            qed
          
          next
            assume "x \<notin> ?\<Delta>"
            hence "A x = None"
              by (metis domA domIff)
            from \<open>A x = None\<close> have "x \<notin> dom A"
              by (metis domIff)
            from \<open>x \<notin> ?\<Delta>\<close> have "?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] x = ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<and>
                                 ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] x = ?mems\<^sub>2'i [\<mapsto> \<sigma>] x"
              using \<open>A x = None\<close>
              unfolding differing_vars_def apply_adaptation_def
              by auto

            thus ?thesis
              by auto
          qed
        qed
        hence adapt_eq: 
              "?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] = ?mems\<^sub>1'i [\<mapsto> \<sigma>] \<and>
               ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] = ?mems\<^sub>2'i [\<mapsto> \<sigma>]"
          by auto

        have "cms\<^sub>1' ! i = cms\<^sub>1 ! i"
          by (metis \<open>i \<noteq> k\<close> b nth_list_update_neq)

        have A_correct': "globally_consistent A (snd (cms\<^sub>1 ! i)) (?mems\<^sub>1i [\<mapsto> \<sigma>']) (?mems\<^sub>2i [\<mapsto> \<sigma>'])"
          (* FIXME: clean up *)
          apply(clarsimp simp: globally_consistent_def)
          apply(rule conjI)
           apply(split option.split)
           apply(intro allI conjI)
            apply simp
           apply(intro allI impI)
           apply(split prod.split)
           apply(intro allI impI)
           apply(simp only:)
           proof -
             fix x v v'
             assume A_updates_x\<^sub>1: "A x = Some (v, v')"
                and A_updates_x\<^sub>2:"subst \<sigma>' (fst (mems ! i)) x \<noteq> v \<or> subst \<sigma>' (snd (mems ! i)) x \<noteq> v'"
             hence "x \<in> dom A" by(blast)
             hence diff:
               "?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
                by (auto simp: differing_vars_def domA)
             show "\<not> var_asm_not_written (snd (cms\<^sub>1 ! i)) x"
             proof (cases "x \<notin> ?X' i \<or> ((dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and> dma mem\<^sub>1' x = dma mem\<^sub>1 x)")
               assume "x \<notin> ?X' i \<or> ((dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and> (dma mem\<^sub>1' x = dma mem\<^sub>1 x))"
               from this p and diff show writable: "\<not> var_asm_not_written (snd (cms\<^sub>1 ! i)) x"
                 by auto
             next
               assume "\<not> (x \<notin> ?X' i \<or> ((dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High) \<and> (dma mem\<^sub>1' x = dma mem\<^sub>1 x)))"
               hence "x \<in> ?X' i" "((dma mem\<^sub>1 x = High \<and> dma mem\<^sub>1' x = Low) \<or> (dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x))"
                 by (metis Sec.exhaust)+

               thus ?thesis by(fastforce simp add: modifies_no_var_asm_not_written)
             qed
                      
          next
            
            have reclas: "(\<forall>x. dma ((subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A]) x \<noteq> dma (subst \<sigma>' (fst (mems ! i))) x \<longrightarrow>
         \<not> var_asm_not_written (snd (cms\<^sub>1 ! i)) x)"
              apply(simp add: adapt_eq dma_eq dma_eq'')
              apply(simp add: modifies_no_var_asm_not_written)
              done

            have "snd (cms\<^sub>2 ! i) = snd (cms\<^sub>1 ! i)"
              by (metis \<open>i < length cms\<^sub>1\<close> equal_size modes_eq nth_map)

            hence low_mds_eq: "(subst \<sigma>' (fst (mems ! i))) =\<^bsub>snd (cms\<^sub>1 ! i)\<^esub>\<^sup>l (subst \<sigma>' (snd (mems ! i)))"
              apply -
              apply(rule mm_equiv_low_eq[where c\<^sub>1="fst (cms\<^sub>1 ! i)" and c\<^sub>2="fst (cms\<^sub>2 ! i)"])
              using bisim
              by (metis prod.collapse)

            have "snd (cms\<^sub>2 ! k) = snd (cms\<^sub>1 ! k)"
              by (metis b equal_size modes_eq nth_map)

            hence low_mds_eq\<^sub>k: "(subst \<sigma>'\<^sub>k (fst (mems ! k))) =\<^bsub>snd (cms\<^sub>1 ! k)\<^esub>\<^sup>l (subst \<sigma>'\<^sub>k (snd (mems ! k)))"
              apply -
              apply(rule mm_equiv_low_eq[where c\<^sub>1="fst (cms\<^sub>1 ! k)" and c\<^sub>2="fst (cms\<^sub>2 ! k)"])
              using bisim\<^sub>k
              by (metis prod.collapse)

            have eq: "\<forall>x. dma ((subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A]) x = Low \<and> (x \<in> (snd (cms\<^sub>1 ! i)) AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow>
        (subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A] x = (subst \<sigma>' (snd (mems ! i))) [\<parallel>\<^sub>2 A] x"
            (* FIXME: clean up *)
            apply(clarsimp simp: adapt_eq dma_eq)
            apply(case_tac "x \<in> dom \<sigma>")
             apply(force simp: subst_def)
            apply(simp add: subst_not_in_dom)
            apply(simp add: dom\<sigma>)
            apply(clarsimp simp: differing_vars_lists_def differing_vars_def)
            apply(case_tac "i = k")
             apply(simp add: \<open>i \<noteq> k\<close>)
            apply(erule mems'_i_cases)
                apply(rule \<open>i < length cms\<^sub>1'\<close>[simplified len_unchanged])
               apply force
              apply fastforce
             apply clarsimp
            apply clarsimp

            apply(case_tac "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i")
             apply(force simp: differing_vars_lists_def differing_vars_def)

            apply(insert low_mds_eq)[1]
            apply(simp add: low_mds_eq_def)
            apply(drule_tac x=x in spec)

            apply(subst (asm) makes_compatible_dma_eq)
               apply(rule compat)
              apply(rule \<open>i < length cms\<^sub>1\<close>)
             apply(rule \<open>dom \<sigma>' = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i\<close>)
            apply simp
            apply(subgoal_tac "x \<notin> dom \<sigma>'")
             apply(simp add: subst_not_in_dom)
             apply force
            apply(simp add: \<open>dom \<sigma>' = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i\<close>)+
            done
          from reclas eq
          show " (\<forall>x. dma ((subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A]) x \<noteq> dma (subst \<sigma>' (fst (mems ! i))) x \<longrightarrow>
         \<not> var_asm_not_written (snd (cms\<^sub>1 ! i)) x) \<and>
    (\<forall>x. dma ((subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A]) x = Low \<and> (x \<in> snd (cms\<^sub>1 ! i) AsmNoReadOrWrite \<longrightarrow> x \<in> \<C>) \<longrightarrow>
         (subst \<sigma>' (fst (mems ! i))) [\<parallel>\<^sub>1 A] x = (subst \<sigma>' (snd (mems ! i))) [\<parallel>\<^sub>2 A] x)"
          by blast
        qed

        have "snd (cms\<^sub>1 ! i) = snd (cms\<^sub>2 ! i)"
          by (metis \<open>i < length cms\<^sub>1\<close> equal_size modes_eq nth_map)

        with bisim have "(cms\<^sub>1 ! i, ?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A]) \<approx> (cms\<^sub>2 ! i, ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A])"
          using A_correct'
          apply (subst surjective_pairing[of "cms\<^sub>1 ! i"])
          apply (subst surjective_pairing[of "cms\<^sub>2 ! i"])
          by (metis surjective_pairing globally_consistent_adapt_bisim)

        thus ?thesis using adapt_eq
          by (metis \<open>i \<noteq> k\<close> b cms\<^sub>2'_def nth_list_update_neq)
      qed
    next
      fix i x

      let ?mems\<^sub>1'i = "fst (mems' ! i)"
      let ?mems\<^sub>2'i = "snd (mems' ! i)"
      assume i_le: "i < length cms\<^sub>1'"
      assume mem_eq': "mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High \<or> x \<in> \<C>"
      show "x \<notin> ?X' i"
      proof (cases "x \<in> \<C>")
        assume "x \<in> \<C>"
        thus ?thesis by(metis not_control i_le)
      next
        assume "x \<notin> \<C>"
        hence mem_eq: "mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High" by(metis mem_eq')
        thus ?thesis
        proof (cases "i = k")
          assume "i = k"
          thus "x \<notin> ?X' i"
            apply (cases "x \<notin> ?X k")
             apply (metis differing_vars_neg_intro mems'_k_1 mems'_k_2)
            by(metis compat_different[OF compat] b mem_eq Sec.distinct(1) x_unchanged)
        next
          assume "i \<noteq> k"
          thus "x \<notin> ?X' i"
          proof (rule mems'_i_cases)
            from b i_le show "i < length cms\<^sub>1"
              by (metis length_list_update)
          next
            assume "fst (mems' ! i) x = mem\<^sub>1' x"
              "snd (mems' ! i) x = mem\<^sub>2' x"
            thus "x \<notin> ?X' i"
              by (metis differing_vars_neg_intro)
          next
            assume "mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x"
              "mem\<^sub>1' x \<noteq> mem\<^sub>2' x" and "dma mem\<^sub>1' x = Low"
            \<comment> \<open>In this case, for example, the values of (mems' ! i) are not needed.\<close>
            thus "x \<notin> ?X' i"
              by (metis Sec.simps(2) mem_eq)
          next
            (* FIXME: clean this up -- there is surely a more direct route.
                      Same must be true of mems'_i definition and o, o_downgrade,
                      p etc. lemmas above that are proved with surely lots of
                      overlapping cases *)
            assume case3: "mem\<^sub>1 x = mem\<^sub>1' x" "mem\<^sub>2 x = mem\<^sub>2' x" 
              "dma mem\<^sub>1 x = Low \<or> dma mem\<^sub>1' x = High"
              "fst (mems' ! i) x = fst (mems ! i) x"
              "snd (mems' ! i) x = snd (mems ! i) x"
            have "x \<in> ?X' i \<Longrightarrow> mem\<^sub>1' x \<noteq> mem\<^sub>2' x \<and> dma mem\<^sub>1' x = Low"
            proof -
              assume "x \<in> ?X' i"
              from case3 and \<open>x \<in> ?X' i\<close> have "x \<in> ?X i"
                by (metis differing_vars_neg differing_vars_elim)
              with case3 have "mem\<^sub>1' x \<noteq> mem\<^sub>2' x \<and> dma mem\<^sub>1 x = Low"
                by (metis b compat compat_different i_le length_list_update)
              with mem_eq have clases: "dma mem\<^sub>1 x = Low \<and> dma mem\<^sub>1' x = High" by auto
              have "fst (mems' ! i) x = mem\<^sub>1' x \<and> snd (mems' ! i) x = mem\<^sub>2' x"
                apply(rule mems'_i_5)
                     apply(rule \<open>i \<noteq> k\<close>)
                    using i_le len_unchanged apply(simp)
                   apply(simp add: case3)+
                 apply(simp add: clases)+
                done
              hence "x \<notin> ?X' i" by (metis differing_vars_neg_intro)
              with \<open>x \<in> ?X' i\<close> show ?thesis by blast
            qed
            with \<open>mem\<^sub>1' x = mem\<^sub>2' x \<or> dma mem\<^sub>1' x = High\<close> show "x \<notin> ?X' i"
              by auto
          next
            assume case4: "mem\<^sub>1 x = mem\<^sub>1' x" "mem\<^sub>2 x = mem\<^sub>2' x"
                   "dma mem\<^sub>1 x = High" "dma mem\<^sub>1' x = Low"
                   "fst (mems' ! i) x = mem\<^sub>1 x" "snd (mems' ! i) x = mem\<^sub>1 x"
            with mem_eq have "mem\<^sub>1' x = mem\<^sub>2' x" by auto
            with case4 show ?thesis by(auto simp: differing_vars_def differing_vars_lists_def)
          next
            assume "fst (mems' ! i) x = mem\<^sub>1' x"
                   "snd (mems' ! i) x = mem\<^sub>2' x" thus ?thesis by(metis differing_vars_neg_intro)
          qed
        qed
      qed
    next
      { fix x
        have "\<exists> i < length cms\<^sub>1. x \<notin> ?X' i"
        proof (cases "mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x")
          assume var_changed: "mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x"
          have "x \<notin> ?X' k"
            apply (rule mems'_k_cases)
             apply (metis differing_vars_neg_intro)
            by (metis var_changed x_unchanged)
          thus ?thesis by (metis b)
        next
          assume "\<not> (mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x)"
          hence assms: "mem\<^sub>1 x = mem\<^sub>1' x" "mem\<^sub>2 x = mem\<^sub>2' x" "dma mem\<^sub>1' x = dma mem\<^sub>1 x" by auto

          have "length cms\<^sub>1 \<noteq> 0"
            using b
            by (metis less_zeroE)
          then obtain i where i_prop: "i < length cms\<^sub>1 \<and> x \<notin> ?X i"
            using compat
            by (auto, blast)
          show ?thesis
          proof (cases "i = k")
            assume "i = k"
            have "x \<notin> ?X' k"
              apply (rule mems'_k_cases)
               apply (metis differing_vars_neg_intro)
              by (metis i_prop \<open>i = k\<close>)
            thus ?thesis
              by (metis b)
          next
            from i_prop have "x \<notin> ?X i" by simp
            assume "i \<noteq> k"
            hence "x \<notin> ?X' i"
              (* FIXME: clean up *)
              apply -
              apply(rule mems'_i_cases)
                    apply assumption
                   apply(simp add: i_prop)
                  apply(simp add: assms)+
               using \<open>x \<notin> ?X i\<close> differing_vars_neg
               using \<open>\<not> (mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x \<or> dma mem\<^sub>1' x \<noteq> dma mem\<^sub>1 x)\<close> differing_vars_elim apply auto[1]
              by(metis differing_vars_neg_intro)
            with i_prop show ?thesis
              by auto
          qed
        qed
      }
      thus "(length cms\<^sub>1' = 0 \<and> mem\<^sub>1' =\<^sup>l mem\<^sub>2') \<or> (\<forall> x. \<exists> i < length cms\<^sub>1'. x \<notin> ?X' i)"
        by (metis cms\<^sub>2'_def equal_size length_list_update new_length)
    qed
  qed

  ultimately show ?thesis using that by blast
qed

text \<open>The Isar proof language provides a readable
way of specifying assumptions while also giving them names for subsequent
usage.\<close>
lemma compat_low_eq:
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes x_low: "dma mem\<^sub>1 x = Low"
  assumes x_readable: "x \<in> \<C> \<or> (\<forall> i < length cms\<^sub>1. x \<notin> snd (cms\<^sub>1 ! i) AsmNoReadOrWrite)"
  shows "mem\<^sub>1 x = mem\<^sub>2 x"
proof -
  let ?X = "\<lambda> i. differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  from compat have "(length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or>
                    (\<forall> x. \<exists> j. j < length cms\<^sub>1 \<and> x \<notin> ?X j)"
    by auto
  thus "mem\<^sub>1 x = mem\<^sub>2 x"
  proof
    assume "length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2"
    with x_low show ?thesis
      by (simp add: low_eq_def)
  next
    assume "\<forall> x. \<exists> j. j < length cms\<^sub>1 \<and> x \<notin> ?X j"
    then obtain j where j_prop: "j < length cms\<^sub>1 \<and> x \<notin> ?X j"
      by auto
    let ?mems\<^sub>1j = "fst (mems ! j)" and
        ?mems\<^sub>2j = "snd (mems ! j)"

    obtain \<sigma> :: "'Var \<rightharpoonup> 'Val" where dom\<sigma>: "dom \<sigma> = ?X j"
      by (metis dom_restrict_total)

    from compat x_low makes_compatible_dma_eq j_prop \<open>dom \<sigma> = ?X j\<close>
    have x_low: "dma (?mems\<^sub>1j [\<mapsto> \<sigma>]) x = Low"
      by metis

    from dom\<sigma> compat and j_prop have "(cms\<^sub>1 ! j, ?mems\<^sub>1j [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! j, ?mems\<^sub>2j [\<mapsto> \<sigma>])"
      by auto
    
    moreover
    have "snd (cms\<^sub>1 ! j) = snd (cms\<^sub>2 ! j)"
      using modes_eq
      by (metis j_prop length_map nth_map)

    ultimately have "?mems\<^sub>1j [\<mapsto> \<sigma>] =\<^bsub>snd (cms\<^sub>1 ! j)\<^esub>\<^sup>l ?mems\<^sub>2j [\<mapsto> \<sigma>]"
      using modes_eq j_prop
      by (metis mm_equiv_low_eq prod.collapse)
    hence "?mems\<^sub>1j x = ?mems\<^sub>2j x"
      using x_low x_readable j_prop \<open>dom \<sigma> = ?X j\<close>
      unfolding low_mds_eq_def
      by (metis subst_not_in_dom)

    thus ?thesis
      using j_prop
      by (metis compat_different_vars)
  qed
qed

lemma loc_reach_subset:
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  shows "loc_reach \<langle>c', mds', mem'\<rangle> \<subseteq> loc_reach \<langle>c, mds, mem\<rangle>"
proof (clarify)
  fix c'' mds'' mem''
  from eval have "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds, mem\<rangle>"
    by (metis loc_reach.refl loc_reach.step surjective_pairing)
  assume "\<langle>c'', mds'', mem''\<rangle> \<in> loc_reach \<langle>c', mds', mem'\<rangle>"
  thus "\<langle>c'', mds'', mem''\<rangle> \<in> loc_reach \<langle>c, mds, mem\<rangle>"
    apply induct
      apply (metis \<open>\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds, mem\<rangle>\<close> surjective_pairing)
     apply (metis loc_reach.step)
    by (metis loc_reach.mem_diff)
qed

lemma locally_sound_modes_invariant:
  assumes sound_modes: "locally_sound_mode_use \<langle>c, mds, mem\<rangle>"
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  shows "locally_sound_mode_use \<langle>c', mds', mem'\<rangle>"
proof -
  from eval have "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds, mem\<rangle>"
    by (metis fst_conv loc_reach.refl loc_reach.step snd_conv)
  thus ?thesis
    using sound_modes
    unfolding locally_sound_mode_use_def
    by (metis (no_types) Collect_empty_eq eval loc_reach_subset subsetD)
qed


lemma meval_sched_one:
  "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem') \<Longrightarrow>
        (cms, mem) \<rightarrow>\<^bsub>[k]\<^esub> (cms', mem')"
  apply(simp)
  done

lemma meval_sched_ConsI: 
  "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem') \<Longrightarrow>
   (cms', mem') \<rightarrow>\<^bsub>sched\<^esub> (cms'', mem'') \<Longrightarrow>
   (cms, mem) \<rightarrow>\<^bsub>(k#sched)\<^esub> (cms'', mem'')"
  by fastforce

lemma reachable_modes_subset:
  assumes eval: "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem')"
  shows "reachable_mode_states (cms', mem') \<subseteq> reachable_mode_states (cms, mem)"
proof
  fix mdss
  assume "mdss \<in> reachable_mode_states (cms', mem')"
  thus "mdss \<in> reachable_mode_states (cms, mem)"
    using assms
    unfolding reachable_mode_states_def 
    by (blast intro: meval_sched_ConsI)
qed

lemma globally_sound_modes_invariant:
  assumes globally_sound: "globally_sound_mode_use (cms, mem)"
  assumes eval: "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem')"
  shows "globally_sound_mode_use (cms', mem')"
  using assms reachable_modes_subset
  unfolding globally_sound_mode_use_def
  by (metis (no_types) subsetD)

lemma loc_reach_mem_diff_subset:
  assumes mem_diff: "\<forall> x. var_asm_not_written mds x \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x \<and> dma mem\<^sub>1 x = dma mem\<^sub>2 x"
  shows "\<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds, mem\<^sub>1\<rangle> \<Longrightarrow> \<langle>c', mds', mem'\<rangle> \<in> loc_reach \<langle>c, mds, mem\<^sub>2\<rangle>"
proof -
  let ?lc = "\<langle>c', mds', mem'\<rangle>"
  assume "?lc \<in> loc_reach \<langle>c, mds, mem\<^sub>1\<rangle>"
  thus ?thesis
  proof (induct)
    case refl
    thus ?case
      by (metis fst_conv loc_reach.mem_diff loc_reach.refl mem_diff snd_conv)
  next
    case step
    thus ?case
      by (metis loc_reach.step)
  next
    case mem_diff
    thus ?case
      by (metis loc_reach.mem_diff)
  qed
qed

lemma loc_reach_mem_diff_eq:
  assumes mem_diff: "\<forall> x. var_asm_not_written mds x \<longrightarrow> mem' x = mem x \<and> dma mem' x = dma mem x"
  shows "loc_reach \<langle>c, mds, mem\<rangle> = loc_reach \<langle>c, mds, mem'\<rangle>"
  using assms loc_reach_mem_diff_subset
  by (auto, metis)

lemma sound_modes_invariant:
  assumes sound_modes: "sound_mode_use (cms, mem)"
  assumes eval: "(cms, mem) \<leadsto>\<^bsub>k\<^esub> (cms', mem')"
  shows "sound_mode_use (cms', mem')"
proof -
  from sound_modes and eval have "globally_sound_mode_use (cms', mem')"
    by (metis globally_sound_modes_invariant sound_mode_use.simps)
  moreover
  from sound_modes have loc_sound: "\<forall> i < length cms. locally_sound_mode_use (cms ! i, mem)"
    unfolding sound_mode_use_def
    by simp (metis list_all_length)
  from eval obtain k cms\<^sub>k' where
    ev: "(cms ! k, mem) \<leadsto> (cms\<^sub>k', mem') \<and> k < length cms \<and> cms' = cms [k := cms\<^sub>k']"
    by (metis meval_elim)
  hence "length cms = length cms'"
    by auto
  have "\<And> i. i < length cms' \<Longrightarrow> locally_sound_mode_use (cms' ! i, mem')"
  proof -
    fix i
    assume i_le: "i < length cms'"
    thus "?thesis i"
    proof (cases "i = k")
      assume "i = k"
      thus ?thesis
        using i_le ev loc_sound
        by (metis (hide_lams, no_types) locally_sound_modes_invariant nth_list_update surj_pair)
    next
      assume "i \<noteq> k"
      hence "cms' ! i = cms ! i"
        by (metis ev nth_list_update_neq)
      from sound_modes have "compatible_modes (map snd cms)"
        unfolding sound_mode_use.simps
        by (metis globally_sound_modes_compatible)
      hence "\<And> x. var_asm_not_written (snd (cms ! i)) x \<Longrightarrow> x \<in> snd (cms ! k) GuarNoWrite \<or> x \<in> snd (cms ! k) GuarNoReadOrWrite"
        unfolding compatible_modes_def
        by (metis (no_types) \<open>i \<noteq> k\<close> \<open>length cms = length cms'\<close> ev i_le length_map nth_map var_asm_not_written_def)
      hence "\<And> x. var_asm_not_written (snd (cms ! i)) x \<longrightarrow> doesnt_modify (fst (cms ! k)) x"
        using ev loc_sound
        unfolding locally_sound_mode_use_def
        by (metis loc_reach.refl surjective_pairing doesnt_read_or_modify_doesnt_modify)
      with ev have "\<And> x. var_asm_not_written (snd (cms ! i)) x \<Longrightarrow> mem x = mem' x \<and> dma mem x = dma mem' x"
        unfolding doesnt_modify_def by (metis prod.collapse)
      with loc_reach_mem_diff_eq have "loc_reach (cms ! i, mem') = loc_reach (cms ! i, mem)"
         apply -
         by(case_tac "cms ! i", simp)
      thus ?thesis
        using loc_sound i_le \<open>length cms = length cms'\<close>
        unfolding locally_sound_mode_use_def
        by (metis \<open>cms' ! i = cms ! i\<close>)
    qed
  qed
  ultimately show ?thesis
    unfolding sound_mode_use.simps
    by (metis (no_types) list_all_length)
qed

lemma app_Cons_rewrite:
  "ns @ (a # ms) = ((ns @ [a]) @ ms)"
  apply simp
  done

lemma meval_sched_app_iff:
  "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns@ms\<^esub> (cms\<^sub>1', mem\<^sub>1') =
   (\<exists>cms\<^sub>1'' mem\<^sub>1''. (cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns\<^esub> (cms\<^sub>1'', mem\<^sub>1'') \<and> (cms\<^sub>1'', mem\<^sub>1'') \<rightarrow>\<^bsub>ms\<^esub> (cms\<^sub>1', mem\<^sub>1'))"
  apply(induct ns arbitrary: ms cms\<^sub>1 mem\<^sub>1)
   apply simp
  apply force
  done

lemmas meval_sched_appD = meval_sched_app_iff[THEN iffD1]
lemmas meval_sched_appI = meval_sched_app_iff[THEN iffD2, OF exI, OF exI]

lemma meval_sched_snocD:
  "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns@[n]\<^esub> (cms\<^sub>1', mem\<^sub>1') \<Longrightarrow>
   \<exists>cms\<^sub>1'' mem\<^sub>1''. (cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns\<^esub> (cms\<^sub>1'', mem\<^sub>1'') \<and> (cms\<^sub>1'', mem\<^sub>1'') \<leadsto>\<^bsub>n\<^esub> (cms\<^sub>1', mem\<^sub>1')"
  apply(fastforce dest: meval_sched_appD)
  done

lemma meval_sched_snocI:
  "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns\<^esub> (cms\<^sub>1'', mem\<^sub>1'') \<and> (cms\<^sub>1'', mem\<^sub>1'') \<leadsto>\<^bsub>n\<^esub> (cms\<^sub>1', mem\<^sub>1') \<Longrightarrow>
  (cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns@[n]\<^esub> (cms\<^sub>1', mem\<^sub>1')"
  apply(fastforce intro: meval_sched_appI)
  done
  
lemma makes_compatible_eval_sched:
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)" "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes eval: "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>1', mem\<^sub>1')"
  shows "\<exists> cms\<^sub>2' mem\<^sub>2' mems'. sound_mode_use (cms\<^sub>1', mem\<^sub>1') \<and>
                              sound_mode_use (cms\<^sub>2', mem\<^sub>2') \<and>
                              map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                              (cms\<^sub>2, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                              makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
proof -
  (* cms\<^sub>1' and mem\<^sub>1' need to be arbitrary so
     that the induction hypothesis is sufficiently general. *)
  from eval show ?thesis
  proof (induct "sched" arbitrary: cms\<^sub>1' mem\<^sub>1' rule: rev_induct)
    case Nil
    hence "cms\<^sub>1' = cms\<^sub>1 \<and> mem\<^sub>1' = mem\<^sub>1"
      by (simp add: Pair_inject meval_sched.simps(1))
    thus ?case
      by (metis compat meval_sched.simps(1) modes_eq sound_modes)
  next
    case (snoc n ns)
    then obtain cms\<^sub>1'' mem\<^sub>1'' where eval'':
      "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>ns\<^esub> (cms\<^sub>1'', mem\<^sub>1'') \<and> (cms\<^sub>1'', mem\<^sub>1'') \<leadsto>\<^bsub>n\<^esub> (cms\<^sub>1', mem\<^sub>1')"
      by (metis meval_sched_snocD prod_cases3 snd_conv)
    hence "(cms\<^sub>1'', mem\<^sub>1'') \<leadsto>\<^bsub>n\<^esub> (cms\<^sub>1', mem\<^sub>1')" ..
    moreover
    from eval'' obtain cms\<^sub>2'' mem\<^sub>2'' mems'' where IH:
      "sound_mode_use (cms\<^sub>1'', mem\<^sub>1'') \<and>
       sound_mode_use (cms\<^sub>2'', mem\<^sub>2'') \<and>
       map snd cms\<^sub>1'' = map snd cms\<^sub>2'' \<and>
       (cms\<^sub>2, mem\<^sub>2) \<rightarrow>\<^bsub>ns\<^esub> (cms\<^sub>2'', mem\<^sub>2'') \<and>
       makes_compatible (cms\<^sub>1'', mem\<^sub>1'') (cms\<^sub>2'', mem\<^sub>2'') mems''"
      using snoc
      by metis
    ultimately obtain cms\<^sub>2' mem\<^sub>2' mems' where
      "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
       (cms\<^sub>2'', mem\<^sub>2'') \<leadsto>\<^bsub>n\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
       makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
      using makes_compatible_invariant
      by blast
    thus ?case
      using IH eval'' meval_sched_snocI sound_modes_invariant
      by metis
  qed
qed

lemma differing_vars_initially_empty:
  "i < n \<Longrightarrow> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 (zip (replicate n mem\<^sub>1) (replicate n mem\<^sub>2)) i"
  unfolding differing_vars_lists_def differing_vars_def
  by auto

lemma compatible_refl:
  assumes coms_secure: "list_all com_sifum_secure cmds"
  assumes low_eq: "mem\<^sub>1 =\<^sup>l mem\<^sub>2"
  shows "makes_compatible (cmds, mem\<^sub>1)
                          (cmds, mem\<^sub>2)
                          (replicate (length cmds) (mem\<^sub>1, mem\<^sub>2))"
proof -
  let ?n = "length cmds"
  let ?mems = "replicate ?n (mem\<^sub>1, mem\<^sub>2)" and
      ?mdss = "map snd cmds"
  let ?X = "differing_vars_lists mem\<^sub>1 mem\<^sub>2 ?mems"
  have diff_empty: "\<forall> i < ?n. ?X i = {}"
    by (metis differing_vars_initially_empty ex_in_conv min.idem zip_replicate)

  show ?thesis
  proof
    show "length cmds = length cmds \<and> length cmds = length ?mems"
      by auto
  next
    fix i and \<sigma> :: "'Var \<Rightarrow> 'Val option"
    let ?mems\<^sub>1i = "fst (?mems ! i)" and ?mems\<^sub>2i = "snd (?mems ! i)"
    let ?mdss\<^sub>i = "?mdss ! i"
    assume i: "i < length cmds"
    assume dom\<sigma>: "dom \<sigma> =
                  differing_vars_lists mem\<^sub>1 mem\<^sub>2
                                      (replicate (length cmds) (mem\<^sub>1, mem\<^sub>2)) i"
    from i have "?mems\<^sub>1i = mem\<^sub>1" "?mems\<^sub>2i = mem\<^sub>2"
      by auto

    with dom\<sigma> have [simp]: "dom \<sigma> = {}" by(auto simp: differing_vars_lists_def differing_vars_def i)

    from i coms_secure have "com_sifum_secure (cmds ! i)"
      using coms_secure
      by (metis length_map length_replicate list_all_length map_snd_zip)
    with i have "\<And> mem\<^sub>1 mem\<^sub>2. mem\<^sub>1 =\<^bsub>?mdss\<^sub>i\<^esub>\<^sup>l mem\<^sub>2 \<Longrightarrow>
      (cmds ! i, mem\<^sub>1) \<approx> (cmds ! i, mem\<^sub>2)"
      using com_sifum_secure_def low_indistinguishable_def
      by auto

    moreover
    have "\<And>x. \<sigma> x = None" using \<open>dom \<sigma> = {}\<close>
      by (metis domIff empty_iff)
    hence [simp]: "\<And> mem. mem [\<mapsto> \<sigma>] = mem"
      by(simp add: subst_def)

    from i have "?mems\<^sub>1i = mem\<^sub>1" "?mems\<^sub>2i = mem\<^sub>2"
      by auto
    with low_eq have "?mems\<^sub>1i [\<mapsto> \<sigma>] =\<^bsub>?mdss\<^sub>i\<^esub>\<^sup>l ?mems\<^sub>2i [\<mapsto> \<sigma>]"
      by (auto simp: low_mds_eq_def low_eq_def)

    ultimately show "(cmds ! i, ?mems\<^sub>1i [\<mapsto> \<sigma>]) \<approx> (cmds ! i, ?mems\<^sub>2i [\<mapsto> \<sigma>])"
      by simp
  next
    fix i x
    assume "i < length cmds"
    with diff_empty show "x \<notin> ?X i" by auto
  next
    show "(length cmds = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or> (\<forall> x. \<exists> i < length cmds. x \<notin> ?X i)"
      using diff_empty
      by (metis bot_less bot_nat_def empty_iff length_zip low_eq min_0L)
  qed
qed

theorem sifum_compositionality_cont:
  assumes com_secure: "list_all com_sifum_secure cmds"
  assumes sound_modes: "\<forall> mem. INIT mem \<longrightarrow> sound_mode_use (cmds, mem)"
  shows "prog_sifum_secure_cont cmds"
  unfolding prog_sifum_secure_cont_def
  using assms
proof (clarify)
  fix mem\<^sub>1 mem\<^sub>2 :: "'Var \<Rightarrow> 'Val"
  fix sched cms\<^sub>1' mem\<^sub>1'
  let ?n = "length cmds"
  let ?mems = "zip (replicate ?n mem\<^sub>1) (replicate ?n mem\<^sub>2)"
  assume INIT\<^sub>1: "INIT mem\<^sub>1" and INIT\<^sub>2: "INIT mem\<^sub>2"
  assume low_eq: "mem\<^sub>1 =\<^sup>l mem\<^sub>2"
  with com_secure have compat:
    "makes_compatible (cmds, mem\<^sub>1) (cmds, mem\<^sub>2) ?mems"
    by (metis compatible_refl fst_conv length_replicate map_replicate snd_conv zip_eq_conv INIT\<^sub>1 INIT\<^sub>2)

  also assume eval: "(cmds, mem\<^sub>1) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>1', mem\<^sub>1')"

  ultimately obtain cms\<^sub>2' mem\<^sub>2' mems'
    where p: "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
             (cmds, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
             makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
    using sound_modes makes_compatible_eval_sched INIT\<^sub>1 INIT\<^sub>2
    by blast

  thus "\<exists> cms\<^sub>2' mem\<^sub>2'. (cmds, mem\<^sub>2) \<rightarrow>\<^bsub>sched\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                        map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                        length cms\<^sub>2' = length cms\<^sub>1' \<and>
                        (\<forall> x. dma mem\<^sub>1' x = Low \<and> (x \<in> \<C> \<or> (\<forall> i < length cms\<^sub>1'. x \<notin> snd (cms\<^sub>1' ! i) AsmNoReadOrWrite))
          \<longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x)"
    using p compat_low_eq
    by (metis length_map)
qed

end

end
