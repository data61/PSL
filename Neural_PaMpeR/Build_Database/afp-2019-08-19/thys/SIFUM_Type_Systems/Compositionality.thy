(*
Title: SIFUM-Type-Systems
Authors: Sylvia Grewe, Heiko Mantel, Daniel Schoepe
*)
section \<open>Compositionality Proof for SIFUM-Security Property\<close>

theory Compositionality
imports Main Security
begin

context sifum_security
begin

(* Set of variables that differs between two memory states: *)
definition differing_vars :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow> 'Var set"
  where
  "differing_vars mem\<^sub>1 mem\<^sub>2 = {x. mem\<^sub>1 x \<noteq> mem\<^sub>2 x}"

definition differing_vars_lists :: "('Var, 'Val) Mem \<Rightarrow> (_, _) Mem \<Rightarrow>
  ((_, _) Mem \<times> (_, _) Mem) list \<Rightarrow> nat \<Rightarrow> 'Var set"
  where
  "differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i =
   (differing_vars mem\<^sub>1 (fst (mems ! i)) \<union> differing_vars mem\<^sub>2 (snd (mems ! i)))"

lemma differing_finite: "finite (differing_vars mem\<^sub>1 mem\<^sub>2)"
  by (metis UNIV_def Un_UNIV_left finite_Un finite_memory)

lemma differing_lists_finite: "finite (differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)"
  by (simp add: differing_finite differing_vars_lists_def)

(* Suggestive notation for substitution / function application *)
definition subst :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)"
  where
  "subst f mem = (\<lambda> x. case f x of
                         None \<Rightarrow> mem x |
                         Some v \<Rightarrow> v)"

abbreviation subst_abv :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("_ [\<mapsto>_]" [900, 0] 1000)
  where
  "f [\<mapsto> \<sigma>] \<equiv> subst \<sigma> f"

lemma subst_not_in_dom : "\<lbrakk> x \<notin> dom \<sigma> \<rbrakk> \<Longrightarrow> mem [\<mapsto> \<sigma>] x = mem x"
  by (simp add: domIff subst_def)

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
       (\<forall> x. (mem\<^sub>1 x = mem\<^sub>2 x \<or> dma x = High) \<longrightarrow>
             x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)) \<and>
    ((length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or> (\<forall> x. \<exists> i. i < length cms\<^sub>1 \<and>
                                          x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i)))"

(* This just restates the previous definition using meta-quantification. This allows
  more readable proof blocks that prove each part separately. *)
lemma makes_compatible_intro [intro]:
  "\<lbrakk> length cms\<^sub>1 = length cms\<^sub>2 \<and> length cms\<^sub>1 = length mems;
     (\<And> i \<sigma>. \<lbrakk> i < length cms\<^sub>1; dom \<sigma> = differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow>
          (cms\<^sub>1 ! i, (fst (mems ! i)) [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! i, (snd (mems ! i)) [\<mapsto> \<sigma>]));
     (\<And> i x. \<lbrakk> i < length cms\<^sub>1; mem\<^sub>1 x = mem\<^sub>2 x \<or> dma x = High \<rbrakk> \<Longrightarrow> 
          x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i);
     (length cms\<^sub>1 = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or>
     (\<forall> x. \<exists> i. i < length cms\<^sub>1 \<and> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i) \<rbrakk> \<Longrightarrow>
  makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  by auto

(* First, some auxiliary lemmas about makes_compatible: *)
lemma compat_low:
  "\<lbrakk> makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems;
     i < length cms\<^sub>1;
     x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow> dma x = Low"
proof -
  assume "i < length cms\<^sub>1" and *: "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i" and
    "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  then have
    "(mem\<^sub>1 x = mem\<^sub>2 x \<or> dma x = High) \<longrightarrow> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
    by (simp add: Let_def, blast)
  with * show "dma x = Low"
    by (cases "dma x") blast
qed

lemma compat_different:
  "\<lbrakk> makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems;
     i < length cms\<^sub>1;
     x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i \<rbrakk> \<Longrightarrow> mem\<^sub>1 x \<noteq> mem\<^sub>2 x \<and> dma x = Low"
  by (cases "dma x", auto)

lemma sound_modes_no_read :
  "\<lbrakk> sound_mode_use (cms, mem); x \<in> (map snd cms ! i) GuarNoRead; i < length cms \<rbrakk> \<Longrightarrow>
  doesnt_read (fst (cms ! i)) x"
proof -
  fix cms mem x i
  assume sound_modes: "sound_mode_use (cms, mem)" and "i < length cms"
  hence "locally_sound_mode_use (cms ! i, mem)"
    by (auto simp: sound_mode_use_def list_all_length)
  moreover
  assume "x \<in> (map snd cms ! i) GuarNoRead"
  ultimately show "doesnt_read (fst (cms !i)) x"
    apply (simp add: locally_sound_mode_use_def)
    by (metis prod.exhaust \<open>i < length cms\<close> fst_conv loc_reach.refl nth_map snd_conv)
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
  by (simp add: globally_sound_mode_use_def reachable_mode_states_def, auto)

(* map snd cms1 = map snd cms2 states that both global configurations use the same modes *)
lemma compatible_different_no_read :
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)"
                       "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes ile: "i < length cms\<^sub>1"
  assumes x: "x \<in> differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  shows "doesnt_read (fst (cms\<^sub>1 ! i)) x \<and> doesnt_read (fst (cms\<^sub>2 ! i)) x"
proof -
  from compat have len: "length cms\<^sub>1 = length cms\<^sub>2"
    by simp

  let ?X\<^sub>i = "differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"

  from compat ile x have a: "dma x = Low"
    by (metis compat_low)

  from compat ile x have b: "mem\<^sub>1 x \<noteq> mem\<^sub>2 x"
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

  with jprop and b have "x \<in> (?mdss ! j) AsmNoRead"
  proof -
    { assume "x \<notin> (?mdss ! j) AsmNoRead"
      then have mems_eq: "?mems\<^sub>1j x = ?mems\<^sub>2j x"
        using \<open>dma x = Low\<close> low_eq subst_eq
        by (metis (full_types) low_mds_eq_def subst_eq)

      hence "mem\<^sub>1 x = mem\<^sub>2 x"
        by (metis compat_different_vars jprop)

      hence False by (metis b)
    }
    thus ?thesis by metis
  qed

  hence "x \<in> (?mdss ! i) GuarNoRead"
    using sound_modes jprop
    by (metis compatible_modes_def globally_sound_modes_compatible
      length_map sound_mode_use.simps x ile)

  thus "doesnt_read (fst (cms\<^sub>1 ! i)) x \<and> doesnt_read (fst (cms\<^sub>2 ! i)) x" using sound_modes ile
    by (metis len modes_eq sound_modes_no_read)
qed

definition func_le :: "('a \<rightharpoonup> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b) \<Rightarrow> bool" (infixl "\<preceq>" 60)
  where "f \<preceq> g = (\<forall> x \<in> dom f. f x = g x)"

fun change_respecting ::
  "('Com, 'Var, 'Val) LocalConf \<Rightarrow>
   ('Com, 'Var, 'Val) LocalConf \<Rightarrow>
   'Var set \<Rightarrow>
   (('Var \<rightharpoonup> 'Val) \<Rightarrow>
   ('Var \<rightharpoonup> 'Val)) \<Rightarrow> bool"
  where "change_respecting (cms, mem) (cms', mem') X g =
      ((cms, mem) \<leadsto> (cms', mem') \<and>
       (\<forall> \<sigma>. dom \<sigma> = X \<longrightarrow> g \<sigma> \<preceq> \<sigma>) \<and>
       (\<forall> \<sigma> \<sigma>'. dom \<sigma> = X \<and> dom \<sigma>' = X \<longrightarrow> dom (g \<sigma>) = dom (g \<sigma>')) \<and>
       (\<forall> \<sigma>. dom \<sigma> = X \<longrightarrow> (cms, mem [\<mapsto> \<sigma>]) \<leadsto> (cms', mem' [\<mapsto> g \<sigma>])))"

lemma change_respecting_dom_unique:
  "\<lbrakk> change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X g \<rbrakk> \<Longrightarrow>
   \<exists> d. \<forall> f. dom f = X \<longrightarrow> d = dom (g f)"
  by (metis change_respecting.simps)

lemma func_le_restrict: "\<lbrakk> f \<preceq> g; X \<subseteq> dom f \<rbrakk> \<Longrightarrow> f |` X \<preceq> g"
  by (auto simp: func_le_def)

definition to_partial :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<rightharpoonup> 'b)"
  where "to_partial f = (\<lambda> x. Some (f x))"

lemma func_le_dom: "f \<preceq> g \<Longrightarrow> dom f \<subseteq> dom g"
  by (auto simp add: func_le_def, metis domIff option.simps(2))

lemma doesnt_read_mutually_exclusive:
  assumes noread: "doesnt_read c x"
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  assumes unchanged: "\<forall> v. \<langle>c, mds, mem (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' (x := v)\<rangle>"
  shows "\<not> (\<forall> v. \<langle>c, mds, mem (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>)"
  using assms
  apply (case_tac "mem' x = some_val")
   apply (metis (full_types) prod.inject deterministic different_values fun_upd_same)
  by (metis (full_types) prod.inject deterministic fun_upd_same)

lemma doesnt_read_mutually_exclusive':
  assumes noread: "doesnt_read c x"
  assumes eval: "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  assumes overwrite: "\<forall> v. \<langle>c, mds, mem (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>"
  shows "\<not> (\<forall> v. \<langle>c, mds, mem (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' (x := v)\<rangle>)"
  by (metis assms doesnt_read_mutually_exclusive)

lemma change_respecting_dom:
  assumes cr: "change_respecting (cms, mem) (cms', mem') X g"
  assumes dom\<sigma>: "dom \<sigma> = X"
  shows "dom (g \<sigma>) \<subseteq> X"
  by (metis assms change_respecting.simps func_le_dom)
  
lemma change_respecting_intro [iff]:
  "\<lbrakk> \<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>;
     \<And> f. dom f = X \<Longrightarrow>
           g f \<preceq> f \<and>
           (\<forall> f'. dom f' = X \<longrightarrow> dom (g f) = dom (g f')) \<and>
           (\<langle> c, mds, mem [\<mapsto> f] \<rangle> \<leadsto> \<langle> c', mds', mem' [\<mapsto> g f] \<rangle>) \<rbrakk>
  \<Longrightarrow> change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X g"
  unfolding change_respecting.simps
  by blast

(* Used for a proof block in the following lemma *)
lemma conjI3: "\<lbrakk> A; B; C \<rbrakk> \<Longrightarrow> A \<and> B \<and> C"
  by simp

lemma noread_exists_change_respecting:
  assumes fin: "finite (X :: 'Var set)"
  assumes eval: "\<langle> c, mds, mem \<rangle> \<leadsto> \<langle> c', mds', mem' \<rangle>"
  assumes noread: "\<forall> x \<in> X. doesnt_read c x"
  shows "\<exists> (g :: ('Var \<rightharpoonup> 'Val) \<Rightarrow> ('Var \<rightharpoonup> 'Val)).  change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X g"
proof -
  let ?lc = "\<langle>c, mds, mem\<rangle>" and ?lc' = "\<langle>c', mds', mem'\<rangle>"
  from fin eval noread show "\<exists> g. change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X g"
  proof (induct "X" arbitrary: mem mem' rule: finite_induct)
    case empty
    let ?g = "\<lambda> \<sigma>. Map.empty"
    have "mem [\<mapsto> Map.empty] = mem" "mem' [\<mapsto> ?g Map.empty] = mem'"
      unfolding subst_def
      by auto
    hence "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> {} ?g"
      using empty
      unfolding change_respecting.simps func_le_def subst_def
      by auto
    thus ?case by auto
  next
    case (insert x X)
    then obtain g\<^sub>X where IH: "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> X g\<^sub>X"
      by (metis insert_iff)
    (* Unfortunately, it is necessary to define the required function in advance for
       all case distinctions we want to make. *)
    define g where "g \<sigma> =
       (let \<sigma>' = \<sigma> |` X in
        (if (\<forall> v. \<langle>c, mds, mem [\<mapsto> \<sigma>'] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X \<sigma>'] (x := v)\<rangle>)
         then (\<lambda> y :: 'Var.
                    if x = y
                    then \<sigma> y
                    else g\<^sub>X \<sigma>' y)
         else (\<lambda> y. g\<^sub>X \<sigma>' y)))"
      for \<sigma> :: "'Var \<rightharpoonup> 'Val"
    have "change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> (insert x X) g"
    proof
      show "\<langle>c, mds, mem\<rangle> \<leadsto> \<langle>c', mds', mem'\<rangle>" using insert by auto
    next \<comment> \<open>We first show that property (2) is satisfied.\<close>
      fix \<sigma> :: "'Var \<rightharpoonup> 'Val"
      let ?\<sigma>\<^sub>X = "\<sigma> |` X"
      assume "dom \<sigma> = insert x X"
      hence "dom ?\<sigma>\<^sub>X = X"
        by (metis dom_restrict inf_absorb2 subset_insertI)
      from insert have "doesnt_read c x" by auto
      moreover
      from IH have eval\<^sub>X: "\<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>"
        using \<open>dom ?\<sigma>\<^sub>X = X\<close>
        unfolding change_respecting.simps
        by auto
      ultimately have
        noread\<^sub>x:
        "(\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v) \<rangle>) \<or>
        (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>)"
        unfolding doesnt_read_def by auto
      show "g \<sigma> \<preceq> \<sigma> \<and>
            (\<forall> \<sigma>'. dom \<sigma>' = insert x X \<longrightarrow> dom (g \<sigma>) = dom (g \<sigma>')) \<and>
            \<langle>c, mds, mem [\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g \<sigma>]\<rangle>"
      proof (rule conjI3)
        from noread\<^sub>x show "g \<sigma> \<preceq> \<sigma>"
        proof
          assume nowrite: "\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto>
                 \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>"
          then have g_simp [simp]: "g \<sigma> = (\<lambda> y. if y = x then \<sigma> y else g\<^sub>X ?\<sigma>\<^sub>X y)"
            unfolding g_def
            by auto
          thus "g \<sigma> \<preceq> \<sigma>"
            using IH
            unfolding g_simp func_le_def
            by (auto, metis \<open>dom (\<sigma> |` X) = X\<close> domI func_le_def restrict_in)
        next
          assume overwrites: "\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto>
            \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>"
          hence
            "\<not> (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>)"
            by (metis \<open>doesnt_read c x\<close> doesnt_read_mutually_exclusive eval\<^sub>X)
          hence g_simp [simp]: "g \<sigma> = g\<^sub>X ?\<sigma>\<^sub>X"
            unfolding g_def
            by (auto simp: Let_def)

          also from IH have "g\<^sub>X ?\<sigma>\<^sub>X \<preceq> ?\<sigma>\<^sub>X"
            by (metis \<open>dom (\<sigma> |` X) = X\<close> change_respecting.simps)

          ultimately show "g \<sigma> \<preceq> \<sigma>"
            unfolding func_le_def
            by (auto, metis \<open>dom (\<sigma> |` X) = X\<close> domI restrict_in)
        qed
      next \<comment> \<open>This part proves that the domain of the family is unique\<close>
        {
        fix \<sigma>' :: "'Var \<rightharpoonup> 'Val"
        assume "dom \<sigma>' = insert x X"
        let ?\<sigma>'\<^sub>X = "\<sigma>' |` X"
        have "dom ?\<sigma>'\<^sub>X = X"
          by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> \<open>dom \<sigma>' = insert x X\<close> dom_restrict)
        \<comment> \<open>We first show, that we are always in the same case of the no read assumption:\<close>
        have same_case:
          "((\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>) \<and>
            (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X] (x := v)\<rangle>))
           \<or>
           ((\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>) \<and>
            (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X]\<rangle>))"
          (is "(?N \<and> ?N') \<or> (?O \<and> ?O')")
        proof -
          \<comment> \<open>By deriving a contradiction under the assumption that we are in different cases:\<close>
          have not_different:
            "\<And> h h'. \<lbrakk> dom h = insert x X; dom h' = insert x X;
                        \<forall> v. \<langle>c, mds, mem [\<mapsto> h |` X] (x := v)\<rangle> \<leadsto>
                             \<langle>c', mds', mem' [\<mapsto> g\<^sub>X (h |` X)] (x := v)\<rangle>;
                        \<forall> v. \<langle>c, mds, mem [\<mapsto> h' |` X] (x := v)\<rangle> \<leadsto>
                             \<langle>c', mds', mem' [\<mapsto> g\<^sub>X (h' |` X)]\<rangle> \<rbrakk>
                      \<Longrightarrow> False"
          proof -
            \<comment> \<open>Introduce new names to avoid clashes with functions in the outer scope.\<close>
            fix h h' :: "'Var \<rightharpoonup> 'Val"
            assume doms: "dom h = insert x X" "dom h' = insert x X"
            assume nowrite: "\<forall> v. \<langle>c, mds, mem [\<mapsto> h |` X] (x := v)\<rangle> \<leadsto>
              \<langle>c', mds', mem' [\<mapsto> g\<^sub>X (h |` X)] (x := v)\<rangle>"
            assume overwrite: "\<forall> v. \<langle>c, mds, mem [\<mapsto> h' |` X] (x := v)\<rangle> \<leadsto>
              \<langle>c', mds', mem' [\<mapsto> g\<^sub>X (h' |` X)]\<rangle>"

            let ?h\<^sub>X = "h |` X"
            let ?h'\<^sub>X = "h' |` X"

            have "dom ?h\<^sub>X = X"
              by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> dom_restrict doms(1))
            have "dom ?h'\<^sub>X = X"
              by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> dom_restrict doms(2))

            with IH have eval\<^sub>X': "\<langle>c, mds, mem [\<mapsto> ?h'\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?h'\<^sub>X]\<rangle>"
              unfolding change_respecting.simps
              by auto
            with \<open>doesnt_read c x\<close> have noread\<^sub>x':
             "(\<forall> v. \<langle>c, mds, mem [\<mapsto> ?h'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?h'\<^sub>X] (x := v)\<rangle>) \<or>
              (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?h'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?h'\<^sub>X]\<rangle>)"
              unfolding doesnt_read_def
              by auto

            from overwrite obtain v where
              "\<not> (\<langle>c, mds, mem [\<mapsto> h' |` X] (x := v)\<rangle> \<leadsto>
              \<langle>c', mds', mem' [\<mapsto> g\<^sub>X (h' |` X)] (x := v)\<rangle>)"
              by (metis \<open>doesnt_read c x\<close> doesnt_read_mutually_exclusive fun_upd_triv)
            moreover

            have "x \<notin> dom (?h'\<^sub>X)"
              by (metis \<open>dom (h' |` X) = X\<close> insert(2))
            with IH have "x \<notin> dom (g\<^sub>X ?h'\<^sub>X)"
              by (metis \<open>dom (h' |` X) = X\<close> change_respecting.simps func_le_dom rev_subsetD)

            ultimately have "mem' x \<noteq> v"
              by (metis fun_upd_triv overwrite subst_not_in_dom)

            let ?mem\<^sub>v = "mem (x := v)"

            obtain mem\<^sub>v' where "\<langle>c, mds, ?mem\<^sub>v\<rangle> \<leadsto> \<langle>c', mds', mem\<^sub>v'\<rangle>"
              using insert \<open>doesnt_read c x\<close>
              unfolding doesnt_read_def
              by (auto, metis)
            also have "\<forall> x \<in> X. doesnt_read c x"
              by (metis insert(5) insert_iff)
              
            ultimately obtain g\<^sub>v where
              IH\<^sub>v: "change_respecting \<langle>c, mds, ?mem\<^sub>v\<rangle> \<langle>c', mds', mem\<^sub>v'\<rangle> X g\<^sub>v"
              by (metis insert(3))

            hence eval\<^sub>v: "\<langle>c, mds, ?mem\<^sub>v [\<mapsto> ?h\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem\<^sub>v' [\<mapsto> g\<^sub>v ?h\<^sub>X]\<rangle>"
                         "\<langle>c, mds, ?mem\<^sub>v [\<mapsto> ?h'\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem\<^sub>v' [\<mapsto> g\<^sub>v ?h'\<^sub>X]\<rangle>"
              apply (metis \<open>dom (h |` X) = X\<close> change_respecting.simps)
              by (metis IH\<^sub>v \<open>dom (h' |` X) = X\<close> change_respecting.simps)

            from eval\<^sub>v(1) have "mem\<^sub>v' x = v"
            proof -
              assume "\<langle>c, mds, mem (x := v) [\<mapsto> ?h\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem\<^sub>v' [\<mapsto> g\<^sub>v ?h\<^sub>X]\<rangle>"
              have "?mem\<^sub>v [\<mapsto> ?h\<^sub>X] = mem [\<mapsto> ?h\<^sub>X] (x := v)"
                apply (rule ext, rename_tac y)
                apply (case_tac "y = x")
                 apply (auto simp: subst_def)
                 apply (metis (full_types) \<open>dom (h |` X) = X\<close> fun_upd_def
                  insert(2) subst_def subst_not_in_dom)
                by (metis fun_upd_other)

              with nowrite have "mem\<^sub>v' [\<mapsto> g\<^sub>v ?h\<^sub>X] = mem' [\<mapsto> g\<^sub>X ?h\<^sub>X] (x := v)"
                using deterministic
                by (erule_tac x = v in allE, auto, metis eval\<^sub>v(1))

              hence "mem\<^sub>v' [\<mapsto> g\<^sub>v ?h\<^sub>X] x = v"
                by simp
              also have "x \<notin> dom (g\<^sub>v ?h\<^sub>X)"
                using IH\<^sub>v \<open>dom ?h\<^sub>X = X\<close> change_respecting_dom
                by (metis func_le_dom insert(2) rev_subsetD)
              ultimately show "mem\<^sub>v' x = v"
                by (metis subst_not_in_dom)
            qed
            moreover
            from eval\<^sub>v(2) have "mem\<^sub>v' x = mem' x"
            proof -
              assume "\<langle>c, mds, ?mem\<^sub>v [\<mapsto> ?h'\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem\<^sub>v' [\<mapsto> g\<^sub>v ?h'\<^sub>X]\<rangle>"
              moreover
              from overwrite have
                "\<langle>c, mds, mem [\<mapsto> ?h'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?h'\<^sub>X]\<rangle>"
                by auto
              moreover
              have "?mem\<^sub>v [\<mapsto> ?h'\<^sub>X] = mem [\<mapsto> ?h'\<^sub>X] (x := v)"
                apply (rule ext, rename_tac "y")
                apply (case_tac "y = x")
                 apply (metis \<open>x \<notin> dom (h' |` X)\<close> fun_upd_apply subst_not_in_dom)
                apply (auto simp: subst_def)
                by (metis fun_upd_other)
              ultimately have "mem' [\<mapsto> g\<^sub>X ?h'\<^sub>X] = mem\<^sub>v' [\<mapsto> g\<^sub>v ?h'\<^sub>X]"
                using deterministic
                by auto
              also have "x \<notin> dom (g\<^sub>v ?h'\<^sub>X)"
                using IH\<^sub>v \<open>dom ?h'\<^sub>X = X\<close> change_respecting_dom
                by (metis func_le_dom insert(2) subsetD)
              ultimately show "mem\<^sub>v' x = mem' x"
                using \<open>x \<notin> dom (g\<^sub>X ?h'\<^sub>X)\<close>
                by (metis subst_not_in_dom)
            qed
            ultimately show False
              using \<open>mem' x \<noteq> v\<close>
              by auto
          qed

          moreover
          have "dom ?\<sigma>'\<^sub>X = X"
            by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> \<open>dom \<sigma>' = insert x X\<close> dom_restrict)

          with IH have eval\<^sub>X': "\<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X]\<rangle>"
            unfolding change_respecting.simps
            by auto
          with \<open>doesnt_read c x\<close> have noread\<^sub>x':
             "(\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X] (x := v)\<rangle>)
              \<or>
              (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X]\<rangle>)"
            unfolding doesnt_read_def
            by auto

          ultimately show ?thesis
            using noread\<^sub>x not_different \<open>dom \<sigma> = insert x X\<close> \<open>dom \<sigma>' = insert x X\<close>
            by auto
        qed
        hence "dom (g \<sigma>) = dom (g \<sigma>')"
        proof
          assume
            "(\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>) \<and>
            (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X] (x := v)\<rangle>)"
          hence g_simp [simp]: "g \<sigma> = (\<lambda> y. if y = x then \<sigma> y else g\<^sub>X ?\<sigma>\<^sub>X y) \<and>
                                g \<sigma>' = (\<lambda> y. if y = x then \<sigma>' y else g\<^sub>X ?\<sigma>'\<^sub>X y)"
            unfolding g_def
            by auto
          thus ?thesis
            using IH \<open>dom \<sigma> = insert x X\<close> \<open>dom \<sigma>' = insert x X\<close>
            unfolding change_respecting.simps
            apply (auto simp: domD)
             apply (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom (\<sigma>' |` X) = X\<close> domD domI)
            by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom (\<sigma>' |` X) = X\<close> domD domI)
        next
          assume
            "(\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>) \<and>
            (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X]\<rangle>)"
          hence
            "\<not> (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>)
            \<and>
            \<not> (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>'\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>'\<^sub>X] (x := v)\<rangle>)"
            by (metis \<open>doesnt_read c x\<close> doesnt_read_mutually_exclusive' fun_upd_triv)

          hence g_simp [simp]: "g \<sigma> = g\<^sub>X ?\<sigma>\<^sub>X \<and> g \<sigma>' = g\<^sub>X ?\<sigma>'\<^sub>X"
            unfolding g_def
            by (auto simp: Let_def)
          with IH show ?thesis
            unfolding change_respecting.simps
            by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom (\<sigma>' |` X) = X\<close>)
        qed
      }
      thus "\<forall> \<sigma>'. dom \<sigma>' = insert x X \<longrightarrow> dom (g \<sigma>) = dom (g \<sigma>')" by blast
    next
      (* Do a case distinction on the no-read statement: *)
      from noread\<^sub>x show "\<langle>c, mds, mem [\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g \<sigma>]\<rangle>"
      proof
        assume nowrite:
          "\<forall> v. \<langle>c, mds, mem[\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>"
        then have g_simp [simp]: "g \<sigma> = (\<lambda> y. if y = x then \<sigma> y else g\<^sub>X ?\<sigma>\<^sub>X y)"
          unfolding g_def
          by auto
        obtain v where "\<sigma> x = Some v"
          by (metis \<open>dom \<sigma> = insert x X\<close> domD insertI1)

        from nowrite have
          "\<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>"
          by auto
        moreover
        have "mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v) = mem [\<mapsto> \<sigma>]"
          apply (rule ext, rename_tac y)
          apply (case_tac "y = x")
           apply (auto simp: subst_def)
           apply (metis \<open>\<sigma> x = Some v\<close> option.simps(5))
          by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> insertE
            restrict_in subst_def subst_not_in_dom)
        moreover
        have "mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v) = mem' [\<mapsto> g \<sigma>]"
          apply (rule ext, rename_tac y)
          apply (case_tac "y = x")
           by (auto simp: subst_def option.simps \<open>\<sigma> x = Some v\<close>)
        ultimately show ?thesis
          by auto
      next
        assume overwrites:
          "\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X]\<rangle>"
        hence
          "\<not> (\<forall> v. \<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g\<^sub>X ?\<sigma>\<^sub>X] (x := v)\<rangle>)"
          by (metis \<open>doesnt_read c x\<close> doesnt_read_mutually_exclusive' eval\<^sub>X)
        hence g_simp [simp]: "g \<sigma> = g\<^sub>X ?\<sigma>\<^sub>X"
          unfolding g_def
          by (auto simp: Let_def)
        obtain v where "\<sigma> x = Some v"
          by (metis \<open>dom \<sigma> = insert x X\<close> domD insertI1)
        have "mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v) = mem [\<mapsto> \<sigma>]"
          apply (rule ext, rename_tac y)
          apply (case_tac "y = x")
           apply (auto simp: subst_def)
           apply (metis \<open>\<sigma> x = Some v\<close> option.simps(5))
          by (metis \<open>dom (\<sigma> |` X) = X\<close> \<open>dom \<sigma> = insert x X\<close> insertE
            restrict_in subst_def subst_not_in_dom)
        moreover
        from overwrites have "\<langle>c, mds, mem [\<mapsto> ?\<sigma>\<^sub>X] (x := v)\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g \<sigma>]\<rangle>"
          by (metis g_simp)
        ultimately show "\<langle>c, mds, mem [\<mapsto> \<sigma>]\<rangle> \<leadsto> \<langle>c', mds', mem' [\<mapsto> g \<sigma>]\<rangle>"
            by auto
        qed
      qed
    qed
    thus "\<exists> g. change_respecting \<langle>c, mds, mem\<rangle> \<langle>c', mds', mem'\<rangle> (insert x X) g"
      by metis
  qed
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

lemma subst_overrides: "dom \<sigma> = dom \<tau> \<Longrightarrow> mem [\<mapsto> \<tau>] [\<mapsto> \<sigma>] = mem [\<mapsto> \<sigma>]"
  unfolding subst_def
  by (metis domIff option.exhaust option.simps(4) option.simps(5))

lemma dom_restrict_total: "dom (to_partial f |` X) = X"
  unfolding to_partial_def
  by (metis Int_UNIV_left dom_const dom_restrict)

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
  assumes cr: "change_respecting (cms, mem) (cms', mem') X g"
  assumes eval: "(cms, mem) \<leadsto> (cms', mem')"
  assumes domf: "dom f = X"
  assumes x_in_dom: "x \<in> dom (g f)"
  assumes noread: "doesnt_read (fst cms) x"
  shows "mem x = mem' x"
proof -
  let ?f' = "to_partial mem |` X"
  have domf': "dom ?f' = X"
    by (metis dom_restrict_total)

  from cr and eval have "\<forall> f. dom f = X \<longrightarrow> (cms, mem [\<mapsto> f]) \<leadsto> (cms', mem' [\<mapsto> g f])"
    unfolding change_respecting.simps
    by metis
  hence eval': "(cms, mem [\<mapsto> ?f']) \<leadsto> (cms', mem' [\<mapsto> g ?f'])"
    by (metis domf')

  have mem_eq: "mem [\<mapsto> ?f'] = mem"
  proof
    fix x
    show "mem [\<mapsto> ?f'] x = mem x"
      unfolding subst_def
      apply (cases "x \<in> X")
       apply (metis option.simps(5) restrict_in to_partial_def)
      by (metis domf' subst_def subst_not_in_dom)
  qed

  then have mem'_eq: "mem' [\<mapsto> g ?f'] = mem'"
    using eval eval' deterministic
    by (metis Pair_inject)

  moreover
  have "dom (g ?f') = dom (g f)"
    by (metis change_respecting.simps cr domf domf')
  hence x_in_dom': "x \<in> dom (g ?f')"
    by (metis x_in_dom)
  have "x \<in> X"
    by (metis change_respecting.simps cr domf func_le_dom in_mono x_in_dom)
  hence "?f' x = Some (mem x)"
    by (metis restrict_in to_partial_def)
  hence "g ?f' x = Some (mem x)"
    using cr func_le_def
    by (metis change_respecting.simps domf' x_in_dom')

  hence "mem' [\<mapsto> g ?f'] x = mem x"
    using subst_def x_in_dom'
    by (metis option.simps(5))
  thus "mem x = mem' x"
    by (metis mem'_eq)
qed

(* Some machinery for making use of closedness under globally consistent changes:
   - We introduce the notion of an "adaptation" that replaces (finitely many)
     variables in two memory states with (possibly different) other values.
   - We then define a function to apply adaptations to memory states
*)

type_synonym ('var, 'val) adaptation = "'var \<rightharpoonup> ('val \<times> 'val)"

definition apply_adaptation ::
  "bool \<Rightarrow> ('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  where "apply_adaptation first mem A =
         (\<lambda> x. case (A x) of
               Some (v\<^sub>1, v\<^sub>2) \<Rightarrow> if first then v\<^sub>1 else v\<^sub>2
             | None \<Rightarrow> mem x)"

abbreviation apply_adaptation\<^sub>1 ::
  "('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  ("_ [\<parallel>\<^sub>1 _]" [900, 0] 1000)
  where "mem [\<parallel>\<^sub>1 A] \<equiv> apply_adaptation True mem A"

abbreviation apply_adaptation\<^sub>2 ::
  "('Var, 'Val) Mem \<Rightarrow> ('Var, 'Val) adaptation \<Rightarrow> ('Var, 'Val) Mem"
  ("_ [\<parallel>\<^sub>2 _]" [900, 0] 1000)
  where "mem [\<parallel>\<^sub>2 A] \<equiv> apply_adaptation False mem A"

definition restrict_total :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a set \<Rightarrow> 'a \<rightharpoonup> 'b" (*infix "|'" 60*)
  where "restrict_total f A = to_partial f |` A"

lemma differing_empty_eq:
  "\<lbrakk> differing_vars mem mem' = {} \<rbrakk> \<Longrightarrow> mem = mem'"
  unfolding differing_vars_def
  by auto

definition globally_consistent_var :: "('Var, 'Val) adaptation \<Rightarrow> 'Var Mds \<Rightarrow> 'Var \<Rightarrow> bool"
  where "globally_consistent_var A mds x \<equiv>
  (case A x of
     Some (v, v') \<Rightarrow> x \<notin> mds AsmNoWrite \<and> (dma x = Low \<longrightarrow> v = v')
   | None \<Rightarrow> True)"

definition globally_consistent  :: "('Var, 'Val) adaptation \<Rightarrow> 'Var Mds \<Rightarrow> bool"
  where "globally_consistent A mds \<equiv> finite (dom A) \<and>
  (\<forall> x \<in> dom A. globally_consistent_var A mds x)"

definition gc2 :: "('Var, 'Val) adaptation \<Rightarrow> 'Var Mds \<Rightarrow> bool"
  where "gc2 A mds = (\<forall> x \<in> dom A. globally_consistent_var A mds x)"

lemma globally_consistent_dom:
  "\<lbrakk> globally_consistent A mds; X \<subseteq> dom A \<rbrakk> \<Longrightarrow> globally_consistent (A |` X) mds"
  unfolding globally_consistent_def globally_consistent_var_def
  by (metis (no_types) IntE dom_restrict inf_absorb2 restrict_in rev_finite_subset)

lemma globally_consistent_writable:
  "\<lbrakk> x \<in> dom A; globally_consistent A mds \<rbrakk> \<Longrightarrow> x \<notin> mds AsmNoWrite"
  unfolding globally_consistent_def globally_consistent_var_def
  by (metis (no_types) domD option.simps(5) split_part)

lemma globally_consistent_loweq:
  assumes globally_consistent: "globally_consistent A mds"
  assumes some: "A x = Some (v, v')"
  assumes low: "dma x = Low"
  shows "v = v'"
proof -
  from some have "x \<in> dom A"
    by (metis domI)
  hence "case A x of None \<Rightarrow> True | Some (v, v') \<Rightarrow> (dma x = Low \<longrightarrow> v = v')"
    using globally_consistent
    unfolding globally_consistent_def globally_consistent_var_def
    by (metis option.simps(5) some split_part)
  with \<open>dma x = Low\<close> show ?thesis
    unfolding some
    by auto
qed

lemma globally_consistent_adapt_bisim:
  assumes bisim: "\<langle>c\<^sub>1, mds, mem\<^sub>1\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2\<rangle>"
  assumes globally_consistent: "globally_consistent A mds"
  shows "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A]\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A]\<rangle>"
proof -
  from globally_consistent have "finite (dom A)"
    by (auto simp: globally_consistent_def)
  thus ?thesis
    using globally_consistent
  proof (induct "dom A" arbitrary: A rule: finite_induct)
    case empty
    hence "\<And> x. A x = None"
      by auto
    hence "mem\<^sub>1 [\<parallel>\<^sub>1 A] = mem\<^sub>1" and "mem\<^sub>2 [\<parallel>\<^sub>2 A] = mem\<^sub>2"
      unfolding apply_adaptation_def
      by auto
    with bisim show ?case
      by auto
  next
    case (insert x X)
    define A' where "A' = A |` X"
    hence "dom A' = X"
      by (metis Int_insert_left_if0 dom_restrict inf_absorb2 insert(2) insert(4) order_refl)
    moreover
    from insert have "globally_consistent A' mds"
      by (metis A'_def globally_consistent_dom subset_insertI)
    ultimately have bisim': "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A']\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A']\<rangle>"
      using insert
      by metis
    with insert have writable: "x \<notin> mds AsmNoWrite"
      by (metis globally_consistent_writable insertI1)
    from insert obtain v v' where "A x = Some (v, v')"
      unfolding globally_consistent_def globally_consistent_var_def
      by (metis (no_types) domD insert_iff option.simps(5) case_prodE)

    have A_A': "\<And> y. y \<noteq> x \<Longrightarrow> A y = A' y"
      unfolding A'_def
      by (metis domIff insert(4) insert_iff restrict_in restrict_out)

    (* The following equalities may have more elegant proofs, but
        this should suffice, since the propositions are
        quite obvious. *)
    have eq\<^sub>1: "mem\<^sub>1 [\<parallel>\<^sub>1 A'] (x := v) = mem\<^sub>1 [\<parallel>\<^sub>1 A]"
      unfolding apply_adaptation_def A'_def
      apply (rule ext, rename_tac y)
      apply (case_tac "x = y")
       apply auto
       apply (metis \<open>A x = Some (v, v')\<close> option.simps(5) split_conv)
      by (metis A'_def A_A')
    have eq\<^sub>2: "mem\<^sub>2 [\<parallel>\<^sub>2 A'] (x := v') = mem\<^sub>2 [\<parallel>\<^sub>2 A]"
      unfolding apply_adaptation_def A'_def
      apply (rule ext, rename_tac y)
      apply (case_tac "x = y")
       apply auto
       apply (metis \<open>A x = Some (v, v')\<close> option.simps(5) split_conv)
      by (metis A'_def A_A')

    show ?case
    proof (cases "dma x")
      assume "dma x = High"
      hence "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A'] (x := v)\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A'] (x := v')\<rangle>"
        using mm_equiv_glob_consistent
        unfolding closed_glob_consistent_def
        by (metis bisim' \<open>x \<notin> mds AsmNoWrite\<close>)
      thus ?case using eq\<^sub>1 eq\<^sub>2
        by auto
    next
      assume "dma x = Low"
      hence "v = v'"
        by (metis \<open>A x = Some (v, v')\<close> globally_consistent_loweq insert.prems)
      moreover
      from writable and bisim have
        "\<langle>c\<^sub>1, mds, mem\<^sub>1 [\<parallel>\<^sub>1 A'] (x := v)\<rangle> \<approx> \<langle>c\<^sub>2, mds, mem\<^sub>2 [\<parallel>\<^sub>2 A'] (x := v)\<rangle>"
        using mm_equiv_glob_consistent
        unfolding closed_glob_consistent_def
        by (metis \<open>dma x = Low\<close> bisim')
      ultimately show ?case using eq\<^sub>1 eq\<^sub>2
        by auto
    qed
  qed
qed

(* This is the central lemma. Unfortunately, I didn't find
   a nice partitioning into several easier lemmas: *)
lemma makes_compatible_invariant:
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)"
                      "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes eval: "(cms\<^sub>1, mem\<^sub>1) \<rightarrow> (cms\<^sub>1', mem\<^sub>1')"
  obtains cms\<^sub>2' mem\<^sub>2' mems' where
      "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
       (cms\<^sub>2, mem\<^sub>2) \<rightarrow> (cms\<^sub>2', mem\<^sub>2') \<and>
       makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
proof -
  let ?X = "\<lambda> i. differing_vars_lists mem\<^sub>1 mem\<^sub>2 mems i"
  from sound_modes compat modes_eq have
    a: "\<forall> i < length cms\<^sub>1. \<forall> x \<in> (?X i). doesnt_read (fst (cms\<^sub>1 ! i)) x \<and>
                                          doesnt_read (fst (cms\<^sub>2 ! i)) x"
    by (metis compatible_different_no_read)
  from eval obtain k where
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
  then obtain g1 where
    c: "change_respecting (cms\<^sub>1 ! k, mem\<^sub>1) (cms\<^sub>1' ! k, mem\<^sub>1') (?X k) g1"
    using noread_exists_change_respecting b a
    by (metis surjective_pairing)

  from compat have "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> ?mems\<^sub>1k [\<mapsto> \<sigma>] = mem\<^sub>1 [\<mapsto> \<sigma>]"
    by (metis (no_types) Un_upper1 differing_vars_lists_def differing_vars_subst)

  with b and c have
    eval\<^sub>\<sigma>: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> (cms\<^sub>1 ! k, ?mems\<^sub>1k [\<mapsto> \<sigma>]) \<leadsto> (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> g1 \<sigma>])"
    by auto

  moreover
  with b and compat have
    bisim\<^sub>\<sigma>: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> (cms\<^sub>1 ! k, ?mems\<^sub>1k [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>])"
    by auto

  moreover have "snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)"
    by (metis b equal_size modes_eq nth_map)
    
  ultimately have d: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> \<exists> c\<^sub>f' mem\<^sub>f'.
    (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>f', ?mds\<^sub>k', mem\<^sub>f' \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> g1 \<sigma>]) \<approx> \<langle> c\<^sub>f', ?mds\<^sub>k', mem\<^sub>f' \<rangle>"
    by (metis mm_equiv_step)

  obtain h :: "'Var \<rightharpoonup> 'Val" where domh: "dom h = ?X k"
    by (metis dom_restrict_total)

  then obtain c\<^sub>h mem\<^sub>h where h_prop:
    "(cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> g1 h]) \<approx> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle>"
    using d
    by metis

  then obtain g2 where e:
    "change_respecting (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h]) \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h \<rangle> (?X k) g2"
    using a b noread_exists_change_respecting
    by (metis differing_lists_finite surjective_pairing)

  \<comment> \<open>The following statements are universally quantified
      since they are reused later:\<close>
  with h_prop have
    "\<forall> \<sigma>. dom \<sigma> = ?X k \<longrightarrow>
      (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> h] [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> g2 \<sigma>] \<rangle>"
    unfolding change_respecting.simps
    by auto

  with domh have f:
    "\<forall> \<sigma>. dom \<sigma> = ?X k \<longrightarrow>
      (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> g2 \<sigma>] \<rangle>"
    by (auto simp: subst_overrides)

  from d and f have g: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow>
    (cms\<^sub>2 ! k, ?mems\<^sub>2k [\<mapsto> \<sigma>]) \<leadsto> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> g2 \<sigma>] \<rangle> \<and>
    (cms\<^sub>1' ! k, mem\<^sub>1' [\<mapsto> g1 \<sigma>]) \<approx> \<langle> c\<^sub>h, ?mds\<^sub>k', mem\<^sub>h [\<mapsto> g2 \<sigma>] \<rangle>"
    using h_prop
    by (metis deterministic)
  let ?\<sigma>_mem\<^sub>2 = "to_partial mem\<^sub>2 |` ?X k"
  define mem\<^sub>2' where "mem\<^sub>2' = mem\<^sub>h [\<mapsto> g2 ?\<sigma>_mem\<^sub>2]"
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

  with i b equal_size have "(cms\<^sub>2, mem\<^sub>2) \<rightarrow> (cms\<^sub>2', mem\<^sub>2')"
    by (metis meval_intro)

  moreover
  from equal_size have new_length: "length cms\<^sub>1' = length cms\<^sub>2'"
    unfolding cms\<^sub>2'_def
    by (metis eval length_list_update meval_elim)

  with modes_eq have "map snd cms\<^sub>1' = map snd cms\<^sub>2'"
    unfolding cms\<^sub>2'_def
    by (metis b map_update snd_conv)

  moreover
  from c and e obtain dom_g1 dom_g2 where
    dom_uniq: "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> dom_g1 = dom (g1 \<sigma>)"
              "\<And> \<sigma>. dom \<sigma> = ?X k \<Longrightarrow> dom_g2 = dom (g2 \<sigma>)"
    by (metis change_respecting.simps domh)

  \<comment> \<open>This is the complicated part of the proof.\<close>
  obtain mems' where "makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
  proof
    define mems'_k
      where "mems'_k x =
      (if x \<notin> ?X k
       then (mem\<^sub>1' x, mem\<^sub>2' x)
       else if (x \<notin> dom_g1) \<or> (x \<notin> dom_g2)
       then (mem\<^sub>1' x, mem\<^sub>2' x)
       else (?mems\<^sub>1k x, ?mems\<^sub>2k x))" for x
    \<comment> \<open>This is used in two of the following cases, so we prove it beforehand:\<close>
    have x_unchanged: "\<And> x. \<lbrakk> x \<in> ?X k; x \<in> dom_g1; x \<in> dom_g2 \<rbrakk> \<Longrightarrow>
      mem\<^sub>1 x = mem\<^sub>1' x \<and> mem\<^sub>2 x = mem\<^sub>2' x"
    proof
      fix x
      assume "x \<in> ?X k" and "x \<in> dom_g1"
      thus "mem\<^sub>1 x = mem\<^sub>1' x"
        using a b c
        by (metis change_respecting_doesnt_modify dom_uniq(1) domh)
    next
      fix x
      assume "x \<in> ?X k" and "x \<in> dom_g2"

      hence eq_mem\<^sub>2: "?\<sigma>_mem\<^sub>2 x = Some (mem\<^sub>2 x)"
        by (metis restrict_in to_partial_def)
      hence "?mems\<^sub>2k [\<mapsto> h] [\<mapsto> ?\<sigma>_mem\<^sub>2] x = mem\<^sub>2 x"
        by (auto simp: subst_def)

      moreover
      from \<open>x \<in> dom_g2\<close> dom_uniq e have g_eq: "g2 ?\<sigma>_mem\<^sub>2 x = Some (mem\<^sub>2 x)"
        unfolding change_respecting.simps func_le_def
        by (metis dom_restrict_total eq_mem\<^sub>2)
      hence "mem\<^sub>h [\<mapsto> g2 ?\<sigma>_mem\<^sub>2] x = mem\<^sub>2 x"
        by (auto simp: subst_def)

      ultimately have "?mems\<^sub>2k [\<mapsto> h] [\<mapsto> ?\<sigma>_mem\<^sub>2] x = mem\<^sub>h [\<mapsto> g2 ?\<sigma>_mem\<^sub>2] x"
        by auto
      thus "mem\<^sub>2 x = mem\<^sub>2' x"
        by (metis \<open>mem\<^sub>2 = ?mems\<^sub>2k [\<mapsto> ?\<sigma>_mem\<^sub>2]\<close> dom\<sigma>_mem\<^sub>2 domh mem\<^sub>2'_def subst_overrides)
    qed

    define mems'_i
      where "mems'_i i x =
       (if ((mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x) \<and>
          (mem\<^sub>1' x = mem\<^sub>2' x \<or> dma x = High))
         then (mem\<^sub>1' x, mem\<^sub>2' x)
         else if ((mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x) \<and>
                  (mem\<^sub>1' x \<noteq> mem\<^sub>2' x \<and> dma x = Low))
              then (some_val, some_val)
              else (fst (mems ! i) x, snd (mems ! i) x))" for i x

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

    have mems'_simp2: "\<lbrakk> i \<noteq> k; i < length cms\<^sub>1 \<rbrakk> \<Longrightarrow>
      mems' ! i = (fst \<circ> mems'_i i, snd \<circ> mems'_i i)"
      unfolding mems'_def
      by auto
    (* Some auxiliary statements to allow reasoning about these definitions as if they were given
       by cases instead of nested if clauses. *)
    have mems'_k_1 [simp]: "\<And> x. \<lbrakk> x \<notin> ?X k \<rbrakk> \<Longrightarrow>
      fst (mems' ! k) x = mem\<^sub>1' x \<and> snd (mems' ! k) x = mem\<^sub>2' x"
      unfolding mems'_k_simp mems'_k_def
      by auto
    have mems'_k_2 [simp]: "\<And> x. \<lbrakk> x \<in> ?X k; x \<notin> dom_g1 \<or> x \<notin> dom_g2 \<rbrakk> \<Longrightarrow>
      fst (mems' ! k) x = mem\<^sub>1' x \<and> snd (mems' ! k) x = mem\<^sub>2' x"
      unfolding mems'_k_simp mems'_k_def
      by auto
    have mems'_k_3 [simp]: "\<And> x. \<lbrakk> x \<in> ?X k; x \<in> dom_g1; x \<in> dom_g2 \<rbrakk> \<Longrightarrow>
      fst (mems' ! k) x = fst (mems ! k) x \<and> snd (mems' ! k) x = snd (mems ! k) x"
      unfolding mems'_k_simp mems'_k_def
      by auto

    have mems'_k_cases:
      "\<And> P x.
        \<lbrakk>
         \<lbrakk> x \<notin> ?X k \<or> x \<notin> dom_g1 \<or> x \<notin> dom_g2;
           fst (mems' ! k) x = mem\<^sub>1' x;
           snd (mems' ! k) x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow> P x;
         \<lbrakk> x \<in> ?X k; x \<in> dom_g1; x \<in> dom_g2;
           fst (mems' ! k) x = fst (mems ! k) x;
           snd (mems' ! k) x = snd (mems ! k) x \<rbrakk> \<Longrightarrow> P x \<rbrakk> \<Longrightarrow> P x"
      using mems'_k_1 mems'_k_2 mems'_k_3
      by blast

    have mems'_i_simp:
      "\<And> i. \<lbrakk> i < length cms\<^sub>1; i \<noteq> k \<rbrakk> \<Longrightarrow> mems' ! i = (fst \<circ> mems'_i i, snd \<circ> mems'_i i)"
      unfolding mems'_def
      by auto

    have mems'_i_1 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
                 mem\<^sub>1' x = mem\<^sub>2' x \<or> dma x = High \<rbrakk> \<Longrightarrow>
               fst (mems' ! i) x = mem\<^sub>1' x \<and> snd (mems' ! i) x = mem\<^sub>2' x"
      unfolding mems'_i_def mems'_i_simp
      by auto

    have mems'_i_2 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
                 mem\<^sub>1' x \<noteq> mem\<^sub>2' x; dma x = Low \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = some_val \<and> snd (mems' ! i) x = some_val"
      unfolding mems'_i_def mems'_i_simp
      by auto
    have mems'_i_3 [simp]:
      "\<And> i x. \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
                 mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow>
              fst (mems' ! i) x = fst (mems ! i) x \<and> snd (mems' ! i) x = snd (mems ! i) x"
      unfolding mems'_i_def mems'_i_simp
      by auto
    (* This may look complicated, but is actually a rather
       mechanical definition, as it merely spells out the cases
       of the definition: *)
    have mems'_i_cases:
      "\<And> P i x.
         \<lbrakk> i \<noteq> k; i < length cms\<^sub>1;
           \<lbrakk> mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
             mem\<^sub>1' x = mem\<^sub>2' x \<or> dma x = High;
             fst (mems' ! i) x = mem\<^sub>1' x; snd (mems' ! i) x = mem\<^sub>2' x \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x;
        mem\<^sub>1' x \<noteq>  mem\<^sub>2' x; dma x = Low;
        fst (mems' ! i) x = some_val; snd (mems' ! i) x = some_val \<rbrakk> \<Longrightarrow> P x;
      \<lbrakk> mem\<^sub>1 x = mem\<^sub>1' x; mem\<^sub>2 x = mem\<^sub>2' x;
        fst (mems' ! i) x = fst (mems ! i) x; snd (mems' ! i) x = snd (mems ! i) x \<rbrakk> \<Longrightarrow> P x \<rbrakk>
      \<Longrightarrow> P x"
      using mems'_i_1 mems'_i_2 mems'_i_3
      by (metis (full_types) Sec.exhaust)

    let ?X' = "\<lambda> i. differing_vars_lists mem\<^sub>1' mem\<^sub>2' mems' i"
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
        define \<sigma>'
          where "\<sigma>' x =
              (if x \<in> ?X k
                then if x \<in> ?X' k
                     then \<sigma> x
                     else if (x \<in> dom (g1 h))
                             then Some (?mems\<^sub>1'i x)
                             else if (x \<in> dom (g2 h))
                                  then Some (?mems\<^sub>2'i x)
                                  else Some some_val
                else None)" for x
        then have dom\<sigma>': "dom \<sigma>' = ?X k"
          by (auto, metis domI domIff, metis \<open>i = k\<close> domD dom\<sigma>)

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

        have differing_in_dom: "\<And>x. \<lbrakk> x \<in> ?X k; x \<in> ?X' k \<rbrakk> \<Longrightarrow> x \<in> dom_g1 \<and> x \<in> dom_g2"
        proof (rule ccontr)
          fix x
          assume "x \<in> ?X k"
          assume "\<not> (x \<in> dom_g1 \<and> x \<in> dom_g2)"
          hence not_in_dom: "x \<notin> dom_g1 \<or> x \<notin> dom_g2" by auto
          hence "?mems\<^sub>1'i x = mem\<^sub>1' x" "?mems\<^sub>2'i x = mem\<^sub>2' x"
            using \<open>i = k\<close> \<open>x \<in> ?X k\<close> mems'_k_2
            by auto

          moreover assume "x \<in> ?X' k"
          ultimately show False
            by (metis \<open>i = k\<close> differing_vars_elim)
        qed

        (* We now show that we can reuse the earlier statements
           by showing the following equality: *)
        have "?mems\<^sub>1'i [\<mapsto> \<sigma>] = mem\<^sub>1' [\<mapsto> g1 \<sigma>']"
        proof (rule ext)
          fix x

          show "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = mem\<^sub>1' [\<mapsto> g1 \<sigma>'] x"
          proof (cases "x \<in> ?X' k")
            assume x_in_X'k: "x \<in> ?X' k"

            then obtain v where "\<sigma> x = Some v"
              by (metis dom\<sigma> domD \<open>i = k\<close>)
            hence "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = v"
              using \<open>x \<in> ?X' k\<close> dom\<sigma>
              by (auto simp: subst_def)
            moreover
            from c have le: "g1 \<sigma>' \<preceq> \<sigma>'"
              using dom\<sigma>'
              by auto
            from dom\<sigma>' and \<open>x \<in> ?X' k\<close> have "x \<in> dom (g1 \<sigma>')"
              by (metis diff_vars_impl differing_in_dom dom_uniq(1))
             
            hence "mem\<^sub>1' [\<mapsto> g1 \<sigma>'] x = v"
              using dom\<sigma>' c le
              unfolding func_le_def subst_def
              by (metis \<sigma>'_def \<open>\<sigma> x = Some v\<close> diff_vars_impl option.simps(5) x_in_X'k)

            ultimately show "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = mem\<^sub>1' [\<mapsto> g1 \<sigma>'] x" ..
          next
            assume "x \<notin> ?X' k"

            hence "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = ?mems\<^sub>1'i x"
              using dom\<sigma>
              by (metis \<open>i = k\<close> subst_not_in_dom)
            show ?thesis
            proof (cases "x \<in> dom_g1")
              assume "x \<in> dom_g1"
              hence "x \<in> dom (g1 \<sigma>')"
                using dom\<sigma>' dom_uniq
                by auto
              hence "g1 \<sigma>' x = \<sigma>' x"
                using c dom\<sigma>'
                by (metis change_respecting.simps func_le_def)
              then have "\<sigma>' x = Some (?mems\<^sub>1'i x)"
                unfolding \<sigma>'_def
                using dom\<sigma>' domh
                by (metis \<open>g1 \<sigma>' x = \<sigma>' x\<close> \<open>x \<in> dom (g1 \<sigma>')\<close> \<open>x \<notin> ?X' k\<close> domIff dom_uniq(1))

              hence "mem\<^sub>1' [\<mapsto> g1 \<sigma>'] x = ?mems\<^sub>1'i x"
                unfolding subst_def
                by (metis \<open>g1 \<sigma>' x = \<sigma>' x\<close> option.simps(5))
              thus ?thesis
                by (metis \<open>?mems\<^sub>1'i [\<mapsto>\<sigma>] x = ?mems\<^sub>1'i x\<close>)
            next
              assume "x \<notin> dom_g1"
              then have "mem\<^sub>1' [\<mapsto> g1 \<sigma>'] x = mem\<^sub>1' x"
                by (metis dom\<sigma>' dom_uniq(1) subst_not_in_dom)
              moreover
              have "?mems\<^sub>1'i x = mem\<^sub>1' x"
                by (metis \<open>i = k\<close> \<open>x \<notin> ?X' k\<close> differing_vars_neg)
              ultimately show ?thesis
                by (metis \<open>?mems\<^sub>1'i [\<mapsto>\<sigma>] x = ?mems\<^sub>1'i x\<close>)
            qed
          qed
        qed
        (* And the same for the second memories: *)
        moreover have "?mems\<^sub>2'i [\<mapsto> \<sigma>] = mem\<^sub>h [\<mapsto> g2 \<sigma>']"
        proof (rule ext)
          fix x

          show "?mems\<^sub>2'i [\<mapsto> \<sigma>] x = mem\<^sub>h [\<mapsto> g2 \<sigma>'] x"
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
            from e have le: "g2 \<sigma>' \<preceq> \<sigma>'"
              using dom\<sigma>'
              by auto
            from \<open>x \<in> ?X' k\<close> have "x \<in> ?X k"
              by auto
            hence "x \<in> dom (g2 \<sigma>')"
              by (metis differing_in_dom dom\<sigma>' dom_uniq(2) \<open>x \<in> ?X' k\<close>)
            hence "mem\<^sub>2' [\<mapsto> g2 \<sigma>'] x = v"
              using dom\<sigma>' c le
              unfolding func_le_def subst_def
              by (metis \<sigma>'_def \<open>\<sigma> x = Some v\<close> diff_vars_impl option.simps(5) \<open>x \<in> ?X' k\<close>)

            ultimately show ?thesis
              by (metis dom\<sigma>' dom_restrict_total dom_uniq(2) mem\<^sub>2'_def subst_overrides)
          next
            assume "x \<notin> ?X' k"

            hence "?mems\<^sub>2'i [\<mapsto> \<sigma>] x = ?mems\<^sub>2'i x"
              using dom\<sigma>
              by (metis \<open>i = k\<close> subst_not_in_dom)
            show ?thesis
            proof (cases "x \<in> dom_g2")
              assume "x \<in> dom_g2"
              hence "x \<in> dom (g2 \<sigma>')"
                using dom\<sigma>'
                by (metis dom_uniq)
              hence "g2 \<sigma>' x = \<sigma>' x"
                using e dom\<sigma>'
                by (metis change_respecting.simps func_le_def)
              then have "\<sigma>' x = Some (?mems\<^sub>2'i x)"
              proof (cases "x \<in> dom_g1")
                \<comment> \<open>This can't happen, so derive a contradiction.\<close>
                assume "x \<in> dom_g1"

                have "x \<notin> ?X k"
                proof (rule ccontr)
                  assume "\<not> (x \<notin> ?X k)"
                  hence "x \<in> ?X k" by auto
                  have "mem\<^sub>1 x = mem\<^sub>1' x \<and> mem\<^sub>2 x = mem\<^sub>2' x"
                    by (metis \<sigma>'_def \<open>g2 \<sigma>' x = \<sigma>' x\<close> \<open>x \<in> dom (g2 \<sigma>')\<close>
                      \<open>x \<in> dom_g1\<close> \<open>x \<in> dom_g2\<close> domIff x_unchanged)
                  moreover
                  from \<open>x \<notin> ?X' k\<close> have
                    "?mems\<^sub>1'i x = ?mems\<^sub>1k x \<and> ?mems\<^sub>2'i x = ?mems\<^sub>2k x"
                    using \<open>x \<in> ?X k\<close> \<open>x \<in> dom_g1\<close> \<open>x \<in> dom_g2\<close>
                    by auto
                  ultimately show False
                    using \<open>x \<in> ?X k\<close> \<open>x \<notin> ?X' k\<close>
                    by (metis \<open>i = k\<close> differing_vars_elim differing_vars_neg)
                qed
                hence False
                  by (metis \<sigma>'_def \<open>g2 \<sigma>' x = \<sigma>' x\<close> \<open>x \<in> dom (g2 \<sigma>')\<close> domIff)
                thus ?thesis
                  by blast
              next
                assume "x \<notin> dom_g1"
                thus ?thesis
                  unfolding \<sigma>'_def
                  by (metis \<open>g2 \<sigma>' x = \<sigma>' x\<close> \<open>x \<in> dom (g2 \<sigma>')\<close> \<open>x \<notin> ?X' k\<close> 
                    domIff dom\<sigma>' dom_uniq domh)
              qed
              hence "mem\<^sub>2' [\<mapsto> g2 \<sigma>'] x = ?mems\<^sub>2'i x"
                unfolding subst_def
                by (metis \<open>g2 \<sigma>' x = \<sigma>' x\<close> option.simps(5))
              thus ?thesis
                using \<open>x \<notin> ?X' k\<close> dom\<sigma> dom\<sigma>'
                by (metis \<open>i = k\<close> dom_restrict_total dom_uniq(2)
                  mem\<^sub>2'_def subst_not_in_dom subst_overrides)
            next
              assume "x \<notin> dom_g2"
              then have "mem\<^sub>h [\<mapsto> g2 \<sigma>'] x = mem\<^sub>h x"
                by (metis dom\<sigma>' dom_uniq(2) subst_not_in_dom)
              moreover
              have "?mems\<^sub>2'i x = mem\<^sub>2' x"
                by (metis \<open>i = k\<close> \<open>x \<notin> dom_g2\<close> mems'_k_1 mems'_k_2)

              hence "?mems\<^sub>2'i x = mem\<^sub>h x"
                unfolding mem\<^sub>2'_def
                by (metis \<open>x \<notin> dom_g2\<close> dom\<sigma>_mem\<^sub>2 dom_uniq(2) subst_not_in_dom)
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
        define \<sigma>'
          where "\<sigma>' x = (if x \<in> ?X i
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
                 (?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                  ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x)
                 \<longrightarrow> (mem\<^sub>1' x \<noteq> mem\<^sub>1 x \<or> mem\<^sub>2' x \<noteq> mem\<^sub>2 x)"
        proof -
          fix x
          {
            assume eq_mem: "mem\<^sub>1' x = mem\<^sub>1 x \<and> mem\<^sub>2' x = mem\<^sub>2 x"
            hence mems'_simp [simp]: "?mems\<^sub>1'i x = ?mems\<^sub>1i x \<and> ?mems\<^sub>2'i x = ?mems\<^sub>2i x"
              using mems'_i_3
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
                apply (auto simp: subst_def)
                 apply (metis mems'_simp)
                by (metis mems'_simp)
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

        from o have
          p: "\<And> x. \<lbrakk> ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or>
                      ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x \<rbrakk> \<Longrightarrow>
          x \<notin> snd (cms\<^sub>1 ! i) AsmNoWrite"
        proof
          fix x
          assume mems_neq:
            "?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
          hence modified:
            "\<not> (doesnt_modify (fst (cms\<^sub>1 ! k)) x) \<or> \<not> (doesnt_modify (fst (cms\<^sub>2 ! k)) x)"
            using b i o
            unfolding doesnt_modify_def
            by (metis surjective_pairing)
          moreover
          from sound_modes have loc_modes:
            "locally_sound_mode_use (cms\<^sub>1 ! k, mem\<^sub>1) \<and>
             locally_sound_mode_use (cms\<^sub>2 ! k, mem\<^sub>2)"
            unfolding sound_mode_use.simps
            by (metis b equal_size list_all_length)
          moreover
          have "snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)"
            by (metis b equal_size modes_eq nth_map)
          have "(cms\<^sub>1 ! k, mem\<^sub>1) \<in> loc_reach (cms\<^sub>1 ! k, mem\<^sub>1)"
            by (metis loc_reach.refl prod.collapse)
          hence guars:
                "x \<in> snd (cms\<^sub>1 ! k) GuarNoWrite \<longrightarrow> doesnt_modify (fst (cms\<^sub>1 ! k)) x \<and>
                 x \<in> snd (cms\<^sub>2 ! k) GuarNoWrite \<longrightarrow> doesnt_modify (fst (cms\<^sub>1 ! k)) x"
            using loc_modes
            unfolding locally_sound_mode_use_def \<open>snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)\<close>
            by (metis loc_reach.refl surjective_pairing)

          hence "x \<notin> snd (cms\<^sub>1 ! k) GuarNoWrite"
            using modified loc_modes locally_sound_mode_use_def
            by (metis \<open>snd (cms\<^sub>1 ! k) = snd (cms\<^sub>2 ! k)\<close> loc_reach.refl prod.collapse)
          moreover
          from sound_modes have "compatible_modes (map snd cms\<^sub>1)"
            by (metis globally_sound_modes_compatible sound_mode_use.simps)

          ultimately show "x \<notin> snd (cms\<^sub>1 ! i) AsmNoWrite"
            unfolding compatible_modes_def
            using \<open>i \<noteq> k\<close> i_le
            by (metis (no_types) b length_list_update length_map nth_map)
        qed

        have q:
          "\<And> x. \<lbrakk> dma x = Low;
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

        let ?\<Delta> = "differing_vars (?mems\<^sub>1i [\<mapsto> \<sigma>']) (?mems\<^sub>1'i [\<mapsto> \<sigma>]) \<union>
                  differing_vars (?mems\<^sub>2i [\<mapsto> \<sigma>']) (?mems\<^sub>2'i [\<mapsto> \<sigma>])"

        have \<Delta>_finite: "finite ?\<Delta>"
          by (metis (no_types) differing_finite finite_UnI)
        \<comment> \<open>We first define the adaptation, then prove that it does the right thing.\<close>
        define A where "A x =
                     (if x \<in> ?\<Delta>
                      then if dma x = High
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

        have A_correct:
              "\<And> x.
               globally_consistent_var A (snd (cms\<^sub>1 ! i)) x \<and>
               ?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] x = ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<and>
               ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] x = ?mems\<^sub>2'i [\<mapsto> \<sigma>] x"
        proof -
          fix x
          show "?thesis x"
            (is "?A \<and> ?Eq\<^sub>1 \<and> ?Eq\<^sub>2")
          proof (cases "x \<in> ?\<Delta>")
            assume "x \<in> ?\<Delta>"
            hence diff:
              "?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>1i [\<mapsto> \<sigma>'] x \<or> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x \<noteq> ?mems\<^sub>2i [\<mapsto> \<sigma>'] x"
              by (auto simp: differing_vars_def)
            from p and diff have writable: "x \<notin> snd (cms\<^sub>1 ! i) AsmNoWrite"
              by auto
            show ?thesis
            proof (cases "dma x")
              assume "dma x = High"
              from \<open>dma x = High\<close> have A_simp [simp]:
                "A x = Some (?mems\<^sub>1'i [\<mapsto> \<sigma>] x, ?mems\<^sub>2'i [\<mapsto> \<sigma>] x)"
                unfolding A_def
                by (metis \<open>x \<in> ?\<Delta>\<close>)
              from writable have "?A"
                unfolding globally_consistent_var_def A_simp
                using \<open>dma x = High\<close>
                by auto
              moreover
              from A_simp have ?Eq\<^sub>1 ?Eq\<^sub>2
                unfolding A_def apply_adaptation_def
                by auto
              ultimately show ?thesis
                by auto
            next
              assume "dma x = Low"
              show ?thesis
              proof (cases "x \<in> ?X' i")
                assume "x \<in> ?X' i"
                then obtain v where "\<sigma> x = Some v"
                  by (metis domD dom\<sigma>)
                hence eq: "?mems\<^sub>1'i [\<mapsto> \<sigma>] x = v \<and> ?mems\<^sub>2'i [\<mapsto> \<sigma>] x = v"
                  unfolding subst_def
                  by auto
                moreover
                from \<open>x \<in> ?X' i\<close> and \<open>dma x = Low\<close> have A_simp [simp]:
                  "A x = (case \<sigma> x of
                            Some v \<Rightarrow> Some (v, v)
                          | None \<Rightarrow> None)"
                  unfolding A_def
                  by (metis Sec.simps(1) \<open>x \<in> ?\<Delta>\<close>)
                with writable eq \<open>\<sigma> x = Some v\<close> have "?A"
                  unfolding globally_consistent_var_def
                  by auto
                ultimately show ?thesis
                  using domA \<open>x \<in> ?\<Delta>\<close> \<open>\<sigma> x = Some v\<close>
                  by (auto simp: apply_adaptation_def)

              next
                assume "x \<notin> ?X' i"
                hence A_simp [simp]: "A x = Some (mem\<^sub>1' x, mem\<^sub>1' x)"
                  unfolding A_def
                  using \<open>x \<in> ?\<Delta>\<close> \<open>dma x = Low\<close>
                  by auto
                from q have "mem\<^sub>1' x = mem\<^sub>2' x"
                  by (metis \<open>dma x = Low\<close> diff \<open>x \<notin> ?X' i\<close>)
                with writable have ?A
                  unfolding globally_consistent_var_def
                  by auto

                moreover
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
            hence "globally_consistent_var A (snd (cms\<^sub>1 ! i)) x"
              by (auto simp: globally_consistent_var_def)
            moreover
            from \<open>A x = None\<close> have "x \<notin> dom A"
              by (metis domIff)
            from \<open>x \<notin> ?\<Delta>\<close> have "?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] x = ?mems\<^sub>1'i [\<mapsto> \<sigma>] x \<and>
                                 ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] x = ?mems\<^sub>2'i [\<mapsto> \<sigma>] x"
              using \<open>A x = None\<close>
              unfolding differing_vars_def apply_adaptation_def
              by auto

            ultimately show ?thesis
              by auto
          qed
        qed
        hence "?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A] = ?mems\<^sub>1'i [\<mapsto> \<sigma>] \<and>
               ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A] = ?mems\<^sub>2'i [\<mapsto> \<sigma>]"
          by auto
        moreover
        from A_correct have "globally_consistent A (snd (cms\<^sub>1 ! i))"
          by (metis \<Delta>_finite globally_consistent_def domA)

        have "snd (cms\<^sub>1 ! i) = snd (cms\<^sub>2 ! i)"
          by (metis \<open>i < length cms\<^sub>1\<close> equal_size modes_eq nth_map)

        with bisim have "(cms\<^sub>1 ! i, ?mems\<^sub>1i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>1 A]) \<approx> (cms\<^sub>2 ! i, ?mems\<^sub>2i [\<mapsto> \<sigma>'] [\<parallel>\<^sub>2 A])"
          using \<open>globally_consistent A (snd (cms\<^sub>1 ! i))\<close>
          apply (subst surjective_pairing[of "cms\<^sub>1 ! i"])
          apply (subst surjective_pairing[of "cms\<^sub>2 ! i"])
          by (metis surjective_pairing globally_consistent_adapt_bisim)

        ultimately show ?thesis
          by (metis \<open>i \<noteq> k\<close> b cms\<^sub>2'_def nth_list_update_neq)
      qed
    next
      fix i x

      let ?mems\<^sub>1'i = "fst (mems' ! i)"
      let ?mems\<^sub>2'i = "snd (mems' ! i)"
      assume i_le: "i < length cms\<^sub>1'"
      assume mem_eq: "mem\<^sub>1' x = mem\<^sub>2' x \<or> dma x = High"
      show "x \<notin> ?X' i"
      proof (cases "i = k")
        assume "i = k"
        thus "x \<notin> ?X' i"
          apply (cases "x \<notin> ?X k \<or> x \<notin> dom_g1 \<or> x \<notin> dom_g2")
           apply (metis differing_vars_neg_intro mems'_k_1 mems'_k_2)
          by (metis Sec.simps(2) b compat compat_different mem_eq x_unchanged)
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
            "mem\<^sub>1' x \<noteq> mem\<^sub>2' x" and "dma x = Low"
          \<comment> \<open>In this case, for example, the values of (mems' ! i) are not needed.\<close>
          thus "x \<notin> ?X' i"
            by (metis Sec.simps(2) mem_eq)
        next
          assume case3: "mem\<^sub>1 x = mem\<^sub>1' x" "mem\<^sub>2 x = mem\<^sub>2' x"
            "fst (mems' ! i) x = fst (mems ! i) x"
            "snd (mems' ! i) x = snd (mems ! i) x"
          have "x \<in> ?X' i \<Longrightarrow> mem\<^sub>1' x \<noteq> mem\<^sub>2' x \<and> dma x = Low"
          proof -
            assume "x \<in> ?X' i"
            from case3 and \<open>x \<in> ?X' i\<close> have "x \<in> ?X i"
              by (metis differing_vars_neg differing_vars_elim)
            with case3 show ?thesis
              by (metis b compat compat_different i_le length_list_update)
          qed
          with \<open>mem\<^sub>1' x = mem\<^sub>2' x \<or> dma x = High\<close> show "x \<notin> ?X' i"
            by auto
        qed
      qed
    next
      { fix x
        have "\<exists> i < length cms\<^sub>1. x \<notin> ?X' i"
        proof (cases "mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x")
          assume var_changed: "mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x"
          have "x \<notin> ?X' k"
            apply (rule mems'_k_cases)
             apply (metis differing_vars_neg_intro)
            by (metis var_changed x_unchanged)
          thus ?thesis by (metis b)
        next
          assume "\<not> (mem\<^sub>1 x \<noteq> mem\<^sub>1' x \<or> mem\<^sub>2 x \<noteq> mem\<^sub>2' x)"
          hence assms: "mem\<^sub>1 x = mem\<^sub>1' x" "mem\<^sub>2 x = mem\<^sub>2' x" by auto

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
            assume "i \<noteq> k"
            hence "fst (mems' ! i) x = fst (mems ! i) x"
                  "snd (mems' ! i) x = snd (mems ! i) x"
              using i_prop assms mems'_i_3
              by auto
            with i_prop have "x \<notin> ?X' i"
              by (metis assms differing_vars_neg differing_vars_neg_intro)
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
  assumes x_low: "dma x = Low"
  assumes x_readable: "\<forall> i < length cms\<^sub>1. x \<notin> snd (cms\<^sub>1 ! i) AsmNoRead"
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

    obtain \<sigma> :: "'Var \<rightharpoonup> 'Val" where "dom \<sigma> = ?X j"
      by (metis dom_restrict_total)

    with compat and j_prop have "(cms\<^sub>1 ! j, ?mems\<^sub>1j [\<mapsto> \<sigma>]) \<approx> (cms\<^sub>2 ! j, ?mems\<^sub>2j [\<mapsto> \<sigma>])"
      by auto
    
    moreover
    have "snd (cms\<^sub>1 ! j) = snd (cms\<^sub>2 ! j)"
      using modes_eq
      by (metis j_prop length_map nth_map)

    ultimately have "?mems\<^sub>1j [\<mapsto> \<sigma>] =\<^bsub>snd (cms\<^sub>1 ! j)\<^esub>\<^sup>l ?mems\<^sub>2j [\<mapsto> \<sigma>]"
      using modes_eq j_prop
      by (metis prod.collapse mm_equiv_low_eq)
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

lemma reachable_modes_subset:
  assumes eval: "(cms, mem) \<rightarrow> (cms', mem')"
  shows "reachable_mode_states (cms', mem') \<subseteq> reachable_mode_states (cms, mem)"
proof
  fix mdss
  assume "mdss \<in> reachable_mode_states (cms', mem')"
  thus "mdss \<in> reachable_mode_states (cms, mem)"
    using reachable_mode_states_def
    apply auto
    by (metis (hide_lams, no_types) assms converse_rtrancl_into_rtrancl)
qed

lemma globally_sound_modes_invariant:
  assumes globally_sound: "globally_sound_mode_use (cms, mem)"
  assumes eval: "(cms, mem) \<rightarrow> (cms', mem')"
  shows "globally_sound_mode_use (cms', mem')"
  using assms reachable_modes_subset
  unfolding globally_sound_mode_use_def
  by (metis (no_types) subsetD)

lemma loc_reach_mem_diff_subset:
  assumes mem_diff: "\<forall> x. x \<in> mds AsmNoWrite \<longrightarrow> mem\<^sub>1 x = mem\<^sub>2 x"
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
  assumes mem_diff: "\<forall> x. x \<in> mds AsmNoWrite \<longrightarrow> mem' x = mem x"
  shows "loc_reach \<langle>c, mds, mem\<rangle> = loc_reach \<langle>c, mds, mem'\<rangle>"
  using assms loc_reach_mem_diff_subset
  by (auto, metis)

lemma sound_modes_invariant:
  assumes sound_modes: "sound_mode_use (cms, mem)"
  assumes eval: "(cms, mem) \<rightarrow> (cms', mem')"
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
      hence "\<And> x. x \<in> snd (cms ! i) AsmNoWrite \<Longrightarrow> x \<in> snd (cms ! k) GuarNoWrite"
        unfolding compatible_modes_def
        by (metis (no_types) \<open>i \<noteq> k\<close> \<open>length cms = length cms'\<close> ev i_le length_map nth_map)
      hence "\<And> x. x \<in> snd (cms ! i) AsmNoWrite \<longrightarrow> doesnt_modify (fst (cms ! k)) x"
        using ev loc_sound
        unfolding locally_sound_mode_use_def
        by (metis loc_reach.refl surjective_pairing)
      with eval have "\<And> x. x \<in> snd (cms ! i) AsmNoWrite \<longrightarrow> mem x = mem' x"
        by (metis (no_types) doesnt_modify_def ev prod.collapse)
      then have "loc_reach (cms ! i, mem') = loc_reach (cms ! i, mem)"
        by (metis loc_reach_mem_diff_eq prod.collapse)
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

lemma makes_compatible_eval_k:
  assumes compat: "makes_compatible (cms\<^sub>1, mem\<^sub>1) (cms\<^sub>2, mem\<^sub>2) mems"
  assumes modes_eq: "map snd cms\<^sub>1 = map snd cms\<^sub>2"
  assumes sound_modes: "sound_mode_use (cms\<^sub>1, mem\<^sub>1)" "sound_mode_use (cms\<^sub>2, mem\<^sub>2)"
  assumes eval: "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>1', mem\<^sub>1')"
  shows "\<exists> cms\<^sub>2' mem\<^sub>2' mems'. sound_mode_use (cms\<^sub>1', mem\<^sub>1') \<and>
                              sound_mode_use (cms\<^sub>2', mem\<^sub>2') \<and>
                              map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                              (cms\<^sub>2, mem\<^sub>2) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                              makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
proof -
  (* cms\<^sub>1' and mem\<^sub>1' need to be arbitrary so
     that the induction hypothesis is sufficiently general. *)
  from eval show ?thesis
  proof (induct "k" arbitrary: cms\<^sub>1' mem\<^sub>1')
    case 0
    hence "cms\<^sub>1' = cms\<^sub>1 \<and> mem\<^sub>1' = mem\<^sub>1"
      by (metis prod.inject meval_k.simps(1))
    thus ?case
      by (metis compat meval_k.simps(1) modes_eq sound_modes)
  next
    case (Suc k)
    then obtain cms\<^sub>1'' mem\<^sub>1'' where eval'':
      "(cms\<^sub>1, mem\<^sub>1) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>1'', mem\<^sub>1'') \<and> (cms\<^sub>1'', mem\<^sub>1'') \<rightarrow> (cms\<^sub>1', mem\<^sub>1')"
      by (metis meval_k.simps(2) prod_cases3 snd_conv)
    hence "(cms\<^sub>1'', mem\<^sub>1'') \<rightarrow> (cms\<^sub>1', mem\<^sub>1')" ..
    moreover
    from eval'' obtain cms\<^sub>2'' mem\<^sub>2'' mems'' where IH:
      "sound_mode_use (cms\<^sub>1'', mem\<^sub>1'') \<and>
       sound_mode_use (cms\<^sub>2'', mem\<^sub>2'') \<and>
       map snd cms\<^sub>1'' = map snd cms\<^sub>2'' \<and>
       (cms\<^sub>2, mem\<^sub>2) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>2'', mem\<^sub>2'') \<and>
       makes_compatible (cms\<^sub>1'', mem\<^sub>1'') (cms\<^sub>2'', mem\<^sub>2'') mems''"
      using Suc
      by metis
    ultimately obtain cms\<^sub>2' mem\<^sub>2' mems' where
      "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
       (cms\<^sub>2'', mem\<^sub>2'') \<rightarrow> (cms\<^sub>2', mem\<^sub>2') \<and>
       makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
      using makes_compatible_invariant
      by blast
    thus ?case
      by (metis IH eval'' meval_k.simps(2) sound_modes_invariant)
  qed
qed

lemma differing_vars_initially_empty:
  "i < n \<Longrightarrow> x \<notin> differing_vars_lists mem\<^sub>1 mem\<^sub>2 (zip (replicate n mem\<^sub>1) (replicate n mem\<^sub>2)) i"
  unfolding differing_vars_lists_def differing_vars_def
  by auto

lemma compatible_refl:
  assumes coms_secure: "list_all com_sifum_secure cmds"
  assumes low_eq: "mem\<^sub>1 =\<^sup>l mem\<^sub>2"
  shows "makes_compatible (add_initial_modes cmds, mem\<^sub>1)
                          (add_initial_modes cmds, mem\<^sub>2)
                          (replicate (length cmds) (mem\<^sub>1, mem\<^sub>2))"
proof -
  let ?n = "length cmds"
  let ?mems = "replicate ?n (mem\<^sub>1, mem\<^sub>2)" and
      ?mdss = "replicate ?n mds\<^sub>s"
  let ?X = "differing_vars_lists mem\<^sub>1 mem\<^sub>2 ?mems"
  have diff_empty: "\<forall> i < ?n. ?X i = {}"
    by (metis differing_vars_initially_empty ex_in_conv min.idem zip_replicate)

  show ?thesis
    unfolding add_initial_modes_def
  proof
    show "length (zip cmds ?mdss) = length (zip cmds ?mdss) \<and> length (zip cmds ?mdss) = length ?mems"
      by auto
  next
    fix i \<sigma>
    let ?mems\<^sub>1i = "fst (?mems ! i)" and ?mems\<^sub>2i = "snd (?mems ! i)"
    assume i: "i < length (zip cmds ?mdss)"
    with coms_secure have "com_sifum_secure (cmds ! i)"
      using coms_secure
      by (metis length_map length_replicate list_all_length map_snd_zip)
    with i have "\<And> mem\<^sub>1 mem\<^sub>2. mem\<^sub>1 =\<^bsub>mds\<^sub>s\<^esub>\<^sup>l mem\<^sub>2 \<Longrightarrow>
      (zip cmds (replicate ?n mds\<^sub>s) ! i, mem\<^sub>1) \<approx> (zip cmds (replicate ?n mds\<^sub>s) ! i, mem\<^sub>2)"
      using com_sifum_secure_def low_indistinguishable_def
      by auto

    moreover
    from i have "?mems\<^sub>1i = mem\<^sub>1" "?mems\<^sub>2i = mem\<^sub>2"
      by auto
    with low_eq have "?mems\<^sub>1i [\<mapsto> \<sigma>] =\<^bsub>mds\<^sub>s\<^esub>\<^sup>l ?mems\<^sub>2i [\<mapsto> \<sigma>]"
      by (auto simp: subst_def mds\<^sub>s_def low_mds_eq_def low_eq_def, case_tac "\<sigma> x", auto)

    ultimately show "(zip cmds ?mdss ! i, ?mems\<^sub>1i [\<mapsto> \<sigma>]) \<approx> (zip cmds ?mdss ! i, ?mems\<^sub>2i [\<mapsto> \<sigma>])"
      by simp
  next
    fix i x
    assume "i < length (zip cmds ?mdss)"
    with diff_empty show "x \<notin> ?X i" by auto
  next
    show "(length (zip cmds ?mdss) = 0 \<and> mem\<^sub>1 =\<^sup>l mem\<^sub>2) \<or> (\<forall> x. \<exists> i < length (zip cmds ?mdss). x \<notin> ?X i)"
      using diff_empty
      by (metis bot_less bot_nat_def empty_iff length_zip low_eq min_0L)
  qed
qed

theorem sifum_compositionality:
  assumes com_secure: "list_all com_sifum_secure cmds"
  assumes no_assms: "no_assumptions_on_termination cmds"
  assumes sound_modes: "\<forall> mem. sound_mode_use (add_initial_modes cmds, mem)"
  shows "prog_sifum_secure cmds"
  unfolding prog_sifum_secure_def
  using assms
proof (clarify)
  fix mem\<^sub>1 mem\<^sub>2 :: "'Var \<Rightarrow> 'Val"
  fix k cms\<^sub>1' mem\<^sub>1'
  let ?n = "length cmds"
  let ?mems = "zip (replicate ?n mem\<^sub>1) (replicate ?n mem\<^sub>2)"
  assume low_eq: "mem\<^sub>1 =\<^sup>l mem\<^sub>2"
  with com_secure have compat:
    "makes_compatible (add_initial_modes cmds, mem\<^sub>1) (add_initial_modes cmds, mem\<^sub>2) ?mems"
    by (metis compatible_refl fst_conv length_replicate map_replicate snd_conv zip_eq_conv)

  also assume eval: "(add_initial_modes cmds, mem\<^sub>1) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>1', mem\<^sub>1')"

  ultimately obtain cms\<^sub>2' mem\<^sub>2' mems'
    where p: "map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
             (add_initial_modes cmds, mem\<^sub>2) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
             makes_compatible (cms\<^sub>1', mem\<^sub>1') (cms\<^sub>2', mem\<^sub>2') mems'"
    using sound_modes makes_compatible_eval_k
    by blast

  thus "\<exists> cms\<^sub>2' mem\<^sub>2'. (add_initial_modes cmds, mem\<^sub>2) \<rightarrow>\<^bsub>k\<^esub> (cms\<^sub>2', mem\<^sub>2') \<and>
                        map snd cms\<^sub>1' = map snd cms\<^sub>2' \<and>
                        length cms\<^sub>2' = length cms\<^sub>1' \<and>
                        (\<forall> x. dma x = Low \<and> (\<forall> i < length cms\<^sub>1'. x \<notin> snd (cms\<^sub>1' ! i) AsmNoRead)
          \<longrightarrow> mem\<^sub>1' x = mem\<^sub>2' x)"
    using p compat_low_eq
    by (metis length_map)
qed

end

end
