theory SM_Ample_Impl
imports SM_Datastructures "../Analysis/SM_POR"
  "HOL-Library.RBT_Mapping"
begin

  text \<open>
    Given a sticky program, we implement
    a valid ample-function by picking the transitions from the first
    PID that qualifies as an ample-set\<close>
  context visible_prog
  begin
    definition ga_gample
      :: "(cmdc\<times>cmdc) set \<Rightarrow> pid_global_config \<Rightarrow> global_action set" 
    where
      "ga_gample sticky_E gc \<equiv> let
        lcs = pid_global_config.processes gc;
        gs = pid_global_config.state gc;
        as = find_min_idx_f (\<lambda>lc.
          let
            c = local_config.command lc;
            ls = local_config.state lc;
            as = set (comp.succ_impl c)
          in
            if (\<forall>(a,_)\<in>as. read_globals a = {} \<and> write_globals a = {}) then
              let 
                as = {(a,c')\<in>as. la_en' (ls,gs) a}
              in
                if as={} \<or> (\<exists>(a,c')\<in>as. (c,c')\<in>sticky_E) then 
                  None 
                else 
                  Some (c,as)
            else
              None
        ) lcs
      in
        case as of
          Some (pid,c,as) \<Rightarrow> (\<lambda>(a,c'). (pid,c,a,c'))`as
        | None \<Rightarrow> ga_gen gc"
    
    definition "ga_ample sticky_E 
      \<equiv> stutter_extend_en (ga_gample sticky_E)"

    lemma ga_gample_subset: "ga_gample sticky_E gc \<subseteq> ga_gen gc"
      unfolding ga_gample_def ga_gen_def
      by (auto 
        simp: comp.astep_impl_def
        split: option.splits if_split_asm 
        dest!: find_min_idx_f_SomeD)

    lemma ga_gample_empty_iff: "ga_gample sticky_E gc = {} \<longleftrightarrow> ga_gen gc = {}"  
      unfolding ga_gample_def ga_gen_def
      by (fastforce 
        simp: comp.astep_impl_def
        split: option.splits if_split_asm 
        dest!: find_min_idx_f_SomeD)

    lemma ga_ample_None_iff: "None \<in> ga_ample sticky_E gc \<longleftrightarrow> None \<in> ga_en gc"
      by (auto 
        simp: ga_ample_def ga_en_def stutter_extend_en_def ga_gample_empty_iff)
      
    lemma ga_ample_neq_en_eq:
      assumes "ga_ample sticky_E gc \<noteq> ga_en gc"
      shows "ga_ample sticky_E gc = Some`ga_gample sticky_E gc \<and> ga_en gc = Some`ga_gen gc"
      using assms ga_gample_subset
      unfolding ga_ample_def ga_en_def stutter_extend_en_def
      by (auto split: if_split_asm simp: ga_gample_empty_iff)

    lemma pid_pac_alt: "pid_pac pid = insert None (Some`{(pid',cac). pid'=pid})" 
      apply (auto simp: pid_pac_def split: option.splits)
      apply (case_tac x)
      apply auto
      done
  end    

  context sticky_prog begin
    sublocale ample_prog prog is_vis_var sticky_E "ga_ample sticky_E"
    proof -
      have aux: "Some ` A = Some ` B \<inter> pid_pac pid \<longleftrightarrow> A = {(pid', cac). (pid', cac) \<in> B \<and> pid' = pid}"
        for A B pid
      proof
        assume 1: "Some ` A = Some ` B \<inter> pid_pac pid"
        show "A = {(pid', cac). (pid', cac) \<in> B \<and> pid' = pid}"
          using 1
          apply (auto simp: pid_pac_alt)
          unfolding image_def
          apply auto
          using 1 by blast
      next
        show "Some ` A = Some ` B \<inter> pid_pac pid" if "A = {(pid', cac). (pid', cac) \<in> B \<and> pid' = pid}"
          using that by (auto simp: pid_pac_alt)
      qed
      show "ample_prog prog is_vis_var sticky_E (ga_ample sticky_E)"
        apply unfold_locales
        apply (frule ga_ample_neq_en_eq, clarsimp)
        apply (intro conjI)
        apply (auto 
          simp: ga_gample_def sticky_ga_def
          dest!: find_min_idx_f_SomeD
          split: option.splits if_split_asm) []
        apply (fastforce
          simp: ga_gample_def sticky_ga_def
          dest!: find_min_idx_f_SomeD
          split: option.splits if_split_asm) []
        unfolding aux (* TODO: Clean up! *)
        apply (simp add: inj_image_eq_iff pid_pac_def)
        apply (thin_tac "ga_ample c a = b" for a b c)
        apply (simp add: ga_gample_def split: option.splits prod.splits)
        apply (thin_tac "a \<noteq> ga_gen b" for a b)
        apply (drule find_min_idx_f_SomeD)
        apply clarsimp
        apply (rename_tac gc pid c as)
        apply (rule_tac x=pid in exI)
        apply (auto 
          split: if_split_asm prod.splits 
          simp: ga_gen_def comp.astep_impl_def)
        unfolding is_ample_static_def comp.astep_impl_def
        apply force
        done
    qed

  end

  text \<open> The following locale expresses a correct ample-reduction on 
    the level of subset and stuttering-equivalences of traces \<close>

  locale hl_reduction =
    visible_prog +
    ample: sa "\<lparr> g_V = UNIV, g_E = step, g_V0 = {pid_init_gc}, sa_L = pid_interp_gc \<rparr>"
    for step +
    assumes ample_accept_subset: "ample.accept w \<Longrightarrow> lv.sa.accept w"
    assumes ample_accept_stuttering: "lv.sa.accept w \<Longrightarrow> \<exists>w'. w\<approx>w' \<and> ample.accept w'"

  locale hl_ample_reduction =
    visible_prog +
    ample: sa "\<lparr> g_V = UNIV, g_E = rel_of_enex (ample, ga_ex), g_V0 = {pid_init_gc},
      sa_L = pid_interp_gc \<rparr>"
    for ample +
    assumes ample_accept_subset: "ample.accept w \<Longrightarrow> lv.sa.accept w"
    assumes ample_accept_stuttering: "lv.sa.accept w \<Longrightarrow> \<exists>w'. w\<approx>w' \<and> ample.accept w'"
  begin
    sublocale hl_reduction prog is_vis_var "rel_of_enex (ample, ga_ex)"
      apply unfold_locales
      using ample_accept_subset ample_accept_stuttering by auto
  end


  context sticky_prog
  begin
    sublocale hl_ample: hl_ample_reduction prog is_vis_var "ga_ample sticky_E"
      apply unfold_locales
      unfolding ample_rel_def[symmetric]
      unfolding reduced_automaton_def[symmetric]
      apply simp
      apply simp
      using ample_accept_subset
      apply simp
      apply (erule ample_accept_stuttering)
      apply blast
      done
  end    

  text \<open>Next, we implement the selection of a set of sticky edges\<close>
  context visible_prog begin
    definition "cr_ample \<equiv> do {
      sticky_E \<leftarrow> find_fas_init cfgc_G vis_edges;
      RETURN (ga_ample (sticky_E))
    }"

    lemma cr_ample_reduction: 
      "cr_ample \<le> SPEC (hl_ample_reduction prog is_vis_var)"
      unfolding cr_ample_def
      apply (refine_vcg order_trans[OF find_fas_init_correct])
      apply unfold_locales[]
      apply simp
    proof clarify  
      fix sticky_E
      assume "is_fas cfgc_G sticky_E" "vis_edges \<subseteq> sticky_E"
      then interpret sticky_prog prog is_vis_var sticky_E
        by unfold_locales

      show "hl_ample_reduction prog is_vis_var (ga_ample sticky_E)" by unfold_locales
    qed
  end  

  text \<open>We derive an implementation for finding the feedback arcs,
    and an efficient implementation for ga_gample.\<close>

  text \<open>We replace finding the sticky edges by an efficient algorithm\<close>

  context visible_prog begin
    definition ga_gample_m 
      :: "_ \<Rightarrow> _ \<Rightarrow> pid_global_config \<Rightarrow> global_action set" 
    where
      "ga_gample_m mem sticky_E gc \<equiv> let
        lcs = pid_global_config.processes gc;
        gs = pid_global_config.state gc;
        as = find_min_idx_f (\<lambda>lc.
          let
            c = local_config.command lc;
            ls = local_config.state lc;
            as = set (comp.succ_impl c)
          in
            if (\<forall>(a,_)\<in>as. read_globals a = {} \<and> write_globals a = {}) then
              let 
                as = {(a,c')\<in>as. la_en' (ls,gs) a}
              in
                if as={} \<or> (\<exists>(a,c')\<in>as. mem (c,c') sticky_E) then 
                  None 
                else 
                  Some (c,as)
            else
              None
        ) lcs
      in
        case as of
          Some (pid,c,as) \<Rightarrow> (\<lambda>(a,c'). (pid,c,a,c'))`as
        | None \<Rightarrow> ga_gen gc"

    lemma ga_gample_m_refine:
      fixes Rs :: "('si\<times>'s) set"
      shows "(ga_gample_m, ga_gample_m) \<in> (Id\<times>\<^sub>rId \<rightarrow> Rs \<rightarrow> bool_rel) \<rightarrow> Rs \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>set_rel"
    proof (intro fun_relI, simp)  
      fix m :: "cmdc\<times>cmdc \<Rightarrow> 's \<Rightarrow> bool" and m' :: "cmdc\<times>cmdc \<Rightarrow> 'si \<Rightarrow> bool" 
        and se se' gc
      assume "(m',m)\<in>Id \<rightarrow> Rs \<rightarrow> bool_rel" and "(se',se)\<in>Rs"
      hence "\<And>c c'. (m' (c,c') se', m (c,c') se)\<in>Id" 
        by parametricity simp_all
      hence A: "\<And>c c'. m' (c,c') se' = m (c,c') se" by simp
      show "ga_gample_m m' se' gc = ga_gample_m m se gc"
        unfolding ga_gample_m_def
        by (subst A) (rule refl)
    qed             

    lemma ga_gample_eq_gample_m: "ga_gample = ga_gample_m (\<in>)"
      unfolding ga_gample_def[abs_def] ga_gample_m_def[abs_def]
      by auto

    lemma stutter_extend_en_refine: 
      "(stutter_extend_en, stutter_extend_en) \<in> (R \<rightarrow> \<langle>Id\<rangle>set_rel) \<rightarrow> R \<rightarrow> \<langle>\<langle>Id\<rangle>option_rel\<rangle>set_rel"
      unfolding stutter_extend_en_def[abs_def]
      apply parametricity
      by auto

    lemma is_vis_var_refine: "(is_vis_var, is_vis_var) \<in> Id \<rightarrow> bool_rel" by simp  

    lemma vis_edges_refine: "(\<lambda>x. x\<in>vis_edges,vis_edges)\<in>\<langle>Id\<times>\<^sub>rId\<rangle>fun_set_rel"
      by (simp add: fun_set_rel_def br_def)

    lemma [autoref_op_pat_def]: 
      "vis_edges \<equiv> Autoref_Tagging.OP vis_edges"  
      "ga_gample_m \<equiv> Autoref_Tagging.OP ga_gample_m"  
      "cfgc_G \<equiv> Autoref_Tagging.OP cfgc_G"
      by simp_all

    schematic_goal cr_ample_impl1_aux:
      notes [autoref_rules] = 
        ga_gample_m_refine stutter_extend_en_refine is_vis_var_refine
        cfgc_G_impl_refine
        vis_edges_refine IdI[of prog]
      shows "(RETURN (?c::?'c),cr_ample)\<in>?R"
      unfolding cr_ample_def ga_ample_def ga_gample_eq_gample_m
      using [[autoref_trace_failed_id, autoref_trace_intf_unif]]
      by (autoref_monadic (plain, trace))
    concrete_definition cr_ample_impl1 uses cr_ample_impl1_aux

    lemma cr_ample_impl1_reduction: 
      "hl_ample_reduction prog is_vis_var cr_ample_impl1"
    proof -
      note cr_ample_impl1.refine[THEN nres_relD]
      also note cr_ample_reduction
      finally show ?thesis by simp
    qed

  end

  text \<open>The efficient implementation of @{const visible_prog.ga_gample} uses 
    the @{const collecti_index} function\<close> 

  lemma collecti_index_cong:
    assumes C: "\<And>i. i<length l \<Longrightarrow> f i (l!i) = f' i (l'!i)"
    assumes [simp]: "l=l'"
    shows "collecti_index f l = collecti_index f' l'"
  proof -
    {
      fix i0 s0
      assume "\<forall>i<length l. f (i0+i) (l!i) = f' (i0+i) (l!i)"
      hence "collecti_index' i0 s0 f l = collecti_index' i0 s0 f' l"
      proof (induction l arbitrary: i0 s0)
        case (Cons a l)

        from Cons.prems[THEN spec, of 0] have 
          [simp]: "f i0 a = f' i0 a" by simp

        from Cons.prems have 
          IHP: "\<forall>i<length l. f (Suc i0+i) (l!i) = f' (Suc i0+i) (l!i)"
          by auto

        show ?case by (auto split: bool.splits simp: Cons.IH[OF IHP])
      qed simp
    } from this[of 0 "{}"] show ?thesis using assms by simp
  qed  

  lemma find_min_idx_f_cong:
    assumes "\<And>x. x\<in>set l \<Longrightarrow> f x = f' x"
    assumes "l=l'"
    shows "find_min_idx_f f l = find_min_idx_f f' l'"
    unfolding assms(2)[symmetric]
    using assms(1)
    apply (induction l)
    apply (auto split: option.split)
    done


  lemma find_min_idx_impl_collecti: "(
      case find_min_idx_f f l of
        Some (i,r) \<Rightarrow> {i} \<times> s1 i r
      | None \<Rightarrow> {(i,r) | i r. i<length l \<and> r\<in>s2 i (l!i)}  
    )
  = (
    collecti_index (\<lambda>i x. 
      case f x of
        Some r \<Rightarrow> (True, s1 i r)
      | None \<Rightarrow> (False, s2 i x)
    ) l
  )" (is "?l=?r" is "_ = collecti_index ?fc l") 
  proof (cases "\<exists>i<length l. f (l!i) \<noteq> None")
    define i where "i \<equiv> LEAST i. i < length l \<and> f (l ! i) \<noteq> None"
    
    have C_ALT: "(\<exists>i<length l. f (l!i) \<noteq> None) 
      \<longleftrightarrow> (\<exists>i. i < length l \<and> fst (?fc i (l ! i)))"
      by (auto split: option.split)

    have i_alt: "i = (LEAST i. i < length l \<and> fst (?fc i (l ! i)))" 
      unfolding i_def 
      apply (fo_rule arg_cong)
      by (auto split: option.split)

    {  
      case True
  
      from LeastI_ex[OF True] obtain r where [simp]: "i<length l" "f (l!i) = Some r"
        by (auto simp: i_def)
  
      from True find_min_idx_f_LEAST_eq[of f l] 
        have "find_min_idx_f f l = Some (i, the (f (l ! i)))" 
        by (simp add: i_def)
      hence LEQ: "?l = {i} \<times> s1 i r" by simp

      from collecti_index_collect[of ?fc l, folded i_alt] True C_ALT have 
        REQ: "?r = {i} \<times> snd (?fc i (l!i))" 
        by simp
      show "?l=?r" unfolding LEQ unfolding REQ by auto
    }
    {
      case False
      from False find_min_idx_f_LEAST_eq[of f l] 
        have "find_min_idx_f f l = None" by simp
      hence LEQ: "?l = {(i,r) | i r. i<length l \<and> r\<in>s2 i (l!i)}" by simp

      from False C_ALT collecti_index_collect[of ?fc l] have
        REQ: "?r = {(i, x) |i x. i < length l \<and> x \<in> snd (?fc i (l ! i))}"
        by auto

      show "?l=?r" unfolding LEQ unfolding REQ using False by auto
    }
  qed


  lemma find_min_idx_impl_collecti_scheme: 
    assumes "\<And>x. s11 x = (case x of (i,r) \<Rightarrow> {i} \<times> iss i r)"
    assumes "s12 = {(i,r) | i r. i<length l \<and> r\<in>isn i (l!i)}"
    assumes "\<And>i. i<length l \<Longrightarrow> f2 i (l!i) = (case f (l!i) of
        Some r \<Rightarrow> (True, iss i r)
      | None \<Rightarrow> (False, isn i (l!i)))"
    shows "(case find_min_idx_f f l of Some x \<Rightarrow> s11 x | None \<Rightarrow> s12)
      = (collecti_index f2 l)"
    apply (simp only: assms(1,2,3) cong: collecti_index_cong)  
    apply (subst find_min_idx_impl_collecti)
    apply simp
    done


  schematic_goal stutter_extend_en_list_aux: "(?c, stutter_extend_en) 
    \<in> (R \<rightarrow> \<langle>S\<rangle>list_set_rel) \<rightarrow> R \<rightarrow> \<langle>\<langle>S\<rangle>option_rel\<rangle>list_set_rel"
    unfolding stutter_extend_en_def[abs_def]
    apply (autoref)
    done
  concrete_definition stutter_extend_en_list uses stutter_extend_en_list_aux

  lemma succ_of_enex_impl_aux: 
    "{s'. \<exists>a\<in>en s. s'=ex a s} = (\<lambda>a. ex a s)`en s" by auto

  schematic_goal succ_of_enex_list_aux: "(?c, succ_of_enex) \<in> 
    (Id \<rightarrow> \<langle>Id\<rangle>list_set_rel) \<times>\<^sub>r (Id \<rightarrow> Id \<rightarrow> Id) \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
    unfolding succ_of_enex_def[abs_def]
    unfolding succ_of_enex_impl_aux
    by (autoref (trace, keep_goal))
  concrete_definition succ_of_enex_list uses succ_of_enex_list_aux

  schematic_goal pred_of_enex_list_aux: "(?c, pred_of_enex) \<in> 
    (Id \<rightarrow> \<langle>Id\<rangle>list_set_rel) \<times>\<^sub>r (Id \<rightarrow> Id \<rightarrow> Id) \<rightarrow> Id \<rightarrow> Id \<rightarrow> bool_rel"
    unfolding pred_of_enex_def[abs_def]
    by (autoref (trace, keep_goal))
  concrete_definition pred_of_enex_list uses pred_of_enex_list_aux

  (* TODO: can this be defined using autoref? *)
  definition "rel_of_enex_list enex \<equiv> rel_of_pred (pred_of_enex_list enex)"
  lemma rel_of_enex_list_refine: "(rel_of_enex_list, rel_of_enex) \<in> 
    (Id \<rightarrow> \<langle>Id\<rangle>list_set_rel) \<times>\<^sub>r (Id \<rightarrow> Id \<rightarrow> Id) \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle> set_rel"
  proof -
    have 1: "rel_of_enex_list = rel_of_pred \<circ> pred_of_enex_list" using rel_of_enex_list_def by force
    have 2: "rel_of_enex = rel_of_pred \<circ> pred_of_enex" by auto
    have 3: "(rel_of_pred, rel_of_pred) \<in> (Id \<rightarrow> Id \<rightarrow> bool_rel) \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>set_rel" by auto
    show ?thesis unfolding 1 2 by (parametricity add: 3 pred_of_enex_list.refine)
  qed

  context visible_prog begin
    definition "ga_gample_mi2 mem sticky_E (gc::pid_global_config) = (
      let 
        lcs = pid_global_config.processes gc;
        gs = pid_global_config.state gc
      in
        collecti_index (\<lambda>_ lc. let
            c = local_config.command lc;
            ls = local_config.state lc;
            as = set (comp.succ_impl c);
            s={(a,c')\<in>as. la_en' (ls,gs) a};
            ample = 
              s\<noteq>{} 
            \<and> (\<forall>(a,_)\<in>as. read_globals a = {} \<and> write_globals a = {}) 
            \<and> (\<forall>(a,c')\<in>s. \<not> mem (c,c') sticky_E)
          in
            (ample,{c}\<times>s)
        ) lcs
    )"

    lemma ga_gample_mi2_impl: 
      "ga_gample_m mem sticky_E gc = ga_gample_mi2 mem sticky_E gc"
      unfolding ga_gample_m_def ga_gample_mi2_def
      apply simp
      apply (rule find_min_idx_impl_collecti_scheme[where 
          iss="\<lambda>pid (c,S). (\<lambda>(a,c'). (c,a,c'))`S" and
          isn="\<lambda>pid lc. {(c,a,c'). cfgc c a c' 
            \<and> c = cmd_of_pid gc pid 
            \<and> la_en' (local_config.state lc, pid_global_config.state gc) a}"]
      )
      apply auto []
      unfolding ga_gen_def
      apply auto []
      apply (auto simp: comp.astep_impl_def)
      done

    definition "cr_ample_impl2 \<equiv>
      let sticky = find_fas_init_code (=) bounded_hashcode_nat
         (def_hashmap_size TYPE(nat)) cfgc_G_impl (\<lambda>x. x \<in> vis_edges)
      in stutter_extend_en (ga_gample_mi2 (\<lambda>x f. f x) sticky)"

    definition "ample_step_impl2 \<equiv> rel_of_enex (cr_ample_impl2,ga_ex)"

    lemma cr_ample_impl2_reduction: 
      "hl_reduction prog is_vis_var ample_step_impl2"
    proof -
      from cr_ample_impl1_reduction 
      interpret hl_ample_reduction prog is_vis_var cr_ample_impl1 .
      
      have 1: "ample_step_impl2 = rel_of_enex (cr_ample_impl1, ga_ex)"
        unfolding ample_step_impl2_def cr_ample_impl1_def cr_ample_impl2_def
        unfolding ga_gample_mi2_impl[abs_def]
        by simp

      show ?thesis
        apply unfold_locales
        unfolding 1
        apply simp
        apply simp
        apply (blast intro: ample_accept_subset ample_accept_stuttering)+
        done
    qed
  end
        
text \<open>Implementing the State\<close>
type_synonym valuation_impl = "(ident,uint32) mapping"

definition "vi_\<alpha> \<equiv> map_option Rep_uint32 \<circ>\<circ> Mapping.rep"
abbreviation "vi_rel \<equiv> br vi_\<alpha> (\<lambda>_. True)"

abbreviation "val_rel \<equiv> br Rep_uint32 (\<lambda>_. True)"

lemma vi_rel_rew: 
  "(x = vi_\<alpha> y) \<longleftrightarrow> (y,x)\<in>vi_rel"
  "(vi_\<alpha> y = x) \<longleftrightarrow> (y,x)\<in>vi_rel"
  by (auto simp: br_def)

export_code Mapping.lookup Mapping.update Mapping.empty checking SML

lift_definition vi_empty :: "valuation_impl" 
  is "Map.empty::valuation" .

lemma [code]: "vi_empty = Mapping.empty" by transfer simp
lemma vi_empty_correct: "vi_\<alpha> vi_empty = Map.empty"
  unfolding vi_\<alpha>_def
  by transfer auto

lift_definition vi_lookup :: "valuation_impl \<Rightarrow> ident \<rightharpoonup> uint32" 
  is "\<lambda>vi::valuation. \<lambda>x. vi x" .
lemma [code]: "vi_lookup = Mapping.lookup"
  apply (intro ext)
  unfolding vi_lookup_def Mapping.lookup_def map_fun_def[abs_def] o_def
    id_apply option.map_comp Rep_uint32_inverse option.map_ident
  by simp

lemma vi_lookup_correct: "vi_lookup v x = map_option Abs_uint32 (vi_\<alpha> v x)"
  unfolding vi_\<alpha>_def
  apply transfer
  apply (simp add: option.map_comp o_def option.map_ident)
  done

lift_definition vi_update :: "ident \<Rightarrow> uint32 \<Rightarrow> valuation_impl \<Rightarrow> valuation_impl" 
  is "\<lambda>x v. \<lambda>vi::valuation. vi(x\<mapsto>v)" .
lemma [code]: "vi_update = Mapping.update"
  by transfer simp

lemma vi_update_correct: "vi_\<alpha> (vi_update k v m) = vi_\<alpha> m (k\<mapsto>Rep_uint32 v)"
  unfolding vi_\<alpha>_def
  by transfer simp

export_code vi_lookup vi_update vi_empty checking SML 


record local_state_impl = 
  variables :: valuation_impl

record global_state_impl = 
  variables :: valuation_impl

type_synonym focused_state_impl = "local_state_impl \<times> global_state_impl"

type_synonym local_config_impl 
  = "(cmdc,local_state_impl) Gen_Scheduler.local_config"
type_synonym pid_global_config_impl 
  = "(cmdc,local_state_impl,global_state_impl) Pid_Scheduler.pid_global_config"

definition "local_state_rel \<equiv> {
  (\<lparr> local_state_impl.variables = vi \<rparr>, \<lparr> local_state.variables = v  \<rparr>) | vi v.
    v = vi_\<alpha> vi 
  }"

definition "global_state_rel \<equiv> {
  (\<lparr> global_state_impl.variables = vi \<rparr>, \<lparr> global_state.variables = v  \<rparr>) | vi v.
    v = vi_\<alpha> vi 
  }"

abbreviation "focused_state_rel \<equiv> local_state_rel \<times>\<^sub>r global_state_rel"

definition "local_config_rel \<equiv> {
  (\<lparr> local_config.command = ci, local_config.state=lsi \<rparr>, 
   \<lparr> local_config.command = c, local_config.state=ls  \<rparr>) | ci c lsi ls.
    (ci::cmdc,c)\<in>Id \<and> (lsi,ls)\<in>local_state_rel
  }"

definition "global_config_rel \<equiv> {
  (\<lparr> pid_global_config.processes = psi, pid_global_config.state = gsi \<rparr>,
   \<lparr> pid_global_config.processes = ps, pid_global_config.state = gs \<rparr>) | psi ps gsi gs.
   (psi,ps)\<in>\<langle>local_config_rel\<rangle>list_rel \<and> (gsi,gs)\<in>global_state_rel
}"

definition "init_valuation_impl vd \<equiv> fold (\<lambda>x v. vi_update x 0 v) vd (vi_empty)"

lemma init_valuation_impl: 
  "(init_valuation_impl, init_valuation) \<in> \<langle>Id\<rangle>list_rel \<rightarrow> vi_rel"
proof -
  {
    fix vd m
    have "m ++ init_valuation vd = fold (\<lambda>x v. v(x\<mapsto>0)) vd m"
      apply (rule sym)
      apply (induction vd arbitrary: m)
      unfolding init_valuation_def[abs_def]
      apply (auto intro!: ext simp: Map.map_add_def)
      done
  } note aux=this
  have E1: "\<And>vd. init_valuation vd = fold (\<lambda>x v. v(x\<mapsto>0)) vd Map.empty"
    by (subst aux[symmetric]) simp
    
  have E2: "\<And>vdi vd. (vdi,vd)\<in>\<langle>Id\<rangle>list_rel 
    \<Longrightarrow> (init_valuation_impl vdi, fold (\<lambda>x v. v(x\<mapsto>0)) vd Map.empty) \<in> vi_rel"
    unfolding init_valuation_impl_def
    apply parametricity
    apply (auto simp: vi_update_correct vi_empty_correct br_def zero_uint32.rep_eq)
    done

  show ?thesis
    apply (intro fun_relI)
    apply (subst E1)
    apply (rule E2)
    by auto
qed

context cprog begin

  definition init_pc_impl :: "proc_decl \<Rightarrow> local_config_impl" where
    "init_pc_impl pd \<equiv> \<lparr>
      local_config.command = comp.\<gamma> (proc_decl.body pd),
      local_config.state = \<lparr>
        local_state_impl.variables = init_valuation_impl (proc_decl.local_vars pd)
      \<rparr>
    \<rparr>"

  lemma init_pc_impl: "(init_pc_impl, init_pc) \<in> Id \<rightarrow> local_config_rel"
    apply (rule fun_relI)
    unfolding init_pc_impl_def init_pc_def local_config_rel_def local_state_rel_def
    apply (simp del: pair_in_Id_conv, intro conjI)
    apply simp
    apply (simp only: vi_rel_rew)
    apply (parametricity add: init_valuation_impl)
    apply simp
    done
  
  definition pid_init_gc_impl :: "pid_global_config_impl" where
    "pid_init_gc_impl \<equiv> \<lparr>
      pid_global_config.processes = (map init_pc_impl (program.processes prog)),
      pid_global_config.state = \<lparr>
        global_state_impl.variables = init_valuation_impl (program.global_vars prog)
      \<rparr>
    \<rparr>"
  
  lemma pid_init_gc_impl: "(pid_init_gc_impl, pid_init_gc) \<in> global_config_rel"
    unfolding pid_init_gc_impl_def pid_init_gc_def global_config_rel_def global_state_rel_def
    apply (simp del: pair_in_Id_conv, intro conjI)
    apply (parametricity add: init_pc_impl)
    apply simp
    apply (simp only: vi_rel_rew)
    apply (parametricity add: init_valuation_impl)
    apply simp
    done  

end
  
lift_definition val_of_bool_impl :: "bool \<Rightarrow> uint32" is val_of_bool .
lemma [code]: "val_of_bool_impl b = (if b then 1 else 0)"
  by transfer auto

lift_definition bool_of_val_impl :: "uint32 \<Rightarrow> bool" is bool_of_val .
lemma [code]: "bool_of_val_impl v = (v\<noteq>0)"
  by transfer (auto simp: bool_of_val_def)

definition "set_of_rel R \<equiv> {(a,b) . R b a}"
definition "rel_of_set S \<equiv> \<lambda>b a. (a,b)\<in>S"

lemma [simp]: 
  "(a,b)\<in>set_of_rel R \<longleftrightarrow> R b a"
  "rel_of_set S b a \<longleftrightarrow> (a,b)\<in>S"
  unfolding rel_of_set_def set_of_rel_def
  by auto

lemma [simp]:
  "set_of_rel (rel_of_set S) = S"
  "rel_of_set (set_of_rel R) = R"
  unfolding rel_of_set_def set_of_rel_def
  by auto

lemma rel_fun_2set: "rel_fun A B = rel_of_set (set_of_rel A \<rightarrow> set_of_rel B)"
  unfolding rel_fun_def fun_rel_def
  unfolding rel_of_set_def set_of_rel_def
  by (auto)

lemma [simp]: 
  "set_of_rel cr_uint32 = val_rel"
  "set_of_rel (=) = Id"
  by (auto simp: br_def cr_uint32_def)

lemma bool_of_val_impl: "(bool_of_val_impl, bool_of_val) \<in> val_rel \<rightarrow> bool_rel"
  using bool_of_val_impl.transfer
  by (simp add: rel_fun_2set)
  


lemma smod_by_div_abs: "a smod b = a - a sdiv b * b"
  using sdiv_smod_id[of a b]
  by (metis add_diff_cancel2)

lift_definition sdiv_impl :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "(sdiv)" .
lift_definition smod_impl :: "uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" is "(smod)" .

(* TODO: Is there a more efficient way? *)
lemma [code]: "sdiv_impl x y = Abs_uint32' (Rep_uint32' x sdiv Rep_uint32' y)"
  apply transfer
  by simp

lemma [code]: "smod_impl a b = a - sdiv_impl a b * b"
  apply transfer
  using sdiv_smod_id
  by (metis add_diff_cancel2)
  

primrec eval_bin_op_impl_aux :: "bin_op \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "eval_bin_op_impl_aux bo_plus v1 v2 = v1+v2"
| "eval_bin_op_impl_aux bo_minus v1 v2 = v1-v2"
| "eval_bin_op_impl_aux bo_mul v1 v2 = v1*v2"
| "eval_bin_op_impl_aux bo_div v1 v2 = sdiv_impl v1 v2"
| "eval_bin_op_impl_aux bo_mod v1 v2 = smod_impl v1 v2"
| "eval_bin_op_impl_aux bo_less v1 v2 = val_of_bool_impl (v1 < v2)"
| "eval_bin_op_impl_aux bo_less_eq v1 v2 = val_of_bool_impl (v1 \<le> v2)"
| "eval_bin_op_impl_aux bo_eq v1 v2 = val_of_bool_impl (v1 = v2)"
| "eval_bin_op_impl_aux bo_and v1 v2 = v1 AND v2"
| "eval_bin_op_impl_aux bo_or v1 v2 = v1 OR v2"
| "eval_bin_op_impl_aux bo_xor v1 v2 = v1 XOR v2"

lift_definition eval_bin_op_impl :: "bin_op \<Rightarrow> uint32 \<Rightarrow> uint32 \<Rightarrow> uint32"
  is eval_bin_op .
print_theorems

lemma [code]: "eval_bin_op_impl bop v1 v2 = eval_bin_op_impl_aux bop v1 v2"
  apply (cases bop)
  apply simp_all
  apply (transfer, simp)+
  done  



primrec eval_un_op_impl_aux :: "un_op \<Rightarrow> uint32 \<Rightarrow> uint32" where
  "eval_un_op_impl_aux uo_minus v = -v"
| "eval_un_op_impl_aux uo_not v = NOT v"

lift_definition eval_un_op_impl :: "un_op \<Rightarrow> uint32 \<Rightarrow> uint32"
  is eval_un_op .

lemma [code]: "eval_un_op_impl uop v = eval_un_op_impl_aux uop v"
  apply (cases uop)
  apply simp_all
  apply (transfer, simp)+
  done  




fun eval_exp_impl :: "exp \<Rightarrow> focused_state_impl \<rightharpoonup> uint32" where
  "eval_exp_impl (e_var x) (ls,gs) = do {
    let lv = local_state_impl.variables ls; 
    let gv = global_state_impl.variables gs;
    case vi_lookup lv x of
      Some v \<Rightarrow> Some v
    | None \<Rightarrow> (case vi_lookup gv x of
        Some v \<Rightarrow> Some v
      | None \<Rightarrow> None)
  }"
| "eval_exp_impl (e_localvar x) (ls,gs) = vi_lookup (local_state_impl.variables ls) x"
| "eval_exp_impl (e_globalvar x) (ls,gs) = vi_lookup (global_state_impl.variables gs) x"
| "eval_exp_impl (e_const n) fs = do {
    assert_option (n\<ge>min_signed \<and> n\<le>max_signed);
    Some (uint32_of_int n)
  }"
| "eval_exp_impl (e_bin bop e1 e2) fs = do {
    v1\<leftarrow>eval_exp_impl e1 fs;
    v2\<leftarrow>eval_exp_impl e2 fs;
    Some (eval_bin_op_impl bop v1 v2)
    }"
| "eval_exp_impl (e_un uop e) fs = do {
    v\<leftarrow>eval_exp_impl e fs;
    Some (eval_un_op_impl uop v)
    }"

(* TODO: Move *)
lemma map_option_bind: "map_option f (m\<bind>g) = m \<bind> (map_option f o g)"
  by (auto split: Option.bind_split)

lemma val_option_rel_as_eq: "(a,b)\<in>\<langle>val_rel\<rangle>option_rel \<longleftrightarrow> map_option Rep_uint32 a = b"
  unfolding br_def
  apply (cases a)
  apply (cases b, simp_all)
  apply (cases b, auto)
  done

lemma eval_exp_impl: "(eval_exp_impl, eval_exp) \<in> Id \<rightarrow> focused_state_rel \<rightarrow> \<langle>val_rel\<rangle>option_rel"
proof -
  {
    fix e ls gs lsi gsi
    assume "(lsi,ls)\<in>local_state_rel" "(gsi,gs)\<in>global_state_rel"
    hence "map_option Rep_uint32 (eval_exp_impl e (lsi,gsi)) = eval_exp e (ls,gs)"
      apply (induction e)
      apply (auto 
        simp: local_state_rel_def global_state_rel_def br_def
        simp: vi_lookup_correct vi_update_correct
        simp: Abs_uint32_inverse[simplified] uint32_of_int.rep_eq signed_of_int_def
        simp: option.map_comp option.map_ident o_def map_option_bind
        simp: eval_bin_op_impl.rep_eq eval_un_op_impl.rep_eq
        split: option.splits)
      apply (drule sym)
      apply (drule sym)
      apply (simp split: Option.bind_split)

      apply (drule sym)
      apply (simp split: Option.bind_split)
      done
  } thus ?thesis
    by (auto simp: val_option_rel_as_eq)
qed

text \<open>Enabledness and effects of actions\<close>
primrec la_en_impl :: "focused_state_impl \<Rightarrow> action \<rightharpoonup> bool" where
  "la_en_impl fs (AAssign e _ _) = do {
    v \<leftarrow> eval_exp_impl e fs;
    Some (bool_of_val_impl v)}"
| "la_en_impl fs (AAssign_local e _ _) = do {
    v \<leftarrow> eval_exp_impl e fs;
    Some (bool_of_val_impl v)}"
| "la_en_impl fs (AAssign_global e _ _) = do {
    v \<leftarrow> eval_exp_impl e fs;
    Some (bool_of_val_impl v)}"
| "la_en_impl fs (ATest e) = do {
    v \<leftarrow> eval_exp_impl e fs;
    Some (bool_of_val_impl v)}"
| "la_en_impl _ (ASkip) = Some True"

lemma param_rec_action[param]: "(rec_action, rec_action) \<in> (Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> A)
    \<rightarrow> (Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> A)
       \<rightarrow> (Id \<rightarrow> Id \<rightarrow> Id \<rightarrow> A) \<rightarrow> (Id \<rightarrow> A) \<rightarrow> A \<rightarrow> Id \<rightarrow> A"
  apply (intro fun_relI)
  subgoal for fi1 f1 fi2 f2 fi3 f3 fi4 f4 fi5 f5 ai a
    apply simp
    apply (induction a)
    apply simp_all
    apply (parametricity, simp_all?)+
    done
  done 

(* TODO: Move *)
lemma param_option_bind[param]:
  "(Option.bind, Option.bind) \<in> \<langle>A\<rangle>option_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle>option_rel) \<rightarrow> \<langle>B\<rangle>option_rel"
  unfolding Option.bind_def by parametricity

lemma la_en_impl: "(la_en_impl,la_en) \<in> focused_state_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>option_rel"
  unfolding la_en_impl_def la_en_def
  by (parametricity add: eval_exp_impl bool_of_val_impl)

definition "la_en'_impl fs a \<equiv> case la_en_impl fs a of Some b \<Rightarrow> b | None \<Rightarrow> False"
  
lemma la_en'_impl: "(la_en'_impl,la_en') \<in> focused_state_rel \<rightarrow> Id \<rightarrow> bool_rel"
  unfolding la_en'_impl_def[abs_def] la_en'_def[abs_def]
  by (parametricity add: la_en_impl)    

abbreviation "exists_var_impl v x \<equiv> vi_lookup v x \<noteq> None"

fun la_ex_impl :: "focused_state_impl \<Rightarrow> action \<rightharpoonup> focused_state_impl" where
  "la_ex_impl (ls,gs) (AAssign ge x e) = do {
    v \<leftarrow> eval_exp_impl ge (ls,gs);
    assert_option (bool_of_val_impl v); 
    v \<leftarrow> eval_exp_impl e (ls,gs);
    if exists_var_impl (local_state_impl.variables ls) x then do {
      let ls = local_state_impl.variables_update (vi_update x v) ls;
      Some (ls,gs)
    } else do {
      assert_option (exists_var_impl (global_state_impl.variables gs) x);
      let gs = global_state_impl.variables_update (vi_update x v) gs;
      Some (ls,gs)
    }
  }"
| "la_ex_impl (ls,gs) (AAssign_local ge x e) = do {
    v \<leftarrow> eval_exp_impl ge (ls,gs);
    assert_option (bool_of_val_impl v); 
    v \<leftarrow> eval_exp_impl e (ls,gs);
    assert_option (exists_var_impl (local_state_impl.variables ls) x);
    let ls = local_state_impl.variables_update (vi_update x v) ls;
    Some (ls,gs)
  }"
| "la_ex_impl (ls,gs) (AAssign_global ge x e) = do {
    v \<leftarrow> eval_exp_impl ge (ls,gs);
    assert_option (bool_of_val_impl v); 
    v \<leftarrow> eval_exp_impl e (ls,gs);
    assert_option (exists_var_impl (global_state_impl.variables gs) x);
    let gs = global_state_impl.variables_update (vi_update x v) gs;
    Some (ls,gs)
  }"
| "la_ex_impl fs (ATest e) = do {
    v \<leftarrow> eval_exp_impl e fs;
    assert_option (bool_of_val_impl v); 
    Some fs
  }"
| "la_ex_impl fs ASkip = Some fs"

(* TODO: Move *)
lemma param_assert_option[param]:
  "(assert_option, assert_option) \<in> bool_rel \<rightarrow> \<langle>unit_rel\<rangle>option_rel"
  unfolding assert_option_def by parametricity


lemma la_ex_impl: "(la_ex_impl, la_ex) 
  \<in> focused_state_rel \<rightarrow> Id \<rightarrow> \<langle>focused_state_rel\<rangle>option_rel"
proof (intro fun_relI)
  fix fsi fs and ai a :: action
  assume "(fsi,fs)\<in>focused_state_rel" "(ai,a)\<in>Id"
  thus "(la_ex_impl fsi ai, la_ex fs a)\<in>\<langle>focused_state_rel\<rangle>option_rel"
    apply (cases fs, cases fsi, clarsimp)
    apply (cases a)
    apply simp_all
    apply (parametricity add: eval_exp_impl bool_of_val_impl)
    apply (auto 
      simp: local_state_rel_def global_state_rel_def
      simp: vi_lookup_correct vi_update_correct 
      simp: br_def 
      intro: domI) [7]
    apply (parametricity add: eval_exp_impl bool_of_val_impl)
    apply (auto 
      simp: local_state_rel_def global_state_rel_def
      simp: vi_lookup_correct vi_update_correct 
      br_def intro: domI) [9]
    apply (parametricity add: eval_exp_impl bool_of_val_impl)
    apply (auto 
      simp: local_state_rel_def global_state_rel_def
      simp: vi_lookup_correct vi_update_correct 
      br_def intro: domI) [4]
    apply (parametricity add: eval_exp_impl bool_of_val_impl)
    apply simp
    done
qed    

definition "la_ex'_impl fs a \<equiv> case la_ex_impl fs a of Some fs' \<Rightarrow> fs' | None \<Rightarrow> fs"
lemma la_ex'_impl: "(la_ex'_impl,la_ex') \<in> focused_state_rel \<rightarrow> Id \<rightarrow> focused_state_rel"
  unfolding la_ex'_impl_def[abs_def] la_ex'_def[abs_def]
  by (parametricity add: la_ex_impl)

lemma param_collecti_index: "(collecti_index, collecti_index) \<in> 
    (nat_rel \<rightarrow> B \<rightarrow> bool_rel \<times>\<^sub>r \<langle>Id\<rangle>set_rel) \<rightarrow> \<langle>B\<rangle>list_rel \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle>set_rel"
  unfolding collecti_index'_def
  apply parametricity  
  apply auto
  done

export_code la_ex_impl la_en_impl checking SML

context visible_prog
begin

  definition "ga_gample_mi3 mem sticky_E (gc::pid_global_config_impl) = (
    let 
      lcs = pid_global_config.processes gc;
      gs = pid_global_config.state gc
    in
      collecti_index (\<lambda>_ lc. let
          c = local_config.command lc;
          ls = local_config.state lc;
          as = set (comp.succ_impl c);
          s={(a,c')\<in>as. la_en'_impl (ls,gs) a};
          ample = 
            s\<noteq>{} 
          \<and> (\<forall>(a,_)\<in>as. read_globals a = {} \<and> write_globals a = {}) 
          \<and> (\<forall>(a,c')\<in>s. \<not> mem (c,c') sticky_E)
        in
          (ample,{c}\<times>s)
      ) lcs
  )"

  lemma ga_gample_mi3_refine: 
    "(ga_gample_mi3, ga_gample_mi2)\<in> 
      Id \<rightarrow> Id \<rightarrow> global_config_rel \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle>set_rel"
  proof -
    have [param]: "(comp.succ_impl,comp.succ_impl)\<in>Id\<rightarrow>\<langle>Id\<times>\<^sub>rId\<rangle>list_rel"
      by simp

    from la_en'_impl have aux1: "\<And>fsi fs a. (fsi,fs)\<in>focused_state_rel \<Longrightarrow>
      la_en'_impl fsi a = la_en' fs a"
      apply (rule_tac IdD)
      apply parametricity
      by auto

    show ?thesis
      using [[goals_limit=1]]
      apply (intro fun_relI)
      unfolding ga_gample_mi3_def ga_gample_mi2_def
      apply (parametricity add: param_collecti_index la_en'_impl)
      apply (auto simp add: global_config_rel_def local_config_rel_def) []
      apply (auto simp add: global_config_rel_def local_config_rel_def) []
      apply (auto simp add: global_config_rel_def local_config_rel_def) []
      apply (auto simp add: global_config_rel_def local_config_rel_def) []
      apply simp
      using aux1
      apply (auto simp add: global_config_rel_def local_config_rel_def) []
      apply simp_all
      done

  qed    

  definition (in cprog) "is_vis_edge is_vis_var \<equiv> \<lambda>(c,c'). 
    \<exists>(a,cc')\<in>set (comp.succ_impl c). c'=cc' \<and> (\<exists>v\<in>write_globals a. is_vis_var v)"

  lemma is_vis_edge_correct: "is_vis_edge is_vis_var = (\<lambda>x. x\<in>vis_edges)"
    unfolding is_vis_edge_def vis_edges_def
    by (auto intro!: ext simp: comp.astep_impl_def)


  definition "cr_ample_impl3 \<equiv>
    let sticky = find_fas_init_code (=) bounded_hashcode_nat
         (def_hashmap_size TYPE(nat)) cfgc_G_impl (\<lambda>x. x \<in> vis_edges)
    in stutter_extend_en (ga_gample_mi3 (\<lambda>x f. f x) sticky)"

    
  lemma cr_ample_impl3_refine: "(cr_ample_impl3, cr_ample_impl2) 
    \<in> global_config_rel \<rightarrow> \<langle>\<langle>nat_rel\<times>\<^sub>rId\<rangle>option_rel\<rangle>set_rel"
  proof -
    have [param]: "\<And>R S. S=Id \<Longrightarrow> 
      (stutter_extend_en, stutter_extend_en)
        \<in> (R \<rightarrow> \<langle>S\<rangle>set_rel) \<rightarrow> R \<rightarrow> \<langle>\<langle>S\<rangle>option_rel\<rangle>set_rel"
      apply (simp only: )
      by (rule stutter_extend_en_refine)
    
    show ?thesis  
      unfolding cr_ample_impl3_def cr_ample_impl2_def is_vis_edge_correct
      apply (parametricity add: stutter_extend_en_refine ga_gample_mi3_refine)
      apply (rule IdI)
      by auto
  qed      
      
(* TODO: The current Pid_Scheduler-locale is focused on refinement.
  We cannot use it to get an instantiation of ga_gex_impl.*)

  definition (in -) ga_gex_impl 
    :: "global_action \<Rightarrow> pid_global_config_impl \<Rightarrow> pid_global_config_impl"
  where
    "ga_gex_impl ga gc \<equiv> let 
      (pid,c,a,c') = ga;
      fs = fs_of_pid gc pid;
      (ls',gs') = la_ex'_impl fs a;
      gc' = \<lparr> 
          pid_global_config.processes = (pid_global_config.processes gc)
            [pid := 
              \<lparr> local_config.command = c', local_config.state = ls'\<rparr>
            ],
          pid_global_config.state = gs'\<rparr>
    in
      gc'"


  lemma lc_of_pid_refine:
    assumes V: "pid_valid gc pid"    
    assumes [param]: "(pidi,pid)\<in>nat_rel"
    assumes GCI: "(gci,gc)\<in>global_config_rel"
    shows "(lc_of_pid gci pidi, lc_of_pid gc pid)\<in>local_config_rel"
    apply parametricity
    apply fact
    using GCI by (auto simp: global_config_rel_def)
    
  lemma ls_of_pid_refine:
    assumes "pid_valid gc pid"    
    assumes "(pidi,pid)\<in>nat_rel"
    assumes "(gci,gc)\<in>global_config_rel"
    shows "(ls_of_pid gci pidi, ls_of_pid gc pid)\<in>local_state_rel"
    using lc_of_pid_refine[OF assms] unfolding local_config_rel_def by auto


  lemma ga_gex_impl:
    assumes V: "pid_valid gc pid"    
    assumes [param]: "(pidi,pid)\<in>Id" "(ci,c)\<in>Id" 
      "(ai,a)\<in>Id" and CI'I: "(ci',c')\<in>Id" and GCI[param]: "(gci,gc)\<in>global_config_rel"
    shows "(ga_gex_impl (pidi,ci,ai,ci') gci, ga_gex (pid,c,a,c') gc) \<in> global_config_rel"
    unfolding ga_gex_impl_def[abs_def] ga_gex_def[abs_def]
    apply simp
    apply (parametricity add: la_ex'_impl ls_of_pid_refine[OF V])
    using GCI CI'I
    apply (auto simp: global_config_rel_def local_config_rel_def) []
    apply parametricity
    apply auto []
    using GCI
    apply (auto simp: global_config_rel_def) []
    done

  definition (in -) "ga_ex_impl \<equiv> stutter_extend_ex ga_gex_impl"

  fun ga_valid where
    "ga_valid gc None = True"
  | "ga_valid gc (Some (pid,c,a,c')) = pid_valid gc pid"  


  lemma ga_ex_impl:
    assumes V: "ga_valid gc ga"    
    assumes P: "(gai,ga)\<in>Id" "(gci,gc)\<in>global_config_rel"
    shows "(ga_ex_impl gai gci, ga_ex ga gc) \<in> global_config_rel"
    using assms
    apply (cases "(gc,ga)" rule: ga_valid.cases)
    using P
    apply (simp add: ga_ex_impl_def)

    apply (simp add: ga_ex_impl_def ga_ex_def)
    apply (parametricity add: ga_gex_impl)
    by auto

  definition "ample_step_impl3 \<equiv> rel_of_enex (cr_ample_impl3,ga_ex_impl)"

  definition (in -) pid_interp_gc_impl 
    :: "(ident \<Rightarrow> bool) \<Rightarrow> pid_global_config_impl \<Rightarrow> exp set"
  where
    "pid_interp_gc_impl is_vis_var gci \<equiv> sm_props (
    vi_\<alpha> (global_state_impl.variables (pid_global_config.state gci)) |` Collect is_vis_var
  )"

  lemma pid_interp_gc_impl: 
    "(pid_interp_gc_impl is_vis_var, pid_interp_gc) \<in> global_config_rel \<rightarrow> Id"
    apply rule
    unfolding pid_interp_gc_impl_def pid_interp_gc_def
    apply (auto simp: global_config_rel_def global_state_rel_def 
      interp_gs_def sm_props_def br_def)
    done

  lemma cr_ample_impl3_sim_aux:
    assumes GCI: "(gci, gc) \<in> global_config_rel"
    assumes GA: "ga \<in> cr_ample_impl3 gci"
    shows "\<exists>gc'. ga\<in>cr_ample_impl2 gc 
      \<and> gc'=ga_ex ga gc 
      \<and> (ga_ex_impl ga gci, gc')\<in>global_config_rel"
  proof (clarsimp, safe)
    show G1: "ga\<in>cr_ample_impl2 gc"
      using cr_ample_impl3_refine[param_fo, OF GCI] GA by auto

    { (* TODO: We are re-proving the validity of the action, due
        to the lack of a clean refinement argumentation *)
      fix mem sticky_E gc pid c
      assume "(pid,c)\<in>ga_gample_m mem sticky_E gc"
      hence "pid_valid gc pid"
        unfolding ga_gample_m_def
        apply (auto split: option.splits)
        apply (auto simp: ga_gen_def) []
        apply (auto dest: find_min_idx_f_SomeD)
        done
    } note aux=this 
    from G1 have "ga_valid gc ga" 
      unfolding cr_ample_impl2_def stutter_extend_en_def
      apply (simp split: if_split_asm)
      unfolding ga_gample_mi2_impl[symmetric]
      apply (auto dest: aux)
      done
    thus "(ga_ex_impl ga gci, ga_ex ga gc)\<in>global_config_rel"
      by (parametricity add: ga_ex_impl GCI IdI[of ga])
  qed    

  lemma cr_ample_impl3_sim_aux2:
    assumes GCI: "(gci, gc) \<in> global_config_rel"
    assumes GA: "ga \<in> cr_ample_impl2 gc"
    shows "ga\<in>cr_ample_impl3 gci 
      \<and> (ga_ex_impl ga gci, ga_ex ga gc) \<in> global_config_rel"
  proof
    show G1: "ga\<in>cr_ample_impl3 gci"
      using cr_ample_impl3_refine[param_fo, OF GCI] GA by auto
    
    from cr_ample_impl3_sim_aux[OF GCI G1] show 
      "(ga_ex_impl ga gci, ga_ex ga gc) \<in> global_config_rel"
      by auto
  qed    

  sublocale impl3: sa "\<lparr> g_V = UNIV, g_E = ample_step_impl3, g_V0 = {pid_init_gc_impl},
      sa_L = pid_interp_gc_impl is_vis_var \<rparr>" by unfold_locales auto

  sublocale impl3_sim: lbisimulation 
    global_config_rel
    "\<lparr> g_V = UNIV, g_E = ample_step_impl3, g_V0 = {pid_init_gc_impl},
      sa_L = pid_interp_gc_impl is_vis_var \<rparr>"
    "\<lparr> g_V = UNIV, g_E = ample_step_impl2, g_V0 = {pid_init_gc},
      sa_L = pid_interp_gc \<rparr>"
    apply unfold_locales
    apply simp
    apply simp
    apply simp
    using pid_init_gc_impl
    apply (auto dest: fun_relD) []
    unfolding ample_step_impl2_def ample_step_impl3_def
    apply (auto dest: cr_ample_impl3_sim_aux) []
    using pid_interp_gc_impl
    apply (auto dest: fun_relD) []
    apply simp
    
    using pid_init_gc_impl
    apply (auto dest: fun_relD) []
    defer    
    using pid_interp_gc_impl
    apply (auto dest: fun_relD) []
    apply auto

    apply (auto dest: cr_ample_impl3_sim_aux2) []
    done

  text \<open>Correctness of impl3\<close>
  (* TODO: Locale hl_reduction seems very special, and we cannot use it here*)
  lemma impl3_accept_subset: "impl3.accept w \<Longrightarrow> lv.sa.accept w"
    using impl3_sim.accept_bisim cr_ample_impl2_reduction hl_reduction.ample_accept_subset
    by simp

  lemma impl3_accept_stuttering: "lv.sa.accept w \<Longrightarrow> \<exists>w'. w\<approx>w' \<and> impl3.accept w'"
    using impl3_sim.accept_bisim cr_ample_impl2_reduction hl_reduction.ample_accept_stuttering
    by simp

  text \<open>Next, we go from sets of actions to lists of actions\<close>
  definition (in cprog) "ga_gample_mil4 mem sticky_Ei (gc::pid_global_config_impl) = (
    let 
      lcs = pid_global_config.processes gc;
      gs = pid_global_config.state gc
    in
      collecti_index_list (\<lambda>_ lc. let
          c = local_config.command lc;
          ls = local_config.state lc;
          as = comp.succ_impl c;
          s = filter (la_en'_impl (ls,gs) o fst) as;
          ample = s\<noteq>[] 
          \<and> (\<forall>(a,_)\<in>set as. read_globals a = {} \<and> write_globals a = {}) 
          \<and> (\<forall>(a,c')\<in>set s. \<not>mem (c,c') sticky_Ei)
        in
          (ample,map (Pair c) s)
      ) lcs
  )"

  lemma ga_gample_mil4_refine:
    "(ga_gample_mil4, ga_gample_mi3) 
    \<in> (Id\<times>\<^sub>rId \<rightarrow> Id \<rightarrow> bool_rel) \<rightarrow> Id \<rightarrow> Id \<rightarrow> \<langle>nat_rel \<times>\<^sub>r Id\<rangle>list_set_rel"
    apply (intro fun_relI)
    unfolding ga_gample_mil4_def ga_gample_mi3_def
    apply (parametricity)
    apply simp
    apply (rule IdI)
    apply simp
    apply (rule IdI)
    apply (intro fun_relI)
    apply (rule collecti_index_list_refine[param_fo])
    apply (intro fun_relI)
    apply (simp add: list_set_rel_def br_def distinct_map 
      comp.succ_impl_invar)
    apply (auto simp: filter_empty_conv)
    apply force
    done

  definition (in cprog) "cr_ample_impl4 is_vis_var \<equiv>
    let sticky = find_fas_init_code (=) bounded_hashcode_nat
         (def_hashmap_size TYPE(nat)) cfgc_G_impl (is_vis_edge is_vis_var)
    in stutter_extend_en_list (ga_gample_mil4 (\<lambda>x f. f x) sticky)"
      
  lemma cr_ample_impl4_refine:
    "(cr_ample_impl4 is_vis_var, cr_ample_impl3)\<in>Id \<rightarrow> \<langle>\<langle>nat_rel \<times>\<^sub>r Id\<rangle>option_rel\<rangle>list_set_rel"
    unfolding cr_ample_impl4_def cr_ample_impl3_def
    apply (parametricity add: stutter_extend_en_list.refine ga_gample_mil4_refine)
    apply (simp_all add: is_vis_edge_correct)
    done

  text \<open>Finally, we combine the ample-implementation and the executable implementation
    to get a step function\<close>  
  definition (in cprog) "ample_step_impl4 is_vis_var \<equiv>
    rel_of_enex_list (cr_ample_impl4 is_vis_var,ga_ex_impl)"

  lemma ample_step_impl4: 
    "(ample_step_impl4 is_vis_var, ample_step_impl3) \<in> \<langle>Id \<times>\<^sub>r Id\<rangle> set_rel"
    unfolding ample_step_impl4_def ample_step_impl3_def rel_of_pred_def
    apply (parametricity add: rel_of_enex_list_refine cr_ample_impl4_refine[simplified])
    by auto

  sublocale impl4: sa "\<lparr> g_V = UNIV, g_E = ample_step_impl4 is_vis_var,
    g_V0 = {pid_init_gc_impl}, sa_L = pid_interp_gc_impl is_vis_var \<rparr>" by unfold_locales auto

  lemma impl4_accept_subset: "impl4.accept w \<Longrightarrow> lv.sa.accept w"
    using impl3_accept_subset ample_step_impl4
    by simp

  lemma impl4_accept_stuttering: "lv.sa.accept w \<Longrightarrow> \<exists>w'. w\<approx>w' \<and> impl4.accept w'"
    using impl3_accept_stuttering ample_step_impl4
    by simp
    
  lemma (in -) pred_of_succ_of_enex_list:
    fixes enex :: "('c \<Rightarrow> 'a list) \<times> ('a \<Rightarrow> 'c \<Rightarrow> 'c)"
    shows "pred_of_succ (set o succ_of_enex_list enex) = pred_of_enex_list enex"
  proof -
    { fix x and l
      have "glist_member (=) x l \<longleftrightarrow> x\<in>set l"
        by (induction l) auto
    } note [simp] = this

    {
      fix l :: "'a list" and g and l0
      have "set (foldli l (\<lambda>_. True) (\<lambda>x. glist_insert (=) (g x)) l0) = set l0 \<union> g`set l"
        by (induction l arbitrary: l0) (auto simp: glist_insert_def)
    } note [simp] = this

    {
      fix l::"'a list" and P i
      have "foldli l Not (\<lambda>x _. P x) i \<longleftrightarrow> i \<or> (\<exists>x\<in>set l. P x)"
        by (induction l arbitrary: i) auto
    } note [simp] = this


    show ?thesis
      unfolding succ_of_enex_list_def[abs_def] pred_of_enex_list_def[abs_def]
      by (auto simp: pred_of_succ_def gen_image_def gen_bex_def intro!: ext)
  qed    
  lemma (in -) rel_of_succ_of_enex_list:
    fixes enex :: "('c \<Rightarrow> 'a list) \<times> ('a \<Rightarrow> 'c \<Rightarrow> 'c)"
    shows "rel_of_succ (set o succ_of_enex_list enex) = rel_of_enex_list enex"
    unfolding rel_of_enex_list_def
    unfolding pred_of_succ_of_enex_list[symmetric]
    by simp

  definition (in cprog) "impl4_succ is_vis_var
    \<equiv> succ_of_enex_list (cr_ample_impl4 is_vis_var,ga_ex_impl)"
  lemma impl4_succ_pred: 
    "rel_of_succ (set o (impl4_succ is_vis_var)) = ample_step_impl4 is_vis_var"
    unfolding impl4_succ_def ample_step_impl4_def 
    by (simp add: rel_of_succ_of_enex_list)
    
end

export_code ga_ex_impl checking SML

definition "ccfg_E_succ_impl mst \<equiv> remdups o map snd o ccfg_succ_impl mst"

lemma (in cprog) ccfg_E_succ_impl: "ccfg_E_succ_impl (comp_info_of prog) = cfgc_E_succ"
  apply (intro ext) 
  unfolding ccfg_E_succ_impl_def cfgc_E_succ_def
  by (simp add: ccfg_succ_impl)


definition init_pc_impl_impl :: "comp_info \<Rightarrow> proc_decl \<Rightarrow> local_config_impl" where
  "init_pc_impl_impl mst pd \<equiv> \<lparr>
    local_config.command = comp_\<gamma>_impl mst (proc_decl.body pd),
    local_config.state = \<lparr>
      local_state_impl.variables = init_valuation_impl (proc_decl.local_vars pd)
    \<rparr>
  \<rparr>"

lemma (in cprog) init_pc_impl_impl: "init_pc_impl_impl (comp_info_of prog) = init_pc_impl"
  apply (intro ext)
  unfolding init_pc_impl_impl_def init_pc_impl_def
  by (simp add: comp_\<gamma>_impl)

definition pid_init_gc_impl_impl :: "program \<Rightarrow> comp_info \<Rightarrow> pid_global_config_impl" where
  "pid_init_gc_impl_impl prog mst \<equiv> \<lparr>
    pid_global_config.processes = (map (init_pc_impl_impl mst) (program.processes prog)),
    pid_global_config.state = \<lparr>
      global_state_impl.variables = init_valuation_impl (program.global_vars prog)
    \<rparr>
  \<rparr>"

lemma (in cprog) pid_init_gc_impl_impl: 
  "pid_init_gc_impl_impl prog (comp_info_of prog) = pid_init_gc_impl"
  unfolding pid_init_gc_impl_impl_def pid_init_gc_impl_def
  by (simp add: init_pc_impl_impl)

definition "ccfg_V0_impl prog mst \<equiv> map (comp_\<gamma>_impl mst) (cfg_V0_list prog)"

lemma (in cprog) ccfg_V0_impl: "ccfg_V0_impl prog (comp_info_of prog) = cfgc_V0_list"
  unfolding ccfg_V0_impl_def cfgc_V0_list_def
  by (simp add: comp_\<gamma>_impl)

definition "ccfg_G_impl_impl prog mst \<equiv>
  \<lparr> gi_V = \<lambda> _. True, gi_E = ccfg_E_succ_impl mst, gi_V0 = ccfg_V0_impl prog mst \<rparr>"

lemma (in cprog) ccfg_G_impl_impl: "ccfg_G_impl_impl prog (comp_info_of prog) = cfgc_G_impl"
  unfolding ccfg_G_impl_impl_def cfgc_G_impl_def
  unfolding ccfg_E_succ_impl ccfg_V0_impl
  by rule

definition "is_vis_edge_impl mst is_vis_var \<equiv> \<lambda>(c,c'). 
  \<exists>(a,cc')\<in>set (ccfg_succ_impl mst c). c'=cc' \<and> (\<exists>v\<in>write_globals a. is_vis_var v)"

lemma (in cprog) is_vis_edge_impl: "is_vis_edge_impl (comp_info_of prog) = is_vis_edge"
  apply (intro ext)
  unfolding is_vis_edge_impl_def is_vis_edge_def
  by (simp add: ccfg_succ_impl)

definition "ga_gample_mil4_impl mst mem sticky_Ei (gc::pid_global_config_impl) = (
  let 
    lcs = pid_global_config.processes gc;
    gs = pid_global_config.state gc
  in
    collecti_index_list (\<lambda>_ lc. let
        c = local_config.command lc;
        ls = local_config.state lc;
        as = ccfg_succ_impl mst c;
        s = filter (la_en'_impl (ls,gs) o fst) as;
        ample = s\<noteq>[] 
        \<and> (\<forall>(a,_)\<in>set as. read_globals a = {} \<and> write_globals a = {}) 
        \<and> (\<forall>(a,c')\<in>set s. \<not>mem (c,c') sticky_Ei)
      in
        (ample,map (Pair c) s)
    ) lcs
)"

lemma (in cprog) ga_gample_mil4_impl: "ga_gample_mil4_impl (comp_info_of prog) = ga_gample_mil4"
  apply (intro ext)
  unfolding ga_gample_mil4_impl_def ga_gample_mil4_def
  by (simp add: ccfg_succ_impl)


definition "cr_ample_impl4_impl prog mst is_vis_var \<equiv>
  let sticky = find_fas_init_code (=) bounded_hashcode_nat
       (def_hashmap_size TYPE(nat)) (ccfg_G_impl_impl prog mst)
       (is_vis_edge_impl mst is_vis_var)
  in stutter_extend_en_list (ga_gample_mil4_impl mst (\<lambda>x f. f x) sticky)"

lemma (in cprog) cr_ample_impl4_impl: "cr_ample_impl4_impl prog (comp_info_of prog) = cr_ample_impl4"
  apply (intro ext)
  unfolding cr_ample_impl4_impl_def cr_ample_impl4_def
  by (simp add: ga_gample_mil4_impl ccfg_G_impl_impl is_vis_edge_impl)

definition "impl4_succ_impl prog mst is_vis_var
    \<equiv> succ_of_enex_list (cr_ample_impl4_impl prog mst is_vis_var,ga_ex_impl)"

lemma (in cprog) impl4_succ_impl: 
  "impl4_succ_impl prog (comp_info_of prog) = impl4_succ"
  apply (intro ext)
  unfolding impl4_succ_impl_def impl4_succ_def
  by (simp add: cr_ample_impl4_impl)

definition "ample_step_impl4_impl prog mst is_vis_var 
  \<equiv> rel_of_enex_list (cr_ample_impl4_impl prog mst is_vis_var,ga_ex_impl)"

lemma (in cprog) ample_step_impl4_impl: 
  "ample_step_impl4_impl prog (comp_info_of prog) = ample_step_impl4"
  apply (intro ext)
  unfolding ample_step_impl4_impl_def ample_step_impl4_def
  by (simp add: cr_ample_impl4_impl)
  
export_code impl4_succ_impl pid_init_gc_impl_impl comp_info_of checking SML

end

