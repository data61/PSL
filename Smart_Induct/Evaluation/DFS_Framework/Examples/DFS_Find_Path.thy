section \<open>Finding a Path between Nodes\<close>
theory DFS_Find_Path
imports 
  "../DFS_Framework"
  CAVA_Automata.Digraph_Impl
  "../Misc/Impl_Rev_Array_Stack"
begin
text \<open>
  We instantiate the DFS framework to find a path to some reachable node 
  that satisfies a given predicate. We present four variants of the algorithm:
  Finding any path, and finding path of at least length one, combined with
  searching the whole graph, and searching the graph restricted to a given set 
  of nodes. The restricted variants are efficiently implemented by 
  pre-initializing the visited set (cf. @{theory DFS_Framework.Restr_Impl}).

  The restricted variants can be used for incremental search, ignoring already 
  searched nodes in further searches. This is required, e.g., for the inner 
  search of nested DFS (Buchi automaton emptiness check).
\<close>

subsection \<open>Including empty Path\<close>
record 'v fp0_state = "'v state" +
  ppath :: "('v list \<times> 'v) option"

type_synonym 'v fp0_param = "('v, ('v,unit) fp0_state_ext) parameterization"

lemma [simp]: "s\<lparr> state.more := \<lparr> ppath = foo \<rparr> \<rparr> = s \<lparr> ppath := foo \<rparr>"
  by (cases s) simp

abbreviation "no_path \<equiv> \<lparr> ppath = None \<rparr>"
abbreviation "a_path p v \<equiv> \<lparr> ppath = Some (p,v) \<rparr>"

definition fp0_params :: "('v \<Rightarrow> bool) \<Rightarrow> 'v fp0_param"
  where "fp0_params P \<equiv> \<lparr>
  on_init = RETURN no_path,
  on_new_root = \<lambda>v0 s. if P v0 then RETURN (a_path [] v0) else RETURN no_path,
  on_discover = \<lambda>u v s. if P v 
                   then \<comment> \<open>\<open>v\<close> is already on the stack, so we need to pop it again\<close>
                      RETURN (a_path (rev (tl (stack s))) v) 
                   else RETURN no_path,
  on_finish = \<lambda>u s. RETURN (state.more s),
  on_back_edge = \<lambda>u v s. RETURN (state.more s),
  on_cross_edge = \<lambda>u v s. RETURN (state.more s),
  is_break = \<lambda>s. ppath s \<noteq> None \<rparr>"

lemmas fp0_params_simps[simp] 
  = gen_parameterization.simps[mk_record_simp, OF fp0_params_def]

interpretation fp0: param_DFS_defs where param = "fp0_params P"
  for G P .

locale fp0 = param_DFS G "fp0_params P"
  for G and P :: "'v \<Rightarrow> bool"
begin

  lemma [simp]: 
    "ppath (empty_state \<lparr>ppath = e\<rparr>) = e"
    by (simp add: empty_state_def)

  lemma [simp]: 
    "ppath (s\<lparr>state.more := state.more s'\<rparr>) = ppath s'"
    by (cases s, cases s') auto

  sublocale DFS where param = "fp0_params P"
    by unfold_locales simp_all

end

lemma fp0I: assumes "fb_graph G" shows "fp0 G"
proof - interpret fb_graph G by fact show ?thesis by unfold_locales qed

locale fp0_invar = fp0 + 
  DFS_invar where param = "fp0_params P"

lemma fp0_invar_eq[simp]: 
  "DFS_invar G (fp0_params P) = fp0_invar G P"
proof (intro ext iffI)
  fix s
  assume "DFS_invar G (fp0_params P) s"
  interpret DFS_invar G "fp0_params P" s by fact
  show "fp0_invar G P s" by unfold_locales
next
  fix s
  assume "fp0_invar G P s"
  interpret fp0_invar G P s by fact
  show "DFS_invar G (fp0_params P) s" by unfold_locales
qed

context fp0 begin

  lemma i_no_path_no_P_discovered:
    "is_invar (\<lambda>s. ppath s = None \<longrightarrow> dom (discovered s) \<inter> Collect P = {})"
  by (rule establish_invarI) simp_all

  lemma i_path_to_P:
    "is_invar (\<lambda>s. ppath s = Some (vs,v) \<longrightarrow> P v)"
  by (rule establish_invarI) auto
  
  lemma i_path_invar:
    "is_invar (\<lambda>s. ppath s = Some (vs,v) \<longrightarrow> 
                   (vs \<noteq> [] \<longrightarrow> hd vs \<in> V0 \<and> path E (hd vs) vs v) 
                 \<and> (vs = [] \<longrightarrow> v \<in> V0 \<and> path E v vs v)
                 \<and> (distinct (vs@[v]))
                 )"
  proof (induct rule: establish_invarI)
    case (discover s s' u v) then interpret fp0_invar where s=s 
      by simp

    from discover have ne: "stack s \<noteq> []" by simp
    from discover have vnis: "v\<notin>set (stack s)" using stack_discovered by auto

    from pendingD discover have "v \<in> succ (hd (stack s))" by simp
    with hd_succ_stack_is_path[OF ne] have "\<exists>v0\<in>V0. path E v0 (rev (stack s)) v" .
    moreover from last_stack_in_V0 ne have "last (stack s) \<in> V0" by simp
    ultimately have "path E (hd (rev (stack s)))  (rev (stack s)) v" "hd (rev (stack s)) \<in> V0"
      using hd_rev[OF ne] path_hd[where p="rev (stack s)"] ne
      by auto
    with ne discover vnis show ?case by (auto simp: stack_distinct)
  qed auto
end

context fp0_invar
begin
  lemmas no_path_no_P_discovered
    = i_no_path_no_P_discovered[THEN make_invar_thm, rule_format]

  lemmas path_to_P
    = i_path_to_P[THEN make_invar_thm, rule_format]

  lemmas path_invar
    = i_path_invar[THEN make_invar_thm, rule_format]

  lemma path_invar_nonempty:
    assumes "ppath s = Some (vs,v)"
    and "vs \<noteq> []"
    shows "hd vs \<in> V0" "path E (hd vs) vs v"
    using assms path_invar
    by auto

  lemma path_invar_empty:
    assumes "ppath s = Some (vs,v)"
    and "vs = []"
    shows "v \<in> V0" "path E v vs v"
    using assms path_invar
    by auto

  lemma fp0_correct:
    assumes "\<not>cond s"
    shows "case ppath s of 
      None \<Rightarrow> \<not>(\<exists>v0\<in>V0. \<exists>v. (v0,v) \<in> E\<^sup>* \<and> P v)
    | Some (p,v) \<Rightarrow> (\<exists>v0\<in>V0. path E v0 p v \<and> P v \<and> distinct (p@[v]))" 
  proof (cases "ppath s")
    case None with assms nc_discovered_eq_reachable no_path_no_P_discovered have
      "reachable \<inter> Collect P = {}" by auto
    thus ?thesis by (auto simp add: None)
  next
    case (Some vvs) then obtain v vs where [simp]: "vvs = (vs,v)" 
      by (cases vvs) auto

    from Some path_invar[of vs v] path_to_P[of _ v] show ?thesis
      by auto
  qed

end

context fp0 begin
  lemma fp0_correct: "it_dfs \<le> SPEC (\<lambda>s. case ppath s of 
      None \<Rightarrow> \<not>(\<exists>v0\<in>V0. \<exists>v. (v0,v) \<in> E\<^sup>* \<and> P v)
    | Some (p,v) \<Rightarrow> (\<exists>v0\<in>V0. path E v0 p v \<and> P v \<and> distinct (p@[v])))" 
    apply (rule weaken_SPEC[OF it_dfs_correct])
    apply clarsimp
    apply (simp add: fp0_invar.fp0_correct)
    done
end

subsubsection \<open>Basic Interface\<close>
text \<open>Use this interface, rather than the internal stuff above! \<close>
(* Making it a well-defined interface. This interface should be used, not
  the internal stuff. If more information about the result is needed, this 
  interface should be extended! *)

type_synonym 'v fp_result = "('v list \<times> 'v) option"
definition "find_path0_pred G P \<equiv> \<lambda>r. case r of 
    None \<Rightarrow> (g_E G)\<^sup>* `` g_V0 G \<inter> Collect P = {}
  | Some (vs,v) \<Rightarrow> P v \<and> distinct (vs@[v]) \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G) v0 vs v)"

definition find_path0_spec
  :: "('v, _) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  \<comment> \<open>Searches a path from the root nodes to some target node that satisfies a 
      given predicate. If such a path is found, the path and the target node
      are returned\<close>
where
  "find_path0_spec G P \<equiv> do {
    ASSERT (fb_graph G);
    SPEC (find_path0_pred G P)
  }"

definition find_path0 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  where "find_path0 G P \<equiv> do {
  ASSERT (fp0 G);
  s \<leftarrow> fp0.it_dfs TYPE('more) G P;
  RETURN (ppath s)
}"

lemma find_path0_correct:
  shows "find_path0 G P \<le> find_path0_spec G P"
  unfolding find_path0_def find_path0_spec_def find_path0_pred_def
  apply (refine_vcg le_ASSERTI order_trans[OF fp0.fp0_correct])
  apply (erule fp0I)
  apply (auto split: option.split) []
  done

lemmas find_path0_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path0_spec_def]
  ASSERT_leof_defI[OF find_path0_spec_def]

subsection \<open>Restricting the Graph\<close>
text \<open> Extended interface, propagating set of already searched nodes (restriction) \<close>
(* Invariant for restriction: The restriction is closed under E 
  and contains no P-nodes *)
definition restr_invar 
  \<comment> \<open>Invariant for a node restriction, i.e., a transition closed set of nodes 
    known to not contain a target node that satisfies a predicate.\<close>
  where
  "restr_invar E R P \<equiv> E `` R \<subseteq> R \<and> R \<inter> Collect P = {}"

lemma restr_invar_triv[simp, intro!]: "restr_invar E {} P" 
  unfolding restr_invar_def by simp

lemma restr_invar_imp_not_reachable: "restr_invar E R P \<Longrightarrow> E\<^sup>*``R \<inter> Collect P = {}"
  unfolding restr_invar_def by (simp add: Image_closed_trancl)

type_synonym 'v fpr_result = "'v set + ('v list \<times> 'v)"
definition "find_path0_restr_pred G P R \<equiv> \<lambda>r. 
    case r of 
      Inl R' \<Rightarrow> R' = R \<union> (g_E G)\<^sup>* `` g_V0 G \<and> restr_invar (g_E G) R' P
    | Inr (vs,v) \<Rightarrow> P v \<and> (\<exists> v0 \<in> g_V0 G - R. path (rel_restrict (g_E G) R) v0 vs v)"

definition find_path0_restr_spec 
  \<comment> \<open>Find a path to a target node that satisfies a predicate, not considering
      nodes from the given node restriction. If no path is found, an extended
      restriction is returned, that contains the start nodes\<close>
  where "find_path0_restr_spec G P R \<equiv> do {
    ASSERT (fb_graph G \<and> restr_invar (g_E G) R P);
    SPEC (find_path0_restr_pred G P R)}"

lemmas find_path0_restr_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path0_restr_spec_def]
  ASSERT_leof_defI[OF find_path0_restr_spec_def]


definition find_path0_restr 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> 'v fpr_result nres"
  where "find_path0_restr G P R \<equiv> do {
  ASSERT (fb_graph G);
  ASSERT (fp0 (graph_restrict G R));
  s \<leftarrow> fp0.it_dfs TYPE('more) (graph_restrict G R) P;
  case ppath s of
    None \<Rightarrow> do {
      ASSERT (dom (discovered s) = dom (finished s));
      RETURN (Inl (R \<union> dom (finished s)))
    }
  | Some (vs,v) \<Rightarrow> RETURN (Inr (vs,v))
}"


lemma find_path0_restr_correct:
  shows "find_path0_restr G P R \<le> find_path0_restr_spec G P R"
proof (rule le_ASSERT_defI1[OF find_path0_restr_spec_def], clarify)
  assume "fb_graph G" 
  interpret a: fb_graph G by fact
  interpret fb_graph "graph_restrict G R" by (rule a.fb_graph_restrict)

  assume I: "restr_invar (g_E G) R P"

  define reachable where "reachable = graph_defs.reachable (graph_restrict G R)"

  interpret fp0 "graph_restrict G R" by unfold_locales
  
  show ?thesis unfolding find_path0_restr_def find_path0_restr_spec_def
    apply (refine_rcg refine_vcg le_ASSERTI order_trans[OF it_dfs_correct])
    apply unfold_locales
    apply (clarsimp_all)
  proof -
    fix s
    assume "fp0_invar (graph_restrict G R) P s"
      and NC[simp]: "\<not>fp0.cond TYPE('b) (graph_restrict G R) P s"
    then interpret fp0_invar "graph_restrict G R" P s by simp

    {
      assume [simp]: "ppath s = None"

      from nc_discovered_eq_finished 
      show "dom (discovered s) = dom (finished s)" by simp

      from nc_finished_eq_reachable 
      have DFR[simp]: "dom (finished s) = reachable"
        by (simp add: reachable_def)

      from I have "g_E G `` R \<subseteq> R" unfolding restr_invar_def by auto

      have "reachable \<subseteq> (g_E G)\<^sup>* `` g_V0 G" 
        unfolding reachable_def
        by (rule Image_mono, rule rtrancl_mono) (auto simp: rel_restrict_def)

      hence "R \<union> dom (finished s) = R \<union> (g_E G)\<^sup>* `` g_V0 G"
        apply -
        apply (rule equalityI)
        apply auto []
        unfolding DFR reachable_def
        apply (auto elim: E_closed_restr_reach_cases[OF _ \<open>g_E G `` R \<subseteq> R\<close>]) []
        done
      moreover from nc_fin_closed I 
      have "g_E G `` (R \<union> dom (finished s)) \<subseteq> R \<union> dom (finished s)"
        unfolding restr_invar_def by (simp add: rel_restrict_def) blast
      moreover from no_path_no_P_discovered nc_discovered_eq_finished I
      have "(R \<union> dom (finished s)) \<inter> Collect P = {}"
        unfolding restr_invar_def by auto
      ultimately 
      show "find_path0_restr_pred G P R (Inl (R \<union> dom (finished s)))"
        unfolding restr_invar_def find_path0_restr_pred_def by auto
    }

    {
      fix v vs
      assume [simp]: "ppath s = Some (vs,v)"
      from fp0_correct 
      show "find_path0_restr_pred G P R (Inr (vs, v))"
        unfolding find_path0_restr_pred_def by auto
    }
  qed
qed

subsection \<open>Path of Minimal Length One, with Restriction\<close>
definition "find_path1_restr_pred G P R \<equiv> \<lambda>r. 
      case r of 
        Inl R' \<Rightarrow> R' = R \<union> (g_E G)\<^sup>+ `` g_V0 G \<and> restr_invar (g_E G) R' P
      | Inr (vs,v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G \<inter> UNIV \<times> -R) v0 vs v)"

definition find_path1_restr_spec 
  \<comment> \<open>Find a path of length at least one to a target node that satisfies P.
    Takes an initial node restriction, and returns an extended node restriction.\<close>
  where "find_path1_restr_spec G P R \<equiv> do {
    ASSERT (fb_graph G \<and> restr_invar (g_E G) R P);
    SPEC (find_path1_restr_pred G P R)}"

lemmas find_path1_restr_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path1_restr_spec_def]
  ASSERT_leof_defI[OF find_path1_restr_spec_def]

definition find_path1_restr
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v set \<Rightarrow> 'v fpr_result nres"
  where "find_path1_restr G P R \<equiv> 
  FOREACHc (g_V0 G) is_Inl (\<lambda>v0 s. do {
    ASSERT (is_Inl s); \<comment> \<open>TODO: Add FOREACH-condition as precondition in autoref!\<close>
    let R = projl s;
    f0 \<leftarrow> find_path0_restr_spec (G \<lparr> g_V0 := g_E G `` {v0} \<rparr>) P R;
    case f0 of 
      Inl _ \<Rightarrow> RETURN f0
    | Inr (vs,v) \<Rightarrow> RETURN (Inr (v0#vs,v))
  }) (Inl R)"

definition "find_path1_tailrec_invar G P R0 it s \<equiv> 
  case s of
    Inl R \<Rightarrow> R = R0 \<union> (g_E G)\<^sup>+ `` (g_V0 G - it) \<and> restr_invar (g_E G) R P
  | Inr (vs, v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G - it. path (g_E G \<inter> UNIV \<times> -R0) v0 vs v)"


lemma find_path1_restr_correct:
  shows "find_path1_restr G P R \<le> find_path1_restr_spec G P R"
proof (rule le_ASSERT_defI1[OF find_path1_restr_spec_def], clarify)
  assume "fb_graph G"
  interpret a: fb_graph G by fact
  interpret fb0: fb_graph "G \<lparr> g_E := g_E G \<inter> UNIV \<times> -R \<rparr>"
    by (rule a.fb_graph_subset, auto)

  assume I: "restr_invar (g_E G) R P"

  have aux2: "\<And>v0. v0 \<in> g_V0 G \<Longrightarrow> fb_graph (G \<lparr> g_V0 := g_E G `` {v0} \<rparr>)"
    by (rule a.fb_graph_subset, auto)

  {
    fix v0 it s
    assume IT: "it \<subseteq> g_V0 G" "v0 \<in> it"
    and "is_Inl s"
    and FPI: "find_path1_tailrec_invar G P R it s"
    and RI: "restr_invar (g_E G) (projl s \<union> (g_E G)\<^sup>+ `` {v0}) P"

    then obtain R' where [simp]: "s = Inl R'" by (cases s) auto

    from FPI have [simp]: "R' = R \<union> (g_E G)\<^sup>+ `` (g_V0 G - it)" 
      unfolding find_path1_tailrec_invar_def by simp

    have "find_path1_tailrec_invar G P R (it - {v0})
            (Inl (projl s \<union> (g_E G)\<^sup>+ `` {v0}))"
      using RI
      by (auto simp: find_path1_tailrec_invar_def it_step_insert_iff[OF IT])
  } note aux4 = this      

  {
    fix v0 u it s v p
    assume IT: "it \<subseteq> g_V0 G" "v0 \<in> it"
    and "is_Inl s"
    and FPI: "find_path1_tailrec_invar G P R it s"
    and PV: "P v"
    and PATH: "path (rel_restrict (g_E G) (projl s)) u p v" "(v0,u)\<in>(g_E G)"
    and PR: "u \<notin> projl s"

    then obtain R' where [simp]: "s = Inl R'" by (cases s) auto

    from FPI have [simp]: "R' = R \<union> (g_E G)\<^sup>+ `` (g_V0 G - it)" 
      unfolding find_path1_tailrec_invar_def by simp

    have "find_path1_tailrec_invar G P R (it - {v0}) (Inr (v0 # p, v))"
      apply (simp add: find_path1_tailrec_invar_def PV)
      apply (rule bexI[where x=v0])
        using PR PATH(2) path_mono[OF rel_restrict_mono2[of R] PATH(1)]
        apply (auto simp: path1_restr_conv) []

        using IT apply blast
      done
  } note aux5 = this

  show ?thesis
    unfolding find_path1_restr_def find_path1_restr_spec_def find_path1_restr_pred_def
    apply (refine_rcg le_ASSERTI
      refine_vcg FOREACHc_rule[where I="find_path1_tailrec_invar G P R"]
      (*order_trans[OF find_path0_restr_correct]*)
      )
    apply simp
    using I apply (auto simp add: find_path1_tailrec_invar_def restr_invar_def) []

    apply (blast intro: aux2)
    apply (auto simp add: find_path1_tailrec_invar_def split: sum.splits) []
    apply (auto 
      simp: find_path0_restr_pred_def aux4 aux5
      simp: trancl_Image_unfold_left[symmetric]
      split: sum.splits) []

    apply (auto simp add: find_path1_tailrec_invar_def split: sum.splits) [2]
    done
qed

definition "find_path1_pred G P \<equiv> \<lambda>r. 
      case r of 
        None \<Rightarrow> (g_E G)\<^sup>+ `` g_V0 G \<inter> Collect P = {}
      | Some (vs, v) \<Rightarrow> P v \<and> vs \<noteq> [] \<and> (\<exists> v0 \<in> g_V0 G. path (g_E G) v0 vs v)"
definition find_path1_spec 
  \<comment> \<open>Find a path of length at least one to a target node that satisfies 
      a given predicate.\<close>
  where "find_path1_spec G P \<equiv> do {
    ASSERT (fb_graph G);
    SPEC (find_path1_pred G P)}"

lemmas find_path1_spec_rule[refine_vcg] = 
  ASSERT_le_defI[OF find_path1_spec_def]
  ASSERT_leof_defI[OF find_path1_spec_def]

subsection \<open>Path of Minimal Length One, without Restriction\<close>
definition find_path1 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v fp_result nres"
  where "find_path1 G P \<equiv> do {
  r \<leftarrow> find_path1_restr_spec G P {};
  case r of 
    Inl _ \<Rightarrow> RETURN None
  | Inr vsv \<Rightarrow> RETURN (Some vsv)
}"

lemma find_path1_correct: 
  shows "find_path1 G P \<le> find_path1_spec G P"
  unfolding find_path1_def find_path1_spec_def find_path1_pred_def
  apply (refine_rcg refine_vcg le_ASSERTI order_trans[OF find_path1_restr_correct])
  apply simp
  apply (fastforce 
    simp: find_path1_restr_spec_def find_path1_restr_pred_def
    split: sum.splits 
    dest!: restr_invar_imp_not_reachable tranclD)
  done

subsection \<open>Implementation\<close>

(* Implementation with stack *)
record 'v fp0_state_impl = "'v simple_state" +
  ppath :: "('v list \<times> 'v) option"

definition "fp0_erel \<equiv> { 
  (\<lparr> fp0_state_impl.ppath = p \<rparr>, \<lparr> fp0_state.ppath = p\<rparr>) | p. True }"

abbreviation "fp0_rel R \<equiv> \<langle>fp0_erel\<rangle>restr_simple_state_rel R"

abbreviation "no_path_impl \<equiv> \<lparr> fp0_state_impl.ppath = None \<rparr>"
abbreviation "a_path_impl p v \<equiv> \<lparr> fp0_state_impl.ppath = Some (p,v) \<rparr>"

lemma fp0_rel_ppath_cong[simp]: 
  "(s,s')\<in>fp0_rel R \<Longrightarrow> fp0_state_impl.ppath s = fp0_state.ppath s'"
  unfolding restr_simple_state_rel_def fp0_erel_def
  by (cases s, cases s', auto)

lemma fp0_ss_rel_ppath_cong[simp]: 
  "(s,s')\<in>\<langle>fp0_erel\<rangle>simple_state_rel \<Longrightarrow> fp0_state_impl.ppath s = fp0_state.ppath s'"
  unfolding simple_state_rel_def fp0_erel_def
  by (cases s, cases s', auto)

lemma fp0i_cong[cong]: "simple_state.more s = simple_state.more s' 
  \<Longrightarrow> fp0_state_impl.ppath s = fp0_state_impl.ppath s'"
  by (cases s, cases s', auto)

lemma fp0_erelI: "p=p' 
  \<Longrightarrow> (\<lparr> fp0_state_impl.ppath = p \<rparr>, \<lparr> fp0_state.ppath = p'\<rparr>)\<in>fp0_erel"
  unfolding fp0_erel_def by auto
  
definition fp0_params_impl 
  :: "_ \<Rightarrow> ('v,'v fp0_state_impl,('v,unit)fp0_state_impl_ext) gen_parameterization"
where "fp0_params_impl P \<equiv> \<lparr>
  on_init = RETURN no_path_impl,
  on_new_root = \<lambda>v0 s. 
    if P v0 then RETURN (a_path_impl [] v0) else RETURN no_path_impl,
  on_discover = \<lambda>u v s. 
    if P v then RETURN (a_path_impl (map fst (rev (tl (CAST (ss_stack s))))) v)
    else RETURN no_path_impl,
  on_finish = \<lambda>u s. RETURN (simple_state.more s),
  on_back_edge = \<lambda>u v s. RETURN (simple_state.more s),
  on_cross_edge = \<lambda>u v s. RETURN (simple_state.more s),
  is_break = \<lambda>s. ppath s \<noteq> None \<rparr>"

lemmas fp0_params_impl_simp[simp, DFS_code_unfold] 
  = gen_parameterization.simps[mk_record_simp, OF fp0_params_impl_def]

interpretation fp0_impl:
  restricted_impl_defs "fp0_params_impl P" "fp0_params P" G R 
  for G P R .

locale fp0_restr = fb_graph
begin
  sublocale fp0?: fp0 "graph_restrict G R" 
    apply (rule fp0I)
    apply (rule fb_graph_restrict)
    done

  sublocale impl: restricted_impl G "fp0_params P" "fp0_params_impl P" 
    fp0_erel R 
    apply unfold_locales
      apply parametricity

      apply (simp add: fp0_erel_def)
      apply (auto) [1]

      apply (auto
        simp: rev_map[symmetric] map_tl comp_def
        simp: fp0_erel_def simple_state_rel_def) [7]

      apply (auto simp: restr_rel_def) [3]
      apply (clarsimp simp: restr_rel_def)
      apply (rule IdD) apply (subst list_rel_id_simp[symmetric])
      apply parametricity
    done
end

definition "find_path0_restr_impl G P R \<equiv> do {
  ASSERT (fb_graph G);
  ASSERT (fp0 (graph_restrict G R));
  s \<leftarrow> fp0_impl.tailrec_impl TYPE('a) G R P;
  case ppath s of
    None \<Rightarrow> RETURN (Inl (visited s))
  | Some (vs,v) \<Rightarrow> RETURN (Inr (vs,v))
}"


lemma find_path0_restr_impl[refine]:
  shows "find_path0_restr_impl G P R 
     \<le> \<Down>(\<langle>Id,Id\<times>\<^sub>rId\<rangle>sum_rel) 
   (find_path0_restr G P R)"
proof (rule refine_ASSERT_defI2[OF find_path0_restr_def])
  assume "fb_graph G"
  then interpret fb_graph G .
  interpret fp0_restr G by unfold_locales

  show ?thesis
   unfolding find_path0_restr_impl_def find_path0_restr_def
   apply (refine_rcg impl.tailrec_refine)
   apply refine_dref_type  
   apply (auto simp: restr_simple_state_rel_def)
   done
qed

definition "find_path0_impl G P \<equiv> do {
  ASSERT (fp0 G);
  s \<leftarrow> fp0_impl.tailrec_impl TYPE('a) G {} P;
  RETURN (ppath s)
}"

lemma find_path0_impl[refine]: "find_path0_impl G P 
  \<le> \<Down> (\<langle>Id\<times>\<^sub>rId\<rangle>option_rel) (find_path0 G P)"
proof (rule refine_ASSERT_defI1[OF find_path0_def])
  assume "fp0 G" 
  then interpret fp0 G .
  interpret r: fp0_restr G by unfold_locales

  show ?thesis
   unfolding find_path0_impl_def find_path0_def
   apply (refine_rcg r.impl.tailrec_refine[where R="{}", simplified])
   apply (auto)
   done
qed

subsection \<open>Synthesis of Executable Code\<close>
(* Autoref *)

record ('v,'si,'nsi)fp0_state_impl' = "('si,'nsi)simple_state_nos_impl" +
  ppath_impl :: "('v list \<times> 'v) option"

definition [to_relAPP]: "fp0_state_erel erel \<equiv> {
  (\<lparr>ppath_impl = pi, \<dots> =  mi\<rparr>,\<lparr>ppath = p, \<dots> = m\<rparr>) | pi mi p m.
    (pi,p)\<in>\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>option_rel \<and> (mi,m)\<in>erel}"

consts 
  i_fp0_state_ext :: "interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of fp0_state_erel i_fp0_state_ext]


term fp0_state_impl_ext
lemma [autoref_rules]:
  fixes ns_rel vis_rel erel
  defines "R \<equiv> \<langle>ns_rel,vis_rel,\<langle>erel\<rangle>fp0_state_erel\<rangle>ssnos_impl_rel"
  shows 
    "(fp0_state_impl'_ext, fp0_state_impl_ext) 
      \<in> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>option_rel \<rightarrow> erel \<rightarrow> \<langle>erel\<rangle>fp0_state_erel"
    "(ppath_impl, fp0_state_impl.ppath) \<in> R \<rightarrow> \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>option_rel"
  unfolding fp0_state_erel_def ssnos_impl_rel_def R_def
  by auto

schematic_goal find_path0_code:
  fixes G :: "('v :: hashable, _) graph_rec_scheme"
  assumes [autoref_rules]:
    "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    "(Pi, P) \<in> Id \<rightarrow> bool_rel"
  notes [autoref_tyrel] = TYRELI[where R="\<langle>Id::('v\<times>'v) set\<rangle>dflt_ahs_rel"]
  shows "(nres_of (?c::?'c dres), find_path0_impl G P) \<in> ?R"
  unfolding find_path0_impl_def[abs_def] DFS_code_unfold ssnos_unfolds
  unfolding if_cancel not_not comp_def nres_monad_laws
  using [[autoref_trace_failed_id]]
  apply (autoref_monadic (trace))
  done

concrete_definition find_path0_code uses find_path0_code
export_code find_path0_code checking SML

lemma find_path0_autoref_aux:
  assumes Vid: "Rv = (Id :: 'a :: hashable rel)"
  shows "(\<lambda>G P. nres_of (find_path0_code G P), find_path0_spec) 
    \<in> \<langle>Rm, Rv\<rangle>g_impl_rel_ext \<rightarrow> (Rv \<rightarrow> bool_rel) 
      \<rightarrow> \<langle>\<langle>\<langle>Rv\<rangle>list_rel \<times>\<^sub>r Rv\<rangle>option_rel\<rangle>nres_rel"
  apply (intro fun_relI nres_relI)
  unfolding Vid
  apply (rule 
    order_trans[OF find_path0_code.refine[param_fo, THEN nres_relD]],
    assumption+
    )
  using find_path0_impl find_path0_correct
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done
lemmas find_path0_autoref[autoref_rules] = find_path0_autoref_aux[OF PREFER_id_D]  




schematic_goal find_path0_restr_code:
  fixes vis_rel :: "('v\<times>'v) set \<Rightarrow> ('visi\<times>'v set) set"
  notes [autoref_rel_intf] = REL_INTFI[of vis_rel "i_set" for I]
  assumes [autoref_rules]: "(op_vis_insert, insert)\<in>Id \<rightarrow> \<langle>Id\<rangle>vis_rel \<rightarrow> \<langle>Id\<rangle>vis_rel"
  assumes [autoref_rules]: "(op_vis_memb, (\<in>))\<in>Id \<rightarrow> \<langle>Id\<rangle>vis_rel \<rightarrow> bool_rel"
  assumes [autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    "(Pi,P)\<in>Id \<rightarrow> bool_rel"
    "(Ri,R)\<in>\<langle>Id\<rangle>vis_rel"
  shows "(nres_of (?c::?'c dres),
    find_path0_restr_impl 
      G
      P 
      (R:::\<^sub>r\<langle>Id\<rangle>vis_rel)) \<in> ?R"
  unfolding find_path0_restr_impl_def[abs_def] DFS_code_unfold ssnos_unfolds
  unfolding if_cancel not_not comp_def nres_monad_laws
  using [[autoref_trace_failed_id]]
  apply (autoref_monadic (trace))
  done

concrete_definition find_path0_restr_code uses find_path0_restr_code
export_code find_path0_restr_code checking SML

lemma find_path0_restr_autoref_aux:
  assumes 1: "(op_vis_insert, insert)\<in>Rv \<rightarrow> \<langle>Rv\<rangle>vis_rel \<rightarrow> \<langle>Rv\<rangle>vis_rel"
  assumes 2: "(op_vis_memb, (\<in>))\<in>Rv \<rightarrow> \<langle>Rv\<rangle>vis_rel \<rightarrow> bool_rel"
  assumes Vid: "Rv = Id"
  shows "(\<lambda> G P R. nres_of (find_path0_restr_code op_vis_insert op_vis_memb G P R), 
    find_path0_restr_spec) 
    \<in> \<langle>Rm, Rv\<rangle>g_impl_rel_ext \<rightarrow> (Rv \<rightarrow> bool_rel) \<rightarrow> \<langle>Rv\<rangle>vis_rel \<rightarrow>
    \<langle>\<langle>\<langle>Rv\<rangle>vis_rel, \<langle>Rv\<rangle>list_rel \<times>\<^sub>r Rv\<rangle>sum_rel\<rangle>nres_rel"
  apply (intro fun_relI nres_relI)
  unfolding Vid
  apply (rule 
    order_trans[OF find_path0_restr_code.refine[OF 1[unfolded Vid] 2[unfolded Vid], param_fo, THEN nres_relD]]
    )
  apply assumption+
  using find_path0_restr_impl find_path0_restr_correct
  apply (simp add: pw_le_iff refine_pw_simps)
  apply blast
  done
lemmas find_path0_restr_autoref[autoref_rules] = find_path0_restr_autoref_aux[OF GEN_OP_D GEN_OP_D PREFER_id_D]  

schematic_goal find_path1_restr_code:
  fixes vis_rel :: "('v\<times>'v) set \<Rightarrow> ('visi\<times>'v set) set"
  notes [autoref_rel_intf] = REL_INTFI[of vis_rel "i_set" for I]
  assumes [autoref_rules]: "(op_vis_insert, insert)\<in>Id \<rightarrow> \<langle>Id\<rangle>vis_rel \<rightarrow> \<langle>Id\<rangle>vis_rel"
  assumes [autoref_rules]: "(op_vis_memb, (\<in>))\<in>Id \<rightarrow> \<langle>Id\<rangle>vis_rel \<rightarrow> bool_rel"
  assumes [autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, Id\<rangle>g_impl_rel_ext"
    "(Pi,P)\<in>Id \<rightarrow> bool_rel"
    "(Ri,R)\<in>\<langle>Id\<rangle>vis_rel"
  shows "(nres_of ?c,find_path1_restr G P R)
  \<in> \<langle>\<langle>\<langle>Id\<rangle>vis_rel, \<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>sum_rel\<rangle>nres_rel"
  unfolding find_path1_restr_def[abs_def]
  using [[autoref_trace_failed_id]]
  apply (autoref_monadic (trace))
  done

concrete_definition find_path1_restr_code uses find_path1_restr_code
export_code find_path1_restr_code checking SML

lemma find_path1_restr_autoref_aux:
  assumes G: "(op_vis_insert, insert)\<in>V \<rightarrow> \<langle>V\<rangle>vis_rel \<rightarrow> \<langle>V\<rangle>vis_rel"
             "(op_vis_memb, (\<in>))\<in>V \<rightarrow> \<langle>V\<rangle>vis_rel \<rightarrow> bool_rel"
  assumes Vid[simp]: "V=Id"
  shows "(\<lambda> G P R. nres_of (find_path1_restr_code op_vis_insert op_vis_memb G P R),find_path1_restr_spec)
  \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> (V \<rightarrow> bool_rel) \<rightarrow> \<langle>V\<rangle>vis_rel \<rightarrow>
    \<langle>\<langle>\<langle>V\<rangle>vis_rel, \<langle>V\<rangle>list_rel \<times>\<^sub>r V\<rangle>sum_rel\<rangle>nres_rel"
    
proof -
  note find_path1_restr_code.refine[OF G[simplified], param_fo, THEN nres_relD]
  also note find_path1_restr_correct
  finally show ?thesis by (force intro!: nres_relI)
qed

lemmas find_path1_restr_autoref[autoref_rules] = find_path1_restr_autoref_aux[OF GEN_OP_D GEN_OP_D PREFER_id_D]

schematic_goal find_path1_code:
  assumes Vid: "V = (Id :: 'a :: hashable rel)"
  assumes [unfolded Vid,autoref_rules]:
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
    "(Pi,P)\<in>V \<rightarrow> bool_rel"
  notes [autoref_tyrel] = TYRELI[where R="\<langle>(Id::('a\<times>'a::hashable)set)\<rangle>dflt_ahs_rel"]
  shows "(nres_of ?c,find_path1 G P)
  \<in> \<langle>\<langle>\<langle>V\<rangle>list_rel \<times>\<^sub>r V\<rangle>option_rel\<rangle>nres_rel"
  unfolding find_path1_def[abs_def] Vid
  using [[autoref_trace_failed_id]]
  apply (autoref_monadic (trace))
  done
concrete_definition find_path1_code uses find_path1_code

export_code find_path1_code checking SML

lemma find_path1_code_autoref_aux:
  assumes Vid: "V = (Id :: 'a :: hashable rel)"
  shows "(\<lambda> G P. nres_of (find_path1_code G P), find_path1_spec)
    \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> (V \<rightarrow> bool_rel) \<rightarrow> \<langle>\<langle>\<langle>V\<rangle>list_rel \<times>\<^sub>r V\<rangle>option_rel\<rangle>nres_rel"
proof -
  note find_path1_code.refine[OF Vid, param_fo, THEN nres_relD, simplified]
  also note find_path1_correct
  finally show ?thesis by (force intro!: nres_relI)
qed

lemmas find_path1_autoref[autoref_rules] = find_path1_code_autoref_aux[OF PREFER_id_D]

subsection \<open>Conclusion\<close>
text \<open>
  We have synthesized an efficient implementation for an algorithm to find a path
  to a reachable node that satisfies a predicate. The algorithm comes in four variants,
  with and without empty path, and with and without node restriction.

  We have set up the Autoref tool, to insert this algorithms for the following 
  specifications:
  \<^item> @{term "find_path0_spec G P"} --- find path to node that satisfies @{term P}.
  \<^item> @{term "find_path1_spec G P"} --- find non-empty path to node that satisfies @{term P}.
  \<^item> @{term "find_path0_restr_spec G P R"} --- find path, with nodes from @{term R} already searched.
  \<^item> @{term "find_path1_restr_spec"} --- find non-empty path, with nodes from @{term R} already searched.

\<close>
thm find_path0_autoref
thm find_path1_autoref
thm find_path0_restr_autoref
thm find_path1_restr_autoref


end

