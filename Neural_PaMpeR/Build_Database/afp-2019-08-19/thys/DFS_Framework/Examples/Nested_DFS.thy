section \<open>Nested DFS\<close>
theory Nested_DFS
imports DFS_Find_Path
begin
text \<open>Nested DFS is a standard method for Buchi-Automaton emptiness check.\<close>

subsection \<open>Auxiliary Lemmas\<close>

lemma closed_restrict_aux:
  assumes CL: "E``F \<subseteq> F \<union> S"
  assumes NR: "E\<^sup>*``U \<inter> S = {}"
  assumes SS: "U \<subseteq> F"
  shows "E\<^sup>*``U \<subseteq> F"
  \<comment> \<open>Auxiliary lemma to show that nodes reachable from a finished node must  
      be finished if, additionally, no stack node is reachable\<close>
proof clarify
  fix u v
  assume A: "(u,v)\<in>E\<^sup>*" "u\<in>U"
  hence M: "E\<^sup>*``{u} \<inter> S = {}" "u\<in>F" using NR SS by blast+

  from A(1) M show "v\<in>F"
    apply (induct rule: converse_rtrancl_induct) 
    using CL apply (auto dest: rtrancl_Image_advance_ss) 
    done

qed


subsection \<open>Instantiation of the Framework\<close>
record 'v blue_dfs_state = "'v state" +
  lasso :: "('v list \<times> 'v list) option" (* pr \<times> pl *)
  red  :: "'v set"

type_synonym 'v blue_dfs_param = "('v, ('v,unit) blue_dfs_state_ext) parameterization"

lemma lasso_more_cong[cong]:"state.more s = state.more s' \<Longrightarrow> lasso s = lasso s'"
  by (cases s, cases s') simp
lemma red_more_cong[cong]: "state.more s = state.more s' \<Longrightarrow> red s = red s'"
  by (cases s, cases s') simp

lemma [simp]: "s\<lparr> state.more := \<lparr> lasso = foo, red = bar \<rparr> \<rparr> = s \<lparr> lasso := foo, red := bar \<rparr>"
  by (cases s) simp


abbreviation "dropWhileNot v \<equiv> dropWhile ((\<noteq>) v)"
abbreviation "takeWhileNot v \<equiv> takeWhile ((\<noteq>) v)"

locale BlueDFS_defs = graph_defs G
  for G :: "('v, 'more) graph_rec_scheme"  +
  fixes accpt :: "'v \<Rightarrow> bool"
begin

  definition "blue s \<equiv> dom (finished s) - red s"
  definition "cyan s \<equiv> set (stack s)"
  definition "white s \<equiv> - dom (discovered s)"

  abbreviation "red_dfs R ss x \<equiv> find_path1_restr_spec (G \<lparr> g_V0 := {x} \<rparr>) ss R"

  definition mk_blue_witness 
    :: "'v blue_dfs_state \<Rightarrow> 'v fpr_result \<Rightarrow> ('v,unit) blue_dfs_state_ext"
    where
    "mk_blue_witness s redS \<equiv> case redS of
                 Inl R' \<Rightarrow> \<lparr> lasso = None, red = (R' \<^cancel>\<open>\<union> red s\<close>) \<rparr>
               | Inr (vs, v) \<Rightarrow> let rs = rev (stack s) in 
                             \<lparr> lasso = Some (rs, vs@dropWhileNot v rs), red = red s\<rparr>"

  definition run_red_dfs 
    :: "'v \<Rightarrow> 'v blue_dfs_state \<Rightarrow> ('v,unit) blue_dfs_state_ext nres" 
    where
    "run_red_dfs u s \<equiv> case lasso s of None \<Rightarrow> do {
             redS \<leftarrow> red_dfs (red s) (\<lambda>x. x = u \<or> x \<in> cyan s) u;
             RETURN (mk_blue_witness s redS)
           }
          | _ \<Rightarrow> NOOP s"

  text \<open> Schwoon-Esparza extension \<close>
  definition "se_back_edge u v s \<equiv> case lasso s of
    None \<Rightarrow> 
      \<comment> \<open>it's a back edge, so \<open>u\<close> and \<open>v\<close> are both on stack\<close>
      \<comment> \<open>we differentiate whether \<open>u\<close> or \<open>v\<close> is the 'culprit'\<close>
      \<comment> \<open>to generate a better counter example\<close>
      if accpt u then
         let rs = rev (tl (stack s));
             ur = rs;
             ul = u#dropWhileNot v rs
         in RETURN \<lparr>lasso = Some (ur,ul), red = red s\<rparr>
      else if accpt v then
         let rs = rev (stack s);
             vr = takeWhileNot v rs;
             vl = dropWhileNot v rs
         in RETURN \<lparr>lasso = Some (vr,vl), red = red s\<rparr>
      else NOOP s
  | _ \<Rightarrow> NOOP s"

  definition blue_dfs_params :: "'v blue_dfs_param"
    where "blue_dfs_params = \<lparr>
    on_init = RETURN \<lparr> lasso = None, red = {} \<rparr>,
    on_new_root = \<lambda>v0 s. NOOP s,
    on_discover = \<lambda>u v s. NOOP s,
    on_finish = \<lambda>u s. if accpt u then run_red_dfs u s else NOOP s,
    on_back_edge = se_back_edge,
    on_cross_edge = \<lambda>u v s. NOOP s,
    is_break = \<lambda>s. lasso s \<noteq> None \<rparr>"
  
  schematic_goal blue_dfs_params_simps[simp]:
    "on_init blue_dfs_params = ?OI"
    "on_new_root blue_dfs_params = ?ONR"
    "on_discover blue_dfs_params = ?OD"
    "on_finish blue_dfs_params = ?OF"
    "on_back_edge blue_dfs_params = ?OBE"
    "on_cross_edge blue_dfs_params = ?OCE"
    "is_break blue_dfs_params = ?IB"
    unfolding blue_dfs_params_def gen_parameterization.simps
    by (rule refl)+


  sublocale param_DFS_defs G blue_dfs_params 
    by unfold_locales

end

locale BlueDFS = BlueDFS_defs G accpt + param_DFS G blue_dfs_params
  for G :: "('v, 'more) graph_rec_scheme" and accpt :: "'v \<Rightarrow> bool"

lemma BlueDFSI: 
  assumes "fb_graph G" 
  shows "BlueDFS G"
proof -
  interpret fb_graph G by fact
  show ?thesis by unfold_locales
qed

locale BlueDFS_invar = BlueDFS +
  DFS_invar where param = blue_dfs_params

context BlueDFS_defs begin

lemma BlueDFS_invar_eq[simp]:
  shows "DFS_invar G blue_dfs_params s \<longleftrightarrow> BlueDFS_invar G accpt s" 
proof
  assume "DFS_invar G blue_dfs_params s"
  interpret DFS_invar G blue_dfs_params s by fact
  show "BlueDFS_invar G accpt s" by unfold_locales
next
  assume "BlueDFS_invar G accpt s"
  then interpret BlueDFS_invar G accpt s .
  show "DFS_invar G blue_dfs_params s" by unfold_locales
qed

end

subsection \<open>Correctness Proof\<close>
context BlueDFS begin

  definition "blue_basic_invar s \<equiv> 
    case lasso s of
      None \<Rightarrow> restr_invar E (red s) (\<lambda>x. x\<in>set (stack s)) 
        \<and> red s \<subseteq> dom (finished s)
    | Some l \<Rightarrow> True"

  lemma (in BlueDFS_invar) red_DFS_precond_aux:
    assumes BI: "blue_basic_invar s"
    assumes [simp]: "lasso s = None"
    assumes SNE: "stack s \<noteq> []"
    shows
      "fb_graph (G \<lparr> g_V0 := {hd (stack s)} \<rparr>)"
    and "fb_graph (G \<lparr> g_E := E \<inter> UNIV \<times> - red s, g_V0 := {hd (stack s)} \<rparr>)" 
    and "restr_invar E (red s) (\<lambda>x. x \<in> set (stack s))"
    using stack_reachable \<open>stack s \<noteq> []\<close> 
    apply (rule_tac fb_graph_subset, auto) []
    using stack_reachable \<open>stack s \<noteq> []\<close> 
    apply (rule_tac fb_graph_subset, auto) []

    using BI apply (simp add: blue_basic_invar_def)
    done

  lemma (in BlueDFS_invar) red_dfs_pres_bbi:
    assumes BI: "blue_basic_invar s"
    assumes [simp]: "lasso s = None" and SNE: "stack s \<noteq> []"
    assumes "pending s `` {hd (stack s)} = {}"
    shows "run_red_dfs (hd (stack s)) (finish (hd (stack s)) s) \<le>\<^sub>n
      SPEC (\<lambda>e. 
        DFS_invar G blue_dfs_params (finish (hd (stack s)) s\<lparr>state.more := e\<rparr>) 
        \<longrightarrow> blue_basic_invar (finish (hd (stack s)) s\<lparr>state.more := e\<rparr>))"
  proof -
    have [simp]: "(\<lambda>x. x = hd (stack s) \<or> x \<in> cyan (finish (hd (stack s)) s)) = 
      (\<lambda>x. x\<in>set (stack s))"
      using \<open>stack s \<noteq> []\<close>
      unfolding finish_def cyan_def by (auto simp: neq_Nil_conv)

    show ?thesis
      unfolding run_red_dfs_def
      apply simp
      apply (refine_vcg)
      apply simp
    proof -
      fix fp1
      define s' where "s' = finish (hd (stack s)) s"
      assume FP_spec: 
        "find_path1_restr_pred (G \<lparr> g_V0 := {hd (stack s)} \<rparr>) (\<lambda>x. x \<in> set (stack s)) (red s) fp1"
      assume "BlueDFS_invar G accpt (s'\<lparr>state.more := mk_blue_witness s' fp1\<rparr>)"      
      then interpret i: BlueDFS_invar G accpt "(s'\<lparr>state.more := mk_blue_witness s' fp1\<rparr>)"
        by simp
      
      have [simp]: 
        "red s' = red s" 
        "discovered s' = discovered s" 
        "dom (finished s') = insert (hd (stack s)) (dom (finished s))"
        unfolding s'_def finish_def by auto

      {
        fix R'
        assume [simp]: "fp1 = Inl R'"
        from FP_spec[unfolded find_path1_restr_pred_def, simplified] 
        have 
          R'FMT: "R' = red s \<union> E\<^sup>+ `` {hd (stack s)}" 
          and RI: "restr_invar E R' (\<lambda>x. x \<in> set (stack s))" 
          by auto

        from BI have "red s \<subseteq> dom (finished s)"
          unfolding blue_basic_invar_def by auto
        also have "E\<^sup>+ `` {hd (stack s)} \<subseteq> dom (finished s)"
        proof (intro subsetI, elim ImageE, simp)
          fix v
          assume "(hd (stack s),v)\<in>E\<^sup>+"

          then obtain u where "(hd (stack s),u)\<in>E" and "(u,v)\<in>E\<^sup>*" 
            by (auto simp: trancl_unfold_left)

          from RI have NR: "E\<^sup>+ `` {hd (stack s)} \<inter> set (stack s) = {}"
            unfolding restr_invar_def by (auto simp: R'FMT)

          with \<open>(hd (stack s),u)\<in>E\<close> have "u\<notin>set (stack s)" by auto
          with i.finished_closed[simplified] \<open>(hd (stack s),u)\<in>E\<close> 
          have UID: "u\<in>dom (finished s)" by (auto simp: stack_set_def)

          from NR \<open>(hd (stack s),u)\<in>E\<close> have NR': "E\<^sup>*``{u} \<inter> set (stack s) = {}"
            by (auto simp: trancl_unfold_left)

          have CL: "E `` dom (finished s) \<subseteq> dom (finished s) \<union> set (stack s)"
            using finished_closed discovered_eq_finished_un_stack
            by simp

          from closed_restrict_aux[OF CL NR'] UID 
          have "E\<^sup>* `` {u} \<subseteq> dom (finished s)" by simp
          with \<open>(u,v)\<in>E\<^sup>*\<close>  show "v \<in> dom (finished s)" by auto
        qed
        finally (sup_least) 
        have "R' \<subseteq> dom (finished s) \<and> red s \<subseteq> dom (finished s)" 
          by (simp add: R'FMT)
      } note aux1 = this

      show "blue_basic_invar (s'\<lparr>state.more := mk_blue_witness s' fp1\<rparr>)"
        unfolding blue_basic_invar_def mk_blue_witness_def
        apply (simp split: option.splits sum.splits)
        apply (intro allI conjI impI)

        using FP_spec SNE
        apply (auto 
          simp: s'_def blue_basic_invar_def find_path1_restr_pred_def
          simp: restr_invar_def
          simp: neq_Nil_conv) []

        apply (auto dest!: aux1) []
        done
    qed
  qed

  lemma blue_basic_invar: "is_invar blue_basic_invar"
  proof (induct rule: establish_invarI)
    case (finish s) then interpret BlueDFS_invar where s=s by simp

    have [simp]: "(\<lambda>x. x = hd (stack s) \<or> x \<in> cyan (finish (hd (stack s)) s)) = 
      (\<lambda>x. x\<in>set (stack s))"
      using \<open>stack s \<noteq> []\<close>
      unfolding finish_def cyan_def by (auto simp: neq_Nil_conv)

    from finish show ?case 
      apply (simp)
      apply (intro conjI impI)
      apply (rule leof_trans[OF red_dfs_pres_bbi], assumption+, simp)

      apply (auto simp: restr_invar_def blue_basic_invar_def neq_Nil_conv) []
      done
  qed (auto simp: blue_basic_invar_def cond_def se_back_edge_def
            simp: restr_invar_def empty_state_def pred_defs
            simp: DFS_invar.discovered_eq_finished_un_stack
            simp del: BlueDFS_invar_eq
            split: option.splits)

  lemmas (in BlueDFS_invar) s_blue_basic_invar 
    = blue_basic_invar[THEN make_invar_thm]

  lemmas (in BlueDFS_invar) red_DFS_precond 
    = red_DFS_precond_aux[OF s_blue_basic_invar]

  sublocale DFS G blue_dfs_params
    apply unfold_locales
    
    apply (clarsimp_all 
      simp:  se_back_edge_def run_red_dfs_def refine_pw_simps pre_on_defs
      split: option.splits)
    
    unfolding nofail_SPEC_iff
    apply (refine_vcg)
      apply (erule BlueDFS_invar.red_DFS_precond, auto) []

      apply (simp add: cyan_def finish_def)
      apply (erule BlueDFS_invar.red_DFS_precond, auto) []

      apply (rule TrueI)
    done

end

context BlueDFS_invar
begin

  context assumes [simp]: "lasso s = None"
  begin
    lemma red_closed:
      "E `` red s \<subseteq> red s"
      using s_blue_basic_invar
      unfolding blue_basic_invar_def restr_invar_def
      by simp
  
    lemma red_stack_disjoint:
      "set (stack s) \<inter> red s = {}"
      using s_blue_basic_invar
      unfolding blue_basic_invar_def restr_invar_def
      by auto
    
    lemma red_finished: "red s \<subseteq> dom (finished s)"
      using s_blue_basic_invar
      unfolding blue_basic_invar_def
      by auto

    (* Play of Colors *)
    lemma all_nodes_colored: "white s \<union> blue s \<union> cyan s \<union> red s = UNIV "  
      unfolding white_def blue_def cyan_def
      by (auto simp: stack_set_def)

    lemma colors_disjoint:
      "white s \<inter> (blue s \<union> cyan s \<union> red s) = {}"
      "blue s \<inter> (white s \<union> cyan s \<union> red s) = {}"
      "cyan s \<inter> (white s \<union> blue s \<union> red s) = {}"
      "red s \<inter> (white s \<union> blue s \<union> cyan s) = {}"
      unfolding white_def blue_def cyan_def
      using finished_discovered red_finished
      unfolding stack_set_def
      by blast+
  
  end

  lemma (in BlueDFS) i_no_accpt_cyle_in_finish:
    "is_invar (\<lambda>s. lasso s = None \<longrightarrow> (\<forall>x. accpt x \<and> x \<in> dom (finished s) \<longrightarrow> (x,x) \<notin> E\<^sup>+))"
  proof (induct rule: establish_invarI)
    case (finish s s' u) then interpret BlueDFS_invar where s=s by simp

    let ?onstack = "\<lambda>x. x\<in>set (stack s)"
    let ?rE = "rel_restrict E (red s)"

    from finish obtain sh st where [simp]: "stack s = sh#st" 
      by (auto simp: neq_Nil_conv)

    have 1: "g_E (G \<lparr> g_V0 := {hd (stack s)} \<rparr>) = E" by simp

    { (* TODO/FIXME: Ughly proof structure! *)
      fix R'::"'v set"
      let ?R' = "R' \<^cancel>\<open>\<union> red s\<close>"
      let ?s = "s'\<lparr> lasso := None, red := ?R'\<rparr>"

      assume "\<And>v. (hd (stack s), v) \<in> ?rE\<^sup>+ \<Longrightarrow> \<not> ?onstack v"
      and accpt: "accpt u"
      and NL[simp]: "lasso s = None"
      hence no_hd_cycle: "(hd (stack s), hd (stack s)) \<notin> ?rE\<^sup>+"
        by auto

      from finish have "stack s \<noteq> []" by simp
      from hd_in_set[OF this] have "hd (stack s) \<notin> red s" 
        using red_stack_disjoint
        by auto
      hence "(hd (stack s),hd (stack s)) \<notin> E\<^sup>+"
        using no_hd_cycle rel_restrict_tranclI red_closed[OF NL]
        by metis 
      with accpt finish have 
        "\<forall>x. accpt x \<and> x \<in> dom (finished ?s) \<longrightarrow> (x,x) \<notin> E\<^sup>+"
        by auto
    } with finish have
      "red_dfs (red s) ?onstack (hd (stack s))
         \<le> SPEC (\<lambda>x. \<forall>R. x = Inl R \<longrightarrow>
             DFS_invar G blue_dfs_params (lasso_update Map.empty s'\<lparr>red := R \<^cancel>\<open>\<union> red s\<close>\<rparr>) \<longrightarrow>
             (\<forall>x. accpt x \<and> x\<in>dom (finished s') \<longrightarrow> (x, x) \<notin> E\<^sup>+))"
      apply -
      apply (rule find_path1_restr_spec_rule, intro conjI)

      apply (rule red_DFS_precond, simp_all) []
      unfolding 1
      apply (rule red_DFS_precond, simp_all) []

      apply (auto simp: find_path1_restr_pred_def restr_invar_def) 
      done
    note aux = leof_trans[OF this[simplified,THEN leof_lift]]

    note [refine_vcg del] = find_path1_restr_spec_rule

    from finish show ?case
      apply simp
      apply (intro conjI impI)
        unfolding run_red_dfs_def mk_blue_witness_def cyan_def
        apply clarsimp
        apply (refine_vcg aux)
        apply (auto split: sum.splits)
      done
  next
    case back_edge thus ?case
      by (simp add: se_back_edge_def split: option.split)
  qed simp_all

  lemma no_accpt_cycle_in_finish:
    "\<lbrakk>lasso s = None; accpt v; v \<in> dom (finished s)\<rbrakk> \<Longrightarrow> (v,v) \<notin> E\<^sup>+"
    using i_no_accpt_cyle_in_finish[THEN make_invar_thm]
    by blast

end

context BlueDFS
begin
  definition lasso_inv where
    "lasso_inv s \<equiv> \<forall>pr pl. lasso s = Some (pr,pl) \<longrightarrow> 
                                      pl \<noteq> []
                                    \<and> (\<exists>v0\<in>V0. path E v0 pr (hd pl)) 
                                    \<and> accpt (hd pl) 
                                    \<and> path E (hd pl) pl (hd pl)"

  lemma (in BlueDFS_invar) se_back_edge_lasso_inv:
    assumes b_inv: "lasso_inv s"
    and ne: "stack s \<noteq> []"
    and R: "lasso s = None"
    and p:"(hd (stack s), v) \<in> pending s"
    and v: "v \<in> dom (discovered s)" "v \<notin> dom (finished s)"
    and s': "s' = back_edge (hd (stack s)) v (s\<lparr>pending := pending s - {(u,v)}\<rparr>)"
    shows "se_back_edge (hd (stack s)) v s'
                \<le> SPEC (\<lambda>e. DFS_invar G blue_dfs_params (s'\<lparr>state.more := e\<rparr>) \<longrightarrow>
                            lasso_inv (s'\<lparr>state.more := e\<rparr>))"
  proof -

    from v stack_set_def have v_in: "v \<in> set (stack s)" by simp
    from p have uv_edg: "(hd (stack s), v) \<in> E" by (auto dest: pendingD)
  
    {
      assume accpt: "accpt (hd (stack s))"
      let ?ur = "rev (tl (stack s))"
      let ?ul = "hd (stack s)#dropWhileNot v (rev (tl (stack s)))"
      let ?s = "s'\<lparr>lasso := Some (?ur, ?ul), red := red s\<rparr>"

      assume "DFS_invar G blue_dfs_params ?s"

      have [simp]: "stack ?s = stack s"
        by (simp add: s')

      have hd_ul[simp]: "hd ?ul = hd (stack s)" by simp

      have "?ul \<noteq> []" by simp

      moreover have P:"\<exists>v0\<in>V0. path E v0 ?ur (hd ?ul)"
        using stack_is_path[OF ne]
        by auto
      moreover
      from accpt have "accpt (hd ?ul)" by simp

      moreover have "path E (hd ?ul) ?ul (hd ?ul)"
      proof (cases "v = hd (stack s)")
        case True 
        with distinct_hd_tl stack_distinct have ul: "?ul = [hd (stack s)]" 
          by force
        from True uv_edg show ?thesis
          by (subst ul)+ (simp add: path1)
      next
        case False with v_in ne have "v \<in> set ?ur"
          by (auto simp add: neq_Nil_conv)
        with P show ?thesis
          by (fastforce intro: path_prepend 
                           dropWhileNot_path[where p="?ur"]
                           uv_edg)
      qed

      ultimately have "lasso_inv ?s" by (simp add: lasso_inv_def)
    }

    moreover
    {
      assume accpt: "accpt v"
      let ?vr = "takeWhileNot v (rev (stack s))"
      let ?vl = "dropWhileNot v (rev (stack s))"
      let ?s = "s'\<lparr>lasso := Some(?vr, ?vl), red := red s\<rparr>"

      assume "DFS_invar G blue_dfs_params ?s"
      
      have [simp]: "stack ?s = stack s"
        by (simp add: s')
      
      from ne v_in have hd_vl[simp]: "hd ?vl = v"
        by (induct ("stack s") rule: rev_nonempty_induct) auto
      
      from v_in have "?vl \<noteq> []" by simp
      
      moreover from hd_succ_stack_is_path[OF ne] uv_edg have 
        P: "\<exists>v0\<in>V0. path E v0 (rev (stack s)) v" 
        by auto
      with ne v_in have "\<exists>v0\<in>V0. path E v0 ?vr (hd ?vl)"
        by (force intro: takeWhileNot_path)

      moreover from accpt have "accpt (hd ?vl)" by simp

      moreover from P ne v_in have "path E (hd ?vl) ?vl (hd ?vl)"
        by (force intro: dropWhileNot_path)

      ultimately have "lasso_inv ?s" by (simp add: lasso_inv_def)
    }

    moreover
    {
      assume "\<not> accpt (hd (stack s))" "\<not> accpt v"
      let ?s = "s'\<lparr>state.more := state.more s'\<rparr>"
      
      assume "DFS_invar G blue_dfs_params ?s"
      
      from assms have "lasso_inv ?s"
        by (auto simp add: lasso_inv_def)
    }

    (* TODO: Clean up this proof, separate logical arguments from framework 
      boilerplate! *)
    ultimately show ?thesis
      using R s'
      unfolding se_back_edge_def
      by (auto split: option.splits)
  qed


  lemma lasso_inv:
    "is_invar lasso_inv"
  proof (induct rule: establish_invarI)
    case (finish s s' u) then interpret BlueDFS_invar where s=s by simp
    (* TODO/FIXME: Ughly proof structure *)
    let ?onstack = "\<lambda>x. x \<in> set (stack s)"
    let ?rE = "rel_restrict E (red s)"
    let ?revs = "rev (tl (stack s))"
    
    note ne = \<open>stack s \<noteq> []\<close>

    note [simp] = \<open>u=hd (stack s)\<close>

    from finish have [simp]: 
      "\<And>x. x = hd (stack s) \<or> x \<in> set (stack s') \<longleftrightarrow> x\<in>set (stack s)"
      "red s' = red s"
      "lasso s' = lasso s"
      by (auto simp: neq_Nil_conv)


    {
      fix v vs
      let ?cyc = "vs @ dropWhileNot v ?revs"
      let ?s = "s'\<lparr>lasso := Some (?revs, ?cyc), red := red s\<rparr>"
      
      assume "DFS_invar G blue_dfs_params ?s"
        and vs: "vs \<noteq> []" "path ?rE (hd (stack s)) vs v"
        and v: "?onstack v"
        and accpt: "accpt (hd (stack s))"
      from vs have P: "path E (hd (stack s)) vs v"
        by (metis path_mono rel_restrict_sub)
      
      have hds[simp]: "hd vs = hd (stack s)" "hd ?cyc = hd (stack s)"
        using vs path_hd
        by simp_all
      
      from vs have "?cyc \<noteq> []" by simp
      
      moreover have P0: "\<exists>v0\<in>V0. path E v0 ?revs (hd ?cyc)"
        using stack_is_path[OF ne]
        by auto

      moreover from accpt have "accpt (hd ?cyc)" by simp

      moreover have "path E (hd ?cyc) ?cyc (hd ?cyc)"
      proof (cases "tl (stack s) = []")
        case True with ne last_stack_in_V0 obtain v0 where "v0 \<in> V0"
          and [simp]: "stack s = [v0]" 
          by (auto simp: neq_Nil_conv)
        with v True finish have [simp]: "v = v0" by simp
        
        from True P show ?thesis by simp
      next
        case False note tl_ne = this

        show ?thesis
        proof (cases "v = hd (stack s)")
          case True hence "v \<notin> set ?revs"
            using ne stack_distinct by (auto simp: neq_Nil_conv)
          hence "?cyc = vs" by fastforce
          with P True show ?thesis by (simp del: dropWhile_eq_Nil_conv)
        next
          case False with finish v have "v \<in> set ?revs" 
            by (auto simp: neq_Nil_conv)
          with tl_ne False P0  show ?thesis 
            by (force intro: path_conc[OF P] 
                dropWhileNot_path[where p="?revs"])
        qed
      qed
      
      ultimately have "lasso_inv ?s" by (simp add: lasso_inv_def)
    }
    hence "accpt (hd (stack s)) \<longrightarrow> lasso s = None \<longrightarrow>
            red_dfs (red s) ?onstack (hd (stack s)) \<le> SPEC (\<lambda>rs. \<forall>vs v. 
                rs = Inr (vs,v) \<longrightarrow>
                  DFS_invar G blue_dfs_params (s'\<lparr>lasso := Some (?revs, vs @ dropWhileNot v ?revs), red:= red s\<rparr>) \<longrightarrow>
                   lasso_inv (s'\<lparr>lasso := Some (?revs, vs @ dropWhileNot v ?revs), red:=red s\<rparr>))"
      apply clarsimp
      apply (rule find_path1_restr_spec_rule, intro conjI)
      apply (rule red_DFS_precond, simp_all add: ne) []
      apply (simp, rule red_DFS_precond, simp_all add: ne) []

      using red_stack_disjoint ne

      apply clarsimp
      apply rprems
      apply (simp_all add: find_path1_restr_pred_def restr_invar_def)
      apply (fastforce intro: path_restrict_tl rel_restrictI)
      done
    note aux1 = this[rule_format,THEN leof_lift]

    show ?case
      apply simp
      unfolding run_red_dfs_def mk_blue_witness_def cyan_def

      apply (simp 
        add: run_red_dfs_def mk_blue_witness_def cyan_def
        split: option.splits)
      apply (intro conjI impI)
      apply (refine_vcg leof_trans[OF aux1])
      using finish
      apply (auto simp add: lasso_inv_def split: sum.split)
      done
  next
    case (back_edge s s' u v) then interpret BlueDFS_invar where s=s by simp
    
    from back_edge se_back_edge_lasso_inv[THEN leof_lift] show ?case
      by auto
  qed (simp_all add: lasso_inv_def empty_state_def)
end

context BlueDFS_invar
begin
  lemmas s_lasso_inv = lasso_inv[THEN make_invar_thm]

  lemma 
    assumes "lasso s = Some (pr,pl)"
    shows loop_nonempty: "pl \<noteq> []"
    and accpt_loop: "accpt (hd pl)"
    and loop_is_path: "path E (hd pl) pl (hd pl)"
    and loop_reachable: "\<exists>v0\<in>V0. path E v0 pr (hd pl)"
    using assms s_lasso_inv
    by (simp_all add: lasso_inv_def)

  lemma blue_dfs_correct:
    assumes NC: "\<not> cond s"
    shows "case lasso s of
      None \<Rightarrow> \<not>(\<exists>v0\<in>V0. \<exists>v. (v0,v) \<in> E\<^sup>* \<and> accpt v \<and> (v,v) \<in> E\<^sup>+)
    | Some (pr,pl) \<Rightarrow> (\<exists>v0\<in>V0. \<exists>v. 
        path E v0 pr v \<and> accpt v \<and> pl\<noteq>[] \<and> path E v pl v)"
  proof (cases "lasso s")
    case None
    moreover
    {
      fix v v0
      assume "v0 \<in> V0" "(v0,v) \<in> E\<^sup>*" "accpt v" "(v,v) \<in> E\<^sup>+"
      moreover
      hence "v \<in> reachable" by (auto)
      with nc_finished_eq_reachable NC None have "v \<in> dom (finished s)"
        by simp
      moreover note no_accpt_cycle_in_finish None
      ultimately have False by blast
    }
    ultimately show ?thesis by auto
  next
    case (Some prpl) with s_lasso_inv show ?thesis
      by (cases prpl) 
         (auto intro: path_is_rtrancl path_is_trancl simp: lasso_inv_def)
  qed

end

subsection \<open>Interface\<close>

interpretation BlueDFS_defs for G accpt .

definition "nested_dfs_spec G accpt \<equiv> \<lambda>r. case r of
  None \<Rightarrow> \<not>(\<exists>v0\<in>g_V0 G. \<exists>v. (v0,v) \<in> (g_E G)\<^sup>* \<and> accpt v \<and> (v,v) \<in> (g_E G)\<^sup>+)
| Some (pr,pl) \<Rightarrow> (\<exists>v0\<in>g_V0 G. \<exists>v. 
    path (g_E G) v0 pr v \<and> accpt v \<and> pl\<noteq>[] \<and> path (g_E G) v pl v)"

definition "nested_dfs G accpt \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> it_dfs TYPE('a) G accpt;
  RETURN (lasso s)
}"

theorem nested_dfs_correct: 
  assumes "fb_graph G"
  shows "nested_dfs G accpt \<le> SPEC (nested_dfs_spec G accpt)"
proof -
  interpret fb_graph G by fact
  interpret BlueDFS G accpt by unfold_locales
  
  show ?thesis 
    unfolding nested_dfs_def
    apply (refine_rcg refine_vcg)
    apply fact
    apply (rule weaken_SPEC[OF it_dfs_correct])
    apply clarsimp
  proof -
    fix s
    assume "BlueDFS_invar G accpt s"
    then interpret BlueDFS_invar G accpt s .
    
    assume "\<not>cond TYPE('b) G accpt s"
    from blue_dfs_correct[OF this] show "nested_dfs_spec G accpt (lasso s)"
      unfolding nested_dfs_spec_def by simp
  qed
qed

subsection \<open>Implementation\<close>

record 'v bdfs_state_impl = "'v simple_state" +
  lasso_impl :: "('v list \<times> 'v list) option"
  red_impl :: "'v set"

definition "bdfs_erel \<equiv> {(\<lparr>lasso_impl=li,red_impl=ri\<rparr>,\<lparr>lasso=l, red=r\<rparr>) 
  | li ri l r. li=l \<and> ri=r}"

abbreviation "bdfs_rel \<equiv> \<langle>bdfs_erel\<rangle>simple_state_rel"

definition mk_blue_witness_impl
  :: "'v bdfs_state_impl \<Rightarrow> 'v fpr_result \<Rightarrow> ('v,unit) bdfs_state_impl_ext"
  where
  "mk_blue_witness_impl s redS \<equiv> 
    case redS of
      Inl R' \<Rightarrow> \<lparr> lasso_impl = None, red_impl = (R' \<^cancel>\<open>\<union> red_impl s\<close>) \<rparr>
    | Inr (vs, v) \<Rightarrow> let 
        rs = rev (map fst (CAST (ss_stack s))) 
      in \<lparr> 
        lasso_impl = Some (rs, vs@dropWhileNot v rs), 
        red_impl = red_impl s\<rparr>"

lemma mk_blue_witness_impl[refine]:
  "\<lbrakk> (si,s)\<in>bdfs_rel; (ri,r)\<in>\<langle>Id, \<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>sum_rel \<rbrakk> 
  \<Longrightarrow> (mk_blue_witness_impl si ri, mk_blue_witness s r)\<in>bdfs_erel"
  unfolding mk_blue_witness_impl_def mk_blue_witness_def
  apply parametricity
  apply (cases si, cases s)
  apply (auto simp: bdfs_erel_def simple_state_rel_def) []
  apply (rule introR[where R="\<langle>Id\<rangle>list_rel"])
  apply (cases si, cases s)
  apply (auto simp: bdfs_erel_def simple_state_rel_def comp_def) []
  apply (cases si, cases s)
  apply (auto simp: bdfs_erel_def simple_state_rel_def) []
  done

definition "cyan_impl s \<equiv> on_stack s"
lemma cyan_impl[refine]: "\<lbrakk>(si,s)\<in>bdfs_rel\<rbrakk> \<Longrightarrow> (cyan_impl si, cyan s)\<in>Id"
  unfolding cyan_impl_def cyan_def
  by (auto simp: bdfs_erel_def simple_state_rel_def)

definition run_red_dfs_impl 
  :: "('v, 'more) graph_rec_scheme \<Rightarrow> 'v \<Rightarrow> 'v bdfs_state_impl \<Rightarrow> ('v,unit) bdfs_state_impl_ext nres" 
  where
  "run_red_dfs_impl G u s \<equiv> case lasso_impl s of None \<Rightarrow> do {
           redS \<leftarrow> red_dfs TYPE('more) G (red_impl s) (\<lambda>x. x = u \<or> x \<in> cyan_impl s) u;
           RETURN (mk_blue_witness_impl s redS)
         }
        | _ \<Rightarrow> RETURN (simple_state.more s)"

  lemma run_red_dfs_impl[refine]: "\<lbrakk>(Gi,G)\<in>Id; (ui,u)\<in>Id; (si,s)\<in>bdfs_rel\<rbrakk> 
    \<Longrightarrow> run_red_dfs_impl Gi ui si \<le>\<Down>bdfs_erel (run_red_dfs TYPE('a) G u s)"
    unfolding run_red_dfs_impl_def run_red_dfs_def
    apply refine_rcg
    apply refine_dref_type
    apply (cases si, cases s, auto simp: bdfs_erel_def simple_state_rel_def) []
    apply (cases si, cases s, 
      auto simp: bdfs_erel_def simple_state_rel_def cyan_impl_def cyan_def) []
    apply (auto simp: bdfs_erel_def simple_state_rel_def) [2]
    done

  definition "se_back_edge_impl accpt u v s \<equiv> case lasso_impl s of
    None \<Rightarrow> 
      if accpt u then
         let rs = rev (map fst (tl (CAST (ss_stack s))));
             ur = rs;
             ul = u#dropWhileNot v rs
         in RETURN \<lparr>lasso_impl = Some (ur,ul), red_impl = red_impl s\<rparr>
      else if accpt v then
         let rs = rev (map fst (CAST (ss_stack s)));
             vr = takeWhileNot v rs;
             vl = dropWhileNot v rs
         in RETURN \<lparr>lasso_impl = Some (vr,vl), red_impl = red_impl s\<rparr>
      else RETURN (simple_state.more s)
  | _ \<Rightarrow> RETURN (simple_state.more s)"

  lemma se_back_edge_impl[refine]: "\<lbrakk> (accpti,accpt)\<in>Id; (ui,u)\<in>Id; (vi,v)\<in>Id; (si,s)\<in>bdfs_rel \<rbrakk> 
    \<Longrightarrow> se_back_edge_impl accpt ui vi si \<le>\<Down>bdfs_erel (se_back_edge accpt u v s)"
    unfolding se_back_edge_impl_def se_back_edge_def
    apply refine_rcg
    apply refine_dref_type  
    apply simp_all
    apply (simp_all add: bdfs_erel_def simple_state_rel_def)
    apply (cases si, cases s, (auto) [])
    apply (cases si, cases s, (auto simp: map_tl comp_def) [])
    apply (cases si, cases s, (auto simp: comp_def) [])
    done


  lemma NOOP_impl: "(si, s) \<in> bdfs_rel 
    \<Longrightarrow> RETURN (simple_state.more si) \<le> \<Down> bdfs_erel (NOOP s)"
    apply (simp add: pw_le_iff refine_pw_simps)
    apply (auto simp: simple_state_rel_def)
    done
    

  definition bdfs_params_impl 
    :: "('v, 'more) graph_rec_scheme \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('v,'v bdfs_state_impl,('v,unit)bdfs_state_impl_ext) gen_parameterization"
  where "bdfs_params_impl G accpt \<equiv> \<lparr>
    on_init = RETURN \<lparr>lasso_impl = None, red_impl = {}\<rparr>,
    on_new_root = \<lambda>v0 s. RETURN (simple_state.more s),
    on_discover = \<lambda>u v s. RETURN (simple_state.more s),
    on_finish = \<lambda>u s. 
      if accpt u then run_red_dfs_impl G u s else RETURN (simple_state.more s),
    on_back_edge = se_back_edge_impl accpt,
    on_cross_edge = \<lambda>u v s. RETURN (simple_state.more s),
    is_break = \<lambda>s. lasso_impl s \<noteq> None \<rparr>"

  lemmas bdfs_params_impl_simps[simp, DFS_code_unfold] = 
    gen_parameterization.simps[mk_record_simp, OF bdfs_params_impl_def]  


  interpretation impl: simple_impl_defs G "bdfs_params_impl G accpt" "blue_dfs_params TYPE('a) G accpt"
    for G accpt .

context BlueDFS begin

  sublocale impl: simple_impl G blue_dfs_params "bdfs_params_impl G accpt" bdfs_erel
    apply unfold_locales

    apply (simp_all 
      add: bdfs_params_impl_def run_red_dfs_impl se_back_edge_impl NOOP_impl)
    apply parametricity
    apply (clarsimp_all simp: pw_le_iff refine_pw_simps bdfs_erel_def simple_state_rel_def)
    apply (rename_tac si s x y, case_tac si, case_tac s)
    apply (auto simp add: bdfs_erel_def simple_state_rel_def) []
    done

  lemmas impl = impl.simple_tailrec_refine
end

definition "nested_dfs_impl G accpt \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> impl.tailrec_impl TYPE('a) G accpt;
  RETURN (lasso_impl s)
}"

lemma nested_dfs_impl[refine]: 
  assumes "(Gi,G)\<in>Id"
  assumes "(accpti,accpt)\<in>Id"
  shows "nested_dfs_impl Gi accpti \<le>\<Down>(\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r \<langle>Id\<rangle>list_rel\<rangle>option_rel) 
    (nested_dfs G accpt)"
  using assms
  unfolding nested_dfs_impl_def nested_dfs_def
  apply refine_rcg
  apply simp_all
  apply (rule intro_prgR[where R=bdfs_rel])
  defer
  apply (rename_tac si s)
  apply (case_tac si, case_tac s)
  apply (auto simp: bdfs_erel_def simple_state_rel_def) []
proof -
  assume "fb_graph G"
  then interpret fb_graph G .
  interpret BlueDFS G by unfold_locales

  from impl show "impl.tailrec_impl TYPE('b) G accpt \<le>\<Down>bdfs_rel (it_dfs TYPE('b) G accpt)" .
qed 

subsection \<open>Synthesis of Executable Code\<close>
(* Straightforward autoref implementation *)
record ('v,'si,'nsi)bdfs_state_impl' = "('si,'nsi)simple_state_impl" +
  lasso_impl' :: "('v list \<times> 'v list) option"
  red_impl' :: 'nsi

definition [to_relAPP]: "bdfs_state_erel' Vi \<equiv> {
  (\<lparr>lasso_impl' = li, red_impl'=ri\<rparr>,\<lparr>lasso_impl = l, red_impl = r\<rparr>) | li ri l r.
    (li,l)\<in>\<langle>\<langle>Vi\<rangle>list_rel \<times>\<^sub>r \<langle>Vi\<rangle>list_rel\<rangle>option_rel \<and> (ri,r)\<in>\<langle>Vi\<rangle>dflt_ahs_rel}"

consts 
  i_bdfs_state_ext :: "interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of bdfs_state_erel' i_bdfs_state_ext]

lemma [autoref_rules]:
  fixes ns_rel vis_rel Vi
  defines "R \<equiv> \<langle>ns_rel,vis_rel,\<langle>Vi\<rangle>bdfs_state_erel'\<rangle>ss_impl_rel"
  shows 
    "(bdfs_state_impl'_ext, bdfs_state_impl_ext) 
      \<in> \<langle>\<langle>Vi\<rangle>list_rel \<times>\<^sub>r \<langle>Vi\<rangle>list_rel\<rangle>option_rel \<rightarrow> \<langle>Vi\<rangle>dflt_ahs_rel \<rightarrow> unit_rel \<rightarrow> \<langle>Vi\<rangle>bdfs_state_erel'"
    "(lasso_impl', lasso_impl) \<in> R \<rightarrow> \<langle>\<langle>Vi\<rangle>list_rel \<times>\<^sub>r \<langle>Vi\<rangle>list_rel\<rangle>option_rel"
    "(red_impl', red_impl) \<in> R \<rightarrow> \<langle>Vi\<rangle>dflt_ahs_rel"
  unfolding bdfs_state_erel'_def ss_impl_rel_def R_def
  by auto

schematic_goal nested_dfs_code:
  assumes Vid: "V = (Id :: ('v::hashable \<times> 'v) set)"
  assumes [unfolded Vid, autoref_rules]:
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
    "(accpti,accpt) \<in> (V \<rightarrow> bool_rel)"
  notes [unfolded Vid, autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>dflt_ahs_rel"]
    TYRELI[where R="\<langle>V\<rangle>ras_rel"]
  shows "(nres_of ?c, nested_dfs_impl G accpt) 
    \<in> \<langle>\<langle>\<langle>V\<rangle>list_rel \<times>\<^sub>r \<langle>V\<rangle>list_rel\<rangle>option_rel\<rangle>nres_rel"
  unfolding nested_dfs_impl_def[abs_def] Vid 
    se_back_edge_impl_def run_red_dfs_impl_def mk_blue_witness_impl_def
    cyan_impl_def
    DFS_code_unfold
  (*apply (subst aux1)*)
  using [[autoref_trace_failed_id]]
  apply (autoref_monadic (trace))
  done

concrete_definition nested_dfs_code uses nested_dfs_code

export_code nested_dfs_code checking SML

subsection \<open>Conclusion\<close>
text \<open>
  We have implemented an efficiently executable nested DFS algorithm.
  The following theorem declares this implementation to the Autoref tool,
  such that it uses it to synthesize efficient code for @{const nested_dfs}.
  Note that you will need the lemma @{thm [source] nested_dfs_correct} to link
  @{const nested_dfs} to an abstract specification, which is usually done in 
  a previous refinement step.
\<close>
theorem nested_dfs_autoref[autoref_rules]:
  assumes "PREFER_id V"
  shows "(\<lambda> G accpt. nres_of (nested_dfs_code G accpt),nested_dfs) \<in>
    \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> (V \<rightarrow> bool_rel) \<rightarrow>
    \<langle>\<langle>\<langle>V\<rangle>list_rel \<times>\<^sub>r \<langle>V\<rangle>list_rel\<rangle>option_rel\<rangle>nres_rel"
proof -
  from assms have Vid: "V=Id" by simp
  note nested_dfs_code.refine[OF Vid,param_fo, THEN nres_relD]
  also note nested_dfs_impl
  finally show ?thesis by (fastforce intro: nres_relI)
qed


end

