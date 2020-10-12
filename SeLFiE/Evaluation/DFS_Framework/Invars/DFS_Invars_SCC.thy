section \<open>Invariants for SCCs\<close>
theory DFS_Invars_SCC
imports 
  DFS_Invars_Basic
begin

definition scc_root' :: "('v \<times> 'v) set \<Rightarrow> ('v,'es) state_scheme  \<Rightarrow> 'v \<Rightarrow> 'v set \<Rightarrow> bool"
    \<comment> \<open>@{term v} is a root of its scc 
        iff all the discovered parts of the scc can be reached by tree edges from @{term v}\<close>
  where
  "scc_root' E s v scc \<longleftrightarrow> is_scc E scc 
                       \<and> v \<in> scc
                       \<and> v \<in> dom (discovered s) 
                       \<and> scc \<inter> dom (discovered s) \<subseteq> (tree_edges s)\<^sup>* `` {v}"

context param_DFS_defs begin
  abbreviation "scc_root \<equiv> scc_root' E"
  lemmas scc_root_def = scc_root'_def

  lemma scc_rootI:
    assumes "is_scc E scc"
    and "v \<in> dom (discovered s)"
    and "v \<in> scc"
    and "scc \<inter> dom (discovered s) \<subseteq> (tree_edges s)\<^sup>* `` {v}"
    shows "scc_root s v scc"
    using assms by (simp add: scc_root_def)

  definition "scc_roots s = {v. \<exists>scc. scc_root s v scc}"
end

context DFS_invar begin
  lemma scc_root_is_discovered:
    "scc_root s v scc \<Longrightarrow> v \<in> dom (discovered s)"
    by (simp add: scc_root_def)

  lemma scc_root_scc_tree_rtrancl:
    assumes "scc_root s v scc"
    and "x \<in> scc" "x \<in> dom (discovered s)"
    shows "(v,x) \<in> (tree_edges s)\<^sup>*"
    using assms
    by (auto simp add: scc_root_def)

  lemma scc_root_scc_reach:
    assumes "scc_root s r scc"
    and "v \<in> scc"
    shows "(r,v) \<in> E\<^sup>*"
  proof -
    from assms have "is_scc E scc" "r \<in> scc" by (simp_all add: scc_root_def)
    with is_scc_connected assms show ?thesis by metis
  qed

  lemma scc_reach_scc_root:
    assumes "scc_root s r scc"
    and "v \<in> scc"
    shows "(v,r) \<in> E\<^sup>*"
  proof -
    from assms have "is_scc E scc" "r \<in> scc" by (simp_all add: scc_root_def)
    with is_scc_connected assms show ?thesis by metis
  qed

  lemma scc_root_scc_tree_trancl:
    assumes "scc_root s v scc"
    and "x \<in> scc" "x \<in> dom (discovered s)" "x \<noteq> v"
    shows "(v,x) \<in> (tree_edges s)\<^sup>+"
    using assms scc_root_scc_tree_rtrancl
    by (auto simp add: rtrancl_eq_or_trancl)

  lemma scc_root_unique_scc:
    "scc_root s v scc \<Longrightarrow> scc_root s v scc' \<Longrightarrow> scc = scc'"
    unfolding scc_root_def
    by (metis is_scc_unique)

  lemma scc_root_unique_root:
    assumes scc1: "scc_root s v scc"
    and scc2: "scc_root s v' scc"
    shows "v = v'"
  proof (rule ccontr)
    assume "v \<noteq> v'"
    from scc1 have "v \<in> scc" "v \<in> dom (discovered s)" 
      by (simp_all add: scc_root_def)
    with scc_root_scc_tree_trancl[OF scc2] \<open>v \<noteq> v'\<close> have "(v',v) \<in> (tree_edges s)\<^sup>+" 
      by simp
    also from scc2 have "v' \<in> scc" "v' \<in> dom (discovered s)" 
      by (simp_all add: scc_root_def)
    with scc_root_scc_tree_trancl[OF scc1] \<open>v\<noteq>v'\<close> have "(v,v') \<in> (tree_edges s)\<^sup>+" 
      by simp
    finally show False using no_loop_in_tree by contradiction
  qed

  lemma scc_root_unique_is_scc:
    assumes "scc_root s v scc"
    shows "scc_root s v (scc_of E v)"
  proof -
    from assms have "v \<in> scc" "is_scc E scc" by (simp_all add: scc_root_def)
    moreover have "v \<in> scc_of E v" "is_scc E (scc_of E v)" by simp_all
    ultimately have "scc = scc_of E v" using is_scc_unique by metis
    thus ?thesis using assms by simp
  qed

  lemma scc_root_finished_impl_scc_finished:
    assumes "v \<in> dom (finished s)"
    and "scc_root s v scc"
    shows "scc \<subseteq> dom (finished s)"
  proof
    fix x
    assume "x \<in> scc"

    let ?E = "Restr E scc"

    from assms have "is_scc E scc" "v \<in> scc" by (simp_all add: scc_root_def)
    hence "(v,x) \<in> (Restr E scc)\<^sup>*" using \<open>x \<in> scc\<close>
      by (simp add: is_scc_connected')
    with rtrancl_is_path obtain p where "path ?E v p x" by metis
    thus "x \<in> dom (finished s)" 
    proof (induction p arbitrary: x rule: rev_induct)
      case Nil hence "v = x" by simp
      with assms show ?case by simp
    next
      case (snoc y ys) hence "path ?E v ys y" "(y,x) \<in> ?E" 
        by (simp_all add: path_append_conv)
      with snoc.IH have "y \<in> dom (finished s)" by simp
      moreover from \<open>(y,x) \<in> ?E\<close> have "(y,x) \<in> E" "x \<in> scc" by auto
      ultimately have "x \<in> dom (discovered s)"
        using finished_imp_succ_discovered
        by blast
      with \<open>x \<in> scc\<close> show ?case
        using assms scc_root_scc_tree_trancl tree_path_impl_parenthesis
        by blast
    qed
  qed

context begin interpretation timing_syntax .
  lemma scc_root_disc_le:
    assumes "scc_root s v scc"
    and "x \<in> scc" "x \<in> dom (discovered s)"
    shows "\<delta> s v \<le> \<delta> s x"
  proof (cases "x = v")
    case False with assms scc_root_scc_tree_trancl tree_path_disc have 
      "\<delta> s v < \<delta> s x" 
      by blast
    thus ?thesis by simp
  qed simp

  lemma scc_root_fin_ge:
    assumes "scc_root s v scc"
    and "v \<in> dom (finished s)"
    and "x \<in> scc"
    shows "\<phi> s v \<ge> \<phi> s x"
  proof (cases "x = v")
    case False
    from assms scc_root_finished_impl_scc_finished have 
      "x \<in> dom (finished s)" by auto
    hence "x \<in> dom (discovered s)" using finished_discovered by auto
    with assms False have "(v,x) \<in> (tree_edges s)\<^sup>+" 
      using scc_root_scc_tree_trancl by simp
    with tree_path_impl_parenthesis assms False show ?thesis by force
  qed simp

  lemma scc_root_is_Min_disc:
    assumes "scc_root s v scc"
    shows "Min (\<delta> s ` (scc \<inter> dom (discovered s))) = \<delta> s v" (is "Min ?S = _")
  proof (rule Min_eqI)
    from discovered_finite show "finite ?S" by auto
    from scc_root_disc_le[OF assms] show "\<And>y. y \<in> ?S \<Longrightarrow> \<delta> s v \<le> y" by force
    
    from assms have "v \<in> scc" "v \<in> dom (discovered s)"
      by (simp_all add: scc_root_def)
    thus "\<delta> s v \<in> ?S" by auto
  qed

  lemma Min_disc_is_scc_root:
    assumes "v \<in> scc" "v \<in> dom (discovered s)"
    and "is_scc E scc"
    and min: "\<delta> s v = Min (\<delta> s ` (scc \<inter> dom (discovered s)))"
    shows "scc_root s v scc"
  proof -
    {
      fix y
      assume A: "y \<in> scc" "y \<in> dom (discovered s)" "y \<noteq> v"
      with min have "\<delta> s v \<le> \<delta> s y" by auto
      with assms disc_unequal A have "\<delta> s v < \<delta> s y" by fastforce
    } note scc_disc = this

    {
      fix x
      assume A: "x \<in> scc \<inter> dom (discovered s)"

      have "x \<in> (tree_edges s)\<^sup>* `` {v}"
      proof (cases "v = x")
        case False with A scc_disc have \<delta>: "\<delta> s v < \<delta> s x" by simp

        have "(v,x) \<in> (tree_edges s)\<^sup>+"
        proof (cases "v \<in> dom (finished s)")
          case False with stack_set_def assms have 
            v_stack: "v \<in> set (stack s)" by auto
          show ?thesis
          proof (cases "x \<in> dom (finished s)")
            case True 
            with parenthesis_impl_tree_path_not_finished[of v x] assms \<delta> False
            show ?thesis by auto
          next
            case False with A stack_set_def have "x \<in> set (stack s)" by auto
            with v_stack \<delta> show ?thesis
              using on_stack_is_tree_path
              by simp
          qed
        next
          case True note v_fin = this

          let ?E = "Restr E scc"

          {
            fix y
            assume "(v, y) \<in> ?E" and "v \<noteq> y"
            hence *: "y \<in> succ v" "y \<in> scc" by auto
            with finished_imp_succ_discovered v_fin have 
              "y \<in> dom (discovered s)" by simp
            with scc_disc \<open>v \<noteq> y\<close> * have "\<delta> s v < \<delta> s y" by simp
            with * finished_succ_impl_path_in_tree v_fin have "(v,y) \<in> (tree_edges s)\<^sup>+" by simp
          } note trancl_base = this

          from A have "x \<in> scc" by simp
          with assms have "(v,x) \<in> ?E\<^sup>*"
            by (simp add: is_scc_connected')
          with \<open>v\<noteq>x\<close> have "(v,x) \<in> ?E\<^sup>+" by (metis rtrancl_eq_or_trancl)
          thus ?thesis using \<open>v\<noteq>x\<close>
          proof (induction)
            case (base y) with trancl_base show ?case .
          next
            case (step y z)
            show ?case
            proof (cases "v = y")
              case True with step trancl_base show ?thesis by simp
            next
              case False with step have "(v,y) \<in> (tree_edges s)\<^sup>+" by simp
              with tree_path_impl_parenthesis[OF _ v_fin] have 
                y_fin: "y \<in> dom (finished s)" 
                and y_t: "\<delta> s v < \<delta> s y" "\<phi> s y < \<phi> s v" 
                by auto
              with finished_discovered have y_disc: "y \<in> dom (discovered s)" 
                by auto

              from step have *: "z \<in> succ y" "z \<in> scc" by auto
              with finished_imp_succ_discovered y_fin have 
                z_disc: "z \<in> dom (discovered s)" by simp
              with * \<open>v\<noteq>z\<close> have \<delta>z: "\<delta> s v < \<delta> s z" by (simp add: scc_disc)
              

              from * edges_covered finished_no_pending[OF \<open>y \<in> dom (finished s)\<close>] 
                   y_disc have "(y,z) \<in> edges s" by auto
              thus ?thesis
              proof safe
                assume "(y,z) \<in> tree_edges s" with \<open>(v,y) \<in> (tree_edges s)\<^sup>+\<close> show ?thesis ..
              next
                assume CE: "(y,z) \<in> cross_edges s" 
                with cross_edges_finished_decr y_fin y_t have "\<phi> s z < \<phi> s v" 
                  by force
                moreover note \<delta>z
                moreover from CE cross_edges_target_finished have 
                  "z \<in> dom (finished s)" by simp
                ultimately show ?thesis 
                  using parenthesis_impl_tree_path[OF v_fin] by metis
              next
                assume BE: "(y,z) \<in> back_edges s" 
                with back_edge_disc_lt_fin y_fin y_t have 
                  "\<delta> s z < \<phi> s v" by force
                moreover note \<delta>z
                moreover note z_disc
                ultimately have "z \<in> dom (finished s)" "\<phi> s z < \<phi> s v" 
                  using parenthesis_contained[OF v_fin] by simp_all
                with \<delta>z show ?thesis 
                  using parenthesis_impl_tree_path[OF v_fin] by metis
              qed
            qed
          qed
        qed
        thus ?thesis by auto
      qed simp
    }
    hence "scc \<inter> dom (discovered s) \<subseteq> (tree_edges s)\<^sup>* `` {v}" by blast

    with assms show ?thesis by (auto intro: scc_rootI)
  qed

  lemma scc_root_iff_Min_disc:
    assumes "is_scc E scc" "r \<in> scc" "r \<in> dom (discovered s)"
    shows "scc_root s r scc \<longleftrightarrow> Min (\<delta> s ` (scc \<inter> dom (discovered s))) = \<delta> s r" (is "?L \<longleftrightarrow> ?R")
  proof
    assume "?L" with scc_root_is_Min_disc show "?R" .
  next
    assume "?R" with Min_disc_is_scc_root assms show "?L" by simp
  qed   

  lemma scc_root_exists:
    assumes "is_scc E scc"
    and scc: "scc \<inter> dom (discovered s) \<noteq> {}"
    shows "\<exists>r. scc_root s r scc"
  proof -
    let ?S = "scc \<inter> dom (discovered s)"

    from discovered_finite have "finite (\<delta> s`?S)" by auto
    moreover from scc have "\<delta> s ` ?S \<noteq> {}" by auto
    moreover have "\<And>(x::nat) f A. x \<notin> f ` A \<or> (\<exists>y. x = f y \<and> y \<in> A)" by blast 
      \<comment> \<open>autogenerated by sledgehammer\<close>
    ultimately have "\<exists>x \<in> ?S. \<delta> s x = Min (\<delta> s ` ?S)" by (metis Min_in)
    with Min_disc_is_scc_root \<open>is_scc E scc\<close> show ?thesis by auto
  qed

  lemma scc_root_of_node_exists:
    assumes "v \<in> dom (discovered s)"
    shows "\<exists>r. scc_root s r (scc_of E v)"
  proof -
    have "is_scc E (scc_of E v)" by simp
    moreover have "v \<in> scc_of E v" by simp
    with assms have "scc_of E v \<inter> dom (discovered s) \<noteq> {}" by blast
    ultimately show ?thesis using scc_root_exists by metis
  qed

  lemma scc_root_transfer':
    assumes "discovered s = discovered s'" "tree_edges s = tree_edges s'"
    shows "scc_root s r scc \<longleftrightarrow> scc_root s' r scc"
    unfolding scc_root_def
    by (simp add: assms)

  lemma scc_root_transfer:
    assumes inv: "DFS_invar G param s'"
    assumes r_d: "r \<in> dom (discovered s)"
    assumes d: "dom (discovered s) \<subseteq> dom (discovered s')"
               "\<forall>x\<in>dom (discovered s). \<delta> s x = \<delta> s' x"
               "\<forall>x\<in>dom (discovered s') - dom (discovered s). \<delta> s' x \<ge> counter s"
    and t: "tree_edges s \<subseteq> tree_edges s'"
    shows "scc_root s r scc \<longleftrightarrow> scc_root s' r scc"
  proof -
    interpret s': DFS_invar where s=s' by fact

    let ?sd = "scc \<inter> dom (discovered s)"
    let ?sd' = "scc \<inter> dom (discovered s')"
    let ?sdd = "scc \<inter> (dom (discovered s') - dom (discovered s))"

    {
      assume r_s: "r \<in> scc" "is_scc E scc"
      with r_d have ne: "\<delta> s'`?sd \<noteq> {}" by blast
      from discovered_finite have fin: "finite (\<delta> s' ` ?sd)" by simp
    
      from timing_less_counter d have "\<And>x. x\<in>\<delta> s' ` ?sd \<Longrightarrow> x < counter s" by auto
      hence Min: "Min (\<delta> s' ` ?sd) < counter s"
        using Min_less_iff[OF fin] ne by blast

      from d have "Min (\<delta> s ` ?sd) = Min (\<delta> s' ` ?sd)" by (auto simp: image_def)
      also from d have "?sd' = ?sd \<union> ?sdd" by auto
      hence *: "\<delta> s' ` ?sd' = \<delta> s' ` ?sd \<union> \<delta> s' ` ?sdd" by auto
      hence "Min (\<delta> s' ` ?sd) = Min (\<delta> s' ` ?sd')"
      proof (cases "?sdd = {}")
        case False
        from d have "\<And>x. x \<in> \<delta> s' ` ?sdd \<Longrightarrow> x \<ge> counter s" by auto
        moreover from False have ne': "\<delta> s' ` ?sdd \<noteq> {}" by blast
        moreover from s'.discovered_finite have fin': "finite (\<delta> s' ` ?sdd)" by blast
        ultimately have "Min (\<delta> s' ` ?sdd) \<ge> counter s"
          using Min_ge_iff by metis
        with Min Min_Un[OF fin ne fin' ne'] * show ?thesis by simp
      qed simp
      finally have "Min (\<delta> s ` ?sd) = Min (\<delta> s' ` ?sd')" .
    } note aux = this

    show ?thesis
    proof
      assume r: "scc_root s r scc"
      from r_d d have "\<delta> s' r = \<delta> s r" by simp
      also from r scc_root_is_Min_disc have "\<delta> s r = Min (\<delta> s ` ?sd)" by simp
      also from r aux have "Min (\<delta> s ` ?sd) = Min (\<delta> s' ` ?sd')" by (simp add: scc_root_def)
      finally show "scc_root s' r scc"
        using r_d d r[unfolded scc_root_def]
        by (blast intro!: s'.Min_disc_is_scc_root)
    next
      assume r': "scc_root s' r scc"
      from r_d d have "\<delta> s r = \<delta> s' r" by simp
      also from r' s'.scc_root_is_Min_disc have "\<delta> s' r = Min (\<delta> s' ` ?sd')" by simp
      also from r' aux have "Min (\<delta> s' ` ?sd') = Min (\<delta> s ` ?sd)" by (simp add: scc_root_def)
      finally show "scc_root s r scc"
        using r_d d r'[unfolded scc_root_def]
        by (blast intro!: Min_disc_is_scc_root)
    qed
  qed

end end

end
