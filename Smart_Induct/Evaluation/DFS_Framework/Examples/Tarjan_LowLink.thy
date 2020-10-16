section \<open>Invariants for Tarjan's Algorithm\<close>
theory Tarjan_LowLink
imports
  "../DFS_Framework"
  "../Invars/DFS_Invars_SCC"
begin

context param_DFS_defs begin

  definition
    "lowlink_path s v p w \<equiv> path E v p w \<and> p \<noteq> []
                          \<and> (last p, w) \<in> cross_edges s \<union> back_edges s
                          \<and> (length p > 1 \<longrightarrow>
                                p!1 \<in> dom (finished s)
                              \<and> (\<forall>k < length p - 1. (p!k, p!Suc k) \<in> tree_edges s))"

  definition
    "lowlink_set s v \<equiv> {w \<in> dom (discovered s).
                         v = w 
                        \<or> (v,w) \<in> E\<^sup>+ \<and> (w,v) \<in> E\<^sup>+ 
                          \<and> (\<exists>p. lowlink_path s v p w)}"

context begin interpretation timing_syntax .
  abbreviation LowLink where
    "LowLink s v \<equiv> Min (\<delta> s ` lowlink_set s v)"
end

end

context DFS_invar begin

  lemma lowlink_setI:
    assumes "lowlink_path s v p w"
    and "w \<in> dom (discovered s)"
    and "(v,w) \<in> E\<^sup>*" "(w,v) \<in> E\<^sup>*"
    shows "w \<in> lowlink_set s v"
  proof (cases "v = w")
    case True thus ?thesis by (simp add: lowlink_set_def assms)
  next
    case False with assms have "(v,w) \<in> E\<^sup>+" "(w,v) \<in> E\<^sup>+" by (metis rtrancl_eq_or_trancl)+
    with assms show ?thesis by (auto simp add: lowlink_set_def)
  qed

  lemma lowlink_set_discovered:
    "lowlink_set s v \<subseteq> dom (discovered s)"
    unfolding lowlink_set_def
    by blast

  lemma lowlink_set_finite[simp, intro!]:
    "finite (lowlink_set s v)"
    using lowlink_set_discovered discovered_finite
    by (metis finite_subset)

  lemma lowlink_set_not_empty:
    assumes "v \<in> dom (discovered s)"
    shows "lowlink_set s v \<noteq> {}"
    unfolding lowlink_set_def
    using assms by auto

  lemma lowlink_path_single:
    assumes "(v,w) \<in> cross_edges s \<union> back_edges s"
    shows "lowlink_path s v [v] w"
    unfolding lowlink_path_def
    using assms cross_edges_ssE back_edges_ssE
    by (auto simp add: path_simps)

  lemma lowlink_path_Cons:
    assumes "lowlink_path s v (x#xs) w"
    and "xs \<noteq> []"
    shows "\<exists>u. lowlink_path s u xs w"
  proof -
    from assms have path: "path E v (x#xs) w" 
      and cb: "(last xs, w) \<in> cross_edges s \<union> back_edges s"
      and f: "(x#xs)!1 \<in> dom (finished s)"
      and t: "(\<forall>k < length xs. ((x#xs)!k, (x#xs)!Suc k) \<in> tree_edges s)"
      unfolding lowlink_path_def
      by auto

    from path obtain u where "path E u xs w" by (auto simp add: path_simps)
    moreover note cb \<open>xs \<noteq> []\<close>
    moreover { fix k define k' where "k' = Suc k"
      assume "k < length xs - 1"
      with k'_def have "k' < length xs" by simp
      with t have "((x#xs)!k', (x#xs)!Suc k') \<in> tree_edges s" by simp
      hence "(xs!k,xs!Suc k) \<in> tree_edges s" by (simp add: k'_def nth_Cons')
    } note t' = this
    moreover {
      assume *: "length xs > 1"
      from f have "xs!0 \<in> dom (finished s)" by auto
      moreover from t'[of 0] * have "(xs!0,xs!1) \<in> tree_edges s" by simp
      ultimately have "xs!1 \<in> dom (finished s)" using tree_edge_impl_parenthesis by metis
    }

    ultimately have "lowlink_path s u xs w" by (auto simp add: lowlink_path_def)
    thus ?thesis ..
  qed

  lemma lowlink_path_in_tree:
    assumes p: "lowlink_path s v p w"
    and j: "j < length p"
    and k: "k < j"
    shows "(p!k, p!j) \<in> (tree_edges s)\<^sup>+"
  proof -
    from p have "p \<noteq> []" by (auto simp add: lowlink_path_def)
    thus ?thesis using p j k
    proof (induction arbitrary: v j k rule: list_nonempty_induct)
      case single thus ?case by auto
    next
      case (cons x xs)
      define j' where "j' = j - 1"
      with cons have j'_le: "j' < length xs" and "k \<le> j'"  and j: "j = Suc j'" by auto

      from cons lowlink_path_Cons obtain u where p: "lowlink_path s u xs w" by blast

      show ?case
      proof (cases "k=0")
        case True
        from cons have "\<And>k. k < length (x#xs) - 1 \<Longrightarrow> ((x#xs)!k,(x#xs)!Suc k) \<in> tree_edges s" 
          unfolding lowlink_path_def
          by auto
        moreover from True cons have "k < length (x#xs) - 1" by auto
        ultimately have *: "((x#xs)!k,(x#xs)!Suc k) \<in> tree_edges s" by metis

        show ?thesis
        proof (cases "j' = 0")
          case True with * j \<open>k=0\<close> show ?thesis by simp
        next
          case False with True have "j' > k" by simp
          with cons.IH[OF p j'_le] have "(xs!k, xs!j') \<in> (tree_edges s)\<^sup>+" .
          with j have "((x#xs)!Suc k, (x#xs)!j) \<in> (tree_edges s)\<^sup>+" by simp
          with * show ?thesis by (metis trancl_into_trancl2)
        qed
      next
        case False 
        define k' where "k' = k - 1"
        with False \<open>k \<le> j'\<close> have "k' < j'" and k: "k = Suc k'" by simp_all
        with cons.IH[OF p j'_le] have "(xs!k', xs!j') \<in> (tree_edges s)\<^sup>+" by metis
        hence "((x#xs)!Suc k', (x#xs)!Suc j') \<in> (tree_edges s)\<^sup>+" by simp
        with k j show ?thesis by simp
      qed
    qed
  qed

  lemma lowlink_path_finished:
    assumes p: "lowlink_path s v p w"
    and j: "j < length p" "j > 0"
    shows "p!j \<in> dom (finished s)"
  proof -
    from j have "length p > 1" by simp
    with p have f: "p!1 \<in> dom (finished s)" by (simp add: lowlink_path_def)
    thus ?thesis
    proof (cases "j=1")
      case False with j have "j > 1" by simp
      with assms lowlink_path_in_tree[where k=1] have "(p!1,p!j) \<in> (tree_edges s)\<^sup>+" by simp
      with f tree_path_impl_parenthesis show ?thesis by simp
    qed simp
  qed

  lemma lowlink_path_tree_prepend:
    assumes p: "lowlink_path s v p w"
    and tree_edges: "(u,v) \<in> (tree_edges s)\<^sup>+"
    and fin: "u \<in> dom (finished s) \<or> (stack s \<noteq> [] \<and> u = hd (stack s))"
    shows "\<exists>p. lowlink_path s u p w"
  proof -
    note lowlink_path_def[simp]

    from tree_edges trancl_is_path obtain tp where 
      tp: "path (tree_edges s) u tp v" "tp \<noteq> []"
      by metis

    from tree_path_impl_parenthesis assms hd_stack_tree_path_finished have 
      v_fin: "v \<in> dom (finished s)" by blast

    from p have "p!0 = hd p" by (simp add: hd_conv_nth)
    with p have p_0: "p!0 = v" by (auto simp add: path_hd)

    let ?p = "tp @ p"

    {
      from tp path_mono[OF tree_edges_ssE] have "path E u tp v" by simp
      also from p have "path E v p w" by simp
      finally have "path E u ?p w" .
    }

    moreover from p have "?p \<noteq> []" by simp

    moreover 
    from p have "(last ?p, w) \<in> cross_edges s \<union> back_edges s" by simp

    moreover {
      assume "length ?p > 1"

      have "?p ! 1 \<in> dom (finished s)"
      proof (cases "length tp > 1")
        case True hence tp1: "?p ! 1 = tp ! 1" by (simp add: nth_append)
        from tp True have "(tp ! 0, tp ! 1) \<in> (tree_edges s)\<^sup>+"
          by (auto simp add: path_nth_conv nth_append elim: allE[where x=0])
        also from True have "tp ! 0 = hd tp" by (simp add: hd_conv_nth)
        also from tp have "hd tp = u" by (simp add: path_hd)
        finally have "tp ! 1 \<in> dom (finished s)"
          using tree_path_impl_parenthesis fin hd_stack_tree_path_finished by blast
        thus ?thesis by (subst tp1)
      next
        case False with tp have "length tp = 1" by (cases tp) auto
        with p_0 have "?p ! 1 = v" by (simp add: nth_append)
        thus ?thesis by (simp add: v_fin)
      qed

      also have "\<forall>k < length ?p - 1. (?p!k, ?p!Suc k) \<in> tree_edges s"
      proof (safe)
        fix k
        assume A: "k < length ?p - 1"
        show "(?p!k, ?p!Suc k) \<in> tree_edges s"
        proof (cases "k < length tp")
          case True hence k: "?p ! k = tp ! k" by (simp add: nth_append)
          show ?thesis
          proof (cases "Suc k < length tp")
            case True hence "?p ! Suc k = tp ! Suc k" by (simp add: nth_append)
            moreover from True tp have "(tp ! k, tp ! Suc k) \<in> tree_edges s"
              by (auto simp add: path_nth_conv nth_append 
                       elim: allE[where x=k])
            ultimately show ?thesis using k by simp
          next
            case False with True have *: "Suc k = length tp" by simp
            with tp True have "(tp ! k, v) \<in> tree_edges s"
              by (auto simp add: path_nth_conv nth_append 
                       elim: allE[where x=k])
            also from * p_0 have "v = ?p ! Suc k" by (simp add: nth_append)
            finally show ?thesis by (simp add: k)
          qed
        next
          case False hence *: "Suc k - length tp = Suc (k - length tp)" by simp
          define k' where "k' = k - length tp"
          with False * have k': "?p ! k = p ! k'" "?p ! Suc k = p ! Suc k'" 
            by (simp_all add: nth_append)
          from k'_def False A have "k' < length p - 1" by simp 
          with p have "(p!k', p!Suc k') \<in> tree_edges s" by simp (* p is lowlink_path *)
          with k' show ?thesis by simp
        qed
      qed

      also (conjI) note calculation
    }

    ultimately have "lowlink_path s u ?p w" by simp
    thus ?thesis ..
  qed
    

  lemma lowlink_path_complex:
    assumes "(u,v) \<in> (tree_edges s)\<^sup>+"
    and "u \<in> dom (finished s) \<or> (stack s \<noteq> [] \<and> u = hd (stack s))"
    and "(v,w) \<in> cross_edges s \<union> back_edges s"
    shows "\<exists>p. lowlink_path s u p w" 
  proof -
    from assms lowlink_path_single have "lowlink_path s v [v] w" by simp
    with assms lowlink_path_tree_prepend show ?thesis by simp
  qed

  lemma no_path_imp_no_lowlink_path:
    assumes "edges s `` {v} = {}"
    shows "\<not>lowlink_path s v p w"
  proof
    assume p: "lowlink_path s v p w"
    hence [simp]: "p\<noteq>[]" by (simp add: lowlink_path_def)
    
    from p have "hd p = v" by (auto simp add: lowlink_path_def path_hd)
    with hd_conv_nth[OF \<open>p\<noteq>[]\<close>] have v: "p!0 = v" by simp

    show False
    proof (cases "length p > 1")
      case True with p have "(p!0,p!1) \<in> tree_edges s" by (simp add: lowlink_path_def)
      with v assms show False by auto
    next
      case False with \<open>p\<noteq>[]\<close> have "length p = 1" by (cases p) auto
      hence "last p = v" by (simp add: last_conv_nth v)
      with p have "(v,w) \<in> edges s" by (simp add: lowlink_path_def)
      with assms show False by auto
    qed
  qed

context begin interpretation timing_syntax .

  lemma LowLink_le_disc:
    assumes "v \<in> dom (discovered s)"
    shows "LowLink s v \<le> \<delta> s v"
    using assms
    unfolding lowlink_set_def
    by clarsimp
  
  lemma LowLink_lessE:
    assumes "LowLink s v < x"
    and "v \<in> dom (discovered s)"
    obtains w where "\<delta> s w < x" "w \<in> lowlink_set s v"
  proof -
    let ?L = "\<delta> s ` lowlink_set s v"

    note assms
    moreover from lowlink_set_finite have "finite ?L" by auto
    moreover from lowlink_set_not_empty assms have "?L \<noteq> {}" by auto
    ultimately show ?thesis using that by (auto simp: Min_less_iff)
  qed

  lemma LowLink_lessI:
    assumes "y \<in> lowlink_set s v"
    and "\<delta> s y < \<delta> s v"
    shows "LowLink s v < \<delta> s v"
  proof -
    let ?L = "\<delta> s ` lowlink_set s v"

    from assms have "\<delta> s y \<in> ?L" by simp
    moreover hence "?L \<noteq> {}" by auto
    moreover from lowlink_set_finite have "finite ?L" by auto
    ultimately show ?thesis 
      by (metis Min_less_iff assms(2))
  qed

  lemma LowLink_eqI:
    assumes "DFS_invar G param s'"
    assumes sub_m: "discovered s \<subseteq>\<^sub>m discovered s'"
    assumes sub: "lowlink_set s w \<subseteq> lowlink_set s' w"
    and rev_sub: "lowlink_set s' w \<subseteq> lowlink_set s w \<union> X"
    and w_disc: "w \<in> dom (discovered s)"
    and X: "\<And>x. \<lbrakk>x \<in> X; x \<in> lowlink_set s' w\<rbrakk> \<Longrightarrow> \<delta> s' x \<ge> LowLink s w"
    shows "LowLink s w = LowLink s' w"
  proof (rule ccontr)
    interpret s': DFS_invar where s=s' by fact
    assume A: "LowLink s w \<noteq> LowLink s' w"

    from lowlink_set_discovered sub sub_m w_disc have 
           sub': "\<delta> s ` lowlink_set s w \<subseteq> \<delta> s' ` lowlink_set s' w"
      and  w_disc': "w \<in> dom (discovered s')"
      and  eq: "\<And>ll. ll \<in> lowlink_set s w \<Longrightarrow> \<delta> s' ll = \<delta> s ll"
      by (force simp: map_le_def)+

    from lowlink_set_not_empty[OF w_disc] A Min_antimono[OF sub'] s'.lowlink_set_finite have 
      "LowLink s' w < LowLink s w" by fastforce
    then obtain ll where ll: "ll \<in> lowlink_set s' w" and ll_le: "\<delta> s' ll < LowLink s w"
      by (metis s'.LowLink_lessE w_disc')
    with rev_sub have "ll \<in> lowlink_set s w \<or> ll \<in> X" by auto
    hence "LowLink s w \<le> \<delta> s' ll"
    proof
      assume "ll \<in> lowlink_set s w" with lowlink_set_finite eq show ?thesis by force
    next
      assume "ll \<in> X" with ll show ?thesis by (metis X)
    qed
    with ll_le show False by simp
  qed
    
  lemma LowLink_eq_disc_iff_scc_root:
    assumes "v \<in> dom (finished s) \<or> (stack s \<noteq> [] \<and> v = hd (stack s) \<and> pending s `` {v} = {})"
    shows "LowLink s v = \<delta> s v \<longleftrightarrow> scc_root s v (scc_of E v)"
  proof 
    let ?scc = "scc_of E v"
    assume scc: "scc_root s v ?scc"
    show "LowLink s v = \<delta> s v"
    proof (rule ccontr)
      assume A: "LowLink s v \<noteq> \<delta> s v"
      
      from assms finished_discovered stack_discovered hd_in_set have disc: "v \<in> dom (discovered s)" by blast
      with assms LowLink_le_disc A have "LowLink s v < \<delta> s v" by force
      with disc obtain w where 
        w: "\<delta> s w < \<delta> s v" "w \<in> lowlink_set s v" 
        by (metis LowLink_lessE)
      with lowlink_set_discovered have wdisc: "w \<in> dom (discovered s)" by auto

      from w have "(v,w) \<in> E\<^sup>*" "(w,v) \<in> E\<^sup>*" by (auto simp add: lowlink_set_def)
      moreover have "is_scc E ?scc" "v \<in> ?scc" by simp_all
      ultimately have "w \<in> ?scc" by (metis is_scc_closed)
      with wdisc scc_root_disc_le[OF scc] have "\<delta> s v \<le> \<delta> s w" by simp
      with w show False by auto
    qed
  next
    assume LL: "LowLink s v = \<delta> s v"
    
    from assms finished_discovered stack_discovered hd_in_set have 
      v_disc: "v \<in> dom (discovered s)" by blast
    
    from assms finished_no_pending have
      v_no_p: "pending s `` {v} = {}" by blast
    
    let ?scc = "scc_of E v"
    have is_scc: "is_scc E ?scc" by simp
    
    {
      fix r
      assume "r \<noteq> v"
      and "r \<in> ?scc" "r \<in> dom (discovered s)"

      have "v \<in> ?scc" by simp
      with \<open>r \<in> ?scc\<close> is_scc have "(v,r) \<in> (Restr E ?scc)\<^sup>*"
        by (simp add: is_scc_connected')
      
      hence "(v,r) \<in> (tree_edges s)\<^sup>+" using \<open>r\<noteq>v\<close>
      proof (induction rule: rtrancl_induct)
        case (step y z) hence "(v,z) \<in> (Restr E ?scc)\<^sup>*"
          by (metis rtrancl_into_rtrancl)
        hence "(v,z) \<in> E\<^sup>*" by (metis Restr_rtrancl_mono)

        from step have "(z,v) \<in> E\<^sup>*" by (simp add: is_scc_connected[OF is_scc])

        {
          assume z_disc: "z \<in> dom (discovered s)"
          and "\<exists>p. lowlink_path s v p z" 
          with \<open>(z,v)\<in>E\<^sup>*\<close> \<open>(v,z)\<in>E\<^sup>*\<close> have ll: "z \<in> lowlink_set s v"
            by (metis lowlink_setI)
          have "\<delta> s v < \<delta> s z"
          proof (rule ccontr)
            presume "\<delta> s v \<ge> \<delta> s z" with \<open>z\<noteq>v\<close> v_disc z_disc disc_unequal have "\<delta> s z < \<delta> s v" by fastforce
            with ll have "LowLink s v < \<delta> s v" by (metis LowLink_lessI)
            with LL show False by simp
          qed simp
        } note \<delta>z = this

        show ?case
        proof (cases "y=v")
          case True note [simp] = this
          with step v_no_p v_disc no_pending_imp_succ_discovered have
            z_disc: "z \<in> dom (discovered s)" by blast
          
          from step edges_covered v_no_p v_disc have "(v,z) \<in> edges s" by auto
          thus ?thesis
          proof (rule edgesE_CB)
            assume "(v,z) \<in> tree_edges s" thus ?thesis ..
          next
            assume CB: "(v,z) \<in> cross_edges s \<union> back_edges s"
            hence "lowlink_path s v [v] z" 
              by (simp add: lowlink_path_single)
            with \<delta>z[OF z_disc] no_pending_succ_impl_path_in_tree v_disc v_no_p step show ?thesis
              by auto
          qed
        next
          case False with step.IH have T: "(v,y) \<in> (tree_edges s)\<^sup>+" .
          with tree_path_impl_parenthesis assms hd_stack_tree_path_finished tree_path_disc have 
            y_fin: "y \<in> dom (finished s)"
            and y_\<delta> : "\<delta> s v < \<delta> s y" by blast+
          with step have z_disc: "z \<in> dom (discovered s)"
            using finished_imp_succ_discovered
            by auto

          from step edges_covered finished_no_pending[of y] y_fin finished_discovered have 
            "(y,z) \<in> edges s" 
            by fast
          thus ?thesis
          proof (rule edgesE_CB)
            assume "(y,z) \<in> tree_edges s" with T show ?thesis ..
          next
            assume CB: "(y,z) \<in> cross_edges s \<union> back_edges s"
            with lowlink_path_complex[OF T] assms have 
              "\<exists>p. lowlink_path s v p z" by blast
            with \<delta>z z_disc have \<delta>z: "\<delta> s v < \<delta> s z" by simp

            show ?thesis
            proof (cases "v \<in> dom (finished s)")
              case True with tree_path_impl_parenthesis T have y_f: "\<phi> s y < \<phi> s v" by blast
                
              from CB show ?thesis
              proof
                assume C: "(y,z) \<in> cross_edges s"
                with cross_edges_finished_decr y_fin y_f have "\<phi> s z < \<phi> s v" 
                  by force
                moreover note \<delta>z
                moreover from C cross_edges_target_finished have 
                  "z \<in> dom (finished s)" by simp
                ultimately show ?thesis 
                  using parenthesis_impl_tree_path[OF True] by metis
              next
                assume B: "(y,z) \<in> back_edges s"
                with back_edge_disc_lt_fin y_fin y_f have "\<delta> s z < \<phi> s v" 
                  by force
                moreover note \<delta>z z_disc
                ultimately have "z \<in> dom (finished s)" "\<phi> s z < \<phi> s v" 
                  using parenthesis_contained[OF True] by simp_all
                with \<delta>z show ?thesis 
                  using parenthesis_impl_tree_path[OF True] by metis
              qed
            next
              case False \<comment> \<open>\<open>v \<notin> dom (finished s)\<close>\<close>
              with assms have st: "stack s \<noteq> []" "v = hd (stack s)" "pending s `` {v} = {}" by blast+
              
              have "z \<in> dom (finished s)"
              proof (rule ccontr)
                assume "z \<notin> dom (finished s)"
                with z_disc have "z \<in> set (stack s)" by (simp add: stack_set_def)
                with \<open>z\<noteq>v\<close> st have "z \<in> set (tl (stack s))" by (cases "stack s") auto
                with st tl_lt_stack_hd_discover \<delta>z show False by force
              qed
              with \<delta>z parenthesis_impl_tree_path_not_finished v_disc False show ?thesis by simp
            qed
          qed
        qed
      qed simp     
      hence "r \<in> (tree_edges s)\<^sup>* `` {v}" by auto
    }
    hence "?scc \<inter> dom (discovered s) \<subseteq> (tree_edges s)\<^sup>* `` {v}"
      by fastforce
    thus "scc_root s v ?scc" by (auto intro!: scc_rootI v_disc)
  qed
end end
end
