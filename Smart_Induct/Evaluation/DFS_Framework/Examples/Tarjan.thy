section \<open>Tarjan's Algorithm\<close>
theory Tarjan
imports 
  Tarjan_LowLink
begin
text \<open>We use the DFS Framework to implement Tarjan's algorithm.
  Note that, currently, we only provide an abstract version, and no refinement to 
  efficient code.
\<close>

subsection \<open>Preliminaries\<close>
(* Though this is a general lemma about dropWhile/takeWhile, it is probably only of use for this algorithm. *)
lemma tjs_union:
  fixes tjs u
  defines "dw \<equiv> dropWhile ((\<noteq>) u) tjs"
  defines "tw \<equiv> takeWhile ((\<noteq>) u) tjs"
  assumes "u \<in> set tjs"
  shows "set tjs = set (tl dw) \<union> insert u (set tw)"
proof -
  from takeWhile_dropWhile_id have "set tjs = set (tw@dw)" by (auto simp: dw_def tw_def)
  hence "set tjs = set tw \<union> set dw" by (metis set_append)
  moreover from \<open>u \<in> set tjs\<close> dropWhile_eq_Nil_conv have "dw \<noteq> []" by (auto simp: dw_def)
  from hd_dropWhile[OF this[unfolded dw_def]] have "hd dw = u" by (simp add: dw_def)
  with \<open>dw \<noteq> []\<close> have "set dw = insert u (set (tl dw))" by (cases "dw") auto
  ultimately show ?thesis by blast
qed

subsection \<open>Instantiation of the DFS-Framework\<close>
record 'v tarjan_state = "'v state" +
  sccs :: "'v set set"
  lowlink :: "'v \<rightharpoonup> nat"
  tj_stack :: "'v list"

type_synonym 'v tarjan_param = "('v, ('v,unit) tarjan_state_ext) parameterization"

abbreviation "the_lowlink s v \<equiv> the (lowlink s v)"

context timing_syntax
begin
  notation the_lowlink ("\<zeta>")
end

locale Tarjan_def = graph_defs G
  for G :: "('v, 'more) graph_rec_scheme"
begin
  context begin interpretation timing_syntax .

  definition tarjan_disc :: "'v \<Rightarrow> 'v tarjan_state \<Rightarrow> ('v,unit) tarjan_state_ext nres" where
    "tarjan_disc v s = RETURN \<lparr> sccs = sccs s, 
                                 lowlink = (lowlink s)(v \<mapsto> \<delta> s v),
                                 tj_stack = v#tj_stack s\<rparr>"

  definition tj_stack_pop :: "'v list \<Rightarrow> 'v \<Rightarrow> ('v list \<times> 'v set) nres" where
    "tj_stack_pop tjs u = RETURN (tl (dropWhile ((\<noteq>) u) tjs), insert u (set (takeWhile ((\<noteq>) u) tjs)))"

  lemma tj_stack_pop_set:
    "tj_stack_pop tjs u \<le> SPEC (\<lambda>(tjs',scc). u \<in> set tjs \<longrightarrow> set tjs = set tjs' \<union> scc \<and> u \<in> scc)"
  proof -
    from tjs_union[of u tjs] show ?thesis
      unfolding tj_stack_pop_def
      by (refine_vcg) auto
  qed

  lemmas tj_stack_pop_set_leof_rule = weaken_SPEC[OF tj_stack_pop_set, THEN leof_lift]

  definition tarjan_fin :: "'v \<Rightarrow> 'v tarjan_state \<Rightarrow> ('v,unit) tarjan_state_ext nres" where
    "tarjan_fin v s = do {
           let ll = (if stack s = [] then lowlink s 
                     else let u = hd (stack s) in
                          (lowlink s)(u \<mapsto> min (\<zeta> s u) (\<zeta> s v)));
           let s' = s\<lparr> lowlink := ll \<rparr>;

           ASSERT (v \<in> set (tj_stack s));
           ASSERT (distinct (tj_stack s));
           if \<zeta> s v = \<delta> s v then do {
                ASSERT (scc_root' E s v (scc_of E v));
                (tjs,scc) \<leftarrow> tj_stack_pop (tj_stack s) v;
                RETURN (state.more (s'\<lparr> tj_stack := tjs, sccs := insert scc (sccs s)\<rparr>))
           } else do {
                ASSERT (\<not> scc_root' E s v (scc_of E v));
                RETURN (state.more s')
           }}"

  definition tarjan_back :: "'v \<Rightarrow> 'v \<Rightarrow> 'v tarjan_state \<Rightarrow> ('v,unit) tarjan_state_ext nres" where
    "tarjan_back u v s = (
       if \<delta> s v < \<delta> s u \<and> v \<in> set (tj_stack s) then
         let ul' = min (\<zeta> s u) (\<delta> s v)
         in RETURN (state.more (s\<lparr> lowlink := (lowlink s)(u\<mapsto>ul') \<rparr>))
       else NOOP s)"
end (* end timing syntax *)

  definition tarjan_params :: "'v tarjan_param" where
    "tarjan_params = \<lparr>
      on_init = RETURN \<lparr> sccs = {}, lowlink = Map.empty, tj_stack = [] \<rparr>,
      on_new_root = tarjan_disc,
      on_discover = \<lambda>u. tarjan_disc,
      on_finish = tarjan_fin,
      on_back_edge = tarjan_back,
      on_cross_edge = tarjan_back,
      is_break = \<lambda>s. False \<rparr>"

  schematic_goal tarjan_params_simps[simp]:
    "on_init tarjan_params = ?OI"
    "on_new_root tarjan_params = ?ONR"
    "on_discover tarjan_params = ?OD"
    "on_finish tarjan_params = ?OF"
    "on_back_edge tarjan_params = ?OBE"
    "on_cross_edge tarjan_params = ?OCE"
    "is_break tarjan_params = ?IB"
    unfolding tarjan_params_def gen_parameterization.simps
    by (rule refl)+

  sublocale param_DFS_defs G tarjan_params .
end

locale Tarjan = Tarjan_def G +
                param_DFS G tarjan_params
  for G :: "('v, 'more) graph_rec_scheme"
begin

  lemma [simp]: 
    "sccs (empty_state \<lparr>sccs = s, lowlink = l, tj_stack = t\<rparr>) = s"
    "lowlink (empty_state \<lparr>sccs = s, lowlink = l, tj_stack = t\<rparr>) = l"
    "tj_stack (empty_state \<lparr>sccs = s, lowlink = l, tj_stack = t\<rparr>) = t"
    by (simp_all add: empty_state_def)

  lemma sccs_more_cong[cong]:"state.more s = state.more s' \<Longrightarrow> sccs s = sccs s'"
    by (cases s, cases s') simp
  lemma lowlink_more_cong[cong]:"state.more s = state.more s' \<Longrightarrow> lowlink s = lowlink s'"
    by (cases s, cases s') simp
  lemma tj_stack_more_cong[cong]:"state.more s = state.more s' \<Longrightarrow> tj_stack s = tj_stack s'"
    by (cases s, cases s') simp

   lemma [simp]: 
     "s\<lparr> state.more := \<lparr>sccs = sc, lowlink = l, tj_stack = t\<rparr>\<rparr>
      = s\<lparr> sccs := sc, lowlink := l, tj_stack := t\<rparr>"                  
    by (cases s) simp
end

locale Tarjan_invar = Tarjan +
  DFS_invar where param = tarjan_params

context Tarjan_def begin
  lemma Tarjan_invar_eq[simp]:
    "DFS_invar G tarjan_params s \<longleftrightarrow> Tarjan_invar G s" (is "?D \<longleftrightarrow> ?T")
  proof
    assume ?D then interpret DFS_invar where param=tarjan_params .
    show ?T ..
  next
    assume ?T then interpret Tarjan_invar .
    show ?D ..
  qed
end

subsection \<open>Correctness Proof\<close>
context Tarjan begin
  lemma i_tj_stack_discovered:
    "is_invar (\<lambda>s. set (tj_stack s) \<subseteq> dom (discovered s))"
  proof (induct rule: establish_invarI)
    case (finish s)
    from finish show ?case
      apply simp
      unfolding tarjan_fin_def
      apply (refine_vcg tj_stack_pop_set_leof_rule)
      apply auto
      done
  qed (auto simp add: tarjan_disc_def tarjan_back_def)

  lemmas (in Tarjan_invar) tj_stack_discovered =
    i_tj_stack_discovered[THEN make_invar_thm]

  lemma i_tj_stack_distinct:
    "is_invar (\<lambda>s. distinct (tj_stack s))"
  proof (induct rule: establish_invarI_ND)
    case (new_discover s s' v) then interpret Tarjan_invar where s=s by simp
    from new_discover tj_stack_discovered have "v \<notin> set (tj_stack s)" by auto
    with new_discover show ?case by (simp add: tarjan_disc_def)
  next
    case (finish s) thus ?case
      apply simp
      unfolding tarjan_fin_def tj_stack_pop_def
      apply (refine_vcg)
      apply (auto intro: distinct_tl)
      done
  qed (simp_all add: tarjan_back_def)

  lemmas (in Tarjan_invar) tj_stack_distinct =
    i_tj_stack_distinct[THEN make_invar_thm]

  context begin interpretation timing_syntax .
  lemma i_tj_stack_incr_disc:
    "is_invar (\<lambda>s. \<forall>k<length (tj_stack s). \<forall>j<k. \<delta> s (tj_stack s ! j) > \<delta> s (tj_stack s ! k))"
  proof (induct rule: establish_invarI_ND)
    case (new_discover s s' v) then interpret Tarjan_invar where s=s by simp

    from new_discover tj_stack_discovered have "v \<notin> set (tj_stack s)" by auto
    moreover {
      fix k j
      assume "k < Suc (length (tj_stack s))" "j < k"
      hence "k - Suc 0 < length (tj_stack s)" by simp
      hence "tj_stack s ! (k - Suc 0) \<in> set (tj_stack s)" using nth_mem by metis
      with tj_stack_discovered timing_less_counter have "\<delta> s (tj_stack s ! (k - Suc 0)) < counter s" by blast
    }
    moreover {
      fix k j
      define k' where "k' = k - Suc 0"
      define j' where "j' = j - Suc 0"

      assume A: "k < Suc (length (tj_stack s))" "j < k" "(v#tj_stack s) ! j \<noteq> v"
      hence gt_0: "j > 0 \<and> k>0" by (cases "j=0") simp_all
      moreover with \<open>j < k\<close> have "j' < k'" by (simp add: j'_def k'_def)
      moreover from A have "k' < length (tj_stack s)" by (simp add: k'_def)
      ultimately have "\<delta> s (tj_stack s ! j') > \<delta> s (tj_stack s ! k')"
        using new_discover by blast
      with gt_0 have "\<delta> s ((v#tj_stack s) ! j) > \<delta> s (tj_stack s ! k')"
        unfolding j'_def
        by (simp add: nth_Cons')
    }

    ultimately show ?case 
      using new_discover
      by (auto simp add: tarjan_disc_def)
  next
    case (finish s s' u)

    {
      let ?dw = "dropWhile ((\<noteq>) u) (tj_stack s)"
      let ?tw = "takeWhile ((\<noteq>) u) (tj_stack s)"

      fix a k j
      assume A: "a = tl ?dw" "k < length a" "j < k"
      and "u \<in> set (tj_stack s)"
      hence "?dw \<noteq> []" by auto

      define j' k' where "j' = Suc j + length ?tw" and "k' = Suc k + length ?tw"
      with \<open>j < k\<close> have "j' < k'" by simp
      
      have "length (tj_stack s) = length ?tw + length ?dw"
        by (simp add: length_append[symmetric])
      moreover from A have *: "Suc k < length ?dw" and **: "Suc j < length ?dw" by auto
      ultimately have "k' < length (tj_stack s)" by (simp add: k'_def)

      with finish \<open>j'<k'\<close> have "\<delta> s (tj_stack s ! k') < \<delta> s (tj_stack s ! j')" by simp
      also from dropWhile_nth[OF *] have "tj_stack s ! k' = ?dw ! Suc k"
        by (simp add: k'_def)
      also from dropWhile_nth[OF **] have "tj_stack s ! j' = ?dw ! Suc j"
        by (simp add: j'_def)
      also from nth_tl[OF \<open>?dw \<noteq> []\<close>] have "?dw ! Suc k = a ! k" by (simp add: A)
      also from nth_tl[OF \<open>?dw \<noteq> []\<close>] have "?dw ! Suc j = a ! j" by (simp add: A)
      finally have "\<delta> s (a ! k) < \<delta> s (a ! j)" .
    } note aux = this

    from finish show ?case
      apply simp
      unfolding tarjan_fin_def tj_stack_pop_def
      apply refine_vcg
      apply (auto intro!: aux)
      done
  qed (simp_all add: tarjan_back_def)
end end

context Tarjan_invar begin context begin interpretation timing_syntax .
  lemma tj_stack_incr_disc:
    assumes "k < length (tj_stack s)"
    and "j < k"
    shows "\<delta> s (tj_stack s ! j) > \<delta> s (tj_stack s ! k)"
    using assms i_tj_stack_incr_disc[THEN make_invar_thm]
    by blast

  lemma tjs_disc_dw_tw:
    fixes u
    defines "dw \<equiv> dropWhile ((\<noteq>) u) (tj_stack s)"
    defines "tw \<equiv> takeWhile ((\<noteq>) u) (tj_stack s)"
    assumes "x \<in> set dw" "y \<in> set tw"
    shows "\<delta> s x < \<delta> s y"
  proof -
    from assms obtain k where k: "dw ! k = x" "k < length dw" by (metis in_set_conv_nth)
    from assms obtain j where j: "tw ! j = y" "j < length tw" by (metis in_set_conv_nth)

    have "length (tj_stack s) = length tw + length dw"
        by (simp add: length_append[symmetric] tw_def dw_def)
    with k j have "\<delta> s (tj_stack s ! (k + length tw)) < \<delta> s (tj_stack s ! j)"
      by (simp add: tj_stack_incr_disc)
    also from j takeWhile_nth have "tj_stack s ! j = y" by (metis tw_def)
    also from dropWhile_nth k have "tj_stack s ! (k + length tw) = x" by (metis tw_def dw_def)
    finally show ?thesis .
  qed
end end

context Tarjan begin context begin interpretation timing_syntax .
  lemma i_sccs_finished_stack_ss_tj_stack:
    "is_invar (\<lambda>s. \<Union>(sccs s) \<subseteq> dom (finished s) \<and> set (stack s) \<subseteq> set (tj_stack s))"
  proof (induct rule: establish_invarI)
    case (finish s s' u) then interpret Tarjan_invar where s=s by simp

    let ?tw = "takeWhile ((\<noteq>) u) (tj_stack s)"
    let ?dw = "dropWhile ((\<noteq>) u) (tj_stack s)"

    {
      fix x
      assume A: "x \<noteq> u" "x \<in> set ?tw" "u \<in> set (tj_stack s)"
      hence x_tj: "x \<in> set (tj_stack s)" by (auto dest: set_takeWhileD)

      have "x \<in> dom (finished s)"
      proof (rule ccontr)
        assume "x \<notin> dom (finished s)"
        with x_tj tj_stack_discovered discovered_eq_finished_un_stack have "x \<in> set (stack s)" by blast
        with \<open>x\<noteq>u\<close> finish have "x \<in> set (tl (stack s))" by (cases "stack s") auto
        with tl_lt_stack_hd_discover finish have *: "\<delta> s x < \<delta> s u" by simp

        from A have "?dw \<noteq> []" by simp
        with hd_dropWhile[OF this] hd_in_set have "u \<in> set ?dw" by metis
        with tjs_disc_dw_tw \<open>x \<in> set ?tw\<close> have "\<delta> s u < \<delta> s x" by simp

        with * show False by force
      qed
      hence "\<exists>y. finished s x = Some y" by blast
    } note aux_scc = this

    {
      fix  x
      assume A: "x \<in> set (tl (stack s))" "u \<in> set (tj_stack s)"
      with finish stack_distinct have "x \<noteq> u" by (cases "stack s") auto

      moreover
      from A have "x \<in> set (stack s)" by (metis in_set_tlD)
      with stack_not_finished have "x \<notin> dom (finished s)" by simp
      with A aux_scc[OF \<open>x \<noteq> u\<close>] have "x \<notin> set ?tw" by blast

      moreover 
      from finish \<open>x \<in> set (stack s)\<close> have "x \<in> set (tj_stack s)" by auto

      moreover note tjs_union[OF \<open>u \<in> set (tj_stack s)\<close>]

      ultimately have "x \<in> set (tl ?dw)" by blast
    } note aux_tj = this
      
    from finish show ?case
      apply simp
      unfolding tarjan_fin_def tj_stack_pop_def
      apply (refine_vcg)
      using aux_scc aux_tj apply (auto dest: in_set_tlD)
      done
  qed (auto simp add: tarjan_disc_def tarjan_back_def)

  lemma i_tj_stack_ss_stack_finished:
    "is_invar (\<lambda>s. set (tj_stack s) \<subseteq> set (stack s) \<union> dom (finished s))"
  proof (induct rule: establish_invarI)
    case (finish s) thus ?case
      apply simp
      unfolding tarjan_fin_def
      apply (refine_vcg tj_stack_pop_set_leof_rule)
      apply ((simp, cases "stack s", simp_all)[])+
      done
  qed (auto simp add: tarjan_disc_def tarjan_back_def)

  lemma i_finished_ss_sccs_tj_stack:
    "is_invar (\<lambda>s. dom (finished s) \<subseteq> \<Union>(sccs s) \<union> set (tj_stack s))"
  proof (induction rule: establish_invarI_ND)
    case (new_discover s s' v) then interpret Tarjan_invar where s=s by simp
    from new_discover finished_discovered have "v \<notin> dom (finished s)" by auto
    with new_discover show ?case
      by (auto simp add: tarjan_disc_def)
  next
    case (finish s s' u) then interpret Tarjan_invar where s=s by simp
    from finish show ?case
      apply simp
      unfolding tarjan_fin_def
      apply (refine_vcg tj_stack_pop_set_leof_rule)
      apply auto
      done
  qed (simp_all add: tarjan_back_def)
end end

context Tarjan_invar begin
  lemmas finished_ss_sccs_tj_stack =
    i_finished_ss_sccs_tj_stack[THEN make_invar_thm]
  
  lemmas tj_stack_ss_stack_finished =
    i_tj_stack_ss_stack_finished[THEN make_invar_thm]

  lemma sccs_finished:
    "\<Union>(sccs s) \<subseteq> dom (finished s)"
    using i_sccs_finished_stack_ss_tj_stack[THEN make_invar_thm]
    by blast

  lemma stack_ss_tj_stack:
    "set (stack s) \<subseteq> set (tj_stack s)"
    using i_sccs_finished_stack_ss_tj_stack[THEN make_invar_thm]
    by blast
  
  lemma hd_stack_in_tj_stack:
    "stack s \<noteq> [] \<Longrightarrow> hd (stack s) \<in> set (tj_stack s)"
    using stack_ss_tj_stack hd_in_set
    by auto
end

context Tarjan begin context begin interpretation timing_syntax .
  lemma i_no_finished_root:
    "is_invar (\<lambda>s. scc_root s r scc \<and> r \<in> dom (finished s) \<longrightarrow> (\<forall>x \<in> scc. x \<notin> set (tj_stack s)))"
  proof (induct rule: establish_invarI_ND_CB)
    case (new_discover s s' v) then interpret Tarjan_invar where s=s by simp
    {
      fix x
      let ?s = "s'\<lparr>state.more := x\<rparr>"

      assume TRANS: "\<And>\<Psi>. tarjan_disc v s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
      and inv': "DFS_invar G tarjan_params (s'\<lparr>state.more := x\<rparr>)"
      and r: "scc_root ?s r scc" "r \<in> dom (finished s')"

      from inv' interpret s': Tarjan_invar where s="?s" by simp

      have "tj_stack ?s = v#tj_stack s"
        by (rule TRANS) (simp add: new_discover tarjan_disc_def)
      
      moreover
      from r s'.scc_root_finished_impl_scc_finished have "scc \<subseteq> dom (finished ?s)" by auto
      with new_discover finished_discovered have "v \<notin> scc" by force

      moreover
      from r finished_discovered new_discover have "r \<in> dom (discovered s)" by auto
      with r inv' new_discover have "scc_root s r scc"
        apply (intro scc_root_transfer[where s'="?s", THEN iffD2])
        apply clarsimp_all
        done
      with new_discover r have "\<forall>x \<in> scc. x \<notin> set (tj_stack s')" by simp

      ultimately have "\<forall>x\<in>scc. x \<notin> set (tj_stack ?s)" by (auto simp: new_discover)
    }
    with new_discover show ?case by (simp add: pw_leof_iff)
  next
    case (cross_back_edge s s' u v) then interpret Tarjan_invar where s=s by simp
    { 
      fix x
      let ?s = "s'\<lparr>state.more := x\<rparr>"
      assume TRANS: "\<And>\<Psi>. tarjan_back u v s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
      and r: "scc_root ?s r scc" "r \<in> dom (finished s')"
      with cross_back_edge have "scc_root s r scc"
        by (simp add: scc_root_transfer'[where s'="?s"])

      moreover
      have "tj_stack ?s = tj_stack s" by (rule TRANS) (simp add: cross_back_edge tarjan_back_def)

      ultimately  have "\<forall>x\<in>scc. x \<notin> set (tj_stack ?s)"
        using cross_back_edge r by simp
    }
    with cross_back_edge show ?case by (simp add: pw_leof_iff)
  next
    case (finish s s' u) then interpret Tarjan_invar where s=s by simp
    
    {
      fix x
      let ?s = "s'\<lparr>state.more := x\<rparr>"
      assume TRANS:  "\<And>\<Psi>. tarjan_fin u s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
      and inv': "DFS_invar G tarjan_params (s'\<lparr>state.more := x\<rparr>)"
      and r: "scc_root ?s r scc" "r \<in> dom (finished s')"

      from inv' interpret s': Tarjan_invar where s="?s" by simp

      have "\<forall>x\<in>scc. x \<notin> set (tj_stack ?s)"
      proof (cases "r = u")
        case False with finish r have "\<forall>x\<in>scc. x \<notin> set (tj_stack s)"
          using scc_root_transfer'[where s'="?s"]
          by simp
        moreover have "set (tj_stack ?s) \<subseteq> set (tj_stack s)"
          apply (rule TRANS)
          unfolding tarjan_fin_def
          apply (refine_vcg tj_stack_pop_set_leof_rule)
          apply (simp_all add: finish)
          done
        ultimately show ?thesis by blast
      next
        case True with r s'.scc_root_unique_is_scc have "scc_root ?s u (scc_of E u)" by simp
        with s'.scc_root_transfer'[where s'=s'] finish have "scc_root s' u (scc_of E u)" by simp

        moreover
        hence [simp]: "tj_stack ?s = tl (dropWhile ((\<noteq>) u) (tj_stack s))"
          apply (rule_tac TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          apply (refine_vcg)
          apply (simp_all add: finish)
          done

        {
          let ?dw = "dropWhile ((\<noteq>) u) (tj_stack s)"
          let ?tw = "takeWhile ((\<noteq>) u) (tj_stack s)"
          fix x
          define j::nat where "j = 0"
          
          assume x: "x \<in> set (tj_stack ?s)"
          then obtain i where i: "i < length (tj_stack ?s)" "tj_stack ?s ! i = x"
            by (metis in_set_conv_nth)

          have "length (tj_stack s) = length ?tw + length ?dw"
            by (simp add: length_append[symmetric])
          with i have "\<delta> s (tj_stack s ! (Suc i + length ?tw)) < \<delta> s (tj_stack s ! length ?tw)"
            by (simp add: tj_stack_incr_disc)

          also from hd_stack_in_tj_stack finish have ne: "?dw \<noteq> []" and "length ?dw > 0" by simp_all
          from hd_dropWhile[OF ne] hd_conv_nth[OF ne] have "?dw ! 0 = u" by simp
          with dropWhile_nth[OF \<open>length ?dw > 0\<close>] have "tj_stack s ! length ?tw = u" by simp

          also from i have "?dw ! Suc i = x" "Suc i < length ?dw" by (simp_all add: nth_tl[OF ne])
          with dropWhile_nth[OF this(2)] have "tj_stack s ! (Suc i + length ?tw) = x" by simp

          finally have "\<delta> ?s x < \<delta> ?s u" by (simp add: finish)

          moreover from x s'.tj_stack_discovered have "x \<in> dom (discovered ?s)" by auto
          ultimately have "x \<notin> scc" using s'.scc_root_disc_le r True by force
        } thus ?thesis by metis
      qed
    }
    with finish show ?case by (simp add: pw_leof_iff)
  qed simp_all
end end

context Tarjan_invar begin
  lemma no_finished_root:
    assumes "scc_root s r scc"
    and "r \<in> dom (finished s)"
    and "x \<in> scc"
    shows "x \<notin> set (tj_stack s)"
    using assms
    using i_no_finished_root[THEN make_invar_thm]
    by blast

  context begin interpretation timing_syntax .

  lemma tj_stack_reach_stack:
    assumes "u \<in> set (tj_stack s)"
    shows "\<exists>v \<in> set (stack s). (u,v) \<in> E\<^sup>* \<and> \<delta> s v \<le> \<delta> s u"
  proof -
    have u_scc: "u \<in> scc_of E u" by simp

    from assms tj_stack_discovered have u_disc: "u \<in> dom (discovered s)" by auto
    with scc_root_of_node_exists obtain r where r: "scc_root s r (scc_of E u)" by blast
    have "r \<in> set (stack s)"
    proof (rule ccontr)
      assume "r \<notin> set (stack s)"
      with r[unfolded scc_root_def] stack_set_def have "r \<in> dom (finished s)" by simp
      with u_scc have "u \<notin> set (tj_stack s)" using no_finished_root r by blast
      with assms show False by contradiction
    qed
    moreover from r scc_reach_scc_root u_scc u_disc have "(u,r) \<in> E\<^sup>*" by blast
    moreover from r scc_root_disc_le u_scc u_disc have "\<delta> s r \<le> \<delta> s u" by blast
    ultimately show ?thesis by metis
  qed

  lemma tj_stack_reach_hd_stack:
    assumes "v \<in> set (tj_stack s)"
    shows "(v, hd (stack s)) \<in> E\<^sup>*"
  proof -
    from tj_stack_reach_stack assms obtain r where r: "r \<in> set (stack s)" "(v,r) \<in> E\<^sup>*" by blast
    hence "r = hd (stack s) \<or> r \<in> set (tl (stack s))" by (cases "stack s") auto
    thus ?thesis
    proof
      assume "r = hd (stack s)" with r show ?thesis by simp
    next
      from r have ne :"stack s \<noteq> []" by auto

      assume "r \<in> set (tl (stack s))"
      with tl_stack_hd_tree_path ne have "(r,hd (stack s)) \<in> (tree_edges s)\<^sup>+" by simp
      with trancl_mono_mp tree_edges_ssE have "(r,hd (stack s))\<in>E\<^sup>*" by (metis rtrancl_eq_or_trancl)
      with \<open>(v,r)\<in>E\<^sup>*\<close> show ?thesis by (metis rtrancl_trans)
    qed
  qed
  
  lemma empty_stack_imp_empty_tj_stack: 
    assumes "stack s = []"
    shows "tj_stack s = []"
  proof (rule ccontr)
    assume ne: "tj_stack s \<noteq> []"
    then obtain x where x: "x \<in> set (tj_stack s)" by auto
    with tj_stack_reach_stack obtain r where "r \<in> set (stack s)" by auto
    with assms show False by simp
  qed
  
  lemma stacks_eq_iff: "stack s = [] \<longleftrightarrow> tj_stack s = []"
    using empty_stack_imp_empty_tj_stack stack_ss_tj_stack
    by auto
end end

context Tarjan begin context begin interpretation timing_syntax .
  lemma i_sccs_are_sccs:
    "is_invar (\<lambda>s. \<forall>scc \<in> sccs s. is_scc E scc)"
  proof (induction rule: establish_invarI)
    case (finish s s' u) then interpret Tarjan_invar where s=s by simp
    from finish have EQ[simp]:
      "finished s' = (finished s)(u \<mapsto> counter s)"
      "discovered s' = discovered s"
      "tree_edges s' = tree_edges s"
      "sccs s' = sccs s"
      "tj_stack s' = tj_stack s"
      by simp_all

    {
      fix x

      let ?s = "s'\<lparr>state.more := x\<rparr>"
      assume TRANS: "\<And>\<Psi>. tarjan_fin u s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
      and inv': "DFS_invar G tarjan_params (s'\<lparr>state.more := x\<rparr>)"
      then interpret s': Tarjan_invar where s="?s" by simp
      
      from finish hd_in_set stack_set_def have 
        u_disc: "u \<in> dom (discovered s)" 
        and u_n_fin: "u \<notin> dom (finished s)" by blast+

      have "\<forall>scc \<in> sccs ?s. is_scc E scc"
      proof (cases "scc_root s' u (scc_of E u)")
        case False
        have "sccs ?s = sccs s"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by (refine_vcg) (simp_all add: False)
        thus ?thesis by (simp add: finish)
      next
        case True
        let ?dw = "dropWhile ((\<noteq>) u) (tj_stack s)"
        let ?tw = "takeWhile ((\<noteq>) u) (tj_stack s)"
        let ?tw' = "insert u (set ?tw)"

        have [simp]: "sccs ?s = insert ?tw' (sccs s)"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by (refine_vcg) (simp_all add: True)

        have [simp]: "tj_stack ?s = tl ?dw"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by (refine_vcg) (simp_all add: True)

        from True scc_root_transfer'[where s'=s'] have "scc_root s u (scc_of E u)" by simp
        with inv' scc_root_transfer[where s'="?s"] u_disc have u_root: "scc_root ?s u (scc_of E u)" by simp

        have "?tw' \<subseteq> scc_of E u"
        proof
          fix v assume v: "v \<in> ?tw'"
          show "v \<in> scc_of E u"
          proof cases
            assume "v \<noteq> u" with v have v: "v \<in> set ?tw" by auto
            hence v_tj: "v \<in> set (tj_stack s)" by (auto dest: set_takeWhileD)
            with tj_stack_discovered have v_disc: "v \<in> dom (discovered s)" by auto

            from hd_stack_in_tj_stack finish  have "?dw \<noteq> []" by simp
            with hd_dropWhile[OF this] hd_in_set have "u \<in> set ?dw" by metis
            with v have "\<delta> s v > \<delta> s u" using tjs_disc_dw_tw by blast
           
            moreover have "v \<in> dom (finished s)"
            proof (rule ccontr)
              assume "v \<notin> dom (finished s)" 
              with v_disc stack_set_def have "v \<in> set (stack s)" by auto
              with \<open>v\<noteq>u\<close> finish have "v \<in> set (tl (stack s))" by (cases "stack s") auto
              with tl_lt_stack_hd_discover finish have "\<delta> s v < \<delta> s u" by simp
              with \<open>\<delta> s v > \<delta> s u\<close> show False by force
            qed

            ultimately have "(u,v) \<in> (tree_edges s)\<^sup>+" 
              using parenthesis_impl_tree_path_not_finished[OF u_disc] u_n_fin
              by force
            with trancl_mono_mp tree_edges_ssE have "(u,v)\<in>E\<^sup>*" by (metis rtrancl_eq_or_trancl)

            moreover
            from tj_stack_reach_hd_stack v_tj finish have "(v,u)\<in>E\<^sup>*" by simp 

            moreover have "is_scc E (scc_of E u)" "u \<in> scc_of E u" by simp_all
            ultimately show ?thesis using is_scc_closed by metis
          qed simp
        qed
        moreover have "scc_of E u \<subseteq> ?tw'"
        proof
          fix v assume v: "v \<in> scc_of E u"
          moreover note u_root
          moreover have "u \<in> dom (finished ?s)" by simp
          ultimately have "v \<in> dom (finished ?s)" "v \<notin> set (tj_stack ?s)" 
            using s'.scc_root_finished_impl_scc_finished s'.no_finished_root
            by auto
          with s'.finished_ss_sccs_tj_stack have "v \<in> \<Union>(sccs ?s)" by blast
          hence "v \<in> \<Union>(sccs s) \<or> v \<in> ?tw'" by auto
          thus "v \<in> ?tw'"
          proof
            assume "v \<in> \<Union>(sccs s)"
            then obtain scc where scc: "v \<in> scc" "scc \<in> sccs s" by auto
            moreover with finish have "is_scc E scc" by simp
            moreover have "is_scc E (scc_of E u)" by simp
            moreover note v
            ultimately have "scc = scc_of E u" using is_scc_unique by metis
            hence "u \<in> scc" by simp
            with scc sccs_finished have "u \<in> dom (finished s)" by auto
            with u_n_fin show ?thesis by contradiction
          qed simp
        qed
        ultimately have "?tw' = scc_of E u" by auto
        hence "is_scc E ?tw'" by simp
        with finish show ?thesis by auto
      qed
    }   
    thus ?case by (auto simp: pw_leof_iff finish)
  qed (simp_all add: tarjan_back_def tarjan_disc_def)
end

  lemmas (in Tarjan_invar) sccs_are_sccs =
    i_sccs_are_sccs[THEN make_invar_thm]

context begin interpretation timing_syntax .

  lemma i_lowlink_eq_LowLink:
    "is_invar (\<lambda>s. \<forall>x \<in> dom (discovered s). \<zeta> s x = LowLink s x)"
  proof -
    {
      fix s s' :: "'v tarjan_state"
      fix v w
      fix x

      let ?s = "s'\<lparr>state.more := x\<rparr>"

      assume pre_ll_sub_rev: "\<And>w. \<lbrakk>Tarjan_invar G ?s; w \<in> dom (discovered ?s); w \<noteq> v\<rbrakk> \<Longrightarrow> lowlink_set ?s w \<subseteq> lowlink_set s w \<union> {v}"
      assume tree_sub : "tree_edges s' = tree_edges s \<or> (\<exists>u. u \<noteq> v \<and> tree_edges s' = tree_edges s \<union> {(u,v)})"

      assume "Tarjan_invar G s"
      assume [simp]: "discovered s' = (discovered s)(v \<mapsto> counter s)"
                     "finished s' = finished s"
                     "lowlink s' = lowlink s"
                     "cross_edges s' = cross_edges s" "back_edges s' = back_edges s"
      assume v_n_disc: "v \<notin> dom (discovered s)"
      assume IH: "\<And>w. w\<in>dom (discovered s) \<Longrightarrow> \<zeta> s w = LowLink s w"

      assume TRANS: "\<And>\<Psi>. tarjan_disc v s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
      and INV: "DFS_invar G tarjan_params ?s"
      and w_disc: "w \<in> dom (discovered ?s)"

      interpret Tarjan_invar where s=s by fact
      from INV interpret s':Tarjan_invar where s="?s" by simp

      have [simp]: "lowlink ?s = (lowlink s)(v \<mapsto> counter s)"
        by (rule TRANS) (auto simp: tarjan_disc_def)

      from v_n_disc edge_imp_discovered have "edges s `` {v} = {}" by auto
      with tree_sub tree_edge_imp_discovered have "edges ?s `` {v} = {}" by auto
      with s'.no_path_imp_no_lowlink_path have "\<And>w. \<not>(\<exists>p. lowlink_path ?s v p w)" by metis
      hence ll_v: "lowlink_set ?s v = {v}"
          unfolding lowlink_set_def by auto

      have "\<zeta> ?s w = LowLink ?s w"
      proof (cases "w=v")
        case True with ll_v show ?thesis by simp 
      next
        case False hence "\<zeta> ?s w = \<zeta> s w" by simp
        also from IH have "\<zeta> s w = LowLink s w" using w_disc False by simp
        also have "LowLink s w = LowLink ?s w"
        proof (rule LowLink_eqI[OF INV])
          from v_n_disc show "discovered s \<subseteq>\<^sub>m discovered ?s" by (simp add: map_le_def)
          
          from tree_sub show "lowlink_set s w \<subseteq> lowlink_set ?s w"
            unfolding lowlink_set_def lowlink_path_def
            by auto

          show "lowlink_set ?s w \<subseteq> lowlink_set s w \<union> {v}"
          proof (cases "w = v")
            case True with ll_v show ?thesis by auto
          next
            case False thus ?thesis
              using pre_ll_sub_rev w_disc INV
              by simp
          qed
          
          show "w \<in> dom (discovered s)" using w_disc False by simp

          fix ll assume "ll \<in> {v}" with timing_less_counter lowlink_set_discovered have 
            "\<And>x. x\<in>\<delta> s`lowlink_set s w \<Longrightarrow> x < \<delta> ?s ll" by simp force
          moreover from Min_in lowlink_set_finite lowlink_set_not_empty w_disc False have 
            "LowLink s w \<in> \<delta> s`lowlink_set s w " by auto
          ultimately show "LowLink s w \<le> \<delta> ?s ll" by force
        qed
        finally show ?thesis .
      qed
    } note tarjan_disc_aux = this

    show ?thesis
    proof (induct rule: establish_invarI_CB)
      case (new_root s s' v0)
      {
        fix w x
        let ?s = "new_root v0 s\<lparr>state.more := x\<rparr>"
        have "lowlink_set ?s w \<subseteq> lowlink_set s w \<union> {v0}"
          unfolding lowlink_set_def lowlink_path_def
          by auto
      } note * = this

      from new_root show ?case
        using tarjan_disc_aux[OF *]
        by (auto simp add: pw_leof_iff)
    next
      case (discover s s' u v) then interpret Tarjan_invar where s=s by simp
      let ?s' = "discover (hd (stack s)) v (s\<lparr>pending := pending s - {(hd (stack s),v)}\<rparr>)"
      {
        fix w x
        let ?s = "?s'\<lparr>state.more := x\<rparr>"
        assume INV: "Tarjan_invar G ?s"
          and d: "w \<in> dom (discovered ?s')"
          and "w\<noteq>v"

        interpret s': Tarjan_invar where s="?s" by fact

        have "lowlink_set ?s w \<subseteq> lowlink_set s w \<union> {v}"
        proof
          fix ll
          assume ll: "ll \<in> lowlink_set ?s w"
          hence "ll = w \<or> (\<exists>p. lowlink_path ?s w p ll)" by (auto simp add: lowlink_set_def)
          thus "ll \<in> lowlink_set s w \<union> {v}" (is "ll \<in> ?L")
          proof
            assume "ll = w" with d show ?thesis by (auto simp add: lowlink_set_def)
          next
            assume "\<exists>p. lowlink_path ?s w p ll"
            then guess p .. note p = this

            hence [simp]: "p\<noteq>[]" by (simp add: lowlink_path_def)
    
            from p have "hd p = w" by (auto simp add: lowlink_path_def path_hd)
            
            show ?thesis
            proof (rule tri_caseE)
              assume "v\<noteq>ll" "v \<notin> set p" hence "lowlink_path s w p ll"
                using p by (auto simp add: lowlink_path_def)
              with ll show ?thesis by (auto simp add: lowlink_set_def)
            next
              assume "v = ll" thus ?thesis by simp
            next
              assume "v \<in> set p" "v \<noteq> ll"
              then obtain i where i: "i < length p" "p!i = v"
                by (metis in_set_conv_nth)
              have "False"
              proof (cases i)
                case "0" with i have "hd p = v" by (simp add: hd_conv_nth)
                with \<open>hd p = w\<close> \<open>w \<noteq> v\<close> show False by simp
              next
                case (Suc n) with i s'.lowlink_path_finished[OF p, where j=i] have 
                  "v \<in> dom (finished ?s)" by simp
                with finished_discovered discover show False by auto
              qed
              thus ?thesis ..
            qed
          qed
        qed
      } note * = this
      
      from discover hd_in_set stack_set_def have "v \<noteq> u" by auto
      with discover have **: "tree_edges ?s' = tree_edges s \<or> (\<exists>u. u \<noteq> v \<and> tree_edges ?s' = tree_edges s \<union> {(u,v)})" by auto

      from discover show ?case
        using tarjan_disc_aux[OF * **]
        by (auto simp: pw_leof_iff)
    next
      case (cross_back_edge s s' u v) then interpret Tarjan_invar where s=s by simp
      from cross_back_edge have [simp]:
        "discovered s' = discovered s"
        "finished s' = finished s"
        "tree_edges s' = tree_edges s"
        "lowlink s' = lowlink s"
        by simp_all
      {
        fix w :: "'v"
        fix x

        let ?s = "s'\<lparr>state.more := x\<rparr>"
        let ?L = "\<delta> s ` lowlink_set s w"
        let ?L' = "\<delta> ?s ` lowlink_set ?s w"

        assume TRANS: "\<And>\<Psi>. tarjan_back u v s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
          and inv': "DFS_invar G tarjan_params ?s"
          and w_disc': "w \<in> dom (discovered ?s)"
        
        from inv' interpret s':Tarjan_invar where s="?s" by simp
   
        have ll_sub: "lowlink_set s w \<subseteq> lowlink_set ?s w"
          unfolding lowlink_set_def lowlink_path_def
          by (auto simp: cross_back_edge)
      
        have ll_sub_rev: "lowlink_set ?s w \<subseteq> lowlink_set s w \<union> {v}"
          unfolding lowlink_set_def lowlink_path_def
          by (auto simp: cross_back_edge)

        from w_disc' have w_disc: "w \<in> dom (discovered s)" by simp
        with LowLink_le_disc have LLw: "LowLink s w \<le> \<delta> s w" by simp

        from cross_back_edge hd_in_set have u_n_fin: "u \<notin> dom (finished s)" 
          using stack_not_finished by auto

        {
          assume *: "v \<in> lowlink_set ?s w \<Longrightarrow> LowLink s w \<le> \<delta> ?s v"
          have "LowLink s w = LowLink ?s w"
          proof (rule LowLink_eqI[OF inv' _ ll_sub ll_sub_rev w_disc])
            show "discovered s \<subseteq>\<^sub>m discovered ?s" by simp
            
            fix ll assume "ll \<in> {v}" "ll \<in> lowlink_set ?s w"
            with * show "LowLink s w \<le> \<delta> ?s ll" by simp
          qed
        } note LL_eqI = this

        have "\<zeta> ?s w = LowLink ?s w"
        proof (cases "w=u")
          case True show ?thesis
          proof (cases "(\<delta> s v < \<delta> s w \<and> v \<in> set (tj_stack s) \<and> \<delta> s v < \<zeta> s w)")
            case False note all_False = this
            with \<open>w = u\<close> have "\<zeta> ?s w = \<zeta> s w"
              by (rule_tac TRANS) (auto simp add: tarjan_back_def cross_back_edge)
            also from cross_back_edge w_disc have \<zeta>w: "... = LowLink s w" by simp
            also have "LowLink s w = LowLink ?s w"
            proof (rule LL_eqI)
              assume v: "v \<in> lowlink_set ?s w"
              show "LowLink s w \<le> \<delta> ?s v"
              proof (cases "\<delta> s v < \<delta> s w \<and> \<delta> s v < \<zeta> s w")
                case False with \<open>LowLink s w \<le> \<delta> s w\<close> \<zeta>w show ?thesis by auto
              next
                case True with all_False have v_n_tj: "v \<notin> set (tj_stack s)" by simp
                from v have e: "(v,u) \<in> E\<^sup>*" "(u,v) \<in> E\<^sup>*" 
                  unfolding lowlink_set_def by (auto simp add: \<open>w=u\<close>)
                
                from v_n_tj have "v \<notin> set (stack s)" using stack_ss_tj_stack by auto
                with cross_back_edge have "v \<in> dom (finished s)" by (auto simp add: stack_set_def)
                with finished_ss_sccs_tj_stack v_n_tj sccs_are_sccs obtain scc 
                  where scc: "v \<in> scc" "scc \<in> sccs s" "is_scc E scc" by blast
                with is_scc_closed e have "u \<in> scc" by metis
                with scc sccs_finished u_n_fin have False by blast
                thus ?thesis ..
              qed
            qed
            finally show ?thesis .
          next
            case True note all_True = this
            with \<open>w=u\<close> have "\<zeta> ?s w = \<delta> s v"
              by (rule_tac TRANS) (simp add: tarjan_back_def cross_back_edge)

            also from True cross_back_edge w_disc have "\<delta> s v < LowLink s w" by simp
            with lowlink_set_finite lowlink_set_not_empty w_disc have "\<delta> s v = Min (?L \<union> {\<delta> s v})" by simp
            also have "v \<in> lowlink_set ?s w"
            proof -
              have cb: "(u,v) \<in> cross_edges ?s \<union> back_edges ?s" by (simp add: cross_back_edge)
              with s'.lowlink_path_single have "lowlink_path ?s u [u] v" by auto
              moreover from cb s'.cross_edges_ssE s'.back_edges_ssE have "(u,v) \<in> E" by blast
              hence "(u,v) \<in> E\<^sup>*" ..
              moreover from all_True tj_stack_reach_hd_stack have "(v,u) \<in> E\<^sup>*" by (simp add: cross_back_edge)
              moreover note \<open>v \<in> dom (discovered s)\<close>
              ultimately show ?thesis by (auto intro: s'.lowlink_setI simp: \<open>w=u\<close>)
            qed
            with ll_sub ll_sub_rev have "lowlink_set ?s w = lowlink_set s w \<union> {v}" by auto
            hence "Min (?L \<union> {\<delta> s v}) = LowLink ?s w" by simp
            finally show ?thesis .
          qed
        next
          case False \<comment> \<open>\<open>w \<noteq> u\<close>\<close>
          hence "\<zeta> ?s w = \<zeta> s w"
            by (rule_tac TRANS) (simp add: tarjan_back_def cross_back_edge)
          also have "\<zeta> s w = LowLink s w" using w_disc False by (simp add: cross_back_edge)
          also have "LowLink s w = LowLink ?s w"
          proof (rule LL_eqI)
            assume v: "v \<in> lowlink_set ?s w"
            thus "LowLink s w \<le> \<delta> ?s v" using LLw
            proof cases
              assume "v \<noteq> w"
              with v obtain p where p: "lowlink_path ?s w p v" "p\<noteq>[]" 
                by (auto simp add: lowlink_set_def lowlink_path_def)
              hence "hd p = w" by (auto simp add: lowlink_path_def path_hd)

              show ?thesis
              proof (cases "u \<in> set p")
                case False with last_in_set p cross_back_edge have "last p \<noteq> hd (stack s)" by force
                with p have "lowlink_path s w p v"
                  by (auto simp: cross_back_edge lowlink_path_def)
                with v have "v \<in> lowlink_set s w" 
                  by (auto intro: lowlink_setI simp: lowlink_set_def cross_back_edge)
                thus ?thesis by simp
              next
                case True then obtain i where i: "i < length p" "p!i = u"
                  by (metis in_set_conv_nth)
                have "False"
                proof (cases i)
                  case "0" with i have "hd p = u" by (simp add: hd_conv_nth)
                  with \<open>hd p = w\<close> \<open>w \<noteq> u\<close> show False by simp
                next
                  case (Suc n) with i s'.lowlink_path_finished[OF p(1), where j=i] have 
                    "u \<in> dom (finished ?s)" by simp
                  with u_n_fin show ?thesis by simp
                qed
                thus ?thesis ..
              qed
            qed simp
          qed
          finally show ?thesis .
        qed
      } note aux = this
      
      with cross_back_edge show ?case by (auto simp: pw_leof_iff)
    next
      case (finish s s' u) then interpret Tarjan_invar where s=s by simp
      from finish have [simp]:
        "discovered s' = discovered s"
        "finished s' = (finished s)(u\<mapsto>counter s)"
        "tree_edges s' = tree_edges s"
        "back_edges s' = back_edges s"
        "cross_edges s' = cross_edges s"
        "lowlink s' = lowlink s" "tj_stack s' = tj_stack s"
        by simp_all

      from finish hd_in_set stack_discovered have u_disc: "u \<in> dom (discovered s)" by blast

      {
        fix w :: "'v"
        fix x

        let ?s = "s'\<lparr>state.more := x\<rparr>"
        let ?L = "\<delta> s ` lowlink_set s w"
        let ?Lu = "\<delta> s ` lowlink_set s u"
        let ?L' = "\<delta> s ` lowlink_set ?s w"

        assume TRANS: "\<And>\<Psi>. tarjan_fin u s' \<le>\<^sub>n SPEC \<Psi> \<Longrightarrow> \<Psi> x"
          and inv': "DFS_invar G tarjan_params ?s"
          and w_disc: "w \<in> dom (discovered ?s)"

        from inv' interpret s':Tarjan_invar where s="?s" by simp
     
        have ll_sub: "lowlink_set s w \<subseteq> lowlink_set ?s w"
          unfolding lowlink_set_def lowlink_path_def
          by auto
      
        have ll_sub_rev: "lowlink_set ?s w \<subseteq> lowlink_set s w \<union> lowlink_set s u"
        proof
          fix ll
          assume ll: "ll \<in> lowlink_set ?s w"
          hence "ll = w \<or> (\<exists>p. lowlink_path ?s w p ll)" by (auto simp add: lowlink_set_def)
          thus "ll \<in> lowlink_set s w \<union> lowlink_set s u" 
          proof (rule disjE1)
            assume "ll = w" with w_disc show ?thesis by (auto simp add: lowlink_set_def)
          next
            assume "ll \<noteq> w"
            assume "\<exists>p. lowlink_path ?s w p ll"
            then guess p .. note p = this

            hence [simp]: "p\<noteq>[]" by (simp add: lowlink_path_def)
    
            from p have "hd p = w" by (auto simp add: lowlink_path_def path_hd)
            
            show ?thesis
            proof (cases "u \<in> set p")
              case False hence "lowlink_path s w p ll"
                using p by (auto simp add: lowlink_path_def)
              with ll show ?thesis by (auto simp add: lowlink_set_def)
            next
              case True
              then obtain i where i: "i < length p" "p!i = u"
                by (metis in_set_conv_nth)
              moreover
              let ?dp = "drop i p"

              from i have "?dp \<noteq> []" by simp

              from i have "hd ?dp = u" by (simp add: hd_drop_conv_nth)
              moreover from i have "last ?dp = last p" by simp
              moreover {
                fix k
                assume "1 < length ?dp"
                and  "k < length ?dp - 1"

                hence l: "1 < length p" "k+i < length p - 1" by (auto)
                with p have "(p!(k+i), p!Suc (k+i)) \<in> tree_edges s" by (auto simp add: lowlink_path_def)
                moreover from l have i: "i+k \<le> length p" "i+Suc k \<le> length p" by simp_all
                ultimately have  "(?dp!k,?dp!Suc k) \<in> tree_edges s" by (simp add: add.commute)
              } note aux = this
              moreover {
                assume *: "1 < length ?dp"
                hence l: "1 + i < length p" by simp
                with s'.lowlink_path_finished[OF p] have "p ! (1+i) \<in> dom (finished ?s)" by auto
                moreover from l have "i+1\<le>length p" by simp
                ultimately have "?dp!1 \<in> dom (finished ?s)" by simp
                moreover from aux[of 0] * have "(?dp!0,?dp!Suc 0) \<in> tree_edges s" by simp
                with \<open>hd ?dp = u\<close> hd_conv_nth[of "?dp"] * have "(u,?dp!Suc 0) \<in> tree_edges s" by simp
                with no_self_loop_in_tree have "?dp!1 \<noteq> u" by auto
                ultimately have "?dp!1 \<in> dom (finished s)" by simp
              }
              moreover 
                from p have P: "path E w p ll" by (simp add: lowlink_path_def)

                have "p = (take i p)@?dp" by simp
                with P path_conc_conv obtain x where p': "path E x ?dp ll" "path E w (take i p) x" by metis
                with \<open>?dp \<noteq> []\<close> path_hd have "hd ?dp = x" by metis
                with \<open>hd ?dp = u\<close> p' have u_path: "path E u ?dp ll" and path_u: "path E w (take i p) u" by metis+

              ultimately have "lowlink_path s u ?dp ll" using p by (simp add: lowlink_path_def)
              moreover from u_path path_is_trancl \<open>?dp \<noteq> []\<close> have "(u,ll) \<in> E\<^sup>+" by force
              moreover { from ll \<open>ll \<noteq> w\<close> have "(ll,w) \<in> E\<^sup>+" by (auto simp add: lowlink_set_def)
                also from path_u path_is_rtrancl have "(w,u) \<in> E\<^sup>*" by metis
                finally have "(ll,u)\<in>E\<^sup>+" .
              }
              moreover note ll u_disc
              ultimately have "ll \<in> lowlink_set s u" unfolding lowlink_set_def by auto
              thus ?thesis by auto
            qed
          qed
        qed
        hence ll_sub_rev': "?L' \<subseteq> ?L \<union> ?Lu" by auto

        have ref_ne: "stack ?s \<noteq> [] \<Longrightarrow> 
             lowlink ?s = (lowlink s)(hd (stack ?s) \<mapsto> min (\<zeta> s (hd (stack ?s))) (\<zeta> s u))"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by refine_vcg simp_all
        
        have ref_e: "stack ?s = [] \<Longrightarrow> lowlink ?s = lowlink s"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by refine_vcg simp_all

        have ref_tj: "\<zeta> s u \<noteq> \<delta> s u \<Longrightarrow> tj_stack ?s = tj_stack s"
          apply (rule TRANS)
          unfolding tarjan_fin_def tj_stack_pop_def
          by refine_vcg simp_all

        have "\<zeta> ?s w = LowLink ?s w"
        proof (cases "w = hd (stack ?s) \<and> stack ?s \<noteq> []")
          case True note all_True = this
          with ref_ne have *: "\<zeta> ?s w = min (\<zeta> s w) (\<zeta> s u)" by simp
          show ?thesis
          proof (cases "\<zeta> s u < \<zeta> s w")
            case False with * finish w_disc have "\<zeta> ?s w = LowLink s w" by simp
            also have "LowLink s w = LowLink ?s w"
            proof (rule LowLink_eqI[OF inv' _ ll_sub ll_sub_rev])
              from w_disc show "w \<in> dom (discovered s)" by simp
              fix ll assume "ll \<in> lowlink_set s u" 
              hence "LowLink s u \<le> \<delta> s ll" by simp
              moreover from False finish w_disc u_disc have "LowLink s w \<le> LowLink s u" by simp
              ultimately show "LowLink s w \<le> \<delta> ?s ll" by simp
            qed simp
            finally show ?thesis .
          next
            case True note \<zeta>rel = this
            have "LowLink s u \<in> ?L'"
            proof -
              from all_True finish have w_tl: "w\<in>set (tl (stack s))" by auto

              obtain ll where ll: "ll \<in> lowlink_set s u" "\<delta> s ll = LowLink s u"
                using Min_in[of ?Lu] lowlink_set_finite lowlink_set_not_empty u_disc
                by fastforce
              have "ll \<in> lowlink_set ?s w"
              proof (cases "\<delta> s u = \<zeta> s u")
                case True
                moreover from w_tl finish tl_lt_stack_hd_discover have "\<delta> s w < \<delta> s u" by simp
                moreover from w_disc have "LowLink s w \<le> \<delta> s w" by (simp add: LowLink_le_disc)
                with w_disc finish have "\<zeta> s w \<le> \<delta> s w" by simp
                moreover note \<zeta>rel
                ultimately have False by force
                thus ?thesis ..
              next
                case False with u_disc finish ll have "u \<noteq> ll" by auto
                with ll have
                  e: "(ll,u) \<in> E\<^sup>+" "(u,ll) \<in> E\<^sup>+" and
                  p: "\<exists>p. lowlink_path s u p ll" and
                  ll_disc: "ll \<in> dom (discovered s)"
                  by (auto simp: lowlink_set_def)

                from p have p': "\<exists>p. lowlink_path ?s u p ll"
                  unfolding lowlink_path_def
                  by auto
                from w_tl tl_stack_hd_tree_path finish have T: "(w,u) \<in> (tree_edges ?s)\<^sup>+" by simp
                with s'.lowlink_path_tree_prepend all_True p' have "\<exists>p. lowlink_path ?s w p ll" by blast
                moreover from T trancl_mono_mp[OF s'.tree_edges_ssE] have "(w,u) \<in> E\<^sup>+" by blast
                with e have "(w,ll) \<in> E\<^sup>+" by simp
                moreover {
                  note e(1)
                  also from finish False ref_tj have "tj_stack ?s = tj_stack s" by simp
                  with hd_in_set finish stack_ss_tj_stack have "u \<in> set (tj_stack ?s)" by auto
                  with s'.tj_stack_reach_stack obtain x where x: "x \<in> set (stack ?s)" "(u,x) \<in> E\<^sup>*" by blast
                  note this(2)
                  also have "(x,w) \<in> E\<^sup>*"
                  proof (rule rtrancl_eq_or_trancl[THEN iffD2], safe)
                    assume "x \<noteq> w" with all_True x have "x \<in> set (tl (stack ?s))" by (cases "stack ?s") auto
                    with s'.tl_stack_hd_tree_path all_True have "(x,w) \<in> (tree_edges s)\<^sup>+" by auto
                    with trancl_mono_mp[OF tree_edges_ssE] show "(x,w) \<in> E\<^sup>+" by simp
                  qed
                  finally have "(ll,w) \<in> E\<^sup>+" .
                }
                moreover note ll_disc
                ultimately show ?thesis by (simp add: lowlink_set_def)
              qed               
              hence "\<delta> s ll \<in> ?L'" by auto
              with ll show ?thesis by simp
            qed
            hence "LowLink ?s w \<le> LowLink s u" 
              using Min_le_iff[of ?L'] s'.lowlink_set_not_empty w_disc s'.lowlink_set_finite
              by fastforce
            also from True u_disc w_disc finish have "LowLink s u < LowLink s w" by simp
            hence "Min (?L \<union> ?Lu) = LowLink s u" 
              using Min_Un[of ?L ?Lu] lowlink_set_finite lowlink_set_not_empty u_disc w_disc
              by simp
            hence "LowLink s u \<le> LowLink ?s w" 
              using Min_antimono[OF ll_sub_rev'] lowlink_set_finite s'.lowlink_set_not_empty w_disc
              by auto
            also from True u_disc finish * have "LowLink s u = \<zeta> ?s w" by simp
            finally show ?thesis ..
          qed
        next
          case False note all_False = this
          have "\<zeta> ?s w = \<zeta> s w"
          proof (cases "stack ?s = []")
            case True with ref_e show ?thesis by simp
          next
            case False with all_False have "w \<noteq> hd (stack ?s)" by simp
            with False ref_ne show ?thesis by simp
          qed
          also from finish have "\<zeta> s w = LowLink s w" using w_disc by simp
          also {
            fix v
            assume "v \<in> lowlink_set s u"
              and *: "v \<notin> lowlink_set s w"
            hence "v \<noteq> w" "w\<noteq>u" by (auto simp add: lowlink_set_def)
            have "v \<notin> lowlink_set ?s w"
            proof (rule notI)
              assume v: "v \<in> lowlink_set ?s w"
              hence e: "(v,w) \<in> E\<^sup>*" "(w,v) \<in> E\<^sup>*"
                and v_disc: "v \<in> dom (discovered s)" by (auto simp add: lowlink_set_def)
              
              from v \<open>v\<noteq>w\<close> obtain p where p: "lowlink_path ?s w p v" by (auto simp add: lowlink_set_def)
              hence [simp]: "p\<noteq>[]" by (simp add: lowlink_path_def)
              
              from p have "hd p = w" by (auto simp add: lowlink_path_def path_hd)
              
              show False
              proof (cases "u \<in> set p")
                case False hence "lowlink_path s w p v"
                  using p by (auto simp add: lowlink_path_def)
                with e v_disc have "v \<in> lowlink_set s w" by (auto intro: lowlink_setI)
                with * show False ..
              next
                case True
                then obtain i where i: "i < length p" "p!i = u"
                  by (metis in_set_conv_nth)
                show "False"
                proof (cases i)
                  case "0" with i have "hd p = u" by (simp add: hd_conv_nth)
                  with \<open>hd p = w\<close> \<open>w \<noteq> u\<close> show False by simp
                next
                  case (Suc n) with i p have *: "(p!n,u) \<in> tree_edges s" "n < length p"
                    unfolding lowlink_path_def
                    by auto
                  with tree_edge_imp_discovered have "p!n \<in> dom (discovered s)" by auto
                  moreover from finish hd_in_set stack_not_finished have "u \<notin> dom (finished s)" by auto
                  with * have pn_n_fin: "p!n \<notin> dom (finished s)" by (metis tree_edge_impl_parenthesis)
                  moreover from * no_self_loop_in_tree have "p!n \<noteq> u" by blast
                  ultimately have "p!n \<in> set (stack ?s)" using stack_set_def finish by (cases "stack s") auto
                  hence s_ne: "stack ?s \<noteq> []" by auto
                  with all_False have "w \<noteq> hd (stack ?s)" by simp
                  from stack_is_tree_path finish obtain v0 where
                    "path (tree_edges s) v0 (rev (stack ?s)) u"
                    by auto
                  with s_ne have "(hd (stack ?s), u) \<in> tree_edges s" by (auto simp: neq_Nil_conv path_simps)
                  with * tree_eq_rule have **: "hd (stack ?s) = p!n" by simp
                  show ?thesis
                  proof (cases n)
                    case "0" with * have "hd p = p!n" by (simp add: hd_conv_nth)
                    with \<open>hd p = w\<close> ** have "w = hd (stack ?s)" by simp
                    with \<open>w\<noteq>hd (stack ?s)\<close> show False ..
                  next
                    case (Suc m) with * ** s'.lowlink_path_finished[OF p, where j=n] have 
                      "hd (stack ?s) \<in> dom (finished ?s)" by simp
                    with hd_in_set[OF s_ne] s'.stack_not_finished show ?thesis by blast
                  qed
                qed
              qed
            qed
          } with ll_sub ll_sub_rev have "lowlink_set ?s w = lowlink_set s w" by auto
          hence "LowLink s w = LowLink ?s w" by simp
          finally show ?thesis .
        qed
      }

      with finish show ?case by (auto simp: pw_leof_iff)
    qed simp_all
  qed
end end

context Tarjan_invar begin context begin interpretation timing_syntax .

  lemmas lowlink_eq_LowLink =
    i_lowlink_eq_LowLink[THEN make_invar_thm, rule_format]

  lemma lowlink_eq_disc_iff_scc_root:
    assumes "v \<in> dom (finished s) \<or> (stack s \<noteq> [] \<and> v = hd (stack s) \<and> pending s `` {v} = {})"
    shows "\<zeta> s v = \<delta> s v \<longleftrightarrow> scc_root s v (scc_of E v)"
  proof -
    from assms have "v \<in> dom (discovered s)" using finished_discovered hd_in_set stack_discovered by blast
    hence "\<zeta> s v = LowLink s v" using lowlink_eq_LowLink by simp
    with LowLink_eq_disc_iff_scc_root[OF assms] show ?thesis by simp
  qed

  lemma nc_sccs_eq_reachable:
    assumes NC: "\<not> cond s"
    shows "reachable = \<Union>(sccs s)"
  proof
    from nc_finished_eq_reachable NC have [simp]: "reachable = dom (finished s)" by simp
    with sccs_finished show "\<Union>(sccs s) \<subseteq> reachable" by simp

    from NC have "stack s = []" by (simp add: cond_alt)
    with stacks_eq_iff have "tj_stack s = []" by simp
    with finished_ss_sccs_tj_stack show "reachable \<subseteq> \<Union>(sccs s)" by simp
  qed
end end

context Tarjan begin
  lemma tarjan_fin_nofail:
    assumes "pre_on_finish u s'"
    shows "nofail (tarjan_fin u s')"
  proof -
    from assms obtain s where s: "DFS_invar G tarjan_params s" "stack s \<noteq> []"  "u = hd (stack s)" "s' = finish u s"  "cond s" "pending s `` {u} = {}"
      by (auto simp: pre_on_finish_def)
    then interpret Tarjan_invar where s=s by simp

    from s hd_stack_in_tj_stack have "u \<in> set (tj_stack s')" by simp

    moreover from s tj_stack_distinct have "distinct (tj_stack s')" by simp
    moreover have "the (lowlink s' u) = the (discovered s' u) \<longleftrightarrow> scc_root s' u (scc_of E u)"
    proof -
      from s have "the (lowlink s' u) = the (discovered s' u) \<longleftrightarrow> the (lowlink s u) = the (discovered s u)" by simp
      also from s lowlink_eq_disc_iff_scc_root have "... \<longleftrightarrow> scc_root s u (scc_of E u)" by blast
      also from s scc_root_transfer'[where s'=s'] have "... \<longleftrightarrow> scc_root s' u (scc_of E u)" by simp
      finally show ?thesis .
    qed
    ultimately show ?thesis 
      unfolding tarjan_fin_def tj_stack_pop_def
      by simp
  qed

  sublocale DFS G tarjan_params
    by unfold_locales (simp_all add: tarjan_disc_def tarjan_back_def tarjan_fin_nofail)
end

interpretation tarjan: Tarjan_def for G .

subsection \<open>Interface\<close>
definition "tarjan G \<equiv> do {
  ASSERT (fb_graph G);
  s \<leftarrow> tarjan.it_dfs TYPE('a) G;
  RETURN (sccs s) }"

definition "tarjan_spec G \<equiv> do {
  ASSERT (fb_graph G); 
  SPEC (\<lambda>sccs.  (\<forall>scc \<in> sccs. is_scc (g_E G) scc)
              \<and> \<Union>sccs = tarjan.reachable TYPE('a) G)}"

lemma tarjan_correct:
  "tarjan G \<le> tarjan_spec G"
  unfolding tarjan_def tarjan_spec_def
proof (refine_vcg le_ASSERTI order_trans[OF DFS.it_dfs_correct])
  assume "fb_graph G"
  then interpret fb_graph G .
  interpret Tarjan ..
  show "DFS G (tarjan.tarjan_params TYPE('b) G)" ..
next
  fix s
  assume C: "DFS_invar G (tarjan.tarjan_params TYPE('b) G) s \<and> \<not> tarjan.cond TYPE('b) G s"
  then interpret Tarjan_invar G s by simp

  from sccs_are_sccs show "\<forall>scc\<in>sccs s. is_scc (g_E G) scc" .
  
  from nc_sccs_eq_reachable C show "\<Union>(sccs s) = tarjan.reachable TYPE('b) G" by simp
qed

end
