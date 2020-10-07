section \<open>Interpreted Transition Systems and Traces\<close>

theory Transition_System_Interpreted_Traces
imports
  Transition_System_Traces
  "Basics/Stuttering"
begin

  locale transition_system_interpreted_traces =
    transition_system_interpreted ex en int +
    transition_system_traces ex en ind
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
    +
    assumes independence_invisible: "a \<in> visible \<Longrightarrow> b \<in> visible \<Longrightarrow> \<not> ind a b"
  begin

    lemma eq_swap_lproject_visible:
      assumes "u =\<^sub>S v"
      shows "lproject visible (llist_of u) = lproject visible (llist_of v)"
      using assms independence_invisible by (induct, auto)
    lemma eq_fin_lproject_visible:
      assumes "u =\<^sub>F v"
      shows "lproject visible (llist_of u) = lproject visible (llist_of v)"
      using assms eq_swap_lproject_visible by (induct, auto)
    lemma le_fin_lproject_visible:
      assumes "u \<preceq>\<^sub>F v"
      shows "lproject visible (llist_of u) \<le> lproject visible (llist_of v)"
    proof -
      obtain w where 1: "u @ w =\<^sub>F v" using assms by rule
      have "lproject visible (llist_of u) \<le>
        lproject visible (llist_of u) $ lproject visible (llist_of w)" by auto
      also have "\<dots> = lproject visible (llist_of (u @ w))" using lappend_llist_of_llist_of by auto
      also have "\<dots> = lproject visible (llist_of v)" using eq_fin_lproject_visible 1 by this
      finally show ?thesis by this
    qed
    lemma le_fininf_lproject_visible:
      assumes "u \<preceq>\<^sub>F\<^sub>I v"
      shows "lproject visible (llist_of u) \<le> lproject visible (llist_of_stream v)"
    proof -
      obtain w where 1: "w \<le>\<^sub>F\<^sub>I v" "u \<preceq>\<^sub>F w" using assms by rule
      have "lproject visible (llist_of u) \<le> lproject visible (llist_of w)"
        using le_fin_lproject_visible 1(2) by this
      also have "\<dots> \<le> lproject visible (llist_of_stream v)" using 1(1) by blast
      finally show ?thesis by this
    qed
    lemma le_inf_lproject_visible:
      assumes "u \<preceq>\<^sub>I v"
      shows "lproject visible (llist_of_stream u) \<le> lproject visible (llist_of_stream v)"
    proof (rule lproject_prefix_limit)
      fix w
      assume 1: "w \<le> llist_of_stream u" "lfinite w"
      have 2: "list_of w \<le>\<^sub>F\<^sub>I stream_of_llist (llist_of_stream u)" using 1 by blast
      have 3: "list_of w \<preceq>\<^sub>F\<^sub>I v" using assms 2 by auto
      have "lproject visible w = lproject visible (llist_of (list_of w))" using 1(2) by simp
      also have "\<dots> \<le> lproject visible (llist_of_stream v)" using le_fininf_lproject_visible 3 by this
      finally show "lproject visible w \<le> lproject visible (llist_of_stream v)" by this
    qed
    lemma eq_inf_lproject_visible:
      assumes "u =\<^sub>I v"
      shows "lproject visible (llist_of_stream u) = lproject visible (llist_of_stream v)"
      using le_inf_lproject_visible assms by (metis antisym eq_infE)

    lemma stutter_selection_lproject_visible:
      assumes "run u p"
      shows "stutter_selection (lift (liset visible (llist_of_stream u)))
        (llist_of_stream (smap int (p ## trace u p)))"
    proof
      show "0 \<in> lift (liset visible (llist_of_stream u))" by auto
    next
      fix k i
      assume 3: "enat (Suc k) < esize (lift (liset visible (llist_of_stream u)))"
      assume 4: "nth_least (lift (liset visible (llist_of_stream u))) k < i"
      assume 5: "i < nth_least (lift (liset visible (llist_of_stream u))) (Suc k)"
      have 6: "int ((p ## trace u p) !! nth_least (lift (liset visible (llist_of_stream u))) k) =
        int ((p ## trace u p) !! i)"
      proof (rule execute_inf_word_invisible)
        show "run u p" using assms by this
        show "nth_least (lift (liset visible (llist_of_stream u))) k \<le> i" using 4 by auto
      next
        fix j
        assume 6: "nth_least (lift (liset visible (llist_of_stream u))) k \<le> j"
        assume 7: "j < i"
        have 8: "Suc j \<notin> lift (liset visible (llist_of_stream u))"
        proof (rule nth_least_not_contains)
          show "enat (Suc k) < esize (lift (liset visible (llist_of_stream u)))" using 3 by this
          show "nth_least (lift (liset visible (llist_of_stream u))) k < Suc j" using 6 by auto
          show "Suc j < nth_least (lift (liset visible (llist_of_stream u))) (Suc k)" using 5 7 by simp
        qed
        have 9: "j \<notin> liset visible (llist_of_stream u)" using 8 by auto
        show "u !! j \<notin> visible" using 9 by auto
      qed
      show "llist_of_stream (smap int (p ## trace u p)) ? i = llist_of_stream (smap int (p ## trace u p)) ?
        nth_least (lift (liset visible (llist_of_stream u))) k"
        using 6 by (metis lnth_list_of_stream snth_smap)
    next
      fix i
      assume 1: "finite (lift (liset visible (llist_of_stream u)))"
      assume 3: "Max (lift (liset visible (llist_of_stream u))) < i"
      have 4: "int ((p ## trace u p) !! Max (lift (liset visible (llist_of_stream u)))) =
        int ((p ## trace u p) !! i)"
      proof (rule execute_inf_word_invisible)
        show "run u p" using assms by this
        show "Max (lift (liset visible (llist_of_stream u))) \<le> i" using 3 by auto
      next
        fix j
        assume 6: "Max (lift (liset visible (llist_of_stream u))) \<le> j"
        assume 7: "j < i"
        have 8: "Suc j \<notin> lift (liset visible (llist_of_stream u))"
        proof (rule ccontr)
          assume 9: "\<not> Suc j \<notin> lift (liset visible (llist_of_stream u))"
          have 10: "Suc j \<in> lift (liset visible (llist_of_stream u))" using 9 by simp
          have 11: "Suc j \<le> Max (lift (liset visible (llist_of_stream u)))" using Max_ge 1 10 by this
          show "False" using 6 11 by auto
        qed
        have 9: "j \<notin> liset visible (llist_of_stream u)" using 8 by auto
        show "u !! j \<notin> visible" using 9 by auto
      qed
      show "llist_of_stream (smap int (p ## trace u p)) ? i = llist_of_stream (smap int (p ## trace u p)) ?
        Max (lift (liset visible (llist_of_stream u)))" using 4 by (metis lnth_list_of_stream snth_smap)
    qed

    lemma execute_fin_visible:
      assumes "path u q" "path v q" "u \<preceq>\<^sub>F\<^sub>I w" "v \<preceq>\<^sub>F\<^sub>I w"
      assumes "project visible u = project visible v"
      shows "int (target u q) = int (target v q)"
    proof -
      obtain w' where 1: "u \<preceq>\<^sub>F w'" "v \<preceq>\<^sub>F w'" using subsume_fin assms(3, 4) by this
      obtain u' v' where 2: "u @ u' =\<^sub>F w'" "v @ v' =\<^sub>F w'" using 1 by blast
      have "u @ u' =\<^sub>F w'" using 2(1) by this
      also have "\<dots> =\<^sub>F v @ v'" using 2(2) by blast
      finally have 3: "u @ u' =\<^sub>F v @ v'" by this
      obtain s\<^sub>1 s\<^sub>2 s\<^sub>3 where 4: "u =\<^sub>F s\<^sub>1 @ s\<^sub>2" "v =\<^sub>F s\<^sub>1 @ s\<^sub>3" "Ind (set s\<^sub>2) (set s\<^sub>3)"
        using levi_lemma 3 by this
      have 5: "project visible (s\<^sub>1 @ s\<^sub>2) = project visible (s\<^sub>1 @ s\<^sub>3)"
        using eq_fin_lproject_visible assms(5) 4(1, 2) by auto
      have 6: "project visible s\<^sub>2 = project visible s\<^sub>3" using 5 by simp
      have 7: "set (project visible s\<^sub>2) = set (project visible s\<^sub>3)" using 6 by simp
      have 8: "set s\<^sub>2 \<inter> visible = set s\<^sub>3 \<inter> visible" using 7 by auto
      have 9: "set s\<^sub>2 \<subseteq> invisible \<or> set s\<^sub>3 \<subseteq> invisible" using independence_invisible 4(3) by auto
      have 10: "set s\<^sub>2 \<subseteq> invisible" "set s\<^sub>3 \<subseteq> invisible" using 8 9 by auto
      have 11: "path s\<^sub>2 (target s\<^sub>1 q)" using eq_fin_word 4(1) assms(1) by auto
      have 12: "path s\<^sub>3 (target s\<^sub>1 q)" using eq_fin_word 4(2) assms(2) by auto
      have "int (fold ex u q) = int (fold ex (s\<^sub>1 @ s\<^sub>2) q)" using eq_fin_execute assms(1) 4(1) by simp
      also have "\<dots> = int (fold ex s\<^sub>1 q)" using execute_fin_word_invisible 11 10(1) by simp
      also have "\<dots> = int (fold ex (s\<^sub>1 @ s\<^sub>3) q)" using execute_fin_word_invisible 12 10(2) by simp
      also have "\<dots> = int (fold ex v q)" using eq_fin_execute assms(2) 4(2) by simp
      finally show ?thesis by this
    qed
    lemma execute_inf_visible:
      assumes "run u q" "run v q" "u \<preceq>\<^sub>I w" "v \<preceq>\<^sub>I w"
      assumes "lproject visible (llist_of_stream u) = lproject visible (llist_of_stream v)"
      shows "snth (smap int (q ## trace u q)) \<approx> snth (smap int (q ## trace v q))"
    proof -
      have 1: "lnth (llist_of_stream (smap int (q ## trace u q))) \<approx>
        lnth (llist_of_stream (smap int (q ## trace v q)))"
      proof
        show "linfinite (llist_of_stream (smap int (q ## trace u q)))" by simp
        show "linfinite (llist_of_stream (smap int (q ## trace v q)))" by simp
        show "stutter_selection (lift (liset visible (llist_of_stream u))) (llist_of_stream (smap int (q ## trace u q)))"
          using stutter_selection_lproject_visible assms(1) by this
        show "stutter_selection (lift (liset visible (llist_of_stream v))) (llist_of_stream (smap int (q ## trace v q)))"
          using stutter_selection_lproject_visible assms(2) by this
        show "lselect (lift (liset visible (llist_of_stream u))) (llist_of_stream (smap int (q ## trace u q))) =
          lselect (lift (liset visible (llist_of_stream v))) (llist_of_stream (smap int (q ## trace v q)))" 
        proof
          have "llength (lselect (lift (liset visible (llist_of_stream u)))
            (llist_of_stream (smap int (q ## trace u q)))) = eSuc (llength (lproject visible (llist_of_stream u)))"
            by (simp add: lselect_llength)
          also have "\<dots> = eSuc (llength (lproject visible (llist_of_stream v)))"
            unfolding assms(5) by rule
          also have "\<dots> = llength (lselect (lift (liset visible (llist_of_stream v)))
            (llist_of_stream (smap int (q ## trace v q))))" by (simp add: lselect_llength)
          finally show "llength (lselect (lift (liset visible (llist_of_stream u)))
            (llist_of_stream (smap int (q ## trace u q)))) = llength (lselect (lift (liset visible (llist_of_stream v)))
            (llist_of_stream (smap int (q ## trace v q))))" by this
        next
          fix i
          assume 1:
            "enat i < llength (lselect (lift (liset visible (llist_of_stream u)))
              (llist_of_stream (smap int (q ## trace u q))))"
            "enat i < llength (lselect (lift (liset visible (llist_of_stream v)))
              (llist_of_stream (smap int (q ## trace v q))))"
          have 2:
            "enat i \<le> llength (lproject visible (llist_of_stream u))"
            "enat i \<le> llength (lproject visible (llist_of_stream v))"
            using 1 by (simp add: lselect_llength)+
          define k where "k \<equiv> nth_least (lift (liset visible (llist_of_stream u))) i"
          define l where "l \<equiv> nth_least (lift (liset visible (llist_of_stream v))) i"
          have "lselect (lift (liset visible (llist_of_stream u))) (llist_of_stream (smap int (q ## trace u q))) ? i =
            int ((q ## trace u q) !! nth_least (lift (liset visible (llist_of_stream u))) i)"
            by (metis 1(1) lnth_list_of_stream lselect_lnth snth_smap)
          also have "\<dots> = int ((q ## trace u q) !! k)" unfolding k_def by rule
          also have "\<dots> = int ((q ## trace v q) !! l)"
          unfolding sscan_scons_snth
          proof (rule execute_fin_visible)
            show "path (stake k u) q" using assms(1) by (metis run_shift_elim stake_sdrop)
            show "path (stake l v) q" using assms(2) by (metis run_shift_elim stake_sdrop)
            show "stake k u \<preceq>\<^sub>F\<^sub>I w" "stake l v \<preceq>\<^sub>F\<^sub>I w" using assms(3, 4) by auto
            have "project visible (stake k u) =
              list_of (lproject visible (llist_of (stake k u)))" by simp
            also have "\<dots> = list_of (lproject visible (ltake (enat k) (llist_of_stream u)))"
              by (metis length_stake llength_llist_of llist_of_inf_llist_prefix lprefix_ltake prefix_fininf_prefix)
            also have "\<dots> = list_of (ltake (enat i) (lproject visible (llist_of_stream u)))"
              unfolding k_def lproject_ltake[OF 2(1)] by rule
            also have "\<dots> = list_of (ltake (enat i) (lproject visible (llist_of_stream v)))"
              unfolding assms(5) by rule
            also have "\<dots> = list_of (lproject visible (ltake (enat l) (llist_of_stream v)))"
              unfolding l_def lproject_ltake[OF 2(2)] by rule
            also have "\<dots> = project visible (stake l v)"
              by (metis length_stake lfilter_llist_of list_of_llist_of llength_llist_of
                llist_of_inf_llist_prefix lprefix_ltake prefix_fininf_prefix)
            finally show "project visible (stake k u) = project visible (stake l v)" by this
          qed
          also have "\<dots> = int ((q ## trace v q) !! nth_least (lift (liset visible (llist_of_stream v))) i)"
            unfolding l_def by simp
          also have "\<dots> = lselect (lift (liset visible (llist_of_stream v)))
            (llist_of_stream (smap int (q ## trace v q))) ? i"
            using 1 by (metis lnth_list_of_stream lselect_lnth snth_smap)
          finally show "lselect (lift (liset visible (llist_of_stream u)))
            (llist_of_stream (smap int (q ## trace u q))) ? i = lselect (lift (liset visible (llist_of_stream v)))
            (llist_of_stream (smap int (q ## trace v q))) ? i" by this
        qed
      qed
      show ?thesis using 1 by simp
    qed

  end

end
