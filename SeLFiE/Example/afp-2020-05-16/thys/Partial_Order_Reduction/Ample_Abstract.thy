section \<open>Abstract Theory of Ample Set Partial Order Reduction\<close>

theory Ample_Abstract
imports
  Transition_System_Interpreted_Traces
  "Extensions/Relation_Extensions"
begin

  (*
    formalization of the abstract partial order reduction theory
    definitions and proofs adapted from
      [1] "Combining Partial Order Reductions with On-the-Fly Model-Checking"
        Doron Peled, FMSD, 1996
      [2] "Formal Verification of a Partial-Order Reduction Technique for Model Checking"
        Ching-Tsun Chou and Doron Peled, TACAS, 1996
  *)

  locale ample_base =
    transition_system_interpreted_traces ex en int ind +
    wellfounded_relation src
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
    and src :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
  begin

    definition ample_set :: "'state \<Rightarrow> 'action set \<Rightarrow> bool"
      where "ample_set q A \<equiv>
        A \<subseteq> {a. en a q} \<and>
        (A \<subset> {a. en a q} \<longrightarrow> A \<noteq> {}) \<and>
        (\<forall> a. A \<subset> {a. en a q} \<longrightarrow> a \<in> A \<longrightarrow> src (ex a q) q) \<and>
        (A \<subset> {a. en a q} \<longrightarrow> A \<subseteq> invisible) \<and>
        (\<forall> w. A \<subset> {a. en a q} \<longrightarrow> path w q \<longrightarrow> A \<inter> set w = {} \<longrightarrow> Ind A (set w))"

    (* implicit in [1, 2] *)
    lemma ample_subset:
      assumes "ample_set q A"
      shows "A \<subseteq> {a. en a q}"
      using assms unfolding ample_set_def by auto
    (* implicit in [1], condition C0 in [2] *)
    lemma ample_nonempty:
      assumes "ample_set q A" "A \<subset> {a. en a q}"
      shows "A \<noteq> {}"
      using assms unfolding ample_set_def by auto
    (* condition C2 in [1, 2] *)
    lemma ample_wellfounded:
      assumes "ample_set q A" "A \<subset> {a. en a q}" "a \<in> A"
      shows "src (ex a q) q"
      using assms unfolding ample_set_def by auto
    (* condition C3' in [1], not needed in [2] *)
    lemma ample_invisible:
      assumes "ample_set q A" "A \<subset> {a. en a q}"
      shows "A \<subseteq> invisible"
      using assms unfolding ample_set_def by auto
    (* condition C1 in [1, 2] *)
    lemma ample_independent:
      assumes "ample_set q A" "A \<subset> {a. en a q}" "path w q" "A \<inter> set w = {}"
      shows "Ind A (set w)"
      using assms unfolding ample_set_def by auto

    lemma ample_en[intro]: "ample_set q {a. en a q}" unfolding ample_set_def by blast

  end

  locale ample_abstract =
    S?: transition_system_complete ex en init int +
    R: transition_system_complete ex ren init int +
    ample_base ex en int ind src
    for ex :: "'action \<Rightarrow> 'state \<Rightarrow> 'state"
    and en :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    and init :: "'state \<Rightarrow> bool"
    and int :: "'state \<Rightarrow> 'interpretation"
    and ind :: "'action \<Rightarrow> 'action \<Rightarrow> bool"
    and src :: "'state \<Rightarrow> 'state \<Rightarrow> bool"
    and ren :: "'action \<Rightarrow> 'state \<Rightarrow> bool"
    +
    assumes reduction_ample: "q \<in> nodes \<Longrightarrow> ample_set q {a. ren a q}"
  begin

    lemma reduction_words_fin:
      assumes "q \<in> nodes" "R.path w q"
      shows "S.path w q"
      using assms(2, 1) ample_subset reduction_ample by induct auto
    lemma reduction_words_inf:
      assumes "q \<in> nodes" "R.run w q"
      shows "S.run w q"
      using reduction_words_fin assms by (auto intro: words_infI_construct)

    (* lemma 3.7 in [1] *)
    lemma reduction_step:
      assumes "q \<in> nodes" "run w q"
      obtains
        (deferred) a where "ren a q" "[a] \<preceq>\<^sub>F\<^sub>I w" |
        (omitted) "{a. ren a q} \<subseteq> invisible" "Ind {a. ren a q} (sset w)"
    proof (cases "{a. en a q} = {a. ren a q}")
      case True
      have 1: "run (shd w ## sdrop 1 w) q" using assms(2) by simp
      show ?thesis
      proof (rule deferred)
        show "ren (shd w) q" using True 1 by blast
        show "[shd w] \<preceq>\<^sub>F\<^sub>I w" by simp
      qed
    next
      case False
      have 1: "{a. ren a q} \<subset> {a. en a q}" using ample_subset reduction_ample assms(1) False by auto
      show ?thesis
      proof (cases "{a. ren a q} \<inter> sset w = {}")
        case True
        show ?thesis
        proof (rule omitted)
          show "{a. ren a q} \<subseteq> invisible" using ample_invisible reduction_ample assms(1) 1 by auto
          show "Ind {a. ren a q} (sset w)"
          proof safe
            fix a b
            assume 2: "b \<in> sset w" "ren a q"
            obtain u v where 3: "w = u @- b ## v" using split_stream_first' 2(1) by this
            have 4: "Ind {a. ren a q} (set (u @ [b]))"
            proof (rule ample_independent)
              show "ample_set q {a. ren a q}" using reduction_ample assms(1) by this
              show "{a. ren a q} \<subset> {a. en a q}" using 1 by this
              show "path (u @ [b]) q" using assms(2) 3 by blast
              show "{a. ren a q} \<inter> set (u @ [b]) = {}" using True 3 by auto
            qed
            show "ind a b" using 2 3 4 by auto
          qed
        qed
      next
        case False
        obtain u a v where 2: "w = u @- a ## v" "{a. ren a q} \<inter> set u = {}" "ren a q"
          using split_stream_first[OF False] by auto
        have 3: "path u q" using assms(2) unfolding 2(1) by auto
        have 4: "Ind {a. ren a q} (set u)"
          using ample_independent reduction_ample assms(1) 1 3 2(2) by this
        have 5: "Ind (set [a]) (set u)" using 4 2(3) by simp
        have 6: "[a] @ u =\<^sub>F u @ [a]" using 5 by blast
        show ?thesis
        proof (rule deferred)
          show "ren a q" using 2(3) by this
          have "[a] \<preceq>\<^sub>F\<^sub>I [a] @- u @- v" by blast
          also have "[a] @- u @- v = ([a] @ u) @- v" by simp
          also have "([a] @ u) @- v =\<^sub>I (u @ [a]) @- v" using 6 by blast
          also have "(u @ [a]) @- v = u @- [a] @- v" by simp
          also have "\<dots> = w" unfolding 2(1) by simp
          finally show "[a] \<preceq>\<^sub>F\<^sub>I w" by this
        qed
      qed
    qed

    (* theorem 3.9 in [1] *)
    lemma reduction_chunk:
      assumes "q \<in> nodes" "run ([a] @- v) q"
      obtains b b\<^sub>1 b\<^sub>2 u
      where
        "R.path (b @ [a]) q"
        "Ind {a} (set b)" "set b \<subseteq> invisible"
        "b =\<^sub>F b\<^sub>1 @ b\<^sub>2" "b\<^sub>1 @- u =\<^sub>I v" "Ind (set b\<^sub>2) (sset u)"
    using wellfounded assms
    proof (induct q arbitrary: thesis v rule: wfP_induct_rule)
      case (less q)
      show ?case
      proof (cases "ren a q")
        case (True)
        show ?thesis
        proof (rule less(2))
          show "R.path ([] @ [a]) q" using True by auto
          show "Ind {a} (set [])" by auto
          show "set [] \<subseteq> invisible" by auto
          show "[] =\<^sub>F [] @ []" by auto
          show "[] @- v =\<^sub>I v" by auto
          show "Ind (set []) (sset v)" by auto
        qed
      next
        case (False)
        have 0: "{a. en a q} \<noteq> {a. ren a q}" using False less(4) by auto
        show ?thesis
        using less(3, 4)
        proof (cases rule: reduction_step)
          case (deferred c)
          have 1: "ren c q" using deferred(1) by simp
          have 2: "ind a c"
          proof (rule le_fininf_ind'')
            show "[a] \<preceq>\<^sub>F\<^sub>I [a] @- v" by blast
            show "[c] \<preceq>\<^sub>F\<^sub>I [a] @- v" using deferred(2) by this
            show "a \<noteq> c" using False 1 by auto
          qed
          obtain v' where 3: "[a] @- v =\<^sub>I [c] @- [a] @- v'"
          proof -
            have 10: "[c] \<preceq>\<^sub>F\<^sub>I v"
            proof (rule le_fininf_not_member')
              show "[c] \<preceq>\<^sub>F\<^sub>I [a] @- v" using deferred(2) by this
              show "c \<notin> set [a]" using False 1 by auto
            qed
            obtain v' where 11: "v =\<^sub>I [c] @- v'" using 10 by blast
            have 12: "Ind (set [a]) (set [c])" using 2 by auto
            have 13: "[a] @ [c] =\<^sub>F [c] @ [a]" using 12 by blast
            have "[a] @- v =\<^sub>I [a] @- [c] @- v'" using 11 by blast
            also have "\<dots> = ([a] @ [c]) @- v'" by simp
            also have "\<dots> =\<^sub>I ([c] @ [a]) @- v'" using 13 by blast
            also have "\<dots> = [c] @- [a] @- v'" by simp
            finally show ?thesis using that by auto
          qed
          have 4: "run ([c] @- [a] @- v') q" using eq_inf_word 3 less(4) by this
          show ?thesis
          proof (rule less(1))
            show "src (ex c q) q"
              using ample_wellfounded ample_subset reduction_ample less(3) 0 1 by blast
            have 100: "en c q" using less(4) deferred(2) le_fininf_word by auto
            show "ex c q \<in> nodes" using less(3) 100 by auto
            show "run ([a] @- v') (ex c q)" using 4 by auto
          next
            fix b b\<^sub>1 b\<^sub>2 u
            assume 5: "R.path (b @ [a]) (ex c q)"
            assume 6: "Ind {a} (set b)"
            assume 7: "set b \<subseteq> invisible"
            assume 8: "b =\<^sub>F b\<^sub>1 @ b\<^sub>2"
            assume 9: "b\<^sub>1 @- u =\<^sub>I v'"
            assume 10: "Ind (set b\<^sub>2) (sset u)"
            show "thesis"
            proof (rule less(2))
              show "R.path (([c] @ b) @ [a]) q" using 1 5 by auto
              show "Ind {a} (set ([c] @ b))" using 6 2 by auto
              have 11: "c \<in> invisible"
                using ample_invisible ample_subset reduction_ample less(3) 0 1 by blast
              show "set ([c] @ b) \<subseteq> invisible" using 7 11 by auto
              have "[c] @ b =\<^sub>F [c] @ b\<^sub>1 @ b\<^sub>2" using 8 by blast
              also have "[c] @ b\<^sub>1 @ b\<^sub>2 = ([c] @ b\<^sub>1) @ b\<^sub>2" by simp
              finally show "[c] @ b =\<^sub>F ([c] @ b\<^sub>1) @ b\<^sub>2" by this
              show "([c] @ b\<^sub>1) @- u =\<^sub>I v"
              proof -
                have 10: "Ind (set [a]) (set [c])" using 2 by auto
                have 11: "[a] @ [c] =\<^sub>F [c] @ [a]" using 10 by blast
                have "[a] @- v =\<^sub>I [c] @- [a] @- v'" using 3 by this
                also have "\<dots> = ([c] @ [a]) @- v'" by simp
                also have "\<dots> =\<^sub>I ([a] @ [c]) @- v'" using 11 by blast
                also have "\<dots> = [a] @- [c] @- v'" by simp
                finally have 12: "[a] @- v =\<^sub>I [a] @- [c] @- v'" by this
                have 12: "v =\<^sub>I [c] @- v'" using 12 by blast
                have "([c] @ b\<^sub>1) @- u = [c] @- b\<^sub>1 @- u" by simp
                also have "\<dots> =\<^sub>I [c] @- v'" using 9 by blast
                also have "\<dots> =\<^sub>I v" using 12 by blast
                finally show ?thesis by this
              qed
              show "Ind (set b\<^sub>2) (sset u)" using 10 by this
            qed
          qed
        next
          case (omitted)
          have 1: "{a. ren a q} \<subseteq> invisible" using omitted(1) by simp
          have 2: "Ind {a. ren a q} (sset ([a] @- v))" using omitted(2) by simp
          obtain c where 3: "ren c q"
          proof -
            have 1: "en a q" using less(4) by auto
            show ?thesis using reduction_ample ample_nonempty less(3) 1 that by blast
          qed
          have 4: "Ind (set [c]) (sset ([a] @- v))" using 2 3 by auto
          have 6: "path [c] q" using reduction_ample ample_subset less(3) 3 by auto
          have 7: "run ([a] @- v) (target [c] q)" using diamond_fin_word_inf_word 4 6 less(4) by this
          show ?thesis
          proof (rule less(1))
            show "src (ex c q) q"
              using reduction_ample ample_wellfounded ample_subset less(3) 0 3 by blast
            show "ex c q \<in> nodes" using less(3) 6 by auto
            show "run ([a] @- v) (ex c q)" using 7 by auto
          next
            fix b s b\<^sub>1 b\<^sub>2 u
            assume 5: "R.path (b @ [a]) (ex c q)"
            assume 6: "Ind {a} (set b)"
            assume 7: "set b \<subseteq> invisible"
            assume 8: "b =\<^sub>F b\<^sub>1 @ b\<^sub>2"
            assume 9: "b\<^sub>1 @- u =\<^sub>I v"
            assume 10: "Ind (set b\<^sub>2) (sset u)"
            show "thesis"
            proof (rule less(2))
              show "R.path (([c] @ b) @ [a]) q" using 3 5 by auto
              show "Ind {a} (set ([c] @ b))"
              proof -
                have 1: "ind c a" using 4 by simp
                have 2: "ind a c" using independence_symmetric 1 by this
                show ?thesis using 6 2 by auto
              qed
              have 11: "c \<in> invisible" using 1 3 by auto
              show "set ([c] @ b) \<subseteq> invisible" using 7 11 by auto
              have 12: "Ind (set [c]) (set b\<^sub>1)"
              proof -
                have 1: "set b\<^sub>1 \<subseteq> sset v" using 9 by force
                have 2: "Ind (set [c]) (sset v)" using 4 by simp
                show ?thesis using 1 2 by auto
              qed
              have "[c] @ b =\<^sub>F [c] @ b\<^sub>1 @ b\<^sub>2" using 8 by blast
              also have "\<dots> = ([c] @ b\<^sub>1) @ b\<^sub>2" by simp
              also have "\<dots> =\<^sub>F (b\<^sub>1 @ [c]) @ b\<^sub>2" using 12 by blast
              also have "\<dots> = b\<^sub>1 @ [c] @ b\<^sub>2" by simp
              finally show "[c] @ b =\<^sub>F b\<^sub>1 @ [c] @ b\<^sub>2" by this
              show "b\<^sub>1 @- u =\<^sub>I v" using 9 by this
              have 13: "Ind (set [c]) (sset u)"
              proof -
                have 1: "sset u \<subseteq> sset v" using 9 by force
                have 2: "Ind (set [c]) (sset v)" using 4 by simp
                show ?thesis using 1 2 by blast
              qed
              show "Ind (set ([c] @ b\<^sub>2)) (sset u)" using 10 13 by auto
            qed
          qed
        qed
      qed
    qed

    (*
      q: initial state
      v\<^sub>1: operations of the original run processed so far
      v\<^sub>2: operations of the original run remaining
      l: operations executed in the reduced run, but not yet in the original run
      w: reduced run processed so far
      w\<^sub>1: selected reduced run processed so far
      w\<^sub>2: unselected reduced run processed so far
      u: continuation of w
    *)
    inductive reduced_run :: "'state \<Rightarrow> 'action list \<Rightarrow> 'action stream \<Rightarrow> 'action list \<Rightarrow>
      'action list \<Rightarrow> 'action list \<Rightarrow> 'action list \<Rightarrow> 'action stream \<Rightarrow> bool"
      where
        init: "reduced_run q [] v [] [] [] [] v" |
        absorb: "reduced_run q v\<^sub>1 ([a] @- v\<^sub>2) l w w\<^sub>1 w\<^sub>2 u \<Longrightarrow> a \<in> set l \<Longrightarrow>
          reduced_run q (v\<^sub>1 @ [a]) v\<^sub>2 (remove1 a l) w w\<^sub>1 w\<^sub>2 u" |
        extend: "reduced_run q v\<^sub>1 ([a] @- v\<^sub>2) l w w\<^sub>1 w\<^sub>2 u \<Longrightarrow> a \<notin> set l \<Longrightarrow>
          R.path (b @ [a]) (target w q) \<Longrightarrow>
          Ind {a} (set b) \<Longrightarrow> set b \<subseteq> invisible \<Longrightarrow>
          b =\<^sub>F b\<^sub>1 @ b\<^sub>2 \<Longrightarrow> [a] @- b\<^sub>1 @- u' =\<^sub>I u \<Longrightarrow> Ind (set b\<^sub>2) (sset u') \<Longrightarrow>
          reduced_run q (v\<^sub>1 @ [a]) v\<^sub>2 (l @ b\<^sub>1) (w @ b @ [a]) (w\<^sub>1 @ b\<^sub>1 @ [a]) (w\<^sub>2 @ b\<^sub>2) u'"

    lemma reduced_run_words_fin:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "R.path w q"
      using assms by induct auto

    lemma reduced_run_invar_2:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "v\<^sub>2 =\<^sub>I l @- u"
    using assms
    proof induct
      case (init q v)
      show ?case by simp
    next
      case (absorb q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u)
      obtain l\<^sub>1 l\<^sub>2 where 10: "l = l\<^sub>1 @ [a] @ l\<^sub>2" "a \<notin> set l\<^sub>1"
        using split_list_first[OF absorb(3)] by auto
      have 11: "Ind {a} (set l\<^sub>1)"
      proof (rule le_fininf_ind')
        show "[a] \<preceq>\<^sub>F\<^sub>I l @- u" using absorb(2) by auto
        show "l\<^sub>1 \<preceq>\<^sub>F\<^sub>I l @- u" unfolding 10(1) by auto
        show "a \<notin> set l\<^sub>1" using 10(2) by this
      qed
      have 12: "Ind (set [a]) (set l\<^sub>1)" using 11 by auto
      have "[a] @ remove1 a l = [a] @ l\<^sub>1 @ l\<^sub>2" unfolding 10(1) remove1_append using 10(2) by auto
      also have "\<dots> =\<^sub>F ([a] @ l\<^sub>1) @ l\<^sub>2" by simp
      also have "\<dots> =\<^sub>F (l\<^sub>1 @ [a]) @ l\<^sub>2" using 12 by blast
      also have "\<dots> = l" unfolding 10(1) by simp
      finally have 13: "[a] @ remove1 a l =\<^sub>F l" by this
      have "[a] @- remove1 a l @- u = ([a] @ remove1 a l) @- u" unfolding conc_conc by simp
      also have "\<dots> =\<^sub>I l @- u" using 13 by blast
      also have "\<dots> =\<^sub>I [a] @- v\<^sub>2" using absorb(2) by auto
      finally show ?case by blast
    next
      case (extend q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u b b\<^sub>1 b\<^sub>2 u')
      have 11: "Ind {a} (set l)"
      proof (rule le_fininf_ind')
        show "[a] \<preceq>\<^sub>F\<^sub>I l @- u" using extend(2) by auto
        show "l \<preceq>\<^sub>F\<^sub>I l @- u" by auto
        show "a \<notin> set l" using extend(3) by this
      qed
      have 11: "Ind (set [a]) (set l)" using 11 by auto
      have 12: "eq_fin ([a] @ l) (l @ [a])" using 11 by blast
      have 131: "set b\<^sub>1 \<subseteq> set b" using extend(7) by auto
      have 132: "Ind (set [a]) (set b)" using extend(5) by auto
      have 13: "Ind (set [a]) (set b\<^sub>1)" using 131 132 by auto
      have 14: "eq_fin ([a] @ b\<^sub>1) (b\<^sub>1 @ [a])" using 13 by blast
      have "[a] @- ((l @ b\<^sub>1) @- u') = ([a] @ l) @- b\<^sub>1 @- u'" by simp
      also have "eq_inf \<dots> ((l @ [a]) @- b\<^sub>1 @- u')" using 12 by blast
      also have "\<dots> = l @- [a] @- b\<^sub>1 @- u'" by simp
      also have "eq_inf \<dots> (l @- u)" using extend(8) by blast
      also have "eq_inf \<dots> ([a] @- v\<^sub>2)" using extend(2) by auto
      finally show ?case by blast
    qed

    lemma reduced_run_invar_1:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "v\<^sub>1 @ l =\<^sub>F w\<^sub>1"
    using assms
    proof induct
      case (init q v)
      show ?case by simp
    next
      case (absorb q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u)
      have 1: "[a] @- v\<^sub>2 =\<^sub>I l @- u" using reduced_run_invar_2 absorb(1) by this
      obtain l\<^sub>1 l\<^sub>2 where 10: "l = l\<^sub>1 @ [a] @ l\<^sub>2" "a \<notin> set l\<^sub>1"
        using split_list_first[OF absorb(3)] by auto
      have 11: "Ind {a} (set l\<^sub>1)"
      proof (rule le_fininf_ind')
        show "[a] \<preceq>\<^sub>F\<^sub>I l @- u" using 1 by auto
        show "l\<^sub>1 \<preceq>\<^sub>F\<^sub>I l @- u" unfolding 10(1) by auto
        show "a \<notin> set l\<^sub>1" using 10(2) by this
      qed
      have 12: "Ind (set [a]) (set l\<^sub>1)" using 11 by auto
      have "[a] @ remove1 a l = [a] @ l\<^sub>1 @ l\<^sub>2" unfolding 10(1) remove1_append using 10(2) by auto
      also have "\<dots> =\<^sub>F ([a] @ l\<^sub>1) @ l\<^sub>2" by simp
      also have "\<dots> =\<^sub>F (l\<^sub>1 @ [a]) @ l\<^sub>2" using 12 by blast
      also have "\<dots> = l" unfolding 10(1) by simp
      finally have 13: "[a] @ remove1 a l =\<^sub>F l" by this
      have "w\<^sub>1 =\<^sub>F v\<^sub>1 @ l" using absorb(2) by auto
      also have "\<dots> =\<^sub>F v\<^sub>1 @ ([a] @ remove1 a l)" using 13 by blast
      also have "\<dots> = (v\<^sub>1 @ [a]) @ remove1 a l" by simp
      finally show ?case by auto
    next
      case (extend q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u b b\<^sub>1 b\<^sub>2 u')
      have 1: "[a] @- v\<^sub>2 =\<^sub>I l @- u" using reduced_run_invar_2 extend(1) by this
      have 11: "Ind {a} (set l)"
      proof (rule le_fininf_ind')
        show "[a] \<preceq>\<^sub>F\<^sub>I l @- u" using 1 by auto
        show "l \<preceq>\<^sub>F\<^sub>I l @- u" by auto
        show "a \<notin> set l" using extend(3) by auto
      qed
      have 11: "Ind (set [a]) (set l)" using 11 by auto
      have 12: "eq_fin ([a] @ l) (l @ [a])" using 11 by blast
      have 131: "set b\<^sub>1 \<subseteq> set b" using extend(7) by auto
      have 132: "Ind (set [a]) (set b)" using extend(5) by auto
      have 13: "Ind (set [a]) (set b\<^sub>1)" using 131 132 by auto
      have 14: "eq_fin ([a] @ b\<^sub>1) (b\<^sub>1 @ [a])" using 13 by blast
      have "eq_fin (w\<^sub>1 @ b\<^sub>1 @ [a]) (w\<^sub>1 @ [a] @ b\<^sub>1)" using 14 by blast
      also have "eq_fin \<dots> ((v\<^sub>1 @ l) @ [a] @ b\<^sub>1)" using extend(2) by blast
      also have "eq_fin \<dots> (v\<^sub>1 @ (l @ [a]) @ b\<^sub>1)" by simp
      also have "eq_fin \<dots> (v\<^sub>1 @ ([a] @ l) @ b\<^sub>1)" using 12 by blast
      also have "\<dots> = (v\<^sub>1 @ [a]) @ l @ b\<^sub>1" by simp
      finally show ?case by auto
    qed

    lemma reduced_run_invisible:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "set w\<^sub>2 \<subseteq> invisible"
    using assms
    proof induct
      case (init q v)
      show ?case by simp
    next
      case (absorb q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u)
      show ?case using absorb(2) by this
    next
      case (extend q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u b b\<^sub>1 b\<^sub>2 u')
      have 1: "set b\<^sub>2 \<subseteq> set b" using extend(7) by auto
      show ?case unfolding set_append using extend(2) extend(6) 1 by blast
    qed

    lemma reduced_run_ind:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "Ind (set w\<^sub>2) (sset u)"
    using assms
    proof induct
      case (init q v)
      show ?case by simp
    next
      case (absorb q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u)
      show ?case using absorb(2) by this
    next
      case (extend q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u b b\<^sub>1 b\<^sub>2 u')
      have 1: "sset u' \<subseteq> sset u" using extend(8) by force
      show ?case using extend(2) extend(9) 1 unfolding set_append by blast
    qed

    lemma reduced_run_decompose:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "w =\<^sub>F w\<^sub>1 @ w\<^sub>2"
    using assms
    proof induct
      case (init q v)
      show ?case by simp
    next
      case (absorb q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u)
      show ?case using absorb(2) by this
    next
      case (extend q v\<^sub>1 a v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u b b\<^sub>1 b\<^sub>2 u')
      have 1: "Ind (set [a]) (set b\<^sub>2)" using extend(5) extend(7) by auto
      have 2: "Ind (set w\<^sub>2) (set (b\<^sub>1 @ [a]))"
      proof -
        have 1: "Ind (set w\<^sub>2) (sset u)" using reduced_run_ind extend(1) by this
        have 2: "u =\<^sub>I [a] @- b\<^sub>1 @- u'" using extend(8) by auto
        have 3: "sset u = sset ([a] @- b\<^sub>1 @- u')" using 2 by blast
        show ?thesis unfolding set_append using 1 3 by simp
      qed
      have "w @ b @ [a] =\<^sub>F (w\<^sub>1 @ w\<^sub>2) @ b @ [a]" using extend(2) by blast
      also have "\<dots> =\<^sub>F (w\<^sub>1 @ w\<^sub>2) @ (b\<^sub>1 @ b\<^sub>2) @ [a]" using extend(7) by blast
      also have "\<dots> = w\<^sub>1 @ w\<^sub>2 @ b\<^sub>1 @ (b\<^sub>2 @ [a])" by simp
      also have "\<dots> =\<^sub>F w\<^sub>1 @ w\<^sub>2 @ b\<^sub>1 @ ([a] @ b\<^sub>2)" using 1 by blast
      also have "\<dots> =\<^sub>F w\<^sub>1 @ (w\<^sub>2 @ (b\<^sub>1 @ [a])) @ b\<^sub>2" by simp
      also have "\<dots> =\<^sub>F w\<^sub>1 @ ((b\<^sub>1 @ [a]) @ w\<^sub>2) @ b\<^sub>2" using 2 by blast
      also have "\<dots> =\<^sub>F (w\<^sub>1 @ b\<^sub>1 @ [a]) @ w\<^sub>2 @ b\<^sub>2" by simp
      finally show ?case by this
    qed

    lemma reduced_run_project:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "project visible w\<^sub>1 = project visible w"
    proof -
      have 1: "w\<^sub>1 @ w\<^sub>2 =\<^sub>F w" using reduced_run_decompose assms by auto
      have 2: "set w\<^sub>2 \<subseteq> invisible" using reduced_run_invisible assms by this
      have 3: "project visible w\<^sub>2 = []" unfolding filter_empty_conv using 2 by auto
      have "project visible w\<^sub>1 = project visible w\<^sub>1 @ project visible w\<^sub>2" using 3 by simp
      also have "\<dots> = project visible (w\<^sub>1 @ w\<^sub>2)" by simp
      also have "\<dots> = list_of (lproject visible (llist_of (w\<^sub>1 @ w\<^sub>2)))" by simp
      also have "\<dots> = list_of (lproject visible (llist_of w))"
        using eq_fin_lproject_visible 1 by metis
      also have "\<dots> = project visible w" by simp
      finally show ?thesis by this
    qed

    lemma reduced_run_length_1:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "length v\<^sub>1 \<le> length w\<^sub>1"
      using reduced_run_invar_1 assms by force
    lemma reduced_run_length:
      assumes "reduced_run q v\<^sub>1 v\<^sub>2 l w w\<^sub>1 w\<^sub>2 u"
      shows "length v\<^sub>1 \<le> length w"
    proof -
      have "length v\<^sub>1 \<le> length w\<^sub>1" using reduced_run_length_1 assms by this
      also have "\<dots> \<le> length w" using reduced_run_decompose assms by force
      finally show ?thesis by this
    qed

    lemma reduced_run_step:
      assumes "q \<in> nodes" "run (v\<^sub>1 @- [a] @- v\<^sub>2) q"
      assumes "reduced_run q v\<^sub>1 ([a] @- v\<^sub>2) l w w\<^sub>1 w\<^sub>2 u"
      obtains l' w' w\<^sub>1' w\<^sub>2' u'
      where "reduced_run q (v\<^sub>1 @ [a]) v\<^sub>2 l' (w @ w') (w\<^sub>1 @ w\<^sub>1') (w\<^sub>2 @ w\<^sub>2') u'"
    proof (cases "a \<in> set l")
      case True
      show ?thesis
      proof (rule that, rule absorb)
        show "reduced_run q v\<^sub>1 ([a] @- v\<^sub>2) l (w @ []) (w\<^sub>1 @ []) (w\<^sub>2 @ []) u" using assms(3) by simp
        show "a \<in> set l" using True by this
      qed
    next
      case False
      have 1: "v\<^sub>1 @ l =\<^sub>F w\<^sub>1" using reduced_run_invar_1 assms(3) by this
      have 2: "[a] @- v\<^sub>2 =\<^sub>I l @- u" using reduced_run_invar_2 assms(3) by this
      have 3: "w =\<^sub>F w\<^sub>1 @ w\<^sub>2" using reduced_run_decompose assms(3) by this
      have "v\<^sub>1 @ l @ w\<^sub>2 = (v\<^sub>1 @ l) @ w\<^sub>2" by simp
      also have "\<dots> =\<^sub>F w\<^sub>1 @ w\<^sub>2" using 1 by blast
      also have "\<dots> =\<^sub>F w" using 3 by blast
      finally have 4: "v\<^sub>1 @ l @ w\<^sub>2 =\<^sub>F w" by this
      have 5: "run ((v\<^sub>1 @ l) @- w\<^sub>2 @- u) q"
      proof (rule diamond_fin_word_inf_word')
        show "Ind (set w\<^sub>2) (sset u)" using reduced_run_ind assms(3) by this
        have 6: "R.path w q" using reduced_run_words_fin assms(3) by this
        have 7: "path w q" using reduction_words_fin assms(1) 6 by auto
        show "path ((v\<^sub>1 @ l) @ w\<^sub>2) q" using eq_fin_word 4 7 by auto
        have 8: "v\<^sub>1 @- [a] @- v\<^sub>2 =\<^sub>I v\<^sub>1 @- l @- u" using 2 by blast
        show "run ((v\<^sub>1 @ l) @- u) q" using eq_inf_word assms(2) 8 by auto
      qed
      have 6: "run (w @- u) q" using eq_inf_word 4 5 by (metis eq_inf_concat_end shift_append)
      have 7: "[a] \<preceq>\<^sub>F\<^sub>I l @- u" using 2 by blast
      have 8: "[a] \<preceq>\<^sub>F\<^sub>I u" using le_fininf_not_member' 7 False by this
      obtain u' where 9: "u =\<^sub>I [a] @- u'" using 8 by rule
      have 101: "target w q \<in> nodes" using assms(1) 6 by auto
      have 10: "run ([a] @- u') (target w q)" using eq_inf_word 9 6 by blast
      obtain b b\<^sub>1 b\<^sub>2 u'' where 11:
        "R.path (b @ [a]) (target w q)"
        "Ind {a} (set b)" "set b \<subseteq> invisible"
        "b =\<^sub>F b\<^sub>1 @ b\<^sub>2" "b\<^sub>1 @- u'' =\<^sub>I u'" "Ind (set b\<^sub>2) (sset u'')"
        using reduction_chunk 101 10 by this
      show ?thesis
      proof (rule that, rule extend)
        show "reduced_run q v\<^sub>1 ([a] @- v\<^sub>2) l w w\<^sub>1 w\<^sub>2 u" using assms(3) by this
        show "a \<notin> set l" using False by this
        show "R.path (b @ [a]) (target w q)" using 11(1) by this
        show "Ind {a} (set b)" using 11(2) by this
        show "set b \<subseteq> invisible" using 11(3) by this
        show "b =\<^sub>F b\<^sub>1 @ b\<^sub>2" using 11(4) by this
        show "[a] @- b\<^sub>1 @- u'' =\<^sub>I u" using 9 11(5) by blast
        show "Ind (set b\<^sub>2) (sset u'')" using 11(6) by this
      qed
    qed

    (* theorem 3.11 in [1] *)
    lemma reduction_word:
      assumes "q \<in> nodes" "run v q"
      obtains u w
      where
        "R.run w q"
        "v =\<^sub>I u" "u \<preceq>\<^sub>I w"
        "lproject visible (llist_of_stream u) = lproject visible (llist_of_stream w)"
    proof -
      define P where "P \<equiv> \<lambda> k w w\<^sub>1. \<exists> l w\<^sub>2 u. reduced_run q (stake k v) (sdrop k v) l w w\<^sub>1 w\<^sub>2 u"
      obtain w w\<^sub>1 where 1: "\<And> k. P k (w k) (w\<^sub>1 k)" "chain w" "chain w\<^sub>1"
      proof (rule chain_construct_2'[of P])
        show "P 0 [] []" unfolding P_def using init by force
      next
        fix k w w\<^sub>1
        assume 1: "P k w w\<^sub>1"
        obtain l w\<^sub>2 u where 2: "reduced_run q (stake k v) (sdrop k v) l w w\<^sub>1 w\<^sub>2 u"
          using 1 unfolding P_def by auto
        obtain l' w' w\<^sub>1' w\<^sub>2' u' where 3:
          "reduced_run q (stake k v @ [v !! k]) (sdrop (Suc k) v) l' (w @ w') (w\<^sub>1 @ w\<^sub>1') (w\<^sub>2 @ w\<^sub>2') u'"
        proof (rule reduced_run_step)
          show "q \<in> nodes" using assms(1) by this
          show "run (stake k v @- [v !! k] @- sdrop (Suc k) v) q"
            using assms(2) by (metis shift_append stake_Suc stake_sdrop)
          show "reduced_run q (stake k v) ([v !! k] @- sdrop (Suc k) v) l w w\<^sub>1 w\<^sub>2 u"
            using 2 by (metis sdrop_simps shift.simps stream.collapse)
        qed
        show "\<exists> w' w\<^sub>1'. P (Suc k) w' w\<^sub>1' \<and> w \<le> w' \<and> w\<^sub>1 \<le> w\<^sub>1'"
          unfolding P_def using 3 by (metis prefix_fin_append stake_Suc)
        show "k \<le> length w" using reduced_run_length 2 by force
        show "k \<le> length w\<^sub>1" using reduced_run_length_1 2 by force
      qed rule
      obtain l w\<^sub>2 u where 2:
        "\<And> k. reduced_run q (stake k v) (sdrop k v) (l k) (w k) (w\<^sub>1 k) (w\<^sub>2 k) (u k)"
        using 1(1) unfolding P_def by metis
      show ?thesis
      proof
        show "R.run (Word_Prefixes.limit w) q" using reduced_run_words_fin 1(2) 2 by blast
        show "v =\<^sub>I Word_Prefixes.limit w\<^sub>1"
        proof
          show "v \<preceq>\<^sub>I Word_Prefixes.limit w\<^sub>1"
          proof (rule le_infI_chain_right')
            show "chain w\<^sub>1" using 1(3) by this
            show "\<And> k. stake k v \<preceq>\<^sub>F w\<^sub>1 k" using reduced_run_invar_1[OF 2] by auto
          qed
          show "Word_Prefixes.limit w\<^sub>1 \<preceq>\<^sub>I v"
          proof (rule le_infI_chain_left)
            show "chain w\<^sub>1" using 1(3) by this
          next
            fix k
            have "w\<^sub>1 k =\<^sub>F stake k v @ l k" using reduced_run_invar_1 2 by blast
            also have "\<dots> \<le>\<^sub>F\<^sub>I stake k v @- l k @- u k" by auto
            also have "\<dots> =\<^sub>I stake k v @- sdrop k v" using reduced_run_invar_2[OF 2] by blast
            also have "\<dots> = v" by simp
            finally show "w\<^sub>1 k \<preceq>\<^sub>F\<^sub>I v" by this
          qed
        qed
        show "Word_Prefixes.limit w\<^sub>1 \<preceq>\<^sub>I Word_Prefixes.limit w"
        proof (rule le_infI_chain_left)
          show "chain w\<^sub>1" using 1(3) by this
        next
          fix k
          have "w\<^sub>1 k \<preceq>\<^sub>F w k" using reduced_run_decompose[OF 2] by blast
          also have "\<dots> \<le>\<^sub>F\<^sub>I Word_Prefixes.limit w" using chain_prefix_limit 1(2) by this
          finally show "w\<^sub>1 k \<preceq>\<^sub>F\<^sub>I Word_Prefixes.limit w" by this
        qed
        show "lproject visible (llist_of_stream (Word_Prefixes.limit w\<^sub>1)) =
          lproject visible (llist_of_stream (Word_Prefixes.limit w))"
          using lproject_eq_limit_chain reduced_run_project 1 unfolding P_def by metis
      qed
    qed

    (* theorem 3.12 in [1] *)
    lemma reduction_equivalent:
      assumes "q \<in> nodes" "run u q"
      obtains v
      where "R.run v q" "snth (smap int (q ## trace u q)) \<approx> snth (smap int (q ## trace v q))"
    proof -
      obtain v w where 1: "R.run w q" "u =\<^sub>I v" "v \<preceq>\<^sub>I w"
        "lproject visible (llist_of_stream v) = lproject visible (llist_of_stream w)"
        using reduction_word assms by this
      show ?thesis
      proof
        show "R.run w q" using 1(1) by this
        show "snth (smap int (q ## trace u q)) \<approx> snth (smap int (q ## trace w q))"
        proof (rule execute_inf_visible)
          show "run u q" using assms(2) by this
          show "run w q" using reduction_words_inf assms(1) 1(1) by auto
          have "u =\<^sub>I v" using 1(2) by this
          also have "\<dots> \<preceq>\<^sub>I w" using 1(3) by this
          finally show "u \<preceq>\<^sub>I w" by this
          show "w \<preceq>\<^sub>I w" by simp
          have "lproject visible (llist_of_stream u) = lproject visible (llist_of_stream v)"
            using eq_inf_lproject_visible 1(2) by this
          also have "\<dots> = lproject visible (llist_of_stream w)" using 1(4) by this
          finally show "lproject visible (llist_of_stream u) = lproject visible (llist_of_stream w)" by this
        qed
      qed
    qed

    lemma reduction_language_subset: "R.language \<subseteq> S.language"
      unfolding S.language_def R.language_def using reduction_words_inf by blast

    lemma reduction_language_stuttering:
      assumes "u \<in> S.language"
      obtains v
      where "v \<in> R.language" "snth u \<approx> snth v"
    proof -
      obtain q v where 1: "u = smap int (q ## trace v q)" "init q" "S.run v q" using assms by rule
      obtain v' where 2: "R.run v' q" "snth (smap int (q ## trace v q)) \<approx> snth (smap int (q ## trace v' q))"
        using reduction_equivalent 1(2, 3) by blast
      show ?thesis
      proof (intro that R.languageI)
        show "smap int (q ## trace v' q) = smap int (q ## trace v' q)" by rule
        show "init q" using 1(2) by this
        show "R.run v' q" using 2(1) by this
        show "snth u \<approx> snth (smap int (q ## trace v' q))" unfolding 1(1) using 2(2) by this
      qed
    qed

  end

end
