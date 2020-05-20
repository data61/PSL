section \<open>Trace Theory\<close>

theory Traces
imports "Basics/Word_Prefixes"
begin

  locale traces =
    fixes ind :: "'item \<Rightarrow> 'item \<Rightarrow> bool"
    assumes independence_symmetric[sym]: "ind a b \<Longrightarrow> ind b a"
  begin

    abbreviation Ind :: "'item set \<Rightarrow> 'item set \<Rightarrow> bool"
      where "Ind A B \<equiv> \<forall> a \<in> A. \<forall> b \<in> B. ind a b"

    inductive eq_swap :: "'item list \<Rightarrow> 'item list \<Rightarrow> bool" (infix "=\<^sub>S" 50)
      where swap: "ind a b \<Longrightarrow> u @ [a] @ [b] @ v =\<^sub>S u @ [b] @ [a] @ v"

    declare eq_swap.intros[intro]
    declare eq_swap.cases[elim]

    lemma eq_swap_sym[sym]: "v =\<^sub>S w \<Longrightarrow> w =\<^sub>S v" using independence_symmetric by auto

    lemma eq_swap_length[dest]: "w\<^sub>1 =\<^sub>S w\<^sub>2 \<Longrightarrow> length w\<^sub>1 = length w\<^sub>2" by force
    lemma eq_swap_range[dest]: "w\<^sub>1 =\<^sub>S w\<^sub>2 \<Longrightarrow> set w\<^sub>1 = set w\<^sub>2" by force

    lemma eq_swap_extend:
      assumes "w\<^sub>1 =\<^sub>S w\<^sub>2"
      shows "u @ w\<^sub>1 @ v =\<^sub>S u @ w\<^sub>2 @ v"
    using assms
    proof induct
      case (swap a b u' v')
      have "u @ (u' @ [a] @ [b] @ v') @ v = (u @ u') @ [a] @ [b] @ (v' @ v)" by simp
      also have "\<dots> =\<^sub>S (u @ u') @ [b] @ [a] @ (v' @ v)" using swap by blast
      also have "\<dots> = u @ (u' @ [b] @ [a] @ v') @ v" by simp
      finally show ?case by this
    qed

    lemma eq_swap_remove1:
      assumes "w\<^sub>1 =\<^sub>S w\<^sub>2"
      obtains (equal) "remove1 c w\<^sub>1 = remove1 c w\<^sub>2" | (swap) "remove1 c w\<^sub>1 =\<^sub>S remove1 c w\<^sub>2"
    using assms
    proof induct
      case (swap a b u v)
      have "c \<notin> set (u @ [a] @ [b] @ v) \<or>
        c \<in> set u \<or>
        c \<notin> set u \<and> c = a \<or>
        c \<notin> set u \<and> c \<noteq> a \<and> c = b \<or>
        c \<notin> set u \<and> c \<noteq> a \<and> c \<noteq> b \<and> c \<in> set v"
        by auto
      thus ?case
      proof (elim disjE)
        assume 0: "c \<notin> set (u @ [a] @ [b] @ v)"
        have 1: "c \<notin> set (u @ [b] @ [a] @ v)" using 0 by auto
        have 2: "remove1 c (u @ [a] @ [b] @ v) = u @ [a] @ [b] @ v" using remove1_idem 0 by this
        have 3: "remove1 c (u @ [b] @ [a] @ v) = u @ [b] @ [a] @ v" using remove1_idem 1 by this
        have 4: "remove1 c (u @ [a] @ [b] @ v) =\<^sub>S remove1 c (u @ [b] @ [a] @ v)"
          unfolding 2 3 using eq_swap.intros swap(1) by this
        show thesis using swap(3) 4 by this
      next
        assume 0: "c \<in> set u"
        have 2: "remove1 c (u @ [a] @ [b] @ v) = remove1 c u @ [a] @ [b] @ v"
          unfolding remove1_append using 0 by simp
        have 3: "remove1 c (u @ [b] @ [a] @ v) = remove1 c u @ [b] @ [a] @ v"
          unfolding remove1_append using 0 by simp
        have 4: "remove1 c (u @ [a] @ [b] @ v) =\<^sub>S remove1 c (u @ [b] @ [a] @ v)"
          unfolding 2 3 using eq_swap.intros swap(1) by this
        show thesis using swap(3) 4 by this
      next
        assume 0: "c \<notin> set u \<and> c = a"
        have 2: "remove1 c (u @ [a] @ [b] @ v) = u @ [b] @ v"
          unfolding remove1_append using remove1_idem 0 by auto
        have 3: "remove1 c (u @ [b] @ [a] @ v) = u @ [b] @ v"
          unfolding remove1_append using remove1_idem 0 by auto
        have 4: "remove1 c (u @ [a] @ [b] @ v) = remove1 c (u @ [b] @ [a] @ v)"
          unfolding 2 3 by rule
        show thesis using swap(2) 4 by this
      next
        assume 0: "c \<notin> set u \<and> c \<noteq> a \<and> c = b"
        have 2: "remove1 c (u @ [a] @ [b] @ v) = u @ [a] @ v"
          unfolding remove1_append using remove1_idem 0 by auto
        have 3: "remove1 c (u @ [b] @ [a] @ v) = u @ [a] @ v"
          unfolding remove1_append using remove1_idem 0 by auto
        have 4: "remove1 c (u @ [a] @ [b] @ v) = remove1 c (u @ [b] @ [a] @ v)"
          unfolding 2 3 by rule
        show thesis using swap(2) 4 by this
      next
        assume 0: "c \<notin> set u \<and> c \<noteq> a \<and> c \<noteq> b \<and> c \<in> set v"
        have 2: "remove1 c (u @ [a] @ [b] @ v) = u @ [a] @ [b] @ remove1 c v"
          unfolding remove1_append using 0 by simp
        have 3: "remove1 c (u @ [b] @ [a] @ v) = u @ [b] @ [a] @ remove1 c v"
          unfolding remove1_append using 0 by simp
        have 4: "remove1 c (u @ [a] @ [b] @ v) =\<^sub>S remove1 c (u @ [b] @ [a] @ v)"
          unfolding 2 3 using eq_swap.intros swap(1) by this
        show ?thesis using swap(3) 4 by this
      qed
    qed

    lemma eq_swap_rev:
      assumes "w\<^sub>1 =\<^sub>S w\<^sub>2"
      shows "rev w\<^sub>1 =\<^sub>S rev w\<^sub>2"
    using assms
    proof induct
      case (swap a b u v)
      have 1: "rev v @ [a] @ [b] @ rev u =\<^sub>S rev v @ [b] @ [a] @ rev u" using swap by blast
      have 2: "rev v @ [b] @ [a] @ rev u =\<^sub>S rev v @ [a] @ [b] @ rev u" using 1 eq_swap_sym by blast
      show ?case using 2 by simp
    qed

    abbreviation eq_fin :: "'item list \<Rightarrow> 'item list \<Rightarrow> bool" (infix "=\<^sub>F" 50)
      where "eq_fin \<equiv> eq_swap\<^sup>*\<^sup>*"

    lemma eq_fin_symp[intro, sym]: "u =\<^sub>F v \<Longrightarrow> v =\<^sub>F u"
      using eq_swap_sym sym_rtrancl[to_pred] unfolding symp_def by metis

    lemma eq_fin_length[dest]: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<Longrightarrow> length w\<^sub>1 = length w\<^sub>2"
      by (induct rule: rtranclp.induct, auto)
    lemma eq_fin_range[dest]: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<Longrightarrow> set w\<^sub>1 = set w\<^sub>2"
      by (induct rule: rtranclp.induct, auto)

    lemma eq_fin_remove1:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2"
      shows "remove1 c w\<^sub>1 =\<^sub>F remove1 c w\<^sub>2"
    using assms
    proof induct
      case (base)
      show ?case by simp
    next
      case (step w\<^sub>2 w\<^sub>3)
      show ?case
      using step(2)
      proof (cases rule: eq_swap_remove1[where ?c = c])
        case equal
        show ?thesis using step equal by simp
      next
        case swap
        show ?thesis using step swap by auto
      qed
    qed

    lemma eq_fin_rev:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2"
      shows "rev w\<^sub>1 =\<^sub>F rev w\<^sub>2"
      using assms by (induct, auto dest: eq_swap_rev)

    lemma eq_fin_concat_eq_fin_start:
      assumes "u @ v\<^sub>1 =\<^sub>F u @ v\<^sub>2"
      shows "v\<^sub>1 =\<^sub>F v\<^sub>2"
    using assms
    proof (induct u arbitrary: v\<^sub>1 v\<^sub>2 rule: rev_induct)
      case (Nil)
      show ?case using Nil by simp
    next
      case (snoc a u)
      have 1: "u @ [a] @ v\<^sub>1 =\<^sub>F u @ [a] @ v\<^sub>2" using snoc(2) by simp
      have 2: "[a] @ v\<^sub>1 =\<^sub>F [a] @ v\<^sub>2" using snoc(1) 1 by this
      show ?case using eq_fin_remove1[OF 2, of a] by simp
    qed

    lemma eq_fin_concat: "u @ w\<^sub>1 @ v =\<^sub>F u @ w\<^sub>2 @ v \<longleftrightarrow> w\<^sub>1 =\<^sub>F w\<^sub>2"
    proof
      assume 0: "u @ w\<^sub>1 @ v =\<^sub>F u @ w\<^sub>2 @ v"
      have 1: "w\<^sub>1 @ v =\<^sub>F w\<^sub>2 @ v" using eq_fin_concat_eq_fin_start 0 by this
      have 2: "rev (w\<^sub>1 @ v) =\<^sub>F rev (w\<^sub>2 @ v)" using 1 by (blast dest: eq_fin_rev)
      have 3: "rev v @ rev w\<^sub>1 =\<^sub>F rev v @ rev w\<^sub>2" using 2 by simp
      have 4: "rev w\<^sub>1 =\<^sub>F rev w\<^sub>2" using eq_fin_concat_eq_fin_start 3 by this
      have 5: "rev (rev w\<^sub>1) =\<^sub>F rev (rev w\<^sub>2)" using 4 by (blast dest: eq_fin_rev)
      show "w\<^sub>1 =\<^sub>F w\<^sub>2" using 5 by simp
    next
      show "u @ w\<^sub>1 @ v =\<^sub>F u @ w\<^sub>2 @ v" if "w\<^sub>1 =\<^sub>F w\<^sub>2"
        using that by (induct, auto dest: eq_swap_extend[of _ _ u v])
    qed
    lemma eq_fin_concat_start[iff]: "w @ w\<^sub>1 =\<^sub>F w @ w\<^sub>2 \<longleftrightarrow> w\<^sub>1 =\<^sub>F w\<^sub>2"
      using eq_fin_concat[of "w" _ "[]"] by simp
    lemma eq_fin_concat_end[iff]: "w\<^sub>1 @ w =\<^sub>F w\<^sub>2 @ w \<longleftrightarrow> w\<^sub>1 =\<^sub>F w\<^sub>2"
      using eq_fin_concat[of "[]" _ "w"] by simp

    lemma ind_eq_fin':
      assumes "Ind {a} (set v)"
      shows "[a] @ v =\<^sub>F v @ [a]"
    using assms
    proof (induct v)
      case (Nil)
      show ?case by simp
    next
      case (Cons b v)
      have 1: "Ind {a} (set v)" using Cons(2) by auto
      have 2: "ind a b" using Cons(2) by auto
      have "[a] @ b # v = [a] @ [b] @ v" by simp
      also have "\<dots> =\<^sub>S [b] @ [a] @ v" using eq_swap.intros[OF 2, of "[]"] by auto
      also have "\<dots> =\<^sub>F [b] @ v @ [a]" using Cons(1) 1 by blast
      also have "\<dots> = (b # v) @ [a]" by simp
      finally show ?case by this
    qed

    lemma ind_eq_fin[intro]:
      assumes "Ind (set u) (set v)"
      shows "u @ v =\<^sub>F v @ u"
    using assms
    proof (induct u)
      case (Nil)
      show ?case by simp
    next
      case (Cons a u)
      have 1: "Ind (set u) (set v)" using Cons(2) by auto
      have 2: "Ind {a} (set v)" using Cons(2) by auto
      have "(a # u) @ v = [a] @ u @ v" by simp
      also have "\<dots> =\<^sub>F [a] @ v @ u" using Cons(1) 1 by blast
      also have "\<dots> = ([a] @ v) @ u" by simp
      also have "\<dots> =\<^sub>F (v @ [a]) @ u" using ind_eq_fin' 2 by blast
      also have "\<dots> = v @ (a # u)" by simp
      finally show ?case by this
    qed

    definition le_fin :: "'item list \<Rightarrow> 'item list \<Rightarrow> bool" (infix "\<preceq>\<^sub>F" 50)
      where "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<equiv> \<exists> v\<^sub>1. w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2"

    lemma le_finI[intro 0]:
      assumes "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
      using assms unfolding le_fin_def by auto
    lemma le_finE[elim 0]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
      obtains v\<^sub>1
      where "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2"
      using assms unfolding le_fin_def by auto

    lemma le_fin_empty[simp]: "[] \<preceq>\<^sub>F w" by force
    lemma le_fin_trivial[intro]: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<Longrightarrow> w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
    proof
      assume 1: "w\<^sub>1 =\<^sub>F w\<^sub>2"
      show "w\<^sub>1 @ [] =\<^sub>F w\<^sub>2" using 1 by simp
    qed

    lemma le_fin_length[dest]: "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<Longrightarrow> length w\<^sub>1 \<le> length w\<^sub>2" by force
    lemma le_fin_range[dest]: "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<Longrightarrow> set w\<^sub>1 \<subseteq> set w\<^sub>2" by force

    lemma eq_fin_alt_def: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<longleftrightarrow> w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<and> w\<^sub>2 \<preceq>\<^sub>F w\<^sub>1"
    proof
      show "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<and> w\<^sub>2 \<preceq>\<^sub>F w\<^sub>1" if "w\<^sub>1 =\<^sub>F w\<^sub>2" using that by blast
    next
      assume 0: "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 \<and> w\<^sub>2 \<preceq>\<^sub>F w\<^sub>1"
      have 1: "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F w\<^sub>1" using 0 by auto
      have 10: "length w\<^sub>1 = length w\<^sub>2" using 1 by force
      obtain v\<^sub>1 v\<^sub>2 where 2: "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2" "w\<^sub>2 @ v\<^sub>2 =\<^sub>F w\<^sub>1" using 1 by (elim le_finE)
      have 3: "length w\<^sub>1 = length (w\<^sub>1 @ v\<^sub>1)" using 2 10 by force
      have 4: "w\<^sub>1 = w\<^sub>1 @ v\<^sub>1" using 3 by auto
      have 5: "length w\<^sub>2 = length (w\<^sub>2 @ v\<^sub>2)" using 2 10 by force
      have 6: "w\<^sub>2 = w\<^sub>2 @ v\<^sub>2" using 5 by auto
      show "w\<^sub>1 =\<^sub>F w\<^sub>2" using 4 6 2 by simp
    qed

    lemma le_fin_reflp[simp, intro]: "w \<preceq>\<^sub>F w" by auto
    lemma le_fin_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
    proof -
      obtain v\<^sub>1 where 1: "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2" using assms(1) by rule
      obtain v\<^sub>2 where 2: "w\<^sub>2 @ v\<^sub>2 =\<^sub>F w\<^sub>3" using assms(2) by rule
      show ?thesis
      proof
        have "w\<^sub>1 @ v\<^sub>1 @ v\<^sub>2 = (w\<^sub>1 @ v\<^sub>1) @ v\<^sub>2" by simp
        also have "\<dots> =\<^sub>F w\<^sub>2 @ v\<^sub>2" using 1 by blast
        also have "\<dots> =\<^sub>F w\<^sub>3" using 2 by blast
        finally show "w\<^sub>1 @ v\<^sub>1 @ v\<^sub>2 =\<^sub>F w\<^sub>3" by this
      qed
    qed
    lemma eq_fin_le_fin_transp[intro, trans]:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
      using assms by auto
    lemma le_fin_eq_fin_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 =\<^sub>F w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
      using assms by auto
    lemma prefix_le_fin_transp[intro, trans]:
      assumes "w\<^sub>1 \<le> w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
    proof -
      obtain v\<^sub>1 where 1: "w\<^sub>2 = w\<^sub>1 @ v\<^sub>1" using assms(1) by rule
      obtain v\<^sub>2 where 2: "w\<^sub>2 @ v\<^sub>2 =\<^sub>F w\<^sub>3" using assms(2) by rule
      show ?thesis
      proof
        show "w\<^sub>1 @ v\<^sub>1 @ v\<^sub>2 =\<^sub>F w\<^sub>3" using 1 2 by simp
      qed
    qed
    lemma le_fin_prefix_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 \<le> w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
    proof -
      obtain v\<^sub>1 where 1: "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2" using assms(1) by rule
      obtain v\<^sub>2 where 2: "w\<^sub>3 = w\<^sub>2 @ v\<^sub>2" using assms(2) by rule
      show ?thesis
      proof
        have "w\<^sub>1 @ v\<^sub>1 @ v\<^sub>2 = (w\<^sub>1 @ v\<^sub>1) @ v\<^sub>2" by simp
        also have "\<dots> =\<^sub>F w\<^sub>2 @ v\<^sub>2" using 1 by blast
        also have "\<dots> = w\<^sub>3" using 2 by simp
        finally show "w\<^sub>1 @ v\<^sub>1 @ v\<^sub>2 =\<^sub>F w\<^sub>3" by this
      qed
    qed
    lemma prefix_eq_fin_transp[intro, trans]:
      assumes "w\<^sub>1 \<le> w\<^sub>2" "w\<^sub>2 =\<^sub>F w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>3"
      using assms by auto

    lemma le_fin_concat_start[iff]: "w @ w\<^sub>1 \<preceq>\<^sub>F w @ w\<^sub>2 \<longleftrightarrow> w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
    proof
      assume 0: "w @ w\<^sub>1 \<preceq>\<^sub>F w @ w\<^sub>2"
      obtain v\<^sub>1 where 1: "w @ w\<^sub>1 @ v\<^sub>1 =\<^sub>F w @ w\<^sub>2" using 0 by auto
      show "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" using 1 by auto
    next
      assume 0: "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
      obtain v\<^sub>1 where 1: "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2" using 0 by auto
      have 2: "(w @ w\<^sub>1) @ v\<^sub>1 =\<^sub>F w @ w\<^sub>2" using 1 by auto
      show "w @ w\<^sub>1 \<preceq>\<^sub>F w @ w\<^sub>2" using 2 by blast
    qed
    lemma le_fin_concat_end[dest]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 @ w"
    proof -
      obtain v\<^sub>1 where 1: "w\<^sub>1 @ v\<^sub>1 =\<^sub>F w\<^sub>2" using assms by rule
      show ?thesis
      proof
        have "w\<^sub>1 @ v\<^sub>1 @ w = (w\<^sub>1 @ v\<^sub>1) @ w" by simp
        also have "\<dots> =\<^sub>F w\<^sub>2 @ w" using 1 by blast
        finally show "w\<^sub>1 @ v\<^sub>1 @ w =\<^sub>F w\<^sub>2 @ w" by this
      qed
    qed

    definition le_fininf :: "'item list \<Rightarrow> 'item stream \<Rightarrow> bool" (infix "\<preceq>\<^sub>F\<^sub>I" 50)
      where "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2 \<equiv> \<exists> v\<^sub>2. v\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>2 \<and> w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2"

    lemma le_fininfI[intro 0]:
      assumes "v\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      using assms unfolding le_fininf_def by auto
    lemma le_fininfE[elim 0]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      obtains v\<^sub>2
      where "v\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2"
      using assms unfolding le_fininf_def by auto

    lemma le_fininf_empty[simp]: "[] \<preceq>\<^sub>F\<^sub>I w" by force

    lemma le_fininf_range[dest]: "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2 \<Longrightarrow> set w\<^sub>1 \<subseteq> sset w\<^sub>2" by force

    lemma eq_fin_le_fininf_transp[intro, trans]:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast
    lemma le_fin_le_fininf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast
    lemma prefix_le_fininf_transp[intro, trans]:
      assumes "w\<^sub>1 \<le> w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by auto
    lemma le_fin_prefix_fininf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" "w\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by auto
    lemma eq_fin_prefix_fininf_transp[intro, trans]:
      assumes "w\<^sub>1 =\<^sub>F w\<^sub>2" "w\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by auto

    lemma le_fininf_concat_start[iff]: "w @ w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w @- w\<^sub>2 \<longleftrightarrow> w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
    proof
      assume 0: "w @ w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w @- w\<^sub>2"
      obtain v\<^sub>2 where 1: "v\<^sub>2 \<le>\<^sub>F\<^sub>I w @- w\<^sub>2" "w @ w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using 0 by rule
      have 2: "length w \<le> length v\<^sub>2" using 1(2) by force
      have 4: "w \<le> v\<^sub>2" using prefix_fininf_extend[OF 1(1) 2] by this
      obtain v\<^sub>1 where 5: "v\<^sub>2 = w @ v\<^sub>1" using 4 by rule
      show "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      proof
        show "v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>2" using 1(1) unfolding 5 by auto
        show "w\<^sub>1 \<preceq>\<^sub>F v\<^sub>1" using 1(2) unfolding 5 by simp
      qed
    next
      assume 0: "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      obtain v\<^sub>2 where 1: "v\<^sub>2 \<le>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using 0 by rule
      show "w @ w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w @- w\<^sub>2"
      proof
        show "w @ v\<^sub>2 \<le>\<^sub>F\<^sub>I (w @- w\<^sub>2)" using 1(1) by auto
        show "w @ w\<^sub>1 \<preceq>\<^sub>F w @ v\<^sub>2" using 1(2) by auto
      qed
    qed

    lemma le_fininf_singleton[intro, simp]: "[shd v] \<preceq>\<^sub>F\<^sub>I v"
    proof -
      have "[shd v] \<preceq>\<^sub>F\<^sub>I shd v ## sdrop 1 v" by blast
      also have "\<dots> = v" by simp
      finally show ?thesis by this
    qed

    definition le_inf :: "'item stream \<Rightarrow> 'item stream \<Rightarrow> bool" (infix "\<preceq>\<^sub>I" 50)
      where "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2 \<equiv> \<forall> v\<^sub>1. v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1 \<longrightarrow> v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"

    lemma le_infI[intro 0]:
      assumes "\<And> v\<^sub>1. v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1 \<Longrightarrow> v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
      using assms unfolding le_inf_def by auto
    lemma le_infE[elim 0]:
      assumes "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2" "v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1"
      obtains "v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      using assms unfolding le_inf_def by auto

    lemma le_inf_range[dest]:
      assumes "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
      shows "sset w\<^sub>1 \<subseteq> sset w\<^sub>2"
    proof
      fix a
      assume 1: "a \<in> sset w\<^sub>1"
      obtain i where 2: "a = w\<^sub>1 !! i" using 1 by (metis imageE sset_range)
      have 3: "stake (Suc i) w\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1" by rule
      have 4: "stake (Suc i) w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2" using assms 3 by rule
      have 5: "w\<^sub>1 !! i \<in> set (stake (Suc i) w\<^sub>1)" by (meson lessI set_stake_snth)
      show "a \<in> sset w\<^sub>2" unfolding 2 using 5 4 by fastforce
    qed

    lemma le_inf_reflp[simp, intro]: "w \<preceq>\<^sub>I w" by auto
    lemma prefix_fininf_le_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast
    lemma le_fininf_le_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast
    lemma le_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>3"
      using assms by blast

    lemma le_infI':
      assumes "\<And> k. \<exists> v. v \<le>\<^sub>F\<^sub>I w\<^sub>1 \<and> k < length v \<and> v \<preceq>\<^sub>F\<^sub>I w\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
    proof
      fix u
      assume 1: "u \<le>\<^sub>F\<^sub>I w\<^sub>1"
      obtain v where 2: "v \<le>\<^sub>F\<^sub>I w\<^sub>1" "length u < length v" "v \<preceq>\<^sub>F\<^sub>I w\<^sub>2" using assms by auto
      have 3: "length u \<le> length v" using 2(2) by auto
      have 4: "u \<le> v" using prefix_fininf_length 1 2(1) 3 by this
      show "u \<preceq>\<^sub>F\<^sub>I w\<^sub>2" using 4 2(3) by rule
    qed

    lemma le_infI_chain_left:
      assumes "chain w" "\<And> k. w k \<preceq>\<^sub>F\<^sub>I v"
      shows "limit w \<preceq>\<^sub>I v"
    proof (rule le_infI')
      fix k
      obtain l where 1: "k < length (w l)" using assms(1) by rule
      show "\<exists> va. va \<le>\<^sub>F\<^sub>I limit w \<and> k < length va \<and> va \<preceq>\<^sub>F\<^sub>I v"
      proof (intro exI conjI)
        show "w l \<le>\<^sub>F\<^sub>I limit w" using chain_prefix_limit assms(1) by this
        show "k < length (w l)" using 1 by this
        show "w l \<preceq>\<^sub>F\<^sub>I v" using assms(2) by this
      qed
    qed
    lemma le_infI_chain_right:
      assumes "chain w" "\<And> u. u \<le>\<^sub>F\<^sub>I v \<Longrightarrow> u \<preceq>\<^sub>F w (l u)"
      shows "v \<preceq>\<^sub>I limit w"
    proof
      fix u
      assume 1: "u \<le>\<^sub>F\<^sub>I v"
      show "u \<preceq>\<^sub>F\<^sub>I limit w"
      proof
        show "w (l u) \<le>\<^sub>F\<^sub>I limit w" using chain_prefix_limit assms(1) by this
        show "u \<preceq>\<^sub>F w (l u)" using assms(2) 1 by this
      qed
    qed
    lemma le_infI_chain_right':
      assumes "chain w" "\<And> k. stake k v \<preceq>\<^sub>F w (l k)"
      shows "v \<preceq>\<^sub>I limit w"
    proof (rule le_infI_chain_right)
      show "chain w" using assms(1) by this
    next
      fix u
      assume 1: "u \<le>\<^sub>F\<^sub>I v"
      have 2: "stake (length u) v = u" using 1 by (simp add: prefix_fininf_def shift_eq)
      have 3: "stake (length u) v \<preceq>\<^sub>F w (l (length u))" using assms(2) by this
      show "u \<preceq>\<^sub>F w (l (length u))" using 3 unfolding 2 by this
    qed

    definition eq_inf :: "'item stream \<Rightarrow> 'item stream \<Rightarrow> bool" (infix "=\<^sub>I" 50)
      where "w\<^sub>1 =\<^sub>I w\<^sub>2 \<equiv> w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2 \<and> w\<^sub>2 \<preceq>\<^sub>I w\<^sub>1"

    lemma eq_infI[intro 0]:
      assumes "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>1"
      shows "w\<^sub>1 =\<^sub>I w\<^sub>2"
      using assms unfolding eq_inf_def by auto
    lemma eq_infE[elim 0]:
      assumes "w\<^sub>1 =\<^sub>I w\<^sub>2"
      obtains "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>1"
      using assms unfolding eq_inf_def by auto

    lemma eq_inf_range[dest]: "w\<^sub>1 =\<^sub>I w\<^sub>2 \<Longrightarrow> sset w\<^sub>1 = sset w\<^sub>2" by force

    lemma eq_inf_reflp[simp, intro]: "w =\<^sub>I w" by auto
    lemma eq_inf_symp[intro]: "w\<^sub>1 =\<^sub>I w\<^sub>2 \<Longrightarrow> w\<^sub>2 =\<^sub>I w\<^sub>1" by auto
    lemma eq_inf_transp[intro, trans]:
      assumes "w\<^sub>1 =\<^sub>I w\<^sub>2" "w\<^sub>2 =\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 =\<^sub>I w\<^sub>3"
      using assms by blast
    lemma le_fininf_eq_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>2 =\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast
    lemma le_inf_eq_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2" "w\<^sub>2 =\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>3"
      using assms by blast
    lemma eq_inf_le_inf_transp[intro, trans]:
      assumes "w\<^sub>1 =\<^sub>I w\<^sub>2" "w\<^sub>2 \<preceq>\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>3"
      using assms by blast
    lemma prefix_fininf_eq_inf_transp[intro, trans]:
      assumes "w\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>2" "w\<^sub>2 =\<^sub>I w\<^sub>3"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>3"
      using assms by blast

    lemma le_inf_concat_start[iff]: "w @- w\<^sub>1 \<preceq>\<^sub>I w @- w\<^sub>2 \<longleftrightarrow> w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
    proof
      assume 1: "w @- w\<^sub>1 \<preceq>\<^sub>I w @- w\<^sub>2"
      show "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
      proof
        fix v\<^sub>1
        assume 2: "v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1"
        have "w @ v\<^sub>1 \<le>\<^sub>F\<^sub>I w @- w\<^sub>1" using 2 by auto
        also have "\<dots> \<preceq>\<^sub>I w @- w\<^sub>2" using 1 by this
        finally show "v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2" by rule
      qed
    next
      assume 1: "w\<^sub>1 \<preceq>\<^sub>I w\<^sub>2"
      show "w @- w\<^sub>1 \<preceq>\<^sub>I w @- w\<^sub>2"
      proof
        fix v\<^sub>1
        assume 2: "v\<^sub>1 \<le>\<^sub>F\<^sub>I w @- w\<^sub>1"
        then show "v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w @- w\<^sub>2"
        proof (cases rule: prefix_fininf_append)
          case (absorb)
          show ?thesis using absorb by auto
        next
          case (extend z)
          show ?thesis using 1 extend by auto
        qed
      qed
    qed
    lemma eq_fin_le_inf_concat_end[dest]: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<Longrightarrow> w\<^sub>1 @- w \<preceq>\<^sub>I w\<^sub>2 @- w"
    proof
      fix v\<^sub>1
      assume 1: "w\<^sub>1 =\<^sub>F w\<^sub>2" "v\<^sub>1 \<le>\<^sub>F\<^sub>I w\<^sub>1 @- w"
      show "v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w\<^sub>2 @- w"
      using 1(2)
      proof (cases rule: prefix_fininf_append)
        case (absorb)
        show ?thesis
        proof
          show "w\<^sub>2 \<le>\<^sub>F\<^sub>I (w\<^sub>2 @- w)" by auto
          show "v\<^sub>1 \<preceq>\<^sub>F w\<^sub>2" using absorb 1(1) by auto
        qed
      next
        case (extend w')
        show ?thesis
        proof
          show "w\<^sub>2 @ w' \<le>\<^sub>F\<^sub>I (w\<^sub>2 @- w)" using extend(2) by auto
          show "v\<^sub>1 \<preceq>\<^sub>F w\<^sub>2 @ w'" unfolding extend(1) using 1(1) by auto
        qed
      qed
    qed

    lemma eq_inf_concat_start[iff]: "w @- w\<^sub>1 =\<^sub>I w @- w\<^sub>2 \<longleftrightarrow> w\<^sub>1 =\<^sub>I w\<^sub>2" by blast
    lemma eq_inf_concat_end[dest]: "w\<^sub>1 =\<^sub>F w\<^sub>2 \<Longrightarrow> w\<^sub>1 @- w =\<^sub>I w\<^sub>2 @- w"
    proof -
      assume 0: "w\<^sub>1 =\<^sub>F w\<^sub>2"
      have 1: "w\<^sub>2 =\<^sub>F w\<^sub>1" using 0 by auto
      show "w\<^sub>1 @- w =\<^sub>I w\<^sub>2 @- w"
        using eq_fin_le_inf_concat_end[OF 0] eq_fin_le_inf_concat_end[OF 1] by auto
    qed

    lemma le_fininf_suffixI[intro]:
      assumes "w =\<^sub>I w\<^sub>1 @- w\<^sub>2"
      shows "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w"
      using assms by blast
    lemma le_fininf_suffixE[elim]:
      assumes "w\<^sub>1 \<preceq>\<^sub>F\<^sub>I w"
      obtains w\<^sub>2
      where "w =\<^sub>I w\<^sub>1 @- w\<^sub>2"
    proof -
      obtain v\<^sub>2 where 1: "v\<^sub>2 \<le>\<^sub>F\<^sub>I w" "w\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using assms(1) by rule
      obtain u\<^sub>1 where 2: "w\<^sub>1 @ u\<^sub>1 =\<^sub>F v\<^sub>2" using 1(2) by rule
      obtain v\<^sub>2' where 3: "w = v\<^sub>2 @- v\<^sub>2'" using 1(1) by rule
      show ?thesis
      proof
        show "w =\<^sub>I w\<^sub>1 @- u\<^sub>1 @- v\<^sub>2'" unfolding 3 using 2 by fastforce
      qed
    qed

    lemma subsume_fin:
      assumes "u\<^sub>1 \<preceq>\<^sub>F\<^sub>I w" "v\<^sub>1 \<preceq>\<^sub>F\<^sub>I w"
      obtains w\<^sub>1
      where "u\<^sub>1 \<preceq>\<^sub>F w\<^sub>1" "v\<^sub>1 \<preceq>\<^sub>F w\<^sub>1"
    proof -
      obtain u\<^sub>2 where 2: "u\<^sub>2 \<le>\<^sub>F\<^sub>I w" "u\<^sub>1 \<preceq>\<^sub>F u\<^sub>2" using assms(1) by rule
      obtain v\<^sub>2 where 3: "v\<^sub>2 \<le>\<^sub>F\<^sub>I w" "v\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using assms(2) by rule
      show ?thesis
      proof (cases "length u\<^sub>2" "length v\<^sub>2" rule: le_cases)
        case le
        show ?thesis
        proof
          show "u\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using 2(2) prefix_fininf_length[OF 2(1) 3(1) le] by auto
          show "v\<^sub>1 \<preceq>\<^sub>F v\<^sub>2" using 3(2) by this
        qed
      next
        case ge
        show ?thesis
        proof
          show "u\<^sub>1 \<preceq>\<^sub>F u\<^sub>2" using 2(2) by this
          show "v\<^sub>1 \<preceq>\<^sub>F u\<^sub>2" using 3(2) prefix_fininf_length[OF 3(1) 2(1) ge] by auto
        qed
      qed
    qed

    lemma eq_fin_end:
      assumes "u\<^sub>1 =\<^sub>F u\<^sub>2" "u\<^sub>1 @ v\<^sub>1 =\<^sub>F u\<^sub>2 @ v\<^sub>2"
      shows "v\<^sub>1 =\<^sub>F v\<^sub>2"
    proof -
      have "u\<^sub>1 @ v\<^sub>2 =\<^sub>F u\<^sub>2 @ v\<^sub>2" using assms(1) by blast
      also have "\<dots> =\<^sub>F u\<^sub>1 @ v\<^sub>1" using assms(2) by blast
      finally show ?thesis by blast
    qed

    definition indoc :: "'item \<Rightarrow> 'item list \<Rightarrow> bool"
      where "indoc a u \<equiv> \<exists> u\<^sub>1 u\<^sub>2. u = u\<^sub>1 @ [a] @ u\<^sub>2 \<and> a \<notin> set u\<^sub>1 \<and> Ind {a} (set u\<^sub>1)"

    lemma indoc_set: "indoc a u \<Longrightarrow> a \<in> set u" unfolding indoc_def by auto

    lemma indoc_appendI1[intro]:
      assumes "indoc a u"
      shows "indoc a (u @ v)"
      using assms unfolding indoc_def by force
    lemma indoc_appendI2[intro]:
      assumes "a \<notin> set u" "Ind {a} (set u)" "indoc a v"
      shows "indoc a (u @ v)"
    proof -
      obtain v\<^sub>1 v\<^sub>2 where 1: "v = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set v\<^sub>1" "Ind {a} (set v\<^sub>1)"
        using assms(3) unfolding indoc_def by blast
      show ?thesis
      proof (unfold indoc_def, intro exI conjI)
        show "u @ v = (u @ v\<^sub>1) @ [a] @ v\<^sub>2" unfolding 1(1) by simp
        show "a \<notin> set (u @ v\<^sub>1)" using assms(1) 1(2) by auto
        show "Ind {a} (set (u @ v\<^sub>1))" using assms(2) 1(3) by auto
      qed
    qed
    lemma indoc_appendE[elim!]:
      assumes "indoc a (u @ v)"
      obtains (first) "a \<in> set u" "indoc a u" | (second)  "a \<notin> set u" "Ind {a} (set u)" "indoc a v"
    proof -
      obtain w\<^sub>1 w\<^sub>2 where 1: "u @ v = w\<^sub>1 @ [a] @ w\<^sub>2" "a \<notin> set w\<^sub>1" "Ind {a} (set w\<^sub>1)"
        using assms unfolding indoc_def by blast
      show ?thesis
      proof (cases "a \<in> set u")
        case True
        obtain u\<^sub>1 u\<^sub>2 where 2: "u = u\<^sub>1 @ [a] @ u\<^sub>2" "a \<notin> set u\<^sub>1"
          using split_list_first[OF True] by auto
        have 3: "w\<^sub>1 = u\<^sub>1"
        proof (rule split_list_first_unique)
          show "w\<^sub>1 @ [a] @ w\<^sub>2 = u\<^sub>1 @ [a] @ u\<^sub>2 @ v" using 1(1) unfolding 2(1) by simp
          show "a \<notin> set w\<^sub>1" using 1(2) by auto
          show "a \<notin> set u\<^sub>1" using 2(2) by this
        qed
        show ?thesis
        proof (rule first)
          show "a \<in> set u" using True by this
          show "indoc a u"
          proof (unfold indoc_def, intro exI conjI)
            show "u = u\<^sub>1 @ [a] @ u\<^sub>2" using 2(1) by this
            show "a \<notin> set u\<^sub>1" using 1(2) unfolding 3 by this
            show "Ind {a} (set u\<^sub>1)" using 1(3) unfolding 3 by this
          qed
        qed
      next
        case False
        have 2: "a \<in> set v" using indoc_set assms False by fastforce
        obtain v\<^sub>1 v\<^sub>2 where 3: "v = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set v\<^sub>1"
          using split_list_first[OF 2] by auto
        have 4: "w\<^sub>1 = u @ v\<^sub>1"
        proof (rule split_list_first_unique)
          show "w\<^sub>1 @ [a] @ w\<^sub>2 = (u @ v\<^sub>1) @ [a] @ v\<^sub>2" using 1(1) unfolding 3(1) by simp
          show "a \<notin> set w\<^sub>1" using 1(2) by auto
          show "a \<notin> set (u @ v\<^sub>1)" using False 3(2) by auto
        qed
        show ?thesis
        proof (rule second)
          show "a \<notin> set u" using False by this
          show "Ind {a} (set u)" using 1(3) 4 by auto
          show "indoc a v"
          proof (unfold indoc_def, intro exI conjI)
            show "v = v\<^sub>1 @ [a] @ v\<^sub>2" using 3(1) by this
            show "a \<notin> set v\<^sub>1" using 1(2) unfolding 4 by auto
            show "Ind {a} (set v\<^sub>1)" using 1(3) unfolding 4 by auto
          qed
        qed
      qed
    qed

    lemma indoc_single: "indoc a [b] \<longleftrightarrow> a = b"
    proof
      assume 1: "indoc a [b]"
      obtain u\<^sub>1 u\<^sub>2 where 2: "[b] = u\<^sub>1 @ [a] @ u\<^sub>2" "Ind {a} (set u\<^sub>1)"
        using 1 unfolding indoc_def by auto
      show "a = b" using 2(1)
        by (metis append_eq_Cons_conv append_is_Nil_conv list.distinct(2) list.inject)
    next
      assume 1: "a = b"
      show "indoc a [b]"
      unfolding indoc_def 1
      proof (intro exI conjI)
        show "[b] = [] @ [b] @ []" by simp
        show "b \<notin> set []" by simp
        show "Ind {b} (set [])" by simp
      qed
    qed

    lemma indoc_append[simp]: "indoc a (u @ v) \<longleftrightarrow>
      indoc a u \<or> a \<notin> set u \<and> Ind {a} (set u) \<and> indoc a v" by blast 
    lemma indoc_Nil[simp]: "indoc a [] \<longleftrightarrow> False" unfolding indoc_def by auto
    lemma indoc_Cons[simp]: "indoc a (b # v) \<longleftrightarrow> a = b \<or> a \<noteq> b \<and> ind a b \<and> indoc a v"
    proof -
      have "indoc a (b # v) \<longleftrightarrow> indoc a ([b] @ v)" by simp
      also have "\<dots> \<longleftrightarrow> indoc a [b] \<or> a \<notin> set [b] \<and> Ind {a} (set [b]) \<and> indoc a v"
        unfolding indoc_append by rule
      also have "\<dots> \<longleftrightarrow> a = b \<or> a \<noteq> b \<and> ind a b \<and> indoc a v" unfolding indoc_single by simp
      finally show ?thesis by this
    qed

    lemma eq_swap_indoc: "u =\<^sub>S v \<Longrightarrow> indoc c u \<Longrightarrow> indoc c v" by auto
    lemma eq_fin_indoc: "u =\<^sub>F v \<Longrightarrow> indoc c u \<Longrightarrow> indoc c v" by (induct rule: rtranclp.induct, auto)

    lemma eq_fin_ind':
      assumes "[a] @ u =\<^sub>F u\<^sub>1 @ [a] @ u\<^sub>2" "a \<notin> set u\<^sub>1"
      shows "Ind {a} (set u\<^sub>1)"
    proof -
      have 1: "indoc a ([a] @ u)" by simp
      have 2: "indoc a (u\<^sub>1 @ [a] @ u\<^sub>2)" using eq_fin_indoc assms(1) 1 by this
      show ?thesis using assms(2) 2 by blast
    qed
    lemma eq_fin_ind:
      assumes "u @ v =\<^sub>F v @ u" "set u \<inter> set v = {}"
      shows "Ind (set u) (set v)"
    using assms
    proof (induct u)
      case Nil
      show ?case by simp
    next
      case (Cons a u)
      have 1: "Ind {a} (set v)"
      proof (rule eq_fin_ind')
        show "[a] @ u @ v =\<^sub>F v @ [a] @ u" using Cons(2) by simp
        show "a \<notin> set v" using Cons(3) by simp
      qed
      have 2: "Ind (set [a]) (set v)" using 1 by simp
      have 4: "Ind (set u) (set v)"
      proof (rule Cons(1))
        have "[a] @ u @ v = (a # u) @ v" by simp
        also have "\<dots> =\<^sub>F v @ a # u" using Cons(2) by this
        also have "\<dots> = (v @ [a]) @ u" by simp
        also have "\<dots> =\<^sub>F ([a] @ v) @ u" using 2 by blast
        also have "\<dots> = [a] @ v @ u" by simp
        finally show "u @ v =\<^sub>F v @ u" by blast
        show "set u \<inter> set v = {}" using Cons(3) by auto
      qed
      show ?case using 1 4 by auto
    qed

    lemma le_fin_member':
      assumes "[a] \<preceq>\<^sub>F u @ v" "a \<in> set u"
      shows "[a] \<preceq>\<^sub>F u"
    proof -
      obtain w where 1: "[a] @ w =\<^sub>F u @ v" using assms(1) by rule
      obtain u\<^sub>1 u\<^sub>2 where 2: "u = u\<^sub>1 @ [a] @ u\<^sub>2" "a \<notin> set u\<^sub>1"
        using split_list_first[OF assms(2)] by auto
      have 3: "Ind {a} (set u\<^sub>1)"
      proof (rule eq_fin_ind')
        show "[a] @ w =\<^sub>F u\<^sub>1 @ [a] @ u\<^sub>2 @ v" using 1 unfolding 2(1) by simp
        show "a \<notin> set u\<^sub>1" using 2(2) by this
      qed
      have 4: "Ind (set [a]) (set u\<^sub>1)" using 3 by simp
      have "[a] \<le> [a] @ u\<^sub>1 @ u\<^sub>2" by auto
      also have "\<dots> = ([a] @ u\<^sub>1) @ u\<^sub>2" by simp
      also have "\<dots> =\<^sub>F (u\<^sub>1 @ [a]) @ u\<^sub>2" using 4 by blast
      also have "\<dots> = u" unfolding 2(1) by simp
      finally show ?thesis by this
    qed
    lemma le_fin_not_member':
      assumes "[a] \<preceq>\<^sub>F u @ v" "a \<notin> set u"
      shows "[a] \<preceq>\<^sub>F v"
    proof -
      obtain w where 1: "[a] @ w =\<^sub>F u @ v" using assms(1) by rule
      have 3: "a \<in> set v" using assms by auto
      obtain v\<^sub>1 v\<^sub>2 where 4: "v = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set v\<^sub>1" using split_list_first[OF 3] by auto
      have 5: "[a] @ w =\<^sub>F u @ v\<^sub>1 @ [a] @ v\<^sub>2" using 1 unfolding 4(1) by this
      have 6: "Ind {a} (set (u @ v\<^sub>1))"
      proof (rule eq_fin_ind')
        show "[a] @ w =\<^sub>F (u @ v\<^sub>1) @ [a] @ v\<^sub>2" using 5 by simp
        show "a \<notin> set (u @ v\<^sub>1)" using assms(2) 4(2) by auto
      qed
      have 9: "Ind (set [a]) (set v\<^sub>1)" using 6 by auto
      have "[a] \<le> [a] @ v\<^sub>1 @ v\<^sub>2" by auto
      also have "\<dots> = ([a] @ v\<^sub>1) @ v\<^sub>2" by simp
      also have "\<dots> =\<^sub>F (v\<^sub>1 @ [a]) @ v\<^sub>2" using 9 by blast
      also have "\<dots> = v\<^sub>1 @ [a] @ v\<^sub>2" by simp
      also have "\<dots> = v" unfolding 4(1) by rule
      finally show ?thesis by this
    qed
    lemma le_fininf_not_member':
      assumes "[a] \<preceq>\<^sub>F\<^sub>I u @- v" "a \<notin> set u"
      shows "[a] \<preceq>\<^sub>F\<^sub>I v"
    proof -
      obtain v\<^sub>2 where 1: "v\<^sub>2 \<le>\<^sub>F\<^sub>I u @- v" "[a] \<preceq>\<^sub>F v\<^sub>2" using le_fininfE assms(1) by this
      show ?thesis
      using 1(1)
      proof (cases rule: prefix_fininf_append)
        case absorb
        have "[a] \<preceq>\<^sub>F v\<^sub>2" using 1(2) by this
        also have "\<dots> \<le> u" using absorb by this
        finally have 2: "a \<in> set u" by force
        show ?thesis using assms(2) 2 by simp
      next
        case (extend z)
        have "[a] \<preceq>\<^sub>F v\<^sub>2" using 1(2) by this
        also have "\<dots> = u @ z" using extend(1) by this
        finally have 2: "[a] \<preceq>\<^sub>F u @ z" by this
        have "[a] \<preceq>\<^sub>F z" using le_fin_not_member' 2 assms(2) by this
        also have "\<dots> \<le>\<^sub>F\<^sub>I v" using extend(2) by this
        finally show ?thesis by this
      qed
    qed

    lemma le_fin_ind'':
      assumes "[a] \<preceq>\<^sub>F w" "[b] \<preceq>\<^sub>F w" "a \<noteq> b"
      shows "ind a b"
    proof -
      obtain u where 1: "[a] @ u =\<^sub>F w" using assms(1) by rule
      obtain v where 2: "[b] @ v =\<^sub>F w" using assms(2) by rule
      have 3: "[a] @ u =\<^sub>F [b] @ v" using 1 2[symmetric] by auto
      have 4: "a \<in> set v" using 3 assms(3)
        by (metis append_Cons append_Nil eq_fin_range list.set_intros(1) set_ConsD)
      obtain v\<^sub>1 v\<^sub>2 where 5: "v = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set v\<^sub>1" using split_list_first[OF 4] by auto
      have 7: "Ind {a} (set ([b] @ v\<^sub>1))"
      proof (rule eq_fin_ind')
        show "[a] @ u =\<^sub>F ([b] @ v\<^sub>1) @ [a] @ v\<^sub>2" using 3 unfolding 5(1) by simp
        show "a \<notin> set ([b] @ v\<^sub>1)" using assms(3) 5(2) by auto
      qed
      show ?thesis using 7 by auto
    qed
    lemma le_fin_ind':
      assumes "[a] \<preceq>\<^sub>F w" "v \<preceq>\<^sub>F w" "a \<notin> set v"
      shows "Ind {a} (set v)"
    using assms
    proof (induct v arbitrary: w)
      case Nil
      show ?case by simp
    next
      case (Cons b v)
      have 1: "ind a b"
      proof (rule le_fin_ind'')
        show "[a] \<preceq>\<^sub>F w" using Cons(2) by this
        show "[b] \<preceq>\<^sub>F w" using Cons(3) by auto
        show "a \<noteq> b" using Cons(4) by auto
      qed
      obtain w' where 2: "[b] @ w' =\<^sub>F w" using Cons(3) by auto
      have 3: "Ind {a} (set v)"
      proof (rule Cons(1))
        show "[a] \<preceq>\<^sub>F w'"
        proof (rule le_fin_not_member')
          show "[a] \<preceq>\<^sub>F [b] @ w'" using Cons(2) 2 by auto
          show "a \<notin> set [b]" using Cons(4) by auto
        qed
        have "[b] @ v = b # v" by simp
        also have "\<dots> \<preceq>\<^sub>F w" using Cons(3) by this
        also have "\<dots> =\<^sub>F [b] @ w'" using 2 by auto
        finally show "v \<preceq>\<^sub>F w'" by blast
        show "a \<notin> set v" using Cons(4) by auto
      qed
      show ?case using 1 3 by auto
    qed
    lemma le_fininf_ind'':
      assumes "[a] \<preceq>\<^sub>F\<^sub>I w" "[b] \<preceq>\<^sub>F\<^sub>I w" "a \<noteq> b"
      shows "ind a b"
      using subsume_fin le_fin_ind'' assms by metis
    lemma le_fininf_ind':
      assumes "[a] \<preceq>\<^sub>F\<^sub>I w" "v \<preceq>\<^sub>F\<^sub>I w" "a \<notin> set v"
      shows "Ind {a} (set v)"
      using subsume_fin le_fin_ind' assms by metis

    lemma indoc_alt_def: "indoc a v \<longleftrightarrow> v =\<^sub>F [a] @ remove1 a v"
    proof
      assume 0: "indoc a v"
      obtain v\<^sub>1 v\<^sub>2 where 1: "v = v\<^sub>1 @ [a] @ v\<^sub>2" "a \<notin> set v\<^sub>1" "Ind {a} (set v\<^sub>1)"
        using 0 unfolding indoc_def by blast
      have 2: "Ind (set [a]) (set v\<^sub>1)" using 1(3) by simp
      have "v = v\<^sub>1 @ [a] @ v\<^sub>2" using 1(1) by this
      also have "\<dots> = (v\<^sub>1 @ [a]) @ v\<^sub>2" by simp
      also have "\<dots> =\<^sub>F ([a] @ v\<^sub>1) @ v\<^sub>2" using 2 by blast
      also have "\<dots> = [a] @ v\<^sub>1 @ v\<^sub>2" by simp
      also have "\<dots> = [a] @ remove1 a v" unfolding 1(1) remove1_append using 1(2) by auto
      finally show "v =\<^sub>F [a] @ remove1 a v" by this
    next
      assume 0: "v =\<^sub>F [a] @ remove1 a v"
      have 1: "indoc a ([a] @ remove1 a v)" by simp
      show "indoc a v" using eq_fin_indoc 0  1 by blast
    qed

    lemma levi_lemma:
      assumes "t @ u =\<^sub>F v @ w"
      obtains p r s q
      where "t =\<^sub>F p @ r" "u =\<^sub>F s @ q" "v =\<^sub>F p @ s" "w =\<^sub>F r @ q" "Ind (set r) (set s)"
    using assms
    proof (induct t arbitrary: thesis v w)
      case Nil
      show ?case
      proof (rule Nil(1))
        show "[] =\<^sub>F [] @ []" by simp
        show "v =\<^sub>F [] @ v" by simp
        show "u =\<^sub>F v @ w" using Nil(2) by simp
        show "w =\<^sub>F [] @ w" by simp
        show "Ind (set []) (set v)" by simp
      qed
    next
      case (Cons a t')
      have 1: "[a] \<preceq>\<^sub>F v @ w" using Cons(3) by blast
      show ?case
      proof (cases "a \<in> set v")
        case False
        have 2: "[a] \<preceq>\<^sub>F w" using le_fin_not_member' 1 False by this
        obtain w' where 3: "w =\<^sub>F [a] @ w'" using 2 by blast
        have 4: "v \<preceq>\<^sub>F v @ w" by auto
        have 5: "Ind (set [a]) (set v)" using le_fin_ind'[OF 1 4] False by simp
        have "[a] @ t' @ u = (a # t') @ u" by simp
        also have "\<dots> =\<^sub>F v @ w" using Cons(3) by this
        also have "\<dots> =\<^sub>F v @ [a] @ w'" using 3 by blast
        also have "\<dots> = (v @ [a]) @ w'" by simp
        also have "\<dots> =\<^sub>F ([a] @ v) @ w'" using 5 by blast
        also have "\<dots> = [a] @ v @ w'" by simp
        finally have 6: "t' @ u =\<^sub>F v @ w'" by blast
        obtain p r' s q where 7: "t' =\<^sub>F p @ r'" "u =\<^sub>F s @ q" "v =\<^sub>F p @ s" "w' =\<^sub>F r' @ q"
          "Ind (set r') (set s)" using Cons(1)[OF _ 6] by this
        have 8: "set v = set p \<union> set s" using eq_fin_range 7(3) by auto
        have 9: "Ind (set [a]) (set p)" using 5 8 by auto
        have 10: "Ind (set [a]) (set s)" using 5 8 by auto
        show ?thesis
        proof (rule Cons(2))
          have "a # t' = [a] @ t'" by simp
          also have "\<dots> =\<^sub>F [a] @ p @ r'" using 7(1) by blast
          also have "\<dots> = ([a] @ p) @ r'" by simp
          also have "\<dots> =\<^sub>F (p @ [a]) @ r'" using 9 by blast
          also have "\<dots> = p @ [a] @ r'" by simp
          finally show "a # t' =\<^sub>F p @ [a] @ r'" by this
          show "u =\<^sub>F s @ q" using 7(2) by this
          show "v =\<^sub>F p @ s" using 7(3) by this
          have "w =\<^sub>F [a] @ w'" using 3 by this
          also have "\<dots> =\<^sub>F [a] @ r' @ q" using 7(4) by blast
          also have "\<dots> = ([a] @ r') @ q" by simp
          finally show "w =\<^sub>F ([a] @ r') @ q" by this
          show "Ind (set ([a] @ r')) (set s)" using 7(5) 10 by auto
        qed
      next
        case True
        have 2: "[a] \<preceq>\<^sub>F v" using le_fin_member' 1 True by this
        obtain v' where 3: "v =\<^sub>F [a] @ v'" using 2 by blast
        have "[a] @ t' @ u = (a # t') @ u" by simp
        also have "\<dots> =\<^sub>F v @ w" using Cons(3) by this
        also have "\<dots> =\<^sub>F ([a] @ v') @ w" using 3 by blast
        also have "\<dots> = [a] @ v' @ w" by simp
        finally have 4: "t' @ u =\<^sub>F v' @ w" by blast
        obtain p' r s q where 7: "t' =\<^sub>F p' @ r" "u =\<^sub>F s @ q" "v' =\<^sub>F p' @ s" "w =\<^sub>F r @ q"
          "Ind (set r) (set s)" using Cons(1)[OF _ 4] by this
        show ?thesis
        proof (rule Cons(2))
          have "a # t' = [a] @ t'" by simp
          also have "\<dots> =\<^sub>F [a] @ p' @ r" using 7(1) by blast
          also have "\<dots> = ([a] @ p') @ r" by simp
          finally show "a # t' =\<^sub>F ([a] @ p') @ r" by this
          show "u =\<^sub>F s @ q" using 7(2) by this
          have "v =\<^sub>F [a] @ v'" using 3 by this
          also have "\<dots> =\<^sub>F [a] @ p' @ s" using 7(3) by blast
          also have "\<dots> = ([a] @ p') @ s" by simp
          finally show "v =\<^sub>F ([a] @ p') @ s" by this
          show "w =\<^sub>F r @ q" using 7(4) by this
          show "Ind (set r) (set s)" using 7(5) by this
        qed
      qed
    qed

  end

end
